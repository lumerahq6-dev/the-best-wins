const http = require('http');
const fs = require('fs');
const https = require('https');
const path = require('path');
const crypto = require('crypto');
const { URL } = require('url');

const PORT = process.env.PORT ? Number(process.env.PORT) : 3002;
const HOST = process.env.HOST || '127.0.0.1';

const DATA_DIR = path.join(__dirname, 'data');
const USERS_FILE = path.join(DATA_DIR, 'users.json');

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
  '/styles.css',
  '/script.js',
  '/login.html',
  '/signup.html',
  '/create-account.html',
  '/',
]);

const imageExts = new Set(['.jpg', '.jpeg', '.png', '.gif', '.webp', '.bmp']);
const videoExts = new Set(['.mp4', '.webm', '.mov', '.avi', '.mkv', '.wmv', '.flv']);

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
  // Note: Secure cookies require https. For localhost dev this is typically plain http.
  const cookie = [
    `${SESSION_COOKIE}=${encodeURIComponent(token)}`,
    'Path=/',
    'HttpOnly',
    'SameSite=Lax',
    `Max-Age=${SESSION_TTL_SECONDS}`,
  ].join('; ');
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

function referralGoalFromCount(count) {
  const n = Number(count || 0);
  if (n >= 3) return 3;
  if (n >= 1) return 3;
  return 1;
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
  // "Live connection": always re-read the file so manual edits/deletes apply immediately.
  // If the file is deleted or invalid, treat it as empty.
  await fs.promises.mkdir(DATA_DIR, { recursive: true });

  // Avoid reloading mid-write.
  await usersDbWritePromise.catch(() => {});

  try {
    const raw = await fs.promises.readFile(USERS_FILE, 'utf8');
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
    await fs.promises.mkdir(DATA_DIR, { recursive: true });
    const tmp = `${USERS_FILE}.tmp`;
    await fs.promises.writeFile(tmp, snapshot);
    await fs.promises.rename(tmp, USERS_FILE);
  }).catch(() => {
    // swallow write errors to avoid crashing server; auth calls will fail gracefully
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

function isAllowedMediaFile(fileName) {
  const ext = path.extname(fileName).toLowerCase();
  return imageExts.has(ext) || videoExts.has(ext);
}

function isVideoFile(fileName) {
  return videoExts.has(path.extname(fileName).toLowerCase());
}

async function listMediaFilesForFolder(folder) {
  const folderDirName = allowedFolders.get(folder);
  if (!folderDirName) return [];
  const folderPath = path.join(__dirname, folderDirName);
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
      const body = await readJsonBody(req, res);
      if (!body) return;

      const username = String(body.username || '').trim();
      const password = String(body.password || '');
      if (!isValidUsername(username)) return sendJson(res, 400, { error: 'Invalid username' });
      if (!isValidPassword(password)) return sendJson(res, 400, { error: 'Invalid password' });

      const db = await ensureUsersDbFresh();
      const key = username.toLowerCase();
      if (db.users[key]) return sendJson(res, 409, { error: 'Username exists' });

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

          if (!Array.isArray(refUser.referralCreditIps)) refUser.referralCreditIps = [];
          const ipAlreadyCredited = signupIp !== 'unknown' && refUser.referralCreditIps.includes(signupIp);

          if (!sameIp && !ipAlreadyCredited) {
            // Credit exactly once per referred username
            if (!Array.isArray(refUser.referredUsers)) refUser.referredUsers = [];
            if (!refUser.referredUsers.includes(key)) {
              refUser.referredUsers.push(key);
            }
            if (signupIp !== 'unknown') refUser.referralCreditIps.push(signupIp);
            db.users[key].referredBy = refCode;
          }
        }
      }

      await queueUsersDbWrite();

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
      const tierLabel = tierLabelFromCount(u.referredUsers.length);
      return sendJson(res, 200, { authed: true, username: u.username || userKey, tierLabel });
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
      const count = u.referredUsers.length;
      const goal = referralGoalFromCount(count);
      const tierLabel = tierLabelFromCount(count);

      // Persist referralCode if it was missing.
      await queueUsersDbWrite();

      const base = `http://localhost:${PORT}`;
      const url = `${base}/${code}`;
      return sendJson(res, 200, { code, url, count, goal, tierLabel });
    }

    // ===== DISCORD OAUTH =====
    if (requestUrl.pathname === '/auth/discord') {
      const clientId = process.env.DISCORD_CLIENT_ID;
      const redirectUri = process.env.DISCORD_REDIRECT_URI;
      if (!clientId || !redirectUri) {
        return sendText(res, 501, 'Discord login not configured. Set DISCORD_CLIENT_ID and DISCORD_REDIRECT_URI env vars.');
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
        return sendText(res, 400, 'Invalid OAuth state.');
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
      if (!db.users[userKey]) {
        db.users[userKey] = {
          username: `discord:${discordName}`,
          provider: 'discord',
          discordId,
          createdAt: Date.now(),
        };
        await queueUsersDbWrite();
      }

      const token = crypto.randomBytes(32).toString('hex');
      sessions.set(token, { userKey, createdAt: Date.now() });
      setSessionCookie(res, token);

      // clear state cookie
      appendSetCookie(res, `tbw_oauth_state=; Path=/; HttpOnly; SameSite=Lax; Max-Age=0`);
      res.writeHead(302, { Location: '/index.html?welcome=1' });
      return res.end();
    }

    // ===== TELEGRAM PLACEHOLDER =====
    if (requestUrl.pathname === '/auth/telegram') {
      // Telegram login is possible but requires a bot + domain config; see instructions.
      return sendText(res, 501, 'Telegram login not configured in this build. See setup instructions and implement Telegram Login Widget verification.');
    }

    // API: list files in a category folder
    if (requestUrl.pathname === '/api/list') {
      if (!await requireAuthedUser(req, res)) return;
      const folder = requestUrl.searchParams.get('folder') || '';
      const folderDirName = allowedFolders.get(folder);
      if (!folderDirName) {
        return sendJson(res, 400, { error: 'Invalid folder' });
      }

      const folderPath = path.join(__dirname, folderDirName);
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

      const files = [];
      for (const name of previewNames) {
        const folderDirName = allowedFolders.get(folder);
        const fullPath = path.join(__dirname, folderDirName, name);
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

      const mediaPath = path.join(__dirname, folderDirName, name);
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

      const mediaPath = path.join(__dirname, folderDirName, name);
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
      ...Array.from(allowedFolders.values()).map((d) => path.normalize(path.join(__dirname, d) + path.sep)),
    ];
    for (const pd of protectedDirs) {
      if (normalized.startsWith(pd)) {
        res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
        return res.end('Not Found');
      }
    }

    // Block any direct serving of image/video files via static handler (must go through /media with auth + range).
    if (isAllowedMediaFile(normalized)) {
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
});

server.on('error', (err) => {
  // eslint-disable-next-line no-console
  console.error('Server error:', err);
});
