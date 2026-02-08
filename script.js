// ===== BACKGROUND PARTICLE EFFECT =====
function initBackground() {
  const canvas = document.getElementById('bg-canvas');
  if (!canvas) return;
  const ctx = canvas.getContext('2d');

  let w, h;
  function resize() {
    w = canvas.width = window.innerWidth;
    h = canvas.height = window.innerHeight;
  }
  resize();
  window.addEventListener('resize', resize);

  const particles = [];
  const PARTICLE_COUNT = 70;

  for (let i = 0; i < PARTICLE_COUNT; i++) {
    particles.push({
      x: Math.random() * w,
      y: Math.random() * h,
      vx: (Math.random() - 0.5) * 0.4,
      vy: (Math.random() - 0.5) * 0.4,
      r: Math.random() * 2 + 0.5,
      color: Math.random() > 0.5
        ? `rgba(124, 58, 237, ${Math.random() * 0.4 + 0.1})`
        : `rgba(255, 77, 109, ${Math.random() * 0.3 + 0.05})`,
    });
  }

  function draw() {
    ctx.clearRect(0, 0, w, h);

    for (let i = 0; i < particles.length; i++) {
      const p = particles[i];
      p.x += p.vx;
      p.y += p.vy;

      if (p.x < 0) p.x = w;
      if (p.x > w) p.x = 0;
      if (p.y < 0) p.y = h;
      if (p.y > h) p.y = 0;

      ctx.beginPath();
      ctx.arc(p.x, p.y, p.r, 0, Math.PI * 2);
      ctx.fillStyle = p.color;
      ctx.fill();

      // Draw connections
      for (let j = i + 1; j < particles.length; j++) {
        const p2 = particles[j];
        const dx = p.x - p2.x;
        const dy = p.y - p2.y;
        const dist = Math.sqrt(dx * dx + dy * dy);

        if (dist < 150) {
          ctx.beginPath();
          ctx.moveTo(p.x, p.y);
          ctx.lineTo(p2.x, p2.y);
          ctx.strokeStyle = `rgba(124, 58, 237, ${0.06 * (1 - dist / 150)})`;
          ctx.lineWidth = 0.5;
          ctx.stroke();
        }
      }
    }

    requestAnimationFrame(draw);
  }

  draw();
}

// ===== DISCLAIMER LOGIC =====
function initDisclaimer() {
  const overlay = document.getElementById('disclaimer-overlay');
  const homepage = document.getElementById('homepage');
  const acceptBtn = document.getElementById('accept-btn');

  if (!overlay || !acceptBtn) return;

  function hideOverlay() {
    overlay.classList.add('hidden');
    if (homepage) homepage.classList.remove('blurred');
  }

  // Check if already accepted
  if (sessionStorage.getItem('age_verified') === 'true') {
    hideOverlay();
    return;
  }

  // If user is authed, skip the warning entirely.
  (async () => {
    try {
      const resp = await fetch('/api/me', { cache: 'no-store' });
      if (!resp.ok) return;
      const data = await resp.json();
      if (data && data.authed) {
        hideOverlay();
        sessionStorage.setItem('age_verified', 'true');
      }
    } catch {
      // ignore
    }
  })();

  acceptBtn.addEventListener('click', () => {
    overlay.style.animation = 'fadeOut 0.3s ease forwards';
    setTimeout(() => {
      hideOverlay();
      sessionStorage.setItem('age_verified', 'true');
    }, 280);
  });
}

// ===== FOLDER PAGE: LOAD MEDIA =====
function initFolderPage() {
  const grid = document.querySelector('.media-grid');
  if (!grid) return;

  const params = new URLSearchParams(window.location.search);
  const folder = params.get('folder');
  if (!folder) return;

  // Set title
  const titleEl = document.querySelector('.folder-page h1');
  const breadcrumbCurrent = document.querySelector('.breadcrumb .current');
  if (titleEl) titleEl.textContent = folder;
  if (breadcrumbCurrent) breadcrumbCurrent.textContent = folder;

  // Load actual files from the directory (requires local server)
  loadFolderFromApi(folder, grid);
}

async function loadFolderFromApi(folder, grid) {
  const previewCta = document.getElementById('preview-cta');
  const setPreviewCta = (visible) => {
    if (!previewCta) return;
    previewCta.hidden = !visible;
  };

  // Always show the CTA banner on folder pages, even when authed.
  setPreviewCta(true);

  grid.innerHTML = `
    <div style="grid-column: 1/-1; text-align: center; padding: 50px 20px; color: #666;">
      <div style="font-size: 44px; margin-bottom: 14px;">⏳</div>
      <h3 style="color: #aaa; margin-bottom: 8px;">Loading files…</h3>
      <p style="font-size: 13px;">Reading <strong>${folder}</strong></p>
    </div>`;

  try {
    const resp = await fetch(`/api/list?folder=${encodeURIComponent(folder)}`);
    if (resp.status === 401) {
      // No auth: show free preview (if enabled on server)
      const prev = await fetch(`/api/preview/list?folder=${encodeURIComponent(folder)}`, { cache: 'no-store' });
      if (prev.ok) {
        const data = await prev.json();
        const files = Array.isArray(data.files) ? data.files : [];
        if (files.length) {
          renderMediaGrid(grid, files);
          const titleEl = document.querySelector('.folder-page h1');
          if (titleEl) titleEl.textContent = `${folder} (Preview)`;
          setPreviewCta(true);
          return;
        }
      }

      grid.innerHTML = `
        <div style="grid-column: 1/-1; text-align: center; padding: 60px 20px; color: #666;">
          <div style="font-size: 48px; margin-bottom: 20px;">👀</div>
          <h3 style="color: #bbb; margin-bottom: 10px;">Preview unavailable</h3>
          <p style="max-width: 680px; margin: 0 auto; line-height: 1.7;">
            This collection doesn’t have a free preview right now.
          </p>
        </div>`;

      // Still show the CTA so users can choose to log in.
      setPreviewCta(true);
      return;
    }
    if (!resp.ok) {
      throw new Error(`API error: ${resp.status}`);
    }

    /** @type {{files: Array<{name: string, type: 'image'|'video', src: string, size?: number}>}} */
    const data = await resp.json();
    const files = Array.isArray(data.files) ? data.files : [];

    if (files.length === 0) {
      grid.innerHTML = `
        <div style="grid-column: 1/-1; text-align: center; padding: 60px 20px; color: #666;">
          <div style="font-size: 48px; margin-bottom: 20px;">📁</div>
          <h3 style="color: #999; margin-bottom: 10px;">No files found</h3>
          <p>Add images or videos to the "${folder}" folder</p>
        </div>`;
      setPreviewCta(true);
      return;
    }

    renderMediaGrid(grid, files);
    setPreviewCta(true);
  } catch (err) {
    grid.innerHTML = `
      <div style="grid-column: 1/-1; text-align: center; padding: 60px 20px; color: #666;">
        <div style="font-size: 48px; margin-bottom: 20px;">⚠️</div>
        <h3 style="color: #bbb; margin-bottom: 10px;">Can’t read folder files</h3>
        <p style="max-width: 680px; margin: 0 auto; line-height: 1.7;">
          Browsers can’t list local folders from a plain <strong>file://</strong> page.
          Start the included local server, then open the site at <strong>${location.origin}</strong>.
        </p>
        <p style="font-size: 13px; margin-top: 12px; color: #777;">Command: <strong>node server.js</strong></p>
      </div>`;
    setPreviewCta(true);
  }
}

function renderMediaGrid(grid, items) {
  grid.innerHTML = '';

  items.forEach((item, idx) => {
    const div = document.createElement('div');
    div.className = `media-item ${item.type === 'video' ? 'video-item' : ''}`;

    if (item.type === 'video') {
      div.innerHTML = `
        <div class="media-thumb-wrapper">
          <video class="media-thumb" preload="metadata" muted playsinline></video>
          <div class="play-icon"></div>
        </div>
        <div class="media-info">
          <div class="name">${item.name}</div>
          <div class="meta">Video ${item.size ? '• ' + formatFileSize(item.size) : ''}</div>
        </div>`;

      // Seek to 0.5s so the browser renders a real frame instead of black
      const vid = div.querySelector('video');
      vid.addEventListener('loadeddata', () => {
        if (vid.duration > 0.5) vid.currentTime = 0.5;
        else if (vid.duration > 0) vid.currentTime = 0;
      }, { once: true });
      vid.src = item.src;
    } else {
      div.innerHTML = `
        <img class="media-thumb" src="${item.src}" alt="${item.name}" loading="lazy">
        <div class="media-info">
          <div class="name">${item.name}</div>
          <div class="meta">Image ${item.size ? '• ' + formatFileSize(item.size) : ''}</div>
        </div>`;
    }

    // Click to open lightbox
    div.addEventListener('click', () => openLightbox(item));
    grid.appendChild(div);
  });
}

function formatFileSize(bytes) {
  if (!bytes || bytes === 'Unknown') return '';
  const size = parseInt(bytes);
  if (size < 1024) return size + 'B';
  if (size < 1024 * 1024) return Math.round(size / 1024) + 'KB';
  return Math.round(size / (1024 * 1024)) + 'MB';
}

// ===== LIGHTBOX =====
function openLightbox(item) {
  if (!item.src) return;
  
  let lightbox = document.getElementById('lightbox');
  if (!lightbox) {
    lightbox = document.createElement('div');
    lightbox.id = 'lightbox';
    lightbox.className = 'lightbox';
    lightbox.innerHTML = `<button class="lightbox-close">&times;</button><div class="lightbox-content"></div>`;
    document.body.appendChild(lightbox);
    
    lightbox.querySelector('.lightbox-close').addEventListener('click', () => {
      lightbox.classList.remove('active');
      lightbox.querySelector('.lightbox-content').innerHTML = '';
    });

    lightbox.addEventListener('click', (e) => {
      if (e.target === lightbox) {
        lightbox.classList.remove('active');
        lightbox.querySelector('.lightbox-content').innerHTML = '';
      }
    });
  }

  const content = lightbox.querySelector('.lightbox-content');
  if (item.type === 'video') {
    content.innerHTML = `<video src="${item.src}" controls autoplay playsinline disablepictureinpicture controlslist="nodownload noremoteplayback" style="max-width:90%;max-height:85vh;border-radius:12px;"></video>`;
  } else {
    content.innerHTML = `<img src="${item.src}" style="max-width:90%;max-height:85vh;border-radius:12px;">`;
  }

  lightbox.classList.add('active');
}

// ===== REFERRAL LEADERBOARD =====
function initLeaderboard() {
  const widget = document.getElementById('leaderboard-widget');
  if (!widget) return;

  const listEl = document.getElementById('leaderboard-list');
  const pageEl = document.getElementById('lb-page');
  const prevBtn = document.getElementById('lb-prev');
  const nextBtn = document.getElementById('lb-next');
  if (!listEl || !pageEl || !prevBtn || !nextBtn) return;

  let currentPage = 0;
  let totalPages = 1;

  async function loadPage(page) {
    try {
      const resp = await fetch(`/api/referral/leaderboard?page=${page}`, { cache: 'no-store' });
      if (!resp.ok) return;
      const data = await resp.json();
      currentPage = data.page || 0;
      totalPages = data.totalPages || 1;
      const entries = Array.isArray(data.entries) ? data.entries : [];

      listEl.innerHTML = '';
      if (entries.length === 0) {
        listEl.innerHTML = '<li style="justify-content:center;color:rgba(255,255,255,0.35);font-size:10px;">No referrals yet</li>';
      } else {
        entries.forEach(e => {
          const li = document.createElement('li');
          li.innerHTML = `<span class="lb-rank">#${e.rank}</span><span class="lb-name">${escapeHtml(e.username)}</span><span class="lb-count">${e.count}</span>`;
          listEl.appendChild(li);
        });
      }

      pageEl.textContent = `${currentPage + 1} / ${totalPages}`;
      prevBtn.disabled = currentPage <= 0;
      nextBtn.disabled = currentPage >= totalPages - 1;
    } catch {
      // ignore
    }
  }

  function escapeHtml(str) {
    const d = document.createElement('div');
    d.textContent = str;
    return d.innerHTML;
  }

  prevBtn.addEventListener('click', () => {
    if (currentPage > 0) loadPage(currentPage - 1);
  });
  nextBtn.addEventListener('click', () => {
    if (currentPage < totalPages - 1) loadPage(currentPage + 1);
  });

  loadPage(0);
}

function initLeaderboardPlacement() {
  const widget = document.getElementById('leaderboard-widget');
  if (!widget) return;

  const originalParent = widget.parentElement;
  const originalNext = widget.nextSibling;
  const referralFooter = document.getElementById('referral-footer');
  const tutorialBtn = document.getElementById('referral-tutorial');

  function place() {
    const isMobile = window.innerWidth <= 768;
    if (isMobile && referralFooter && tutorialBtn) {
      tutorialBtn.insertAdjacentElement('afterend', widget);
      return;
    }
    if (!originalParent) return;
    if (originalNext && originalNext.parentNode === originalParent) {
      originalParent.insertBefore(widget, originalNext);
    } else {
      originalParent.appendChild(widget);
    }
  }

  place();
  window.addEventListener('resize', () => {
    place();
  });
}

// ===== TOS / DMCA POPUP =====
function initTosDmcaPopup() {
  const link = document.getElementById('tos-dmca-link');
  const overlay = document.getElementById('tos-dmca-overlay');
  if (!link || !overlay) return;

  const closeBtn = document.getElementById('tos-dmca-close');

  function setOpen(isOpen) {
    overlay.classList.toggle('active', isOpen);
    overlay.setAttribute('aria-hidden', isOpen ? 'false' : 'true');
    document.body.style.overflow = isOpen ? 'hidden' : '';
  }

  link.addEventListener('click', () => setOpen(true));
  if (closeBtn) closeBtn.addEventListener('click', () => setOpen(false));
  overlay.addEventListener('click', (e) => {
    if (e.target === overlay) setOpen(false);
  });
  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape') setOpen(false);
  });
}

// ===== INIT =====
document.addEventListener('DOMContentLoaded', () => {
  initBackground();
  initDisclaimer();
  initFolderPage();

  initAuthModal();
  initProfileMenu();
  initHomeReferralAndAuth();
  initTierMegaUnlock();
  initLeaderboard();
  initLeaderboardPlacement();
  initTosDmcaPopup();

  // Best-effort: block right-click save/download menu on videos.
  document.addEventListener('contextmenu', (e) => {
    const target = e.target;
    if (target && target.tagName === 'VIDEO') {
      e.preventDefault();
    }
  });
});

// Fade out keyframe (added dynamically)
const style = document.createElement('style');
style.textContent = `@keyframes fadeOut { to { opacity: 0; } }`;
document.head.appendChild(style);

// ===== AUTH MODAL (ACCESS PAGE) =====
function initAuthModal() {
  const overlay = document.getElementById('auth-overlay');
  if (!overlay) return;

  const modal = overlay.querySelector('.auth-modal');
  const closeBtn = overlay.querySelector('.auth-close');
  const messageEl = document.getElementById('auth-message');
  const tabs = Array.from(overlay.querySelectorAll('[data-auth-tab]'));
  const panes = Array.from(overlay.querySelectorAll('[data-auth-pane]'));
  const loginForm = document.getElementById('auth-login');
  const signupForm = document.getElementById('auth-signup');
  const socialBtns = Array.from(overlay.querySelectorAll('[data-social]'));

  function setMessage(text, kind) {
    if (!messageEl) return;
    messageEl.textContent = text || '';
    messageEl.classList.remove('error', 'success');
    if (kind) messageEl.classList.add(kind);
  }

  function openModal() {
    overlay.classList.add('active');
    overlay.setAttribute('aria-hidden', 'false');
    document.body.style.overflow = 'hidden';
    setMessage('', null);
    // focus first input
    const first = overlay.querySelector('input');
    if (first) first.focus();
  }

  function closeModal() {
    overlay.classList.remove('active');
    overlay.setAttribute('aria-hidden', 'true');
    document.body.style.overflow = '';
    setMessage('', null);
  }

  function setTab(tabName) {
    tabs.forEach((t) => {
      const isActive = t.getAttribute('data-auth-tab') === tabName;
      t.classList.toggle('active', isActive);
      t.setAttribute('aria-selected', isActive ? 'true' : 'false');
    });
    panes.forEach((p) => {
      const isActive = p.getAttribute('data-auth-pane') === tabName;
      p.classList.toggle('hidden', !isActive);
    });
    setMessage('', null);
  }

  // Open modal when clicking tier cards
  document.querySelectorAll('[data-auth-open]').forEach((btn) => {
    btn.addEventListener('click', () => {
      setTab('login');
      openModal();
    });
  });

  // Close behaviors
  if (closeBtn) closeBtn.addEventListener('click', closeModal);
  overlay.addEventListener('click', (e) => {
    if (e.target === overlay) closeModal();
  });
  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape' && overlay.classList.contains('active')) {
      closeModal();
    }
  });

  // Tabs
  tabs.forEach((t) => {
    t.addEventListener('click', () => setTab(t.getAttribute('data-auth-tab')));
  });

  // Social buttons (server-backed if configured)
  socialBtns.forEach((b) => {
    b.addEventListener('click', async () => {
      const provider = String(b.getAttribute('data-social') || '').toLowerCase();
      if (provider === 'discord') {
        window.location.href = '/auth/discord';
        return;
      }
      if (provider === 'google') {
        window.location.href = '/auth/google';
        return;
      }
      setMessage('Unknown provider.', 'error');
    });
  });

  if (loginForm) {
    loginForm.addEventListener('submit', async (e) => {
      e.preventDefault();
      setMessage('Checking…', null);
      const fd = new FormData(loginForm);
      const username = String(fd.get('username') || '').trim();
      const password = String(fd.get('password') || '');

      try {
        const resp = await fetch('/api/login', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ username, password }),
        });
        if (!resp.ok) {
          setMessage('Invalid username or password.', 'error');
          return;
        }
        setMessage('Logged in. Redirecting…', 'success');
        sessionStorage.setItem('tbw_show_ref_tutorial', '1');
        setTimeout(() => {
          location.href = '/index.html?welcome=1';
        }, 250);
      } catch {
        setMessage('Login failed. Try again.', 'error');
      }
    });
  }

  if (signupForm) {
    signupForm.addEventListener('submit', async (e) => {
      e.preventDefault();
      setMessage('Creating account…', null);
      const fd = new FormData(signupForm);
      const username = String(fd.get('username') || '').trim();
      const password = String(fd.get('password') || '');
      const password2 = String(fd.get('password2') || '');

      if (password !== password2) {
        setMessage('Passwords do not match.', 'error');
        return;
      }

      try {
        const resp = await fetch('/api/signup', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ username, password }),
        });
        if (resp.status === 409) {
          let errMsg = 'That username is already taken.';
          try {
            const errData = await resp.json();
            if (errData && errData.error) errMsg = errData.error;
          } catch {}
          setMessage(errMsg, 'error');
          return;
        }
        if (!resp.ok) {
          let errMsg = 'Sign up failed. Try again.';
          try {
            const errData = await resp.json();
            if (errData && errData.error) errMsg = errData.error;
          } catch {}
          setMessage(errMsg, 'error');
          return;
        }

        // Auto-login after signup
        const loginResp = await fetch('/api/login', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ username, password }),
        });
        if (!loginResp.ok) {
          setMessage('Account created. Now login.', 'success');
          setTab('login');
          return;
        }
        setMessage('Account created. Redirecting…', 'success');
        sessionStorage.setItem('tbw_show_ref_tutorial', '1');
        setTimeout(() => {
          location.href = '/index.html?welcome=1';
        }, 250);
      } catch (err) {
        setMessage('Sign up failed. Check your connection and try again.', 'error');
      }
    });
  }

  // Prevent form submit on Enter inside modal from bubbling weirdly
  if (modal) {
    modal.addEventListener('submit', (e) => e.stopPropagation());
  }
}

// ===== HOME: REFERRAL + AUTH FLOW =====
function initHomeReferralAndAuth() {
  const referralFooter = document.getElementById('referral-footer');
  const goalCountEl = document.getElementById('referral-goal-count');
  const barFillEl = document.getElementById('referral-bar-fill');
  const tutorialBtn = document.getElementById('referral-tutorial');
  const homeLoginBtn = document.getElementById('home-login');

  const refOverlay = document.getElementById('referral-overlay');
  const refClose = document.getElementById('referral-close');
  const refHelloName = document.getElementById('referral-hello-name');
  const refLinkInput = document.getElementById('referral-link');
  const refCopyBtn = document.getElementById('referral-copy');
  const refCopiedEl = document.getElementById('referral-copied');

  const refOpenTriggers = Array.from(document.querySelectorAll('[data-ref-open]'));

  const authOverlay = document.getElementById('auth-overlay');

  // Not on home page.
  if (!referralFooter && !refOverlay && !homeLoginBtn) return;

  // Default: never show referral UI until we confirm auth.
  if (referralFooter) referralFooter.hidden = true;

  function setOverlayOpen(isOpen) {
    if (!refOverlay) return;
    refOverlay.classList.toggle('active', isOpen);
    refOverlay.setAttribute('aria-hidden', isOpen ? 'false' : 'true');
    document.body.style.overflow = isOpen ? 'hidden' : '';
    if (!isOpen && refCopiedEl) refCopiedEl.textContent = '';
  }

  function openAuthModal(tab) {
    if (!authOverlay) return;
    const tabBtn = authOverlay.querySelector(`[data-auth-tab="${tab}"]`);
    if (tabBtn) tabBtn.click();
    authOverlay.classList.add('active');
    authOverlay.setAttribute('aria-hidden', 'false');
    document.body.style.overflow = 'hidden';
    const first = authOverlay.querySelector('input');
    if (first) first.focus();
  }

  function normalizePath(pathname) {
    if (!pathname) return '';
    // handle Windows-ish or trailing slashes
    return pathname.endsWith('/') ? pathname.slice(0, -1) : pathname;
  }

  async function fetchMe() {
    try {
      const resp = await fetch('/api/me', { cache: 'no-store' });
      if (!resp.ok) return { authed: false };
      return await resp.json();
    } catch {
      return { authed: false };
    }
  }

  async function refreshReferralUi() {
    if (!referralFooter && !refOverlay) return;

    const me = await fetchMe();
    const authed = !!(me && me.authed);
    if (!authed) {
      if (referralFooter) referralFooter.hidden = true;
      if (homeLoginBtn) homeLoginBtn.hidden = false;
      return;
    }
    if (homeLoginBtn) homeLoginBtn.hidden = true;
    if (referralFooter) referralFooter.hidden = false;
    if (refHelloName) refHelloName.textContent = String(me.username || 'USER').toUpperCase();

    try {
      const resp = await fetch('/api/referral/status', { cache: 'no-store' });
      if (!resp.ok) return;
      const data = await resp.json();
      if (refLinkInput && data && data.url) refLinkInput.value = String(data.url);

      const count = Number(data.count || 0);
      const goal = Number(data.goal || 1);
      const pct = goal > 0 ? Math.min(100, Math.round((count / goal) * 100)) : 0;
      if (goalCountEl) goalCountEl.textContent = `${count}/${goal}`;
      if (barFillEl) barFillEl.style.width = `${pct}%`;

      // Also update profile tier if present
      const profileTier = document.getElementById('profile-tier');
      if (profileTier && data && data.tierLabel) profileTier.textContent = String(data.tierLabel);
    } catch {
      // ignore
    }
  }

  async function copyText(text) {
    const value = String(text || '');
    if (!value) return false;

    try {
      await navigator.clipboard.writeText(value);
      return true;
    } catch {
      // Fallback
      try {
        const ta = document.createElement('textarea');
        ta.value = value;
        ta.setAttribute('readonly', '');
        ta.style.position = 'fixed';
        ta.style.left = '-9999px';
        document.body.appendChild(ta);
        ta.select();
        const ok = document.execCommand('copy');
        document.body.removeChild(ta);
        return ok;
      } catch {
        return false;
      }
    }
  }

  // Bind tutorial popup open/close
  if (tutorialBtn) {
    tutorialBtn.addEventListener('click', () => {
      setOverlayOpen(true);
    });
  }
  if (refOpenTriggers.length) {
    refOpenTriggers.forEach((btn) => btn.addEventListener('click', async (e) => {
      e.preventDefault();
      const me = await fetchMe();
      const authed = !!(me && me.authed);
      if (!authed && authOverlay) return openAuthModal('login');
      setOverlayOpen(true);
      refreshReferralUi();
    }));
  }
  if (refClose) refClose.addEventListener('click', () => setOverlayOpen(false));
  if (refOverlay) {
    refOverlay.addEventListener('click', (e) => {
      if (e.target === refOverlay) setOverlayOpen(false);
    });
  }
  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape') setOverlayOpen(false);
  });

  if (refCopyBtn) {
    refCopyBtn.addEventListener('click', async () => {
      const value = refLinkInput ? refLinkInput.value : '';
      const ok = await copyText(value);
      if (refCopiedEl) refCopiedEl.textContent = ok ? 'Copied.' : 'Copy failed.';
      if (ok) setTimeout(() => {
        if (refCopiedEl) refCopiedEl.textContent = '';
      }, 1200);
    });
  }

  // Home login button
  if (homeLoginBtn) {
    homeLoginBtn.addEventListener('click', () => openAuthModal('login'));
  }

  // Query-driven behaviors
  (async () => {
    const params = new URLSearchParams(location.search);
    const wantsLogin = params.get('login') === '1';
    const welcome = params.get('welcome') === '1';
    const ipError = params.get('ip_error') === '1';
    const vpnError = params.get('vpn_error') === '1';

    if (ipError || vpnError) {
      const alert = document.createElement('div');
      alert.className = 'ip-error-alert';
      alert.textContent = vpnError
        ? 'VPN or proxy detected. Please disable it to sign up.'
        : 'An account already exists on this IP';
      document.body.appendChild(alert);
      requestAnimationFrame(() => alert.classList.add('visible'));
      setTimeout(() => {
        alert.classList.remove('visible');
        setTimeout(() => alert.remove(), 400);
      }, 5000);
      // Clean URL
      const clean = new URL(location.href);
      clean.searchParams.delete('ip_error');
      clean.searchParams.delete('vpn_error');
      history.replaceState(null, '', clean.toString());
    }
    const ref = params.get('ref');

    const me = await fetchMe();
    const authed = !!(me && me.authed);

    // If arriving from a referral link and not authed, push user into signup.
    if (ref && !authed) {
      sessionStorage.setItem('tbw_has_ref', '1');
      openAuthModal('signup');
    } else if (wantsLogin && !authed) {
      openAuthModal('login');
    }

    // Auto-open tutorial after login redirect.
    const shouldShow = sessionStorage.getItem('tbw_show_ref_tutorial') === '1' || welcome;
    if (authed && shouldShow) {
      sessionStorage.removeItem('tbw_show_ref_tutorial');
      setOverlayOpen(true);
    }

    // Clean URL params to keep it neat.
    if (location.search) {
      const cleaned = normalizePath(location.pathname) || '/index.html';
      history.replaceState(null, '', cleaned);
    }
  })();

  // Initial paint
  refreshReferralUi();
}

// ===== PROFILE MENU (TOP RIGHT) =====
function initProfileMenu() {
  const root = document.getElementById('profile');
  if (!root) return;

  const btn = document.getElementById('profile-btn');
  const dropdown = document.getElementById('profile-dropdown');
  const usernameEl = document.getElementById('profile-username');
  const avatarEl = document.getElementById('profile-avatar');
  const logoutBtn = document.getElementById('profile-logout');
  const telegramExt = document.getElementById('profile-telegram-ext');

  if (!btn || !dropdown || !usernameEl || !logoutBtn || !avatarEl) return;

  let authedUsername = null;

  function setOpen(isOpen) {
    dropdown.classList.toggle('active', isOpen);
    btn.setAttribute('aria-expanded', isOpen ? 'true' : 'false');
  }

  function initialsFor(name) {
    const s = String(name || '').trim();
    if (!s) return 'U';
    const parts = s.split(/\s+/).filter(Boolean);
    const first = parts[0] ? parts[0][0] : s[0];
    const second = parts.length > 1 ? parts[1][0] : (s.length > 1 ? s[1] : '');
    return (first + second).toUpperCase();
  }

  async function refreshMe() {
    try {
      const resp = await fetch('/api/me', { cache: 'no-store' });
      if (!resp.ok) {
        root.hidden = true;
        return;
      }
      const data = await resp.json();
      if (!data || !data.authed) {
        root.hidden = true;
        if (telegramExt) telegramExt.hidden = true;
        return;
      }
      authedUsername = String(data.username || 'User');
      usernameEl.textContent = authedUsername;
      const tierEl = document.getElementById('profile-tier');
      if (tierEl) tierEl.textContent = String(data.tierLabel || 'NO TIER');
      avatarEl.textContent = initialsFor(authedUsername);
      root.hidden = false;
      if (telegramExt) telegramExt.hidden = false;
    } catch {
      root.hidden = true;
      if (telegramExt) telegramExt.hidden = true;
    }
  }

  btn.addEventListener('click', () => {
    if (root.hidden) return;
    const open = dropdown.classList.contains('active');
    setOpen(!open);
  });

  document.addEventListener('click', (e) => {
    if (root.hidden) return;
    if (!root.contains(e.target)) setOpen(false);
  });

  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape') setOpen(false);
  });

  logoutBtn.addEventListener('click', async () => {
    try {
      await fetch('/api/logout', { method: 'POST' });
    } finally {
      sessionStorage.removeItem('age_verified');
      setOpen(false);
      root.hidden = true;
      if (telegramExt) telegramExt.hidden = true;
      // If user is on a locked page, send them home.
      if (location.pathname.endsWith('/folder.html') || location.pathname.endsWith('/access.html')) {
        location.href = '/index.html';
      } else {
        location.reload();
      }
    }
  });

  // initial load
  refreshMe();
}

// ===== TIER 1+ MEGA LINK UI =====
function initTierMegaUnlock() {
  const btn = document.getElementById('tier-unlocked-btn');
  const overlay = document.getElementById('mega-overlay');
  if (!btn || !overlay) return;

  const closeBtn = document.getElementById('mega-close');
  const linkInput = document.getElementById('mega-link');
  const copyBtn = document.getElementById('mega-copy');
  const copiedEl = document.getElementById('mega-copied');

  let currentTier = null;

  function setOverlayOpen(isOpen) {
    overlay.classList.toggle('active', isOpen);
    overlay.setAttribute('aria-hidden', isOpen ? 'false' : 'true');
    document.body.style.overflow = isOpen ? 'hidden' : '';
    if (!isOpen && copiedEl) copiedEl.textContent = '';
  }

  async function copyText(text) {
    const value = String(text || '');
    if (!value) return false;

    try {
      await navigator.clipboard.writeText(value);
      return true;
    } catch {
      try {
        const ta = document.createElement('textarea');
        ta.value = value;
        ta.setAttribute('readonly', '');
        ta.style.position = 'fixed';
        ta.style.left = '-9999px';
        document.body.appendChild(ta);
        ta.select();
        const ok = document.execCommand('copy');
        document.body.removeChild(ta);
        return ok;
      } catch {
        return false;
      }
    }
  }

  function b64ToText(b64) {
    const s = String(b64 || '');
    if (!s) return '';
    try {
      // atob handles base64 -> binary string; this is fine for URLs.
      return atob(s);
    } catch {
      return '';
    }
  }

  async function refreshTierButton() {
    try {
      const resp = await fetch('/api/me', { cache: 'no-store' });
      if (!resp.ok) {
        btn.hidden = true;
        return;
      }
      const data = await resp.json();
      if (!data || !data.authed) {
        btn.hidden = true;
        return;
      }

      currentTier = String(data.tierLabel || 'NO TIER');
      const unlocked = currentTier === 'TIER 1' || currentTier === 'TIER 2';
      btn.hidden = !unlocked;
      if (unlocked) {
        btn.textContent = currentTier === 'TIER 2'
          ? 'TIER 2 UNLOCKED - CLICK HERE'
          : 'TIER 1 UNLOCKED - CLICK HERE';
      }
    } catch {
      btn.hidden = true;
    }
  }

  btn.addEventListener('click', async () => {
    if (copiedEl) copiedEl.textContent = '';
    if (linkInput) linkInput.value = '';

    btn.disabled = true;
    const oldText = btn.textContent;
    btn.textContent = 'LOADING…';

    try {
      const resp = await fetch('/api/mega', { cache: 'no-store' });
      if (!resp.ok) {
        btn.textContent = oldText;
        btn.disabled = false;
        return;
      }
      const data = await resp.json();
      const encoding = String(data && data.encoding || '');
      const payload = String(data && data.link || '');
      const link = encoding === 'base64' ? b64ToText(payload) : payload;
      if (linkInput) linkInput.value = link;
      setOverlayOpen(true);
    } catch {
      // ignore
    } finally {
      btn.textContent = oldText;
      btn.disabled = false;
    }
  });

  if (copyBtn) {
    copyBtn.addEventListener('click', async () => {
      const value = linkInput ? linkInput.value : '';
      const ok = await copyText(value);
      if (copiedEl) copiedEl.textContent = ok ? 'Copied.' : 'Copy failed.';
      if (ok) setTimeout(() => {
        if (copiedEl) copiedEl.textContent = '';
      }, 1200);
    });
  }

  if (closeBtn) closeBtn.addEventListener('click', () => setOverlayOpen(false));
  overlay.addEventListener('click', (e) => {
    if (e.target === overlay) setOverlayOpen(false);
  });
  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape') setOverlayOpen(false);
  });

  refreshTierButton();
}

/* ================================================================
   PAYMENT POPUP
   ================================================================ */
(function initPaymentPopup() {
  const overlay = document.getElementById('payment-overlay');
  if (!overlay) return;

  const closeBtn = document.getElementById('payment-close');
  const step1    = document.getElementById('pay-step-1');
  const step2    = document.getElementById('pay-step-2');
  const step3    = document.getElementById('pay-step-3');
  const planLabel = document.getElementById('pay-plan-label');
  const amountEl  = document.getElementById('pay-amount');
  const toUser    = document.getElementById('pay-to-user');
  const toMethod  = document.getElementById('pay-to-method');
  const toDetail  = document.getElementById('pay-to-detail');
  const warnEl    = document.getElementById('pay-warn');
  const dropzone  = document.getElementById('pay-dropzone');
  const fileInput = document.getElementById('pay-file');
  const preview   = document.getElementById('pay-preview');
  const submitBtn = document.getElementById('pay-submit');
  const backBtn1  = document.getElementById('pay-back-1');
  const backBtn2  = document.getElementById('pay-back-2');

  const PLANS = {
    tier1:   { label: 'Tier 1',  price: '$5.99' },
    premium: { label: 'Premium', price: '$9.99' }
  };

  const METHODS = {
    paypal:   { user: 'indoshray@gmail.com', display: 'PayPal',    warn: 'FRIENDS AND FAMILY OR WE IGNORE YOU' },
    cashapp:  { user: '$shreygg',             display: 'Cash App',  warn: '' },
    zelle:    { user: '571-326-6602',         display: 'Zelle',     warn: '' },
    venmo:    { user: 'shrayg',               display: 'Venmo',     warn: '' },
    applepay: { user: '571-326-6602',         display: 'Apple Pay', warn: '' }
  };

  let chosenPlan   = null;   // 'tier1' | 'premium'
  let chosenMethod = null;   // key in METHODS
  let chosenFile   = null;

  function showStep(n) {
    [step1, step2, step3].forEach((s, i) => {
      if (s) s.classList.toggle('active', i === n - 1);
    });
  }

  async function openPayment() {
    // Require login before allowing payment
    try {
      const meResp = await fetch('/api/me', { cache: 'no-store' });
      if (meResp.ok) {
        const meData = await meResp.json();
        if (!meData || !meData.authed) {
          window.location.href = '/login.html';
          return;
        }
      } else {
        window.location.href = '/login.html';
        return;
      }
    } catch {
      window.location.href = '/login.html';
      return;
    }
    chosenPlan = null; chosenMethod = null; chosenFile = null;
    if (preview) { preview.style.display = 'none'; preview.src = ''; }
    if (submitBtn) submitBtn.disabled = true;
    showStep(1);
    overlay.classList.add('active');
    overlay.setAttribute('aria-hidden', 'false');
    document.body.style.overflow = 'hidden';
  }

  function closePayment() {
    overlay.classList.remove('active');
    overlay.setAttribute('aria-hidden', 'true');
    document.body.style.overflow = '';
  }

  // Open trigger — the "Or Click Here To Unlock Full Access" button
  const openBtn = document.getElementById('open-payment');
  if (openBtn) openBtn.addEventListener('click', (e) => { e.preventDefault(); openPayment(); });

  // Close
  if (closeBtn) closeBtn.addEventListener('click', closePayment);
  overlay.addEventListener('click', (e) => { if (e.target === overlay) closePayment(); });
  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape' && overlay.classList.contains('active')) closePayment();
  });

  // Step 1 → Step 2: pick a plan
  document.querySelectorAll('[data-plan]').forEach(btn => {
    btn.addEventListener('click', () => {
      chosenPlan = btn.dataset.plan;
      const p = PLANS[chosenPlan];
      if (planLabel) planLabel.textContent = p.label + ' — ' + p.price;
      showStep(2);
    });
  });

  // Step 2 → Step 3: pick payment method
  document.querySelectorAll('[data-method]').forEach(btn => {
    btn.addEventListener('click', () => {
      chosenMethod = btn.dataset.method;
      const m = METHODS[chosenMethod];
      const p = PLANS[chosenPlan];
      if (amountEl) amountEl.textContent = p.price;
      if (toUser)   toUser.textContent   = m.user;
      if (toMethod) toMethod.textContent = m.display;
      if (toDetail) toDetail.textContent = m.user;
      if (warnEl)   { warnEl.textContent = m.warn; warnEl.style.display = m.warn ? 'block' : 'none'; }
      // Reset file
      chosenFile = null;
      if (preview) { preview.style.display = 'none'; preview.src = ''; }
      if (submitBtn) submitBtn.disabled = true;
      if (fileInput) fileInput.value = '';
      showStep(3);
    });
  });

  // Back buttons
  if (backBtn1) backBtn1.addEventListener('click', () => showStep(1));
  if (backBtn2) backBtn2.addEventListener('click', () => showStep(2));

  // File upload / drag-drop
  function handleFile(file) {
    if (!file || !file.type.startsWith('image/')) return;
    chosenFile = file;
    const reader = new FileReader();
    reader.onload = () => {
      if (preview) { preview.src = reader.result; preview.style.display = 'block'; }
      // Auto-submit immediately after file selected
      doSubmit();
    };
    reader.readAsDataURL(file);
  }

  if (dropzone && fileInput) {
    dropzone.addEventListener('click', () => fileInput.click());
    dropzone.addEventListener('dragover', (e) => { e.preventDefault(); dropzone.classList.add('dragover'); });
    dropzone.addEventListener('dragleave', () => dropzone.classList.remove('dragover'));
    dropzone.addEventListener('drop', (e) => {
      e.preventDefault(); dropzone.classList.remove('dragover');
      if (e.dataTransfer.files.length) handleFile(e.dataTransfer.files[0]);
    });
    fileInput.addEventListener('change', () => { if (fileInput.files.length) handleFile(fileInput.files[0]); });
  }

  // Submit (auto-called after file selection)
  async function doSubmit() {
    if (!chosenFile || !chosenPlan || !chosenMethod) return;
    if (submitBtn) { submitBtn.disabled = true; submitBtn.style.display = 'none'; }

    // Show processing animation
    const dropText = dropzone ? dropzone.querySelector('.payment-dropzone__text') : null;
    if (dropText) dropText.style.display = 'none';
    if (preview) preview.style.display = 'none';

    // Create processing overlay inside step 3
    let processingEl = document.getElementById('pay-processing');
    if (!processingEl) {
      processingEl = document.createElement('div');
      processingEl.id = 'pay-processing';
      processingEl.className = 'payment-processing';
      processingEl.innerHTML =
        '<div class="payment-spinner"></div>' +
        '<div class="payment-processing-text">Processing Payment...</div>' +
        '<div class="payment-processing-sub">Please wait while we verify your screenshot</div>';
      step3.insertBefore(processingEl, step3.firstChild.nextSibling);
    }
    processingEl.style.display = 'block';

    // Hide other step 3 content
    const step3Children = step3.children;
    for (let i = 0; i < step3Children.length; i++) {
      const el = step3Children[i];
      if (el !== processingEl && !el.classList.contains('payment-methods-title')) {
        el.dataset.prevDisplay = el.style.display;
        el.style.display = 'none';
      }
    }
    const step3Title = step3.querySelector('.payment-methods-title');
    if (step3Title) step3Title.textContent = 'Processing...';

    try {
      const fd = new FormData();
      fd.append('screenshot', chosenFile);
      fd.append('plan', chosenPlan);
      fd.append('method', chosenMethod);

      const resp = await fetch('/api/payment-screenshot', { method: 'POST', body: fd });
      if (resp.ok) {
        const data = await resp.json().catch(() => ({}));

        // Fake a short delay for the processing feel
        await new Promise(r => setTimeout(r, 2200));

        // Show success state
        processingEl.innerHTML =
          '<div class="payment-success-check">✓</div>' +
          '<div class="payment-processing-text">Payment Verified!</div>' +
          '<div class="payment-processing-sub">' +
            (data.grantedTier === 2
              ? 'Premium access has been unlocked. Enjoy 3,000+ videos!'
              : 'Tier 1 access has been unlocked. Enjoy 500+ videos!') +
          '</div>';
        processingEl.classList.add('success');
        if (step3Title) step3Title.textContent = 'Welcome!';

        // Close and reload after a moment
        setTimeout(() => { closePayment(); location.reload(); }, 2500);
      } else {
        const errText = await resp.text().catch(() => '');
        console.error('[payment] Server responded', resp.status, errText);
        showSubmitError(processingEl, step3Children, step3Title);
      }
    } catch (err) {
      console.error('[payment] Fetch error:', err);
      showSubmitError(processingEl, step3Children, step3Title);
    }
  }

  function showSubmitError(processingEl, step3Children, step3Title) {
    if (processingEl) {
      processingEl.innerHTML =
        '<div class="payment-success-check" style="color:#ff4d6d">✗</div>' +
        '<div class="payment-processing-text">Something went wrong</div>' +
        '<div class="payment-processing-sub">Please try again or contact support</div>';
    }
    if (step3Title) step3Title.textContent = 'Error';
    // Re-show elements after a moment
    setTimeout(() => {
      if (processingEl) processingEl.style.display = 'none';
      for (let i = 0; i < step3Children.length; i++) {
        const el = step3Children[i];
        if (el.dataset.prevDisplay !== undefined) {
          el.style.display = el.dataset.prevDisplay;
          delete el.dataset.prevDisplay;
        }
      }
      if (step3Title) step3Title.textContent = 'Complete Payment';
      if (submitBtn) { submitBtn.style.display = 'block'; submitBtn.disabled = false; submitBtn.textContent = 'Submit for Review'; }
    }, 2500);
  }

  if (submitBtn) {
    submitBtn.addEventListener('click', () => doSubmit());
  }
})();
