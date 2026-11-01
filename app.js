'use strict';
// Pokemon Prisma Edition - Web-Version (iPhone/Browser): Bild, Ton, Touch-Tasten, Controller, Spielstand.
// Die Spieldatei ist nicht Teil der Webseite: Sie wird einmalig ausgewaehlt, ihre Signatur geprueft
// (nur Pokemon Prisma laeuft) und dann wie der Spielstand nur auf diesem Geraet gespeichert (IndexedDB).

const FRAME_MS = 1000 / 59.7275;
const KEY = { A: 1, B: 2, SELECT: 4, START: 8, RIGHT: 16, LEFT: 32, UP: 64, DOWN: 128 };

// ---------------- Speicher auf dem Geraet ----------------
const DB = {
  db: null,
  open() {
    if (this.db) return Promise.resolve(this.db);
    return new Promise((res, rej) => {
      const r = indexedDB.open('prisma', 1);
      r.onupgradeneeded = () => r.result.createObjectStore('files');
      r.onsuccess = () => { this.db = r.result; res(this.db); };
      r.onerror = () => rej(r.error);
    });
  },
  async get(k) {
    const db = await this.open();
    return new Promise((res, rej) => {
      const r = db.transaction('files').objectStore('files').get(k);
      r.onsuccess = () => res(r.result || null); r.onerror = () => rej(r.error);
    });
  },
  async put(k, v) {
    const db = await this.open();
    return new Promise((res, rej) => {
      const t = db.transaction('files', 'readwrite'); t.objectStore('files').put(v, k);
      t.oncomplete = () => res(); t.onerror = () => rej(t.error);
    });
  },
};
if (navigator.storage && navigator.storage.persist) navigator.storage.persist().catch(() => {});

let saveCache = null;   // Uint8Array des zuletzt gespeicherten Spielstands
const Bridge = {
  loadSave() { return saveCache; },
  storeSave(bytes) { saveCache = bytes.slice(); DB.put('sav', saveCache).catch(() => toast('Speichern fehlgeschlagen!')); },
  async exportSave() {
    if (!saveCache) { toast('Noch kein Spielstand vorhanden.'); return; }
    const file = new File([saveCache], 'pokemon-prisma.sav', { type: 'application/octet-stream' });
    if (navigator.canShare && navigator.canShare({ files: [file] })) {
      try { await navigator.share({ files: [file], title: 'Pokémon Prisma Spielstand' }); return; } catch (e) { if (e.name === 'AbortError') return; }
    }
    const a = document.createElement('a');
    a.href = URL.createObjectURL(file); a.download = file.name; a.click();
    setTimeout(() => URL.revokeObjectURL(a.href), 5000);
  },
  importSave() { document.getElementById('file').click(); },
  vibrate(ms) { if (navigator.vibrate) navigator.vibrate(ms); },
  quit() {},
  isApp() { return false; },
};

// ---------------- Pruefung: nur Pokemon Prisma ----------------
// Jede Prisma-Spieldatei traegt am Ende eine Signatur (ECDSA P-256). Hier liegt nur der oeffentliche Schluessel.
const PRISMA_KEY = { kty: 'EC', crv: 'P-256', x: 'eb-NpigE1AL0i7inRcun8QHXuJSeBBa6cRPrx3aEh5Q', y: 'Lwqj_eU5YQW3QNg-xsEm5gkRt5q1y44VegiPkSD3DVg' };
const SIG_MAGIC = 'PRISMASIG1';
async function isPrisma(rom) {
  try {
    if (rom.length < 0x8000 || rom.length % 0x4000) return false;
    // Signatur am Dateiende, bei der Zeitreise-Datei (Kanto + Johto) am Ende der Kanto-Haelfte
    const both = rom.length >= 0x400000 && String.fromCharCode.apply(null, rom.subarray(0x200134, 0x20013e)) === 'PM_CRYSTAL';
    const at = both ? 0x200000 - 80 : rom.length - 80;
    const tail = rom.subarray(at, at + 80);
    if (String.fromCharCode.apply(null, tail.subarray(0, 10)) !== SIG_MAGIC) return false;
    const sig = tail.slice(16, 80);
    const msg = rom.slice(); msg.fill(0, at, at + 80); msg[0x14e] = 0; msg[0x14f] = 0;
    const key = await crypto.subtle.importKey('jwk', PRISMA_KEY, { name: 'ECDSA', namedCurve: 'P-256' }, false, ['verify']);
    return await crypto.subtle.verify({ name: 'ECDSA', hash: 'SHA-256' }, key, sig, msg);
  } catch (e) { return false; }
}

function b64ToBytes(s) {
  const bin = atob(s); const out = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
  return out;
}
function bytesToB64(bytes) {
  let s = '';
  for (let i = 0; i < bytes.length; i += 0x8000) s += String.fromCharCode.apply(null, bytes.subarray(i, i + 0x8000));
  return btoa(s);
}
let toastTimer = 0;
function toast(msg) {
  const t = document.getElementById('toast');
  t.textContent = msg; t.classList.add('show');
  clearTimeout(toastTimer); toastTimer = setTimeout(() => t.classList.remove('show'), 2200);
}

// ---------------- Emulator ----------------
let core, sramSize = 0;
function mem() { return core.memory.buffer; }
function sramView() { return new Uint8Array(mem(), core.wc_sram(), sramSize); }

// Spieldatei: gespeicherte nehmen oder einmalig auswaehlen lassen (immer mit Signaturpruefung)
function askRom(message) {
  const setup = document.getElementById('setup');
  document.getElementById('setupErr').textContent = message || '';
  setup.hidden = false;
  document.getElementById('hint').hidden = true;
  return new Promise((resolve) => {
    const input = document.getElementById('romFile');
    input.value = '';
    input.onchange = async () => {
      const f = input.files[0]; if (!f) return;
      const rom = new Uint8Array(await f.arrayBuffer());
      if (!(await isPrisma(rom))) {
        document.getElementById('setupErr').textContent = 'Dieser Emulator spielt ausschließlich Pokémon Prisma. Bitte wähle die Prisma-Spieldatei aus.';
        return;
      }
      await DB.put('rom', rom);
      setup.hidden = true;
      resolve(rom);
    };
  });
}
async function getRom() {
  let rom = null;
  try { rom = await DB.get('rom'); } catch (e) {}
  if (rom && await isPrisma(rom)) return rom;
  return askRom(rom ? 'Die gespeicherte Spieldatei ist ungültig. Bitte wähle sie erneut aus.' : '');
}

async function startCore() {
  const wasm = await (await fetch('core.wasm')).arrayBuffer();
  const { instance } = await WebAssembly.instantiate(wasm, {});
  core = instance.exports;
  core._initialize();
  const rom = await getRom();
  document.getElementById('hint').hidden = false;
  const p = core.wc_rom_alloc(rom.length);
  new Uint8Array(mem(), p, rom.length).set(rom);
  sramSize = core.wc_init();
  try { saveCache = await DB.get('sav'); } catch (e) { saveCache = null; }
  // auch alte, kleinere Spielstaende (32 KB Kanto) uebernehmen
  if (saveCache && saveCache.length) sramView().set(saveCache.subarray(0, Math.min(sramSize, saveCache.length)));
  setClock();
  if (core.wc_start() < 0) throw new Error('Spieldatei konnte nicht gestartet werden');
  core.wc_sram_dirty();
}
// Ortszeit fuer die Uhr in Johto (Kristall)
function setClock() {
  const now = new Date();
  core.wc_set_time(Math.floor(now.getTime() / 1000) - now.getTimezoneOffset() * 60);
}
let blockPersist = false;
function persist() {
  if (blockPersist) return;
  if (core && core.wc_sram_dirty()) Bridge.storeSave(sramView());
}

// ---------------- Bild ----------------
const canvas = document.getElementById('lcd');
const ctx2d = canvas.getContext('2d');
function draw() {
  core.wc_compose();
  const px = new Uint8ClampedArray(mem(), core.wc_screen(), 160 * 144 * 4);
  ctx2d.putImageData(new ImageData(px, 160, 144), 0, 0);
}

// ---------------- Ton ----------------
let actx = null, soundOn = true, volume = 100, volGain = 1 / 32768;
const RING = 32768;
const ringL = new Float32Array(RING), ringR = new Float32Array(RING);
let rw = 0, rr = 0, rfrac = 0, coreRate = 32768;
function ringLevel() { return (rw - rr + RING) % RING; }
function pushAudio() {
  if (!actx || !soundOn) return;
  const n = core.wc_audio_len();
  const a = new Int16Array(mem(), core.wc_audio(), n);
  for (let i = 0; i < n; i += 2) {
    if (ringLevel() >= RING - 2) break;
    ringL[rw] = a[i] * volGain; ringR[rw] = a[i + 1] * volGain;
    rw = (rw + 1) % RING;
  }
}
function startAudio() {
  if (actx) { if (actx.state !== 'running') actx.resume(); return; }
  const AC = window.AudioContext || window.webkitAudioContext;
  if (!AC) return;
  try { actx = new AC({ sampleRate: coreRate, latencyHint: 'interactive' }); } catch (e) { actx = new AC(); }
  const node = actx.createScriptProcessor(2048, 0, 2);
  node.onaudioprocess = (ev) => {
    const L = ev.outputBuffer.getChannelData(0), R = ev.outputBuffer.getChannelData(1);
    const step = coreRate / actx.sampleRate;
    for (let i = 0; i < L.length; i++) {
      if (ringLevel() < 2) { L[i] = R[i] = 0; continue; }
      L[i] = ringL[rr]; R[i] = ringR[rr];
      rfrac += step;
      while (rfrac >= 1) { rfrac -= 1; if (ringLevel() > 1) rr = (rr + 1) % RING; }
    }
  };
  node.connect(actx.destination);
}

// ---------------- Eingabe ----------------
let touchBits = 0, keyBits = 0, padBits = 0, axisBits = 0;
function buttons() { return touchBits | keyBits | padBits | axisBits; }

const els = {
  A: document.getElementById('btnA'), B: document.getElementById('btnB'),
  SELECT: document.getElementById('btnSel'), START: document.getElementById('btnStart'),
};
const dpad = document.getElementById('dpad');
const hl = { UP: 'hlU', DOWN: 'hlD', LEFT: 'hlL', RIGHT: 'hlR' };
function inRect(r, x, y, m) { return x >= r.left - m && x <= r.right + m && y >= r.top - m && y <= r.bottom + m; }

function updateTouches(e) {
  if (!document.getElementById('menu').hidden) return;
  let bits = 0;
  const d = dpad.getBoundingClientRect();
  const cx = d.left + d.width / 2, cy = d.top + d.height / 2, r = d.width / 2;
  for (const t of e.touches) {
    const x = t.clientX, y = t.clientY;
    const dx = x - cx, dy = y - cy;
    if (Math.abs(dx) < r * 1.35 && Math.abs(dy) < r * 1.35) {
      const dead = r * 0.22;
      if (dx > dead && Math.abs(dx) > Math.abs(dy) * 0.45) bits |= KEY.RIGHT;
      if (dx < -dead && Math.abs(dx) > Math.abs(dy) * 0.45) bits |= KEY.LEFT;
      if (dy < -dead && Math.abs(dy) > Math.abs(dx) * 0.45) bits |= KEY.UP;
      if (dy > dead && Math.abs(dy) > Math.abs(dx) * 0.45) bits |= KEY.DOWN;
      continue;
    }
    for (const k of ['A', 'B', 'SELECT', 'START']) {
      const rect = els[k].getBoundingClientRect();
      const m = k === 'A' || k === 'B' ? rect.width * 0.25 : 10;
      if (inRect(rect, x, y, m)) { bits |= KEY[k]; break; }
    }
  }
  if (bits & ~touchBits) Bridge.vibrate(12);
  touchBits = bits;
  for (const k of ['A', 'B', 'SELECT', 'START']) els[k].classList.toggle('on', !!(bits & KEY[k]));
  for (const k in hl) document.getElementById(hl[k]).classList.toggle('on', !!(bits & KEY[k]));
}
for (const ev of ['touchstart', 'touchmove', 'touchend', 'touchcancel']) {
  document.addEventListener(ev, (e) => {
    startAudio();
    if (e.target.closest && (e.target.closest('#menu') || e.target.closest('#menuBtn') || e.target.closest('#setup'))) return;
    e.preventDefault();
    updateTouches(e);
  }, { passive: false });
}

const keyMap = {
  ArrowUp: 'UP', ArrowDown: 'DOWN', ArrowLeft: 'LEFT', ArrowRight: 'RIGHT', w: 'UP', s: 'DOWN', a: 'LEFT', d: 'RIGHT',
  x: 'A', k: 'A', ' ': 'A', y: 'B', z: 'B', l: 'B', Enter: 'START', Backspace: 'SELECT', Shift: 'SELECT',
};
document.addEventListener('keydown', (e) => {
  startAudio();
  if (e.key === 'Escape') { toggleMenu(); return; }
  const k = keyMap[e.key] || keyMap[e.key.toLowerCase()];
  if (k) { keyBits |= KEY[k]; e.preventDefault(); }
});
document.addEventListener('keyup', (e) => {
  const k = keyMap[e.key] || keyMap[e.key.toLowerCase()];
  if (k) keyBits &= ~KEY[k];
});

// Controller: von Java weitergereicht (Android) - Namen wie in KEY
window.padKey = (name, down) => {
  startAudio();
  if (name === 'MENU') { if (down) toggleMenu(); return; }
  if (!document.getElementById('menu').hidden) {
    if (down && (name === 'B' || name === 'A')) closeMenu();
    return;
  }
  if (down) padBits |= KEY[name]; else padBits &= ~KEY[name];
};
window.padAxis = (x, y) => {
  let b = 0;
  if (x > 0.5) b |= KEY.RIGHT; if (x < -0.5) b |= KEY.LEFT;
  if (y > 0.5) b |= KEY.DOWN; if (y < -0.5) b |= KEY.UP;
  axisBits = b;
};

// ---------------- Menue ----------------
const menu = document.getElementById('menu');
let paused = false;
function openMenu() { menu.hidden = false; paused = true; touchBits = 0; persist(); }
function closeMenu() { menu.hidden = true; paused = false; last = performance.now(); }
function toggleMenu() { if (menu.hidden) openMenu(); else closeMenu(); }
window.toggleMenu = toggleMenu;
document.getElementById('menuBtn').addEventListener('click', () => { startAudio(); openMenu(); });
document.getElementById('mResume').addEventListener('click', closeMenu);
// Einstellungen wie im Pause-Menue der PC-Version (Lautstaerke, Helligkeit, Grafik, Tempo, Neustart)
let brightness = 100, smooth = false, speed = 1;
function loadSetting(k, d) { try { const v = localStorage.getItem('prisma-' + k); return v === null ? d : +v; } catch (e) { return d; } }
function saveSetting(k, v) { try { localStorage.setItem('prisma-' + k, String(v)); } catch (e) {} }
function applySettings() {
  soundOn = volume > 0; volGain = volume / 100 / 32768;
  canvas.style.filter = brightness === 100 ? '' : 'brightness(' + brightness / 100 + ')';
  canvas.style.imageRendering = smooth ? 'auto' : 'pixelated';
  document.getElementById('mVolume').textContent = 'Lautstärke: ' + (volume ? volume + ' %' : 'aus');
  document.getElementById('mBright').textContent = 'Helligkeit: ' + brightness + ' %';
  document.getElementById('mGfx').textContent = 'Grafik: ' + (smooth ? 'weich' : 'scharf');
  document.getElementById('mSpeed').textContent = 'Tempo: ' + speed + 'x';
}
document.getElementById('mVolume').addEventListener('click', () => {
  volume = volume >= 100 ? 0 : volume + 10; saveSetting('volume', volume); applySettings();
  if (soundOn) startAudio();
});
document.getElementById('mBright').addEventListener('click', () => {
  brightness = brightness >= 150 ? 50 : brightness + 10; saveSetting('bright', brightness); applySettings();
});
document.getElementById('mGfx').addEventListener('click', () => { smooth = !smooth; saveSetting('smooth', smooth ? 1 : 0); applySettings(); });
document.getElementById('mSpeed').addEventListener('click', () => { speed = speed >= 4 ? 1 : speed + 1; saveSetting('speed', speed); applySettings(); });
document.getElementById('mReset').addEventListener('click', () => {
  if (!confirm('Spiel neu starten? Was seit dem letzten SICHERN im Spiel passiert ist, geht verloren.')) return;
  persist(); core.wc_reset(); rw = rr = 0; closeMenu();
});
document.getElementById('mExport').addEventListener('click', () => { persist(); Bridge.exportSave(); });
document.getElementById('mImport').addEventListener('click', () => {
  if (confirm('Der aktuelle Spielstand in der App wird ersetzt. Vorher exportieren, falls du ihn behalten willst. Fortfahren?')) Bridge.importSave();
});
document.getElementById('mQuit').addEventListener('click', () => { persist(); Bridge.quit(); });
document.getElementById('mRom').addEventListener('click', async () => {
  if (!confirm('Neue Prisma-Spieldatei laden (zum Beispiel ein Update)? Dein Spielstand bleibt erhalten.')) return;
  persist();
  const input = document.getElementById('romFile');
  input.value = '';
  input.onchange = async () => {
    const f = input.files[0]; if (!f) return;
    const rom = new Uint8Array(await f.arrayBuffer());
    if (!(await isPrisma(rom))) { toast('Dieser Emulator spielt ausschließlich Pokémon Prisma.'); return; }
    await DB.put('rom', rom);
    blockPersist = true; location.reload();
  };
  input.click();
});
document.getElementById('file').addEventListener('change', async (e) => {
  const f = e.target.files[0]; if (!f) return;
  const b = new Uint8Array(await f.arrayBuffer());
  if (b.length < 32768 || b.length > 262144) { toast('Das ist kein passender Spielstand (.sav).'); return; }
  await DB.put('sav', b.slice(0, Math.max(sramSize, 32768)));   // alter Kanto-Spielstand (32 KB) passt auch
  blockPersist = true; location.reload();
});
volume = loadSetting('volume', loadSetting('sound', 1) ? 100 : 0);   // alte Einstellung "Ton aus" uebernehmen
brightness = loadSetting('bright', 100); smooth = !!loadSetting('smooth', 0); speed = loadSetting('speed', 1);
applySettings();

// App in den Hintergrund: anhalten und sichern
window.appPause = () => { persist(); if (actx) actx.suspend(); };
window.appResume = () => { last = performance.now(); if (actx && soundOn) actx.resume(); };
document.addEventListener('visibilitychange', () => { if (document.hidden) window.appPause(); else window.appResume(); });
window.onImported = (ok) => { if (ok) { blockPersist = true; location.reload(); return; } toast('Das ist kein passender Spielstand (.sav, 32 KB).'); };
window.onExported = (ok) => toast(ok ? 'Spielstand exportiert.' : 'Export abgebrochen.');

// ---------------- Hauptschleife ----------------
let last = performance.now(), acc = 0;
function step() {
  for (let i = 0; i < speed; i++) { core.wc_frame(buttons()); if (i === 0) pushAudio(); }   // schneller: Ton nur vom ersten Bild
}
function tick(now) {
  let dt = now - last; last = now;
  if (dt > 250 || dt < 0) dt = FRAME_MS;
  if (!paused && !document.hidden) {
    // Ton-Puffer haelt die Geschwindigkeit ruhig: etwas schneller, wenn er leer laeuft
    let rate = 1;
    if (actx && soundOn && actx.state === 'running') {
      const lvl = ringLevel() / (coreRate / 59.7275);
      if (lvl < 2) rate = 1.02; else if (lvl > 6) rate = 0.98;
    }
    acc += dt * rate;
    let n = 0;
    while (acc >= FRAME_MS && n < 4) { step(); acc -= FRAME_MS; n++; }
    if (acc > FRAME_MS * 4) acc = 0;
    if (n) draw();
  }
  requestAnimationFrame(tick);
}

if ('serviceWorker' in navigator) navigator.serviceWorker.register('sw.js').catch(() => {});
document.addEventListener('pagehide', () => persist());
startCore().then(() => {
  document.getElementById('hint').remove();
  setInterval(persist, 1000);
  draw();
  requestAnimationFrame(tick);
}).catch((err) => {
  document.getElementById('hint').textContent = 'Fehler beim Start: ' + err;
});
