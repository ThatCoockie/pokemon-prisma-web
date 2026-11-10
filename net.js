// Prisma: Mitspielen ohne eigenen Server (WebRTC). Jeder hat einen festen Freundes-Code; Freunde sehen sich in der
// Freundesliste, einer eroeffnet als Host eine Runde, die anderen treten mit einem Tipp bei. Die Geraete finden sich ueber
// einen kostenlosen oeffentlichen Vermittlungsdienst (verschluesselt); STUN hilft beim Verbinden. Danach laufen die Daten
// direkt zwischen den Spielern. Notloesung ohne Vermittlung: Codes per Hand tauschen. Der Host verteilt Liste und Chat.
// Gemeinsam fuer Web-App und Android (gleiche Datei). Spielstaende werden nie verschickt.
(function () {
  'use strict';
  const PROTO = 1;                                   // Protokoll-Version (bei Aenderungen erhoehen)
  const ICE = [{ urls: 'stun:stun.l.google.com:19302' }];
  const MAX_PLAYERS = 8;
  const MAX_MSG = 2048, MAX_TEXT = 200, MAX_NAME = 12;
  const CODE_PREFIX = 'PRISMA1:';

  let gameId = '';                                   // Kennung der Spieldatei (nur gleiche Version spielt zusammen)
  let role = null;                                   // null | 'host' | 'guest'
  let myName = cleanName(loadName());
  const peers = new Map();                           // Host: id -> { pc, dc, name }
  let nextId = 1;
  let pending = null;                                // Host: Einladung, auf deren Antwort-Code gewartet wird
  let guest = null;                                  // Gast: { pc, dc }
  let players = [];                                  // [{ id, name }] wie vom Host verteilt
  const chatLog = [];

  // ---------------- Mitspieler in der Welt ----------------
  // Jeder liest seine Position aus dem Spiel und schickt sie ~10x pro Sekunde. Andere Spieler auf derselben Karte zeichnet
  // der Emulator ueber das Bild: keine echte Spielfigur, daher keine Kollision; die ROM bleibt unberuehrt.
  // Adressen (deutsche ROMs, am Code geprueft): Gelb = Englisch + 5 ($d05b Kampf, $cfc8 Schrift geladen, $d362 Karte,
  // $d365/$d366 Y/X, $c1xx Spielerfigur, $d726 Bit 0 Maedchen); Kristall = Englisch ($d22d Kampf, $d0ed Bit 6 Text/Menue,
  // $dcb5/$dcb6 Karte, $dcb7/$dcb8 Y/X, $d4d6 Spielerfigur, $d472 Bit 0 Maedchen).
  const RAM = [
    { map: (p) => p(0xd362), tx: 0xd366, ty: 0xd365, here: (p) => p(0xc100) !== 0,
      hide: (p) => p(0xd05b) !== 0 || (p(0xcfc8) & 1) !== 0,
      face: (p) => (p(0xc109) >> 2) & 3, girl: (p) => p(0xd726) & 1, sx: (p) => p(0xc106), sy: (p) => p(0xc104),
      mode: (p) => Math.min(p(0xd704), 2) },                          // wWalkBikeSurfState: 0 laufen, 1 Rad, 2 surfen
    { map: (p) => p(0xdcb5) * 256 + p(0xdcb6), tx: 0xdcb8, ty: 0xdcb7, here: (p) => p(0xd4d6) !== 0,
      hide: (p) => p(0xd22d) !== 0 || (p(0xd0ed) & 0x40) !== 0,
      face: (p) => (p(0xd4de) >> 2) & 3, girl: (p) => p(0xd472) & 1, sx: (p) => p(0xd4ed), sy: (p) => (p(0xd4ee) - 4) & 255,
      mode: (p) => { const v = p(0xd95d); return v & 0x0c ? 2 : v & 0x03 ? 1 : 0; } },   // wPlayerState: 1 Rad, 2 Rollschuh, 4/8 surfen
  ];
  // Figuren aus der eigenen Spieldatei (keine Spielgrafik in dieser Datei): je 6 Bilder 16x16 (unten, oben, links, dann laufend).
  // Container-Offsets [Region][laufen, Rad, surfen][Junge, Maedchen]. Gelb: Rot 05:4571, Rad 05:43f1, Seel 05:7ab1;
  // Prisma-Maedchen 3d:704f (Rad) / 3d:71cf (laufen). Kristall (+2 MB): Chris 30:4000/30:4180, Kris 31:7a40/31:7bc0,
  // Surfen 31:7200. Alle in Englisch und Deutsch gleich (geprueft). Bei Umbau von girl.asm den Maedchen-Offset pruefen!
  const SHEETS = [[[0x014571, 0x0f71cf], [0x0143f1, 0x0f704f], [0x017ab1, 0x017ab1]],
                  [[0x2c0000, 0x2c7a40], [0x2c0180, 0x2c7bc0], [0x2c7200, 0x2c7200]]];
  const SKIN = [248, 200, 160], DARK = [32, 32, 40];
  const PALS = [[[SKIN, [224, 72, 64], DARK], [SKIN, [224, 104, 168], DARK]], [[SKIN, [232, 64, 48], DARK], [SKIN, [64, 120, 232], DARK]]];
  const SURF_PAL = [[232, 240, 248], [96, 144, 216], DARK];
  let core = null, sheets = null, labels = null;
  const ghosts = new Map();                          // id -> { r, m, x, y, f, g, h, dx, dy, dist, moving, seen }
  const own = { region: -1, map: -1, accX: 0, accY: 0, offX: 0, offY: 0, synced: false, scx: 0, scy: 0, tx: -1, ty: -1,
    still: 0, wait: 0, wx: 0, wy: 0, scrX: 64, scrY: 60, face: 0, girl: 0, mode: 0, here: false, hidden: true, sendT: 0 };

  function decodeSheet(v, off) {
    if (off + 0x180 > v.length) return null;
    const out = new Uint8Array(6 * 256);
    for (let f = 0; f < 6; f++) for (let t = 0; t < 4; t++) {
      const b = off + f * 64 + t * 16, x0 = (t & 1) * 8, y0 = (t >> 1) * 8;   // Reihenfolge oben-links, oben-rechts, unten-links, unten-rechts
      for (let r = 0; r < 8; r++) {
        const lo = v[b + 2 * r], hi = v[b + 2 * r + 1];
        for (let x = 0; x < 8; x++) out[f * 256 + (y0 + r) * 16 + x0 + x] = (((hi >> (7 - x)) & 1) << 1) | ((lo >> (7 - x)) & 1);
      }
    }
    return out;
  }
  function attach(c, mem, ptr, len) {                // nach wc_init: ROM ist entpackt
    core = c;
    const v = new Uint8Array(mem(), ptr, len);
    gameId = v[0x14e].toString(16).padStart(2, '0') + v[0x14f].toString(16).padStart(2, '0');
    sheets = SHEETS.map((r) => r.map((m) => m.map((off) => decodeSheet(v, off))));
  }
  // Eigene Position in Pixeln: Feld x 16 plus Feinanteil aus dem Bild-Scrollen (SCX/SCY). Steht der Spieler still, wird
  // beides exakt abgeglichen; bei Spruengen (Tuer, Kartenwechsel) bleiben die Mitspieler aus, bis er einmal stillsteht.
  function tick() {
    if (!core || typeof core.wc_peek !== 'function') return;
    const p = core.wc_peek, region = core.wc_active_game() ? 1 : 0, R = RAM[region];
    const map = R.map(p), tx = p(R.tx), ty = p(R.ty), scx = p(0xff43), scy = p(0xff42);
    if (region !== own.region || map !== own.map) { own.region = region; own.map = map; own.synced = false; own.wait = 30; }
    let dx = ((scx - own.scx + 128) & 255) - 128, dy = ((scy - own.scy + 128) & 255) - 128;
    own.scx = scx; own.scy = scy;
    if (Math.abs(dx) > 20 || Math.abs(dy) > 20) { own.synced = false; dx = 0; dy = 0; }
    own.accX += dx; own.accY += dy;
    own.still = (dx || dy || tx !== own.tx || ty !== own.ty) ? 0 : own.still + 1;
    own.tx = tx; own.ty = ty;
    own.here = R.here(p); own.hidden = R.hide(p);
    if (own.wait > 0) own.wait--;
    if (own.still >= 2 && own.here && !own.hidden) {
      own.offX = tx * 16 - own.accX; own.offY = ty * 16 - own.accY; own.synced = true;
      own.scrX = R.sx(p); own.scrY = R.sy(p);
    }
    let wx = own.accX + own.offX, wy = own.accY + own.offY;
    if (!own.synced || Math.abs(wx - tx * 16) > 20 || Math.abs(wy - ty * 16) > 20) { own.synced = false; wx = tx * 16; wy = ty * 16; }
    own.wx = wx; own.wy = wy; own.face = R.face(p); own.girl = R.girl(p); own.mode = R.mode(p);
    if (role && ++own.sendT >= 6) { own.sendT = 0; sendPos(); }
    for (const g of ghosts.values()) {               // Mitspieler weich nachziehen (Daten kommen ~10x pro Sekunde)
      const ex = g.x - g.dx, ey = g.y - g.dy;
      if (Math.abs(ex) > 48 || Math.abs(ey) > 48) { g.dx = g.x; g.dy = g.y; g.moving = false; continue; }
      const mx = Math.sign(ex) * Math.min(Math.abs(ex), Math.max(1, Math.ceil(Math.abs(ex) / 4)));
      const my = Math.sign(ey) * Math.min(Math.abs(ey), Math.max(1, Math.ceil(Math.abs(ey) / 4)));
      g.dx += mx; g.dy += my; g.dist += Math.abs(mx) + Math.abs(my); g.moving = mx !== 0 || my !== 0;
    }
  }
  function sendPos() {
    const m = { t: 'pos', r: own.region, m: own.map, x: own.wx, y: own.wy, f: own.face, g: own.girl, v: own.mode, h: own.here ? 0 : 1 };
    if (role === 'host') { m.id = 0; for (const pp of peers.values()) send(pp.dc, m); }
    else if (connectedGuest()) send(guest.dc, m);
  }
  function cleanPos(o) {
    const n = (v, lo, hi) => Number.isInteger(v) && v >= lo && v <= hi;
    if (!n(o.r, 0, 1) || !n(o.m, 0, 65535) || !n(o.x, -32768, 32767) || !n(o.y, -32768, 32767) || !n(o.f, 0, 3)) return null;
    return { r: o.r, m: o.m, x: o.x, y: o.y, f: o.f, g: o.g ? 1 : 0, v: n(o.v, 0, 2) ? o.v : 0, h: o.h ? 1 : 0 };
  }
  function onPos(id, q) {
    if (!q) return;
    let g = ghosts.get(id);
    if (!g || g.r !== q.r || g.m !== q.m) { g = { dx: q.x, dy: q.y, dist: 0, moving: false }; ghosts.set(id, g); }
    Object.assign(g, q, { seen: performance.now() });
  }
  function nameOf(id) { const p = players.find((x) => x.id === id); return p ? p.name : ''; }
  function draw(px) {
    let used = 0;
    const show = core && sheets && role !== null && own.synced && own.here && !own.hidden && own.wait === 0 &&
      document.getElementById('menu').hidden;
    if (show && ghosts.size) {
      const now = performance.now(), rect = document.getElementById('lcd').getBoundingClientRect();
      for (const [id, g] of ghosts) {
        if (g.h || g.r !== own.region || g.m !== own.map || now - g.seen > 3000) continue;
        const sx = Math.round(own.scrX + g.dx - own.wx), sy = Math.round(own.scrY + g.dy - own.wy);
        if (sx <= -16 || sx >= 160 || sy <= -16 || sy >= 144) continue;
        blit(px, g, sx, sy);
        label(used++, nameOf(id), sx, sy, rect);
      }
    }
    if (labels) for (let i = used; i < labels.children.length; i++) labels.children[i].hidden = true;
  }
  function blit(px, g, sx, sy) {
    const sheet = sheets[g.r][g.v][g.g];
    if (!sheet) return;
    const pal = g.v === 2 ? SURF_PAL : PALS[g.r][g.g], ph = g.moving ? Math.floor(g.dist / 8) % 4 : 0;
    let frame, flip;
    if (g.f < 2) { frame = (ph & 1) ? 3 + g.f : g.f; flip = ph === 3; }   // unten/oben: Schritt, Stand, Schritt gespiegelt
    else { frame = (ph & 1) ? 5 : 2; flip = g.f === 3; }                  // rechts = links gespiegelt
    const base = frame * 256;
    for (let y = 0; y < 16; y++) {
      const py = sy + y;
      if (py < 0 || py >= 144) continue;
      for (let x = 0; x < 16; x++) {
        const qx = sx + x;
        if (qx < 0 || qx >= 160) continue;
        const c = sheet[base + y * 16 + (flip ? 15 - x : x)];
        if (!c) continue;
        const col = pal[c - 1], i = (py * 160 + qx) * 4;
        px[i] = col[0]; px[i + 1] = col[1]; px[i + 2] = col[2]; px[i + 3] = 255;
      }
    }
  }
  function label(i, name, sx, sy, rect) {
    if (!labels) {
      labels = document.createElement('div');
      labels.style.cssText = 'position:fixed;inset:0;pointer-events:none;z-index:5';
      document.body.appendChild(labels);
    }
    while (labels.children.length <= i) {
      const d = document.createElement('div');
      d.style.cssText = 'position:absolute;transform:translate(-50%,-100%);font:bold 11px system-ui;color:#fff;' +
        'text-shadow:0 0 3px #000,0 0 2px #000;white-space:nowrap';
      labels.appendChild(d);
    }
    const d = labels.children[i];
    d.hidden = false;
    if (d.textContent !== name) d.textContent = name;
    d.style.left = (rect.left + (sx + 8) * rect.width / 160) + 'px';
    d.style.top = (rect.top + (sy - 1) * rect.height / 144) + 'px';
  }

  // ---------------- Hilfen ----------------
  function say(msg) { if (typeof window.toast === 'function') window.toast(msg); }
  function loadName() { try { return (localStorage.getItem('prisma-netname') || '').slice(0, MAX_NAME); } catch (e) { return ''; } }
  function saveName(n) { try { localStorage.setItem('prisma-netname', n); } catch (e) {} }
  function cleanName(n) { return String(n || '').replace(/[\u0000-\u001f\u007f]/g, '').trim().slice(0, MAX_NAME) || 'Spieler'; }
  function cleanText(t) { return String(t || '').replace(/[\u0000-\u001f\u007f]/g, ' ').trim().slice(0, MAX_TEXT); }

  function b64u(bytes) {
    let s = '';
    for (let i = 0; i < bytes.length; i += 0x8000) s += String.fromCharCode.apply(null, bytes.subarray(i, i + 0x8000));
    return btoa(s).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
  }
  function unb64u(s) {
    const b = atob(s.replace(/-/g, '+').replace(/_/g, '/') + '==='.slice((s.length + 3) % 4));
    const out = new Uint8Array(b.length);
    for (let i = 0; i < b.length; i++) out[i] = b.charCodeAt(i);
    return out;
  }
  async function deflate(bytes, inflate) {
    const t = inflate ? new DecompressionStream('deflate-raw') : new CompressionStream('deflate-raw');
    return new Uint8Array(await new Response(new Blob([bytes]).stream().pipeThrough(t)).arrayBuffer());
  }
  // Verbindungsbeschreibung (SDP) -> kurzer Code zum Kopieren und zurueck
  async function pack(desc) {
    const raw = new TextEncoder().encode(JSON.stringify({ t: desc.type, s: desc.sdp, g: gameId, v: PROTO }));
    if (typeof CompressionStream === 'function') return CODE_PREFIX + 'z' + b64u(await deflate(raw, false));
    return CODE_PREFIX + 'r' + b64u(raw);
  }
  async function unpack(code) {
    code = String(code || '').replace(/\s+/g, '');
    if (!code.startsWith(CODE_PREFIX)) throw new Error('Das ist kein Prisma-Code.');
    const kind = code[CODE_PREFIX.length], body = unb64u(code.slice(CODE_PREFIX.length + 1));
    if (kind === 'z' && typeof DecompressionStream !== 'function') throw new Error('Dieses Gerät ist zu alt für Prisma-Codes.');
    const raw = kind === 'z' ? await deflate(body, true) : body;
    const o = JSON.parse(new TextDecoder().decode(raw));
    if (o.v !== PROTO) throw new Error('Andere Prisma-Version beim Freund (Protokoll).');
    if (o.g !== gameId) throw new Error('Andere Spielversion beim Freund. Bitte beide dieselbe Version nutzen.');
    if ((o.t !== 'offer' && o.t !== 'answer') || typeof o.s !== 'string') throw new Error('Code ist beschaedigt.');
    return { type: o.t, sdp: o.s };
  }
  function waitIce(pc) {                             // alle Adressen sammeln (inkl. STUN), dann erst den Code bauen
    return new Promise((resolve) => {
      if (pc.iceGatheringState === 'complete') return resolve();
      const done = () => { if (pc.iceGatheringState === 'complete') { pc.removeEventListener('icegatheringstatechange', done); resolve(); } };
      pc.addEventListener('icegatheringstatechange', done);
      setTimeout(resolve, 5000);
    });
  }
  function send(dc, obj) { if (dc && dc.readyState === 'open') dc.send(JSON.stringify(obj)); }
  function parse(data) {
    if (typeof data !== 'string' || data.length > MAX_MSG) return null;
    try { const o = JSON.parse(data); return o && typeof o === 'object' && typeof o.t === 'string' ? o : null; } catch (e) { return null; }
  }

  // ---------------- Vermittlung (automatisch, ohne eigenen Server) ----------------
  // Treffpunkt: kostenloser oeffentlicher MQTT-Dienst (HiveMQ, WebSocket). Darueber laufen nur Online-Status und die
  // Verbindungsbeschreibungen, verschluesselt mit AES-GCM; Schluessel und Themen werden aus dem Freundes-Code abgeleitet,
  // der Dienst sieht nur Datensalat. Gleiches Verfahren in der PC-Exe (prisma_net.c). Kleines eigenes MQTT 3.1.1 (QoS 0).
  const BROKER = 'wss://broker.hivemq.com:8884/mqtt';
  const ALPHA = '23456789ABCDEFGHJKMNPQRSTUVWXYZ';  // ohne 0/O, 1/I/L
  const enc8 = new TextEncoder(), dec8 = new TextDecoder();
  let myCode = loadCode();
  let friends = loadFriends();                       // [{ code, name, online, host, g }]
  let mq = null, mqUp = false, mqPid = 1, mqPing = null, mqTimer = null, mqDelay = 3000;
  const tids = new Map(), keys = new Map();
  const pendingByCode = new Map();                   // Host: Freundes-Code -> { pc, dc } (wartet auf Antwort)
  let joinTarget = null;                             // Gast: Code des Hosts, bei dem wir beitreten

  function loadCode() {
    let c = '';
    try { c = localStorage.getItem('prisma-code') || ''; } catch (e) {}
    if (!/^[2-9A-HJKMNP-Z]{8}$/.test(c)) {
      const r = new Uint8Array(8);
      crypto.getRandomValues(r);
      c = Array.from(r, (b) => ALPHA[b % ALPHA.length]).join('');
      try { localStorage.setItem('prisma-code', c); } catch (e) {}
    }
    return c;
  }
  function loadFriends() {
    try {
      const a = JSON.parse(localStorage.getItem('prisma-friends') || '[]');
      return Array.isArray(a) ? a.filter((f) => f && /^[2-9A-HJKMNP-Z]{8}$/.test(f.code)).slice(0, 50)
        .map((f) => ({ code: f.code, name: cleanName(f.name), online: false, host: false, g: '' })) : [];
    } catch (e) { return []; }
  }
  function saveFriends() {
    try { localStorage.setItem('prisma-friends', JSON.stringify(friends.map((f) => ({ code: f.code, name: f.name })))); } catch (e) {}
  }
  function normCode(s) {
    const c = String(s || '').toUpperCase().replace(/O/g, '0').split('').filter((ch) => ALPHA.includes(ch)).join('');
    return c.length === 8 ? c : '';
  }
  function showCode(c) { return c.slice(0, 4) + '-' + c.slice(4); }
  function friendOf(code) { return friends.find((f) => f.code === code); }
  async function sha(str) { return new Uint8Array(await crypto.subtle.digest('SHA-256', enc8.encode(str))); }
  async function tid(code) {
    if (!tids.has(code)) tids.set(code, Array.from((await sha('prisma-topic:' + code)).slice(0, 12), (b) => b.toString(16).padStart(2, '0')).join(''));
    return tids.get(code);
  }
  async function aes(code) {
    if (!keys.has(code)) keys.set(code, await crypto.subtle.importKey('raw', await sha('prisma-key:' + code), 'AES-GCM', false, ['encrypt', 'decrypt']));
    return keys.get(code);
  }
  async function seal(code, obj) {
    const iv = crypto.getRandomValues(new Uint8Array(12));
    const ct = new Uint8Array(await crypto.subtle.encrypt({ name: 'AES-GCM', iv }, await aes(code), enc8.encode(JSON.stringify(obj))));
    const out = new Uint8Array(12 + ct.length);
    out.set(iv); out.set(ct, 12);
    return out;
  }
  async function unseal(code, data) {
    if (data.length < 28 || data.length > 20000) return null;
    try {
      const pt = await crypto.subtle.decrypt({ name: 'AES-GCM', iv: data.slice(0, 12) }, await aes(code), data.slice(12));
      const o = JSON.parse(dec8.decode(pt));
      return o && typeof o === 'object' && typeof o.t === 'string' ? o : null;
    } catch (e) { return null; }
  }
  const pTopic = async (code) => 'prisma1/p/' + await tid(code);
  const iTopic = async (code) => 'prisma1/i/' + await tid(code);

  // MQTT 3.1.1, nur was gebraucht wird: CONNECT (mit Testament = offline), SUBSCRIBE, PUBLISH QoS 0, PING
  function mStr(s) { const b = enc8.encode(s); return [b.length >> 8, b.length & 255, ...b]; }
  function mPacket(type, body) {
    const len = []; let n = body.length;
    do { let d = n % 128; n = Math.floor(n / 128); if (n) d |= 128; len.push(d); } while (n);
    const out = new Uint8Array(1 + len.length + body.length);
    out[0] = type; out.set(len, 1); out.set(body, 1 + len.length);
    return out;
  }
  function mSend(type, body) { if (mq && mq.readyState === 1) mq.send(mPacket(type, body)); }
  async function mPublish(topic, payload, retain) { mSend(0x30 | (retain ? 1 : 0), [...mStr(topic), ...payload]); }
  async function mSubscribe(topic) { const id = mqPid++ & 0xffff || 1; mSend(0x82, [id >> 8, id & 255, ...mStr(topic), 0]); }
  function netWanted() { try { return localStorage.getItem('prisma-net-on') === '1'; } catch (e) { return false; } }
  function mqConnect() {
    if (mq || !netWanted() || !crypto.subtle || typeof WebSocket !== 'function') return;
    let ws, buf = new Uint8Array(0);
    try { ws = new WebSocket(BROKER, 'mqtt'); } catch (e) { mqRetry(); return; }
    ws.binaryType = 'arraybuffer';
    mq = ws;
    ws.onopen = async () => {
      const cid = 'prisma-' + Array.from(crypto.getRandomValues(new Uint8Array(6)), (b) => b.toString(16).padStart(2, '0')).join('');
      // Saubere Sitzung, Testament: leere, gemerkte Online-Meldung (= offline), Lebenszeichen alle 60 s
      mSend(0x10, [...mStr('MQTT'), 4, 0x02 | 0x04 | 0x20, 0, 60, ...mStr(cid), ...mStr(await pTopic(myCode)), 0, 0]);
    };
    ws.onmessage = (ev) => {
      const add = new Uint8Array(ev.data), nb = new Uint8Array(buf.length + add.length);
      nb.set(buf); nb.set(add, buf.length); buf = nb;
      for (;;) {
        if (buf.length < 2) break;
        let rl = 0, mul = 1, i = 1;
        for (; i < 5 && i < buf.length; i++) { rl += (buf[i] & 127) * mul; mul *= 128; if (!(buf[i] & 128)) break; }
        if (i >= buf.length || (buf[i] & 128)) break;
        const total = i + 1 + rl;
        if (buf.length < total) break;
        mHandle(buf[0], buf.slice(i + 1, total));
        buf = buf.slice(total);
      }
    };
    ws.onclose = () => {
      if (mq === ws) { mq = null; mqUp = false; }
      clearInterval(mqPing); mqPing = null;
      for (const f of friends) { f.online = false; f.host = false; }
      render();
      mqRetry();
    };
    ws.onerror = () => {};
  }
  function mqRetry() {
    clearTimeout(mqTimer);
    mqTimer = setTimeout(mqConnect, mqDelay);
    mqDelay = Math.min(mqDelay * 2, 60000);
  }
  async function mHandle(type, body) {
    const kind = type >> 4;
    if (kind === 2) {                                // CONNACK
      if (body[1] !== 0) { try { mq.close(); } catch (e) {} return; }
      mqUp = true; mqDelay = 3000;
      clearInterval(mqPing); mqPing = setInterval(() => mSend(0xc0, []), 30000);
      await mSubscribe(await iTopic(myCode));
      for (const f of friends) await mSubscribe(await pTopic(f.code));
      publishPresence();
      render();
    } else if (kind === 3) {                         // PUBLISH
      const tl = body[0] << 8 | body[1], qos = (type >> 1) & 3;
      const topic = dec8.decode(body.slice(2, 2 + tl)), payload = body.slice(2 + tl + (qos ? 2 : 0));
      if (topic === await iTopic(myCode)) { const o = await unseal(myCode, payload); if (o) onInbox(o); return; }
      for (const f of friends) {
        if (topic !== await pTopic(f.code)) continue;
        const o = payload.length ? await unseal(f.code, payload) : null;
        f.online = !!(o && o.t === 'here'); f.host = !!(o && o.host); f.g = o && typeof o.g === 'string' ? o.g : '';
        if (o && o.name) { const n = cleanName(o.name); if (n !== f.name) { f.name = n; saveFriends(); } }
        render();
      }
    }
  }
  async function publishPresence() {
    if (!mqUp) return;
    await mPublish(await pTopic(myCode), await seal(myCode, { t: 'here', name: myName, host: role === 'host' ? 1 : 0, g: gameId }), true);
  }
  async function sendInbox(code, obj) {
    if (!mqUp) { say('Keine Verbindung zur Vermittlung.'); return; }
    await mPublish(await iTopic(code), await seal(code, Object.assign({ from: myCode, v: PROTO }, obj)), false);
  }
  function mqOffline() {                             // App wird geschlossen: sauber abmelden
    if (!mq || !mqUp) return;
    pTopic(myCode).then((t) => { mSend(0x31, mStr(t)); mSend(0xe0, []); });
  }
  async function onInbox(o) {
    const from = normCode(o.from);
    if (!from || from === myCode || o.v !== PROTO) return;
    if (o.t === 'join') {
      const deny = (msg) => sendInbox(from, { t: 'deny', msg });
      if (role !== 'host') return deny('Gerade ist keine Runde offen.');
      if (o.g !== gameId) return deny('Andere Spielversion. Bitte beide dieselbe Version nutzen.');
      if (!friendOf(from)) { say(cleanName(o.name) + ' möchte mitspielen: erst als Freund hinzufügen (' + showCode(from) + ').'); return deny('Du stehst nicht in der Freundesliste des Hosts.'); }
      if (peers.size + pendingByCode.size + 1 >= MAX_PLAYERS) return deny('Die Runde ist voll.');
      autoInvite(from);
    } else if (o.t === 'offer') {
      if (role !== 'guest' || joinTarget !== from || guest || typeof o.s !== 'string' || o.s.length > 16000) return;
      guestFromOffer(from, o.s);
    } else if (o.t === 'answer') {
      const p = pendingByCode.get(from);
      if (role !== 'host' || !p || typeof o.s !== 'string' || o.s.length > 16000) return;
      pendingByCode.delete(from);
      try { await p.pc.setRemoteDescription({ type: 'answer', sdp: o.s }); hostAttach(p.pc, p.dc); say('Verbinde …'); }
      catch (e) { try { p.pc.close(); } catch (e2) {} }
    } else if (o.t === 'deny') {
      if (joinTarget === from) { say(cleanText(o.msg) || 'Beitreten abgelehnt.'); leave(true); }
    }
  }
  async function autoInvite(code) {
    const old = pendingByCode.get(code);
    if (old) { try { old.pc.close(); } catch (e) {} }
    const pc = new RTCPeerConnection({ iceServers: ICE }), dc = pc.createDataChannel('prisma');
    pendingByCode.set(code, { pc, dc });
    try {
      await pc.setLocalDescription(await pc.createOffer());
      await waitIce(pc);
      sendInbox(code, { t: 'offer', s: pc.localDescription.sdp, g: gameId });
    } catch (e) { pendingByCode.delete(code); return; }
    setTimeout(() => { const p = pendingByCode.get(code); if (p && p.pc === pc) { pendingByCode.delete(code); try { pc.close(); } catch (e) {} } }, 60000);
  }
  function autoJoin(code) {
    leave(true);
    role = 'guest'; joinTarget = code;
    const f = friendOf(code);
    say('Frage ' + (f && f.name ? f.name : showCode(code)) + ' …');
    sendInbox(code, { t: 'join', name: myName, g: gameId });
    setTimeout(() => { if (joinTarget === code && !guest) { say('Keine Antwort vom Host.'); leave(true); } }, 20000);
    render();
  }
  async function guestFromOffer(code, sdp) {
    const pc = guestSetup();
    try {
      await pc.setRemoteDescription({ type: 'offer', sdp });
      await pc.setLocalDescription(await pc.createAnswer());
      await waitIce(pc);
      if (joinTarget === code) sendInbox(code, { t: 'answer', s: pc.localDescription.sdp });
    } catch (e) { say('Beitreten fehlgeschlagen.'); leave(true); }
  }
  function addFriend() {
    const code = normCode(ui.addIn.value);
    if (!code) { say('Ein Freundes-Code hat 8 Zeichen, z. B. ' + showCode(myCode) + '.'); return; }
    if (code === myCode) { say('Das ist dein eigener Code.'); return; }
    if (friendOf(code)) { say('Ist schon in der Liste.'); return; }
    if (friends.length >= 50) { say('Die Freundesliste ist voll.'); return; }
    friends.push({ code, name: '', online: false, host: false, g: '' });
    saveFriends();
    ui.addIn.value = '';
    if (mqUp) pTopic(code).then(mSubscribe);
    render();
  }
  function removeFriend(code) {
    friends = friends.filter((f) => f.code !== code);
    saveFriends();
    render();
  }

  // ---------------- Host ----------------
  function hostStart() {
    leave(true);
    role = 'host';
    players = [{ id: 0, name: myName }];
    publishPresence();
    render();
  }
  async function hostInvite() {
    if (role !== 'host') return;
    if (peers.size + 1 >= MAX_PLAYERS) { say('Die Runde ist voll (' + MAX_PLAYERS + ' Spieler).'); return; }
    if (pending) pending.pc.close();
    const pc = new RTCPeerConnection({ iceServers: ICE });
    const dc = pc.createDataChannel('prisma');
    pending = { pc, dc };
    ui.inviteCode.value = 'Code wird erstellt …';
    render();
    try {
      await pc.setLocalDescription(await pc.createOffer());
      await waitIce(pc);
      ui.inviteCode.value = await pack(pc.localDescription);
    } catch (e) { ui.inviteCode.value = ''; say('Einladung fehlgeschlagen: ' + e.message); pending = null; }
    render();
  }
  async function hostAccept() {
    if (role !== 'host' || !pending) { say('Erst „Freund einladen“ drücken.'); return; }
    const p = pending;
    try { await p.pc.setRemoteDescription(await unpack(ui.answerIn.value)); }
    catch (e) { say(e.message); return; }
    pending = null;
    ui.inviteCode.value = ''; ui.answerIn.value = '';
    hostAttach(p.pc, p.dc);
    say('Verbinde …');
  }
  function hostAttach(pc, dc) {                      // Verbindung steht fest: als Mitspieler aufnehmen
    const id = nextId++;
    peers.set(id, { pc, dc, name: '…' });
    dc.onmessage = (ev) => hostReceive(id, ev.data);
    dc.onclose = () => hostDrop(id);
    pc.onconnectionstatechange = () => { if (['failed', 'closed'].includes(pc.connectionState)) hostDrop(id); };
    render();
  }
  function hostReceive(id, data) {
    const peer = peers.get(id), o = parse(data);
    if (!peer || !o) return;
    if (o.t === 'hello') {
      if (o.v !== PROTO || o.g !== gameId) { send(peer.dc, { t: 'err', msg: 'Andere Spielversion.' }); hostDrop(id); return; }
      peer.name = cleanName(o.name);
      say(peer.name + ' ist beigetreten.');
      hostBroadcastList();
    } else if (o.t === 'chat') {
      const text = cleanText(o.text);
      if (text) hostChat(peer.name, text);
    } else if (o.t === 'pos') {
      const q = cleanPos(o);
      if (!q) return;
      onPos(id, q);
      const m = Object.assign({ t: 'pos', id }, q);
      for (const [oid, pp] of peers) if (oid !== id) send(pp.dc, m);
    }
  }
  function hostDrop(id) {
    const peer = peers.get(id);
    if (!peer) return;
    peers.delete(id);
    ghosts.delete(id);
    try { peer.pc.close(); } catch (e) {}
    if (peer.name !== '…') say(peer.name + ' hat die Runde verlassen.');
    hostBroadcastList();
  }
  function hostBroadcastList() {
    players = [{ id: 0, name: myName }];
    for (const [id, p] of peers) if (p.name !== '…') players.push({ id, name: p.name });
    for (const p of peers.values()) send(p.dc, { t: 'list', p: players });
    render();
  }
  function hostChat(from, text) {
    addChat(from, text);
    for (const p of peers.values()) send(p.dc, { t: 'chat', from, text });
  }

  // ---------------- Gast ----------------
  async function guestJoin() {
    const code = ui.inviteIn.value;                  // vor leave() lesen, leave() leert die Felder
    leave(true);
    ui.inviteIn.value = code;
    role = 'guest';
    let offer;
    try { offer = await unpack(code); }
    catch (e) { say(e.message); role = null; render(); return; }
    const pc = guestSetup();
    ui.answerCode.value = 'Antwort-Code wird erstellt …';
    render();
    try {
      await pc.setRemoteDescription(offer);
      await pc.setLocalDescription(await pc.createAnswer());
      await waitIce(pc);
      ui.answerCode.value = await pack(pc.localDescription);
    } catch (e) { say('Beitreten fehlgeschlagen: ' + e.message); leave(true); }
    render();
  }
  function guestSetup() {                            // Gast-Verbindung anlegen (Code per Hand oder automatisch)
    const pc = new RTCPeerConnection({ iceServers: ICE });
    guest = { pc, dc: null };
    pc.ondatachannel = (ev) => {
      const dc = ev.channel;
      guest.dc = dc;
      dc.onopen = () => { send(dc, { t: 'hello', name: myName, g: gameId, v: PROTO }); say('Verbunden!'); render(); };
      dc.onmessage = (m) => guestReceive(m.data);
      dc.onclose = () => { if (role === 'guest') { say('Verbindung zum Host verloren.'); leave(true); } };
    };
    pc.onconnectionstatechange = () => { if (pc.connectionState === 'failed' && role === 'guest') { say('Verbindung fehlgeschlagen. Am besten beide im WLAN versuchen.'); leave(true); } };
    return pc;
  }
  function guestReceive(data) {
    const o = parse(data);
    if (!o) return;
    if (o.t === 'list' && Array.isArray(o.p)) {
      players = o.p.slice(0, MAX_PLAYERS).map((x) => ({ id: x.id | 0, name: cleanName(x.name) }));
      render();
    } else if (o.t === 'chat') {
      const text = cleanText(o.text);
      if (text) addChat(cleanName(o.from), text);
    } else if (o.t === 'pos') {
      if (Number.isInteger(o.id) && o.id >= 0) onPos(o.id, cleanPos(o));
    } else if (o.t === 'err') {
      say(cleanText(o.msg) || 'Vom Host abgelehnt.');
      leave(true);
    }
  }

  // ---------------- Gemeinsam ----------------
  function chatSend() {
    const text = cleanText(ui.chatIn.value);
    if (!text) return;
    ui.chatIn.value = '';
    if (role === 'host') hostChat(myName, text);
    else if (role === 'guest' && guest && guest.dc) send(guest.dc, { t: 'chat', text });
  }
  function addChat(from, text) {
    chatLog.push({ from, text });
    if (chatLog.length > 50) chatLog.shift();
    if (from !== myName && document.getElementById('menu').hidden) say(from + ': ' + text);
    render();
  }
  function leave(quiet) {
    if (pending) { try { pending.pc.close(); } catch (e) {} pending = null; }
    for (const p of peers.values()) { try { p.pc.close(); } catch (e) {} }
    peers.clear();
    if (guest) { try { guest.pc.close(); } catch (e) {} guest = null; }
    for (const p of pendingByCode.values()) { try { p.pc.close(); } catch (e) {} }
    pendingByCode.clear();
    joinTarget = null;
    const was = role;
    role = null; players = []; ghosts.clear();
    if (was === 'host') publishPresence();
    if (ui.inviteCode) { ui.inviteCode.value = ''; ui.answerIn.value = ''; ui.inviteIn.value = ''; ui.answerCode.value = ''; }
    if (!quiet && was) say('Runde verlassen.');
    render();
  }
  function connectedGuest() { return role === 'guest' && guest && guest.dc && guest.dc.readyState === 'open'; }

  // ---------------- Oberflaeche ----------------
  const ui = {};
  function el(tag, attrs, text) {
    const e = document.createElement(tag);
    for (const k in attrs || {}) e.setAttribute(k, attrs[k]);
    if (text) e.textContent = text;
    return e;
  }
  function copy(ta) {
    const v = ta.value;
    if (!v.startsWith(CODE_PREFIX)) return;
    const ok = () => say('Code kopiert.');
    if (navigator.clipboard && window.isSecureContext) navigator.clipboard.writeText(v).then(ok, () => fallback());
    else fallback();
    function fallback() { ta.removeAttribute('readonly'); ta.select(); try { document.execCommand('copy'); ok(); } catch (e) {} ta.setAttribute('readonly', ''); }
  }
  function share(ta) {
    const v = ta.value;
    if (v.startsWith(CODE_PREFIX) && navigator.share) navigator.share({ text: v }).catch(() => {});
  }
  function build() {
    const menu = document.getElementById('menu');
    const mainCard = menu.querySelector('.card');
    const style = el('style');
    style.textContent =
      '#net textarea,#net input{width:100%;box-sizing:border-box;border:0;border-radius:10px;padding:10px;margin:6px 0;' +
      'background:#0004;color:inherit;font:12px/1.3 monospace}#net input{font:15px system-ui}' +
      '#net textarea{height:64px;resize:none;word-break:break-all}#net h2{font-size:14px;margin:14px 0 2px}' +
      '#net .row{display:flex;gap:8px}#net .row button{flex:1}#net .list div,#net .log div{font-size:14px;padding:3px 0}' +
      '#net .log{max-height:140px;overflow-y:auto;background:#0003;border-radius:10px;padding:6px 10px;margin:6px 0}' +
      '#net [hidden]{display:none!important}#net .code{font:bold 22px monospace;letter-spacing:2px;margin:4px 0}' +
      '#net .fr{display:flex;align-items:center;gap:8px;padding:4px 0}#net .fr span{flex:1;font-size:14px}' +
      '#net .fr button{width:auto;margin:0;padding:8px 12px;flex:0 0 auto}#net details{margin-top:12px}' +
      '#net summary{cursor:pointer;color:var(--dim);font-size:13px}#net .dim{color:var(--dim);font-size:12px}';
    document.head.appendChild(style);

    const btn = el('button', { id: 'mNet' }, 'Mitspielen (online)');
    mainCard.insertBefore(btn, document.getElementById('mResume').nextSibling);

    const c = el('div', { class: 'card', id: 'net', hidden: '' });
    c.appendChild(el('h1', null, 'Mitspielen'));
    ui.status = c.appendChild(el('p'));
    c.appendChild(el('h2', null, 'Dein Name'));
    ui.name = c.appendChild(el('input', { maxlength: String(MAX_NAME), placeholder: 'Name', autocomplete: 'off' }));
    ui.name.value = myName;

    c.appendChild(el('h2', null, 'Dein Freundes-Code'));
    ui.myCode = c.appendChild(el('div', { class: 'code' }, showCode(myCode)));
    const r0 = c.appendChild(el('div', { class: 'row' }));
    ui.bCopyMine = r0.appendChild(el('button', null, 'Kopieren'));
    ui.bShareMine = r0.appendChild(el('button', null, 'Teilen'));
    ui.bHostAuto = c.appendChild(el('button', { class: 'main' }, 'Runde eröffnen'));
    c.appendChild(el('h2', null, 'Freunde'));
    ui.friends = c.appendChild(el('div'));
    const ra = c.appendChild(el('div', { class: 'row' }));
    ui.addIn = ra.appendChild(el('input', { maxlength: '12', placeholder: 'Freundes-Code', autocomplete: 'off', autocapitalize: 'characters' }));
    ui.bAdd = ra.appendChild(el('button', null, 'Hinzufügen'));
    ui.bAdd.style.flex = '0 0 120px';
    ui.mqState = c.appendChild(el('p', { class: 'dim' }));

    const det = el('details');
    det.appendChild(el('summary', null, 'Ohne Vermittlung (Codes per Hand tauschen)'));
    ui.start = det.appendChild(el('div', { class: 'row' }));
    ui.bHost = ui.start.appendChild(el('button', null, 'Runde eröffnen'));
    ui.bJoinShow = ui.start.appendChild(el('button', null, 'Beitreten'));

    ui.host = det.appendChild(el('div'));
    ui.bInvite = ui.host.appendChild(el('button', { class: 'main' }, 'Freund einladen'));
    ui.host.appendChild(el('h2', null, '1. Diesen Code dem Freund schicken'));
    ui.inviteCode = ui.host.appendChild(el('textarea', { readonly: '' }));
    const r1 = ui.host.appendChild(el('div', { class: 'row' }));
    ui.bCopyInv = r1.appendChild(el('button', null, 'Kopieren'));
    ui.bShareInv = r1.appendChild(el('button', null, 'Teilen'));
    ui.host.appendChild(el('h2', null, '2. Antwort-Code des Freundes einfügen'));
    ui.answerIn = ui.host.appendChild(el('textarea', { placeholder: 'PRISMA1:…' }));
    ui.bAccept = ui.host.appendChild(el('button', null, 'Verbinden'));

    ui.join = det.appendChild(el('div'));
    ui.join.appendChild(el('h2', null, '1. Einladungs-Code vom Host einfügen'));
    ui.inviteIn = ui.join.appendChild(el('textarea', { placeholder: 'PRISMA1:…' }));
    ui.bJoin = ui.join.appendChild(el('button', { class: 'main' }, 'Antwort-Code erstellen'));
    ui.join.appendChild(el('h2', null, '2. Diesen Code an den Host zurückschicken'));
    ui.answerCode = ui.join.appendChild(el('textarea', { readonly: '' }));
    const r2 = ui.join.appendChild(el('div', { class: 'row' }));
    ui.bCopyAns = r2.appendChild(el('button', null, 'Kopieren'));
    ui.bShareAns = r2.appendChild(el('button', null, 'Teilen'));

    ui.online = c.appendChild(el('div'));
    ui.online.appendChild(el('h2', null, 'Online'));
    ui.list = ui.online.appendChild(el('div', { class: 'list' }));
    ui.online.appendChild(el('h2', null, 'Nachrichten'));
    ui.log = ui.online.appendChild(el('div', { class: 'log' }));
    const r3 = ui.online.appendChild(el('div', { class: 'row' }));
    ui.chatIn = r3.appendChild(el('input', { maxlength: String(MAX_TEXT), placeholder: 'Nachricht', autocomplete: 'off' }));
    ui.bSend = r3.appendChild(el('button', null, 'Senden'));
    ui.bSend.style.flex = '0 0 90px';

    ui.bLeave = c.appendChild(el('button', null, 'Runde verlassen'));
    c.appendChild(det);
    ui.bBack = c.appendChild(el('button', null, 'Zurück'));
    menu.appendChild(c);
    ui.card = c; ui.mainCard = mainCard; ui.joinMode = false;

    btn.addEventListener('click', () => {
      mainCard.hidden = true; c.hidden = false;
      try { localStorage.setItem('prisma-net-on', '1'); } catch (e) {}   // ab jetzt Freunde online sehen
      mqConnect();
      render();
    });
    ui.bHostAuto.addEventListener('click', () => { ui.joinMode = false; hostStart(); });
    ui.bAdd.addEventListener('click', addFriend);
    ui.addIn.addEventListener('keydown', (e) => { if (e.key === 'Enter') addFriend(); });
    ui.bCopyMine.addEventListener('click', () => {
      const v = showCode(myCode);
      if (navigator.clipboard && window.isSecureContext) navigator.clipboard.writeText(v).then(() => say('Code kopiert.'), () => {});
      else say('Dein Code: ' + v);
    });
    ui.bShareMine.addEventListener('click', () => { if (navigator.share) navigator.share({ text: 'Mein Pokémon-Prisma-Freundes-Code: ' + showCode(myCode) }).catch(() => {}); });
    window.addEventListener('pagehide', mqOffline);
    ui.bBack.addEventListener('click', () => { c.hidden = true; mainCard.hidden = false; });
    document.getElementById('mResume').addEventListener('click', () => { c.hidden = true; mainCard.hidden = false; });
    ui.name.addEventListener('change', () => {
      myName = cleanName(ui.name.value); ui.name.value = myName; saveName(myName);
      if (role === 'host') hostBroadcastList();
      publishPresence();
    });
    ui.bHost.addEventListener('click', () => { ui.joinMode = false; hostStart(); });
    ui.bJoinShow.addEventListener('click', () => { leave(true); ui.joinMode = true; render(); });
    ui.bInvite.addEventListener('click', hostInvite);
    ui.bAccept.addEventListener('click', hostAccept);
    ui.bJoin.addEventListener('click', guestJoin);
    ui.bCopyInv.addEventListener('click', () => copy(ui.inviteCode));
    ui.bCopyAns.addEventListener('click', () => copy(ui.answerCode));
    ui.bShareInv.addEventListener('click', () => share(ui.inviteCode));
    ui.bShareAns.addEventListener('click', () => share(ui.answerCode));
    ui.bSend.addEventListener('click', chatSend);
    ui.chatIn.addEventListener('keydown', (e) => { if (e.key === 'Enter') chatSend(); });
    ui.bLeave.addEventListener('click', () => { ui.joinMode = false; leave(false); });
    if (!navigator.share) { ui.bShareInv.hidden = true; ui.bShareAns.hidden = true; ui.bShareMine.hidden = true; }
    if (!window.crypto || !crypto.subtle) ui.mqState.textContent = 'Automatisches Verbinden ist auf diesem Gerät nicht möglich – nutze „Ohne Vermittlung“.';
    mqConnect();
    if (typeof RTCPeerConnection !== 'function') { btn.disabled = true; btn.textContent = 'Mitspielen (auf diesem Gerät nicht möglich)'; }
    render();
  }
  function render() {
    if (!ui.card) return;
    const inRound = role === 'host' || connectedGuest();
    ui.start.hidden = role !== null;
    ui.host.hidden = role !== 'host';
    ui.join.hidden = !(ui.joinMode && role !== 'host' && !connectedGuest());
    ui.online.hidden = !inRound;
    ui.bLeave.hidden = role === null && !ui.joinMode;
    ui.status.textContent =
      role === 'host' ? 'Du bist Host. Deine Freunde sehen „Runde offen“ und tippen auf Beitreten. Bleib in der App, sonst endet die Runde.' :
      connectedGuest() ? 'Verbunden mit der Runde.' :
      role === 'guest' && joinTarget ? 'Verbinde mit dem Host …' :
      role === 'guest' ? 'Schick den Antwort-Code an den Host und warte, bis er „Verbinden“ drückt.' :
      ui.joinMode ? 'Füge den Einladungs-Code des Hosts ein.' :
      'Gebt euch einmal gegenseitig eure Freundes-Codes. Einer eröffnet die Runde, die anderen tippen in der Freundesliste auf Beitreten. Am besten alle im WLAN.';
    ui.bHostAuto.hidden = role !== null;
    if (window.crypto && crypto.subtle) ui.mqState.textContent = mqUp ? 'Vermittlung verbunden.' : 'Verbinde mit der Vermittlung …';
    ui.friends.textContent = '';
    if (!friends.length) ui.friends.appendChild(el('div', { class: 'dim' }, 'Noch keine Freunde. Tauscht eure Freundes-Codes aus und tragt sie unten ein.'));
    for (const f of friends) {
      const row = ui.friends.appendChild(el('div', { class: 'fr' }));
      const state = !f.online ? 'offline' : f.g && f.g !== gameId ? 'andere Version' : f.host ? 'Runde offen' : 'online';
      row.appendChild(el('span', null, (f.online ? '● ' : '○ ') + (f.name || showCode(f.code)) + ' – ' + state));
      if (f.online && f.host && f.g === gameId && role === null) {
        const b = row.appendChild(el('button', { class: 'main' }, 'Beitreten'));
        b.addEventListener('click', () => autoJoin(f.code));
      }
      const x = row.appendChild(el('button', { title: 'Entfernen' }, '✕'));
      x.addEventListener('click', () => { if (confirm('Freund entfernen?')) removeFriend(f.code); });
    }
    ui.list.textContent = '';
    for (const p of players) ui.list.appendChild(el('div', null, (p.id === 0 ? '★ ' : '• ') + p.name));
    ui.log.textContent = '';
    for (const m of chatLog) ui.log.appendChild(el('div', null, m.from + ': ' + m.text));
    ui.log.scrollTop = ui.log.scrollHeight;
  }

  window.PrismaNet = {
    attach, tick, draw,
    isTyping(e) { const t = e && e.target; return !!(t && (t.tagName === 'INPUT' || t.tagName === 'TEXTAREA')); },
  };
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', build); else build();
})();
