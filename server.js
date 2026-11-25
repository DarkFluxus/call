'use strict';
// Resenha v2: sinalização (long-polling) + upload de arquivos. Zero dependências.
// Áudio e tela vão direto entre os navegadores (WebRTC); o servidor só repassa mensagens e arquivos.
//
// Variáveis opcionais:
//   SENHA=xxxx          exige senha pra CRIAR sala (quem tem o código entra sem senha)
//   PORT=3000           porta (hospedagem define sozinha)
//   HOST=127.0.0.1      onde escuta (padrão: só local; vira 0.0.0.0 se a hospedagem definir PORT)
//   TRUST_PROXY=1       confia no X-Forwarded-For (use em Render/Railway/Fly etc.)
//   MAX_FILE_MB=2048    tamanho máximo de arquivo     ROOM_QUOTA_MB=4096 limite por sala    GLOBAL_QUOTA_MB=4096  limite do servidor todo
//                       (se a hospedagem tiver disco pequeno, diminua esses três; o servidor também recusa upload quando o disco está acabando)
//   CF_TURN_KEY_ID / CF_TURN_TOKEN     TURN grátis da Cloudflare (faz tela/voz funcionar pra quem está em 4G ou rede restrita)
//   TURN_URL / TURN_USER / TURN_PASS   ou qualquer outro servidor TURN
const http = require('http'), fs = require('fs'), path = require('path'), os = require('os'), zlib = require('zlib'), crypto = require('crypto');
const PORT = +process.env.PORT || 3000;
const HOST = process.env.HOST || (process.env.PORT ? '0.0.0.0' : '127.0.0.1');
const SENHA = process.env.SENHA || '', TRUST = process.env.TRUST_PROXY === '1';
const MAX = 8, POLL_MS = 25000, GONE_MS = 40000, EMPTY_MS = 15 * 60000, MAX_ROOMS = 60, MAX_CLIENTS = 300;
const MAX_FILE = (+process.env.MAX_FILE_MB || 2048) * 1048576, QUOTA = (+process.env.ROOM_QUOTA_MB || 4096) * 1048576, GLOBAL = (+process.env.GLOBAL_QUOTA_MB || 4096) * 1048576, CHUNK_MAX = 16 * 1048576, DISK_RESERVE = 300 * 1048576;
const HTML = fs.readFileSync(path.join(__dirname, 'index.html'), 'utf8');
const DIR = fs.mkdtempSync(path.join(os.tmpdir(), 'resenha-'));
const KEY = crypto.randomBytes(32);
const AL = 'ABCDEFGHJKMNPQRSTUVWXYZ23456789';
const ROOM = /^[A-Z0-9]{4,10}$/, PID = /^[a-z0-9]{6,32}$/, TOK = /^[a-f0-9]{24,64}$/, FID = /^[a-f0-9]{24}$/;
const INLINE = /^(image\/(png|jpe?g|gif|webp|avif)|video\/(mp4|webm|ogg|quicktime)|audio\/(mpeg|mp3|ogg|wav|webm|mp4|aac|x-m4a|flac))$/;
const rooms = new Map(); // código -> {peers:Map(id->cliente), files:Map(fid->arquivo), bytes, empty}

/* ---------- utilitários ---------- */
const sha = s => crypto.createHash('sha256').update(String(s)).digest();
const same = (a, b) => crypto.timingSafeEqual(sha(a), sha(b));
const clean = (s, n) => String(s || '').replace(/[\u0000-\u001f\u007f-\u009f\u200e\u200f\u202a-\u202e\u2066-\u2069]/g, '').trim().slice(0, n);
const sign = (room, fid, id) => crypto.createHmac('sha256', KEY).update(room + '|' + fid + '|' + id).digest('hex').slice(0, 32);
const newCode = () => { let s = ''; for (let i = 0; i < 8; i++) s += AL[crypto.randomInt(AL.length)]; return s; };
const end = (res, c) => { res.writeHead(c); res.end(); };
const json = (res, c, o) => { res.writeHead(c, { 'Content-Type': 'application/json', 'Cache-Control': 'no-store' }); res.end(JSON.stringify(o)); };
const lo = a => a === '127.0.0.1' || a === '::1' || a === '::ffff:127.0.0.1';
const ipOf = req => {
  const a = req.socket.remoteAddress || '?', h = req.headers;
  if (lo(a) && h['cf-connecting-ip']) return clean(h['cf-connecting-ip'], 45); // túnel Cloudflare no mesmo aparelho
  if (TRUST) { const f = h['cf-connecting-ip'] || String(h['x-forwarded-for'] || '').split(',')[0].trim(); if (f) return clean(f, 45); } // Render/Cloudflare: o IP real do cliente vem nesses cabeçalhos
  return a;
};

/* ---------- limite de requisições por IP ---------- */
const hits = new Map(), conns = new Map();
const hit = (ip, k, max, win) => { // true = estourou o limite
  const key = ip + '|' + k, now = Date.now();
  let h = hits.get(key);
  if (!h || now - h.t > win) { h = { n: 0, t: now, w: win }; hits.set(key, h); }
  return ++h.n > max;
};
const banned = ip => { const h = hits.get(ip + '|bad'); return !!h && Date.now() - h.t <= h.w && h.n > 20; };
const strike = ip => hit(ip, 'bad', 20, 600000); // tentativa errada (sala/senha): 20 em 10 min = bloqueio por 10 min
setInterval(() => { const now = Date.now(); hits.forEach((h, k) => { if (now - h.t > h.w) hits.delete(k); }); }, 60000);

/* ---------- ícone do app (PWA), gerado sem arquivo ---------- */
const crcT = new Uint32Array(256).map((_, n) => { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; return c >>> 0; });
const crc = b => { let c = 0xffffffff; for (const x of b) c = crcT[(c ^ x) & 255] ^ (c >>> 8); return (c ^ 0xffffffff) >>> 0; };
const chunk = (t, d) => { const b = Buffer.alloc(12 + d.length); b.writeUInt32BE(d.length, 0); b.write(t, 4, 'latin1'); d.copy(b, 8); b.writeUInt32BE(crc(b.subarray(4, 8 + d.length)), 8 + d.length); return b; };
function icon(S) {
  const rr = (x, y, cx, cy, hw, hh, r) => { const dx = Math.abs(x - cx) - hw + r, dy = Math.abs(y - cy) - hh + r; return Math.hypot(Math.max(dx, 0), Math.max(dy, 0)) + Math.min(Math.max(dx, dy), 0) - r; };
  const cv = d => Math.max(0, Math.min(1, 0.5 - d));
  const raw = Buffer.alloc(S * (S * 4 + 1)), BG = [0x26, 0x1b, 0x38], YL = [0xff, 0xd8, 0x4d];
  for (let y = 0; y < S; y++) {
    raw[y * (S * 4 + 1)] = 0;
    for (let x = 0; x < S; x++) {
      const u = x / S, v = y / S;
      const bub = Math.max(cv(rr(u, v, .5, .47, .24, .17, .1) * S), cv(rr(u, v, .36, .66, .055, .06, .02) * S));
      const dot = Math.max(...[-.1, 0, .1].map(o => cv((Math.hypot(u - .5 - o, v - .47) - .03) * S)));
      const o = y * (S * 4 + 1) + 1 + x * 4;
      for (let i = 0; i < 3; i++) { const a = BG[i] + (YL[i] - BG[i]) * bub; raw[o + i] = Math.round(a + (BG[i] - a) * dot); }
      raw[o + 3] = 255;
    }
  }
  const ih = Buffer.alloc(13); ih.writeUInt32BE(S, 0); ih.writeUInt32BE(S, 4); ih[8] = 8; ih[9] = 6;
  return Buffer.concat([Buffer.from([137, 80, 78, 71, 13, 10, 26, 10]), chunk('IHDR', ih), chunk('IDAT', zlib.deflateSync(raw, { level: 9 })), chunk('IEND', Buffer.alloc(0))]);
}
const ICON = { 192: icon(192), 512: icon(512) };
const MANIFEST = JSON.stringify({ name: 'Resenha', short_name: 'Resenha', start_url: '/', scope: '/', display: 'standalone', background_color: '#1a1326', theme_color: '#261b38', lang: 'pt-BR',
  icons: [{ src: '/icon-192.png', sizes: '192x192', type: 'image/png', purpose: 'any maskable' }, { src: '/icon-512.png', sizes: '512x512', type: 'image/png', purpose: 'any maskable' }] });
const SW = "self.addEventListener('install',()=>self.skipWaiting());self.addEventListener('activate',e=>e.waitUntil(self.clients.claim()));" +
  "self.addEventListener('fetch',e=>{if(e.request.mode==='navigate')e.respondWith(fetch(e.request).catch(()=>new Response('Sem conexão com o servidor.',{status:503,headers:{'Content-Type':'text/plain;charset=utf-8'}})))});";

/* ---------- salas ---------- */
const flush = c => {
  if (!c.res) return;
  const r = c.res; c.res = null; clearTimeout(c.t); c.seen = Date.now();
  json(r, 200, c.q.splice(0));
};
const push = (c, e, d) => { c.q.push({ e, d }); flush(c); };
const others = (r, id, e, d) => r.peers.forEach((c, k) => { if (k !== id) push(c, e, d); });
const remove = (r, id) => {
  const c = r.peers.get(id);
  if (!c) return;
  r.peers.delete(id);
  if (c.res) { clearTimeout(c.t); c.res.writeHead(404); c.res.end(); c.res = null; }
  others(r, id, 'leave', { id });
  if (!r.peers.size) r.empty = Date.now();
};
const dropRoom = code => { const r = rooms.get(code); if (!r) return; r.files.forEach(f => fs.unlink(f.p, () => {})); r.ups.forEach(u => fs.unlink(u.fp, () => {})); rooms.delete(code); };
const auth = (room, id, k) => { // só quem tem o token secreto do cliente passa
  const r = rooms.get(room), c = r && r.peers.get(id);
  return c && TOK.test(k) && crypto.timingSafeEqual(c.th, sha(k)) ? { r, c } : null;
};
const STUN = [{ urls: ['stun:stun.l.google.com:19302', 'stun:stun1.l.google.com:19302', 'stun:stun.cloudflare.com:3478'] }];
let turnC = { t: 0, list: [] };
async function turnList() {
  const out = [];
  if (process.env.TURN_URL) out.push({ urls: process.env.TURN_URL.split(','), username: process.env.TURN_USER || '', credential: process.env.TURN_PASS || '' });
  const kid = process.env.CF_TURN_KEY_ID, tok = process.env.CF_TURN_TOKEN;
  if (kid && tok) {
    if (Date.now() - turnC.t > 3600e3) { // credencial da Cloudflare dura 24h; renova a cada 1h
      try {
        const r = await fetch('https://rtc.live.cloudflare.com/v1/turn/keys/' + encodeURIComponent(kid) + '/credentials/generate-ice-servers', {
          method: 'POST', headers: { Authorization: 'Bearer ' + tok, 'Content-Type': 'application/json' }, body: JSON.stringify({ ttl: 86400 }), signal: AbortSignal.timeout(8000) });
        if (!r.ok) throw new Error('HTTP ' + r.status);
        const d = await r.json(), is = d.iceServers;
        turnC = { t: Date.now(), list: (Array.isArray(is) ? is : is ? [is] : []).filter(x => x && x.urls) };
      } catch (e) { console.error('TURN da Cloudflare falhou:', e.message); turnC.t = Date.now() - 3000e3; } // tenta de novo em ~10 min
    }
    out.push(...turnC.list);
  }
  return out;
}
const HIST_MAX = 300;
const histFor = (room, r, pid) => r.hist.map(x => x.k === 'c'
  ? { e: 'chat', d: { name: x.name, text: x.text, mid: x.mid, re: x.re, t: x.t } }
  : { e: 'file', d: { name: x.name, mid: x.mid, re: x.re, t: x.t, file: { name: x.f.name, size: x.f.size, mime: x.f.mime, u: '/f?room=' + room + '&id=' + pid + '&fid=' + x.fid + '&s=' + sign(room, x.fid, pid) } } });
const small = (o, n) => String(o || '').slice(0, n);

/* ---------- servidor ---------- */
const server = http.createServer({ maxHeaderSize: 8192 }, (req, res) => {
  const h = req.headers, m = req.method, ip = ipOf(req);
  res.setHeader('X-Content-Type-Options', 'nosniff');
  res.setHeader('Referrer-Policy', 'no-referrer');
  res.setHeader('X-Frame-Options', 'DENY');
  res.setHeader('Cross-Origin-Opener-Policy', 'same-origin');
  res.setHeader('Permissions-Policy', 'microphone=(self), display-capture=(self), fullscreen=(self), camera=(), geolocation=(), payment=(), usb=()');
  if (String(h['x-forwarded-proto'] || '').includes('https')) res.setHeader('Strict-Transport-Security', 'max-age=15552000');
  if (m !== 'GET' && m !== 'POST') return end(res, 405);
  let u; try { u = new URL(req.url, 'http://x'); } catch (e) { return end(res, 400); }
  if (m === 'POST' && h.origin) { let o; try { o = new URL(h.origin).host; } catch (e) { o = ''; } if (o !== h.host) return end(res, 403); } // anti-CSRF
  if (hit(ip, 'all', 1500, 60000)) return json(res, 429, { error: 'devagar' });
  const p = u.pathname, q = u.searchParams;

  if (m === 'GET') {
    if (p === '/') {
      const n = crypto.randomBytes(16).toString('base64');
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-store',
        'Content-Security-Policy': `default-src 'none'; script-src 'nonce-${n}'; style-src 'nonce-${n}'; img-src 'self' blob:; media-src 'self' blob:; connect-src 'self'; manifest-src 'self'; worker-src 'self'; base-uri 'none'; form-action 'none'; frame-ancestors 'none'` });
      return res.end(HTML.split('__N__').join(n));
    }
    if (p === '/config') return json(res, 200, { pass: !!SENHA, maxFile: MAX_FILE });
    if (p === '/manifest.webmanifest') { res.writeHead(200, { 'Content-Type': 'application/manifest+json', 'Cache-Control': 'public, max-age=3600' }); return res.end(MANIFEST); }
    if (p === '/sw.js') { res.writeHead(200, { 'Content-Type': 'application/javascript; charset=utf-8', 'Cache-Control': 'no-cache' }); return res.end(SW); }
    if (p === '/icon-192.png' || p === '/icon-512.png' || p === '/apple-touch-icon.png') {
      res.writeHead(200, { 'Content-Type': 'image/png', 'Cache-Control': 'public, max-age=86400' });
      return res.end(p === '/icon-512.png' ? ICON[512] : ICON[192]);
    }
    if (p === '/favicon.ico') return end(res, 204);
  }

  if (m === 'POST' && p === '/create') {
    if (banned(ip)) return json(res, 429, { error: 'bloqueado' });
    if (hit(ip, 'create', 10, 60000)) return json(res, 429, { error: 'devagar' });
    if (SENHA && !same(h['x-senha'] || '', SENHA)) { strike(ip); return json(res, 403, { error: 'senha' }); }
    if (rooms.size >= MAX_ROOMS) return json(res, 503, { error: 'lotado' });
    let c; do c = newCode(); while (rooms.has(c));
    rooms.set(c, { peers: new Map(), files: new Map(), ups: new Map(), hist: [], bytes: 0, empty: Date.now() });
    return json(res, 200, { room: c });
  }

  const room = q.get('room') || '', id = q.get('id') || '', k = q.get('k') || '';
  if (!ROOM.test(room) || !PID.test(id)) return end(res, 404);

  if (m === 'GET' && p === '/f') { // download/visualização de arquivo: link assinado por pessoa
    const fid = q.get('fid') || '', s = q.get('s') || '', r = rooms.get(room), f = r && FID.test(fid) && r.files.get(fid);
    if (!f || !r.peers.has(id) || !same(s, sign(room, fid, id))) return end(res, 404);
    let a = 0, b = f.size - 1, code = 200;
    const rg = /^bytes=(\d*)-(\d*)$/.exec(h.range || '');
    if (rg && (rg[1] || rg[2])) {
      if (rg[1] === '') a = Math.max(0, f.size - +rg[2]); else { a = +rg[1]; if (rg[2]) b = Math.min(b, +rg[2]); }
      if (a > b || a >= f.size) { res.writeHead(416, { 'Content-Range': 'bytes */' + f.size }); return res.end(); }
      code = 206;
    }
    const inl = INLINE.test(f.mime) && q.get('dl') !== '1';
    const hd = { 'Content-Type': f.mime, 'Content-Length': b - a + 1, 'Accept-Ranges': 'bytes', 'Cache-Control': 'private, max-age=600',
      'Content-Disposition': (inl ? 'inline' : 'attachment') + "; filename*=UTF-8''" + encodeURIComponent(f.name).replace(/['()*]/g, c => '%' + c.charCodeAt(0).toString(16).toUpperCase()),
      'Content-Security-Policy': "sandbox; default-src 'none'", 'Cross-Origin-Resource-Policy': 'same-origin' };
    if (code === 206) hd['Content-Range'] = 'bytes ' + a + '-' + b + '/' + f.size;
    res.writeHead(code, hd);
    const rs = fs.createReadStream(f.p, { start: a, end: b });
    rs.on('error', () => res.destroy());
    return rs.pipe(res);
  }

  if (m === 'POST' && p === '/join') {
    if (banned(ip)) return json(res, 429, { error: 'bloqueado' });
    if (hit(ip, 'join', 40, 60000)) return json(res, 429, { error: 'devagar' });
    if (!TOK.test(k)) return end(res, 400);
    const r = rooms.get(room);
    if (!r) { strike(ip); return json(res, 404, { error: 'sala' }); }
    const old = r.peers.get(id);
    if (old) { if (!crypto.timingSafeEqual(old.th, sha(k))) { strike(ip); return end(res, 403); } }
    else {
      if (r.peers.size >= MAX) return json(res, 200, { full: true });
      let n = 0; rooms.forEach(x => n += x.peers.size);
      if (n >= MAX_CLIENTS) return json(res, 503, { error: 'lotado' });
    }
    const name = clean(q.get('name'), 24) || 'Visitante';
    const peers = [...r.peers].filter(([x]) => x !== id).map(([x, c]) => ({ id: x, name: c.name }));
    if (old) { old.q.length = 0; flush(old); }
    r.peers.set(id, { name, th: sha(k), q: [], res: null, t: null, seen: Date.now(), cr: [] });
    r.empty = 0;
    others(r, id, 'join', { id, name });
    return json(res, 200, { peers, hist: histFor(room, r, id) });
  }

  const a = auth(room, id, k);
  if (!a) return end(res, 404); // sala/cliente desconhecido ou token errado: o cliente tenta entrar de novo
  const { r, c } = a;

  if (m === 'GET' && p === '/ice') { // credenciais TURN só pra quem já está na sala
    return turnList().then(t => json(res, 200, { ice: [...STUN, ...t], turn: t.length > 0 }));
  }

  if (m === 'GET' && p === '/poll') {
    const n = conns.get(ip) || 0;
    if (n >= 30) return end(res, 429);
    conns.set(ip, n + 1);
    c.seen = Date.now();
    if (c.res) flush(c);
    if (c.q.length) { conns.set(ip, (conns.get(ip) || 1) - 1); return json(res, 200, c.q.splice(0)); }
    c.res = res;
    c.t = setTimeout(() => flush(c), POLL_MS);
    res.on('close', () => { conns.set(ip, Math.max(0, (conns.get(ip) || 1) - 1)); if (c.res === res) { c.res = null; clearTimeout(c.t); } c.seen = Date.now(); });
    return;
  }

  if (m === 'POST' && p === '/leave') { remove(r, id); return end(res, 204); }

  if (m === 'POST' && p === '/send') {
    let b = '';
    req.setEncoding('utf8');
    req.on('data', x => { b += x; if (b.length > 65536) { b = ''; req.destroy(); } });
    req.on('end', () => {
      if (!r.peers.has(id)) return end(res, 404);
      let d; try { d = JSON.parse(b); } catch (e) { return end(res, 400); }
      if (!d || typeof d !== 'object') return end(res, 400);
      if (d.t === 'chat') {
        const now = Date.now(); c.cr = c.cr.filter(t => now - t < 10000);
        if (c.cr.length >= 10) return end(res, 429);
        c.cr.push(now);
        const text = clean(d.text, 500);
        const re = d.re && typeof d.re === 'object' ? { id: clean(d.re.id, 16), name: clean(d.re.name, 24), text: clean(d.re.text, 80) } : null;
        if (text) {
          const mid = clean(d.mid, 16), t = Date.now();
          r.hist.push({ k: 'c', name: c.name, text, mid, re, t }); if (r.hist.length > HIST_MAX) r.hist.shift();
          others(r, id, 'chat', { name: c.name, text, mid, re, t });
        }
      } else if (d.t === 'sig' && typeof d.to === 'string' && d.to !== id && r.peers.has(d.to)) {
        push(r.peers.get(d.to), 'sig', { from: id, d: d.d });
      } else if (d.t === 'share') {
        others(r, id, 'share', { id, on: !!d.on });
      }
      end(res, 204);
    });
    return;
  }

  if (m === 'POST' && p === '/upload') { // arquivo grande vai em pedaços de ~8 MB (proxies/túneis cortam pedidos grandes)
    if (hit(ip, 'up', 600, 60000)) return json(res, 429, { error: 'devagar' });
    const upid = q.get('up') || '', part = +q.get('part'), parts = +q.get('parts'), total = +q.get('size'), len = +h['content-length'];
    if (!FID.test(upid) || !Number.isInteger(part) || !Number.isInteger(parts) || part < 0 || parts < 1 || parts > 400 || part >= parts) return json(res, 400, { error: 'pedido' });
    if (!(total > 0) || total > MAX_FILE) { res.writeHead(413, { 'Content-Type': 'application/json' }); req.resume(); return res.end('{"error":"grande"}'); }
    if (!(len > 0) || len > CHUNK_MAX) return json(res, 400, { error: 'pedaço' });
    let u = r.ups.get(upid);
    if (!u) {
      if (part !== 0 || r.files.has(upid)) return json(res, 404, { error: 'sessão' });
      let g = 0; rooms.forEach(x => g += x.bytes);
      if (r.bytes + total > QUOTA || g + total > GLOBAL) { res.writeHead(413, { 'Content-Type': 'application/json' }); req.resume(); return res.end('{"error":"cota"}'); }
      try { const f = fs.statfsSync(DIR); if (f.bavail * f.bsize < total + DISK_RESERVE) { res.writeHead(413, { 'Content-Type': 'application/json' }); req.resume(); return res.end('{"error":"disco"}'); } } catch (e) {} // não deixa encher o disco
      r.bytes += total;
      u = { by: id, total, got: 0, next: 0, fp: path.join(DIR, room + '-' + upid), t: Date.now(), busy: false };
      r.ups.set(upid, u);
    } else if (u.by !== id) return json(res, 404, { error: 'sessão' });
    if (u.busy || part !== u.next) return json(res, 409, { error: 'ordem', next: u.next });
    if (u.got + len > u.total) return json(res, 400, { error: 'tamanho' });
    u.busy = true;
    const ws = fs.createWriteStream(u.fp, { flags: 'a', mode: 0o600 });
    let n = 0, dead = false;
    const die = (code, e) => { if (dead) return; dead = true; u.busy = false; ws.once('close', () => fs.truncate(u.fp, u.got, () => {})); ws.destroy(); if (!res.headersSent) json(res, code, { error: e, next: u.next }); };
    const abort = () => { r.ups.delete(upid); r.bytes -= u.total; fs.unlink(u.fp, () => {}); };
    req.on('data', ch => { n += ch.length; if (n > len) die(400, 'tamanho'); });
    req.on('close', () => { if (!req.complete) die(400, 'abortado'); });
    ws.on('error', () => die(500, 'disco'));
    ws.on('finish', () => {
      if (dead) return;
      if (n !== len || !r.peers.has(id)) return die(400, 'tamanho');
      u.got += n; u.next++; u.busy = false; u.t = Date.now();
      if (u.next < parts) return json(res, 200, { ok: true });
      if (u.got !== u.total) { abort(); return json(res, 400, { error: 'tamanho' }); }
      r.ups.delete(upid);
      const mt = clean(q.get('type'), 60).toLowerCase(), mime = INLINE.test(mt) ? mt : 'application/octet-stream';
      const fname = clean(q.get('name'), 100).replace(/[\\/:*?"<>|]/g, '_') || 'arquivo';
      r.files.set(upid, { name: fname, mime, size: u.total, p: u.fp });
      let re = null; try { const o = JSON.parse(q.get('re') || 'null'); if (o && typeof o === 'object') re = { id: clean(o.id, 16), name: clean(o.name, 24), text: clean(o.text, 80) }; } catch (e) {}
      const mid = clean(q.get('mid'), 16);
      const t = Date.now();
      r.hist.push({ k: 'f', name: c.name, mid, re, t, fid: upid, f: { name: fname, size: u.total, mime } }); if (r.hist.length > HIST_MAX) r.hist.shift();
      r.peers.forEach((pc, pid) => { if (pid !== id) push(pc, 'file', { name: c.name, mid, re, t, file: { name: fname, size: u.total, mime, u: '/f?room=' + room + '&id=' + pid + '&fid=' + upid + '&s=' + sign(room, upid, pid) } }); });
      json(res, 200, { ok: true, done: true });
    });
    return req.pipe(ws);
  }
  end(res, 404);
});
server.headersTimeout = 20000; server.requestTimeout = 600000; server.keepAliveTimeout = 65000;
server.listen(PORT, HOST, () => console.log('Resenha rodando em http://localhost:' + PORT + (SENHA ? '  (criar sala exige senha)' : '  (sem senha: defina SENHA=... pra proteger)')));

// quem some (sem poll aberto por GONE_MS) sai da sala; sala vazia por 15 min é apagada com seus arquivos
setInterval(() => {
  const now = Date.now();
  rooms.forEach((r, code) => {
    r.peers.forEach((c, id) => { if (!c.res && now - c.seen > GONE_MS) remove(r, id); });
    r.ups.forEach((u, k) => { if (now - u.t > 1800e3) { r.ups.delete(k); r.bytes -= u.total; fs.unlink(u.fp, () => {}); } });
    if (!r.peers.size && now - r.empty > EMPTY_MS) dropRoom(code);
  });
}, 10000);
const bye = () => { try { fs.rmSync(DIR, { recursive: true, force: true }); } catch (e) {} };
process.on('exit', bye);
['SIGINT', 'SIGTERM'].forEach(s => process.on(s, () => process.exit(0)));
process.on('uncaughtException', e => console.error(e)); // a sala não cai por um erro isolado
