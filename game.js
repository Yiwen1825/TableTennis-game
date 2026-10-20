// Yi Table Tennis YTT：物理、擊球辨識、電腦對手、球拍控制、畫面與 HUD
// 需要先載入 three.js r128（index.html 已處理）
(function(){
const T3 = window.THREE;
const $ = id => document.getElementById(id);
const app = $('app'), canvas = $('gl');

/* ---------------- 物理常數（公尺、秒、rad/s） ---------------- */
const R = 0.02, G = 9.81;
const KD = 0.126;      // 空氣阻力：a = -KD |v| v
const KL = 0.5 * 1.2 * Math.PI * 0.02 * 0.02 / 0.0027;   // 馬格努斯：a = KL·CL·v²，方向 ω × v
/* 升力係數隨「旋轉比」S = Rω/v 增加，但會飽和：轉速很高時力量增加得越來越慢 */
const liftCoef = S => 0.32 * S / (1 + 0.55 * S);
const SPIN_DECAY = 0.04;
const HL = 1.37, HW = 0.7625, NET_H = 0.1525, NET_W = 0.915, FLOOR = -0.76;
const E_TABLE = 0.89, MU_TABLE = 0.3, M = 0.0027, I = (2/3) * M * R * R; // 空心球殼
const DT = 0.001, TAU = Math.PI * 2;
const C_EAT = 0.004;   // （保留舊常數名稱）
/* 吃轉：來球旋轉讓回球偏掉的速度（m/s），轉越強偏越多，但會飽和，最多約 2 m/s */
const EAT_MAX = 2.0, EAT_W0 = 500;
const eatSat = x => Math.sign(x) * EAT_MAX * Math.tanh(Math.abs(x) / EAT_W0);
const LAMBDA = 0.95;   // 玩家刷球抵銷吃轉的效率
const MAXSPIN = 150;   // 擊球轉速上限 r/s（板型倍率前）
const SPIN_GAIN = 1.0;  // 整體旋轉倍率：各技術轉速已直接依真實數據設定
const BASE_SPEED = 0.8; // 整體球速倍率（整場節奏變慢，弧線形狀不變）

/* 板型：spin 製造上旋/側旋的能力、chop 製造下旋的能力、tempo 出球時間倍率（越小越快）、
   ctrl 落點誤差倍率（越小越穩）、eat 受來球旋轉影響的程度、keep 保留來球旋轉的比例（顆粒會把旋轉「反過來」） */
const RACKETS = {
  allround:  { name: '全能型',   mat: '五夾木＋標準反膠',   spin: 1.0,  chop: 1.0,  tempo: 1.0,  ctrl: 1.0,  eat: 1.0,  keep: 0,    color: 0xd22a3c,
               note: '各項平均，適合先熟悉旋轉。' },
  offense:   { name: '弧圈進攻', mat: '碳纖維板＋澀性反膠', spin: 1.25, chop: 0.9,  tempo: 0.8,  ctrl: 1.45, eat: 1.25, keep: 0,    color: 0xff4d2e,
               note: '球速快、上旋強，但對來球旋轉很敏感，落點也比較難控制。' },
  defense:   { name: '削球防守', mat: '削球板＋軟反膠',     spin: 0.85, chop: 1.4,  tempo: 1.25, ctrl: 0.7,  eat: 0.85, keep: 0,    color: 0x2f9e6a,
               note: '球速慢但很穩，往下切能削出極強的下旋。' },
  shortpips: { name: '正膠快攻', mat: '快攻板＋短顆粒',     spin: 0.6,  chop: 0.6,  tempo: 0.85, ctrl: 1.1,  eat: 0.5,  keep: 0,    color: 0x2f6fde,
               note: '轉不起來，但不太吃轉，適合彈打和快撥。' },
  longpips:  { name: '長顆粒',   mat: '防守板＋長顆粒',     spin: 0.25, chop: 0.45, tempo: 1.15, ctrl: 0.9,  eat: 0.2,  keep: 0.7,  color: 0x8a52e0,
               note: '自己幾乎轉不起來，會把來球的旋轉反過來送回去：你拉上旋，回來的是下旋。' },
  anti:      { name: '防弧膠',   mat: '防守板＋防弧膠皮',   spin: 0.2,  chop: 0.25, tempo: 1.2,  ctrl: 0.85, eat: 0.1,  keep: 0.12, color: 0xe0b52a,
               note: '摩擦力極低，幾乎不吃轉，也幾乎不轉，回球軟而不轉。' }
};
const RK_KEYS = Object.keys(RACKETS);

/* 電腦難度：f＝電腦擊球轉速佔真實數據的比例，serve＝發球轉速 r/s */
const LEVELS = {
  easy:   { f: 0.6, serve: 30, sigma: 0.16, skill: 0.5,  corner: 0.42 },
  normal: { f: 0.8, serve: 45, sigma: 0.10, skill: 0.75, corner: 0.58 },
  hard:   { f: 1.0, serve: 60, sigma: 0.05, skill: 0.9,  corner: 0.66 }
};

const clamp = (x, a, b) => Math.max(a, Math.min(b, x));
const lerp = (a, b, k) => a + (b - a) * k;
const rand = (a, b) => a + Math.random() * (b - a);
const other = s => s === 'P' ? 'A' : 'P';
function gauss(){ let u = 0, v = 0; while(!u) u = Math.random(); while(!v) v = Math.random(); return Math.sqrt(-2*Math.log(u)) * Math.cos(TAU*v); }

/* ---------------- 球的物理 ---------------- */
function bounceTable(s){
  const v = s.v, w = s.w;
  const Jn = M * (1 + E_TABLE) * (-v[1]);
  v[1] = -E_TABLE * v[1];
  // 接觸點切向速度 vc = v + ω × r，r = (0,-R,0)
  const vcx = v[0] + R * w[2];
  const vcz = v[2] - R * w[0];
  let Jx = -M * vcx / 2.5, Jz = -M * vcz / 2.5;   // 剛好轉為滾動所需的衝量
  const Jt = Math.hypot(Jx, Jz), Jmax = MU_TABLE * Jn;
  if (Jt > Jmax) { const k = Jmax / Jt; Jx *= k; Jz *= k; }
  v[0] += Jx / M; v[2] += Jz / M;
  w[0] += -R * Jz / I; w[2] += R * Jx / I;         // Δω = (r × J) / I
}

function stepBall(s, dt, collide, ev, t){
  const v = s.v, w = s.w, p = s.p;
  const sp = Math.hypot(v[0], v[1], v[2]);
  const wm = Math.hypot(w[0], w[1], w[2]);
  const km = (wm > 1e-6 && sp > 1e-6) ? KL * liftCoef(R * wm / sp) * sp / wm : 0;
  const ax = -KD*sp*v[0] + km*(w[1]*v[2] - w[2]*v[1]);
  const ay = -KD*sp*v[1] + km*(w[2]*v[0] - w[0]*v[2]) - G;
  const az = -KD*sp*v[2] + km*(w[0]*v[1] - w[1]*v[0]);
  v[0] += ax*dt; v[1] += ay*dt; v[2] += az*dt;
  const pz = p[2];
  p[0] += v[0]*dt; p[1] += v[1]*dt; p[2] += v[2]*dt;
  const d = 1 - SPIN_DECAY*dt; w[0] *= d; w[1] *= d; w[2] *= d;
  if (!collide) return;

  // 球網
  if ((pz > 0) !== (p[2] > 0) && Math.abs(p[0]) < NET_W && p[1] - R < NET_H && p[1] + R > 0) {
    if (p[1] > NET_H - 0.004) {          // 擦網
      v[0] *= 0.7; v[2] *= 0.55; v[1] = Math.abs(v[1]) * 0.3 + 0.45;
      if (ev) ev.push({ type: 'cord', x: p[0], z: p[2], t });
    } else {                             // 下網
      p[2] = pz > 0 ? R*0.6 : -R*0.6;
      v[2] *= -0.12; v[0] *= 0.3; v[1] *= 0.3; w[0] *= 0.3; w[1] *= 0.3; w[2] *= 0.3;
      if (ev) ev.push({ type: 'net', x: p[0], z: p[2], t });
    }
  }
  // 球台
  if (v[1] < 0 && p[1] < R && p[1] > -0.03 && Math.abs(p[0]) <= HW && Math.abs(p[2]) <= HL) {
    p[1] = R; bounceTable(s);
    if (ev) ev.push({ type: 'table', x: p[0], z: p[2], side: p[2] > 0 ? 'P' : 'A', t });
  }
  // 地板
  if (p[1] - R <= FLOOR && v[1] < 0) {
    p[1] = FLOOR + R;
    if (v[1] < -0.4) { v[1] *= -0.7; v[0] *= 0.8; v[2] *= 0.8; if (ev) ev.push({ type: 'floor', x: p[0], z: p[2], t }); }
    else { v[1] = 0; v[0] *= 0.97; v[2] *= 0.97; }
  }
  if (Math.abs(p[2]) > 7 || Math.abs(p[0]) > 6) {
    if ((v[0] || v[2]) && ev) ev.push({ type: 'floor', x: p[0], z: p[2], t });
    v[0] = v[1] = v[2] = 0; p[1] = FLOOR + R;
  }
}

function simulate(p, v, w, maxT, need){
  const s = { p: p.slice(), v: v.slice(), w: w.slice() }, ev = [];
  let t = 0;
  while (t < maxT) {
    stepBall(s, DT, true, ev, t); t += DT;
    let n = 0; for (const e of ev) if (e.type !== 'cord') n++;
    if (n >= need) break;
  }
  return ev.filter(e => e.type !== 'cord');
}
function flightAt(p, v, w, T){
  const s = { p: p.slice(), v: v.slice(), w: w.slice() };
  const n = Math.round(T / DT);
  for (let i = 0; i < n; i++) stepBall(s, DT, false, null, 0);
  return s.p;
}

/* 落點反解：給定旋轉與目標落點，迭代找出初速度 */
function solveFlight(p0, w, L, T){
  const v = [(L[0]-p0[0])/T, (L[1]-p0[1] + 0.5*G*T*T)/T, (L[2]-p0[2])/T];
  for (let i = 0; i < 30; i++) {
    const P = flightAt(p0, v, w, T);
    const ex = L[0]-P[0], ey = L[1]-P[1], ez = L[2]-P[2];
    if (Math.abs(ex) + Math.abs(ey) + Math.abs(ez) < 0.002) break;
    v[0] += ex/T; v[1] += ey/T; v[2] += ez/T;
  }
  return v;
}
/* 過網高度：球心越過 z=0 時，球底比網頂高多少（公尺） */
function flightInfo(p0, v, w){
  const s = { p: p0.slice(), v: v.slice(), w: w.slice() };
  let clear = -1, apex = p0[1];
  for (let i = 0; i < 2500; i++) {
    const pz = s.p[2];
    stepBall(s, DT, false, null, 0);
    if (s.p[1] > apex) apex = s.p[1];
    if ((pz > 0) !== (s.p[2] > 0)) { clear = s.p[1] - R - NET_H; }
    if (s.p[1] < R && clear !== -1) break;
  }
  return { clear, apex };
}
function landsOn(p0, v, w, L, recv){
  const e = simulate(p0, v, w, 2.5, 1)[0];
  return e && e.type === 'table' && e.side === recv && Math.hypot(e.x-L[0], e.z-L[2]) < 0.1;
}
/* 依「想要的過網高度」反解：過網越低，球越快越平；高球則要求頂點夠高 */
function solveRally(p0, w, L, wantClear, recv, lob){
  let fallback = null;
  if (lob) {
    for (let T = 1.0; T <= 1.6; T += 0.1) {
      const v = solveFlight(p0, w, L, T);
      if (!fallback) fallback = v;
      if (flightInfo(p0, v, w).apex > 0.8 && landsOn(p0, v, w, L, recv)) return v;
    }
    return fallback;
  }
  let lo = 0.18, hi = 1.1, best = null;
  for (let i = 0; i < 13; i++) {
    const T = (lo + hi) / 2;
    const v = solveFlight(p0, w, L, T);
    const c = flightInfo(p0, v, w).clear;
    if (c >= wantClear && Math.hypot(v[0], v[1], v[2]) < 24) { best = v; hi = T; } else lo = T;
  }
  if (best && landsOn(p0, best, w, L, recv)) return best;
  for (let T = hi; T <= 1.3; T += 0.05) {         // 低點擊球等特殊情況：慢慢拉高直到能過網
    const v = solveFlight(p0, w, L, T);
    if (!fallback) fallback = v;
    if (flightInfo(p0, v, w).clear >= 0.01 && landsOn(p0, v, w, L, recv)) return v;
  }
  return best || fallback;
}
function solveServe(p0, w, L, server){
  const recv = other(server);
  const vys = [-2.6, -3.2, -2.0, -3.8, -1.5, -4.4, -1.0];
  let best = null, bestErr = 1e9;
  for (const vy of vys) {
    let vx = (L[0]-p0[0]) / 0.75, vz = (L[2]-p0[2]) / 0.75;
    for (let i = 0; i < 40; i++) {
      const ev = simulate(p0, [vx, vy, vz], w, 2.2, 2);
      const c1 = ev[0], c2 = ev[1];
      if (!c1) { vx *= 0.85; vz *= 0.85; continue; }
      if (c1.type === 'net') { vx *= 0.9; vz *= 0.9; continue; }
      if (c1.type === 'table' && c1.side !== server) { vx *= 0.85; vz *= 0.85; continue; }
      if (c1.type !== 'table') {
        const behind = server === 'P' ? c1.z > HL - 0.01 : c1.z < -HL + 0.01;
        if (behind) { vx *= 1.25; vz *= 1.25; } else { vx *= 0.85; vz *= 0.85; }
        continue;
      }
      if (!c2) { vx *= 0.9; vz *= 0.9; continue; }
      if (c2.type === 'net') { vx *= 1.06; vz *= 1.06; continue; }
      const ex = L[0]-c2.x, ez = L[2]-c2.z, err = Math.hypot(ex, ez);
      if (c2.type === 'table' && c2.side === recv && err < bestErr) { bestErr = err; best = [vx, vy, vz]; }
      if (err < 0.02 && c2.type === 'table') break;
      vx += ex / c2.t * 0.9; vz += ez / c2.t * 0.9;
    }
    if (bestErr < 0.08) return best;
  }
  return best || [(L[0]-p0[0])/0.8, -1, (L[2]-p0[2])/0.8];
}

/* 吃轉：來球旋轉讓回球在 上下(ev) / 左右(el) 方向偏掉的速度 */
function computeEat(w, v, l){
  const sp = Math.hypot(v[0], v[1], v[2]) || 1;
  const d = [v[0]/sp, v[1]/sp, v[2]/sp];
  const cx = w[1]*d[2] - w[2]*d[1], cy = w[2]*d[0] - w[0]*d[2], cz = w[0]*d[1] - w[1]*d[0];
  const cm = Math.hypot(cx, cy, cz);
  if (cm < 1e-6) return { ev: 0, el: 0 };
  const k = eatSat(cm) / cm;
  return { ev: -k*cy, el: -k*(cx*l[0] + cz*l[2]) };
}
function reduce(e, c){ return e*c < 0 ? Math.sign(e) * Math.max(0, Math.abs(e) - Math.abs(c)) : e; }
/* 從玩家視角描述球的旋轉 */
function relSpin(w, v){
  const h = Math.hypot(v[0], v[2]) || 1, dx = v[0]/h, dz = v[2]/h;
  const top = (w[0]*dz - w[2]*dx) / TAU;
  const side = Math.abs(w[1]) / TAU;
  return { top, side: (w[1]*dz > 0) ? side : -side };
}
function spinLabel(top, side){
  const parts = [];
  if (Math.abs(top) < 3) parts.push('幾乎不轉');
  else parts.push((top > 0 ? '上旋 ' : '下旋 ') + Math.round(Math.abs(top)) + ' r/s');
  if (Math.abs(side) >= 3) parts.push('側旋 ' + Math.round(Math.abs(side)) + '（向' + (side > 0 ? '右' : '左') + '拐）');
  return parts.join(' · ');
}

/* ---------------- 遊戲狀態 ---------------- */
const ball = { p: [0,0,0], v: [0,0,0], w: [0,0,0] };
let phase = 'serveWait', server = 'P', firstServer = 'P';
let lastHitter = null, isServe = false, contacts = 0, awaitingHit = null, netTouched = false;
const score = { P: 0, A: 0 };
let aiTimer = 0, pointTimer = 0, pendingServe = null, gameOverFlag = false;
let level = 'normal', showHints = true, timeScale = BASE_SPEED;
let pRk = 'allround', aRkSel = 'allround', aRk = 'allround';
const evs = [];

function executeHit(h, o){
  const recv = other(h), dir = h === 'P' ? -1 : 1, l = [-dir, 0, 0];   // l：擊球者的右手方向
  const rk = o.rk || RACKETS.allround;
  const Tw = o.top * (o.top >= 0 ? rk.spin : rk.chop) * SPIN_GAIN * TAU, Sw = o.side * rk.spin * SPIN_GAIN * TAU;
  const w = [-l[0]*Tw, -Sw, 0];                                      // 上旋軸 = -l，側旋軸 = -y
  if (!o.isServe && rk.keep) { w[0] += rk.keep*ball.w[0]; w[1] += rk.keep*ball.w[1]; w[2] += rk.keep*ball.w[2]; }
  const sig = o.sigma * rk.ctrl;
  const L = [o.tx + gauss()*sig, R, o.tz + gauss()*sig*1.3];
  const p0 = ball.p.slice();
  let v, res = null, Eabs = 0;
  if (o.isServe) v = solveServe(p0, w, L, h);
  else {
    // 想要的過網高度：拉上旋可以過高一點再往下栽，搓下旋貼網走；快板型壓得更低，防守板型留更多空間
    const want = (o.want != null ? o.want : 0.045 + 0.0006*Math.max(0, o.top) - 0.0003*Math.max(0, -o.top)) * rk.tempo;
    v = solveRally(p0, w, L, Math.max(0.02, want), recv, !!o.lob);
    const e = computeEat(ball.w, ball.v, l);
    Eabs = Math.hypot(e.ev, e.el);
    let ev = e.ev * rk.eat, el = e.el * rk.eat;
    if (o.skill != null) { ev *= 1 - o.skill; el *= 1 - o.skill; }
    else { ev = reduce(ev, LAMBDA*eatSat(Tw)); el = reduce(el, LAMBDA*eatSat(Sw)); }
    if (o.comp) { ev *= 1 - (ev > 0 ? o.comp.up : o.comp.down); el *= 1 - o.comp.side; }
    v[0] += el*l[0]; v[1] += ev; v[2] += el*l[2];
    res = { ev, el };
  }
  const sp = Math.hypot(v[0], v[1], v[2]);
  if (sp > 30) { v[0] *= 30/sp; v[1] *= 30/sp; v[2] *= 30/sp; }
  ball.v = v; ball.w = w;
  lastHitter = h; isServe = !!o.isServe; contacts = 0; awaitingHit = null; netTouched = false; phase = 'rally';
  return { res, Eabs };
}

function currentServer(){
  const tot = score.P + score.A;
  if (score.P >= 10 && score.A >= 10) return tot % 2 === 0 ? firstServer : other(firstServer);
  return Math.floor(tot/2) % 2 === 0 ? firstServer : other(firstServer);
}
function setupServe(){
  server = currentServer(); phase = 'serveWait'; pendingServe = null;
  aRk = aRkSel === 'random' ? RK_KEYS[Math.floor(Math.random()*RK_KEYS.length)] : aRkSel;
  applyRacketLooks();
  lastHitter = null; awaitingHit = null; contacts = 0;
  const s = server === 'P' ? 1 : -1;
  // 玩家發球位置跟著滑鼠左右移動；電腦每次隨機站位
  const sx = server === 'P' ? serveX() : rand(-0.55, 0.55);
  ball.p = [sx, 0.18, s*(HL + 0.18)]; ball.v = [0,0,0]; ball.w = [0,0,0];
  aiTimer = 1.3;
  resetTrail();
  updateScore();
  if (server === 'A') { $('inMain').textContent = '—'; $('inSub').textContent = '電腦準備發球，注意看球的轉動'; $('inSub').className = 'sub'; }
}
function toss(){ phase = 'toss'; ball.v = [0, 2.4, 0]; ball.w = [0,0,0]; resetTrail(); updateScore(); }
/* 拿球的手在球拍左邊一點；可以站到球台兩側外一點點 */
function serveX(){ return clamp(bat.gx - 0.1, -HW - 0.12, HW + 0.12); }

function aiServe(){
  const lv = LEVELS[level], sgn = Math.random() < 0.5 ? -1 : 1;
  const menu = [
    { top: -lv.serve,     side: 0,                 z: [0.3, 0.55] },   // 下旋短球
    { top: -lv.serve*0.6, side: sgn*lv.serve*0.7,  z: [0.4, 0.85] },   // 側下旋
    { top: lv.serve*0.7,  side: 0,                 z: [0.95, 1.22] },  // 上旋長球
    { top: 0,            side: 0,              z: [0.6, 1.1] }     // 不轉
  ];
  const o = menu[Math.floor(Math.random()*menu.length)];
  aiStroke = '發球';
  aiSwing();
  executeHit('A', { top: o.top, side: o.side, tx: rand(-0.55, 0.55), tz: rand(o.z[0], o.z[1]), sigma: lv.sigma*0.5, isServe: true, rk: RACKETS[aRk] });
}
let aiStroke = '';
function aiHit(){
  const lv = LEVELS[level], f = lv.f;
  const mid = k => (SPIN_RANGE[k][0] + SPIN_RANGE[k][1]) / 2 * f * rand(0.85, 1.1);
  const tIn = relSpin(ball.w, ball.v).top * -1;   // 從電腦的視角看
  const short = ball.p[2] > -HL + 0.1;             // 球還在電腦的台內
  let top, tz = rand(0.45, 1.22), want = null, side = 0;
  if (short && tIn < -6 && Math.random() < 0.45) { top = -mid('push'); tz = rand(0.3, 0.5); want = 0.03; aiStroke = '擺短'; }
  else if (aRk === 'defense' && tIn > 6) { top = -mid('chop'); want = 0.1; aiStroke = '削球'; }
  else if (tIn < -6) {
    if (Math.random() < 0.55) { top = short ? mid('flick') : mid('loop'); aiStroke = short ? '挑球' : '拉球'; }
    else { top = -mid('push'); want = 0.03; aiStroke = '切球'; }
  } else if (tIn > 6) {
    const r = Math.random();
    if (r < 0.45) { top = mid('loop'); aiStroke = '拉球'; }
    else if (r < 0.75) { top = mid('block') * 0.6; want = 0.045; aiStroke = '擋球'; }
    else { top = -mid('chop'); want = 0.09; aiStroke = '削球'; }
  } else {
    if (Math.random() < 0.7) { top = mid('loop'); aiStroke = '拉球'; }
    else { top = mid('drive'); want = 0.04; aiStroke = '攻球'; }
  }
  side = (Math.random() - 0.5) * Math.abs(top) * 0.35;
  aiSwing();
  executeHit('A', { top, side, tx: rand(-lv.corner, lv.corner), tz, sigma: lv.sigma, isServe: false, skill: lv.skill, rk: RACKETS[aRk], want });
}

/* ---------------- 擊球技術辨識 ----------------
   依揮拍方向與速度、正反手、擊球當下球在台內或台外、高或低，判斷是哪一種技術 */
const REACH = 0.105;
const STROKES = { loop: '拉球', flick: '挑球', twist: '擰球', push: '切球', chop: '削球', smash: '扣殺', block: '擋球', drive: '攻球', punch: '快撥' };
function classifyStroke(sp, vx, vy){
  const z = ball.p[2], y = ball.p[1];
  const overTable = z < HL - 0.05;         // 球還在台內（短球）
  const deep = z > HL + 0.3;               // 已經退到台外
  const high = y > 0.32;                   // 高球
  if (sp < 0.8) return 'block';
  if (high && z < HL + 0.5 && sp > 3.5) return 'smash';
  if (overTable && !pose.fore && vx > 0.8 && vy > -0.3 && sp > 1.2) return 'twist';
  if (overTable && vy > 0.6 && sp > 1.2 && sp < 5) return 'flick';
  if (vy > 1.8 && sp > 2.5) return 'loop';
  if (vy < -1.5 && sp > 2.5 && deep) return 'chop';
  if (vy < -0.4) return 'push';
  return pose.fore ? 'drive' : 'punch';
}
/* 各技術轉速（r/s）參考真實數據：揮拍越快越接近範圍上限
   拉球 110–150｜擰球 90–120｜削球 60–90｜切球 50–75｜挑球 40–75｜快撥 30–60｜攻球 20–50｜擋球 15–40｜扣殺 5–20 */
const SPIN_RANGE = {
  loop: [110, 150], twist: [90, 120], chop: [60, 90], push: [50, 75], flick: [40, 75],
  punch: [30, 60], drive: [20, 50], block: [15, 40], smash: [5, 20]
};
function rangeSpin(type, t){ const r = SPIN_RANGE[type]; return r[0] + (r[1] - r[0]) * clamp(t, 0, 1); }
function strokeParams(type, sp, vx, vy, pw, inTop){
  const dirX = sp > 0.4 ? vx / sp : 0;
  let top, side = clamp(vx * 5, -30, 30), depth, want, sig = 1;
  switch (type) {
    case 'loop':  top = rangeSpin('loop', (sp - 2.5) / 4.5);                                                   // 弧圈：極強上旋，往下栽
                  depth = 0.85 + 0.4*pw; want = 0.07; break;
    case 'flick': top = rangeSpin('flick', (sp - 1.2) / 3.8); depth = 0.85 + 0.35*pw; want = 0.035; sig = 1.1; break; // 台內上挑
    case 'twist': { const T = rangeSpin('twist', (sp - 1.2) / 3);                                               // 擰拉：強烈側上旋
                  top = T * 0.8; side = T * 0.6; depth = 0.8 + 0.4*pw; want = 0.04; sig = 1.15; break; }
    case 'push':  top = -rangeSpin('push', (sp - 0.4) / 3); side = clamp(vx*3, -15, 15); want = 0.045; sig = 0.8; // 輕切擺短，大力一點變劈長
                  depth = sp < 1.8 ? 0.3 + 0.15*sp/1.8 : 0.9 + 0.3*Math.min(1, (sp - 1.8)/2); break;
    case 'chop':  top = -Math.min(95, rangeSpin('chop', (sp - 2.5) / 4.5) + 0.2*Math.max(0, inTop));            // 削球：借對方上旋反轉成強下旋
                  side = clamp(vx*4, -20, 20); depth = 0.95 + 0.3*pw; want = 0.11; sig = 0.75; break;
    case 'smash': top = rangeSpin('smash', (sp - 3.5) / 5); side = clamp(vx*2, -10, 10);                       // 扣殺：幾乎不轉
                  depth = 0.9 + 0.2*pw; want = 0.015; sig = 1.25; break;
    case 'block': { const mag = clamp(Math.abs(inTop) * 0.3, 15, 40);                                          // 擋球：轉速取決於來球
                  top = (inTop < -5 ? -1 : 1) * mag; side = 0; depth = 0.7 + 0.45*pw; want = 0.045; sig = 0.9; break; }
    case 'punch': top = rangeSpin('punch', (sp - 0.8) / 4); depth = 0.7 + 0.5*pw; want = 0.04; break;        // 快撥：速度大於旋轉
    default:      top = rangeSpin('drive', (sp - 0.8) / 5); depth = 0.7 + 0.5*pw; want = 0.04;               // 攻球：撞擊為主
  }
  const tx = clamp(ball.p[0]*0.35 + dirX*0.6*Math.min(1, sp/2.5), -0.66, 0.66);
  // 每種技術本身的拍面角度能吃住多少來球旋轉：up＝對上旋（會往上飛）、down＝對下旋（會往下掉）
  const COMP = {
    loop:  { up: 0.85, down: 0,   side: 0.3 },   // 對下旋靠往上摩擦抵銷；對拉（反拉）要蓋拍
    flick: { up: 0.3, down: 0.3,  side: 0.3 },
    twist: { up: 0.3, down: 0.45, side: 0.55 },
    push:  { up: 0,   down: 0.95, side: 0.3 },   // 開拍吃下旋很穩，但搓上旋會冒高
    chop:  { up: 0.6, down: 0.5,  side: 0.3 },
    smash: { up: 0.6, down: 0.6,  side: 0.3 },
    block: { up: 0.7, down: 0,    side: 0.3 },   // 蓋拍擋上旋很穩，擋下旋會下網
    drive: { up: 0.5, down: 0.2,  side: 0.3 },
    punch: { up: 0.5, down: 0.2,  side: 0.3 }
  };
  return { top, side, tz: -Math.min(depth, 1.27), tx, want, sig, comp: COMP[type] };
}
function serveName(top, side, power){
  const len = power < 0.35 ? '短' : power > 0.65 ? '長' : '';
  let t;
  if (Math.abs(side) > 20) t = top < -15 ? '側下旋' : top > 15 ? '側上旋' : '側旋';
  else t = top < -15 ? '下旋' : top > 15 ? '上旋' : '不轉';
  return len + t + '發球';
}
function playerContact(off, serve){
  const sp = Math.hypot(bat.vx, bat.vy), rk = RACKETS[pRk];
  const vx = bat.vx, vy = bat.vy;
  const power = clamp(sp / 7, 0, 1);
  bat.flash = 0.18;
  if (serve) {
    let top = clamp(vy * 14, -80, 80), side = clamp(vx * 10, -60, 60);
    if (sp < 0.8) { top *= 0.4; side *= 0.4; }
    const dirX = sp > 0.4 ? vx / sp : 0;
    const tz = -(0.3 + 0.95*power), tx = clamp(ball.p[0]*0.3 + dirX*0.55, -0.62, 0.62);
    executeHit('P', { top, side, tx, tz, sigma: 0.03 + 0.05*off, isServe: true, rk });
    const name = serveName(top, side, power);
    toast(name);
    showShot(null, null, true, sp, off, name);
    return;
  }
  const inc = Math.hypot(ball.v[0], ball.v[1], ball.v[2]);
  const pw = Math.max(power, clamp(inc / 16, 0, 0.7));        // 擋快球時借力
  let q = 1 - Math.min(1, Math.abs(ball.v[1] + 0.3) / 3.2);
  if (ball.p[1] < 0.02) q *= 0.6;
  if (off > 0.65) q *= 1 - (off - 0.65) / 0.35 * 0.6;         // 打到拍緣
  const lob = shiftDown || lobOn;
  const type = classifyStroke(sp, vx, vy);
  const inTop = relSpin(ball.w, ball.v).top;                  // 來球的上旋（負值＝下旋），擋球、削球會借它
  const sk = strokeParams(type, sp, vx, vy, pw, inTop);
  const name = lob ? '放高球' : (pose.fore ? '正手' : '反手') + STROKES[type];
  const info = executeHit('P', { top: sk.top, side: sk.side, tx: sk.tx, tz: sk.tz, sigma: (0.025 + 0.22*(1 - q)) * sk.sig, isServe: false, rk, lob, want: sk.want, comp: sk.comp });
  if (lobOn) setLob(false);
  toast(name);
  showShot(q, info, false, sp, off, name);
}
function batContact(frac){
  const canRally = phase === 'rally' && awaitingHit === 'P' && ball.p[2] > -0.05 && ball.p[1] > -0.3;
  const canServe = phase === 'toss' && server === 'P' && ball.v[1] < 0.6;
  if (!canRally && !canServe) return;
  const x = lerp(bat.px, bat.x, frac), y = lerp(bat.py, bat.y, frac);
  // 用畫面判定：畫面上拍面蓋到球就算打到（不管球在台內多遠）
  const w = canvas.clientWidth || 1, h = canvas.clientHeight || 1;
  _pa.set(x, y, bat.z).project(camera);
  _pb.set(ball.p[0], ball.p[1], ball.p[2]).project(camera);
  _pc.set(x + REACH * bat.s, y, bat.z).project(camera);
  if (_pb.z > 1 || _pa.z > 1) return;                       // 在鏡頭後面
  const r = Math.abs(_pc.x - _pa.x) * w / 2;
  const d = Math.hypot((_pb.x - _pa.x) * w / 2, (_pb.y - _pa.y) * h / 2);
  if (d < r) playerContact(d / r, canServe);
}
const _pa = new T3.Vector3(), _pb = new T3.Vector3(), _pc = new T3.Vector3();

const TXT = {
  net:   ['你的球下網', '電腦下網'],
  out:   ['你的球出界', '電腦出界'],
  own:   ['你的球打在自己這邊', '電腦打在自己那邊'],
  miss:  ['你沒接到', '電腦沒接到'],
  serve: ['發球失誤', '電腦發球失誤']
};
function pointTo(winner, kind){
  const loser = other(winner);
  score[winner]++;
  phase = 'pointOver'; pointTimer = 1.6; awaitingHit = null;
  banner(winner === 'P' ? '得分' : '失分', TXT[kind][loser === 'P' ? 0 : 1], winner === 'P' ? 'win' : 'lose');
  if ((score.P >= 11 || score.A >= 11) && Math.abs(score.P - score.A) >= 2) { gameOverFlag = true; pointTimer = 1.8; }
  updateScore();
}
function onEvent(e){
  const h = lastHitter, r = other(h);
  if (e.type === 'cord') { netTouched = true; toast('擦網！'); return; }
  if (e.type === 'net') { netTouched = true; return; }
  if (e.type === 'table') {
    contacts++;
    if (isServe) {
      if (contacts === 1) { if (e.side !== h) return pointTo(r, 'serve'); }
      else if (contacts === 2) { if (e.side !== r) return pointTo(r, 'serve'); awaitingHit = r; }
      else return pointTo(h, 'miss');
    } else {
      if (contacts === 1) { if (e.side !== r) return pointTo(r, netTouched ? 'net' : 'own'); awaitingHit = r; }
      else return pointTo(h, 'miss');
    }
    return;
  }
  if (e.type === 'floor') {
    if (awaitingHit === r) return pointTo(h, 'miss');
    if (isServe) return pointTo(r, 'serve');
    return pointTo(r, netTouched ? 'net' : 'out');
  }
}

function physicsStep(frac){
  if (phase === 'serveWait') {
    if (server === 'A') { aiTimer -= DT; if (aiTimer <= 0) toss(); }
    return;
  }
  stepBall(ball, DT, true, evs, 0);
  for (const e of evs) if (e.type === 'table') spawnMarker(e.x, e.z);
  if (phase === 'toss') {
    evs.length = 0;
    if (ball.v[1] < 0 && ball.p[1] <= 0.24) {
      if (server === 'A') aiServe();
    }
    if (phase === 'toss') batContact(frac);
    if (phase === 'toss' && ball.p[1] < -0.1) { toast('沒擊到球，重新拋球'); setupServe(); }
    return;
  }
  if (phase === 'rally') {
    for (const e of evs) { onEvent(e); if (phase !== 'rally') break; }
    evs.length = 0;
    if (phase === 'rally' && awaitingHit === 'A') {
      if ((ball.v[1] <= 0 && ball.p[1] > 0.03) || ball.p[2] < -HL - 0.3) { if (ball.p[1] > -0.3) aiHit(); }
    }
    if (phase === 'rally') batContact(frac);
    return;
  }
  evs.length = 0;
  if (phase === 'pointOver') {
    pointTimer -= DT;
    if (pointTimer <= 0) {
      if (gameOverFlag) showGameOver(); else setupServe();
    }
  }
}

/* ---------------- 3D 場景 ---------------- */
const renderer = new T3.WebGLRenderer({ canvas, antialias: true });
renderer.setPixelRatio(Math.min(2, window.devicePixelRatio || 1));
const scene = new T3.Scene();
scene.background = new T3.Color(0x0d1220);
scene.fog = new T3.Fog(0x0d1220, 6, 15);
const camera = new T3.PerspectiveCamera(48, 1, 0.05, 50);
scene.add(new T3.HemisphereLight(0xd4ddff, 0x3a1a1e, 0.8));
const sun = new T3.DirectionalLight(0xffffff, 0.8); sun.position.set(1.2, 4, 2.5); scene.add(sun);

const floor = new T3.Mesh(new T3.PlaneGeometry(30, 30), new T3.MeshLambertMaterial({ color: 0x24131a }));
floor.rotation.x = -Math.PI/2; floor.position.y = FLOOR; scene.add(floor);
const court = new T3.Mesh(new T3.PlaneGeometry(7, 12), new T3.MeshLambertMaterial({ color: 0x6a2630 }));
court.rotation.x = -Math.PI/2; court.position.y = FLOOR + 0.001; scene.add(court);
const barrierMat = new T3.MeshLambertMaterial({ color: 0x1c2b56 });
for (const z of [-6, 6]) { const b = new T3.Mesh(new T3.BoxGeometry(7, 0.7, 0.04), barrierMat); b.position.set(0, FLOOR + 0.35, z); scene.add(b); }
for (const x of [-3.5, 3.5]) { const b = new T3.Mesh(new T3.BoxGeometry(0.04, 0.7, 12), barrierMat); b.position.set(x, FLOOR + 0.35, 0); scene.add(b); }

const tableTop = new T3.Mesh(new T3.BoxGeometry(HW*2, 0.03, HL*2), new T3.MeshLambertMaterial({ color: 0x2457b8 }));
tableTop.position.y = -0.015; scene.add(tableTop);
const lineMat = new T3.MeshBasicMaterial({ color: 0xf2f5fb });
function lineRect(w, l, x, z){ const m = new T3.Mesh(new T3.PlaneGeometry(w, l), lineMat); m.rotation.x = -Math.PI/2; m.position.set(x, 0.0008, z); scene.add(m); }
lineRect(0.02, HL*2, -HW + 0.01, 0); lineRect(0.02, HL*2, HW - 0.01, 0);
lineRect(HW*2, 0.02, 0, HL - 0.01); lineRect(HW*2, 0.02, 0, -HL + 0.01);
lineRect(0.003, HL*2, 0, 0);
const legMat = new T3.MeshLambertMaterial({ color: 0x1f2436 });
for (const sx of [-1, 1]) for (const sz of [-1, 1]) {
  const g = new T3.Mesh(new T3.BoxGeometry(0.05, 0.73, 0.05), legMat);
  g.position.set(sx*(HW - 0.12), -0.395, sz*(HL - 0.25)); scene.add(g);
}
const nc = document.createElement('canvas'); nc.width = nc.height = 16;
const ng = nc.getContext('2d'); ng.fillStyle = 'rgba(20,26,40,0.25)'; ng.fillRect(0,0,16,16);
ng.strokeStyle = 'rgba(14,18,30,0.95)'; ng.lineWidth = 2; ng.strokeRect(0,0,16,16);
const netTex = new T3.CanvasTexture(nc); netTex.wrapS = netTex.wrapT = T3.RepeatWrapping; netTex.repeat.set(90, 8);
const net = new T3.Mesh(new T3.PlaneGeometry(NET_W*2, NET_H), new T3.MeshBasicMaterial({ map: netTex, transparent: true, side: T3.DoubleSide, depthWrite: false }));
net.position.set(0, NET_H/2, 0); scene.add(net);
const tape = new T3.Mesh(new T3.BoxGeometry(NET_W*2, 0.012, 0.004), new T3.MeshBasicMaterial({ color: 0xf2f5fb }));
tape.position.set(0, NET_H - 0.006, 0); scene.add(tape);
for (const x of [-NET_W, NET_W]) { const pst = new T3.Mesh(new T3.BoxGeometry(0.02, 0.17, 0.03), legMat); pst.position.set(x, 0.085, 0); scene.add(pst); }

function ballTexture(){
  const c = document.createElement('canvas'); c.width = 256; c.height = 128;
  const g = c.getContext('2d');
  g.fillStyle = '#ff8a2a'; g.fillRect(0, 0, 256, 128);
  g.fillStyle = '#fff3e4'; g.fillRect(0, 0, 22, 128); g.fillRect(128, 0, 22, 128);
  g.fillStyle = '#2a1406'; g.beginPath(); g.arc(70, 64, 14, 0, TAU); g.fill();
  return new T3.CanvasTexture(c);
}
const ballMesh = new T3.Mesh(new T3.SphereGeometry(0.024, 24, 16), new T3.MeshLambertMaterial({ map: ballTexture(), emissive: 0x3a1800 }));
scene.add(ballMesh);
const shadow = new T3.Mesh(new T3.CircleGeometry(0.03, 20), new T3.MeshBasicMaterial({ color: 0x000000, transparent: true, opacity: 0.4, depthWrite: false }));
shadow.rotation.x = -Math.PI/2; scene.add(shadow);

const TN = 42;
const tPos = new Float32Array(TN*3), tCol = new Float32Array(TN*3);
for (let i = 0; i < TN; i++) { const k = Math.pow(1 - i/TN, 1.6); tCol[i*3] = 1.0*k; tCol[i*3+1] = 0.55*k; tCol[i*3+2] = 0.18*k; }
const trailGeo = new T3.BufferGeometry();
trailGeo.setAttribute('position', new T3.BufferAttribute(tPos, 3));
trailGeo.setAttribute('color', new T3.BufferAttribute(tCol, 3));
const trail = new T3.Line(trailGeo, new T3.LineBasicMaterial({ vertexColors: true, transparent: true, blending: T3.AdditiveBlending, depthWrite: false }));
trail.frustumCulled = false; scene.add(trail);
function resetTrail(){ for (let i = 0; i < TN; i++) { tPos[i*3] = ball.p[0]; tPos[i*3+1] = ball.p[1]; tPos[i*3+2] = ball.p[2]; } trailGeo.attributes.position.needsUpdate = true; }

const reticle = new T3.Group();
const ring = new T3.Mesh(new T3.RingGeometry(0.045, 0.058, 36), new T3.MeshBasicMaterial({ color: 0xff8a2a, transparent: true, opacity: 0.95, depthWrite: false }));
const dot = new T3.Mesh(new T3.CircleGeometry(0.01, 16), new T3.MeshBasicMaterial({ color: 0xff8a2a, transparent: true, opacity: 0.95, depthWrite: false }));
ring.rotation.x = dot.rotation.x = -Math.PI/2;
reticle.add(ring); reticle.add(dot); reticle.visible = false; scene.add(reticle);

const markers = [];
for (let i = 0; i < 6; i++) {
  const m = new T3.Mesh(new T3.RingGeometry(0.02, 0.03, 28), new T3.MeshBasicMaterial({ color: 0xffffff, transparent: true, opacity: 0, depthWrite: false }));
  m.rotation.x = -Math.PI/2; m.visible = false; scene.add(m);
  markers.push({ m, life: 0 });
}
let markerIdx = 0;
function spawnMarker(x, z){ const k = markers[markerIdx++ % markers.length]; k.life = 1.4; k.m.position.set(x, 0.0012, z); k.m.visible = true; }

/* 球拍：外層負責拍面的開合（pitch）與左右轉向（yaw），內層 roll 負責握拍方向（拍柄朝哪裡） */
/* 握柄貼圖：紅色側片＋中間木紋條＋細線，底部一個金色圓徽（不放任何品牌字樣） */
function handleTexture(){
  const c = document.createElement('canvas'); c.width = 64; c.height = 256;
  const g = c.getContext('2d');
  g.fillStyle = '#c4203a'; g.fillRect(0, 0, 64, 256);
  const grd = g.createLinearGradient(0, 0, 64, 0);
  grd.addColorStop(0, 'rgba(0,0,0,0.25)'); grd.addColorStop(0.5, 'rgba(255,255,255,0.08)'); grd.addColorStop(1, 'rgba(0,0,0,0.25)');
  g.fillStyle = grd; g.fillRect(0, 0, 64, 256);
  g.fillStyle = '#e4c38e'; g.fillRect(22, 0, 20, 256);                 // 中間木紋條
  g.strokeStyle = 'rgba(150,100,50,0.35)'; g.lineWidth = 1;
  for (let x = 24; x < 42; x += 3) { g.beginPath(); g.moveTo(x, 0); g.lineTo(x + 1, 256); g.stroke(); }
  g.fillStyle = '#3a1c10'; g.fillRect(20, 0, 2, 256); g.fillRect(42, 0, 2, 256);
  g.fillStyle = '#f4ead8'; g.fillRect(17, 0, 1.5, 256); g.fillRect(45.5, 0, 1.5, 256);
  g.fillStyle = '#c99a2e'; g.beginPath(); g.arc(32, 214, 11, 0, TAU); g.fill();   // 金色圓徽
  g.strokeStyle = '#6b4a12'; g.lineWidth = 2; g.beginPath(); g.arc(32, 214, 8, 0, TAU); g.stroke();
  g.fillStyle = '#e8c55a'; g.beginPath(); g.arc(32, 214, 4, 0, TAU); g.fill();
  const t = new T3.CanvasTexture(c);
  return t;
}
const HANDLE_TEX = handleTexture();
/* 木板貼圖：淺色木頭加直向木紋 */
function woodTexture(){
  const c = document.createElement('canvas'); c.width = 128; c.height = 128;
  const g = c.getContext('2d');
  g.fillStyle = '#d2a468'; g.fillRect(0, 0, 128, 128);
  for (let i = 0; i < 26; i++) {
    const x = Math.random() * 128, w = 0.6 + Math.random() * 1.6;
    g.strokeStyle = `rgba(${120 + Math.random()*30|0},${78 + Math.random()*20|0},40,${0.18 + Math.random()*0.25})`;
    g.lineWidth = w; g.beginPath(); g.moveTo(x, 0);
    g.bezierCurveTo(x + 3, 40, x - 3, 88, x + 1, 128); g.stroke();
  }
  return new T3.CanvasTexture(c);
}
const WOOD_TEX = woodTexture();
/* 球拍：外層負責拍面的開合（pitch）與左右轉向（yaw），內層 roll 負責握拍方向（拍柄朝哪裡） */
function makeRacket(color, opacity){
  const tr = opacity < 1;
  const outer = new T3.Group(), roll = new T3.Group();
  outer.add(roll);
  const mats = [];
  // 拍頭可半透明（方便看到後面的球），拍頸和握柄永遠不透明
  const M = (c, extra) => { const m = new T3.MeshPhongMaterial(Object.assign({ color: c, transparent: tr, opacity, shininess: 12, specular: 0x222222 }, extra || {})); mats.push(m); return m; };
  const S = (c, extra) => new T3.MeshPhongMaterial(Object.assign({ color: c, shininess: 18, specular: 0x333333 }, extra || {}));
  // 木板：拍頭（橢圓，寬 15 cm、高 16 cm）和拍肩是同一片木頭，拍肩從拍頭兩側收窄接到握柄
  const RX = 0.0765, RY = 0.08, deg = Math.PI / 180;
  const blade = new T3.Shape();
  blade.moveTo(-0.0135, -0.092);
  blade.quadraticCurveTo(-0.0160, -0.080, RX*Math.cos(245*deg), RY*Math.sin(245*deg));
  blade.absellipse(0, 0, RX, RY, 245*deg, 295*deg, true);
  blade.quadraticCurveTo(0.0160, -0.080, 0.0135, -0.092);
  blade.closePath();
  const woodTex = WOOD_TEX.clone(); woodTex.needsUpdate = true;
  woodTex.repeat.set(1/0.17, 1/0.2); woodTex.offset.set(0.5, 0.56);
  const bladeMesh = new T3.Mesh(new T3.ExtrudeGeometry(blade, { depth: 0.0058, bevelEnabled: false, curveSegments: 48 }),
    [M(0xffffff, { map: woodTex }), M(0x9c6c3a)]);
  bladeMesh.position.z = -0.0029; roll.add(bladeMesh);
  // 膠皮：只蓋拍頭，底部平切，露出下面的木頭拍肩
  const rr = 0.9935, cutY = -0.0735, a0 = Math.asin(cutY / (RY*rr));
  const rubShape = new T3.Shape();
  rubShape.moveTo(RX*rr*Math.cos(Math.PI - a0), cutY);
  rubShape.absellipse(0, 0, RX*rr, RY*rr, Math.PI - a0, 2*Math.PI + a0, true);
  rubShape.closePath();
  const rubGeo = new T3.ExtrudeGeometry(rubShape, { depth: 0.0032, bevelEnabled: false, curveSegments: 48 });
  const front = new T3.Mesh(rubGeo, M(0x16171b, { shininess: 30 })); front.position.z = 0.0029; roll.add(front);       // 朝向自己：黑色
  const back = new T3.Mesh(rubGeo, M(0xb3172c, { shininess: 30 })); back.position.z = -0.0029 - 0.0032; roll.add(back); // 另一面：紅色
  // 邊條：沿著拍頭外緣，到拍肩為止（顏色＝板型顏色）
  const tapeCurve = new T3.EllipseCurve(0, 0, RX + 0.0008, RY + 0.0008, Math.PI - a0 + 0.04, 2*Math.PI + a0 - 0.04, true);
  const pts = tapeCurve.getPoints(60).map(q => new T3.Vector3(q.x, q.y, 0));
  const tape = M(color);
  const tapeMesh = new T3.Mesh(new T3.TubeGeometry(new T3.CatmullRomCurve3(pts), 80, 0.0044, 6, false), tape);
  tapeMesh.scale.z = 1.4; roll.add(tapeMesh);
  // 握柄：喇叭形（FL），從拍肩往下越來越寬
  const L = 0.1, hs = new T3.Shape();
  hs.moveTo(-0.0165, 0);
  hs.quadraticCurveTo(-0.0175, 0.008, -0.0145, 0.03);
  hs.lineTo(-0.0132, L); hs.lineTo(0.0132, L); hs.lineTo(0.0145, 0.03);
  hs.quadraticCurveTo(0.0175, 0.008, 0.0165, 0);
  hs.quadraticCurveTo(0, -0.004, -0.0165, 0);
  const hGeo = new T3.ExtrudeGeometry(hs, { depth: 0.02, bevelEnabled: true, bevelThickness: 0.002, bevelSize: 0.0018, bevelSegments: 2, curveSegments: 8 });
  const tex = HANDLE_TEX.clone(); tex.needsUpdate = true;
  tex.repeat.set(1 / 0.036, 1 / L); tex.offset.set(0.5, 0);
  const hMesh = new T3.Mesh(hGeo, [S(0xffffff, { map: tex }), S(0xb07a45)]);
  hMesh.position.set(0, -0.088 - L, -0.01); roll.add(hMesh);
  scene.add(outer);
  outer.userData = { roll, rubber: tape, mats };
  return outer;
}
const pr = { g: makeRacket(0xd22a3c, 0.85), swing: null };
const ar = { g: makeRacket(0xd22a3c, 1), swing: null };
pr.g.position.set(0.3, 0.1, HL + 0.3); ar.g.position.set(0, 0.12, -HL - 0.3);
ar.g.userData.roll.rotation.z = 0.64;                 // 電腦正手握拍
/* 玩家球拍姿勢：位置在身體右邊用正手、左邊用反手；揮拍方向決定拍面角度 */
const BODY_X = -0.05;
const pose = { roll: -0.64, pitch: -0.15, yaw: 0, fore: true };
/* 球拍（含拍頭寬度）是否在球台正上方 */
function racketOverTable(x, z){ return Math.abs(x) < HW + 0.09 && Math.abs(z) < HL + 0.02; }
/* 拍面中心到整支球拍最低點的垂直距離（依握拍方向 roll 和拍面傾角 pitch） */
function racketDrop(roll, pitch){
  const s = Math.abs(Math.sin(roll)), c = Math.cos(roll);
  const head = Math.sqrt((0.0765*s)**2 + (0.08*c)**2) + 0.0055;   // 含邊條厚度
  const handle = 0.19 * c + 0.017 * s;                             // 握柄尾端
  return Math.max(head, handle) * Math.abs(Math.cos(pitch)) + 0.012 * Math.abs(Math.sin(pitch));
}
function updatePlayerPose(dt){
  // 用握柄（手）的位置判斷正反手，避免拍面翻過去造成來回切換
  if (pose.fore && bat.gx < BODY_X - 0.025) { pose.fore = false; pose.switching = true; }
  else if (!pose.fore && bat.gx > BODY_X + 0.025) { pose.fore = true; pose.switching = true; }
  const vx = bat.vx, vy = bat.vy;
  // 握拍：正手拍柄指向左下（朝身體），反手拍柄指向右邊；橫向揮拍時手腕會帶著轉
  let roll = pose.fore ? -0.64 : 1.15;
  // 在球台上方、手放低時，手腕放平：拍柄轉成水平，拍頭才伸得到台內的低球
  if (racketOverTable(bat.gx, bat.z)) {
    const low = clamp((0.26 - bat.gy) / 0.2, 0, 1);
    roll = lerp(roll, pose.fore ? -1.45 : 1.45, low);
  }
  roll += clamp(vx * 0.05, -0.45, 0.45);
  // 拍面：往上拉時前傾蓋拍，往下切時後仰開拍，平常微蓋
  let pitch = -0.15;
  if (vy > 0) pitch -= clamp(vy * 0.11, 0, 0.75);
  else pitch += clamp(-vy * 0.14, 0, 0.95);
  // 左右揮：拍面朝揮拍方向轉
  const yaw = -clamp(vx * 0.07, -0.6, 0.6) + (pose.fore ? -0.12 : 0.12);
  // 揮出去時快速到位，收拍時慢慢回來，看起來像有隨揮動作
  const ease = (cur, tgt, base) => lerp(cur, tgt, Math.min(1, dt * (Math.abs(tgt - base) > Math.abs(cur - base) ? 22 : 6)));
  // 正反手切換時直接快速翻拍，不走收拍的慢速
  if (pose.switching) {
    pose.roll = lerp(pose.roll, roll, Math.min(1, dt * 28));
    if (Math.abs(pose.roll - roll) < 0.05) pose.switching = false;
  } else pose.roll = ease(pose.roll, roll, pose.fore ? -0.64 : 1.15);
  pose.pitch = ease(pose.pitch, pitch, -0.15);
  pose.yaw = ease(pose.yaw, yaw, 0);
  pr.g.rotation.order = 'YXZ';
  pr.g.rotation.set(pose.pitch, pose.yaw, 0);
  pr.g.userData.roll.rotation.z = pose.roll;
}

function playerSwing(sw, atBall){
  const b = atBall ? ball.p : [pr.g.position.x, pr.g.position.y, pr.g.position.z];
  const sx = sw.sx, sy = sw.sy;
  pr.swing = { t: 0, dur: 0.16, hold: 0,
    from: [b[0] - sx*0.18, b[1] - sy*0.14, b[2] + 0.12],
    to:   [b[0] + sx*0.18, b[1] + sy*0.14, b[2] - 0.08] };
  pr.g.rotation.x = -sy * 0.5; pr.g.rotation.z = -sx * 0.3;
}
function aiSwing(){
  const b = ball.p;
  ar.swing = { t: 0, dur: 0.16, hold: 0, from: [b[0], b[1] - 0.1, b[2] - 0.12], to: [b[0], b[1] + 0.1, b[2] + 0.08] };
}
function updRacket(r, idle, dt){
  const p = r.g.position;
  if (r.swing) {
    const s = r.swing; s.t += dt;
    const k = Math.min(1, s.t / s.dur), e = 1 - Math.pow(1 - k, 3);
    p.set(lerp(s.from[0], s.to[0], e), lerp(s.from[1], s.to[1], e), lerp(s.from[2], s.to[2], e));
    if (k >= 1) { s.hold += dt; if (s.hold > 0.25) r.swing = null; }
  } else {
    const k = Math.min(1, dt * 9);
    p.x += (idle[0] - p.x) * k; p.y += (idle[1] - p.y) * k; p.z += (idle[2] - p.z) * k;
    r.g.rotation.x *= 1 - k; r.g.rotation.z *= 1 - k;
  }
}

function resize(){
  const w = app.clientWidth || 1, h = app.clientHeight || 1;
  renderer.setSize(w, h, false);
  camera.aspect = w / h;
  if (w / h < 0.8) { camera.fov = 70; camBase.pos = [0, 1.25, 3.3]; camBase.look = [0, -0.1, -0.35]; }
  else { camera.fov = 50; camBase.pos = [0, 0.92, 2.95]; camBase.look = [0, -0.05, -0.6]; }
  placeCamera();
  camera.updateProjectionMatrix();
}
/* 長球時視角往後退（退台），擊球後再慢慢回到台前 */
const camBase = { pos: [0, 0.92, 2.95], look: [0, -0.05, -0.6] };
let camBack = 0;
function placeCamera(){
  const b = camBack;
  camera.position.set(camBase.pos[0], camBase.pos[1] + b * 0.28, camBase.pos[2] + b);
  camera.lookAt(camBase.look[0], camBase.look[1], camBase.look[2] + b * 0.35);
}
function updateCamera(dt){
  let target = 0;
  if (phase === 'rally' && lastHitter === 'A' && awaitingHit === 'P') {
    const ahead = ball.p[2] + Math.max(0, ball.v[2]) * 0.25;   // 預判球會往後跑多遠
    target = clamp(ahead - (HL - 0.15), 0, 1.3);
  } else if (phase === 'rally' && lastHitter === 'A') target = camBack;          // 還沒彈地前保持不動
  const rate = target > camBack ? 4 : 1.6;
  camBack = lerp(camBack, target, Math.min(1, dt * rate));
  placeCamera();
}
new ResizeObserver(resize).observe(app);
resize();

/* ---------------- 球拍控制 ---------------- */
let shiftDown = false, lobOn = false;
function setLob(on){ lobOn = on; $('lob').setAttribute('aria-pressed', on ? 'true' : 'false'); }
const ray = new T3.Raycaster(), ndc = new T3.Vector2(0.25, -0.35), zPlane = new T3.Plane(new T3.Vector3(0, 0, 1), 0), hitV = new T3.Vector3();
const bat = { x: 0.3, y: 0.15, z: HL + 0.35, px: 0.3, py: 0.15, gx: 0.3, gy: 0.05, s: 1, sd: 0, vx: 0, vy: 0, refX: 0, refY: 0, flash: 0 };
function onPlane(z){
  zPlane.constant = -z;
  ray.setFromCamera(ndc, camera);
  if (!ray.ray.intersectPlane(zPlane, hitV)) return { x: 0, y: 0.15 };
  return { x: hitV.x, y: hitV.y };
}
/* 球拍的深度自動跟著球走（自動步法），滑鼠只負責左右和高低 */
/* 球拍深度固定在你站的位置（端線後），不會被球拉著跑；長球退台時跟著鏡頭一起後退 */
function batDepth(){ return HL + 0.35 + camBack; }
function updateBat(dt){
  bat.px = bat.x; bat.py = bat.y;
  bat.z = Math.min(batDepth(), camera.position.z - 0.6);   // 不讓球拍貼到鏡頭上
  const p = onPlane(bat.z);
  // 滑鼠對到的是握柄；拍面中心依目前握拍方向（roll）和拍面傾角（pitch）算出來
  bat.gx = clamp(p.x, -1.3, 1.3); bat.gy = clamp(p.y, -0.4, 0.8);
  const GRIP = 0.138;
  // 大小跟著遠近變，但用平滑過的距離，讓變化慢慢過渡（擊球範圍、握柄位置一起縮放，看到的就是打得到的）
  const camDist = Math.hypot(camera.position.x - bat.gx, camera.position.y - bat.gy, camera.position.z - bat.z);
  if (!bat.sd) bat.sd = camDist;
  bat.sd = lerp(bat.sd, camDist, Math.min(1, dt * 1.8));
  bat.s = clamp(camDist / bat.sd, 0.4, 2.5);
  bat.x = bat.gx - Math.sin(pose.roll) * GRIP * bat.s;
  bat.y = bat.gy + Math.cos(pose.roll) * GRIP * Math.cos(pose.pitch) * bat.s;
  // 球拍不能穿過球台：在球台上方時，整支拍子的最低點要留在桌面上
  if (racketOverTable(bat.x, bat.z)) {
    const minY = racketDrop(pose.roll, pose.pitch) * bat.s + 0.006;
    if (bat.y < minY) bat.y = minY;
  }
  const ref = onPlane(HL + 0.4);                 // 揮拍速度用固定深度量，避免深度改變造成假速度
  if (dt > 0) {
    bat.vx = lerp(bat.vx, (ref.x - bat.refX) / dt, 0.55);
    bat.vy = lerp(bat.vy, (ref.y - bat.refY) / dt, 0.55);
  }
  bat.refX = ref.x; bat.refY = ref.y;
}
function setNdc(e){
  const r = canvas.getBoundingClientRect();
  ndc.set(((e.clientX - r.left) / r.width) * 2 - 1, -((e.clientY - r.top) / r.height) * 2 + 1);
}
function tryToss(){ if (phase === 'serveWait' && server === 'P') toss(); }
canvas.addEventListener('pointermove', setNdc);
canvas.addEventListener('pointerdown', e => {
  setNdc(e); e.preventDefault();
  try { canvas.setPointerCapture(e.pointerId); } catch (_) {}
  tryToss();
});
addEventListener('keydown', e => {
  if (e.key === 'Shift') shiftDown = true;
  if (e.code === 'Space' && (e.target === document.body || e.target === canvas)) { e.preventDefault(); tryToss(); }
});
addEventListener('keyup', e => { if (e.key === 'Shift') shiftDown = false; });
addEventListener('blur', () => { shiftDown = false; });

/* ---------------- HUD ---------------- */
function updateScore(){
  $('sP').textContent = score.P; $('sA').textContent = score.A;
  $('whoP').classList.toggle('serving', server === 'P');
  $('whoA').classList.toggle('serving', server === 'A');
  let s = '先得 11 分 · 每 2 分換發';
  if (phase === 'serveWait' || phase === 'toss') s = server === 'P' ? (phase === 'serveWait' ? '輪到你發球：左右移動選位置，點一下拋球' : '球落下時揮拍') : '電腦發球';
  else if (phase === 'rally') s = '對打中';
  $('status').textContent = s;
}
let bannerTimer = 0, toastTimer = 0;
function banner(title, sub, cls){
  const b = $('banner');
  b.innerHTML = ''; b.append(title);
  const sm = document.createElement('small'); sm.textContent = sub; b.append(sm);
  b.className = 'banner ' + cls; void b.offsetWidth; b.classList.add('pop');
  b.hidden = false; bannerTimer = 1.5;
}
function toast(t){ const el = $('toast'); el.textContent = t; el.hidden = false; toastTimer = 1.4; }

function showShot(q, info, serve, sp, off, name){
  const rs = relSpin(ball.w, ball.v);
  $('shMain').textContent = name + ' · ' + spinLabel(rs.top, rs.side);
  const s1 = $('shSub'), s2 = $('shSub2');
  const swing = sp < 0.8 ? '擋球' : '揮拍 ' + sp.toFixed(1) + ' m/s';
  const edge = off > 0.65 ? ' · 打到拍緣' : '';
  if (serve) { s1.textContent = swing + edge; s1.className = 'sub'; s2.textContent = ''; return; }
  s1.textContent = swing + ' · 時機' + (q > 0.8 ? '完美' : q > 0.5 ? '不錯' : '勉強') + edge;
  s1.className = 'sub' + (q > 0.8 ? ' good' : q > 0.5 ? '' : ' bad');
  const r = info.res, mag = Math.hypot(r.ev, r.el);
  if (mag > 0.25) {
    const dir = Math.abs(r.ev) >= Math.abs(r.el) ? (r.ev < 0 ? '下' : '上') : (r.el > 0 ? '右' : '左');
    s2.textContent = `吃轉：回球被往${dir}帶偏 ${mag.toFixed(1)} m/s`; s2.className = 'sub bad';
  } else if (info.Eabs > 0.3) {
    s2.textContent = '成功抵銷來球旋轉'; s2.className = 'sub good';
  } else { s2.textContent = '來球幾乎不轉，沒有吃轉'; s2.className = 'sub'; }
}
function updateIncoming(){
  const main = $('inMain'), sub = $('inSub');
  if (phase === 'rally' && lastHitter === 'A') {
    const rs = relSpin(ball.w, ball.v);
    main.textContent = '電腦' + aiStroke + ' · ' + spinLabel(rs.top, rs.side);
    if (showHints) {
      const e = computeEat(ball.w, ball.v, [1, 0, 0]), parts = [], k = RACKETS[pRk].eat;
      e.ev *= k; e.el *= k;
      if (e.ev < -0.15) parts.push('↑ 由下往上揮'); else if (e.ev > 0.15) parts.push('↓ 往下壓');
      if (e.el > 0.15) parts.push('← 往左揮'); else if (e.el < -0.15) parts.push('→ 往右揮');
      sub.textContent = parts.length ? '建議：' + parts.join('、') + '，抵銷它的旋轉'
        : (k < 0.6 && Math.hypot(ball.w[0], ball.w[1], ball.w[2]) > 60 ? '你的膠皮不太吃轉，可以直接打' : '來球不太轉，自由發揮');
      sub.className = 'sub' + (parts.length ? ' hint' : '');
    } else { sub.textContent = '提示已關閉，從球的轉動自己判斷'; sub.className = 'sub'; }
  } else if (phase === 'rally' && lastHitter === 'P') {
    main.textContent = '—'; sub.textContent = '等待電腦回球'; sub.className = 'sub';
  }
}

function showGameOver(){
  phase = 'over';
  $('final').textContent = score.P + ' : ' + score.A;
  $('finalMsg').textContent = score.P > score.A ? '你贏了！' : '電腦獲勝，再挑戰一次';
  $('over').hidden = false; $('again').focus();
}
$('again').addEventListener('click', () => {
  score.P = score.A = 0; gameOverFlag = false; $('over').hidden = true;
  $('shMain').textContent = '—'; $('shSub').textContent = '擊球後顯示揮拍速度、旋轉和吃轉情況'; $('shSub').className = 'sub'; $('shSub2').textContent = '';
  setupServe();
});
$('lvl').addEventListener('change', e => { level = e.target.value; });
function fillRacketSelect(sel, withRandom, value){
  for (const k of RK_KEYS) { const op = document.createElement('option'); op.value = k; op.textContent = RACKETS[k].name; sel.append(op); }
  if (withRandom) { const op = document.createElement('option'); op.value = 'random'; op.textContent = '每分隨機'; sel.append(op); }
  sel.value = value;
}
fillRacketSelect($('prk'), false, pRk);
fillRacketSelect($('ark'), true, aRkSel);
function hex(c){ return '#' + c.toString(16).padStart(6, '0'); }
function renderRacketCard(){
  const rk = RACKETS[pRk];
  const bars = [
    ['速度', clamp((1/rk.tempo - 0.75) / 0.55, 0.05, 1)],
    ['旋轉', clamp(Math.max(rk.spin, rk.chop) / 1.4, 0.05, 1)],
    ['控制', clamp((1/rk.ctrl) / 1.43, 0.05, 1)],
    ['不吃轉', clamp(1 - rk.eat / 1.3, 0.05, 1)]
  ];
  const card = $('rkCard'); card.innerHTML = '';
  const nm = document.createElement('div'); nm.className = 'rk-name';
  const sw = document.createElement('span'); sw.className = 'rk-sw'; sw.style.background = hex(rk.color);
  const mat = document.createElement('span'); mat.className = 'mat'; mat.textContent = rk.mat;
  nm.append(sw, rk.name, mat);
  const grid = document.createElement('div'); grid.className = 'rk-bars';
  for (const [lab, v] of bars) {
    const l = document.createElement('span'); l.textContent = lab;
    const b = document.createElement('div'); b.className = 'rk-bar';
    const i = document.createElement('i'); i.style.width = Math.round(v*100) + '%'; b.append(i);
    grid.append(l, b);
  }
  const note = document.createElement('div'); note.className = 'rk-note'; note.textContent = rk.note;
  card.append(nm, grid, note);
}
function applyRacketLooks(){
  pr.g.userData.rubber.color.setHex(RACKETS[pRk].color);
  ar.g.userData.rubber.color.setHex(RACKETS[aRk].color);
  $('inLab').textContent = '來球旋轉 · 電腦用' + RACKETS[aRk].name;
}
$('prk').addEventListener('change', e => { pRk = e.target.value; renderRacketCard(); applyRacketLooks(); });
$('ark').addEventListener('change', e => {
  aRkSel = e.target.value;
  if (aRkSel !== 'random') aRk = aRkSel;
  else if (phase === 'serveWait') aRk = RK_KEYS[Math.floor(Math.random()*RK_KEYS.length)];
  applyRacketLooks();
});
renderRacketCard();
$('hint').addEventListener('change', e => { showHints = e.target.checked; });
$('lob').addEventListener('click', () => setLob(!lobOn));
$('slow').addEventListener('change', e => { timeScale = e.target.checked ? 0.5 : BASE_SPEED; });

/* ---------------- 主迴圈 ---------------- */
const qRot = new T3.Quaternion(), axis = new T3.Vector3();
let last = performance.now(), acc = 0, hudT = 0;
function frame(now){
  const dt = Math.min(0.05, (now - last) / 1000); last = now;
  const sdt = dt * timeScale;
  acc += sdt;
  updateBat(dt);
  if (phase === 'serveWait' && server === 'P') { ball.p[0] = serveX(); resetTrail(); }
  const n = Math.min(120, Math.floor(acc / DT));
  for (let i = 0; i < n; i++) physicsStep((i + 1) / n);
  acc -= n * DT; if (n >= 120) acc = 0;

  ballMesh.position.set(ball.p[0], ball.p[1], ball.p[2]);
  const wm = Math.hypot(ball.w[0], ball.w[1], ball.w[2]);
  if (wm > 0.1) {   // 旋轉視覺化放慢約 40 倍，避免看起來像倒轉
    axis.set(ball.w[0]/wm, ball.w[1]/wm, ball.w[2]/wm);
    qRot.setFromAxisAngle(axis, Math.min(wm * sdt * 0.1, 1.2));
    ballMesh.quaternion.premultiply(qRot);
  }
  const over = Math.abs(ball.p[0]) <= HW && Math.abs(ball.p[2]) <= HL && ball.p[1] > -0.01;
  const gy = over ? 0.0015 : FLOOR + 0.002, hgt = Math.max(0, ball.p[1] - gy);
  shadow.position.set(ball.p[0], gy, ball.p[2]);
  shadow.material.opacity = 0.5 / (1 + hgt * 5);
  const sc = 1 + hgt * 1.2; shadow.scale.set(sc, sc, 1);

  if (phase !== 'serveWait') {
    for (let i = TN - 1; i > 0; i--) { tPos[i*3] = tPos[(i-1)*3]; tPos[i*3+1] = tPos[(i-1)*3+1]; tPos[i*3+2] = tPos[(i-1)*3+2]; }
    tPos[0] = ball.p[0]; tPos[1] = ball.p[1]; tPos[2] = ball.p[2];
    trailGeo.attributes.position.needsUpdate = true;
  }
  for (const k of markers) {
    if (k.life > 0) { k.life -= sdt; const f = Math.max(0, k.life / 1.4); k.m.material.opacity = f * 0.9; const s = 1 + (1 - f) * 1.8; k.m.scale.set(s, s, 1); }
    else k.m.visible = false;
  }

  reticle.visible = false;
  const tracking = phase === 'rally' && lastHitter === 'A';
  pr.g.position.set(bat.x, bat.y, bat.z);
  updatePlayerPose(dt);
  if (bat.flash > 0) bat.flash -= dt;
  pr.g.scale.set(bat.s, bat.s, bat.s);
  for (const m of pr.g.userData.mats) m.opacity = tracking || phase === 'toss' ? 0.62 : 0.88;
  const toAI = phase === 'rally' && lastHitter === 'P';
  // 電腦發球時球拍跟著拿球的手走（球拍在球的右手邊，從你這邊看是左邊）
  const aiServing = server === 'A' && (phase === 'serveWait' || phase === 'toss');
  const aiIdle = toAI ? [clamp(ball.p[0], -0.9, 0.9), 0.12, -HL - 0.3]
    : aiServing ? [ball.p[0] - 0.13, 0.14, -HL - 0.22]
    : [0, 0.12, -HL - 0.3];
  updRacket(ar, aiIdle, sdt);
  if (racketOverTable(ar.g.position.x, ar.g.position.z)) ar.g.position.y = Math.max(ar.g.position.y, racketDrop(0.64, 0) + 0.006);

  hudT -= dt; if (hudT <= 0) { hudT = 0.1; updateIncoming(); if (phase === 'rally') updateScore(); }
  if (bannerTimer > 0) { bannerTimer -= dt; if (bannerTimer <= 0) $('banner').hidden = true; }
  if (toastTimer > 0) { toastTimer -= dt; if (toastTimer <= 0) $('toast').hidden = true; }

  updateCamera(dt);
  renderer.render(scene, camera);
  requestAnimationFrame(frame);
}
setupServe();
requestAnimationFrame(frame);
})();