
const exprInput = document.getElementById('exprInput');
const resultText = document.getElementById('resultText');
const resultAlt = document.getElementById('resultAlt');
const recentExpr = document.getElementById('recentExpr');
const recentRes = document.getElementById('recentRes');
const historyList = document.getElementById('historyList');
const ansShow = document.getElementById('ansShow');
const modeShow = document.getElementById('modeShow');

let history = JSON.parse(localStorage.getItem('calc_history') || '[]'); // {expr,res,alt}
let ANS = null;
let radMode = true; // true = Rad, false = Deg
let undoStack = [], redoStack = [];
let caps = false;

/* ============================
   Math helpers (fact, nCr, nPr,...)
   ============================ */
function fact(n){
  n = Math.floor(Number(n));
  if(!isFinite(n) || n<0) return NaN;
  if(n===0 || n===1) return 1;
  let r=1;
  for(let i=2;i<=n;i++) r*=i;
  return r;
}
function nCr(n,k){ n=Math.floor(n);k=Math.floor(k); if(k>n||k<0) return 0; return fact(n)/(fact(k)*fact(n-k)); }
function nPr(n,k){ n=Math.floor(n);k=Math.floor(k); if(k>n||k<0) return 0; return fact(n)/fact(n-k); }
function mean(...a){ if(a.length===1 && Array.isArray(a[0])) a = a[0]; a = a.map(Number).filter(x=>!isNaN(x)); if(a.length===0) return NaN; return a.reduce((s,v)=>s+v,0)/a.length; }
function stdev(...a){ if(a.length===1 && Array.isArray(a[0])) a = a[0]; a=a.map(Number).filter(x=>!isNaN(x)); let n=a.length; if(n<=1) return 0; let m=mean(a); let s=a.reduce((acc,v)=>acc+(v-m)*(v-m),0); return Math.sqrt(s/(n-1)); }
function stdevp(...a){ if(a.length===1 && Array.isArray(a[0])) a = a[0]; a=a.map(Number).filter(x=>!isNaN(x)); let n=a.length; if(n===0) return 0; let m=mean(a); let s=a.reduce((acc,v)=>acc+(v-m)*(v-m),0); return Math.sqrt(s/n); }
function root(a,b){ a=Number(a);b=Number(b); if(!isFinite(a)||!isFinite(b)||a===0) return NaN; return Math.pow(b,1/a); }

/* ============================
   Preprocess & evaluator
   ============================ */
function preprocess(expr){
  if(!expr) return expr;
  expr = String(expr).trim();

  // replace unicode pi
  expr = expr.replace(/π/g,'pi');

  // convert common symbols: × ÷ − to * / -
  expr = expr.replace(/×/g,'*').replace(/÷/g,'/').replace(/−/g,'-');

  // colon used as divide
  expr = expr.replace(/:/g,'/');

  // caret to **
  expr = expr.replace(/\^/g,'**');

  // percentages like 12% -> (12/100)
  expr = expr.replace(/(\d+(\.\d+)?)%/g,'($1/100)');

  // Replace ANS with value
  expr = expr.replace(/\bANS\b/g, '(' + (ANS===null? '0' : String(ANS)) + ')');

  // factorial: convert n! or (expr)! to fact(expr)
  expr = expr.replace(/([0-9\.]+|\([^()]*\))!/g, function(m,p1){ return 'fact(' + p1 + ')'; });

  // implicit multiplication like 2(, )(3) , number)( -> *
  expr = expr.replace(/(\d)\s*\(/g,'$1*(');
  expr = expr.replace(/\)\s*(\d)/g,')*$1');
  expr = expr.replace(/\)\s*\(/g,')*(');

  return expr;
}

/* Wrap trig functions when in Degree mode */
function wrapDegrees(expr){
  if(radMode) return expr;
  // replace sin(x) -> __deg('sin', x) etc.
  expr = expr.replace(/\b(sin|cos|tan|asin|acos|atan)\s*\(/g, function(m,fn){ return "__degwrap('" + fn + "',"; });
  return expr;
}

/* Safe evaluation using new Function closure with helpers injected */
function safeEval(raw){
  try{
    if(!raw || raw.trim()==='') return undefined;
    let s = preprocess(raw);
    s = wrapDegrees(s);

    const fnBody = `
      const pi=Math.PI; const e=Math.E;
      function sin(x){return Math.sin(x);} function cos(x){return Math.cos(x);} function tan(x){return Math.tan(x);}
      function asin(x){return Math.asin(x);} function acos(x){return Math.acos(x);} function atan(x){return Math.atan(x);}
      function sqrt(x){return Math.sqrt(x);} function abs(x){return Math.abs(x);} function round(x){return Math.round(x);}
      function ln(x){return Math.log(x);} function log(x){return Math.log10?Math.log10(x):Math.log(x)/Math.LN10;}
      function exp(x){return Math.exp(x);}
      function __degwrap(fnName, val){ const v=Number(val)*Math.PI/180; if(fnName==='sin') return Math.sin(v); if(fnName==='cos') return Math.cos(v); if(fnName==='tan') return Math.tan(v); if(fnName==='asin') return Math.asin(v); if(fnName==='acos') return Math.acos(v); if(fnName==='atan') return Math.atan(v); return NaN;}
      return (${s});
    `;
    const evaluator = new Function('fact','nCr','nPr','mean','stdev','stdevp','root', fnBody);
    const res = evaluator(fact,nCr,nPr,mean,stdev,stdevp,root);
    if(typeof res === 'number' && Object.is(res,-0)) return 0;
    return res;
  } catch(e){
    console.warn('Eval error',e);
    return undefined;
  }
}

/* ============================
   Fraction & repeating decimal utilities
   ============================ */

/* Convert float to best rational approximation using continued fractions
   returns {num, den} with den <= maxDen
*/
function floatToFraction(x, maxDen=10000){
  if(!isFinite(x)) return null;
  let neg = x<0; if(neg) x = -x;
  const eps = 1e-12;
  let a = Math.floor(x);
  if (Math.abs(a - x) < eps) return {num: neg? -a : a, den:1};
  let h1=1, k1=0, h= a, k=1;
  let frac = x - a;
  let it = 0;
  while(Math.abs(h/k - x) > eps && it < 80){
    it++;
    frac = 1/frac;
    a = Math.floor(frac);
    let h2 = h1; let k2 = k1;
    h1 = h; k1 = k;
    h = a*h1 + h2;
    k = a*k1 + k2;
    if(k > maxDen) break;
    frac = frac - a;
    if(frac === 0) break;
  }
  // reduce
  const g = gcd(Math.round(h), Math.round(k));
  let num = Math.round(h/g); let den = Math.round(k/g);
  if(neg) num = -num;
  return {num, den};
}

function gcd(a,b){
  a=Math.abs(a); b=Math.abs(b);
  while(b){ const t=a%b; a=b; b=t; } return a;
}

/* Given numerator & denominator (integers), produce decimal expansion and detect repeating cycle
   Returns object: {intPart, nonRepeat, repeat} where nonRepeat and repeat are strings
*/
function getDecimalExpansion(num, den, maxDigits=2000){
  num = Math.abs(Math.trunc(num));
  den = Math.abs(Math.trunc(den));
  if(den === 0) return null;
  const intPart = Math.floor(num / den);
  let rem = num % den;
  let digits = [];
  let seen = {}; // map remainder -> position
  let pos = 0;
  while(rem !== 0 && pos < maxDigits){
    if(seen.hasOwnProperty(rem)){
      // cycle found from seen[rem] to pos-1
      const start = seen[rem];
      const nonRepeat = digits.slice(0,start).join('') || '';
      const repeat = digits.slice(start).join('') || '';
      return {intPart: String(intPart), nonRepeat, repeat};
    }
    seen[rem] = pos;
    rem *= 10;
    const d = Math.floor(rem / den);
    digits.push(String(d));
    rem = rem % den;
    pos++;
  }
  // no repeat
  return {intPart: String(intPart), nonRepeat: digits.join('') || '', repeat: ''};
}

/* Format fraction in HTML for nice display */
function renderFractionHTML(num, den){
  if(den === 1) return String(num);
  const sign = (num<0) ? '-' : '';
  num = Math.abs(num);
  return `${sign}<span class="frac"><span class="num">${num}</span><span class="den">${den}</span></span>`;
}

/* Create string with repeating decimal notation like 0.(3) or 1.2(34) */
function renderDecimalWithRepeat(num, den){
  const dec = getDecimalExpansion(num, den);
  if(!dec) return null;
  const intP = dec.intPart;
  if(dec.repeat){
    if(dec.nonRepeat === '') return `${intP}.(${dec.repeat})`;
    return `${intP}.${dec.nonRepeat}(${dec.repeat})`;
  } else {
    if(dec.nonRepeat === '') return `${intP}`;
    return `${intP}.${dec.nonRepeat}`;
  }
}

/* Attempt to show fraction or repeating form for a numeric result
   Strategy:
   - If result is integer: show integer
   - Else try to get rational approximation via continued fraction; if denom small enough (<=10000), show fraction and repeating decimal either
*/
function getAlternateRepresentations(value){
  if(typeof value !== 'number' || !isFinite(value)) return null;
  // if integer
  if(Number.isInteger(value)) return {display: String(value), fractionHTML: null, repeating: null};

  // Attempt to convert float to fraction
  const frac = floatToFraction(value, 10000);
  if(!frac) return null;
  const {num, den} = frac;
  // if denominator not too large, show fraction and repeating decimal form
  if(Math.abs(den) <= 10000){
    const fracHTML = renderFractionHTML(num, den);
    const repeat = renderDecimalWithRepeat(num, den);
    return {display: String(value), fractionHTML: fracHTML, repeating: repeat};
  }
  return {display: String(value), fractionHTML: null, repeating: null};
}

/* ============================
   UI behaviours
   ============================ */

/* Insert token at cursor */
function insertAtCursor(text){
  const el = exprInput;
  const start = el.selectionStart;
  const end = el.selectionEnd;
  const before = el.value.substring(0, start);
  const after  = el.value.substring(end);
  el.value = before + text + after;
  const pos = before.length + text.length;
  el.setSelectionRange(pos,pos);
  el.focus();
  pushUndo();
}

/* Undo/Redo stacks */
function pushUndo(){
  // only push when top different
  const cur = exprInput.value;
  if(undoStack.length===0 || undoStack[undoStack.length-1] !== cur){
    undoStack.push(cur);
    if(undoStack.length>200) undoStack.shift();
  }
  // clear redo
  redoStack = [];
}
function doUndo(){ if(undoStack.length===0) return; const cur = exprInput.value; redoStack.push(cur); const prev = undoStack.pop(); exprInput.value = prev; exprInput.focus(); }
function doRedo(){ if(redoStack.length===0) return; undoStack.push(exprInput.value); const next = redoStack.pop(); exprInput.value = next; exprInput.focus(); }

/* Evaluate and store result */
function evaluateAndStore(){
  const expr = exprInput.value.trim();
  if(expr === '') {
    resultText.textContent = '—';
    resultAlt.textContent = 'Không có phép tính.';
    return;
  }
  const val = safeEval(expr);
  if(val === undefined || Number.isNaN(val)){
    resultText.textContent = 'undefined';
    resultAlt.textContent = 'Biểu thức không hợp lệ hoặc lỗi tính toán.';
    recentExpr.textContent = expr;
    recentRes.textContent = 'undefined';
    addHistoryEntry(expr,'undefined', null);
    exprInput.value = ''; // clear per requirement
    return;
  }

  // Format main display
  if(typeof val === 'number'){
    // nice format
    let display;
    if(Number.isInteger(val)) display = String(val);
    else {
      // choose precision 12 significant
      display = Number.parseFloat(val.toPrecision(12)).toString();
    }
    resultText.textContent = display;
    // alt: fraction and repeating info
    const alt = getAlternateRepresentations(val);
    if(alt && (alt.fractionHTML || alt.repeating)){
      let altHtml = '';
      if(alt.fractionHTML) altHtml += 'Phân số: ' + alt.fractionHTML;
      if(alt.repeating){
        if(altHtml) altHtml += ' — ';
        altHtml += 'Dạng thập phân: ' + escapeHtml(alt.repeating);
      }
      // set as HTML
      resultAlt.innerHTML = altHtml;
      addHistoryEntry(expr,display, altHtml);
    } else {
      resultAlt.textContent = 'Không có biểu diễn phân số chính xác trong giới hạn.';
      addHistoryEntry(expr,display, null);
    }
    ANS = val;
    ansShow.textContent = (Number.isFinite(ANS) ? String(Number(ANS.toPrecision(12))) : String(ANS));
  } else {
    // not a number (could be array or string)
    resultText.textContent = String(val);
    resultAlt.textContent = '';
    addHistoryEntry(expr,String(val), null);
    ANS = val;
    ansShow.textContent = String(val);
  }

  recentExpr.textContent = expr;
  recentRes.textContent = resultText.textContent;
  exprInput.value = ''; // clear per requirement
  saveHistoryToLocalStorage();
}

/* History */
function addHistoryEntry(expr,res, alt){
  history.unshift({expr,res,alt});
  if(history.length>8) history.length=8;
  renderHistory();
}
function renderHistory(){
  historyList.innerHTML = '';
  for(let i=0;i<history.length;i++){
    const it = history[i];
    const li = document.createElement('li');
    li.className = 'hist-item';
    li.innerHTML = `<strong>${escapeHtml(it.expr)}</strong><br><small style="color:${getComputedStyle(document.documentElement).getPropertyValue('--muted')};">${escapeHtml(it.res)}</small>`;
    li.addEventListener('click', ()=> {
      exprInput.value = it.expr;
      exprInput.focus();
    });
    historyList.appendChild(li);
  }
}
function saveHistoryToLocalStorage(){
  localStorage.setItem('calc_history', JSON.stringify(history));
}
// Inline confirm + toast implementation
const clearHistoryBtn = document.querySelector('.clear-history-btn');
const confirmBox = document.getElementById('confirmBox');
const confirmOk = document.getElementById('confirmOk');
const confirmCancel = document.getElementById('confirmCancel');
const historyToast = document.getElementById('historyToast');

function showConfirmBox(){
  if(!confirmBox) return;
  confirmBox.style.display = 'flex';
  confirmBox.setAttribute('aria-hidden','false');
  // scroll into view to ensure user sees it (optional)
  confirmBox.scrollIntoView({behavior:'smooth', block:'nearest'});
}
function hideConfirmBox(){
  if(!confirmBox) return;
  confirmBox.style.display = 'none';
  confirmBox.setAttribute('aria-hidden','true');
}

function showToast(msg = 'Đã xóa lịch sử', ms = 1800){
  if(!historyToast) return;
  historyToast.textContent = msg;
  historyToast.style.display = 'inline-block';
  historyToast.style.opacity = '1';
  // auto hide
  setTimeout(()=> {
    historyToast.style.opacity = '0';
    // small delay to allow transition (if any)
    setTimeout(()=> historyToast.style.display = 'none', 200);
  }, ms);
}

if(clearHistoryBtn){
  clearHistoryBtn.addEventListener('click', (e)=>{
    // show inline confirm box (k thay đổi lịch sử ngay)
    showConfirmBox();
  });
}

if(confirmCancel){
  confirmCancel.addEventListener('click', ()=>{
    hideConfirmBox();
  });
}

if(confirmOk){
  confirmOk.addEventListener('click', ()=>{
    // do deletion:
    history = [];                 // clear in-memory
    renderHistory();              // cập nhật UI
    localStorage.removeItem('calc_history'); // xóa khỏi storage
    // cập nhật recent/result
    recentExpr.textContent = '—';
    recentRes.textContent = '—';
    resultAlt.textContent = 'Lịch sử đã được xóa.';
    // show toast
    showToast('Đã xóa toàn bộ lịch sử');
    // hide confirm box
    hideConfirmBox();
  });
}



/* escape html */
function escapeHtml(s){
  return String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
}

/* Wire up keys */
document.querySelectorAll('[data-insert]').forEach(btn=>{
  btn.addEventListener('click', ()=> {
    const token = btn.getAttribute('data-insert');
    if(token === 'ANS') insertAtCursor('ANS');
    else insertAtCursor(token);
  });
});

/* Special buttons */
document.getElementById('enterBtn').addEventListener('click', evaluateAndStore);
document.getElementById('nangEnter').addEventListener('click', evaluateAndStore);
document.getElementById('abcEnter').addEventListener('click', evaluateAndStore);

document.getElementById('clearAll').addEventListener('click', ()=>{
  exprInput.value = '';
  resultText.textContent = '—';
  resultAlt.textContent = 'Đã xóa.';
  pushUndo();
});

document.getElementById('radToggle').addEventListener('click', (e)=>{
  radMode = !radMode;
  e.target.textContent = radMode ? 'Rad' : 'Độ';
  modeShow.textContent = radMode ? 'Radian' : 'Độ';
  e.target.classList.toggle('active', !radMode);
});

/* Undo/Redo */
document.getElementById('undoBtn').addEventListener('click', doUndo);
document.getElementById('redoBtn').addEventListener('click', doRedo);

/* Backspace */
document.getElementById('backspace').addEventListener('click', ()=>{
  const el = exprInput;
  const s = el.selectionStart, e = el.selectionEnd;
  if(s===e && s>0){
    const before = el.value.slice(0,s-1);
    const after = el.value.slice(e);
    el.value = before + after;
    el.setSelectionRange(s-1,s-1);
  } else {
    const before = el.value.slice(0,s);
    const after = el.value.slice(e);
    el.value = before + after;
    el.setSelectionRange(s,s);
  }
  el.focus();
  pushUndo();
});

/* cursor move */
document.getElementById('moveLeft').addEventListener('click', ()=>{
  exprInput.setSelectionRange(Math.max(0,exprInput.selectionStart-1), Math.max(0,exprInput.selectionEnd-1));
  exprInput.focus();
});
document.getElementById('moveRight').addEventListener('click', ()=>{
  exprInput.setSelectionRange(Math.min(exprInput.value.length,exprInput.selectionStart+1), Math.min(exprInput.value.length,exprInput.selectionEnd+1));
  exprInput.focus();
});

/* frac helper */
document.getElementById('fracAB').addEventListener('click', ()=>{
  insertAtCursor('(');
  insertAtCursor(')/('); // helper; user completes manually
});

/* copy/paste */
document.getElementById('copyBtn').addEventListener('click', ()=> {
  navigator.clipboard?.writeText(resultText.textContent || '').then(()=> alert('Đã sao chép kết quả'));
});
document.getElementById('pasteBtn').addEventListener('click', async ()=> {
  const txt = await navigator.clipboard.readText().catch(()=>null);
  if(txt) insertAtCursor(txt);
});

/* ABC keyboard special */
document.getElementById('abcBack').addEventListener('click', ()=> {
  exprInput.value = exprInput.value.slice(0,-1);
  exprInput.focus();
});
document.getElementById('capsLock').addEventListener('click', ()=>{
  caps = !caps;
  document.querySelectorAll('#tab-abc .key[data-insert]').forEach(k=>{
    let t = k.getAttribute('data-insert');
    if(t.length===1 && /[a-z]/i.test(t)){
      k.textContent = caps ? t.toUpperCase() : t.toLowerCase();
      k.setAttribute('data-insert', caps ? t.toUpperCase() : t.toLowerCase());
    }
  });
});
const tabABC = document.getElementById('tab-abc');
const numpadWrapper = document.querySelector('.numpad-wrapper');



/* Tabs */
// document.querySelectorAll('.tab').forEach(tab=>{
//   tab.addEventListener('click', ()=>{
//     document.querySelectorAll('.tab').forEach(t=>t.classList.remove('active'));
//     tab.classList.add('active');
//     const id = tab.getAttribute('data-tab');
//     document.getElementById('tab-chinh').style.display = id==='chinh' ? 'grid' : 'none';
//     document.getElementById('tab-abc').style.display = id==='abc' ? 'grid' : 'none';
//     document.getElementById('tab-nangcao').style.display = id==='nangcao' ? 'grid' : 'none';
//   });
// });
document.addEventListener('DOMContentLoaded', ()=>{
  const tabs = document.querySelectorAll('.tab');
  const tabChinh = document.getElementById('tab-chinh');
  const tabAbc = document.getElementById('tab-abc');
  const tabNang = document.getElementById('tab-nangcao');

  // ensure elements exist
  if(!tabs.length) return;

  function setActiveTab(tab){
    // toggle active class on tabs
    tabs.forEach(t=>t.classList.remove('active'));
    tab.classList.add('active');

    const id = tab.getAttribute('data-tab');

    // show/hide tab panels
    if(tabChinh) tabChinh.style.display = id === 'chinh' ? 'grid' : 'none';
    if(tabAbc)   tabAbc.style.display   = id === 'abc'   ? 'grid' : 'none';
    if(tabNang)  tabNang.style.display  = id === 'nangcao'? 'grid' : 'none';

    // ADD/REMOVE body class so CSS can shrink the numpad
    if(id === 'abc'){
      document.body.classList.add('show-abc');
    } else {
      document.body.classList.remove('show-abc');
    }
  }

  // attach click listeners
  tabs.forEach(tab=>{
    tab.addEventListener('click', ()=> setActiveTab(tab));
  });

  // optional: set the initial active tab based on existing .active or default first tab
  const initial = document.querySelector('.tab.active') || tabs[0];
  if(initial) setActiveTab(initial);
});


/* keyboard input handling */
exprInput.addEventListener('keydown', (e)=>{
  if(e.key === 'Enter'){
    e.preventDefault();
    pushUndo();
    evaluateAndStore();
  } else {
    if(undoStack.length===0 || undoStack[undoStack.length-1] !== exprInput.value){
      pushUndo();
    }
  }
});

/* clickable history items will fill input (renderHistory sets that) */
renderHistory();

/* dark mode toggle */
const darkToggle = document.getElementById('darkToggle');
darkToggle.addEventListener('click', ()=>{
  document.body.classList.toggle('dark');
  darkToggle.textContent = document.body.classList.contains('dark') ? 'Light' : 'Dark';
});

/* small helpful console */
console.log('Máy tính online - sẵn sàng. Chế độ:', radMode ? 'Rad' : 'Độ');

/* Persist history on unload */
window.addEventListener('beforeunload', saveHistoryToLocalStorage);

/* Preload history into UI */
(function initFromStorage(){
  try{
    const saved = JSON.parse(localStorage.getItem('calc_history') || '[]');
    if(Array.isArray(saved) && saved.length) history = saved;
  } catch(e){}
  renderHistory();
})();

/* ============================
   Extra: keyboard shortcuts
   - Ctrl+Enter = evaluate
   - Ctrl+L = clear history
   ============================ */
document.addEventListener('keydown', (e)=>{
  if(e.ctrlKey && e.key === 'Enter'){
    evaluateAndStore();
  } else if(e.ctrlKey && e.key.toLowerCase() === 'l'){
    history = []; renderHistory(); saveHistoryToLocalStorage(); alert('Đã xóa lịch sử');
  }
});
