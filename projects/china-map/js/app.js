/* ============================================================
   华夏五千年 · 历史疆域时间地图 —— 应用引擎
   (无依赖, 纯 SVG/DOM; 数据见 data/*.js)
   ============================================================ */
(function(){
'use strict';

/* ---------- 时间工具 ---------- */
var T0 = -8000, T1 = 2026.5;             // 时间轴范围 (至今)
var MDAYS=[31,28,31,30,31,30,31,31,30,31,30,31];
var MCUM=[0]; for(var i=0;i<11;i++) MCUM.push(MCUM[i]+MDAYS[i]);

function yearOf(t){ return Math.floor(t); }
function ymd(t){
  var y=Math.floor(t), f=t-y;
  var doy=Math.min(364, Math.max(0, Math.round(f*365)));
  var m=0; while(m<11 && doy>=MCUM[m+1]) m++;
  return {y:y, m:m+1, d:doy-MCUM[m]+1};
}
function fmtY(y){ return y<=0 ? '前'+(-y+ (y===0?1:0))+'年' : y+'年'; }
function fmtDate(t, span){
  var o=ymd(t);
  if(span===undefined) span=1e9;
  if(span>2.2) return fmtY(o.y);
  if(span>0.45) return fmtY(o.y)+' '+o.m+'月';
  return fmtY(o.y)+' '+o.m+'月'+o.d+'日';
}
function fmtRange(a,b){
  if(b-a<1.5){ var A=ymd(a),B=ymd(b); return fmtY(A.y)+A.m+'月'+A.d+'日 — '+fmtY(B.y)+B.m+'月'+B.d+'日'; }
  return fmtY(yearOf(a))+' — '+fmtY(yearOf(b));
}
function durText(a,b){
  var n=b-a;
  if(n<0.02) return Math.max(1,Math.round(n*365))+'天';
  if(n<1) return Math.round(n*12)+'个月';
  return Math.round(n)+'年';
}

/* ---------- 投影 ---------- */
var LON=68, LAT=56, SX=12.5, SY=12.5/Math.cos(32*Math.PI/180);
var W=1000, H=Math.round((56-6)*SY);
function PX(lon){ return (lon-LON)*SX; }
function PY(lat){ return (LAT-lat)*SY; }
function pathOf(rings){
  var d='';
  rings.forEach(function(r){
    r.forEach(function(p,i){ d+=(i?'L':'M')+PX(p[0]).toFixed(2)+' '+PY(p[1]).toFixed(2); });
    d+='Z';
  });
  return d;
}
function centroidOf(ring){
  var a=0,cx=0,cy=0;
  for(var i=0;i<ring.length;i++){
    var p=ring[i], q=ring[(i+1)%ring.length];
    var x1=PX(p[0]),y1=PY(p[1]),x2=PX(q[0]),y2=PY(q[1]);
    var cr=x1*y2-x2*y1; a+=cr; cx+=(x1+x2)*cr; cy+=(y1+y2)*cr;
  }
  if(Math.abs(a)<1e-6){ return [PX(ring[0][0]),PY(ring[0][1]),0]; }
  return [cx/(3*a), cy/(3*a), Math.abs(a/2)];
}

/* ---------- 疆域精化: 栅格分割 → 归属判定 → 缝隙填充 → 描迹平滑 ----------
   政权疆界数据为低分辨率手绘概形, 直接叠画会在国与国之间留缝、
   彼此重叠、沿海露地。渲染前把当前时刻所有政权栅格化到 0.15° 经纬网格:
   1. 栅格化   每国多边形按扫描线落入网格;
   2. 归属判定 重叠格唯一归属: 面积小者优先(飞地小国不被大邻国吞没);
              数据中帧标记 ov:1 的政权(拉锯/占领区)不参与争夺,
              其与他国的重叠区单独描迹, 以双色斜纹渲染;
   3. 缝隙填充 无归属陆地格若位于两国之间(d1+d2≤GAP)或国与海岸之间
              (d1+d海≤GAP), 划归最近政权 —— 相邻政权无缝相接、
              沿海政权覆盖至真实海岸线; 距离场只沿陆地传播(跨海高代价),
              不会隔着海峡把归属"漂"到对岸;
   4. 描迹平滑 对每国格集沿格线描迹成环, Chaikin 切角平滑;
              相邻两国共享同一条格线边界, 平滑对称, 结果仍完全重合。 */
var SMOOTH_IT=3;
var CELL=0.15, GLON0=64, GLAT0=6, GNX=560, GNY=334;
var KX=[1,-1,0,0,1,1,-1,-1], KY=[0,0,1,-1,1,-1,1,-1], KC=[10,10,10,10,14,14,14,14];
var FILLD=Math.round(1.6/CELL*10);   // 政权最大外扩 ≈1.6°
var FILLP=Math.round(0.6/CELL*10);   // 史前文化外扩上限 ≈0.6°
var GAPD=Math.round(2.2/CELL*10);    // 可填充的国间缝隙总宽 ≈2.2°
var GAPP=Math.round(1.0/CELL*10);
var GAPSEA=Math.round(0.9/CELL*10);  // 国界—海岸走廊总宽 ≈0.9° (防止沿海外溢到无主邻邦)
var landMask=null, seaDist=null;
// 扫描线栅格化: 对每一格行求多边形交点, 中心落入区间的格子回调
function scanRings(rings, mark){
  for(var gy=0;gy<GNY;gy++){
    var lat=GLAT0+(gy+0.5)*CELL, xs=[];
    for(var ri=0;ri<rings.length;ri++){
      var r=rings[ri];
      for(var i=0,j=r.length-1;i<r.length;j=i++){
        if((r[i][1]>lat)!==(r[j][1]>lat))
          xs.push(r[i][0]+(lat-r[i][1])/(r[j][1]-r[i][1])*(r[j][0]-r[i][0]));
      }
    }
    if(!xs.length) continue;
    xs.sort(function(a,b){return a-b;});
    for(var k=0;k+1<xs.length;k+=2){
      var g0=Math.max(0,Math.ceil((xs[k]-GLON0)/CELL-0.5));
      var g1=Math.min(GNX-1,Math.floor((xs[k+1]-GLON0)/CELL-0.5));
      for(var gx=g0;gx<=g1;gx++) mark(gx,gy);
    }
  }
}
// Dial 桶式 BFS 距离场 (单位: 格宽/10; 斜向14)
// mode 1: 仅沿陆地  mode 2: 无主陆地格代价1, 海上代价4, 有主陆地格阻断
function bfs(dist,seeds,maxd,mode,owner){
  var buckets=[],i,c;
  for(i=0;i<seeds.length;i++) dist[seeds[i]]=0;
  buckets[0]=seeds.slice();
  for(var d=0;d<=maxd;d++){
    var q=buckets[d]; if(!q) continue;
    for(var qi=0;qi<q.length;qi++){
      c=q[qi]; if(dist[c]!==d) continue;
      var cx=c%GNX, cy=(c-cx)/GNX;
      for(var k=0;k<8;k++){
        var nx=cx+KX[k], ny=cy+KY[k];
        if(nx<0||ny<0||nx>=GNX||ny>=GNY) continue;
        var nc=ny*GNX+nx, mult;
        if(mode===1){ if(!landMask[nc]) continue; mult=1; }
        else if(landMask[nc]){ if(owner[nc]>=0) continue; mult=1; }
        else mult=4;
        var nd=d+KC[k]*mult;
        if(nd<=maxd && nd<dist[nc]){ dist[nc]=nd; (buckets[nd]||(buckets[nd]=[])).push(nc); }
      }
    }
  }
}
function buildLandGrid(){
  landMask=new Uint8Array(GNX*GNY);
  scanRings(BASEMAP.land,function(gx,gy){ landMask[gy*GNX+gx]=1; });
  // 陆地格到海岸的距离场 (供"国界—海岸"走廊填充)
  seaDist=new Uint16Array(GNX*GNY); seaDist.fill(0xFFFF);
  var seeds=[];
  for(var cy=0;cy<GNY;cy++)for(var cx=0;cx<GNX;cx++){
    var c=cy*GNX+cx;
    if(!landMask[c]) continue;
    if((cx>0&&!landMask[c-1])||(cx<GNX-1&&!landMask[c+1])||
       (cy>0&&!landMask[c-GNX])||(cy<GNY-1&&!landMask[c+GNX])) seeds.push(c);
  }
  bfs(seaDist,seeds,GAPD,1);
}
// 二值格集描迹: 沿格线走边(内部恒在左侧), 输出经纬度环; 直行段就地合并
function traceMask(mask){
  var W1=GNX+1, DX=[1,0,-1,0], DY=[0,1,0,-1];
  var out={}, key;
  function add(cx,cy,d){ var k=cy*W1+cx; if(out[k]) out[k].push(d); else out[k]=[d]; }
  for(var y=0;y<GNY;y++){
    var row=y*GNX;
    for(var x=0;x<GNX;x++){
      if(!mask[row+x]) continue;
      if(x===0||!mask[row+x-1]) add(x,y+1,3);
      if(x===GNX-1||!mask[row+x+1]) add(x+1,y,1);
      if(y===0||!mask[row+x-GNX]) add(x,y,0);
      if(y===GNY-1||!mask[row+x+GNX]) add(x+1,y+1,2);
    }
  }
  var rings=[];
  for(key in out){
    for(;;){
      var lst=out[key];
      if(!lst||!lst.length) break;
      var start=+key, cd=lst.pop();
      var px=start%W1, py=(start-px)/W1;
      var pts=[], lastd=-1;
      for(;;){
        if(cd!==lastd){ pts.push([GLON0+px*CELL, GLAT0+py*CELL]); lastd=cd; }
        px+=DX[cd]; py+=DY[cd];
        var ck=py*W1+px;
        if(ck===start) break;
        var l2=out[ck], nd=-1;
        if(l2&&l2.length){
          var pref=[(cd+1)&3, cd, (cd+3)&3, (cd+2)&3];
          for(var pi=0;pi<4;pi++){
            var ii=l2.indexOf(pref[pi]);
            if(ii>=0){ nd=pref[pi]; l2.splice(ii,1); break; }
          }
        }
        if(nd<0) break;
        cd=nd;
      }
      if(pts.length>=4) rings.push(pts);
    }
  }
  return rings;
}
function chaikinRing(r){
  var out=[], n=r.length;
  for(var i=0;i<n;i++){
    var p=r[i], q=r[(i+1)%n];
    out.push([p[0]*0.75+q[0]*0.25, p[1]*0.75+q[1]*0.25]);
    out.push([p[0]*0.25+q[0]*0.75, p[1]*0.25+q[1]*0.75]);
  }
  return out;
}
// 近共线点抽稀 (判据对方向反转对称, 共享边界两侧结果一致)
function simplifyRing(r){
  var out=[], n=r.length;
  for(var i=0;i<n;i++){
    var a=r[(i+n-1)%n], b=r[i], q=r[(i+1)%n];
    var cr=(b[0]-a[0])*(q[1]-b[1])-(b[1]-a[1])*(q[0]-b[0]);
    if(cr>1e-4||cr<-1e-4) out.push(b);
  }
  return out.length>3?out:r;
}
function smoothRings(rings){
  return rings.map(function(r){
    for(var s=0;s<SMOOTH_IT;s++) r=simplifyRing(chaikinRing(r));
    return r;
  });
}
function refineItems(items){
  var N=GNX*GNY, n=items.length, i, j, c;
  // 1. 栅格化 + 面积/填充参数
  items.forEach(function(it){
    it.mask=new Uint8Array(N);
    scanRings(it.raw,function(gx,gy){ it.mask[gy*GNX+gx]=1; });
    var a=0;
    it.raw.forEach(function(r){
      for(var x=0,y=r.length-1;x<r.length;y=x++) a+=r[y][0]*r[x][1]-r[x][0]*r[y][1];
    });
    it.area=Math.abs(a/2);
    var pre=it.p.tp==='p';
    it.fmax=pre?FILLP:FILLD;
    it.gap=pre?GAPP:GAPD;
  });
  // 2. 归属判定: 拉锯覆盖层最先画, 其余按面积从大到小 —— 后画的小国保住重叠区
  var owner=new Int16Array(N); owner.fill(-1);
  var order=[]; for(i=0;i<n;i++) order.push(i);
  order.sort(function(a,b){
    var fa=items[a].fr.ov?0:1, fb=items[b].fr.ov?0:1;
    return fa!==fb ? fa-fb : items[b].area-items[a].area;
  });
  order.forEach(function(ix){
    var m=items[ix].mask;
    for(var cc=0;cc<N;cc++) if(m[cc]) owner[cc]=ix;
  });
  // 3. 距离场 + 缝隙填充
  var d1=new Uint16Array(N), d2=new Uint16Array(N);
  var i1=new Int16Array(N), i2=new Int16Array(N);
  d1.fill(0xFFFF); d2.fill(0xFFFF); i1.fill(-1); i2.fill(-1);
  var tmp=new Uint16Array(N);
  items.forEach(function(it,ix){
    tmp.fill(0xFFFF);
    var seeds=[];
    for(var cc=0;cc<N;cc++){
      if(!it.mask[cc]) continue;
      var cx=cc%GNX, cy=(cc-cx)/GNX;
      if(cx===0||cy===0||cx===GNX-1||cy===GNY-1||
         !it.mask[cc-1]||!it.mask[cc+1]||!it.mask[cc-GNX]||!it.mask[cc+GNX]) seeds.push(cc);
    }
    bfs(tmp,seeds,it.fmax,2,owner);
    for(cc=0;cc<N;cc++){
      var v=tmp[cc]; if(v===0xFFFF||it.mask[cc]) continue;
      if(v<d1[cc]){ d2[cc]=d1[cc]; i2[cc]=i1[cc]; d1[cc]=v; i1[cc]=ix; }
      else if(v<d2[cc]){ d2[cc]=v; i2[cc]=ix; }
    }
  });
  var own2=new Int16Array(N);
  for(c=0;c<N;c++){
    var o=owner[c];
    if(o<0 && landMask[c] && i1[c]>=0){
      var A=items[i1[c]];
      if(d1[c]<=A.fmax){
        var betweenStates=i2[c]>=0 && d1[c]+d2[c]<=Math.min(A.gap, items[i2[c]].gap);
        var toCoast=d1[c]+seaDist[c]<=Math.min(GAPSEA, A.gap);
        if(betweenStates||toCoast) o=i1[c];
      }
    }
    own2[c]=o;
  }
  // 3.5 多数表决平滑: 仅作用于填充所得/无主的陆地格 (原始疆界内的格子不动),
  //     抹平距离场等值线的锯齿、消除孤立小块; 只统计陆地邻格, 不侵蚀沿海窄条
  var cnt=new Int16Array(n+2);
  for(var pass=0;pass<2;pass++){
    var nxt=new Int16Array(own2);
    for(c=0;c<N;c++){
      if(!landMask[c]||owner[c]>=0) continue;
      var mx=c%GNX, my=(c-mx)/GNX, k2;
      for(k2=0;k2<n+2;k2++) cnt[k2]=0;
      for(k2=0;k2<8;k2++){
        var qx=mx+KX[k2], qy=my+KY[k2];
        if(qx<0||qy<0||qx>=GNX||qy>=GNY) continue;
        var qc=qy*GNX+qx;
        if(!landMask[qc]) continue;
        cnt[own2[qc]+1]++;
      }
      var bl=own2[c], bc=4;
      for(k2=0;k2<n+1;k2++) if(cnt[k2]>bc){ bc=cnt[k2]; bl=k2-1; }
      if(bl!==own2[c]) nxt[c]=bl;
    }
    own2=nxt;
  }
  // 3.6 无主小飞地填充: 被政权与海岸围住的无主小块(如半岛尖端、疆界与海
  //     之间的死角)逐圈划归相邻政权; 大片无主之地(无数据的邻邦、草原、
  //     未被任何政权触及的岛屿)保持原样
  var POCKET_MAX=160;                       // ≈3.6平方度
  var visited=new Uint8Array(N), stack=[];
  for(c=0;c<N;c++){
    if(visited[c]||!landMask[c]||own2[c]>=0) continue;
    var cells=[c]; visited[c]=1; stack.length=0; stack.push(c);
    var adjOwn=false, atEdge=false;
    while(stack.length){
      var cc=stack.pop();
      var sx=cc%GNX, sy=(cc-sx)/GNX;
      if(sx===0||sy===0||sx===GNX-1||sy===GNY-1) atEdge=true;
      for(var k4=0;k4<4;k4++){
        var tx=sx+KX[k4], ty=sy+KY[k4];
        if(tx<0||ty<0||tx>=GNX||ty>=GNY) continue;
        var tc=ty*GNX+tx;
        if(!landMask[tc]) continue;
        if(own2[tc]>=0){ adjOwn=true; continue; }
        if(!visited[tc]){ visited[tc]=1; cells.push(tc); stack.push(tc); }
      }
    }
    if(!adjOwn||atEdge||cells.length>POCKET_MAX) continue;
    var frontier=cells, guard=0;
    while(frontier.length && guard++<POCKET_MAX){
      var rest=[], assign=[];
      for(var fi=0;fi<frontier.length;fi++){
        var fc=frontier[fi], fx=fc%GNX, fy=(fc-fx)/GNX, fo=-1;
        for(var k5=0;k5<8;k5++){
          var ux=fx+KX[k5], uy=fy+KY[k5];
          if(ux<0||uy<0||ux>=GNX||uy>=GNY) continue;
          var uc=uy*GNX+ux;
          if(landMask[uc]&&own2[uc]>=0){ fo=own2[uc]; break; }
        }
        if(fo>=0) assign.push(fc,fo); else rest.push(fc);
      }
      if(!assign.length) break;
      for(var ai=0;ai<assign.length;ai+=2) own2[assign[ai]]=assign[ai+1];
      frontier=rest;
    }
  }
  // 4. 近岸外扩两格 (最终被陆地剪裁, 仅保证覆盖到真实海岸线/近岸小岛)
  for(var round=0;round<2;round++){
    var adds=[];
    for(c=0;c<N;c++){
      if(landMask[c]||own2[c]>=0) continue;
      var cx=c%GNX, cy=(c-cx)/GNX;
      for(var k=0;k<8;k++){
        var nx=cx+KX[k], ny=cy+KY[k];
        if(nx<0||ny<0||nx>=GNX||ny>=GNY) continue;
        var o2=own2[ny*GNX+nx];
        if(o2>=0){ adds.push(c,o2); break; }
      }
    }
    for(i=0;i<adds.length;i+=2) own2[adds[i]]=adds[i+1];
  }
  // 5. 每国描迹 + 平滑
  items.forEach(function(it){ it.fin=new Uint8Array(N); });
  for(c=0;c<N;c++) if(own2[c]>=0) items[own2[c]].fin[c]=1;
  items.forEach(function(it){
    var rings=traceMask(it.fin);
    it.rings=rings.length?smoothRings(rings)
      :it.raw.map(function(r){ return r.map(function(p){ return [p[0],p[1]]; }); });
  });
  // 6. 拉锯/占领重叠区 (帧数据 ov:1 标记) → 斜纹层
  var stripes=[];
  for(i=0;i<n;i++)for(j=i+1;j<n;j++){
    if(!(items[i].fr.ov||items[j].fr.ov)) continue;
    var pm=null, cnt=0;
    for(c=0;c<N;c++){
      if(items[i].mask[c]&&items[j].mask[c]){
        var oo=own2[c];
        if(!landMask[c]||oo===i||oo===j){ if(!pm)pm=new Uint8Array(N); pm[c]=1; cnt++; }
      }
    }
    if(cnt>2){
      var rr=smoothRings(traceMask(pm));
      if(rr.length) stripes.push({a:i,b:j,rings:rr});
    }
  }
  return stripes;
}

/* ---------- 状态 ---------- */
var state={ t:1005, lo:T0, hi:T1, zoomStack:[], playing:false, speed:1, sel:null, vb:[0,0,W,H] };
var SVGNS='http://www.w3.org/2000/svg';
function el(n,attrs,parent){
  var e=document.createElementNS(SVGNS,n);
  for(var k in attrs) e.setAttribute(k,attrs[k]);
  if(parent) parent.appendChild(e);
  return e;
}
function div(cls,parent,html){
  var e=document.createElement('div'); if(cls)e.className=cls;
  if(html!==undefined)e.innerHTML=html; if(parent)parent.appendChild(e); return e;
}
function esc(s){ return String(s==null?'':s).replace(/&/g,'&amp;').replace(/</g,'&lt;'); }

/* ---------- SVG 地图基础 ---------- */
var svg, defs, gBase, gPolity, gStripe, gBorder, gLabel, tooltip;
function buildMap(){
  var wrap=document.getElementById('map');
  svg=el('svg',{viewBox:'0 0 '+W+' '+H, id:'mapsvg'}); wrap.appendChild(svg);
  defs=el('defs',{},svg);
  // 海洋
  el('rect',{x:-2000,y:-2000,width:5000,height:5000,'class':'sea'},svg);
  // 陆地剪裁路径
  var clip=el('clipPath',{id:'landclip'},defs);
  var landD='';
  BASEMAP.land.forEach(function(r){ landD+=pathOf([r]); });
  el('path',{d:landD},clip);
  gBase=el('g',{},svg);
  el('path',{d:landD,'class':'land'},gBase);
  // 湖泊与河流
  BASEMAP.lakes.forEach(function(r){ el('path',{d:pathOf([r]),'class':'lake'},gBase); });
  BASEMAP.rivers.forEach(function(rv){
    var d=''; rv.p.forEach(function(p,i){ d+=(i?'L':'M')+PX(p[0]).toFixed(1)+' '+PY(p[1]).toFixed(1); });
    el('path',{d:d,'class':'river'},gBase);
  });
  gPolity=el('g',{'clip-path':'url(#landclip)'},svg);
  gStripe=el('g',{'clip-path':'url(#landclip)'},svg);
  gBorder=el('g',{'clip-path':'url(#landclip)','class':'noptr'},svg);
  gLabel=el('g',{'class':'noptr'},svg);
  tooltip=div('tooltip',document.body); tooltip.style.display='none';
  initPanZoom(wrap);
}

/* ---------- 地图平移缩放 ---------- */
function applyVB(){ svg.setAttribute('viewBox',state.vb.join(' ')); }
function initPanZoom(wrap){
  var dragging=false,moved=false,px=0,py=0;
  wrap.addEventListener('pointerdown',function(e){
    if(e.target.closest('.panel,.card,.modal'))return;
    dragging=true;moved=false;px=e.clientX;py=e.clientY;
  });
  window.addEventListener('pointermove',function(e){
    if(!dragging)return;
    var dx=e.clientX-px, dy=e.clientY-py;
    if(Math.abs(dx)+Math.abs(dy)>4)moved=true;
    if(moved){
      var r=wrap.getBoundingClientRect();
      var k=state.vb[2]/r.width;
      state.vb[0]-=dx*k; state.vb[1]-=dy*k; applyVB();
      px=e.clientX;py=e.clientY;
    }
  });
  window.addEventListener('pointerup',function(){ dragging=false; setTimeout(function(){moved=false;},0); });
  wrap.addEventListener('wheel',function(e){
    e.preventDefault();
    var r=wrap.getBoundingClientRect();
    var mx=state.vb[0]+(e.clientX-r.left)/r.width*state.vb[2];
    var my=state.vb[1]+(e.clientY-r.top)/r.height*state.vb[3];
    var f=e.deltaY>0?1.18:1/1.18;
    var w=Math.min(Math.max(state.vb[2]*f,140),2600), h=w*H/W;
    state.vb=[mx-(mx-state.vb[0])*w/state.vb[2], my-(my-state.vb[1])*h/state.vb[3], w, h];
    applyVB();
  },{passive:false});
  wrap._movedRef=function(){return moved;};
}

/* ---------- 政权 活跃/边框 ---------- */
function frameAt(p,t){
  var fs=p.frames;
  for(var i=0;i<fs.length;i++) if(t>=fs[i].f && t<fs[i].t) return fs[i];
  return null;
}
function activeList(t){
  var out=[];
  POLITIES.forEach(function(p){
    if(t>=p.f && t<p.t){
      var fr=frameAt(p,t);
      if(fr) out.push({p:p,fr:fr});
    }
  });
  // 中原主线排前 (条纹绘制顺序: 先大后小)
  out.sort(function(a,b){
    var w=function(x){return x.p.tp==='c'?0:(x.p.tp==='s'?1:2);};
    return w(a)-w(b);
  });
  return out;
}

/* ---------- 渲染地图图层 ---------- */
var lastKey='';
function renderMap(){
  var act=activeList(state.t);
  var key=act.map(function(a){return a.p.id+'@'+a.fr.f;}).join('|');
  if(key===lastKey){ return act; }
  lastKey=key;
  gPolity.innerHTML=''; gStripe.innerHTML=''; gBorder.innerHTML=''; gLabel.innerHTML='';
  // 清理旧 pattern/clip
  Array.prototype.slice.call(defs.querySelectorAll('.dyn')).forEach(function(n){n.remove();});

  var items=act.map(function(a){
    return {p:a.p, fr:a.fr, raw:a.fr.ps};
  });
  var stripes=refineItems(items);
  items.forEach(function(it){ it.d=pathOf(it.rings); });
  // 填充 + 交互 (同色描边盖住相邻色块间的抗锯齿细缝)
  items.forEach(function(it){
    var path=el('path',{d:it.d,fill:it.p.c,stroke:it.p.c,'stroke-width':1.1,'stroke-linejoin':'round','fill-opacity':0.88,'class':'polity'},gPolity);
    path.addEventListener('pointerenter',function(e){ showTip(it.p,e); path.setAttribute('fill-opacity',1); });
    path.addEventListener('pointermove',function(e){ moveTip(e); });
    path.addEventListener('pointerleave',function(){ hideTip(); path.setAttribute('fill-opacity',0.88); });
    path.addEventListener('click',function(e){
      if(document.getElementById('map')._movedRef()) return;
      e.stopPropagation(); hideTip(); openCard(it.p);
    });
    el('path',{d:it.d,'class':'polity-border'},gBorder);
  });
  // 拉锯/占领重叠区条纹 (仅数据 ov:1 标记的政权参与)
  stripes.forEach(function(s){
    var A=items[s.a], B=items[s.b];
    var pid='pat_'+A.p.id+'_'+B.p.id;
    var pat=el('pattern',{id:pid,'class':'dyn',width:14,height:14,patternUnits:'userSpaceOnUse',patternTransform:'rotate(45)'},defs);
    el('rect',{x:0,y:0,width:7,height:14,fill:A.p.c},pat);
    el('rect',{x:7,y:0,width:7,height:14,fill:B.p.c},pat);
    el('path',{d:pathOf(s.rings),fill:'url(#'+pid+')','fill-opacity':0.96,'class':'noptr'},gStripe);
  });
  // 标签
  items.forEach(function(it){
    var best=null;
    it.rings.forEach(function(r){
      var c=centroidOf(r);
      if(!best||c[2]>best[2])best=c;
    });
    if(!best)return;
    var fs=Math.max(11,Math.min(46,Math.sqrt(best[2])/3.2));
    var t=el('text',{x:best[0],y:best[1],'class':'plabel','font-size':fs},gLabel);
    t.textContent=it.p.abbr;
    if(fs>17 && it.p.n!==it.p.abbr){
      var t2=el('text',{x:best[0],y:best[1]+fs*0.78,'class':'plabel sub','font-size':Math.max(9,fs*0.3)},gLabel);
      t2.textContent=it.p.n;
    }
  });
  return act;
}

/* ---------- 提示框 ---------- */
function showTip(p,e){
  tooltip.innerHTML='<b>'+esc(p.n)+'</b><span>'+fmtRange(p.f,p.t)+' · 存续'+durText(p.f,p.t)+'</span><i>点击查看详情</i>';
  tooltip.style.display='block'; moveTip(e);
}
function moveTip(e){ tooltip.style.left=(e.clientX+14)+'px'; tooltip.style.top=(e.clientY+14)+'px'; }
function hideTip(){ tooltip.style.display='none'; }

/* ---------- 政权详情卡 ---------- */
function openCard(p){
  state.sel=p.id;
  var c=document.getElementById('card');
  var pop=(p.pop||[]).map(function(x){
    return '<tr><td>'+fmtY(x[0])+'</td><td>'+esc(x[1])+'</td></tr>';
  }).join('');
  var srcs=(p.srcs||[]).map(function(id){
    var s=SOURCES.find(function(s){return s.id===id;});
    return s?'<li>'+esc(s.zh)+'</li>':'';
  }).join('');
  c.innerHTML=
    '<div class="card-head" style="border-color:'+p.c+'">'+
      '<span class="chip" style="background:'+p.c+'">'+esc(p.abbr)+'</span>'+
      '<div><h2>'+esc(p.n)+'</h2><p>'+fmtRange(p.f,p.t)+' · 存续'+durText(p.f,p.t)+'</p></div>'+
      '<button class="x" id="cardx">✕</button></div>'+
    '<div class="card-body">'+
      '<dl>'+
      '<dt>都城</dt><dd>'+esc(p.cap||'—')+'</dd>'+
      '<dt>开创</dt><dd>'+esc(p.fdr||'—')+'</dd>'+
      '<dt>结局</dt><dd>'+esc(p.lr||'—')+'</dd>'+
      '</dl>'+
      (pop?'<h3>人口</h3><table class="pop">'+pop+'</table>':'')+
      (p.note?'<h3>概述</h3><p class="note">'+esc(p.note)+'</p>':'')+
      (srcs?'<h3>本条主要来源</h3><ul class="srcs">'+srcs+'</ul>':'')+
      '<button class="linkbtn" onclick="document.getElementById(\'srcbtn\').click()">查看全部来源与精度说明 →</button>'+
    '</div>';
  c.style.display='flex';
  document.getElementById('cardx').onclick=closeCard;
}
function closeCard(){ document.getElementById('card').style.display='none'; state.sel=null; }

/* ---------- 浮动面板 (帝王 / 政权) ---------- */
var panelTab='emp';
function buildPanel(){
  var p=document.getElementById('panel');
  p.innerHTML='<div class="phead" id="phead"><span class="grip">⣿</span>'+
    '<div class="tabs"><button id="tab-emp" class="on">帝王</button><button id="tab-dyn">政权</button></div>'+
    '<button class="mini" id="pfold">—</button></div>'+
    '<div class="pbody" id="pbody"></div>';
  document.getElementById('tab-emp').onclick=function(){setTab('emp');};
  document.getElementById('tab-dyn').onclick=function(){setTab('dyn');};
  var folded=false;
  document.getElementById('pfold').onclick=function(){
    folded=!folded;
    document.getElementById('pbody').style.display=folded?'none':'block';
    this.textContent=folded?'+':'—';
  };
  // 拖动
  var head=document.getElementById('phead'), sx=0,sy=0,ox=0,oy=0,drag=false;
  head.addEventListener('pointerdown',function(e){
    if(e.target.tagName==='BUTTON')return;
    drag=true; sx=e.clientX; sy=e.clientY;
    var r=p.getBoundingClientRect(); ox=r.left; oy=r.top;
    head.setPointerCapture(e.pointerId);
  });
  head.addEventListener('pointermove',function(e){
    if(!drag)return;
    var x=Math.min(window.innerWidth-120,Math.max(4,ox+e.clientX-sx));
    var y=Math.min(window.innerHeight-80,Math.max(4,oy+e.clientY-sy));
    p.style.left=x+'px'; p.style.top=y+'px'; p.style.right='auto';
  });
  head.addEventListener('pointerup',function(){drag=false;});
}
function setTab(t){
  panelTab=t;
  document.getElementById('tab-emp').className=t==='emp'?'on':'';
  document.getElementById('tab-dyn').className=t==='dyn'?'on':'';
  renderPanel(true);
}
function eraAt(emp,t){
  if(!emp.e||!emp.e.length)return null;
  var cur=null;
  emp.e.forEach(function(x){ if(t>=x[1])cur=x; });
  return cur;
}
function avatarSVG(emp,color){
  var ch=emp.n.replace(/[·(].*$/,''); ch=ch.charAt(ch.length-1);
  return '<svg viewBox="0 0 44 44"><circle cx="22" cy="22" r="20" fill="'+color+'"/>'+
    '<circle cx="22" cy="22" r="20" fill="none" stroke="rgba(255,255,255,.55)" stroke-width="1.6"/>'+
    '<text x="22" y="29" text-anchor="middle" font-size="20" fill="#fff" font-family="Songti SC,STSong,serif" font-weight="700">'+esc(ch)+'</text></svg>';
}
var lastPanelKey='';
function renderPanel(force){
  var act=activeList(state.t);
  var body=document.getElementById('pbody');
  if(panelTab==='emp'){
    var ids={}; act.forEach(function(a){ids[a.p.id]=a.p;});
    var rows=[];
    EMPERORS.forEach(function(emp,idx){
      if(state.t>=emp.rf && state.t<emp.rt && ids[emp.y]) rows.push({e:emp,i:idx,p:ids[emp.y]});
    });
    var key='e'+rows.map(function(r){return r.i;}).join(',')+'~'+Math.round(state.t*12);
    if(!force && key===lastPanelKey)return; lastPanelKey=key;
    if(!rows.length){ body.innerHTML='<p class="empty">此刻无在位君主记录<br><small>(史前时代、现代或数据未及之政权)</small></p>'; return; }
    body.innerHTML=rows.map(function(r){
      var e=r.e, era=eraAt(e,state.t);
      var pred=null,succ=null;
      for(var i=r.i-1;i>=0;i--) if(EMPERORS[i].y===e.y){pred=EMPERORS[i];break;}
      for(var j=r.i+1;j<EMPERORS.length;j++) if(EMPERORS[j].y===e.y){succ=EMPERORS[j];break;}
      var age=e.b!=null?('<b>'+Math.max(0,Math.floor(state.t-e.b))+'岁</b>'):'生年不详';
      var life=(e.b!=null?fmtY(yearOf(e.b)):'?')+' — '+(e.d!=null?fmtY(yearOf(e.d)):'?');
      var reignYrs=state.t-e.rf;
      var reignTxt=reignYrs<1?('在位第'+Math.max(1,Math.ceil(reignYrs*365))+'天'):('在位第'+Math.ceil(reignYrs)+'年');
      return '<div class="emp">'+
        '<div class="eav">'+avatarSVG(e,r.p.c)+'</div>'+
        '<div class="einfo">'+
          '<div class="el1"><b>'+esc(e.t)+'</b><span class="dyntag" style="background:'+r.p.c+'">'+esc(r.p.abbr)+'</span></div>'+
          '<div class="el2">名讳 '+esc(e.n)+(e.tm?' · 庙号'+esc(e.tm):'')+(e.sh?' · 谥'+esc(e.sh):'')+'</div>'+
          '<div class="el2">'+(era?'年号 <b>'+esc(era[0])+'</b>('+Math.max(1,Math.ceil(state.t-era[1]))+'年) · ':'')+reignTxt+'</div>'+
          '<div class="el2">'+life+' · 现年'+age+'</div>'+
          '<div class="el3">'+(pred?'← '+esc(pred.t):'← 开国')+' &nbsp; '+(succ?esc(succ.t)+' →':'末代 →')+'</div>'+
          (e.note?'<div class="enote">'+esc(e.note)+'</div>':'')+
        '</div></div>';
    }).join('');
  } else {
    var key2='d'+act.map(function(a){return a.p.id;}).join(',')+'~'+Math.round(state.t*4);
    if(!force && key2===lastPanelKey)return; lastPanelKey=key2;
    if(!act.length){ body.innerHTML='<p class="empty">此刻无政权记录</p>'; return; }
    body.innerHTML=act.map(function(a){
      var p=a.p;
      var frac=Math.min(1,Math.max(0,(state.t-p.f)/(p.t-p.f)));
      var leftPct=Math.round((1-frac)*100);
      return '<div class="dyn-row" data-id="'+p.id+'">'+
        '<span class="chip" style="background:'+p.c+'">'+esc(p.abbr)+'</span>'+
        '<div class="dinfo"><div class="dl1"><b>'+esc(p.n)+'</b><span>'+fmtY(yearOf(p.f))+' — '+fmtY(yearOf(p.t))+'</span></div>'+
        '<div class="lifebar"><div class="lifefill" style="width:'+(frac*100).toFixed(1)+'%;background:'+p.c+'"></div><div class="lifedot" style="left:'+(frac*100).toFixed(1)+'%"></div></div>'+
        '<div class="dl2">已历'+durText(p.f,state.t)+' · 国祚余'+leftPct+'%</div></div></div>';
    }).join('');
    Array.prototype.forEach.call(body.querySelectorAll('.dyn-row'),function(row){
      row.onclick=function(){
        var p=POLITIES.find(function(x){return x.id===row.dataset.id;});
        if(p)openCard(p);
      };
    });
  }
}

/* ---------- 时间轴 ---------- */
var ANCH=[[-8000,0],[-2070,0.10],[-770,0.24],[-221,0.36],[220,0.46],[907,0.60],[1368,0.775],[1912,0.92],[2026.5,1]];
function isFull(){ return state.lo===T0 && state.hi===T1; }
function valToPos(v){
  if(!isFull()) return (v-state.lo)/(state.hi-state.lo);
  for(var i=0;i<ANCH.length-1;i++){
    if(v<=ANCH[i+1][0]||i===ANCH.length-2){
      var a=ANCH[i],b=ANCH[i+1];
      return a[1]+(v-a[0])/(b[0]-a[0])*(b[1]-a[1]);
    }
  }
  return 1;
}
function posToVal(f){
  f=Math.min(1,Math.max(0,f));
  if(!isFull()) return state.lo+f*(state.hi-state.lo);
  for(var i=0;i<ANCH.length-1;i++){
    if(f<=ANCH[i+1][1]||i===ANCH.length-2){
      var a=ANCH[i],b=ANCH[i+1];
      return a[0]+(f-a[1])/(b[1]-a[1])*(b[0]-a[0]);
    }
  }
  return T1;
}
function tickStep(span){
  if(span>4000)return 1000; if(span>1600)return 500; if(span>700)return 200;
  if(span>280)return 100; if(span>130)return 50; if(span>55)return 20;
  if(span>26)return 10; if(span>11)return 5; if(span>4.5)return 2;
  if(span>2.2)return 1; if(span>0.45)return 1/12; return 1/365;
}
var tlCanvas, tlThumb, tlWrap;
function drawTimeline(){
  var r=tlWrap.getBoundingClientRect();
  var dpr=window.devicePixelRatio||1;
  tlCanvas.width=r.width*dpr; tlCanvas.height=54*dpr;
  tlCanvas.style.width=r.width+'px'; tlCanvas.style.height='54px';
  var ctx=tlCanvas.getContext('2d'); ctx.scale(dpr,dpr);
  ctx.clearRect(0,0,r.width,54);
  var span=state.hi-state.lo;
  // 时期底色带 (全览时)
  if(isFull()){
    var bands=[[-8000,-2070,'#3a3427','史前'],[-2070,-770,'#4a3b22','夏商周'],[-770,-221,'#3d3040','春秋战国'],[-221,589,'#31404d','秦汉魏晋南北朝'],[589,979,'#4d4327','隋唐五代'],[979,1279,'#4d2b2b','宋辽金'],[1279,1644,'#2b3d4d','元明'],[1644,1912,'#4a3f20','清'],[1912,1949.75,'#28405c','民国'],[1949.75,2026.5,'#5c2a2a','共和国']];
    bands.forEach(function(b){
      var x0=valToPos(b[0])*r.width, x1=valToPos(b[1])*r.width;
      ctx.fillStyle=b[2]; ctx.fillRect(x0,26,x1-x0,14);
      if(x1-x0>34){ ctx.fillStyle='rgba(255,240,210,.75)'; ctx.font='10px sans-serif'; ctx.textAlign='center'; ctx.fillText(b[3],(x0+x1)/2,36.5); }
    });
  } else {
    ctx.fillStyle='rgba(160,140,90,.18)'; ctx.fillRect(0,26,r.width,14);
  }
  // 刻度
  var step=tickStep(span);
  var v0=Math.ceil(state.lo/step)*step;
  ctx.strokeStyle='rgba(220,200,150,.5)'; ctx.fillStyle='rgba(235,220,180,.9)';
  ctx.font='10px sans-serif'; ctx.textAlign='center';
  var lastX=-100;
  for(var v=v0;v<=state.hi+1e-9;v+=step){
    var x=valToPos(v)*r.width;
    ctx.beginPath(); ctx.moveTo(x,18); ctx.lineTo(x,26); ctx.stroke();
    if(x-lastX>42){
      var lab;
      if(step>=1) lab=(v<=0?'前'+Math.round(-v):Math.round(v));
      else if(step>=1/12-1e-9){ var o=ymd(v+1e-6); lab=o.m+'月'; if(o.m===1)lab=fmtY(o.y); }
      else { var o2=ymd(v+1e-6); lab=o2.m+'/'+o2.d; }
      ctx.fillText(String(lab),x,14); lastX=x;
    }
  }
  // 缩放窗口指示与按钮状态
  document.getElementById('tl-range').textContent=
    isFull() ? '' : fmtDate(state.lo,span)+' ~ '+fmtDate(state.hi,span);
  document.getElementById('tl-in').disabled=span<=0.03;
  document.getElementById('tl-out').disabled=isFull();
  document.getElementById('tl-reset').disabled=isFull();
  positionThumb();
  updateHeader();
}
function positionThumb(){
  var r=tlWrap.getBoundingClientRect();
  tlThumb.style.left=(valToPos(state.t)*r.width)+'px';
}
function setT(t,skipMap){
  state.t=Math.min(T1-0.0001,Math.max(T0,t));
  positionThumb();
  updateHeader();
  if(!skipMap){ renderMap(); renderPanel(); }
  // 若详情卡的政权已消亡则关闭
  if(state.sel){
    var p=POLITIES.find(function(x){return x.id===state.sel;});
    if(p&&(state.t<p.f||state.t>=p.t)) closeCard();
  }
}
function zoomTimeline(center){
  var span=state.hi-state.lo;
  if(span<=0.03) return false;
  var ns=Math.max(0.03, span/6);
  // 全览首次缩放取800年窗口以获得舒适密度
  if(isFull()) ns=800;
  var lo=center-ns/2, hi=center+ns/2;
  if(lo<T0){lo=T0;hi=T0+ns;} if(hi>T1){hi=T1;lo=T1-ns;}
  state.zoomStack.push([state.lo,state.hi]);
  state.lo=lo; state.hi=hi;
  drawTimeline();
  flashZoom();
  return true;
}
function resetZoom(){
  state.zoomStack=[]; state.lo=T0; state.hi=T1; drawTimeline();
}
function zoomOutOnce(){
  var prev=state.zoomStack.pop();
  if(prev){ state.lo=prev[0]; state.hi=prev[1]; } else { state.lo=T0; state.hi=T1; }
  drawTimeline();
}
function flashZoom(){
  tlWrap.classList.add('zooming');
  setTimeout(function(){tlWrap.classList.remove('zooming');},350);
}
function initTimeline(){
  tlWrap=document.getElementById('tl-track');
  tlCanvas=document.getElementById('tl-canvas');
  tlThumb=document.getElementById('tl-thumb');
  var isDown=false;
  function evPos(e){
    var r=tlWrap.getBoundingClientRect();
    return (e.clientX-r.left)/r.width;
  }
  tlWrap.addEventListener('pointerdown',function(e){
    isDown=true;
    tlWrap.setPointerCapture(e.pointerId);
    setT(posToVal(evPos(e)));
  });
  tlWrap.addEventListener('pointermove',function(e){
    if(!isDown)return;
    setT(posToVal(evPos(e)));
  });
  function up(){ isDown=false; }
  tlWrap.addEventListener('pointerup',up);
  tlWrap.addEventListener('pointercancel',up);
  document.getElementById('tl-in').onclick=function(){ zoomTimeline(state.t); };
  document.getElementById('tl-reset').onclick=resetZoom;
  document.getElementById('tl-out').onclick=zoomOutOnce;
  window.addEventListener('resize',drawTimeline);
  window.addEventListener('keydown',function(e){
    if(e.target.tagName==='INPUT')return;
    var span=state.hi-state.lo;
    if(e.key==='ArrowLeft'){ setT(state.t-span/400); e.preventDefault(); }
    if(e.key==='ArrowRight'){ setT(state.t+span/400); e.preventDefault(); }
    if(e.key===' '){ togglePlay(); e.preventDefault(); }
  });
}

/* ---------- 播放 ---------- */
var rafId=null,lastTs=0;
function togglePlay(){
  state.playing=!state.playing;
  document.getElementById('playbtn').textContent=state.playing?'⏸':'▶';
  if(state.playing){ lastTs=0; rafId=requestAnimationFrame(tick); }
  else if(rafId) cancelAnimationFrame(rafId);
}
function tick(ts){
  if(!state.playing)return;
  if(lastTs){
    var dt=(ts-lastTs)/1000;
    var span=state.hi-state.lo;
    var rate=isFull()? 40 : span/18;   // 年/秒
    var nt=state.t+dt*rate*state.speed;
    if(nt>=T1-0.001){ nt=T1-0.001; togglePlay(); }
    setT(nt);
  }
  lastTs=ts;
  rafId=requestAnimationFrame(tick);
}

/* ---------- 顶栏 ---------- */
function updateHeader(){
  var span=state.hi-state.lo;
  document.getElementById('bigdate').textContent=fmtDate(state.t,span);
  var act=activeList(state.t);
  var main=act.filter(function(a){return a.p.tp==='c';}).map(function(a){return a.p.n;});
  var era=document.getElementById('eraline');
  era.textContent = main.length? main.join(' · ') : (act.length?act[0].p.n+' 等':'—');
}

/* ---------- 来源弹窗 ---------- */
function buildSources(){
  var m=document.getElementById('modal');
  var list=SOURCES.map(function(s){
    return '<li><b>'+esc(s.zh)+'</b><p>'+esc(s.detail)+'</p>'+(s.url?'<a href="'+s.url+'" target="_blank" rel="noopener">'+esc(s.url)+'</a>':'')+'</li>';
  }).join('');
  var notes=SOURCE_NOTES.map(function(n){return '<li>'+esc(n)+'</li>';}).join('');
  m.innerHTML='<div class="mbox"><div class="mhead"><h2>数据来源与精度说明</h2><button class="x" id="mx">✕</button></div>'+
    '<div class="mbody"><h3>⚠ 精度与取舍说明</h3><ul class="notes">'+notes+'</ul>'+
    '<h3>主要文献与数据集</h3><ul class="srclist">'+list+'</ul></div></div>';
  m.querySelector('#mx').onclick=function(){m.style.display='none';};
  m.addEventListener('click',function(e){ if(e.target===m)m.style.display='none'; });
  document.getElementById('srcbtn').onclick=function(){ m.style.display='flex'; };
  var h=document.getElementById('helpmodal');
  h.querySelector('#hx').onclick=function(){h.style.display='none';};
  h.addEventListener('click',function(e){ if(e.target===h)h.style.display='none'; });
  document.getElementById('helpbtn').onclick=function(){ h.style.display='flex'; };
}

/* ---------- 启动 ---------- */
function init(){
  buildLandGrid();
  buildMap();
  buildPanel();
  buildSources();
  initTimeline();
  document.getElementById('playbtn').onclick=togglePlay;
  document.getElementById('speed').onchange=function(){ state.speed=parseFloat(this.value); };
  document.getElementById('map').addEventListener('click',function(e){
    if(e.target.tagName!=='path'||!e.target.classList.contains('polity')) closeCard();
  });
  drawTimeline();
  var h=parseFloat((location.hash||'').replace(/^#/,''));
  setT(isFinite(h)?h:1005);   // 默认: 澶渊之盟之年 —— 宋辽夏并立, 画面最丰富; 可用 #年份 直达
  renderPanel(true);
}
if(document.readyState==='loading') document.addEventListener('DOMContentLoaded',init);
else init();
})();
