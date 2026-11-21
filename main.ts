import {mkdirSync,readdirSync,readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
const I=process.env.MAKEFUN_INPUT_DIR??'/input';
const O=process.env.MAKEFUN_OUTPUT_DIR??'/output';
const DIRS:[[number,number,string]]=[[0,-1,'u'],[0,1,'d'],[-1,0,'l'],[1,0,'r']];
type L={w:number;h:number;wall:boolean[];goals:number[];boxes:number[];player:number};
function parse(t:string):L{
  const rows=t.split('\n');
  while(rows.length&&rows[rows.length-1]==='')rows.pop();
  const w=Math.max(...rows.map(r=>r.length)),h=rows.length,wall:boolean[]=[],goals:number[]=[];
  let boxes:number[]=[],player=0;
  rows.forEach((row,y)=>{for(let x=0;x<w;x++){const c=row[x]??'#',i=y*w+x;wall[i]=c==='#';if('.*+'.includes(c))goals.push(i);if('$*'.includes(c))boxes.push(i);if('@+'.includes(c))player=i;}});
  boxes.sort((a,b)=>a-b);
  return{w,h,wall,goals,boxes,player};
}
function liveCells(l:L):boolean[]{
  const live=new Array(l.w*l.h).fill(false),q=[...l.goals];
  for(const g of l.goals)live[g]=true;
  while(q.length){
    const y=q.shift()!;
    for(const[dx,dy]of DIRS){
      const x=y-dy*l.w-dx;
      if(x<0||x>=l.w*l.h||l.wall[x]||live[x])continue;
      const s=x-dy*l.w-dx;
      if(s<0||s>=l.w*l.h||l.wall[s])continue;
      live[x]=true;q.push(x);
    }
  }
  return live;
}
function reach(l:L,boxes:number[],from:number):Set<number>{
  const seen=new Set<number>([from]),q=[from],bs=new Set(boxes);
  while(q.length){
    const c=q.pop()!;
    for(const[dx,dy]of DIRS){
      const n=c+dy*l.w+dx;
      if(n<0||n>=l.w*l.h||l.wall[n]||bs.has(n)||seen.has(n))continue;
      seen.add(n);q.push(n);
    }
  }
  return seen;
}
function bfsDist(l:L,from:number):number[]{
  const d=new Array(l.w*l.h).fill(Infinity),q=[from];
  d[from]=0;
  while(q.length){
    const c=q.shift()!;
    for(const[dx,dy]of DIRS){
      const n=c+dy*l.w+dx;
      if(n<0||n>=l.w*l.h||l.wall[n]||d[n]!==Infinity)continue;
      d[n]=d[c]!+1;q.push(n);
    }
  }
  return d;
}
function path(l:L,boxes:number[],a:number,b:number):string|null{
  if(a===b)return'';
  const prev=new Map<number,[number,string]>(),q=[a],bs=new Set(boxes);
  prev.set(a,[-1,'']);
  while(q.length){
    const c=q.shift()!;
    for(const[dx,dy,ch]of DIRS){
      const n=c+dy*l.w+dx;
      if(n<0||n>=l.w*l.h||l.wall[n]||bs.has(n)||prev.has(n))continue;
      prev.set(n,[c,ch]);
      if(n===b){
        let s='',t=b;
        while(t!==a){const[p,m]=prev.get(t)!;s=m+s;t=p;}
        return s;
      }
      q.push(n);
    }
  }
  return null;
}
function perms(n:number):number[][]{
  if(n===1)return[[0]];
  const out:number[][]=[];
  for(const p of perms(n-1))for(let i=0;i<n;i++){const q=p.slice();q.splice(i,0,n-1);out.push(q);}
  return out;
}
function dead(l:L,live:boolean[],bs:number[]):boolean{
  const set=new Set(bs),goals=new Set(l.goals);
  for(const b of bs)if(!live[b])return true;
  const N=l.w*l.h;
  const frozen=new Set(bs);
  let changed=true;
  while(changed){
    changed=false;
    for(const b of [...frozen]){
      let can=false;
      for(const[dx,dy]of DIRS){
        const pp=b-dy*l.w-dx,tt=b+dy*l.w+dx;
        if(pp<0||pp>=N||tt<0||tt>=N)continue;
        if(!l.wall[pp]&&!frozen.has(pp)&&!l.wall[tt]&&!frozen.has(tt)){can=true;break;}
      }
      if(can){frozen.delete(b);changed=true;}
    }
  }
  for(const b of frozen)if(!goals.has(b))return true;
  for(let y=0;y<l.h-1;y++)for(let x=0;x<l.w-1;x++){
    const cs=[y*l.w+x,y*l.w+x+1,(y+1)*l.w+x,(y+1)*l.w+x+1];
    if(cs.every(c=>l.wall[c]||set.has(c))&&cs.some(c=>set.has(c))&&!cs.some(c=>goals.has(c)))return true;
  }
  return false;
}
function astar(l:L,exit:number,budget:number):[number,number][]|null{
  const live=liveCells(l),goals=new Set(l.goals),n=l.boxes.length;
  const dg=l.goals.map(g=>bfsDist(l,g)),ps=perms(n);
  const heur=(bs:number[]):number=>{
    let best=Infinity;
    for(const p of ps){
      let s=0,ok=true;
      for(let i=0;i<n;i++){const d=dg[p[i]!]![bs[i]!]!;if(d===Infinity){ok=false;break;}s+=d;}
      if(ok&&s<best)best=s;
    }
    return best;
  };
  const key=(bs:number[],r:number):string=>bs.join(',')+'|'+r;
  const sp:number[]=[l.player],sb:number[][]=[l.boxes.slice()],sg:number[]=[0],par:number[]=[-1],pb:number[]=[-1],pd:number[]=[-1],sk:string[]=[];
  const r0=reach(l,l.boxes,l.player);
  sk.push(key(l.boxes,Math.min(...r0)));
  const best=new Map<string,number>([[sk[0]!,0]]);
  const heap:[number,number,number,number][]=[];
  const less=(a:[number,number,number,number],b:[number,number,number,number]):boolean=>a[0]<b[0]||(a[0]===b[0]&&(a[1]>b[1]||(a[1]===b[1]&&a[2]<b[2])));
  const hpush=(e:[number,number,number,number]):void=>{let i=heap.length;heap.push(e);while(i>0){const p=(i-1)>>1;if(!less(heap[i]!,heap[p]!))break;[heap[i],heap[p]]=[heap[p]!,heap[i]!];i=p;}};
  const hpop=():[number,number,number,number]=>{const t=heap[0]!,last=heap.pop()!;if(heap.length>0){heap[0]=last;for(let i=0;;){let c=2*i+1;if(c>=heap.length)break;if(c+1<heap.length&&less(heap[c+1]!,heap[c]!))c++;if(!less(heap[c]!,heap[i]!))break;[heap[i],heap[c]]=[heap[c]!,heap[i]!];i=c;}}return t;};
  let seq=0,expanded=0;
  hpush([heur(l.boxes),0,seq++,0]);
  while(heap.length>0&&expanded<budget){
    if(sp.length>400000)return null;
    const[,g,,s]=hpop();
    if(best.get(sk[s]!)!==s)continue;
    const bs=sb[s]!;
    if(bs.every(b=>goals.has(b))){
      if(exit<0||reach(l,bs,sp[s]!).has(exit)){
        const out:[number,number][]=[];
        for(let t=s;t>0;t=par[t]!)out.unshift([pb[t]!,pd[t]!]);
        return out;
      }
      continue;
    }
    expanded++;
    const region=reach(l,bs,sp[s]!);
    for(let i=0;i<bs.length;i++){
      const b=bs[i]!;
      for(let di=0;di<4;di++){
        const[dx,dy]=DIRS[di]!;
        const pp=b-dy*l.w-dx,tt=b+dy*l.w+dx;
        if(!region.has(pp))continue;
        if(tt<0||tt>=l.w*l.h||l.wall[tt]||bs.includes(tt))continue;
        const nb=bs.slice();nb[i]=tt;nb.sort((a,b2)=>a-b2);
        if(dead(l,live,nb))continue;
        const rg=reach(l,nb,b),k=key(nb,Math.min(...rg));
        const seen=best.get(k);
        if(seen!==undefined&&sg[seen]!<=g+1)continue;
        const t=sp.length;
        sp.push(b);sb.push(nb);sg.push(g+1);par.push(s);pb.push(b);pd.push(di);sk.push(k);
        best.set(k,t);
        hpush([g+1+heur(nb),g+1,seq++,t]);
      }
    }
  }
  return null;
}
function expand(l:L,pushes:[number,number][],player:number,boxes:number[]):[string,number,number[]]|null{
  let moves='',cur=player,curBoxes=boxes.slice();
  for(const[box,di]of pushes){
    const[dx,dy]=DIRS[di]!;
    const pp=box-dy*l.w-dx;
    const wp=path(l,curBoxes,cur,pp);
    if(wp===null)return null;
    moves+=wp+DIRS[di]![2];
    cur=box;
    const ix=curBoxes.indexOf(box);
    curBoxes[ix]=box+dy*l.w+dx;
    curBoxes.sort((a,b)=>a-b);
  }
  return[moves,cur,curBoxes];
}
function whole(l:L):string{
  const r=astar(l,-1,250000);
  if(!r)return'';
  const e=expand(l,r,l.player,l.boxes);
  return e?e[0]:'';
}
function decompose(l:L):{door:number;cells:Set<number>;boxes:number[];goals:number[];}[]|null{
  const floor:number[]=[];
  for(let i=0;i<l.w*l.h;i++)if(!l.wall[i])floor.push(i);
  const cands:{door:number;cells:Set<number>;boxes:number[];goals:number[]}[]=[];
  for(const v of floor){
    const seen=new Set<number>();
    for(const s of floor){
      if(s===v||seen.has(s))continue;
      const comp=new Set<number>(),q=[s];
      seen.add(s);comp.add(s);
      while(q.length){
        const c=q.pop()!;
        for(const[dx,dy]of DIRS){
          const n=c+dy*l.w+dx;
          if(n===v||l.wall[n]||seen.has(n))continue;
          seen.add(n);comp.add(n);q.push(n);
        }
      }
      const bs=l.boxes.filter(b=>comp.has(b)),gs=l.goals.filter(g=>comp.has(g));
      if(bs.length>=3&&bs.length<=4&&bs.length===gs.length&&!comp.has(l.player))cands.push({door:v,cells:comp,boxes:bs,goals:gs});
    }
  }
  cands.sort((a,b)=>a.cells.size-b.cells.size);
  const used=new Set<number>(),rooms:{door:number;cells:Set<number>;boxes:number[];goals:number[]}[]=[];
  for(const c of cands){
    if(c.boxes.some(b=>used.has(b)))continue;
    c.boxes.forEach(b=>used.add(b));
    rooms.push(c);
  }
  if(used.size!==l.boxes.length)return null;
  const gu=new Set<number>();
  for(const r of rooms)r.goals.forEach(g=>gu.add(g));
  if(gu.size!==l.goals.length)return null;
  rooms.sort((a,b)=>a.door-b.door);
  return rooms;
}
function solve(t:string):string{
  const l=parse(t),rooms=decompose(l);
  if(!rooms)return whole(l);
  let moves='',player=l.player,boxes=l.boxes.slice();
  for(const r of rooms){
    const w1=path(l,boxes,player,r.door);
    if(w1===null)return whole(l);
    moves+=w1;player=r.door;
    const sub:L={w:l.w,h:l.h,wall:l.wall.map((_,i)=>!r.cells.has(i)&&i!==r.door),goals:r.goals,boxes:r.boxes.slice(),player:r.door};
    const res=astar(sub,r.door,120000);
    if(!res)return whole(l);
    const em=expand(sub,res,r.door,r.boxes);
    if(em===null)return whole(l);
    moves+=em[0];
    const we=path(sub,em[2],em[1],r.door);
    if(we===null)return whole(l);
    moves+=we;player=r.door;
    boxes=boxes.filter(b=>!r.boxes.includes(b)).concat(r.goals.slice());
    boxes.sort((a,b)=>a-b);
  }
  return moves;
}
for(const id of readdirSync(I).sort()){
  let moves='';
  try{moves=solve(readFileSync(join(I,id,'level.txt'),'utf8'));}catch{moves='';}
  mkdirSync(join(O,id),{recursive:true});
  writeFileSync(join(O,id,'solution.txt'),`${moves}\n`);
}
