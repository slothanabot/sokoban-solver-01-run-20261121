import{mkdirSync,readdirSync,readFileSync,writeFileSync}from"node:fs";
const I=process.env.MAKEFUN_INPUT_DIR??"/input",O=process.env.MAKEFUN_OUTPUT_DIR??"/output",X=[0,0,-1,1],Y=[-1,1,0,0],C="udlr";
function D(w,wall,g){let d=new Int32Array(wall.length).fill(-1),q=[g];d[g]=0;for(let i=0;i<q.length;i++){let x=q[i];for(let k=0;k<4;k++){let e=Y[k]*w+X[k],y=x-e;if(!wall[y]&&!wall[y-e]&&d[y]<0){d[y]=d[x]+1;q.push(y)}}}return d}
function R(w,wall,o,f,s,t){let a=[f];s[f]=t;let l=f,n=1;for(;n;){let p=a[--n];if(p<l)l=p;for(let k=0;k<4;k++){let q=p+Y[k]*w+X[k];if(!wall[q]&&!o[q]&&s[q]!=t){s[q]=t;a[n++]=q}}}return l}
function F(w,wall,o,G,t){for(let a of[t,t-1,t-w,t-w-1]){let c=a+w;if((wall[a]||o[a])&&(wall[a+1]||o[a+1])&&(wall[c]||o[c])&&(wall[c+1]||o[c+1])&&((o[a]&&!G[a])||(o[a+1]&&!G[a+1])||(o[c]&&!G[c])||(o[c+1]&&!G[c+1])))return 1}return 0}
function S(w,wall,gs,bs,pl){
let n=bs.length,N=wall.length,G=new Uint8Array(N),ds=gs.map(g=>D(w,wall,g)),live=new Uint8Array(N),seen=new Int32Array(N),mark=new Int32Array(N),st=0,ms=0;
for(let g of gs)G[g]=1;
for(let s=0;s<N;s++)for(let j=0;j<n;j++)if(ds[j][s]>=0)live[s]=1;
if(bs.some(x=>!live[x]))return null;
let H=a=>{let b=1/0,u=new Array(n).fill(0),r=(i,s)=>{if(s>=b)return;if(i==n){b=s;return}for(let j=0;j<n;j++){if(u[j])continue;let d=ds[j][a[i]];if(d<0)continue;u[j]=1;r(i+1,s+d);u[j]=0}};r(0,0);return b};
let V=a=>a.every(x=>G[x]);
let K=(a,l)=>{let k=l;for(let x of a)k=k*N+x;return k};
let nodes,ab,mn,path=[],T=new Map();
let dfs=(a,p,g,bd)=>{
if(ab)return 0;
if(++nodes>2e5){ab=1;return 0}
let h=H(a);if(h==1/0)return 0;
let f=g+h;if(f>bd){if(f<mn)mn=f;return 0}
if(V(a))return 1;
let o=new Uint8Array(N);
for(let x of a)o[x]=1;
let hr=++st,lw=R(w,wall,o,p,seen,hr),k=K(a,lw),pv=T.get(k);
if(pv!==void 0&&pv<=g)return 0;
T.set(k,g);
for(let i=0;i<n;i++){let b=a[i];
for(let d=0;d<4;d++){let e=Y[d]*w+X[d],t=b+e,s=b-e;
if(wall[t]||o[t]||!live[t]||seen[s]!=hr)continue;
o[b]=0;o[t]=1;let fz=F(w,wall,o,G,t),nx=null;
if(!fz){nx=a.slice();nx[i]=t;nx.sort((x,y)=>x-y)}
o[t]=0;o[b]=1;
if(fz||!nx)continue;
path.push([b,d]);
if(dfs(nx,b,g+1,bd))return 1;
path.pop();
hr=++st;R(w,wall,o,p,seen,hr)}}
return 0};
let bd=H(bs);
if(bd!=1/0)for(;;){nodes=0;ab=0;mn=1/0;T.clear();path.length=0;if(dfs(bs,pl,0,bd))return path.slice();if(ab||mn==1/0)break;bd=mn}
if(!ab)return null;
let Q=[bs],QP=[pl],PP=[-1],PQ=[0],ix=new Map,o=new Uint8Array(N);
for(let x of bs)o[x]=1;
ix.set(K(bs,R(w,wall,o,pl,seen,++st)),0);
for(let x of bs)o[x]=0;
let fd=V(bs)?0:-1;
for(let h=0;fd<0&&h<Q.length;h++){let a=Q[h];
for(let x of a)o[x]=1;
R(w,wall,o,QP[h],seen,++st);let hr=st;
for(let i=0;i<n&&fd<0;i++){let b=a[i];
for(let d=0;d<4;d++){let e=Y[d]*w+X[d],t=b+e,s=b-e;
if(seen[s]!=hr||wall[t]||o[t]||!live[t])continue;
o[b]=0;o[t]=1;let fz=F(w,wall,o,G,t),k=-1,nx=null;
if(!fz){nx=a.slice();nx[i]=t;nx.sort((x,y)=>x-y);k=K(nx,R(w,wall,o,b,mark,++ms))}
o[t]=0;o[b]=1;
if(fz||!nx||ix.has(k))continue;
if(Q.length>=25e4){for(let x of a)o[x]=0;return null}
ix.set(k,Q.length);Q.push(nx);QP.push(b);PP.push(h);PQ.push(d);
if(V(nx)){fd=Q.length-1;break}}}
for(let x of a)o[x]=0}
if(fd<0)return null;
let out=[];
for(let s=fd;s>0;s=PP[s])out.push([QP[s],PQ[s]]);
out.reverse();
return out}
function W(w,wall,o,f,t){if(f==t)return"";let pv=new Int32Array(wall.length).fill(-1),hw=new Array(wall.length),q=[f];pv[f]=f;for(let i=0;i<q.length;i++){let p=q[i];if(p==t)break;for(let k=0;k<4;k++){let x=p+Y[k]*w+X[k];if(wall[x]||o[x]||pv[x]!=-1)continue;pv[x]=p;hw[x]=C[k];q.push(x)}}let s="";for(let p=t;p!=f;p=pv[p])s=hw[p]+s;return s}
function solve(t){
let r=t.split("\n").filter(x=>x.length),h=r.length,w=Math.max(...r.map(x=>x.length)),N=w*h,wall=new Uint8Array(N).fill(1),gs=[],bs=[],pl=-1;
r.forEach((row,y)=>{for(let x=0;x<row.length;x++){let ch=row[x];if(ch=="#")continue;let i=y*w+x;wall[i]=0;if(".*+".includes(ch))gs.push(i);if("$*".includes(ch))bs.push(i);if("@+".includes(ch))pl=i}});
for(let y=0;y<h;y++)for(let x=0;x<w;x++)if(!x||!y||x==w-1||y==h-1)wall[y*w+x]=1;
bs.sort((a,b)=>a-b);
let ds=gs.map(g=>D(w,wall,g)),live=new Uint8Array(N);
for(let s=0;s<N;s++)for(let j=0;j<gs.length;j++)if(ds[j][s]>=0)live[s]=1;
let pr=Math.floor(pl/w),cut=new Uint8Array(N);
for(let x=0;x<w;x++){let i=pr*w+x;if(!wall[i]&&!live[i])cut[i]=1}
let cp=new Int32Array(N).fill(-1),rm=[];
for(let s=0;s<N;s++){if(wall[s]||cut[s]||cp[s]>=0)continue;let sq=[s];cp[s]=rm.length;for(let i=0;i<sq.length;i++)for(let k=0;k<4;k++){let q=sq[i]+Y[k]*w+X[k];if(!wall[q]&&!cut[q]&&cp[q]<0){cp[q]=rm.length;sq.push(q)}}rm.push({b:[],g:[]})}
for(let x of bs){if(cp[x]<0)return"";rm[cp[x]].b.push(x)}
for(let g of gs){if(cp[g]<0)return"";rm[cp[g]].g.push(g)}
let rs=rm.filter(q=>q.b.length);
if(rs.some(q=>q.b.length!=q.g.length)||!rs.length)return"";
let m="",cur=bs.slice(),o=new Uint8Array(N);
for(let q of rs){
let sub=wall.slice();
for(let x of cur)if(!q.b.includes(x))sub[x]=1;
let rb=cur.filter(x=>q.b.includes(x)).sort((a,b)=>a-b);
let ps=S(w,sub,q.g.slice().sort((a,b)=>a-b),rb,pl);
if(!ps)return"";
for(let x of cur)o[x]=1;
for(let p of ps){let e=Y[p[1]]*w+X[p[1]];m+=W(w,wall,o,pl,p[0]-e);m+=C[p[1]];o[p[0]]=0;o[p[0]+e]=1;pl=p[0];cur=cur.map(x=>x==p[0]?p[0]+e:x).sort((a,b)=>a-b)}
for(let x of cur)o[x]=0}
return m}
for(let id of readdirSync(I).sort()){let mv=solve(readFileSync(I+"/"+id+"/level.txt","utf8"));mkdirSync(O+"/"+id,{recursive:!0});writeFileSync(O+"/"+id+"/solution.txt",mv+"\n")}
