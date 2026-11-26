#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std; using U=unsigned int;using LL=unsigned long long;
const U FULL=(1u<<25)-1,WANT=3195660;int numNot,keepMax;double secs;int late=0; bool stopflag=false;string directory;chrono::steady_clock::time_point start;
struct Node{int op,p,q;U v;};static Node path[10];static U input[10];LL visited,offered,valid;
struct Key{array<U,14> a{};bool operator==(const Key&o)const{return a==o.a;}};struct H{size_t operator()(const Key&k)const{LL h=0;for(auto x:k.a)h=(h^x)*1099511628211ull;return h;}};
unordered_set<Key,H> memo;int stamp=0,seen[1<<14];
U val(int op,U x,U y){return op==0?x|y:op==1?x&y:FULL^x;}
void output(int l,int goal){
 bool live[21]{};live[goal]=true;for(int i=l-1;i>=0;--i)if(live[10+i]){live[path[i].p]=true;if(path[i].op<2)live[path[i].q]=true;}
 int ids[21],next=10;for(int i=0;i<10;++i)ids[i]=i;U all[21];copy(input,input+10,all);
 FILE*f=fopen((directory+"/candidate.json").c_str(),"w");fprintf(f,"{\"n\":5,\"gates\":[");
 for(int i=0;i<l;++i){auto g=path[i];all[10+i]=val(g.op,all[g.p],all[g.q]);if(live[10+i]){ids[10+i]=next++;fprintf(f,"%s[\"%s\",%d",ids[10+i]>10?",":"",g.op==0?"or":g.op==1?"and":"not",ids[g.p]);if(g.op!=2)fprintf(f,",%d",ids[g.q]);fprintf(f,"]");}}
 assert(all[goal]==WANT);fprintf(f,"],\"output\":%d}\n",ids[goal]);fclose(f);
}
bool go(int depth,vector<int> live,vector<int> cases,int keep,int neg){
 if(stopflag)return false;int sz=live.size();if(sz==1&&cases.size()==2){/* One live bit may be complemented: check concrete function below. */}
 U values[21];copy(input,input+10,values);for(int i=0;i<depth;++i)values[10+i]=path[i].v;
 for(int w:live)if(values[w]==WANT){output(depth,w);return true;}if(depth==10||sz-1>10-depth-neg)return false;
 Key key;key.a[0]=1u+keep+8u*neg;int j=1;for(int w:live)key.a[j++]=values[w]+1;sort(key.a.begin()+1,key.a.begin()+j);
 if(!memo.insert(key).second)return false;
 if(((++visited)&8191)==0&&(chrono::duration<double>(chrono::steady_clock::now()-start).count()>secs||memo.size()>1800000)){stopflag=true;return false;}
 auto search=[&](int a,int b,int op,int r){int binary=op!=2,c=__builtin_popcount((unsigned)r);if(c>keep)return false;
  int p=live[a],q=live[b];U v=val(op,values[p],values[q]);if(v==0||v==FULL)return false;for(int w:live)if(values[w]==v)return false;
  if(depth==9&&v!=WANT)return false;int top=sz-(1+binary)+c;int must0=!(r&1),must1=binary&&!(r&2);int mask=0;for(int z=0;z<sz;++z)if((z!=a||!must0)&&(z!=b||!must1))mask|=1<<z;
  int compress[1<<14];(void)compress; // only up to two coordinate deletions.
  auto drop=[](int x,int i){return (x&((1<<i)-1))|((x>>(i+1))<<i);};
  ++offered;++stamp;vector<int> cc;cc.reserve(cases.size());for(int row:cases){int old=row>>1,yt=row&1,x=(old>>a)&1,y=(old>>b)&1,u=old;
   if(must1)u=drop(u,b);if(must0)u=drop(u,a);
   int z=op==0?x|y:op==1?x&y:x^1;u|=z<<top;
   if(seen[u]==stamp){if((seen[(1<<13)+u]&1)!=yt)return false;}else{seen[u]=stamp;seen[(1<<13)+u]=yt;cc.push_back(2*u+yt);}}
  ++valid;vector<int> lv;for(int z=0;z<sz;++z)if((mask>>z)&1)lv.push_back(live[z]);lv.push_back(10+depth);
  path[depth]={op,p,q,v};return go(depth+1,lv,cc,keep-c,neg-(op==2));};
 if(neg)for(int a=0;a<sz;++a)for(int r=0;r<=min(1,keep);++r)if(search(a,a,2,r))return true;
 for(int a=0;a<sz;++a)for(int b=a+1;b<sz;++b)for(int op=0;op<2;++op)for(int r=0;r<4;++r)if(search(a,b,op,r))return true;
 return false;
}
int main(int argc,char**argv){if(argc!=5)return 1;numNot=atoi(argv[1]);keepMax=atoi(argv[2]);secs=atof(argv[3]);directory=argv[4];assert(numNot>=0&&keepMax+numNot<=3);for(int i=0;i<5;++i)for(int j=0;j<5;++j){U q=1u<<(5*i+j);input[i]|=q;input[5+j]|=q;}
 int total=0,done=0;start=chrono::steady_clock::now();
 for(int m=0;m<1024;++m){int n=__builtin_popcount((unsigned)m),a=__builtin_popcount((unsigned)m&31),b=n-a;if(a<4||b<4||10-n+1-numNot!=keepMax)continue;++total;}
 for(int m=0;m<1024&&!stopflag;++m){int n=__builtin_popcount((unsigned)m),a=__builtin_popcount((unsigned)m&31),b=n-a;if(a<4||b<4||10-n+1-numNot!=keepMax)continue;
  vector<int> lv,cs;for(int i=0;i<10;++i)if(m>>i&1)lv.push_back(i);for(int i=0;i<25;++i){int v=0;for(int j=0;j<n;++j)if((input[lv[j]]>>i)&1)v|=1<<j;cs.push_back(2*v+((WANT>>i)&1));}
  memo.clear();if(go(0,lv,cs,keepMax,numNot)){printf("SAT!!! not=%d keep=%d mask=%d\n",numNot,keepMax,m);return 0;}if(!stopflag)++done;
 }
 printf("not=%d extra=%d %s seedsets=%d/%d states=%llu candidates=%llu valid=%llu sec=%.2f\n",numNot,keepMax,stopflag?"LIMIT":"UNSAT",done,total,visited,offered,valid,chrono::duration<double>(chrono::steady_clock::now()-start).count());}
