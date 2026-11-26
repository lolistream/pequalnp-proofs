#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <unordered_set>
#include <vector>
using Word=uint16_t; using Obl=uint64_t; constexpr int N=8, ALL=32767;
struct Gate {int op,a,b;};
struct Key {std::array<Word,13> w{};bool operator==(const Key&o)const{return w==o.w;}};
struct Hash {size_t operator()(const Key&k)const{uint64_t h=1469598103934665603ull;for(auto x:k.w)h=(h^x)*1099511628211ull;return h;}};
int mask,k;Word val[24];Obl sep[ALL+1],wanted;Gate path[16],sol[16];int solvedN,solvedW;
std::unordered_set<Key,Hash> memo;uint64_t states,tried,passed;bool stopped;double cap;std::chrono::steady_clock::time_point started;
static int secondsUp(){return std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()>=cap;}
bool search(int depth,const std::vector<int>&live,int spare){
 if(stopped)return false;for(int w:live)if(val[w]==mask){std::copy(path,path+depth,sol);solvedN=depth;solvedW=w;return true;}
 if(depth==k)return false;int s=live.size();if(s-1>k-depth)std::abort();
 Key key;key.w[0]=spare+1;int ix=1;for(int w:live)key.w[ix++]=val[w]+1;std::sort(key.w.begin()+1,key.w.begin()+ix);
 if(!memo.insert(key).second)return false;
 if((++states&8191)==0&&(secondsUp()||memo.size()>1500000)){stopped=true;return false;}
 for(int a=0;a<s;++a)for(int b=a+1;b<s;++b){int x=live[a],y=live[b];Obl others=0;for(int j=0;j<s;++j)if(j!=a&&j!=b)others|=sep[val[live[j]]];
  for(int op=0;op<2;++op){Word z=op?(val[x]&val[y]):(val[x]|val[y]);if(z==0||z==ALL||(depth==k-1&&z!=mask))continue;
   bool same=false;for(int w:live)if(val[w]==z){same=true;break;}if(same)continue;
   Obl base=others|sep[z];for(int retain=0;retain<4;++retain){int use=__builtin_popcount((unsigned)retain);if(use>spare)continue;++tried;
    Obl kept=base|(retain&1?sep[val[x]]:0)|(retain&2?sep[val[y]]:0);if(kept!=wanted)continue;++passed;
    std::vector<int> next;next.reserve(s+1);for(int j=0;j<s;++j)if((j!=a||(retain&1))&&(j!=b||(retain&2)))next.push_back(live[j]);next.push_back(N+depth);
    val[N+depth]=z;path[depth]={op,x,y};if(search(depth+1,next,spare-use))return true;if(stopped)return false;
   }
  }
 }return false;
}
void witness(){bool use[24]{};use[solvedW]=true;for(int j=solvedN-1;j>=0;--j)if(use[N+j])use[sol[j].a]=use[sol[j].b]=true;
 int ids[24],count=0;Word words[24];std::copy(val,val+N,words);for(int i=0;i<N;++i)ids[i]=i;
 printf(",\"witness\":{\"inputs\":8,\"gates\":[");for(int j=0;j<solvedN;++j){auto g=sol[j];words[N+j]=g.op?(words[g.a]&words[g.b]):(words[g.a]|words[g.b]);if(!use[N+j])continue;
  ids[N+j]=N+count++;printf("%s[\"%s\",%d,%d]",count==1?"":",",g.op?"and":"or",ids[g.a],ids[g.b]);}
 if(words[solvedW]!=mask||count>k)std::abort();printf("],\"output\":%d}",ids[solvedW]);}
int main(int argc,char**argv){if(argc!=4)return 2;mask=atoi(argv[1]);k=atoi(argv[2]);cap=atof(argv[3]);if(mask<=0||mask>=ALL||k<0||k>10||cap<=0)return 3;
 for(int a=0;a<3;++a)for(int b=0;b<5;++b){auto bit=1u<<(5*a+b);val[a]|=bit;val[3+b]|=bit;}
 std::vector<std::pair<int,int>> obligations;for(int p=0;p<15;++p)if(mask>>p&1)for(int q=0;q<15;++q)if(!(mask>>q&1))obligations.push_back({p,q});wanted=(1ull<<obligations.size())-1;
 for(int z=0;z<=ALL;++z){Obl s=0;for(int i=0;i<(int)obligations.size();++i){auto [p,q]=obligations[i];if((z>>p&1)&&!(z>>q&1))s|=1ull<<i;}sep[z]=s;}
 std::vector<int> enabled;int support=N+1;for(int raw=1;raw<(1<<N);++raw){Obl s=0;for(int i=0;i<N;++i)if(raw>>i&1)s|=sep[val[i]];if(s==wanted){int n=__builtin_popcount((unsigned)raw);support=std::min(support,n);if(n<=k+1)enabled.push_back(raw);}}
 std::stable_sort(enabled.begin(),enabled.end(),[](int a,int b){return __builtin_popcount((unsigned)a)>__builtin_popcount((unsigned)b);});
 printf("{\"mask\":%d,\"budget\":%d,\"support\":%d,\"feasible_supports\":%zu,\"profiles\":[",mask,k,support,enabled.size());int done=0;bool sat=false;started=std::chrono::steady_clock::now();
 for(int raw:enabled){if(secondsUp()){stopped=true;break;}memo.clear();states=tried=passed=0;std::vector<int> lv;for(int i=0;i<N;++i)if(raw>>i&1)lv.push_back(i);
  sat=search(0,lv,k+1-lv.size());printf("%s[%d,%llu,%llu,%llu,\"%s\"]",done?",":"",raw,(unsigned long long)states,(unsigned long long)tried,(unsigned long long)passed,sat?"sat":stopped?"limit":"unsat");++done;if(sat||stopped)break;}
 printf("],\"status\":\"%s\"",sat?"sat":stopped?"limit":"unsat");if(sat)witness();printf("}\n");return stopped?5:0;
}
