// Exact backward search for a counterexample to Conjecture 3.7 of arXiv:2008.01501.
// Discovery only. Any returned identity must be independently checked and formalized.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>
using std::uint16_t;
constexpr uint16_t INF=65535;
int main(int argc,char**argv){
 int N=argc>1?std::stoi(argv[1]):5000;
 if(N<2 || N>12000) throw std::invalid_argument("2 <= N <= 12000 required");
 std::vector<std::vector<uint16_t>> cost(N+1),step(N+1);
 for(int a=1;a<=N;++a){
  cost[a].assign(a+3,INF);step[a].assign(a+3,0);
  for(int r=a;r<=2*a+2;++r){
   auto &best=cost[a][r-a];auto &next=step[a][r-a];
   for(int d=1,pow2=2;d<a && pow2<=r; ++d,pow2*=2){
    if(r%pow2) break;
    int b=a-d, carry=r/pow2;
    if(carry==b && b+1<best){best=uint16_t(b+1);next=uint16_t(0x8000|d);}
    int nr=b+carry;
    if(nr<b || nr>2*b+2) throw std::logic_error("invariant violation");
    if(cost[b][nr-b]!=INF && 1+cost[b][nr-b]<best){
     best=uint16_t(1+cost[b][nr-b]);next=uint16_t(d);
    }
   }
  }
  if(cost[a][0]!=INF && a>2*int(cost[a][0])){
   int b=a,r=a,n=0;std::vector<int> terms{a};
   while(true){int s=step[b][r-b],d=s&0x7fff;if(d==0)throw std::logic_error("missing step");
    if(s&0x8000){n=b-d;break;}r=(b-d)+(r/(1<<d));b-=d;terms.push_back(b);
   }
   std::reverse(terms.begin(),terms.end());
   std::cout<<"{\"found\":true,\"n\":"<<n<<",\"k\":"<<terms.size()<<",\"max\":"<<a<<",\"terms\":[";
   for(std::size_t i=0;i<terms.size();++i)std::cout<<(i?",":"")<<terms[i];
   std::cout<<"],\"cost\":"<<cost[a][0]<<"}\n";return 0;
  }
  if(a%1000==0)std::cerr<<"checked_max_exponent="<<a<<"\n";
 }
 std::cout<<"{\"found\":false,\"max_exponent_checked\":"<<N<<",\"formal_verification\":false}\n";
}
