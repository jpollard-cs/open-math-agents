#include <bit>
#include <array>
#include <cstdint>
#include <unordered_set>
#include <vector>
#include <algorithm>
using W=std::uint64_t;
struct M { W a,b; bool operator==(const M&)const=default; };
struct H {std::size_t operator()(const M&x)const{return x.a^(x.b+0x9e3779b97f4a7c15ULL+(x.a<<6)+(x.a>>2));}};
extern "C" W* combinations120(const W* a,int na,const W*b,int nb,int* count){
    std::unordered_set<M,H> masks;
    for(int i=0;i<na;i++){
        auto v=a+6*i;
        for(int j=0;j<nb;j++){
            auto z=b+6*j;
            M x{(v[0]|z[0])&(v[2]|z[2])&(v[4]|z[4]),(v[1]|z[1])&(v[3]|z[3])&(v[5]|z[5])};
            masks.insert(x);
        }
    }
    *count=(int)masks.size(); W* out=new W[2*masks.size()];int i=0;
    for(auto m:masks){out[i++]=m.a;out[i++]=m.b;}
    return out;
}
extern "C" void free120(W* vals){delete[] vals;}
struct Tri{W a,b,c;bool operator==(const Tri&)const=default;};
struct HT {std::size_t operator()(const Tri& m)const{return H{}({m.a^m.c,m.b^std::rotl(m.c,23)});}};
extern "C" W* combinations180(const W* a,int na,const W* b,int nb,int* count){
    std::unordered_set<Tri,HT> ms;
    for(int i=0;i<na;i++)for(int j=0;j<nb;j++){
        auto u=a+6*i;auto v=b+6*j;
        ms.insert({(u[0]|v[0])&(u[3]|v[3]),(u[1]|v[1])&(u[4]|v[4]),(u[2]|v[2])&(u[5]|v[5])});
    }
    W* out=new W[3*ms.size()];int i=0;*count=(int)ms.size();
    for(auto m:ms){out[i++]=m.a;out[i++]=m.b;out[i++]=m.c;}return out;
}
