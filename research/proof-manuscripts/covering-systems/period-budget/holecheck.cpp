#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <unordered_map>
#include <vector>

struct Mask {
    std::array<std::uint64_t,3> w{};
    bool operator==(const Mask&) const=default;
    bool empty() const {return !(w[0]|w[1]|w[2]);}
    int count() const {return std::popcount(w[0])+std::popcount(w[1])+std::popcount(w[2]);}
    int overlap(const Mask& b) const {return std::popcount(w[0]&b.w[0])+std::popcount(w[1]&b.w[1])+std::popcount(w[2]&b.w[2]);}
    Mask remove(const Mask& b) const {return {{w[0]&~b.w[0],w[1]&~b.w[1],w[2]&~b.w[2]}};}
};
struct Key {unsigned left; Mask holes;bool operator==(const Key&) const=default;};
struct Hash {
    std::size_t operator()(const Key& k) const {std::size_t v=k.left;for(auto x:k.holes.w){v^=x+0x9e3779b97f4a7c15ULL+(v<<6)+(v>>2);}return v;}
};
struct Search {
    std::vector<std::vector<Mask>> rows;
    std::unordered_map<Key,bool,Hash> cache;
    bool fill(unsigned left,const Mask& holes){
        if(holes.empty())return true;
        if(!left)return false;
        Key key{left,holes};
        auto found=cache.find(key);
        if(found!=cache.end())return found->second;
        std::array<int,32> best{};
        int sum=0,need=holes.count();
        for(unsigned bits=left;bits;bits&=bits-1){
            int i=std::countr_zero(bits);
            for(const auto& m:rows[i])best[i]=std::max(best[i],m.overlap(holes));
            sum+=best[i];
        }
        bool ok=false;
        if(sum>=need){
            int choice=-1,least=10000;
            for(unsigned bits=left;bits;bits&=bits-1){
                int i=std::countr_zero(bits),cnt=0,th=std::max(1,best[i]-(sum-need));
                for(const auto& m:rows[i])if(m.overlap(holes)>=th)++cnt;
                if(cnt<least){choice=i;least=cnt;}
            }
            int threshold=std::max(1,best[choice]-(sum-need));
            std::vector<std::pair<int,int>> trial;
            for(int j=0;j<(int)rows[choice].size();j++){
                int gain=holes.overlap(rows[choice][j]);
                if(gain>=threshold)trial.push_back({-gain,j});
            }
            std::sort(trial.begin(),trial.end());
            std::vector<Mask> tried;
            for(auto [gain,j]:trial){
                Mask h=holes.remove(rows[choice][j]);
                if(std::find(tried.begin(),tried.end(),h)!=tried.end())continue;
                tried.push_back(h);
                if(fill(left^(1u<<choice),h)){ok=true;break;}
            }
        }
        if(cache.size()>1200000)cache.clear();
        cache.emplace(key,ok);
        return ok;
    }
};
extern "C" int check_holes(int base,int n,const int* ds,int count,const std::uint64_t* data){
    Search solver;
    for(int i=0;i<n;i++){
        int d=ds[i];
        int period=d<0?120:d;
        std::vector<Mask> row(period);
        for(int r=0;r<period;r++)for(int j=0;j<base;j++){
            bool hit=d<0?(j%24==r%24||j%40==r%40):j%d==r;
            if(hit)row[r].w[j/64]|=1ULL<<(j%64);
        }
        solver.rows.push_back(std::move(row));
    }
    for(int j=0;j<count;j++){
        Mask h{{data[3*j],data[3*j+1],data[3*j+2]}};
        if(solver.fill((1u<<n)-1,h))return 1;
    }
    return 0;
}
