// Enumerate integers by increasing distinct prime factors and test all axis subsets.
// Compile with g++ -O2 -std=c++17 independent_census.cpp -o census
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <limits>
#include <vector>
using Int = __int128_t;
constexpr int limit = 1000000;
struct Axis { int p, power, exponent; };
std::vector<int> primes;
std::vector<Axis> factors;
std::array<int,5> counts{};
void classify() {
    int first=0,t=1;
    while(first < static_cast<int>(factors.size()) && factors[first].p==t+1) {
        t *= (1+factors[first].exponent);
        ++first;
    }
    if(first==static_cast<int>(factors.size())) { ++counts[1]; return; }
    if(factors[first].p<=t) { ++counts[0]; return; }
    const int size = 1 << (factors.size()-first);
    std::vector<Int> D(size,1), geom(size,1);
    bool positive=true;
    for(int m=1;m<size;++m) {
        const int bit=__builtin_ctz(m);
        const auto& a=factors[first+bit];
        const int rem=m&(m-1), v=(a.power-1)/(a.p-1);
        geom[m]=v*geom[rem];
        Int sum=0;
        for(int sub=rem;;sub=(sub-1)&rem) {
            sum += geom[sub]*D[rem^sub];
            if(!sub) break;
        }
        D[m]=a.power*D[rem]-t*v*sum;
        if(m!=size-1 && D[m]<=0) positive=false;
    }
    ++counts[D.back()<=0 ? 2 : positive ? 3 : 4];
}
void generate(int n, size_t next) {
    classify();
    for(size_t i=next;i<primes.size() && primes[i]<=limit/n;++i) {
        int p=primes[i],power=p,e=1;
        while(power<=limit/n) {
            factors.push_back({p,power,e});
            generate(n*power,i+1);
            factors.pop_back();
            if(power>(limit/n)/p) break;
            power*=p; ++e;
        }
    }
}
int main() {
    std::vector<bool> composite(limit+1);
    for(int i=2;i<=limit;++i) if(!composite[i]) {
        primes.push_back(i);
        if(i<=limit/i) for(int j=i*i;j<=limit;j+=i) composite[j]=true;
    }
    generate(1,0);
    assert((counts==std::array<int,5>{103205,92,158,896545,0}));
    for(int x:counts)std::cout << x << ' ';
    std::cout<<"\n";
}
