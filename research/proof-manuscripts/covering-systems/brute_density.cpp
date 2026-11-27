// Exhaust all possible actual residues and modulus subsets. Period limited to 64 sites.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <vector>
using Mask = std::uint64_t;

struct Exhaust {
    std::vector<std::vector<Mask>> masks;
    std::vector<int> best;
    void visit(int i, int subset, Mask covered) {
        if(i == static_cast<int>(masks.size())) {
            best[subset] = std::max(best[subset], __builtin_popcountll(covered));
            return;
        }
        visit(i+1, subset, covered);
        for(Mask m: masks[i]) visit(i+1, subset | (1<<i), covered | m);
    }
};

int main(int argc, char** argv) {
    if (argc<3) return 2;
    const int period = std::stoi(argv[1]);
    if(period<1 || period>64) return 2;
    Exhaust s;
    for(int j=2;j<argc;j++) {
        int n=std::stoi(argv[j]);
        if(n<=0 || period%n) return 2;
        std::vector<Mask> list(n);
        for(int x=0;x<period;x++) list[x%n] |= Mask(1)<<x;
        s.masks.push_back(list);
    }
    s.best.resize(1<<s.masks.size());
    s.visit(0,0,0);
    for(int v: s.best) std::cout<<v<<'\n';
}
