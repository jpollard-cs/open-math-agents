#include <algorithm>
#include <array>
#include <cstdint>
#include <map>
#include <set>
#include <vector>

// A column fixes the mod-5 coordinate, and stores three bytes indexed
// by the mod-3 coordinate. A byte records the binary coordinate mod 8.
using Columns = std::array<unsigned,5>;
using Table = std::array<unsigned,256>;
static std::vector<Table> tree_permutations() {
    std::vector<Table> tables;
    for(unsigned switches=0; switches<128; ++switches) {
        Table table{};
        for(unsigned i=0;i<8;++i) {
            unsigned b0 = (i&1) ^ (switches&1);
            unsigned b1 = ((i>>1)&1) ^ ((switches>>(1+(i&1)))&1);
            unsigned b2 = (i>>2) ^ ((switches>>(3+(i&3)))&1);
            unsigned j=b0+2*b1+4*b2;
            for(unsigned mask=0;mask<256;++mask)
                if(mask & (1u<<i)) table[mask] |= 1u<<j;
        }
        tables.push_back(table);
    }
    return tables;
}

extern "C" int orbit120(int n,const std::uint64_t* words,int* indices) {
    std::map<Columns,int> columns;
    for(int i=0;i<n;++i) {
        Columns c{};
        for(int x=0;x<120;++x)
            if((words[2*i+x/64]>>(x%64))&1)
                c[x%5] |= 1u<<(8*(x%3)+x%8);
        std::sort(c.begin(),c.end());
        columns.emplace(c,i);
    }
    auto tables=tree_permutations();
    std::set<Columns> done;
    int count=0;
    for(const auto& [c,index]:columns) {
        if(done.contains(c)) continue;
        indices[count++]=index;
        for(const auto& table:tables) {
            std::array<std::array<unsigned,3>,5> pieces;
            for(int i=0;i<5;++i)
                for(int j=0;j<3;++j) pieces[i][j]=table[(c[i]>>(8*j))&255];
            std::array<int,3> p{0,1,2};
            do {
                Columns out;
                for(int i=0;i<5;++i)
                    out[i]=pieces[i][p[0]] | (pieces[i][p[1]]<<8) | (pieces[i][p[2]]<<16);
                std::sort(out.begin(),out.end());
                done.insert(out);
            } while(std::next_permutation(p.begin(),p.end()));
        }
    }
    return count;
}
