// Four translates, exactly three holes, period groups of order at most 127.
// Compile with g++ -std=c++20 -O3 census.cpp -o census and run ./census.
#include <algorithm>
#include <array>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <set>
#include <utility>
#include <vector>
using Mask = __uint128_t;
using Cell = std::pair<int, int>;
Mask bit(int i) { return Mask(1) << i; }
int mod(int x, int n) { return (x % n + n) % n; }

bool tiles(const std::vector<Cell>& cells) {
    const int size = cells.size();
    for (int width = 1; width <= size; ++width) {
        if (size % width) continue;
        const int height = size / width;
        for (int shear = 0; shear < width; ++shear) {
            Mask seen = 0;
            bool collision = false;
            for (auto [x, y] : cells) {
                int row = mod(y, height);
                int col = mod(x - (y-row)/height * shear, width);
                Mask label = bit(row * width + col);
                if (seen & label) { collision = true; break; }
                seen |= label;
            }
            if (!collision) return true;
        }
    }
    return false;
}

struct Census {
    int a, b, order, size;
    Mask full;
    std::vector<std::vector<int>> add, sub, automorphisms, containing;
    std::vector<Mask> translates;
    std::set<Mask> center_orbit, cell_types;
    long long motifs = 0, leaves = 0, winding = 0, flat = 0, nodes = 0;

    int scale(int k, int x) const {
        return mod(k*(x/b),a)*b + mod(k*(x%b),b);
    }

    Census(int first, int second) : a(first), b(second), order(a*b),
        size((order-3)/4), full(bit(order)-1),
        add(order, std::vector<int>(order)), sub(add) {
        for (int i=0; i<order; ++i) for (int j=0; j<order; ++j) {
            add[i][j] = mod(i/b+j/b,a)*b + mod(i%b+j%b,b);
            sub[i][j] = mod(i/b-j/b,a)*b + mod(i%b-j%b,b);
        }
        for (int x=0; x<order; ++x) {
            if (scale(a,x)) continue;
            for (int y=0; y<order; ++y) {
                std::vector<int> f(order);
                Mask image = 0;
                for (int j=0; j<order; ++j) {
                    f[j] = add[scale(j/b,x)][scale(j%b,y)];
                    image |= bit(f[j]);
                }
                if (image == full) automorphisms.push_back(f);
            }
        }
    }

    Mask normalize(const std::vector<int>& points, bool cache_centers) {
        Mask best = ~Mask(0);
        for (int t : points) for (const auto& f : automorphisms) {
            Mask translated = 0;
            for (int x : points) translated |= bit(f[sub[x][t]]);
            if (cache_centers) center_orbit.insert(translated);
            best = std::min(best,translated);
        }
        return best;
    }

    void check_lifts(Mask cells) {
        std::vector<int> points, index(order,-1);
        for (int x=0; x<order; ++x) if (cells & bit(x)) {
            index[x] = points.size();
            points.push_back(x);
        }
        for (int g=1; g<order; ++g) for (int h=g; h<order; ++h) {
            if (g>sub[0][g] || h>sub[0][h]) continue;
            // The two grid steps must generate the group modulo each prime.
            if (std::gcd(std::gcd(g%b,h%b),b)!=1 ||
                std::gcd(std::gcd(g/b,h/b),a)!=1 ||
                std::gcd((g/b)*(h%b)-(h/b)*(g%b),a)!=1) continue;
            std::vector<int> queue{0};
            std::vector<Cell> lift(size);
            Mask seen=1;
            bool inconsistent=false;
            for (size_t pos=0; pos<queue.size(); ++pos) {
                int i=queue[pos];
                for (int axis=0; axis<2; ++axis) for (int sign : {-1,1}) {
                    int step=axis?h:g;
                    int j=index[(sign>0?add:sub)[points[i]][step]];
                    if (j<0) continue;
                    Cell want={lift[i].first+sign*(1-axis),lift[i].second+sign*axis};
                    if (seen & bit(j)) {
                        if (lift[j]!=want) inconsistent=true;
                    } else {
                        lift[j]=want;
                        seen |= bit(j);
                        queue.push_back(j);
                    }
                }
            }
            if (int(queue.size())!=size) continue;
            if (inconsistent) ++winding;
            else ++flat;
            // In the inconsistent case the cylinder theorem handles all lifts.
            // Independently test this particular spanning-tree lift as well.
            if (!tiles(lift)) {
                std::cerr<<"Failed tiling test for group "<<a<<" x "<<b
                         <<", steps "<<g<<","<<h<<" and cells ";
                for (auto [x,y]:lift) std::cerr<<"("<<x<<","<<y<<") ";
                std::cerr<<"\n";
                std::exit(1);
            }
        }
    }

    void solve(Mask occupied, Mask starts, int holes) {
        ++nodes;
        if (occupied==full) {
            if (holes!=3) return;
            ++leaves;
            std::vector<int> points;
            for (int i=0;i<order;++i) if (starts & bit(i)) points.push_back(i);
            Mask cells=normalize(points,false);
            if (cell_types.insert(cells).second) check_lifts(cells);
            return;
        }
        int chosen=-1, least=5;
        for (int x=0;x<order;++x) if (!(occupied & bit(x))) {
            int options=0;
            for (int j:containing[x]) if (!(occupied & translates[j])) ++options;
            if (options<least) { least=options; chosen=x; }
            if (least==0) break;
        }
        if (holes<3) solve(occupied|bit(chosen),starts,holes+1);
        for (int j:containing[chosen]) if (!(occupied & translates[j]))
            solve(occupied|translates[j],starts|bit(j),holes);
    }

    void run() {
        for (int e=1;e<order;++e) for (int i=e+1;i<order;++i)
            for (int j=i+1;j<order;++j) {
                if (center_orbit.count(1|bit(e)|bit(i)|bit(j))) continue;
                std::vector<int> centers={0,e,i,j};
                normalize(centers,true);
                ++motifs;
                translates.assign(order,0);
                containing.assign(order,{});
                for (int z=0;z<order;++z) for (int d:centers) {
                    int v=add[z][d];
                    translates[z]|=bit(v);
                    containing[v].push_back(z);
                }
                solve(1,0,1); // translate the cell set to put a hole at zero
            }
        std::cout<<"group="<<a<<"x"<<b<<" size="<<size<<" motifs="<<motifs
                 <<" leaves="<<leaves<<" cellorbits="<<cell_types.size()
                 <<" winding="<<winding<<" flat="<<flat<<" nodes="<<nodes<<std::endl;
    }
};

int main(int argc,char** argv) {
    int end=argc>1?std::atoi(argv[1]):127;
    if (end<7 || end>127) return 2;
    for (int n=7;n<=end;n+=4) for (int a=1;a*a<=n;++a)
        if (n%(a*a)==0) Census(a,n/a).run();
}
