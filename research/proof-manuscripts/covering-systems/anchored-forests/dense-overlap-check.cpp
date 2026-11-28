// Outward interval bounds for Buchstab's omega and Weingartner's d on closed cells.
// The omega bounds are for the part of its domain at or above 1.
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>

using Integer = std::int64_t;
constexpr int mesh = 500;
constexpr int end = 30 * mesh;
constexpr Integer unit = 100000000;
Integer ceiling(Integer a, Integer b) { return (a + b - 1) / b; }

int main() {
    std::vector<Integer> wl(end + 3), wu(end + 3), sl(end + 4), su(end + 4);
    for (int i = mesh; i <= end + 2; ++i) {
        // z*omega(z) = 1 + integral from 1 to max(1,z-1) of omega.
        wl[i] = (unit * mesh + sl[std::max(mesh, i - mesh)]) / (i + 1);
        wu[i] = ceiling(unit * mesh + su[std::max(mesh, i + 1 - mesh)], i);
        sl[i+1] = sl[i] + wl[i];
        su[i+1] = su[i] + wu[i];
    }
    std::vector<Integer> lower(end), upper(end);
    Integer sumlo = 0, sumhi = 0;
    for (int i = 0; i < end; ++i) {
        Integer integral_lo = 0, integral_hi = 0;
        for (int j = 0; 2*j < i + 1 - mesh; ++j) {
            int first = std::max(mesh, (i-j-1)*mesh/(mesh+j+1));
            int last = (i+1-j)*mesh/(mesh+j);
            Integer small = unit, large = 0;
            for (int b = first; b <= last; ++b) {
                small = std::min(small, wl[b]);
                large = std::max(large, wu[b]);
            }
            integral_hi += ceiling(upper[j] * large, unit * (mesh+j));
            if (2*(j+1) <= i-mesh)
                integral_lo += lower[j] * small / (unit * (mesh+j+1));
        }
        lower[i] = std::max<Integer>(0, unit-integral_hi);
        upper[i] = unit-integral_lo;
        assert(0 <= lower[i] && lower[i] <= upper[i] && upper[i] <= unit);
        sumlo += lower[i];
        sumhi += upper[i];
        if (i+1 == 10*mesh) assert(1000*sumhi < 476*unit*(i+1));
        if ((i+1) % mesh == 0 && i+1 >= 6*mesh) {
            std::cout << (i+1)/mesh << " " << double(sumlo)/(unit*(i+1))
                      << " " << double(sumhi)/(unit*(i+1)) << "\n";
        }
    }
}
