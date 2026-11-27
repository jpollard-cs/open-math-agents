// Enumerate vertices of the gap polytopes in the proof, using integer arithmetic.
#include <algorithm>
#include <cassert>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <numeric>
#include <vector>

using Row = std::array<long long, 7>;
using Mask = std::uint64_t;
struct Enumerator {
    int n, d;
    std::vector<Row> rows;
    std::vector<std::array<int, 3>> triples;
    std::array<int, 6> choice{};
    std::map<Mask, Row> examples;
    explicit Enumerator(int n) : n(n), d(n - 1) {
        for (int i = 0; i < d; ++i) {
            Row row{}; row[i] = row[d] = 1; rows.push_back(row);
        }
        for (int i = 0; i < n; ++i) {
            for (int j = i + 1; j < n; ++j) {
                for (int k = j + 1; k < n; ++k) {
                    triples.push_back({i, j, k}); Row row{};
                    for (int t = i; t < j; ++t) row[t] = 1;
                    for (int t = j; t < k; ++t) row[t] = -1;
                    rows.push_back(row);
                }
            }
        }
    }
    void visit() {
        std::array<Row, 6> a{};
        for (int i = 0; i < d; ++i) a[i] = rows[choice[i]];
        long long previous = 1;
        for (int j = 0; j < d - 1; ++j) {
            int pivot = j;
            while (pivot < d && !a[pivot][j]) ++pivot;
            if (pivot == d) return;
            if (pivot != j) std::swap(a[j], a[pivot]);
            for (int i = j + 1; i < d; ++i)
                for (int k = j + 1; k <= d; ++k) {
                    const long long numerator = a[j][j]*a[i][k] - a[i][j]*a[j][k];
                    assert(numerator % previous == 0);
                    a[i][k] = numerator / previous;
                }
            previous = a[j][j];
        }
        long long denom = std::abs(a[d - 1][d - 1]);
        if (!denom) return;
        Row gaps{};
        for (int i = d - 1; i >= 0; --i) {
            long long value = a[i][d] * denom;
            for (int k = i + 1; k < d; ++k) value -= a[i][k] * gaps[k];
            assert(value % a[i][i] == 0);
            gaps[i] = value / a[i][i];
            if (gaps[i] < denom) return;
        }
        Row x{}; long long common = 0;
        for (int i = 0; i < d; ++i) common = std::gcd(common, gaps[i]);
        for (int i = 0; i < d; ++i) x[i+1] = x[i]+gaps[i]/common;
        Mask mask = 0;
        for (std::size_t t = 0; t < triples.size(); ++t) {
            auto [i, j, k] = triples[t];
            if (x[i] + x[k] == 2*x[j]) mask |= Mask{1} << t;
        }
        auto it = examples.find(mask);
        if (it == examples.end() || x < it->second) examples[mask] = x;
    }
    void select(int depth, int first) {
        if (depth == d) { visit(); return; }
        int last = int(rows.size()) - (d - depth);
        if (depth == 0) last = std::min(last, d - 1); // at least one unit gap
        for (int i = first; i <= last; ++i) {
            choice[depth] = i; select(depth + 1, i + 1);
        }
    }
    void print() {
        std::vector<Mask> all, maximal;
        for (auto const& [mask, x] : examples) all.push_back(mask);
        std::sort(all.begin(), all.end(), [](Mask a, Mask b) {
            return __builtin_popcountll(a) > __builtin_popcountll(b);
        });
        for (auto mask : all) {
            if (std::any_of(maximal.begin(), maximal.end(),
                [=](Mask m) { return (m & mask) == mask; })) continue;
            maximal.push_back(mask);
            std::cout << n << ' ' << mask;
            for (int i = 0; i < n; ++i) std::cout << ' ' << examples[mask][i];
            std::cout << '\n';
        }
    }
};
int main(int argc, char** argv) {
    int largest = (argc == 2) ? std::atoi(argv[1]) : 7;
    if (largest < 3 || largest > 7) return 1;
    for (int n = 3; n <= largest; ++n) {
        Enumerator e(n); e.select(0, 0); e.print();
    }
}
