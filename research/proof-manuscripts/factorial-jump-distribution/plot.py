"""Draw the theoretical coefficient. The tail correction error is O(K^-2)."""
from math import gcd, log1p
import matplotlib.pyplot as plt
import numpy as np

K = 12000
e = np.arange(1, K + 1, dtype=float)

def harmonic_log(a):
    return np.sum(np.log1p(1 / (a * e)) / e) + 1 / (a * K)

kappa = harmonic_log(1)
fig, ax = plt.subplots(figsize=(7.4, 3.25), layout="constrained")
slopes = np.array([1.05, 3.05])
ax.plot(slopes, (1 + slopes) * kappa, color="#447489", lw=1.35,
        label="irrational slopes")
for b in range(18, 0, -1):
    for a in range(b + 1, int(3.05*b) + 1):
        x = a/b
        if x < slopes[0] or gcd(a,b) != 1:
            continue
        top = (1+x)*kappa
        bottom = top - 2*harmonic_log(a)/b
        ax.vlines(x, bottom, top, lw=.7, color="#a6b7bc", alpha=.7)
        ax.scatter(x,bottom,s=9 if b>4 else 22,color="#962e36",zorder=4)
        if (a,b) in [(2,1),(3,1),(3,2),(4,3)]:
            label = str(a) if b==1 else f"{a}/{b}"
            ax.annotate(label, (x,bottom), xytext=(5,-2), textcoords="offset points",
                        fontsize=8, color="#6e1f27")
ax.scatter([],[],s=14,color="#962e36",label="rational slopes shown")
ax.set_xlabel("Endpoint slope β")
ax.set_ylabel("Mean absolute log change\n(multiplied by log X)")
ax.spines[["top","right"]].set_visible(False)
ax.legend(loc="upper left",frameon=False,fontsize=8)
ax.set_xlim(1.03,3.13)
fig.savefig("slope-variation.pdf")
fig.savefig("slope-variation.png",dpi=155)
