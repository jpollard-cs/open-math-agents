# Adjacent starting integers and several nearby limits

Fix an integer cofactor D≥1 and an integer r≥1. In the range of window lengths in the manuscript, there are starting integers n tending to infinity for which the ratios at n and n+1 tend respectively to (1+1/D)^r and (1+1/D)^(r−1). Both conclusions hold along the same sequence. In particular, for every such window function the ratio can be arbitrarily close to 2 at one start and arbitrarily close to 1 at the next.

Indeed choose the successful start from the main proof with at least r distinguished prime rows. Let n be one less than the r-th such row counting backwards. Advancing to n+1 removes that prime row. At both starting integers all remaining distinguished rows are within the window for all large n. Both windows stay in the interval on which the ordinary rows have total log gain tending to zero. The finitely many distinguished composite rows also have negligible log gain. The proof of the main theorem now gives both limits, including when the two window lengths differ.

More generally at bounded nonnegative shifts of n one obtains the whole list of powers from r down to zero in that order. Choose each starting offset immediately before the first remaining distinguished prime row, and use an offset after the last row for the empty suffix. All shifts are bounded by the fixed width of the tuple times D. Passing to a subsequence makes these integer shifts constant. The prime rows used for all the limits belong to a single selected cluster at each starting scale.

For every nondecreasing growing window function in this range the relative drop is sharp:
    
$$
\liminf_{n\to\infty} \frac{F_f(n+1)}{F_f(n)}=\frac12 .
$$

To see the reverse bound, put $h_n=\lfloor f(n)\rfloor$ and $U(j)=\tau(j!)/\tau((j-1)!)$. The numerator of $F_f(n+1)$ comes from a factorial at least as large as the one in the numerator of $F_f(n)$. Factorial divisibility gives $F_f(n+1)/F_f(n)\ge 1/U(n+1)$. By EGIP Theorem 2, $U(n+1)\le 2+O(n^{-1/2})$. The simultaneous limit pair $(2,1)$ gives equality in the liminf. The absolute decrease $F_f(n)-F_f(n+1)$ can be arbitrarily large, even for oscillating growing windows in the stated range, since every fixed pair $(2^r,2^{r-1})$ is attained as a joint limit.

As a finite illustration, n=7,972,317 has n+1 and n+5 equal to twice the twin primes 3,986,159 and 3,986,161, respectively. Exact arithmetic gives 2.2595908425 (rounded) for a window of length five and 2.2688958037 for length fifteen. Every one of the eleven integer window lengths from five to fifteen has a ratio strictly between 2.25 and 2.27. The script checks the endpoints and the interval using exact integer valuations in two ways. This example illustrates the prime contributions; the proof applies at arbitrarily large n. [Exact checker](example.py)
