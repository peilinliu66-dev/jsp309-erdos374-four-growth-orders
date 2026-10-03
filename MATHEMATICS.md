# Mathematical scope and proof map

This exposition describes the supplied Lean proof chain and the original problem correspondence. Formal verification outcomes are recorded separately in [AUDIT_REPORT.md](AUDIT_REPORT.md). The mathematical solution followed here is Fedir Yudin's [October 2026 paper](https://arxiv.org/html/2610.01899v1), Theorems 1.1 and 1.2 and Corollary 1.3. The original growth question is for $3\le k\le6$; the contribution of this project is its Lean formalization of those four orders.

## Definitions and endpoint

A representation of size $k$ at endpoint $n$ is a finite set $S$ of natural numbers satisfying

$$|S|=k,\quad n\in S,\quad 1\le a\le n\ (a\in S),\quad \prod_{a\in S}a!\text{ is a square}.$$

The finite-set presentation is equivalent to a strictly increasing positive tuple ending at $n$. `HasRepresentation k n` imposes those conditions. `IsInD k n` additionally requires $k\ge2$ and excludes **every** smaller $j\ge2$. Hence it expresses the least admissible number of factorials, not merely the existence of a $k$-factor construction. The conditions imply $n\ge2$, since $k$ distinct positive indices at most $n$ require $k\le n$.

`countD k X` is the number of such endpoints in the integer interval $[1,X]$. `HasOrder f g` requires fixed positive real constants $c,C$ such that both inequalities $c g(X)\le f(X)\le Cg(X)$ hold for every sufficiently large integer $X$. The final declaration

```lean
theorem Erdos374Research.erdos_374_original_growth :
    Erdos374Research.OriginalGrowthConclusion
```

has exactly the four clauses for $3\le k\le6$:

$$D_3(X)\asymp\sqrt X,\qquad D_4(X)\asymp X,\qquad D_5(X)\asymp X,\qquad D_6(X)\asymp X.$$

There are no additional mathematical premises at that endpoint. The auxiliary short-block interface is discharged in `FinalTheorem.lean` by the proved ordered long-block theorem. The target does not demand the paper's sharper leading constant and error term for $D_3$, or existence of limiting densities for $D_4,D_5,D_6$.

## Supplied proof map

The following mathematical text is retained from the source package without removing any of its proof steps. Its introductory sentence describes an exposition rather than a compilation certificate. Additional implementation clarifications follow it.

### Proof map

This explains the complete source draft; it is not verification.

#### D3 and D4

Finite-set representations are equivalent to increasing tuples. Erdős–Selfridge
reduces two-factor representations to squares. The family 2q² supplies the D3
lower bound. Consecutive triples are bounded by sqrt(X) times a summable factorial
squarefree weight. Nonconsecutive triples use uniform Pell estimates and a two-range
larger sieve, giving exponent 0.4996. Thus D3 has an actual constant-factor sqrt(X)
upper bound without a logarithmic loss. Multiples of four give four-factor
representations; removing D2 and D3 gives a linear lower bound for D4.

#### Long blocks

Four or five factorials become two ordered falling-factorial blocks and a smaller
factorial coefficient. The genuine all-interval prime theorem at exponent 3/5 gives
preliminary length≤n^(2/3); upper-half primes in c! give c=O(L log n+1). When n=a·p
with a small, p forces m−j=t·p in the lower block, with 1≤t<a. A smooth detecting
weight at P=ceil(L log² n) vanishes at every prime but has a positive comparison
integral. Rational-period mass, square-divisibility avoidance, C³ and rounding
bounds are derived. The fixed reciprocal-phase estimate contradicts L≥n^ε.
Consequently both lengths are<n^ε and c<n^(2ε).

#### Candidate density

Even squarefree cofactors have positive lower density. For D6 use squarefree a
such that a≤s(a·c!) for every c, with s the squarefree component. Roughness handles
small c; an exponential summable tail handles the remaining excluded densities.
A finite CRT sieve supplies the rough squarefree cofactors.

Windowed Abel summation gives harmonic mass≫α log X in X^(α/2)<a≤X^α.
Upper-half primes give≫αX distinct products n=a·p in (X/2,X]. An elementary finite
Euler-product moment and a square-divisor tail bound the failure of a prime
>X^(3ε) in s(n−1) by C exp(−1/(9ε))X+O(X^(3/4)). One sufficiently small ε makes
this error smaller than both positive candidate densities. No independence
assumption is made.

#### D5 and D6

The large odd-valuation prime in n−1 forces the first short block to be a singleton.
If the second block has length≥2, cancelling its unique p factor leaves a scalar
times a product of distinct linear factors with one root removed. The sharp Weil
bound and finite large sieve give O(sqrt(X) log X) solutions per parameter tuple.
Counting all five parameters still gives O(X^(3/4)) exceptional endpoints.

Outside that exception, both blocks are singletons. Squarefreeness excludes four
factors; the admissible cofactor condition excludes five factors too. Even
candidates have the Straus five-factor construction; admissible candidates have
the Erdős–Graham six-factor construction. Every factorial index is distinct and
positive. Removing D3 leaves linear lower bounds for D5 and D6; count≤X gives
their upper bounds. FinalTheorem.lean assembles all four clauses without added
mathematical premises.


## Implementation clarifications from the source review

### Three-factor constant bounds

The two-factor theorem identifies $\mathcal D_2$ with the squares $n\ge4$. For $q\ge2$, $n=2q^2$ has the three distinct positive indices $2,n-1,n$ and

$$2!(n-1)!n!=2n((n-1)!)^2=(2q(n-1)!)^2.$$

Since $2q^2$ is not a square, this gives membership in $\mathcal D_3$, including minimality. The implementation obtains an eventual lower bound $D_3(X)\ge\sqrt X/4$.

For the upper bound, the consecutive family for a fixed smallest index $a$ contributes at most $\sqrt X/\sqrt{s(a!)}$. The eventual estimate $\log s(a!)\ge a/4$ makes the weight at most $e^{-a/8}$. Its sum over all $a$ is finite, so summing over the smallest index costs a fixed constant rather than $\log X$.

For nonconsecutive representations, the implementation uses the fixed values

$$\eta=1/100000,\quad \beta=1/10000,\quad \gamma=999/2000,\quad \delta=1249/2500.$$

The two-range larger sieve gives a positive denominator proportional to $\log X$. Its leading coefficient is

$$\frac1{400}+\frac{10000}{5001}\left((1-1/100000)\frac{999}{2000}-\frac2{10000}\right)-1
=\frac{89051}{100020000}>\frac1{1250}.$$

After the explicit error allowance, the denominator is at least $(\log X)/2000$. Each hard fibre is $O(X^\gamma)$; counting both free parameters contributes $X^{2\eta}$, so the exponent is $\gamma+2\eta=0.49952\le\delta=0.4996<1/2$. The other Pell branch is $O(X^{3/8})$. These weaker but sufficient exponents give the constant-factor $\sqrt X$ upper bound required here. The project does not replace that bound by $X^{1/2+o(1)}$.

For $D_4$, the indices $u-1,u,4u-1,4u$ with $u\ge2$ give

$$(u-1)!u!(4u-1)!(4u)!=\bigl(2u(u-1)!(4u-1)!\bigr)^2.$$

This first proves that the minimum representation size is at most four. Removing the already bounded $D_2$ and $D_3$ terms then gives the linear $D_4$ lower bound; the finite counting bound $D_4(X)\le X$ gives its upper bound.

### Ordered blocks and cancellation

Write an ordered four- or five-factor representation as two positive falling-factorial blocks, with the smallest factorial coefficient $c!$ in the five-factor case. In the four-factor case $c=1$ is a coefficient convention: it does not add an extra factorial index to the representation.

For a candidate $n=ap$ with a sufficiently large prime $p$, the upper block contains one factor divisible by $p$, to valuation one. The square condition forces a unique lower-block term $m-j=tp$ with $1\le t<a$. The block bounds make all relevant factorial and block parameters smaller than $p$.

The long-block argument uses a genuinely uniform all-interval prime theorem and a smooth detecting weight. Its rational-period estimate uses the complete $a$-term orbit of $e(t/a)$, whose sum is zero even when $a$ and $t$ are not coprime. Thus no extra coprimality assumption is introduced. The positive comparison mass, reciprocal-phase estimate, rounding bounds and square-divisibility exclusion force both lengths below $n^\varepsilon$ and $c\le n^{2\varepsilon}$.

The additional prime $q>X^{3\varepsilon}$ divides $s(n-1)$, so its valuation in $n-1$ is odd. If both blocks contained the forbidden odd valuation, $q$ would divide a nonzero integer of the form $a(j-i)+t$, with absolute value less than $a\ell_2$. The source bounds make that smaller than $q$, a contradiction. The first block is therefore a singleton. All natural-number subtraction and puncturing identities are used under their explicit index bounds.

### Counting every short-block parameter

If the second block has length at least two, cancelling its unique $p$ term leaves a nonzero scalar times a product of distinct field roots, with one root removed. The polynomial remains nonconstant. The residue count includes zero values as squares, giving the correct bound

$$\frac{q+r+(r-1)\sqrt q}{2}$$

for $r$ distinct roots. The large-sieve stage uses the complementary forbidden residues in the appropriate direction.

The exceptional-set count includes all five parameters $(a,t,c,\ell_2,j)$. With $B=\lceil X^{2\varepsilon}\rceil$ and $K=\lfloor\sqrt X\rfloor$, the finite bound used is

$$K|E(X)|\le(B+1)^5\,96(X+1)\log X.$$

Consequently $|E(X)|=O(X^{1/2+10\varepsilon}\log X)$. For the selected $0<\varepsilon<1/100000$, the implementation conservatively absorbs $X^{10\varepsilon}$ and $\log X$ into two factors $X^{1/8}$, obtaining $|E(X)|\le93312X^{3/4}$ eventually. This is sublinear, which is all the final density subtraction needs.

### Density quantifiers

The admissible cofactor condition is imposed on a positive squarefree integer $a$ and requires

$$a\le s(ac!)\qquad\text{for every }c\in\mathbb N.$$

It includes $c=0$. For a fixed roughness cutoff $B$, a finite CRT sieve first supplies a positive-density rough squarefree family. Its period is fixed before $X$ is sent to infinity. For $c\le B$, roughness makes $a$ coprime to $c!$ and gives the admissibility inequality.

For the remaining $c$, write $b=s(c!)$ and $g=\gcd(a,b)$. Squarefreeness yields

$$s(ac!)g^2=ab.$$

An inadmissible $a$ has $b<g^2$, providing a large-divisor witness. The divisor bound and $\log b\ge c/4$ give an exclusion weight $O(e^{-c/16})$. In each finite endpoint interval, only the finite set of chosen bad witnesses is summed. The uniform finite-tail estimate applies even though that witness set may depend on $X$. This avoids exchanging a density limit with an uncontrolled infinite union.

Windowed harmonic mass and upper-half primes supply distinct products $n=ap$. The prime is eventually larger than every allowed cofactor, so equality of two products forces equality of their prime and cofactor choices. The loss from $s(n-1)$ having no prime factor above $X^{3\varepsilon}$ is bounded explicitly. One fixed sufficiently small $\varepsilon$ is chosen before the endpoint threshold and works for both candidate families; it does not vary with $X$. No probabilistic independence premise is used.

### Exact minimality for five and six factors

For even $n\ge8$, the five-factor construction uses the distinct indices

$$2,\quad n/2-1,\quad n/2,\quad n-1,\quad n.$$

For $n=ap$, the six-factor construction uses

$$a-1,\quad a,\quad p-1,\quad p,\quad ap-1,\quad ap,$$

with $a\ge3$ and $a+1<p$. Those inequalities give strict ordering and positivity.

Outside the exceptional set both blocks are singletons. A four-factor representation would make $nm$ square with squarefree $n$ and $0<m<n$, which is impossible. A five-factor representation for an admissible cofactor would make $atc!$ square with $0<t<a$; admissibility would force $s(t)=s(ac!)\ge a$, contradicting $s(t)\le t<a$. These are exclusions of smaller representation sizes, not just constructions of the desired size.

The assembly excludes sizes $2,3,4$ for $D_5$ and $2,3,4,5$ for $D_6$. Positive-density candidates are covered by the desired set, the short-block exceptional set and $D_3$. The latter two each cost at most $\delta X/4$ eventually, leaving $\delta X/2$. Together with $D_k(X)\le X$, this gives fixed positive linear lower and upper constants for both final clauses.
