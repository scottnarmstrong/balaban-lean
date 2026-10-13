# LFH7PRIME2: physical base and same-rate transport of the hole-shell charge

**Verdict (2026-10-13).** G1 is **OPEN** for the actual O(N) coefficients; automatic transfer from P5/P7
large-field factors to H7′ is **REFUTED** by their placement in operators, not coefficients. G2 is **OPEN**,
with a stronger inequality than `LFH7PRIME.md`'s (P6-spend): the output must retain the *same* $\sigma q$ as
well as pay its modular size. R1 is therefore not yet a viable Roland-independent route for blocker 3. Send
the question below before designing Lean leaves.

**Scope/freeze.** Focused refute-first source/design check at `19dd0a56` (after fast-forward from `main`);
P5 `s002200050433 (1).pdf` SHA256 `b3f0ef34`, P6 `s002200050470.pdf` `ee0ca061`, P7 `s002200050486.pdf`
`c48e08dd`, `LFH7PRIME.md` `8423e5df`, `LFROOT3.md` `78eed465`. Printed pages/equations are cited below.
H7′, $q$, and the proposed allocations are ours, not Balaban's. No physical coefficient is calculated here;
a class counterexample is not one.

## G1. Does a physical boundary coefficient acquire $e^{-\sigma q}$?

**Refutation test.** In `LFROOT3.md` §2, a constant H7 coefficient on the two-step rectangle has
$D_-(X_n)=O(1)$ and $q_-(X_n)=\Theta(n)$; no interpolation marks survive. It violates every fixed $\sigma>0$
H7′ bound when its nonzero magnitude is chosen independent of $n$. This is an admissible *H7-class*
coefficient, not an exhibited physical O(N) one. Any proposed G1 proof must use the physical producer, not
H7 alone.

**Candidate (a), large-field small factors.** P5 p. 492 (1.18)–(1.19) are characteristic functions with
values $0,1$. P5 pp. 495–96 (1.29)–(1.31) estimates $T_k(Z)$ *after integration* by $e^{-\ell
p_2(\beta_k)-H_k|Z|_\eta}$; H7 on p. 497 (1.38)–(1.39) separately bounds $B^{(k)}(X)$ by $B_0e^{-\kappa
d_k(X\bmod\Omega_k^c)}$. In P5 p. 513, after (2.48), the pre-integration boundary expression is explicitly
independent of the new $P,Q,R,S$ cubes; their restrictions enter through characteristic functions and
integrations. Thus a bad cube adjacent to a new hole does not itself multiply *each* boundary coefficient
touching that hole by a probability factor.

The first P5 boundary producers already show the scale of the available gain: pp. 508–9 (2.31)–(2.33)
bound a quadratic and a surface-wall term by $O(e^{-R_k})$ using their fixed separation from fluctuation
support. P5 p. 515 (3.2)–(3.4) spends $d_k(X\bmod\Omega_k^c)>R_k$ from an *old* boundary term to gain
$e^{-R_k}$ in its localized successor. Neither is a bound proportional to the entire hole shell. At the
no-hole base $q=0$ is vacuous; the first nontrivial physical-base test is the first hole's birth.

At creation, one could seek an exact conditional expansion $T^{\rm new}e^{B_{\rm edge}}=\widetilde T^{\rm
new} e^{\widetilde B_{\rm edge}}$ with $|\widetilde B_A(X)|\le C e^{-aD(X)-\sigma q(A,X)}$. It must give a
per-coefficient allocation: for every hole $H$ and every cluster of boundary terms it touches, the assigned
discounts $\sigma q(H,X)$ plus operator/gas entropy costs cannot exceed the *single* available large-field
budget of that event. Merely writing $T=e^{-c} (e^cT)$ only moves a scalar between factors; it does not make
$B$ small. P5 (1.31) supplies no such identity or allocation. Its $p_2$ reserve is per component, so a fixed
share cannot pay a shell with $q=\Theta(n)$ uniformly in $n$; $H_k|Z|_\eta$ might pay shell cells only after
an injective shell-to-restricted-cubes map and the existing operator and polymer-gas expenditures are
subtracted. No such map or residual constant is in P5.

P7 pp. 519–20 (3.7)–(3.10) likewise gives its $p_2+H_k|Z|_\eta$ gain to the $R$ operator of a **removed**
component $Z$, after costs such as (3.9). P7 pp. 525–27 (3.22)–(3.25) creates new boundary terms by
background/action conversion; (3.23)'s small constant comes from the distance of localization from a changed
boundary, and the later extension terms need not even have that small constant. P7 pp. 527–29 (3.26)–(3.28)
uses (3.10) again to make the gas summable and returns ordinary H7 coefficients, with $B_0$ independent of
the old one. Neither passage states a shell charge on a *retained* hole. Assigning the same $R$ discount to
its gas and to every new H7′ term would spend it twice. **G1 status: OPEN for a new conditional producer;
REFUTED as a consequence of the displayed source bounds.**

**Candidate (b), decay through a hole.** P7 (3.22)–(3.24) localizes the change in background data to
boundary layers and applies the P3 off-diagonal expansion; P6 p. 34 localizes an old term from its active
part $X\cap\Omega_{k+1}$ using marks. These yield decay with the distance from a *read/change site* to a
localization site, not with the perimeter of every hole completed into the label. On the `LFROOT3` zero-mark
rectangle, label completion reaches the far end although the coefficient has no read there. Hence the
proposed implication “touches a collar $\Rightarrow e^{-\sigma q(H,X)}$” is **REFUTED** for localization
estimates alone. A physical cancellation or a different labeling of all source terms is still **OPEN**.

## G2. Can one step return H7′ with the same $\sigma$?

Write $a_-=3\kappa/2$, $a_+=\kappa$, $D_-=d7SizePre$, $D_+=d7Size$, and $q_\pm$ for the input/output history
labels. For every nonzero P6 assignment $(X,J,Y)$, a sufficient termwise budget (with strict prefactor
slack) is
$$
\kappa D_+(Y)+\sigma q_+(Y)+E_{X,J,Y}
\le a_-D_-(X)+\sigma q_-(X)+g|J|+G_{\rm birth}(X,J,Y). \tag{*}
$$
$E$ includes label/mark fibers and new prefactors; $g|J|$ is the proved marked-localization gain;
$G_{\rm birth}$ may be positive only when a **new, separately allocated** large-field event produces this
coefficient. For old seedless terms it is zero. The old (P6-spend) in `LFH7PRIME.md` omits $\sigma q_+(Y)$
and so establishes, at best, ordinary post-H7. For a newly born shell with $q_-=0$, (*) requires a creation
gain of at least $\sigma q_+$ plus the new-size deficit.

**Rectangle test.** For `LFROOT3`'s zero-mark family, $D_-(X_n)=O(1)$, $D_+(Y_n)\ge cn-O(1)$, and
$q_-(X_n)=s_-n+O(1)$, $q_+(Y_n)=s_+n+O(1)$ for shell-count slopes fixed by the two grids and the inherited
enlargement. Thus (*) requires $\sigma(s_--s_+)\ge\kappa c+\limsup E_n/n$. If $s_-\le s_+$ it fails for
a coefficient saturating H7′; a coarsening saving $s_->s_+$ works only if that inequality is proved
uniformly for the actual aligned history. Neither slope comparison nor the available creation rate is
established by H7′ or P6 (4.32)–(4.34).

**Growth, merges, and removal.** For multiple input labels and holes, the necessary cluster version is
$$
\kappa D_+(Y)+\sigma q_+(Y)+E_\Gamma
\le\sum_{i\in\Gamma}(a_-D_-(X_i)+\sigma q_-(X_i)+g|J_i|)
   +G_{\rm new}(\Gamma)+R_{\rm rem}(\Gamma). \tag{**}
$$
Count each new large-field cube and each removed-component $R$
reserve at most once. Growing a shell, joining two holes with a strip, or post-$R$ relabeling can create
$q_+$ not present in the old $q_i$; the excess requires $G_{\rm new}$ or a proved geometric saving. For two
labels meeting only in one retained hole (`VMOD-41` §2), the two $q_i$ may fund an output shell and part of
the $\Omega(n)$ bridge, but (**) needs explicit rates, active-overlap incidence, and an absolute cluster
bound. P7 (3.10) pays the two **removed** cores, not the retained bridge; (3.26)–(3.28) do not establish
(**). If a hole is removed, its output $q$ disappears, but the same saved factor cannot then also pay the
gas activity. New action-conversion terms (3.23), including ones born beside retained holes, must satisfy
(**) separately. **G2 status: OPEN, with no same-$\sigma$ induction.**

**Decision and exact leaves.** R1 remains a conditional research idea, not a closed alternative to asking
Roland. The required leaves are: physical G1 at every P5/P7 creation site with a shell-to-event map; an
operator/coefficient/gas ledger for each event; (*) for P6's physical background and mixed covariance square
root; (**) for P7's absolute gas and new terms; and a uniform geometry lemma for $q$ under growth, merges,
and removal. No Lean implementation follows from the present evidence.

**Question to Roland (five sentences).** In the P5–P7 construction, can an actual boundary coefficient
touching a large-field hole be bounded by $e^{-\sigma q_k(A,X)}$ for a fixed $\sigma>0$, where $q_k$ counts
that hole's boundary-shell cells? If so, which formula assigns the gain to the coefficient when the hole is
born, rather than to P5's operator estimate (1.31) or P7's removed-component operator (3.10)? How much of
the same large-field gain must remain for the P7 polymer gas (3.26)–(3.28)? When a hole grows or two holes
merge, what estimate pays both the new modular size and the output shell charge at the same $\sigma$? If
this coefficient charge is unavailable, is the intended repair a different boundary-label localization or a
factorization/cancellation in the physical O(N) gas?
