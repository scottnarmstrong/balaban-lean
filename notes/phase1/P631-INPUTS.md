# Inputs to the window action conversion of P631

**12 October 2026.** The target is P631 §2–§3, with the finite regional action
of P631 §1. This note proves the scale-ratio arithmetic and the finite wall
and action-difference inequalities. It identifies the exact hypotheses still
needed to apply them to the window. A complete unconditional proof of (W),
the first inequality of P7 (2.11), and the P6 (2.25) wall estimate for the
actual regional variational solution does **not** follow from the landed
results or the proved statements of LF-RECONSTRUCTION. The missing claims are
stated below as quantified targets. A citation to P6 or P7 for an asserted
estimate is not a proof that the estimate follows from the landed Lean API.

| P631 input | Proved here | Remaining assertion |
|---|---|---|
| (W) window decay | finite action difference and absorption of a polynomial by the chosen collar for $j\ge1$ | OPEN-P631-W-CROSS; OPEN-P631-W-MARGIN; OPEN-P631-W-BASE when $k_1=0$ |
| P7 (2.11) | exact free-flow and running ratios, with uniform geometric factor $9e^{2\epsilon}$ | OPEN-P631-RELATIVE-COST |
| P6 wall after (2.25) | finite bond estimate and conversion from local product/count bounds | OPEN-P631-WALL-LOCAL |

## 1. Domain and existing inputs

Use $1\le k\le k_0$ of LF-RECONSTRUCTION (A-III.2),
$k_1\le j<k$, $X_j=Z_j^c\cap Z_{j+1}$, and
$D_j=M([\hat R_{j-1}]-1)-2M_1$ **when $j\ge1$**. LF-RECONSTRUCTION
§I.1.2 allows $k_1=0$ if its defining set is empty, whereas its base
case in §I.3.1 expressly never uses $R_{-1}$. Thus P631's stated formula
does not define $D_0$. An independent base-layer version of (W), with
a defined decay distance and its own action/collar proof, is required if
the window includes $j=0$; call it **OPEN-P631-W-BASE**. Assigning a
value to $\hat R_{-1}$ would change the source convention without proof.
All backgrounds in this window use the
field-free variational equation, while the physical $\nu$ term remains in
the action. The P5 (1.32) complex window set must have an **open**
neighbourhood on which each compared background, its composition, and the
regional P6 (2.24) solution are analytic. The parameter family may include
the localization parameters only when those are needed for an expansion;
the raw identity and the per-volume estimate do not require an I-5 polymer
expansion.

The following source statements are available without strengthening them:

* LF-RECONSTRUCTION Lemma II.2.5(a),(c) proves that the local step sets are
  generating sets and that their **layers** coincide with those of the
  boundary set on $E_{Z'}=Z'^{\sim[R_j]}$. It does not say their minimizers
  agree on $E_{Z'}$.
* LF-RECONSTRUCTION Definition III.2.1 specifies $\mathbb B_{k_1,k}$;
  Lemma III.2.2 labels the window action conversion *cited* and conditional
  on O-2′. Its displayed (2.15′) cannot be used as an input to prove itself.
  Lemma IV.1.3 is likewise conditional on the FLUCTUATION Theorem 4.2 inputs;
  using it to supply those inputs would be circular.
* `theorem73_real` and `theorem73_complex` in
  `Balaban/Background/Theorem73.lean` give composition for a `Precedes`
  pair with their stated domain hypotheses. `lemma62` in
  `Balaban/Background/CompositionDomain.lean` is a **real** domain
  inclusion requiring `FieldBounds` and a mass bound. None compares
  minimizers of two different generating sets at distant sites.
* `lemma41_domain_uncond` in
  `Balaban/Fluctuation/FarDecayUncond.lean` is now proved using the corrected
  `WeightedProp51S`. It yields value, gradient, Laplacian, and multiplier
  decay for **two data on one fixed generating set**, with equal $h$,
  prescribed support of $\delta\Psi$, both complex-domain inclusions and
  `Dec2.OpSetting`. It does not change the generating set.
* `i4b_close`, `i4b_analytic`, and `i4b_local` in the landed
  `Balaban/Localization/Decoupled2Background*.lean` files have explicit
  `CoverBase` or `CoverLocal` hypotheses for a cover/operator pair.
  `i5_background` and `i5_fluct` also retain their `BgSetting`/
  `FlSetting` and cover hypotheses. These are theorems **under** those
  structures; no theorem in these files instantiates them for every
  window pair $G^{Z'}_{j+1},\mathbb B_{k_1,k}$.
* `prop51_exists_unique` and `prop51_analytic` in
  `Balaban/Background/Contraction.lean` and
  `Balaban/Background/ContractionAnalytic.lean` solve a general small
  source problem. `IsRenSol` in
  `Balaban/Fluctuation/RenormExpLemma35.lean` specializes to the
  whole-lattice renormalization source; it has no P6 (2.31) boundary cut
  source. `renormC1`, `renormC2`, `renormC3`,
  `lemma35_i_complete`, and `lemma35_i_nuFree` in
  `Balaban/Fluctuation/RenormIdentity.lean` have no regional star term.

The exact mixed-cover warning is substantive: VMOD-2 §2–§3 and VMOD-7 §5
leave `OPEN-NC3-MIXED-WALL`, hence the needed mixed `CoverBase.nc`, open at
a physical Dirichlet wall. `i4b_close` is not an unconditional comparison
of the two window backgrounds merely because it is a proved declaration.

## 2. The window decay (W)

### 2.1 A finite action estimate that is proved

The estimate below is independent of the method used to obtain background
decay. Let $Q$ be one action cube and $R$ contain every bond endpoint and
block read by its regional action. Let $\phi'=\phi+\tau$ be two hard-spin
backgrounds for the *same* action datum. Suppose, on $R$, the block
residual and each bond derivative of $\phi$ are at most $r$ in the
normalization of P631 (1), and the corresponding value, block average and
derivative of $\tau$ are at most $T$. Suppose also
$\nu\|\phi-h\|\le m$ there. If $c_{\rm cell}$ bounds the number of
block, bond, mass and boundary reads per action site and their fixed
weights, then

$$\left|\beta\big(A_Q(\psi,\phi+\tau)-A_Q(\psi,\phi)\big)\right|
\le c_{\rm cell}|Q|\,\beta\{2rT+T^2+mT+\nu T^2/2\}.\tag{2.1}$$

The same inequality includes a crossing bond when it is assigned to $Q$
with the P631 half-bond convention. **Proof.** For each complex bilinear
quadratic term, $B(u+v,u+v)-B(u,u)=2B(u,v)+B(v,v)$.
The ordinary triangle inequality and
$|\sum_i u_iv_i|\le(\sum_i|u_i|^2)^{1/2}(\sum_i|v_i|^2)^{1/2}$
bound its linear and quadratic parts by $2rT+T^2$.
For the mass term, expand
$\nu[(\phi+\tau-h)^2-(\phi-h)^2]/2$; its bound is
$mT+\nu T^2/2$. Sum the finitely many reads, charging a crossing bond
according to its half weight. This is (2.1). $\square$

For a *single fixed* generating set $G$, `lemma41_domain_uncond` supplies
$T=K_wc_F\delta_1e^{-\gamma_w d_G(R,S)}$ when its two complex-domain,
same-$h$, support, source-size, and operator-setting hypotheses hold.
`cubeDiff_step3` and `cubeDiff_step3_quadratic` in
`Balaban/Fluctuation/CubeActionBound.lean` formalize (2.1)'s block/bond
part with the explicit factor
$\frac12(d+3)N(2rT+T^2)$ per site. Their statements still bind one $G$,
one pair of data, and `RegIneq` on $R$; they are not a cross-generating-set
window comparison. The field-free action needs the $mT$ term because its
physical mass is absent from the variational equation.

### 2.2 Exact missing bridge and the conditional proof

For each $j$ and each lineage component meeting $X_j$, define the
following **OPEN-P631-W-CROSS** datum. There must be one common action
carrier and, on one open complex window neighbourhood, analytic fields
$\phi_j^{\rm old},\phi_j^{\rm win}$ representing respectively the
converted local and the $\mathbb B_{k_1,k}$ backgrounds on every block and
bond read by $X_j$. Both must lie in the required background domains.
Their difference $\tau_j$ and its first differences and Laplacian obey

$$\|\tau_j\|_{*,R(Q)}+\|\delta\alpha_j\|_{*,R(Q)}
\le K_{\rm resp}\varepsilon_j
 e^{-\gamma_{\rm far}d_j^{\rm phys}(Q,S_j)}
\quad(Q\subset X_j),\tag{2.2}$$

where $S_j$ is the actual set where the two input equations or data differ,
and $d_j^{\rm phys}$ is the path distance in the operator generating set.
The representation must preserve the physical $\nu$ action term, use the
field-free solver, and keep $h$ fixed. It must also prove the site/bond
read inclusion $R(Q)\subset$ the common domain and the collar separation
from $S_j$. The layer agreement of Lemma II.2.5(c) supplies an equation
agreement *candidate* on $E_{Z'}$; it does not supply (2.2).

The last scalar step in (W) is not automatic from decay alone. Assume the
complex small-field bounds $r_j\le K_r\varepsilon_j$ and
$m_j\le K_m\varepsilon_j$ on each $R(Q)$, the bounded cube-read count
$\sum_{Q\subset X_j}|Q|\le K_{\rm count}|X_j|_{j+1}$, and either

$$d_j^{\rm phys}(Q,S_j)\ge D_j+\sigma\hat R_{j-1}
\quad\text{with }\gamma_{\rm far}=\gamma_w,\ \sigma>0,\tag{2.3a}$$

or the corresponding weaker geometric inequality with a **strictly
larger** input decay rate $\gamma_{\rm far}>\gamma_w$ and enough rate
slack that $(\gamma_{\rm far}d_j^{\rm phys}-\gamma_wD_j)$ grows at least
$c\hat R_{j-1}$. Call this precise margin **OPEN-P631-W-MARGIN** until
proved for the actual local/window pair; do not identify a $pi_j$ collar
with an operator path distance without the layer comparison.

For $j\ge1$, under (2.2)–(2.3), (2.1) gives

$$|B_j|\le C_{\rm loc}\,\beta_j\varepsilon_j^2
e^{-\gamma_{\rm far}d_j^{\rm phys}}
|X_j|_{j+1}
\le K_{\rm bg}e^{-\gamma_wD_j}|X_j|_{j+1}.\tag{2.4}$$

Here the second inequality has a **proved numerical reason**: from
LF-RECONSTRUCTION (I.1)–(I.3), Definition II.1.1 and row 11,
$\varepsilon_j\le3\alpha_0L^{-\alpha j}$ and
$\beta_j\le e^\epsilon\beta_0L^{j(d-2)}$. Thus
$\log(\beta_j\varepsilon_j^2)$ is bounded above by an affine function
of $x_j=\log(\beta_0a)+1+j(d-2)\log L$, while
$\hat R_{j-1}=R_{\rm base}x_{j-1}^2$. For every $c>0$,
$\sup_{x\ge\lambda_*}\exp(C_0+C_1x-cR_{\rm base}x^2)<\infty$.
Take that supremum into $K_{\rm bg}$; it depends on the row 0–11
constants, not on $B_0,H_0,c_1,c_2$ or the final $\beta_0$.
Analyticity and dependence on $\psi|_{W^\sim\cap U_k^\sim}$ follow by
finite composition once the representation and domain/support clauses of
OPEN-P631-W-CROSS hold. This proves the $j\ge1$ part of (W)
**conditional on the two precisely stated cross-set and margin claims**.
The $j=0$ part additionally needs OPEN-P631-W-BASE.

The $m_j$ premise must be checked on the **actual** complex domain.
For the Part III physical window $h$ is a fixed real unit vector (or is
restricted to a fixed bounded complex neighbourhood), and
$\beta_j\nu_j\le e^{2\epsilon}$ makes
$\nu_j\|\phi-h\|\le K_m\varepsilon_j$ after the ordinary background
bound and a sufficiently large final threshold. On a domain allowing
arbitrary independent complex $h$, this assertion is false: for any
nonzero $\tau$, the mass cross term
$\nu_j\langle\tau,\phi-h\rangle$ is unbounded as $h$ moves along
$\tau$. Thus a uniform reading of (W) on such an $h$ domain is false;
the fixed-$h$ domain is part of the theorem, not a dispensable proof
device.

The source P6 (2.13) has the stronger-looking distance
$2MR_j-M-2M_1$ for its particular pair; P631's $D_j$ is
$M([\hat R_{j-1}]-1)-2M_1$. Transferring that extra margin to *every*
local window component is an additional geometric statement, not a
consequence of `theorem73_complex`. LF-RECONSTRUCTION Lemma III.6.4(c)
uses a surface exponential under (Λ25)(c), but concerns a later
background comparison and does not establish OPEN-P631-W-MARGIN.

**Relation to named open items.** The needed common-cover route to
OPEN-P631-W-CROSS is an instance of the **type** of two-operator estimate
called OPEN-NC-MIXED in VMOD.md, followed by LOC I-4b and the relevant
composition. The already named OPEN-NC-MIXED is written for P6's
$H^-,H^\partial$ pair; the worker must still prove that its cover and
geometry instantiate the local/window pair here. At a crossed physical
wall, OPEN-NC3-MIXED-WALL is a missing sublemma of that route. Neither
open item by itself includes (2.3), the complex-domain inclusions, or the
action-read bound. OPEN-P631-W-BASE is a separate index-zero action and
collar obligation; neither NC item defines $\hat R_{-1}$. Q13 is
irrelevant to this $k\le k_0$ window.

## 3. P7 (2.11): what is proved and what is open

Let $q_j=1+\sum_{m\ge j}m^{-2}$ with the $m=0$ summand interpreted as
zero, as in landed `epsTail`. The landed `epsSeq` is
$\varepsilon_j=\alpha_0q_jL^{-\alpha j}$ and
`epsSeq_gapE` proves its one-step gap. LF-RECONSTRUCTION row 11 gives
$1\le q_j<3$. The running coefficient identity (I.2), supported by
`betaSeq_eq` and `norm_gammaSeq_le` in
`Balaban/Flow/RunningCoefficients.lean`, is
$\beta_j=\beta_0L^{j(d-2)}g_j$ with
$e^{-\epsilon}\le g_j\le e^\epsilon$.

**Proved ratio lemma.** If $j+2\le n$, $\alpha=(d-2)/2-\gamma$ and
$\gamma>0$, then

$$0<\frac{\beta_{j+1}\varepsilon_{j+1}^2}
              {\beta_n\varepsilon_n^2}
=\frac{g_{j+1}}{g_n}
 \left(\frac{q_{j+1}}{q_n}\right)^2
 L^{-2\gamma(n-j-1)}
\le9e^{2\epsilon}L^{-2\gamma(n-j-1)}.\tag{3.1}$$

**Proof.** Substitute the two definitions. The power of $L$ is
$-(n-j-1)(d-2-2\alpha)=-2\gamma(n-j-1)$; the initial
$\beta_0\alpha_0^2$ cancels. Positivity follows from
$\beta_0,\alpha_0>0$. The running factors have ratio at most
$e^{2\epsilon}$ and $q_{j+1}/q_n<3$. $\square$

For the free-flow stream used in P631 §3, LF-RECONSTRUCTION Definition
II.1.1 gives $\beta_m^{(t)}=\beta_tL^{-(t-m)(d-2)}$ for $m\le t$.
Consequently, for $t\ge n$,

$$\frac{\beta_{j+1}^{(t)}\varepsilon_{j+1}^2}
        {\beta_n^{(t)}\varepsilon_n^2}
=\left(\frac{q_{j+1}}{q_n}\right)^2
 L^{-2\gamma(n-j-1)}
\le9L^{-2\gamma(n-j-1)}.\tag{3.2}$$

This follows by substitution and the same cancellation of
$d-2-2\alpha$ as in (3.1), uniformly in the target $t$. If the
originating $j+1$ action retains its actual running coefficient, then
$\beta_{j+1}/\beta_n^{(t)}$
has running factor $g_{j+1}/g_t$; the same computation gives

$$\frac{\beta_{j+1}\varepsilon_{j+1}^2}
        {\beta_n^{(t)}\varepsilon_n^2}
=\frac{g_{j+1}}{g_t}
 \left(\frac{q_{j+1}}{q_n}\right)^2
 L^{-2\gamma(n-j-1)}
\le9e^{2\epsilon}L^{-2\gamma(n-j-1)}.\tag{3.3}$$

P631 defines its intermediate converted action with the P7 (2.10)
coefficients. Equations (3.2) and (3.3) cover respectively a converted
origin coefficient and the original running coefficient; (3.1) covers
two actual running coefficients.

The first inequality of P7 (2.11) is the further assertion

$$\boxed{|R_{j,n}(\psi)|\le K_{\rm rel}
\frac{\beta_{j+1}\varepsilon_{j+1}^2}
     {\beta_n^{(t)}\varepsilon_n^2}|X_j|_{j+1}}
\tag{OPEN-P631-RELATIVE-COST}$$

uniformly for $k_1\le j$, $j+2\le n\le k\le k_0$, every admissible
history and every datum in an open neighbourhood of P5 (1.32), where
$R_{j,n}=\beta_n^{(t)} C_{X_j}^{(n)}+\beta_{n,u}^{(t)}S_{X_j}^{(n)}$
is the actual P631 regional conversion at its P7 (2.10) intermediate
coefficient stream, with $t\ge n$ the fixed target scale. The numerator
is the coefficient of the original $j+1$ action. The
constant must be fixed from rows 0–11, before $B_0,H_0,c_1,c_2$.
To prove it term by term, it suffices to establish the same relative
factor for the regional cube sum and for the surface sum, plus the mixed
cube/wall-to-$|X_j|_{j+1}$ count. The P6 (2.25) bound, read with the
intermediate coefficient, is
$|C^{(n)}(\square)|\le3C_4B_6K_5/\beta_n^{(t)}$; it gives only an
$O(1)$ bound after multiplication by $\beta_n^{(t)}$. It contains no
$j$ and cannot
imply a factor tending to zero as $n-j\to\infty$: the constant family
$\beta_n^{(t)} C^{(n)}(\square)=1$ satisfies such an unscaled bound but
violates OPEN-P631-RELATIVE-COST. The landed
`norm_renC1Site_le`, `norm_renC2Site_le_renSol` and
`norm_renC1On_le`/`norm_renC2On_le_renSol` in
`Balaban/Fluctuation/RenormExpBounds.lean` are one-level, whole-lattice
pointwise bounds; they likewise do not retain the originating index $j$.
The reconstruction repeats P7 (2.11) as a cited input and contains no
proof of this relative estimate.

Once OPEN-P631-RELATIVE-COST holds, (3.3) gives the **uniform** second
inequality with the explicit constant $9e^{2\epsilon}K_{\rm rel}$ for
the P631 conversion from the original running action. If its origin
coefficient has already been converted, (3.2) gives $9K_{\rm rel}$.
This is the complete proof of the arithmetic
part of P7 (2.11). The remaining first inequality is a new
scale-indexed estimate for the regional conversion; it does not coincide
with OPEN-NC-MIXED or OPEN-NC3-MIXED-WALL. In the window range it does not
cross $k_0$, so Q13 does not supply or obstruct it. An extension through
$k_0$ on a mass-uniform full complex $h$ tube would invoke Q13 and cannot
be inferred from this window statement.

## 4. The P6 wall term after (2.25)

Let $F$ be one $(d-1)$-dimensional $M$-cube wall in the P6 decomposition
and $E_F$ the oriented crossing bonds assigned to it, each assigned once.
The P631 surface term over $F$ is
$S_F=\sum_{b\in E_F}\frac12(w_{b,+}+w_{b,-})\cdot\partial\phi(b)$.

**Finite wall lemma (proved).** If
$\|w_{b,+}\|_2,\|w_{b,-}\|_2\le V$ and
$\|\partial\phi(b)\|_2\le G$ on $E_F$, then

$$|S_F|\le |E_F|VG,\qquad
|\beta_uS_F|\le|\beta_u|\,|E_F|VG.\tag{4.1}$$

**Proof.** Complex bilinearity and Cauchy–Schwarz give
$|\frac12(w_++w_-)\cdot\partial\phi|
\le\frac12(\|w_+\|_2+\|w_-\|_2)
\|\partial\phi\|_2\le VG$ on each bond. Sum by the triangle
inequality. $\square$

The numerical form printed immediately after P6 (2.25), checked against
the PDF image on printed p. 11, is

$$|S_F|\le c_{\rm wall}\,
K_3K_4^{1/2}\varepsilon_n^2 B_6K_5
\beta_n^{-1}\varepsilon_n^{-2}
=c_{\rm wall}\beta_n^{-1}B_6K_3K_4^{1/2}K_5,\tag{4.2}$$

where its $O(1)$ is an unspecified wall-geometry constant
$c_{\rm wall}$, not a numerical value supplied by P6.
For a Lean theorem, (4.2) follows from (4.1) once the following **actual
regional** hypotheses are proved on the same open complex neighbourhood:

$$|E_F|V_nG_n\le
c_{\rm wall}\beta_n^{-1}B_6K_3K_4^{1/2}K_5,
\quad\sum_F|E_F|\le c_{\rm inc}
\big(|D\cap\Omega_n^c|_\eta+|D\cap\Omega_n|\big).\tag{4.3}$$

The first part is the precise product of the P2 Proposition 3.1 bound
for the **cut-source** solution $(w,t)$ of P6 (2.31), the complex
background derivative bound, the P4 (5.31) renormalization-parameter
bound, and the wall bond count. The second is the wall-to-mixed-cube
incidence estimate. These clauses are **OPEN-P631-WALL-LOCAL** for the
regional mixed-scale $D=Z_{n-1}^c\cap Z_n$: no landed declaration
states either one with that $D$ and its star. `IsRenSol.sup` proves
`SupBounds` for the standard whole-lattice renormalization source,
and `prop51_analytic` can solve a general source **after** its strict
small-data hypotheses are checked; neither checks the additional
$\chi_{\Omega_1}\Delta\chi_{\Omega_1^c\cap\Omega_n}Q_n^*v$
source or allocates bonds to these walls. The finite incidence proof
requires the exact half-bond convention and mixed $n-1/n$ cube units.
The constants $c_{\rm wall},c_{\rm inc}$ must be uniform in the window
indices and chosen from the geometry and rows 0–11 before
$B_0,H_0,c_1,c_2$.
If the renormalization radius gives $|b/\beta_n|\le1/16$, then
$|\beta_{n,u}/\beta_n|=|1+b/\beta_n|\le17/16$; multiplying (4.2)
by $\beta_{n,u}$ costs at most this fixed factor. Summing the assigned
walls and using the second part of (4.3) gives exactly the volume form
consumed by P631 (L), with
$K_{\partial}=(17/16)c_{\rm wall}c_{\rm inc}
B_6K_3K_4^{1/2}K_5$.

Thus (4.1) is proved, and (4.2) follows rigorously from the explicit
local obligations (4.3). The P6 printed assertion is evidence of the
intended result, not a landed proof of (4.3). This wall is the boundary
of the **action region**. OPEN-NC3-MIXED-WALL concerns pointwise Green
bounds at a **physical Dirichlet/operator cut** in a common-cover
parametrix; the two statements are different. OPEN-NC-MIXED may help
construct decoupled fields for (W), but it does not count $E_F$ or
establish the cut-source variation. Q13 is absent for $n\le k_0$.

## 5. Lean lemma order

1. `p631_epsTail_bounds`: from `epsTail`, prove $1\le q_j<3$;
   `p631_ratio`: combine `epsSeq`, `Flow.betaSeq_eq`, the bound on
   `gammaSeq`, and $d-2-2\alpha=2\gamma$ to prove (3.1).
2. `p631_region_reads` and `p631_wall_partition`: define the block/bond
   read sets and $E_F$ with half-bond weights; prove bounded reads,
   disjoint assignment and the second inequality of (4.3), with the
   actual mixed cube normalization.
3. `p631_cut_source_strict`: prove that the P6 (2.31) cut source and both
   field-free base data satisfy `StrictData` on an open neighbourhood;
   apply landed `prop51_analytic`, with `prop51_exists_unique` for
   uniqueness, to get regional $(w,t)$ and `SupBounds`. This requires
   the cutoff-source and coefficient estimates, not merely `IsRenSol`.
4. `p631_wall_pointwise` and `p631_wall_sum`: combine those bounds,
   complex background derivative bounds and P4 (5.31) to prove the
   first part of (4.3), then apply the finite lemma (4.1).
5. `p631_relative_cube`, `p631_relative_wall`, and
   `p631_relative_cost`: prove OPEN-P631-RELATIVE-COST with the
   originating index $j$ in every statement. This is the missing
   substantive scale estimate; use `p631_ratio` only **after** it.
6. `p631_window_common_cover`: instantiate the actual local/window
   generating sets, common partition, `CoverBase`/`CoverLocal`, and
   source-domain inclusions. The mixed-wall NC3 field and other
   VMOD-2 obligations must be discharged before invoking `i4b_close`.
7. `p631_window_far`: use `theorem73_complex`, the appropriate complex
   composition-domain lemma, `i4b_*` or a new cross-set comparison, and
   the proved local layer agreement of LF-RECONSTRUCTION II.2.5(c) to
   establish (2.2) on all reads. A same-$G$ subcase can use
   `lemma41_domain_uncond` directly.
8. `p631_window_margin` and `p631_window_action`: prove (2.3), apply
   the finite action estimate (2.1), absorb the polynomial factor as in
   (2.4), and obtain (W), analyticity and support for $j\ge1$.
   `p631_window_base`: if $k_1=0$, specify and prove the separate $j=0$
   decay/collar estimate required by OPEN-P631-W-BASE. Finally telescope
   as in P631 §3.

**Disposition.** Ratio arithmetic and the two finite inequalities are
proved here. W requires OPEN-P631-W-CROSS and OPEN-P631-W-MARGIN, plus
OPEN-P631-W-BASE when $k_1=0$;
the former needs a suitable mixed-cover instance and can encounter
OPEN-NC-MIXED/OPEN-NC3-MIXED-WALL. P7 (2.11)'s first inequality requires
OPEN-P631-RELATIVE-COST. The P6 wall estimate for the actual regional
solution requires OPEN-P631-WALL-LOCAL. None is a k₀-switch estimate in
the window range $k\le k_0$.
