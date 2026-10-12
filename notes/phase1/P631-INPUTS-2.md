# The analytic inputs of P631: source reconstruction and exact gaps

**12 October 2026.** This note uses the regional, complex bilinear action and
star term of P631 §1. The source is P6 pp. 10–12 (2.22)–(2.25), p. 14 (2.31),
P7 pp. 500–501 (2.10)–(2.15), and the cited reconstruction and Lean
declarations. The massless Euler–Lagrange convention applies for
$n-1\le k_0$, while the physical mass remains in the action.

Three analytic estimates requested by P631 remain unproved for the actual
window. This note proves the numerical and finite-action reductions, states
the exact additional estimates, and gives counterexamples to deriving them
from the weaker premises currently offered. These counterexamples do not
refute the specialized Balaban RG step. There is, however, a direct
counterexample to the constant-one ratio demanded by the landed
ActionConvInput (§2.1).

## 1. The window remainder (W)

### 1.1 The applicable proved response theorem

The PROVED lemma41_domain_uncond in
Balaban/Fluctuation/FarDecayUncond.lean, using the PROVED
weightedProp51S_exists in Balaban/Fluctuation/WeightedProp51.lean,
gives, for two small solutions on **one fixed generating set** $G$,
with the same $h$, source support $S$, its two complex InDomainC
premises, BgHyp, OpSetting, and the stated numerical smallness,

$$\|\delta\phi\|_{*,R}+\|\delta\alpha\|_{*,R}
 \le K_wc_F\delta_1 e^{-\gamma_wd_G(R,S)}. \tag{1.1}$$

The PROVED theorem73_complex of Balaban/Background/Theorem73.lean
gives the composition identity for a Precedes pair on its complex
domains. The PROVED real_step1_flow in
Balaban/Fluctuation/Theorem42RealFlow.lean obtains a supported data
change for the *one-step* local/boundary pair, under its domain
premises. The landed theorem42_of_input in
Balaban/Fluctuation/Theorem42.lean takes DecoupledCubeResponse as a
hypothesis; it proves the expansion from that response. None of
these statements instantiates (1.1) for the P7 local/window pair.
FLUCTUATION Theorem 4.2 and its Corollary 4.3 likewise retain the
decoupled common-cover and complex-domain hypotheses.

The precise missing **WINDOW-PAIR** theorem must provide, for every
$k_1\le j<k\le k_0$, each lineage component meeting
$X_j=Z_j^c\cap Z_{j+1}$, and every datum in an open neighbourhood of
P5 (1.32), a generating set $G_j$ and same-$h$ data $D_j,D'_j$ such that:

1. P7 (2.14) and theorem73_complex identify their backgrounds with
   the converted local and the $\mathbb B_{k_1,k}$ backgrounds on
   every block and bond read by the P631 regional action;
2. $\delta\Psi_j=D'_j-D_j$ is supported in $S_j$, has norm at most
   $C_{\rm data}r_j$, and the two data obey all premises of (1.1)
   uniformly on that open neighbourhood;
3. for $j\ge1$, the **operator** distance on every action read obeys
   $$d_{G_j}(R(X_j),S_j)\ge
     a_j:=2M[\hat R_j]-M-2M_1\ge0; \tag{1.2}$$
4. the response has the P6 (2.13) rate $\gamma_0/4=2\gamma_w$
   for this actual pair, or an equivalent extra collar distance.
5. **WINDOW-NORMALIZATION:** after transporting the P7 (2.10)
   coefficients and every fine-lattice site and bond read to
   scale-$(j+1)$ units, the sums of the absolute weights of the
   block and kinetic reads per mixed cube are at most
   $C_{\rm act}\beta_j$, and the corresponding physical-mass
   weights are at most $C_{\rm act}\beta_j\nu_j$, for one constant
   fixed before the final $\beta$ threshold. The coefficient
   comparisons
   $\beta_{j+1}^{(k)}/\beta_j=L^{d-2}g_k/g_j
   \le L^{d-2}e^{2\epsilon}$ and
   $\beta_{j+1}^{(k)}\nu_{j+1}^{(k)}/(\beta_j\nu_j)
   \le L^de^{4\epsilon}$ prove only the coefficient part.
   Fine-bond derivative scaling and the mixed cube count remain
   to be checked. This is needed because P631 and the landed
   WindowSetup.windowAction write the final action as
   $\beta_kA_k^*$, while the estimate (W) counts
   $|X_j|_{j+1}$.

The need for the first clause is concrete. LF-RECONSTRUCTION Lemma
II.2.5(c) proves layer agreement on $E_{Z'}$ between
$G^{Z'}_{j+1}$ and $\mathbb B^\partial_{j+1}$; it does not mention
$\mathbb B_{k_1,k}$, defined later in III.2.1. The sentence following
III.2.2 (2.15′) cites II.2.5(c) for agreement with the window set,
but that does not follow: $A\cap E=B\cap E$ gives no assertion about
$C\cap E$ (take $A=B=\varnothing$, $C=E$). This counters the cited
inference. The actual window layer agreement, block reads, nesting,
and complex-domain inclusions need their own proofs. If a
localization expansion is sought, the common cover and parameter
version of these statements must also instantiate DecoupledCubeResponse
for theorem42_of_input; the raw (W) only needs the undecoupled case.

### 1.2 Complete bound conditional on WINDOW-PAIR

Assume the action residual and derivative on every read are at most
$K_0r_j$, the mass first-variation coefficient satisfies
$\nu_j|\phi-h|\le K_mr_j$, $0\le\nu_j\le1$, and
$r_j\le C_H\alpha_0$. The mass estimate is valid only after the
fixed-$h$ H7-to-BG inclusion and the $j\le k_0$ bound
$\beta_j\nu_j\le e^{2\epsilon}$ are checked. The unrestricted
complex $h$ domain would make the mass cross term unbounded.
By WINDOW-PAIR, let
$T_j\le K_Rr_je^{-2\gamma_wa_j}$ bound the field and first
difference on the action reads.

Expanding each complex bilinear block, kinetic, and mass square gives
$2B(v,w)+B(w,w)$; the mass linear term is
$\nu_j(\phi-h)\cdot w$. With $c_{\rm read}$ reads per cube and
$c_{\rm count}$ cube-count conversion, the triangle inequality gives

$$|B_j|\le C_A\beta_jr_j^2e^{-2\gamma_wa_j}|X_j|_{j+1},
\quad C_A=C_{\rm act}c_{\rm read}c_{\rm count}
[K_R(2K_0+K_m)+\tfrac32K_R^2]. \tag{1.3}$$

The P6 (2.14) half-bond variation is among the kinetic reads; no
bulk stationarity is used to discard it. The quadratic factor is
bounded by $e^{-2\gamma_wa_j}$ when $a_j\ge0$.
For $D_j=M([\hat R_{j-1}]-1)-2M_1$ and nondecreasing radii,

$$2a_j-D_j
=4M[\hat R_j]-M[\hat R_{j-1}]-M-2M_1
\ge3M[\hat R_j]-M-2M_1. \tag{1.4}$$

Put $x_j=\log(\beta_0a)+1+j(d-2)\log L$ and
$\hat R_j=R_{\rm base}x_j^2$. Reconstruction (I.2) gives
$\beta_j\le a^{-1}e^{x_j-1+\epsilon}$ and
$[\hat R_j]\ge R_{\rm base}x_j^2-1$. Since
$\sup_{x\in\mathbb R}(x-Ax^2)=1/(4A)$ for $A>0$,
(1.3)–(1.4) prove (W), for $j\ge1$, with the explicit uniform
constant

$$K_{\rm bg}=C_AC_H^2\alpha_0^2a^{-1}
\exp\{\epsilon-1+\gamma_w(4M+2M_1)
          +(12\gamma_wMR_{\rm base})^{-1}\}. \tag{1.5}$$

Thus the scalar absorption and finite action estimate are **proved
conditional on WINDOW-PAIR and WINDOW-NORMALIZATION**. The weaker
same-$G$ bound (1.1) at
distance only $D_j$ gives
$C_A\beta_jr_j^2e^{-\gamma_wD_j}$; it cannot yield a uniform
$K_{\rm bg}e^{-\gamma_wD_j}$, because for
$r_j=\varepsilon_j$ the free flow has
$\beta_jr_j^2\asymp L^{2\gamma j}$. A one-cube
quadratic action with residual $r_j$ and displacement
$r_je^{-\gamma_wD_j}$ has a nonzero linear variation of precisely
this order. This is a counterexample to the **same-distance
inference**, and (1.4) displays the margin that repairs it.

LF-RECONSTRUCTION §I.1.2 also permits $k_1=0$, whereas P631 (7)
uses $\hat R_{j-1}$ at $j=k_1$. Its base convention expressly says
$R_{-1}$ is never used. Hence (W) as written has no value at $j=0$.
Lean's natural subtraction in ActionConvInput.window_decay sets
$j-1=0$ there, which silently changes the paper convention. The
base layer needs a separately stated estimate or a restriction
$k_1\ge1$.

## 2. P7 (2.11): the true ratio and the missing source gain

### 2.1 The ratio is proved; its landed constant-one version is false

Let $q_j=1+\sum_{m\ge j}m^{-2}$, with the $m=0$ term zero.
The landed epsTail and epsSeq in Balaban/SmallField/Xi.lean give
$\varepsilon_j=\alpha_0q_jL^{-\alpha j}$ and $1\le q_j<3$.
For the free-flow P7 coefficients
$\beta_m^{(t)}=\beta_tL^{-(t-m)(d-2)}$, $t\ge n$,
substitution and $d-2-2\alpha=2\gamma$ give

$$\frac{\beta_{j+1}^{(t)}\varepsilon_{j+1}^2}
        {\beta_n^{(t)}\varepsilon_n^2}
=\left(\frac{q_{j+1}}{q_n}\right)^2
 L^{-2\gamma(n-j-1)}
\le9L^{-2\gamma(n-j-1)}. \tag{2.1}$$

For original running $\beta_{j+1}$ and converted
$\beta_n^{(t)}$, the extra factor is $g_{j+1}/g_t$, at most
$e^{2\epsilon}$ by reconstruction (I.2), corresponding to landed
Flow.betaSeq_eq and Flow.norm_gammaSeq_le. This proves P7's
**printed** second inequality with constant $9e^{2\epsilon}$.

The landed ActionConvInput.p7_ratio in
Balaban/LargeField/R/ActionConvWindow.lean instead demands the
right side of (2.1) with constant $1$. Set all running corrections
to zero and choose $n=j+2$, for example $j=1,n=3$. Then
$q_{j+1}>q_n$, so the left side equals
$(q_{j+1}/q_n)^2L^{-2\gamma}>L^{-2\gamma}$. This is a direct
counterexample within the exact epsSeq and free-flow stream.
P7 (2.11) writes an unspecified constant on both sides. The Lean
field must allow a ratio constant, or incorporate it in Kconv; the
resulting $C_{15}$ is
$C_{\rm ratio}K_{\rm conv}/(1-L^{-2\gamma})+K_{\rm bg}$.

### 2.2 What P6 and P4 fail to prove

For the actual intermediate regional conversion, write
$R_{j,n}=\beta_nC_{X_j}^{(n)}+\beta_{n,u}S_{X_j}^{(n)}$.
The required first inequality is

$$|R_{j,n}|\le K_{\rm rel}\rho_{j,n}|X_j|_{j+1},
\qquad
\rho_{j,n}:=\frac{\beta_{j+1}\varepsilon_{j+1}^2}
                  {\beta_n\varepsilon_n^2},
\quad j+2\le n\le k. \tag{2.2}$$

P6 (2.25) gives a $\beta_n^{-1}$ cube bound and the printed wall
sentence gives a $\beta_n^{-1}$ wall bound. Their regional sum is
$O(|X_j|_{j+1})$ after multiplication by $\beta_n$.
The landed ActionConvInput.cost_le proves exactly that sum bound
from cube_bound and wall_bound; its p7_first is a **separate input**.
P4 (5.31) bounds the renormalization parameter by
$\eta_n=B_6K_5/(\beta_n\varepsilon_n^2)$, but has no originating
index $j$. A sufficient missing **RELATIVE-SOURCE** estimate would
bound the transported data/coefficient increment on each cube and
wall by $C\eta_n\rho_{j,n}$ in the P4 (4.10) source norm, including
the P6 (2.31) cut source. Then a regional P2 response estimate
and quadratic action expansion of size
$C\beta_n\varepsilon_n^2\eta_n\rho_{j,n}$
would give (2.2). The factor $\rho_{j,n}$ is the exact missing
lineage-dependent gain; a variant may prove (2.2) directly.

For clarity, the weaker premises do not imply that gain. Take a
nonconstant small stationary hard-spin field with
$|\partial\phi|=c\varepsilon_n+O(\varepsilon_n^2)$ on one whole
action region, $c\ne0$. Set $v=e=\nu=0$ and
$b_n/\beta_n=\xi_n=c_0/(\beta_n\varepsilon_n^2)$, adjusting
$a_u$ so $\beta_{n,u}a_u=\beta_na$. The change is within the P4
(5.31) order. Differentiating the stationary **whole-region**
action at $\xi_n=0$ (or expanding and using its EL equation) yields

$$\frac{d}{d\xi_n}
 [\beta_{n,u}A_u-\beta_nA]_{\xi_n=0}
=\tfrac12\beta_n|\partial\phi|^2
=\tfrac12c^2\beta_n\varepsilon_n^2
  +O(\beta_n\varepsilon_n^3). \tag{2.3}$$

Thus the cost for this perturbation tends to $c_0c^2/2\ne0$ as
$\beta_n\varepsilon_n^2\to\infty$, while the P6 $O(1)$ cube bound
holds and $\rho_{j,n}\to0$ for fixed $j$, $n-j\to\infty$.
The finite stationary solution is analytic in $\xi_n$; its second-order
remainder after this substitution is
$O((\beta_n\varepsilon_n^2)^{-1})$, while the error displayed in
(2.3) contributes $O(\varepsilon_n)$.
This counters the inference from P2 smallness, P4 (5.31) and P6
(2.25) to (2.2), not a possible additional constraint of the
actual window lineage.

## 3. The wall after P6 (2.25)

Let $F$ be a P6 $M$-cube wall, $E_F$ its oriented crossing bonds
assigned once, and $S_F$ the P631 (2) term there. Complex
Cauchy–Schwarz, applied bond by bond, proves

$$|S_F|\le |E_F|
\sup_{b\in E_F}\frac{|w_{b,+}|+|w_{b,-}|}{2}
\sup_{b\in E_F}|\partial\phi(b)|. \tag{3.1}$$

With $\eta_n=B_6K_5/(\beta_n\varepsilon_n^2)$, the exact local
estimates sufficient for P6's printed wall value are

$$|E_F|\le c_E,\qquad
\frac{|w_{b,+}|+|w_{b,-}|}{2}
 \le K_3\varepsilon_n\eta_n,\qquad
|\partial\phi(b)|\le K_4^{1/2}\varepsilon_n
\quad(b\in E_F). \tag{3.2}$$

Substitution proves

$$|S_F|\le c_EK_3K_4^{1/2}B_6K_5\,\beta_n^{-1}. \tag{3.3}$$

This is precisely the product
$O(1)K_3K_4^{1/2}\varepsilon_n^2
B_6K_5\beta_n^{-1}\varepsilon_n^{-2}$
printed after P6 (2.25). If $|b/\beta_n|\le1/16$, then
$|\beta_{n,u}/\beta_n|\le17/16$. Charging at most
$c_{\rm inc}$ walls per mixed cube gives the P631 (L) constant
$(17/16)c_Ec_{\rm inc}K_3K_4^{1/2}B_6K_5$.
Equations (3.1)–(3.3) are a **complete finite proof conditional on
(3.2)**, including the half-bond and $\beta_{n,u}$ factors.

The middle estimate of (3.2) is the missing **WALL-CUT** theorem
for the actual P6 (2.31) regional variational solution. For
$n-1\le k_0$ its equation has, besides the P4 coefficient-change
source, the extra term

$$f_{\rm cut}=
\chi_{\Omega_1(G)}\Delta
\chi_{\Omega_1(G)^c\cap\Omega_n}Q_n^*v. \tag{3.4}$$

The nearest-neighbour stencil gives
$\|f_{\rm cut}\|_\infty\le2d\|Q_n^*v\|_\infty$ in unit
lattice normalization (with the appropriate $\ell^{-2}$ in fine
units). This alone is not $O(\varepsilon_n\eta_n)$.
To use P2 Proposition 3.1 (3.47), or the PROVED
prop51_exists_unique and prop51_analytic, one must verify their
strict small-source and complex-domain hypotheses for the **full**
source including (3.4), and derive the middle bound in (3.2).
The last bound in (3.2) requires the P5 (1.32) domain inclusion on
all wall reads; the first and $c_{\rm inc}$ require the mixed
$n-1/n$ wall assignment. The landed IsRenSol.sup and renormC*
declarations concern the whole-lattice source, without (3.4).

Here is a finite hard-spin counterexample to getting a
$\beta^{-1}$ wall bound from existence and smallness alone.
In a two-site local block/bond chart take
$\phi_i=(\cos\theta_i,\sin\theta_i)$,
$\psi_1=(\cos u,\sin u)$, $\psi_2=(1,0)$, and

$$A(\psi,\phi)=\frac a2\sum_{i=1}^2|\psi_i-\phi_i|^2
 +\frac12|\phi_2-\phi_1|^2,\qquad a>0. \tag{3.5}$$

The positive tangent Hessian is
$\left(\begin{smallmatrix}a+1&-1\\-1&a+1\end{smallmatrix}\right)$.
Its inverse gives, for small $u$,
$\theta_1=(a+1)u/(a+2)+O(u^2)$ and
$\theta_2=u/(a+2)+O(u^2)$.
Perturb the first datum angle by fixed small $t$ while taking
$b=e=\nu=0$ and the same $a$. Then
$w_1=(a+1)t/(a+2)e_2+O((|u|+|t|)|t|)$ and
$w_2=t/(a+2)e_2+O((|u|+|t|)|t|)$.
For the region containing site 1, its crossing-bond term is

$$S_D=\frac{w_1+w_2}{2}\cdot(\phi_2-\phi_1)
=-\frac{a}{2(a+2)}ut
  +O(u^2|t|+|u|t^2). \tag{3.6}$$

Choose fixed small nonzero $u,t$ so $S_D\ne0$. The solution is
small and independent of $\beta$, but (3.3) tends to zero as
$\beta\to\infty$. This counters the inference from P631 §1's
coefficient identities and P2 small-solution existence; the data
increment here is not the required RG-size increment. The same
local block/bond mechanism is present in the P631 action. The
source-size assertion of WALL-CUT is what excludes this example.

WINDOW-NORMALIZATION is independent of OPEN-NC-MIXED: it compares
the fine-lattice regional action with the scale-$(j+1)$ mixed count.
The bare WindowSetup in ActionConvWindow.lean does not require that
comparison; its $\beta_k$ kinetic coefficient can grow relative
to $\beta_j$ as $k-j$ increases. WALL-CUT is distinct from
OPEN-NC3-MIXED-WALL, which concerns
Green kernels at a physical operator cut. WINDOW-PAIR can require
the *type* of common-cover estimate called OPEN-NC-MIXED in VMOD,
and a physical window wall can require OPEN-NC3-MIXED-WALL, but
those items do not prove the local/window layer agreement or (1.2).
RELATIVE-SOURCE is independent of both. All requested window
indices satisfy $n\le k\le k_0$, so none of these is the
$k_0$ switch Q13.

## 4. Lean dependency order

The names after semicolons are proposed; the preceding names are
landed declarations, checked in the stated files.

1. epsTail, epsSeq in Balaban/SmallField/Xi.lean and
   Flow.betaSeq_eq, Flow.norm_gammaSeq_le in
   Balaban/Flow/RunningCoefficients.lean;
   p631_ratio_free, p631_ratio_mixed,
   p631_ratio_one_counterexample. Repair ActionConvInput.p7_ratio.
2. Region.actionRegion_conversion in
   Balaban/LargeField/R/ActionConvIdentity.lean and
   StepDecomp.starPair_sum, StepDecomp.sum_le in
   ActionConvWindow.lean; p631_wall_partition,
   p631_action_reads, p631_regional_identity.
3. prop51_exists_unique and prop51_analytic in
   Balaban/Background/Contraction*.lean;
   p631_cut_source_strict, p631_regional_response,
   p631_wall_pointwise, p631_wall_bound.
4. theorem73_complex, real_step1_flow, and
   LF-RECONSTRUCTION II.2.5(c); p631_window_layers,
   p631_window_precedes, p631_window_complex_domain,
   p631_window_data_support, p631_window_normalization.
   The first two must compare the *window* set; the last
   must account for every fine bond and mixed cube weight.
5. weightedProp51S_exists and lemma41_domain_uncond in
   Balaban/Fluctuation/WeightedProp51.lean and
   FarDecayUncond.lean; p631_window_response and
   p631_window_margin. A decoupled expansion additionally
   instantiates DecoupledCubeResponse for theorem42_of_input
   in Balaban/Fluctuation/Theorem42.lean.
6. p631_window_action from (1.3)–(1.5), plus
   p631_window_base for $k_1=0$ under an explicit base convention.
7. p631_relative_source_gain, p631_relative_cube,
   p631_relative_wall, then p631_relative_cost with the
   originating $j$ retained; only then invoke
   ActionConvInput.cost_le and window_conversion in
   Balaban/LargeField/R/ActionConvWindow.lean.

**Status.** The corrected ratio and the finite reductions are
proved. The constant-one landed ratio is false. The actual (W),
the first P7 (2.11) inequality, and the P6 wall estimate still
require WINDOW-PAIR plus WINDOW-NORMALIZATION, RELATIVE-SOURCE,
and WALL-CUT respectively;
the displayed examples show why the weaker premises do not suffice.
