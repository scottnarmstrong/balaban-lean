# The transverse source radius in route R-YM

**Verdict (case (c), with a counterexample).** The proposed uniform activity
bound on a full transverse $b$-polydisc of radius $c\beta_k^{-1/2}$ does not
follow from source-free sharp supports and the landed weight lemmas. It is
false for the *raw source-carrying mass weight* on that support, already on
one site. The largest uniform radius supplied by that weight is of order
$\sqrt{m_k/\beta_k}$, where $m_k$ is the coefficient of
$|\phi-h|^2/2$ in the same units as $\beta_k$. A different, optimized
one-block weight is bounded at radius $c\beta_k^{-1/2}$; the distinction is
essential. Hence the current R-YM class cannot be closed by assigning its
raw large-field weights the proposed bounded-activity norm. A class that
keeps the exact physical mass factor outside that norm, and bounds only
normalized fluctuation and $R$ activities, is the minimal viable design;
its physical production estimates remain open.

## Scope and exact source anchors

The input repository was read at commit
`e0704387636faf0a1e08304b2613fd211618a739` (17 October 2026).
This is a calculation about the radius, not an audit of all of P5--P7.
Page keys are those of `/home/scott/Balaban/review/SOURCES.md`.

* P5 pp. 489--490, (1.5)--(1.9): the physical main action retains
  $\nu_k|\phi-h|^2/2$, while its variational background omits that term for
  $\beta_k\nu_k\leq1$. P5 p. 492, (1.18)--(1.19), omits the two directional
  tests in that regime. P5 p. 497, (1.36)--(1.39), requires analytic
  large-field boundary coefficients bounded by
  $B_0e^{-\kappa d_k(X\operatorname{mod}\Omega_k^c)}$.
* P1 p. 117, (H.5), requires analytic small-field localization coefficients
  bounded by $E_0e^{-\kappa d_j(X)}$. Its real source condition (3.13),
  p. 123, and its complex source increments (3.14), p. 123, are distinct;
  the transverse Cauchy disc in (3.29)--(3.32), pp. 126--127, is wider than
  the physical real slice near small mass. P3 p. 74, (4.25)--(4.26), likewise
  specifies complex source increments. A $\beta_j^{-1/2}$ disc is a proposed
  changed class, not a radius stated in these passages.
* P6 p. 11, following (2.25), describes the extra field term below the
  switch and the two-stage change of background. P2 p. 610, (1.11), imposes
  mass alignment also on its boundary data; Proposition 1.1,
  (1.15)--(1.16), p. 611, uses that domain. P7 p. 497, Theorem 2, takes
  $R^{(k)}$ to be the identity for $k\geq k_0$.
* The exact landed facts used below are
  `A0PrimeSupport.lean:chiK_zero_mass_h_free` and
  `chiK_zero_mass_rot_fixed_h`,
  `A0PrimeWeight.lean:actionG_sub_massless`, `weight_real_bounds`,
  `differentiable_massTermC`, `norm_exp_neg_massTermC_le`,
  `analyticOn_blockGap`, `norm_exp_neg_blockGap_le`, and
  `blockGap_re_lt_of_imag`, and `A0PrimeReserve.lean:collar_reserve`.
  They are in `/home/scott/Balaban/Balaban/LargeField/Regime/`.
  The task context is Q13-YM.md §§3--6 and its W862 addendum, Q13-LATE.md,
  Q13-LATE2.md, Q13-DECISION.md, YMACCOUNT.md, and item 13 with addenda of
  QUESTIONS-ROLAND-2.md. The Yang--Mills reading in YMACCOUNT is an
  unrefereed account; no estimate below is imported from it.

Here $N\geq2$, $d\geq3$, $L\geq2$, and $a,A_0>0$ are fixed. Write
$\lambda_k=\log(a\beta_k)$ and
$\delta_k=A_0\lambda_k^{p_0}/\sqrt{a\beta_k}$. At scale $k$ in P5's
rescaled units the mass coefficient is $m_k=\nu_k$. The landed `actionG`
uses the corresponding fine-lattice coefficient
$\mu_k=\nu_kL^{-2k}$; one must rescale both the action and inverse
temperature before identifying its `μ` with $m_k$. The counterexample
below is at $k=0$, where they coincide.

## What a closing radius estimate would have to say

For every $k\leq k_0$, every permitted real massless support history,
every local small-field coefficient $\mathcal E^{(j)}(y,X)$ entering P5
(1.7)--(1.8), every large-field boundary coefficient
$\mathcal B^{(k)}(X)$ of P5 (1.38), and every new $R$ coefficient of
P5 (H.4), one needs a *single specified normalization* of the exact
physical action for which these coefficients are holomorphic in all
transverse source coordinates on
$$
 D_k(r_k)=\{b=b_k^0+q:\ |q_i|<r_k\ (i=2,\ldots,N)\},\qquad
 r_k=c_{d,L,N,p_0,A_0}\beta_k^{-1/2},                 \tag{1}
$$
with positive $c_{d,L,N,p_0,A_0}$ independent of $k$, the initial
$\beta$, the physical field strength, the volume, and the large-field
history. The required output norms are the $E_0e^{-\kappa d_j(X)}$
bound of P1 (H.5), the $B_0e^{-\kappa d_k(X\operatorname{mod}\Omega_k^c)}$
bound of P5 (1.39), and P5 (H.4)'s $\beta_k^{-n-1}$ bound for its
$R_n^{(k)}$, with the same constants after the step. For the part of the
large-field kernel to which P5 (1.30)--(1.31) assigns the Peierls gain,
the source cost of one failed test and its whole enlarged collar must
leave a positive fraction of
$$
 \beta_k\delta_k^2=\frac{A_0^2}{a}\lambda_k^{2p_0}.       \tag{2}
$$
One also needs a zero-free normalized integral wherever its logarithm
defines an activity. Holomorphy of an integrand alone proves neither
the logarithm's holomorphy nor the stated $E_0,B_0$ bounds. These are
the precise extra assertions that would keep the output in its form.

The phrase **raw weight** below means the source-dependent factor of
the physical main action *before* dividing by a source-dependent
reference density or extracting an exact source free energy. The
printed inductive class stores that main action separately from
$\mathcal E$ and $\mathcal B$; its coefficients need not bound the raw
factor. The stronger claim in Q13-YM §2 and §5 leaf 3 that the
source-carrying weight itself has an $O(1)$ per-block bound on (1) is
what the counterexample disproves.

## Exact counterexample to the proposed raw-weight bound

Use one site, $N=2$, a real unit field $\phi=e_1$, and physical centre
$h_0=e_1$, $b_0=m e_1$, with $0<m\leq1/\beta$. A constant configuration
in any unit direction passes the massless geometric tests: its block,
gradient, multiplier, and sphere defects vanish, and P5 (1.19) has no
direction test for $k\leq k_0$. The landed
`chiK_zero_mass_h_free` makes this support independent of the chosen
source. Set $b=b_0+q e_2$, $h=b/m$, and continue the square bilinearly,
as in `A0PrimeWeight.lean:massTermC_ofReal`. The raw factor is
$$
 W_m(q)=\exp\left[-\frac{\beta m}{2}
          \sum_{i=1}^2(\phi_i-h_i)^2\right]
       =\exp\left[-\frac{\beta q^2}{2m}\right].       \tag{3}
$$
This is entire. At the interior point
$q=i c/(2\sqrt\beta)$ of (1), however,
$$
 |W_m(q)|=\exp\left(\frac{c^2}{8m}\right).          \tag{4}
$$
Choose $m=\theta/\beta$, $0<\theta\leq1$, so the early-regime
condition $\beta m\leq1$ holds. Then
$\log|W_m(q)|=c^2\beta/(8\theta)$. For every fixed
$d,L,N,p_0,A_0,a,c>0$ and every fixed constant $C$,
$$
 \frac{c^2\beta}{8\theta}
   > C+\frac{A_0^2}{a}\bigl(\log(a\beta)\bigr)^{2p_0}
   > C
       \qquad\text{for all sufficiently large }\beta.       \tag{5}
$$
Thus neither an $e^C$ one-site activity bound nor the whole reserve
(2) pays (4). Increasing $p_0$ or $A_0$ after fixing them does not
alter this comparison: $\beta/(\log\beta)^{2p_0}\to\infty$.
The example uses a strictly interior point, so open versus closed
polydiscs do not matter. It uses no dimensional or collar geometry;
it embeds in every $d\geq3$, $L\geq2$, $N\geq2$.

There are two possible attempted escapes, neither gives the claimed
bound. Constraining $h\cdot h=1$ removes the point of (4), but this
constraint is not a transverse *polydisc* in $b$. At $b_0=me_1$ its
analytic parametrization has $b_1=\sqrt{m^2-q^2}$, with branch points
at $q=\pm m$; in the switching regime $m=O(\beta^{-1})$ this germ is
smaller than $c\beta^{-1/2}$. Extracting only the source scalar
$\exp[-\beta b\cdot b/(2m)]$ removes (4) but leaves
$\exp(\beta b\cdot\phi)$ (up to a source-independent factor).
The same h-free support permits $\phi=e_2$ and $q=c/(2\sqrt\beta)>0$,
giving $\exp(c\sqrt\beta/2)$; it also permits $\phi=-e_2$ for the
opposite real source. An exact main-action factor or a new norm is
needed, not a scalar subtraction alone.

This refutes a claim about the raw factor, **not** every conceivable
normalized polymer activity. A cancellation in the actual localized
fluctuation and $R$ integrals would have to be exhibited, with its
normalization and complex-domain bounds, before it could support (1).
Neither the source-free support theorem nor the collar reserve is such
an identity.

## Sharp true bounds and the radius direction

For a finite set $C$ of $n$ real fields $\phi_x$, a real source centre
$h_0$, and $b=m h_0+q$ with $m>0$, let
$$
 W_C(b)=\exp\left[-\frac{\beta m}{2}
       \sum_{x\in C}\sum_{i=1}^N
       \left(\phi_{x,i}-h_{0,i}-\frac{q_i}{m}\right)^2\right].
$$
Writing $q_i=u_i+iv_i$ and taking real parts gives, term by term,
$$
 \Re\left(\phi_{x,i}-h_{0,i}-\frac{q_i}{m}\right)^2
   =\left(\phi_{x,i}-h_{0,i}-\frac{u_i}{m}\right)^2
       -\frac{v_i^2}{m^2}\geq-\frac{v_i^2}{m^2}.
$$
Consequently the entire weight obeys the exact uniform inequality
$$
 |W_C(b)|\leq
 \exp\left[\frac{\beta n}{2m}\sum_i(\Im q_i)^2\right].       \tag{6}
$$
This is the landed `norm_exp_neg_massTermC_le` after $h=h_0+q/m$.
For an $s=N-1$ coordinate transverse polydisc, the choice
$$
 |q_i|<r_k^{\rm raw}:=\frac{c}{\sqrt{s}}
                   \sqrt{\frac{m_k}{\beta_k}}
       \quad (i=2,\ldots,N)                              \tag{7}
$$
gives $|W_C|\leq e^{c^2n/2}$. The factor $1/\sqrt{s}$ can be omitted
if the radius is defined by $\sum_i|q_i|^2<c^2m_k/\beta_k$ instead.
Equation (4) with $\phi=h_0$ proves that the order
$\sqrt{m_k/\beta_k}$ is sharp for this raw-weight norm. For real unit
$h$ and real unit $\phi_x$, the different landed bound is
$e^{-2E n}\leq W_C\leq1$ when $\beta_km_k\leq E$;
it says nothing about the large imaginary displacement $q/m_k$ in (1).

The thin radius has a usable *bare-weight* Peierls account. If a bad
seed's extended collar has at most
$J_k=(2\rho_k+1)^d$ charged sites, $\rho_k=2\lfloor
R_b\lambda_{k-1}^2\rfloor+3$, choose $c\leq1$. Equations (6)--(7)
cost at most $e^{J_k/2}$; `collar_reserve` gives
$J_k<\beta_k\delta_k^2$ under
$p_0>d$, $\lambda_{k-1}\geq1$, monotonicity of $\lambda_k$, and
$a(4R_b+7)^d<A_0^2\lambda_{k-1}^2$. Hence, explicitly,
$$
 e^{-\beta_k\delta_k^2}e^{J_k/2}
 \leq e^{-\beta_k\delta_k^2/2}.                    \tag{8}
$$
If an application charges more than one action site per counted collar
cube, its actual site-to-cube factor must multiply $J_k$ in (8), and
the numerical threshold must be strengthened accordingly. This is a
bound for the raw source factor and reserve, not a bound for the
localized $\mathcal E,\mathcal B,R$ activities or their logarithms.
P5 (1.30) allows $p_2=p_0-2d-2$ and requires $p_2\geq2d+2$,
so that particular source choice has $p_0\geq4d+4$ and subsumes
the $p_0>d$ arithmetic used here. The value of $R_b$ and any
site-to-cube multiplicity remain part of the actual LF construction.
Since $\beta_km_k\leq1$ on early levels,
$\sqrt{m_k/\beta_k}\geq m_k$; this thin $b$ tube still contains a
fixed-size local germ in $h=b/m_k$ (up to the displayed constants).
It can serve an analysis pinned at a real unit $h$, although it is
narrower than P1's mass-independent complex $b$ increments.

There *is* a $\beta^{-1/2}$ estimate for a different object. With
$a+m>0$, the optimized one-block gap
$$
 G(q)=(a+m)\sqrt{1+(q/(a+m))^2}-(a+m)
$$
is analytic for $|q|<a+m$, and the landed
`norm_exp_neg_blockGap_le` gives
$$
 |e^{-\beta G(q)}|\leq
       \exp\left(\frac{\beta|q|^2}{a+m}\right)
       \leq e^{c^2/(a+m)}
       \quad\text{if } |q|\leq c\beta^{-1/2}<a+m.       \tag{9}
$$
The constant $1/[2(a+m)]$ is false as a complex modulus bound, by
`blockGap_re_lt_of_imag`; $1/(a+m)$ is the landed safe constant.
Equation (9) bounds an *optimized difference*. It does not replace
the pre-integration factor (3), and there is no landed theorem that
converts every physical LF history into products of (9) with a
uniform normalization. This is the exact inference in Q13-YM §2
that fails.

The proposed radius $r_k=c\beta_k^{-1/2}$ **shrinks with $k$**.
Indeed `RunningHyp.beta_eq` gives
$\beta_k=\beta L^{(d-2)k}\gamma_k$ with
$e^{-\epsilon}\leq\gamma_k\leq e^\epsilon$ and
$\epsilon\leq1/20$. Therefore
$$
 \frac{r_{k+1}}{r_k}
 =L^{-(d-2)/2}\sqrt{\gamma_k/\gamma_{k+1}}
 \leq L^{-(d-2)/2}e^\epsilon<1
 \quad(d\geq3,L\geq2).                              \tag{10}
$$
The *thin raw-weight* radius (7) instead has scale factor
$L^{(4-d)/2}\sqrt{(\delta_{k+1}/\delta_k)
(\gamma_k/\gamma_{k+1})}$ when
$\nu_k=\nu L^{2k}\delta_k$; it need not be monotone under the
stated bounded-correction hypothesis. The radius in the $h$ variable
is $r_k^{\rm raw}/m_k=c/[\sqrt{s\beta_km_k}]$.

## Lean shape and status

No new Lean theorem is claimed. The precise immediate corollary of
the landed `norm_exp_neg_massTermC_le` has the following mathematical
type (notation simplified; `M` is the displayed expression, since the
landed file has no named `massTermC` definition):
```
M (m : ℝ) (C : Finset Site) (φ : Site → Fin N → ℝ)
  (h₀ : Fin N → ℝ) (q : Fin N → ℂ) : ℂ :=
  (m / 2 : ℂ) * ∑ x ∈ C, ∑ i,
    (((φ x i - h₀ i : ℝ) : ℂ) - q i / m)^2

rawWeight_transverse_bound
  (hm : 0 < m) (hβ : 0 < β) (C : Finset Site)
  (φ : Site → Fin N → ℝ) (h₀ : Fin N → ℝ) (q : Fin N → ℂ)
  (hq : ∑ i, ‖q i‖^2 ≤ c^2 * m / β) :
  ‖exp (-β * M m C φ h₀ q)‖
    ≤ Real.exp (c^2 * C.card / 2)
```
Its proof is substitution into that landed lemma and
$\sum_i(\Im q_i)^2\leq\sum_i|q_i|^2$; the one-site equality (4)
is a separate counterexample declaration. In the actual action, use
`actionG_sub_massless` and the correct scale conversion for `μ`.
`weight_real_bounds` gives the real-unit slice. For an optimized block,
`analyticOn_blockGap` and `norm_exp_neg_blockGap_le` give (9).
`collar_reserve` gives (8) after the explicit factor $1/2$.

A genuine output-class theorem would instead quantify over the actual
localized coefficients of P1 (H.5), P5 (H.4), (1.38)--(1.39), and the
actual $R$ window kernel, state the exact action/reference factorization,
prove zero-free normalized integrals on its chosen complex domain,
and preserve the old-term domain under source rescaling. None of
`A0Prime{Support,Weight,Reserve}` states those premises or conclusions.
Adding (1) as an axiom for `postTerm2`, `locOp`, or an abstract family
would hide the missing physical estimate rather than prove it.

## Consequences for the remaining R-YM leaves

* **Leaf 1 (three masses).** The action mass, background mass and cutoff
  mass must still be separated for A0'. This is an exact algebraic
  factorization task. The raw source factor must stay in the main-action
  part of that factorization; leaf 3's one-block estimate cannot be used
  as a blanket activity bound. The physical SF action and inherited
  SF terms should use complete backgrounds as in Q13-HYBRID.md, while
  early LF sharp tests and the auxiliary $R$ reference remain massless.
* **Leaf 4 (extended direction stencil).** The required read radius
  $\rho_k=2\lfloor R_{k-1}\rfloor+3$ and its changes to `FieldClose`,
  `chiK_stencil`, `chiY`, and P5 (1.22) remain necessary. Equation (8)
  pays the *thin-tube raw source cost* for one counted collar when its
  site count is justified. It does not prove that every background datum
  in the collar is tested, nor a bound for a complementary failed-test
  sector.
* **Leaf 5 (late `ChiDomProp`/`ChiDomAt`).** P2 (1.11) requires
  direction at collar data for the complete solver above $k_0$.
  Q13-LATE2.md's retained-shell partition and complementary sector
  remain open. A complex radius change cannot make a real unaligned
  retained datum satisfy that hypothesis. The support identity and
  large-field cost for newly excluded configurations must be proved
  before strengthening `locOp_vanish_chiDom` and `DomainIdentity`.
* **Leaf 6 (`LateParentR3`).** Its R3 arithmetic is conditional on
  `YDirectionAtParent` and `RetainedDirectionAtParent`, as written in
  Q13-LATE.md. Once leaf 4 and the supported clause of leaf 5 produce
  those inequalities on *all* `dataSites`, the algebra may proceed;
  the radius estimate contributes none of those real-domain premises.

The minimal analytic redesign is to preserve the h-free early sharp
partition but treat $\exp[-\beta A^{m,b}]$ as an **exact main-action
factor**, outside the bounded $E_0/B_0$ activity norms. Keep complete
backgrounds for SF coefficients; define normalized LF fluctuation and
$R$ activities by an explicit source-dependent reference density;
prove their holomorphy, zero-free normalization and bounds on the
chosen tube; and carry any transverse free energy not canceled by
that normalization as an explicit source sector with its own recursion.
For a quadratic coefficient $Q_k b_{k,\perp}^2$, the rescaling
$b_k=L^{-2}b_{k+1}$ and $L^d$ old blocks per new block give
$Q_{k+1}=L^{d-4}Q_k$ before its new birth contribution. The
homogeneous coefficient decays only in $d=3$, is marginal in $d=4$,
and grows for $d>4$; the source sector must track the birth term in
every dimension. This is bookkeeping, not a bound on that term.
If one insists on bounding the raw weight itself, (7), not (1), is
the necessary radius, and P1's wide-disc Cauchy argument for the
$W^2$ term must be replaced. Merely shrinking that disc does not prove
P1's irrelevance rate: a second transverse derivative costs
$O(\beta_k/m_k)$ for (3) and $O(\beta_k)$ even for the optimized
Gaussian term. Q13-HYBRID.md already identifies the physical
factorization and complete-action $R$ window estimate as open; this
radius calculation adds the exact norm restriction they must respect.

**Confidence.** High in (3)--(10), the scale direction, and the
non-implication from the landed lemmas. The alternative class is a
precise proof design, not a completed physical RG estimate. I have not
verified the full P5--P7 fluctuation kernels or a cancellation among
their localized terms; no such cancellation is claimed.

## Part II. Route R-YM′: exact class and production audit

This part answers the follow-up request. The proposed class is viable as a
*specification*, but the requested one-step production estimates cannot be
proved from the cited sources and landed facts. The obstruction is at the
actual physical kernels, not at the elementary source radius. Below are the
estimates that do follow, an exact conditional form of the remaining
production theorem, and the changes needed before it could be proved. In
particular, no P5 (1.30) or P7 (3.10) theorem is claimed for a kernel that
has not been constructed.

### 1. The class, including its normalization

Fix a **real** unit direction $h_*$ and put $b_k^*=m_kh_*$, with $m_k=\nu_k$
in P5's rescaled units. At one scale use two independent source domains:
the original P1/P3 small-field domain $\Xi_k$ for the small-field
coefficients, and the thin tube
$$
 T_k(c)=\left\{b=b_k^*+q:\quad
       \sum_{i=1}^N|q_i|^2<c^2\frac{m_k}{\beta_k}\right\}.
                                                        \tag{11}
$$
The transverse coordinate-polydisc inside it has radius
$c\sqrt{m_k/((N-1)\beta_k)}$; all estimates below use the Euclidean tube
to avoid an implicit factor $N-1$. A complex continuation of the
longitudinal coordinate, if used, obeys the same bound. The real unit
slice $b=m_kh$, $|h|=1$, is covered locally by such tubes; a global
complex $h$-polydisc is neither needed nor supplied. The final theorem
quantifies over real $h$.

The canonical main factor is **exactly**
$\exp[-\beta_k A_k^{m_k}(\psi,\phi;h)]$, with the positive real mass
$m_k\sum_x|\phi_x-h|^2/2$ and the original kinetic terms, restricted to
the component or region on which that factor is written. It receives
no $E_0$, $B_0$, or $R$ activity norm. Fixing this action and the
restriction is essential: multiplying it by an arbitrary $e^{F(b)}$ and
the activity by $e^{-F(b)}$ would make an unspecified “normalized
activity bound” meaningless. On a finite set $C$, its mass part has the
proved complex majorant (6), $e^{c^2|C|/2}$ on (11) **when the
integrated spin field is real**, and is at most one on the real unit
slice. For a complex background field, its imaginary part contributes
additional terms; a separate background-tube action bound is required.
A source-dependent reference denominator
is the integral of this *same restricted physical action* at the
specified reference configuration, with the same cutoff. Every
logarithm of such a denominator additionally requires a zero-free
theorem on its asserted tube.

The class assigns norms as follows. The small-field $\mathcal E^{(j)}$
and $R_n^{(j)}$ of P1 (H.5), P5 (H.4), and P3 (4.25)--(4.26) retain
their original **wide** $\Xi_j$ norms, respectively
$E_0e^{-\kappa d_j(X)}$ and the printed
$\beta_j^{-n-1}e^{-\kappa d_j(X)}$ bound (P5 p. 491, H.4,
where $E_0$ is replaced by $\beta_j^{-n-1}$). Their observable
$g$ domains and symmetry requirements remain those of the cited
hypotheses. Their main physical action
is extracted before these norms are taken. The large-field boundary
$\mathcal B^{(j)}$ of P5 (1.36)--(1.39) is holomorphic on
the **product** of (11) with P5's configuration spaces
(1.36)--(1.37) and $\|g\|_{\ell^1}<1$, after the same extraction,
with
$B_0e^{-\kappa d_j(X\bmod\Omega_j^c)}$.
The five kept outcomes and the removed outcome of the large-field
operator have the P5 (1.26) and P7 (3.10) weighted-kernel norms on
(11), including the same $\kappa_j-C_R\lambda_j^{2d+1}+\gamma_j(\varkappa)$
and $p_2(\beta_j)+H_j|Z|_\eta$ exponents. P5 (1.30) uses
$|Z|_\xi$ before the integration in (1.31), whereas P7 (3.10)
uses $|Z|_\eta$ after it. Here
$p_2(\beta)=A_2(\log\beta)^{p_2}$,
$H_j=H_0\log\beta_j$, $p_2\geq2d+2$, and the source-independent
decoration weights $C_{\rm dec}(\varkappa)$ retain
$\sum_{\varkappa=1}^5C_{\rm dec}(\varkappa)^{-1}\leq1$.
This is the *same-constant target*, not an established bound.
The sharp real cutoffs are fixed by the real center $h_*$ and do not
move in the complex continuation. Below the switch, their **test
background** is the massless solver and their directional tests are
omitted, so these early indicators are $h$-free. The **action
background** for SF and LF terms is the complete solver, with mass
$m_j$ at every scale. Thus R-YM′ needs two separately evaluated
backgrounds on a common datum; using the complete background inside
the early block/gradient tests would destroy the landed $h$-free
support property. Above the switch the cutoff uses the complete
solver and requires the late collar-alignment proof. A separate
source free-energy coefficient is
permitted only if explicitly recorded and recursively controlled; it
cannot be hidden in an activity with an unstated norm.

This two-domain class matters. Putting every coefficient on (11)
would not preserve the wide Cauchy estimates of P1 (3.29)--(3.32).
Conversely, putting the large-field raw factor on $\Xi_j$ contradicts
(3)--(5). At a small-field/large-field interface the exact physical
factor must agree before either norm is applied; its regional
factorization and the old $E/F/R$ localization remain separate proof
obligations (Q13-SHARED.md, A0′ account).

There is a clean scale-transport inequality for the *field* radius.
Write $m_k=\nu L^{2k}\eta_k$ and
$\beta_k=\beta L^{(d-2)k}\gamma_k$, where the running corrections
obey $e^{-\epsilon}\leq\eta_k,\gamma_k\leq e^\epsilon$ and
$\epsilon\leq1/20$. Then
$$
 \frac{\beta_{k+1}m_{k+1}}{\beta_km_k}
 =L^d\frac{\gamma_{k+1}\eta_{k+1}}{\gamma_k\eta_k}
 \geq L^de^{-4\epsilon}>1.                    \tag{12}
$$
Thus the radius in $h=b/m_k$,
$c/(\sqrt{\beta_km_k})$, strictly *shrinks*.
For $j\leq k$, a single complex physical $h$ in the $k$-tube
induces $q_j=m_j(h-h_*)$ and satisfies
$|q_j|^2\leq c^2m_j/\beta_j$ because
$\beta_jm_j\leq\beta_km_k$. This gives exact inherited-domain
compatibility. The $b$ radius itself is
$c\sqrt{m_k/\beta_k}$ and can grow in $d=3$, be nearly level in
$d=4$, or shrink in $d>4$, subject to the running corrections;
there is no uniform monotonicity assertion for it. The wider
$c\beta_k^{-1/2}$ radius still shrinks by (10), but is not the
raw-factor radius.

### 2. What the reserve proves, with its collar

Here is an actual failed-*direction*-test estimate. Let $\phi_x$
be a real vector and $h_*$ a real unit vector. Suppose the real test at one site
fails by $|\phi_x-h_*|\geq\delta_k/\sqrt{m_k}$; let
$h=h_*+q/m_k$ lie in (11). For any complex vector $z=u+iv$, its
bilinear square has real part $|u|^2-|v|^2$. By the triangle
inequality,
$$
 |\phi_x-h_*-\Re(q)/m_k|
 \geq\delta_k/\sqrt{m_k}
       -c/\sqrt{\beta_km_k}
 \geq\delta_k/(2\sqrt{m_k})
                                                        \tag{13}
$$
provided $c\leq\sqrt{\beta_k}\delta_k/2
=A_0\lambda_k^{p_0}/(2\sqrt a)$. Also
$|\Im(q)/m_k|^2\leq c^2/(\beta_km_k)$. Therefore
$$
 \Re\frac{m_k}{2}(\phi_x-h)\cdot(\phi_x-h)
 \geq\frac{\delta_k^2}{8}-\frac{c^2}{2\beta_k},
 \qquad
 1_{\rm fail}|e^{-\beta_km_k(\phi_x-h)^2/2}|
 \leq e^{-\beta_k\delta_k^2/8+c^2/2}.       \tag{14}
$$
All inequalities are pointwise and uniform in $N$ because (11) uses
the Euclidean norm. This spends only a factor $1/8$ of the original
reserve. The $e^{-\beta_k\delta_k^2}$ in (8) is a **hypothetical
available Peierls gain**, not a consequence of the landed
`collar_reserve` for a particular failed test; (14) is the direct
direction-failure gain. In P5 (1.19) the early direction tests are
omitted, so (14) cannot be charged to an early block or gradient
failure. For those tests the requisite Peierls source is the actual
mass-independent Gaussian/gradient defect and its background
response, which has not been proved here. The late retained-shell
direction test also needs P2 (1.11) on every datum read by its collar.

The exact collar arithmetic can nonetheless be stated. With
$\rho_k=2\lfloor R_b\lambda_{k-1}^2\rfloor+3$,
$$
 J_k=(2\rho_k+1)^d
 \leq(4R_b+7)^d\lambda_{k-1}^{2d}
 \leq(4R_b+7)^d\lambda_k^{2d},                 \tag{15}
$$
assuming $\lambda_{k-1}\geq1$ and monotonicity. Suppose a *proved*
failure estimate supplies (14), at most $C_{\rm site}J_k$ other
mass sites are charged to this seed, and all additional local
factors cost at most $e^{C_{\rm old}J_k}$, with
$C_{\rm site},C_{\rm old}\geq0$ fixed by the actual kernels.
The whole collar then costs at most
$$
 \exp\{-\beta_k\delta_k^2/8
       +(c^2C_{\rm site}/2+C_{\rm old})J_k\}.
                                                        \tag{16}
$$
It retains $e^{-\beta_k\delta_k^2/16}$ if
$$
 \lambda_{\min}^{2(p_0-d)}
 \geq {16a(4R_b+7)^d\over A_0^2}
       (c^2C_{\rm site}/2+C_{\rm old}).          \tag{17}
$$
Indeed (15) and $\beta_k\delta_k^2=A_0^2\lambda_k^{2p_0}/a$
make the positive term in (16) at most
$\beta_k\delta_k^2/16$. This explicitly tracks $d,p_0,A_0,a$;
$L,N$ occur only in the as-yet-unproved kernel constants and in
the scale threshold. The landed `collar_reserve` proves (15) versus
the *full* reserve under its hypotheses. It does not supply
$C_{\rm site}$, $C_{\rm old}$, (14) for every P5 failure type, or
the field-aligned collar support; thus (16)--(17) are conditional
production accounting, not a finished LF estimate.

The normalization itself can genuinely tame a fluctuation source.
For the elementary Gaussian $X\sim N(0,(\beta a)^{-1})$,
completing the square gives
$\mathbb E e^{\beta qX}=e^{\beta q^2/(2a)}$, hence
$|\mathbb E e^{\beta qX}|\leq e^{c^2/(2a)}$ for
$|q|\leq c/\sqrt\beta$. On a real cutoff
$|X|\leq R/\sqrt\beta$, its normalized moment generating
function $F$ satisfies
$|F(q)-1|\leq e^{cR}-1$, and is zero-free when
$cR<\log2$. These are direct proofs for this model, not estimates
for P5's constrained, interacting fluctuation and $R$ kernels.
In particular, a positive real denominator need not have a
volume-independent zero-free complex tube merely from positivity:
take $n$ perfectly aligned hard spins, with just the two allowed
configurations $\phi_x=+e_2$ and $\phi_x=-e_2$, equally weighted,
and $h_*=e_1$. Their exact mass-weight average is
$e^{-\beta nm-\beta nq^2/(2m)}\cosh(\beta nq)$.
After division by its nonzero value at $q=0$, the exponential factor
is zero-free but $\cosh(\beta nq)$ vanishes at
$q=i\pi/(2\beta n)$. If $m=\theta/\beta$, this lies in (11)
as soon as $n>\pi/(2c\sqrt\theta)$. This is a countermodel to
deducing a uniform zero-free radius from h-free support and real
positivity alone; it is **not** asserted to be P7's restricted
reference measure, whose pinning and localization may remove this
collective mode.

### 3. The P5--P7 production gap, stated at the same constants

P5 (1.30)--(1.31) is an inductive *assumption* about admissible
histories, with $p_2\geq2d+2$ and the possible choice
$p_2=p_0-2d-2$ (P5 p. 495). A complete one-step theorem for R-YM′
would assert, for every admissible history and every $b$ in (11),
both the SF $E_0/R_n$ and LF $B_0$ bounds above and, for each
retained or removed outcome, the P5 (1.26) bound with the same
$C_R,A_2,H_0,\kappa,\gamma,C_{\rm dec}$ and the support required for
the next history. The physical action and its restricted reference
integral must factor **exactly** before that assertion. The
source-free Yang--Mills analogy in YMACCOUNT.md is no proof of this
O($N$) statement. The indicated choice $p_2=p_0-2d-2$ together
with $p_2\geq2d+2$ requires $p_0\geq4d+4$. P5 states that $A_2$
depends on $p_0,A_0,L,M$ and other constants but gives no numerical
formula here; P7's window estimates contain unspecified $O(1)$
constants. Consequently a numerical $C_{\rm win}$ or an explicit
threshold solely in $d,L,N,p_0,A_0$ cannot be extracted from these
passages without the missing physical estimates.

The final P7 subtraction is also more than Peierls arithmetic.
P7 (2.58) supplies the printed action conversion used in its $R$
operator; P7 (3.3)--(3.5) defines the reference denominator.
P7 (3.7)--(3.10) multiplies a core estimate of the form (3.8) by a
window estimate of the form (3.9), cancels the matching denominator,
and spends one $p_2(\beta_k)$ to obtain the removed estimate (3.10).
For clarity, if the core is bounded by
$e^{-2P_2-H_k|Z|_\eta-Q_k}$, the **proved** window quotient by
$e^{Q_k+L_k+C_{\rm src}J_k}$, put $t_k=\log\beta_k$ and suppose
$t_k\geq\max\{1,|\log a|\}$, so $\lambda_k\leq2t_k$. If
$$
 L_k\leq C_{\rm win}t_k^{2d+2}+C_Et_k^{2d+1},\quad
 J_k\leq C_J\lambda_k^{2d}\leq2^{2d}C_Jt_k^{2d},\quad
 C_{\rm win}t_k^{2d+2}+C_Et_k^{2d+1}
       +2^{2d}C_{\rm src}C_Jt_k^{2d}
       \leq P_2=A_2t_k^{p_2},                     \tag{18}
$$
then multiplication proves *with exactly the same* $A_2,H_0$
$$
 |\mathcal T_{k,\rm rem}^{\rm norm}|
 \leq e^{-P_2-H_k|Z|_\eta}.                       \tag{19}
$$
P7 p. 520 bounds the *whole* window factor (3.9) by order
$t_k^{2d+2}$ and the later vacuum factor by order $t_k^{2d+1}$;
the two terms in $L_k$ reflect that distinction. If
$p_2=2d+2$, (18) requires actual leading-constant slack
$A_2>C_{\rm win}$, and follows for
$$
 t_k\geq\max\left\{1,|\log a|,
 \frac{2C_E}{A_2-C_{\rm win}},
 \sqrt{\frac{2^{2d+1}C_{\rm src}C_J}{A_2-C_{\rm win}}}\right\}.
$$
For $p_2>2d+2$, it follows once each of the three terms on the
left of (18) is at most $A_2t_k^{p_2}/3$. Thus the *printed*
$A_2$ is preserved only if it was chosen with enough slack at the
outset. The landed reserve lemma does not establish this slack.
This is the full algebra of the source-loss allowance. It is not a
proof of the two antecedent estimates or of the identity of the
quotient. P7 pp. 520--523 also removes cutoff dependence by an
$O(N)$ coset rotation before analytic extension; (18) by itself
does not make a sharp, moving cutoff analytic.

The exact missing inputs are currently visible in the landed Lean
interfaces. `LargeField/R/RRemovedWindow.lean:removed_exponent_le`
assumes the window fraction bound `hFr`, vacuum-energy bound `hEZ`,
core-to-prior exponent comparison `hκ`, and volume/constants bound
`hCR`; `window_lintegral_le_exp` additionally assumes the pointwise
window identity/bound `hid`, core integral `hcore`, and weighted
volume `hvol`. These theorems correctly prove the **consequence**
of P7 (3.7)--(3.9); they do not produce those hypotheses for a
physical complex source. `LargeField/Operators/StepData.lean:KeptData.bound`
is likewise a field of the input data for all five kept outcomes,
not a production theorem. `LargeField/R/RhoZeroPhysical.lean:
rhoZeroPhysicalWith` uses `massFunctional G` over all of $G.\Omega_1$;
P7 (3.3)--(3.5) requires a denominator restricted to its particular
component/window. If $G=Z\sqcup Y$ and the action splits with
$A_Y$ independent of the core variable, then
$D_G=e^{-\beta A_Y}D_Z$ and dividing the numerator by $D_G$
leaves $e^{+\beta A_Y}$. Thus the present definition cannot be
identified with P7's denominator by the source-weight bound alone.
The required restriction and action decomposition are exact
mathematical statements, not a choice of larger constants.

There is a second interface gap. `Operators/Setup.lean:OpConsts.mu`
currently supplies both the background and the early cutoff mass,
whereas `muAct` supplies the physical main action. R-YM′ requires
`muBg=muAct` below $k_0$ and `muCut=0` there, so one field cannot
serve both roles. `Operators/MainAction.lean:locBg` reads `cs.mu`,
while `mainActionLoc` uses `cs.muAct` but takes a real source and the
real part of the background. It does not define the required
holomorphic complex-source action. `Operators/KerBound.lean:KerBound`
also quantifies over a real source vector, so its present type cannot
state (19) uniformly on (11). These are concrete changes to the
objects, not a missing application of `norm_exp_neg_massTermC_le`.
The original P7 massless-reference stationarity identity (2.52)
cannot simply be copied with an A0′ complete LF background: the
reference field and its first variation change. A new exact
*modified* (2.58′) action identity is required; the prime denotes
the proposed R-YM′ version, not a numbered formula in P7.

Consequently the requested proof of production of the normalized
fluctuation activities, the five kept activities, and the removed
$R$ activity **from one step to the next with the printed constants**
is not available from the allowed facts. Assuming those activities
already obey the bounds would just assume the conclusion. Equations
(12)--(19) isolate the radius transport, one legitimate directional
Peierls gain, collar budget, and the conditional P7 exponent
collection; none hides the unproved physical window integral.

### 4. The kept mass factor in the final observable

At bare hard-spin level, for real unit $\phi,h$ the identity is
$$
 e^{-\beta\nu|\phi-h|^2/2}
 =e^{-\beta\nu}e^{\beta\nu h\cdot\phi}.
                                                        \tag{20}
$$
Let $z_{\beta\nu}=\int_{S^{N-1}}
e^{-\beta\nu|\phi-h|^2/2}\,d\sigma(\phi)$.
Rotation invariance makes $z_{\beta\nu}$ independent of real unit
$h$, and $d\mu_h=z_{\beta\nu}^{-1}
e^{-\beta\nu|\phi-h|^2/2}d\sigma$ is a probability measure.
For the *mass-square* partition function used by the frozen Lean
`Frozen/Model/Energy.lean:energy` on a finite torus $\Lambda$, this gives
the exact factorization
$$
 Z_\Lambda(h,g)=z_{\beta\nu}^{|\Lambda|}
 \int e^{-\beta H_{\nabla}(\phi)+\sum_xg_x\cdot\phi_x}
          \prod_{x\in\Lambda}d\mu_h(\phi_x).       \tag{21}
$$
The scalar $z^{|\Lambda|}$ cancels in $Z(h,g)/Z(h,0)$.
If one uses the equivalent linear-field convention
$e^{\beta\nu h\cdot\phi}$ instead, (20) contributes the additional
$e^{\beta\nu|\Lambda|}$, which also cancels in the ratio.
The $h$-dependent probability law **does not** cancel: discarding it
would discard the physical field. At the RG endpoint, if an actual
convergent, zero-free polymer expansion has been produced in the form
$\log Z(h,g)=V(h)+\sum_XP_X(h,g)$, the exact observable is
$$
 \log\frac{Z(h,g)}{Z(h,0)}
   =\sum_X\bigl(P_X(h,g)-P_X(h,0)\bigr),          \tag{22}
$$
with any vacuum term $V(h)$ canceled. Extraction of
$\sum_xg_x\cdot h$ and reorganization of the remainder into the
multiscale $T_j(x,X;g)$ are precisely P7 (4.15)--(4.17), with the
P9 (4.4)--(4.7) polymer term included. Formula (22) is an
identity *conditional on convergence and a normalized logarithm*; it does not prove the
analyticity, decay, or volume independence required by the frozen
`logPartition_multiscale`. Thus the mass factor is **absorbed in the
physical measure and canceled only in its source-only scalar and
vacuum normalization**, never erased from the nontrivial observable.

### 5. Lean statements and the status of Q13-YM §5

The following are statement shapes, not declarations proved in the
read-only repository. The first two can be proved from landed facts
and elementary inequalities; the remaining statements are the
actual production targets. The ellipses denote data and arguments
that must be fixed before Lean elaboration; no repository code was
changed here.

```
structure SourceTube (k : ℕ) (h0 : RealVec N) (b : ComplexVec N) : Prop where
  sq_le : ∑ i, ‖b i - (m k * h0 i : ℂ)‖ ^ 2 ≤ c ^ 2 * m k / beta k

theorem sourceTube_old_of_new (j k : ℕ) (hjk : j ≤ k)
    (hpos : 0 < beta j ∧ 0 < beta k ∧ 0 < m j ∧ 0 < m k)
    (hmono : beta j * m j ≤ beta k * m k)
    (hb : SourceTube k h0 (m k • h)) :
    SourceTube j h0 (m j • h)

theorem failed_direction_mass_cost
    (hfail : ‖phi - h0‖ ≥ delta k / Real.sqrt (m k))
    (hq : SourceTube k h0 b)
    (hc : c ≤ Real.sqrt (beta k) * delta k / 2) :
    ‖Complex.exp (-beta k * massAt phi (b / m k))‖ ≤
      Real.exp (-(beta k * delta k ^ 2) / 8 + c ^ 2 / 2)

structure SourceSplitStep where
  muBg : ℕ → ℝ
  muCut : ℕ → ℝ
  bgAct : Region → Config → ComplexVec N → ComplexField
  bgCut : Region → Config → RealVec N → RealField
  actionPhysicalC : Region → Config → ComplexVec N → ℂ
  referenceRestrictedC : Region → Config → ComplexVec N → ℂ

theorem physicalAction_holo (step : SourceSplitStep) (hin : ClassAt k) :
    ∀ region cfg, AdmissibleRegionCfg step region cfg →
      AnalyticOnNhd ℂ (step.actionPhysicalC region cfg)
        {b | SourceTube k h0 b}

theorem physicalRegionFactorization (step : SourceSplitStep)
    (hin : ClassAt k) : ExactOverlapActionIdentity step

theorem physicalReferenceRestriction (step : SourceSplitStep)
    (hin : ClassAt k) : P7Reference335Identity step

theorem physicalReference_nonzero (step : SourceSplitStep)
    (hin : ClassAt k) :
    ∀ region cfg b, AdmissibleRegionCfg step region cfg →
      SourceTube k h0 b →
      step.referenceRestrictedC region cfg b ≠ 0

theorem physicalActionIdentity258Prime (step : SourceSplitStep)
    (hin : ClassAt k) : ActionIdentity258Prime step

theorem physicalFluctuationBound (step : SourceSplitStep)
    (hin : ClassAt k) :
    WideSFCoefficientBound step.newE step.newRn ∧
    ThinLFBoundaryBound step.newB

theorem produceRemovedR (step : SourceSplitStep) (hin : ClassAt k) :
    ThinKerBound step.removed (p2 (beta k) + H k * weightedSizeEta Z)

theorem produceKeptR (step : SourceSplitStep) (hout : Fin 5)
    (hin : ClassAt k) :
    ThinKerBound (step.kept hout)
      (kappaPre k - CR * lambda k ^ (2*d+1) + gamma k hout)

theorem produceClassAtNext (step : SourceSplitStep) (hin : ClassAt k)
    (hfluct : WideSFCoefficientBound step.newE step.newRn ∧
      ThinLFBoundaryBound step.newB)
    (hremoved : ThinKerBound step.removed ...)
    (hkept : ∀ hout : Fin 5, ThinKerBound (step.kept hout) ...)
    (hsupport : ExactSupportAndLocalization step) : ClassAt (k+1)

theorem finalObservable_of_physicalExpansion
    (hexp : ConvergentPhysicalPolymerExpansion ...)
    (hvac : VacuumAtZeroIdentity ...) :
    FrozenRootFObservableIdentity ...
```

The production targets must be proved for the constructed
kernels without adding their own bounds as hypotheses. In particular,
`produceRemovedR` must internally establish the physical analogues of
P7's core and window bounds; `produceKeptR` must internally establish
all five outcome estimates. Stating those estimates as fields would
reproduce the current gap. `OpConsts` must split `mu` into background and cutoff
coefficients; all `Quiet*` and `ChiDomAt` uses must be routed to the
correct one. `locBg` uses the complete background; a new complex
regional action must accompany real `mainActionLoc`. The exact
restricted reference density must replace the current full-$G$
candidate for P7's $R$ denominator. `KerBound` and `KeptData.bound`
need source-tube versions, and the SF `Xi` domain must remain
separate from that tube. None of the frozen theorem statements needs
to change: its source $h$ is real and unit, and its complex variable
is the observable $g$.

For Q13-YM.md §5: **leaf 1** gains a precise complete-background,
source-independent-cutoff class, but still needs the exact regional
SF/LF factorization and inherited $E/F/R$ localization. **Leaf 4**
still needs the extended direction stencil in `FieldClose`,
`chiK_stencil`, and `chiY`, with read-collar support and cost;
(14)--(17) cover only one real directional failure and conditional
collar accounting. **Leaf 5** still needs the late retained-shell partition, direction
on the full P2 (1.11) collar, and a bound for the complementary
sector. **Leaf 6** is conditional on the real direction premises on
*all* data sites; (11)--(19) provide no such premises. The
unnumbered activity-radius and complete-action $R$ tasks in §5
require the restricted physical reference, the modified (2.58′),
the complex window/core estimates, and the five kept outcomes;
(18) handles only their final exponent arithmetic. The remaining
route is therefore a mathematically specified research program,
not a closed proof of the main theorem.

**Confidence for Part II.** High for (12)--(17), the conditional
implication (18)--(19), the bare partition identity (20)--(22), and
the type-level/normalization obstructions in the landed files.
Moderate for the proposed division of analytic domains, which is a
design choice awaiting the physical one-step estimates. No claim of
their production, or of a completed R-YM′, is made.
