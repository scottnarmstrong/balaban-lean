# A support and size repair for hat-field labels

**Scope and status (12 October 2026).** This note answers the follow-up in
`followup_lb.txt`. All geometric and finite-sum assertions below are proved in
ordinary mathematics for a finite whole-lattice torus. They are not landed Lean
theorems. The abstract Mayer and marked-Mayer conclusions are **PROVED
CONDITIONAL ON** the displayed geometric and activity hypotheses, by the
existing Lean theorems. Applying them to the physical RG step is **OPEN** at the
named class, analytic, and localization bridges in §§5–6. No claim that the
present Def-6 class is preserved is made. In particular, the no-closure result
of `RATES.md` remains correct for the *present* multiplicative conversion.

## 1. Where the extra hat support enters

The mathematical locality statement in P1 §§2–3, P3 §4, and P5 §3 uses the
generating-set decoupling: with the cut parameters outside a connected
component set to zero, the decoupled covariance and its square root act
block-diagonally across those components. That statement concerns the
fluctuation variables of the chosen component. It does not by itself assert
that a term expressed in the *landed unit-point hat coordinates* uses only
variables of the original cover core.

The exact landed chain is as follows.

* `Localization/I5FluctLocal.lean` defines `psiThick Y` as `Y` plus nearest
  neighbours. Its `fan_local_fl` needs the fluctuation field there because
  the action/Laplacian and response data read a nearest-neighbour collar.
* `Fluctuation/StepObjects.lean` `liftU` copies a unit-point hat variable over
  its `(k+1)` unit block. `Localization/DecoupledCovLocal2Free.lean`,
  `I4c_local_sqrt3`, compares square-root outputs under agreement of inputs
  on the same unit block. The locality proofs use `unitP_ne_zero_imp` and
  `unitQ_ne_zero_imp`: the block projection and average mix points inside
  that unit block. The decoupled operator suppresses communication *between*
  disconnected components; it does not remove this within-block mixing.
* `Fluctuation/HatEngineLocal.lean` defines `blockThick Y` to be all sites in
  unit blocks meeting `psiThick Y`. Its `hatPsiF_local` asks the hat variables
  to agree at unit points of `blockThick Y` to conclude equality of
  `liftC (cc • C^{1/2}(s) ψ̂)` on `psiThick Y`.
* `Fluctuation/HatEngineLocalFan.lean` `AgHat` retains raw-data agreement on
  `thickSet Y` and hat agreement on `blockThick Y`.
  `Fluctuation/InteractionHatV.lean` `AgHatF` retains the latter. The label
  conversion occurs in `Fluctuation/HatLabelsDep.lean`,
  `StepSetting.agHatF_hatOf`: agreement of block configurations on every
  $a$-cell of `psiThick Y` implies `AgHatF`. `HatLabelsGeom.thick_spec`
  then encloses those cells in new cover cubes; `HatLabelsExpansion.lean`
  `labelAct_of_hatExpansion` spends its multiplicative covering bound.

Thus `blockThick Y` is required by the **currently proved locality chain**.
The full cover enlargement is a convenient overestimate, and a stronger
component-sensitive hat locality may exist. Neither the source-paper
block-diagonal observation nor a landed theorem proves such a sharper
statement for these coordinates. An additive estimate for the canonical
thickening is also unsupported: a long thin core may have a collar along
its whole length. We choose the separate-size-and-support repair below.

## 2. The abstract geometric replacement

Work first with $Omega$ equal to the whole finite torus. Let $B$ be its
finite lattice of aligned $a$-cells, $a=L^{j+m_0+m_1}$, and let
$\mathcal D_j$ be the nonempty connected unions of aligned cover cubes of
side $La$. For $W\in\mathcal D_j$, write $d(W)=d_j^{\rm cov}(W)$ and
$n(W)$ for its number of $a$-cells. The landed `G1_cellCount` gives

$$n(W)\le c_1(1+d(W)),\qquad c_1=[3(2L-1)]^d.\tag{2.1}$$

For a set of cells $W$, let $N_R(W)$ be the union of all cells at periodic
Chebyshev cell distance at most $R$ from a cell of $W$. Set

$$R=2,\qquad h=(2R+1)^d=5^d,\qquad C=hc_1,\qquad
J=4d(L+R+2).\tag{2.2}$$

The actual `blockThick Y` is contained in the sites of $N_R(Y)$: first add
one lattice-site neighbour, then fill its unit block; a unit block is
contained in one $a$-cell since $L^{j+1}\mid a$ for $j=k+1$ and $m_0+m_1\ge0$.
A boundary crossing may add one adjacent $a$-cell. Radius two gives a spare
cell for the scale map. This is a direct coordinate observation; the exact
Lean containment for all torus/divisibility hypotheses is **OPEN**.

For every nonempty finite support $S\subset B$ define

$$D_R(S)=\min\{d(W): W\in\mathcal D_j,\ S\subset N_R(W)\},
\qquad D_R(\varnothing)=0.\tag{2.3}$$

The minimum exists: the finite torus itself is a witness. It is invariant
under translations and lattice symmetries, is finite and nonnegative, and

$$D_R(N_R(Y))\le d(Y).\tag{2.4}$$

It measures the *smallest core that can carry the dependence support*;
it is not the covering length of that support. No arbitrary minimizer is
used in the definition or in the final covariant reindexing.

**Lemma 2.1 (all-support geometry; PROVED here).** For nonempty $S,T\subset B$:

$$|S|\le C(1+D_R(S));\tag{G1-R}$$
$$S\cap T\ne\varnothing\quad\Longrightarrow\quad
D_R(S\cup T)\le D_R(S)+D_R(T)+J.\tag{G3-R}$$

*Proof.* Choose a minimizing core $W$ in (2.3). Each of its cells contributes
at most $h$ cells to $N_R(W)$. Thus $|S|\le h n(W)$ and (2.1) proves G1-R.
For G3-R choose minimizing cores $W_S,W_T$ and $b\in S\cap T$. Pick cells
$u\in W_S$, $v\in W_T$ at Chebyshev distance at most $R$ from $b$.
Their $ell^1$ cell distance is at most $2Rd$. Join them by a shortest
cell path. Take optimal connected $La$-cube covering trees for $W_S,W_T$.
The cover cube containing $u$ (respectively $v$) can be joined to its
tree by at most $dL$ normalized bonds inside that cube; adjoining the
cover cubes met by the cell path costs at most $2Rd+2dL$ further bonds.
The union is a connected admissible cover core $W'$ containing both cores;
its cover cost is at most $d(W_S)+d(W_T)+2Rd+4dL\le
d(W_S)+d(W_T)+J$. As $S\cup T\subset N_R(W')$, (2.3) proves the claim.
The bound $J$ is deliberately larger than the path estimate, so choices
of endpoint convention do not affect it. $\square$

Iterating G3-R along a spanning tree of the graph of intersecting supports
gives, for any connected family $S_1,\ldots,S_n$,

$$D_R\Big(\bigcup_i S_i\Big)\le\sum_iD_R(S_i)+J(n-1).\tag{2.5}$$

This is exactly the form of `hG3T` and `hG3P` in
`Polymer/MayerMarked.lean` with $c=c_P=J$.

**Lemma 2.2 (two entropy bounds; PROVED here).** Let the landed core
counting estimate `G2_X` be written

$$\sup_b\sum_{W\in\mathcal D_j:\,b\in W}e^{-t d(W)}
\le K_0(d,L,t)\quad(t\ge a_{\rm ent}(d,L)+1).\tag{2.6}$$

If $\kappa_0-C\log2\ge a_{\rm ent}+1$, then

$$\sup_b\sum_{Y\in\mathcal D_j:\,b\in N_R(Y)}e^{-\kappa_0d(Y)}
\le K_T:=hK_0(d,L,\kappa_0),\tag{G2-T}$$
$$\sup_b\sum_{\varnothing\ne S\subset B:\,b\in S}e^{-\kappa_0D_R(S)}
\le K_P:=h2^C K_0(d,L,\kappa_0-C\log2).\tag{G2-P}$$

*Proof.* If $b\in N_R(Y)$, $Y$ contains one of the at most $h$ cells
within distance $R$ of $b$; sum (2.6) over these cells. For G2-P, assign
to each $S$ one minimizing core $W$ only for the purpose of an upper bound.
Then $b\in N_R(W)$, and for fixed $W$ there are at most
$2^{|N_R(W)|}\le2^{C(1+d(W))}$ possible $S\subset N_R(W)$. Hence the
left side is bounded by
$2^C\sum_{W:b\in N_R(W)}e^{-(\kappa_0-C\log2)d(W)}$.
Apply the first argument at the lower rate. No tie-breaking is needed in
the mathematical inequality. $\square$

For boundary polymers $\Omega\ne\mathbb T$, the analogous $D_{R,\Omega}$
must use the finite all-support modular size and an interface-compatible
halo. The needed G1/G2/G3 and component containment are **OPEN-MOD-HALO**;
whole-lattice Lemmas 2.1–2.2 do not supply them.

## 3. Labels, pre-summation, and the landed cluster theorem

Give each original expansion label $Y$ two independent data:

$$\operatorname{core}(Y)=Y,\quad d_Y=d(Y),\quad
\operatorname{supp}(Y)=N_R(Y).\tag{3.1}$$

The physical complex activity premise is
$|A_Y(\Phi)|\le\varepsilon_Ue^{-\kappa_H d_Y}$, with
$\kappa_H=2\kappa_{\rm dec}-1$ from
`interaction_expansion_hat_bound`, and `DepOn(supp(Y),A_Y)`.
Here $\varepsilon_U$ denotes the effective label amplitude, including
the interpolation-disc factor $R_\sigma$ which
`HatLabelsExpansion.lean` includes in its current `hatEpsH`; if the
Proposition 3.3 bound is denoted $\varepsilon_U^{\rm raw}$, require
$\varepsilon_U\ge R_\sigma\varepsilon_U^{\rm raw}$.
That bound and dependence are **OPEN-PHYSICAL-LABEL-ACTIVITY** until the
actual complex class and hat locality are joined to the landed theorem.
For a nonempty support $S$ pre-sum
$\widetilde A_S=\sum_{Y:\,\operatorname{supp}(Y)=S}A_Y$.
If $\kappa_H\ge\kappa_0$, (2.4), G2-T, and a choice of $b\in S$ give

$$|\widetilde A_S|\le\varepsilon_U K_T
e^{-(\kappa_H-\kappa_0)D_R(S)}.\tag{3.2}$$

Indeed split $e^{-\kappa_Hd_Y}$ into
$e^{-(\kappa_H-\kappa_0)d_Y}e^{-\kappa_0d_Y}$;
replace the first factor using $D_R(S)\le d_Y$ and sum the second over
labels whose support contains $b$. This proof also applies uniformly on a
complex parameter polydisc and to marked activities if their common
polydisc bound holds. Pre-summing preserves locality, measurability and
analyticity because the label set is finite.

Take $K_c\ge\max\{1,K_T,K_P\}$ and put
$\varepsilon_H=\varepsilon_UK_c$, $H_0=2\varepsilon_HK_c$,
$\kappa_1=\kappa_H-2\kappa_0$. Then (3.2) implies the `hH` premise of
`Polymer/MayerMarked.lean:mayer_marked` at
$\kappa_0+\kappa_1=\kappa_H-\kappa_0$.
The exact remaining rates are

$$\kappa_H\ge\kappa'+3\kappa_0+C+\tfrac32,
\qquad\kappa_1\ge0,\qquad\kappa'\ge0.\tag{3.3}$$

Use G1-R with $c_1=C$, G2-P with $K_0=K_{0P}=K_c$ and
$\kappa_{0P}=\kappa_0$, and (2.5) with $c=c_P=J$. The existing
`numerics_PE` certifies `hq`, `hα`, and $H_0\le\log2$ if

$$0<\varepsilon_U\le
\frac{1}{8K_c^4C\exp((\kappa_H-2\kappa_0)J+C+\kappa'J)}.
\tag{3.4}$$

For the two-mark observable reserve another factor four on the right
of (3.4), as in the existing marked application. There is no lost factor
$A^{-1}$ in the exponent. The landed `mayer_pe` gives a weighted sum
of nonnegative norms of connected coefficients at rate $\kappa'$ measured
by $D_R(S)$; each coefficient obeys the same bound by dropping the other
summands. For marks, use the weighted derivative sums behind
`mayer_marked` and the landed `Marked.sum_norm_D1_Ff_le` and
`Marked.sum_norm_D2_Ff_le`. Their individual coefficients satisfy the
corresponding bound for the same reason. This is **PROVED CONDITIONAL ON**
the complex activity and geometry hypotheses.

This use checks the actual landed hypothesis order. In `mayer_marked`,
`sup : T → Finset B` controls integration dependence, overlap and marks,
while `d : Finset B → ℝ` enters G1–G3 and activities separately. Nothing
in the generic theorem equates $d(S)$ with the covering length of $S$.
`Mayer.lean` has the same separation. The identification occurs in
`Polymer/MarkedCubes.lean:CubeLabels`, where `ysite` supplies both support
and `dl`; `dExt_le` and `presum_bound` compare them, and `dExt_unionCs_le`
from `Fluctuation/CubeSystem.lean` supplies G3. Replace those wrapper
arguments by (2.4), (3.2), and G3-R. The algebraic
`labelAct_integral_eq_exp` and its marked versions then use support for
locality and (2.3) for size; their abstract Mayer proofs do not change.
The wrapper theorems' *statements* do change.

## 4. Returning the cluster output to a core class

The statement “Mayer gives decay in $D_R(S)$” alone does not close Def-6.
Here is the required finite, covariant reindexing. Suppose a cluster
coefficient $F_z(S)$ has a root cell $z\in S$, depends only on $S$, and

$$|F_z(S)|\le A_0e^{-\kappa'D_R(S)}.\tag{4.1}$$

For each $S$, let $\mathcal W_z(S)$ be all cores $W\in\mathcal D_j$ with

$$z\in W,\quad S\subset N_R(W),\quad d(W)\le D_R(S)+J.\tag{4.2}$$

This set is nonempty. From a minimizing core, choose a cell at distance
at most $R$ from $z$ and join it to the $La$-cube containing $z$;
the same path estimate as Lemma 2.1 costs at most $J$. Distribute
$F_z(S)$ equally over all $W\in\mathcal W_z(S)$. This rule is invariant
under translations and the cube symmetries; no noncovariant choice of a
minimizer survives. Summing over $W$ recovers $F_z(S)$ exactly.

For fixed $W$, only supports $S\subset N_R(W)$ occur, at most
$2^{|N_R(W)|}\le 2^{C(1+d(W))}$ of them. By (4.2),
$D_R(S)\ge d(W)-J$. Therefore the reindexed term obeys

$$|F_z(W)|\le 2^C A_0e^{\kappa'J}
e^{-(\kappa'-C\log2)d(W)},\qquad
\operatorname{Dep}(F_z(W))\subset N_R(W).\tag{4.3}$$

This is **PROVED** for the finite abstract sum. The energy output rate is
$\kappa'-C\log2$. The observable extraction in the landed
`Thm31b.thm31b_of_input` spends $\kappa_0+1$ in addition; with the same
core reindexing, its class rate is at least
$\kappa'-\kappa_0-1-C\log2$, subject to the marked premises.
The prefactor $2^Ce^{\kappa'J}$ must be put into the output $E_0$ and
observable amplitude choices; it is fixed before $\beta$ and does not
alter the rate.

**Amended class clause (OPEN-CLASS-HALO).** A scale-$j$ term indexed by
connected core $X$ has size $d_j^{\rm cov}(X)$, bound
$E_0e^{-\kappa d_j^{\rm cov}(X)}$, and dependence on the fields and
sources in $N_2(X)$, with analytic extension to an *open neighbourhood*
of the corresponding halo-domain projection. The energy anchor $y$ lies
in $X$; a marked term has its marked site in $X$. Point-group action
transports core and halo together. The old class with dependence on $X$
is a special case; the converse needs new declarations. If coarse-graining
contracts cell distances by $L$ and the local construction adds at most
one cell, a halo radius obeys
$r_{j+1}\le\lceil r_j/L\rceil+1$. Thus $R=2$ is invariant for $L\ge3$.
That **geometric transport and the analytic neighbourhood inclusion are
OPEN-SCALE-HALO**, not consequences of (4.3).

The consumer audit is concrete:

1. `SmallField/Def6v2.lean:SFTermClauses.localE/localM` currently require
   equality only on $X$. Their statements must use $N_2(X)$; `boundE/M`
   keep `sizeJ X`. `Def6.lean` and `Def6v2Source.lean` class/source
   constructors and `Def6v2Inhabited.lean` must be transported.
2. `SmallField/RenormTermwiseDefs.lean:TermFamily/PremisesTerm` packages
   `term X` on `Cfg X`. A halo-dependent term cannot instantiate it.
   Replace the carrier by `Cfg (N_2 X)` while retaining the core distance.
   The landed `Itw_congr` already has the separate $X\cup\operatorname{st}_+(y)$
   support; the replacement must allow that star *and* the inherited halo.
   `Def6v2Renorm.lean` and `RenormTermwiseIrrel.lean` then need a halo
   version of `PremisesTerm` and the anisotropic I-6 estimate. This is
   **OPEN-I6-HALO**, in addition to the existing **OPEN-I6-XIDOM**.
3. Proposition 3.3's old-energy input, including
   `InteractionHatAssemble.lean` `hEbdE/hEbdM`, must receive the halo
   terms with the same core decay. Numerical rate comparison remains
   $\kappa_{\rm dec}\le\kappa$ along termwise I-6; the locality proof
   has to enlarge `CovSetup`/`BgSetting` and show the collar lies within
   the chosen generating set. `Localization/I5.lean:i5_background`
   currently localizes core-supported terms and does not prove this.
   This is **OPEN-I5-HALO**, also requiring the modular version in VMOD.
4. `Fluctuation/Theorem42.lean` trace action and its numerical decay do
   not use the new class carrier. Its boundary application reads H7 and
   the decoupled response on a common cover; the H7 halo-domain
   inclusion is **OPEN-H7-HALO**. The real trace and late numerical
   estimates remain as stated in `FLUCTUATION.md` §4.2.
5. `Thm31b` and the observable marked layer use support overlap and
   mark containment. Feed their generic `sup` the halo support, use
   G2-T/G2-P, and reindex by (4.2). Their final `localM` conclusion must
   be on $N_2(X)$. The two-mark activity reserve in (3.4) applies.

These are substantive changes to the induction statement. They cannot be
obtained by renaming the old `X` or by treating (4.3) as a proof of the
present `localE/localM` fields.

## 5. Admissible rate order and an explicit three-dimensional instance

The following is a complete witness for the *abstract rate inequalities*.
The physical and class bridges just named remain open. First choose
$d,N,\gamma,\alpha,\alpha_1,L$, then $m_0$ as in
`FLUCTUATION.md` §1.5. Form $c_1,C,J,a_{\rm ent},a_{\rm Multi}$.
Choose in order

$$\begin{aligned}
&\kappa_0\ge C\log2+a_{\rm ent}+1,\\
&K_c\ge1+\max\{hK_0(d,L,\kappa_0),
                 h2^C K_0(d,L,\kappa_0-C\log2)\},\\
&\kappa\ge\max\{3\kappa_0+3,
                 2a_{\rm Multi}+4,
                 8\kappa_0+2C(1+\log2)+7\},\\
&\kappa_{\rm dec}=\kappa,\qquad
 \kappa_H=2\kappa-1,\\
&\kappa'=\tfrac32\kappa+\kappa_0+1+C\log2,\\
&\kappa_{\rm AE}\ge\max\{4d(2L+1)^d\kappa,
             6,\ 4\log(((2L+1)^d)(L^{m_0})^d)+2\}.
\end{aligned}\tag{5.1}$$

The third lower bound for $\kappa$ is exactly (3.3): substitution gives
$2\kappa-1\ge\kappa'+3\kappa_0+C+3/2$.
Also $\kappa_H-2\kappa_0\ge0$ and the landed decoupling and trace
rate tests hold. The rate after marked extraction and (4.3) is

$$\kappa_{\rm next}^{\rm cert}
=\kappa'-\kappa_0-1-C\log2
=\tfrac32\kappa\ge\kappa.\tag{5.2}$$

This is the intended statement `stepRates_consistent`: **PROVED as real
arithmetic conditional on G1-R/G2-T/G2-P/G3-R and on the amended class
bridge**. It is false if `κH` is replaced by the current multiplicative
rate of `labelAct_of_hatExpansion`; see `RATES.md` (4)–(6).

After $\kappa_{\rm AE}$ choose $m_1$ so that at least

$$L^{m_1}\ge c_*^X(d,L)e^{N_0(d,L)\kappa_{\rm AE}},\qquad
C_0^2K_2^\Xi N K_{\rm close}e^{-\gamma_wL^{m_1}}<1/2,\tag{5.3}$$

and all independent I-4/I-5 lower bounds from §1.5 hold. These are
eventually true as $m_1\to\infty$ once their constants are fixed.
Then choose $\alpha_0,E_0$ in the order of §1.5 and finally
$\beta\ge\beta_*(\alpha_0,E_0)$ to make the actual positive activity
$\varepsilon_U$ satisfy the two-mark bound

$$\varepsilon_U\le
\frac{1}{32K_c^4C\exp((\kappa_H-2\kappa_0)J+C+\kappa'J)}.\tag{5.4}$$

That final implication is **CONDITIONAL ON OPEN-PHYSICAL-LABEL-ACTIVITY**;
the numerical threshold itself is explicit. Other late thresholds,
including (Λ28′), are independent maxima in $\beta_*$.

For one fully specified *arithmetic* instance take $d=3$, $N=2$,
$\gamma=1/4$, $\alpha=1/4$, $\alpha_1=1/16$,
$L=2^{90}+1$ (odd), and $m_0=3$. Then
$L^{1/4}>2(8d+12)^4$ and
$L^{m_0}\ge\max\{14d,L+9,4+(4dL^3+L)/L\}$.
Put $h=125$, $c_1=[3(2L-1)]^3$, $C=125c_1$,
$J=12(L+4)$, and choose the concrete real numbers

$$\begin{aligned}
\kappa_0&=\lceil C\log2+a_{\rm ent}(3,L)\rceil+2,\\
K_c&=1+125K_0(3,L,\kappa_0)
          +125\,2^C K_0(3,L,\kappa_0-C\log2),\\
\kappa&=\left\lceil\max\{3\kappa_0+3,
  2a_{\rm Multi}(3,L)+4,
  8\kappa_0+2C(1+\log2)+7\}\right\rceil+10,\\
\kappa_{\rm AE}&=1+\max\{12(2L+1)^3\kappa,
  6,\ 4\log(((2L+1)^3)L^9)+2\},\\
\kappa_{\rm dec}&=\kappa,\quad
\kappa_H=2\kappa-1,\quad
\kappa'=3\kappa/2+\kappa_0+1+C\log2.
\end{aligned}\tag{5.5}$$

The functions $a_{\rm ent},K_0,a_{\rm Multi},c_*^X,N_0$ are the
landed definitions in `SizeModEntropy.lean`, `TraceEntropyCells.lean`,
`DecoupledXBounds.lean`, and `Cover.lean`; thus (5.5) defines numbers,
not unspecified “large constants.” Take $m_1$ to be the least integer
satisfying (5.3) and the finite §1.5 I-4/I-5 conditions, and then take
$\beta$ according to (5.4) and those conditions. This is an explicit
selection algorithm; there is no closed physical $\beta$ value until
OPEN-PHYSICAL-LABEL-ACTIVITY supplies its $\beta$ dependence.

## 6. Lean change list and bounded proof sequence

The following names are targets, **OPEN in Lean** unless marked as an
already landed declaration. Each proposed leaf is sized for roughly
100–300 Lean lines; the large bridges should be split at the indicated
interface, rather than stated with the desired conclusion as a premise.

| Order | Target and derivation | Status |
|---|---|---|
| 1 | `haloCells`, `halo_contains_blockThick`: coordinate quotient by $a$, unit-block divisibility, one-neighbour crossing. | OPEN |
| 2 | `coreHaloSize`, `coreHaloSize_le_core`, `coreHaloSize_nonneg`: finite minimization (2.3), torus witness, (2.4). | OPEN |
| 3 | `halo_card_le`: map each halo cell to a core cell, at most $h$ preimages; apply landed `G1_cellCount`. | OPEN; conditional on landed G1 |
| 4 | `halo_bridge`: shortest cell path, connect its cover cubes to the two optimal core trees, cost $J$. | OPEN |
| 5 | `halo_union_le`, `halo_unionCs_le`: minimize and use `halo_bridge`, then induct on a connected support spanning tree. | OPEN |
| 6 | `halo_label_entropy`: sum over the at most $h$ nearby root cells and use landed `G2_X`. | OPEN; conditional on landed G2_X |
| 7 | `halo_support_entropy`: count $2^{|N_R(W)|}$ sub-supports and apply the preceding lemma at $\kappa_0-C\log2$. | OPEN |
| 8 | `HaloCubeLabels`: fields `core`, `support`, `coreSize`, `support_subset_halo`, `dep`, and core covariance; replace the statements of landed `CubeLabels.dExt_le`, `presum_bound`, `LabelAct.presum_bound`, `labelAct_integral_eq_exp`, and `MarkedCubesTwo` wrapper. Derive (3.2) from targets 2 and 6. | OPEN; generic `Mayer.lean`/`MayerMarked.lean:mayer_marked` PROVED |
| 9 | `halo_numerics_PE`, `halo_two_mark`: instantiate landed `numerics_PE` with $C,J,K_c$ and $\varepsilon_H=\varepsilon_UK_c$; use the extra factor four. | OPEN as wrapper; arithmetic PROVED |
| 10 | `rooted_halo_reindex`: construct finite set (4.2), divide by its cardinality, prove covariance, exact sum, and (4.3). | OPEN |
| 11 | `SFTermClausesHalo` in `Def6v2.lean` and the corresponding `Def6.lean` class: replace `localE/localM` by $N_2(X)$ agreement; keep `sizeJ X` in bounds; transport monotonicity and source constructors. | OPEN-CLASS-HALO |
| 12 | `PremisesTermHalo`/`ItwHalo`/`termwise_irrelevant_aniso_halo`: carrier `Cfg(N_2 X)`, star closure, tube/slit domain, core rate and scaling. Change `RenormTermwiseDefs`, `RenormTermwiseProps`, `RenormTermwiseIrrel`, `Def6v2Renorm`, `Def6BridgeLift`, and their immediate consumers. | OPEN-I6-HALO and OPEN-I6-XIDOM |
| 13 | `i5_background_halo`, `interaction_expansion_hat_halo`: collar-aware `CovSetup` and decoupled locality, then the old-term `hEbdE/hEbdM` at $\kappa_{\rm dec}-1$. Change `Localization/I5.lean`, `I5FluctLocal.lean`, `InteractionHat*`. | OPEN-I5-HALO |
| 14 | `labelAct_of_hatExpansion_halo`: use target 1 and core size directly, avoiding `HatLabelsGeom.thick_spec` in the activity exponent. Change `HatLabelsTerms.lean`/`HatLabelsExpansion.lean` output statements; keep `thick_spec` as a valid but insufficient bound. | OPEN-PHYSICAL-LABEL-ACTIVITY |
| 15 | `thm31b_halo`, `theorem42_halo_boundary`, `step_class_halo`: apply targets 8–10, retain trace numerical bounds, prove the marked observable and rescaled $R=2$ clause. Change `Thm31b` wrappers, `Theorem42` boundary consumer, `SmallField/Step`. | OPEN-SCALE-HALO, OPEN-H7-HALO, OPEN-MOD-HALO |
| 16 | `stepRates_consistent`: substitute (5.1) into (3.3), (4.3), and (5.2); state its exact geometry/class assumptions. | OPEN as Lean declaration; arithmetic PROVED here |

The landed declarations `hatPsiF_local`, `AgHat`, `AgHatF`,
`agHatF_hatOf`, `thick_spec`, `labelAct_of_hatExpansion`, `CubeLabels`,
`numerics_PE`, `mayer_marked`, `SFTermClauses.localE/localM`,
`PremisesTerm`, and `i5_background` exist in the cited files. The proposed
halo versions do not. In particular, replacing only the last label theorem
would hide unsupported input locality and would not establish a step.

**Conclusion.** Separate support from core size in the cluster geometry.
The finite whole-lattice support theorem, entropy bounds, pre-summation,
rooted reindexing and abstract rate certificate are **PROVED** above.
Preservation of the physical Def-6 class is **CONDITIONAL ON OPEN-CLASS-HALO,
OPEN-I6-HALO/XIDOM, OPEN-I5-HALO, OPEN-PHYSICAL-LABEL-ACTIVITY,
OPEN-SCALE-HALO, OPEN-H7-HALO**, and the modular **OPEN-MOD-HALO** where
boundaries occur.
