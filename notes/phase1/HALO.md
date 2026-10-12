# Halo locality in the small-field class: proved geometry and remaining bridges

**Scope and decision (12 October 2026).** This follows `LABELS.md`, whose
separate core-size/dependence-support plan is retained. Here **PROVED** means
the displayed mathematical argument is complete; **LANDED** means the cited
Lean declaration already exists; **OPEN** means neither that declaration nor
an argument deriving it from landed premises is available. In particular,
the requested theorem with *only* OPEN-PHYSICAL-LABEL-ACTIVITY and
OPEN-H7-HALO as hypotheses cannot yet be asserted: §3 gives a structural
counterexample to a counting-only I-6 bridge, and §4 identifies a missing
two-set I-5 estimate. A precise conditional theorem with these additional
inputs is stated in §6.

Notation is fixed throughout. At birth level $j$, let
$a_j=L^{j+m_0+m_1}$ in fine-site units, and let $C_j(x)$ be the aligned
$a_j$-cell containing $x$. A core $X\in\mathcal D_j$ is a connected union
of aligned $La_j$ cover cubes, hence a union of $a_j$-cells and of
$j$-blocks. For an integer $w\ge0$ put

$$X^{+w}:=\bigcup\{C_j(z):
  \operatorname{dist}_\infty(C_j(z),C_j(X))\le w\},\quad w>0,
\qquad X^{+0}:=X.\tag{0.1}$$

Here cell distance is the periodic distance on the $a_j$-cell torus. For
polymer cores the special $w=0$ convention agrees with the union formula.
It makes the embedding of the landed class literally identity at width
zero. Write $h_w=(2w+1)^d$ and $M=L^{m_0+m_1}$, the number of $j$-blocks
along one $a_j$-cell side.

## 1. Exact amended v2 class, field by field

`Balaban/SmallField/Def6v2.lean:SFTermClauses` is a proposition about
`Terms`, a `FieldDom`, and constants `P`. Define
`SFTermClausesHalo w P Dom Tm` with the *same* term indices
`(j,y,X)` and `(j,x,X)`, `IsPolyDom P.m₀ j X`, and the same
`sizeJ P.m₀ j X`. Change the following fields exactly:

* `gs_spec`: replace its first conclusion $X\subset(\mathrm{gs}_jX).\Omega_1$
  by $X^{+w}\subset(\mathrm{gs}_jX).\Omega_1$. Retain
  $\Omega_i=\varnothing$ for $i>j$. This makes the generating set contain
  every spin and source coordinate read by the term. At $w=0$ it is the
  landed field.
* `localE`: replace agreement on $X$ by agreement of both $\Psi$ and $h$
  on $X^{+w}$, for all arguments as in the landed field. `localM` replaces
  agreement of $\Psi,h,g$ on $X$ by agreement on $X^{+w}$.
  Both remain unconditional equalities of functions, not merely
  equalities on real data.
* `analyticE/M`: retain the actual `AnalyticOnNhd ℂ` conclusions on
  `Dom.dom j (Tm.gs j X)` and its intersection with
  $\|g\|_1<1$. The syntax need not change, but their generating set is now
  the one from the stronger `gs_spec`. For the lifted finite-dimensional
  function on `Cfg(X^{+w})`, a separate *chart inclusion* must show an open
  anisotropic polydisc of halo configurations maps into this domain.
  `AnalyticOnNhd` then composes with that chart. The old inclusion for
  `Cfg X` is insufficient. This is **OPEN-I6-HALO-DOMAIN**.
* `boundE/M`: retain the displayed amplitude and
  $e^{-P.\kappa\operatorname{sizeJ}(X)}$ with $X$ the **core**. The domain
  is again `Dom.dom j (Tm.gs j X)`, now with the stronger generating set.
  The observable bound retains its source norm, scale factor, and strict
  inequality. No $d(X^{+w})$ is substituted.

The remaining fields have the following exact dispositions.

| v2 field | Amended statement | Reason |
|---|---|---|
| `rotE`, `rotM` | Unchanged syntax, on the new `Dom.dom` sets. | Internal $O(N)$ acts pointwise, so it commutes with $X\mapsto X^{+w}$. |
| `pavingGS` | Unchanged syntax. | Paving symmetries preserve the aligned $a_j$-cell lattice; prove $(rX)^{+w}=r(X^{+w})$. |
| `eucE`, `eucM` | Unchanged syntax. | Index remains core $X$; halo is transported by the same paving symmetry. |
| `eucEloc`, `eucMloc` | Unchanged syntax. | These are statements about the sums `Eloc/Mloc` on full level data. |
| `analyticE`, `analyticM` | Same formula; stronger generating-set and chart inclusion obligations. | Analyticity on the old core projection does not control new halo coordinates. |
| `boundE`, `boundM` | Same formula with `sizeJ X`. | Separating size from support is the point of the repair. |

`GsSpecClass.lean:SFTermClausesStrong.gsStrong` must become
`GsSpecStrong j hjk (X^{+w}) (Tm.gs j X)`. The definition of
`GsSpecStrong` accepts any set; its fields `subset`, `topLayer`,
`layerEq`, and `blkEq` must now hold at every halo site. The landed
`GsSpecStrong j hjk X G` does **not** imply this for $w>0$.
`GsSpecStrong.adj_dataSites` then applies to the halo and its immediate
neighbours. The whole-level generating set gives a formal witness
(`levelGS_strong`), but the local minimal set `polyGS X` has no landed
halo-strong theorem; changing it to `polyGS (X^{+w})` is a genuine
generating-set change. The latter set need not itself be in
$\mathcal D_j$ (it is an $a_j$-cell union, generally not a union of
$La_j$ cover cubes), though `GsSpecStrong` does not require it.

`IsSF2.density`, `expo2`, the parameters and source norm, `IsSFFamily2`
`admissible`/`coeff`, and `RenormCond` remain textually unchanged.
`IsSFFamily2.torus` uses `SFTermClausesHalo` and `torusIndep` must be
strengthened in *applications*: if the lifted core $X$ does not wind
on a torus but $X^{+w}$ does, the value of a halo-dependent term cannot
be identified with its value on another torus by the current
`TorusIndep.E_eq` hypothesis. Require `NonWind` of the halo in the
comparison, or restrict to the eventual large tori where this follows
for every fixed finite core. The latter suffices for `Einf`, but the
landed `Einf_eq_torus` on an arbitrary nominated torus changes statement.
The `SourceForm` and `RefJet` consumers have a `Cfg X` carrier and must
likewise be parameterized by the halo carrier; their algebraic source
factorization is unchanged.

**Lemma 1.1 (landed members embed; PROVED).** Every landed
`SFTermClauses P Dom Tm` yields `SFTermClausesHalo 0 P Dom Tm`.
Field by field, (0.1) gives $X^{+0}=X$, so copy each field verbatim.
The same is true of `SFTermClausesStrong`, `IsSF2`, and `IsSFFamily2`
with width zero and the same density and family data. For any $w\ge0$,
the *locality equality alone* follows from the landed one since
$X\subset X^{+w}$: agreement on the halo implies agreement on $X$.
No claim is made that a landed member satisfies the stronger `gs_spec`,
`gsStrong`, or the halo chart at positive width. This is the exact sense
in which the amended class loses no existing member.

## 2. Cell-scale transport and its rounding

Let $q_L:\mathbb Z^d\to\mathbb Z^d$ take an old $a_j$-cell index
$n$ to the parent $a_{j+1}=La_j$ cell index
$q_L(n)_\mu=\lfloor n_\mu/L\rfloor$; use the periodic quotient on a
divisible torus. The following is independent of the field theory.

**Lemma 2.1 (parent halo; PROVED).** For any old cell sets $C$ and
integer $w\ge0$,

$$q_L(N_w(C))\subset N_{\lceil w/L\rceil}(q_L(C)).\tag{2.1}$$

*Proof.* In one coordinate, if $|n-m|\le w$, write $n=La+r$,
$m=Lb+s$ with $0\le r,s<L$. The difference of quotient indices is
at most $\lceil w/L\rceil$ in absolute value: crossing $t$ distinct
parent boundaries requires displacement at least $(t-1)L+1$, and
$t\le\lceil w/L\rceil$. Apply this to each coordinate and choose
periodic lifts realizing the old cell distance. $\square$

The step's *hat-variable* addition has one cell of width:
`I5FluctLocal.psiThick` adds one nearest-neighbour fine site;
`HatEngineLocal.blockThick` fills the `(k+1)` unit block of such a site.
Since $L^{k+1}$ divides the $a_{k+1}$ cell side, that unit block lies
in one $a_{k+1}$ cell. Hence, for the hat variable alone,

$$\operatorname{cellSupp}(\operatorname{blockThick}Y)
\subset N_1(\operatorname{cellSupp}Y).\tag{2.2}$$

This statement concerns hat coordinates. `I5Local.thickSet` additionally
uses `resDep`, and a corresponding *raw-data* one-cell bound has not
been proved. The class halo width must cover all class fields, so (2.2)
does not by itself settle OPEN-SCALE-HALO for the physical step.

If a new core $Y$ contains the parent image of the old core and the
step introduces at most one new $a_{j+1}$ cell beyond the parent
support, (2.1)–(2.2) prove the **conditional exact recurrence**

$$w_{j+1}\le\lceil w_j/L\rceil+1.\tag{2.3}$$

For $L\ge3$, $w=2$ is invariant because
$\lceil2/L\rceil+1=2$; starting from $w=0$ the first
two widths are at most $1,2$, then remain at most $2$.
The *real affine* inequality requested in the follow-up needs a
rounding allowance: for integer $w$,

$$\lceil w/L\rceil+1\le w/L+(2-1/L),\qquad
w_j\le\frac{2L-1}{L-1}\quad\text{under that affine recursion from }w_0=0.
\tag{2.4}$$

To verify the constant, write $w=La+r$, $0\le r<L$.
For $r=0$ the excess is $1$; for $r>0$ it is $2-r/L\le2-1/L$.
Iterate $u_{n+1}\le u_n/L+(2-1/L)$ to obtain
$u_n\le(2-1/L)(1-L^{-n})/(1-L^{-1})$.
An affine bound with geometric addition $1$ is **false**: at
$w=1$, (2.3) permits $w'=2$, while $w/L+1<2$.
The integer invariant $2$ is sharper than the affine bound.

**Cover-cell warning.** The parent of one old $La_j$ cover cube is
one $a_{j+1}$ cell. It is not itself a $La_{j+1}$ cover cube, so
$q_L(X)$ need not belong to $\mathcal D_{j+1}$, already in $d=1$.
Taking the union of new $La_{j+1}$ cover cubes meeting $q_L(X)$
produces an admissible connected core and can only improve the
containment in (2.3), but its *covering length and rate* need a separate
comparison. The landed one-step I-5 instead constructs new cores
$Y\in\mathcal D_{j+1}$; to invoke (2.3) one must prove that such a
$Y$ contains the parent image of the old halo core. This is
**OPEN-SCALE-HALO-CORE**, not a consequence of cell division.

## 3. I-6: exact changed carrier, counting, and cancellations

The landed `RenormDefs.lean:TermFamily` has
`term : (X : Finset (Site d)) → Cfg d N X → ℂ`.
`PremisesTerm` (`RenormTermwiseDefs.lean`), `PremisesCore`, and
`PremisesTermAniso` (`RenormAnisoCtx.lean`) use the same carrier.
Their analyticity, tube bound, rotation invariance, and data bound are
all stated on configurations of **$X$**. `Def6v2Renorm.lean`
`IsSFFamily2.premisesTermAnisoInf`, `premisesCoreInf`,
`premisesTermAnisoAvg`, and `premisesTermAvgA` are **LANDED** for the
existing class; their proofs reduce to the landed Def-6 class via
`toLanded`. They do not accept the positive-width class of §1.

**Obstruction (PROVED).** Take core $X=\{0\}$ and halo containing a
different site $z$. The term $E_X(\psi)=\psi(z)_1$ is local in $X^+$,
but two fields agreeing on $X$ and differing at $z$ give different
values. There is therefore no function `Cfg X → ℂ` representing it.
An entropy/counting estimate cannot supply that missing function.
The replacement structure must keep separate `core X`,
`carrier H(X)=X^{+w}`, `dist=d(X)`, and
`term X : Cfg(H(X)) → ℂ` (or an equivalent dependent family).

The changed I-6 steps are specific:

1. `RenormAnisoBridge.lean:Eaux`, `termLA`, `xiDom_of_polyA` and
   `RenormAnisoBridgeInf.lean:liftInfA` must pack and rotate
   `Cfg(H(X))`. The open `polyAniso`/`TubeAniso` are on $H(X)$.
   `xiDom_of_aniso` remains a domain lemma for the full field, but
   the witness field `fieldOf` must now realize arbitrary coordinates
   on $H(X)$; a witness on $X$ is insufficient. This is
   **OPEN-I6-HALO-DOMAIN** even though the radius
   `anisoRadius ≍ ε_j` and the ordinary class theorem are LANDED.
2. `tensA`, `tensB`, `tensM`, `Ax`, and the sums forming `SumConds`
   range over $H(X)$ for a halo term. `Ttw` still reads the centre,
   and `Phitw` still reads the forward star. The changed
   `Itw_congr` uses $H(X)\cup\operatorname{st}_+(0)$, which lies
   in $X^{+\max(w,1)}$ since $0\in X$.
   `RenormTermwiseSub.lean:IW_congr` similarly uses
   $(H(X)\cap W)\cup\operatorname{st}_+(0)$.
3. `RenormCond` itself is already imposed on the full density and may
   retain its four displayed clauses. But
   `Def6InfExpand.lean:LiftCtx.Hterm_eq_tensB`,
   `momentSum_shapes`, `Def6BridgeInfMoment.lean:liftInf_moment`,
   and the first-derivative bridge must sum derivative coordinates
   over $H(X)$, including sites outside the core. Their present
   proofs use `localE X`; merely changing the counting constant
   would omit genuine derivative terms. The centred cancellations
   can then be proved from the unchanged full-density (H.5) by
   differentiating its absolutely convergent halo expansion.
   That last interchange is **OPEN-I6-HALO-MOMENT**.
4. `RenormAnisoLocal.lean:TermOK.local_bound_aniso` and
   `RenormAnisoIrrel.lean:termwise_irrelevant_aniso` are abstract
   estimates once a correctly packaged halo `PremisesTermAniso`
   is available. Their Taylor algebra does not use the geometric
   identity `carrier=core`. Bounds on pair counts and diameters
   must use $H(X)$, while the exponential keeps $d(X)$.
   The reference-jet version in `Def6v2RefJet.lean` changes carrier
   identically.

**Lemma 3.1 (halo counting; PROVED).** Assume the lifted core shapes are
unions of $a_j$-cells and their centred count is the landed
`Def6BridgeInfLift.sum_wt_dInf_le`:

$$\sum_{X\ni0}|X|^2(1+d(X))^6e^{-(\kappa-1)d(X)}\le K_\infty,
\quad K_\infty=
\big[c_1L^{d(m_0+m_1)}\big]^2(8!e)
K_0(d,L,\kappa-2),\quad\kappa\ge a_{\rm ent}+3.\tag{3.1}$$

For fixed width $w$, with $h_w=(2w+1)^d$, one has

$$\sum_{X\ni0}|X^{+w}|^2(1+d(X))^6e^{-(\kappa-1)d(X)}
\le h_w^2K_\infty,\tag{3.2}$$

and, allowing a root only in the halo,

$$\sum_{X:\,0\in X^{+w}}|X^{+w}|^2
(1+d(X))^6e^{-(\kappa-1)d(X)}\le h_w^3K_\infty.
\tag{3.3}$$

*Proof.* Each $a_j$-cell of $X$ contributes at most $h_w$ cells to
$X^{+w}$; the cells are disjoint and contain the same number of
$j$-blocks, so $|X^{+w}|\le h_w|X|$. This gives (3.2).
For (3.3), if the origin lies in $X^{+w}$, $X$ contains at least one
of the $h_w$ $a_j$-cells within cell distance $w$ of the origin's cell.
Choose the fixed base $j$-block of each candidate cell. Because $X$
is a union of full cells, that base belongs to $X$. Bound the indicator
of halo incidence by the sum of these $h_w$ core-incidence indicators.
Translation by a cell multiple takes each corresponding shape family
bijectively to a family of core shapes containing $0$, preserving
$d(X)$ and $|X|$. Apply (3.1) to each. Multiplication by the
$h_w^2$ volume factor proves (3.3). On finite tori use periodic cell
translations; on the stabilized infinite family use the same
translation and then the landed finite-sum bound. $\square$

The diameter estimate also changes by a fixed constant. For
$x\in X^{+w}$ choose a core cell within $w$ cells and the point
of it with the same within-cell $j$-block offset. Their coordinate
distance is at most $wM$ per axis. If the landed core bound is
$\|u\|_1\le A(1+d(X))$, then

$$\|x\|_1\le(A+dwM)(1+d(X)).\tag{3.4}$$

Thus the elementary *counting and diameter* part of halo I-6 has no
rate loss; at $w=2$ the explicit factors are $h_w^2=5^{2d}$ and
$h_w^3=5^{3d}$. This does **not** prove the analytic or cancellation
bridges above. Moreover, if a support is not a union of entire aligned
$a_j$-cells, the base-point argument in (3.3) needs its own
cell-completion premise; the class cores do satisfy it.

## 4. I-5 and the old-term input

The numerical `hEbdE` and `hEbdM` of
`Fluctuation/InteractionHatAssemble.lean:interaction_expansion_hat_bound`
and its component theorems bound `EE τ` and `EM τ` on `XiCRaw Gj` by
$E_b(τ)e^{-(\kappa_{\rm dec}-1)d(X_τ)}$.
They do not mention field dependence; if a halo term has the same
bound and domain inclusion, the numerical step is unchanged.
`InteractionHatE.lean:eTermFun_bound` simply evaluates that bound
at the decoupled argument. Its analyticity theorem similarly needs
only the inclusion of the decoupled argument in the old term's
*halo* `XiCRaw` open domain.

The locality and cover are different. `eTermFun_local` proves global
equality of the composed raw argument by using `BgSetting.dep` and
`FlSetting.depm` into `X₁f`; it then applies `congrArg E`, without a
separate `localE` premise. Its proof works for **any** functional
$E$ if the chosen generating sets and `X₁f` already contain every
data site it reads. `CovSetup Gp m₀ j X 𝒦X` defines `X1` from the
*chosen cover cubes of $X$*: a coarse cover cube is selected only if it
contains an old cube of $\mathcal K_X$. The specification does not
promise $X^{+w}\subset X1$. A core cube at the edge of a selected
coarse cube has a one-cell halo in the adjacent coarse cube, which
`X1` need not include. Thus the existing `eTermFun_local` instance
cannot be fed a general halo class term using the same `CovSetup`.

The required **OPEN-I5-HALO** statement must carry two sets:

* a core $X\in\mathcal D_j$, its cover tree, and the input exponent
  $e^{-(\kappa_{\rm dec}-1)d_j(X)}$;
* a dependence set $H=X^{+w}$, generating sets for $H$, and an
  active/dependency region $X_{1,H}$ containing the `dataSites`,
  `composeDep`, `resDep` and fluctuation sites required by
  `BgSetting`, `FlSetting`, `fanH_local`.

The output core $Y\in\mathcal D_{k+1}$ must contain the coarse
image of $H$ (or have a declared bounded halo containing it), while
the bound must retain the *input core* size $d_j(X)$.
`i5_functional_hatLC` presently uses one set for both its
`CovSetup` tree and its dependency region; it must be restated with
this pair and a new base-polymer estimate. Enlarging $X$ to $H$
and applying the landed theorem loses the core exponent: the
covering length of a collar along a long core has no proved
additive comparison with $d(X)$ (`RATES.md` and `LABELS.md` §1).

**Conditional support conclusion (PROVED).** If this two-set I-5
theorem produces $Y$ containing the parent image of $H$, and its
decoupled output has the landed `AgHatF Y` locality, then its hat
dependence lies in $N_1(Y)$ by (2.2); it is in the fixed width-two
class. This is a set inclusion, independent of the activity rate.
The antecedent, the domain inclusion, and the decay estimate of the
two-set I-5 are **OPEN-I5-HALO**. The raw-data `thickSet` can require
more than the one-cell hat collar, so a common-cover bound for it
is also part of that open input.

## 5. Cluster interface with independent size and support

Here is a precise replacement for the whole-lattice part of
`Polymer/MarkedCubes.lean`; the modular form needs the separate
interface-compatible size in `VMOD.md`. Write
`B = CubeB m₀ j Ω`, with the same implicit torus parameters as the
landed structure. For the whole-lattice wrapper take $\Omega$ to be
the full torus. In Lean-style specification syntax (omitting those
implicit parameters):

```text
structure CubeLabelsHalo (Lb : Type*) where
  core       : Lb → Set CTorus
  supp       : Lb → Finset B
  dl         : Lb → ℝ
  isDj       : ∀ y, IsDj m₀ j (core y)
  meets      : ∀ y, (core y ∩ Ω).Nonempty
  size       : ∀ y, dl y = treeLenCovOne m₀ j (core y) ∨
                         (DjMod m₀ j Ω (core y) ∧
                          dl y = dcovMod m₀ j Ω (core y))
  suppNe     : ∀ y, (supp y).Nonempty
  suppHalo   : ∀ y, supp y ⊆ haloBlocks w Ω (core y)
```

The `core`, `isDj`, `meets`, and `size` fields reproduce the landed
`ysite`, `isDj`, `meets`, and `size` fields; `supp` now supplies the
integration carrier independently. The landed `size` disjunction is
retained, with its first branch used for the whole-lattice rate proof.
The `suppHalo` field proves $D_w(\operatorname{supp}y)\le dl(y)$ by
taking `core y` as a witness in the definition of $D_w$. It does not
assert equality of either quantity with the tree length of `supp y`.
For the modular branch, $D_{w,\Omega}$ must be finite on every
nonempty support and must admit that branch as a witness; this is
**OPEN-MOD-HALO**. Covariance of `core` and `supp` under paving
symmetries belongs in the physical activity wrapper, whose labels
carry that action; abstract Mayer does not use it.

```text
structure LabelActHalo (Lab : CubeLabelsHalo Lb) ... where
  H       : Lb → (∀ b : B, Ωb b) → ℂ
  meas    : ∀ y, Measurable (H y)
  dep     : ∀ y, DepOn (Lab.supp y) (H y)
  bound   : ∀ y Φ, ‖H y Φ‖ ≤ εH * exp (-κH * Lab.dl y)
  entropy : ∀ b : B, ∑ y, (if b ∈ Lab.supp y
                      then exp (-κ0 * Lab.dl y) else 0) ≤ Kc
```

Pre-sum over the fiber `supp y = S`. The proof of
`MarkedCubes.presum_bound` changes only at two points:
`dExt_le` is replaced by $D_w(S)\le dl(y)$, and the entropy predicate
`b` in `blocksOf(ysite y)` is replaced by `b∈supp y`. Choosing
$b\in S$ gives exactly `LABELS.md` (3.2):

$$\|\widetilde H(S)\|\le\varepsilon_HK_c
e^{-(\kappa_H-\kappa_0)D_w(S)}.\tag{5.1}$$

`presum_meas`, `presum_dep`, and `presum_sum` are finite-sum facts
using the `supp` fiber. `labelAct_integral_eq_exp`
(`Fluctuation/StepNonvanishCluster.lean`) then invokes generic
`Polymer/MayerPE.lean:mayer_pe` with `sup S=S`, `d=D_w`, G1/G2/G3
from `LABELS.md` §2, and (5.1). Its existing proof uses
`size = tree length of support` only through the wrapper lemmas
`presum_bound`, `sum_exp_dExt_le`, `dExt_unionCs_le`, and
`card_le_dExt`; all are replaced by the halo versions.
`Polymer/MayerMarked.lean:mayer_marked` itself needs no changed
statement: its `sup` and `d` are already separate parameters.
`MarkedCubesTwo.lean` and the one-mark wrappers repeat the same
substitutions, with the two-mark activity slack of `LABELS.md` (3.4).
The generic analytic identities and Cauchy estimates use `supp`
for integration dependence and require no tree-length identity.

**Status.** The finite whole-lattice pre-summation derivation is
**PROVED** given the core halo containment and the entropy bound;
generic Mayer/marked-Mayer is **LANDED**. The new wrapper structures
and declarations are **OPEN in Lean**. The physical complex activity
and its common open domain remain **OPEN-PHYSICAL-LABEL-ACTIVITY**.

## 6. Correct rate theorem and why the proposed two-input version fails

Let `HaloGeom(w=2)` denote the mathematical G1/G2/G3, counting,
rooted-reindexing, and exact integer recurrence (2.3). Let
`ClassBridgeHalo` denote §1 plus the chart and torus transport of §3;
`I6Halo` the changed carrier, full-site cancellation, and anisotropic
estimate; `I5Halo` the two-set old-term theorem of §4;
`ScaleHaloCore` the new-core containment and covering-rate transport
of §2; `ModHalo` the modular versions where required. Then the exact
conditional theorem supported by the arguments is:

> **`stepRates_consistent_halo` (PROVED CONDITIONAL ON the named inputs).**
> Assume `HaloGeom(2)`, `ClassBridgeHalo`, `I6Halo`, `I5Halo`,
> `ScaleHaloCore`, and, in the boundary case, `ModHalo`. Assume the
> complex `PhysicalLabelActivity` with effective amplitude satisfying
> `LABELS.md` (5.4), and `H7Halo` for the trace/boundary response.
> Choose the rates in `LABELS.md` (5.1). Then the fluctuation and
> marked-cluster outputs have core decay at least $3\kappa/2$ and
> dependence within width two; old scale terms retain their core
> rate $\kappa$. Hence the amended class has rate $\kappa$ after one
> step, with the stated amplitude threshold.

*Proof.* The purely numerical substitution is `LABELS.md` (5.1)–(5.2).
`I6Halo` supplies the old-term rate $\kappa-1$ on its core and its
halo analyticity. `I5Halo` turns that input into the old-term part
of the complex activity at decoupling rate
$\kappa_{\rm dec}=\kappa$, keeping core sizes; the potential/trace
parts use their existing hypotheses and `H7Halo`. `PhysicalLabelActivity`
gives the original-core activity at $\kappa_H=2\kappa-1$.
`HaloGeom(2)` and §5 give the cluster coefficient at $\kappa'$ in
$D_2$; the covariant rooted reindexing of `LABELS.md` (4.2)–(4.3)
spends $C\log2$, and the observable extraction spends
$\kappa_0+1$. The remaining rate is exactly $3\kappa/2$.
`ScaleHaloCore` gives width two at the next class scale and transports
the size without reducing this rate. All prefactors are fixed before
the final $\beta$ choice. $\square$

There is no derivation that drops `ClassBridgeHalo`, `I6Halo`,
`I5Halo`, `ScaleHaloCore`, and `ModHalo` while keeping only
`PhysicalLabelActivity` and `H7Halo` open. The one-site counterexample
in §3 shows the landed `PremisesTerm` cannot even *state* an arbitrary
positive-width term. The edge-of-coarse-cube example in §4 shows the
landed `CovSetup` does not cover it. The old cover-cell image in §2
shows the scale core is not automatically admissible. These are
independent, concrete missing assertions, not numerical choices.

## 7. Lean declaration sequence

Each target is a bounded lemma/module (roughly 100–300 lines), with the
displayed derivation. Nothing here authorizes changes to the read-only
`/home/scott/Balaban` tree.

| Order | Target / landed declarations whose statements change | Derivation and status |
|---|---|---|
| 1 | `haloSites`, `haloBlocks`, `halo_zero`, `halo_mono`, `halo_equivariant` (new). | Quotient by `cellSide`; `halo_zero` on cell-union cores; cell-distance symmetry. **OPEN in Lean; PROVED mathematically.** |
| 2 | `halo_cell_card`, `halo_parent`, `blockThick_subset_halo` (new). | At most $(2w+1)^d$ neighboring cells; coordinate quotient proof of (2.1); divisibility of unit block by $a_j$. **OPEN in Lean; PROVED mathematically for hat support.** |
| 3 | `halo_rate_recurrence`, `halo_fixed_two` (new). | Integer ceiling (2.3), not the false affine bound with addition one; prove the weaker affine (2.4). **OPEN in Lean; PROVED conditional on new-core containment.** |
| 4 | `SFTermClausesHalo`, `SFTermClausesStrongHalo`, `IsSF2Halo`, `IsSFFamily2Halo`; changed `gs_spec`, `localE/M`; unchanged fields listed in §1. | Copy old fields at $w=0$; prove `toHaloZero`; for positive $w$, prove strong specification on halo. **OPEN-CLASS-HALO.** |
| 5 | `TorusIndepHalo`, `NonWindHalo_eventually`, changed `Einf_eq_torus` with halo nonwind. | Fixed-width halo of a finite shape is finite, so eventually nonwinding; no arbitrary-torus inference from core nonwind. **OPEN-I6-HALO.** |
| 6 | `sum_wt_halo_anchored`, `sum_wt_halo_incidence`, `halo_diam` (new). | (3.2)–(3.4) from landed `sum_wt_dInf_le`; constants $h_w^2K_\infty$, $h_w^3K_\infty$, $A+dwM$. **OPEN in Lean; PROVED mathematically conditional on landed core count.** |
| 7 | `TermFamilyHalo`, `PremisesCoreHalo`, `PremisesTermAnisoHalo`; change `RenormDefs`, `RenormTermwiseDefs`, `RenormAnisoCtx`. | Separate index core and `Cfg halo`; prove old carrier as width-zero specialization. **OPEN-I6-HALO.** |
| 8 | `xiDom_of_polyA_halo`, `Eaux_halo`, `termLA_halo`, `liftInfA_halo`, `premisesTermAnisoInf_halo`; change `RenormAnisoBridge`, `RenormAnisoBridgeInf`, `Def6v2Renorm`. | Construct open halo-coordinate chart and transport rotation/source bound; use stronger `gs_spec`. **OPEN-I6-HALO-DOMAIN.** |
| 9 | `Hterm_eq_tensB_halo`, `momentSum_shapes_halo`, `sumCondsInf_halo`; change `Def6InfExpand`, `Def6BridgeInfMoment`, `RenormTermwiseDefs`. | Differentiate over all halo coordinates, prove summable interchange with (3.3), identify unchanged full-density H.5. **OPEN-I6-HALO-MOMENT.** |
| 10 | `Itw_congr_halo`, `IW_congr_halo`, `termwise_irrelevant_aniso_halo`; change `RenormTermwiseProps`, `RenormTermwiseSub`, `RenormAnisoIrrel`. | Reuse Taylor algebra with support $H(X)$, star inside $H_{\max(w,1)}(X)$, rate measured by core, constants of (3.2)–(3.4). **OPEN-I6-HALO.** |
| 11 | `BgSettingHalo`, `CovSetupCoreSupport`, `eTermFun_local_halo`, `i5_functional_hatLC_halo`; change `Localization/I5Fan`, `TreeLengthCov`, `I5Fluct`, `Fluctuation/InteractionHatE`. | Keep core cover tree and size, put all dependency sites in a second region; prove new base term and common open-domain inclusion. **OPEN-I5-HALO.** |
| 12 | `CubeLabelsHalo`, `LabelActHalo`, `presum_bound_halo`, `presum_dep_halo`, `presum_sum_halo`; change `Polymer/MarkedCubes.lean`. | Exact fields and proof substitutions of §5. **OPEN in Lean; abstract finite-sum proof PROVED.** |
| 13 | `labelAct_integral_eq_exp_halo`, `markInt_expansion_halo`, `twoMark_expansion_halo`; change wrappers in `StepNonvanishCluster`, `MarkedCubes`, `MarkedCubesTwo`. | Invoke landed `mayer_pe`/`mayer_marked` with `sup S=S`, `d=D_w` and G1/G2/G3; use activity slack. **OPEN as wrappers; generic cluster theorem LANDED.** |
| 14 | `rooted_halo_reindex`, `stepRates_consistent_halo`. | Covariant equal splitting and fiber count from `LABELS.md` §4; substitute §6 hypotheses and rate chain. **OPEN in Lean; PROVED CONDITIONAL ON the named physical/class inputs.** |

The already LANDED anisotropic declarations
`termwise_irrelevant_aniso`, `IsSFFamily2.premisesTermAnisoInf`, and
`IsSFFamily2.renormalization_aniso_scaled` are valid for the current
core-local class. They are *ingredients*, not positive-width proofs.

**Disposition.** OPEN-CLASS-HALO is resolved as an exact proposed
definition plus a proved width-zero embedding. The cell-scale and
I-6 counting lemmas are proved mathematically. The positive-width
I-6 analytic/cancellation bridge, the two-set I-5 bound, the
new-core cover transport, and the modular analogue remain OPEN.
