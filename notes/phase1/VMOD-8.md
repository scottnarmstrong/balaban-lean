# The cut pointwise estimate at a mixed physical wall

**12 October 2026.** This note addresses `followup_r8.txt` and only the target OPEN-NC3-MIXED-WALL from `VMOD-7.md` (5.1). The requested dichotomy is **not resolved**: I have neither a proof of the uniform high-source-scale cut pointwise and Hölder estimates nor a counterexample to the landed `CubeBlockBounds` field. In particular, this note does not assert (A) or (B). It gives a complete uniform theorem for source scales $j'\le2$, identifies the precise high-scale obstruction, and reduces the Laplacian part of the general theorem to one open pointwise assertion. All cited declarations below were checked in the landed files; nothing under `/home/scott/Balaban` was edited.

## 1. The target and the geometry it actually needs

Fix $d,L\ge3$, $K\ge1$, a generating set $H$ on the torus of side $(N_1L^{m_1})L^K$, admissible weights $a$, mass $0\le\nu$ with $\nu L^{2K}\le1$, and separation
$$2d\log L\le \frac{\operatorname{agmonRate}(d)}{16}(\varrho-1).\tag{1.1}$$
These are exactly the analytic fields of landed `Dec2.OpSetting` in `Balaban/Localization/Decoupled2.lean`; the parameter cube $q$ comes from the *common* cover $C=\operatorname{coverOf}F^\sharp$, while the operator and its physical Dirichlet boundary come from $H\in\{H^-,H^\partial\}$. The pair geometry supplies `Dec2.CoverGeom.blockAligned q`, hence
$$\Lambda_q=\operatorname{intBox}q\quad\text{is `BlockAligned H`, and}\quad
\mathrm{cut}_q=\operatorname{cubeCut}H\Lambda_q\quad\text{is `CutAligned H`}.\tag{1.2}$$
The second implication is landed `Multiscale/CutOperator.lean cubeCut_aligned`. The potential condition `AdmPot H α` is exactly
$|\alpha(x)|\le\operatorname{coerciveConst}(d)/(2\ell_H(x)^2)$, by `Localization/Decoupled.lean AdmPot`.

Let
$$u_q=\operatorname{zeroExt}_{\Omega_1(H)}
 \bigl(H_{\mathrm{cut}_q}(\alpha)^{-1}f\bigr),\qquad
\gamma=\operatorname{agmonRate}(d)/2,\qquad
F_{j'}=L^{2j'}M_f.\tag{1.3}$$
Here $1\le j'\le K$, $y'\in H.\mathrm{layer}(j')\cap\Lambda_q$, and $f$ is supported in the **complete $H$ $j'$-block** of $y'$, with $|f|\le M_f$ and $M_f\ge0$. `Decoupled.lean cubeH` is definitionally this cut operator. The exact full target is `Localization/DecoupledCube.lean CubeBlockBounds H a ν α q Kc`: value at every $x\in\Omega_1(H)\cap\Lambda_q$; a forward difference at $x$ when *every* forward neighbor lies in $\Lambda_q$; and the full symmetric Laplacian when every forward and backward neighbor lies there. All three have right side $K_c e^{-\gamma d_H(x,y')}F_{j'}$, where the exponential is the landed `decay` of `H.pathDist`. The two-center target is `Localization/DecoupledCubeHolder.lean CubeBlockHolder` with its exact $\theta$, center, displacement, retained-neighbor, and layer-order quantifiers. Its constant is also required to depend only on $d,L$.

The physical Dirichlet boundary is the complement of $\Omega_1(H)$ in the zero extension. The artificial cube face deletes only the crossing bonds of $\mathrm{cut}_q$ and is Neumann. These two boundaries can meet. `ReflectedGeneratingSet.lean FoldSetting`, used in `NC3.lean`, requires its original cube and one-site collar in $\Omega_1(H)$; therefore the landed fold theorem is unavailable at such a meeting. Reflection across that face without reflecting the physical hole would change the operator. The fact that $\Lambda_q$ is block aligned does *not* imply the fold hypotheses.

## 2. A complete uniform result for bounded source scale

Set
$$c_s(d,L)=\frac{13L^{d+1}}{\operatorname{poincareConst}(d)},\qquad
K_s(d,L)=\max\{c_s(d,L),,e^{\operatorname{agmonRate}(d)d}(1+4c_s(d,L))\}.\tag{2.1}$$
Both are nonnegative and independent of $K,m_0,m_1$, the torus, history, wall shape, $q,a,\nu,\alpha$. The expression $c_s$ is exactly landed `NC3Small.lean smallConst`, rewritten algebraically.

**Theorem 2.1 (proved conditional only on landed results).** Under (1.1)–(1.3), (1.2), and $j'\le2$, the three conclusions of `CubeBlockBounds.bounds` hold for this source $f$ and this cube, with constant $K_s(d,L)$, including **every** operator site of $\Lambda_q$. No condition that the physical wall avoid $\Lambda_q$ is needed. If also $x,x'\in\Omega_1(H)\cap\Lambda_q$, the forward bonds at both points in direction $\mu$ are retained, $\operatorname{layerIndex}_H(x)\le2$, and the remaining hypotheses of `CubeBlockHolder.pair` hold, its conclusion holds for this source and pair with
$$K_{h,s}(d,L)=L^3c_s(d,L).\tag{2.2}$$
There is **no** $\operatorname{layerIndex}_H(x)\le2$ premise in the full `CubeBlockHolder` field, so this is a proper partial theorem.

**Proof.** By (1.2), `cubeCut_aligned` supplies the `CutAligned` premise of landed `Localization/NC3Small.lean small_value_cut`, `small_pointwise_cut`, `small_laplacian_cut`, and `small_holder_pair_cut`. Their source support premise is precisely the complete $H$ block premise in (1.3); `AdmPot` supplies their potential premise. Inequality (1.1) implies $1\le\varrho$ and $L\le\exp[\gamma(\varrho-1)]$ because $d\ge3$ and $\operatorname{agmonRate}(d)>0$. These are the remaining separation premises. The cut solution in those theorems is definitionally $u_q$.

`small_value_cut` gives $|u_q(x)|\le c_s\operatorname{decay}(\gamma,d_H(x,y'))F_{j'}$ for **all** $x\in\Omega_1(H)$; restricting to $\Lambda_q$ proves the first clause. If $x$ and every forward neighbor lie in $\Lambda_q$, `CutOperator.lean mem_cubeCut` shows $(x,\mu)\notin\mathrm{cut}_q$ for each $\mu$. `small_pointwise_cut` gives
$$|u_q(x)|+\ell_H(x)|u_q(x+e_\mu)-u_q(x)|
 \le c_s\operatorname{decay}(\gamma,d_H(x,y'))F_{j'}.$$
Dropping the nonnegative value term proves the second clause. If both signs of every neighbor lie in $\Lambda_q$, landed `Decoupled.lean noCutAt_cubeCut` gives `NoCutAt` at $x$. `small_laplacian_cut` then gives the symmetric Laplacian with coefficient $e^{\operatorname{agmonRate}(d)d}(1+4c_s)$. Taking the maximum proves the triple with $K_s$. Finally `small_holder_pair_cut` has the two-center expression and the coefficient $L^3c_s/\theta$ under the stated layer and retained-bond conditions; the displacement restriction required by `CubeBlockHolder` can simply be retained. $\square$

This theorem is stronger than a statement restricted to the support of $\chi_q$ in its value clause. It settles every mixed-wall cube/source configuration with $j'\le2$. It does **not** settle a high-scale source inside a common-cover box that meets a physical $H$ wall. In the same-set proof of `DecoupledCube.lean cubeBlockBounds_exists`, the only non-fold case is $q.1=1$, and landed `BoxGeometry.lean layer_le_of_mem_box` makes $j'\le2$ there. For the pair $(\operatorname{coverOf}F^\sharp,H)$, that theorem cannot simply be called with $H$ and a cube index of $F^\sharp$: its `q ∈ cubeIdx H` premise is missing. Pairwise block alignment alone does not give a source-layer cap. A separate history-dependent layer comparison might yield one for some cubes, but no such comparison is used here to claim the full theorem.

## 3. Exact reduction of the remaining full `CubeBlockBounds`

The following is the single open analytic assertion needed for the **value and forward-gradient** clauses. It is deliberately stated for the actual cut and complete source block, and is required uniformly for $j'\ge3$; allowing $j'\le2$ does not change it.

**OPEN-CUT-POINTWISE-WALL.** There is a number $K_p(d,L)\ge0$ such that for every data set of §1, every $q\in C.\mathrm{cubeIdx}$ for which `BlockAligned H (intBox q)` holds, every admissible $\alpha$, every complete block source (1.3), and every $x\in\Omega_1(H)\cap\Lambda_q$,
$$|u_q(x)|\le K_p\operatorname{decay}(\gamma,d_H(x,y'))F_{j'},\tag{3.1}$$
and, whenever $x+e_\mu\in\Lambda_q$,
$$\ell_H(x)|u_q(x+e_\mu)-u_q(x)|
 \le K_p\operatorname{decay}(\gamma,d_H(x,y'))F_{j'}.\tag{3.2}$$
The constants and quantifiers have exactly the independence specified in §1. The required gradient is on a **retained** bond. A useful stronger version bounds $|u_q(x)|+\ell_H(x)\sum_{\mu:(x,\mu)\notin\mathrm{cut}_q}|\nabla_\mu u_q(x)|$; the sum must omit removed bonds. A version summing every forward difference of the zero extension is not the cut energy controlled by the landed estimates, since a removed bond can join a nonzero interior value to zero outside the cube.

**Proposition 3.1 (proved conditional on OPEN-CUT-POINTWISE-WALL).** Its constant $K_p$ yields the *full* `CubeBlockBounds H a ν α q K_c` at every mixed wall, with the explicit choice
$$K_c(d,L)=\max\{K_p(d,L),,e^{\operatorname{agmonRate}(d)d}(1+4K_p(d,L))\}.\tag{3.3}$$

**Proof.** Equations (3.1)–(3.2) give the first two fields, since the landed field asks for the gradient only under the stronger all-forward-neighbors condition. For the Laplacian field, its all-neighbors condition gives `NoCutAt` by `noCutAt_cubeCut`. Take any $z$ in the complete $H$ block of $x$. By `BlockAligned`, $z\in\Lambda_q$; by the generating-set block property, $z\in\Omega_1(H)$. Thus (3.1) applies at $z$ with coefficient $V=K_p F_{j'}$ and with its own path decay. Landed `NC3.lean laplacian_cut_bound` applies to this blockwise value premise and returns
$$\ell_H(x)^2|\Delta^D u_q(x)|
 \le e^{\operatorname{agmonRate}(d)d}(F_{j'}+4K_pF_{j'})
       \operatorname{decay}(\gamma,d_H(x,y')).$$
This is the third field with (3.3). Its proof uses landed `Multiscale/CutPointwise.lean cutOperator_eq_local`, `laplacian_eq_of_cut`, and `laplacian_bound_cut` through `laplacian_cut_bound`; those row identities retain the physical Dirichlet zero extension. $\square$

No separate new wall Laplacian estimate is needed for the landed `CubeBlockBounds` field. The real missing pointwise theorem is (3.1)–(3.2). The landed `CutPointwise.lean cut_pointwise_crude` gives instead a factor $\sqrt{\operatorname{sqNorm}f}$; on a complete $j'$-block, its available conversion to $M_f$ contributes $L^{dj'/2}$. At fixed or short $H$ path distance that factor cannot be bounded by a constant depending only on $d,L$. `NC3Small` removes it only for $j'\le2$.

The Hölder conclusion needs a **separate** assertion, **OPEN-CUT-HOLDER-WALL**: the exact `CubeBlockHolder.pair` bound for the same data, with $K_h(d,L)$ uniform for $j'\ge3$ and arbitrary eligible $x,x'\in\Omega_1(H)\cap\Lambda_q$. The low-scale theorem above supplies only $j'\le2$ and $\operatorname{layerIndex}_H(x)\le2$. `Multiscale/PointwiseHolderI.lean holder_caseI` and `PointwiseHolderMain.lean holder_bound` are formulated for the uncut `PointwiseAgmon.PtSetting.u`; their lifted local Poisson ball may cross the artificial Neumann face. A wall theorem must use a local equation that preserves the physical Dirichlet sites and treats the cut face, or a Dirichlet-compatible reflection proved at their intersections. A global gradient bound alone does not yield the stated $\theta$-Hölder scaling for neighboring centers at large $\ell_H(x)$.

## 4. Why the landed chain does not close the high-scale case

The direct route is mathematically plausible, but the following are genuine proof obligations, not consequences of the cited declarations.

1. `Multiscale/CutAgmon.lean agmon_energy_cut`, `green_G2i_cut_of_pathDist`, and `cutBlockGrad` control weighted block $\ell^2$ values and **retained** gradients for arbitrary `CutAligned` cuts. The step from these to the uniform $M_f$ pointwise bound at an operator site for $j'\ge3$ is exactly the high-scale Lemma-P mechanism. The landed `PointwiseAgmon.lean PtSetting` fixes the *uncut* inverse and its pointwise quantity includes all forward gradients. It cannot be instantiated by setting the cut inverse equal to `PtSetting.u`.
2. `Multiscale/PointwiseCase2a.lean g_bound` calls the uncut `laplacian_bound` on its whole lifted ball. The replacement `laplacian_bound_cut` requires `NoCutAt` at each point of that ball. At a cube-face site, this fails. `PointwiseLift.lean lift_mem_layers` protects the lifted ball from a physical wall at high layer, but does not protect it from the artificial face. At a physical wall and a cut corner, the case split must retain zero extension on the physical outside and omit cut bonds on the artificial outside.
3. Landed reflection in `Localization/NC3.lean` handles a cube whose doubled collar lies in the operator domain. At a mixed wall, its reflected generating set would have to remember the preimage of the physical hole; `ReflectionOperator.lean operator_intertwine` in its current hypotheses does not do this. No constant from `pointwise_cut_cube` or `holder_pair_cut_cube` can be reused there without a new intertwining and separation proof.
4. There is no demonstrated counterexample to `CubeBlockBounds` here. The loss $L^{dj'/2}$ in `cut_pointwise_crude` is a loss in the proof, not evidence that the target is false. A replacement for `Dec2.CoverBase.nc` therefore cannot be justified under option (B).

The consumer is precise: `Dec2.CoverBase.nc` in `Decoupled2.lean` requests `CubeBlockBounds` for every cover cube. `Decoupled2Dg.lean cube_weighted` calls `S.nc` once and uses **all three** fields at arbitrary points of $\Omega_1(H)\cap\operatorname{intBox}q$ to invoke `weighted_sum_bound`. A support-of-$\chi_q$ only value estimate does not instantiate that theorem. A proposed smaller consumer field would require a new proof of `cube_weighted` and its weighted sum inputs; no such replacement is proved. `CubeBlockHolder` is not a field of `CoverBase` and is not directly referenced by the landed `Decoupled2*.lean` consumers; it remains a separate requested analytic target.

## 5. Lean dependency order and status

| Order | Declaration and location | Mathematical role | Status |
|---|---|---|---|
| 1 | Landed `CutOperator.mem_cubeCut`, `cubeCut_aligned`; `Decoupled.noCutAt_cubeCut` | Identify retained forward bonds and no-cut symmetric sites from `BlockAligned`. | Proved |
| 2 | Landed `CutAgmon.green_G2i_cut_of_pathDist`, `CutPointwise.single_le_cutBlockGrad`, `NC3Small.small_value_cut`, `small_pointwise_cut`, `small_laplacian_cut`, `small_holder_pair_cut` | Theorem 2.1, including the mixed wall for $j'\le2$. | Proved conditional on these proved declarations |
| 3 | New `Dec2.cubeBlockBounds_smallSource` (roughly 80–120 Lean lines) | Package Theorem 2.1's triple for a `CoverGeom` pair, retaining the source-scale premise rather than claiming `CubeBlockBounds`. | Planned packaging; mathematics proved in §2 |
| 4 | New `Dec2.cubeBlockHolder_smallSource_lowTarget` (roughly 60–90 lines) | Package the restricted pair estimate (2.2). | Planned packaging; mathematics proved in §2 |
| 5 | New `Multiscale.cutPointwise_blockSource_wall` | Establish (3.1)–(3.2) uniformly for high source scales on a block-aligned cube cut, keeping both boundary types. Reuse `CutAgmon` and cut row lemmas; a local boundary pointwise argument is still required. | **OPEN-CUT-POINTWISE-WALL**; size unknown |
| 6 | Landed `NC3.laplacian_cut_bound` plus new `Dec2.cubeBlockBounds_of_cutPointwise` (roughly 60–100 lines) | Proposition 3.1 and the `CoverBase.nc` field, with constant (3.3). | Proved implication; the premise in order 5 is open |
| 7 | New `Multiscale.cutHolder_pair_wall`, then `Dec2.cubeBlockHolder_wall` | Full two-center estimate, respecting retained bonds and corner geometry. | **OPEN-CUT-HOLDER-WALL**; size unknown |

`Dec2.cubeBlockBounds_smallSource` and `Dec2.cubeBlockHolder_smallSource_lowTarget` are proposed names, **not** landed declarations. Orders 5 and 7 are the missing research assertions. Even a successful proof of order 5 would close `CoverBase.nc` but would not by itself close the requested `CubeBlockHolder` estimate.

**Confidence.** High for the bounded-source-scale theorem and the conditional Laplacian reduction, because their hypotheses and conclusions align directly with the cited landed statements. Moderate for the claim that the cut pointwise and Hölder estimates should hold uniformly at all mixed walls: it is a proposed theorem, not established by this note. No confidence is assigned to a numerical wall constant or a counterexample, since neither has been constructed.
