# ROOTASM — from one-step observables to Root-F terms

**PROVED (snapshot).** Read-only `/home/scott/Balaban` HEAD `4f45447a64870d794b0a7a586b55709e37b51dd1` (13 October 2026). No Lean build was run. “PROVED” for a proposed implication below means the displayed mathematical deduction follows from the cited landed statement; it does not mean its proposed Lean wrapper has landed.

## T1. Site support and the physical torus

**PROVED (frozen target).** `Balaban/Frozen/Geometry/IsPolymer.lean` defines `IsPolymer d ℓ s X` as `X.Nonempty`, closure under equality of every coordinate quotient `(x μ).val / s`, and `Relation.ReflTransGen` of the edge relation `a,b∈X ∧ ∃μ, b=a+Pi.single μ 1 ∨ a=b+Pi.single μ 1`. `Balaban/Frozen/Roots/LogPartitionMultiscale.lean:logPartition_multiscale` uses `s=M L^j`, where `X` is a **finite set of fine physical sites**.

**PROVED (torus arithmetic).** `CTorus d L N₁ m₁ K = Torus d ((N₁ L^{m₁})L^K)` (`Localization/Cover.lean`). At output level `K=j`, take `m₀=1`, `M=L^{m₁+1}`, and `ℓ=q M L^K`: setting `N₁=qL` represents every admissible physical torus and satisfies `L∣N₁`. At the final output `K=k_f+1`, the landed fixed-`L=3` tower also assumes `5<N₁` and `k≥1`. It therefore excludes the smallest admissible torus `q=1` (`N₁=3`) and the base output `K=1`; it includes `q≥2`. For general `L`, `q=1` fails `5<N₁` exactly when `L≤5`. These are hypothesis exclusions, not failures of the torus representation.

**OPEN (small torus/base).** Root-F quantifies over *every* `ℓ` divisible by `M L^{k_f+1}`. Supply the physical step theorem for `N₁=L` (or a separate small-torus proof) and a base-step theorem for `k=0`/`K=1`. The latter is Proposition IV.4.3 in `notes/phase1/LF-RECONSTRUCTION.md`, Definition IV.5.2; a `k≥1` theorem alone cannot discharge it.

**PROVED (step domain).** `SmallField/Def6Terms.lean:IsPolyDom` requires a nonempty set, a chosen cover by aligned overlapping cubes, and nearest-neighbour site-path connectivity. `Localization/PolymerGeometry.lean:Nbr` is definitionally the edge relation in frozen `IsPolymer`; `Fluctuation/CubeSystem.lean:sitesOf` unions the aligned cells of side `a=cellSide L 1 m₁ K=L^{K+1+m₁}=M L^K`. `Localization/PolymerGeometry.lean:cellSide_dvd`, `mem_box_cbase`, and `cbase_eq_of_mem_box` provide the cell partition when `L∣N₁`.

**OPEN (exact bridge lemma; no such landed declaration was found).** For `d,L,N₁,m₁,K`, `[NeZero L] [NeZero N₁]`, `hN:L∣N₁`, `T′:Finset (CubeB (d:=d) (L:=L) (N₁:=N₁) (m₁:=m₁) (K:=K) 1 K Set.univ)`, and `hpoly:IsPolyDom 1 K (sitesOf T′)`, prove
$$\operatorname{IsPolymer}\ d\ ((N₁L^{m₁})L^K)\ (L^{m₁+1}L^K)\ \bigl(\operatorname{Finset.univ.filter}(x\in\operatorname{sitesOf}T′)\bigr).\tag{B1}$$
The filtered finite set has precisely the sites of `sitesOf T′`. Nonemptiness and site-path connectivity follow from `hpoly`; block closure follows because each member belongs to an aligned side-`a` cell, and equality of coordinate quotients by `a` identifies that cell. The cited partition lemmas and the `Nbr` definition are landed; this final finite-set bridge is OPEN.

**OPEN (fine observable site).** The support clause of `Inhabited/ObsFamilyJoint.lean:obsFamily_full_fromTower` says a nonzero coefficient has `rootCube (blockIndex y)∈T′` and `IsPolyDom 1 K (sitesOf T′)`. `Fluctuation/RootPavingMap.lean:rootSite_mem_sitesOf_iff` proves membership of `rootSite(blockIndex y)`, not yet the needed `y∈sitesOf T′`. Prove `mem_sitesOf_of_rootCube_blockIndex`: under `L∣N₁`, `rootCube(blockIndex y)∈T′ → y∈sitesOf T′`. Indeed `rootSite_blockIndex` and `pow_dvd_cellSide` put `y` and its root site in the same side-`a` cell, which lies in `sitesOf T′`. This is the root clause `x∈X` with `x=y`.

**PROVED (lattice convention).** `SmallField/Def6Terms.lean` defines all terms on the fine `CTorus`; scale-`j` cubes are represented by aligned subsets of those fine sites. `notes/phase1/LF-RECONSTRUCTION.md` IV.5.2 says old localized `ℳ^{(j)}` are retained after creation (P4 (1.8)). For a fixed physical `ℓ`, their domain `X` is the same subset of physical sites at later steps; it is not a lift of a coarse-site set. Lean still needs equality/transport between the level-dependent `CTorus` types and proof that the retained coefficient and finite site set agree under it.

**OPEN (transport).** The preceding cross-step physical transport and its torus-coherent version are not furnished by the one-step `sitesOf` lemmas. They belong to the flow and TORUSCOH2 interface.

## T2. Conversion of the one-step rate

**PROVED (landed inputs).** `Fluctuation/SizeModG1.lean:G1_card` gives, for `hY:IsDj 1 j Y` and `L∣N₁`, with `a=cellSide L 1 m₁ j=M L^j`,
$$|Y|\le c_1(d,L)a^d(1+\operatorname{sizeJ}_j(Y)).$$
`Fluctuation/MarkFibreSitesOf.lean:markFibre_sitesOf` gives `IsDj 1 K (sitesOf T′)`, `dExt T′=sizeJ 1 K (sitesOf T′)`, injectivity of `T′↦sitesOf T′`, and a single-fibre regrouping with **no rate loss**.

**PROVED (exact inequality).** If `κ>0`, `λ≥c₁(d,L)κ`, and `sizeJ(Y)≥0`, then `κ|Y|/a^d≤λ(1+sizeJ(Y))`; hence
$$e^{-\lambda\operatorname{sizeJ}(Y)}\le e^\lambda e^{-\kappa|Y|/a^d},\qquad B e^{-\lambda\operatorname{sizeJ}(Y)}\le B e^\lambda e^{-\kappa|Y|/a^d}\quad(B\ge0).\tag{R}$$
Here `λ` is nonnegative since `c₁(d,L)>0`. Thus the exact per-term prefactor is `C=e^λ`, or `B e^λ` when `B` is included.

**OPEN (Lean wrapper `rootRate_of_sizeJ`).** State it with `hN:L∣N₁`, `hj:j≤K`, `hY:IsDj 1 j Y`, `κ>0`, `λ≥c1 d L * κ`, `B≥0`, `a=cellSide L 1 m₁ j`, and conclude the second inequality (R) with `Y.ncard` and `((a:ℝ)^d)`. Use `G1_card`; `sizeJ=treeLenCovOne`; the nonnegativity of tree length; `Real.exp_le_exp`. This lemma is independent of the RG induction.

**PROVED (what the root asks).** Root-F's identity is a finite sum over all `X:Finset (Torus d ℓ)` and has a bound on **each** `T ℓ j x X g`; it asserts no separate absolute-convergence or sum-over-`X` estimate. Its locality clause is an equality for each coefficient, also without summability. Therefore no polymer entropy loss is needed for (R) or the injective `sitesOf` regrouping.

**PROVED (different later loss).** At the final scale, `LF-RECONSTRUCTION.md` IV.5.2–5.3 groups many domains `Y` with the same covering polymer `\bar Y=X`; its recorded bound `2^{L^d|X|/a^d}` consumes decay. That loss concerns the final `R_n` and large-field `P` terms, not the one-step observable fibre of `markFibre_sitesOf`.

## T3. The coefficient which Root-F needs

**PROVED (exact frozen form).** On `∑_{y,i}‖g(y,i)‖<1`, Root-F asserts
$$\operatorname{Complex.log}\frac{\operatorname{partitionFunction}(d,N,\ell,\beta,\nu,h,g)}{\operatorname{partitionFunction}(d,N,\ell,\beta,\nu,h,0)}=\sum_{x,i}g(x,i)h_i+\sum_{j=1}^{k_f+1}\sum_x\sum_{X:\operatorname{Finset}(\operatorname{Torus}d\ell)}\sum_i g(x,i)T(\ell,j,x,X,g)_i.$$
The single `T` is chosen before `ℓ` and `g`; it returns a **vector coefficient**, can depend analytically and nonlinearly on the whole source, and is multiplied by `g(x,i)` in the identity. A scalar `g·T` is not itself the value of `T`.

**PROVED (paper construction as recorded).** `LF-RECONSTRUCTION.md` Definition IV.5.2 identifies ordinary `1≤j≤k_f` terms with `ℳ^{(j)}(x,X;h,h,g)`. At `j=k_f+1` it adds `ℳ^{(k_f+1)}_0` and `∫_0^1 ∂_{g(x)}f(Y;h,tg)dt` for final `R_n` and `P` polymer activities grouped by `\bar Y=X`; `k_f=0` uses its separate Proposition IV.4.3. Thus `T_j` is a source-dependent coefficient, not merely its value or derivative at `g=0`. `notes/phase1/SCOPE.md`, `STEPSTATEMENT3.md`, and `TSTEPID.md` describe the one-step zero-class ingredient of this construction, not the completed multiscale identity.

**PROVED (landed source channel).** `Fluctuation/StepComplexOut.lean:E0C` has no source argument; its `F0C(g)` and `M0C(g)` do. `Fluctuation/StepComplexSource.lean:F0C_eq_pair_zeroClass` gives `F0C(g)=β_U^{-1/2}∑_{y,i}g(y,i)M0C(g,y,i)` under its nonvanishing premises. `Inhabited/ObsFamilyJoint.lean:obsFamily_full_fromTower` gives, for one site/component family chosen before the source, `M0C(g,y,i)=√β_U∑_{T′}obsCoeffParam_{y,i}((rawOf D,g),T′)` at chart data. The two square-root factors cancel. `labelActFamilyOn … e u` is an auxiliary source-dependent activity used to construct these coefficients; it is not an extra `T_j` by itself. `FcompAtC` contains the retained old source pairing and is not part of the new `M0C` coefficient.

**REFUTED (landed W571 claim at this HEAD).** No declaration named `stepIdentity_zeroClass_fibre_fromTower` occurs in `Balaban/` at this snapshot. `notes/phase1/TSTEPID.md` states it as an OPEN target. Its required exponent includes `-Eppp(C) nU` even for `zeroClass`; dropping this term is incorrect. The landed `prop26C_zeroClass_of_activity`, `F0C_eq_pair_zeroClass`, observable family, and energy-family pieces do not yet constitute the cited joint identity.

**OPEN (candidate new zero-class coefficient).** Fix a *constant-`h`* chart datum `D_h`, a physical torus `ℓ=(N₁L^{m₁})L^K`, `K=k+1`, and one compatible choice of observable coefficient families for all `x,i` before `g`. Put `Y(T′)=sitesOf T′`, `C_{x,i}(g,T′)=obsCoeffParam_{x,i}((rawOf D_h,g),T′)`. For a legal root polymer `X` and `x∈X`, set
$$T^{\rm new}_K(x,X,g)_i=\sum_{T′:\,Y(T′)=X} C_{x,i}(g|_X,T′).\tag{C}$$
Here `g|_X` means extension by zero outside `X`. If its `ℓ¹` norm is at least one, define (C) to be zero; define it as zero for illegal `(K,x,X)` too. On the root's source ball this equals the coefficient at `g`. This restriction-based extension gives the frozen locality for **all** pairs `g,g′`, including those outside the ball. By `markFibre_sitesOf`, each nonzero fibre in (C) is a singleton.

**OPEN (candidate's clauses).** The new fine-site lemma and (B1) give support `x∈X` and `IsPolymer`; `obsFamily_full_fromTower` gives source locality on `sitesOf T′`, analyticity on `physVq` with `q=1`, and a `(B₁+B₂)e^{-λdExt T′}` rate for its *same* family; `markFibre_sitesOf` plus (R) give the root per-term rate `B e^λ e^{-κ|X|/a^d}`. Its value theorem plus `F0C_eq_pair_zeroClass` gives the new `∑gT` term. The sharp `obsPrefactor` bound of a pointwise chosen coefficient cannot automatically replace the joint family's bound; the bound must be proved for the family used in (C). TORUSCOH2 must identify (C) on two admissible tori.

**OPEN (full exponent and logarithm).** To use (C) in Root-F, the one-step identity must join the observable and energy families, preserve the retained `FcompAtC` term and `-Eppp nU`, subtract the zero-source exponent, identify the bare `∑g h` at the constant datum, and select the principal logarithm on the source ball. The final `R_n/P` increments and earlier `ℳ^{(j)}` terms then supply the rest of `T`; none follows from (C) alone.

## T4. Exports required of a one-step theorem

**OPEN (uniform family and domain).** Export one family for every `(x,i,T′)` selected before `g`, with its physical value, nonzero support, analytic dependence on the unscaled source on the **open** `ℓ¹` ball of radius one, and a common bound on the closed radius-`1/2` ball. `obsFamily_full_fromTower` has `q≤1` and per-site `Ev` chosen before `D,g`; package these choices across all sites/components for the fixed torus and prove the chart inclusion at `q=1`. `physInclScaled_apply` identifies the internal source as `g/β`; it does not insert `1/β` into `T`. The `√β_U` in `M0C` cancels the `β_U^{-1/2}` in `F0C` exactly.

**OPEN (indices and normalization).** Export the finite `T′↦X` regrouping, the fine-site support, and a vector-valued `(x,X,g)↦T_K(x,X,g)`; the root sum itself supplies `∑_i g(x,i)T_K(x,X,g)_i`. Add the no-source energy cancellation/normalization and the retained-source-to-bare-pairing statement in the same chosen family. Export two-torus agreement and physical index transport for old terms. The running target W571 must remain an **exponential** identity with `Eppp nU`; W571's claimed landed name and any target omitting this term need correction.

**OPEN (arbitrary root parameters).** The fixed `3,3,2` tower does not prove Root-F's `∀κ>0 ∀c₉>0 ∃L,M,β₀` or all `d≥3,N≥2`. For each requested `κ`, choose the tower decay `λ≥c₁(d,L)κ` and an amplitude `B` with `B e^λ≤c₉L^{-K((d-2)/2+δ)}`. The general selectable-`κ₀` tower and its numerical budget are needed for the full quantifiers; the geometry and rate conversion are valid at `3,3,2` now.

## T5. Bounded leaves, in dependency order

**OPEN 1 (≤220 lines, now).** `sitesOf_isPolymer`, precisely (B1): reuse `IsPolyDom`, `Nbr`, `sitesOf`, `cellSide_dvd`, `mem_box_cbase`, `cbase_eq_of_mem_box`; no tower dependency. Prove generally, then instantiate at `3,3,2`.

**OPEN 2 (≤140 lines, now).** `mem_sitesOf_of_rootCube_blockIndex`: reuse `rootSite_blockIndex`, `rootSite_mem_sitesOf_iff`, `pow_dvd_cellSide`, cell partition. No induction; valid at `3,3,2`.

**OPEN 3 (≤100 lines, now).** `rootRate_of_sizeJ`: reuse `G1_card`, nonnegative `sizeJ`, and exponential monotonicity; then `markFibre_sitesOf` identifies `dExt=sizeJ`. No induction; valid at `3,3,2` for every `κ` whose requested `λ` is available.

**OPEN 4 (≤280 lines, after 1–3).** A *definition-free* fixed-torus theorem: assume a cube coefficient family `C_{x,i}(g,T′)` with uniform support, source locality, analyticity, and `‖C‖≤B e^{-λdExt T′}` on the unit chart; conclude existence of a site/polymer vector family `U(x,X,g)` satisfying root support, global source locality (by restriction), analyticity on the open ball, and `‖U‖≤B e^λ e^{-κ|X|/a^d}` on the half-ball, provided `λ≥c₁κ`. Use the singleton fibres of `markFibre_sitesOf`; do not refer to the RG induction. Its abstract theorem and fixed-`3,3,2` instance can start now. A physical instance with the sharp root prefactor depends on the joint-family numerical estimate and, for arbitrary `κ`, the general tower.

**OPEN 5 (≤220 lines, after 4 and the step identity).** The fixed-torus source-pairing assembly: use the *same* family in leaf 4, `M0C`'s value theorem and `F0C_eq_pair_zeroClass` to prove `F0C(g)=∑_{x,X,i}g(x,i)U(x,X,g)_i`; keep `FcompAtC`, `Eppp`, and energy in the surrounding exponent. The full Root-F identity additionally needs the earlier-scale flow, final `R_n/P`, small-torus/base steps, and the principal-log and two-torus theorems.

**PROVED (confidence).** High for the torus arithmetic, exact frozen clauses, source normalization, and rate inequality; medium for the proposed finite-set bridge proof and leaf sizes; low for closing the full root until the explicitly OPEN step, flow, small-torus, and coherence inputs land. The read-only checkout was not edited.
