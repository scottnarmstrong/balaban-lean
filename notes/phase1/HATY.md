# HATY — paper domains and the additive rate budget

**PROVED (scope).** Read-only audit of `/home/scott/Balaban` at `ed348d4`; no Lean code or tower numeral was changed. “PROVED” below means an exact cited Lean declaration, source statement, or arithmetic consequence; it does not assert that the full step has been assembled.

## T1. The source map and its losses

**PROVED (source).** `notes/phase1/FLUCTUATION.md:73-87` defines `𝒟_j` as connected unions of aligned `π′_j` cubes of side `LMℓ_j`. Its `d^cov_j(X)` is the infimum of `M⁻¹` times the tree length in scale-`j` units, over chosen `π′_j` covers and trees inside `X` meeting every cover cube. In the modular version the cover need only contain `X∩Ω`, and `X∈𝒟_j(mod Ωᶜ)` must contain or miss each component of `Ωᶜ`.

**PROVED (source).** For a nonempty support `S` of `π_j` cubes inside `Ω`, `Ŷ(S)=S∪{components of Ωᶜ adjacent to S}`. If `Ŷ(S)` is connected, `d_Ω(S)=d^cov_j(Ŷ(S) mod Ωᶜ)`; otherwise the manuscript assigns a large *finite* `D_Ω` only for Mayer hypotheses. The latter value is not the decay size of an actual connected-cluster coefficient (`FLUCTUATION.md:82-84,97-102`).

**PROVED (source).** G4 says that a connected label `Y` with `Y∩Ω=S≠∅` satisfies `Y⊆Ŷ(S)` and `d_Ω(S)≤d^cov_j(Y)` (with modular size when `Y` is modular). It does **not** assert `d^cov_j(Ŷ(S))≤d^cov_j(S)+C` for arbitrary `S`; `S` need not itself be a `𝒟_j` domain. Thus pre-summing labels at rate `κH` over fixed `S` spends `κ0`, leaving `κH−κ0` in `d_Ω(S)` (`:86-100,505-535`).

**PROVED (source).** Theorem 3.4 spends a further `κ0+3/2` in MY and `κ0+c1` in PE-L: total `3κ0+c1+3/2`. Theorem 3.1(a) uses `κa=κU−3κ0−c1−3/2`, `κU=2κ−1`; (b) additionally spends `κ0+1` for the connected union of kernel labels and marked supports, yielding `κb=κa−κ0−1` (`:540-555,569-578,681-694`). These costs already include the source's label presummation; they must not be paid a second time for the cube-to-domain index change.

**PROVED (constant distinction).** The manuscript's G1 chooses `c1=(2L+3)^d=729` at `d=L=3` (`FLUCTUATION.md:89-95`), while the Lean `c1 3 3=3375` is conservative (`Fluctuation/SizeModCore.lean:159`; `Inhabited/RenormDetFibreTower.lean:123-124`). The Lean ledger below uses **3375** throughout.

**REFUTED (proposed L subsidy).** The source does not use a factor `L` in `S↦Ŷ(S)`: both are at level `k+1`, and G4 supplies the comparison directly (`:82-100,505-535`). `Localization/TreeLength.lean:528` gives `scaleW(L,m₀,m₁,j+1)=scaleW(...,j)/L` for fixed bonds, but that identity is not a size comparison for the new output map.

## T2. The present Lean carriers

**PROVED.** `CubeSystem.lean:36-48` defines `CubeB m₀ j Ω` as aligned boxes of side `cellSide=L^(j+m₀+m₁)` (`Localization/PolymerGeometry.lean:237`). For the zero class `m₀=1`, `j=K=k+1`, `Ω=univ`: the cubes have side `3^(k+2+m₁)` in fine sites, exactly `π′_{k+1}` rather than the smaller `π_{k+1}` blocks. `sitesOf T` is their union. `dExt T` is `dOmega 1 K univ (sitesOf T)` converted to reals when finite, and `Mbig=|CTorus|²+1` when infinite (`CubeSystem.lean:103-110`).

**PROVED.** `SizeModDefs.lean:46-66,87-116` defines `IsDj` as nonempty, site-connected, covered by contained `π′_j` cubes; `dcovModE` as the normalized infimum over admissible covers and trees; `Yhat`; and `dOmega`, which is `⊤` for disconnected `Yhat`. `SmallField/Def6Terms.lean:95-104` defines `IsPolyDom` with a chosen `π′_j` cover and `sizeJ=treeLenCovOne`; `Def6BridgeGeom.lean:123` proves `IsPolyDom→IsDj`. At `Ω=univ`, `Yhat univ X=X` (`RootActiveSize.lean:66`) and `sizeJ X=dcovMod univ X` on the active domain (`RootActiveSize.lean:93-107,134-137`). The source's finite disconnected `D_Ω` and Lean's `⊤/Mbig` are different off active support, immaterial to this whole-lattice coefficient map.

**PROVED.** `e1Dom` is the `polyDom` family of root-cover domains (`Inhabited/E1LabelsBudget.lean:38-51`); `obsDomains` is `polymerDomains` from the sharp hat cover (`Fluctuation/ObsMarksAssembly.lean:181-192`). Their members are `IsDj`; they are input label families, not the final `T↦Y` map. `bridgeFamily` consists of bridges of contributing labels, and when the root cube belongs to an `IsDj` label its bridge is that same label (`MarkedRootGeometry.lean:370-390`). `thickSet Y=Y∪resDep(Y)` is a *datum-dependency* enlargement (`Localization/I5Local.lean:82-84`), not `Yhat` and not a new `𝒟` index.

**PROVED.** For a coefficient supported where `IsPolyDom 1 K (sitesOf T)`, `sitesOf T∈𝒟_K` and `dExt T=sizeJ 1 K (sitesOf T)` exactly (`RootActiveSize.lean:134-137`, `MarkFibreSitesOf.lean:39-69`). Thus the comparison is `size(Y(T))=dExt T`, with multiplicative constant **1** and additive constant **0**. No thickening or `detCollarHull_sizeJ_le` is involved. `Thm31aPolymer.lean:76-105`, `GsumActiveParam.lean:78-110`, and `Thm31bKernelSupport.lean:141ff` supply the relevant energy, mark, and canonical observable support clauses under their stated hypotheses.

## T3. The exact domain map and fibre

**PROVED.** Choose `Y(T):=sitesOf T=Yhat univ (sitesOf T)` on nonzero coefficients. `MarkFibreSitesOf.markFibre_sitesOf` proves `IsDj Y(T)`, `sizeJ Y(T)=dExt T`, equivariance under paving symmetries, and injectivity of `T↦sitesOf T` when `L^m₀∣N₁` (`:39-85`). Consequently `#{T:Y(T)=Y}≤1`; the regrouped coefficient `e_Y:=∑_{sitesOf T=Y}e_T` has the *same* bound `B exp(-λ sizeJ Y)` and exact total-sum identity (`:39-104`). Its entropy cost and rate loss are both **0**. Include zero terms on unused `𝒟_K` domains if a larger finite index family is chosen.

**PROVED (rates).** Marks have `λ=κ′=(3/2)κdec+κ0+1` (`StepTower.lean:34-39`), hence surplus `κ0+1` over `κout=3κdec/2`. The observable coefficient has `λ=min(κh,κ′)−κ0−1=κout`, with `κh=2κdec`; therefore it has **zero** surplus for any positive-slope index loss (`Thm31bResum.lean:63-73`, `StepOutputPhysical.lean:52-73`). The singleton fibre consumes none of either surplus.

**OPEN (record completion).** The fibre lemma is a norm/sum/geometry result, not an `IsLocExp` constructor: parameter analyticity, exact locality on `sitesOf T`, root membership, reality/symmetry, and uniform bounds over a common complex domain must be carried from the canonical families. In particular, a premise giving only agreement on `thickSet Y` does not imply `IsLocExp.local_` on `Y`; this needs the paper's final-domain locality argument or a matching target interface (`Thm31CoeffA.lean:100-113`; `RenormExpCauchy.lean:87-108`).

## T4. The later renormalization cover

**PROVED (source).** Theorem 3.1(g),(h) and its proof (`FLUCTUATION.md:416-419,619-640`) use `𝒟_{k+1}` localization terms: (g) combines (a) with localized `C_i` and old-energy differences; (h) combines (b) with `δφ` and old-observable differences. No new stated fibre quotient of the (a),(b) domains appears there; their rates are `κa` and `κb` or better. Thus the source prescribes *common domain-indexed expansions*, not a forced map to `renYs`.

**PROVED (Lean).** `renYs` is the finset image of domains `Y[𝒞]` from connected families of localization cover labels and `renDY=treeLenCov` (`Localization/RenormLocFibre.lean:95-125`). The determinant route maps a polymer `X` meeting the root neighbourhood to `renFibreMap X∈renYs`, with `renDY(ΦX)≤A sizeJ X+A`, `A=renDetA 3 3 1=93,767,625`, and fibre count `≤exp(3375 log2)exp(3375 log2·renDY Y)` (`RenormDetFibreMap.lean:177-203,309-333,383-400`; `RenormDetFibreTower.lean:123-124`). Its sufficient output rate is `λ/A−3375 log2` (`RenormDetFibreMap.lean:555-574`).

**REFUTED (current fibre for marks/observable).** With `λ=κ′`, `κ′/A−3375 log2<κout`; with `λ=κout`, `κout/A−3375 log2<κout` for `κout>0`. The former follows from `κ′=κout+κ0+1`, `κdec=100(κ0+3375+10)`, `κ0≥0`; the latter is immediate. So the landed `renRegroup_norm_le` cannot produce the target (g),(h) rate for either lane. This refutes that *proved estimate*, not every conceivable sharper geometric map.

**OPEN (interface choice).** Keep the (a),(b) terms on their actual `IsDj` site domains. To combine them with determinant/`C_i` terms by `IsLocExp.add`, build a common finite `Ys` containing all nonzero domains and re-express every lane on that `Ys` with zero extension; use one `Dom`, radius, `dY=sizeJ 1 K` and rate `κout` after justified monotonicity. `IsLocExp.add` requires those parameters *definitionally identical* (`RenormExpCauchy.lean:87-117`). The current determinant `renYs/renDY` record does not meet that interface; either retain/reprove its pre-fibre polymer-domain terms at high determinant rate, or prove a new rate-preserving joint cover. The paper's (g),(h) do not by themselves certify either Lean construction.

## T5. Additive ledger and bounded Lean leaves

**PROVED (ledger).** Start `κH=2κdec−1`. Pay `κ0` label presummation, `κ0+3/2` MY, `κ0+3375` PE-L: `κa,Lean=2κdec−1−3κ0−3375−3/2`. The pinned `StepTower.κdec_eq` and `κ′_eq`, rather than `rate_rel` alone, give `κ′≤κa,Lean`: the slack is `0.5κdec−4κ0−3378.5=46κ0+165871.5≥0` (`StepTower.lean:34-66`). The energy mark remains at `κ′` after the singleton fibre; the determinant is separately paid by `det_rate` and its existing threshold (`StepTower.lean:77-79`; `RenormDetFibreTower.lean:139-161`).

**PROVED (ledger).** For (b), the first-order kernel/mark rate `min(2κdec,κ′)` pays `κ0+1` in the connected-union resummation; at these tower values `κ′≤2κdec`, so the result is exactly `κout=1.5κdec`. The remainder starts at `κ′` and weakens to `κout`. `T↦sitesOf T` pays zero. The paper's (g),(h) use the (a),(b) rates together with `2κ−1` or `2κ` for the other terms; the Lean target may weaken each to `κout` if the common domain interface is proved (`FLUCTUATION.md:628-640`; `StepOutputPhysical.lean:52-85`). No `StepTower` numeral need change.

**OPEN (leaf 1, ≤300 lines).** `Fluctuation/MarkCoeffSites.lean`: for canonical `e1CoeffC` and `gsumCoeff` with the landed support hypotheses, define `e_Y=∑_{sitesOf T=Y}e_T`; prove sum identity, `Y∈IsDj 1 K`, root membership, `‖e_Y‖≤B exp(-κ′ sizeJ Y)`, symmetry. Consume `Thm31aPolymer`, `GsumActiveParam`, `MarkFibreSitesOf`, `RootPavingMap`.

**OPEN (leaf 2, ≤300 lines).** `Fluctuation/ObsCoeffSites.lean`: same statement for canonical `obsCoeff`, with `κout` and the exact `Thm31bKernelSupport` common-witness support premise. Consume `MarkFibreSitesOf`, `Thm31bResum`, `Thm31bKernelSupport`; prove the finite sum and no remainder.

**OPEN (leaf 3, ≤300 lines).** `Inhabited/SitesCoeffLocal.lean`: for two physical parameters agreeing on `Y=sitesOf T`, prove equality of the canonical energy/observable `e_T`; then analytic-on-common-domain and symmetry statements for `e_Y`. State explicitly any extra `thickSet Y` dependence that prevents the claimed `IsLocExp.local_`. Consume `ParamCarrierLocal`, `Thm31CoeffA/B`, and the landed physical parameter families.

**OPEN (leaf 4, ≤300 lines).** `Fluctuation/LocExpCommonDomains.lean`: zero-extension lemma from an `IsLocExp` on `Ys₁` to `Ys₁∪Ys₂` with a common `Dom,r,dY,κ`, plus `sum_eq`, analytic, local, and bound. No size/fibre estimate is hidden in this leaf. Apply `IsLocExp.add` only after the parameters match.

**OPEN (leaf 5, ≤300 lines).** `Inhabited/RenormPaperDomains.lean`: produce the determinant and `C_i/δφ` records on the chosen common `IsDj` domains at `κout`, or state and prove a different fibre inequality `renDY(ΦX)≤sizeJ X+C_add` with fibre exponent slope `≤λ−κout` and locality. The existing `renYs` map has neither required bound for marks nor observable; this is the decisive integration gate.

**PROVED (code disposition).** Keep the determinant `DetCollarHull`, `RenormDetFibreMap`, and `RenormDetFibreTower` as its proved lane; they are not consumed by leaves 1–3. The observable collar and scalar non-polymer remainder in `Inhabited/Thm31bPolymer.lean` are unused for this output route. No observable collar extension or tower numeral edit is justified by the domain map.

## T6. Questions for Scott and the author

**OPEN (question 1).** “For the whole-lattice version of Theorem 3.1(a),(b), may the output be indexed directly by the nonzero connected `π′_{k+1}` site unions `sitesOf T`, with `d^cov_{k+1}=sizeJ` and zero terms on the other `𝒟_{k+1}` domains? This is the exact Lean coefficient support.”

**OPEN (question 2).** “In (g),(h), must every new term use the particular cover domains `Y[𝒞]` (`renYs` in Lean), or is any finite family of `𝒟_{k+1}` domains containing the term supports acceptable? If the particular cover is required, what source inequality controls its size by the marked support with coefficient one and only an additive cost?”

**OPEN (question 3).** “Does final locality in (a),(b) mean dependence on the set `Y` itself for all raw data, or on a dependency thickening such as Lean's `thickSet Y` before the composition? Please identify the precise locality statement used when adding (a)/(b) to (g)/(h).”

**PROVED (confidence).** High confidence in the exact `sitesOf` domain/size/singleton-fibre conclusion and the no-surplus obstruction for the current `renYs` inequality; medium confidence in the proposed common-domain assembly until the analytic/locality bridge and author interface are fixed. No full Lean build was run for this design report.
