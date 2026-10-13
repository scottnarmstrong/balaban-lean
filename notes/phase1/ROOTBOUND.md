# ROOTBOUND — the frozen root's rate versus the landed step

**PROVED (snapshot).** I read `/home/scott/Balaban` at commit `6fa45d77032cb193d5b9c8c760c175fa980f05ec`; this note changes no file there. “PROVED” means a cited Lean statement or an explicit deduction from its definitions, not a proof of the frozen root. No build was run.

## T1. Quantifiers and units

**PROVED.** `Balaban.logPartition_multiscale` in `Balaban/Frozen/Roots/LogPartitionMultiscale.lean` has the following order:
`∀ d,N (3≤d) (2≤N), ∃δ>0, ∀κ>0, ∀c₉>0, ∃L,M (2≤L) (1≤M), ∃β₀, ∀β≥β₀, ∀ν (0<ν≤1), ∀h (‖h‖=1), ∃kf, ∃T, ∀ admissible ℓ, ∀j,x,X,g, ...`.
The chosen `kf` obeys `L^kf √ν ≤ L` and `1/2 ≤ L^(kf+1) √ν`; admissibility means `M*L^(kf+1) ∣ ℓ`. The same `T` is chosen before the admissible torus and before `g`, and is compared across any two admissible tori. Thus `L`, `M`, and `β₀` may depend on `d,N,κ,c₉`; `δ` cannot depend on `κ,c₉`. The root does **not** quantify over every `L`.

**PROVED.** For `j∈Finset.Icc 1 (kf+1)` and `∑ y, ∑ i, ‖g y i‖ ≤ 1/2`, the exact root bound is
`‖T ℓ j x X g‖ ≤ c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d)`.
`X.card` counts fine lattice **sites** of `Torus d ℓ`, not blocks. `IsPolymer d ℓ (M*L^j) X` (`Frozen/Geometry/IsPolymer.lean`) requires a nonempty union of the side-`M L^j` blocks, connected by nearest-neighbour site paths; for such a union the quotient `X.card/(M L^j)^d` is its block count. The identity sums over **every** `X : Finset (Torus d ℓ)`, with terms zero off `j∈[1,kf+1]`, `x∈X`, and `IsPolymer`. Locality, source analyticity, and the two-torus equality are additional clauses of the same `T`.

**PROVED.** The source record `notes/phase0/surface-v1-for-approval.md` S0-Q05 and `notes/phase0/surface-v1-audit.md` C.3, F-6 transcribe P1 p. 118 and P4 (H.4), p. 677 as allowing an arbitrarily prescribed decay rate with a subsequent choice of `M`. The frozen anchor places `κ,c₉` **before** existential `L,M,β₀`; it is at least this precise assertion, not a theorem for all large prescribed `L`.

## T2. What the one-step rate measures

**PROVED.** `Localization.cellSide L m₀ m₁ j = L^(j+m₀+m₁)` (`PolymerGeometry.lean`), while `SmallField.Def6.sizeJ m₀ j Y = treeLenCovOne m₀ j Y` (`Def6Terms.lean`). The `obsFamily_full_fromTower` family has a bound `(B₁+B₂) exp(-λ dExt T')`; `obsFamilyRate_eq_tower` gives `λ=3κdec/2`. On active cube sets `RootActiveSize.isPolyDom_and_dExt_eq_sizeJ` gives `dExt T' = sizeJ m₀ j (sitesOf T')`. With its fixed `m₀=1` and output `j=k+1`, the matching root block side is `M L^j` with **`M=L^(m₁+1)`**, not `L^m₁`.

**PROVED.** The landed counting direction is `SizeModG1.G1_card`: for `IsDj m₀ j Y`, divisibility `L^m₀ ∣ N₁`, and `j≤K`, `Y.ncard ≤ c1 d L * (cellSide L m₀ m₁ j)^d * (1 + sizeJ m₀ j Y)`. Here `c1 d L=(3(2L-1))^d` (`SizeModCore.lean`), independent of `m₁`. Thus, if `n=Y.ncard/(M L^j)^d` and `λ≥c1(d,L)κ`, then `exp(-λ sizeJ(Y)) ≤ exp(λ) exp(-κ n)`. A later entropy loss `E` requires `λ-E≥c1(d,L)κ`. This is a proved *conditional conversion*, not yet a Lean bridge from `IsDj` to frozen `IsPolymer` or from the physical coefficient to `T`.

**REFUTED.** “`treeLenCovOne` is at least `n−1` for `n` scale-`j` cells” is false as the needed general statement: `ChosenOne` uses overlapping cubes of side `L*cellSide`, and one point may meet several cubes. The cited landed bound has factor `c1(d,L)` and an additive `1`. `Theorem42Geom.treeLenCovOne_box` also gives length zero for a whole side-`L*cellSide` cube. The `n−1` picture applies to a different cell-spanning model.

**PROVED.** In `Inhabited/StepTower.lean`, `κ0=aEnt 3 3+2`, `κdec=100(κ0+c1 3 3+10)`, and `κ'=3κdec/2+κ0+1` are **pinned**. `exists_stepTower κmin` holds for every `κmin`, but its field `κmin_le` says only `κmin≤κ`, the interpolation rate. `LevelPairGeneral.tower_core_rates_general` chooses `κ` at least `κmin` and `m₁` large enough that `cstarX d L * exp(N0 d L * κ) ≤ L^m₁`; `StepOutputConsts.stepOutput_consts_exists_ge_general` likewise raises `κ` while pinning `κdec`. `κ_lower` is `4d(2L+1)^d κdec≤κ`, the opposite direction from a lower bound on `κdec` supplied by `κmin`.

**REFUTED.** Increasing `κmin`, `κ`, and consequently `m₁` at fixed `L=3` makes the landed observable rate `3κdec/2` arbitrarily large. It remains exactly the same number. Enlarging `M=L^(m₁+1)` changes the physical cell side in both `Y.ncard` and the root denominator and leaves `c1(d,L)` unchanged.

**PROVED (algebra).** Even allowing `L` to grow, the **pinned** formula and this particular `G1_card` conversion have a finite per-block ceiling at each fixed `d`. Put `B=(2L-1)^d`, `Δ=3^d`; then `c1=Δ B` and `aEnt=log B+2Δ log(2Δ²)+2Δ B(1+Δ)log 2` by `SizeModEntropy.entQ`. Hence `λ/c1=150[1+(aEnt+12)/c1]` is bounded uniformly for `L≥3` since `log B/B≤1` and `1/B≤1`. No choice of `L`, `κmin`, or `m₁` makes the **certified** root rate arbitrary while these equations and this conversion are retained.

**OPEN.** This ceiling is about the available estimates; it does not disprove stronger decay of the actual coefficients or a different regrouping. The direct `IsDj`-to-`IsPolymer` support bridge, exact coefficient transport to the root's `X`, and all-torus coverage have not landed. `obsFamily_full_fromTower` also assumes `k≥1`, `3∣N₁`, `5<N₁`; the root includes `kf=0` and the smallest admissible torus, so the one-step theorem by itself cannot be Root-F even at `d=3,N=2`.

## T3. Prefactor and accumulated observable

**PROVED.** `Thm31bFromTower.obsPrefactor p s b = obsW p b^4*b^(-1/2-s)+obsW p b^2/b` and `ObsScalarTilt.obsW p b=(log b)^p`. `thm31b_zeroClass_at_of_ray_rho` bounds one scale's coefficient by `C*obsPrefactor p s (β*3^k)*exp(-(3κdec/2)dExt T')`, under its displayed ray and witness premises. The family theorem itself states `B₁+B₂`; equating it to the prefactor needs the separate one-scale estimates/assembly.

**PROVED (arithmetic).** Fix `0<s<1/2` **before** `κ,c₉`, and choose `0<δ<s(d−2)`. Standard `log^m b≤C_ε b^ε` for `b≥1` gives, with `E=(d−2)/2+δ`, `obsPrefactor(p,s,β L^{k(d−2)}) ≤ C β^{-E/(d−2)} L^{-kE}` for `β≥1`: use `ε=s−δ/(d−2)` for the first term and `ε=1/2−δ/(d−2)` for the second. At `d=L=3`, `s=1/4`, `δ=1/8`, this is `C β^{-5/8}3^{-5k/8}`. The output index is `j=k+1`, costing a fixed factor `L^E`. After all rate and counting constants, including `exp(λ)`, are fixed, a sufficiently large `β₀(c₉)` would make the one-scale prefactor at most `c₉ L^{-jE}`. This argument does **not** increase the spatial rate.

**OPEN.** The frozen `T_j` is the coefficient of the **whole** logarithmic partition expansion, chosen once for all scales and tori; it has not been identified with a single `obsCoeffParam` or `thm31b` output. `RenormExpInputOn.thm31h_on` adds the field contribution $K_{\mathrm{loc}}c_K c_{K2}(d,L,N)B\varepsilon_R$ and an inherited observable contribution $B_{\mathrm{old},M}\varepsilon_R/r_0$ to $B_{M0}$. A completed induction must show that these and final/large-field terms keep the required **birth-scale** factor `β^{-E/(d−2)}L^{-jE}` and one uniform spatial rate after all later steps. This estimate is not supplied by `obsPrefactor_small_scale`, which only gives uniform smallness.

## T4–T5. Decision for `StepTowerG`

**REFUTED.** The recommendation in `notes/phase1/STOWERG.md` T1/T5 to retain **both** `κ0_eq : κ0=aEnt d L+2` and `κdec_eq : κdec=100(κ0+c1 d L+10)` while raising only `κ` through `κmin` suffices for the frozen root's arbitrary `κ`. The displayed output estimate plus `G1_card` proves only rates `κ≤(3κdec/2-E)/c1(d,L)`; its right side is bounded for pinned rates. `stepOutput_consts_exists_ge_general` has the same limitation despite its “for every `κmin`” producer.

**OPEN (smallest proposed record change).** Keep `κdec_eq` and `κ'_eq`, but replace `κ0_eq` by `κ0_ge : aEnt d L+2≤κ0`; choose `κ0` **after** the root's desired rate so that `3κdec/2-E≥c1(d,L)κroot`, then choose interpolation `κ` and `m₁` from `tower_core_rates_general`. A separate `κroot` input/output-rate floor must be known before the tower is produced; the root gives it before existential `L`, although the internal tower may be chosen after `L`. Keep `κmin` for the interpolation rate only. Fix `s` before the root's `κ,c₉` to choose `δ`; it need not be a tower field. Alternatively free `κdec` with a lower bound, but that disturbs more exact-equality consumers. `stepOutput_consts_exists_ge_general` needs a variable-`κ0` variant. The fixed `StepTower` maps to the revised general record by its equality, preserving the old `3,3,2` endpoint. Numeric rewrites using `κ0_eq` must become inequalities or remain in fixed wrappers.

**PROVED.** The root's binder is `∃ L M : ℕ, 2 ≤ L ∧ 1 ≤ M`, after `κ,c₉`; no root quantifier forces `L>3`. The current **certificates** at `L=3` fail to supply unbounded rate, but a retuned `κ0,κdec` could in principle do so at `L=3` for `d=3,N=2`. Any source requirement `L≥L₀` or other geometry restriction is a separate proof issue, not a consequence of this binder.

**OPEN (worker targets).** Keep the current workers' statements with rate `(3/2)κdec` in `sizeJ` and the `obsPrefactor` form: these are the right one-step interfaces. The general tower worker must expose a selectable `κ0` or `κdec` and an output-rate floor; subsequent workers must prove the `G1_card`/entropy conversion, root support and torus transport, and the accumulated prefactor estimate. Merely increasing `κmin` is not a substitute.

**OPEN (author question).** May `StepTowerG` replace `κ0_eq` by `aEnt d L+2≤κ0`, retain the two other rate equalities, and add a requested **output** rate floor, while the existing `StepTower` remains the fixed-rate specialization? This is the smallest change I can justify from the landed interfaces.

**OPEN (confidence).** High confidence in the quantifier, definition, and pinned-rate verdict; moderate confidence in the proposed minimal general-tower change, whose downstream proofs and full root induction remain open.
