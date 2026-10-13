# AUDIT-1013 — fidelity of three landed results

PROVED. Audit snapshot: `/home/scott/Balaban` commit `067f4c33f88e7c6cd4496152d370f445a639cafe`, 2026-10-13. I read the declarations and definitions in the cited Lean files and checked the local P1, P3, P4, P5 and P6 PDFs. The repository was not changed.

PROVED. Status convention: PROVED means the cited source or declaration directly establishes the narrow claim; REFUTED rejects a stated equivalence or sufficiency claim; OPEN identifies a missing bridge or a non-vacuity fact not supplied by the landed theorem. A proved abstract implication is not evidence that its physical input has been constructed.

## A. Source dependent zero-class activity

PROVED. Exact outer binders of `Balaban.Inhabited.stepActivityBound_zeroClass_source_scale` and `Balaban.Inhabited.sourceActivityC_scale` are identical: implicit `{A₁ : ℝ}`, explicit `hA : 0 < A₁`, `p : ℕ`, implicit `{κ0 κdec κ' : ℝ}`, and equality inputs `κ0 = aEnt 3 3 + 1`, `κdec = 100*(κ0+c1 3 3+10)`, `κ' = 3/2*κdec+κ0+1` ([SourceActivityScale.lean](/home/scott/Balaban/Balaban/Inhabited/SourceActivityScale.lean:272)). No class or activity witness is an input.

PROVED. Their conclusion chooses `m₁ : ℕ` and `t δ β₀ CE CF : ℝ` before `k,N₁,ν,β,g`, with `2 ≤ β₀`, `CE,CF,t,δ > 0`; then it quantifies `k : ℕ`, `hk : 1 ≤ k`, `N₁ : ℕ`, instance `[NeZero N₁]`, `3 ∣ N₁`, `5 < N₁`, `ν : ℝ`, `0 < ν`, `ν*3^(2*(k+1)) ≤ 1`, `β : ℝ`, `β₀ ≤ β`, and `g : Fld 3 3 N₁ m₁ (k+1) 2` in `l1Ball 3 3 N₁ m₁ (k+1) 2`.

PROVED. The real conclusion is `∃ B : StepActivityBound (hatStepK k m₁ hk ν β (pLog A₁ p (β*3^k)) δ) (zeroClass …) g`; the complex conclusion changes only `StepActivityBound` to `StepActivityBoundC`. Both expose `B.κH = 2κdec−1`, `B.εH ≤ CE(log(β3^k))^(3p)/√(β3^k) + CF(log(β3^k))^p/√(β3^k)`, the displayed rate inequality `κ' + 3κ0 + c1 3 3 + 3/2 ≤ 2κdec−1`, and `∃ κout = 3κdec/2` between `κdec` and `min κ' (κ'−κ0−1)`.

PROVED. `hatStepK` fixes `d=L=3`, `N=2`, the full level `G'=lvTop`, the constant unit background and external direction, `a₁=1`, and the supplied `ν,β,p₁,δ` ([LevelStepSetting.lean](/home/scott/Balaban/Balaban/Inhabited/LevelStepSetting.lean:75)). `zeroClass` has `m₀=0`, zero old terms and `Ek=0` ([StepIdentityInhabited.lean](/home/scott/Balaban/Balaban/Fluctuation/StepIdentityInhabited.lean:34)). `l1Ball` means the **strict coordinate sum** `∑_x∑_i ‖g x i‖ < 1`, not the Euclidean fibre norm ([InteractionFPart.lean](/home/scott/Balaban/Balaban/Fluctuation/InteractionFPart.lean:128)). `pLog A₁ p b = A₁(log b)^p`.

PROVED. `StepActivityBoundC` includes `m₀`, divisibility `L^m₀ ∣ N₁`, a product `BlockSplit`, a finite label type and `CubeLabels`, `εH,κH,κ0,κ',Kc`, and activities `A(s,t)` in `LabelAct` ([StepComplexNonvanish.lean](/home/scott/Balaban/Balaban/Fluctuation/StepComplexNonvanish.lean:57)). Its numerical fields are `aEnt+1 ≤ κ0`, `K0+1 ≤ Kc`, `εH>0`, `κ'≥0`, `κ'+3κ0+c1+3/2 ≤ κH`, and the explicit `hε` threshold `εH ≤ [8 Kc³ c1 exp((κH−2κ0)cG+c1+κ'cG)]⁻¹`.

PROVED. Its `hW` is an **almost everywhere identity at this step datum**: for each `p ∈ stepSegments`, `S.WoneC C p.1 x + S.WtwoC C g p.2 x = ∑_y (A p).H y (BS.restr x)` for almost every `x` under `S.nuFl`. There is no quantifier over other chart data. The complex record is obtained by transporting the real record across an almost everywhere exponent equality.

PROVED. Typing data are `p`, `hk`, `[NeZero N₁]`, the source field type and the defining equalities for rates. `hA` and `β≥β₀` are source-sized cutoff/low-temperature premises. Positivity and mass cap on `ν`, `3∣N₁`, `N₁>5`, and the fixed dimension/spin count are standing conditions of this witness, not hypotheses of the general papers. No conclusion-shaped activity or localization premise is assumed.

PROVED. The campaign explicitly records the fixed `d=L=3,N=2`, `3∣N₁>5`, `ν3^{2(k+1)}≤1`, physical `pLog`, strict source ball and central datum in [LEDGER.md](/home/scott/Balaban/orchestration/LEDGER.md) at the W387 source-activity entry. [AGENTS.md](/home/scott/Balaban/AGENTS.md) instead gives the ultimate scope `d≥3,N≥2`; it does not approve replacing the general roots by this witness.

PROVED. Non-vacuity is stronger than a zero-source example: `sourceActivityC_scale_instance` proves a nonzero source `g=½` at one coordinate, `k=1`, `N₁=6`, `ν=1/81`, for all sufficiently large `β`. The universal scale theorem also instantiates at `k=2` by taking any positive `ν≤3^{-6}`, `N₁=6`, then `β≥β₀`; hence its parameter range is jointly satisfiable beyond scale one.

OPEN. The landed instance does not show a **nonzero activity on a proper label**. `zeroClass` has no inherited terms; the direct-term construction produces labels and bounds but the cited scale theorem states neither a proper-label existence nor that such a label carries a nonzero value. A proper-component row witness elsewhere does not establish this for A's activity.

REFUTED. “P3 Theorem 3.1 / P4 Proposition 3.3” is not a sound citation for this bound. P3 prints **Proposition 3.1** on the localized covariance operator on p. 67, after (3.22)–(3.24), and P4's direct new-term statements are Propositions **2.1 and 2.2**, p. 696. P5 Proposition 3.3, p. 518, concerns inherited `R_n` expectation values, not this zero-class source activity.

PROVED. The closest printed activity input is P6 Lemma 4.1, p. 32: its localized interaction is analytic in the data, fluctuation, source and interpolation parameter on (4.25), depends on the corresponding domain, and satisfies (4.28), `|U(Y)| < ε exp(-(2κ−1)d_{k+1}(Y))`, with `ε` arbitrarily small for large `β`. P4 (2.51)–(2.57), pp. 694–695, defines the fluctuation terms and includes the source in the generating functional.

PROVED. A's `CE(log β_k)^{3p}/√β_k + CF(log β_k)^p/√β_k` tends to zero and its rate is explicit; both are compatible with the small amplitude and `2κ−1` pattern of P6 (4.28). P6's lemma is a **chart and locality family** for general step inputs, while A supplies only the zero class at the central real datum, with a fixed unit external direction. Its two constants are uniform in `k,N₁,ν,β,g` in the stated range.

REFUTED. A is not a formalization of the complete paper activity family or of Root-F's general step. P6 (4.25), p. 31, requires analytic data variation, while `StepActivityBoundC.hW` in A is at `S.D'`; Root-F quantifies all `d≥3,N≥2`, every unit direction and the whole low-mass flow. The campaign ledger separately records the chart family and output terms as open.

PROVED. For consumption, `stepNonvanishingC_of_activityBoundC` takes only `B` and derives nonvanishing on the two segments; `stepNonvanishingC_zeroClass_source_scale` applies it directly. `prop26C_step` takes `StepRegularC` and `StepNonvanishingC`, so A supplies only the latter, at the central datum; regularity and chart-wide instances remain separate ([StepComplexProp26.lean](/home/scott/Balaban/Balaban/Fluctuation/StepComplexProp26.lean:491)).

OPEN. `sourceActivityC_scale` exposes `κH` and an upper bound on `εH`, but not `B.κ0`, `B.κ'`, `B.Kc`, or a fixed common label family across sources. The stronger cutoff theorem exposes `B.Kc` and paired real/complex fields. A consumer demanding the prescribed record rates or a termwise source coefficient needs a strengthened public conclusion; existential `B.κ0` and `B.κ'` cannot be identified with the outer rates from this statement alone.

PROVED. Verdict A: **FAITHFUL WITH RECORDED SPECIALIZATIONS** as a central-datum zero-class bound. The first failed stronger claim is chart-wide activity, not a hidden source hypothesis. Its status toward the full roots is OPEN.

OPEN. Repairs for A: expose `B.κ0`, `B.κ'`, `B.Kc` and shared labels in a from-tower theorem; prove the exponent identity and bounded label family at every relative chart datum; prove termwise affine source dependence if pointwise `‖g‖₁` is needed; exhibit a nonzero proper-label activity; then generalize the witness beyond fixed `3,3,2` only where the root's quantifiers require it.

## B. Localized determinant output

PROVED. `DetExpansionLocC` has implicit `{d L N₁ m₁ k N : ℕ}`, instances `[NeZero L]`, `[NeZero N₁]`, implicit `{ϱ : ℝ}`, then `S : StepSetting d L N₁ m₁ k N ϱ`, `m₀ : ℕ`, root `z : Torus d (N₁ L^m₁ L^(k+1−(k+1)))`, and `eps κ'' cdet : ℝ` ([DetOutputTerms.lean](/home/scott/Balaban/Balaban/Fluctuation/DetOutputTerms.lean:147)). These are typing and output parameters, not a bundled proof premise.

PROVED. Its `term` is defined on **every** `BgData S.G' N` and finite cube set `T`. For `D` in `XiCData S.G' S.a S.ν (k+1) 1 eps`, `sum_eq` says the sum over all `T` is the rooted trace of the complex background covariance; `bound` says `‖term D T‖≤cdet exp(-κ'' dExt T)`; `anchor` says a nonzero term contains the root cube and is a polymer; `local_resDep` makes it depend on raw data in the `resDep` neighbourhood of sites of `T`; `analyticAt_raw` extends each term analytically near each raw chart point. These are record conclusions, not inputs.

PROVED. The generic `exists_detExpansionLocC_of_chart_uniform` has implicit dimensions, two generating sets, all tower constants, and the step `S`; explicit inputs are `FlCore`, `δc≥0`, a block size lower bound, decoupling margin, coercivity margin, smallness `δc² smallConstX≤1/4`, `HatConn`, `L^m₀∣N₁`, `((detDeg+1)^2)(2/e^κ)<1`, and root `z` ([DetPrefactor.lean](/home/scott/Balaban/Balaban/Fluctuation/DetPrefactor.lean:238)). It concludes an `E` with the rate `(κ−log2−2log(detDeg+1))/(2dL)` and constant `L^d·(N/2)·covBLogMax/(1−((detDeg+1)^2)2/e^κ)`, with `E.term` equal to the sum of `detActivityBg` over the block of `z`.

PROVED. Those generic inputs are substantial proof premises, not source assumptions of the physical model. The separate `stepActivityBound_detExpansionLocC_scale` discharges them for `hatStepK`, selecting `m₁,t,δ,β₀,C,BG,κ` before the scale, torus, mass, temperature, cutoff and root ([DetStepScale.lean](/home/scott/Balaban/Balaban/Inhabited/DetStepScale.lean:72)). It also constructs the zero-source real activity record and chart membership of the central datum.

PROVED. B's scale binders are the same `A₁>0,p,κ0,κdec,κ'` equalities as A; its quantified range is `k≥1`, `[NeZero N₁]`, `3∣N₁`, `5<N₁`, `ν>0`, `ν3^{2(k+1)}≤1`, `β≥β₀`, and every `0<p₁≤pLog A₁ p (β3^k)`. It fixes `d=L=3,N=2,m₀=1`; the determinant rate is at least `κ'`, and the constant simplifies to `27·covBLogMax 3 3 κ/(1−z_κ)` with `z_κ=((detDeg 3 3+1)^2)2/e^κ`.

PROVED. These scale/torus/mass restrictions are recorded witness specializations in the W387 determinant ledger entry; `AGENTS.md` still specifies the general root scope. They are not a source theorem hypothesis. `FlCore` in the generic constructor would be conclusion-shaped if left as a premise of the physical theorem; the landed scale theorem does not leave it there.

PROVED. `detActivityBg_sym` has implicit generating set, symmetry, cover and block structures plus unit-block preservation; explicit `L^m₀∣N₁`, membership in `pavingSymGroup`, the exact patch-image identity, unit point `y`, radius `ρ`, datum `D` and cube set `Y` ([DetRootTraceSymm.lean](/home/scott/Balaban/Balaban/Fluctuation/DetRootTraceSymm.lean:135)). It equates the term at transformed data/root/polymer with the original. This is covariance for compatible paving symmetries, not yet every Euclidean or spin symmetry in P4 (H.4).

PROVED. P4 (2.54), p. 694, writes the new energy contribution as a `log det C^(k)` part plus the expectation term; (2.57)–(2.60), pp. 695–696, split and prelocalize it. P4 Proposition 2.1, p. 696, claims the combined energy term satisfies H.4 with constant `NL^d B₄+1` and reduced rate `2κ−3−6κ₀`. P3 Proposition 3.1, p. 67, supplies localized covariance and states that a similar conclusion applies to the log operator's trace; it does not give the finished coefficient bound by itself.

PROVED. P5 p. 519 explicitly says the `−½D^(k)` determinant from (2.48) is combined with the expectation term as in P4 (2.54), then prelocalized as in P4 (2.60). Its Proposition 3.4, p. 520, gives the anchored new energy expansion with constant `(NL^d B₅+1)K₀`. Thus B isolates a genuine paper contribution, but the paper's final claim concerns its **sum with marks** and class properties.

PROVED. `thm31aC_coeff_detLoc_withDatum` consumes `E`, a chart datum with constant `h`, an `E1MarksC` record and `I.κ'≤κ''`; it proves the coefficient sum and a bound with `cdet` added to the mark constant ([DetStepInstance.lean](/home/scott/Balaban/Balaban/Fluctuation/DetStepInstance.lean:81)). The theorem does not consume B's `anchor`, `local_resDep` or `analyticAt_raw` in that bound, although later class use will need them.

PROVED. Non-vacuity of the record itself is proved for the scale witness: `detExpansionLocC_scale` and `stepActivityBound_detExpansionLocC_scale` construct chart data and `E` for every permitted `k,N₁,z`. A proper cube set exists on sufficiently large allowed tori, and the record's fields quantify over it.

OPEN. I found no landed example showing **`E.term D T ≠ 0` for a proper `T`** in the scale family. The support implication `term≠0 → root∈T` and universal locality are substantive laws, but a witness with every nonzero term on the whole torus would satisfy them without exercising proper-term locality. This is an evidence gap, not proof that the terms vanish.

REFUTED. `DetExpansionLocC` alone is not P4 H.4: its locality reads `resDep` beyond `T`, and its `analyticAt_raw` is pointwise on a relatively open chart whose image has empty ambient interior; the record itself says both are weaker than class clauses. `detActivityBg_sym` also assumes a compatible paving action and does not close spin rotations or every required output-term symmetry.

REFUTED. The determinant bound is not a small activity bound: `half_le_detConst` shows its generic constant is at least `N/2`. This matches its role as an `E₀` contribution in P4 Proposition 2.1; it cannot be charged to A's vanishing `εH` by identification.

PROVED. Verdict B: **DEFECT** as the claimed paper-ready localized output term. The first defect is `local_resDep` being wider than the polymer; class-wide covariance and relative-domain analyticity remain additional bridges. The narrower determinant component and its scale-uniform rate are faithful within recorded specializations.

OPEN. Repairs for B: prove a proper nonzero term instance, shrink the dependency claim or prove the needed chart-domain locality after regrouping, carry the analytic extension to the class's relative domain, finish all required symmetries, and combine determinant and mark bounds with a common tower. The ledger's CONSTS entry observes that separately invoked scale existentials do not provide the same `m₁,t,δ,κ`; from-tower restatements are required.

## C. Bare sector and good-spin Gaussian identity

PROVED. `partitionFunction_eq_sum_kf0Sector` has implicit `{d N ℓ : ℕ}`, `[NeZero ℓ]`, block parameters `s m : ℕ`, `[NeZero m]`, then `r β ν : ℝ`, `h : EuclideanSpace ℝ (Fin N)`, and complex `g : Torus d ℓ → Fin N → ℂ` ([KF0BlockSplit.lean](/home/scott/Balaban/Balaban/LargeField/Base/KF0BlockSplit.lean:236)). Its exact equality sums over every `B : Finset (Torus d m)`; no sign, temperature or geometry premise is needed for this algebraic identity.

PROVED. `kf0Sector` is `sourceIntegral` with multiplier `sectorWeight`: `∏_{Q∈B}(1−χ_Q)∏_{Q∉B}χ_Q`, where `χ_Q` tests whether all spins in block `Q` satisfy `‖φ_x−h‖<r`. `siteUnion B` is the set of physical sites whose block index lies in `B`. The block identity remains true even if `s,m,ℓ` do not describe a surjective genuine block tiling; the intended block geometry needs `ℓ=s*m` in later non-vacuity results.

PROVED. `kf0Sector_iterated` has the same implicit dimensions and block parameters, real `g`, `β,ν`, and `B`; it is an equality of **nonnegative `lintegral`s**, not literally an equality to the complex `kf0Sector`. It integrates bad spins `q` against `sigmaIn` and good spins `p` against `sigmaOut`, with `exp(−β blockEnergyIn+sourceIn)·badWeight` outside and `exp(−β goodEnergy+sourceOut)·goodWeight` inside. `goodEnergy` retains every crossing bond ([KF0BlockSplit.lean](/home/scott/Balaban/Balaban/LargeField/Base/KF0BlockSplit.lean:637)).

PROVED. `sigmaOut D` is the product of Mathlib surface measures on the sphere at sites outside `D`, not a normalized probability measure; `sigmaIn` is the analogous product on `D`. The Fubini split is exact for this same product measure ([KF0BlockSplit.lean](/home/scott/Balaban/Balaban/LargeField/Base/KF0BlockSplit.lean:452)). `goodWeight` is the product of `chiOut` over blocks outside `B`, where every good spin of a block must lie in the radius `r` ball.

PROVED. `lintegral_goodInner_gaussian` has implicit `{d N ℓ : ℕ}`, `[NeZero ℓ]`, fixed `D : Finset (Torus d ℓ)` and `h : EuclideanSpace ℝ (Fin N)` from its section, plus `{m : ℕ}`, `[NeZero m]`, `s,r,B`, `hD : D=siteUnion s m B`, `{β ν : ℝ}`, `β>0`, `ν>0`, `‖h‖=1`, `r≤1`, real `g`, and fixed bad spins `q` ([KF0GoodChart.lean](/home/scott/Balaban/Balaban/LargeField/Base/KF0GoodChart.lean:486)). None is an assumed Gaussian identity or outcome-shaped localization bound.

PROVED. Its right side is `(√β)^{-|G|(N−1)}·kwGaussNorm·∫ d(goodGaussian) [chartJac β(C_G ψ)·goodWeight(chart((√β)⁻¹ C_G ψ))·exp(goodChartExponent(C_G ψ))]`, with `G=Dᶜ`. `chartJac` is the product of `1[‖v_x‖<√β](1−‖v_x‖²/β)^{-1/2}` ([ChartIntegral.lean](/home/scott/Balaban/Balaban/LargeField/Base/ChartIntegral.lean:150)).

PROVED. `goodChartExponent` is minus the boundary linear, boundary normal, boundary constant and nonlinear remainder terms, plus the constant, tangent and normal source terms. The quadratic `½ goodQuad` is carried by the Gaussian reference. The exact formula includes the Jacobian and the good-sector cutoff; dropping either changes the integral.

PROVED. The hypothesis `r≤1` ensures nonzero `goodWeight` places every good spin in the upper hemisphere when `‖h‖=1`; `β,ν>0` make the chart and massive Gaussian reference valid. These are genuine analytic premises for the chart lemma. The bare sector sum requires none of them, so they do not secretly restrict the original partition identity.

PROVED. P1 (1.1), p. 103, defines a normalized probability density with `E=log Z`; its hard-spin limit (1.5)–(1.6), p. 104, keeps the gradient and external-field action on the unit sphere. The frozen `energy` is `½∑_{x,μ}‖φ_{x+eμ}−φ_x‖² + (ν/2)∑_x‖φ_x−h‖²`, and `partitionFunction` integrates `exp(−β energy+∑g_iφ_i)` against `aprioriMeasure`, the unnormalized product surface measure ([Energy.lean](/home/scott/Balaban/Balaban/Frozen/Model/Energy.lean:22), [PartitionFunction.lean](/home/scott/Balaban/Balaban/Frozen/Model/PartitionFunction.lean:22)).

PROVED. The frozen hard-spin choice and measure convention are recorded in [AprioriMeasure.lean](/home/scott/Balaban/Balaban/Frozen/Model/AprioriMeasure.lean:22) as the `λ=∞` specialization, up to a volume-dependent surface factor that cancels in normalized observables. Root-F explicitly uses `log(Z(g)/Z(0))`, so it reads the same frozen `partitionFunction` and cancels that factor; it does not use the P1 probability density directly ([LogPartitionMultiscale.lean](/home/scott/Balaban/Balaban/Frozen/Roots/LogPartitionMultiscale.lean:48)).

PROVED. This is a recorded specialization rather than a mismatch in C: `N` and `d` remain arbitrary in the C identities, while the chart theorem assumes a unit `h` and positive mass. The fixed `β,ν` non-vacuity instance has `d=N=3`, `ℓ=4`, `s=m=2`, `r=1/4`, unit `h`, and proves **every sector integral positive**, including proper bad sets ([KF0BlockSplit.lean](/home/scott/Balaban/Balaban/LargeField/Base/KF0BlockSplit.lean:810)).

REFUTED. The triple is not yet an exact complex-source Gaussian formula for `kf0Sector`: the sum theorem uses complex Bochner integrals, the iterated and chart theorems use real-source `lintegral`s. A conversion to the complex source and one shared sector sum/reference measure is a further theorem, not definitional equality.

OPEN. No current consumer derives Root-F from this triple. The next consumer needs to combine the fixed-`B` chart identities with bad-spin integration, the B-dependent Gaussian normalizations and determinant ratios, then prove linked local activities with a uniform volume bound and a bridge to `log(Z(g)/Z(0))`. [KF0-LAST.md](/home/scott/Balaban/notes/phase1/KF0-LAST.md) records that P7 (4.10), p. 531, invokes the inherited P5 (1.31) reserve, which this bare identity does not supply.

PROVED. Verdict C: **FAITHFUL WITH RECORDED SPECIALIZATIONS** for the bare partition, exact real sector split and inner good-spin integral. The first failed stronger claim is that these identities already yield one normalized, complex-source, localized root input. They do not.

OPEN. Repairs for C: state and prove a complex-source iterated sector identity against the frozen measure, assemble all sectors with their exact Gaussian determinant ratios on one reference space, establish positive bad-sector control and linked support locality, then normalize by `Z(0)` before feeding Root-F. Keep the `λ=∞` and surface-measure convention explicit.

## Cross-check and closeout

REFUTED. The conjunction of A, B and C is not an end-to-end proof of either frozen root: A and B each choose their own existential tower, A lacks chart-wide source activity, B lacks class-local determinant terms, and C has no linked sector expansion. These are concrete missing interfaces, not extra premises hidden in the displayed headline theorems.

PROVED. No cited headline theorem assumes its own conclusion. The generic B constructor does assume substantial `FlCore` and margin records, but the scale theorem supplies them; the C Gaussian theorem's geometric and positivity hypotheses are independently satisfiable in the explicit nontrivial sector setting.

OPEN. The strongest unresolved vacuity checks are a nonzero proper A label and a nonzero proper B determinant term. The landed nonzero source, arbitrary `k≥1` range, and positive proper C sectors rule out the simpler empty-domain objections.

PROVED. Source page references above are printed page numbers. PDF identities checked: P1 `BF02099355.pdf`; P3 `BF02506385.pdf`; P4 `Balaban.pdf`; P5 `s002200050433 (1).pdf`; P6 `s002200050470.pdf`. All Lean declaration names in this note were located in the current source tree by `rg`; no build or source edit was needed for this read-only audit.
