# C1STAR — the extra physical input of Root-C

**PROVED. Verdict and scope.** At the audited `/home/scott/Balaban` snapshot `c09d1bcb7bd1ac033c8cd1c9a9e97fe27775ac94`, the implication `rootC_of_rootFAndC1Star` is landed, but no physical producer of `RootFAndC1Star` is landed. This is a focused, read-only source-to-Lean audit; the three frozen roots/providers were not edited.

**PROVED. Frozen-v1 evidence.** SHA256: `C1Star.lean` `37bdffd07567bcfff63571d3f90a0536a5d7fd0a4f8ab8caa372fae2f3e291d3`; `RootCFromFlow.lean` `652955500d7371fe70754079c7ee3ce6b1a5142b34a23d8c28dd8e8b4b0a52c2`; `RunningCoefficients.lean` `e21084e62f6dd804664112fbacea6c6a23ac2f69ca3ea89a9dad4a78745cd4e0`. P9 PDF `eb78658c0bd5ca3807d85566ff8ccec809ab10af57424c2b845b37a97412d245`; P4 PDF `804ba741c65367a4ba3e1ce84f0c415999a32de0ff2e1c337b41d9fa9104a303`; P8 PDF `f9b1a1630d1f2d040e585880cf1c9d5cea102628ad0764456a16c6a3e69eb889`.

**PROVED. Audit gate.** I tried to discharge C-1* from Root-F's source derivative identities, to find a physical C-1* witness elsewhere in the tree, and to identify P8 as a cited P9 input. Each attempted shortcut fails for a stated reason below. The positive claims here concern the exact displayed declarations, not an unchecked build.

## 1. Exact joint interface and its mathematical content

**PROVED. Verbatim declaration** from [C1Star.lean](/home/scott/Balaban/Balaban/Correlations/C1Star.lean:156); `hN` is an explicit proof, `hL` constructs `[NeZero L]`, and the `C1Star` witness is chosen before `β`:

```lean
def RootFAndC1Star (d N : ℕ) (hN : 2 ≤ N) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ L M : ℕ, ∃ hL : 3 ≤ L, 1 ≤ M ∧ ∃ β₀ : ℝ,
    (∀ β : ℝ, β₀ ≤ β → ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
      ∃ kf : ℕ, (L : ℝ) ^ kf * Real.sqrt ν ≤ L ∧ 1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν ∧
        ∃ T : RootFFamily d N, RootFClauses d N L M β ν h kf (kappaStar d) 1 δ T) ∧
    Nonempty (@C1Star d N L M ⟨by omega⟩ hN)
```

**PROVED.** `RootFClauses` includes the torus-local source representation, polymer support, source locality/analyticity/bound, and nonwinding agreement. The joint declaration takes this **one slice** at `κ=kappaStar d`, `c₉=1`; it does not itself state Root-F's `∀κ,c₉` outer quantifiers. `L≥3,M≥1,β₀` are shared with C-1*, and `T` may depend on `β,ν,h` but works on every admissible torus for those parameters ([Clauses.lean](/home/scott/Balaban/Balaban/Correlations/Clauses.lean:51)).

**PROVED. Every `C1Star` field** is: reals `a,γ₀,cStar,cXi,cPrime,ρ₀,ρ₁,βStar`; `a_range : 1/[2(1−L⁻²)]<a<3/2`; `γ₀_range : 0<γ₀≤1/2`; positivity of `cStar,cXi,cPrime`; `ρ₀_range : 0<ρ₀≤d−2`; `ρ₁_range : 0<ρ₁<1`; and the `data` field described next ([C1Star.lean](/home/scott/Balaban/Balaban/Correlations/C1Star.lean:124)). No kernel witness is a field: the consumer constructs it separately.

**PROVED. Exact `data` order.** For every `β≥βStar`, it chooses `J : ℝ→ℕ`, real `ξ : ℝ→ℕ→Fin 3→ℝ`, `μ : ℕ→ℝ→ℤ^d→ℝ`, torus remainders `rtr,rlg`, magnetization error `em`, fixed-mass torus limits `rtrLim,rlgLim`, and zero-mass limits `rtrZero,rlgZero`. It requires `Jν≥1` for `0<ν≤1`, `Jν→∞` as `ν↓0`, and `1/2≤L^{Jν}√ν≤L²`, followed by `C1StarF1 ∧ C1StarF2 ∧ C1StarF3`. All eight constants precede `β`; `J` and the functions may depend on it.

**PROVED. F1.** `C1StarF1` bounds every `‖ξ(ν)_k‖≤cXi/(4β)·(L^{-2γ₀})^{k+1}` for `ν∈[0,1]` and requires `ξ(ν)_k→ξ(0)_k` as `ν↓0` for each `k`. `xiC` complexifies the real coefficients. `gammaR`, `deltaR`, `betaR` are the real products formed from `ξ`, with component 2 changing the inverse temperature and component 1 changing the mass.

**PROVED. F2.** `C1StarF2` requires `|μ_j(ν,x)|≤cStar β^{-1/2+ρ₁}L^{-jρ₀}` for `j≥1,ν∈[0,1]`, and continuity at zero mass. For each `0<ν≤1,x`, after some torus-size threshold `ℓ₀`, every `ℓ` divisible by `ML^{Jν+1}` satisfies `blockM = magJ+em`, with `|em|≤cStar β^{-2}L^{-2Jν(d−2)}`. Here `magJ=1−∑_{j<J}β_j^{-1/2}μ_{j+1}`: the distinguished one-point term is `magJ h`, not merely a small correction to `h`.

**PROVED. F3.** For `0<ν≤1`, admissible `ℓ`, and nonwinding displacement `2|(x−y)_i|<ℓ`, `C1StarF3` singles out `blockGtr = magJ(x)magJ(y)·mainTr + rtr` and `blockGlg=rlg`. The transverse main term is `mainTr=∑_{j<J}(β γ_j)^{-1} T_j^{ℓ,νδ_j}(x,y)`, where `T_j` is `termKernel` with `freeSeq d L a`; there is no longitudinal Gaussian main term in the hard-spin interface.

**PROVED. F3 remainder.** Each `|rtr|,|rlg|` is at most `cStar[(1+‖x−y‖)^{-(d−2+ρ₀)}+ν^{(d−2)/2}]e^{-cPrime√ν‖x−y‖}`. F3 also requires `LimAlong (ML)` of the two remainders at fixed positive `ν`, and the right limits of those limits as `ν↓0`. The extra `ν^{(d−2)/2}` term pays the final Gaussian tail; it vanishes at fixed separation as `ν↓0`.

**PROVED.** `rootC_of_rootFAndC1Star` takes `d,N`, `3≤d`, `2≤N`, and this joint hypothesis, then proves `RootCStatement d N`; `kernelHyp_and_large_holds` supplies both ordinary and large-mass Gaussian kernel hypotheses for the same free-flow kernel ([RootCFromFlow.lean](/home/scott/Balaban/Balaban/Correlations/RootCFromFlow.lean:20), [KernelLargeAssembly.lean](/home/scott/Balaban/Balaban/Correlations/KernelLargeAssembly.lean:22)). `RootCStatement` is a copy of the frozen conclusion, whose actual provider remains unfilled.

## 2. The printed P9 route and exact flow inputs

**PROVED.** P9 (2.1), printed p. 496, expands the renormalized generating functional into a linear source function `M_k`, a quadratic kernel `G_k`, and higher source orders. Its (H.1), (2.2)–(2.9), pp. 496–497, gives `M_k=m_k φ_k+∑β_{j-1}^{-1/2}M^{(j)}`, localized analytic `M^{(j)}` with `β^{-1/2+ρ₁}L^{-jρ₀}` size, the normalization `M^{(j)}(h,h)=0`, and `m_k=1−∑β_{j-1}^{-1/2}m_0^{(j)}`. These are the source of F2's `μ_j` and `magJ`.

**PROVED.** P9 (H.2), (2.10)–(2.20), pp. 497–499, separates `G_k=C_k+R_k`. The `C_k` part has Gaussian fluctuation covariances transported by background derivatives; `R_k` is a localized second-source remainder. This is the source of F3's main term/remainder split, beyond Root-F's aggregate bound on `T_j`.

**PROVED.** P9 Proposition 3.1, (3.11)–(3.13), printed pp. 502–504, localizes one marked expectation and a truncated expectation of **two** marks, with a rate `2κ` before later losses. The two-mark clause is needed for the differentiated quadratic kernel; a one-mark `M` expansion cannot prove F3.

**PROVED.** P9 (3.43)–(3.45), printed pp. 511–512, transports the marks through the change of background under the renormalized coefficients: `z_{k+1}ψ_{k+1}` enters both new `M` and `G` terms, while the shifts `δφ,δα,δψ` and the inherited `M^{(j)},G^{(j)},R^{ij}` create further localized terms. Thus the field-renormalization factor and old observable class must be carried together at each step; the new zero-class mark alone is insufficient.

**PROVED.** P4 (H.7), printed pp. 678–679, provides the source analyticity/locality class whose one-source descendants P9 refines; P4 (5.23), p. 715, solves the renormalization equations, and (5.28), (5.31)–(5.33), pp. 716–717, give the running `β_j,ν_j`, the decay of `ξ_j`, and limiting `γ∞,δ∞`. F1 needs the physical solutions of these equations, with a bound uniform in the model's `β` and continuity as `ν↓0`.

**PROVED.** P7 (4.15)–(4.17), printed p. 533, gives the last integral's localized logarithm and source representation after the large-field gas. P9 (4.3)–(4.6), printed p. 516, adds its final boundary and large-field polymer terms. Thus the last scale contributes to F2's `em` and F3's `rtr,rlg`; small-field output alone omits these terms.

**PROVED.** P9 (4.7)–(4.9), printed pp. 516–517, differentiates the last generating function: its one-point function is the derivative of `F_{k+1}` plus derivatives of `R^{(k+1)}` and `P^{(k+1)}`, while its truncated two-point function is `G_{k+1}` plus their second derivatives. (4.10), p. 517, reduces the leading first derivative at the constant background to `m_k h`; (4.11) splits the two-point function into transverse and longitudinal projectors.

**PROVED.** P9 (4.12)–(4.14), pp. 517–518, calculates the transverse Gaussian part from the background response and fluctuation covariance. Equation (4.15), p. 518, separates the positive-mass difference from the zero-mass sum; (4.16) is that zero-mass scale sum. Equation (4.17), p. 518, identifies the corresponding **free** scale sum with the lattice Green function, and (4.18), p. 519, compares `β_j^{-1}` with `(βγ∞)^{-1}L^{-j(d−2)}` plus a faster scale remainder.

**REFUTED.** P8 is not a cited dependency of P9: its bibliography, printed pp. 519–520, has no Balaban–O'Carroll “simple method” entry. P8 (19)–(20), printed p. 5, is a general generating-functional/Gaussian-translation template in another model; P9 (4.17) cites **[10] Parisi**, not P8. The Lean Gaussian identity here must stand on the repository's own proof, and it does.

**PROVED CONDITIONAL ON the P9 inductive hypotheses.** P9's argument supplies the path from (H.1)/(H.2) through marked RG transport and the last integral to the leading terms and their bounds. P9 states several steps by reference to P4/P5/P7 and does not itself furnish a Lean physical constructor for the joint record. Its formal status here is a source roadmap, not a completed root proof.

## 3. Lane-by-lane producer audit

**PROVED CONDITIONAL ON a physical `ObsMarks` family.** `thm31bC_of_input_M0` expands the complex step's new `M0C` from `ObsMarks`. The zero class is not vacuous for this task: `McompAtC_zero_eq` leaves the background response. Current `Thm31bWitness` has nondegenerate **one-datum** inhabitants, while `ObsRowLabels` and `ObsScalarTilt` explicitly leave the common physical family/coefficients open ([StepComplexThm31.lean](/home/scott/Balaban/Balaban/Fluctuation/StepComplexThm31.lean:184)).

**OPEN.** STEPOUT package 8 is the physical source-ball, relative-chart `obsMarks_zeroClass_family`; package 9 is analytic/local/symmetric `observableOutputTerms_zero`; package 13 assembles `RenormExpInput`, including `expM0`, from the actual output. None of those named producer theorems was found in the current Lean tree. `ObsRowCoeff.lean` now proves `obsRowCoeff_of_sharpHat`, the coordinate coefficient and support bounds conditional on the sharp-hat premises; it explicitly does not construct the full tilt/remainder `ObsMarks` family. `RenormInputZero` still takes `expM0` as an input ([STEPOUT.md](/home/scott/Balaban/notes/phase1/STEPOUT.md), [ObsRowCoeff.lean](/home/scott/Balaban/Balaban/Fluctuation/ObsRowCoeff.lean:225)).

**PROVED.** The flow lane has `betaSeq_eq`, `nuSeq_eq`, `exists_gamma_infty`, and `exists_inv_betaSeq_asymptotics` in `RunningCoefficients.lean`: they prove P4 (H.6)/(5.32) and P9 (4.18) **from** a geometric bound on `ξ`. `RealSequences.lean` packages positivity and `1/2≤γ_j,δ_j≤2` under `SeqHyp`. This is substantial, generator-neutral arithmetic.

**OPEN.** Neither file produces the physical `ξ(ν,k)` from the actual class transition, its `O(β^{-1}L^{-2γ₀k})` bound with `cXi` chosen before `β`, nor `ν↓0` continuity. P4's renormalization equations and class output must supply that input; separately proved sequence estimates do not imply F1.

**OPEN.** FINALMAP identifies the positive stopping-scale physical Hessian, cutoff, complex chart, localized logarithm and nonempty-region gas as separate bridges. `FinalCutoffPack.lean` now packages the cutoff at the stop index under an explicit cover premise; it supplies neither the physical cover nor the full last integral. The zero-scale sector result is also not a full last integral. P7 (4.15)–(4.17) must hold for the actual stopped density and its source derivatives before F2/F3 can absorb its errors ([FINALMAP.md](/home/scott/Balaban/notes/phase1/FINALMAP.md), [FinalCutoffPack.lean](/home/scott/Balaban/Balaban/SmallField/FinalCutoffPack.lean)).

**OPEN.** The large-field lane must preserve the source/observable class through its operators, show local two-mark bounds and torus agreement, and control final polymer `P^{(J)}` and its first two source derivatives. P9 (4.5)–(4.6), p. 516, gives a small activity claim; it is not an instance of the current C-1* remainder fields until differentiated, localized and summed.

**PROVED.** The pure Gaussian lane is farther along: `sum_rule_matrix` and `sum_rule_apply` give the finite-torus multiscale identity; `termDirect_freeSeq_unit` matches free scale terms to the Green operators; `termKernel_nested` handles nested tori; `KernelHyp.tsum_eq_latticeGreen` proves the infinite sum is the lattice Green function; `kernelHyp_and_large_holds` supplies the common ordinary/large-mass kernels. These settle the **pure** content of P9 (4.17) with the repository's precise indexing, independently of P8/Parisi.

**PROVED CONDITIONAL ON F1.** `exists_inv_betaSeq_asymptotics` gives P9 (4.18) and `Asymptotics.lean` sums the faster-decaying comparison error against a kernel majorant. The conditional Root-C assembly already consumes this, with `goldstone_uniform` and the C-1* remainder bounds. The remaining input is to identify those abstract `ξ` and Gaussian terms with the physical flow.

## 4. Bounded Lean work that can start now

**PROVED.** There is no need to restate P9 (4.17) as an open analytic theorem: `KernelHyp.tsum_eq_latticeGreen` plus `kernelHyp_and_large_holds` already provides it. A ≤100-line wrapper may expose the exact `freeSeq`/`termKernel` indexing used by `mainTr`; its target is `∑' j, t0 j x y = latticeGreen d (x−y)` under `3≤d,3≤L,a_range`, with the `t0` returned by `kernelHyp_and_large_holds`. **Start now: yes; Sonnet; purely packaging.**

**PROVED.** There is also no new abstract P9 (4.18) proof to commission: `exists_inv_betaSeq_asymptotics` already gives `γ∞`, `|γ∞−1|≤c₈q/[2(1−q)]`, and the coefficient error `e² c₈q/[2(1−q)]·|β|^{-1}L^{-j(d−2)}q^j`. A ≤160-line real wrapper can set `q=rate L γ₀`, `c₈=cXi/β`, use `SeqHyp`/`betaR_eq`, and conclude the same inequality for `(betaR L d ξ β j)⁻¹`. **Start now: yes; Sonnet; no physical ξ claim.**

**OPEN, exact new target `c1Star_remainder_limit_criterion`.** For each fixed `x,y`, take local summands `u : ℕ→ℕ→ℝ→ℝ` indexed by scale and torus; assume every fixed-scale `u j ℓ ν` has `LimAlong (ML)` as `ℓ→∞`, then a right limit at `ν=0`, and `|u j ℓ ν|≤b j` for all admissible `ℓ,ν∈[0,1]` with `Summable b`. Prove `LimAlong (ML)` and the right limit for `∑' j,u j ℓ ν`, with limit `∑' j,u_j(ν)` and zero limit `∑' j,u_j(0)`. This is the precise Tannery mechanism required by F3, without assuming F3 itself. **Start now: yes; Sonnet; ≤220 lines.**

```lean
theorem c1Star_remainder_limit_criterion (q : ℕ) (hq : 1 ≤ q) (u : ℕ → ℕ → ℝ → ℝ)
    (v : ℕ → ℝ → ℝ) (v0 b : ℕ → ℝ) (hb0 : ∀ j, 0 ≤ b j)
    (hb : Summable b)
    (hu : ∀ j ℓ ν, ν ∈ Set.Ioc (0 : ℝ) 1 → |u j ℓ ν| ≤ b j)
    (ht : ∀ j ν, ν ∈ Set.Ioc (0 : ℝ) 1 →
      LimAlong q (fun ℓ _ => u j ℓ ν) (v j ν))
    (h0 : ∀ j, Tendsto (v j) (𝓝[>] 0) (𝓝 (v0 j))) :
    (∀ ν ∈ Set.Ioc (0 : ℝ) 1,
      LimAlong q (fun ℓ _ => ∑' j, u j ℓ ν) (∑' j, v j ν)) ∧
    Tendsto (fun ν => ∑' j, v j ν) (𝓝[>] 0) (𝓝 (∑' j, v0 j))
```

**OPEN, exact new target `c1Star_running_from_class`.** Input: one actual flow class family at fixed `L,M` whose renormalization equation produces real `ξ(ν,k)` for all `ν∈[0,1]`, with the P4 (5.31) bound and its class continuity clause at `ν=0`; output: `C1StarF1 L γ₀ cXi β ξ` plus `betaR_eq`, `gammaR`/`deltaR` identification for that same `ξ`. The `cXi` and flow construction must precede `β`, matching the `C1Star` prefix. **Start now: yes for the producer interface and first-scale instance; strong; ≤300 lines per declaration.**

**OPEN, exact new target `c1Star_first_source_from_step`.** Input: the physical P9 (H.1) local `M^{(j)}` family and its normalization at the constant saddle, compatible torus agreement, the new `M0C` terms of every small-field step, and first derivatives of the last `R^{(J)}+P^{(J)}` with the P9 p. 516 estimate. Output: `C1StarF2 d N L M hN cStar ρ₀ ρ₁ J β ξ μ em`, where `μ_j` is the normalized layer coefficient and `em` is the last derivative plus winding error. **Start now: yes for the generator-neutral summation lemma; physical theorem waits for STEPOUT 8–9/13; strong; ≤300 lines each.**

**OPEN, exact new target `c1Star_second_source_from_step`.** Input: the physical P9 (H.2) two-mark family and `G_k=C_k+R_k`, finite-torus covariance identification with `termKernel`, the last-step second derivatives and its Gaussian tail, and uniform local majorants plus `ν↓0` continuity. Output: the two finite-torus equalities and the two explicit bounds that form the **first conjunct** of `C1StarF3`; apply `c1Star_remainder_limit_criterion` to produce its other two conjuncts. **Start now: yes for the finite-sum algebra and abstract limit criterion; physical theorem waits for the two-mark and last-step lanes; strong; ≤300 lines per declaration.**

**OPEN, exact final producer `rootFAndC1Star_physical`.** Target `RootFAndC1Star d N hN` for `3≤d,2≤N`, from a **single** physical flow that returns `L≥3,M≥1,β₀`, all Root-F clauses at `kappaStar d,1`, and a `C1Star d N L M hN` with the same `L,M`. The final assembly is ≤300 lines once those inputs exist; **start now: no** as a closure claim. The provider for the frozen Root-C should be touched only after this target and its exact frozen export are checked.

## 5. Report-on-tension and closeout

**REFUTED.** Root-F alone does not imply Root-C's rates: its direct derivative identities give a small fixed `c₉` correction and roughly `((d−2)/2+δ)` polymer decay, without F2's `β^{-1+ρ₁}` magnetization or F3's `d−2` Gaussian leading term. Choosing `c₉` as a function of `β` violates Root-F's order `∀c₉ ∃L,M,β₀ ∀β`. This failed shortcut survives checking the exact `RootFClauses` and source derivative theorems.

**OPEN.** The zero-class step is a useful first instance but cannot supply a general `C1Star`: the physical flow must transport inherited `M^{(j)}`, two-mark `R^{ij}`, late large-field terms, and the final gas, with shared source conventions. The L-class/output generator remains pending; a zero-class-only producer would miss both (H.1) and (H.2) after the first step.

**OPEN.** Uniformity tensions for the author: `L,M,cStar,cXi,cPrime,ρ₀,ρ₁` are chosen before `β`; `J` is chosen after `β` but must satisfy the same mass window and tend to infinity; the actual flow's stopping index and extension of `ξ,μ` to `ν=0` need a compatible convention. The frozen Root-C also fixes one torus base `q` and one decay constant before `β` ([LowTemperatureCorrelations.lean](/home/scott/Balaban/Balaban/Frozen/Roots/LowTemperatureCorrelations.lean:37)).

**PROVED.** The recorded F-B repair in `C1StarF3` permits a `ν^{(d−2)/2}` last-Gaussian tail while still yielding the frozen zero-mass remainder estimate; P9's printed (4.14)–(4.18) omits that tail in its displayed regular covariance sum. The hard-spin longitudinal Gaussian main term is zero only after the sphere/response identification, not by an abstract `RootFClauses` argument. These are reporting obligations, not reasons to edit a frozen file.

**OPEN.** P9 does not print a proof of every torus remainder limit or every right limit as `ν↓0`; `C1StarF3` requires both. The generic limit criterion above can handle the passage once a **physical**, summable majorant and coefficientwise continuity are available. The source's formal remainder bound and the frozen root's regularized `1+‖z‖` bound should remain distinguished at `z=0`.

**PROVED. Closeout.** The audited statement, P9 equation chain, current conditional consumers, generator-neutral work and open physical producers are separated above. No claim of a physical `RootFAndC1Star` inhabitant, a sealed frozen root, or a fresh Lean build is made. All existing Lean declaration names in this note were checked against the current tree with `rg`; proposed names are explicitly marked new.
