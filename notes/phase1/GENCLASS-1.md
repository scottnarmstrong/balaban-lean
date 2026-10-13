# GENCLASS-1: exact interfaces for the first general-class leaves

**PROVED (source snapshot).** Read-only main commit 8a1bdf723d2e424cfea29662e2c1f7b1b1847cab. The fibre files are now on main: Inhabited/StepIdentityFibre.lean:71 contains stepActivityBoundC_fibre_fromTower. No build was run. Proposed code below is a statement target, not an elaboration claim. Source line numbers refer to this commit.

**REFUTED (correction to GENCLASS.md T4).** The broad leaf 3 is already in main: StepActivityHatGeneral.lean:304,330 defines OldEnergyHatMatch and OldObsHatMatch; StepActivityDirectGeneral.lean:491 proves physVal_eq_stepExponent_of_oldHatMatch and :732 proves stepActivityBound_direct_source_of_oldHatMatch for a general C. Its source uses physical_directTerms, two sources 0 and g/β, and scaled hat variables at σ=1. A new proof of those assertions would duplicate landed work. The η-restricted physical_directTerms_eta_scaled at SharpAssemblyScaled.lean:1561 is an alternative DirectTerms producer, not by itself an identification with WoneC + WtwoC.

## Leaf 1: StepOldTermSplit.lean

**OPEN (file and imports).** Proposed file Balaban/Fluctuation/StepOldTermSplit.lean; public import Balaban.Fluctuation.StepComplexSource (which imports StepComplexObs and hence StepComplexOut). Source declarations: StepComplex.lean:111 EcompAtC, :131 FcompAtC, :342 dEC, :348 dFC, :355 WoneC, :359 WtwoC; StepComplexOut.lean:210–224 WoneCT/dECT/WVCT, :272 WoneCT_eq_add, :279 WtwoC_eq_sum; StepComplexNonvanish.lean:306 EcompAtC_zero, :311 FcompAtC_zero_eq; StepComplexSmall.lean:54 WoneC_zeroClass; StepComplexSource.lean:65 dFC_zeroClass and :94 WtwoCT_zeroClass_eq_sum.

**OPEN (exact new Lean statement targets; the first is definitional, the second expands FcompAtC).**
~~~lean
namespace Balaban.Fluctuation
open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)
  (C : StepClass d L N₁ m₁ k N ϱ)

theorem WoneC_eq_action_add_oldE (s : ℝ) (x : S.E) :
    S.WoneC C s x =
      -(S.β : ℂ) * S.VkC (S.psiAtC s x) +
      (EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
          (S.dataUC (S.psiAtC s x)) -
       EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
          (S.dataUC S.psi0C)) := by
  rfl

theorem WtwoC_eq_bare_add_oldM
    (g : Fld d L N₁ m₁ (k + 1) N) (t : ℝ) (x : S.E) :
    S.WtwoC C g t x =
      S.WtwoC (zeroClass d L N₁ m₁ k N ϱ) g t x +
      ((∑ j ∈ Finset.Icc 1 k,
          Floc C.m₀ C.Tm j
            (composedPairAtC S.a S.ν (Nat.le_succ k) j
              (S.dataUC (S.psiAtC t x))).1
            (composedPairAtC S.a S.ν (Nat.le_succ k) j
              (S.dataUC (S.psiAtC t x))).2 g) -
       (∑ j ∈ Finset.Icc 1 k,
          Floc C.m₀ C.Tm j
            (composedPairAtC S.a S.ν (Nat.le_succ k) j
              (S.dataUC S.psi0C)).1
            (composedPairAtC S.a S.ν (Nat.le_succ k) j
              (S.dataUC S.psi0C)).2 g)) := by
  -- unfold WtwoC, dFC, FcompAtC; use FcompAtC_zero_eq; regroup finite sums.
  sorry
end Balaban.Fluctuation
~~~

**PROVED (difference interpretation).** The energy difference is exactly dEC C (S.psiAtC s x); the source difference is the difference of the two sums of Floc C.m₀ C.Tm over j∈[1,k]. The first summand of the source statement is the bare background-source increment because FcompAtC_zero_eq removes all Floc terms. WoneCT_eq_add is the same energy split after chiFl truncation, not an identity between WoneCT and WoneC off the support.

**OPEN (proof route, four lines).** The first proof is rfl after unfolding WoneC/dEC. For source, unfold WtwoC/dFC/FcompAtC at ψAtC t x and ψ0C; use FcompAtC_zero_eq for zeroTerms; commute subtraction with the finite j sums; normalize the additive expression. WtwoC_eq_sum and FcompAtC_eq_pair (StepComplex.lean:143) provide an independent componentwise check. The landed WoneC_zeroClass (StepComplexSmall.lean:54) is the one-line zero corollary via EcompAtC_zero; dFC_zeroClass (StepComplexSource.lean:65), hence WtwoCT_zeroClass_eq_sum (:94), is the source corollary via Floc_zero and FcompAtC_zero_eq. Existing statements need not be moved or renamed.

**OPEN (limit).** This leaf supplies identities only. It supplies no analytic bounds, locality of a polymer term, or nonvanishing.

## Leaf 2: StepClassPath.lean

**PROVED.** The requested exponent equality is already prop26C_class_of_activity, StepComplexProp26.lean:655–662, with the full section hypotheses at :613–633. Its exact central conclusion is:
~~~lean
S.TstepC C g = Complex.exp (-(S.β : ℂ) * S.AnewC +
  EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC -
  (S.Eppp C : ℂ) * (S.nU : ℂ) +
  FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC g +
  S.E0C C + S.F0C C g)
~~~
**PROVED.** Its nontrivial inputs are hreg : S.ClassRegularC C g and hact : StepActivityBoundC S C g; the other section inputs include FlCore, margins, β>0, 0<p₁<pp and XiCData. The proof invokes prop26C_class and stepNonvanishingC_of_activityBoundC. StepComplexOutAnalytic.lean:636–643 separately gives a chart function F with conditional analyticity from EdensAnalyticOnPath and FlocAnalyticOnPath, defined at :199 and :207. Path analyticity alone is not stated to imply ClassRegularC; keep hreg explicit.

**OPEN (exact useful wrapper; import both modules).** Balaban/Fluctuation/StepClassPath.lean imports Balaban.Fluctuation.StepComplexProp26 and Balaban.Fluctuation.StepComplexOutAnalytic. With the following typed hypotheses, the only new work is packaging the two landed conclusions:
~~~lean
open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.SmallField
namespace Balaban.Fluctuation.StepSetting
variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
  {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
  (hcore : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
  {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) {pp : ℝ} (hlt : S.p₁ < pp)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')

theorem classPath_step (g : Fld d L N₁ m₁ (k + 1) N)
    (hpaths : ∀ (D : BgData S.G' N)
      (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
      XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      (S.withDatum D hDh).EdensAnalyticOnPath C ∧
      (S.withDatum D hDh).FlocAnalyticOnPath C g)
    (hreg : S.ClassRegularC C g) (hact : StepActivityBoundC S C g) :
    (∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        F (rawOf D) = (S.withDatum D hDh).TstepC C g ∧
        AnalyticAt ℂ F (rawOf D)) ∧
    (S.TstepC C g = Complex.exp (-(S.β : ℂ) * S.AnewC +
      EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC -
      (S.Eppp C : ℂ) * (S.nU : ℂ) +
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC g +
      S.E0C C + S.F0C C g)) := by
  -- exact pair of the two landed theorems, using hpaths for the analytic implication.
  sorry
end Balaban.Fluctuation.StepSetting
~~~

**OPEN (proof route, four lines).** Apply exists_analyticAt_TstepC_of_analyticAt_class with hβ.le; for each D split its returned value and conditional analyticity, then use hpaths D hDh. Apply prop26C_class_of_activity to the second conjunct. The zero-class analytic theorem exists_analytic_TstepC_zeroClass, StepComplexOutAnalytic.lean:666, is stronger (analytic on the whole chart); it is not literally this wrapper's corollary without supplying hpaths, hreg, hact. The zero-class exponent theorem prop26C_zeroClass_of_activity, StepComplexSource.lean:285, is a one-line instance of the second conjunct after classRegularC_zeroClass. **OPEN (limit).** The wrapper does not derive the path hypotheses or hreg from IsSF2; that domain bridge remains separate.

## Leaf 3: StepPhysicalActivityBridge.lean, narrowed to transport and input matching

**PROVED (landed exact match statements).** StepActivityHatGeneral.lean:304–326 defines OldEnergyHatMatch as the support-wise equation
$\beta\sum_{\tau\in\mathcal T_E}(H_\tau(\hat\psi)-H_\tau(0))=S.dE\,C\,(S.psiAt\,1\,x)$,
where $H_\tau(z)=\operatorname{hatFun}(\operatorname{flComp}(hBE_\tau,hFE_\tau,EE_\tau))(\operatorname{rawOf}S.D',z)$ and the actual Lean sum has the membership-dependent hBE/hFE proofs. At :330–356 OldObsHatMatch is
$\beta\sum_{\tau\in\mathcal T_M}(g(y_\tau,i_\tau)/\beta)(K_\tau(\hat\psi)-K_\tau(0))
=S.dF\,C\,g\,(S.psiAt\,1\,x)-S.dF\,zeroClass\,g\,(S.psiAt\,1\,x)$.
Both quantify x : S.E with chiFl S.U N S.p₁ x = 1. The factor β⁻¹ belongs in EE, while EM has no β⁻¹: StepActivityHatLevel.lean:179–189 oldEnergyHatMatch_level uses EE_j=β⁻¹ Edens_j; :232–255 oldObsHatMatch_level uses EM_{j,y,i}=Mloc_j(y)_i.

**OPEN (exact class enumeration to construct).** For energy take labels $(j,y,X)$ with $j\in[1,k]$, $y$ a $j$-aligned site and $X\in\mathrm{polysAt}(C.m₀,j,y)$; set $EE_{j,y,X}(r)=\beta^{-1}C.Tm.E\,j\,y\,X\,r.1\,r.2$. For observables take $(j,y,i,X)$ with $X\in\mathrm{polysAt}(C.m₀,j,y)$ and $EM_{j,y,i,X}(r)=C.Tm.M\,j\,y\,X\,r.1\,r.2\,g\,i$, and $ys=y$, $is=i$. The enumeration must sum exactly to Edens and Floc (SmallField/Def6.lean:101–125), including the aligned-site filter and source factor. Each label also needs BgSetting, FlSetting and cover data on its chosen local generator.

**OPEN (explicit chart assumptions, in the landed theorem's exact types).** For every $\tau\in\mathcal T_E$ require
~~~lean
hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ)
  (XiCRaw (GjE τ) (compWeight L S.a₁) S.ν (jE τ)
    (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl))
hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L S.a₁) S.ν (jE τ)
  (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
  ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) *
    treeLenCovOne m₀ (jE τ) (XE τ))
~~~
**OPEN.** The M assumptions are the same with EM, GjM, jM, EbM, XM and hEanM/hEbdM; their exact binders occur in StepActivityDirectGeneral.lean:818–839. These are hypotheses of the already landed generic constructor, not consequences of Def6v2.lean:82–85 analyticE/M and :124–129 boundE/M. The latter live on Dom.dom j (C.Tm.gs j X), with cost $P.\kappa\,sizeJ(C.m₀,j,X)$, whereas the former live on the enlarged XiCRaw chart of Gj and demand the specified tree cost. Name the needed inclusion plus norm-transfer assertion LocalGeneratorChartBridgeE/M. Its analytic part is the hardest unresolved hypothesis of this lane; merely setting Gj=C.Tm.gs j X does not supply the chart inclusion. InteractionETerm.lean:64 flComp and InteractionHatE.lean:57 eTermFun are the actual compositions. The landed oldEnergyHatMatch_level/oldObsHatMatch_level handle whole-level generators only.

**PROVED (exact general constructor already on main).** StepActivityDirectGeneral.lean:732–858 assumes hEanE, hEbdE, hEanM, hEbdM, the enumerations, cover/margin/summability data, hmatchE : OldEnergyHatMatch S C 𝒯E hBE hFE EE, hmatchM : OldObsHatMatch S C g 𝒯M ys is hBM hFM EM, $g/\beta$ in l1Ball, a RayData witness and numerical smallness. Its conclusion is exactly
~~~lean
∃ B : StepActivityBound S C g,
  B.κH = 2 * κdec - 1 ∧ B.εH = 2 * (Rσ * εU) ∧ B.Kc = 2 * Kc'
~~~
StepActivityDirectGeneral.lean:491–500 gives the exact value at the *scaled* hats and $\sigma=1$, on chiFl support:
~~~lean
physVal (EE := EE) (EM := EM) S (S.β : ℂ) S.hG
  ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) 𝒯E hBE hFE 𝒯M ys is hBM hFM (0 : ℂ)
  ((s : ℂ) • S.hatC x, (t : ℂ) • S.hatC x)
  ((s : ℂ) • S.hatC x, (t : ℂ) • S.hatC x) 1
  (rawOf S.D', fun y i => g y i / (S.β : ℂ)) =
    S.Wone C s x + S.Wtwo C g t x
~~~
**REFUTED.** The corresponding assertion at unscaled hats and $\sigma=u$ is false in general: StepActivityDirectGeneral.lean:519–529 displays the extra $(1-u^2)$ potential remainder.

**OPEN (only new generic wrapper worth a separate file).** Import Balaban.Fluctuation.SourceSliceScaled and Balaban.Fluctuation.StepActivityDirectGeneral. The direct-term constructor supplies hreal below; the complex transport is already SourceSliceScaled.lean:237–244:
~~~lean
namespace Balaban.Fluctuation
variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ}
  {C : StepClass d L N₁ m₁ k N ϱ}
  {g : Fld d L N₁ m₁ (k + 1) N} {pp a εH Kc : ℝ}

theorem complexActivity_of_physical
    (R : S.RayData pp) (hp : 0 < S.p₁) (hlt : S.p₁ < pp)
    (hreal : ∃ I : StepActivityBound S C g,
      I.κH = a ∧ I.εH = εH ∧ I.Kc = Kc) :
    ∃ B : StepActivityBoundC S C g,
      B.κH = a ∧ B.εH = εH ∧ B.Kc = Kc := by
  rcases hreal with ⟨I, hκ, hε, hK⟩
  obtain ⟨B, hκB, hεB, hKB, -, -, -⟩ :=
    stepActivityBoundC_of_activityBound R hp hlt I
  exact ⟨B, hκB.trans hκ, hεB.trans hε, hKB.trans hK⟩
end Balaban.Fluctuation
~~~

**PROVED (zero case and limit).** oldEnergyHatMatch_zeroClass and oldObsHatMatch_zeroClass are on StepActivityHatGeneral.lean:371,410, so empty families instantiate the *landed matching predicates*. They do not make stepActivityBoundC_fibre_fromTower (Inhabited/StepIdentityFibre.lean:71) a one-line corollary: that theorem also chooses uniform tower constants, family activities and fibre values. The wrapper above only transports an already obtained real activity record. **OPEN.** The local-generator enumeration and LocalGeneratorChartBridgeE/M are needed to obtain hreal for the physical nonzero class.

**OPEN (proof route, six steps).** Enumerate the finite E and M polymer terms and show their sums are Edens/Floc. Establish the local chart inclusion and norm transfer named LocalGeneratorChartBridgeE/M, yielding hEanE/hEbdE and hEanM/hEbdM. Prove the two pointwise flComp identities against composedPairAt and hence OldEnergyHatMatch/OldObsHatMatch. Invoke the landed physical_directTerms and stepActivityBound_direct_source_of_oldHatMatch with the numerical smallness hypotheses. Apply stepActivityBoundC_of_activityBound, or the wrapper above, at the real datum. No step identifies the η-restricted output with a class term automatically.

## T4. Ownership and size

**OPEN (schedule).** Leaves 1 and 2 can run concurrently: separate files and no cross-import. Their remaining sizes are about 50–100 and 40–80 Lean lines. Leaf 3's transport wrapper can run concurrently in its own file and is about 15–40 lines; because the generic value and activity theorems already exist, a larger generic bridge leaf should not be assigned. The substantive class-term enumeration/chart bridge should be a later separate file, likely 200–300 lines per E/M piece, after the local-generator interface is fixed. None of these edits belongs in the read-only main checkout during this task.

**PROVED (confidence in source audit).** High for names, line-addressed landed conclusions, scaling, and the correction that the generic activity constructor already exists. **OPEN (confidence in proposed statements).** Medium for the two unbuilt wrapper statements and the source split's Lean normalization; low for discharge of LocalGeneratorChartBridgeE/M until its generator and domain types are fixed.
