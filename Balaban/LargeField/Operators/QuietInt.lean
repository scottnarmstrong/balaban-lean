module

public import Balaban.LargeField.Operators.QuietShell

/-!
# Bounds on the remainder of the quiet kernel and the integrals of the shell indicators
(Part II, Lemma II.5.14)

* `quietRest_unit`: `0 ≤ quietRest ≤ 1` (all factors are indicators or `e^{-𝒜}` with `𝒜 ≥ 0`);
  `quietRest_eq_zero`: it vanishes off `χ^new_k`;
* `lintegral_indOut_le_one`, `lintegral_indNew_le_one`: the integral of the product of shell
  indicators over the new′ variables is `≤ (c_N t)^{#} ≤ 1`;
* `mWit_one`: the Gaussian measure of the trivial witness function is `1`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory ENNReal

theorem charFn_le_one' {X : Type*} (P : X → Prop) (x : X) : charFn P x ≤ 1 := by
  classical
  rw [charFn_apply]; split_ifs <;> norm_num

theorem unit_mul {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) : 0 ≤ a * b ∧ a * b ≤ 1 :=
  ⟨mul_nonneg ha.1 hb.1, by nlinarith [ha.1, ha.2, hb.1, hb.2]⟩

theorem cubeProd_unit {d m : ℕ} {X : Type*} {χ : Torus d m → X → ℝ}
    (h : ∀ y x, 0 ≤ χ y x ∧ χ y x ≤ 1) (A : Finset (Torus d m)) (x : X) :
    0 ≤ cubeProd χ A x ∧ cubeProd χ A x ≤ 1 :=
  ⟨Finset.prod_nonneg fun y _ => (h y x).1, Finset.prod_le_one₀ (fun y _ => (h y x).1)
    fun y _ => (h y x).2⟩

section QuietRestBounds

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}
  (g : Geo S n R M) (Hl : RegionHistory S n R k0) (k : ℕ) (Zc : Finset (Torus S.d (n (k + 1))))
  (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1))) (cs : OpConsts) (hk : k + 1 ≤ K)
  (hrem : ∀ j, Hl.rem j = ∅)

open Classical in
theorem quietRest_unit (hb : 0 ≤ cs.beta (k + 1)) (ha : ∀ n, 0 ≤ cs.aw n)
    (hμ : 0 ≤ cs.muAct (k + 1))
    (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    0 ≤ quietRest g Hl k Zc hZc cs hk hrem o x hv ∧ quietRest g Hl k Zc hZc cs hk hrem o x hv ≤ 1 := by
  have hA := mainActionLoc_nonneg g Hl k Zc hZc cs hk hrem hb ha hμ o x hv
  unfold quietRest
  refine unit_mul (unit_mul (unit_mul (unit_mul (unit_mul (unit_mul ?_ ?_) ?_) ?_) ?_) ?_) ?_
  · exact cubeProd_unit (fun y x => ⟨by unfold chiK; exact charFn_nonneg' _ _,
      by unfold chiK; exact charFn_le_one' _ _⟩) _ _
  · exact cubeProd_unit (fun y x => ⟨by unfold chiPrimeNew; exact charFn_nonneg' _ _,
      by unfold chiPrimeNew; exact charFn_le_one' _ _⟩) _ _
  · exact cubeProd_unit (fun y x => ⟨by unfold chiPrimeNew; exact charFn_nonneg' _ _,
      by unfold chiPrimeNew; exact charFn_le_one' _ _⟩) _ _
  · exact cubeProd_unit (fun y x => ⟨by unfold chiNext chiK; exact charFn_nonneg' _ _,
      by unfold chiNext chiK; exact charFn_le_one' _ _⟩) _ _
  · unfold chiNew; exact ⟨charFn_nonneg' _ _, charFn_le_one' _ _⟩
  · split_ifs <;> norm_num
  · exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩

open Classical in
theorem quietRest_eq_zero
    (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N))
    (hn : ¬ ChiNewProp (locHist Hl M K (k + 1) Zc) k
      (Hl.histGen (M := M) hrem Hl.F.ok.two_le_L K (fun j _ _ => g.hRlow j))
      (fineSet (S := S) (n := n) M K (k + 1) (Zc : Set (Torus S.d (n (k + 1))))) cs.delta cs.p0
      cs.Cpsi
      (subMultiscaleField N (locHist Hl M K (k + 1) Zc) (k + 1)
        (Vblk R (locHist Hl M K (k + 1) Zc) (k + 1)) x o)
      (subFluctField N (locHist Hl M K (k + 1) Zc) (k + 1) x)) :
    quietRest g Hl k Zc hZc cs hk hrem o x hv = 0 := by
  unfold quietRest
  have : chiNew (locHist Hl M K (k + 1) Zc) k
      (Hl.histGen (M := M) hrem Hl.F.ok.two_le_L K (fun j _ _ => g.hRlow j))
      (fineSet (S := S) (n := n) M K (k + 1) (Zc : Set (Torus S.d (n (k + 1))))) cs.delta cs.p0
      cs.Cpsi
      (subMultiscaleField N (locHist Hl M K (k + 1) Zc) (k + 1)
        (Vblk R (locHist Hl M K (k + 1) Zc) (k + 1)) x o,
        subFluctField N (locHist Hl M K (k + 1) Zc) (k + 1) x) = 0 := charFn_eq_zero hn
  rw [this]
  simp

end QuietRestBounds

theorem measurableSet_shellSet (N : ℕ) (t : ℝ) : MeasurableSet (shellSet N t) := by
  unfold shellSet
  exact measurableSet_lt ((measurable_norm.pow_const 2).sub_const 1 |>.abs) measurable_const

theorem pi_pi_le_one {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (s : ∀ i, Set (α i))
    (h : ∀ i, μ i (s i) ≤ 1) : Measure.pi μ (Set.pi Set.univ s) ≤ 1 := by
  rw [Measure.pi_pi]
  exact Finset.prod_le_one fun i _ => h i

open Classical in
/-- The integral of the shell indicator over the new output variables is at most `1`. -/
theorem lintegral_indOut_le_one (N : ℕ) (hN : 2 ≤ N) {α : Type} [Finite α] (V : Set α)
    (P : α → Prop) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 2) (hct : cShell N * t ≤ 1) :
    ∫⁻ on : OutPart N V P, (if ∀ y, |‖on y‖ ^ 2 - 1| < t then (1 : ℝ≥0∞) else 0)
      ∂(outPartMeasure N V P) ≤ 1 := by
  classical
  have hset : {on : OutPart N V P | ∀ y, |‖on y‖ ^ 2 - 1| < t} =
      Set.pi Set.univ (fun _ => shellSet N t) := by
    ext on; simp [shellSet]
  have hmeas : MeasurableSet {on : OutPart N V P | ∀ y, |‖on y‖ ^ 2 - 1| < t} := by
    rw [hset]
    exact MeasurableSet.univ_pi fun _ => measurableSet_shellSet N t
  have : (fun on : OutPart N V P => (if ∀ y, |‖on y‖ ^ 2 - 1| < t then (1 : ℝ≥0∞) else 0)) =
      Set.indicator {on : OutPart N V P | ∀ y, |‖on y‖ ^ 2 - 1| < t} 1 := by
    funext on; simp [Set.indicator]
  rw [this, lintegral_indicator_one hmeas, hset]
  unfold outPartMeasure
  let _ : Fintype {y : α // y ∈ V ∧ P y} := Fintype.ofFinite _
  exact pi_pi_le_one (fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) _
    fun _ => (volume_shellSet_le N hN ht ht1).trans (ENNReal.ofReal_le_one.mpr hct)

section NewInt

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]

open Classical in
/-- The integral of the shell indicator over the new′ internal variables (all Lebesgue) is at
most `1`. -/
theorem lintegral_indNew_le_one (N : ℕ) (hN : 2 ≤ N) (a : LocalHistory S n M K) {k' : ℕ}
    (A : Set (InternalVars a k')) (hA : ∀ p ∈ A, p.isSpin = false) {t : ℝ} (ht : 0 < t)
    (ht1 : t ≤ 1 / 2) (hct : cShell N * t ≤ 1) :
    ∫⁻ x' : SubCfg N a k' A, (if ∀ p : A, |‖VarVal.toEuc (x' p)‖ ^ 2 - 1| < t then (1 : ℝ≥0∞) else 0)
      ∂(subMeasure N a k' A) ≤ 1 := by
  have hset : {x' : SubCfg N a k' A | ∀ p : A, |‖VarVal.toEuc (x' p)‖ ^ 2 - 1| < t} =
      Set.pi Set.univ (fun p : A => (VarVal.toEuc : VarVal N p.1.isSpin → _) ⁻¹' shellSet N t) := by
    ext x'; simp [shellSet]
  have hmeas : MeasurableSet {x' : SubCfg N a k' A | ∀ p : A, |‖VarVal.toEuc (x' p)‖ ^ 2 - 1| < t} := by
    rw [hset]
    exact MeasurableSet.univ_pi fun p => (VarVal.measurable_toEuc N _) (measurableSet_shellSet N t)
  have : (fun x' : SubCfg N a k' A =>
      (if ∀ p : A, |‖VarVal.toEuc (x' p)‖ ^ 2 - 1| < t then (1 : ℝ≥0∞) else 0)) =
      Set.indicator {x' : SubCfg N a k' A | ∀ p : A, |‖VarVal.toEuc (x' p)‖ ^ 2 - 1| < t} 1 := by
    funext x'; simp [Set.indicator]
  rw [this, lintegral_indicator_one hmeas, hset]
  unfold subMeasure
  refine pi_pi_le_one (fun p : A => varMeasure N p.1.isSpin) _ fun p => ?_
  rw [(measurePreserving_toEuc_false (N := N) _ (hA p.1 p.2)).measure_preimage
    (measurableSet_shellSet N t).nullMeasurableSet]
  exact (volume_shellSet_le N hN ht ht1).trans (ENNReal.ofReal_le_one.mpr hct)

theorem mWit_one (N : ℕ) [NeZero N] {c : ℝ} (hc : 0 < c) (a : LocalHistory S n M K) (k : ℕ) :
    mWit N c a k (fun (_ : Unit) _ => (1 : ℝ)) () = 1 := by
  classical
  unfold mWit
  simp only [ENNReal.ofReal_one, mul_one]
  let _ : Fintype ↥(gaussBlocks a k) := Fintype.ofFinite _
  have h1 : ∀ u : ↥(gaussBlocks a k) → EuclideanSpace ℝ (Fin N),
      ENNReal.ofReal (∏ y, gaussT N c (u y) 0) = ∏ y, ENNReal.ofReal (gaussT N c (u y) 0) :=
    fun u => ENNReal.ofReal_prod_of_nonneg fun y _ => gaussT_nonneg N c hc.le _ _
  simp_rw [h1]
  rw [PiTools.lintegral_fintype_prod_eq_prod _ (fun _ v => ENNReal.ofReal (gaussT N c v 0))
    (fun _ => ENNReal.measurable_ofReal.comp (by
      unfold gaussT; exact measurable_const.mul (Real.measurable_exp.comp
        (measurable_const.mul ((measurable_norm.comp (measurable_id.sub_const _)).pow_const 2)))))]
  simp [lintegral_gaussT N hc]

end NewInt

open Classical in
theorem measurable_indOut (N : ℕ) {α : Type} [Finite α] (V : Set α) (P : α → Prop) (t : ℝ) :
    Measurable fun on : OutPart N V P =>
      (if ∀ y, |‖on y‖ ^ 2 - 1| < t then (1 : ℝ≥0∞) else 0) := by
  have hset : {on : OutPart N V P | ∀ y, |‖on y‖ ^ 2 - 1| < t} =
      Set.pi Set.univ (fun _ => shellSet N t) := by
    ext on; simp [shellSet]
  have hmeas : MeasurableSet {on : OutPart N V P | ∀ y, |‖on y‖ ^ 2 - 1| < t} := by
    rw [hset]
    exact MeasurableSet.univ_pi fun _ => measurableSet_shellSet N t
  exact Measurable.ite hmeas measurable_const measurable_const

open Classical in
theorem measurable_indNew (N : ℕ) {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ}
    [NeZero M] [NeZero S.L] (a : LocalHistory S n M K) {k' : ℕ} (A : Set (InternalVars a k'))
    (t : ℝ) :
    Measurable fun x' : SubCfg N a k' A =>
      (if ∀ p : A, |‖VarVal.toEuc (x' p)‖ ^ 2 - 1| < t then (1 : ℝ≥0∞) else 0) := by
  have hset : {x' : SubCfg N a k' A | ∀ p : A, |‖VarVal.toEuc (x' p)‖ ^ 2 - 1| < t} =
      Set.pi Set.univ (fun p : A => (VarVal.toEuc : VarVal N p.1.isSpin → _) ⁻¹' shellSet N t) := by
    ext x'; simp [shellSet]
  have hmeas : MeasurableSet {x' : SubCfg N a k' A | ∀ p : A, |‖VarVal.toEuc (x' p)‖ ^ 2 - 1| < t} := by
    rw [hset]
    exact MeasurableSet.univ_pi fun p => (VarVal.measurable_toEuc N _) (measurableSet_shellSet N t)
  exact Measurable.ite hmeas measurable_const measurable_const

end Balaban.LargeField
