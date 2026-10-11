module

public import Balaban.Polymer.MayerAnalytic
public import Balaban.Polymer.MayerPE
public import Balaban.Polymer.Marked

/-!
# Truncated expectations from the Mayer layer (POLYMER.md §4.1, instance-free form)

For the integral `Ξ(λ) = ∫ exp(∑_t H_λ t) dν` of a product measure against potentials
`H_λ t = a t + ∑_j λ_j g_j t`, affine in the marks `λ ∈ ℂ^ι`, with `g_j t = 0` unless the support
of the term contains the set `S_j` of blocks, `mayer_marked` combines MY (`mayer_integral_eq`,
`mayer_activity_bound`), PE-L (`pe_size`) and the marked results of `Marked.lean`:

* `∂_i Ξ/Ξ(0) = ∑_Y ∂_i P(Y)(0)` and the truncated second moment
  `∂_j ∂_i Ξ/Ξ(0) - (∂_i Ξ/Ξ(0))(∂_j Ξ/Ξ(0)) = ∑_Y ∂_j ∂_i P(Y)(0)`;
* the decay bounds `|∂_i Ξ/Ξ(0)| e^{G} ≤ α / r_i` and
  `|∂_j ∂_i Ξ/Ξ(0) - (∂_i Ξ/Ξ(0))(∂_j Ξ/Ξ(0))| e^{G} ≤ α / (r_i r_j)`,
  where `G ≤ κ'(d(Y) + c)` for all `Y ⊇ S_i` (respectively `Y ⊇ S_i ∪ S_j`), and `α` is the
  constant of PE-L (this is (3.12), (3.13) of P9 with the P9 constants made explicit).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory Balaban.Analysis

namespace Balaban.Polymer

section Marks

variable {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
  {T : Type*} [Fintype T] (sup : T → Finset B) {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The activity of the polymer `Z` as a function of the marks. -/
def marksK (a : T → (∀ b, Ω b) → ℂ) (g : ι → T → (∀ b, Ω b) → ℂ) (Z : NePoly B)
    (l : ι → ℂ) : ℂ := mayerK μ sup (Hlam a g l) Z

/-- The partition function as a function of the marks. -/
def marksXi (a : T → (∀ b, Ω b) → ℂ) (g : ι → T → (∀ b, Ω b) → ℂ) (l : ι → ℂ) : ℂ :=
  ∫ Φ, Complex.exp (∑ t, Hlam a g l t Φ) ∂(Measure.pi μ)

omit [Fintype B] [(b : B) → MeasurableSpace (Ω b)] [Fintype T] in
theorem Hlam_translate (a : T → (∀ b, Ω b) → ℂ) (g : ι → T → (∀ b, Ω b) → ℂ) (l : ι → ℂ)
    (i : ι) (s : ℂ) (t : T) (Φ : ∀ b, Ω b) :
    Hlam a g (l + s • Pi.single i 1) t Φ = Hlam a g l t Φ + s * g i t Φ := by
  unfold Hlam
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  ring

omit [∀ (b : B), IsProbabilityMeasure (μ b)] in
theorem marksK_indep {a : T → (∀ b, Ω b) → ℂ} {g : ι → T → (∀ b, Ω b) → ℂ} {S : ι → Finset B}
    (hS : ∀ j t Φ, ¬ S j ⊆ sup t → g j t Φ = 0) (i : ι) (Z : NePoly B) (hZ : ¬ S i ⊆ Z.1)
    (l : ι → ℂ) (s : ℂ) :
    marksK μ sup a g Z (l + s • Pi.single i 1) = marksK μ sup a g Z l := by
  unfold marksK mayerK mayerAct polyAct
  refine integral_congr_ae (Filter.Eventually.of_forall (fun Φ => ?_))
  refine Finset.sum_congr rfl (fun C hC => Finset.prod_congr rfl (fun t ht => ?_))
  have hsub : sup t ⊆ Z.1 := sub_of_mem_Cfam hC ht
  have : g i t Φ = 0 := hS i t Φ (fun h => hZ (h.trans hsub))
  simp only []
  rw [Hlam_translate, this, mul_zero, add_zero]

end Marks

section Main

variable {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
  {T : Type*} [Fintype T] (sup : T → Finset B) {ι : Type*} [Fintype ι] [DecidableEq ι]
  {a : T → (∀ b, Ω b) → ℂ} {g : ι → T → (∀ b, Ω b) → ℂ} {d : Finset B → ℝ}
  {H0 κ0 κ1 c K0 c1 κ' κ0P K0P cP : ℝ} {r : ι → ℝ} {S : ι → Finset B}

/-- **MY + PE-L + PE-M**: truncated expectations for the integral `Ξ(λ) = ∫ exp(∑ H_λ) dν`. -/
theorem mayer_marked (hne : ∀ t, (sup t).Nonempty) (hr : ∀ i, 0 < r i)
    (ha : ∀ t, Measurable (a t)) (hab : ∀ t, Bdd (a t))
    (hg : ∀ j t, Measurable (g j t)) (hgb : ∀ j t, Bdd (g j t))
    (hloca : ∀ t, DepOn (sup t) (a t)) (hlocg : ∀ j t, DepOn (sup t) (g j t))
    (hS : ∀ j t Φ, ¬ S j ⊆ sup t → g j t Φ = 0)
    (hH0 : 0 ≤ H0) (hH0' : H0 ≤ Real.log 2) (hκ0 : 0 ≤ κ0) (hκ1 : 0 ≤ κ1) (hc : 0 ≤ c)
    (hd : ∀ Y, 0 ≤ d Y)
    (hH : ∀ l ∈ polydisc (0 : ι → ℂ) r, ∀ t Φ,
      ‖Hlam a g l t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d (sup t)))
    (hK0 : 0 ≤ K0)
    (hG2T : ∀ b : B, ∑ t ∈ Finset.univ.filter (fun t => b ∈ sup t),
      Real.exp (-κ0 * d (sup t)) ≤ K0)
    (hG3T : ∀ C : Finset T, ConnSet sup C →
      d (unionCs sup C) ≤ ∑ t ∈ C, d (sup t) + c * ((C.card : ℝ) - 1))
    (hc1 : 0 ≤ c1) (hq : 2 * H0 * K0 * Real.exp (κ1 * c) * c1 ≤ 1 / 2)
    (hG1 : ∀ Y : NePoly B, (Y.1.card : ℝ) ≤ c1 * (1 + d Y.1))
    (hκ' : 0 ≤ κ') (hcP : 0 ≤ cP)
    (hG2P : ∀ b : B, ∑ Y : NePoly B, (if b ∈ Y.1 then Real.exp (-κ0P * d Y.1) else 0) ≤ K0P)
    (hG3P : ∀ (n : ℕ) (X : Fin (n + 1) → NePoly B),
      (clusterGraph (shareBlock (Subtype.val : NePoly B → Finset B)) X).Connected →
        d (unionOf (Subtype.val : NePoly B → Finset B) X) ≤ ∑ i, d (X i).1 + cP * n)
    (hκ : κ' + κ0P + c1 ≤ κ1 - 3 / 2)
    (hα : 2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 * K0P * Real.exp (c1 + κ' * cP) ≤ 1) :
    (∀ i, D1 i (marksXi μ a g) / marksXi μ a g 0 =
      ∑ Y : Finset B, D1 i (Ff (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
        (marksK μ sup a g) Y)) ∧
    (∀ i j, D2 i j (marksXi μ a g) / marksXi μ a g 0 -
        (D1 i (marksXi μ a g) / marksXi μ a g 0) * (D1 j (marksXi μ a g) / marksXi μ a g 0) =
      ∑ Y : Finset B, D2 i j (Ff (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
        (marksK μ sup a g) Y)) ∧
    (∀ (i : ι) {b : B}, b ∈ S i → ∀ {G : ℝ},
      (∀ Y : Finset B, S i ⊆ Y → G ≤ κ' * (d Y + cP)) →
      ‖D1 i (marksXi μ a g) / marksXi μ a g 0‖ * Real.exp G ≤
        (2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 * K0P * Real.exp (c1 + κ' * cP)) / r i) ∧
    (∀ {i j : ι}, i ≠ j → ∀ {b : B}, b ∈ S i → ∀ {G : ℝ},
      (∀ Y : Finset B, S i ⊆ Y → S j ⊆ Y → G ≤ κ' * (d Y + cP)) →
      ‖D2 i j (marksXi μ a g) / marksXi μ a g 0 -
          (D1 i (marksXi μ a g) / marksXi μ a g 0) * (D1 j (marksXi μ a g) / marksXi μ a g 0)‖ *
        Real.exp G ≤
        (2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 * K0P * Real.exp (c1 + κ' * cP)) / r i / r j) := by
  set inc : NePoly B → NePoly B → Prop := shareBlock (Subtype.val : NePoly B → Finset B) with hinc
  set ε : ℝ := 2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 with hε
  have hε0 : 0 ≤ ε := by positivity
  set α : ℝ := ε * K0P * Real.exp (c1 + κ' * cP) with hαdef
  have hα1 : ε * K0P * Real.exp (c1 + κ' * cP) ≤ 1 := hα
  have hlocl : ∀ l t, DepOn (sup t) (Hlam a g l t) := fun l t Φ Φ' h => by
    unfold Hlam
    rw [hloca t Φ Φ' h]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by rw [hlocg j t Φ Φ' h])
  have hq0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hq1 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
  have hb_le : ∀ l ∈ polydisc (0 : ι → ℂ) r, ∀ t Φ, ‖Hlam a g l t Φ‖ ≤ Real.log 2 := by
    intro l hl t Φ
    refine (hH l hl t Φ).trans ?_
    calc H0 * Real.exp (-(κ0 + κ1) * d (sup t)) ≤ H0 * 1 := by
          gcongr
          exact Real.exp_le_one_iff.mpr (by nlinarith [hd (sup t)])
      _ ≤ _ := by rw [mul_one]; exact hH0'
  have hKan : ∀ Z : NePoly B, AnalyticOnNhd ℂ (marksK μ sup a g Z) (polydisc 0 r) := fun Z =>
    analyticOnNhd_mayerK_marks μ sup hq0 hq1 r ha hab hg hgb hb_le Z
  have hKbd : ∀ (Z : NePoly B), ∀ l ∈ polydisc (0 : ι → ℂ) r,
      ‖marksK μ sup a g Z l‖ ≤ ε * Real.exp (-(κ1 - 3 / 2) * d Z.1) := fun Z l hl =>
    mayer_activity_bound μ hH0 hH0' hκ0 hκ1 hc hd hne (hH l hl) hG2T hG3T hc1 hq Z (hG1 Z)
  have hW := sizeW_nonneg (κ := κ1 - 3 / 2) (κ' := κ') (c := cP) (Subtype.val : NePoly B → Finset B) d hε0
  have hent := size_entropy (Subtype.val : NePoly B → Finset B) d (κ := κ1 - 3 / 2) (κ' := κ')
    (κ0 := κ0P) (K0 := K0P) (c := cP) (c1 := c1) hε0 hd hG1 hG2P hκ hα1
  have hKP := kp_of_entropy (Subtype.val : NePoly B → Finset B) _ hW hent
  have hg0 : ∀ Y : Finset B, 0 ≤ κ' * (d Y + cP) := fun Y => by have := hd Y; positivity
  have hb : ∀ (Z : NePoly B), ∀ l ∈ polydisc (0 : ι → ℂ) r,
      ‖marksK μ sup a g Z l‖ ≤ sizeW (Subtype.val : NePoly B → Finset B) d ε (κ1 - 3 / 2) κ' cP Z := by
    intro Z l hl
    refine (hKbd Z l hl).trans ?_
    unfold sizeW
    calc ε * Real.exp (-(κ1 - 3 / 2) * d Z.1) = ε * Real.exp (-(κ1 - 3 / 2) * d Z.1) * 1 := by
          rw [mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_le_exp (by
          have := hg0 Z.1; simpa using this)) (by positivity)
  have hrefl : ∀ x : NePoly B, inc x x := shareBlock_refl _ (fun Y => Y.2)
  have hdep : MarkDep (Subtype.val : NePoly B → Finset B) S (marksK μ sup a g) :=
    fun i Z hZ l s => marksK_indep μ sup hS i Z hZ l s
  have hZ : ∀ l ∈ polydisc (0 : ι → ℂ) r, marksXi μ a g l = Xi inc (fun Z => marksK μ sup a g Z l) := by
    intro l hl
    exact mayer_integral_eq μ hne (hlocl l) (measurable_Hlam ha hg l)
      (fun t => ⟨_, hH l hl t⟩)
  have hG3' := size_g_G3 (Subtype.val : NePoly B → Finset B) d (c := cP) hκ' hG3P
  have hent' : ∀ b : B, ∑ x : NePoly B, (if b ∈ x.1 then
      sizeW (Subtype.val : NePoly B → Finset B) d ε (κ1 - 3 / 2) κ' cP x *
        Real.exp (α * (x.1.card : ℝ)) else 0) ≤ α := hent
  refine ⟨fun i => D1_Zf_div inc Subtype.val hKP hr hKan hb hrefl _ hZ i,
    fun i j => D2_Zf_div inc Subtype.val hKP hr hKan hb hrefl _ hZ i j, ?_, ?_⟩
  · intro i b hbS G hG
    have := norm_truncated_first_le inc Subtype.val hKP hr hKan hb hrefl hdep _ hZ
      (fun Y : Finset B => κ' * (d Y + cP)) 0 le_rfl hg0 hG3' (κ0 := fun x => ε * Real.exp (-(κ1 - 3 / 2) * d x.1))
      (fun x => rfl) (fun x l hl => hKbd x l hl) i hbS hG
    exact this.trans (div_le_div_of_nonneg_right (hent' b) (hr i).le)
  · intro i j hij b hbS G hG
    have := norm_truncated_second_le inc Subtype.val hKP hr hKan hb hrefl hdep _ hZ
      (fun Y : Finset B => κ' * (d Y + cP)) 0 le_rfl hg0 hG3' (κ0 := fun x => ε * Real.exp (-(κ1 - 3 / 2) * d x.1))
      (fun x => rfl) (fun x l hl => hKbd x l hl) hij hbS hG
    exact this.trans (div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right (hent' b) (hr i).le) (hr j).le)

end Main

end Balaban.Polymer
