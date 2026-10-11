module

public import Balaban.Polymer.Decomposition
public import Mathlib.Probability.Independence.Integration

/-!
# The Mayer layer for product measures (MY)

A product probability measure `ν = ⨂_b μ_b` on configurations `Φ ∈ ∏_b Ω_b` (one factor space per
charged block), and local terms `H t` depending on `Φ` only through the blocks `sup t`.  Expanding
`e^{∑ H} = ∏ (1 + (e^{H t} - 1))` and grouping the families of terms into connected components
(`Balaban.Polymer.decomposition`), the integral of `e^{∑ H}` is the partition function of a polymer
gas, whose activities `∫ ∑_C ∏_{t ∈ C} (e^{H t} - 1) dν` are integrals over connected families
(`mayer_integral_eq`).  The factorization over the components uses independence of the coordinates
(`integral_prod_depOn`).  Bounds: `mayer_activity_bound` (POLYMER.md §2.4 (iii), §3.7).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory ProbabilityTheory

namespace Balaban.Polymer

section Independence

variable {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]

/-- `F` depends on the configuration only through its restriction to `S`. -/
def DepOn (S : Finset B) (F : (∀ b, Ω b) → ℂ) : Prop :=
  ∀ Φ Φ' : ∀ b, Ω b, (∀ b ∈ S, Φ b = Φ' b) → F Φ = F Φ'

omit [Fintype B] [∀ b, MeasurableSpace (Ω b)] in
theorem DepOn.mono {S S' : Finset B} (h : S ⊆ S') {F : (∀ b, Ω b) → ℂ} (hF : DepOn S F) :
    DepOn S' F := fun Φ Φ' hΦ => hF Φ Φ' (fun b hb => hΦ b (h hb))

/-- Extension of a configuration on `S` by the reference configuration `Φ₀`. -/
def extendCfg (S : Finset B) (Φ₀ : ∀ b, Ω b) (x : ∀ i : S, Ω i) : ∀ b, Ω b :=
  fun b => if h : b ∈ S then x ⟨b, h⟩ else Φ₀ b

omit [Fintype B] in
theorem measurable_extendCfg (S : Finset B) (Φ₀ : ∀ b, Ω b) :
    Measurable (extendCfg S Φ₀) := by
  refine measurable_pi_iff.mpr (fun b => ?_)
  by_cases h : b ∈ S
  · simp only [extendCfg, h, dite_true]
    exact measurable_pi_apply (⟨b, h⟩ : S)
  · simp only [extendCfg, h, dite_false]
    exact measurable_const

omit [Fintype B] [∀ b, MeasurableSpace (Ω b)] in
theorem depOn_factor {S : Finset B} {F : (∀ b, Ω b) → ℂ} (hF : DepOn S F) (Φ₀ : ∀ b, Ω b) :
    F = (fun x => F (extendCfg S Φ₀ x)) ∘ (fun Φ (i : S) => Φ i) := by
  funext Φ
  refine hF Φ _ (fun b hb => ?_)
  simp [extendCfg, hb]

theorem indepFun_of_depOn {S T : Finset B} (hST : Disjoint S T) {F G : (∀ b, Ω b) → ℂ}
    (hF : Measurable F) (hG : Measurable G) (hFS : DepOn S F) (hGT : DepOn T G) :
    IndepFun F G (Measure.pi μ) := by
  have : ∀ b, Nonempty (Ω b) := fun b => nonempty_of_isProbabilityMeasure (μ b)
  let Φ₀ : ∀ b, Ω b := fun b => Classical.arbitrary _
  have hind : iIndepFun (fun (b : B) (Φ : ∀ b, Ω b) => Φ b) (Measure.pi μ) :=
    iIndepFun_pi (X := fun b => id) (fun b => aemeasurable_id)
  have h := hind.indepFun_finset S T hST (fun b => measurable_pi_apply b)
  have h2 := h.comp (φ := fun x => F (extendCfg S Φ₀ x)) (ψ := fun x => G (extendCfg T Φ₀ x))
    (hF.comp (measurable_extendCfg S Φ₀)) (hG.comp (measurable_extendCfg T Φ₀))
  rw [← depOn_factor hFS Φ₀, ← depOn_factor hGT Φ₀] at h2
  exact h2

theorem integral_prod_depOn {ι : Type*} (Γ : Finset ι) (S : ι → Finset B)
    (F : ι → (∀ b, Ω b) → ℂ) (hdisj : ∀ i ∈ Γ, ∀ j ∈ Γ, i ≠ j → Disjoint (S i) (S j))
    (hdep : ∀ i ∈ Γ, DepOn (S i) (F i)) (hmeas : ∀ i, Measurable (F i)) :
    ∫ Φ, ∏ i ∈ Γ, F i Φ ∂(Measure.pi μ) = ∏ i ∈ Γ, ∫ Φ, F i Φ ∂(Measure.pi μ) := by
  induction Γ using Finset.induction_on with
  | empty => simp
  | insert i Γ hi ih =>
    have hdisj' : ∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → Disjoint (S a) (S b) := fun a ha b hb hab =>
      hdisj a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
    have hdep' : ∀ a ∈ Γ, DepOn (S a) (F a) := fun a ha => hdep a (Finset.mem_insert_of_mem ha)
    rw [Finset.prod_insert hi, ← ih hdisj' hdep']
    simp_rw [Finset.prod_insert hi]
    have hT : DepOn (Γ.biUnion S) (fun Φ => ∏ j ∈ Γ, F j Φ) := fun Φ Φ' hΦ => by
      refine Finset.prod_congr rfl (fun j hj => hdep' j hj Φ Φ' (fun b hb => hΦ b ?_))
      exact Finset.mem_biUnion.mpr ⟨j, hj, hb⟩
    have hdisjT : Disjoint (S i) (Γ.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      exact fun j hj => hdisj i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun h => hi (h ▸ hj))
    have hmT : Measurable (fun Φ => ∏ j ∈ Γ, F j Φ) :=
      Finset.measurable_prod _ (fun j _ => hmeas j)
    have hind := indepFun_of_depOn μ hdisjT (hmeas i) hmT (hdep i (Finset.mem_insert_self _ _)) hT
    exact hind.integral_fun_mul_eq_mul_integral (hmeas i).aestronglyMeasurable
      hmT.aestronglyMeasurable

end Independence

section Mayer

variable {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
  {T : Type*} [Fintype T] (sup : T → Finset B) (H : T → (∀ b, Ω b) → ℂ)

/-- A function bounded in norm. -/
def Bdd {X : Type*} (F : X → ℂ) : Prop := ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C

omit [Fintype B] in
theorem Bdd.sum {X κ : Type*} {F : κ → X → ℂ} (s : Finset κ) (h : ∀ k ∈ s, Bdd (F k)) :
    Bdd (fun x => ∑ k ∈ s, F k x) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun x => by simp⟩
  | insert i s hi ih =>
    obtain ⟨C₁, h₁⟩ := h i (Finset.mem_insert_self _ _)
    obtain ⟨C₂, h₂⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    refine ⟨C₁ + C₂, fun x => ?_⟩
    show ‖∑ k ∈ insert i s, F k x‖ ≤ _
    rw [Finset.sum_insert hi]
    exact (norm_add_le _ _).trans (add_le_add (h₁ x) (h₂ x))

omit [Fintype B] in
theorem Bdd.prod {X κ : Type*} {F : κ → X → ℂ} (s : Finset κ) (h : ∀ k ∈ s, Bdd (F k)) :
    Bdd (fun x => ∏ k ∈ s, F k x) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, fun x => by simp⟩
  | insert i s hi ih =>
    obtain ⟨C₁, h₁⟩ := h i (Finset.mem_insert_self _ _)
    obtain ⟨C₂, h₂⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    refine ⟨C₁ * C₂, fun x => ?_⟩
    show ‖∏ k ∈ insert i s, F k x‖ ≤ _
    rw [Finset.prod_insert hi, norm_mul]
    exact mul_le_mul (h₁ x) (h₂ x) (norm_nonneg _) ((norm_nonneg _).trans (h₁ x))

variable {sup H} in
omit [Fintype B] [∀ b, MeasurableSpace (Ω b)] [Fintype T] in
theorem bdd_expm1 {t : T} (h : Bdd (H t)) : Bdd (fun Φ => Complex.exp (H t Φ) - 1) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨Real.exp C + 1, fun Φ => ?_⟩
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]
  exact add_le_add ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (hC Φ))) le_rfl

/-- The integrand of the activity of the polymer `Y`: the sum over connected families of terms
with union `Y` of the products of `e^{H t} - 1`. -/
def mayerAct (Y : NePoly B) (Φ : ∀ b, Ω b) : ℂ :=
  polyAct sup (fun _ : Finset T => True) (fun t => Complex.exp (H t Φ) - 1) Y

/-- The activity of the polymer `Y`. -/
def mayerK (Y : NePoly B) : ℂ := ∫ Φ, mayerAct sup H Y Φ ∂(Measure.pi μ)

variable {sup H}

omit [Fintype B] in
theorem measurable_mayerAct (hmeas : ∀ t, Measurable (H t)) (Y : NePoly B) :
    Measurable (mayerAct sup H Y) := by
  unfold mayerAct polyAct
  refine Finset.measurable_fun_sum _ (fun C _ => Finset.measurable_fun_prod _ (fun t _ => ?_))
  exact (Complex.measurable_exp.comp (hmeas t)).sub_const 1

omit [(b : B) → MeasurableSpace (Ω b)] in
omit [Fintype B] in
theorem bdd_mayerAct (hbdd : ∀ t, Bdd (H t)) (Y : NePoly B) : Bdd (mayerAct sup H Y) := by
  unfold mayerAct polyAct
  exact Bdd.sum _ (fun C _ => Bdd.prod _ (fun t _ => bdd_expm1 (hbdd t)))

omit [Fintype B] [∀ b, MeasurableSpace (Ω b)] in
theorem depOn_mayerAct (hloc : ∀ t, DepOn (sup t) (H t)) (Y : NePoly B) :
    DepOn Y.1 (mayerAct sup H Y) := by
  intro Φ Φ' hΦ
  unfold mayerAct polyAct
  refine Finset.sum_congr rfl (fun C hC => Finset.prod_congr rfl (fun t ht => ?_))
  have : sup t ⊆ Y.1 := sub_of_mem_Cfam hC ht
  show Complex.exp (H t Φ) - 1 = Complex.exp (H t Φ') - 1
  rw [hloc t Φ Φ' (fun b hb => hΦ b (this hb))]

/-- **MY (i)**: the integral of `e^{∑ H}` against a product measure is the partition function of
the polymer gas with the activities `mayerK`. -/
theorem mayer_integral_eq (hne : ∀ t, (sup t).Nonempty) (hloc : ∀ t, DepOn (sup t) (H t))
    (hmeas : ∀ t, Measurable (H t)) (hbdd : ∀ t, Bdd (H t)) :
    ∫ Φ, Complex.exp (∑ t, H t Φ) ∂(Measure.pi μ) =
      Xi (shareBlock (Subtype.val : NePoly B → Finset B)) (mayerK μ sup H) := by
  have hpt : ∀ Φ : ∀ b, Ω b, Complex.exp (∑ t, H t Φ) =
      Xi (shareBlock (Subtype.val : NePoly B → Finset B)) (fun Y => mayerAct sup H Y Φ) := by
    intro Φ
    rw [Complex.exp_sum]
    have h1 : ∏ t, Complex.exp (H t Φ) = ∏ t, (1 + (Complex.exp (H t Φ) - 1)) :=
      Finset.prod_congr rfl (fun t _ => by ring)
    rw [h1, Finset.prod_one_add, Finset.powerset_univ]
    have := decomposition (cs := sup) (A := fun _ : Finset T => True) (fun D _ t _ => hne t)
      (fun D => by simp) (fun t => Complex.exp (H t Φ) - 1)
    simpa [mayerAct] using this
  simp_rw [hpt]
  unfold Xi
  have hK : ∀ Y, Measurable (mayerAct sup H Y) := measurable_mayerAct hmeas
  have hint : ∀ Γ : Finset (NePoly B), Integrable (fun Φ => ∏ Y ∈ Γ, mayerAct sup H Y Φ)
      (Measure.pi μ) := fun Γ => by
    obtain ⟨C, hC⟩ := (Bdd.prod Γ (fun Y _ => bdd_mayerAct hbdd Y) :
      Bdd (fun Φ => ∏ Y ∈ Γ, mayerAct sup H Y Φ))
    exact Integrable.of_bound (Finset.measurable_prod _ (fun Y _ => hK Y)).aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)
  rw [integral_finsetSum _ (fun Γ _ => hint Γ)]
  refine Finset.sum_congr rfl (fun Γ hΓ => ?_)
  rw [Finset.mem_filter] at hΓ
  have hdisj : ∀ Y ∈ Γ, ∀ Y' ∈ Γ, Y ≠ Y' → Disjoint Y.1 Y'.1 := by
    intro Y hY Y' hY' hne'
    have := hΓ.2 Y hY Y' hY' hne'
    rw [lnk_shareBlock] at this
    exact not_not.mp this
  exact integral_prod_depOn μ Γ (fun Y => Y.1) (fun Y => mayerAct sup H Y) hdisj
    (fun Y _ => depOn_mayerAct hloc Y) hK

end Mayer

section Bound

variable {B : Type*} [Fintype B] {T : Type*} [Fintype T] (sup : T → Finset B)
  (d : Finset B → ℝ) (κ0 κ1 c H0 : ℝ)

/-- The weight `ρ t = 2 H₀ e^{-κ₀ d(t)}` of a term. -/
def mayerRho (t : T) : ℝ := 2 * H0 * Real.exp (-κ0 * d (sup t))

variable {sup d κ0 κ1 c H0}

omit [Fintype B] [Fintype T] in
theorem mayerRho_nonneg (hH0 : 0 ≤ H0) (t : T) : 0 ≤ mayerRho sup d κ0 H0 t := by
  unfold mayerRho; positivity

omit [Fintype B] [Fintype T] in
/-- A connected family with union `Y` has weight at most `e^{-κ₁ d(Y)} e^{-κ₁ c}` times the
product of the enlarged weights `ρ e^{κ₁ c}` (this is where (G3) enters). -/
theorem prod_a_le (hκ1 : 0 ≤ κ1) (hρ : ∀ t, 0 ≤ mayerRho sup d κ0 H0 t)
    (hG3 : ∀ C : Finset T, ConnSet sup C →
      d (unionCs sup C) ≤ ∑ t ∈ C, d (sup t) + c * ((C.card : ℝ) - 1))
    {C : Finset T} (hC : ConnSet sup C) :
    ∏ t ∈ C, (mayerRho sup d κ0 H0 t * Real.exp (-κ1 * d (sup t))) ≤
      Real.exp (-κ1 * d (unionCs sup C)) * Real.exp (-κ1 * c) *
        ∏ t ∈ C, (mayerRho sup d κ0 H0 t * Real.exp (κ1 * c)) := by
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_const,
    ← Real.exp_nat_mul]
  have hprod : 0 ≤ ∏ t ∈ C, mayerRho sup d κ0 H0 t :=
    Finset.prod_nonneg (fun t _ => hρ t)
  have h3 := hG3 C hC
  have hexp : Real.exp (-κ1 * ∑ t ∈ C, d (sup t)) ≤
      Real.exp (-κ1 * d (unionCs sup C)) * Real.exp (-κ1 * c) *
        Real.exp ((C.card : ℝ) * (κ1 * c)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left h3 hκ1
    nlinarith
  calc (∏ t ∈ C, mayerRho sup d κ0 H0 t) * Real.exp (∑ t ∈ C, -κ1 * d (sup t))
      = (∏ t ∈ C, mayerRho sup d κ0 H0 t) * Real.exp (-κ1 * ∑ t ∈ C, d (sup t)) := by
        rw [Finset.mul_sum]
    _ ≤ (∏ t ∈ C, mayerRho sup d κ0 H0 t) * (Real.exp (-κ1 * d (unionCs sup C)) *
        Real.exp (-κ1 * c) * Real.exp ((C.card : ℝ) * (κ1 * c))) :=
        mul_le_mul_of_nonneg_left hexp hprod
    _ = _ := by ring

/-- The terms supported in `Y`. -/
def termsIn (sup : T → Finset B) (Y : Finset B) : Finset T :=
  Finset.univ.filter (fun t => sup t ⊆ Y)

omit [Fintype B] in
theorem cfam_subset_powerset {Y : NePoly B} :
    Cfam sup (fun _ : Finset T => True) Y.1 ⊆ ((termsIn sup Y.1).powerset).erase ∅ := by
  intro C hC
  have h := mem_Cfam.mp hC
  rw [Finset.mem_erase, Finset.mem_powerset]
  refine ⟨fun h0 => ?_, fun t ht => ?_⟩
  · have := h.1.1
    rw [h0] at this
    exact Finset.not_nonempty_empty this
  · simp only [termsIn, Finset.mem_filter, Finset.mem_univ, true_and]
    exact sub_of_mem_Cfam hC ht

omit [Fintype B] in
/-- The entropy sum for the terms in `Y`. -/
theorem sum_rho_le (hH0 : 0 ≤ H0) {K0 : ℝ} {Y : Finset B}
    (hY : ∀ t ∈ termsIn sup Y, (sup t).Nonempty)
    (hG2 : ∀ b : B, ∑ t ∈ Finset.univ.filter (fun t => b ∈ sup t), Real.exp (-κ0 * d (sup t)) ≤ K0) :
    ∑ t ∈ termsIn sup Y, mayerRho sup d κ0 H0 t * Real.exp (κ1 * c) ≤
      (2 * H0 * K0 * Real.exp (κ1 * c)) * (Y.card : ℝ) := by
  set r : T → ℝ := fun t => mayerRho sup d κ0 H0 t * Real.exp (κ1 * c) with hr
  have hr0 : ∀ t, 0 ≤ r t := fun t => mul_nonneg (mayerRho_nonneg hH0 t) (Real.exp_pos _).le
  calc ∑ t ∈ termsIn sup Y, r t
      ≤ ∑ t ∈ termsIn sup Y, ∑ b ∈ Y, (if b ∈ sup t then r t else 0) := by
        refine Finset.sum_le_sum (fun t ht => ?_)
        obtain ⟨b, hb⟩ := hY t ht
        have hbY : b ∈ Y := by
          simp only [termsIn, Finset.mem_filter, Finset.mem_univ, true_and] at ht
          exact ht hb
        calc r t = (if b ∈ sup t then r t else 0) := by rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
          _ ≤ _ := Finset.single_le_sum (f := fun b => (if b ∈ sup t then r t else 0))
            (fun _ _ => by split_ifs <;> simp [hr0 t]) hbY
    _ = ∑ b ∈ Y, ∑ t ∈ termsIn sup Y, (if b ∈ sup t then r t else 0) := Finset.sum_comm
    _ ≤ ∑ b ∈ Y, (2 * H0 * K0 * Real.exp (κ1 * c)) := by
        refine Finset.sum_le_sum (fun b _ => ?_)
        calc ∑ t ∈ termsIn sup Y, (if b ∈ sup t then r t else 0)
            ≤ ∑ t, (if b ∈ sup t then r t else 0) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun t _ _ => by split_ifs <;> simp [hr0 t])
          _ = ∑ t ∈ Finset.univ.filter (fun t => b ∈ sup t), r t := by
              rw [Finset.sum_filter]
          _ = 2 * H0 * Real.exp (κ1 * c) *
              ∑ t ∈ Finset.univ.filter (fun t => b ∈ sup t), Real.exp (-κ0 * d (sup t)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun t _ => ?_)
              simp only [hr, mayerRho]; ring
          _ ≤ 2 * H0 * Real.exp (κ1 * c) * K0 :=
              mul_le_mul_of_nonneg_left (hG2 b) (by positivity)
          _ = _ := by ring
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end Bound

section RealBound

/-- The real-variable inequality closing the proof of MY (iii). -/
theorem mayer_real_bound {q c1 κ1 c D n : ℝ} (hq0 : 0 ≤ q) (hc1 : 0 ≤ c1) (hκ1 : 0 ≤ κ1)
    (hc : 0 ≤ c) (hD : 0 ≤ D) (hn : 0 ≤ n) (hqc : q * c1 ≤ 1 / 2) (hG1 : n ≤ c1 * (1 + D)) :
    Real.exp (-κ1 * D) * Real.exp (-κ1 * c) * (Real.exp (q * n) - 1) ≤
      2 * q * c1 * Real.exp (-(κ1 - 3 / 2) * D) := by
  set x : ℝ := q * n with hx
  have hx0 : 0 ≤ x := mul_nonneg hq0 hn
  have hx1 : x ≤ q * c1 * (1 + D) := by
    rw [hx]; calc q * n ≤ q * (c1 * (1 + D)) := mul_le_mul_of_nonneg_left hG1 hq0
      _ = _ := by ring
  have hx2 : q * c1 * (1 + D) ≤ (1 + D) / 2 := by nlinarith
  have h1 : Real.exp x - 1 ≤ x * Real.exp x := by
    have := Real.add_one_le_exp (-x)
    have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos x]
  have h3 : x * Real.exp x ≤ q * c1 * (1 + D) * Real.exp ((1 + D) / 2) :=
    mul_le_mul hx1 (Real.exp_le_exp.mpr (hx1.trans hx2)) (Real.exp_pos _).le
      (by positivity)
  have h4 : 1 + D ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have h5 : q * c1 * (1 + D) * Real.exp ((1 + D) / 2) ≤
      q * c1 * (Real.exp D * Real.exp (1 / 2) * Real.exp (D / 2)) := by
    have e1 : Real.exp ((1 + D) / 2) = Real.exp (1 / 2) * Real.exp (D / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e1]
    have hqc0 : 0 ≤ q * c1 := mul_nonneg hq0 hc1
    calc q * c1 * (1 + D) * (Real.exp (1 / 2) * Real.exp (D / 2))
        ≤ q * c1 * Real.exp D * (Real.exp (1 / 2) * Real.exp (D / 2)) := by
          gcongr
      _ = q * c1 * (Real.exp D * Real.exp (1 / 2) * Real.exp (D / 2)) := by ring
  have h6 : Real.exp (1 / 2) ≤ 2 := by
    have : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2)]
  have h7 : Real.exp (-κ1 * c) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hqc0 : 0 ≤ q * c1 := mul_nonneg hq0 hc1
  have h8 : Real.exp (q * n) - 1 ≤ q * c1 * (Real.exp D * Real.exp (1 / 2) * Real.exp (D / 2)) :=
    h1.trans (h3.trans h5)
  calc Real.exp (-κ1 * D) * Real.exp (-κ1 * c) * (Real.exp (q * n) - 1)
      ≤ Real.exp (-κ1 * D) * 1 * (q * c1 * (Real.exp D * Real.exp (1 / 2) * Real.exp (D / 2))) := by
        have : 0 ≤ Real.exp (q * n) - 1 := by
          have := Real.add_one_le_exp (q * n); linarith
        gcongr
    _ ≤ Real.exp (-κ1 * D) * 1 * (q * c1 * (Real.exp D * 2 * Real.exp (D / 2))) := by
        gcongr
    _ = 2 * q * c1 * (Real.exp (-κ1 * D) * Real.exp D * Real.exp (D / 2)) := by ring
    _ = 2 * q * c1 * Real.exp (-(κ1 - 3 / 2) * D) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring

end RealBound

section Activity

variable {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
  {T : Type*} [Fintype T] {sup : T → Finset B} {H : T → (∀ b, Ω b) → ℂ}
  {d : Finset B → ℝ} {κ0 κ1 c H0 : ℝ}

omit [Fintype B] [(b : B) → MeasurableSpace (Ω b)] [Fintype T] in
theorem norm_expm1_le_rho (hH0 : 0 ≤ H0) (hH0' : H0 ≤ Real.log 2) (hκ0 : 0 ≤ κ0)
    (hκ1 : 0 ≤ κ1) (hd : ∀ Y, 0 ≤ d Y) (t : T) (Φ : ∀ b, Ω b)
    (hH : ‖H t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d (sup t))) :
    ‖Complex.exp (H t Φ) - 1‖ ≤ mayerRho sup d κ0 H0 t * Real.exp (-κ1 * d (sup t)) := by
  have hle : Real.exp (-(κ0 + κ1) * d (sup t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [hd (sup t)])
  have h1 : ‖H t Φ‖ ≤ 1 := by
    have : H0 * Real.exp (-(κ0 + κ1) * d (sup t)) ≤ H0 := by
      calc _ ≤ H0 * 1 := mul_le_mul_of_nonneg_left hle hH0
        _ = H0 := mul_one _
    have h2 : Real.log 2 ≤ 1 := (Real.log_two_lt_d9).le.trans (by norm_num)
    linarith
  refine (Complex.norm_exp_sub_one_le h1).trans ?_
  have : mayerRho sup d κ0 H0 t * Real.exp (-κ1 * d (sup t)) =
      2 * (H0 * Real.exp (-(κ0 + κ1) * d (sup t))) := by
    unfold mayerRho
    rw [mul_assoc, mul_assoc, ← Real.exp_add]
    have : -κ0 * d (sup t) + -κ1 * d (sup t) = -(κ0 + κ1) * d (sup t) := by ring
    rw [this]
  rw [this]
  exact mul_le_mul_of_nonneg_left hH (by norm_num)

omit [Fintype B] [(b : B) → MeasurableSpace (Ω b)] in
theorem norm_mayerAct_le (hH0 : 0 ≤ H0) (hH0' : H0 ≤ Real.log 2) (hκ0 : 0 ≤ κ0)
    (hκ1 : 0 ≤ κ1) (hd : ∀ Y, 0 ≤ d Y)
    (hH : ∀ t Φ, ‖H t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d (sup t))) (Y : NePoly B)
    (Φ : ∀ b, Ω b) :
    ‖mayerAct sup H Y Φ‖ ≤ ∑ C ∈ Cfam sup (fun _ : Finset T => True) Y.1,
      ∏ t ∈ C, (mayerRho sup d κ0 H0 t * Real.exp (-κ1 * d (sup t))) := by
  unfold mayerAct polyAct
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun C _ => ?_))
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun t _ => norm_nonneg _)
    (fun t _ => norm_expm1_le_rho hH0 hH0' hκ0 hκ1 hd t Φ (hH t Φ))

/-- **MY (iii)**: the bound on the activities of the Mayer polymer gas.  With
`q = 2 H₀ K₀ e^{κ₁ c}` and `q c₁ ≤ 1/2`, every polymer `Y` with `|Y| ≤ c₁ (1 + d(Y))` has
`|K(Y)| ≤ 2 q c₁ e^{-(κ₁ - 3/2) d(Y)}`. -/
theorem mayer_activity_bound (hH0 : 0 ≤ H0) (hH0' : H0 ≤ Real.log 2) (hκ0 : 0 ≤ κ0)
    (hκ1 : 0 ≤ κ1) (hc : 0 ≤ c) (hd : ∀ Y, 0 ≤ d Y) (hne : ∀ t, (sup t).Nonempty)
    (hH : ∀ t Φ, ‖H t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d (sup t)))
    {K0 : ℝ} (hG2 : ∀ b : B, ∑ t ∈ Finset.univ.filter (fun t => b ∈ sup t),
      Real.exp (-κ0 * d (sup t)) ≤ K0)
    (hG3 : ∀ C : Finset T, ConnSet sup C →
      d (unionCs sup C) ≤ ∑ t ∈ C, d (sup t) + c * ((C.card : ℝ) - 1))
    {c1 : ℝ} (hc1 : 0 ≤ c1) (hq : 2 * H0 * K0 * Real.exp (κ1 * c) * c1 ≤ 1 / 2)
    (Y : NePoly B) (hG1 : (Y.1.card : ℝ) ≤ c1 * (1 + d Y.1)) :
    ‖mayerK μ sup H Y‖ ≤
      2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 * Real.exp (-(κ1 - 3 / 2) * d Y.1) := by
  obtain ⟨b0, hb0⟩ := Y.2
  have hK0 : 0 ≤ K0 := le_trans (Finset.sum_nonneg (fun t _ => (Real.exp_pos _).le)) (hG2 b0)
  set q := 2 * H0 * K0 * Real.exp (κ1 * c) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hρ := mayerRho_nonneg (sup := sup) (d := d) (κ0 := κ0) hH0
  have hr0 : ∀ t, 0 ≤ mayerRho sup d κ0 H0 t * Real.exp (κ1 * c) := fun t =>
    mul_nonneg (hρ t) (Real.exp_pos _).le
  have hpre : 0 ≤ Real.exp (-κ1 * d Y.1) * Real.exp (-κ1 * c) := by positivity
  have hΦ : ∀ Φ, ‖mayerAct sup H Y Φ‖ ≤
      Real.exp (-κ1 * d Y.1) * Real.exp (-κ1 * c) * (Real.exp (q * Y.1.card) - 1) := by
    intro Φ
    refine (norm_mayerAct_le hH0 hH0' hκ0 hκ1 hd hH Y Φ).trans ?_
    calc ∑ C ∈ Cfam sup (fun _ : Finset T => True) Y.1,
          ∏ t ∈ C, (mayerRho sup d κ0 H0 t * Real.exp (-κ1 * d (sup t)))
        ≤ ∑ C ∈ Cfam sup (fun _ : Finset T => True) Y.1,
          Real.exp (-κ1 * d Y.1) * Real.exp (-κ1 * c) *
            ∏ t ∈ C, (mayerRho sup d κ0 H0 t * Real.exp (κ1 * c)) :=
          Finset.sum_le_sum (fun C hC => by
            have h := mem_Cfam.mp hC
            have := prod_a_le hκ1 hρ hG3 h.1
            rwa [h.2.2] at this)
      _ = Real.exp (-κ1 * d Y.1) * Real.exp (-κ1 * c) *
          ∑ C ∈ Cfam sup (fun _ : Finset T => True) Y.1,
            ∏ t ∈ C, (mayerRho sup d κ0 H0 t * Real.exp (κ1 * c)) := by rw [← Finset.mul_sum]
      _ ≤ Real.exp (-κ1 * d Y.1) * Real.exp (-κ1 * c) *
          (Real.exp (∑ t ∈ termsIn sup Y.1, mayerRho sup d κ0 H0 t * Real.exp (κ1 * c)) - 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hpre
          refine le_trans ?_ (sum_powerset_erase_le _ hr0 (termsIn sup Y.1))
          exact Finset.sum_le_sum_of_subset_of_nonneg cfam_subset_powerset
            (fun _ _ _ => Finset.prod_nonneg (fun t _ => hr0 t))
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ hpre
          have := sum_rho_le (sup := sup) (d := d) (κ0 := κ0) (κ1 := κ1) (c := c) hH0
            (Y := Y.1) (fun t _ => hne t) hG2
          have := Real.exp_le_exp.mpr this
          linarith
  have hint := norm_integral_le_of_norm_le_const (μ := Measure.pi μ)
    (f := mayerAct sup H Y) (Filter.Eventually.of_forall hΦ)
  have hreal : (Measure.pi μ).real Set.univ = 1 := by simp
  unfold mayerK
  refine hint.trans ?_
  rw [hreal, mul_one]
  have := mayer_real_bound (q := q) (c1 := c1) (κ1 := κ1) (c := c) (D := d Y.1)
    (n := (Y.1.card : ℝ)) hq0 hc1 hκ1 hc (hd _) (Nat.cast_nonneg _) hq hG1
  exact this

end Activity

end Balaban.Polymer
