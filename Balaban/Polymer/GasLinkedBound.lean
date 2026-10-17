/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.GasLinkedEq

/-!
# Activity estimate for a linked gas

An activated linked family is a landed admissible family when activation is contained in the
charged footprint. Therefore the landed absolute family majorants, entropy bound, and heavy
counting estimates apply with no loss in their numerical constants.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset

namespace Balaban.Polymer

section Bound

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {allRequired : Yt → Bool} {activation footprint : Yt → Finset B}
  {zs cr : Zt → Finset B} {β : Yt → ℂ} {τ : Zt → ℂ}

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- A linked family is landed-admissible when every activation set lies in its footprint. -/
theorem gasLinkedA_imp_gasA (hact : ∀ y, activation y ⊆ footprint y)
    (D : Finset (Yt ⊕ Zt))
    (h : gasLinkedA allRequired activation zs cr D) :
    gasA footprint zs cr D := by
  refine ⟨h.1, ?_⟩
  intro y hy
  have hmeet := gasLinkedActive_footprint_meets hact y D.toRight (h.2 y hy)
  rw [Finset.disjoint_biUnion_right] at hmeet
  push Not at hmeet
  exact hmeet

/-- The connected linked activity has the same bound as the landed gas when the decay and
geometry are measured on charged footprints. The geometric subadditivity premise is stated
for the landed family so that its existing absolute family majorant applies directly. -/
theorem gasLinked_activity_bound {d : Finset B → ℝ}
    {B0 κ' κ'' c c1 c2 p h : ℝ}
    (hact : ∀ y, activation y ⊆ footprint y)
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c)
    (hc1 : 0 ≤ c1) (hp : 0 ≤ p) (hd : ∀ Y, 0 ≤ d Y)
    (hz : ∀ z, (zs z).Nonempty) (hcr : ∀ z, cr z ⊆ zs z)
    (hB : ∀ y, ‖β y‖ ≤ B0 * Real.exp (-κ'' * d (footprint y)))
    (hτ : ∀ z, ‖τ z‖ ≤ Real.exp (-p - h * (zs z).card))
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt),
      ConnSet (gasCs footprint zs) C → gasA footprint zs cr C →
      d (unionCs (gasCs footprint zs) C) ≤
        ∑ t ∈ C, d (gasCs footprint zs t) + c * ((C.card : ℝ) - 1))
    {K0' K0'' : ℝ} (hK0' : 0 ≤ K0')
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ footprint y),
      Real.exp (-(κ'' - κ') * d (footprint y)) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) ≤ K0'' ^ v)
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' +
      κ' * (c2 + c) + c1 + 3 + Real.log K0'' ≤ h)
    (X : NePoly B) (hG1 : (X.1.card : ℝ) ≤ c1 * (1 + d X.1)) :
    ‖gasLinkedK allRequired activation footprint zs cr β τ X‖ ≤
      3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d X.1) := by
  set Cc : ℝ := B0 * Real.exp B0 * Real.exp (κ' * c) * K0' with hCc
  set lam : ℝ := h - κ' * (c2 + c) - Cc with hlam
  have hlam' : c1 + 3 + Real.log K0'' ≤ lam := by rw [hlam]; linarith
  have hCc0 : 0 ≤ Cc := by positivity
  set ζ : Zt → ℝ := fun z => Real.exp (-p) * Real.exp (-lam * (zs z).card) with hζ
  have hζ0 : ∀ z, 0 ≤ ζ z := fun z => by positivity
  have hsub : Cfam (gasCs footprint zs)
      (gasLinkedA allRequired activation zs cr) X.1 ⊆
      Cfam (gasCs footprint zs) (gasA footprint zs cr) X.1 := by
    intro C hC
    obtain ⟨hconn, hA, hU⟩ := mem_Cfam.mp hC
    exact mem_Cfam.mpr ⟨hconn, gasLinkedA_imp_gasA hact C hA, hU⟩
  have hfam : ∀ C ∈ Cfam (gasCs footprint zs) (gasA footprint zs cr) X.1,
      Real.exp (κ' * d X.1) * ‖∏ t ∈ C, gasW β τ t‖ ≤
        (∏ y ∈ C.toLeft, gasG footprint d B0 κ' κ'' c y) *
          ∏ z ∈ C.toRight, gasAz zs κ' c c2 p h z :=
    fun C hC => gas_family_bound hB0 hκ' hκ'' hc hd hz hB hτ hzd hG3 hC
  have h1 : Real.exp (κ' * d X.1) *
      ‖gasLinkedK allRequired activation footprint zs cr β τ X‖ ≤
      ∑ C ∈ Cfam (gasCs footprint zs) (gasA footprint zs cr) X.1,
        (∏ y ∈ C.toLeft, gasG footprint d B0 κ' κ'' c y) *
          ∏ z ∈ C.toRight, gasAz zs κ' c c2 p h z := by
    unfold gasLinkedK polyAct gasLinkedW
    calc
      Real.exp (κ' * d X.1) *
          ‖∑ C ∈ Cfam (gasCs footprint zs)
              (gasLinkedA allRequired activation zs cr) X.1, ∏ t ∈ C, gasW β τ t‖
          ≤ Real.exp (κ' * d X.1) *
              ∑ C ∈ Cfam (gasCs footprint zs)
                (gasLinkedA allRequired activation zs cr) X.1,
                  ‖∏ t ∈ C, gasW β τ t‖ :=
            mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.exp_pos _).le
      _ = ∑ C ∈ Cfam (gasCs footprint zs)
            (gasLinkedA allRequired activation zs cr) X.1,
              Real.exp (κ' * d X.1) * ‖∏ t ∈ C, gasW β τ t‖ := by
            rw [Finset.mul_sum]
      _ ≤ ∑ C ∈ Cfam (gasCs footprint zs)
            (gasA footprint zs cr) X.1,
              Real.exp (κ' * d X.1) * ‖∏ t ∈ C, gasW β τ t‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun C _ _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      _ ≤ _ := Finset.sum_le_sum hfam
  have h2 := sum_cfam_le (cy := footprint) (zs := zs) (cr := cr)
    (gasG footprint d B0 κ' κ'' c) (gasAz zs κ' c c2 p h)
    (gasG_nonneg hB0) gasAz_nonneg X.1
  have h3 : ∀ Γ ∈ ((gasZsub zs X.1).powerset).erase ∅,
      (∏ z ∈ Γ, gasAz zs κ' c c2 p h z) *
          ∏ y ∈ gasYm footprint cr Γ, (1 + gasG footprint d B0 κ' κ'' c y) ≤
        ∏ z ∈ Γ, ζ z := by
    intro Γ _
    calc
      _ ≤ (∏ z ∈ Γ, gasAz zs κ' c c2 p h z) *
          Real.exp (Cc * ∑ z ∈ Γ, ((zs z).card : ℝ)) :=
        mul_le_mul_of_nonneg_left (gas_prod_le hB0 hK0' hcr hent Γ)
          (Finset.prod_nonneg (fun z _ => gasAz_nonneg z))
      _ = ∏ z ∈ Γ, (gasAz zs κ' c c2 p h z * Real.exp (Cc * (zs z).card)) := by
        rw [Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]
      _ = ∏ z ∈ Γ, ζ z := by
        refine Finset.prod_congr rfl (fun z _ => ?_)
        simp only [gasAz, hζ, hlam]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have h4 := (Finset.sum_le_sum h3).trans
    (sum_powerset_erase_le ζ hζ0 (gasZsub zs X.1))
  have h5 : ∑ z ∈ gasZsub zs X.1, ζ z ≤
      X.1.card * (Real.exp (-p) * Real.exp (-(c1 + 2))) := by
    refine (sum_le_sum_cover (gasZsub zs X.1) zs X.1 ζ hζ0
      (fun z hz' => ?_)).trans ?_
    · obtain ⟨b, hb⟩ := hz z
      simp only [gasZsub, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
      exact ⟨b, hz' hb, hb⟩
    · calc
        ∑ b ∈ X.1, ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z), ζ z
            ≤ ∑ b ∈ X.1, Real.exp (-p) * Real.exp (-(c1 + 2)) := by
              refine Finset.sum_le_sum (fun b _ => ?_)
              rw [hζ, ← Finset.mul_sum]
              exact mul_le_mul_of_nonneg_left
                (heavy_entropy hc1 hK1 hz hcount hlam' b) (Real.exp_pos _).le
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have h6 := gas_real_bound (p := p) (c1 := c1) (D := d X.1)
    (n := (X.1.card : ℝ)) hp hc1 (hd _) (Nat.cast_nonneg _) hG1
  have h7 : Real.exp (κ' * d X.1) *
      ‖gasLinkedK allRequired activation footprint zs cr β τ X‖ ≤
      3 * c1 * Real.exp (-p) * Real.exp (2 * d X.1) := by
    refine h1.trans (h2.trans (h4.trans ?_))
    have := Real.exp_le_exp.mpr h5
    linarith
  have h8 : ‖gasLinkedK allRequired activation footprint zs cr β τ X‖ ≤
      Real.exp (-κ' * d X.1) *
        (3 * c1 * Real.exp (-p) * Real.exp (2 * d X.1)) := by
    have he : Real.exp (-κ' * d X.1) * Real.exp (κ' * d X.1) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      ‖gasLinkedK allRequired activation footprint zs cr β τ X‖ =
          Real.exp (-κ' * d X.1) *
            (Real.exp (κ' * d X.1) *
              ‖gasLinkedK allRequired activation footprint zs cr β τ X‖) := by
          rw [← mul_assoc, he, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left h7 (Real.exp_pos _).le
  refine h8.trans (le_of_eq ?_)
  have he : Real.exp (-κ' * d X.1) * Real.exp (2 * d X.1) =
      Real.exp (-(κ' - 2) * d X.1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← he]
  ring

/-- The landed activity estimate is the intersection-mode specialization of the linked
estimate. Its numeric hypotheses and conclusion are unchanged. -/
theorem gas_activity_bound_of_gasLinked {d : Finset B → ℝ}
    {B0 κ' κ'' c c1 c2 p h : ℝ}
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c)
    (hc1 : 0 ≤ c1) (hp : 0 ≤ p) (hd : ∀ Y, 0 ≤ d Y)
    (hz : ∀ z, (zs z).Nonempty) (hcr : ∀ z, cr z ⊆ zs z)
    (hB : ∀ y, ‖β y‖ ≤ B0 * Real.exp (-κ'' * d (footprint y)))
    (hτ : ∀ z, ‖τ z‖ ≤ Real.exp (-p - h * (zs z).card))
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt),
      ConnSet (gasCs footprint zs) C → gasA footprint zs cr C →
      d (unionCs (gasCs footprint zs) C) ≤
        ∑ t ∈ C, d (gasCs footprint zs t) + c * ((C.card : ℝ) - 1))
    {K0' K0'' : ℝ} (hK0' : 0 ≤ K0')
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ footprint y),
      Real.exp (-(κ'' - κ') * d (footprint y)) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) ≤ K0'' ^ v)
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' +
      κ' * (c2 + c) + c1 + 3 + Real.log K0'' ≤ h)
    (X : NePoly B) (hG1 : (X.1.card : ℝ) ≤ c1 * (1 + d X.1)) :
    ‖gasK footprint zs cr β τ X‖ ≤
      3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d X.1) := by
  simpa only [gasLinkedK_intersection_eq] using
    (gasLinked_activity_bound (allRequired := fun _ => false)
      (activation := footprint) (footprint := footprint) (zs := zs) (cr := cr)
      (β := β) (τ := τ) (fun _ => Finset.Subset.rfl) hB0 hκ' hκ'' hc
      hc1 hp hd hz hcr hB hτ hzd hG3 hK0' hent hK1 hcount hh X hG1)

end Bound

end Balaban.Polymer
