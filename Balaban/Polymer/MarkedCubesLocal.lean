/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MarkedCubes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 3.4: explicit local terms and locality (FLUCTUATION.md §3.4)

The local terms `P(S)` and `G*(Y₀,S)` of `marked_cubes` are made explicit (`Pst`, `Gst`) and shown
to depend only on the pre-summed terms inside `S` and on the measure on `S`
(`Pst_congr`, `Gst_congr`).
-/

@[expose] public section

namespace Balaban.Polymer

open MeasureTheory

section Measure

variable {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]

/-- Integrals of a function depending only on `Z` see the product measure only through `Z`. -/
theorem integral_pi_congr_depOn (μ μ' : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
    [∀ b, IsProbabilityMeasure (μ' b)] {Z : Finset B} (hμ : ∀ b ∈ Z, μ b = μ' b)
    {F : (∀ b, Ω b) → ℂ} (hF : DepOn Z F) :
    ∫ Φ, F Φ ∂(Measure.pi μ) = ∫ Φ, F Φ ∂(Measure.pi μ') := by
  classical
  have : ∀ b, Nonempty (Ω b) := fun b => nonempty_of_isProbabilityMeasure (μ b)
  let p : B → Prop := fun b => b ∈ Z
  let e := MeasurableEquiv.piEquivPiSubtypeProd Ω p
  let y0 : ∀ i : {i // ¬ p i}, Ω i := fun i => Classical.arbitrary _
  let g : (∀ i : {i // p i}, Ω i) → ℂ := fun x => F (e.symm (x, y0))
  have hkey : ∀ w, F (e.symm w) = g w.1 := by
    intro w
    refine hF _ _ (fun b hb => ?_)
    show (Equiv.piEquivPiSubtypeProd p Ω).symm w b = (Equiv.piEquivPiSubtypeProd p Ω).symm (w.1, y0) b
    have hb' : p b := hb
    rw [Equiv.piEquivPiSubtypeProd_symm_apply, Equiv.piEquivPiSubtypeProd_symm_apply]
    simp [hb']
  have h1 : ∀ (ν : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (ν b)],
      ∫ Φ, F Φ ∂(Measure.pi ν) = ∫ x, g x ∂(Measure.pi fun i : {i // p i} => ν i) := by
    intro ν _
    have hmp := measurePreserving_piEquivPiSubtypeProd ν p
    have := hmp.integral_comp' (g := fun w => F (e.symm w))
    have h2 : ∫ Φ, F Φ ∂(Measure.pi ν) = ∫ x, F (e.symm (e x)) ∂(Measure.pi ν) := by simp
    rw [h2, this]
    simp_rw [hkey]
    rw [integral_fun_fst]
    simp
    convert rfl
  rw [h1 μ, h1 μ']
  congr 2
  funext i
  exact hμ i.1 i.2

end Measure

section Mayer

variable {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (μ μ' : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)] [∀ b, IsProbabilityMeasure (μ' b)]
  {T : Type*} [Fintype T] (sup : T → Finset B) {H H' : T → (∀ b, Ω b) → ℂ}

/-- Locality of the Mayer activity `K(Z)`: it sees only the terms inside `Z` and the measure on `Z`. -/
theorem mayerK_congr (hloc : ∀ t, DepOn (sup t) (H t)) (Z : NePoly B)
    (hμ : ∀ b ∈ Z.1, μ b = μ' b) (hH : ∀ t, sup t ⊆ Z.1 → H t = H' t) :
    mayerK μ sup H Z = mayerK μ' sup H' Z := by
  have hact : mayerAct sup H Z = mayerAct sup H' Z := by
    funext Φ
    unfold mayerAct polyAct
    refine Finset.sum_congr rfl (fun C hC => Finset.prod_congr rfl (fun t ht => ?_))
    show Complex.exp (H t Φ) - 1 = Complex.exp (H' t Φ) - 1
    rw [hH t (sub_of_mem_Cfam hC ht)]
  unfold mayerK
  rw [← hact]
  exact integral_pi_congr_depOn μ μ' hμ (depOn_mayerAct hloc Z)

end Mayer

end Balaban.Polymer

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

section Explicit

variable {Lb : Type*} [Fintype Lb]

/-- **The local term `P(S)` of `log Ξ`** (Theorem 3.4): the `S`-term of the cluster sum of the
activities `K(Z)` of the pre-summed system. -/
noncomputable def Pst {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] (Lab : CubeLabels m₀ j Ω Lb)
    (H : Lb → (∀ b, Ωb b) → ℂ) (S : Finset 𝔅) : ℂ :=
  PY (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
    (fun Z => mayerK μ Subtype.val (presum Lab H) Z) S

/-- **The local term `G*(Y₀, S)` of `⟨G⟩`** (Theorem 3.4): the derivative at `0` of the `S`-term
of the cluster sum when the mark `λ G` is added to the term of `S₀ = blocksOf Y₀`. -/
noncomputable def Gst {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] (Lab : CubeLabels m₀ j Ω Lb)
    (H : Lb → (∀ b, Ωb b) → ℂ) (S₀ : Finset 𝔅) (G : (∀ b, Ωb b) → ℂ) (S : Finset 𝔅) : ℂ :=
  D1 () (Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
    (marksK μ Subtype.val (presum Lab H) (gMark S₀ G)) S)

theorem Ff_zero_eq_Pst {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] (Lab : CubeLabels m₀ j Ω Lb)
    (H : Lb → (∀ b, Ωb b) → ℂ) (S₀ : Finset 𝔅) (G : (∀ b, Ωb b) → ℂ) (S : Finset 𝔅) :
    Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
      (marksK μ Subtype.val (presum Lab H) (gMark S₀ G)) S 0 = Pst μ Lab H S := by
  unfold Ff Pst marksK
  have : Hlam (presum Lab H) (gMark S₀ G) (0 : Unit → ℂ) = presum Lab H := by
    funext t Φ; simp [Hlam]
  simp only [this]

open Classical in
/-- **Theorem 3.4, one mark, with the local terms explicit**: `marked_cubes` with
`P = Pst` and `G*(Y₀, ·) = Gst`. -/
theorem marked_cubes_explicit {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc F0 : ℝ}
    (A : LabelAct Lab Ωb εH κH κ0 Kc) (y0 : Lb) (G : (∀ b, Ωb b) → ℂ)
    (hGm : Measurable G) (hGdep : DepOn (blocksOf m₀ j Ω (Lab.ysite y0)) G)
    (hG : ∀ Φ, ‖G Φ‖ ≤ F0 * Real.exp (-κG * Lab.dl y0))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH) (hF0 : 0 < F0)
    (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))) :
    (∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ) ≠ 0) ∧
    (∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ) = Complex.exp (∑ Y, Pst μ Lab A.H Y) ∧
      ∀ Y : Finset 𝔅, Y.Nonempty →
        ‖Pst μ Lab A.H Y‖ ≤ εH * Kc * CPE d L Kc κH κ0 κ' * Real.exp (-κ' * dExt Y)) ∧
    ((∫ Φ, G Φ * Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ)) /
        (∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ)) =
        ∑ Y, Gst μ Lab A.H (blocksOf m₀ j Ω (Lab.ysite y0)) G Y ∧
      (∀ Y : Finset 𝔅, ¬ blocksOf m₀ j Ω (Lab.ysite y0) ⊆ Y →
        Gst μ Lab A.H (blocksOf m₀ j Ω (Lab.ysite y0)) G Y = 0) ∧
      ∀ Y : Finset 𝔅, ‖Gst μ Lab A.H (blocksOf m₀ j Ω (Lab.ysite y0)) G Y‖ ≤
        CPE d L Kc κH κ0 κ' * F0 * Real.exp (-κ0 * Lab.dl y0) * Real.exp (-κ' * dExt Y)) := by
  have hcore := marked_cubes_core μ hN hj hΩ A y0 G hGm hGdep hG hκ0 hKc hεpos hF0 hκ' hκG hκ hε
  obtain ⟨h1, h2, h3, h3', h4⟩ := hcore
  have hS0ne : (blocksOf m₀ j Ω (Lab.ysite y0)).Nonempty := Lab.blocksOf_nonempty hN hj hΩ y0
  have hcG : 0 ≤ cG d L := by unfold cG; positivity
  have hXi0 : marksXi μ (presum Lab A.H) (gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G) 0 =
      ∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ) := by
    rw [marksXi_zero_eq μ hN hj hΩ Lab A.H _ hS0ne G 0]
    simp
  have hne : ∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ) ≠ 0 := by
    rw [← hXi0, h1]; exact Complex.exp_ne_zero _
  simp only [Ff_zero_eq_Pst] at h1 h2
  refine ⟨hne, ⟨by rw [← hXi0, h1], fun Y hY => ?_⟩, ?_⟩
  · obtain ⟨b, hb⟩ := hY
    have := h2 b Y hb
    have hexp : Real.exp (κ' * dExt Y) ≤ Real.exp (κ' * (dExt Y + cG d L)) :=
      Real.exp_le_exp.2 (by nlinarith [mul_nonneg hκ' hcG])
    have h5 : ‖Pst μ Lab A.H Y‖ * Real.exp (κ' * dExt Y) ≤ εH * Kc * CPE d L Kc κH κ0 κ' :=
      (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)).trans this
    have := le_of_mul_exp_le h5
    rwa [show -κ' * dExt Y = -(κ' * dExt Y) by ring]
  · have hc1 := one_le_c1 d L
    have hκHnn : 0 ≤ κH := by linarith [aEnt_nonneg d L]
    have hκGnn : 0 ≤ κG := by linarith
    have hGC : ∀ Φ, ‖G Φ‖ ≤ F0 := fun Φ => (hG Φ).trans (by
      have : Real.exp (-κG * Lab.dl y0) ≤ 1 := Real.exp_le_one_iff.2 (by
        nlinarith [Lab.dl_nonneg y0, hκGnn])
      nlinarith)
    have hAb : ∀ Φ, ‖∑ y, A.H y Φ‖ ≤ ∑ y : Lb, εH := fun Φ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => (A.bound y Φ).trans (by
        have : Real.exp (-κH * Lab.dl y) ≤ 1 := Real.exp_le_one_iff.2 (by
          nlinarith [Lab.dl_nonneg y, hκHnn])
        nlinarith))
    have hAm : Measurable (fun Φ => ∑ y, A.H y Φ) := Finset.measurable_sum _ (fun y _ => A.meas y)
    have hD1 := D1_expMark (Measure.pi μ) (fun Φ => ∑ y, A.H y Φ) G hAm hGm hF0.le hAb hGC
    have hfun : marksXi μ (presum Lab A.H) (gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G) =
        fun l : Unit → ℂ => ∫ Φ, Complex.exp (∑ y, A.H y Φ + l () * G Φ) ∂(Measure.pi μ) :=
      funext fun l => marksXi_zero_eq μ hN hj hΩ Lab A.H _ hS0ne G l
    refine ⟨?_, fun Y hY => h3' Y hY, fun Y => ?_⟩
    · unfold Gst
      rw [← hXi0, ← h3, hfun, hD1]
    · by_cases hY : blocksOf m₀ j Ω (Lab.ysite y0) ⊆ Y
      · obtain ⟨b, hb⟩ := hS0ne
        have := h4 hb Y (hY hb)
        have hexp : Real.exp (κ' * dExt Y) ≤ Real.exp (κ' * (dExt Y + cG d L)) :=
          Real.exp_le_exp.2 (by nlinarith [mul_nonneg hκ' hcG])
        have h5 := (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)).trans this
        have := le_of_mul_exp_le h5
        rwa [show -κ' * dExt Y = -(κ' * dExt Y) by ring]
      · show ‖D1 () (Ff _ _ _ _)‖ ≤ _
        rw [h3' Y hY]
        simp only [norm_zero]
        unfold CPE
        have := one_le_c1 d L
        positivity

theorem presum_congr {Ωb : 𝔅 → Type*} (Lab : CubeLabels m₀ j Ω Lb)
    (H H' : Lb → (∀ b, Ωb b) → ℂ) (S : NePoly 𝔅) (T : Finset 𝔅) (hST : S.1 ⊆ T)
    (hH : ∀ y, blocksOf m₀ j Ω (Lab.ysite y) ⊆ T → H y = H' y) :
    presum Lab H S = presum Lab H' S := by
  funext Φ
  unfold presum
  refine Finset.sum_congr rfl (fun y hy => ?_)
  have hyS : blocksOf m₀ j Ω (Lab.ysite y) = S.1 := (Finset.mem_filter.1 hy).2
  rw [hH y (hyS ▸ hST)]

/-- **Locality of `P(S)`**: it depends only on the labels with `Y ∩ Ω ⊆ S` and on the measure
on `S`. -/
theorem Pst_congr {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ μ' : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    [∀ b, IsProbabilityMeasure (μ' b)] {Lab : CubeLabels m₀ j Ω Lb} {εH κH κ0 Kc : ℝ}
    (A : LabelAct Lab Ωb εH κH κ0 Kc) (H' : Lb → (∀ b, Ωb b) → ℂ) (S : Finset 𝔅)
    (hμ : ∀ b ∈ S, μ b = μ' b)
    (hH : ∀ y, blocksOf m₀ j Ω (Lab.ysite y) ⊆ S → A.H y = H' y) :
    Pst μ Lab A.H S = Pst μ' Lab H' S := by
  unfold Pst
  refine PY_congr (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val S
    (fun x hx => ?_)
  exact mayerK_congr μ μ' Subtype.val (fun t => A.presum_dep t) x (fun b hb => hμ b (hx hb))
    (fun t ht => presum_congr Lab A.H H' t S (ht.trans hx) hH)

/-- **Locality of `G*(Y₀, S)`**: it depends only on the labels with `Y ∩ Ω ⊆ S`, on the mark `G`
(when `S ⊇ S₀`) and on the measure on `S`. -/
theorem Gst_congr {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ μ' : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    [∀ b, IsProbabilityMeasure (μ' b)] {Lab : CubeLabels m₀ j Ω Lb} {εH κH κ0 Kc : ℝ}
    (A : LabelAct Lab Ωb εH κH κ0 Kc) (H' : Lb → (∀ b, Ωb b) → ℂ) (S₀ S : Finset 𝔅)
    {G G' : (∀ b, Ωb b) → ℂ} (hGdep : DepOn S₀ G)
    (hμ : ∀ b ∈ S, μ b = μ' b)
    (hH : ∀ y, blocksOf m₀ j Ω (Lab.ysite y) ⊆ S → A.H y = H' y)
    (hG : S₀ ⊆ S → G = G') :
    Gst μ Lab A.H S₀ G S = Gst μ' Lab H' S₀ G' S := by
  unfold Gst
  have hF : Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
      (marksK μ Subtype.val (presum Lab A.H) (gMark S₀ G)) S =
      Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
      (marksK μ' Subtype.val (presum Lab H') (gMark S₀ G')) S := by
    funext l
    unfold Ff
    refine PY_congr (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val S
      (fun x hx => ?_)
    unfold marksK
    refine mayerK_congr μ μ' Subtype.val (fun t Φ Φ' h => ?_) x (fun b hb => hμ b (hx hb))
      (fun t ht => ?_)
    · unfold Hlam
      rw [A.presum_dep t Φ Φ' h]
      congr 1
      exact Finset.sum_congr rfl (fun _ _ => by rw [gMark_dep S₀ hGdep t Φ Φ' h])
    · funext Φ
      unfold Hlam
      have h1 := congrFun (presum_congr Lab A.H H' t S (ht.trans hx) hH) Φ
      have h2 : gMark S₀ G () t Φ = gMark S₀ G' () t Φ := by
        by_cases h : t.1 = S₀
        · have := hG (h ▸ ht.trans hx)
          subst this; rfl
        · simp [gMark, h]
      simp only [Finset.univ_unique, Finset.sum_singleton, h1, h2]
  rw [hF]

omit [NeZero N₁] [NeZero L] in
theorem Yhat_mono {S S' : Set (CTorus d L N₁ m₁ K)} (h : S ⊆ S') : Yhat Ω S ⊆ Yhat Ω S' := by
  rintro y (hy | ⟨z, hz, ⟨s, hs, hsz⟩, hyz⟩)
  · exact Or.inl (h hy)
  · exact Or.inr ⟨z, hz, ⟨s, h hs, hsz⟩, hyz⟩

omit [NeZero N₁] [NeZero L] in
theorem sitesOf_mono {S S' : Finset 𝔅} (h : S ⊆ S') : sitesOf S ⊆ sitesOf S' := by
  intro z hz
  obtain ⟨b, hb, hzb⟩ := mem_sitesOf.1 hz
  exact mem_sitesOf.2 ⟨b, h hb, hzb⟩

omit [Fintype Lb] in
/-- The sites of a label lie in `Ŷ` of every set of blocks containing the blocks of the label
(consequence of (G4)). -/
theorem ysite_subset_Yhat (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    (Lab : CubeLabels m₀ j Ω Lb) (y : Lb) {S : Finset 𝔅}
    (h : blocksOf m₀ j Ω (Lab.ysite y) ⊆ S) : Lab.ysite y ⊆ Yhat Ω (sitesOf S) := by
  refine (G4_subset (Lab.isDj y) (Lab.meets y)).trans (Yhat_mono ?_)
  rw [← sitesOf_blocksOf hN hj hΩ (Lab.isDj y).2.1]
  exact sitesOf_mono h

section External

/-- **Locality of `P(S)` in the non-integrated variables**: if the activity of each label depends on
the external variables `θ` only through their restriction to the label, then `P(S)` depends on `θ`
only through its restriction to `Ŷ(S)`. -/
theorem Pst_ext_congr {E : Type*} {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κ0 Kc : ℝ}
    (A : (CTorus d L N₁ m₁ K → E) → LabelAct Lab Ωb εH κH κ0 Kc)
    (hdep : ∀ y (θ θ' : CTorus d L N₁ m₁ K → E), (∀ z ∈ Lab.ysite y, θ z = θ' z) →
      (A θ).H y = (A θ').H y)
    (S : Finset 𝔅) {θ θ' : CTorus d L N₁ m₁ K → E}
    (hagree : ∀ z ∈ Yhat Ω (sitesOf S), θ z = θ' z) :
    Pst μ Lab (A θ).H S = Pst μ Lab (A θ').H S :=
  Pst_congr μ μ (A θ) (A θ').H S (fun _ _ => rfl) (fun y hy =>
    hdep y θ θ' (fun z hz => hagree z (ysite_subset_Yhat hN hj hΩ Lab y hy hz)))

/-- **Locality of `G*(Y₀, S)` in the non-integrated variables**: `G*(Y₀, S)` depends on `θ` only
through its restriction to `Ŷ(S)`. -/
theorem Gst_ext_congr {E : Type*} {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κ0 Kc : ℝ}
    (A : (CTorus d L N₁ m₁ K → E) → LabelAct Lab Ωb εH κH κ0 Kc)
    (hdep : ∀ y (θ θ' : CTorus d L N₁ m₁ K → E), (∀ z ∈ Lab.ysite y, θ z = θ' z) →
      (A θ).H y = (A θ').H y)
    (y0 : Lb) (G : (CTorus d L N₁ m₁ K → E) → (∀ b, Ωb b) → ℂ)
    (hGdep : ∀ θ, DepOn (blocksOf m₀ j Ω (Lab.ysite y0)) (G θ))
    (hGθ : ∀ (θ θ' : CTorus d L N₁ m₁ K → E), (∀ z ∈ Lab.ysite y0, θ z = θ' z) → G θ = G θ')
    (S : Finset 𝔅) {θ θ' : CTorus d L N₁ m₁ K → E}
    (hagree : ∀ z ∈ Yhat Ω (sitesOf S), θ z = θ' z) :
    Gst μ Lab (A θ).H (blocksOf m₀ j Ω (Lab.ysite y0)) (G θ) S =
      Gst μ Lab (A θ').H (blocksOf m₀ j Ω (Lab.ysite y0)) (G θ') S :=
  Gst_congr μ μ (A θ) (A θ').H _ S (hGdep θ) (fun _ _ => rfl) (fun y hy =>
    hdep y θ θ' (fun z hz => hagree z (ysite_subset_Yhat hN hj hΩ Lab y hy hz)))
    (fun hS => hGθ θ θ' (fun z hz => hagree z
      (ysite_subset_Yhat hN hj hΩ Lab y0 hS hz)))

end External

end Explicit

end Balaban.Fluctuation
