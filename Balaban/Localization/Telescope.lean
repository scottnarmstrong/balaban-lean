/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.PartialDeriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Iterated interval integrals and the telescoping identity

`iterInt l h s` is the iterated integral `∫_0^1 ⋯ ∫_0^1 h (s[l := t]) dt` over the coordinates of
the list `l` (the head is the outermost integral).  The telescoping identity
(`telescope`) expands `F 1` as the sum over subsets `C` of the coordinates of
`iterInt lC (∂_{lC} F) (1_C)`, where `lC` lists `C` in the order of the list `l`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban.Analysis MeasureTheory intervalIntegral

variable {ι : Type*} [DecidableEq ι]

/-- Iterated integral over `[0,1]` in the coordinates of the list (head outermost). -/
noncomputable def iterInt : List ι → ((ι → ℂ) → ℂ) → (ι → ℂ) → ℂ
  | [], h, s => h s
  | j :: l, h, s => ∫ t in (0 : ℝ)..1, iterInt l h (Function.update s j (t : ℂ))

/-- Set the coordinates in `A` to `0`. -/
def zeroOn (A : Finset ι) (s : ι → ℂ) : ι → ℂ := fun j => if j ∈ A then 0 else s j

/-- The closed unit polydisc. -/
def unitCube (ι : Type*) : Set (ι → ℂ) := {w | ∀ j, ‖w j‖ ≤ 1}

/-- Points whose coordinates outside `l` lie in the unit disc. -/
def cubeOff (l : List ι) : Set (ι → ℂ) := {s | ∀ j, j ∉ l → ‖s j‖ ≤ 1}

theorem update_mem_cubeOff {l : List ι} {i : ι} {z : ι → ℂ} (hz : z ∈ cubeOff (i :: l))
    {t : ℝ} (ht : t ∈ Set.uIcc (0 : ℝ) 1) : Function.update z i (t : ℂ) ∈ cubeOff l := by
  intro j hj
  by_cases hji : j = i
  · subst hji
    simp only [Function.update_self, Complex.norm_real, Real.norm_eq_abs]
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  · rw [Function.update_of_ne hji]
    exact hz j (by simp [hji, hj])

theorem iterInt_congr {h h' : (ι → ℂ) → ℂ} (hh : ∀ w ∈ unitCube ι, h w = h' w) :
    ∀ (l : List ι) {s : ι → ℂ}, s ∈ cubeOff l → iterInt l h s = iterInt l h' s := by
  intro l
  induction l with
  | nil =>
    intro s hs
    exact hh s (fun j => hs j (by simp))
  | cons i l ih =>
    intro s hs
    simp only [iterInt]
    refine intervalIntegral.integral_congr fun t ht => ?_
    exact ih (update_mem_cubeOff hs ht)

theorem norm_iterInt_le {h : (ι → ℂ) → ℂ} {b : ℝ} (hh : ∀ w ∈ unitCube ι, ‖h w‖ ≤ b) :
    ∀ (l : List ι) {s : ι → ℂ}, s ∈ cubeOff l → ‖iterInt l h s‖ ≤ b := by
  intro l
  induction l with
  | nil =>
    intro s hs
    exact hh s (fun j => hs j (by simp))
  | cons i l ih =>
    intro s hs
    simp only [iterInt]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := b)
      (f := fun t : ℝ => iterInt l h (Function.update s i (t : ℂ)))
      (fun t ht => ih (update_mem_cubeOff hs (Set.uIoc_subset_uIcc ht)))
    simpa using this

theorem continuous_iterInt {h : (ι → ℂ) → ℂ} (hh : Continuous h) :
    ∀ l : List ι, Continuous (iterInt l h) := by
  intro l
  induction l with
  | nil => exact hh
  | cons i l ih =>
    simp only [iterInt]
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 1
    refine ih.comp ?_
    exact (continuous_fst.update i (Complex.continuous_ofReal.comp continuous_snd))

/-- Retraction of `ℂ` onto the closed unit disc. -/
noncomputable def clamp1 (z : ℂ) : ℂ := z / ((max 1 ‖z‖ : ℝ) : ℂ)

theorem continuous_clamp1 : Continuous clamp1 := by
  unfold clamp1
  refine continuous_id.div (Complex.continuous_ofReal.comp (continuous_const.max continuous_norm))
    fun z => ?_
  have : (0 : ℝ) < max 1 ‖z‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
  exact_mod_cast this.ne'

theorem clamp1_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) : clamp1 z = z := by
  simp [clamp1, max_eq_left hz]

theorem norm_clamp1_le (z : ℂ) : ‖clamp1 z‖ ≤ 1 := by
  unfold clamp1
  have h0 : (0 : ℝ) < max 1 ‖z‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0, div_le_one h0]
  exact le_max_right _ _

/-- Coordinatewise retraction onto the unit cube. -/
noncomputable def clampCube (s : ι → ℂ) : ι → ℂ := fun j => clamp1 (s j)

omit [DecidableEq ι] in
theorem continuous_clampCube : Continuous (clampCube (ι := ι)) :=
  continuous_pi fun j => continuous_clamp1.comp (continuous_apply j)

omit [DecidableEq ι] in
theorem clampCube_mem (s : ι → ℂ) : clampCube s ∈ unitCube ι := fun _ => norm_clamp1_le _

omit [DecidableEq ι] in
theorem clampCube_of_mem {s : ι → ℂ} (hs : s ∈ unitCube ι) : clampCube s = s :=
  funext fun j => clamp1_of_norm_le (hs j)

section Fin

variable [Fintype ι]

omit [DecidableEq ι] [Fintype ι] in
theorem unitCube_subset_polydisc {R : ℝ} (hR : 1 < R) :
    unitCube ι ⊆ polydisc (0 : ι → ℂ) (fun _ => R) := fun w hw j => by
  simpa using lt_of_le_of_lt (hw j) hR

omit [DecidableEq ι] [Fintype ι] in
theorem continuous_comp_clampCube {R : ℝ} (hR : 1 < R) {h : (ι → ℂ) → ℂ}
    (hh : ContinuousOn h (polydisc (0 : ι → ℂ) (fun _ => R))) :
    Continuous (h ∘ clampCube) :=
  hh.comp_continuous continuous_clampCube fun s => unitCube_subset_polydisc hR (clampCube_mem s)

omit [Fintype ι] in
theorem iterInt_eq_clamp {h : (ι → ℂ) → ℂ}
    (l : List ι) {s : ι → ℂ} (hs : s ∈ cubeOff l) :
    iterInt l h s = iterInt l (h ∘ clampCube) s :=
  iterInt_congr (fun w hw => by simp [Function.comp, clampCube_of_mem hw]) l hs

omit [Fintype ι] in
theorem intervalIntegrable_iterInt {R : ℝ} (hR : 1 < R) {h : (ι → ℂ) → ℂ}
    (hh : ContinuousOn h (polydisc (0 : ι → ℂ) (fun _ => R))) (l : List ι) (i : ι)
    {z : ι → ℂ} (hz : z ∈ cubeOff (i :: l)) :
    IntervalIntegrable (fun t : ℝ => iterInt l h (Function.update z i (t : ℂ))) volume 0 1 := by
  have hc : Continuous (fun t : ℝ => iterInt l (h ∘ clampCube) (Function.update z i (t : ℂ))) :=
    (continuous_iterInt (continuous_comp_clampCube hR hh) l).comp
      (continuous_const.update i Complex.continuous_ofReal)
  refine (hc.intervalIntegrable 0 1).congr ?_
  intro t ht
  exact (iterInt_eq_clamp l (update_mem_cubeOff hz (Set.uIoc_subset_uIcc ht))).symm

/-- The one-variable fundamental theorem of calculus in the coordinate `i`. -/
theorem sub_eq_integral_pder {R : ℝ} (hR : 1 < R) {F : (ι → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polydisc (0 : ι → ℂ) (fun _ => R))) {s : ι → ℂ}
    (hs : s ∈ polydisc (0 : ι → ℂ) (fun _ => R)) (i : ι) (hi : s i = 1) :
    F s = F (Function.update s i 0) + ∫ t in (0 : ℝ)..1, pder i F (Function.update s i (t : ℂ)) := by
  set P := polydisc (0 : ι → ℂ) (fun _ => R) with hP
  have hpath : ∀ t : ℝ, t ∈ Set.uIcc (0 : ℝ) 1 → Function.update s i (t : ℂ) ∈ P := by
    intro t ht j
    by_cases hji : j = i
    · subst hji
      rw [Set.uIcc_of_le zero_le_one] at ht
      simp only [Function.update_self, Complex.norm_real, Real.norm_eq_abs, Pi.zero_apply,
        sub_zero]
      exact lt_of_le_of_lt (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩) hR
    · rw [Function.update_of_ne hji]; exact hs j
  have hline : ∀ τ : ℂ, Function.update s i τ = Function.update s i 0 + τ • (Pi.single i 1 : ι → ℂ) := by
    intro τ; ext j
    by_cases hji : j = i
    · subst hji
      simp only [Function.update_self, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
        smul_eq_mul, mul_one, zero_add]
    · simp only [Function.update_of_ne hji, Pi.add_apply, Pi.smul_apply,
        Pi.single_eq_of_ne hji, smul_zero, add_zero]
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => F (Function.update s i (x : ℂ)))
        (pder i F (Function.update s i (t : ℂ))) t := by
    intro t ht
    have hp := hpath t ht
    have h1 : HasDerivAt (fun τ : ℂ => Function.update s i 0 + τ • (Pi.single i 1 : ι → ℂ))
        (Pi.single i 1) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).smul_const (Pi.single i 1 : ι → ℂ)).const_add
        (Function.update s i 0)
    have h2 : HasFDerivAt F (fderiv ℂ F (Function.update s i (t : ℂ)))
        (Function.update s i 0 + (t : ℂ) • (Pi.single i 1 : ι → ℂ)) := by
      rw [← hline]; exact (hF _ hp).differentiableAt.hasFDerivAt
    have h3 := (h2.comp_hasDerivAt (t : ℂ) h1).comp_ofReal
    rw [pder_eq_fderiv i (hF _ hp).differentiableAt]
    have hfun : (fun x : ℝ => F (Function.update s i (x : ℂ))) =
        fun x : ℝ => F (Function.update s i 0 + (x : ℂ) • (Pi.single i 1 : ι → ℂ)) := by
      funext x; rw [hline (x : ℂ)]
    have hpt : Function.update s i 0 + (t : ℂ) • (Pi.single i 1 : ι → ℂ) =
        Function.update s i (t : ℂ) := (hline (t : ℂ)).symm
    rw [hfun]
    exact h3
  have hcont : ContinuousOn (fun t : ℝ => pder i F (Function.update s i (t : ℂ)))
      (Set.uIcc 0 1) := by
    refine ((analyticOnNhd_pder hF i).continuousOn).comp ?_ hpath
    exact (continuous_const.update i Complex.continuous_ofReal).continuousOn
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)
  have hs1 : Function.update s i ((1 : ℝ) : ℂ) = s := by
    have h1' : ((1 : ℝ) : ℂ) = s i := by rw [hi]; simp
    rw [h1']; exact Function.update_eq_self i s
  simp only [Complex.ofReal_zero] at this
  rw [hs1] at this
  rw [this]; ring

omit [Fintype ι] in
theorem zeroOn_update {A : Finset ι} {i : ι} (hi : i ∉ A) (s : ι → ℂ) (τ : ℂ) :
    zeroOn A (Function.update s i τ) = Function.update (zeroOn A s) i τ := by
  ext j
  by_cases hji : j = i
  · subst hji; simp [zeroOn, hi]
  · simp [zeroOn, Function.update_of_ne hji]

theorem telescope {R : ℝ} (hR : 1 < R) :
    ∀ (l : List ι), l.Nodup → ∀ {F : (ι → ℂ) → ℂ},
      AnalyticOnNhd ℂ F (polydisc (0 : ι → ℂ) (fun _ => R)) → ∀ {s : ι → ℂ},
      s ∈ unitCube ι → (∀ j ∈ l, s j = 1) →
      F s = ∑ C ∈ l.toFinset.powerset,
        iterInt (l.filter (· ∈ C)) (pderList (l.filter (· ∈ C)) F) (zeroOn (l.toFinset \ C) s) := by
  intro l
  induction l with
  | nil =>
    intro _ F _ s _ _
    have : zeroOn (∅ : Finset ι) s = s := by ext j; simp [zeroOn]
    simp [iterInt, this]
  | cons i l ih =>
    intro hnd F hF s hs h1
    have hil : i ∉ l := (List.nodup_cons.mp hnd).1
    have hl : l.Nodup := (List.nodup_cons.mp hnd).2
    have hne : ∀ j ∈ l, j ≠ i := fun j hj h => hil (h ▸ hj)
    set S := l.toFinset with hS
    have hiS : i ∉ S := by simpa [hS] using hil
    have hsP : s ∈ polydisc (0 : ι → ℂ) (fun _ => R) := unitCube_subset_polydisc hR hs
    have hsi : s i = 1 := h1 i (by simp)
    rw [sub_eq_integral_pder hR hF hsP i hsi]
    -- first term
    have hs0 : Function.update s i 0 ∈ unitCube ι := by
      intro j; by_cases hji : j = i
      · subst hji; simp
      · rw [Function.update_of_ne hji]; exact hs j
    have h0 := ih hl hF hs0 (fun j hj => by
      rw [Function.update_of_ne (hne j hj)]; exact h1 j (by simp [hj]))
    -- second term
    have hG : AnalyticOnNhd ℂ (pder i F) (polydisc (0 : ι → ℂ) (fun _ => R)) :=
      analyticOnNhd_pder hF i
    have hst : ∀ t ∈ Set.uIcc (0 : ℝ) 1, Function.update s i (t : ℂ) ∈ unitCube ι := by
      intro t ht j
      by_cases hji : j = i
      · subst hji
        rw [Set.uIcc_of_le zero_le_one] at ht
        simp only [Function.update_self, Complex.norm_real, Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      · rw [Function.update_of_ne hji]; exact hs j
    have h2 : ∀ t ∈ Set.uIcc (0 : ℝ) 1, pder i F (Function.update s i (t : ℂ)) =
        ∑ C ∈ S.powerset, iterInt (l.filter (· ∈ C)) (pderList (l.filter (· ∈ C)) (pder i F))
          (Function.update (zeroOn (S \ C) s) i (t : ℂ)) := by
      intro t ht
      rw [ih hl hG (hst t ht) (fun j hj => by
        rw [Function.update_of_ne (hne j hj)]; exact h1 j (by simp [hj]))]
      refine Finset.sum_congr rfl fun C hC => ?_
      rw [zeroOn_update (fun h => hiS (Finset.mem_sdiff.mp h).1)]
    rw [intervalIntegral.integral_congr h2, intervalIntegral.integral_finsetSum]
    · have hins : (i :: l).toFinset = insert i S := by simp [hS]
      rw [h0, hins, Finset.sum_powerset_insert hiS]
      congr 1
      · refine Finset.sum_congr rfl fun C hC => ?_
        have hiC : i ∉ C := fun h => hiS (Finset.mem_powerset.mp hC h)
        have hf : (i :: l).filter (· ∈ C) = l.filter (· ∈ C) := by
          simp [hiC]
        have hz : zeroOn (insert i S \ C) s = zeroOn (S \ C) (Function.update s i 0) := by
          ext j
          by_cases hji : j = i
          · subst hji; simp [zeroOn, hiS, hiC]
          · simp [zeroOn, hji]
        rw [hf, hz]
      · refine Finset.sum_congr rfl fun C hC => ?_
        have hf : (i :: l).filter (· ∈ insert i C) = i :: l.filter (· ∈ C) := by
          rw [List.filter_cons_of_pos (by simp)]
          congr 1
          refine List.filter_congr fun x hx => ?_
          have : x ≠ i := hne x hx
          simp [this]
        have hz : zeroOn (insert i S \ insert i C) s = zeroOn (S \ C) s := by
          ext j
          by_cases hji : j = i
          · subst hji; simp [zeroOn, hiS]
          · simp [zeroOn, hji]
        rw [hf, hz]
        rfl
    · intro C hC
      refine intervalIntegrable_iterInt hR ?_ _ i ?_
      · exact (analyticOnNhd_pderList _ hG).continuousOn
      · intro j _; simp only [zeroOn]; split_ifs
        · simp
        · exact hs j

end Fin

end Balaban.Localization
