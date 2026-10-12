/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.ParameterAnalytic
import Mathlib.Tactic.Linarith

/-!
# Lemma AE with a set of data and analytic dependence on the data (LOCALIZATION.md §4.1, §4.4)

* `analyticOnNhd_coef_of_analyticOnNhd`: `analyticOnNhd_coef` for an arbitrary set `S` of data:
  only analyticity of `Φ` on `S × {|s i| < R}` is assumed (analytic at every point), no bound and no
  openness of `S`; the local bound comes from compactness of the closed polydisc of radius
  `(1+R)/2` and the tube lemma;
* `abstract_expansion_on`: Lemma AE when the hypotheses (AE1), (AE2) hold only for the data in a
  set `S`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban.Analysis Filter Set

section Param

variable {Λ ι : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ] [Fintype ι] [DecidableEq ι]

/-- **Lemma AE, parameter dependence, for an arbitrary set of data.**  If `Φ` is analytic at every
point of `S × {|s i| < R}`, `R > 1`, then every coefficient `a ↦ F_C(a)` is analytic at every point
of `S`. -/
theorem analyticOnNhd_coef_of_analyticOnNhd {S : Set Λ} {R : ℝ} (hR : 1 < R)
    {Φ : Λ × (ι → ℂ) → ℂ}
    (hΦ : AnalyticOnNhd ℂ Φ (S ×ˢ polydisc (0 : ι → ℂ) (fun _ => R))) (C : Finset ι) :
    AnalyticOnNhd ℂ (fun a : Λ => coef (fun s => Φ (a, s)) C) S := by
  intro a ha
  set R' : ℝ := (1 + R) / 2 with hR'
  have hR'1 : 1 < R' := by rw [hR']; linarith
  have hR'R : R' < R := by rw [hR']; linarith
  set K : Set (ι → ℂ) := Metric.closedBall (0 : ι → ℂ) R' with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hKpoly : K ⊆ polydisc (0 : ι → ℂ) (fun _ => R) := by
    intro s hs i
    have : ‖s‖ ≤ R' := by simpa [hK] using hs
    have := (norm_le_pi_norm s i).trans this
    simp only [sub_zero, Pi.zero_apply]
    linarith
  have hanK : ∀ s ∈ K, AnalyticAt ℂ Φ (a, s) := fun s hs => hΦ (a, s) ⟨ha, hKpoly hs⟩
  set U : Set (Λ × (ι → ℂ)) := {x | AnalyticAt ℂ Φ x} with hU
  have hUo : IsOpen U := isOpen_analyticAt ℂ Φ
  have hcont : ContinuousOn Φ U := fun x hx => (hx : AnalyticAt ℂ Φ x).continuousAt.continuousWithinAt
  have hcontK : ContinuousOn (fun s : ι → ℂ => Φ (a, s)) K := fun s hs =>
    ((hanK s hs).continuousAt.comp (f := fun s' : ι → ℂ => (a, s')) (by fun_prop)).continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := hKc.exists_bound_of_continuousOn hcontK
  set n : Set (Λ × (ι → ℂ)) := U ∩ {x | ‖Φ x‖ < ‖M₀‖ + 1} with hn
  have hno : IsOpen n := by
    have := hcont.norm.isOpen_inter_preimage hUo (isOpen_Iio : IsOpen (Set.Iio (‖M₀‖ + 1)))
    convert this using 1
    ext x; simp [hn, hU]
  have hsub : ({a} : Set Λ) ×ˢ K ⊆ n := by
    rintro ⟨a', s⟩ ⟨ha', hs⟩
    rw [Set.mem_singleton_iff] at ha'
    subst ha'
    refine ⟨hanK s hs, ?_⟩
    have h2 : ‖Φ (a', s)‖ ≤ ‖M₀‖ := (hM₀ s hs).trans (by rw [Real.norm_eq_abs]; exact le_abs_self _)
    show ‖Φ (a', s)‖ < ‖M₀‖ + 1
    linarith
  obtain ⟨u, v, hu, hv, hau, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hKc hno hsub
  have hVsub : u ×ˢ polydisc (0 : ι → ℂ) (fun _ => R') ⊆ n := by
    refine (Set.prod_mono subset_rfl ?_).trans huv
    refine fun s hs => hKv ?_
    show s ∈ Metric.closedBall (0 : ι → ℂ) R'
    rw [mem_closedBall_zero_iff]
    exact (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => by simpa using (hs i).le
  have hΦV : AnalyticOnNhd ℂ Φ (u ×ˢ polydisc (0 : ι → ℂ) (fun _ => R')) := fun x hx =>
    (hVsub hx).1
  have hB : ∀ x ∈ u ×ˢ polydisc (0 : ι → ℂ) (fun _ => R'), ‖Φ x‖ ≤ ‖M₀‖ + 1 := fun x hx =>
    (hVsub hx).2.le
  exact analyticOnNhd_coef hR'1 hu hΦV hB C a (hau rfl)

end Param

section Near

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- Parameters vanishing outside `C`, all coordinates of modulus `< R`. -/
def supN (C : Finset ι) (R : ℝ) : Set (ι → ℂ) := {w | w ∈ supportedOn C ∧ ∀ i, ‖w i‖ < R}

omit [Fintype ι] in
theorem add_single_mem_supN {C : Finset ι} {R : ℝ} {w : ι → ℂ} (hw : w ∈ supN C R) {a : ι}
    (ha : a ∈ C) {τ : ℂ} (hτ : ‖w a + τ‖ < R) : w + τ • (Pi.single a 1 : ι → ℂ) ∈ supN C R := by
  refine ⟨add_single_mem_supportedOn hw.1 ha τ, fun i => ?_⟩
  by_cases hia : i = a
  · subst hia; simpa using hτ
  · simpa [Pi.single_eq_of_ne hia] using hw.2 i

omit [Fintype ι] in
theorem eventually_add_single_mem_supN {C : Finset ι} {R : ℝ} {w : ι → ℂ} (hw : w ∈ supN C R)
    {a : ι} (ha : a ∈ C) : ∀ᶠ t : ℂ in nhds 0, w + t • (Pi.single a 1 : ι → ℂ) ∈ supN C R := by
  have hc : Continuous fun t : ℂ => ‖w a + t‖ := by fun_prop
  have h0 : ‖w a + 0‖ < R := by simpa using hw.2 a
  filter_upwards [hc.continuousAt.eventually_lt continuousAt_const
    (by simpa using h0 : (fun t : ℂ => ‖w a + t‖) 0 < (fun _ : ℂ => R) 0)] with t ht
  exact add_single_mem_supN hw ha ht

omit [Fintype ι] in
theorem pder_congr_near {C : Finset ι} {R : ℝ} {f g : (ι → ℂ) → ℂ}
    (hfg : ∀ w ∈ supN C R, f w = g w) {a : ι} (ha : a ∈ C) {w : ι → ℂ} (hw : w ∈ supN C R) :
    pder a f w = pder a g w := by
  unfold pder
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [eventually_add_single_mem_supN hw ha] with t ht
  exact hfg _ ht

omit [Fintype ι] in
theorem pderList_congr_near {C : Finset ι} {R : ℝ} :
    ∀ (l : List ι), (∀ a ∈ l, a ∈ C) → ∀ {f g : (ι → ℂ) → ℂ},
      (∀ w ∈ supN C R, f w = g w) → ∀ w ∈ supN C R, pderList l f w = pderList l g w := by
  intro l
  induction l with
  | nil => intro _ f g h w hw; exact h w hw
  | cons a l ih =>
    intro hl f g h w hw
    exact ih (fun b hb => hl b (by simp [hb])) (fun w' hw' => pder_congr_near h (hl a (by simp)) hw')
      w hw

omit [Fintype ι] in
theorem iterInt_congr_near {C : Finset ι} {R : ℝ} (hR : 1 < R) {h h' : (ι → ℂ) → ℂ}
    (hh : ∀ w ∈ supN C R, h w = h' w) :
    ∀ (l : List ι), (∀ a ∈ l, a ∈ C) → ∀ {s : ι → ℂ}, s ∈ supportedOn C → (∀ i, ‖s i‖ ≤ 1) →
      iterInt l h s = iterInt l h' s := by
  intro l
  induction l with
  | nil => intro _ s hs hs1; exact hh s ⟨hs, fun i => lt_of_le_of_lt (hs1 i) hR⟩
  | cons a l ih =>
    intro hl s hs hs1
    simp only [iterInt]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    refine ih (fun b hb => hl b (by simp [hb])) (update_mem_supportedOn hs (hl a (by simp)) _)
      (fun i => ?_)
    by_cases hia : i = a
    · subst hia
      simp only [Function.update_self, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    · rw [Function.update_of_ne hia]; exact hs1 i

theorem coef_congr_near {C : Finset ι} {R : ℝ} (hR : 1 < R) {f g : (ι → ℂ) → ℂ}
    (hfg : ∀ w ∈ supN C R, f w = g w) : coef f C = coef g C := by
  have hl : ∀ a ∈ Finset.univ.toList.filter (· ∈ C), a ∈ C := fun a ha => mem_filter_toList.mp ha
  unfold coef
  exact iterInt_congr_near hR (fun w hw => pderList_congr_near _ hl hfg w hw) _ hl
    (fun i _ => rfl) (fun i => by simp)

/-- A function constant along the `i₀`-th direction on `supN C R`. -/
def InvAlongN (C : Finset ι) (R : ℝ) (i₀ : ι) (g : (ι → ℂ) → ℂ) : Prop :=
  ∀ w ∈ supN C R, ∀ τ : ℂ, ‖w i₀ + τ‖ < R → g (w + τ • (Pi.single i₀ 1 : ι → ℂ)) = g w

omit [Fintype ι] in
theorem invAlongN_pder {C : Finset ι} {R : ℝ} {i₀ : ι} {g : (ι → ℂ) → ℂ}
    (hg : InvAlongN C R i₀ g) {a : ι} (ha : a ∈ C) : InvAlongN C R i₀ (pder a g) := by
  intro w hw τ hτ
  unfold pder
  refine Filter.EventuallyEq.deriv_eq ?_
  have hc : Continuous fun t : ℂ => ‖(w + t • (Pi.single a 1 : ι → ℂ)) i₀ + τ‖ := by fun_prop
  have h0 : ‖(w + (0 : ℂ) • (Pi.single a 1 : ι → ℂ)) i₀ + τ‖ < R := by simpa using hτ
  filter_upwards [eventually_add_single_mem_supN hw ha,
    hc.continuousAt.eventually_lt continuousAt_const
      (by simpa using h0 : (fun t : ℂ => ‖(w + t • (Pi.single a 1 : ι → ℂ)) i₀ + τ‖) 0 <
        (fun _ : ℂ => R) 0)] with t ht1 ht2
  have e : w + τ • (Pi.single i₀ 1 : ι → ℂ) + t • (Pi.single a 1 : ι → ℂ) =
      (w + t • (Pi.single a 1 : ι → ℂ)) + τ • (Pi.single i₀ 1 : ι → ℂ) := by abel
  rw [e]
  exact hg _ ht1 τ ht2

omit [Fintype ι] in
theorem invAlongN_pder_self_eq_zero {C : Finset ι} {R : ℝ} {i₀ : ι} {g : (ι → ℂ) → ℂ}
    (hg : InvAlongN C R i₀ g) : ∀ w ∈ supN C R, pder i₀ g w = 0 := by
  intro w hw
  unfold pder
  have hc : Continuous fun t : ℂ => ‖w i₀ + t‖ := by fun_prop
  have h0 : ‖w i₀ + 0‖ < R := by simpa using hw.2 i₀
  have : (fun t : ℂ => g (w + t • (Pi.single i₀ 1 : ι → ℂ))) =ᶠ[nhds 0] fun _ => g w := by
    filter_upwards [hc.continuousAt.eventually_lt continuousAt_const
      (by simpa using h0 : (fun t : ℂ => ‖w i₀ + t‖) 0 < (fun _ : ℂ => R) 0)] with t ht
    exact hg w hw t ht
  rw [this.deriv_eq]; simp

omit [Fintype ι] in
theorem pderList_eq_zero_of_invN {C : Finset ι} {R : ℝ} {i₀ : ι} :
    ∀ (l : List ι), (∀ a ∈ l, a ∈ C) → i₀ ∈ l → ∀ {g : (ι → ℂ) → ℂ}, InvAlongN C R i₀ g →
      ∀ w ∈ supN C R, pderList l g w = 0 := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons a l ih =>
    intro hl hi g hg w hw
    have hl' : ∀ b ∈ l, b ∈ C := fun b hb => hl b (by simp [hb])
    by_cases hai : a = i₀
    · subst hai
      have := pderList_congr_near (C := C) (R := R) l hl' (f := pder a g) (g := fun _ => 0)
        (fun w hw => invAlongN_pder_self_eq_zero hg w hw) w hw
      simpa [pderList_zero] using this
    · have hi' : i₀ ∈ l := by simpa [Ne.symm hai] using hi
      exact ih hl' hi' (invAlongN_pder hg (hl a (by simp))) w hw

theorem coef_eq_zero_of_invN {C : Finset ι} {R : ℝ} (hR : 1 < R) {i₀ : ι} (hi : i₀ ∈ C)
    {f : (ι → ℂ) → ℂ} (hf : InvAlongN C R i₀ f) : coef f C = 0 := by
  have hl : ∀ a ∈ Finset.univ.toList.filter (· ∈ C), a ∈ C := fun a ha => mem_filter_toList.mp ha
  unfold coef
  have := iterInt_congr_near (C := C) (R := R) hR
    (h := pderList (Finset.univ.toList.filter (· ∈ C)) f) (h' := fun _ => 0)
    (fun w hw => pderList_eq_zero_of_invN _ hl (mem_filter_toList.mpr hi) hf w hw) _ hl
    (s := 0) (fun i _ => rfl) (fun i => by simp)
  rw [this]
  exact iterInt_zero _ _

end Near

section AEOn

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {Ω U : Type*}

/-- (AE2) for the data in a set `S`, for the parameters in the polydisc of radius `R`, with the
connectivity region `Yc C` for the parameters and an abstract agreement relation `Ag C` of two
data (in the application: agreement on a thickening of `Yc C`). -/
def LocalityAEOn (R : ℝ) (S : Set U) (P : ι → Set Ω) (Yc : Finset ι → Set Ω)
    (Ag : Finset ι → U → U → Prop) (F : U → (ι → ℂ) → ℂ) : Prop :=
  ∀ (C : Finset ι) (u u' : U), u ∈ S → u' ∈ S → ∀ (s s' : ι → ℂ), s ∈ supN C R →
    s' ∈ supN C R → (∀ i ∈ C, P i ⊆ Yc C → s i = s' i) → Ag C u u' → F u s = F u' s'

theorem coef_eq_zero_of_not_connected_on {R : ℝ} (hR : 1 < R) {S : Set U} {P : ι → Set Ω}
    {Yc : Finset ι → Set Ω} {Ag : Finset ι → U → U → Prop} {F : U → (ι → ℂ) → ℂ}
    (hloc : LocalityAEOn R S P Yc Ag F) (hrefl : ∀ C u, u ∈ S → Ag C u u)
    {u : U} (hu : u ∈ S) {C : Finset ι} (hC : ¬ IsConnectedFamily P Yc C) :
    coef (F u) C = 0 := by
  simp only [IsConnectedFamily, not_forall] at hC
  obtain ⟨i₀, hi₀, hP⟩ := hC
  refine coef_eq_zero_of_invN hR hi₀ fun w hw τ hτ => ?_
  refine hloc C u u hu hu _ _ (add_single_mem_supN hw hi₀ hτ) hw (fun i hi hPi => ?_)
    (hrefl C u hu)
  have : i ≠ i₀ := fun h => hP (h ▸ hPi)
  simp [Pi.single_eq_of_ne this]

theorem coef_congr_of_agree_on {R : ℝ} (hR : 1 < R) {S : Set U} {P : ι → Set Ω}
    {Yc : Finset ι → Set Ω} {Ag : Finset ι → U → U → Prop} {F : U → (ι → ℂ) → ℂ}
    (hloc : LocalityAEOn R S P Yc Ag F)
    (C : Finset ι) {u u' : U} (hu : u ∈ S) (hu' : u' ∈ S)
    (huu : Ag C u u') : coef (F u) C = coef (F u') C :=
  coef_congr_near hR fun w hw => hloc C u u' hu hu' w w hw hw (fun _ _ _ => rfl) huu

open scoped Classical in
/-- **Lemma AE for the data of a set `S`** (the hypotheses (AE1), (AE2) are only assumed for
`u ∈ S` and the parameters in the polydisc). -/
theorem abstract_expansion_on {S : Set U} {P : ι → Set Ω} {Yc : Finset ι → Set Ω}
    {Ag : Finset ι → U → U → Prop} {F : U → (ι → ℂ) → ℂ} {κ₁ B : ℝ} (hκ : 1 ≤ κ₁)
    (hana : ∀ u ∈ S, AnalyticOnNhd ℂ (F u) (polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁)))
    (hbd : ∀ u ∈ S, ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁), ‖F u s‖ ≤ B)
    (hloc : LocalityAEOn (Real.exp κ₁) S P Yc Ag F) (hrefl : ∀ C u, u ∈ S → Ag C u u) :
    (∀ u ∈ S, F u 1 = ∑ C ∈ Finset.univ.filter (fun C => IsConnectedFamily P Yc C), coef (F u) C) ∧
    (∀ u ∈ S, ∀ C, ¬ IsConnectedFamily P Yc C → coef (F u) C = 0) ∧
    (∀ C u u', u ∈ S → u' ∈ S → Ag C u u' → coef (F u) C = coef (F u') C) ∧
    (∀ u ∈ S, ∀ C, ‖coef (F u) C‖ ≤ B * Real.exp (-(κ₁ - 1) * C.card)) := by
  classical
  have hR : 1 < Real.exp κ₁ := Real.one_lt_exp_iff.mpr (by linarith)
  refine ⟨fun u hu => ?_, fun u hu C hC => coef_eq_zero_of_not_connected_on hR hloc hrefl hu hC,
    fun C u u' hu hu' huu => coef_congr_of_agree_on hR hloc C hu hu' huu,
    fun u hu C => norm_coef_le_exp hκ (hana u hu) (hbd u hu) C⟩
  rw [sum_coef_eq hR (hana u hu), Finset.sum_filter]
  refine Finset.sum_congr rfl fun C _ => ?_
  split_ifs with h
  · rfl
  · exact coef_eq_zero_of_not_connected_on hR hloc hrefl hu h

end AEOn

end Balaban.Localization
