/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Telescope
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Lemma AE: abstract interpolation–resummation

`notes/phase1/LOCALIZATION.md` §4.1 (P3 (4.41), (4.43), (4.47)).

Data: a finite index type `ι` of "patches" with `P : ι → Set Ω` (subsets of the site set `Ω`),
a set-valued map `Y` on families `C : Finset ι` (in the application `Y C` is the connected
component of `X₁ ∪ ⋃_{i ∈ C} P i` containing `X₁`, `componentOf`; the proof of Lemma AE uses no
property of `Y` beyond the locality hypothesis), and a function `F u s`, `u : Ω → E`, `s : ι → ℂ`.

* (AE1) `F u` is analytic on the open polydisc `|s i| < R` and bounded there by `B`.
* (AE2) `F u s = F u' s'` when `s, s'` vanish outside `C`, agree on `{i ∈ C | P i ⊆ Y C}` and
  `u = u'` on `Y C`.

Conclusions (`abstract_expansion`): with `coef (F u) C` the iterated integral over `[0,1]^C` of the
mixed derivative `∏_{i ∈ C} ∂_{s_i} F` at `s_i = 0` off `C`,
* `F u 1 = ∑_{C connected} coef (F u) C`;
* `coef (F u) C` depends on `u` only through `u|_{Y C}` (for connected `C`) and vanishes for
  non-connected `C`;
* `‖coef (F u) C‖ ≤ B (R-1)^{-|C|}`, and `≤ B e^{-(κ₁-1)|C|}` for `R = e^{κ₁}`, `κ₁ ≥ 1`.

The iterated integral is taken in the order of `Finset.univ.toList` (Fubini makes the order
immaterial).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban.Analysis

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The mixed-derivative coefficient `F_C`: the iterated integral over `[0,1]^C` of
`∏_{i ∈ C} ∂_{s_i} F` evaluated at `s_i = 0` for `i ∉ C`. -/
noncomputable def coef (f : (ι → ℂ) → ℂ) (C : Finset ι) : ℂ :=
  iterInt (Finset.univ.toList.filter (· ∈ C)) (pderList (Finset.univ.toList.filter (· ∈ C)) f) 0

theorem mem_filter_toList {C : Finset ι} {a : ι} :
    a ∈ (Finset.univ.toList.filter (· ∈ C)) ↔ a ∈ C := by simp

theorem nodup_filter_toList (C : Finset ι) : (Finset.univ.toList.filter (· ∈ C)).Nodup :=
  (Finset.nodup_toList _).filter _

theorem toFinset_filter_toList (C : Finset ι) :
    (Finset.univ.toList.filter (· ∈ C)).toFinset = C := by
  ext a; simp

omit [Fintype ι] in
theorem iterInt_congr_off {h : (ι → ℂ) → ℂ} :
    ∀ (l : List ι) {s s' : ι → ℂ}, (∀ j, j ∉ l → s j = s' j) → iterInt l h s = iterInt l h s' := by
  intro l
  induction l with
  | nil => intro s s' hs; exact congrArg h (funext fun j => hs j (by simp))
  | cons i l ih =>
    intro s s' hs
    simp only [iterInt]
    refine intervalIntegral.integral_congr fun t _ => ih fun j hj => ?_
    by_cases hji : j = i
    · subst hji; simp
    · rw [Function.update_of_ne hji, Function.update_of_ne hji]
      exact hs j (by simp [hji, hj])

/-- The expansion `F 1 = ∑_C F_C` (no locality needed). -/
theorem sum_coef_eq {R : ℝ} (hR : 1 < R) {f : (ι → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f (polydisc (0 : ι → ℂ) (fun _ => R))) :
    f 1 = ∑ C : Finset ι, coef f C := by
  have h := telescope hR Finset.univ.toList (Finset.nodup_toList _) hf
    (s := 1) (fun j => by simp) (fun j _ => rfl)
  rw [Finset.toList_toFinset, Finset.powerset_univ] at h
  rw [h]
  refine Finset.sum_congr rfl fun C _ => ?_
  unfold coef
  refine iterInt_congr_off _ fun j hj => ?_
  have hjC : j ∉ C := fun h => hj (mem_filter_toList.mpr h)
  simp [zeroOn, hjC]

/-! ### Support on a family and locality -/

/-- Parameters vanishing outside `C`. -/
def supportedOn (C : Finset ι) : Set (ι → ℂ) := {w | ∀ i, i ∉ C → w i = 0}

omit [Fintype ι] in
theorem update_mem_supportedOn {C : Finset ι} {w : ι → ℂ} (hw : w ∈ supportedOn C) {a : ι}
    (ha : a ∈ C) (τ : ℂ) : Function.update w a τ ∈ supportedOn C := by
  intro i hi
  have : i ≠ a := fun h => hi (h ▸ ha)
  rw [Function.update_of_ne this]; exact hw i hi

omit [Fintype ι] in
theorem add_single_mem_supportedOn {C : Finset ι} {w : ι → ℂ} (hw : w ∈ supportedOn C) {a : ι}
    (ha : a ∈ C) (τ : ℂ) : w + τ • (Pi.single a 1 : ι → ℂ) ∈ supportedOn C := by
  intro i hi
  have : i ≠ a := fun h => hi (h ▸ ha)
  simp [hw i hi, Pi.single_eq_of_ne this]

omit [Fintype ι] in
theorem pder_congr {C : Finset ι} {f g : (ι → ℂ) → ℂ} (hfg : ∀ w ∈ supportedOn C, f w = g w)
    {a : ι} (ha : a ∈ C) : ∀ w ∈ supportedOn C, pder a f w = pder a g w := by
  intro w hw
  unfold pder
  congr 1
  funext t
  exact hfg _ (add_single_mem_supportedOn hw ha t)

omit [Fintype ι] in
theorem pderList_congr {C : Finset ι} :
    ∀ (l : List ι), (∀ a ∈ l, a ∈ C) → ∀ {f g : (ι → ℂ) → ℂ},
      (∀ w ∈ supportedOn C, f w = g w) →
      ∀ w ∈ supportedOn C, pderList l f w = pderList l g w := by
  intro l
  induction l with
  | nil => intro _ f g h; exact h
  | cons a l ih =>
    intro hl f g h
    exact ih (fun b hb => hl b (by simp [hb])) (pder_congr h (hl a (by simp)))

omit [Fintype ι] in
theorem iterInt_congr_supportedOn {C : Finset ι} {h h' : (ι → ℂ) → ℂ}
    (hh : ∀ w ∈ supportedOn C, h w = h' w) :
    ∀ (l : List ι), (∀ a ∈ l, a ∈ C) → ∀ {s : ι → ℂ}, s ∈ supportedOn C →
      iterInt l h s = iterInt l h' s := by
  intro l
  induction l with
  | nil => intro _ s hs; exact hh s hs
  | cons a l ih =>
    intro hl s hs
    simp only [iterInt]
    exact intervalIntegral.integral_congr fun t _ =>
      ih (fun b hb => hl b (by simp [hb])) (update_mem_supportedOn hs (hl a (by simp)) _)

theorem coef_congr {C : Finset ι} {f g : (ι → ℂ) → ℂ} (hfg : ∀ w ∈ supportedOn C, f w = g w) :
    coef f C = coef g C := by
  have h0 : (0 : ι → ℂ) ∈ supportedOn C := fun i _ => rfl
  unfold coef
  have hl : ∀ a ∈ Finset.univ.toList.filter (· ∈ C), a ∈ C := fun a ha => mem_filter_toList.mp ha
  exact iterInt_congr_supportedOn (fun w hw => pderList_congr _ hl hfg w hw) _ hl h0

/-- A function constant along the `i₀`-th direction on the support. -/
def InvAlong (C : Finset ι) (i₀ : ι) (g : (ι → ℂ) → ℂ) : Prop :=
  ∀ w ∈ supportedOn C, ∀ τ : ℂ, g (w + τ • (Pi.single i₀ 1 : ι → ℂ)) = g w

omit [Fintype ι] in
theorem invAlong_pder {C : Finset ι} {i₀ : ι} {g : (ι → ℂ) → ℂ} (hg : InvAlong C i₀ g) {a : ι}
    (ha : a ∈ C) : InvAlong C i₀ (pder a g) := by
  intro w hw τ
  unfold pder
  congr 1
  funext t
  have : w + τ • (Pi.single i₀ 1 : ι → ℂ) + t • (Pi.single a 1 : ι → ℂ) =
      (w + t • (Pi.single a 1 : ι → ℂ)) + τ • (Pi.single i₀ 1 : ι → ℂ) := by abel
  rw [this]
  exact hg _ (add_single_mem_supportedOn hw ha t) τ

omit [Fintype ι] in
theorem invAlong_pder_self_eq_zero {C : Finset ι} {i₀ : ι} {g : (ι → ℂ) → ℂ}
    (hg : InvAlong C i₀ g) : ∀ w ∈ supportedOn C, pder i₀ g w = 0 := by
  intro w hw
  unfold pder
  have : (fun t : ℂ => g (w + t • (Pi.single i₀ 1 : ι → ℂ))) = fun _ => g w :=
    funext fun t => hg w hw t
  rw [this]; simp

omit [Fintype ι] in
theorem pder_zero (a : ι) : pder a (fun _ : ι → ℂ => (0 : ℂ)) = fun _ => 0 := by
  funext w; simp [pder]

omit [Fintype ι] in
theorem pderList_zero : ∀ (l : List ι), pderList l (fun _ : ι → ℂ => (0 : ℂ)) = fun _ => 0 := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => simp [pder_zero, ih]

omit [Fintype ι] in
theorem pderList_eq_zero_of_inv {C : Finset ι} {i₀ : ι} :
    ∀ (l : List ι), (∀ a ∈ l, a ∈ C) → i₀ ∈ l → ∀ {g : (ι → ℂ) → ℂ}, InvAlong C i₀ g →
      ∀ w ∈ supportedOn C, pderList l g w = 0 := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons a l ih =>
    intro hl hi g hg w hw
    have hl' : ∀ b ∈ l, b ∈ C := fun b hb => hl b (by simp [hb])
    by_cases hai : a = i₀
    · subst hai
      have := pderList_congr (C := C) l hl' (f := pder a g) (g := fun _ => 0)
        (fun w hw => invAlong_pder_self_eq_zero hg w hw) w hw
      simpa [pderList_zero] using this
    · have hi' : i₀ ∈ l := by simpa [Ne.symm hai] using hi
      exact ih hl' hi' (invAlong_pder hg (hl a (by simp))) w hw

omit [Fintype ι] in
theorem iterInt_zero : ∀ (l : List ι) (s : ι → ℂ), iterInt l (fun _ => (0 : ℂ)) s = 0 := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons a l ih => intro s; simp [iterInt, ih]

/-- The coefficient of a family containing an index `i₀` along which `f` is constant on the
support vanishes. -/
theorem coef_eq_zero_of_inv {C : Finset ι} {i₀ : ι} (hi : i₀ ∈ C) {f : (ι → ℂ) → ℂ}
    (hf : InvAlong C i₀ f) : coef f C = 0 := by
  have h0 : (0 : ι → ℂ) ∈ supportedOn C := fun i _ => rfl
  have hl : ∀ a ∈ Finset.univ.toList.filter (· ∈ C), a ∈ C := fun a ha => mem_filter_toList.mp ha
  unfold coef
  have := iterInt_congr_supportedOn (C := C)
    (h := pderList (Finset.univ.toList.filter (· ∈ C)) f) (h' := fun _ => 0)
    (fun w hw => pderList_eq_zero_of_inv _ hl (mem_filter_toList.mpr hi) hf w hw) _ hl h0
  rw [this]
  exact iterInt_zero _ _

/-! ### The Cauchy bound -/

/-- `‖F_C‖ ≤ B (R-1)^{-|C|}`. -/
theorem norm_coef_le {R : ℝ} (hR : 1 < R) {f : (ι → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f (polydisc (0 : ι → ℂ) (fun _ => R))) {B : ℝ}
    (hB : ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => R), ‖f s‖ ≤ B) (C : Finset ι) :
    ‖coef f C‖ ≤ B / (R - 1) ^ C.card := by
  have h0P : (0 : ι → ℂ) ∈ polydisc (0 : ι → ℂ) (fun _ => R) := fun i => by simp; linarith
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 h0P)
  have hpos : 0 < (R - 1) ^ C.card := pow_pos (by linarith) _
  unfold coef
  refine norm_iterInt_le (b := B / (R - 1) ^ C.card) (fun w hw => ?_) _ (fun j _ => by simp)
  have h1 := norm_pderList_le (c := (0 : ι → ℂ)) (r := fun _ => R) hf hB
    (Finset.univ.toList.filter (· ∈ C)) (nodup_filter_toList C) (unitCube_subset_polydisc hR hw)
  rw [toFinset_filter_toList] at h1
  refine h1.trans (div_le_div_of_nonneg_left hB0 hpos ?_)
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => by linarith) (fun i _ => by
    have := hw i; simp only [Pi.zero_apply, sub_zero]; linarith)

theorem sub_one_ge_exp {κ₁ : ℝ} (hκ : 1 ≤ κ₁) : Real.exp (κ₁ - 1) ≤ Real.exp κ₁ - 1 := by
  have h1 : 1 ≤ Real.exp (κ₁ - 1) := Real.one_le_exp (by linarith)
  have h2 : Real.exp κ₁ = Real.exp (κ₁ - 1) * Real.exp 1 := by
    rw [← Real.exp_add]; ring_nf
  have h3 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  nlinarith

theorem norm_coef_le_exp {κ₁ : ℝ} (hκ : 1 ≤ κ₁) {f : (ι → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f (polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁))) {B : ℝ}
    (hB : ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁), ‖f s‖ ≤ B) (C : Finset ι) :
    ‖coef f C‖ ≤ B * Real.exp (-(κ₁ - 1) * C.card) := by
  have hR : 1 < Real.exp κ₁ := Real.one_lt_exp_iff.mpr (by linarith)
  have h0P : (0 : ι → ℂ) ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁) := fun i => by
    simp; linarith
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 h0P)
  refine (norm_coef_le hR hf hB C).trans ?_
  have hx : 0 < Real.exp (κ₁ - 1) := Real.exp_pos _
  have hle : (Real.exp (κ₁ - 1)) ^ C.card ≤ (Real.exp κ₁ - 1) ^ C.card :=
    pow_le_pow_left₀ hx.le (sub_one_ge_exp hκ) _
  have : Real.exp (-(κ₁ - 1) * C.card) = 1 / (Real.exp (κ₁ - 1)) ^ C.card := by
    rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg]; ring_nf
  rw [this, mul_one_div]
  exact div_le_div_of_nonneg_left hB0 (pow_pos hx _) hle

/-! ### Lemma AE -/

section AE

variable {Ω E : Type*}

/-- A family `C` of patches is connected (with respect to `Y`) if each patch lies in `Y C`. -/
def IsConnectedFamily (P : ι → Set Ω) (Y : Finset ι → Set Ω) (C : Finset ι) : Prop :=
  ∀ i ∈ C, P i ⊆ Y C

/-- The locality hypothesis (AE2). -/
def LocalityAE (P : ι → Set Ω) (Y : Finset ι → Set Ω) (F : (Ω → E) → (ι → ℂ) → ℂ) : Prop :=
  ∀ (C : Finset ι) (u u' : Ω → E) (s s' : ι → ℂ), s ∈ supportedOn C → s' ∈ supportedOn C →
    (∀ i ∈ C, P i ⊆ Y C → s i = s' i) → (∀ x ∈ Y C, u x = u' x) → F u s = F u' s'

theorem coef_eq_zero_of_not_connected {P : ι → Set Ω} {Y : Finset ι → Set Ω}
    {F : (Ω → E) → (ι → ℂ) → ℂ} (hloc : LocalityAE P Y F) (u : Ω → E) {C : Finset ι}
    (hC : ¬ IsConnectedFamily P Y C) : coef (F u) C = 0 := by
  simp only [IsConnectedFamily, not_forall] at hC
  obtain ⟨i₀, hi₀, hP⟩ := hC
  refine coef_eq_zero_of_inv hi₀ fun w hw τ => ?_
  refine hloc C u u _ _ (add_single_mem_supportedOn hw hi₀ τ) hw (fun i hi hPi => ?_)
    (fun _ _ => rfl)
  have : i ≠ i₀ := fun h => hP (h ▸ hPi)
  simp [Pi.single_eq_of_ne this]

theorem coef_congr_of_agree {P : ι → Set Ω} {Y : Finset ι → Set Ω}
    {F : (Ω → E) → (ι → ℂ) → ℂ} (hloc : LocalityAE P Y F) (C : Finset ι)
    {u u' : Ω → E} (huu : ∀ x ∈ Y C, u x = u' x) :
    coef (F u) C = coef (F u') C :=
  coef_congr fun w hw => hloc C u u' w w hw hw (fun _ _ _ => rfl) huu

open scoped Classical in
/-- **Lemma AE** (abstract interpolation–resummation; P3 (4.41), (4.43), (4.47)). -/
theorem abstract_expansion {P : ι → Set Ω} {Y : Finset ι → Set Ω} {F : (Ω → E) → (ι → ℂ) → ℂ}
    {κ₁ B : ℝ} (hκ : 1 ≤ κ₁)
    (hana : ∀ u, AnalyticOnNhd ℂ (F u) (polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁)))
    (hbd : ∀ u, ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁), ‖F u s‖ ≤ B)
    (hloc : LocalityAE P Y F) :
    (∀ u, F u 1 = ∑ C ∈ Finset.univ.filter (fun C => IsConnectedFamily P Y C), coef (F u) C) ∧
    (∀ u C, ¬ IsConnectedFamily P Y C → coef (F u) C = 0) ∧
    (∀ C u u', (∀ x ∈ Y C, u x = u' x) →
      coef (F u) C = coef (F u') C) ∧
    (∀ u C, ‖coef (F u) C‖ ≤ B / (Real.exp κ₁ - 1) ^ C.card) ∧
    (∀ u C, ‖coef (F u) C‖ ≤ B * Real.exp (-(κ₁ - 1) * C.card)) := by
  classical
  have hR : 1 < Real.exp κ₁ := Real.one_lt_exp_iff.mpr (by linarith)
  refine ⟨fun u => ?_, fun u C hC => coef_eq_zero_of_not_connected hloc u hC,
    fun C u u' huu => coef_congr_of_agree hloc C huu,
    fun u C => norm_coef_le hR (hana u) (hbd u) C,
    fun u C => norm_coef_le_exp hκ (hana u) (hbd u) C⟩
  rw [sum_coef_eq hR (hana u), Finset.sum_filter]
  refine Finset.sum_congr rfl fun C _ => ?_
  split_ifs with h
  · rfl
  · exact coef_eq_zero_of_not_connected hloc u h

end AE

end Balaban.Localization
