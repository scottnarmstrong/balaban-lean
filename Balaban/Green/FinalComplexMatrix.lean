/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalMassSqrt
public import Balaban.Localization.DecoupledCovAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Complex perturbations of the final reference operator (FINAL §3, package 5)

Let `U = finalOp d L N₀ k v a` be the real reference operator of `Green/FinalMassGreen.lean`, with
gap `g_* = finalGap d L`, entry decay `|U_{xy}| ≤ c_* e^{-s_* dist x y}` and Combes–Thomas rate
`r_* = finalRate d L`.  A complex matrix `E` on the same torus is *`(r, η)`-small* (`WSmall r η E`)
when its exponentially weighted row sums and column sums are at most `η`:
`∑_y ‖E x y‖ e^{r dist x y} ≤ η` and `∑_x ‖E x y‖ e^{r dist x y} ≤ η`.

For `0 < r`, `0 ≤ η < g_*` and `WSmall r η E` we prove, by route (A) (the Combes–Thomas theorem
applied directly to `U + E`):

* `U + E` is `(g_* − η)`-coercive (Schur test) and has entries `≤ (c_* + η) e^{-min(s_*, r) dist}`;
* for every `t ≥ 0`, `U + E + t` is invertible and
  `‖(U + E + t)⁻¹ x y‖ ≤ 2/((g_* − η) + t) · e^{-r′ dist x y}` with
  `r′ = ctRate (c_* + η) (min s_* r) (g_* − η) (ballConst d (min s_* r / 4))`;
* `ResOK (U + E)`, `sqrtMat (U+E)² = (U+E)⁻¹`, and the entries of `(U+E)⁻¹` and of `sqrtMat (U+E)`
  are bounded by `2/(g_*−η)` and `2/√(g_*−η)` times `e^{-r′ dist}`;
* along a family `z ↦ E z` analytic on an open set, with `WSmall r η (E z)` for all `z`, the
  entries of `(U + E z)⁻¹` (and, for `z ∈ ℂ`, of `sqrtMat (U + E z)`) are analytic.

All constants are independent of the torus size, of `k`, of `t` and of `E` in the class.

NOT proved here: that the physical chart of the last step produces a perturbation in this class
(`FINAL-COMPLEX-DOMAIN`), the identification of the reference operator with the Hessian of the
final density (`FINAL-HESSIAN-BRIDGE`), and the cut-parameter family needed for exact locality.
-/

@[expose] public section

open Matrix Finset MeasureTheory Set

namespace Balaban.Green

section WeightedClass

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace ι]

/-- `E` is `(r, η)`-small: its row sums and column sums of `‖E x y‖ e^{r dist x y}` are at most
`η`. -/
def WSmall (r η : ℝ) (E : Matrix ι ι ℂ) : Prop :=
  (∀ x, ∑ y, ‖E x y‖ * Real.exp (r * dist x y) ≤ η) ∧
  (∀ y, ∑ x, ‖E x y‖ * Real.exp (r * dist x y) ≤ η)

omit [DecidableEq ι] in
theorem WSmall.entry {r η : ℝ} {E : Matrix ι ι ℂ} (h : WSmall r η E) (x y : ι) :
    ‖E x y‖ ≤ η * Real.exp (-r * dist x y) := by
  have h1 : ‖E x y‖ * Real.exp (r * dist x y) ≤ η :=
    (Finset.single_le_sum (f := fun y => ‖E x y‖ * Real.exp (r * dist x y))
      (fun _ _ => by positivity) (Finset.mem_univ y)).trans (h.1 x)
  have h2 : Real.exp (r * dist x y) * Real.exp (-r * dist x y) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 := Real.exp_pos (-r * dist x y)
  calc ‖E x y‖ = ‖E x y‖ * Real.exp (r * dist x y) * Real.exp (-r * dist x y) := by
        rw [mul_assoc, h2, mul_one]
    _ ≤ η * Real.exp (-r * dist x y) := mul_le_mul_of_nonneg_right h1 h3.le

omit [DecidableEq ι] in
theorem WSmall.mono {r η η' : ℝ} {E : Matrix ι ι ℂ} (h : WSmall r η E) (hη : η ≤ η') :
    WSmall r η' E :=
  ⟨fun x => (h.1 x).trans hη, fun y => (h.2 y).trans hη⟩

omit [DecidableEq ι] in
theorem WSmall.add {r η η' : ℝ} {E F : Matrix ι ι ℂ} (hE : WSmall r η E) (hF : WSmall r η' F) :
    WSmall r (η + η') (E + F) := by
  have key : ∀ x y, ‖(E + F) x y‖ * Real.exp (r * dist x y) ≤
      ‖E x y‖ * Real.exp (r * dist x y) + ‖F x y‖ * Real.exp (r * dist x y) := fun x y => by
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (by simpa [Matrix.add_apply] using norm_add_le (E x y) (F x y))
      (Real.exp_pos _).le
  refine ⟨fun x => ?_, fun y => ?_⟩
  · calc _ ≤ ∑ y, (‖E x y‖ * Real.exp (r * dist x y) + ‖F x y‖ * Real.exp (r * dist x y)) :=
          Finset.sum_le_sum fun y _ => key x y
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := add_le_add (hE.1 x) (hF.1 x)
  · calc _ ≤ ∑ x, (‖E x y‖ * Real.exp (r * dist x y) + ‖F x y‖ * Real.exp (r * dist x y)) :=
          Finset.sum_le_sum fun x _ => key x y
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := add_le_add (hE.2 y) (hF.2 y)

omit [DecidableEq ι] in
theorem WSmall.smul {r η : ℝ} {E : Matrix ι ι ℂ} (h : WSmall r η E) (c : ℂ) :
    WSmall r (‖c‖ * η) (c • E) := by
  have key : ∀ x y, ‖(c • E) x y‖ * Real.exp (r * dist x y) =
      ‖c‖ * (‖E x y‖ * Real.exp (r * dist x y)) := fun x y => by
    simp only [Matrix.smul_apply, smul_eq_mul, norm_mul]; ring
  refine ⟨fun x => ?_, fun y => ?_⟩
  · simp only [key, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (h.1 x) (norm_nonneg _)
  · simp only [key, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (h.2 y) (norm_nonneg _)

omit [DecidableEq ι] in
theorem WSmall.neg {r η : ℝ} {E : Matrix ι ι ℂ} (h : WSmall r η E) : WSmall r η (-E) := by
  have := h.smul (-1)
  simpa using this

omit [DecidableEq ι] in
theorem WSmall.zero {r η : ℝ} (hη : 0 ≤ η) : WSmall r η (0 : Matrix ι ι ℂ) :=
  ⟨fun x => by simpa using hη, fun y => by simpa using hη⟩

/-- A scalar multiple of the identity is `(r, ‖c‖)`-small for every `r`. -/
theorem wSmall_smul_one (r : ℝ) (c : ℂ) {η : ℝ} (hc : ‖c‖ ≤ η) :
    WSmall r η (c • (1 : Matrix ι ι ℂ)) := by
  refine ⟨fun x => ?_, fun y => ?_⟩
  · rw [Finset.sum_eq_single x]
    · simpa using hc
    · intro b _ hb
      simp [Matrix.one_apply_ne (Ne.symm hb)]
    · simp
  · rw [Finset.sum_eq_single y]
    · simpa using hc
    · intro b _ hb
      simp [Matrix.one_apply_ne hb]
    · simp

/-- Non-vacuity of the class: it contains `0`, and a non-zero matrix for every `η > 0`
(on a non-empty index set). -/
theorem wSmall_nonempty [Nonempty ι] (r : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ E : Matrix ι ι ℂ, E ≠ 0 ∧ WSmall r η E := by
  refine ⟨((η : ℂ)) • 1, ?_, wSmall_smul_one r _ (by simp [abs_of_pos hη])⟩
  intro h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have := congrFun (congrFun h i) i
  simp at this
  linarith

omit [DecidableEq ι] in
/-- **Schur test**: for `0 ≤ r`, an `(r, η)`-small `E` has `-η‖v‖² ≤ Re⟨v, E v⟩`. -/
theorem WSmall.reQuad_ge {r η : ℝ} (hr : 0 ≤ r) {E : Matrix ι ι ℂ} (h : WSmall r η E)
    (v : ι → ℂ) : -(η * sqNorm v) ≤ reQuad E v := by
  have hle : ∀ x y, ‖E x y‖ ≤ ‖E x y‖ * Real.exp (r * dist x y) := fun x y => by
    have : 1 ≤ Real.exp (r * dist x y) :=
      Real.one_le_exp (mul_nonneg hr dist_nonneg)
    nlinarith [norm_nonneg (E x y)]
  exact reQuad_ge_of_entry_bound E (fun x y => ‖E x y‖) (fun _ _ => le_rfl)
    (fun x => (Finset.sum_le_sum fun y _ => hle x y).trans (h.1 x))
    (fun y => (Finset.sum_le_sum fun x _ => hle x y).trans (h.2 y)) v

omit [DecidableEq ι] in
/-- Two-sided Schur bound: `|Re⟨v, E v⟩| ≤ η‖v‖²`. -/
theorem WSmall.abs_reQuad_le {r η : ℝ} (hr : 0 ≤ r) {E : Matrix ι ι ℂ} (h : WSmall r η E)
    (v : ι → ℂ) : |reQuad E v| ≤ η * sqNorm v := by
  have h1 := h.reQuad_ge hr v
  have h2 := h.neg.reQuad_ge hr v
  have e : reQuad (-E) v = -reQuad E v := by
    have := reQuad_add E (-E) v
    have h0 : reQuad (0 : Matrix ι ι ℂ) v = 0 := by simp [reQuad]
    rw [add_neg_cancel, h0] at this
    linarith
  rw [e] at h2
  rw [abs_le]; constructor <;> linarith

omit [DecidableEq ι] in
/-- Coercivity survives a small perturbation: `γ`-coercive `A` plus `(r, η)`-small `E` is
`(γ - η)`-coercive. -/
theorem IsCoercive.add_wSmall {A : Matrix ι ι ℂ} {γ r η : ℝ} (hA : IsCoercive A γ) (hr : 0 ≤ r)
    {E : Matrix ι ι ℂ} (hE : WSmall r η E) : IsCoercive (A + E) (γ - η) := by
  intro v
  rw [reQuad_add]
  have := hA v
  have := hE.reQuad_ge hr v
  nlinarith

end WeightedClass

section NearestNeighbour

variable {d m : ℕ} [NeZero m]

/-- A small multiple of the nearest-neighbour matrix on the `ℓ¹` torus is in the class:
`ε · 1[dist x y = 1]` is `(r, ‖ε‖ e^{r+1} ballConst d 1)`-small. -/
theorem wSmall_nearestNeighbour (r : ℝ) (ε : ℂ) :
    WSmall r (‖ε‖ * Real.exp r * (Real.exp 1 * ballConst d 1))
      (Matrix.of fun x y : L1Torus d m => if dist x y = 1 then ε else 0) := by
  have term : ∀ x y : L1Torus d m,
      ‖(Matrix.of fun x y : L1Torus d m => if dist x y = 1 then ε else 0) x y‖ *
          Real.exp (r * dist x y) ≤
        ‖ε‖ * Real.exp r * Real.exp 1 * Real.exp (-1 * dist x y) := fun x y => by
    by_cases h : dist x y = 1
    · simp only [Matrix.of_apply, h, ite_true, mul_one]
      rw [mul_assoc (‖ε‖ * Real.exp r), ← Real.exp_add]; simp
    · simp only [Matrix.of_apply, h, ite_false, norm_zero, zero_mul]; positivity
  have hb : ∀ x : L1Torus d m, ∑ y, Real.exp (-1 * dist x y) ≤ ballConst d 1 :=
    fun x => ballSum_L1Torus (d := d) (m := m) one_pos x
  have hn : 0 ≤ ‖ε‖ * Real.exp r * Real.exp 1 := by positivity
  refine ⟨fun x => ?_, fun y => ?_⟩
  · calc _ ≤ ∑ y, ‖ε‖ * Real.exp r * Real.exp 1 * Real.exp (-1 * dist x y) :=
          Finset.sum_le_sum fun y _ => term x y
      _ = ‖ε‖ * Real.exp r * Real.exp 1 * ∑ y, Real.exp (-1 * dist x y) := by
          rw [Finset.mul_sum]
      _ ≤ ‖ε‖ * Real.exp r * Real.exp 1 * ballConst d 1 :=
          mul_le_mul_of_nonneg_left (hb x) hn
      _ = _ := by ring
  · calc _ ≤ ∑ x, ‖ε‖ * Real.exp r * Real.exp 1 * Real.exp (-1 * dist y x) := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [dist_comm y x]; exact term x y
      _ = ‖ε‖ * Real.exp r * Real.exp 1 * ∑ x, Real.exp (-1 * dist y x) := by
          rw [Finset.mul_sum]
      _ ≤ ‖ε‖ * Real.exp r * Real.exp 1 * ballConst d 1 :=
          mul_le_mul_of_nonneg_left (hb y) hn
      _ = _ := by ring

end NearestNeighbour

section Perturbed

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

private instance : Nonempty (L1Torus d N₀) := ⟨(0 : Torus d N₀)⟩

/-- **Entry decay of `U + E`** (T2): constant `c_* + η`, rate `min(s_*, r)`. -/
theorem finalPert_entry_decay (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) {r η : ℝ} {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ}
    (hE : WSmall r η E) (x y : L1Torus d N₀) :
    ‖(finalOp d L N₀ k v a + E) x y‖ ≤
      (finalDecayC d L + η) * Real.exp (-min (blockDecayRate d) r * dist x y) := by
  have h1 := finalMass_entry_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 ha1 ha2 x y
  have h2 := hE.entry x y
  have hC := finalDecayC_pos (L := L) hd
  have hη : 0 ≤ η := le_trans (by positivity) (hE.1 x)
  have hdist : 0 ≤ dist x y := dist_nonneg
  have e1 : Real.exp (-blockDecayRate d * dist x y) ≤ Real.exp (-min (blockDecayRate d) r * dist x y) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left (blockDecayRate d) r])
  have e2 : Real.exp (-r * dist x y) ≤ Real.exp (-min (blockDecayRate d) r * dist x y) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right (blockDecayRate d) r])
  calc ‖(finalOp d L N₀ k v a + E) x y‖ ≤ ‖finalOp d L N₀ k v a x y‖ + ‖E x y‖ := by
        simpa [Matrix.add_apply] using norm_add_le (finalOp d L N₀ k v a x y) (E x y)
    _ ≤ finalDecayC d L * Real.exp (-min (blockDecayRate d) r * dist x y) +
        η * Real.exp (-min (blockDecayRate d) r * dist x y) :=
        add_le_add (h1.trans (mul_le_mul_of_nonneg_left e1 hC.le))
          (h2.trans (mul_le_mul_of_nonneg_left e2 hη))
    _ = _ := by ring

/-- **Coercivity of `U + E`** (T2): `Re⟨u, (U+E) u⟩ ≥ (g_* − η)‖u‖²`. -/
theorem finalPert_isCoercive (hd : 0 < d) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha : 1 / 2 ≤ a) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) {r η : ℝ} (hr : 0 ≤ r)
    {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hE : WSmall r η E) :
    IsCoercive (finalOp d L N₀ k v a + E) (finalGap d L - η) :=
  (finalMass_isCoercive (k := k) hd hv0 hv1 ha hmass).add_wSmall hr hE

/-- **Resolvent decay of `U + E`** (T3).  For `0 < r`, `0 ≤ η < g_*`, `WSmall r η E`, every
`t ≥ 0`: `U + E + t` is invertible and
`‖(U + E + t)⁻¹ x y‖ ≤ 2/((g_* − η) + t) · e^{-r′ dist x y}`,
`r′ = ctRate (c_* + η) (min s_* r) (g_* − η) (ballConst d (min s_* r / 4))`. -/
theorem finalPert_resolvent_decay (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {r η : ℝ} (hr : 0 < r) (hη0 : 0 ≤ η) (hηg : η < finalGap d L)
    {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hE : WSmall r η E) {t : ℝ} (ht : 0 ≤ t) :
    IsUnit (finalOp d L N₀ k v a + E + (t : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ)) ∧
      ∀ x y : L1Torus d N₀,
        ‖(finalOp d L N₀ k v a + E + (t : ℂ) •
            (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ))⁻¹ x y‖ ≤
          2 / ((finalGap d L - η) + t) *
            Real.exp (-ctRate (finalDecayC d L + η) (min (blockDecayRate d) r)
              (finalGap d L - η) (ballConst d (min (blockDecayRate d) r / 4)) * dist x y) := by
  have hs := blockDecayRate_pos hd
  have hm : 0 < min (blockDecayRate d) r := lt_min hs hr
  have hC := finalDecayC_pos (L := L) hd
  have := combesThomas (c₀ := finalDecayC d L + η) (δ₀ := min (blockDecayRate d) r)
    (γ₀ := finalGap d L - η) (κ := ballConst d (min (blockDecayRate d) r / 4))
    (by linarith) hm (by linarith) (ballConst_decay_nonneg (by positivity))
    (finalPert_entry_decay hd hk hv0 ha1 ha2 hE)
    (fun x => ballSum_L1Torus (d := d) (m := N₀) (by positivity) x)
    (finalPert_isCoercive hd hv0 hv1 ha1 hmass hr.le hE) ht
  refine ⟨this.1, fun x y => (this.2 x y).trans_eq ?_⟩
  simp only [div_eq_mul_inv]

/-- The uniform form (T3): for `WSmall r η E` with `η ≤ g_*/4` the same holds with `η`
replaced by `g_*/4`; the constants then depend only on `d, L, r`. -/
theorem finalPert_resolvent_decay_uniform (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {r η : ℝ} (hr : 0 < r) (hη : η ≤ finalGap d L / 4)
    {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hE : WSmall r η E) {t : ℝ} (ht : 0 ≤ t) :
    IsUnit (finalOp d L N₀ k v a + E + (t : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ)) ∧
      ∀ x y : L1Torus d N₀,
        ‖(finalOp d L N₀ k v a + E + (t : ℂ) •
            (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ))⁻¹ x y‖ ≤
          2 / ((finalGap d L - finalGap d L / 4) + t) *
            Real.exp (-ctRate (finalDecayC d L + finalGap d L / 4) (min (blockDecayRate d) r)
              (finalGap d L - finalGap d L / 4)
              (ballConst d (min (blockDecayRate d) r / 4)) * dist x y) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  exact finalPert_resolvent_decay hd hk hv0 hv1 ha1 ha2 hmass hr (by linarith) (by linarith)
    (hE.mono hη) ht

/-- `U + E` has resolvent entries for all `x ≥ 0` (`ResOK`). -/
theorem finalPert_resOK (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {r η : ℝ} (hr : 0 < r) (hη0 : 0 ≤ η) (hηg : η < finalGap d L)
    {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hE : WSmall r η E) :
    Localization.ResOK (finalOp d L N₀ k v a + E) := by
  intro x hx
  have := (finalPert_resolvent_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass hr
    hη0 hηg hE hx).1
  rwa [add_comm] at this

/-- Entries of the inverse of `U + E` (T4). -/
theorem finalPert_inverse_decay (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {r η : ℝ} (hr : 0 < r) (hη0 : 0 ≤ η) (hηg : η < finalGap d L)
    {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hE : WSmall r η E) (x y : L1Torus d N₀) :
    ‖(finalOp d L N₀ k v a + E)⁻¹ x y‖ ≤
      2 / (finalGap d L - η) *
        Real.exp (-ctRate (finalDecayC d L + η) (min (blockDecayRate d) r)
          (finalGap d L - η) (ballConst d (min (blockDecayRate d) r / 4)) * dist x y) := by
  have h := (finalPert_resolvent_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass
    hr hη0 hηg hE (le_refl (0 : ℝ))).2 x y
  simpa using h

/-- The Stieltjes integration step: a resolvent bound `2/(γ+t) e^{-ρ dist}` for all `t ≥ 0`
gives `‖sqrtMat M x y‖ ≤ 2/√γ e^{-ρ dist}`. -/
theorem sqrtMat_entry_le_of_resolvent {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [PseudoMetricSpace ι] (M : Matrix ι ι ℂ) {γ ρ : ℝ} (hγ : 0 < γ)
    (hres : ∀ t : ℝ, 0 ≤ t → ∀ x y : ι,
      ‖(M + (t : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ x y‖ ≤ 2 / (γ + t) * Real.exp (-ρ * dist x y))
    (x y : ι) :
    ‖Localization.sqrtMat M x y‖ ≤ 2 / Real.sqrt γ * Real.exp (-ρ * dist x y) := by
  set B0 : ℝ := 2 * Real.exp (-ρ * dist x y) with hB0
  have hB0nn : 0 ≤ B0 := by rw [hB0]; positivity
  unfold Localization.sqrtMat
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold Localization.intMat
  have hint : Integrable (fun s : ℝ => B0 * (s ^ (-(1 / 2 : ℝ)) * (γ + s)⁻¹))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (Localization.integrableOn_rpow_inv_add hγ).const_mul B0
  have hbound := norm_integral_le_of_norm_le
    (f := fun s : ℝ => (((s ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      ((s : ℂ) • (1 : Matrix ι ι ℂ) + M)⁻¹) x y)
    hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => by
      have hs0 : 0 < s := mem_Ioi.mp hs
      have h3 : 0 < s ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hs0 _
      simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg h3.le]
      have := hres s hs0.le x y
      rw [add_comm] at this
      calc s ^ (-(1 / 2 : ℝ)) * ‖((s : ℂ) • (1 : Matrix ι ι ℂ) + M)⁻¹ x y‖
          ≤ s ^ (-(1 / 2 : ℝ)) * (B0 * (γ + s)⁻¹) := by
            refine mul_le_mul_of_nonneg_left (this.trans (le_of_eq ?_)) h3.le
            rw [hB0]; ring
        _ = _ := by ring))
  rw [integral_const_mul, Localization.integral_rpow_inv_add hγ] at hbound
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : 0 < Real.sqrt γ := Real.sqrt_pos.2 hγ
  rw [abs_of_pos (by positivity)]
  calc 1 / Real.pi * ‖∫ s in Ioi (0 : ℝ), (((s ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
        ((s : ℂ) • (1 : Matrix ι ι ℂ) + M)⁻¹) x y‖
      ≤ 1 / Real.pi * (B0 * (Real.pi / Real.sqrt γ)) := by gcongr
    _ = _ := by rw [hB0]; field_simp

/-- `sqrtMat (U + E)` is the principal inverse square root (T4). -/
theorem finalPert_sqrt_mul_self (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {r η : ℝ} (hr : 0 < r) (hη0 : 0 ≤ η) (hηg : η < finalGap d L)
    {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hE : WSmall r η E) :
    Localization.sqrtMat (finalOp d L N₀ k v a + E) * Localization.sqrtMat (finalOp d L N₀ k v a + E) =
      (finalOp d L N₀ k v a + E)⁻¹ :=
  Localization.sqrtMat_mul_self (finalPert_resOK hd hk hv0 hv1 ha1 ha2 hmass hr hη0 hηg hE)

/-- **Inverse square root decay of `U + E`** (T4). -/
theorem finalPert_sqrt_decay (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {r η : ℝ} (hr : 0 < r) (hη0 : 0 ≤ η) (hηg : η < finalGap d L)
    {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hE : WSmall r η E) (x y : L1Torus d N₀) :
    ‖Localization.sqrtMat (finalOp d L N₀ k v a + E) x y‖ ≤
      2 / Real.sqrt (finalGap d L - η) *
        Real.exp (-ctRate (finalDecayC d L + η) (min (blockDecayRate d) r)
          (finalGap d L - η) (ballConst d (min (blockDecayRate d) r / 4)) * dist x y) :=
  sqrtMat_entry_le_of_resolvent _ (by linarith)
    (fun t ht x y => by
      have := (finalPert_resolvent_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass
        hr hη0 hηg hE ht).2 x y
      exact this) x y

/-! ### Holomorphy -/

/-- Entries of `(U + E z)⁻¹` are analytic along an analytic family in the class (T5). -/
theorem finalPert_analytic_inverse (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {r η : ℝ} (hr : 0 < r) (hη0 : 0 ≤ η) (hηg : η < finalGap d L)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {Ω : Set F}
    {E : F → Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ}
    (hana : ∀ z ∈ Ω, ∀ i j, AnalyticAt ℂ (fun w => E w i j) z)
    (hE : ∀ z ∈ Ω, WSmall r η (E z)) (x y : L1Torus d N₀) :
    ∀ z ∈ Ω, AnalyticAt ℂ (fun w => (finalOp d L N₀ k v a + E w)⁻¹ x y) z := by
  intro z hz
  have hM : Localization.RectAt (fun w => finalOp d L N₀ k v a + E w) z :=
    (Localization.RectAt.const _ z).add (hana z hz)
  have hdet : ((finalOp d L N₀ k v a + E z)).det ≠ 0 := by
    have := (finalPert_resolvent_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass
      hr hη0 hηg (hE z hz) (le_refl (0 : ℝ))).1
    simp only [Complex.ofReal_zero, zero_smul, add_zero] at this
    exact (Matrix.isUnit_iff_isUnit_det _).1 this |>.ne_zero
  exact hM.inv hdet x y

/-- Entries of `sqrtMat (U + E z)` are analytic on an open set of `ℂ` along an analytic family in
the class (T5). -/
theorem finalPert_analytic_sqrt (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {r η : ℝ} (hr : 0 < r) (hη0 : 0 ≤ η) (hηg : η < finalGap d L)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {E : ℂ → Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ}
    (hana : ∀ z ∈ Ω, ∀ i j, AnalyticAt ℂ (fun w => E w i j) z)
    (hE : ∀ z ∈ Ω, WSmall r η (E z)) (x y : L1Torus d N₀) :
    AnalyticOnNhd ℂ (fun z => Localization.sqrtMat (finalOp d L N₀ k v a + E z) x y) Ω :=
  Localization.analyticOnNhd_sqrtMat_fam hΩ
    (fun z hz => finalPert_resOK hd hk hv0 hv1 ha1 ha2 hmass hr hη0 hηg (hE z hz))
    (fun z hz => (Localization.RectAt.const _ z).add (hana z hz)) x y

/-! ### Non-vacuity at the parameters of `finalMass_instance` -/

/-- **Instance** (T6): `d = 3`, `L = 3`, `k = 1`, `a = 1`, `N₀ = 1`, `v ∈ (7/72, 1]`, `r = 1`.
For `E z = z · i · (g_*/8) · 1` (non-zero for `z ≠ 0`) and `z` in the open unit disc, `E z` is
`(1, g_*/8)`-small, `U + E z + t` is invertible with the resolvent bound for all `t ≥ 0`, the
square root satisfies the entry bound, and `z ↦ sqrtMat (U + E z)` is entrywise analytic on the
disc. -/
theorem finalPert_instance {v : ℝ} (hv : 7 / 72 < v) (hv1 : v ≤ 1)
    (E : ℂ → Matrix (L1Torus 3 1) (L1Torus 3 1) ℂ)
    (hE : ∀ z, E z = (z * Complex.I * ((finalGap 3 3 / 8 : ℝ) : ℂ)) • 1) :
    E 1 ≠ 0 ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, WSmall 1 (finalGap 3 3 / 8) (E z)) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ t : ℝ, 0 ≤ t →
      IsUnit (finalOp 3 3 1 1 v 1 + E z + (t : ℂ) • (1 : Matrix (L1Torus 3 1) (L1Torus 3 1) ℂ)) ∧
      ∀ x y : L1Torus 3 1,
        ‖(finalOp 3 3 1 1 v 1 + E z + (t : ℂ) • (1 : Matrix (L1Torus 3 1) (L1Torus 3 1) ℂ))⁻¹ x y‖ ≤
          2 / ((finalGap 3 3 - finalGap 3 3 / 8) + t) *
            Real.exp (-ctRate (finalDecayC 3 3 + finalGap 3 3 / 8) (min (blockDecayRate 3) 1)
              (finalGap 3 3 - finalGap 3 3 / 8)
              (ballConst 3 (min (blockDecayRate 3) 1 / 4)) * dist x y)) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ x y : L1Torus 3 1,
      ‖Localization.sqrtMat (finalOp 3 3 1 1 v 1 + E z) x y‖ ≤
        2 / Real.sqrt (finalGap 3 3 - finalGap 3 3 / 8) *
          Real.exp (-ctRate (finalDecayC 3 3 + finalGap 3 3 / 8) (min (blockDecayRate 3) 1)
            (finalGap 3 3 - finalGap 3 3 / 8)
            (ballConst 3 (min (blockDecayRate 3) 1 / 4)) * dist x y)) ∧
    (∀ x y : L1Torus 3 1, AnalyticOnNhd ℂ
      (fun z => Localization.sqrtMat (finalOp 3 3 1 1 v 1 + E z) x y) (Metric.ball (0 : ℂ) 1)) := by
  have hm : 7 / 8 * (((3 : ℕ) : ℝ) ^ 2)⁻¹ < v := by norm_num; linarith
  have hv0 : (0 : ℝ) ≤ v := by linarith
  have hg : 0 < finalGap 3 3 := finalGap_pos (by norm_num)
  have hW : ∀ z ∈ Metric.ball (0 : ℂ) 1, WSmall 1 (finalGap 3 3 / 8) (E z) := by
    intro z hz
    rw [hE]
    refine wSmall_smul_one _ _ ?_
    have hz' : ‖z‖ < 1 := by simpa using hz
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]
    nlinarith
  have hηg : finalGap 3 3 / 8 < finalGap 3 3 := by linarith
  have hη0 : (0 : ℝ) ≤ finalGap 3 3 / 8 := by positivity
  refine ⟨?_, hW, fun z hz t ht => ?_, fun z hz x y => ?_, fun x y => ?_⟩
  · rw [hE]
    intro h
    let i : L1Torus 3 1 := (0 : Torus 3 1)
    have := congrFun (congrFun h i) i
    simp at this
    linarith
  · exact finalPert_resolvent_decay (by norm_num) le_rfl hv0 hv1 (by norm_num) (by norm_num) hm
      one_pos hη0 hηg (hW z hz) ht
  · exact finalPert_sqrt_decay (by norm_num) le_rfl hv0 hv1 (by norm_num) (by norm_num) hm
      one_pos hη0 hηg (hW z hz) x y
  · refine finalPert_analytic_sqrt (by norm_num) le_rfl hv0 hv1 (by norm_num) (by norm_num) hm
      one_pos hη0 hηg Metric.isOpen_ball (fun z _ i j => ?_) hW x y
    simp only [hE, Matrix.smul_apply, smul_eq_mul]
    fun_prop

end Perturbed

end Balaban.Green
