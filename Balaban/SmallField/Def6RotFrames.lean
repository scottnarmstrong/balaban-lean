/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6RotContinuation
public import Balaban.SmallField.Def6RotFramesPolar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Complex invariance along the frames of the renormalization chain

The frame bridges of the renormalization step apply the complex invariance of `ℰ` to a complex
orthogonal `M = W' R W⁻¹`.  The landed class asks real `O(N)` invariance only
(`Def6RotContinuation`).  The matrices that occur are not near a real rotation (see
`notes/phase1/CROTE.md`), but they relate two points of the ball around `(e, e)`; their polar
decomposition `M = Q · cay(S)` (`Def6RotFramesPolar`) gives a path `s ↦ cay(sS)` that stays in a ball
of comparable radius.  This file proves the continuation along that path.

* `eq_of_rotation_family_local`: the identity theorem along a segment for a family of matrices
  that is analytic along the segment and real orthogonal at the real points near `0` only;
* `rotCay`: the family `w ↦ (1 - A(w))⁻¹ (1 + A(w))`; `rotE_eq_of_cay_path`: invariance along
  `R = Q · cay(S)`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Symmetry Balaban.SmallField Balaban.SmallField.Def6 Filter Topology

section Local

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ι : Type*} [Fintype ι]

theorem analyticAt_rotField_of_entries {R : (ι → ℂ) → Matrix (Fin N) (Fin N) ℂ} {w : ι → ℂ}
    (hR : ∀ i j, AnalyticAt ℂ (fun w => R w i j) w) (Ψ : Fld d L N₁ m₁ k N) :
    AnalyticAt ℂ (fun w => Def6.rotField (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
      (R w) Ψ) w := by
  refine analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_
  simp only [Def6.rotField, Matrix.mulVec, dotProduct]
  exact Finset.analyticAt_fun_sum _ fun l _ => (hR i l).mul analyticAt_const

/-- **The identity theorem along a segment, with the neighbourhood relative to a set `S`.**  As
`eq_of_rotation_family_local`, with `D ∈ 𝓝[S] (Ψ, h)` in place of `D ∈ 𝓝 (Ψ, h)`, where `S`
contains every pair `(R w Ψ, R w h)`.  (The class domain is open only relative to the layer-constant
pairs, so the neighbourhood of the start point is needed only within a set of such pairs.) -/
theorem eq_of_rotation_family_within [DecidableEq ι]
    (F : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (D : Set (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N))
    (hF : AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => F p.1 p.2) D)
    (hreal : ∀ Q : Matrix (Fin N) (Fin N) ℂ, IsRot Q → ∀ Ψ h, (Ψ, h) ∈ D →
      (rotField Q Ψ, rotField Q h) ∈ D → F (rotField Q Ψ) (rotField Q h) = F Ψ h)
    (R : (ι → ℂ) → Matrix (Fin N) (Fin N) ℂ) (hR0 : R 0 = 1)
    (S : Set (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N))
    {Ψ h : Fld d L N₁ m₁ k N} (hD : D ∈ 𝓝[S] (Ψ, h))
    (hS : ∀ w, (rotField (R w) Ψ, rotField (R w) h) ∈ S) {w₁ : ι → ℂ}
    (hRa : ∀ w ∈ segment ℝ (0 : ι → ℂ) w₁, ∀ i j, AnalyticAt ℂ (fun w => R w i j) w)
    (hRr : ∀ᶠ w in 𝓝 (0 : ι → ℂ), (∀ i, (w i).im = 0) → IsRot (R w))
    (hpath : ∀ w ∈ segment ℝ (0 : ι → ℂ) w₁, (rotField (R w) Ψ, rotField (R w) h) ∈ D) :
    F (rotField (R w₁) Ψ) (rotField (R w₁) h) = F Ψ h := by
  set q : (ι → ℂ) → Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N :=
    fun w => (rotField (R w) Ψ, rotField (R w) h) with hq
  have hqa : ∀ w ∈ segment ℝ (0 : ι → ℂ) w₁, AnalyticAt ℂ q w := fun w hw =>
    (analyticAt_rotField_of_entries (hRa w hw) Ψ).prod (analyticAt_rotField_of_entries (hRa w hw) h)
  have h0 : (0 : ι → ℂ) ∈ segment ℝ (0 : ι → ℂ) w₁ := left_mem_segment ℝ _ _
  have hq0 : q 0 = (Ψ, h) := by simp [hq, hR0, rotField_one]
  have hS0 : (Ψ, h) ∈ S := by simpa [hq, hR0, rotField_one] using hS 0
  have hev : ∀ᶠ w in 𝓝 (0 : ι → ℂ), q w ∈ D := by
    have ht : Tendsto q (𝓝 (0 : ι → ℂ)) (𝓝[S] (Ψ, h)) := by
      rw [← hq0]
      exact tendsto_nhdsWithin_iff.2 ⟨(hqa 0 h0).continuousAt, Eventually.of_forall hS⟩
    exact ht.eventually_mem hD
  have key := eq_zero_of_real_on_segment
    (g := fun w => F (q w).1 (q w).2 - F Ψ h) (w₁ := w₁)
    (fun w hw => ((hF (q w) (hpath w hw)).comp (hqa w hw)).sub analyticAt_const) (by
      filter_upwards [hev, hRr] with w hw hr hwr
      have := hreal (R w) (hr hwr) Ψ h (mem_of_mem_nhdsWithin hS0 hD) hw
      simpa [hq, sub_eq_zero] using this)
  simpa [hq, sub_eq_zero] using key


theorem eq_of_rotation_family_local [DecidableEq ι]
    (F : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (D : Set (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N))
    (hF : AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => F p.1 p.2) D)
    (hreal : ∀ Q : Matrix (Fin N) (Fin N) ℂ, IsRot Q → ∀ Ψ h, (Ψ, h) ∈ D →
      (rotField Q Ψ, rotField Q h) ∈ D → F (rotField Q Ψ) (rotField Q h) = F Ψ h)
    (R : (ι → ℂ) → Matrix (Fin N) (Fin N) ℂ) (hR0 : R 0 = 1)
    {Ψ h : Fld d L N₁ m₁ k N} (hD : D ∈ 𝓝 (Ψ, h)) {w₁ : ι → ℂ}
    (hRa : ∀ w ∈ segment ℝ (0 : ι → ℂ) w₁, ∀ i j, AnalyticAt ℂ (fun w => R w i j) w)
    (hRr : ∀ᶠ w in 𝓝 (0 : ι → ℂ), (∀ i, (w i).im = 0) → IsRot (R w))
    (hpath : ∀ w ∈ segment ℝ (0 : ι → ℂ) w₁, (rotField (R w) Ψ, rotField (R w) h) ∈ D) :
    F (rotField (R w₁) Ψ) (rotField (R w₁) h) = F Ψ h :=
  eq_of_rotation_family_within F D hF hreal R hR0 Set.univ (by rwa [nhdsWithin_univ])
    (fun _ => Set.mem_univ _) hRa hRr hpath

end Local


section Cayley

variable {N : ℕ}

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The Cayley family `w ↦ (1 - A(w))⁻¹ (1 + A(w))`, `A(w)` the antisymmetric matrix with
parameters `w`. -/
noncomputable def rotCay (w : Fin N × Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (1 - soParam w)⁻¹ * (1 + soParam w)

theorem rotCay_zero : rotCay (0 : Fin N × Fin N → ℂ) = 1 := by
  have : soParam (0 : Fin N × Fin N → ℂ) = 0 := by ext i j; simp [soParam]
  simp [rotCay, this]

theorem analyticAt_rotCay {w : Fin N × Fin N → ℂ} (hw : IsUnit (1 - soParam w).det) (i j : Fin N) :
    AnalyticAt ℂ (fun w => rotCay w i j) w := by
  let L : (Fin N × Fin N → ℂ) →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ :=
    { toFun := soParam
      map_add' := fun a b => by ext i j; simp [soParam]; ring
      map_smul' := fun c a => by ext i j; simp [soParam]; ring }
  let Lc := LinearMap.toContinuousLinearMap L
  let E : Matrix (Fin N) (Fin N) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  have hLc : ∀ w, Lc w = soParam w := fun w => rfl
  have hu : IsUnit (1 - Lc w) := by
    rw [hLc, isUnit_iff_isUnit_det]; exact hw
  have h1 : AnalyticAt ℂ (fun w => Ring.inverse (1 - Lc w)) w :=
    (analyticAt_inverse (𝕜 := ℂ) hu.unit).comp_of_eq
      (analyticAt_const.sub (Lc.analyticAt w)) (by simp)
  have h2 : AnalyticAt ℂ (fun w => (1 : Matrix (Fin N) (Fin N) ℂ) + Lc w) w :=
    analyticAt_const.add (Lc.analyticAt w)
  have h3 := h1.mul h2
  have : (fun w => rotCay w i j) = fun w => E (Ring.inverse (1 - Lc w) * (1 + Lc w)) := by
    funext w
    simp only [rotCay, hLc, nonsing_inv_eq_ringInverse]
    rfl
  rw [this]
  exact (E.analyticAt _).comp h3

theorem continuous_soParam : Continuous (soParam : (Fin N × Fin N → ℂ) → Matrix (Fin N) (Fin N) ℂ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [soParam, Matrix.of_apply]
  fun_prop

theorem eventually_isUnit_det_zero :
    ∀ᶠ w in 𝓝 (0 : Fin N × Fin N → ℂ), IsUnit (1 - soParam w).det ∧ IsUnit (1 + soParam w).det := by
  have h0 : soParam (0 : Fin N × Fin N → ℂ) = 0 := by ext i j; simp [soParam]
  have c1 : Continuous fun w : Fin N × Fin N → ℂ => (1 - soParam w).det :=
    Continuous.matrix_det (continuous_const.sub continuous_soParam)
  have c2 : Continuous fun w : Fin N × Fin N → ℂ => (1 + soParam w).det :=
    Continuous.matrix_det (continuous_const.add continuous_soParam)
  have e1 : ∀ᶠ w in 𝓝 (0 : Fin N × Fin N → ℂ), (1 - soParam w).det ≠ 0 :=
    c1.continuousAt.eventually_ne (by simp [h0])
  have e2 : ∀ᶠ w in 𝓝 (0 : Fin N × Fin N → ℂ), (1 + soParam w).det ≠ 0 :=
    c2.continuousAt.eventually_ne (by simp [h0])
  filter_upwards [e1, e2] with w h1 h2
  exact ⟨isUnit_iff_ne_zero.2 h1, isUnit_iff_ne_zero.2 h2⟩

theorem rotCay_isRot {w : Fin N × Fin N → ℂ} (hw : ∀ i, (w i).im = 0)
    (h1 : IsUnit (1 - soParam w).det) (h2 : IsUnit (1 + soParam w).det) : IsRot (rotCay w) := by
  set X := soParam w with hX
  have hXT : X.transpose = -X := soParam_transpose w
  have hXC : Xᴴ = -X := soParam_conjTranspose_of_real hw
  set A : Matrix (Fin N) (Fin N) ℂ := 1 - X with hA
  set B : Matrix (Fin N) (Fin N) ℂ := 1 + X with hB
  have hAT : A.transpose = B := by rw [hA, hB, transpose_sub, transpose_one, hXT, sub_neg_eq_add]
  have hBT : B.transpose = A := by rw [hA, hB, transpose_add, transpose_one, hXT, sub_eq_add_neg]
  have hAC : Aᴴ = B := by rw [hA, hB, conjTranspose_sub, conjTranspose_one, hXC, sub_neg_eq_add]
  have hBC : Bᴴ = A := by rw [hA, hB, conjTranspose_add, conjTranspose_one, hXC, sub_eq_add_neg]
  have hAB : A * B = B * A := by rw [hA, hB]; noncomm_ring
  have hinvc : B⁻¹ * A⁻¹ = A⁻¹ * B⁻¹ := by
    rw [← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, hAB]
  have hAu : A * A⁻¹ = 1 := mul_nonsing_inv _ h1
  have hBu : B * B⁻¹ = 1 := mul_nonsing_inv _ h2
  have hAu' : A⁻¹ * A = 1 := nonsing_inv_mul _ h1
  have hBu' : B⁻¹ * B = 1 := nonsing_inv_mul _ h2
  have hRT : (rotCay w).transpose = A * B⁻¹ := by
    unfold rotCay
    rw [← hA, ← hB, transpose_mul, hBT, transpose_nonsing_inv, hAT]
  have hRC : (rotCay w)ᴴ = A * B⁻¹ := by
    unfold rotCay
    rw [← hA, ← hB, conjTranspose_mul, hBC, conjTranspose_nonsing_inv, hAC]
  refine ⟨?_, ?_⟩
  · rw [hRT]
    unfold rotCay
    rw [← hA, ← hB]
    calc A * B⁻¹ * (A⁻¹ * B) = A * (B⁻¹ * A⁻¹) * B := by simp only [Matrix.mul_assoc]
      _ = A * (A⁻¹ * B⁻¹) * B := by rw [hinvc]
      _ = (A * A⁻¹) * (B⁻¹ * B) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAu, hBu', Matrix.one_mul]
  · intro i j
    have := congrFun (congrFun (hRC.trans hRT.symm) j) i
    simp only [conjTranspose_apply, transpose_apply] at this
    exact Complex.conj_eq_iff_im.1 this

end Cayley


section CayPath

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

open Matrix NormedSpace

theorem rotCay_smul_soCoord {S : Matrix (Fin N) (Fin N) ℂ} (hS : S.transpose = -S) (s : ℝ) :
    rotCay ((s : ℂ) • soCoord S) = RotFrames.cayMat S (s : ℂ) := by
  unfold rotCay RotFrames.cayMat
  rw [soParam_smul, soParam_soCoord hS]

/-- **Invariance along the Cayley path `R = Q · cay(S)`.**  As `rotE_eq_of_exp_path`, with the
path `s ↦ cay(sS)`, `cay(sS) = (1 - sS)⁻¹ (1 + sS)`, in place of `exp(sA)`; `S` is complex
antisymmetric with `1 - sS` invertible for `s ∈ [0, 1]`.  The neighbourhood `hD` of the start point
is relative to a set `Z` that contains all the rotated pairs. -/
theorem rotE_eq_of_cay_path_within (F : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (D : Set (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N))
    (hF : AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => F p.1 p.2) D)
    (hreal : ∀ Q : Matrix (Fin N) (Fin N) ℂ, IsRot Q → ∀ Ψ h, (Ψ, h) ∈ D →
      (Def6.rotField Q Ψ, Def6.rotField Q h) ∈ D →
      F (Def6.rotField Q Ψ) (Def6.rotField Q h) = F Ψ h)
    {Q S : Matrix (Fin N) (Fin N) ℂ} (hQ : IsRot Q) (hS : S.transpose = -S)
    (hunit : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → IsUnit (1 - (s : ℂ) • S).det)
    (Z : Set (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N))
    {Ψ h : Fld d L N₁ m₁ k N} (hD : D ∈ 𝓝[Z] (Ψ, h))
    (hZ : ∀ R : Matrix (Fin N) (Fin N) ℂ, (Def6.rotField R Ψ, Def6.rotField R h) ∈ Z)
    (hpath : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (Def6.rotField (RotFrames.cayMat S (s : ℂ)) Ψ,
        Def6.rotField (RotFrames.cayMat S (s : ℂ)) h) ∈ D)
    (hend : (Def6.rotField (Q * RotFrames.cayMat S 1) Ψ,
      Def6.rotField (Q * RotFrames.cayMat S 1) h) ∈ D) :
    F (Def6.rotField (Q * RotFrames.cayMat S 1) Ψ) (Def6.rotField (Q * RotFrames.cayMat S 1) h) =
      F Ψ h := by
  have hseg : ∀ w ∈ segment ℝ (0 : Fin N × Fin N → ℂ) (soCoord S), ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      w = (s : ℂ) • soCoord S := fun w hw => by
    obtain ⟨s, h0, h1, rfl⟩ := mem_segment_zero hw
    exact ⟨s, h0, h1, by simp [Complex.coe_smul]⟩
  have h1 := eq_of_rotation_family_within F D hF hreal rotCay rotCay_zero Z hD (fun w => hZ _)
    (w₁ := soCoord S)
    (fun w hw i j => by
      obtain ⟨s, h0, h1, rfl⟩ := hseg w hw
      refine analyticAt_rotCay ?_ i j
      rw [soParam_smul, soParam_soCoord hS]; exact hunit s h0 h1)
    (by
      filter_upwards [eventually_isUnit_det_zero (N := N)] with w hw hwr
      exact rotCay_isRot hwr hw.1 hw.2)
    (fun w hw => by
      obtain ⟨s, h0, h1, rfl⟩ := hseg w hw
      rw [rotCay_smul_soCoord hS]
      exact hpath s h0 h1)
  have e1 : rotCay (soCoord S) = RotFrames.cayMat S 1 := by
    simpa using rotCay_smul_soCoord hS 1
  rw [e1] at h1
  have hp1 : (Def6.rotField (RotFrames.cayMat S 1) Ψ, Def6.rotField (RotFrames.cayMat S 1) h) ∈ D := by
    simpa using hpath 1 zero_le_one le_rfl
  rw [rotField_mul, rotField_mul] at hend ⊢
  rw [hreal Q hQ _ _ hp1 hend, h1]


/-- **Invariance along the Cayley path `R = Q · cay(S)`.**  As `rotE_eq_of_cay_path_within`, with the
neighbourhood of the start point in the whole space. -/
theorem rotE_eq_of_cay_path (F : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (D : Set (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N))
    (hF : AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => F p.1 p.2) D)
    (hreal : ∀ Q : Matrix (Fin N) (Fin N) ℂ, IsRot Q → ∀ Ψ h, (Ψ, h) ∈ D →
      (Def6.rotField Q Ψ, Def6.rotField Q h) ∈ D →
      F (Def6.rotField Q Ψ) (Def6.rotField Q h) = F Ψ h)
    {Q S : Matrix (Fin N) (Fin N) ℂ} (hQ : IsRot Q) (hS : S.transpose = -S)
    (hunit : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → IsUnit (1 - (s : ℂ) • S).det)
    {Ψ h : Fld d L N₁ m₁ k N} (hD : D ∈ 𝓝 (Ψ, h))
    (hpath : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (Def6.rotField (RotFrames.cayMat S (s : ℂ)) Ψ,
        Def6.rotField (RotFrames.cayMat S (s : ℂ)) h) ∈ D)
    (hend : (Def6.rotField (Q * RotFrames.cayMat S 1) Ψ,
      Def6.rotField (Q * RotFrames.cayMat S 1) h) ∈ D) :
    F (Def6.rotField (Q * RotFrames.cayMat S 1) Ψ) (Def6.rotField (Q * RotFrames.cayMat S 1) h) =
      F Ψ h :=
  rotE_eq_of_cay_path_within F D hF hreal hQ hS hunit Set.univ (by rwa [nhdsWithin_univ])
    (fun _ => Set.mem_univ _) hpath hend

end CayPath

section NearVec

open Balaban.Multiscale Matrix

variable {N : ℕ}

theorem vn_mulVec_le_of_entry {A : Matrix (Fin N) (Fin N) ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ i j, ‖A i j‖ ≤ B) (x : Fin N → ℂ) : vn (A *ᵥ x) ≤ N * B * vn x := by
  have hrow : ∀ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ N * B ^ 2 * vn x ^ 2 := by
    intro i
    have h1 : ‖(A *ᵥ x) i‖ ≤ vn (A i) * vn x := by
      have := norm_dot_le (A i) x
      simpa [Matrix.mulVec, dotProduct] using this
    have h2 : vn (A i) ^ 2 ≤ N * B ^ 2 := by
      rw [vn_sq]
      calc ∑ j, ‖A i j‖ ^ 2 ≤ ∑ _j : Fin N, B ^ 2 :=
            Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hA i j) 2
        _ = N * B ^ 2 := by simp
    calc ‖(A *ᵥ x) i‖ ^ 2 ≤ (vn (A i) * vn x) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = vn (A i) ^ 2 * vn x ^ 2 := by ring
      _ ≤ N * B ^ 2 * vn x ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have hsq : vn (A *ᵥ x) ^ 2 ≤ (N * B * vn x) ^ 2 := by
    rw [vn_sq]
    calc ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ ∑ _i : Fin N, (N * B ^ 2 * vn x ^ 2) :=
          Finset.sum_le_sum fun i _ => hrow i
      _ = (N * B * vn x) ^ 2 := by simp; ring
  exact le_of_sq_le_sq hsq (by have := vn_nonneg x; positivity)

theorem vn_le_add_of_nsq {a b c : Fin N → ℂ} (h : ∑ i, ‖a i‖ ^ 2 ≤ ∑ i, ‖b i‖ ^ 2 + ∑ i, ‖c i‖ ^ 2) :
    vn a ≤ vn b + vn c := by
  rw [← vn_sq, ← vn_sq, ← vn_sq] at h
  refine le_of_sq_le_sq ?_ (add_nonneg (vn_nonneg b) (vn_nonneg c))
  nlinarith [vn_nonneg b, vn_nonneg c]

theorem vn_le_of_nsq {a c : Fin N → ℂ} (h : ∑ i, ‖a i‖ ^ 2 ≤ ∑ i, ‖c i‖ ^ 2) : vn a ≤ vn c := by
  rw [← vn_sq, ← vn_sq] at h
  exact le_of_sq_le_sq h (vn_nonneg c)

theorem vn_star_fun (v : Fin N → ℂ) : vn (fun i => star (v i)) = vn v := by
  have h : ∑ i, ‖star (v i)‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by simp
  have := congrArg Real.sqrt h
  rw [← vn_eq_sqrt, ← vn_eq_sqrt] at this
  exact this


/-- `Mᴴ e - e = star (Mᵀ e - e)` for a real vector `e`. -/
theorem conjTranspose_mulVec_sub {M : Matrix (Fin N) (Fin N) ℂ} {e : Fin N → ℂ}
    (he : ∀ i, star (e i) = e i) :
    Mᴴ *ᵥ e - e = fun i => star ((M.transpose *ᵥ e - e) i) := by
  funext i
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, conjTranspose_apply, transpose_apply,
    star_sub, star_sum, star_mul', he]

/-- **The path bound.**  Let `M` be complex orthogonal with entries bounded by `B`, `e` a real
vector with `‖M e - e‖ ≤ η₀`, and `v` a vector with `‖v - e‖ ≤ ρ` and `‖M v - e‖ ≤ ρ'`.  Then every
point `cay(sS) v`, `s ∈ [0, 1]`, of the path of the polar decomposition `M = Q · cay(S)` satisfies
`‖cay(sS) v - e‖ ≤ ρ + ρ' + (1 + 2 N B) η₀`. -/
theorem exists_cay_path_near {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.transpose * M = 1) {B : ℝ}
    (hB : 0 ≤ B) (hMb : ∀ i j, ‖M i j‖ ≤ B) {e : Fin N → ℂ} (he : ∀ i, star (e i) = e i)
    {η₀ : ℝ} (hη : vn (M *ᵥ e - e) ≤ η₀) :
    ∃ Q S : Matrix (Fin N) (Fin N) ℂ, IsRot Q ∧ S.transpose = -S ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ 1 → IsUnit (1 - (s : ℂ) • S).det) ∧ M = Q * RotFrames.cayMat S 1 ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ (ρ ρ' : ℝ) (v : Fin N → ℂ), vn (v - e) ≤ ρ →
        vn (M *ᵥ v - e) ≤ ρ' →
        vn (RotFrames.cayMat S (s : ℂ) *ᵥ v - e) ≤ ρ + ρ' + (1 + 2 * (N * B)) * η₀ := by
  obtain ⟨Q, S, hQQ, hQre, hS, hMQ, hmain⟩ := RotFrames.frame_decomp hM
  refine ⟨Q, S, ⟨hQQ, hQre⟩, hS, fun s h0 h1 => (hmain s h0 h1).1, hMQ, ?_⟩
  intro s h0 h1 ρ ρ' v hv hMv
  obtain ⟨-, hE1, hE2⟩ := hmain s h0 h1
  set x : ℝ := N * B with hx
  have hx0 : 0 ≤ x := by positivity
  set R := RotFrames.cayMat S (s : ℂ) with hR
  set η := vn (M *ᵥ e - e) with hη'
  -- the conjugate-transpose bound
  have hMH : ∀ i j, ‖Mᴴ i j‖ ≤ B := fun i j => by
    simpa only [conjTranspose_apply, norm_star] using hMb j i
  have hMT : ∀ i j, ‖M.transpose i j‖ ≤ B := fun i j => hMb j i
  have hP1 : vn (Mᴴ *ᵥ e - e) ≤ x * η := by
    rw [conjTranspose_mulVec_sub he, vn_star_fun]
    have e1 : M.transpose *ᵥ e - e = M.transpose *ᵥ (e - M *ᵥ e) := by
      rw [mulVec_sub, mulVec_mulVec, hM, one_mulVec]
    rw [e1]
    refine (vn_mulVec_le_of_entry hB hMT _).trans ?_
    rw [vn_sub_comm]
  have hP2 : vn ((Mᴴ * M) *ᵥ e - e) ≤ 2 * x * η := by
    have e1 : (Mᴴ * M) *ᵥ e - e = Mᴴ *ᵥ (M *ᵥ e - e) + (Mᴴ *ᵥ e - e) := by
      rw [← mulVec_mulVec, mulVec_sub]; abel
    rw [e1]
    refine (vn_add _ _).trans ?_
    have := vn_mulVec_le_of_entry hB hMH (M *ᵥ e - e)
    nlinarith
  -- assemble
  have hRv : R *ᵥ v - e = R *ᵥ (v - e) + (R *ᵥ e - e) := by
    rw [mulVec_sub]; abel
  have hA : vn (R *ᵥ (v - e)) ≤ vn (v - e) + vn (M *ᵥ (v - e)) :=
    vn_le_add_of_nsq (hE1 (v - e))
  have hMu : vn (M *ᵥ (v - e)) ≤ ρ' + η := by
    have e1 : M *ᵥ (v - e) = (M *ᵥ v - e) - (M *ᵥ e - e) := by
      rw [mulVec_sub]; abel
    rw [e1]
    exact (vn_sub_le_add _ _).trans (by linarith)
  have hC : vn (R *ᵥ e - e) ≤ 2 * x * η := (vn_le_of_nsq (hE2 e)).trans hP2
  rw [hRv]
  refine (vn_add _ _).trans ?_
  nlinarith [vn_nonneg (v - e), mul_le_mul_of_nonneg_left hη (by linarith : (0 : ℝ) ≤ 1 + 2 * x)]


theorem vn_le_sqrt_card_mul {v : Fin N → ℂ} {r : ℝ} (hr : 0 ≤ r) (h : ∀ i, ‖v i‖ ≤ r) :
    vn v ≤ Real.sqrt N * r := by
  have hsq : vn v ^ 2 ≤ (Real.sqrt N * r) ^ 2 := by
    rw [vn_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin N, r ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2
      _ = N * r ^ 2 := by simp
  exact le_of_sq_le_sq hsq (by positivity)

end NearVec

section NearField

open Balaban.Multiscale Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

/-- **Complex invariance for the frames of the renormalization chain.**  Let `F` be analytic on a
set `D` of pairs of fields and invariant under the real orthogonal matrices.  Let `M` be a complex
orthogonal matrix with entries bounded by `B`, `e` a real vector, and let the pairs `(Ψ, h)` and
`(MΨ, Mh)` satisfy, at every site and in every coordinate,
`|Ψ - e| ≤ r`, `|MΨ - e| ≤ r'`, `|h - e| ≤ rh`, `|Mh - e| ≤ rh'`, and `|M e - e| ≤ re`.
Let `D` contain every pair of the class `P` (closed under all matrices) with `|Ψ' - e| ≤ r₁` and
`|h' - e| ≤ r₁h`, where `r₁ ≥ √N (r + r' + (1 + 2 N B) re)` and
`r₁h ≥ √N (rh + rh' + (1 + 2 N B) re)`.  Then `F (MΨ) (Mh) = F Ψ h`.

No closeness of `M` to a real rotation is needed: the path of the polar decomposition
(`exists_cay_path_near`) stays in the ball of radius `r₁` (and `r₁h`).  The neighbourhood `D` of
`(Ψ, h)` is relative to the pairs of the class `P` (the class domain is open only relative to the
layer-constant pairs). -/
theorem rotE_of_near_within (F : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (D : Set (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N))
    (hF : AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => F p.1 p.2) D)
    (hreal : ∀ Q : Matrix (Fin N) (Fin N) ℂ, IsRot Q → ∀ Ψ h, (Ψ, h) ∈ D →
      (Def6.rotField Q Ψ, Def6.rotField Q h) ∈ D →
      F (Def6.rotField Q Ψ) (Def6.rotField Q h) = F Ψ h)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.transpose * M = 1) {B : ℝ} (hB : 0 ≤ B)
    (hMb : ∀ i j, ‖M i j‖ ≤ B) {e : Fin N → ℂ} (he : ∀ i, star (e i) = e i)
    {r r' rh rh' re r₁ r₁h : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (hrh : 0 ≤ rh) (hrh' : 0 ≤ rh')
    (hre : 0 ≤ re) (hMe : ∀ i, ‖(M *ᵥ e) i - e i‖ ≤ re)
    (hr₁ : Real.sqrt N * (r + r' + (1 + 2 * (N * B)) * re) ≤ r₁)
    (hr₁h : Real.sqrt N * (rh + rh' + (1 + 2 * (N * B)) * re) ≤ r₁h)
    (P : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → Prop)
    (hP : ∀ (R : Matrix (Fin N) (Fin N) ℂ) Ψ h, P Ψ h → P (Def6.rotField R Ψ) (Def6.rotField R h))
    (hDm : ∀ Ψ' h', P Ψ' h' → (∀ x i, ‖Ψ' x i - e i‖ ≤ r₁) → (∀ x i, ‖h' x i - e i‖ ≤ r₁h) →
      (Ψ', h') ∈ D)
    {Ψ h : Fld d L N₁ m₁ k N}
    (hDn : D ∈ 𝓝[{p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N | P p.1 p.2}] (Ψ, h)) (hPΨ : P Ψ h)
    (hΨ : ∀ x i, ‖Ψ x i - e i‖ ≤ r) (hh : ∀ x i, ‖h x i - e i‖ ≤ rh)
    (hΨM : ∀ x i, ‖Def6.rotField M Ψ x i - e i‖ ≤ r')
    (hhM : ∀ x i, ‖Def6.rotField M h x i - e i‖ ≤ rh') :
    F (Def6.rotField M Ψ) (Def6.rotField M h) = F Ψ h := by
  have hη : vn (M *ᵥ e - e) ≤ Real.sqrt N * re :=
    vn_le_sqrt_card_mul hre (fun i => hMe i)
  obtain ⟨Q, S, hQ, hS, hunit, hMQ, hpathv⟩ :=
    exists_cay_path_near hM hB hMb he hη
  set x : ℝ := N * B with hx
  have hx0 : 0 ≤ x := by positivity
  have vΨ : ∀ y, vn (Ψ y - e) ≤ Real.sqrt N * r := fun y =>
    vn_le_sqrt_card_mul hr (fun i => hΨ y i)
  have vh : ∀ y, vn (h y - e) ≤ Real.sqrt N * rh := fun y =>
    vn_le_sqrt_card_mul hrh (fun i => hh y i)
  have vΨM : ∀ y, vn (M *ᵥ Ψ y - e) ≤ Real.sqrt N * r' := fun y =>
    vn_le_sqrt_card_mul hr' (fun i => hΨM y i)
  have vhM : ∀ y, vn (M *ᵥ h y - e) ≤ Real.sqrt N * rh' := fun y =>
    vn_le_sqrt_card_mul hrh' (fun i => hhM y i)
  have hpath : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (Def6.rotField (RotFrames.cayMat S (s : ℂ)) Ψ,
        Def6.rotField (RotFrames.cayMat S (s : ℂ)) h) ∈ D := by
    intro s h0 h1
    refine hDm _ _ (hP _ _ _ hPΨ) (fun y i => ?_) (fun y i => ?_)
    · have := hpathv s h0 h1 _ _ (Ψ y) (vΨ y) (vΨM y)
      calc ‖Def6.rotField (RotFrames.cayMat S (s : ℂ)) Ψ y i - e i‖
          = ‖(RotFrames.cayMat S (s : ℂ) *ᵥ Ψ y - e) i‖ := rfl
        _ ≤ vn (RotFrames.cayMat S (s : ℂ) *ᵥ Ψ y - e) := norm_le_vn _ i
        _ ≤ Real.sqrt N * r + Real.sqrt N * r' + (1 + 2 * x) * (Real.sqrt N * re) := this
        _ = Real.sqrt N * (r + r' + (1 + 2 * x) * re) := by ring
        _ ≤ r₁ := hr₁
    · have := hpathv s h0 h1 _ _ (h y) (vh y) (vhM y)
      calc ‖Def6.rotField (RotFrames.cayMat S (s : ℂ)) h y i - e i‖
          = ‖(RotFrames.cayMat S (s : ℂ) *ᵥ h y - e) i‖ := rfl
        _ ≤ vn (RotFrames.cayMat S (s : ℂ) *ᵥ h y - e) := norm_le_vn _ i
        _ ≤ Real.sqrt N * rh + Real.sqrt N * rh' + (1 + 2 * x) * (Real.sqrt N * re) := this
        _ = Real.sqrt N * (rh + rh' + (1 + 2 * x) * re) := by ring
        _ ≤ r₁h := hr₁h
  have hrr : Fin N → r' ≤ r₁ ∧ rh' ≤ r₁h := fun i => by
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i
    have h1 : (1 : ℝ) ≤ Real.sqrt N := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hN
    have hq : 0 ≤ (1 + 2 * x) * re := by positivity
    constructor
    · calc r' ≤ 1 * (r + r' + (1 + 2 * x) * re) := by linarith
        _ ≤ Real.sqrt N * (r + r' + (1 + 2 * x) * re) :=
            mul_le_mul_of_nonneg_right h1 (by linarith)
        _ ≤ r₁ := hr₁
    · calc rh' ≤ 1 * (rh + rh' + (1 + 2 * x) * re) := by linarith
        _ ≤ Real.sqrt N * (rh + rh' + (1 + 2 * x) * re) :=
            mul_le_mul_of_nonneg_right h1 (by linarith)
        _ ≤ r₁h := hr₁h
  have hend : (Def6.rotField (Q * RotFrames.cayMat S 1) Ψ,
      Def6.rotField (Q * RotFrames.cayMat S 1) h) ∈ D := by
    rw [← hMQ]
    exact hDm _ _ (hP _ _ _ hPΨ) (fun y i => (hΨM y i).trans (hrr i).1)
      (fun y i => (hhM y i).trans (hrr i).2)
  have := rotE_eq_of_cay_path_within F D hF hreal hQ hS hunit
    {p | P p.1 p.2} hDn (fun R => hP R Ψ h hPΨ) hpath hend
  rwa [← hMQ] at this


/-- **Complex invariance for the frames of the renormalization chain**, with `D` a neighbourhood
of `(Ψ, h)`; see `rotE_of_near_within`. -/
theorem rotE_of_near (F : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (D : Set (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N))
    (hF : AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => F p.1 p.2) D)
    (hreal : ∀ Q : Matrix (Fin N) (Fin N) ℂ, IsRot Q → ∀ Ψ h, (Ψ, h) ∈ D →
      (Def6.rotField Q Ψ, Def6.rotField Q h) ∈ D →
      F (Def6.rotField Q Ψ) (Def6.rotField Q h) = F Ψ h)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.transpose * M = 1) {B : ℝ} (hB : 0 ≤ B)
    (hMb : ∀ i j, ‖M i j‖ ≤ B) {e : Fin N → ℂ} (he : ∀ i, star (e i) = e i)
    {r r' rh rh' re r₁ r₁h : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (hrh : 0 ≤ rh) (hrh' : 0 ≤ rh')
    (hre : 0 ≤ re) (hMe : ∀ i, ‖(M *ᵥ e) i - e i‖ ≤ re)
    (hr₁ : Real.sqrt N * (r + r' + (1 + 2 * (N * B)) * re) ≤ r₁)
    (hr₁h : Real.sqrt N * (rh + rh' + (1 + 2 * (N * B)) * re) ≤ r₁h)
    (P : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → Prop)
    (hP : ∀ (R : Matrix (Fin N) (Fin N) ℂ) Ψ h, P Ψ h → P (Def6.rotField R Ψ) (Def6.rotField R h))
    (hDm : ∀ Ψ' h', P Ψ' h' → (∀ x i, ‖Ψ' x i - e i‖ ≤ r₁) → (∀ x i, ‖h' x i - e i‖ ≤ r₁h) →
      (Ψ', h') ∈ D)
    {Ψ h : Fld d L N₁ m₁ k N} (hDn : D ∈ 𝓝 (Ψ, h)) (hPΨ : P Ψ h)
    (hΨ : ∀ x i, ‖Ψ x i - e i‖ ≤ r) (hh : ∀ x i, ‖h x i - e i‖ ≤ rh)
    (hΨM : ∀ x i, ‖Def6.rotField M Ψ x i - e i‖ ≤ r')
    (hhM : ∀ x i, ‖Def6.rotField M h x i - e i‖ ≤ rh') :
    F (Def6.rotField M Ψ) (Def6.rotField M h) = F Ψ h :=
  rotE_of_near_within F D hF hreal hM hB hMb he hr hr' hrh hrh' hre hMe hr₁ hr₁h P hP hDm
    (mem_nhdsWithin_of_mem_nhds hDn) hPΨ hΨ hh hΨM hhM

end NearField


section Clauses

open Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The restricted complex invariance `CRotE` at the matrices of the frame bridges.**  For a
member of the term clauses (`SFTermClauses`, real `O(N)` invariance and analyticity on the domain)
the energy terms are invariant under every complex orthogonal `M` with entries bounded by `B` that
relates two pairs `(Ψ, h)`, `(MΨ, Mh)` lying close to a real constant `e` (the radii are those of
`rotE_of_near`), provided the domain contains the pairs of the class `P'` (closed under all
matrices: block-constant fields with a constant `h`) within the radii `r₁`, `r₁h` of `e`, and is a
neighbourhood of `(Ψ, h)`. -/
theorem SFTermClauses.rotE_of_near_within {P : Consts} {Dom : FieldDom d L N₁ m₁ k N ϱ}
    {Tm : Terms d L N₁ m₁ k N ϱ} (hT : SFTermClauses P Dom Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y X}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.transpose * M = 1) {B : ℝ} (hB : 0 ≤ B)
    (hMb : ∀ i j, ‖M i j‖ ≤ B) {e : Fin N → ℂ} (he : ∀ i, star (e i) = e i)
    {r r' rh rh' re r₁ r₁h : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (hrh : 0 ≤ rh) (hrh' : 0 ≤ rh')
    (hre : 0 ≤ re) (hMe : ∀ i, ‖(M *ᵥ e) i - e i‖ ≤ re)
    (hr₁ : Real.sqrt N * (r + r' + (1 + 2 * (N * B)) * re) ≤ r₁)
    (hr₁h : Real.sqrt N * (rh + rh' + (1 + 2 * (N * B)) * re) ≤ r₁h)
    (P' : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → Prop)
    (hP : ∀ (R : Matrix (Fin N) (Fin N) ℂ) Ψ h, P' Ψ h →
      P' (Def6.rotField R Ψ) (Def6.rotField R h))
    (hDm : ∀ Ψ' h', P' Ψ' h' → (∀ x i, ‖Ψ' x i - e i‖ ≤ r₁) → (∀ x i, ‖h' x i - e i‖ ≤ r₁h) →
      Dom.dom j (Tm.gs j X) Ψ' h')
    {Ψ h : Fld d L N₁ m₁ k N}
    (hDn : {p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N | Dom.dom j (Tm.gs j X) p.1 p.2} ∈
      𝓝[{p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N | P' p.1 p.2}] (Ψ, h))
    (hPΨ : P' Ψ h) (hΨ : ∀ x i, ‖Ψ x i - e i‖ ≤ r) (hh : ∀ x i, ‖h x i - e i‖ ≤ rh)
    (hΨM : ∀ x i, ‖Def6.rotField M Ψ x i - e i‖ ≤ r')
    (hhM : ∀ x i, ‖Def6.rotField M h x i - e i‖ ≤ rh') :
    Tm.E j y X (Def6.rotField M Ψ) (Def6.rotField M h) = Tm.E j y X Ψ h :=
  Balaban.SmallField.Def6v2.rotE_of_near_within (fun Ψ h => Tm.E j y X Ψ h)
    {p | Dom.dom j (Tm.gs j X) p.1 p.2}
    (hT.analyticE j hj1 hjk y X hX hy)
    (fun Q hQ Ψ h h1 h2 => hT.rotE j hj1 hjk y X hX hy Q hQ Ψ h h1 h2) hM hB hMb he hr hr' hrh
    hrh' hre hMe hr₁ hr₁h P' hP hDm hDn hPΨ hΨ hh hΨM hhM


theorem SFTermClauses.rotE_of_near {P : Consts} {Dom : FieldDom d L N₁ m₁ k N ϱ}
    {Tm : Terms d L N₁ m₁ k N ϱ} (hT : SFTermClauses P Dom Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y X}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.transpose * M = 1) {B : ℝ} (hB : 0 ≤ B)
    (hMb : ∀ i j, ‖M i j‖ ≤ B) {e : Fin N → ℂ} (he : ∀ i, star (e i) = e i)
    {r r' rh rh' re r₁ r₁h : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (hrh : 0 ≤ rh) (hrh' : 0 ≤ rh')
    (hre : 0 ≤ re) (hMe : ∀ i, ‖(M *ᵥ e) i - e i‖ ≤ re)
    (hr₁ : Real.sqrt N * (r + r' + (1 + 2 * (N * B)) * re) ≤ r₁)
    (hr₁h : Real.sqrt N * (rh + rh' + (1 + 2 * (N * B)) * re) ≤ r₁h)
    (P' : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → Prop)
    (hP : ∀ (R : Matrix (Fin N) (Fin N) ℂ) Ψ h, P' Ψ h →
      P' (Def6.rotField R Ψ) (Def6.rotField R h))
    (hDm : ∀ Ψ' h', P' Ψ' h' → (∀ x i, ‖Ψ' x i - e i‖ ≤ r₁) → (∀ x i, ‖h' x i - e i‖ ≤ r₁h) →
      Dom.dom j (Tm.gs j X) Ψ' h')
    {Ψ h : Fld d L N₁ m₁ k N}
    (hDn : {p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N | Dom.dom j (Tm.gs j X) p.1 p.2} ∈
      𝓝 (Ψ, h))
    (hPΨ : P' Ψ h) (hΨ : ∀ x i, ‖Ψ x i - e i‖ ≤ r) (hh : ∀ x i, ‖h x i - e i‖ ≤ rh)
    (hΨM : ∀ x i, ‖Def6.rotField M Ψ x i - e i‖ ≤ r')
    (hhM : ∀ x i, ‖Def6.rotField M h x i - e i‖ ≤ rh') :
    Tm.E j y X (Def6.rotField M Ψ) (Def6.rotField M h) = Tm.E j y X Ψ h :=
  hT.rotE_of_near_within hj1 hjk hX hy hM hB hMb he hr hr' hrh hrh' hre hMe hr₁ hr₁h P' hP hDm
    (mem_nhdsWithin_of_mem_nhds hDn) hPΨ hΨ hh hΨM hhM

end Clauses

section Boost

open Matrix

/-! ### The frames are not near real rotations: a concrete configuration

For `N = 3`, `e = e₃`: the boost below is complex orthogonal, fixes `e₃`, maps the point
`e₃ + ρ (1, i, 0)` of the ball of radius `ρ` around `e₃` to the point `e₃ + (ρ/2) (1, i, 0)` of the
same ball, and is at distance `≥ 3/4` from every real matrix (the same holds for `cosh t`, `sinh t`
up to the entry bound of the frames, `cosh t ≤ 40`).  So two points of a ball of any radius can be
related by a matrix that is not near a real rotation; a near-real bound `M = Q exp(A)`,
`‖A‖ ≲ ε`, is false for the frames of `Def6BridgeLift` (`LiftCtx.witness`) as landed. -/

/-- The complex boost in the plane of the first two coordinates (`cosh t = 5/4`, `sinh t = 3/4`,
`e^t = 2`), fixing the third coordinate. -/
noncomputable def boost3 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![5 / 4, (3 / 4) * Complex.I, 0; -((3 / 4) * Complex.I), 5 / 4, 0; 0, 0, 1]

theorem boost3_orth : boost3.transpose * boost3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boost3, Matrix.mul_apply, Fin.sum_univ_three] <;> ring_nf <;>
    simp [Complex.I_sq] <;> norm_num

/-- The boost maps the point `e₃ + ρ (1, i, 0)` of the ball of radius `ρ` around `e₃` to the point
`e₃ + (ρ/2) (1, i, 0)` of the same ball, and fixes `e₃`. -/
theorem boost3_pair (ρ : ℂ) :
    boost3 *ᵥ ![ρ, ρ * Complex.I, 1] = ![ρ / 2, ρ / 2 * Complex.I, 1] := by
  ext i
  fin_cases i
  · simp only [boost3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    simp
    linear_combination (3 / 4 * ρ) * Complex.I_sq
  · simp only [boost3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    simp
    ring
  · simp [boost3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem boost3_fix : boost3 *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
  ext i
  fin_cases i <;> simp [boost3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The boost is at distance at least `3/4` (in an entry) from every real matrix. -/
theorem boost3_far_from_real {Q : Matrix (Fin 3) (Fin 3) ℂ} (hQ : ∀ i j, (Q i j).im = 0) :
    (3 : ℝ) / 4 ≤ ‖boost3 0 1 - Q 0 1‖ := by
  have h := Complex.abs_im_le_norm (boost3 0 1 - Q 0 1)
  have : (boost3 0 1 - Q 0 1).im = 3 / 4 := by simp [boost3, hQ 0 1]
  rw [this] at h
  simpa [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)] using h


end Boost

end Balaban.SmallField.Def6v2
