/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CancelIdentity
public import Balaban.LargeField.R.DenominatorSqueeze
public import Balaban.LargeField.R.PsiZeroHessInput
public import Balaban.LargeField.R.PsiZeroHessLine
public import Balaban.LargeField.R.PsiZeroHessRef
public import Balaban.LargeField.R.PsiZeroAnalyticAction
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The first variation at `ψ⁰_k` (P7 (2.52); LF-RECONSTRUCTION Lemmas III.3.3 and III.6.3, first step)

Convention: the massless reference of P7 (mass `0` in `BgHyp`).

* `firstVar_basis`: the first variation `firstVar` of the effective action at a real block field `ψ` in the
  direction of the basis perturbation at `(z₀, i₀)`, `z₀` a block of `Z`, is
  `(a_k / L^{2k}) · L^{kd} · Re r(z₀, i₀)`, `r = ψ - Q_k φ_k(ψ)` the residual of Definition III.6.1.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.ActionConv

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.LargeField Finset

section Basic

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}

/-- The data `lift_k ψ̃⁰_k` with a real constant `h` is real. -/
theorem psiZeroData_isReal (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ) :
    (psiZeroData G ψ0 h).IsReal := by
  intro x i
  constructor
  · by_cases hx : x ∈ dataSites G
    · simp [psiZeroData, liftSingle_Ψ G _ _ hx]
    · simp [(psiZeroData G ψ0 h).Ψ_zero x hx]
  · by_cases hx : x ∈ G.Ω 1
    · simp [psiZeroData, liftSingle_h G _ _ hx]
    · simp [(psiZeroData G ψ0 h).h_zero x hx]

/-- `psiZeroData` and `dataR` have the same field `Ψ` (they differ only in the constant `h`). -/
theorem psiZeroData_Ψ_eq_dataR (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    (ψ : BlockField d L N₀ k N) (hψ : ∀ z i, ψ0 ⟨k, z⟩ i = ψ z i) :
    (psiZeroData G ψ0 h).Ψ = (dataR G ψ).Ψ := by
  funext x
  by_cases hx : x ∈ dataSites G
  · funext i
    simp [psiZeroData, dataR, dataC, liftSingle_Ψ G _ _ hx, hψ]
  · rw [(psiZeroData G ψ0 h).Ψ_zero x hx, (dataR G ψ).Ψ_zero x hx]

/-- At mass `0` the background field only depends on the field `Ψ` of (real) data. -/
theorem bgField_congr_Ψ {D D' : BgData G N} (hD : D.IsReal) (hD' : D'.IsReal) (hΨ : D.Ψ = D'.Ψ) :
    bgField G a 0 D = bgField G a 0 D' := by
  have hact : ∀ φ, action G a 0 D φ = action G a 0 D' φ := by
    intro φ; simp [action, hΨ]
  have hiff : ∀ φ, IsMinimizer G a 0 D φ ↔ IsMinimizer G a 0 D' φ := by
    intro φ
    unfold IsMinimizer
    simp only [hact, hD, hD', true_and]
  have e : IsMinimizer G a 0 D = IsMinimizer G a 0 D' := funext fun φ => propext (hiff φ)
  classical
  have key : ∀ P Q : (↥(G.Ω 1) × Fin N → ℂ) → Prop, P = Q →
      (if H : ∃! φ, P φ then H.exists.choose else (0 : ↥(G.Ω 1) × Fin N → ℂ)) =
        if H : ∃! φ, Q φ then H.exists.choose else 0 := by
    rintro P Q rfl; rfl
  exact key _ _ e

variable (G a) in
/-- The residual `r = ψ - Q_k φ_k(ψ)` of Definition III.6.1 for a real block field `ψ`. -/
noncomputable def resField (ψ : BlockField d L N₀ k N) (z : Torus d (N₀ * L ^ (k - k))) (i : Fin N) : ℂ :=
  (ψ z i : ℂ) - kAvg (fun y j => svec G (bgField G a 0 (dataR G ψ)) y j) z i

theorem rBlk_eq_resField (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    (ψ : BlockField d L N₀ k N) (hψ : ∀ z i, ψ0 ⟨k, z⟩ i = ψ z i) (hR : (dataR G ψ).IsReal)
    (z : Torus d (N₀ * L ^ (k - k))) (i : Fin N) :
    rBlk G a ψ0 h z i = resField G a ψ z i := by
  unfold rBlk resField phiZero
  rw [bgField_congr_Ψ (psiZeroData_isReal ψ0 h) hR (psiZeroData_Ψ_eq_dataR ψ0 h ψ hψ), hψ z i]

theorem sub_blockAvg_eq_resField (ψ : BlockField d L N₀ k N) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) (hp : G.layerIndex x = k) (i : Fin N) :
    (dataR G ψ).Ψ x i - blockAvg G (bgField G a 0 (dataR G ψ)) x i =
      resField G a ψ (jBlock d L N₀ k k x) i := by
  have hd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
  unfold resField kAvg blockAvg
  rw [dataR_Ψ G ψ hd i, hp, blk_eq_fib]
  unfold blockVol liftR
  push_cast
  rfl

theorem resField_im (ψ : BlockField d L N₀ k N)
    (hφ : ∀ p, (bgField G a 0 (dataR G ψ) p).im = 0) (z : Torus d (N₀ * L ^ (k - k))) (i : Fin N) :
    (resField G a ψ z i).im = 0 := by
  have hs : ∀ y j, (svec G (bgField G a 0 (dataR G ψ)) y j).im = 0 := by
    intro y j
    by_cases hy : y ∈ G.Ω 1
    · rw [svec_of_mem G _ ⟨y, hy⟩ j]; exact hφ _
    · rw [svec_of_not_mem G _ hy j]; simp
  simp [resField, kAvg, Complex.mul_im, Complex.im_sum, hs]

end Basic

section FirstVar

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}
  {Z : Finset (Torus d (N₀ * L ^ (k - k)))}

/-- **The first variation of the effective action along a perturbation supported over `Z`**: for a block
field `ψ` and `v` supported in `Z` (a set of blocks lying over `Ω_k`), the real part of `firstVar` is
`(a_k / L^{2k}) · L^{kd} · ∑_{z, i} ṽ(z, i) Re r(z, i)`, `r = resField` (`blockVol d L k = L^{kd}`). -/
theorem firstVar_re (hk : 1 ≤ k) (hΩ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k)))))
    (v : SuppSpace Z N) (ψ : BlockField d L N₀ k N) :
    (firstVar a (dataR G ψ) (topTangent G v) (bgField G a 0 (dataR G ψ))).re =
      a k / ((L : ℝ) ^ k) ^ 2 * blockVol d L k *
        ∑ z ∈ Z, ∑ i, extSupp Z v z i * (resField G a ψ z i).re := by
  classical
  set H : Torus d (N₀ * L ^ (k - k)) → ℝ := fun z =>
    a k / ((L : ℝ) ^ k) ^ 2 * ∑ i, extSupp Z v z i * (resField G a ψ z i).re with hH
  have hterm : ∀ x : Torus d (N₀ * L ^ k), x ∈ G.Ω 1 →
      (((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
        ∑ i, (topTangent G v).Ψ x i *
          ((dataR G ψ).Ψ x i - blockAvg G (bgField G a 0 (dataR G ψ)) x i)).re =
        if jBlock d L N₀ k k x ∈ Z then H (jBlock d L N₀ k k x) else 0 := by
    intro x hx
    have hds : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    by_cases hz : jBlock d L N₀ k k x ∈ Z
    · obtain ⟨-, hlay, -⟩ := (topLift_block_count hΩ hk hz).2 x rfl
      have e1 : ∀ i, (topTangent G v).Ψ x i *
          ((dataR G ψ).Ψ x i - blockAvg G (bgField G a 0 (dataR G ψ)) x i) =
          ((extSupp Z v (jBlock d L N₀ k k x) i : ℝ) : ℂ) *
            resField G a ψ (jBlock d L N₀ k k x) i := fun i => by
        rw [topTangent_Ψ v hds i, sub_blockAvg_eq_resField ψ hx hlay i]
      simp only [e1]
      rw [hlay]
      simp only [hz, ↓reduceIte]
      rw [Complex.re_ofReal_mul, Complex.re_sum]
      simp only [Complex.re_ofReal_mul]
      rfl
    · have e0 : ∀ i, (topTangent G v).Ψ x i = 0 := fun i => by
        rw [topTangent_Ψ v hds i]; simp [extSupp, hz]
      simp [e0, hz]
  have hsub : ∀ x : Torus d (N₀ * L ^ k), x ∉ G.Ω 1 →
      (if jBlock d L N₀ k k x ∈ Z then H (jBlock d L N₀ k k x) else 0) = 0 := by
    intro x hx
    by_cases hz : jBlock d L N₀ k k x ∈ Z
    · exact absurd (G.Ω_antitone le_rfl hk (by omega) (hΩ x hz)) hx
    · simp [hz]
  unfold firstVar
  rw [Complex.re_sum]
  calc _ = ∑ x : G.Ω 1, (if jBlock d L N₀ k k (x : Torus d (N₀ * L ^ k)) ∈ Z then
          H (jBlock d L N₀ k k (x : Torus d (N₀ * L ^ k))) else 0) :=
        Finset.sum_congr rfl fun x _ => hterm x x.2
    _ = ∑ x ∈ G.Ω 1, (if jBlock d L N₀ k k x ∈ Z then H (jBlock d L N₀ k k x) else 0) :=
        Finset.sum_coe_sort (G.Ω 1) (fun x => if jBlock d L N₀ k k x ∈ Z then
          H (jBlock d L N₀ k k x) else 0)
    _ = ∑ x : Torus d (N₀ * L ^ k), (if jBlock d L N₀ k k x ∈ Z then H (jBlock d L N₀ k k x) else 0) :=
        Finset.sum_subset (Finset.subset_univ _) fun x _ hx => hsub x hx
    _ = ((L : ℝ) ^ k) ^ d * ∑ z ∈ Z, H z := sum_fiber_top hk hΩ H
    _ = _ := by
        simp only [hH, ← Finset.mul_sum]
        unfold blockVol
        ring

/-- **T1 (`firstVar_basis`)**: the first variation in the direction of the basis perturbation at
`(z₀, i₀)`, `z₀ ∈ Z`, is `(a_k / L^{2k}) · L^{kd} · Re r(z₀, i₀)` (the constant is
`a k / (L ^ k) ^ 2 * blockVol d L k`, `blockVol d L k = (L ^ k) ^ d`; the effective action here is the
unnormalized `effAction`, so no further factor enters). -/
theorem firstVar_basis (hk : 1 ≤ k) (hΩ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k)))))
    (ψ : BlockField d L N₀ k N) {z0 : Torus d (N₀ * L ^ (k - k))} (hz0 : z0 ∈ Z) (i0 : Fin N) :
    (firstVar a (dataR G ψ)
        (topTangent G (EuclideanSpace.single (⟨z0, hz0⟩, i0) (1 : ℝ) : SuppSpace Z N))
        (bgField G a 0 (dataR G ψ))).re =
      a k / ((L : ℝ) ^ k) ^ 2 * blockVol d L k * (resField G a ψ z0 i0).re := by
  classical
  rw [firstVar_re hk hΩ]
  congr 1
  have hext : ∀ z i, extSupp Z (EuclideanSpace.single (⟨z0, hz0⟩, i0) (1 : ℝ) : SuppSpace Z N) z i =
      if z = z0 ∧ i = i0 then 1 else 0 := by
    intro z i
    by_cases hz : z ∈ Z
    · simp [extSupp, hz, Prod.ext_iff, Subtype.ext_iff]
    · have hn : ¬ (z = z0 ∧ i = i0) := fun h => hz (h.1 ▸ hz0)
      simp [extSupp, hz, hn]
  simp only [hext]
  simp [ite_and, hz0]

end FirstVar

end Balaban.LargeField.ActionConv
