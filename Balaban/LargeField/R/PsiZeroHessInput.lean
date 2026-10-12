/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroHessCoerc
public import Balaban.LargeField.R.PsiZeroExists
public import Balaban.Localization.DecoupledBackground

/-!
# The Hessian field of `PsiZeroInput` under the geometry (1.1) (PSIZERO-HESS §5, row 6)

`psiZero_hess_of_geometry`: for `BgHyp`, `d, L ≥ 3`, `k ≥ 1`, a proper box `Z₀ = box b₀ w` with
`1 ≤ w_i ≤ D`, `D + 2 ≤ N₀ L^{k-k}`, `OverTop G (Z₀ ∪ shellOut Z₀)`, and a block field `ψ` of the tube
`Ψ̃(𝔹_k; η)` with `η ≤ η_hess`, the second derivative of the variational function at `ψ↾Z₀` satisfies
`⟨δψ, Δ δψ⟩ ≥ c_k ‖δψ‖²` with the explicit constant `c_k = ½ γ_LF c_D L^{k(d-2)}` (`γ_LF = 1/(28 d)`,
`c_D = 4/(D+1)²`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section HessInput

/-- `g_D = ½ γ_LF c_D`: the Gaussian constant of a box of diameter `≤ D`. -/
noncomputable def gaussConst (d D : ℕ) : ℝ := gamma0 d / 2 * cDirichlet D

theorem gaussConst_pos (d D : ℕ) (hd : 0 < d) : 0 < gaussConst d D := by
  unfold gaussConst gamma0 cDirichlet
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

/-- The Hessian constant `c_k = ½ γ_LF c_D L^{k(d-2)}` of the unnormalized variational function. -/
noncomputable def hessConst (d L k D : ℕ) : ℝ := gaussConst d D * (L : ℝ) ^ (k * (d - 2))

/-- The tube radius on which the multiplier term is absorbed. -/
noncomputable def etaHess (d L N D : ℕ) [NeZero L] : ℝ :=
  gaussConst d D / (8 * (gaussConst d D + 1) * (bgK1 d L N + 1))

theorem etaHess_pos (d L N D : ℕ) [NeZero L] (hd : 0 < d) : 0 < etaHess d L N D := by
  have := gaussConst_pos d D hd
  have := bgK1_pos (d := d) (L := L) (N := N)
  unfold etaHess; positivity

/-- The multiplier term is absorbed when `η ≤ etaHess`. -/
theorem absorb_cond (d L N D : ℕ) [NeZero L] (hd : 0 < d) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ etaHess d L N D) :
    8 * (bgK1 d L N * η) * (gaussConst d D + 1) ≤ gaussConst d D := by
  have hg := gaussConst_pos d D hd
  have hB := bgK1_pos (d := d) (L := L) (N := N)
  unfold etaHess at hη
  have h1 : η * (8 * (gaussConst d D + 1) * (bgK1 d L N + 1)) ≤ gaussConst d D :=
    (le_div_iff₀ (by positivity)).1 hη
  nlinarith [mul_nonneg hη0 (by positivity : 0 ≤ 8 * (gaussConst d D + 1))]

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}

theorem coe_boxFinset (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ) :
    ((boxFinset (L := L) (N₀ := N₀) (k := k) b0 w : Finset _) : Set (Torus d (N₀ * L ^ (k - k)))) =
      box b0 w := by
  simp [boxFinset]

variable [NeZero N]

theorem psiZero_derivs_core {D : ℕ} (H : BgHyp d L k ϱ a 0) (hk : 1 ≤ k)
    (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
    (Z : Finset (Torus d (N₀ * L ^ (k - k)))) (hZ : (Z : Set (Torus d (N₀ * L ^ (k - k)))) = box b0 w)
    (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D)
    (hm : D + 2 ≤ N₀ * L ^ (k - k))
    (hΩ : OverTop G ((box b0 w : Set (Torus d (N₀ * L ^ (k - k)))) ∪
      shellOut (box b0 w : Set (Torus d (N₀ * L ^ (k - k)))))) {η : ℝ} (hη : 0 < η)
    (hη0 : η ≤ bgC0 d L N) (hη1 : η ≤ bgC1 d L N) (hηh : η ≤ etaHess d L N D)
    {ψ : BlockField d L N₀ k N} (ht : TubeOn G Set.univ η ψ) (v : SuppSpace Z N) :
    fderiv ℝ (effOn G a Z ψ) (restrictSupp Z ψ) v =
        (firstVar a (dataR G ψ) (topTangent G v) (bgField G a 0 (dataR G ψ))).re ∧
      hessConst d L k D * ‖v‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ (effOn G a Z ψ)) (restrictSupp Z ψ) v v := by
  have hd : 0 < d := by have := H.hd; omega
  have hD1 : 1 ≤ D := (hw1 ⟨0, hd⟩).trans (hwD _)
  have hL2 : 2 ≤ L := by have := H.hL; omega
  have hϱ : 2 * (d : ℝ) * L ≤ ϱ := by
    refine le_trans ?_ H.hϱ
    unfold bgR0
    refine le_trans ?_ (le_max_left _ _)
    have : (0 : ℝ) ≤ (d : ℝ) * L := by positivity
    nlinarith
  have hd3 := H.hd
  have hΩZ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k)))) := by
    intro x hx
    exact hΩ x (Or.inl (by rw [← hZ]; exact hx))
  have hm1 : D + 1 ≤ N₀ * L ^ (k - k) := by omega
  have hn3 : 3 ≤ N₀ * L ^ (k - k) := by omega
  have hDdom : InDomainR G 0 η (dataR G ψ) := inDomainR_of_tube G hη ht
  have hUnion : InUnionDomainR G (bgC1 d L N) 0 (dataR G ψ) := ⟨η, hη, hη1, hDdom⟩
  obtain ⟨-, -, -, -, hbd⟩ := theorem71 H hUnion
  have hα := (hbd η hη hη1 hDdom).alpha
  have hθ : 0 ≤ bgK1 d L N * η := mul_nonneg (bgK1_pos (d := d) (L := L) (N := N)).le hη.le
  have hc := absorb_cond d L N D hd hη.le hηh
  have key := effOn_derivs (a := a) (Z := Z) H hk hη hη0 hη1 hΩZ ht v
    (gaussConst d D * (L : ℝ) ^ (k * (d - 2)) * ‖v‖ ^ 2 / 2) (fun t τ hτ => by
      have h := quad_ge_half (a := a) (G := G) (by omega : 2 ≤ d) hL2 hϱ hk H.weights b0 w Z hZ hwD
        hm1 hn3 hΩ v t hτ hα hθ hc
      have e : gaussConst d D * (L : ℝ) ^ (k * (d - 2)) * ‖v‖ ^ 2 / 2 * t ^ 2 =
          gamma0 d / 2 * cDirichlet D * (L : ℝ) ^ (k * (d - 2)) * (t ^ 2 * ‖v‖ ^ 2) / 2 := by
        unfold gaussConst; ring
      rw [e]
      exact h)
  refine ⟨key.1, ?_⟩
  unfold hessConst
  linarith [key.2]

/-- **Row 6: the Hessian field under the geometry (1.1).** -/
theorem psiZero_hess_of_geometry {D : ℕ} (H : BgHyp d L k ϱ a 0) (hk : 1 ≤ k)
    (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ) (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D)
    (hm : D + 2 ≤ N₀ * L ^ (k - k))
    (hΩ : OverTop G ((box b0 w : Set (Torus d (N₀ * L ^ (k - k)))) ∪
      shellOut (box b0 w : Set (Torus d (N₀ * L ^ (k - k)))))) {η : ℝ} (hη : 0 < η)
    (hη0 : η ≤ bgC0 d L N) (hη1 : η ≤ bgC1 d L N) (hηh : η ≤ etaHess d L N D)
    {ψ : BlockField d L N₀ k N} (ht : TubeOn G Set.univ η ψ)
    (v : SuppSpace (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) N) :
    hessConst d L k D * ‖v‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (effOn G a (boxFinset b0 w) ψ)) (restrictSupp (boxFinset b0 w) ψ) v v :=
  (psiZero_derivs_core H hk b0 w (boxFinset b0 w) (coe_boxFinset b0 w) hw1 hwD hm hΩ hη hη0 hη1 hηh ht v).2

end HessInput

end Balaban.LargeField
