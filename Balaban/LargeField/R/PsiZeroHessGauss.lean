/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroHessPair
public import Balaban.LargeField.R.PsiZeroHessGrad
public import Balaban.LargeField.R.ZeroDomainCoercive
public import Balaban.Fluctuation.CubeActionReal
public import Balaban.Multiscale.ConstraintKernel
public import Balaban.LargeField.R.SmallFactorAction
public import Balaban.LargeField.R.PsiZeroTube

/-!
# The Gaussian lower bound for the action of a top-layer datum (PSIZERO-HESS §5, rows 5-6)

`action_ge_actionG`: for a datum `D` vanishing off `Ω₁` with `h̃ = 0`, the real action `A(D, τ)` dominates the
multiscale action `A_G(Ω₁; ψ, φ̂)` of LF-1 (the bonds from `Ω₁` to its complement count `½` instead of `¼`).
Together with `lf1_gradient`, `top_pairSum_dirichlet` and `dirichlet_box_coercive` this gives
`A(tJv, τ) ≥ ½ γ_LF c_D L^{k(d-2)} t² ‖v‖²` (`action_top_ge`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

section Gauss

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}

/-- The bond-difference sum of the complex image is the real bond term. -/
theorem bond_sum_cast (D : BgData G N) (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin N))
    (hout : ∀ x, x ∉ G.Ω 1 → ∀ i, D.Ψ x i = ((φ x i : ℝ) : ℂ)) (x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    ∑ i, (barField G D.Ψ (toFieldC G φ) (x + Pi.single μ 1) i - barField G D.Ψ (toFieldC G φ) x i) *
      (barField G D.Ψ (toFieldC G φ) (x + Pi.single μ 1) i - barField G D.Ψ (toFieldC G φ) x i) =
      ((bondTerm φ μ x : ℝ) : ℂ) := by
  unfold bondTerm
  have e1 : ∀ i, barField G D.Ψ (toFieldC G φ) (x + Pi.single μ 1) i -
      barField G D.Ψ (toFieldC G φ) x i =
      (((φ (x + Pi.single μ 1) - φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) := by
    intro i
    rw [barField_toFieldC D φ hout, barField_toFieldC D φ hout, ← Complex.ofReal_sub]
    rfl
  simp only [e1]
  exact sum_sq_complex _

open Classical in
/-- **The action dominates the multiscale action `A_G(Ω₁; ψ, φ)`** (mass `0`, `h = 0`). -/
theorem action_ge_actionG (hd : 2 ≤ d) (D : BgData G N) (hD : D.IsReal)
    (hDh : ∀ x i, D.h x i = 0) (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin N))
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin N))
    (hout : ∀ x, x ∉ G.Ω 1 → ∀ i, D.Ψ x i = ((φ x i : ℝ) : ℂ))
    (hΨ : ∀ n, 1 ≤ n → n ≤ k → ∀ x ∈ G.layer n, ∀ i,
      D.Ψ x i = ((ψ n (blkMap d L N₀ k n x) i : ℝ) : ℂ)) :
    actionG G a 0 0 (G.Ω 1) ψ φ ≤ action G a 0 D (toFieldC G φ) := by
  have hstar := cubeActionStar_eq_actionG (a := a) (G := G) hd (G.Ω 1) subset_rfl
    (fun n hn1 hnk x hx hxl y hy => blk_subset_Ω G hn1 hnk hxl hy) 0 D φ ψ 0 hout hΨ
    (fun x _ i => by rw [hDh]; simp)
  have hφim : ∀ (x : G.Ω 1) i, (toFieldC G φ (x, i)).im = 0 := fun x i => by simp [toFieldC]
  have hcast := action_cast (a := a) (ν := 0) D hD hφim
  set R : ℝ := 1 / 2 * ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        (1 - ((if x ∈ G.Ω 1 then 1 else 0) + (if x + Pi.single μ 1 ∈ G.Ω 1 then 1 else 0)) / 2) *
          bondTerm φ μ x else 0) with hR
  have hR0 : 0 ≤ R := by
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun μ _ => ?_)
    by_cases hc : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1
    · simp only [hc, ↓reduceIte]
      refine mul_nonneg ?_ (bondTerm_nonneg φ μ x)
      split_ifs <;> norm_num
    · simp only [hc, ↓reduceIte]; exact le_rfl
  have hbond : ∀ x μ, (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
      ∑ i, (barField G D.Ψ (toFieldC G φ) (x + Pi.single μ 1) i - barField G D.Ψ (toFieldC G φ) x i) *
        (barField G D.Ψ (toFieldC G φ) (x + Pi.single μ 1) i - barField G D.Ψ (toFieldC G φ) x i)
      else 0) = ((if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then bondTerm φ μ x else 0 : ℝ) : ℂ) := by
    intro x μ
    split_ifs
    · exact bond_sum_cast D φ hout x μ
    · simp
  have key : ((action G a 0 D (toFieldC G φ) : ℝ) : ℂ) =
      ((actionG G a 0 0 (G.Ω 1) ψ φ + 1 / 4 * starBondE (G.Ω 1) φ + R : ℝ) : ℂ) := by
    rw [hcast]
    have hsplit : ∀ (x : Torus d (N₀ * L ^ k)) (μ : Fin d),
        (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then ((bondTerm φ μ x : ℝ) : ℂ) else 0) =
          (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
            starWeight (G.Ω 1) x μ * ((bondTerm φ μ x : ℝ) : ℂ) else 0) +
          ((if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
            (1 - ((if x ∈ G.Ω 1 then 1 else 0) + (if x + Pi.single μ 1 ∈ G.Ω 1 then 1 else 0)) / 2) *
              bondTerm φ μ x else 0 : ℝ) : ℂ) := by
      intro x μ
      by_cases h1 : x ∈ G.Ω 1 <;> by_cases h2 : x + Pi.single μ 1 ∈ G.Ω 1 <;>
        simp [h1, h2, starWeight] <;> ring
    have h2 : actionC G a 0 D (toFieldC G φ) =
        cubeActionStar G a 0 (G.Ω 1) D.Ψ D.h (toFieldC G φ) + ((R : ℝ) : ℂ) := by
      unfold actionC cubeActionStar cubeBlockTerm cubeBondStar cubeMassTerm
      simp only [bond_sum_cast D φ hout, Complex.ofReal_zero, zero_div, zero_mul, add_zero,
        Finset.coe_mem, ↓reduceIte]
      rw [hR]
      push_cast
      simp only [hsplit, Finset.sum_add_distrib, mul_add]
      ring
    rw [h2, hstar]
    push_cast
    ring
  have key' := Complex.ofReal_injective key
  have := starBondE_nonneg (G.Ω 1) φ
  linarith

/-- The multiscale block field of a top-layer datum: `t ṽ` at scale `k`, `0` at the other scales. -/
noncomputable def topPsi (Z : Finset (Torus d (N₀ * L ^ (k - k)))) (v : SuppSpace Z N) (t : ℝ) :
    (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin N) := fun m y =>
  if h : m = k then t • extSupp Z v (cast (congrArg (fun j => Torus d (N₀ * L ^ (k - j))) h) y) else 0

theorem topPsi_self (Z : Finset (Torus d (N₀ * L ^ (k - k)))) (v : SuppSpace Z N) (t : ℝ)
    (y : Torus d (N₀ * L ^ (k - k))) : topPsi (L := L) (N₀ := N₀) Z v t k y = t • extSupp Z v y := by
  simp [topPsi]

theorem topPsi_of_ne (Z : Finset (Torus d (N₀ * L ^ (k - k)))) (v : SuppSpace Z N) (t : ℝ) {m : ℕ}
    (hm : m ≠ k) (y : Blk d L N₀ k m) : topPsi (L := L) (N₀ := N₀) Z v t m y = 0 := by
  simp [topPsi, hm]

/-- The real field `τ` as a function on the torus, zero off `Ω₁`. -/
noncomputable def realExt (G : GeneratingSet d L N₀ k ϱ) (τ : G.Ω 1 × Fin N → ℂ) :
    Site d L N₀ k → EuclideanSpace ℝ (Fin N) := fun x =>
  eu (fun i => if h : x ∈ G.Ω 1 then (τ (⟨x, h⟩, i)).re else 0)

theorem toFieldC_realExt (G : GeneratingSet d L N₀ k ϱ) {τ : G.Ω 1 × Fin N → ℂ}
    (hτ : ∀ (x : G.Ω 1) i, (τ (x, i)).im = 0) : toFieldC G (realExt G τ) = τ := by
  funext p
  obtain ⟨x, i⟩ := p
  simp only [toFieldC, realExt, eu, x.2, dite_true]
  exact Complex.ext (by simp) (by simp [hτ x i])

/-- **The Gaussian lower bound (rows 5-6).**  For a perturbation `v` supported in a box `Z` with
`OverTop G (Z ∪ shellOut Z)` and every real field `τ`, the action of the datum `t Jv` satisfies
`A(tJv, τ) ≥ ½ γ_LF c_D L^{k(d-2)} t² ‖v‖²`. -/
theorem action_top_ge {D₀ : ℕ} (hd : 2 ≤ d) (hL : 2 ≤ L) (hϱ : 2 * (d : ℝ) * L ≤ ϱ) (hk : 1 ≤ k)
    (ha : IsAdmissibleWeights k a) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
    (Z : Finset (Torus d (N₀ * L ^ (k - k)))) (hZ : (Z : Set (Torus d (N₀ * L ^ (k - k)))) = box b0 w)
    (hwD : ∀ i, w i ≤ D₀) (hm : D₀ + 1 ≤ N₀ * L ^ (k - k)) (hn3 : 3 ≤ N₀ * L ^ (k - k))
    (hΩ : OverTop G ((box b0 w : Set (Torus d (N₀ * L ^ (k - k)))) ∪
      shellOut (box b0 w : Set (Torus d (N₀ * L ^ (k - k))))))
    (v : SuppSpace Z N) (t : ℝ)
    {τ : G.Ω 1 × Fin N → ℂ} (hτ : ∀ (x : G.Ω 1) i, (τ (x, i)).im = 0) :
    gamma0 d / 2 * cDirichlet D₀ * (L : ℝ) ^ (k * (d - 2)) * (t ^ 2 * ‖v‖ ^ 2) ≤
      action G a 0 ((bgZero G N).lineAt (topTangent G v) (t : ℂ)) τ := by
  rw [← hZ] at hΩ
  have hΩZ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k)))) := fun x hx => hΩ x (Or.inl hx)
  set E := topTangent G v with hE
  set D := (bgZero G N).lineAt E (t : ℂ) with hD
  have hDΨ : ∀ x, D.Ψ x = (t : ℂ) • E.Ψ x := fun x => by simp [hD, BgData.lineAt, bgZero]
  have hEo : ∀ x, x ∉ G.Ω 1 → E.Ψ x = 0 := fun x hx => topTangent_zero_off hΩZ hk v hx
  have hDR : D.IsReal := isReal_lineAt isReal_bgZero (topTangent_isReal v) t
  have hDh : ∀ x i, D.h x i = 0 := fun x i => by simp [hD, BgData.lineAt, bgZero, hE, topTangent_h]
  have hψ : ∀ n, 1 ≤ n → n ≤ k → ∀ x ∈ G.layer n, ∀ i,
      D.Ψ x i = ((topPsi Z v t n (blkMap d L N₀ k n x) i : ℝ) : ℂ) := by
    intro n hn1 hnk x hx i
    have hx1 : x ∈ G.Ω 1 := G.layer_subset hn1 hnk hx
    have hds : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx1)
    rw [hDΨ]
    by_cases hnk' : n = k
    · subst hnk'
      rw [topPsi_self]
      simp only [Pi.smul_apply, smul_eq_mul, PiLp.smul_apply]
      rw [topTangent_Ψ v hds i]
      simp [blkMap, jBlock]
    · rw [topPsi_of_ne Z v t hnk']
      have hn : n + 1 ≤ k := by omega
      have hz : E.Ψ x i = 0 := by
        rw [hE, topTangent_Ψ v hds i]
        have : jBlock d L N₀ k k x ∉ Z := fun h => by
          have hxk : x ∈ G.Ω k := hΩZ x h
          exact (G.mem_layer.1 hx).2 (G.Ω_antitone (by omega) hn (by omega) hxk)
        simp [extSupp, this]
      simp [hz]
  have hout : ∀ x, x ∉ G.Ω 1 → ∀ i, D.Ψ x i = ((realExt G τ x i : ℝ) : ℂ) := by
    intro x hx i
    rw [hDΨ, hEo x hx]
    simp [realExt, eu, hx]
  have hge := action_ge_actionG (a := a) hd D hDR hDh (realExt G τ) (topPsi Z v t) hout hψ
  rw [toFieldC_realExt G hτ] at hge
  refine le_trans ?_ hge
  -- LF-1
  have hlf := lf1_gradient G hd hL hϱ ha (μ := 0) le_rfl (0 : EuclideanSpace ℝ (Fin N)) (G.Ω 1)
    (fun n hn1 hnk => layer_isBlockUnion G hn1 hnk) (topPsi Z v t) (realExt G τ)
  have hg : 0 ≤ gamma0 d := by unfold gamma0; positivity
  have hnn : ∀ n ∈ Finset.range (k + 1), 0 ≤ ((L : ℝ) ^ (n * (d - 2)) / 2) *
      pairSumT (tBlocks d L N₀ k n (lam G n ∩ G.Ω 1)) (psiFull (realExt G τ) (topPsi Z v t) n) :=
    fun n _ => mul_nonneg (by positivity) (pairSumT_nonneg _ _)
  have hcr : 0 ≤ ∑ n ∈ Finset.range k, ((L : ℝ) ^ ((n + 1) * (d - 2)) / 2) *
      crossSumP G n (G.Ω 1) (psiFull (realExt G τ) (topPsi Z v t)) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (crossSumP_nonneg _ _ _ _)
  have h1 := Finset.single_le_sum hnn (Finset.mem_range.2 (Nat.lt_succ_self k))
  rw [psiFull_of_pos _ _ hk] at h1
  have htop : t ^ 2 * dirichletForm Z v ≤ pairSumT (tBlocks d L N₀ k k (lam G k ∩ G.Ω 1))
      (topPsi Z v t k) := by
    have := top_pairSum_dirichlet (G := G) hk hn3 hΩ v t
    simpa [funext (topPsi_self (L := L) (N₀ := N₀) Z v t)] using this
  have hcoer : cDirichlet D₀ * ‖v‖ ^ 2 ≤ dirichletForm Z v := by
    have := dirichlet_box_coercive (V := EuclideanSpace ℝ (Fin N)) (by omega : 0 < d) b0 w hwD hm
      (extSupp Z v) (fun x hx => by
        have hx' : x ∉ Z := fun h => hx (hZ ▸ Finset.mem_coe.2 h)
        simp [extSupp, hx'])
    rw [sum_sq_extSupp] at this
    exact this
  have hs : 0 ≤ (L : ℝ) ^ (k * (d - 2)) / 2 := by positivity
  calc gamma0 d / 2 * cDirichlet D₀ * (L : ℝ) ^ (k * (d - 2)) * (t ^ 2 * ‖v‖ ^ 2)
      = gamma0 d * ((L : ℝ) ^ (k * (d - 2)) / 2 * (t ^ 2 * (cDirichlet D₀ * ‖v‖ ^ 2))) := by ring
    _ ≤ gamma0 d * ((L : ℝ) ^ (k * (d - 2)) / 2 *
          pairSumT (tBlocks d L N₀ k k (lam G k ∩ G.Ω 1)) (topPsi Z v t k)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hs) hg
        refine le_trans ?_ htop
        exact mul_le_mul_of_nonneg_left hcoer (sq_nonneg t)
    _ ≤ _ := by
        refine le_trans (mul_le_mul_of_nonneg_left h1 hg) (le_trans ?_ hlf)
        nlinarith [mul_nonneg hg hcr]

end Gauss

end Balaban.LargeField
