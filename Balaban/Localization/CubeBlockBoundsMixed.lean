/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.CutPointwiseWallMax
public import Balaban.Localization.Decoupled2
public import Balaban.Localization.DecoupledCube
public import Balaban.Localization.NC3
public import Balaban.Localization.BoxCube

/-!
# `CubeBlockBounds` at a mixed physical wall (VMOD-9 Theorem 1.1, (1.5))

`Dec2.cubeBlockBounds_mixed`: for an operator generating set `H` with `OpSetting H a ν`, an
admissible potential and a cube index `q` of a common cover (a cube index of a generating set `F` of
the same torus, `N₁ > 5`) whose interaction cube is `BlockAligned H`, the cut solution of the cube
operator `H_z(α)` of `H` satisfies the three-field estimate `CubeBlockBounds` with the constant
`K_c = max {K_p, e^{ε₀ d} (1 + 4 K_p)}` (`mixedKc d L`, `K_p = cutKp d L`), whatever the position of the
physical Dirichlet wall of `Ω₁(H)` relative to the cube.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}

/-- **The constant `K_c = max {K_p, e^{ε₀ d} (1 + 4 K_p)}` of VMOD-9 (1.5).** -/
noncomputable def mixedKc (d L : ℕ) : ℝ :=
  max (cutKp d L) (Real.exp (agmonRate d * d) * (1 + 4 * cutKp d L))

theorem cutKp_nonneg (hd : 3 ≤ d) : 0 ≤ cutKp d L := by
  unfold cutKp
  have := cutK1_nonneg (L := L) hd
  positivity

omit [NeZero L] in
/-- The separation `2 d log L ≤ ε₀/16 (ϱ - 1)` gives the two consequences used by Lemma P. -/
theorem sep_consequences (hd : 3 ≤ d) (hL : 3 ≤ L) {ϱ : ℝ}
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1)) :
    1 ≤ ϱ ∧ (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) := by
  have hd0 : 0 < d := by omega
  have hε := agmonRate_pos hd0
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hlog : 0 < Real.log L := Real.log_pos (by linarith)
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 0 < 2 * (d : ℝ) * Real.log L := by positivity
  have h2 : 0 < ϱ - 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  refine ⟨by linarith, ?_⟩
  have h3 : (L : ℝ) ^ d = Real.exp (d * Real.log L) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log (by linarith)]
    simp
  rw [h3]
  apply Real.exp_le_exp.2
  nlinarith

/-- **VMOD-9 Theorem 1.1 (the `CubeBlockBounds` field of `CoverBase.nc` at a mixed wall).** -/
theorem cubeBlockBounds_mixed (hN : 5 < N₁) (F : GeneratingSet d L (N₁ * L ^ m₁) K ϱ')
    {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} (S : OpSetting H a ν)
    {α : H.Ω 1 → ℂ} (hα : AdmPot H α) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx F)
    (hba : BlockAligned H (intBox q)) : CubeBlockBounds H a ν α q (mixedKc d L) := by
  classical
  have hd := S.hd
  have hL := S.hL
  have hd0 : 0 < d := by omega
  obtain ⟨hϱ, hsepL⟩ := sep_consequences hd hL S.sep
  obtain ⟨⟨hm1, hmK⟩, -, -⟩ := (mem_cubeIdx F).1 hq
  have hbox := box_eq_cubeSet hN hq
  have hLpos : 0 < L ^ (q.1 + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have : NeZero (5 * L ^ (q.1 + m₁)) := ⟨by positivity⟩
  have hSℓ : 5 * L ^ (q.1 + m₁) < (N₁ * L ^ m₁) * L ^ K := by
    have := torusSide_ge (L := L) (m₁ := m₁) hN hmK
    omega
  have hΛ : BlockAligned H (cubeSet ((N₁ * L ^ m₁) * L ^ K) (5 * L ^ (q.1 + m₁)) (boxCorner q)) := by
    rw [← hbox]; exact hba
  have hcut : CutAligned H (cubeCut H (intBox q)) := cubeCut_aligned H hba
  have hαa : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (H.spacing x) ^ 2) := hα
  refine ⟨fun {j'} {y'} hj'1 hj'k hy' hy'b f hsupp {Mf} hMf0 hMf => ?_⟩
  set Kp := cutKp d L with hKp
  have hKp0 : 0 ≤ Kp := cutKp_nonneg hd
  have hF0 : 0 ≤ (L : ℝ) ^ (2 * j') * Mf := by positivity
  have hy'b' : y' ∈ cubeSet ((N₁ * L ^ m₁) * L ^ K) (5 * L ^ (q.1 + m₁)) (boxCorner q) := by
    rw [← hbox]; exact hy'b
  -- the pointwise estimate (1.4)
  have hU : ∀ {x : CTorus d L N₁ m₁ K}, x ∈ H.Ω 1 →
      cutU H (cubeCut H (intBox q))
        (zeroExt (H.Ω 1) ((cutOperator H a ν (cubeCut H (intBox q)) α)⁻¹ *ᵥ f)) x ≤
      Kp * decay (agmonRate d / 2) (H.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf) := by
    intro x hx
    have h := cut_prop48_cube hd hL hϱ hsepL (G := H) (a := a) (ν := ν) S.mass S.massLe S.weights
      hαa (5 * L ^ (q.1 + m₁)) (boxCorner q) hSℓ hΛ hj'1 hj'k hy' hy'b' hsupp hMf0 hMf hx
    rw [hbox]
    by_cases hinf : H.pathDist x y' = ⊤
    · have := h.2 hinf
      rw [this]; unfold decay; simp [hinf]
    · have := h.1 hinf
      refine this.trans (le_of_eq ?_)
      unfold decay
      simp [hinf, hKp]
  have hKpc : Kp ≤ mixedKc d L := le_max_left _ _
  have hdec := fun x => decay_nonneg (agmonRate d / 2) (H.pathDist x y')
  refine ⟨?_, ?_, ?_⟩
  · -- value
    intro x hx hxb
    have h1 := (norm_le_cutU H _ _ x).trans (hU hx)
    refine h1.trans ?_
    have : Kp * decay (agmonRate d / 2) (H.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf) ≤
        mixedKc d L * decay (agmonRate d / 2) (H.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf) := by
      have := hdec x
      gcongr
    exact this
  · -- forward gradient
    intro x hx hxb hxe μ
    have hnc : (x, μ) ∉ cubeCut H (intBox q) := by
      rw [mem_cubeCut]
      rintro (⟨-, -, h3⟩ | ⟨h1, -, -⟩)
      · exact h3 (hxe μ)
      · exact h1 hxb
    have h1 : H.spacing x * ‖zeroExt (H.Ω 1) ((cutOperator H a ν (cubeCut H (intBox q)) α)⁻¹ *ᵥ f)
        (x + Pi.single μ 1) - zeroExt (H.Ω 1)
          ((cutOperator H a ν (cubeCut H (intBox q)) α)⁻¹ *ᵥ f) x‖ ≤
        cutU H (cubeCut H (intBox q))
          (zeroExt (H.Ω 1) ((cutOperator H a ν (cubeCut H (intBox q)) α)⁻¹ *ᵥ f)) x := by
      unfold cutU
      have hsp := (spacing_pos H (x := x)).le
      have hnn : ∀ μ' : Fin d, 0 ≤ (if (x, μ') ∈ cubeCut H (intBox q) then (0 : ℝ) else
          ‖zeroExt (H.Ω 1) ((cutOperator H a ν (cubeCut H (intBox q)) α)⁻¹ *ᵥ f)
            (x + Pi.single μ' 1) - zeroExt (H.Ω 1)
              ((cutOperator H a ν (cubeCut H (intBox q)) α)⁻¹ *ᵥ f) x‖) :=
        fun μ' => by split_ifs <;> positivity
      have h3 := Finset.single_le_sum (fun μ' _ => hnn μ') (Finset.mem_univ μ)
      simp only [hnc, ↓reduceIte] at h3
      have := mul_le_mul_of_nonneg_left h3 hsp
      have h4 := norm_nonneg (zeroExt (H.Ω 1)
        ((cutOperator H a ν (cubeCut H (intBox q)) α)⁻¹ *ᵥ f) x)
      linarith
    refine h1.trans ((hU hx).trans ?_)
    have := hdec x
    gcongr
  · -- Laplacian
    intro x hx hxb hxe
    have hnc : NoCutAt (cubeCut H (intBox q)) x :=
      noCutAt_cubeCut (G := H) (intBox q) hxb fun μ => hxe μ
    obtain ⟨hj1, hjk, hxl⟩ := H.layerIndex_spec hx
    have hlap := Balaban.Reflection.laplacian_cut_bound hcut hd0 S.mass S.massLe S.weights α hαa hj'1
      hj'k hy' f hsupp hMf0 hMf hx hnc (V := Kp * ((L : ℝ) ^ (2 * j') * Mf)) (by positivity)
      (by
        intro q' hq'
        have hq'Ω : q' ∈ H.Ω 1 :=
          H.layer_subset hj1 hjk ((H.mem_layer_iff hj1 hjk hq').2 hxl)
        have hq'b : q' ∈ intBox q := (hba _ hj1 hjk x q' hxl hq').1 hxb
        refine ((norm_le_cutU H _ _ q').trans (hU hq'Ω)).trans (le_of_eq ?_)
        ring)
    refine hlap.trans ?_
    have hE : Real.exp (agmonRate d * d) * ((L : ℝ) ^ (2 * j') * Mf + 4 * (Kp * ((L : ℝ) ^ (2 * j') * Mf))) *
        decay (agmonRate d / 2) (H.pathDist x y') ≤
        mixedKc d L * decay (agmonRate d / 2) (H.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf) := by
      have h5 : Real.exp (agmonRate d * d) * (1 + 4 * Kp) ≤ mixedKc d L := le_max_right _ _
      have := hdec x
      calc _ = (Real.exp (agmonRate d * d) * (1 + 4 * Kp)) * decay (agmonRate d / 2) (H.pathDist x y') *
            ((L : ℝ) ^ (2 * j') * Mf) := by ring
        _ ≤ _ := by gcongr
    exact hE

end Balaban.Localization.Dec2
