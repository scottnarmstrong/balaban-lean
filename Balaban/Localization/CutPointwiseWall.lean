/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PointwiseScale
public import Balaban.Localization.CubeFoldPoisson
public import Balaban.Multiscale.CutPointwise
public import Balaban.Multiscale.Locality

/-!
# The pointwise cut estimate at a mixed physical wall: scale arithmetic (VMOD-9 §3, (3.1))

`cut_scale_abs`: the geometric proof of `PointwiseScale.scale_abs` for a layer `j`, a source scale
`j'` and a separation, without the bundled `PtSetting` (and so without the uncut operator).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Finset Matrix

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **VMOD-9 (3.1).** The scale mismatch `bd^{j'}` of the source block is absorbed by the layer
separation. -/
theorem cut_scale_abs {G : GeneratingSet d L N₀ k ϱ} (hd : 0 < d) (hϱ : 1 ≤ ϱ)
    (hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1))) {j j' : ℕ} (hj1 : 1 ≤ j)
    (hj'k : j' ≤ k) {y' : Torus d (N₀ * L ^ k)} (hy' : y' ∈ G.layer j')
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ENNReal.ofReal t ≤ G.pathDist x y') :
    ∃ t₂ : ℝ, t ≤ t₂ ∧ ENNReal.ofReal t₂ ≤ G.pathDist x y' ∧
      bd d L ^ j' * Real.exp (-(agmonRate d * t₂)) ≤
        bd d L ^ j * bd d L * Real.exp (-(agmonRate d / 2 * t)) := by
  have hε0 := agmonRate_pos hd
  have hb1 := one_le_bd (d := d) (L := L)
  have hb0 : 0 < bd d L := by linarith
  rcases le_or_gt j' j with h | h
  · refine ⟨t, le_rfl, ht, ?_⟩
    have h1 : bd d L ^ j' ≤ bd d L ^ j := pow_le_pow_right₀ hb1 h
    have h2 : Real.exp (-(agmonRate d * t)) ≤ Real.exp (-(agmonRate d / 2 * t)) := by
      apply Real.exp_le_exp.2
      nlinarith
    calc bd d L ^ j' * Real.exp (-(agmonRate d * t)) ≤ bd d L ^ j *
          Real.exp (-(agmonRate d / 2 * t)) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ ≤ _ := by
          rw [mul_assoc, mul_comm (bd d L) _, ← mul_assoc]
          have : 0 ≤ bd d L ^ j * Real.exp (-(agmonRate d / 2 * t)) := by positivity
          nlinarith
  · have hsep0 := G.pathDist_separation_le hϱ hj1 hj'k hx (G.mem_layer.1 hy').1
    set s0 : ℝ := (ϱ - 1) * ((j' - j - 1 : ℕ) : ℝ) with hs0
    have hs00 : 0 ≤ s0 := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    refine ⟨max t s0, le_max_left _ _, ?_, ?_⟩
    · rcases le_total t s0 with h' | h'
      · rw [max_eq_right h']; exact hsep0
      · rw [max_eq_left h']; exact ht
    · set m := j' - j with hm
      have hjm : j' = j + m := by omega
      have hexp : Real.exp (-(agmonRate d * max t s0)) ≤
          Real.exp (-(agmonRate d / 2 * t)) * Real.exp (-(agmonRate d / 2 * s0)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        have h1 : t ≤ max t s0 := le_max_left _ _
        have h2 : s0 ≤ max t s0 := le_max_right _ _
        nlinarith
      have hc : bd d L ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) :=
        (bd_le d).trans hsep
      have habs := pow_mul_exp_le' hb1 hc m
      have e : agmonRate d / 2 * s0 = agmonRate d / 2 * (ϱ - 1) * ((m - 1 : ℕ) : ℝ) := by
        rw [hs0]; ring
      rw [e] at hexp
      calc bd d L ^ j' * Real.exp (-(agmonRate d * max t s0))
          ≤ bd d L ^ (j + m) * (Real.exp (-(agmonRate d / 2 * t)) *
            Real.exp (-(agmonRate d / 2 * (ϱ - 1) * ((m - 1 : ℕ) : ℝ)))) := by
            rw [hjm]; exact mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = bd d L ^ j * Real.exp (-(agmonRate d / 2 * t)) *
            (bd d L ^ m * Real.exp (-(agmonRate d / 2 * (ϱ - 1) * ((m - 1 : ℕ) : ℝ)))) := by
            rw [pow_add]; ring
        _ ≤ bd d L ^ j * Real.exp (-(agmonRate d / 2 * t)) * bd d L :=
            mul_le_mul_of_nonneg_left habs (by positivity)
        _ = _ := by ring

/-- **VMOD-9 (3.3).** The value and the retained forward gradient at a point `x` of the layer `j`
are controlled by the cut Agmon block estimate. -/
theorem cut_case1_retained {G : GeneratingSet d L N₀ k ϱ}
    {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)} (hcut : CutAligned G cut) (hd : 3 ≤ d)
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    (α : G.Ω 1 → ℂ) (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {x y' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {u f : G.Ω 1 → ℂ} (hu : cutOperator G a ν cut α *ᵥ u = f)
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    {t : ℝ} (ht0 : 0 ≤ t) {t₂ : ℝ} (htt₂ : t ≤ t₂)
    (ht₂ : ENNReal.ofReal t₂ ≤ G.pathDist x y') :
    cutU G cut (zeroExt (G.Ω 1) u) x ≤
      (Real.sqrt 8 / poincareConst d + d * Real.sqrt (10 / poincareConst d)) *
        (L : ℝ) ^ j * Real.exp (-(agmonRate d * t₂)) * (L : ℝ) ^ j' * Real.sqrt (Green.sqNorm f) := by
  have hd0 : 0 < d := by omega
  have hc := poincareConst_pos hd0
  have hε0 := agmonRate_pos hd0
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨hb1, hb2⟩ := agmon_block_cut G hcut hd0 hν ha α hα hj1 hjk hj'1 hj'k hx hy' hu hsupp
    (ht0.trans htt₂) ht₂ hε0.le le_rfl
  set F := Green.sqNorm f with hF
  have hF0 : 0 ≤ F := Green.sqNorm_nonneg f
  set E := Real.exp (-(agmonRate d * t₂)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE2 : Real.exp (-(2 * agmonRate d * t₂)) = E ^ 2 := by
    rw [hE, sq, ← Real.exp_add]; congr 1; ring
  rw [hE2] at hb1 hb2
  set Lj := (L : ℝ) ^ j with hLj
  set Lj' := (L : ℝ) ^ j' with hLj'
  have hLj0 : 0 < Lj := by positivity
  have hLj'0 : 0 < Lj' := by positivity
  set w := zeroExt (G.Ω 1) u with hw
  -- the value
  have hval : ‖w x‖ ≤ Real.sqrt 8 / poincareConst d * Lj * E * Lj' * Real.sqrt F := by
    have hxb : x ∈ G.blk j x := G.mem_blk.2 rfl
    have h1 : ‖w x‖ ^ 2 ≤ ∑ z ∈ G.blk j x, ‖w z‖ ^ 2 :=
      Finset.single_le_sum (f := fun z => ‖w z‖ ^ 2) (fun _ _ => sq_nonneg _) hxb
    have hY0 : 0 ≤ Real.sqrt 8 / poincareConst d * Lj * E * Lj' * Real.sqrt F := by positivity
    have hY : (Real.sqrt 8 / poincareConst d * Lj * E * Lj' * Real.sqrt F) ^ 2 =
        8 / poincareConst d ^ 2 * Lj ^ 2 * Lj' ^ 2 * E ^ 2 * F := by
      have : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
      have h2 : Real.sqrt F ^ 2 = F := Real.sq_sqrt hF0
      calc _ = Real.sqrt 8 ^ 2 / poincareConst d ^ 2 * Lj ^ 2 * E ^ 2 * Lj' ^ 2 * Real.sqrt F ^ 2 := by
            field_simp
        _ = _ := by rw [this, h2]; ring
    exact (sq_le_sq₀ (norm_nonneg _) hY0).1 (by rw [hY]; exact h1.trans hb1)
  -- the retained gradients
  have hZ0 : 0 ≤ Real.sqrt (10 / poincareConst d) * Lj' * E * Real.sqrt F := by positivity
  have hZ : (Real.sqrt (10 / poincareConst d) * Lj' * E * Real.sqrt F) ^ 2 =
      10 / poincareConst d * Lj' ^ 2 * E ^ 2 * F := by
    have h1 : Real.sqrt (10 / poincareConst d) ^ 2 = 10 / poincareConst d :=
      Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt F ^ 2 = F := Real.sq_sqrt hF0
    calc _ = Real.sqrt (10 / poincareConst d) ^ 2 * Lj' ^ 2 * E ^ 2 * Real.sqrt F ^ 2 := by ring
      _ = _ := by rw [h1, h2]
  have hgrad : ∀ μ : Fin d, (if (x, μ) ∈ cut then (0 : ℝ) else ‖w (x + Pi.single μ 1) - w x‖) ≤
      Real.sqrt (10 / poincareConst d) * Lj' * E * Real.sqrt F := by
    intro μ
    split_ifs with hμ
    · exact hZ0
    · refine (sq_le_sq₀ (norm_nonneg _) hZ0).1 ?_
      rw [hZ]
      exact (single_le_cutBlockGrad G j w hμ).trans hb2
  have hsum : ∑ μ : Fin d, (if (x, μ) ∈ cut then (0 : ℝ) else ‖w (x + Pi.single μ 1) - w x‖) ≤
      d * (Real.sqrt (10 / poincareConst d) * Lj' * E * Real.sqrt F) := by
    calc _ ≤ ∑ _μ : Fin d, (Real.sqrt (10 / poincareConst d) * Lj' * E * Real.sqrt F) :=
          Finset.sum_le_sum fun μ _ => hgrad μ
      _ = _ := by simp
  unfold cutU
  rw [G.spacing_eq hj1 hjk hx]
  calc _ ≤ Real.sqrt 8 / poincareConst d * Lj * E * Lj' * Real.sqrt F +
        Lj * (d * (Real.sqrt (10 / poincareConst d) * Lj' * E * Real.sqrt F)) :=
        add_le_add hval (mul_le_mul_of_nonneg_left hsum hLj0.le)
    _ = _ := by ring

/-- **VMOD-9 (3.3), uniform form at bounded evaluation scale.** If `ℓ_j = L^j ≤ J` the value and
the retained forward gradient at `x` are bounded by `A₀ b √(J^d) e^{-γ t} L^{2j'} M_f`, with no
volume factor of the source block. -/
theorem cut_case1_retained_unif {G : GeneratingSet d L N₀ k ϱ}
    {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)} (hcut : CutAligned G cut) (hd : 3 ≤ d)
    (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    (α : G.Ω 1 → ℂ) (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {x y' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {u f : G.Ω 1 → ℂ} (hu : cutOperator G a ν cut α *ᵥ u = f)
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ i, ‖f i‖ ≤ Mf) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ENNReal.ofReal t ≤ G.pathDist x y') {J : ℝ} (hJ : (L : ℝ) ^ j ≤ J) :
    cutU G cut (zeroExt (G.Ω 1) u) x ≤
      (Real.sqrt 8 / poincareConst d + d * Real.sqrt (10 / poincareConst d)) * bd d L *
        Real.sqrt (J ^ d) * Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * j') * Mf) := by
  have hd0 : 0 < d := by omega
  have hc := poincareConst_pos hd0
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hb0 : 0 < bd d L := lt_of_lt_of_le one_pos (one_le_bd (d := d) (L := L))
  obtain ⟨t₂, htt₂, ht₂, habs⟩ := cut_scale_abs (G := G) hd0 hϱ hsep hj1 hj'k hy' hx ht0 ht
  have h33 := cut_case1_retained hcut hd hν ha α hα hj1 hjk hj'1 hj'k hx hy' hu hsupp ht0 htt₂ ht₂
  have hsq := sqrt_sqNorm_le_of_supp G hj'k hMf0 hMf hsupp
  rw [sqrt_L_pow_eq (by omega)] at hsq
  set A₀ := Real.sqrt 8 / poincareConst d + d * Real.sqrt (10 / poincareConst d) with hA₀
  have hA0 : 0 ≤ A₀ := by positivity
  set E := Real.exp (-(agmonRate d * t₂)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have hLj' : (0 : ℝ) < (L : ℝ) ^ j' := by positivity
  have hJ0 : 0 ≤ J := le_trans hLj.le hJ
  have hpow : (L : ℝ) ^ j * bd d L ^ j ≤ Real.sqrt (J ^ d) := by
    rw [← sqrt_L_pow_eq (by omega)]
    exact Real.sqrt_le_sqrt (pow_le_pow_left₀ hLj.le hJ d)
  have h2j' : (L : ℝ) ^ (2 * j') = ((L : ℝ) ^ j') ^ 2 := by rw [pow_mul']
  refine h33.trans ?_
  calc A₀ * (L : ℝ) ^ j * E * (L : ℝ) ^ j' * Real.sqrt (Green.sqNorm f)
      ≤ A₀ * (L : ℝ) ^ j * E * (L : ℝ) ^ j' * ((L : ℝ) ^ j' * bd d L ^ j' * Mf) := by
        gcongr
    _ = A₀ * (L : ℝ) ^ j * (bd d L ^ j' * E) * (((L : ℝ) ^ j') ^ 2 * Mf) := by ring
    _ ≤ A₀ * (L : ℝ) ^ j * (bd d L ^ j * bd d L * Real.exp (-(agmonRate d / 2 * t))) *
          (((L : ℝ) ^ j') ^ 2 * Mf) := by gcongr
    _ = A₀ * bd d L * ((L : ℝ) ^ j * bd d L ^ j) * Real.exp (-(agmonRate d / 2 * t)) *
          (((L : ℝ) ^ j') ^ 2 * Mf) := by ring
    _ ≤ A₀ * bd d L * Real.sqrt (J ^ d) * Real.exp (-(agmonRate d / 2 * t)) *
          (((L : ℝ) ^ j') ^ 2 * Mf) := by gcongr
    _ = _ := by rw [h2j']

end Balaban.Localization
