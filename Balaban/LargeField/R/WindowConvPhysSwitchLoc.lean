/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseBudgetDiff
public import Balaban.LargeField.R.WindowConvPhysReadPiece
public import Balaban.Background.GenSetStability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The switch of the background in the restricted action, locally (P7 (2.14)–(2.16))

* `Region.actionDiff_local_le`: the restricted action `A_X` at two fields `φ`, `φ'` with the
  difference `w = φ' - φ` bounded by `V` on the blocks of the sites of `X` and with
  `ℓ |∂w| ≤ V` at the sites of `X` (only there): the read budgets (52)–(53) give
  `β |A_X(φ) - A_X(φ')| ≤ A |X|_{mix} (V (…) + V²/2 (…))`.  The bounds on `w` are needed on the
  sites read by `A_X` only (`Region.actionDiff_response_le` asks for them on all of `Ω₁`);
* `jBlock_equivCast_iff`: the torus identification `Equiv.cast` of two tori of the same side
  carries `n`-blocks to `n`-blocks.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Finset

section Local

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- A block average is bounded by a bound of the zero extension on the block. -/
theorem blockAvg_norm_le_of_blk (τ : G.Ω 1 × Fin N → ℂ) {V : ℝ} {x : Torus d (N₀ * L ^ K)}
    (hx : x ∈ G.Ω 1) {i : Fin N} (hbd : ∀ y ∈ G.blk (G.layerIndex x) x, ‖svec G τ y i‖ ≤ V) :
    ‖blockAvg G τ x i‖ ≤ V := by
  obtain ⟨-, h2, -⟩ := G.layerIndex_spec hx
  unfold blockAvg
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hsum : ‖∑ y ∈ G.blk (G.layerIndex x) x, svec G τ y i‖ ≤
      ((G.blk (G.layerIndex x) x).card : ℝ) * V := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ y ∈ G.blk (G.layerIndex x) x, ‖svec G τ y i‖
        ≤ ∑ _y ∈ G.blk (G.layerIndex x) x, V := Finset.sum_le_sum fun y hy => hbd y hy
      _ = _ := by simp
  rw [card_blk_cast G _ h2] at hsum
  have hpos : (0 : ℝ) < (((L : ℝ) ^ G.layerIndex x) ^ d) := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  calc (((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ * ‖∑ y ∈ G.blk (G.layerIndex x) x, svec G τ y i‖
      ≤ (((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ * ((((L : ℝ) ^ G.layerIndex x) ^ d) * V) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = V := by field_simp

/-- **The action switch from local bounds on the difference** (P7CONV (52)–(53)): with the unprimed
reads of `φ` (`S_b`, `S_g`, `S_m`) and the per-cube coefficient budgets (`C_b`, `C_g`, `C_m`), if
`|φ' - φ| ≤ V` on the blocks of the sites of `X` and `ℓ |∂(φ' - φ)| ≤ V` at the sites of `X`, then
`β |A_X(φ) - A_X(φ')| ≤ A |X|_{mix} (V (√(S_b C_b N C_b) + √(d S_g C_g d N C_g) + √(S_m C_m N C_m)) +
V²/2 (N C_b + d N C_g + N C_m))`. -/
theorem Region.actionDiff_local_le (X : Region G) (Dc : StepDecomp X) (a : ℕ → ℝ) (ν : ℝ)
    (Dat : BgData G N) (φ φ' : G.Ω 1 × Fin N → ℂ)
    {β A V Cb Cg Cm Sb Sg Sm : ℝ} (hβ : 0 ≤ β) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (hCb : 0 ≤ Cb) (hCg : 0 ≤ Cg) (hCm : 0 ≤ Cm) (hSb : 0 ≤ Sb) (hSg : 0 ≤ Sg) (hSm : 0 ≤ Sm)
    (hcb : ∀ c, β * ∑ x ∈ (Dc.cube c).sites, ‖levelCoeff G a x‖ ≤ Cb * (A * Dc.wt c))
    (hcg : ∀ c, β * ∑ x ∈ (Dc.cube c).sites, ((G.spacing x) ^ 2)⁻¹ ≤ Cg * (A * Dc.wt c))
    (hcm : ∀ c, β * ∑ _x ∈ (Dc.cube c).sites, |ν| ≤ Cm * (A * Dc.wt c))
    (hval : ∀ x ∈ X.sites, ∀ y ∈ G.blk (G.layerIndex x) x, ∀ j : Fin N,
      ‖svec G (φ' - φ) y j‖ ≤ V)
    (hfwd : ∀ x ∈ X.sites, ∀ (μ : Fin d) (j : Fin N),
      G.spacing x * ‖svec G (φ' - φ) (x + Pi.single μ 1) j - svec G (φ' - φ) x j‖ ≤ V)
    (hbwd : ∀ x ∈ X.sites, ∀ (μ : Fin d) (j : Fin N),
      G.spacing x * ‖svec G (φ' - φ) (x - Pi.single μ 1) j - svec G (φ' - φ) x j‖ ≤ V)
    (hrB : ∀ x ∈ X.sites, ∑ j, ‖Dat.Ψ x j - blockAvg G φ x j‖ ^ 2 ≤ Sb)
    (hrGf : ∀ x ∈ X.sites, ∀ μ : Fin d, G.spacing x ^ 2 * ∑ j,
      ‖barField G Dat.Ψ φ (x + Pi.single μ 1) j - barField G Dat.Ψ φ x j‖ ^ 2 ≤ Sg)
    (hrGb : ∀ x ∈ X.sites, ∀ μ : Fin d, G.spacing x ^ 2 * ∑ j,
      ‖barField G Dat.Ψ φ (x - Pi.single μ 1) j - barField G Dat.Ψ φ x j‖ ^ 2 ≤ Sg)
    (hrM : ∀ x ∈ X.sites, ∑ j, ‖svec G φ x j - Dat.h x j‖ ^ 2 ≤ Sm) :
    ‖(β : ℂ) * actionRegionC X a ν Dat φ - (β : ℂ) * actionRegionC X a ν Dat φ'‖ ≤
      A * Dc.total * (V * (Real.sqrt ((Sb * Cb) * (N * Cb)) +
        Real.sqrt ((d * (Sg * Cg)) * (d * (N * Cg))) + Real.sqrt ((Sm * Cm) * (N * Cm))) +
      V ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm)) := by
  have hT := Dc.total_nonneg
  have hAT : 0 ≤ A * Dc.total := mul_nonneg hA hT
  have hNV : 0 ≤ (N : ℝ) * V ^ 2 := by positivity
  have hsp : ∀ x, 0 ≤ G.spacing x := fun x => (spacing_pos G (x := x)).le
  have e1 : φ + (φ' - φ) = φ' := by abel
  have key := actionRegionC_add_sub_le X a ν Dat φ (φ' - φ) (β := β) (A := A * Dc.total)
    (σ := V) (GB := Sb * Cb) (GB' := N * Cb) (GG := d * (Sg * Cg)) (GG' := d * (N * Cg))
    (GM := Sm * Cm) (GM' := N * Cm) hβ hAT hV (mul_nonneg hSb hCb) (by positivity)
    (mul_nonneg hSm hCm)
    (by
      have := Region.siteEnergy_le Dc (fun x => ‖levelCoeff G a x‖)
        (fun x j => Dat.Ψ x j - blockAvg G φ x j) (B := Sb) (κ := Cb * A) hβ hSb
        (fun x => norm_nonneg _) hrB (fun c => by simpa only [mul_assoc] using hcb c)
      calc _ ≤ _ := this
        _ = _ := by ring)
    (by
      have := Region.siteEnergy_le Dc (fun x => ‖levelCoeff G a x‖) (blockAvg G (φ' - φ))
        (B := N * V ^ 2) (κ := Cb * A) hβ hNV (fun x => norm_nonneg _)
        (fun x hx => sumsq_le_of_comp fun j =>
          blockAvg_norm_le_of_blk (φ' - φ) (X.sub_Ω hx) (hval x hx · · j))
        (fun c => by simpa only [mul_assoc] using hcb c)
      calc _ ≤ _ := this
        _ = _ := by ring)
    (by
      have := Region.bondEnergy_le Dc (barField G Dat.Ψ φ) (B := Sg) (κ := Cg * A) hβ hSg
        hrGf hrGb (fun c => by simpa only [mul_assoc] using hcg c)
      calc _ ≤ _ := this
        _ = _ := by ring)
    (by
      have := Region.bondEnergy_le Dc (svec G (φ' - φ)) (B := N * V ^ 2) (κ := Cg * A) hβ hNV
        (fun x hx μ => sq_mul_sumsq_le (hsp x) (fun j => hfwd x hx μ j))
        (fun x hx μ => sq_mul_sumsq_le (hsp x) (fun j => hbwd x hx μ j))
        (fun c => by simpa only [mul_assoc] using hcg c)
      calc _ ≤ _ := this
        _ = _ := by ring)
    (by
      have := Region.siteEnergy_le Dc (fun _ => |ν|) (fun x j => svec G φ x j - Dat.h x j)
        (B := Sm) (κ := Cm * A) hβ hSm (fun _ => abs_nonneg _) hrM
        (fun c => by simpa only [mul_assoc] using hcm c)
      calc _ ≤ _ := this
        _ = _ := by ring)
    (by
      have := Region.siteEnergy_le Dc (fun _ => |ν|) (svec G (φ' - φ)) (B := N * V ^ 2)
        (κ := Cm * A) hβ hNV (fun _ => abs_nonneg _)
        (fun x hx => sumsq_le_of_comp fun j =>
          hval x hx x (GeneratingSet.mem_blk.2 rfl) j)
        (fun c => by simpa only [mul_assoc] using hcm c)
      calc _ ≤ _ := this
        _ = _ := by ring)
  rw [e1] at key
  have hsym : ‖(β : ℂ) * actionRegionC X a ν Dat φ - (β : ℂ) * actionRegionC X a ν Dat φ'‖ =
      ‖(β : ℂ) * (actionRegionC X a ν Dat φ' - actionRegionC X a ν Dat φ)‖ := by
    rw [← norm_neg]; congr 1; ring
  rw [hsym]
  calc _ ≤ _ := key
    _ = _ := by ring

end Local

section Cast

theorem val_equivCast_symm {d a b : ℕ} (h : a = b) (x : Torus d b) (i : Fin d) :
    ((Equiv.cast (congrArg (Torus d) h)).symm x i).val = (x i).val := by
  subst h; rfl

/-- **`Equiv.cast` carries `n`-blocks to `n`-blocks** between the tori `𝕋(N₀_w L^{k_w})` and
`𝕋(N₀_l L^{k_l})` of the same side, `n ≤ k_l, k_w`. -/
theorem jBlock_equivCast_iff {d L N₀l kl N₀w kw : ℕ} [NeZero N₀l] [NeZero N₀w] [NeZero L]
    (h : N₀w * L ^ kw = N₀l * L ^ kl) {n : ℕ} (hnl : n ≤ kl) (hnw : n ≤ kw)
    (x y : Torus d (N₀l * L ^ kl)) :
    jBlock d L N₀l kl n x = jBlock d L N₀l kl n y ↔
      jBlock d L N₀w kw n ((Equiv.cast (congrArg (Torus d) h)).symm x) =
        jBlock d L N₀w kw n ((Equiv.cast (congrArg (Torus d) h)).symm y) := by
  unfold jBlock
  rw [blockMap_eq_iff_val (side_eq (N₀ := N₀l) (L := L) (k := kl) hnl),
    blockMap_eq_iff_val (side_eq (N₀ := N₀w) (L := L) (k := kw) hnw)]
  constructor
  · intro hxy i
    rw [val_equivCast_symm h, val_equivCast_symm h]
    exact hxy i
  · intro hxy i
    have := hxy i
    rwa [val_equivCast_symm h, val_equivCast_symm h] at this

end Cast

end Balaban.LargeField.ActionConv
