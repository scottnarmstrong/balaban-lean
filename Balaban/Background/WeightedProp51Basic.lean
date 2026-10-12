module

public import Balaban.Background.Contraction
public import Balaban.Localization.DecoupledWeighted
public import Balaban.Multiscale.ConstraintComm
public import Balaban.Multiscale.ConstraintSup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weighted norms for the perturbed system (weighted Proposition 5.1, part 1)

Weights and the Agmon exponent `log w / γ`; the weighted `StarBound`; the weighted commutator
bound and the weighted bound of `R`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban Balaban.Multiscale Balaban.Localization Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Weights

variable {G : GeneratingSet d L N₀ k ϱ} {γ : ℝ} {w : Torus d (N₀ * L ^ k) → ℝ}

/-- The two-sided weight comparison along a path distance bound. -/
theorem weight_two_sided (hγ : 0 ≤ γ) (hw : IsWeight G γ w) {x y : Torus d (N₀ * L ^ k)}
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hxy : G.pathDist x y ≤ ENNReal.ofReal ρ) :
    w x ≤ w y * Real.exp (γ * ρ) ∧ w y ≤ w x * Real.exp (γ * ρ) := by
  refine ⟨hw.le_mul hγ hρ hxy, hw.le_mul hγ hρ ?_⟩
  rw [GeneratingSet.pathDist_comm]; exact hxy

/-- Weights vary by `e^{2dγ}` on a block of its layer. -/
theorem weight_block_le (hγ : 0 ≤ γ) (hw : IsWeight G γ w) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    {x y : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j) (hy : y ∈ G.blk j x) :
    w x ≤ w y * Real.exp (γ * (2 * d)) :=
  (weight_two_sided hγ hw (by positivity) (G.pathDist_block_le hj hjk hx (GeneratingSet.mem_blk.1 hy))).1

/-- Weights vary by `e^{γ}` along bonds of `Ω₁`. -/
theorem weight_adj_le (hγ : 0 ≤ γ) (hw : IsWeight G γ w) {x y : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) (hy : y ∈ G.Ω 1) (hadj : Adj x y) :
    w x ≤ w y * Real.exp (γ * G.bondCost x y) ∧ w y ≤ w x * Real.exp (γ * G.bondCost x y) := by
  refine weight_two_sided hγ hw (G.bondCost_nonneg x y) (G.pathDist_le_bondCost hx hy hadj)

theorem abs_log_div_sub_le (hγ : 0 < γ) (hw : IsWeight G γ w) {x y : Torus d (N₀ * L ^ k)} {ρ : ℝ}
    (h1 : w x ≤ w y * Real.exp (γ * ρ)) (h2 : w y ≤ w x * Real.exp (γ * ρ)) :
    |Real.log (w x) / γ - Real.log (w y) / γ| ≤ ρ := by
  have hx := hw.pos x
  have hy := hw.pos y
  have l1 : Real.log (w x) ≤ Real.log (w y) + γ * ρ := by
    calc Real.log (w x) ≤ Real.log (w y * Real.exp (γ * ρ)) := Real.log_le_log hx h1
      _ = _ := by rw [Real.log_mul hy.ne' (Real.exp_pos _).ne', Real.log_exp]
  have l2 : Real.log (w y) ≤ Real.log (w x) + γ * ρ := by
    calc Real.log (w y) ≤ Real.log (w x * Real.exp (γ * ρ)) := Real.log_le_log hy h2
      _ = _ := by rw [Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [← sub_div, abs_le]
  constructor
  · rw [le_div_iff₀ hγ]; nlinarith
  · rw [div_le_iff₀ hγ]; nlinarith

/-- A weight of rate `γ > 0` gives the admissible exponent `log w / γ`. -/
theorem isAgmonWeight_log (hγ : 0 < γ) (hw : IsWeight G γ w) :
    IsAgmonWeight G (fun x => Real.log (w x) / γ) where
  bond := fun x x' hx hx' hadj => by
    obtain ⟨h1, h2⟩ := weight_adj_le hγ.le hw hx hx' hadj
    exact abs_log_div_sub_le hγ hw h1 h2
  block := fun j hj hjk x x' hx h => by
    have hx' : x' ∈ G.blk j x := GeneratingSet.mem_blk.2 h
    have h1 := weight_block_le hγ.le hw hj hjk hx hx'
    have h2 : w x' ≤ w x * Real.exp (γ * (2 * d)) :=
      (weight_two_sided hγ.le hw (by positivity)
        (G.pathDist_block_le hj hjk hx h)).2
    exact abs_log_div_sub_le hγ hw h1 h2

theorem exp_log_div (hγ : 0 < γ) (hw : IsWeight G γ w) (x : Torus d (N₀ * L ^ k)) :
    Real.exp (γ * (Real.log (w x) / γ)) = w x := by
  rw [mul_div_cancel₀ _ hγ.ne', Real.exp_log (hw.pos x)]

end Weights


section Star

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The weighted `StarBound`: `w |u|₀`, `w |∂u|₁` (both directions) are at most `V`. -/
structure StarBoundW (w : Torus d (N₀ * L ^ k) → ℝ) (u : G.Ω 1 × Fin N → ℂ) (V : ℝ) : Prop where
  val : ∀ (y : Torus d (N₀ * L ^ k)) (i : Fin N), w y * ‖svec G u y i‖ ≤ V
  fwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N),
    w x * (G.spacing x * ‖svec G u (x + Pi.single μ 1) i - svec G u x i‖) ≤ V
  bwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N),
    w x * (G.spacing x * ‖svec G u (x - Pi.single μ 1) i - svec G u x i‖) ≤ V

end Star

section Comm

variable {G : GeneratingSet d L N₀ k ϱ} {γ : ℝ} {w : Torus d (N₀ * L ^ k) → ℝ}

/-- The weighted commutator constant. -/
noncomputable def commKConstW (d N : ℕ) (γ : ℝ) : ℝ :=
  N * (2 * d + 1 + 4 * d * Real.exp (γ * (2 * d)))

theorem commKConstW_nonneg (d N : ℕ) (γ : ℝ) : 0 ≤ commKConstW d N γ := by
  unfold commKConstW; positivity

/-- **The weighted commutator bound**: `w ℓ² |K(φ₀) s| ≤ C_w δ V` for `s` with `StarBoundW`. -/
theorem commK_weighted (hγ : 0 < γ) (hw : IsWeight G γ w) {a : ℕ → ℝ}
    (ha : IsAdmissibleWeights k a) (ν : ℝ) (α : G.Ω 1 → ℂ) {δ : ℝ}
    {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ)
    {s : G.Ω 1 × Fin N → ℂ} {V : ℝ} (hV : 0 ≤ V) (hs : StarBoundW G w s V) (x : G.Ω 1) :
    w x * (G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
        ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖) ≤
      commKConstW d N γ * δ * V := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec x.2
  set j := G.layerIndex (x : Torus d (N₀ * L ^ k)) with hjdef
  have hsp : G.spacing x = (L : ℝ) ^ j := G.spacing_eq hj1 hjk hxl
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have h := commK_pointwise G ha ν α hφ hδ (isAgmonWeight_log hγ hw) hγ.le s hj1 hjk x hxl
  simp only [exp_log_div hγ hw] at h
  rw [hsp] at h ⊢
  set p : Torus d (N₀ * L ^ k) := (x : Torus d (N₀ * L ^ k)) with hp
  set ℓ : ℝ := (L : ℝ) ^ j with hℓ
  have hwp : 0 < w p := hw.pos p
  have hNV : 0 ≤ (N : ℝ) * V := by positivity
  have hvx : w p * vn (svec G s p) ≤ N * V := by
    have := vn_le_card_mul (v := svec G s p) (m := V / w p) (by positivity) (fun i => by
      rw [le_div_iff₀ hwp, mul_comm]; exact hs.val p i)
    calc w p * vn (svec G s p) ≤ w p * (N * (V / w p)) :=
          mul_le_mul_of_nonneg_left this hwp.le
      _ = N * V := by field_simp
  have hvf : ∀ μ : Fin d, w p * (ℓ * vn (svec G s (p + Pi.single μ 1) - svec G s p)) ≤ N * V := by
    intro μ
    have hm : 0 ≤ V / (w p * ℓ) := by positivity
    have := vn_le_card_mul (v := svec G s (p + Pi.single μ 1) - svec G s p) hm (fun i => by
      rw [le_div_iff₀ (by positivity), mul_comm]
      have := hs.fwd p x.2 μ i
      rw [hsp] at this
      simpa [mul_assoc] using this)
    calc w p * (ℓ * vn _) = (w p * ℓ) * vn _ := by ring
      _ ≤ (w p * ℓ) * (N * (V / (w p * ℓ))) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = N * V := by field_simp
  have hvb : ∀ μ : Fin d, w p * (ℓ * vn (svec G s (p - Pi.single μ 1) - svec G s p)) ≤ N * V := by
    intro μ
    have hm : 0 ≤ V / (w p * ℓ) := by positivity
    have := vn_le_card_mul (v := svec G s (p - Pi.single μ 1) - svec G s p) hm (fun i => by
      rw [le_div_iff₀ (by positivity), mul_comm]
      have := hs.bwd p x.2 μ i
      rw [hsp] at this
      simpa [mul_assoc] using this)
    calc w p * (ℓ * vn _) = (w p * ℓ) * vn _ := by ring
      _ ≤ (w p * ℓ) * (N * (V / (w p * ℓ))) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = N * V := by field_simp
  have hblk : (((L : ℝ) ^ j) ^ d)⁻¹ * ∑ y ∈ G.blk j p, w y * vn (svec G s y) ≤ N * V := by
    have hc := card_blk_cast G j hjk x
    have hsum : ∑ y ∈ G.blk j p, w y * vn (svec G s y) ≤ (G.blk j p).card * (N * V) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun y _ => ?_
      have hwy : 0 < w y := hw.pos y
      have := vn_le_card_mul (v := svec G s y) (m := V / w y) (by positivity) (fun i => by
        rw [le_div_iff₀ hwy, mul_comm]; exact hs.val y i)
      calc w y * vn (svec G s y) ≤ w y * (N * (V / w y)) :=
            mul_le_mul_of_nonneg_left this hwy.le
        _ = N * V := by field_simp
    rw [hc] at hsum
    have hp0 : (0 : ℝ) < ((L : ℝ) ^ j) ^ d := by positivity
    rw [inv_mul_le_iff₀ hp0]
    linarith
  have hsumμ : ∑ μ : Fin d, (w p * (ℓ * (vn (svec G s (p + Pi.single μ 1) - svec G s p) +
      vn (svec G s (p - Pi.single μ 1) - svec G s p)))) ≤ d * (N * V + N * V) := by
    calc _ ≤ ∑ _μ : Fin d, (N * V + N * V) := by
          refine Finset.sum_le_sum fun μ _ => ?_
          have := hvf μ
          have := hvb μ
          nlinarith
      _ = _ := by simp; ring
  have hb2 : 0 ≤ ∑ μ : Fin d, (vn (svec G s (p + Pi.single μ 1) - svec G s p) +
      vn (svec G s (p - Pi.single μ 1) - svec G s p)) :=
    Finset.sum_nonneg fun μ _ => add_nonneg (vn_nonneg _) (vn_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left h hLj.le
  have hE : 0 ≤ 4 * (d : ℝ) * δ * Real.exp (γ * (2 * d)) := by positivity
  calc w p * (ℓ ^ 2 * ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖)
      = ℓ * (ℓ * w p * ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖) := by
        ring
    _ ≤ _ := hmul
    _ ≤ commKConstW d N γ * δ * V := by
        unfold commKConstW
        have e : ∀ A B C : ℝ, ℓ * (δ * w p * A + δ * ℓ⁻¹ * (w p * B) +
            4 * d * δ * Real.exp (γ * (2 * d)) * ℓ⁻¹ * C) =
            δ * (w p * (ℓ * A)) + δ * (w p * B) + 4 * d * δ * Real.exp (γ * (2 * d)) * C := by
          intro A B C; field_simp
        rw [e]
        have hS : w p * (ℓ * ∑ μ : Fin d, (vn (svec G s (p + Pi.single μ 1) - svec G s p) +
            vn (svec G s (p - Pi.single μ 1) - svec G s p))) ≤ d * (N * V + N * V) := by
          rw [Finset.mul_sum, Finset.mul_sum]; exact hsumμ
        have h1 := mul_le_mul_of_nonneg_left hS hδ
        have h2 := mul_le_mul_of_nonneg_left hvx hδ
        have h3 := mul_le_mul_of_nonneg_left hblk hE
        nlinarith

end Comm


section RBound

variable {G : GeneratingSet d L N₀ k ϱ} {γ : ℝ} {w : Torus d (N₀ * L ^ k) → ℝ}

/-- The weighted bound of the block average. -/
theorem blockTerm_weighted_le (hγ : 0 ≤ γ) (hw : IsWeight G γ w) {a : ℕ → ℝ}
    (ha : IsAdmissibleWeights k a) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    {f : Torus d (N₀ * L ^ k) → ℂ} {F : ℝ} (hf : ∀ y, w y * ‖f y‖ ≤ F) :
    w x * ‖blockTerm G a f x‖ ≤
      a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 * (Real.exp (γ * (2 * d)) * F) := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hx
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have haj : 0 ≤ a (G.layerIndex x) := by linarith [(ha _ hj1 hjk).1]
  have hLj : (0 : ℝ) < ((L : ℝ) ^ G.layerIndex x) ^ d := by positivity
  have hc : ((G.blk (G.layerIndex x) x).card : ℝ) = ((L : ℝ) ^ G.layerIndex x) ^ d :=
    card_blk_cast G _ hjk x
  have hwx := hw.pos x
  unfold blockTerm
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity)]
  have hsum : w x * ‖∑ y ∈ G.blk (G.layerIndex x) x, f y‖ ≤
      ((L : ℝ) ^ G.layerIndex x) ^ d * (Real.exp (γ * (2 * d)) * F) := by
    calc w x * ‖∑ y ∈ G.blk (G.layerIndex x) x, f y‖
        ≤ w x * ∑ y ∈ G.blk (G.layerIndex x) x, ‖f y‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) hwx.le
      _ = ∑ y ∈ G.blk (G.layerIndex x) x, w x * ‖f y‖ := by rw [Finset.mul_sum]
      _ ≤ ∑ _y ∈ G.blk (G.layerIndex x) x, (Real.exp (γ * (2 * d)) * F) := by
          refine Finset.sum_le_sum fun y hy => ?_
          have h1 := weight_block_le hγ hw hj1 hjk hxl hy
          calc w x * ‖f y‖ ≤ (w y * Real.exp (γ * (2 * d))) * ‖f y‖ :=
                mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
            _ = Real.exp (γ * (2 * d)) * (w y * ‖f y‖) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (hf y) (Real.exp_pos _).le
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hc]
  have h1 : w x * ((((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ *
      ‖∑ y ∈ G.blk (G.layerIndex x) x, f y‖) ≤ Real.exp (γ * (2 * d)) * F := by
    calc _ = (((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ *
          (w x * ‖∑ y ∈ G.blk (G.layerIndex x) x, f y‖) := by ring
      _ ≤ (((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ * (((L : ℝ) ^ G.layerIndex x) ^ d *
          (Real.exp (γ * (2 * d)) * F)) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by field_simp
  have hc0 : 0 ≤ a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 := by positivity
  calc _ = a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 *
        (w x * ((((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ *
          ‖∑ y ∈ G.blk (G.layerIndex x) x, f y‖)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 hc0


/-- The constant of the weighted bound of `R`. -/
noncomputable def RConstW (d : ℕ) (γ : ℝ) : ℝ := 2 * d + 4 + 4 * Real.exp (γ * (2 * d))

theorem RConstW_nonneg (d : ℕ) (γ : ℝ) : 0 ≤ RConstW d γ := by unfold RConstW; positivity

/-- The weighted bound of `R(u, v)` at a point: `u` weighted, `v` unweighted. -/
theorem Rsc_bound_weighted (hγ : 0 ≤ γ) (hw : IsWeight G γ w) {a : ℕ → ℝ}
    (ha : IsAdmissibleWeights k a) {ν : ℝ} (hν0 : 0 ≤ ν)
    {α : G.Ω 1 → ℂ} {x : G.Ω 1} (hν : ν * G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 ≤ 1)
    (hα : G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x‖ ≤ 1)
    {u v : G.Ω 1 → ℂ} {U W : ℝ} (hU : 0 ≤ U) (hW : 0 ≤ W)
    (hu0 : ∀ y, w y * ‖zeroExt (G.Ω 1) u y‖ ≤ U) (hv0 : ∀ y, ‖zeroExt (G.Ω 1) v y‖ ≤ W)
    (hu1 : ∀ μ : Fin d, w x * (G.spacing (x : Torus d (N₀ * L ^ k)) *
      ‖zeroExt (G.Ω 1) u ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) - u x‖) ≤ U)
    (hu2 : ∀ μ : Fin d, w x * (G.spacing (x : Torus d (N₀ * L ^ k)) *
      ‖zeroExt (G.Ω 1) u ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) - u x‖) ≤ U)
    (hv1 : ∀ μ : Fin d, G.spacing (x : Torus d (N₀ * L ^ k)) *
      ‖zeroExt (G.Ω 1) v ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) - v x‖ ≤ W)
    (hv2 : ∀ μ : Fin d, G.spacing (x : Torus d (N₀ * L ^ k)) *
      ‖zeroExt (G.Ω 1) v ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) - v x‖ ≤ W) :
    w x * (G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
        ‖Rsc (dirichletOperator G a ν α) u v x‖) ≤ RConstW d γ * (U * W) := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec x.2
  set p : Torus d (N₀ * L ^ k) := (x : Torus d (N₀ * L ^ k)) with hp
  set ℓ : ℝ := G.spacing p with hℓdef
  have hsp : ℓ = (L : ℝ) ^ G.layerIndex p := G.spacing_eq hj1 hjk hxl
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hℓ : 0 < ℓ := by rw [hsp]; positivity
  have hUW : 0 ≤ U * W := mul_nonneg hU hW
  have hwp : 0 < w p := hw.pos p
  have hE : 1 ≤ Real.exp (γ * (2 * d)) := Real.one_le_exp (by positivity)
  have hxe : ∀ f : G.Ω 1 → ℂ, zeroExt (G.Ω 1) f p = f x := fun f => zeroExt_mem _ _ _
  have key : ∀ b c : ℂ, w p * (ℓ * ‖b‖) ≤ U → ℓ * ‖c‖ ≤ W → w p * (ℓ ^ 2 * ‖b * c‖) ≤ U * W := by
    intro b c hb hc
    rw [norm_mul]
    calc w p * (ℓ ^ 2 * (‖b‖ * ‖c‖)) = (w p * (ℓ * ‖b‖)) * (ℓ * ‖c‖) := by ring
      _ ≤ U * W := mul_le_mul hb hc (by positivity) hU
  rw [Rsc_apply]
  set T1 := ∑ μ : Fin d, ((zeroExt (G.Ω 1) u (p + Pi.single μ 1) - u x) *
          (zeroExt (G.Ω 1) v (p + Pi.single μ 1) - v x) +
        (zeroExt (G.Ω 1) u (p - Pi.single μ 1) - u x) *
          (zeroExt (G.Ω 1) v (p - Pi.single μ 1) - v x)) with hT1
  set T2 := blockTerm G a (fun y => zeroExt (G.Ω 1) u y * zeroExt (G.Ω 1) v y) p -
        u x * blockTerm G a (zeroExt (G.Ω 1) v) p - v x * blockTerm G a (zeroExt (G.Ω 1) u) p
    with hT2
  set T3 := ((ν : ℂ) + α x) * (u x * v x) with hT3
  have h1 : w p * (ℓ ^ 2 * ‖T1‖) ≤ 2 * d * (U * W) := by
    calc w p * (ℓ ^ 2 * ‖T1‖) ≤ w p * (ℓ ^ 2 * ∑ μ : Fin d, (‖(zeroExt (G.Ω 1) u (p + Pi.single μ 1) - u x) *
          (zeroExt (G.Ω 1) v (p + Pi.single μ 1) - v x)‖ +
        ‖(zeroExt (G.Ω 1) u (p - Pi.single μ 1) - u x) *
          (zeroExt (G.Ω 1) v (p - Pi.single μ 1) - v x)‖)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            ((norm_sum_le _ _).trans ?_) (by positivity)) hwp.le
          exact Finset.sum_le_sum fun μ _ => norm_add_le _ _
      _ = ∑ μ : Fin d, (w p * (ℓ ^ 2 * ‖(zeroExt (G.Ω 1) u (p + Pi.single μ 1) - u x) *
          (zeroExt (G.Ω 1) v (p + Pi.single μ 1) - v x)‖) +
        w p * (ℓ ^ 2 * ‖(zeroExt (G.Ω 1) u (p - Pi.single μ 1) - u x) *
          (zeroExt (G.Ω 1) v (p - Pi.single μ 1) - v x)‖)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun μ _ => by ring
      _ ≤ ∑ _μ : Fin d, (U * W + U * W) := by
          refine Finset.sum_le_sum fun μ _ => add_le_add ?_ ?_
          · exact key _ _ (hu1 μ) (hv1 μ)
          · exact key _ _ (hu2 μ) (hv2 μ)
      _ = 2 * d * (U * W) := by simp; ring
  have hc : ℓ ^ 2 * (a (G.layerIndex p) / ((L : ℝ) ^ G.layerIndex p) ^ 2) ≤ 2 := by
    have h2 := (ha _ hj1 hjk).2
    rw [hsp]
    have : (0 : ℝ) < ((L : ℝ) ^ G.layerIndex p) ^ 2 := by positivity
    calc ((L : ℝ) ^ G.layerIndex p) ^ 2 * (a (G.layerIndex p) / ((L : ℝ) ^ G.layerIndex p) ^ 2)
        = a (G.layerIndex p) := by field_simp
      _ ≤ 2 := h2
  have hc0 : 0 ≤ a (G.layerIndex p) / ((L : ℝ) ^ G.layerIndex p) ^ 2 := by
    have := (ha _ hj1 hjk).1
    positivity
  have hux : w p * ‖u x‖ ≤ U := by simpa [hxe] using hu0 p
  have hvx : ‖v x‖ ≤ W := by simpa [hxe] using hv0 p
  have hb1 := blockTerm_weighted_le hγ hw ha x.2
    (f := fun y => zeroExt (G.Ω 1) u y * zeroExt (G.Ω 1) v y) (F := U * W) (fun y => by
      rw [norm_mul]
      calc w y * (‖zeroExt (G.Ω 1) u y‖ * ‖zeroExt (G.Ω 1) v y‖)
          = (w y * ‖zeroExt (G.Ω 1) u y‖) * ‖zeroExt (G.Ω 1) v y‖ := by ring
        _ ≤ U * W := mul_le_mul (hu0 y) (hv0 y) (norm_nonneg _) hU)
  have hb2 := blockTerm_norm_le (G := G) ha x.2 (f := zeroExt (G.Ω 1) v) hv0
  have hb3 := blockTerm_weighted_le hγ hw ha x.2 (f := zeroExt (G.Ω 1) u) hu0
  set c := a (G.layerIndex p) / ((L : ℝ) ^ G.layerIndex p) ^ 2 with hcdef
  set e := Real.exp (γ * (2 * d)) with hedef
  have h2 : w p * ‖T2‖ ≤ c * (e * (U * W)) + U * (c * W) + W * (c * (e * U)) := by
    have hn : w p * ‖T2‖ ≤ w p * ‖blockTerm G a (fun y => zeroExt (G.Ω 1) u y *
        zeroExt (G.Ω 1) v y) p‖ + w p * (‖u x‖ * ‖blockTerm G a (zeroExt (G.Ω 1) v) p‖) +
        w p * (‖v x‖ * ‖blockTerm G a (zeroExt (G.Ω 1) u) p‖) := by
      rw [← mul_add, ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hwp.le
      refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add le_rfl ?_)) ?_)
      · rw [norm_mul]
      · rw [norm_mul]
    refine hn.trans (add_le_add (add_le_add hb1 ?_) ?_)
    · calc w p * (‖u x‖ * ‖blockTerm G a (zeroExt (G.Ω 1) v) p‖)
          = (w p * ‖u x‖) * ‖blockTerm G a (zeroExt (G.Ω 1) v) p‖ := by ring
        _ ≤ U * (c * W) := mul_le_mul hux hb2 (norm_nonneg _) hU
    · calc w p * (‖v x‖ * ‖blockTerm G a (zeroExt (G.Ω 1) u) p‖)
          = ‖v x‖ * (w p * ‖blockTerm G a (zeroExt (G.Ω 1) u) p‖) := by ring
        _ ≤ W * (c * (e * U)) := mul_le_mul hvx hb3 (by positivity) hW
  have h2' : w p * (ℓ ^ 2 * ‖T2‖) ≤ (4 * e + 2) * (U * W) := by
    calc w p * (ℓ ^ 2 * ‖T2‖) = ℓ ^ 2 * (w p * ‖T2‖) := by ring
      _ ≤ ℓ ^ 2 * (c * (2 * e + 1) * (U * W)) := by
          refine mul_le_mul_of_nonneg_left (h2.trans (le_of_eq (by ring))) (by positivity)
      _ = (ℓ ^ 2 * c) * ((2 * e + 1) * (U * W)) := by ring
      _ ≤ 2 * ((2 * e + 1) * (U * W)) := by
          refine mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  have h3 : w p * (ℓ ^ 2 * ‖T3‖) ≤ 2 * (U * W) := by
    have hn : ‖((ν : ℂ) + α x)‖ ≤ ν + ‖α x‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_of_nonneg hν0]
    calc w p * (ℓ ^ 2 * ‖T3‖) = ℓ ^ 2 * ‖((ν : ℂ) + α x)‖ * ((w p * ‖u x‖) * ‖v x‖) := by
          rw [hT3, norm_mul, norm_mul]; ring
      _ ≤ (ν * ℓ ^ 2 + ℓ ^ 2 * ‖α x‖) * (U * W) := by
          have hq : ℓ ^ 2 * ‖((ν : ℂ) + α x)‖ ≤ ν * ℓ ^ 2 + ℓ ^ 2 * ‖α x‖ := by nlinarith [sq_nonneg ℓ]
          exact mul_le_mul hq (mul_le_mul hux hvx (norm_nonneg _) hU) (by positivity) (by positivity)
      _ ≤ (1 + 1) * (U * W) := by gcongr
      _ = _ := by ring
  have hsum : ‖-T1 + T2 - T3‖ ≤ ‖T1‖ + ‖T2‖ + ‖T3‖ := by
    refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) le_rfl)
    rw [norm_neg]
  unfold RConstW
  calc w p * (ℓ ^ 2 * ‖-T1 + T2 - T3‖) ≤ w p * (ℓ ^ 2 * (‖T1‖ + ‖T2‖ + ‖T3‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) hwp.le
    _ = w p * (ℓ ^ 2 * ‖T1‖) + w p * (ℓ ^ 2 * ‖T2‖) + w p * (ℓ ^ 2 * ‖T3‖) := by ring
    _ ≤ 2 * d * (U * W) + (4 * e + 2) * (U * W) + 2 * (U * W) := by linarith
    _ = _ := by ring

/-- The weighted bound of the vector `R(u, v)`: `u` with weighted `StarBoundW`, `v` unweighted. -/
theorem Rvec_bound_weighted (hγ : 0 ≤ γ) (hw : IsWeight G γ w) {a : ℕ → ℝ}
    (ha : IsAdmissibleWeights k a) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    {α : G.Ω 1 → ℂ} (hα : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x‖ ≤ 1)
    {u v : G.Ω 1 × Fin N → ℂ} {U W : ℝ} (hU : 0 ≤ U) (hW : 0 ≤ W)
    (hu : StarBoundW G w u U) (hv : StarBound G v W) (x : G.Ω 1) :
    w x * (G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
        ‖Rvec (dirichletOperator G a ν α) u v x‖) ≤ N * (RConstW d γ * (U * W)) := by
  have hwp : 0 < w x := hw.pos x
  have hνx : ν * G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hν0) hν
    exact pow_le_pow_left₀ (spacing_pos G).le (spacing_le G x.2) 2
  have hxe : ∀ (s : G.Ω 1 × Fin N → ℂ) (i : Fin N) (y : G.Ω 1),
      zeroExt (G.Ω 1) (comp G s i) (y : Torus d (N₀ * L ^ k)) = s (y, i) :=
    fun s i y => zeroExt_mem _ _ _
  have hi : ∀ i : Fin N, w x * (G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
      ‖Rsc (dirichletOperator G a ν α) (comp G u i) (comp G v i) x‖) ≤ RConstW d γ * (U * W) := by
    intro i
    refine Rsc_bound_weighted hγ hw ha hν0 hνx (hα x) hU hW (fun y => hu.val y i)
      (fun y => hv.val y i) (fun μ => ?_) (fun μ => ?_) (fun μ => ?_) (fun μ => ?_)
    · have := hu.fwd x x.2 μ i
      rwa [svec_of_mem] at this
    · have := hu.bwd x x.2 μ i
      rwa [svec_of_mem] at this
    · have := hv.fwd x x.2 μ i
      rwa [svec_of_mem] at this
    · have := hv.bwd x x.2 μ i
      rwa [svec_of_mem] at this
  unfold Rvec
  calc w x * (G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
        ‖∑ i, Rsc (dirichletOperator G a ν α) (comp G u i) (comp G v i) x‖)
      ≤ w x * (G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
        ∑ i, ‖Rsc (dirichletOperator G a ν α) (comp G u i) (comp G v i) x‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_sum_le _ _)
          (by positivity)) hwp.le
    _ = ∑ i, w x * (G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
        ‖Rsc (dirichletOperator G a ν α) (comp G u i) (comp G v i) x‖) := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ ∑ _i : Fin N, RConstW d γ * (U * W) := Finset.sum_le_sum fun i _ => hi i
    _ = _ := by simp


end RBound

end Balaban.Background
