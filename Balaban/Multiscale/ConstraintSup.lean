/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.GlobalBound
public import Balaban.Multiscale.ConstraintSandwich
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The constraint sandwich in the weighted sup norms (GREEN.md G-2(v'))

Norms: `|f|₂ = sup_x ℓ(x)² |f(x)|` (stated as `∀ x, ℓ(x)² ‖f x‖ ≤ C`; for vector sources
componentwise), `|u|₀`, `|∂u|₁`, `|Δ^D u|₂` as in `global_bound` (bundled as `SupBounds`).

* `KGphi_sup`: `|K(φ₀) Ĝ φ₀ s|₂ ≤ c_* δ |s|₂`, `c_* = sandwichConst d L N`;
* `constraintM_inv_sup`: `|M⁻¹ g|₂ ≤ 2 |g|₂` if `(1 + c_*) δ ≤ 1/2`;
* `constraintForm_inv_mul_green`: `[φ₀ · Ĝ φ₀]⁻¹ Ĝ = M⁻¹`; `constrainedOp_eq_dirichlet`;
* `constrained_sup`: `Π f` and `(Ĝ - Π) f` satisfy the sup bounds with constants `B₁'`, `B + B₁'`,
  including `|Δ^D Π f|₂`.

The constants depend on `(d, L, N)`: the vector norm of `Ĝ(φ₀ s)` is estimated componentwise. The
hypotheses are those of `Standing` (so complex `φ₀`, bilinear dot product) plus the hypotheses of
`global_bound` on `ν` and `ϱ`; the lower bound `|φ₀| > 1/2` is not used.
-/

@[expose] public section

namespace Balaban.Multiscale

open Matrix Finset Balaban Balaban.LatticeGreen

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem vn_le_card_mul {v : Fin N → ℂ} {m : ℝ} (hm : 0 ≤ m) (h : ∀ i, ‖v i‖ ≤ m) :
    vn v ≤ N * m := by
  have h1 : vn v ^ 2 ≤ (N * m) ^ 2 := by
    rw [vn_sq]
    calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin N, m ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2
      _ = N * m ^ 2 := by simp
      _ ≤ (N : ℝ) ^ 2 * m ^ 2 := by
          have : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
            rcases Nat.eq_zero_or_pos N with h0 | h0
            · simp [h0]
            · have : (1 : ℝ) ≤ N := by exact_mod_cast h0
              nlinarith
          exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = (N * m) ^ 2 := by ring
  exact le_of_sq_le_sq h1 (by positivity)

/-- A site of `Ω₁` adjacent to a site outside `Ω₁` lies in layer `1`: `ℓ(x) ≤ L`. -/
theorem spacing_le_of_adj_not_mem (G : GeneratingSet d L N₀ k ϱ) (hϱ : 1 < ϱ) (hL : 1 ≤ L)
    {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hx' : x' ∉ G.Ω 1) (h : Adj x x') :
    G.spacing x ≤ L := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hx
  by_cases hj : G.layerIndex x = 1
  · rw [GeneratingSet.spacing, hj, pow_one]
  · exfalso
    have hj2 : 2 ≤ G.layerIndex x := by omega
    have hx2 : x ∈ G.Ω 2 := G.Ω_antitone (by omega) hj2 (by omega) (G.mem_layer.1 hxl).1
    have hs := G.separation 1 le_rfl (by omega) x' hx' x hx2
    have h1 := h.symm.torusDist_le
    have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
    rw [pow_one] at hs
    nlinarith


section KBound

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The constant of the sup-norm bound for `K(φ₀)`. -/
noncomputable def commKConst (d L N : ℕ) : ℝ := N * (2 * d * L + 1 + 4 * d)

/-- **The commutator bound in the sup norms.**  If all component values of `s̃` are at most `V`
and the forward (resp. backward) component differences satisfy `ℓ(x) |∂ s̃| ≤ V` (resp. `L V`),
then `ℓ² |K(φ₀) s| ≤ C δ V`. -/
theorem commK_sup_bound (hd : 0 < d) (hL : 1 ≤ L) {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a)
    (ν : ℝ) (α : G.Ω 1 → ℂ) {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ) (s : G.Ω 1 × Fin N → ℂ) {V : ℝ} (hV0 : 0 ≤ V)
    (hV : ∀ y i, ‖svec G s y i‖ ≤ V)
    (hf : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N),
      G.spacing x * ‖svec G s (x + Pi.single μ 1) i - svec G s x i‖ ≤ V)
    (hb : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N),
      G.spacing x * ‖svec G s (x - Pi.single μ 1) i - svec G s x i‖ ≤ L * V) (x : G.Ω 1) :
    G.spacing x ^ 2 * ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖ ≤
      commKConst d L N * δ * V := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec x.2
  set j := G.layerIndex (x : Torus d (N₀ * L ^ k)) with hjdef
  have hsp : G.spacing x = (L : ℝ) ^ j := G.spacing_eq hj1 hjk hxl
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have h := commK_pointwise G ha ν α hφ hδ (isAgmonWeight_zero G) (le_refl (0 : ℝ)) s hj1 hjk x hxl
  simp only [zero_mul, Real.exp_zero, one_mul, mul_one] at h
  rw [hsp] at h ⊢
  set p : Torus d (N₀ * L ^ k) := (x : Torus d (N₀ * L ^ k)) with hp
  set ℓ : ℝ := (L : ℝ) ^ j with hℓ
  have hNV : 0 ≤ (N : ℝ) * V := by positivity
  -- vector norms
  have hvx : vn (svec G s p) ≤ N * V := vn_le_card_mul hV0 (hV _)
  have hvf : ∀ μ : Fin d, ℓ * vn (svec G s (p + Pi.single μ 1) - svec G s p) ≤ N * V := by
    intro μ
    have hm : 0 ≤ V / ℓ := by positivity
    have := vn_le_card_mul (v := svec G s (p + Pi.single μ 1) - svec G s p) hm (fun i => by
      rw [le_div_iff₀ hLj, mul_comm]
      have := hf p x.2 μ i
      rw [hsp] at this
      simpa using this)
    calc ℓ * vn _ ≤ ℓ * (N * (V / ℓ)) := mul_le_mul_of_nonneg_left this hLj.le
      _ = N * V := by field_simp
  have hvb : ∀ μ : Fin d, ℓ * vn (svec G s (p - Pi.single μ 1) - svec G s p) ≤ N * (L * V) := by
    intro μ
    have hm : 0 ≤ L * V / ℓ := by positivity
    have := vn_le_card_mul (v := svec G s (p - Pi.single μ 1) - svec G s p) hm (fun i => by
      rw [le_div_iff₀ hLj, mul_comm]
      have := hb p x.2 μ i
      rw [hsp] at this
      simpa using this)
    calc ℓ * vn _ ≤ ℓ * (N * (L * V / ℓ)) := mul_le_mul_of_nonneg_left this hLj.le
      _ = N * (L * V) := by field_simp
  -- the block average
  have hblk : (((L : ℝ) ^ j) ^ d)⁻¹ * ∑ y ∈ G.blk j p, vn (svec G s y) ≤ N * V := by
    have hc := card_blk_cast G j hjk x
    have hsum : ∑ y ∈ G.blk j p, vn (svec G s y) ≤ (G.blk j p).card * (N * V) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun y _ => vn_le_card_mul hV0 (hV _)
    rw [hc] at hsum
    have hp : (0 : ℝ) < ((L : ℝ) ^ j) ^ d := by positivity
    rw [inv_mul_le_iff₀ hp]
    linarith
  have hsumμ : (∑ μ : Fin d, (vn (svec G s (p + Pi.single μ 1) - svec G s p) +
      vn (svec G s (p - Pi.single μ 1) - svec G s p))) * ℓ ≤ d * (N * V + N * (L * V)) := by
    rw [Finset.sum_mul]
    calc _ ≤ ∑ _μ : Fin d, (N * V + N * (L * V)) := by
          refine Finset.sum_le_sum fun μ _ => ?_
          have := hvf μ
          have := hvb μ
          nlinarith
      _ = _ := by simp; ring
  -- assemble
  have hlead : ℓ * ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖ ≤ _ := h
  have hb2 : 0 ≤ ∑ μ : Fin d, (vn (svec G s (p + Pi.single μ 1) - svec G s p) +
      vn (svec G s (p - Pi.single μ 1) - svec G s p)) :=
    Finset.sum_nonneg fun μ _ => add_nonneg (vn_nonneg _) (vn_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hlead hLj.le
  calc ℓ ^ 2 * ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖
      = ℓ * (ℓ * ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖) := by ring
    _ ≤ _ := hmul
    _ ≤ commKConst d L N * δ * V := by
        unfold commKConst
        have e : ∀ A B C : ℝ, ℓ * (δ * A + δ * ℓ⁻¹ * B + 4 * d * δ * ℓ⁻¹ * C) =
            δ * (A * ℓ) + δ * B + 4 * d * δ * C := by
          intro A B C; field_simp
        rw [e]
        have h1 := mul_le_mul_of_nonneg_left hsumμ hδ
        have h2 := mul_le_mul_of_nonneg_left hvx hδ
        have h3 := mul_le_mul_of_nonneg_left hblk (by positivity : (0 : ℝ) ≤ 4 * d * δ)
        have h4 : 0 ≤ (d : ℝ) * (L - 1) * N * V * δ := by
          have : (0 : ℝ) ≤ L - 1 := by linarith
          positivity
        nlinarith
end KBound


section GreenSup

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The component sup bounds on a vector field `u` on `Ω₁` (zero extended): `|u|₀`, `|∂u|₁` (both
directions) and `|Δ^D u|₂` are at most `V`, componentwise. -/
structure SupBounds (u : G.Ω 1 × Fin N → ℂ) (V : ℝ) : Prop where
  val : ∀ (y : Torus d (N₀ * L ^ k)) (i : Fin N), ‖svec G u y i‖ ≤ V
  fwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N),
    G.spacing x * ‖svec G u (x + Pi.single μ 1) i - svec G u x i‖ ≤ V
  bwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N),
    G.spacing x * ‖svec G u (x - Pi.single μ 1) i - svec G u x i‖ ≤ V
  lap : ∀ x ∈ G.Ω 1, ∀ i : Fin N, G.spacing x ^ 2 * ‖∑ μ : Fin d, (2 * svec G u x i -
    svec G u (x + Pi.single μ 1) i - svec G u (x - Pi.single μ 1) i)‖ ≤ V

variable {G}

theorem SupBounds.mono {u : G.Ω 1 × Fin N → ℂ} {V V' : ℝ} (h : SupBounds G u V) (hV : V ≤ V') :
    SupBounds G u V' :=
  ⟨fun y i => (h.val y i).trans hV, fun x hx μ i => (h.fwd x hx μ i).trans hV,
    fun x hx μ i => (h.bwd x hx μ i).trans hV, fun x hx i => (h.lap x hx i).trans hV⟩

theorem svec_liftOp (A : Matrix (G.Ω 1) (G.Ω 1) ℂ) (g : G.Ω 1 × Fin N → ℂ) (i : Fin N)
    (y : Torus d (N₀ * L ^ k)) :
    svec G (liftOp N A *ᵥ g) y i = zeroExt (G.Ω 1) (A *ᵥ comp G g i) y := by
  unfold svec
  congr 1
  funext z
  exact congrFun (comp_liftOp A g i) z

/-- The statement of the sup bounds for `Ĝ g` with constant `B`. -/
def GreenSupSpec (d L : ℕ) [NeZero L] (B : ℝ) : Prop :=
  ∀ {k N₀ N : ℕ} [NeZero N₀] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)
      {a : ℕ → ℝ} {ν : ℝ}, 0 ≤ ν → ν * ((L : ℝ) ^ k) ^ 2 ≤ 1 →
      IsAdmissibleWeights k a → ∀ {α : G.Ω 1 → ℂ},
      (∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) →
      2 * d * Real.log L ≤ agmonRate d / 2 / 2 * (ϱ - 1) → ∀ (g : G.Ω 1 × Fin N → ℂ) {Cg : ℝ},
      0 ≤ Cg → (∀ (x : G.Ω 1) (i : Fin N), (G.spacing (x : Torus d (N₀ * L ^ k))) ^ 2 * ‖g (x, i)‖ ≤ Cg) →
      SupBounds G (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) (B * Cg)

/-- **The sup bounds for `Ĝ g`**, from the global weighted bound G-2(iv) applied to each
component (the constant is `L B` with `B` of `global_bound`). -/
theorem exists_green_sup (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ GreenSupSpec d L B := by
  classical
  obtain ⟨B1, hB1, hB⟩ := global_bound (d := d) (L := L) hd hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  refine ⟨L * B1, by positivity, ?_⟩
  intro k N₀ N _ ϱ G a ν hν0 hν1 ha α hα hϱ g Cg hCg hg
  have hε := agmonRate_pos (d := d) (by omega)
  have hL3 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hlog : 0 < Real.log L := Real.log_pos hL3
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hϱ1 : 1 < ϱ := by
    by_contra hcon
    push Not at hcon
    have : agmonRate d / 2 / 2 * (ϱ - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have : 0 < 2 * d * Real.log L := by positivity
    linarith
  have hBC : B1 * Cg ≤ L * B1 * Cg := by nlinarith [mul_nonneg hB1 hCg]
  have hcomp := fun (i : Fin N) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) =>
    hB G hν0 hν1 ha hα hϱ (comp G g i) hCg (fun x => hg x i) hx
  -- rewrite svec
  have hs : ∀ y i, svec G (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) y i =
      zeroExt (G.Ω 1) ((dirichletOperator G a ν α)⁻¹ *ᵥ comp G g i) y :=
    fun y i => svec_liftOp _ g i y
  have hval : ∀ (y : Torus d (N₀ * L ^ k)) (i : Fin N),
      ‖zeroExt (G.Ω 1) ((dirichletOperator G a ν α)⁻¹ *ᵥ comp G g i) y‖ ≤ B1 * Cg := by
    intro y i
    by_cases hy : y ∈ G.Ω 1
    · exact (hcomp i hy).1
    · rw [zeroExt_not_mem _ _ hy]; simpa using mul_nonneg hB1 hCg
  refine ⟨fun y i => ?_, fun x hx μ i => ?_, fun x hx μ i => ?_, fun x hx i => ?_⟩ <;>
    simp only [hs]
  · exact (hval y i).trans hBC
  · exact ((hcomp i hx).2.1 μ).1.trans hBC
  swap
  · exact ((hcomp i hx).2.2).trans hBC
  by_cases hp : x - Pi.single μ 1 ∈ G.Ω 1
  · have h1 := ((hcomp i hp).2.1 μ).2 (by simpa using hx)
    rw [sub_add_cancel] at h1
    have e : G.spacing (x - Pi.single μ 1 + Pi.single μ 1) = G.spacing x := by
      rw [sub_add_cancel]
    rw [norm_sub_rev]
    simpa [sub_add_cancel] using h1.trans hBC
  · rw [zeroExt_not_mem _ _ hp, zero_sub, norm_neg]
    have hadj : Adj x (x - Pi.single μ 1) := ⟨μ, Or.inr (by simp)⟩
    have hs := spacing_le_of_adj_not_mem G hϱ1 (by omega) hx hp hadj
    calc _ ≤ (L : ℝ) * ‖zeroExt (G.Ω 1) ((dirichletOperator G a ν α)⁻¹ *ᵥ comp G g i) x‖ :=
          mul_le_mul hs le_rfl (norm_nonneg _) (by positivity)
      _ ≤ L * (B1 * Cg) := mul_le_mul_of_nonneg_left (hval x i) (by positivity)
      _ = _ := by ring

end GreenSup


section Sandwich

/-- The constant `B = B(d, L)` of the sup bounds for `Ĝ g` (zero outside the range of
`exists_green_sup`). -/
noncomputable def greenSupConst (d L : ℕ) [NeZero L] : ℝ := by
  classical
  exact if h : 3 ≤ d ∧ 3 ≤ L then Classical.choose (exists_green_sup (d := d) (L := L) h.1 h.2)
    else 0

theorem greenSupConst_nonneg (d L : ℕ) [NeZero L] : 0 ≤ greenSupConst d L := by
  unfold greenSupConst
  split_ifs with h
  · exact (Classical.choose_spec (exists_green_sup (d := d) (L := L) h.1 h.2)).1
  · exact le_rfl

theorem greenSupConst_spec (hd : 3 ≤ d) (hL : 3 ≤ L) : GreenSupSpec d L (greenSupConst d L) := by
  unfold greenSupConst
  split_ifs with h
  · exact (Classical.choose_spec (exists_green_sup (d := d) (L := L) h.1 h.2)).2
  · exact absurd ⟨hd, hL⟩ h

/-- The constant `c_* = c_*(d, L, N)` of G-2(v'): `|K(φ₀) Ĝ φ₀ s|₂ ≤ c_* δ |s|₂`. -/
noncomputable def sandwichConst (d L N : ℕ) [NeZero L] : ℝ :=
  3 / 2 * commKConst d L N * greenSupConst d L

theorem sandwichConst_nonneg (d L N : ℕ) [NeZero L] : 0 ≤ sandwichConst d L N := by
  unfold sandwichConst commKConst
  have := greenSupConst_nonneg d L
  positivity

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ} {δ : ℝ}
  {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}

/-- **`K(φ₀) Ĝ g` in the sup norm**, for a source with `ℓ² |g_i| ≤ C_g` componentwise. -/
theorem KG_sup (hd : 3 ≤ d) (hL : 3 ≤ L) (St : Standing G a ν α δ φ)
    (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (hϱ : 2 * d * Real.log L ≤ agmonRate d / 2 / 2 * (ϱ - 1)) (g : G.Ω 1 × Fin N → ℂ) {Cg : ℝ}
    (hCg : 0 ≤ Cg) (hg : ∀ (x : G.Ω 1) (i : Fin N), (G.spacing (x : Torus d (N₀ * L ^ k))) ^ 2 *
      ‖g (x, i)‖ ≤ Cg) (x : G.Ω 1) :
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖(commK (dirichletOperator G a ν α)
        (restrictField G φ) *ᵥ (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g)) x‖ ≤
      commKConst d L N * δ * (greenSupConst d L * Cg) := by
  have hS := greenSupConst_spec hd hL G St.mass hν1 St.weights St.alpha hϱ g hCg hg
  have hV0 : 0 ≤ greenSupConst d L * Cg := mul_nonneg (greenSupConst_nonneg d L) hCg
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  exact commK_sup_bound G St.pos (by omega) St.weights ν α St.field.toIsSmoothField St.nonneg _ hV0
    hS.val hS.fwd (fun x hx μ i => (hS.bwd x hx μ i).trans (le_mul_of_one_le_left hV0 hL1)) x

/-- **G-2(v'), item 1.**  `|K(φ₀) Ĝ φ₀ s|₂ ≤ c_* δ |s|₂`. -/
theorem KGphi_sup (hd : 3 ≤ d) (hL : 3 ≤ L) (St : Standing G a ν α δ φ)
    (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (hϱ : 2 * d * Real.log L ≤ agmonRate d / 2 / 2 * (ϱ - 1)) (s : G.Ω 1 → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hs : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖s x‖ ≤ C)
    (x : G.Ω 1) :
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖(commK (dirichletOperator G a ν α)
        (restrictField G φ) *ᵥ (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ
          (fieldMul (restrictField G φ) *ᵥ s))) x‖ ≤ sandwichConst d L N * δ * C := by
  have h := KG_sup hd hL St hν1 hϱ (fieldMul (restrictField G φ) *ᵥ s) (Cg := 3 / 2 * C)
    (by positivity) (fun y i => by
      rw [fieldMul_mulVec, norm_mul]
      have h1 : ‖restrictField G φ y i‖ ≤ 3 / 2 := (norm_le_vn _ i).trans (St.field.bound y y.2)
      calc _ = ‖restrictField G φ y i‖ * (G.spacing (y : Torus d (N₀ * L ^ k)) ^ 2 * ‖s y‖) := by
            ring
        _ ≤ 3 / 2 * C := mul_le_mul h1 (hs y) (by positivity) (by norm_num)) x
  refine h.trans (le_of_eq ?_)
  unfold sandwichConst
  ring

/-- **G-2(v'), item 2.**  `M = φ₀² - K(φ₀) Ĝ φ₀` is invertible with `|M⁻¹ g|₂ ≤ 2 |g|₂`, as soon as
`(1 + c_*) δ ≤ 1/2`. -/
theorem constraintM_inv_sup (hd : 3 ≤ d) (hL : 3 ≤ L) (St : Standing G a ν α δ φ)
    (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (hϱ : 2 * d * Real.log L ≤ agmonRate d / 2 / 2 * (ϱ - 1))
    (hδ : (1 + sandwichConst d L N) * δ ≤ 1 / 2) (g : G.Ω 1 → ℂ) {C : ℝ}
    (hg : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖g x‖ ≤ C)
    (x : G.Ω 1) :
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖((constraintM (dirichletOperator G a ν α)
      (dirichletOperator G a ν α)⁻¹ (restrictField G φ))⁻¹ *ᵥ g) x‖ ≤ 2 * C := by
  classical
  set Mm := constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
    (restrictField G φ) with hMm
  have hU : IsUnit Mm := constraintM_isUnit St
  have hMinv : Mm * Mm⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU)
  set s : G.Ω 1 → ℂ := Mm⁻¹ *ᵥ g with hs
  have hMs : Mm *ᵥ s = g := by rw [hs, mulVec_mulVec, hMinv, one_mulVec]
  have : Nonempty (G.Ω 1) := ⟨x⟩
  obtain ⟨x₀, hx₀⟩ := Finite.exists_max
    (fun y : G.Ω 1 => G.spacing (y : Torus d (N₀ * L ^ k)) ^ 2 * ‖s y‖)
  set m := G.spacing (x₀ : Torus d (N₀ * L ^ k)) ^ 2 * ‖s x₀‖ with hm
  have hm0 : 0 ≤ m := by positivity
  have hsm : ∀ y : G.Ω 1, G.spacing (y : Torus d (N₀ * L ^ k)) ^ 2 * ‖s y‖ ≤ m := hx₀
  have key := constraintM_mulVec (G := G) (a := a) (ν := ν) (α := α) (φ := φ) s
  rw [hMs] at key
  have hK := KGphi_sup hd hL St hν1 hϱ s hm0 hsm x₀
  have hsq : ‖(1 - ∑ i, restrictField G φ x₀ i * restrictField G φ x₀ i) * s x₀‖ ≤ δ * ‖s x₀‖ := by
    rw [norm_mul, norm_sub_rev]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact St.field.sq x₀ x₀.2
  have h1 := congrFun key x₀
  have hpt : s x₀ = g x₀ + ((fun x : G.Ω 1 => (1 - ∑ i, φ x i * φ x i) * s x) +
        commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ
          (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ (fieldMul (restrictField G φ) *ᵥ s))) x₀ := by
    rw [← h1]; simp
  have hsp : 0 ≤ G.spacing (x₀ : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
  have hn : ‖s x₀‖ ≤ ‖g x₀‖ + (δ * ‖s x₀‖ + ‖(commK (dirichletOperator G a ν α)
        (restrictField G φ) *ᵥ (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ
          (fieldMul (restrictField G φ) *ᵥ s))) x₀‖) := by
    conv_lhs => rw [hpt]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ((norm_add_le _ _).trans ?_))
    exact add_le_add hsq le_rfl
  have h2 := mul_le_mul_of_nonneg_left hn hsp
  have hgx := hg x₀
  have hδ0 := St.nonneg
  have hc0 := sandwichConst_nonneg d L N
  have h3 : G.spacing (x₀ : Torus d (N₀ * L ^ k)) ^ 2 * (δ * ‖s x₀‖) ≤ δ * m := by
    rw [hm]; nlinarith
  have h4 : m ≤ C + (δ * m + sandwichConst d L N * δ * m) := by
    calc m = G.spacing (x₀ : Torus d (N₀ * L ^ k)) ^ 2 * ‖s x₀‖ := rfl
      _ ≤ _ := h2
      _ ≤ _ := by nlinarith
  have h5 : m ≤ 2 * C := by nlinarith [mul_le_mul_of_nonneg_right hδ hm0]
  exact (hsm x).trans h5


theorem svec_sub (u w : G.Ω 1 × Fin N → ℂ) (y : Torus d (N₀ * L ^ k)) (i : Fin N) :
    svec G (u - w) y i = svec G u y i - svec G w y i := by
  unfold svec zeroExt
  split_ifs <;> simp

theorem SupBounds.sub {u w : G.Ω 1 × Fin N → ℂ} {V W : ℝ} (hu : SupBounds G u V)
    (hw : SupBounds G w W) : SupBounds G (u - w) (V + W) := by
  have key : ∀ (y z : Torus d (N₀ * L ^ k)) (i : Fin N),
      svec G (u - w) y i - svec G (u - w) z i =
        (svec G u y i - svec G u z i) - (svec G w y i - svec G w z i) := by
    intro y z i; simp only [svec_sub]; ring
  refine ⟨fun y i => ?_, fun x hx μ i => ?_, fun x hx μ i => ?_, fun x hx i => ?_⟩
  · rw [svec_sub]; exact (norm_sub_le _ _).trans (add_le_add (hu.val y i) (hw.val y i))
  · rw [key, mul_comm, ← mul_comm]
    calc _ ≤ G.spacing x * (‖svec G u (x + Pi.single μ 1) i - svec G u x i‖ +
          ‖svec G w (x + Pi.single μ 1) i - svec G w x i‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (spacing_pos G).le
      _ ≤ _ := by rw [mul_add]; exact add_le_add (hu.fwd x hx μ i) (hw.fwd x hx μ i)
  · rw [key]
    calc _ ≤ G.spacing x * (‖svec G u (x - Pi.single μ 1) i - svec G u x i‖ +
          ‖svec G w (x - Pi.single μ 1) i - svec G w x i‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (spacing_pos G).le
      _ ≤ _ := by rw [mul_add]; exact add_le_add (hu.bwd x hx μ i) (hw.bwd x hx μ i)
  · have e : ∑ μ : Fin d, (2 * svec G (u - w) x i - svec G (u - w) (x + Pi.single μ 1) i -
        svec G (u - w) (x - Pi.single μ 1) i) =
        ∑ μ : Fin d, (2 * svec G u x i - svec G u (x + Pi.single μ 1) i -
          svec G u (x - Pi.single μ 1) i) -
        ∑ μ : Fin d, (2 * svec G w x i - svec G w (x + Pi.single μ 1) i -
          svec G w (x - Pi.single μ 1) i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun μ _ => by simp only [svec_sub]; ring
    rw [e]
    calc _ ≤ G.spacing x ^ 2 * (‖∑ μ : Fin d, (2 * svec G u x i - svec G u (x + Pi.single μ 1) i -
          svec G u (x - Pi.single μ 1) i)‖ + ‖∑ μ : Fin d, (2 * svec G w x i -
          svec G w (x + Pi.single μ 1) i - svec G w (x - Pi.single μ 1) i)‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ _ := by rw [mul_add]; exact add_le_add (hu.lap x hx i) (hw.lap x hx i)

/-- **G-2(v'), item 3a.**  `[φ₀ · G φ₀]⁻¹ G = M⁻¹`. -/
theorem constraintForm_inv_mul_green (St : Standing G a ν α δ φ) :
    (constraintForm (dirichletOperator G a ν α)⁻¹ (restrictField G φ))⁻¹ *
        (dirichletOperator G a ν α)⁻¹ =
      (constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
        (restrictField G φ))⁻¹ := by
  rw [constraintForm_inv (dirichlet_mul_inv St) (dirichlet_inv_mul St), Matrix.mul_assoc,
    dirichlet_mul_inv St, Matrix.mul_one]

/-- **The sandwich formula** `Π = Ĝ φ₀ M⁻¹ N`, with `H = G_D(α)⁻¹ = dirichletOperator`. -/
theorem constrainedOp_eq_dirichlet (St : Standing G a ν α δ φ) :
    constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) =
      liftOp N (dirichletOperator G a ν α)⁻¹ * fieldMul (restrictField G φ) *
        (constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
          (restrictField G φ))⁻¹ *
        constraintN (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
          (restrictField G φ) :=
  constrainedOp_eq (dirichlet_mul_inv St) (dirichlet_inv_mul St) _

/-- The constant `B₁'` of G-2(v'): `|Π f|₀ + |∂ Π f|₁ + |Δ^D Π f|₂ ≤ B₁' |f|₂`. -/
noncomputable def piSupConst (d L N : ℕ) [NeZero L] : ℝ :=
  3 * (3 / 2 * N + commKConst d L N * greenSupConst d L) * greenSupConst d L

theorem piSupConst_nonneg (d L N : ℕ) [NeZero L] : 0 ≤ piSupConst d L N := by
  unfold piSupConst commKConst
  have := greenSupConst_nonneg d L
  positivity

/-- **G-2(v'), item 3b.**  For a source `f` with `ℓ² |f_i| ≤ C` componentwise, the constrained
operator `Π = Ĝ φ₀ [φ₀ · Ĝ φ₀]⁻¹ φ₀ · Ĝ` satisfies the sup bounds `|Π f|₀, |∂ Π f|₁, |Δ^D Π f|₂ ≤ B₁' C`
(`SupBounds`), and so does `Ĝ - Π` (the constrained Green's function) with constant
`B + B₁'`. -/
theorem constrained_sup (hd : 3 ≤ d) (hL : 3 ≤ L) (St : Standing G a ν α δ φ)
    (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (hϱ : 2 * d * Real.log L ≤ agmonRate d / 2 / 2 * (ϱ - 1))
    (hδ : (1 + sandwichConst d L N) * δ ≤ 1 / 2) (f : G.Ω 1 × Fin N → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ (x : G.Ω 1) (i : Fin N), G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖f (x, i)‖ ≤ C) :
    SupBounds G (constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f)
        (piSupConst d L N * C) ∧
      SupBounds G ((liftOp N (dirichletOperator G a ν α)⁻¹ -
          constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ)) *ᵥ f)
        ((greenSupConst d L + piSupConst d L N) * C) := by
  classical
  have hB0 := greenSupConst_nonneg d L
  have hc0 := sandwichConst_nonneg d L N
  have hδ0 := St.nonneg
  have hδ1 : δ ≤ 1 := by nlinarith
  have hcK : 0 ≤ commKConst d L N := by unfold commKConst; positivity
  set Mm := constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
    (restrictField G φ) with hMm
  set Dn : ℝ := 3 / 2 * N + commKConst d L N * greenSupConst d L with hDn
  have hDn0 : 0 ≤ Dn := by positivity
  -- the source `N f`
  have hNf : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
      ‖(constraintN (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
        (restrictField G φ) *ᵥ f) x‖ ≤ Dn * C := by
    intro x
    unfold constraintN
    rw [sub_mulVec, ← mulVec_mulVec, Pi.sub_apply]
    have h1 : G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
        ‖((fieldMul (restrictField G φ))ᵀ *ᵥ f) x‖ ≤ 3 / 2 * N * C := by
      rw [fieldMul_transpose_mulVec]
      calc _ ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ∑ i, ‖restrictField G φ x i * f (x, i)‖ :=
            mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
        _ = ∑ i, ‖restrictField G φ x i‖ * (G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
              ‖f (x, i)‖) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [norm_mul]; ring
        _ ≤ ∑ _i : Fin N, 3 / 2 * C := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h1 : ‖restrictField G φ x i‖ ≤ 3 / 2 :=
              (norm_le_vn _ i).trans (St.field.bound x x.2)
            exact mul_le_mul h1 (hf x i) (by positivity) (by norm_num)
        _ = 3 / 2 * N * C := by simp; ring
    have h2 := KG_sup hd hL St hν1 hϱ f hC hf x
    have h3 : commKConst d L N * δ * (greenSupConst d L * C) ≤
        commKConst d L N * greenSupConst d L * C := by
      have : 0 ≤ commKConst d L N * (greenSupConst d L * C) := by positivity
      nlinarith
    calc _ ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
          (‖((fieldMul (restrictField G φ))ᵀ *ᵥ f) x‖ + ‖(commK (dirichletOperator G a ν α)
            (restrictField G φ) *ᵥ (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ f)) x‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ _ := by rw [mul_add]; nlinarith
  -- the solution `h = M⁻¹ N f`
  set h : G.Ω 1 → ℂ := Mm⁻¹ *ᵥ (constraintN (dirichletOperator G a ν α)
    (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f) with hh
  have hh2 : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖h x‖ ≤ 2 * (Dn * C) :=
    fun x => constraintM_inv_sup hd hL St hν1 hϱ hδ _ hNf x
  have hPi : constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f =
      liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ (fieldMul (restrictField G φ) *ᵥ h) := by
    rw [constrainedOp_eq_dirichlet St, hh]
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  have hCg : 0 ≤ 3 * (Dn * C) := by positivity
  have hS := greenSupConst_spec hd hL G St.mass hν1 St.weights St.alpha hϱ
    (fieldMul (restrictField G φ) *ᵥ h) hCg (fun y i => by
      rw [fieldMul_mulVec, norm_mul]
      have h1 : ‖restrictField G φ y i‖ ≤ 3 / 2 := (norm_le_vn _ i).trans (St.field.bound y y.2)
      calc _ = ‖restrictField G φ y i‖ * (G.spacing (y : Torus d (N₀ * L ^ k)) ^ 2 * ‖h y‖) := by
            ring
        _ ≤ 3 / 2 * (2 * (Dn * C)) :=
            mul_le_mul h1 (hh2 y) (by positivity) (by norm_num)
        _ = 3 * (Dn * C) := by ring)
  have hPi' : SupBounds G (constrainedOp (dirichletOperator G a ν α)⁻¹ (restrictField G φ) *ᵥ f)
      (piSupConst d L N * C) := by
    rw [hPi]
    refine hS.mono (le_of_eq ?_)
    unfold piSupConst
    rw [hDn]
    ring
  refine ⟨hPi', ?_⟩
  rw [sub_mulVec]
  have hG := greenSupConst_spec hd hL G St.mass hν1 St.weights St.alpha hϱ f hC hf
  have := hG.sub hPi'
  refine this.mono (le_of_eq ?_)
  ring

end Sandwich

end Balaban.Multiscale
