/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Xi
public import Balaban.Multiscale.ConstraintSup
public import Balaban.Background.Theorem73
public import Balaban.Background.MinimizerExpansion

/-!
# The inequalities of `Ξ^c` for the renormalized datum

`RenormThetaDatum` item (ii): the complex datum `Dᶜ` of a member of `Ξ^c_n(𝔹; σ, ε)` is replaced by
`D^n = (1 + ζ) Dᶜ` (`ζ = ε ξ₁`), with displacement `Ψ''_n = Ψ'' + ζ Dᶜ.Ψ`.  The solution of `D^n` differs
from that of `Dᶜ` by `F = φ^n - φ^c` with `SupBounds F V`, `Small (α^n - α^c) V` (the solution map `F` of
`IsRenSol`, `IsRenSol.eq_bgC`).  `XiCBounds.scale` states that the eight inequalities of `XiCBounds` persist
with a larger radius `ε' = ε + Δ`, when `Δ` satisfies the explicit inequalities `room_*` (the loss of
P4 (4.19)).  The only place where the scale `ℓ(x)` of the blocks matters is the boundary of `Ω₁`: a site
of `Ω₁` adjacent to a site outside `Ω₁` lies in layer `1`, so `ℓ(x) ≤ L` there, and the loss does not
depend on the scale `k`.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}

/-- The block average of a field with `‖svec‖ ≤ V` is at most `V`. -/
theorem norm_blockAvg_le {φ : G.Ω 1 × Fin N → ℂ} {V : ℝ} (h : ∀ (y : Torus d (N₀ * L ^ k)) (i : Fin N), ‖svec G φ y i‖ ≤ V) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) (i : Fin N) : ‖blockAvg G φ x i‖ ≤ V := by
  obtain ⟨hn1, hnk, -⟩ := G.layerIndex_spec hx
  unfold blockAvg
  have hc := card_blk_cast G (G.layerIndex x) hnk x
  have hL : (0 : ℝ) < ((L : ℝ) ^ G.layerIndex x) ^ d := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hL)]
  calc (((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ * ‖∑ y ∈ G.blk (G.layerIndex x) x, svec G φ y i‖
      ≤ (((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ * ∑ y ∈ G.blk (G.layerIndex x) x, V :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun y _ => h y i)) (inv_nonneg.2 hL.le)
    _ = V := by
        rw [Finset.sum_const, nsmul_eq_mul, hc]; field_simp

/-- The difference of the extensions of the renormalized and the old solution: `F` on `Ω₁`, `ζ Ψ` outside. -/
theorem bar_diff_scaled {Dc Dn : BgData G N} {ζ : ℂ}
    (hΨn : ∀ x ∈ dataSites G, ∀ i, Dn.Ψ x i = (1 + ζ) * Dc.Ψ x i)
    (φn φc : G.Ω 1 × Fin N → ℂ) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ dataSites G) (i : Fin N) :
    barField G Dn.Ψ φn y i - barField G Dc.Ψ φc y i =
      svec G (φn - φc) y i + (if y ∈ G.Ω 1 then 0 else ζ * Dc.Ψ y i) := by
  classical
  by_cases hy1 : y ∈ G.Ω 1
  · simp [barField, svec, zeroExt, hy1]
  · simp only [barField, svec, zeroExt, hy1, dite_false, ↓reduceIte, zero_add]
    rw [hΨn y hy i]; ring

variable {ν σ ε ε' V : ℝ} {ζ : ℂ} {Dr Dc Dn : BgData G N}
  {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φr φc φn : G.Ω 1 × Fin N → ℂ}
  {αr αc αn : G.Ω 1 → ℂ}

/-- **The inequalities of `Ξ^c` for the renormalized datum.**  Let `Dc` be the complex datum of a member
of `Ξ^c_n(𝔹; σ, ε)` (`XiCBounds` for the real datum `Dr`), `Dn = (1 + ζ) Dc` on the data sites, and let
the solutions `(φn, αn)` of `Dn` and `(φc, αc)` of `Dc` differ by `F = φn − φc` with `SupBounds F V` and
`Small (αn − αc) V`.  Then `XiCBounds` holds for `Dn`, with the displacement `Ψ'' + ζ Dc.Ψ` and the radius
`ε' ≥ ε`, as soon as the loss `Δ = ε' − ε` satisfies `room1`–`room6`.  Here `vn (Dc.Ψ x) ≤ 3` on the data
sites and `|Dc.Ψ z − Dc.Ψ z'| ≤ 2 σ ε` on adjacent collar sites are consequences of the domain and of
`XiBounds`, `XiCBounds` for `Dc`. -/
theorem XiCBounds.scale {Ψ''n : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hΨ''n : ∀ x ∈ dataSites G, ∀ i, Ψ''n x i = Ψ'' x i + ζ * Dc.Ψ x i)
    (hB : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc) (hϱ : 1 < ϱ)
    (hΨn : ∀ x ∈ dataSites G, ∀ i, Dn.Ψ x i = (1 + ζ) * Dc.Ψ x i)
    (hsup : SupBounds G (φn - φc) V) (hsm : Small G (αn - αc) V) (hV : 0 ≤ V) (hσ : 0 < σ) (hε0 : 0 < ε)
    (hvΨ : ∀ x ∈ dataSites G, vn (Dc.Ψ x) ≤ 3)
    (hcol : ∀ z ∈ collar G, ∀ z' ∈ collar G, Adj z z' →
      vn (fun i => Dc.Ψ z i - Dc.Ψ z' i) ≤ 2 * σ * ε) (hε : ε ≤ ε')
    (room1 : N * V + 3 * ‖ζ‖ * L ≤ σ * (ε' - ε))
    (room2 : N * (V + 6 * d * ‖ζ‖ * (L : ℝ) ^ 2) ≤ σ ^ 2 * (ε' - ε))
    (room3 : V ≤ σ ^ 2 * (ε' - ε)) (room4 : N * V ≤ ε' - ε)
    (room5 : N * (3 * ‖ζ‖ + V) ≤ σ ^ 2 * (ε' - ε))
    (room6 : 2 * σ * ε * ‖ζ‖ ≤ σ * (ε' - ε)) :
    XiCBounds G ν σ ε' Dr Dn Ψ''n h'' φr φn αr αn := by
  classical
  have hρ := norm_nonneg ζ
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hΔ : 0 ≤ ε' - ε := by linarith
  -- the ζ-term outside `Ω₁`
  have ht : ∀ y ∈ dataSites G, vn (fun i => if y ∈ G.Ω 1 then (0 : ℂ) else ζ * Dc.Ψ y i) ≤ 3 * ‖ζ‖ := by
    intro y hy
    by_cases hy1 : y ∈ G.Ω 1
    · simp only [hy1, ↓reduceIte]
      have : vn (fun _ : Fin N => (0 : ℂ)) = 0 := vn_zero
      rw [this]; positivity
    · simp only [hy1, ↓reduceIte]
      rw [vn_smul_complex]
      have := hvΨ y hy
      nlinarith
  have hsupn : ∀ y i, ‖svec G (φn - φc) y i‖ ≤ V := fun y i => hsup.val y i
  -- grad in one direction
  have gradDir : ∀ x ∈ G.Ω 1, ∀ y, y ∈ dataSites G → Adj x y →
      (∀ i, G.spacing x * ‖svec G (φn - φc) y i - svec G (φn - φc) x i‖ ≤ V) →
      vn (fun i => (barField G Dc.Ψ φc y i - barField G Dr.Ψ φr y i) -
        (barField G Dc.Ψ φc x i - barField G Dr.Ψ φr x i)) < σ * ε / G.spacing x →
      vn (fun i => (barField G Dn.Ψ φn y i - barField G Dr.Ψ φr y i) -
        (barField G Dn.Ψ φn x i - barField G Dr.Ψ φr x i)) < σ * ε' / G.spacing x := by
    intro x hx y hy hadj hcomp hold
    have hℓ : 0 < G.spacing x := spacing_pos G
    have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    set F := φn - φc
    have e : (fun i => (barField G Dn.Ψ φn y i - barField G Dr.Ψ φr y i) -
          (barField G Dn.Ψ φn x i - barField G Dr.Ψ φr x i)) =
        fun i => ((barField G Dc.Ψ φc y i - barField G Dr.Ψ φr y i) -
          (barField G Dc.Ψ φc x i - barField G Dr.Ψ φr x i)) +
          ((fun i => svec G F y i - svec G F x i) i +
            (fun i => if y ∈ G.Ω 1 then (0 : ℂ) else ζ * Dc.Ψ y i) i) := by
      funext i
      have h1 := bar_diff_scaled hΨn φn φc hy i
      have h2 := bar_diff_scaled hΨn φn φc hxd i
      simp only [hx, ↓reduceIte, add_zero] at h2
      simp only
      linear_combination h1 - h2
    rw [e]
    have h1 := vn_add' (fun i => ((barField G Dc.Ψ φc y i - barField G Dr.Ψ φr y i) -
          (barField G Dc.Ψ φc x i - barField G Dr.Ψ φr x i)))
      (fun i => (svec G F y i - svec G F x i) +
        (if y ∈ G.Ω 1 then (0 : ℂ) else ζ * Dc.Ψ y i))
    have h2 := vn_add' (fun i => svec G F y i - svec G F x i)
      (fun i => if y ∈ G.Ω 1 then (0 : ℂ) else ζ * Dc.Ψ y i)
    have h3 : vn (fun i => svec G F y i - svec G F x i) ≤ N * (V / G.spacing x) :=
      vn_le_card_mul (by positivity) fun i => by
        rw [le_div_iff₀ hℓ]; rw [mul_comm]; exact hcomp i
    have h4 := ht y hy
    have key : N * (V / G.spacing x) + (if y ∈ G.Ω 1 then 0 else 3 * ‖ζ‖) ≤
        σ * (ε' - ε) / G.spacing x := by
      by_cases hy1 : y ∈ G.Ω 1
      · simp only [hy1, ↓reduceIte, add_zero]
        rw [← mul_div_assoc, div_le_div_iff_of_pos_right hℓ]
        nlinarith
      · simp only [hy1, ↓reduceIte]
        have hℓL := spacing_le_of_adj_not_mem G hϱ hL1 hx hy1 hadj
        rw [← mul_div_assoc, div_add' _ _ _ hℓ.ne', div_le_div_iff_of_pos_right hℓ]
        nlinarith
    have h5 : vn (fun i => (svec G F y i - svec G F x i) +
        (if y ∈ G.Ω 1 then (0 : ℂ) else ζ * Dc.Ψ y i)) ≤
        N * (V / G.spacing x) + (if y ∈ G.Ω 1 then 0 else 3 * ‖ζ‖) := by
      refine h2.trans (add_le_add h3 ?_)
      by_cases hy1 : y ∈ G.Ω 1
      · simp only [hy1, ↓reduceIte]
        exact le_of_eq vn_zero
      · simp only [hy1, ↓reduceIte]
        have := ht y hy; simp only [hy1, ↓reduceIte] at this; exact this
    have : σ * ε' / G.spacing x = σ * ε / G.spacing x + σ * (ε' - ε) / G.spacing x := by
      field_simp; ring
    rw [this]
    linarith
  have hinfo : ∀ y ∈ dataSites G, ∀ i, ‖(if y ∈ G.Ω 1 then (0 : ℂ) else ζ * Dc.Ψ y i)‖ ≤ 3 * ‖ζ‖ :=
    fun y hy i => (norm_le_vn (fun i => if y ∈ G.Ω 1 then (0 : ℂ) else ζ * Dc.Ψ y i) i).trans (ht y hy)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- grad
    intro x hx μ
    obtain ⟨h1, h2⟩ := hB.grad x hx μ
    obtain ⟨n1, n2⟩ := nbr_mem_dataSites hx μ
    refine ⟨gradDir x hx _ n1 (adj_add_single x μ) (fun i => hsup.fwd x hx μ i) h1,
      gradDir x hx _ n2 (adj_sub_single x μ) (fun i => hsup.bwd x hx μ i) h2⟩
  · -- lap
    intro x hx
    have hℓ : 0 < G.spacing x := spacing_pos G
    have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    set F := φn - φc
    have hold := hB.lap x hx
    have hnb := fun μ : Fin d => nbr_mem_dataSites hx μ
    set extra : Fin N → ℂ := fun i => ∑ μ : Fin d,
      (((svec G F (x + Pi.single μ 1) i +
          (if x + Pi.single μ 1 ∈ G.Ω 1 then (0 : ℂ) else ζ * Dc.Ψ (x + Pi.single μ 1) i)) +
        (svec G F (x - Pi.single μ 1) i +
          (if x - Pi.single μ 1 ∈ G.Ω 1 then (0 : ℂ) else ζ * Dc.Ψ (x - Pi.single μ 1) i))) -
        2 * svec G F x i) with hextra
    have e : (fun i => ∑ μ : Fin d,
        ((barField G Dn.Ψ φn (x + Pi.single μ 1) i - barField G Dr.Ψ φr (x + Pi.single μ 1) i) +
          (barField G Dn.Ψ φn (x - Pi.single μ 1) i - barField G Dr.Ψ φr (x - Pi.single μ 1) i) -
          2 * (barField G Dn.Ψ φn x i - barField G Dr.Ψ φr x i))) =
        fun i => (∑ μ : Fin d,
        ((barField G Dc.Ψ φc (x + Pi.single μ 1) i - barField G Dr.Ψ φr (x + Pi.single μ 1) i) +
          (barField G Dc.Ψ φc (x - Pi.single μ 1) i - barField G Dr.Ψ φr (x - Pi.single μ 1) i) -
          2 * (barField G Dc.Ψ φc x i - barField G Dr.Ψ φr x i))) + extra i := by
      funext i
      rw [hextra]
      simp only []
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      have h1 := bar_diff_scaled hΨn φn φc (hnb μ).1 i
      have h2 := bar_diff_scaled hΨn φn φc (hnb μ).2 i
      have h3 := bar_diff_scaled hΨn φn φc hxd i
      simp only [hx, ↓reduceIte, add_zero] at h3
      linear_combination h1 + h2 - 2 * h3
    -- the bound of the extra part
    have hcomp : ∀ i, ‖extra i‖ ≤ (V + 6 * d * ‖ζ‖ * (L : ℝ) ^ 2) / G.spacing x ^ 2 := by
      intro i
      have hA : ‖∑ μ : Fin d, (svec G F (x + Pi.single μ 1) i + svec G F (x - Pi.single μ 1) i -
          2 * svec G F x i)‖ ≤ V / G.spacing x ^ 2 := by
        have := hsup.lap x hx i
        have e2 : ∑ μ : Fin d, (svec G F (x + Pi.single μ 1) i + svec G F (x - Pi.single μ 1) i -
            2 * svec G F x i) = -∑ μ : Fin d, (2 * svec G F x i - svec G F (x + Pi.single μ 1) i -
            svec G F (x - Pi.single μ 1) i) := by
          rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun μ _ => by ring
        rw [e2, norm_neg, le_div_iff₀ (by positivity)]
        linarith
      have hB' : G.spacing x ^ 2 * ‖∑ μ : Fin d,
          ((if x + Pi.single μ 1 ∈ G.Ω 1 then (0 : ℂ) else ζ * Dc.Ψ (x + Pi.single μ 1) i) +
          (if x - Pi.single μ 1 ∈ G.Ω 1 then (0 : ℂ) else ζ * Dc.Ψ (x - Pi.single μ 1) i))‖ ≤
          6 * d * ‖ζ‖ * (L : ℝ) ^ 2 := by
        by_cases hall : ∀ μ : Fin d, x + Pi.single μ 1 ∈ G.Ω 1 ∧ x - Pi.single μ 1 ∈ G.Ω 1
        · have : ∑ μ : Fin d, ((if x + Pi.single μ 1 ∈ G.Ω 1 then (0 : ℂ) else
              ζ * Dc.Ψ (x + Pi.single μ 1) i) + (if x - Pi.single μ 1 ∈ G.Ω 1 then (0 : ℂ) else
              ζ * Dc.Ψ (x - Pi.single μ 1) i)) = 0 :=
            Finset.sum_eq_zero fun μ _ => by simp [(hall μ).1, (hall μ).2]
          rw [this, norm_zero, mul_zero]; positivity
        · push Not at hall
          obtain ⟨μ, hμ⟩ := hall
          have hℓL : G.spacing x ≤ L := by
            by_cases h1 : x + Pi.single μ 1 ∈ G.Ω 1
            · exact spacing_le_of_adj_not_mem G hϱ hL1 hx (hμ h1) (adj_sub_single x μ)
            · exact spacing_le_of_adj_not_mem G hϱ hL1 hx h1 (adj_add_single x μ)
          have hb : ‖∑ μ : Fin d, ((if x + Pi.single μ 1 ∈ G.Ω 1 then (0 : ℂ) else
              ζ * Dc.Ψ (x + Pi.single μ 1) i) + (if x - Pi.single μ 1 ∈ G.Ω 1 then (0 : ℂ) else
              ζ * Dc.Ψ (x - Pi.single μ 1) i))‖ ≤ 6 * d * ‖ζ‖ := by
            calc _ ≤ ∑ μ : Fin d, (3 * ‖ζ‖ + 3 * ‖ζ‖) :=
                  (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ =>
                    (norm_add_le _ _).trans (add_le_add (hinfo _ (hnb μ).1 i) (hinfo _ (hnb μ).2 i)))
              _ = 6 * d * ‖ζ‖ := by simp; ring
          calc G.spacing x ^ 2 * _ ≤ (L : ℝ) ^ 2 * (6 * d * ‖ζ‖) :=
                mul_le_mul (pow_le_pow_left₀ hℓ.le hℓL 2) hb (norm_nonneg _) (by positivity)
            _ = 6 * d * ‖ζ‖ * (L : ℝ) ^ 2 := by ring
      have hsplit : extra i = (∑ μ : Fin d, (svec G F (x + Pi.single μ 1) i +
          svec G F (x - Pi.single μ 1) i - 2 * svec G F x i)) + ∑ μ : Fin d,
          ((if x + Pi.single μ 1 ∈ G.Ω 1 then (0 : ℂ) else ζ * Dc.Ψ (x + Pi.single μ 1) i) +
          (if x - Pi.single μ 1 ∈ G.Ω 1 then (0 : ℂ) else ζ * Dc.Ψ (x - Pi.single μ 1) i)) := by
        rw [hextra, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun μ _ => by ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      rw [le_div_iff₀ (by positivity)] at hA ⊢
      nlinarith [norm_nonneg (∑ μ : Fin d, (svec G F (x + Pi.single μ 1) i +
          svec G F (x - Pi.single μ 1) i - 2 * svec G F x i))]
    have hvn : vn extra ≤ N * ((V + 6 * d * ‖ζ‖ * (L : ℝ) ^ 2) / G.spacing x ^ 2) :=
      vn_le_card_mul (by positivity) hcomp
    rw [e]
    have h1 := vn_add' (fun i => ∑ μ : Fin d,
        ((barField G Dc.Ψ φc (x + Pi.single μ 1) i - barField G Dr.Ψ φr (x + Pi.single μ 1) i) +
          (barField G Dc.Ψ φc (x - Pi.single μ 1) i - barField G Dr.Ψ φr (x - Pi.single μ 1) i) -
          2 * (barField G Dc.Ψ φc x i - barField G Dr.Ψ φr x i))) extra
    have h2 : (N : ℝ) * ((V + 6 * d * ‖ζ‖ * (L : ℝ) ^ 2) / G.spacing x ^ 2) ≤
        σ ^ 2 * (ε' - ε) / G.spacing x ^ 2 := by
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)]
      nlinarith
    have : σ ^ 2 * ε' / G.spacing x ^ 2 =
        σ ^ 2 * ε / G.spacing x ^ 2 + σ ^ 2 * (ε' - ε) / G.spacing x ^ 2 := by
      field_simp; ring
    rw [this]
    linarith
  · -- mult
    intro x
    have h1 := hB.mult x
    have h2 := hsm x
    simp only [Pi.sub_apply] at h2
    have e : αn x - αr x = (αn x - αc x) + (αc x - αr x) := by ring
    rw [e]
    have hsp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
    calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖(αn x - αc x) + (αc x - αr x)‖
        ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * (‖αn x - αc x‖ + ‖αc x - αr x‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hsp
      _ < σ ^ 2 * ε' := by rw [mul_add]; nlinarith
  · -- val
    intro x
    have h1 := hB.val x
    have e : (fun i => φn (x, i) - φr (x, i)) =
        (fun i => φc (x, i) - φr (x, i)) + (fun i => φn (x, i) - φc (x, i)) := by
      funext i; simp
    rw [e]
    have h2 := vn_add (fun i => φc (x, i) - φr (x, i)) (fun i => φn (x, i) - φc (x, i))
    have h3 : vn (fun i => φn (x, i) - φc (x, i)) ≤ N * V :=
      vn_le_card_mul hV fun i => by
        have := hsupn x i
        simpa [svec, zeroExt, Pi.sub_apply] using this
    linarith
  · -- close
    intro x hx
    have h1 := hB.close x hx
    have hxd0 : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    have e0 : (fun i => Ψ''n x i - blockAvg G (φn - φr) x i) =
        fun i => (Ψ'' x i + ζ * Dc.Ψ x i) - blockAvg G (φn - φr) x i := by
      funext i; rw [hΨ''n x hxd0 i]
    rw [e0]
    have hφ : φn - φr = (φc - φr) + (φn - φc) := by funext p; simp
    have e : (fun i => (Ψ'' x i + ζ * Dc.Ψ x i) - blockAvg G (φn - φr) x i) =
        fun i => (Ψ'' x i - blockAvg G (φc - φr) x i) +
          (ζ * Dc.Ψ x i - blockAvg G (φn - φc) x i) := by
      funext i
      rw [hφ, blockAvg_add]; ring
    rw [e]
    have h2 := vn_add' (fun i => Ψ'' x i - blockAvg G (φc - φr) x i)
      (fun i => ζ * Dc.Ψ x i - blockAvg G (φn - φc) x i)
    have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    have h3 : vn (fun i => ζ * Dc.Ψ x i - blockAvg G (φn - φc) x i) ≤ N * (3 * ‖ζ‖ + V) :=
      vn_le_card_mul (by positivity) fun i => by
        refine (norm_sub_le _ _).trans (add_le_add ?_ (norm_blockAvg_le hsupn hx i))
        rw [norm_mul]
        have := (norm_le_vn (Dc.Ψ x) i).trans (hvΨ x hxd)
        nlinarith
    linarith
  · -- collarBond
    intro z hz z' hz' hadj
    have h1 := hB.collarBond z hz z' hz' hadj
    have hzd : z ∈ dataSites G := (mem_dataSites G).2 (Or.inr hz)
    have hzd' : z' ∈ dataSites G := (mem_dataSites G).2 (Or.inr hz')
    have e0 : (fun i => Ψ''n z i - Ψ''n z' i) =
        fun i => (Ψ'' z i + ζ * Dc.Ψ z i) - (Ψ'' z' i + ζ * Dc.Ψ z' i) := by
      funext i; rw [hΨ''n z hzd i, hΨ''n z' hzd' i]
    rw [e0]
    have e : (fun i => (Ψ'' z i + ζ * Dc.Ψ z i) - (Ψ'' z' i + ζ * Dc.Ψ z' i)) =
        fun i => (Ψ'' z i - Ψ'' z' i) + ζ * (Dc.Ψ z i - Dc.Ψ z' i) := by
      funext i; ring
    rw [e]
    have h2 := vn_add' (fun i => Ψ'' z i - Ψ'' z' i) (fun i => ζ * (Dc.Ψ z i - Dc.Ψ z' i))
    rw [vn_smul_complex] at h2
    have h3 := hcol z hz z' hz' hadj
    nlinarith
  · -- hAbs
    intro x hx
    have h1 := hB.hAbs x hx
    have e : (σ * ε) ^ 2 / ε = σ ^ 2 * ε := by field_simp
    have e' : (σ * ε') ^ 2 / ε' = σ ^ 2 * ε' := by
      have : 0 < ε' := by linarith
      field_simp
    rw [e'] at *
    rw [e] at h1
    nlinarith [sq_nonneg σ]
  · -- hDot
    intro x
    have h1 := hB.hDot x
    have : (σ * ε) ^ 2 ≤ (σ * ε') ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hε hσ.le) 2
    linarith

end Balaban.SmallField
