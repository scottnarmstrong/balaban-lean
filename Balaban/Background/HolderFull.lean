/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.ApproxSecond
public import Balaban.Background.Holder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# I-1(e): the Hölder bound for the full background field

* `lattice_path`: summation of unit-step increments along a coordinate-monotone lattice path;
* `holderSeminormLE_of_bounds`: the Hölder seminorm `|g|_{(θ),2-θ}` of a function with
  `ℓ |∂ g| ≤ K₁` and `ℓ² |Δ_μ ∂_ν g| ≤ K₂` (at sites of layer `≥ 2`) is at most
  `max (L²(L+1) K₁, K₂ L² d)`: for `‖z‖ ≳ ℓ(x)` by the sup bound, for `‖z‖ < ℓ(x)` by summing the
  mixed second differences along a lattice path from `x` to `x + z`;
* `approxField_holder`: the Hölder seminorm of `φ₀ = approxField` is at most `C δ`
  (from `phi0_isSmoothField` and `phi0_sq`);
* `bgFieldExt`, `bgFieldC_holder`: the Hölder bound for `bgFieldC` itself, extended to the collar
  by the approximate field.

**Remark (the extension to the collar).**  With the zero extension `svec` outside `Ω₁` the bound for
the field itself is false: for a layer-one site `x` with a collar neighbour, the bond function
`g(x) = φ̃(x + e_ν) - φ̃(x) = -φ(x)` has size `≈ 1` while `g(x') = O(δ)` at an interior site `x'` of the
same block.  The Hölder seminorm of the field is therefore taken with its boundary values on the
collar `C`, namely the values `φ^z` of the approximate field there (`bgFieldExt`).  The increment
`φ - φ₀` vanishes on `C` and its zero extension is the one of `bgFieldC_increment_holder`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

section Path

variable {d : ℕ}

theorem norm_sub_single_le (z : Fin d → ℤ) (μ : Fin d) (s : ℤ)
    (hsg : (z μ - s).natAbs ≤ (z μ).natAbs) : ‖z - Pi.single μ s‖ ≤ ‖z‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro j
  by_cases hj : j = μ
  · subst hj
    simp only [Pi.sub_apply, Pi.single_eq_same, Int.norm_eq_abs]
    have h2 : |(z j : ℝ)| ≤ ‖z‖ := by
      have := norm_le_pi_norm z j
      rwa [Int.norm_eq_abs] at this
    have h3 : |((z j - s : ℤ) : ℝ)| ≤ |(z j : ℝ)| := by
      rw [← Int.cast_abs, ← Int.cast_abs]
      rw [← Int.natCast_natAbs, ← Int.natCast_natAbs]
      exact_mod_cast hsg
    exact h3.trans h2
  · simp only [Pi.sub_apply, Pi.single_eq_of_ne hj, sub_zero]
    exact norm_le_pi_norm z j

theorem sum_natAbs_step (z : Fin d → ℤ) (μ : Fin d) (s : ℤ)
    (hsg : (z μ - s).natAbs + 1 = (z μ).natAbs) :
    ∑ j, ((z - Pi.single μ s : Fin d → ℤ) j).natAbs + 1 = ∑ j, (z j).natAbs := by
  have e : (z μ).natAbs + ∑ j ∈ Finset.univ.erase μ, (z j).natAbs = ∑ j, (z j).natAbs :=
    Finset.add_sum_erase Finset.univ (fun j => (z j).natAbs) (Finset.mem_univ μ)
  have e' : ((z - Pi.single μ s : Fin d → ℤ) μ).natAbs +
      ∑ j ∈ Finset.univ.erase μ, ((z - Pi.single μ s : Fin d → ℤ) j).natAbs =
      ∑ j, ((z - Pi.single μ s : Fin d → ℤ) j).natAbs :=
    Finset.add_sum_erase Finset.univ (fun j => ((z - Pi.single μ s : Fin d → ℤ) j).natAbs)
      (Finset.mem_univ μ)
  have hrest : ∑ j ∈ Finset.univ.erase μ, ((z - Pi.single μ s : Fin d → ℤ) j).natAbs =
      ∑ j ∈ Finset.univ.erase μ, (z j).natAbs := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have : j ≠ μ := (Finset.mem_erase.1 hj).1
    simp [Pi.single_eq_of_ne this]
  have hμ : (z - Pi.single μ s : Fin d → ℤ) μ = z μ - s := by simp
  rw [hμ, hrest] at e'
  omega

/-- Increments of a function on `ℤ^d` along unit steps within a box add up along a
coordinate-monotone path from `0` to `z`. -/
theorem lattice_path (F : (Fin d → ℤ) → ℂ) {R c : ℝ}
    (hstep : ∀ (w : Fin d → ℤ) (μ : Fin d), ‖w‖ ≤ R → ‖w + Pi.single μ 1‖ ≤ R →
      ‖F (w + Pi.single μ 1) - F w‖ ≤ c) :
    ∀ (m : ℕ) (z : Fin d → ℤ), ∑ μ, (z μ).natAbs = m → ‖z‖ ≤ R → ‖F z - F 0‖ ≤ c * m := by
  intro m
  induction m with
  | zero =>
    intro z hz _
    have : z = 0 := by
      funext j
      have := (Finset.sum_eq_zero_iff.1 hz) j (Finset.mem_univ j)
      simpa using this
    subst this
    simp
  | succ m ih =>
    intro z hz hzR
    have hex : ∃ μ, z μ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      simp [hcon] at hz
    obtain ⟨μ, hμ⟩ := hex
    -- one step `z' = z - sign(z μ) e_μ` towards `0`
    have step : ∃ z' : Fin d → ℤ, ∑ j, (z' j).natAbs = m ∧ ‖z'‖ ≤ ‖z‖ ∧
        ‖F z - F z'‖ ≤ c := by
      rcases lt_or_gt_of_ne hμ with hneg | hpos
      · have hsg : (z μ - (-1)).natAbs + 1 = (z μ).natAbs := by omega
        have hn := norm_sub_single_le z μ (-1) (by omega)
        have e : z - Pi.single μ (-1 : ℤ) = z + Pi.single μ 1 := by
          rw [Pi.single_neg, sub_neg_eq_add]
        refine ⟨z - Pi.single μ (-1), ?_, hn, ?_⟩
        · have := sum_natAbs_step z μ (-1) hsg
          omega
        · rw [e, norm_sub_rev]
          rw [e] at hn
          exact hstep z μ hzR (hn.trans hzR)
      · have hsg : (z μ - 1).natAbs + 1 = (z μ).natAbs := by omega
        have hn := norm_sub_single_le z μ 1 (by omega)
        refine ⟨z - Pi.single μ 1, ?_, hn, ?_⟩
        · have := sum_natAbs_step z μ 1 hsg
          omega
        · have := hstep (z - Pi.single μ 1) μ (hn.trans hzR) (by rw [sub_add_cancel]; exact hzR)
          rwa [sub_add_cancel] at this
    obtain ⟨z', hz', hnz', hc⟩ := step
    have ih' := ih z' hz' (hnz'.trans hzR)
    calc ‖F z - F 0‖ ≤ ‖F z - F z'‖ + ‖F z' - F 0‖ := by
          have := norm_add_le (F z - F z') (F z' - F 0)
          rwa [sub_add_sub_cancel] at this
      _ ≤ c + c * m := add_le_add hc ih'
      _ = c * ((m + 1 : ℕ) : ℝ) := by push_cast; ring

end Path

section Power

theorem rp_large {s Z θ : ℝ} (hs : 1 ≤ s) (hZ : s ≤ Z) (hθ1 : θ ≤ 1) :
    s ^ (2 - θ) * (Z ^ (1 - θ))⁻¹ ≤ s := by
  have hs0 : 0 < s := by linarith
  have h1 : s ^ (1 - θ) ≤ Z ^ (1 - θ) := Real.rpow_le_rpow hs0.le hZ (by linarith)
  have h2 : 0 < s ^ (1 - θ) := Real.rpow_pos_of_pos hs0 _
  have h3 : s ^ (2 - θ) = s * s ^ (1 - θ) := by
    have : (2 : ℝ) - θ = 1 + (1 - θ) := by ring
    rw [this, Real.rpow_add hs0, Real.rpow_one]
  calc s ^ (2 - θ) * (Z ^ (1 - θ))⁻¹ ≤ s ^ (2 - θ) * (s ^ (1 - θ))⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ h2 h1) (Real.rpow_nonneg hs0.le _)
    _ = s := by rw [h3]; field_simp

theorem rp_small {s θ : ℝ} (hs : 1 ≤ s) (hθ0 : 0 ≤ θ) : s ^ (2 - θ) ≤ s * s := by
  have hs0 : 0 < s := by linarith
  have h3 : s ^ (2 - θ) = s * s ^ (1 - θ) := by
    have : (2 : ℝ) - θ = 1 + (1 - θ) := by ring
    rw [this, Real.rpow_add hs0, Real.rpow_one]
  have h4 : s ^ (1 - θ) ≤ s ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hs (by linarith)
  rw [Real.rpow_one] at h4
  rw [h3]
  exact mul_le_mul_of_nonneg_left h4 hs0.le

theorem rp_mid {s Z θ : ℝ} (hs : 1 ≤ s) (hZ1 : 1 ≤ Z) (hZs : Z ≤ s) (hθ0 : 0 ≤ θ) : s ^ (2 - θ) * (Z ^ (1 - θ))⁻¹ * Z ≤ s * s := by
  have hs0 : 0 < s := by linarith
  have hZ0 : 0 < Z := by linarith
  have h1 : Z ^ (1 - θ) * Z ^ θ = Z := by
    rw [← Real.rpow_add hZ0]; simp
  have h2 : 0 < Z ^ (1 - θ) := Real.rpow_pos_of_pos hZ0 _
  have h3 : (Z ^ (1 - θ))⁻¹ * Z = Z ^ θ := by
    calc (Z ^ (1 - θ))⁻¹ * Z = (Z ^ (1 - θ))⁻¹ * (Z ^ (1 - θ) * Z ^ θ) := by rw [h1]
      _ = Z ^ θ := by field_simp
  have h4 : Z ^ θ ≤ s ^ θ := Real.rpow_le_rpow hZ0.le hZs hθ0
  have h5 : s ^ (2 - θ) * s ^ θ = s * s := by
    rw [← Real.rpow_add hs0]
    have : (2 : ℝ) - θ + θ = 2 := by ring
    rw [this]; norm_num [Real.rpow_two, sq]
  calc s ^ (2 - θ) * (Z ^ (1 - θ))⁻¹ * Z = s ^ (2 - θ) * ((Z ^ (1 - θ))⁻¹ * Z) := by ring
    _ = s ^ (2 - θ) * Z ^ θ := by rw [h3]
    _ ≤ s ^ (2 - θ) * s ^ θ := mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hs0.le _)
    _ = s * s := h5

end Power

section Reduction

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}

/-- **The Hölder reduction.**  A function with `ℓ |∂ g| ≤ K₁` at all sites of `Ω₁` and
`ℓ² |Δ_μ ∂_τ g| ≤ K₂` (unit squares based at sites of layer `≥ 2`) has
`|g|_{(θ),2-θ} ≤ max (L² (L+1) K₁, K₂ L² d)`. -/
theorem holder_of_bounds (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 2 ≤ L)
    {g : Torus d (N₀ * L ^ k) → ℂ} {K1 K2 : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hsup : ∀ y ∈ G.Ω 1, ∀ τ : Fin d, ‖g (y + Pi.single τ 1) - g y‖ ≤ K1 / G.spacing y)
    (hsq : ∀ y ∈ G.Ω 1, 2 ≤ G.layerIndex y → ∀ μ τ : Fin d,
      ‖g (y + Pi.single μ 1 + Pi.single τ 1) - g (y + Pi.single μ 1) - g (y + Pi.single τ 1) +
        g y‖ ≤ K2 / G.spacing y ^ 2)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    HolderSeminormLE G g θ (2 - θ)
      (max (((L : ℝ) ^ 2 * ((L : ℝ) + 1)) * K1) (K2 * (L : ℝ) ^ 2 * d)) := by
  intro x hx x' hx' hne z hz τ
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hρ : (d : ℝ) < ϱ := by nlinarith
  obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hx
  set n := G.layerIndex x with hn
  set s := G.spacing x with hsdef
  have hsn : s = (L : ℝ) ^ n := rfl
  have hs1 : (1 : ℝ) ≤ s := by rw [hsn]; exact one_le_pow₀ hL1
  have hs0 : 0 < s := by linarith
  have hx'Ω : x' ∈ G.Ω 1 := hx'.1
  have hlay := layer_le_of_tildeDelta G hρ hx hx'
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hne (by rw [← hz]; exact (liftPt_zero x).symm)
  have hZ1 : 1 ≤ ‖z‖ := one_le_norm_of_ne_zero hz0
  set Z := ‖z‖ with hZ
  have hZ0 : 0 < Z := by linarith
  -- the sup bound for the difference
  have hsp' : s ≤ L * G.spacing x' := by
    have : (L : ℝ) ^ n ≤ (L : ℝ) ^ (G.layerIndex x' + 1) := pow_le_pow_right₀ hL1 hlay
    unfold GeneratingSet.spacing
    rw [hsn]
    calc (L : ℝ) ^ n ≤ (L : ℝ) ^ (G.layerIndex x' + 1) := this
      _ = L * (L : ℝ) ^ G.layerIndex x' := by ring
  have hsp0 : 0 < G.spacing x' := by unfold GeneratingSet.spacing; positivity
  have hΔ : ‖(g (x' + Pi.single τ 1) - g x') - (g (x + Pi.single τ 1) - g x)‖ ≤
      K1 * (L + 1) / s := by
    refine (norm_sub_le _ _).trans ?_
    have a1 := hsup x' hx'Ω τ
    have a2 := hsup x hx τ
    have b1 : K1 / G.spacing x' ≤ K1 * L / s := by
      rw [div_le_div_iff₀ hsp0 hs0]
      nlinarith
    have : K1 * (L + 1) / s = K1 * L / s + K1 / s := by ring
    rw [this]
    exact add_le_add (a1.trans b1) a2
  have hΔ0 := norm_nonneg ((g (x' + Pi.single τ 1) - g x') - (g (x + Pi.single τ 1) - g x))
  set Δ := ‖(g (x' + Pi.single τ 1) - g x') - (g (x + Pi.single τ 1) - g x)‖ with hΔdef
  have hM1 : ((L : ℝ) ^ 2 * ((L : ℝ) + 1)) * K1 ≤
      max (((L : ℝ) ^ 2 * ((L : ℝ) + 1)) * K1) (K2 * (L : ℝ) ^ 2 * d) := le_max_left _ _
  have hM2 : K2 * (L : ℝ) ^ 2 * d ≤
      max (((L : ℝ) ^ 2 * ((L : ℝ) + 1)) * K1) (K2 * (L : ℝ) ^ 2 * d) := le_max_right _ _
  have hpos : 0 ≤ (Z ^ (1 - θ))⁻¹ := inv_nonneg.2 (Real.rpow_nonneg hZ0.le _)
  by_cases hC : 3 ≤ n ∧ Z < s
  · -- the path argument
    obtain ⟨hn3, hZs⟩ := hC
    set F : (Fin d → ℤ) → ℂ := fun w => g (liftPt x w + Pi.single τ 1) - g (liftPt x w) with hF
    have hc0 : 0 ≤ K2 * (L : ℝ) ^ 2 / s ^ 2 := by positivity
    have hstep : ∀ (w : Fin d → ℤ) (μ : Fin d), ‖w‖ ≤ Z → ‖w + Pi.single μ 1‖ ≤ Z →
        ‖F (w + Pi.single μ 1) - F w‖ ≤ K2 * (L : ℝ) ^ 2 / s ^ 2 := by
      intro w μ hw _
      set p := liftPt x w with hp
      have hdist : Green.torusDist d (N₀ * L ^ k) x p ≤ 4 * d * (L : ℝ) ^ n := by
        have h1 := torusDist_liftPt_le x w
        have h2 : (d : ℝ) * ‖w‖ ≤ d * s :=
          mul_le_mul_of_nonneg_left (hw.trans hZs.le) (by positivity)
        rw [← hsn] at *
        nlinarith
      have hpΩ : p ∈ G.Ω (n - 1) :=
        mem_pred_of_dist_le G hϱ (by omega) hnk (G.mem_layer.1 hxl).1 hdist
      have hp1 : p ∈ G.Ω 1 := G.Ω_antitone le_rfl (by omega) (by omega) hpΩ
      have hm := (mem_Ω_iff_le_layerIndex G hp1 (by omega) (by omega)).1 hpΩ
      have hsqp := hsq p hp1 (by omega) μ τ
      have hsp : s ≤ L * G.spacing p := by
        have : (L : ℝ) ^ n ≤ (L : ℝ) ^ (G.layerIndex p + 1) := pow_le_pow_right₀ hL1 (by omega)
        unfold GeneratingSet.spacing
        rw [hsn]
        calc (L : ℝ) ^ n ≤ (L : ℝ) ^ (G.layerIndex p + 1) := this
          _ = L * (L : ℝ) ^ G.layerIndex p := by ring
      have hspp : 0 < G.spacing p := by unfold GeneratingSet.spacing; positivity
      have hF1 : F (w + Pi.single μ 1) - F w =
          g (p + Pi.single μ 1 + Pi.single τ 1) - g (p + Pi.single μ 1) -
            g (p + Pi.single τ 1) + g p := by
        simp only [hF, liftPt_add_single, hp]; ring
      rw [hF1]
      refine hsqp.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : s ^ 2 ≤ (L * G.spacing p) ^ 2 := pow_le_pow_left₀ hs0.le hsp 2
      nlinarith
    have hmz := lattice_path F hstep _ z rfl le_rfl
    have hsum : (∑ μ, (z μ).natAbs : ℕ) ≤ (d : ℝ) * Z := by
      have : ∀ μ, ((z μ).natAbs : ℝ) ≤ Z := fun μ => by
        have h := norm_le_pi_norm z μ
        rw [Int.norm_eq_abs] at h
        rwa [Nat.cast_natAbs, Int.cast_abs]
      push_cast
      calc ∑ μ, ((z μ).natAbs : ℝ) ≤ ∑ _μ : Fin d, Z := Finset.sum_le_sum fun μ _ => this μ
        _ = d * Z := by simp
    have hΔF : Δ = ‖F z - F 0‖ := by
      simp only [hΔdef, hF, hz, liftPt_zero]
    have hΔle : Δ ≤ K2 * (L : ℝ) ^ 2 / s ^ 2 * (d * Z) := by
      rw [hΔF]
      exact hmz.trans (mul_le_mul_of_nonneg_left hsum hc0)
    have hmid := rp_mid hs1 hZ1 hZs.le hθ0
    calc s ^ (2 - θ) * (Z ^ (1 - θ))⁻¹ * Δ
        ≤ s ^ (2 - θ) * (Z ^ (1 - θ))⁻¹ * (K2 * (L : ℝ) ^ 2 / s ^ 2 * (d * Z)) :=
          mul_le_mul_of_nonneg_left hΔle (mul_nonneg (Real.rpow_nonneg hs0.le _) hpos)
      _ = (s ^ (2 - θ) * (Z ^ (1 - θ))⁻¹ * Z) * (K2 * (L : ℝ) ^ 2 / s ^ 2 * d) := by ring
      _ ≤ (s * s) * (K2 * (L : ℝ) ^ 2 / s ^ 2 * d) :=
          mul_le_mul_of_nonneg_right hmid (by positivity)
      _ = K2 * (L : ℝ) ^ 2 * d := by field_simp
      _ ≤ _ := hM2
  · -- sup bound only
    have hΔ' : s * Δ ≤ K1 * (L + 1) := by
      calc s * Δ ≤ s * (K1 * (L + 1) / s) := mul_le_mul_of_nonneg_left hΔ hs0.le
        _ = K1 * (L + 1) := by field_simp
    have hK1L : K1 * (L + 1) ≤ ((L : ℝ) ^ 2 * ((L : ℝ) + 1)) * K1 := by
      have : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ hL1
      nlinarith [mul_nonneg hK1 (by linarith : (0 : ℝ) ≤ (L : ℝ) + 1)]
    by_cases hsZ : s ≤ Z
    · calc s ^ (2 - θ) * (Z ^ (1 - θ))⁻¹ * Δ ≤ s * Δ :=
            mul_le_mul_of_nonneg_right (rp_large hs1 hsZ hθ1) hΔ0
        _ ≤ _ := (hΔ'.trans hK1L).trans hM1
    · push Not at hsZ
      have hn2 : n ≤ 2 := by
        by_contra hcon
        exact hC ⟨by omega, hsZ⟩
      have hsL : s ≤ (L : ℝ) ^ 2 := by
        rw [hsn]; exact pow_le_pow_right₀ hL1 hn2
      have hinv : (Z ^ (1 - θ))⁻¹ ≤ 1 := by
        have : (1 : ℝ) ≤ Z ^ (1 - θ) := Real.one_le_rpow hZ1 (by linarith)
        exact inv_le_one_of_one_le₀ this
      have h1 : s ^ (2 - θ) * (Z ^ (1 - θ))⁻¹ ≤ s * s :=
        (mul_le_of_le_one_right (Real.rpow_nonneg hs0.le _) hinv).trans (rp_small hs1 hθ0)
      calc s ^ (2 - θ) * (Z ^ (1 - θ))⁻¹ * Δ ≤ (s * s) * Δ :=
            mul_le_mul_of_nonneg_right h1 hΔ0
        _ = s * (s * Δ) := by ring
        _ ≤ s * (K1 * (L + 1)) := mul_le_mul_of_nonneg_left hΔ' hs0.le
        _ ≤ (L : ℝ) ^ 2 * (K1 * (L + 1)) :=
            mul_le_mul_of_nonneg_right hsL (mul_nonneg hK1 (by positivity))
        _ = ((L : ℝ) ^ 2 * ((L : ℝ) + 1)) * K1 := by ring
        _ ≤ _ := hM1

end Reduction

section Apply

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem holder_mono {G : GeneratingSet d L N₀ k ϱ} {g : Torus d (N₀ * L ^ k) → ℂ}
    {θ σ C C' : ℝ} (h : HolderSeminormLE G g θ σ C) (hC : C ≤ C') : HolderSeminormLE G g θ σ C' :=
  fun x hx x' hx' hne z hz ν => (h x hx x' hx' hne z hz ν).trans hC

theorem holder_add {G : GeneratingSet d L N₀ k ϱ} {g₁ g₂ : Torus d (N₀ * L ^ k) → ℂ}
    {θ σ C₁ C₂ : ℝ} (h₁ : HolderSeminormLE G g₁ θ σ C₁) (h₂ : HolderSeminormLE G g₂ θ σ C₂) :
    HolderSeminormLE G (fun y => g₁ y + g₂ y) θ σ (C₁ + C₂) := by
  intro x hx x' hx' hne z hz ν
  have a1 := h₁ x hx x' hx' hne z hz ν
  have a2 := h₂ x hx x' hx' hne z hz ν
  have hnn : 0 ≤ (G.spacing x) ^ σ * (‖z‖ ^ (1 - θ))⁻¹ := by
    have : 0 ≤ G.spacing x := by unfold GeneratingSet.spacing; positivity
    exact mul_nonneg (Real.rpow_nonneg this _) (inv_nonneg.2 (Real.rpow_nonneg (norm_nonneg _) _))
  have e : ((g₁ (x' + Pi.single ν 1) + g₂ (x' + Pi.single ν 1)) - (g₁ x' + g₂ x')) -
      ((g₁ (x + Pi.single ν 1) + g₂ (x + Pi.single ν 1)) - (g₁ x + g₂ x)) =
      ((g₁ (x' + Pi.single ν 1) - g₁ x') - (g₁ (x + Pi.single ν 1) - g₁ x)) +
      ((g₂ (x' + Pi.single ν 1) - g₂ x') - (g₂ (x + Pi.single ν 1) - g₂ x)) := by ring
  rw [e]
  calc (G.spacing x) ^ σ * (‖z‖ ^ (1 - θ))⁻¹ * ‖_ + _‖ ≤
      (G.spacing x) ^ σ * (‖z‖ ^ (1 - θ))⁻¹ * (‖(g₁ (x' + Pi.single ν 1) - g₁ x') -
        (g₁ (x + Pi.single ν 1) - g₁ x)‖ + ‖(g₂ (x' + Pi.single ν 1) - g₂ x') -
        (g₂ (x + Pi.single ν 1) - g₂ x)‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hnn
    _ = (G.spacing x) ^ σ * (‖z‖ ^ (1 - θ))⁻¹ * ‖(g₁ (x' + Pi.single ν 1) - g₁ x') -
        (g₁ (x + Pi.single ν 1) - g₁ x)‖ + (G.spacing x) ^ σ * (‖z‖ ^ (1 - θ))⁻¹ *
        ‖(g₂ (x' + Pi.single ν 1) - g₂ x') - (g₂ (x + Pi.single ν 1) - g₂ x)‖ := by ring
    _ ≤ C₁ + C₂ := add_le_add a1 a2

theorem norm_le_cNorm (v : Fin N → ℂ) (i : Fin N) : ‖v i‖ ≤ cNorm v := norm_le_vn v i

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν δ ε : ℝ} {D : BgData G N}

/-- The constant of the Hölder bound of `φ₀`, a function of `(d, L)` only. -/
noncomputable def cHold (d L : ℕ) : ℝ :=
  max (((L : ℝ) ^ 2 * ((L : ℝ) + 1)) * cSm d L) (cMix d L * (L : ℝ) ^ 2 * d)

/-- **The Hölder seminorm of the approximate field**: `|∂ φ₀ᵢ|_{(θ),2-θ} ≤ C δ`, for every fixed
`θ ∈ [0, 1]`, with `C = cHold d L`. -/
theorem approxField_holder (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D)
    (hs : cA2 d L * δ ≤ 1 / 100) (hδ1 : δ ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (i : Fin N) :
    HolderSeminormLE G (fun y => approxField G a ν D.Ψ D.h y i) θ (2 - θ) (cHold d L * δ) := by
  have hL3 := S.hL
  have hδ0 : 0 ≤ δ := S.hδ0.le
  have hsm := phi0_isSmoothField S W hs hδ1
  have hcS : 0 ≤ cSm d L := by
    have h1 : 0 ≤ cE d L * (L : ℝ) ^ 2 := by have := cE_pos d L; positivity
    exact h1.trans (le_max_of_le_left (le_max_left _ _))
  have hKs : 0 ≤ cSm d L * δ := by positivity
  have hKm : 0 ≤ cMix d L * δ := mul_nonneg (cMix_nonneg d L) hδ0
  have hcomp : ∀ (u v : Torus d (N₀ * L ^ k)), ‖(approxField G a ν D.Ψ D.h u -
      approxField G a ν D.Ψ D.h v) i‖ = ‖approxField G a ν D.Ψ D.h u i -
      approxField G a ν D.Ψ D.h v i‖ := fun u v => by simp
  have hmain := holder_of_bounds (G := G) (g := fun y => approxField G a ν D.Ψ D.h y i)
    (K1 := cSm d L * δ) (K2 := cMix d L * δ) S.hϱ S.hd hL3 hKs hKm
    (fun y hy τ => by
      have h1 := (hsm.grad y hy τ).1
      have h2 := norm_le_cNorm (approxField G a ν D.Ψ D.h (y + Pi.single τ 1) -
        approxField G a ν D.Ψ D.h y) i
      rw [hcomp] at h2
      exact h2.trans h1)
    (fun y hy hy2 μ τ => by
      obtain ⟨hm1, hmk, hyl⟩ := G.layerIndex_spec hy
      have h1 := phi0_sq S W hs hδ1 hy2 hmk hyl μ τ
      have h2 := norm_le_cNorm (approxField G a ν D.Ψ D.h (y + Pi.single μ 1 + Pi.single τ 1) -
        approxField G a ν D.Ψ D.h (y + Pi.single μ 1) -
        approxField G a ν D.Ψ D.h (y + Pi.single τ 1) + approxField G a ν D.Ψ D.h y) i
      have e : ((approxField G a ν D.Ψ D.h (y + Pi.single μ 1 + Pi.single τ 1) -
        approxField G a ν D.Ψ D.h (y + Pi.single μ 1) -
        approxField G a ν D.Ψ D.h (y + Pi.single τ 1) + approxField G a ν D.Ψ D.h y) i) =
        approxField G a ν D.Ψ D.h (y + Pi.single μ 1 + Pi.single τ 1) i -
        approxField G a ν D.Ψ D.h (y + Pi.single μ 1) i -
        approxField G a ν D.Ψ D.h (y + Pi.single τ 1) i + approxField G a ν D.Ψ D.h y i := by simp
      rw [e] at h2
      unfold GeneratingSet.spacing
      exact h2.trans h1)
    hθ0 hθ1
  refine holder_mono hmain (max_le ?_ ?_)
  · calc ((L : ℝ) ^ 2 * ((L : ℝ) + 1)) * (cSm d L * δ) =
        (((L : ℝ) ^ 2 * ((L : ℝ) + 1)) * cSm d L) * δ := by ring
      _ ≤ cHold d L * δ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0
  · calc cMix d L * δ * (L : ℝ) ^ 2 * d = (cMix d L * (L : ℝ) ^ 2 * d) * δ := by ring
      _ ≤ cHold d L * δ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδ0

end Apply

section Final

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The background field with boundary values on the collar.**  On `Ω₁` it is `bgFieldC`; on
the collar `C` (and elsewhere) it is the approximate field `φ₀`, whose values on `C` are the
boundary values `φ^z` of the problem.  The Hölder seminorm of the field is taken for this
extension (the zero extension is not meaningful at the boundary, see the module docstring). -/
noncomputable def bgFieldExt (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν c₀ : ℝ)
    (D : BgData G N) (y : Torus d (N₀ * L ^ k)) (i : Fin N) : ℂ := by
  classical
  exact if h : y ∈ G.Ω 1 then bgFieldC G a ν c₀ D (⟨y, h⟩, i)
    else approxField G a ν D.Ψ D.h y i

/-- **I-1(e), the Hölder bound for the background field itself.**  For a fixed `θ ∈ (0, 1)`, the
field `bgFieldExt` (the small solution `bgFieldC` on `Ω₁`, the boundary values of the approximate
field on the collar) has `|∂φ|_{(θ),2-θ} ≤ ((B/θ)(C₃ + (3/2) K₁) + C_H) δ` componentwise, with
constants depending on `(d, L)` only.  It is the sum of `bgFieldC_increment_holder` (for
`φ - φ₀`) and `approxField_holder` (for `φ₀`, which needs the mixed second differences of `φ₀`,
`phi0_sq`). -/
theorem bgFieldC_holder (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ {N k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ}
      (G : GeneratingSet d L N₀ k ϱ) {a : ℕ → ℝ} {ν : ℝ}, BgHyp d L k ϱ a ν →
      ∀ {D : BgData G N} {δ ε : ℝ}, 0 < δ → δ ≤ ε → ε ≤ bgC0 d L N → δ ≤ bgC1 d L N →
      ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2 → InDomainC G ν δ ε D → ∀ i : Fin N,
      HolderSeminormLE G (fun y => bgFieldExt G a ν (bgC0 d L N) D y i) θ (2 - θ)
        (B / θ * ((lemma53Const d L + 3 / 2 * bgK1 d L N) * δ) + cHold d L * δ) := by
  classical
  obtain ⟨B, hB0, hinc⟩ := bgFieldC_increment_holder (d := d) (L := L) hd hL
  refine ⟨B, hB0, ?_⟩
  intro θ hθ0 hθ1 N k N₀ _ ϱ G a ν H D δ ε hδ0 hδε hε hδ hνε hDC i
  have hd0 : 0 < d := by omega
  have h1 := hinc hθ0 hθ1 G H hδ0 hδε hε hδ hνε hDC i
  obtain ⟨W⟩ := DataWit.exists hDC
  obtain ⟨hδa, -, -, -⟩ := bgC1_facts d L N hd0 hδ
  have hdelta := approxDelta_le d L hδa
  have S : ApproxSetting d L k ϱ a ν δ ε :=
    H.approxSetting hδ0 hδε (hε.trans (bgC0_le d L N)) hdelta.1 hνε
  have h2 := approxField_holder S W hdelta.2 (hdelta.1.trans (by norm_num)) hθ0.le hθ1.le i
  have h3 := holder_add h1 h2
  have e : (fun y => bgFieldExt G a ν (bgC0 d L N) D y i) =
      fun y => svec G (fun p => bgFieldC G a ν (bgC0 d L N) D p -
          approxField G a ν D.Ψ D.h p.1 p.2) y i + approxField G a ν D.Ψ D.h y i := by
    funext y
    by_cases hy : y ∈ G.Ω 1
    · have := svec_of_mem G (fun p => bgFieldC G a ν (bgC0 d L N) D p -
          approxField G a ν D.Ψ D.h p.1 p.2) ⟨y, hy⟩ i
      simp only [bgFieldExt, hy, dite_true]
      rw [this]
      ring
    · have := svec_of_not_mem G (fun p => bgFieldC G a ν (bgC0 d L N) D p -
          approxField G a ν D.Ψ D.h p.1 p.2) hy i
      simp only [bgFieldExt, hy, dite_false]
      rw [this, zero_add]
  rw [e]
  exact h3

end Final

end Balaban.Background
