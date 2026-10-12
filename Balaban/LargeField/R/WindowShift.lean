module

public import Balaban.LargeField.R.WindowErr
public import Balaban.LargeField.R.HatW

/-!
# The deep layers and the mean shift (Part III, Lemmas III.1.7, III.1.7′)

* `layerFrac B n = f_n(z)`, the volume fraction of the leaves of layer `n`; `deepLayer_frac_le` is the
  bound `f_n ≤ ν_max(k) (L M crit_k)^d L^{-(k-n)d}` from the block count of Lemma III.1.2 (c);
* `shiftBar B z = ∑_x w_x |ϖ_{n_x} - 1|` (`\bar ς_z`), bounded by `∑_n f_n ς_n` (`shiftBar_le_layers`);
* `meanShift_le`: `β_k^{1/2} \bar ς_z ≤ C_ς β^{-1/2} λ̂_k^{p₂+2d} L^{-kγ}` (III.1.7).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Finset

namespace BlockTree

variable {m k1 k : ℕ} (B : BlockTree m k1 k)

/-- `f_n(z) = ∑_{x : n_x = n} w_x`, the volume fraction of the leaves of layer `n`. -/
noncomputable def layerFrac (n : ℕ) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : Fin B.nLeaf => B.leafScale x = n), blockFrac m k (B.leafScale x)

theorem layerFrac_eq (n : ℕ) : B.layerFrac n = (B.nLeaves n : ℝ) * blockFrac m k n := by
  unfold layerFrac nLeaves
  rw [Finset.sum_congr rfl (fun _ hx => by rw [(Finset.mem_filter.mp hx).2])]
  simp

theorem layerFrac_nonneg (n : ℕ) : 0 ≤ B.layerFrac n :=
  Finset.sum_nonneg fun _ _ => blockFrac_nonneg _ _ _

/-- `\bar ς_z = ∑_x w_x |ϖ_{n_x} - 1|`. -/
noncomputable def shiftBar (z : ℕ → ℝ) : ℝ :=
  ∑ x : Fin B.nLeaf, blockFrac m k (B.leafScale x) * |varpi k z (B.leafScale x) - 1|

theorem shiftBar_nonneg (z : ℕ → ℝ) : 0 ≤ B.shiftBar z :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (blockFrac_nonneg _ _ _) (abs_nonneg _)

theorem shiftBar_le_layers (z : ℕ → ℝ) (ς : ℕ → ℝ)
    (hς : ∀ n, k1 ≤ n → n < k → |varpi k z n - 1| ≤ ς n) :
    B.shiftBar z ≤ ∑ n ∈ Finset.Ico k1 k, B.layerFrac n * ς n := by
  unfold shiftBar
  rw [← Finset.sum_fiberwise_of_maps_to (g := B.leafScale) (t := Finset.Ico k1 k)
    (s := Finset.univ) (fun x _ => Finset.mem_Ico.mpr ⟨B.leafScale_ge x, B.leafScale_lt x⟩)]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn' := Finset.mem_Ico.mp hn
  unfold layerFrac
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun x hx => ?_
  have hxn : B.leafScale x = n := (Finset.mem_filter.mp hx).2
  rw [hxn]
  exact mul_le_mul_of_nonneg_left (hς n hn'.1 hn'.2) (blockFrac_nonneg _ _ _)

end BlockTree

/-- exponent bookkeeping of (III.1.7) -/
theorem layer_exponent {ℓ : ℝ} (hℓ : 0 < ℓ) (d k n : ℕ) (hnk : n ≤ k) {α γ : ℝ}
    (hα : α + γ = ((d : ℝ) - 2) / 2) :
    ℓ ^ ((k : ℝ) * ((d : ℝ) - 2) / 2) * ℓ ^ (-(((k - n : ℕ) : ℝ) * d)) *
        ℓ ^ (-(((n : ℝ) + 1) * (α + 2 * γ))) =
      ℓ ^ (-(α + 2 * γ)) * ℓ ^ (-((k : ℝ) * γ)) *
        (ℓ ^ (-(((d : ℝ) + 2) / 2 - γ))) ^ (k - n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ.le, ← Real.rpow_add hℓ, ← Real.rpow_add hℓ,
    ← Real.rpow_add hℓ, ← Real.rpow_add hℓ]
  congr 1
  rw [Nat.cast_sub hnk]
  have : (α : ℝ) = ((d : ℝ) - 2) / 2 - γ := by linarith
  subst this
  ring

/-- The sum over the layers `n = k - m`, `m ≥ 1`, of the terms of (III.1.7). -/
theorem layer_sum_le {ℓ : ℝ} (hℓ : 1 < ℓ) (d k k1 : ℕ) {α γ : ℝ} (hα : α + γ = ((d : ℝ) - 2) / 2)
    (he : 0 < ((d : ℝ) + 2) / 2 - γ) {E N C : ℝ} (hE : 0 ≤ E) (hN : 0 ≤ N) (hC : 0 ≤ C) :
    ∑ n ∈ Finset.Ico k1 k,
      (E * ℓ ^ ((k : ℝ) * ((d : ℝ) - 2) / 2)) * (N * ℓ ^ (-(((k - n : ℕ) : ℝ) * d))) *
        (C * ℓ ^ (-(((n : ℝ) + 1) * (α + 2 * γ)))) ≤
      E * N * C * ℓ ^ (-(α + 2 * γ)) * ℓ ^ (-((k : ℝ) * γ)) *
        (1 - ℓ ^ (-(((d : ℝ) + 2) / 2 - γ)))⁻¹ := by
  have hℓ0 : 0 < ℓ := by linarith
  set y : ℝ := ℓ ^ (-(((d : ℝ) + 2) / 2 - γ)) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hℓ0 _
  have hy1 : y < 1 := Real.rpow_lt_one_of_one_lt_of_neg hℓ (by linarith)
  have h1 : ∀ n ∈ Finset.Ico k1 k,
      (E * ℓ ^ ((k : ℝ) * ((d : ℝ) - 2) / 2)) * (N * ℓ ^ (-(((k - n : ℕ) : ℝ) * d))) *
        (C * ℓ ^ (-(((n : ℝ) + 1) * (α + 2 * γ)))) =
      E * N * C * ℓ ^ (-(α + 2 * γ)) * ℓ ^ (-((k : ℝ) * γ)) * y ^ (k - n) := by
    intro n hn
    have hnk : n ≤ k := (Finset.mem_Ico.mp hn).2.le
    have := layer_exponent hℓ0 d k n hnk hα
    calc _ = E * N * C * (ℓ ^ ((k : ℝ) * ((d : ℝ) - 2) / 2) * ℓ ^ (-(((k - n : ℕ) : ℝ) * d)) *
          ℓ ^ (-(((n : ℝ) + 1) * (α + 2 * γ)))) := by ring
      _ = _ := by rw [this]; ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have hpos : 0 ≤ E * N * C * ℓ ^ (-(α + 2 * γ)) * ℓ ^ (-((k : ℝ) * γ)) := by positivity
  have hs : ∑ n ∈ Finset.Ico k1 k, y ^ (k - n) ≤ (1 - y)⁻¹ := by
    have h2 : ∑ n ∈ Finset.Ico k1 k, y ^ (k - n) = y * ∑ t ∈ Finset.range (k - k1), y ^ t := by
      rw [Finset.mul_sum]
      refine Finset.sum_nbij' (fun n => k - 1 - n) (fun t => k - 1 - t) ?_ ?_ ?_ ?_ ?_
      · intro n hn; simp only [Finset.mem_Ico, Finset.mem_range] at hn ⊢; omega
      · intro t ht; simp only [Finset.mem_Ico, Finset.mem_range] at ht ⊢; omega
      · intro n hn; simp only [Finset.mem_Ico] at hn; omega
      · intro t ht; simp only [Finset.mem_range] at ht; omega
      · intro n hn
        simp only [Finset.mem_Ico] at hn
        rw [← pow_succ']; congr 1; omega
    have hgeom : (∑ t ∈ Finset.range (k - k1), y ^ t) * (1 - y) = 1 - y ^ (k - k1) := geom_sum_mul_neg y _
    have hpow : 0 ≤ y ^ (k - k1) := by positivity
    have h0 : 0 ≤ ∑ t ∈ Finset.range (k - k1), y ^ t := Finset.sum_nonneg fun t _ => by positivity
    have h1y : 0 < 1 - y := by linarith
    have hle : ∑ t ∈ Finset.range (k - k1), y ^ t ≤ (1 - y)⁻¹ := by
      rw [← one_div, le_div_iff₀ h1y]; linarith
    rw [h2]
    nlinarith
  exact mul_le_mul_of_nonneg_left hs hpos

theorem blockFrac_rpow {L d : ℕ} (hL : 0 < L) (k n : ℕ) :
    blockFrac (L ^ d) k n = (L : ℝ) ^ (-(((k - n : ℕ) : ℝ) * d)) := by
  unfold blockFrac
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  rw [Real.rpow_neg hL'.le, ← Real.rpow_natCast]
  push_cast
  rw [← Real.rpow_natCast (L : ℝ) d, ← Real.rpow_mul hL'.le]
  congr 2
  ring

/-- The shift constant `C_ς` of (III.1.7), explicit. -/
noncomputable def shiftConst (S : Setting) (ε α0 cξ γ : ℝ) : ℝ :=
  6 * Real.exp ε * α0 * cξ * (2 * S.Cν) *
    ((S.L : ℝ) * S.M * (2 * S.c0 * (S.Rb + 1) + 10)) ^ S.d * (S.L : ℝ) ^ (-(S.α + 2 * γ)) *
    (1 - (S.L : ℝ) ^ (-(((S.d : ℝ) + 2) / 2 - γ)))⁻¹

namespace BlockTree

variable {m k1 k : ℕ} (B : BlockTree m k1 k)

/-- **Lemma III.1.7, first part**: the volume fraction of the leaves of the layer `n` satisfies
`f_n(z) ≤ ν_max(k) (L M crit_k)^d L^{-(k-n)d}`, from the block count of Lemma III.1.2 (c)
(`Λ_n ∩ z` has at most `ν (L M crit_{n+1})^d` blocks of scale `n`, `ν ≤ ν_max(k)`). -/
theorem deepLayer_frac_le {S : Setting} (hS : S.Ok) (hmL : m = S.L ^ S.d) {n : ℕ} (hnk : n < k)
    (hcount : (B.nLeaves n : ℝ) ≤ S.numax k * ((S.L : ℝ) * S.M * S.crit (n + 1)) ^ S.d) :
    B.layerFrac n ≤ S.numax k * ((S.L : ℝ) * S.M * S.crit k) ^ S.d *
      (S.L : ℝ) ^ (-(((k - n : ℕ) : ℝ) * S.d)) := by
  have hL2 := hS.two_le_L
  have hbf : blockFrac m k n = (S.L : ℝ) ^ (-(((k - n : ℕ) : ℝ) * S.d)) := by
    rw [hmL]; exact blockFrac_rpow (by omega) k n
  rw [B.layerFrac_eq, hbf]
  have hc1 : (S.crit (n + 1) : ℝ) ≤ S.crit k := by exact_mod_cast hS.crit_mono (by omega : n + 1 ≤ k)
  have h2 : (B.nLeaves n : ℝ) ≤ S.numax k * ((S.L : ℝ) * S.M * S.crit k) ^ S.d := by
    refine hcount.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hc1 (by positivity)) _
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

/-- **Lemma III.1.7, (III.1.7), mean shift**: the weighted shift of the composed mean by the field
renormalizations `ϖ_n - 1` satisfies
`β_k^{1/2} \bar ς_z ≤ C_ς β^{-1/2} λ̂_k^{p₂+2d} L^{-kγ}`. -/
theorem meanShift_le {S : Setting} (hS : S.Ok) (hmL : m = S.L ^ S.d)
    {γ ε α0 cξ β βk : ℝ} (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hα : S.α = ((S.d : ℝ) - 2) / 2 - γ)
    (hε : 0 ≤ ε) (hα0 : 0 ≤ α0) (hcξ : 0 ≤ cξ) (hβ : 0 < β)
    (hβkle : βk ≤ Real.exp ε * β * (S.L : ℝ) ^ ((k : ℝ) * ((S.d : ℝ) - 2)))
    (z : ℕ → ℝ)
    (hς : ∀ n, k1 ≤ n → n < k → |varpi k z n - 1| ≤
      6 * α0 * cξ / β * (S.L : ℝ) ^ (-(((n : ℝ) + 1) * (S.α + 2 * γ))))
    (hcount : ∀ n, k1 ≤ n → n < k → (B.nLeaves n : ℝ) ≤
      S.numax k * ((S.L : ℝ) * S.M * S.crit (n + 1)) ^ S.d) :
    Real.sqrt βk * B.shiftBar z ≤
      shiftConst S ε α0 cξ γ * (Real.sqrt β)⁻¹ * S.lam k ^ (S.p2 + 2 * S.d) *
        (S.L : ℝ) ^ (-((k : ℝ) * γ)) := by
  have hL2 := hS.two_le_L
  have hℓ1 : (1 : ℝ) < S.L := by exact_mod_cast (by omega : 1 < S.L)
  have hℓ0 : (0 : ℝ) < S.L := by linarith
  have hd3 := hS.three_le_d
  have hαγ : S.α + γ = ((S.d : ℝ) - 2) / 2 := by rw [hα]; ring
  have he : 0 < ((S.d : ℝ) + 2) / 2 - γ := by
    have : (3 : ℝ) ≤ S.d := by exact_mod_cast hd3
    linarith
  set ℓ : ℝ := (S.L : ℝ) with hℓ
  -- step 1
  have hsq : Real.sqrt βk ≤ Real.exp ε * Real.sqrt β * ℓ ^ ((k : ℝ) * ((S.d : ℝ) - 2) / 2) := by
    refine (Real.sqrt_le_sqrt hβkle).trans ?_
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    have h1 : Real.sqrt (Real.exp ε) ≤ Real.exp ε := by
      rw [Real.sqrt_le_iff]
      refine ⟨(Real.exp_pos _).le, ?_⟩
      have : 1 ≤ Real.exp ε := Real.one_le_exp hε
      nlinarith
    have h2 : Real.sqrt (ℓ ^ ((k : ℝ) * ((S.d : ℝ) - 2))) = ℓ ^ ((k : ℝ) * ((S.d : ℝ) - 2) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hℓ0.le]; congr 1; ring
    rw [h2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)) (by positivity)
  -- the layer bound
  set N : ℝ := (S.numax k : ℝ) * (ℓ * (S.M : ℝ) * (S.crit k : ℝ)) ^ S.d with hN
  have hN0 : 0 ≤ N := by positivity
  set C : ℝ := 6 * α0 * cξ / β with hC
  have hC0 : 0 ≤ C := by positivity
  set E : ℝ := Real.exp ε * Real.sqrt β with hE
  have hE0 : 0 ≤ E := by positivity
  have hf : ∀ n ∈ Finset.Ico k1 k, B.layerFrac n ≤ N * ℓ ^ (-(((k - n : ℕ) : ℝ) * S.d)) := by
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    exact B.deepLayer_frac_le hS hmL hn'.2 (hcount n hn'.1 hn'.2)
  have hmain : Real.sqrt βk * B.shiftBar z ≤
      (E * ℓ ^ ((k : ℝ) * ((S.d : ℝ) - 2) / 2)) *
        ∑ n ∈ Finset.Ico k1 k, (N * ℓ ^ (-(((k - n : ℕ) : ℝ) * S.d))) *
          (C * ℓ ^ (-(((n : ℝ) + 1) * (S.α + 2 * γ)))) := by
    refine mul_le_mul hsq ?_ (B.shiftBar_nonneg z) (by positivity)
    refine (B.shiftBar_le_layers z (fun n => C * ℓ ^ (-(((n : ℝ) + 1) * (S.α + 2 * γ)))) hς).trans ?_
    refine Finset.sum_le_sum fun n hn => ?_
    exact mul_le_mul_of_nonneg_right (hf n hn) (by positivity)
  have hsum := layer_sum_le hℓ1 S.d k k1 hαγ he hE0 hN0 hC0
  rw [Finset.mul_sum] at hmain
  have hmain' : Real.sqrt βk * B.shiftBar z ≤
      E * N * C * ℓ ^ (-(S.α + 2 * γ)) * ℓ ^ (-((k : ℝ) * γ)) *
        (1 - ℓ ^ (-(((S.d : ℝ) + 2) / 2 - γ)))⁻¹ := by
    refine hmain.trans (le_trans (le_of_eq ?_) hsum)
    refine Finset.sum_congr rfl fun n _ => by ring
  refine hmain'.trans ?_
  -- polynomial bounds on `N`
  have hlam : 1 ≤ S.lam k := hS.one_le_lam k
  have hlam0 : 0 < S.lam k := by linarith
  have hnu := hS.hatW_numax_le k
  have hcr := hS.hatW_crit_le k
  set c' : ℝ := 2 * S.c0 * (S.Rb + 1) + 10 with hc'
  have hN' : N ≤ 2 * S.Cν * ((ℓ * S.M * c') ^ S.d) * S.lam k ^ (S.p2 + 2 * S.d) := by
    have h1 : (ℓ * (S.M : ℝ) * (S.crit k : ℝ)) ^ S.d ≤ (ℓ * S.M * (c' * S.lam k ^ 2)) ^ S.d :=
      pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left hcr (by positivity)) _
    calc N = (S.numax k : ℝ) * (ℓ * (S.M : ℝ) * (S.crit k : ℝ)) ^ S.d := rfl
      _ ≤ (2 * S.Cν * S.lam k ^ S.p2) * (ℓ * S.M * (c' * S.lam k ^ 2)) ^ S.d :=
          mul_le_mul hnu h1 (by positivity) (by have := hS.Cν_pos; positivity)
      _ = 2 * S.Cν * ((ℓ * S.M * c') ^ S.d) * S.lam k ^ (S.p2 + 2 * S.d) := by
          rw [show ℓ * (S.M : ℝ) * (c' * S.lam k ^ 2) = (ℓ * S.M * c') * S.lam k ^ 2 by ring,
            mul_pow, ← pow_mul, pow_add]
          ring
  have hEC : E * C = 6 * Real.exp ε * α0 * cξ * (Real.sqrt β)⁻¹ := by
    have hsb : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
    have hb : β = Real.sqrt β * Real.sqrt β := (Real.mul_self_sqrt hβ.le).symm
    rw [hE, hC]
    nth_rewrite 2 [hb]
    field_simp
  have hy1 : 0 < (1 - ℓ ^ (-(((S.d : ℝ) + 2) / 2 - γ)))⁻¹ := by
    have : ℓ ^ (-(((S.d : ℝ) + 2) / 2 - γ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hℓ1 (by linarith)
    exact inv_pos.mpr (by linarith)
  have hrest : 0 ≤ ℓ ^ (-(S.α + 2 * γ)) * ℓ ^ (-((k : ℝ) * γ)) *
      (1 - ℓ ^ (-(((S.d : ℝ) + 2) / 2 - γ)))⁻¹ := by positivity
  calc E * N * C * ℓ ^ (-(S.α + 2 * γ)) * ℓ ^ (-((k : ℝ) * γ)) *
        (1 - ℓ ^ (-(((S.d : ℝ) + 2) / 2 - γ)))⁻¹
      = (E * C) * N * (ℓ ^ (-(S.α + 2 * γ)) * ℓ ^ (-((k : ℝ) * γ)) *
        (1 - ℓ ^ (-(((S.d : ℝ) + 2) / 2 - γ)))⁻¹) := by ring
    _ ≤ (E * C) * (2 * S.Cν * ((ℓ * S.M * c') ^ S.d) * S.lam k ^ (S.p2 + 2 * S.d)) *
        (ℓ ^ (-(S.α + 2 * γ)) * ℓ ^ (-((k : ℝ) * γ)) *
        (1 - ℓ ^ (-(((S.d : ℝ) + 2) / 2 - γ)))⁻¹) := by
        have hEC0 : 0 ≤ E * C := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN' hEC0) hrest
    _ = _ := by
        rw [hEC]; unfold shiftConst; ring


end BlockTree

end Balaban.LargeField
