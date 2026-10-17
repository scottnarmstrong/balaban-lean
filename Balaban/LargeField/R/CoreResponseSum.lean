/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoreResponse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The core-to-action response: summed first-derivative bounds (Q13-SHARED (2.4), `A₁`, `A₂`)

Let `J_{x i, z j} = ∂ φ⁰(ψ_k)(x, i) / ∂ ψ_k(z)_j` be the one-site derivative of the massless background
(`coreResponse_deriv_le`).  For a block `z` of the top layer `Ω_k` (`OverTop G {z}`) and every site `x` of `Ω₁`:

* `sum_siteWeight_decay_shadow_fib_le`, `sum_decay_shadow_fib_le` (counting, any rate `γ` with the separation
  `2 d log L ≤ (γ/2)(ϱ - 1)` of Lemma 4.4): `∑_x ℓ(x)^{-d} e^{-γ d(x, W_z)} ≤ e^{γ(2d+1)} C(d, L, γ)` and
  `∑_{z ∈ Z_f} e^{-γ d(x, W_z)} ≤ e^{γ(2d+1)} C(d, L, γ)` (`C = countConst`), uniformly in the torus, in `k`, in `x`,
  `z` and `Z_f`;
* `coreResponse_sum_le` (the first bound of (2.4)): `∑_x ℓ(x)^{-d} |J_{x i, z j}| ≤ A₁` and
  `L^{-kd} ∑_x |J_{x i, z j}| ≤ A₁`, `A₁ = K_w C_F e^{γ_w(2d+1)} C(d, L, γ_w)`;
* `coreResponse_sum_sq_le` (the second bound of (2.4)): `∑_x ℓ(x)^{-d} |J_{x i, z j}|² ≤ A₂` and
  `L^{-kd} ∑_x |J_{x i, z j}|² ≤ A₂`, `A₂ = K_w C_F A₁`;
* `coreResponse_sum_blocks_le` (the opposite-index Schur bound): `∑_{z ∈ Z_f} |J_{x i, z j}| ≤ A₁` for a set `Z_f` of
  top-layer blocks.

The separation premise of the counting lemma at the rate `γ_w` is the separation of `Dec2.OpSetting`
(`opSetting_counting`).  The sums over `x` run over all of `Ω₁`, hence over every action region `D_Z ⊆ Ω₁`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization

section Counting

variable {d L : ℕ} [NeZero L]

/-- The separation of `Dec2.OpSetting` is the premise of the counting lemma (Lemma 4.4) at the rate `γ_w`. -/
theorem opSetting_counting {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ}
    {a : ℕ → ℝ} {ν : ℝ} (hOp : Dec2.OpSetting G a ν) :
    1 < ϱ ∧ 2 * d * Real.log L ≤ gammaW d / 2 * (ϱ - 1) := by
  have hd : 3 ≤ d := hOp.hd
  have hL : 3 ≤ L := hOp.hL
  have hsep := hOp.sep
  have e : gammaW d / 2 = agmonRate d / 16 := by unfold gammaW; ring
  refine ⟨?_, by rw [e]; exact hsep⟩
  have hA := agmonRate_pos (d := d) (by omega)
  have hlog : 0 < Real.log L := Real.log_pos (by exact_mod_cast (by omega : 1 < L))
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  by_contra hϱ
  push Not at hϱ
  have h1 : agmonRate d / 16 * (ϱ - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  nlinarith [mul_pos (mul_pos two_pos hd0) hlog]

variable {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ}

theorem fib_subset_layer (hk : 1 ≤ k) {z : Torus d (N₁ * L ^ m₁ * L ^ (k - k))}
    (hz : OverTop G ({z} : Set (Torus d (N₁ * L ^ m₁ * L ^ (k - k))))) {y : Torus d (N₁ * L ^ m₁ * L ^ k)}
    (hy : y ∈ fib d L (N₁ * L ^ m₁) k k z) : y ∈ G.layer k ∧ y ∈ G.Ω 1 := by
  have hyk : y ∈ G.Ω k := hz y (by rw [mem_fib] at hy; exact hy)
  have hyl : y ∈ G.layer k := G.mem_layer.2 ⟨hyk, by rw [G.top]; simp⟩
  exact ⟨hyl, G.layer_subset hk le_rfl hyl⟩

/-- **Counting from a top-layer block, sum over sites**: `∑_{x ∈ Ω₁} ℓ(x)^{-d} e^{-γ d(x, W_z)} ≤ e^{γ(2d+1)} C(d, L, γ)`
under the separation premise of Lemma 4.4. -/
theorem sum_siteWeight_decay_shadow_fib_le (hk : 1 ≤ k) (hϱ : 1 < ϱ) {γ : ℝ} (hγ : 0 < γ)
    (hcond : 2 * d * Real.log L ≤ γ / 2 * (ϱ - 1)) {z : Torus d (N₁ * L ^ m₁ * L ^ (k - k))}
    (hz : OverTop G ({z} : Set (Torus d (N₁ * L ^ m₁ * L ^ (k - k))))) :
    ∑ x : G.Ω 1, siteWeight G x * decay γ (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) ≤
      Real.exp (γ * (2 * d + 1)) * countConst d L γ := by
  obtain ⟨y, hy⟩ := fib_nonempty (d := d) (L := L) (N₀ := N₁ * L ^ m₁) (q := k) le_rfl z
  have hyΩ := (fib_subset_layer hk hz hy).2
  have hE : 0 ≤ Real.exp (γ * (2 * d + 1)) := (Real.exp_pos _).le
  calc ∑ x : G.Ω 1, siteWeight G x * decay γ (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x)
      ≤ ∑ x : G.Ω 1, Real.exp (γ * (2 * d + 1)) * (siteWeight G x * decay γ (G.pathDist y x)) := by
        refine Finset.sum_le_sum fun x _ => ?_
        have h1 := decay_shadow_fib_le hk hγ.le hz hy (x : Torus d (N₁ * L ^ m₁ * L ^ k))
        rw [G.pathDist_comm] at h1
        calc siteWeight G x * decay γ (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x)
            ≤ siteWeight G x * (Real.exp (γ * (2 * d + 1)) * decay γ (G.pathDist y x)) :=
              mul_le_mul_of_nonneg_left h1 (siteWeight_nonneg G _)
          _ = _ := by ring
    _ = Real.exp (γ * (2 * d + 1)) * ∑ x : G.Ω 1, siteWeight G x * decay γ (G.pathDist y x) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (γ * (2 * d + 1)) * countConst d L γ :=
        mul_le_mul_of_nonneg_left (sum_siteWeight_decay_le G hϱ hγ hcond hyΩ) hE

/-- The site weights of the fine sites of a top-layer block add up to `1`. -/
theorem sum_siteWeight_fib (hk : 1 ≤ k) {z : Torus d (N₁ * L ^ m₁ * L ^ (k - k))}
    (hz : OverTop G ({z} : Set (Torus d (N₁ * L ^ m₁ * L ^ (k - k))))) :
    ∑ y ∈ fib d L (N₁ * L ^ m₁) k k z, siteWeight G y = 1 := by
  have hw : ∀ y ∈ fib d L (N₁ * L ^ m₁) k k z, siteWeight G y = (((L : ℝ) ^ k)⁻¹) ^ d := by
    intro y hy
    unfold siteWeight
    rw [G.layerIndex_eq hk le_rfl (fib_subset_layer hk hz hy).1]
  rw [Finset.sum_congr rfl hw, Finset.sum_const, card_fib le_rfl, nsmul_eq_mul]
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  push_cast
  rw [← mul_pow, mul_inv_cancel₀ (by positivity), one_pow]

/-- **Counting from a top-layer block, sum over blocks**: for `x ∈ Ω₁` and a set `Z_f` of top-layer blocks,
`∑_{z ∈ Z_f} e^{-γ d(x, W_z)} ≤ e^{γ(2d+1)} C(d, L, γ)`. -/
theorem sum_decay_shadow_fib_le (hk : 1 ≤ k) (hϱ : 1 < ϱ) {γ : ℝ} (hγ : 0 < γ)
    (hcond : 2 * d * Real.log L ≤ γ / 2 * (ϱ - 1)) (Zf : Finset (Torus d (N₁ * L ^ m₁ * L ^ (k - k))))
    (hZ : ∀ z ∈ Zf, OverTop G ({z} : Set (Torus d (N₁ * L ^ m₁ * L ^ (k - k))))) (x : G.Ω 1) :
    ∑ z ∈ Zf, decay γ (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) ≤
      Real.exp (γ * (2 * d + 1)) * countConst d L γ := by
  classical
  set c := Real.exp (γ * (2 * d + 1)) with hc
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  set F : Torus d (N₁ * L ^ m₁ * L ^ k) → ℝ := fun y => siteWeight G y * (c * decay γ (G.pathDist x y)) with hF
  have hF0 : ∀ y, 0 ≤ F y := fun y =>
    mul_nonneg (siteWeight_nonneg G y) (mul_nonneg hc0 (decay_nonneg _ _))
  have step1 : ∀ z ∈ Zf, decay γ (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) ≤
      ∑ y ∈ fib d L (N₁ * L ^ m₁) k k z, F y := by
    intro z hz
    have hsum := sum_siteWeight_fib (G := G) hk (hZ z hz)
    calc decay γ (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x)
        = ∑ y ∈ fib d L (N₁ * L ^ m₁) k k z, siteWeight G y *
            decay γ (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) := by
          rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ y ∈ fib d L (N₁ * L ^ m₁) k k z, F y := by
          refine Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_left ?_ (siteWeight_nonneg G y)
          exact decay_shadow_fib_le hk hγ.le (hZ z hz) hy (x : Torus d (N₁ * L ^ m₁ * L ^ k))
  have hdisj : (Zf : Set (Torus d (N₁ * L ^ m₁ * L ^ (k - k)))).PairwiseDisjoint
      (fib d L (N₁ * L ^ m₁) k k) := by
    intro z _ z' _ hne
    refine Finset.disjoint_left.2 fun y hy hy' => hne ?_
    rw [mem_fib] at hy hy'
    exact hy.symm.trans hy'
  have hsub : Zf.biUnion (fib d L (N₁ * L ^ m₁) k k) ⊆ G.Ω 1 := by
    intro y hy
    obtain ⟨z, hz, hyz⟩ := Finset.mem_biUnion.1 hy
    exact (fib_subset_layer hk (hZ z hz) hyz).2
  calc ∑ z ∈ Zf, decay γ (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x)
      ≤ ∑ z ∈ Zf, ∑ y ∈ fib d L (N₁ * L ^ m₁) k k z, F y := Finset.sum_le_sum step1
    _ = ∑ y ∈ Zf.biUnion (fib d L (N₁ * L ^ m₁) k k), F y := (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ y ∈ G.Ω 1, F y := Finset.sum_le_sum_of_subset_of_nonneg hsub fun y _ _ => hF0 y
    _ = ∑ y : G.Ω 1, F y := (Finset.sum_coe_sort (G.Ω 1) F).symm
    _ = c * ∑ y : G.Ω 1, siteWeight G y * decay γ (G.pathDist x y) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        simp only [hF]
        ring
    _ ≤ c * countConst d L γ :=
        mul_le_mul_of_nonneg_left (sum_siteWeight_decay_le G hϱ hγ hcond x.2) hc0

/-- `L^{-kd} ≤ ℓ(x)^{-d}` on `Ω₁` (the site weight of a site of layer `≤ k`). -/
theorem inv_pow_le_siteWeight (x : G.Ω 1) : (((L : ℝ) ^ k) ^ d)⁻¹ ≤ siteWeight G x := by
  obtain ⟨-, hxk, -⟩ := G.layerIndex_spec x.2
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  unfold siteWeight
  rw [inv_pow]
  refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ d)
  exact pow_le_pow_right₀ hL hxk

end Counting

section Sums

variable {d L N : ℕ} [NeZero L]

/-- **(2.4), first bound**: for a top-layer block `z`, `∑_{x ∈ Ω₁} ℓ(x)^{-d} |J_{x i, z j}| ≤ A₁` and
`L^{-kd} ∑_{x ∈ Ω₁} |J_{x i, z j}| ≤ A₁`, `A₁ = K_w C_F e^{γ_w(2d+1)} C(d, L, γ_w)`, uniformly in the torus, `k`,
`z`, `j`, `i` and the field `ψ_k ∈ Ψ̃(𝔹; τ)`. -/
theorem coreResponse_sum_le (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ},
        BgHyp d L k ϱ a 0 → Dec2.OpSetting G a 0 → 1 ≤ k →
        ∀ {τ : ℝ}, 0 < τ → τ ≤ bgC1 d L N → bgK1 d L N * τ ≤ min (deltaStar d L N) δw →
        ∀ {ψ : BlockField d L (N₁ * L ^ m₁) k N}, TubeOn G Set.univ τ ψ →
        ∀ (z : Torus d (N₁ * L ^ m₁ * L ^ (k - k))), OverTop G ({z} : Set _) →
        ∀ (j i : Fin N),
        ∑ x : G.Ω 1, siteWeight G x *
            ‖deriv (fun t : ℝ => bgField G a 0 (dataR G (ψ + t •
              (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i)) 0‖ ≤
          Kw * cF d L * Real.exp (gammaW d * (2 * d + 1)) * countConst d L (gammaW d) ∧
        (((L : ℝ) ^ k) ^ d)⁻¹ * ∑ x : G.Ω 1,
            ‖deriv (fun t : ℝ => bgField G a 0 (dataR G (ψ + t •
              (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i)) 0‖ ≤
          Kw * cF d L * Real.exp (gammaW d * (2 * d + 1)) * countConst d L (gammaW d) := by
  obtain ⟨Kw, δw, hK, hδw, hJ⟩ := coreResponse_deriv_le (N := N) hd hL
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro N₁ m₁ k _ ϱ G a H hOp hk τ hτ hτ1 hτs ψ ht z hz j i
  obtain ⟨hϱ, hcond⟩ := opSetting_counting hOp
  have hγ : 0 < gammaW d := by unfold gammaW; have := agmonRate_pos (d := d) (by omega); positivity
  set J : G.Ω 1 → ℝ := fun x => ‖deriv (fun t : ℝ => bgField G a 0 (dataR G (ψ + t •
      (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i)) 0‖ with hJdef
  have hKc : 0 ≤ Kw * cF d L := mul_nonneg hK.le (cF_pos d L).le
  have h1 : ∑ x : G.Ω 1, siteWeight G x * J x ≤
      Kw * cF d L * Real.exp (gammaW d * (2 * d + 1)) * countConst d L (gammaW d) := by
    calc ∑ x : G.Ω 1, siteWeight G x * J x
        ≤ ∑ x : G.Ω 1, Kw * cF d L * (siteWeight G x *
            decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x)) := by
          refine Finset.sum_le_sum fun x _ => ?_
          calc siteWeight G x * J x ≤ siteWeight G x * (Kw * cF d L *
                decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x)) :=
                mul_le_mul_of_nonneg_left (hJ H hOp hτ hτ1 hτs ht z j x i) (siteWeight_nonneg G _)
            _ = _ := by ring
      _ = Kw * cF d L * ∑ x : G.Ω 1, siteWeight G x *
            decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) := by
          rw [Finset.mul_sum]
      _ ≤ Kw * cF d L * (Real.exp (gammaW d * (2 * d + 1)) * countConst d L (gammaW d)) :=
          mul_le_mul_of_nonneg_left (sum_siteWeight_decay_shadow_fib_le hk hϱ hγ hcond hz) hKc
      _ = _ := by ring
  refine ⟨h1, ?_⟩
  refine le_trans ?_ h1
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_right (inv_pow_le_siteWeight x) (norm_nonneg _)

/-- **(2.4), second bound**: `∑_{x ∈ Ω₁} ℓ(x)^{-d} |J_{x i, z j}|² ≤ A₂` and `L^{-kd} ∑_x |J_{x i, z j}|² ≤ A₂`,
`A₂ = K_w C_F · A₁` (`|J| ≤ K_w C_F`). -/
theorem coreResponse_sum_sq_le (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ},
        BgHyp d L k ϱ a 0 → Dec2.OpSetting G a 0 → 1 ≤ k →
        ∀ {τ : ℝ}, 0 < τ → τ ≤ bgC1 d L N → bgK1 d L N * τ ≤ min (deltaStar d L N) δw →
        ∀ {ψ : BlockField d L (N₁ * L ^ m₁) k N}, TubeOn G Set.univ τ ψ →
        ∀ (z : Torus d (N₁ * L ^ m₁ * L ^ (k - k))), OverTop G ({z} : Set _) →
        ∀ (j i : Fin N),
        ∑ x : G.Ω 1, siteWeight G x *
            ‖deriv (fun t : ℝ => bgField G a 0 (dataR G (ψ + t •
              (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i)) 0‖ ^ 2 ≤
          Kw * cF d L * (Kw * cF d L * Real.exp (gammaW d * (2 * d + 1)) * countConst d L (gammaW d)) ∧
        (((L : ℝ) ^ k) ^ d)⁻¹ * ∑ x : G.Ω 1,
            ‖deriv (fun t : ℝ => bgField G a 0 (dataR G (ψ + t •
              (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i)) 0‖ ^ 2 ≤
          Kw * cF d L * (Kw * cF d L * Real.exp (gammaW d * (2 * d + 1)) * countConst d L (gammaW d)) := by
  obtain ⟨Kw, δw, hK, hδw, hJ⟩ := coreResponse_deriv_le (N := N) hd hL
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro N₁ m₁ k _ ϱ G a H hOp hk τ hτ hτ1 hτs ψ ht z hz j i
  obtain ⟨hϱ, hcond⟩ := opSetting_counting hOp
  have hγ : 0 < gammaW d := by unfold gammaW; have := agmonRate_pos (d := d) (by omega); positivity
  have hγ0 := hγ.le
  set J : G.Ω 1 → ℝ := fun x => ‖deriv (fun t : ℝ => bgField G a 0 (dataR G (ψ + t •
      (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i)) 0‖ with hJdef
  have hKc : 0 ≤ Kw * cF d L := mul_nonneg hK.le (cF_pos d L).le
  have hJd : ∀ x : G.Ω 1, J x ≤ Kw * cF d L *
      decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) :=
    fun x => hJ H hOp hτ hτ1 hτs ht z j x i
  have hJ1 : ∀ x : G.Ω 1, J x ≤ Kw * cF d L := fun x =>
    (hJd x).trans (by
      have := decay_le_one hγ0 (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x)
      nlinarith)
  have hsq : ∀ x : G.Ω 1, J x ^ 2 ≤ Kw * cF d L * (Kw * cF d L *
      decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x)) := by
    intro x
    have h0 : 0 ≤ J x := norm_nonneg _
    rw [sq]
    exact mul_le_mul (hJ1 x) (hJd x) h0 hKc
  have h1 : ∑ x : G.Ω 1, siteWeight G x * J x ^ 2 ≤
      Kw * cF d L * (Kw * cF d L * Real.exp (gammaW d * (2 * d + 1)) * countConst d L (gammaW d)) := by
    calc ∑ x : G.Ω 1, siteWeight G x * J x ^ 2
        ≤ ∑ x : G.Ω 1, (Kw * cF d L) * (Kw * cF d L) * (siteWeight G x *
            decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x)) := by
          refine Finset.sum_le_sum fun x _ => ?_
          calc siteWeight G x * J x ^ 2 ≤ siteWeight G x * (Kw * cF d L * (Kw * cF d L *
                decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x))) :=
                mul_le_mul_of_nonneg_left (hsq x) (siteWeight_nonneg G _)
            _ = _ := by ring
      _ = (Kw * cF d L) * (Kw * cF d L) * ∑ x : G.Ω 1, siteWeight G x *
            decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) := by
          rw [Finset.mul_sum]
      _ ≤ (Kw * cF d L) * (Kw * cF d L) * (Real.exp (gammaW d * (2 * d + 1)) * countConst d L (gammaW d)) :=
          mul_le_mul_of_nonneg_left (sum_siteWeight_decay_shadow_fib_le hk hϱ hγ hcond hz)
            (mul_nonneg hKc hKc)
      _ = _ := by ring
  refine ⟨h1, ?_⟩
  refine le_trans ?_ h1
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_right (inv_pow_le_siteWeight x) (sq_nonneg _)

/-- **(2.4), the opposite-index Schur bound**: for `x ∈ Ω₁` and a set `Z_f` of top-layer blocks,
`∑_{z ∈ Z_f} |J_{x i, z j}| ≤ A₁ = K_w C_F e^{γ_w(2d+1)} C(d, L, γ_w)`. -/
theorem coreResponse_sum_blocks_le (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ},
        BgHyp d L k ϱ a 0 → Dec2.OpSetting G a 0 → 1 ≤ k →
        ∀ {τ : ℝ}, 0 < τ → τ ≤ bgC1 d L N → bgK1 d L N * τ ≤ min (deltaStar d L N) δw →
        ∀ {ψ : BlockField d L (N₁ * L ^ m₁) k N}, TubeOn G Set.univ τ ψ →
        ∀ (Zf : Finset (Torus d (N₁ * L ^ m₁ * L ^ (k - k)))), (∀ z ∈ Zf, OverTop G ({z} : Set _)) →
        ∀ (j : Fin N) (x : G.Ω 1) (i : Fin N),
        ∑ z ∈ Zf,
            ‖deriv (fun t : ℝ => bgField G a 0 (dataR G (ψ + t •
              (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i)) 0‖ ≤
          Kw * cF d L * Real.exp (gammaW d * (2 * d + 1)) * countConst d L (gammaW d) := by
  obtain ⟨Kw, δw, hK, hδw, hJ⟩ := coreResponse_deriv_le (N := N) hd hL
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro N₁ m₁ k _ ϱ G a H hOp hk τ hτ hτ1 hτs ψ ht Zf hZ j x i
  obtain ⟨hϱ, hcond⟩ := opSetting_counting hOp
  have hγ : 0 < gammaW d := by unfold gammaW; have := agmonRate_pos (d := d) (by omega); positivity
  have hKc : 0 ≤ Kw * cF d L := mul_nonneg hK.le (cF_pos d L).le
  calc _ ≤ ∑ z ∈ Zf, Kw * cF d L *
          decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) :=
        Finset.sum_le_sum fun z _ => hJ H hOp hτ hτ1 hτs ht z j x i
    _ = Kw * cF d L * ∑ z ∈ Zf,
          decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) := by
        rw [Finset.mul_sum]
    _ ≤ Kw * cF d L * (Real.exp (gammaW d * (2 * d + 1)) * countConst d L (gammaW d)) :=
        mul_le_mul_of_nonneg_left (sum_decay_shadow_fib_le hk hϱ hγ hcond Zf hZ x) hKc
    _ = _ := by ring

end Sums

end Balaban.LargeField
