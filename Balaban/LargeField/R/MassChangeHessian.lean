/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.MassChangeWall
public import Balaban.LargeField.R.ActionConvWitness
public import Balaban.Green.OneScaleDecay
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The localized Hessian bound and the wall count (MASS-RESPONSE (2.1), (2.4), (2.5))

* `Region.touching`, `Region.card_touching_le`, `Region.card_crossing_le`: the bonds meeting `D`
  number at most `2 d |D|`, and so do the crossing bonds;
* `massChangeChord_norm_le_of_pointwise`: `‖2 · chord‖ ≤ (2 d + 4) |D| ℓ₀⁻² W²`;
* `massChange_hHess_of_pointwise`, `region_ratio_eq`: the consumer's form of the Hessian bound;
* `crossing_sum_le`, `massChange_region_bound_of_response`: the wall sum and the region bound.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- The bonds `(x, x + e_μ)` with at least one endpoint in `D`. -/
noncomputable def Region.touching (D : Region G) : Finset (Torus d (N₀ * L ^ K) × Fin d) :=
  open Classical in
  Finset.univ.filter fun b => b.1 ∈ D.sites ∨ b.1 + Pi.single b.2 1 ∈ D.sites

theorem Region.card_touching_le (D : Region G) : D.touching.card ≤ 2 * d * D.sites.card := by
  classical
  have h1 : D.touching ⊆
      (D.sites ×ˢ (Finset.univ : Finset (Fin d))) ∪
        (Finset.univ : Finset (Fin d)).biUnion fun μ =>
          (D.sites.image fun y => y - Pi.single μ 1) ×ˢ {μ} := by
    intro b hb
    simp only [Region.touching, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    rcases hb with h | h
    · exact Finset.mem_union.2 (Or.inl (Finset.mem_product.2 ⟨h, Finset.mem_univ _⟩))
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_biUnion.2 ⟨b.2, Finset.mem_univ _,
        Finset.mem_product.2 ⟨Finset.mem_image.2 ⟨_, h, by simp⟩, Finset.mem_singleton_self _⟩⟩))
  refine (Finset.card_le_card h1).trans ((Finset.card_union_le _ _).trans ?_)
  have h2 : ((Finset.univ : Finset (Fin d)).biUnion fun μ =>
      (D.sites.image fun y => y - Pi.single μ 1) ×ˢ ({μ} : Finset (Fin d))).card ≤
      d * D.sites.card := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ μ : Fin d, ((D.sites.image fun y => y - Pi.single μ 1) ×ˢ {μ}).card
        ≤ ∑ _μ : Fin d, D.sites.card := Finset.sum_le_sum fun μ _ => by
          rw [Finset.card_product, Finset.card_singleton, mul_one]
          exact Finset.card_image_le
      _ = d * D.sites.card := by simp
  have h3 : (D.sites ×ˢ (Finset.univ : Finset (Fin d))).card = D.sites.card * d := by
    simp
  rw [h3]; nlinarith

theorem Region.crossing_subset_touching (D : Region G) : D.crossing ⊆ D.touching := by
  classical
  intro b hb
  simp only [Region.crossing, Region.touching, Finset.mem_filter, Finset.mem_univ,
    true_and] at hb ⊢
  by_contra h
  push Not at h
  exact hb ⟨fun h' => absurd h' h.1, fun h' => absurd h' h.2⟩

/-- **The count of crossing bonds**: `|st(D)| ≤ 2 d |D|`. -/
theorem Region.card_crossing_le (D : Region G) : D.crossing.card ≤ 2 * d * D.sites.card :=
  (Finset.card_le_card D.crossing_subset_touching).trans D.card_touching_le

theorem vnorm_sum_le {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin N → ℂ) :
    vnorm (fun i => ∑ y ∈ s, f y i) ≤ ∑ y ∈ s, vnorm (f y) := by
  unfold vnorm
  have : (WithLp.toLp 2 (fun i => ∑ y ∈ s, f y i) : EuclideanSpace ℂ (Fin N)) =
      ∑ y ∈ s, WithLp.toLp 2 (f y) := by
    ext i; simp
  rw [this]
  exact norm_sum_le _ _

theorem svec_diff_eq_wExt (Dat : BgData G N) (φ0 φm : G.Ω 1 × Fin N → ℂ)
    {x : Torus d (N₀ * L ^ K)} (hx : x ∈ G.Ω 1) :
    svec G (φ0 - φm) x = wExt Dat Dat φm φ0 x := by
  funext i
  simp [svec, zeroExt, wExt, barField, hx]

theorem vnorm_svec_le (Dat : BgData G N) (φ0 φm : G.Ω 1 × Fin N → ℂ) {W : ℝ} (hW0 : 0 ≤ W)
    (hW : ∀ x, vnorm (wExt Dat Dat φm φ0 x) ≤ W) (x : Torus d (N₀ * L ^ K)) :
    vnorm (svec G (φ0 - φm) x) ≤ W := by
  by_cases hx : x ∈ G.Ω 1
  · rw [svec_diff_eq_wExt Dat φ0 φm hx]; exact hW x
  · have : svec G (φ0 - φm) x = fun _ => 0 := by
      funext i; exact svec_of_not_mem G _ hx i
    rw [this]
    have : vnorm (fun _ : Fin N => (0 : ℂ)) = 0 := by
      unfold vnorm
      have h0 : (WithLp.toLp 2 (fun _ : Fin N => (0 : ℂ)) : EuclideanSpace ℂ (Fin N)) = 0 := rfl
      rw [h0, norm_zero]
    rw [this]; exact hW0

theorem vnorm_blockAvg_le (Dat : BgData G N) (φ0 φm : G.Ω 1 × Fin N → ℂ) {W : ℝ}
    (hW0 : 0 ≤ W) (hW : ∀ x, vnorm (wExt Dat Dat φm φ0 x) ≤ W)
    {x : Torus d (N₀ * L ^ K)} (hx : x ∈ G.Ω 1) :
    vnorm (fun i => blockAvg G (φ0 - φm) x i) ≤ W := by
  obtain ⟨h1, h2, -⟩ := G.layerIndex_spec hx
  have hpos : (0 : ℝ) < (((L : ℝ) ^ G.layerIndex x) ^ d) := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have e : (fun i => blockAvg G (φ0 - φm) x i) =
      fun i => ((((((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ : ℝ) : ℂ)) *
        ∑ y ∈ G.blk (G.layerIndex x) x, svec G (φ0 - φm) y i := rfl
  rw [e, vnorm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hs := (vnorm_sum_le (N := N) (G.blk (G.layerIndex x) x) (svec G (φ0 - φm))).trans
    (Finset.sum_le_card_nsmul _ _ W fun y _ => vnorm_svec_le Dat φ0 φm hW0 hW y)
  rw [nsmul_eq_mul, card_blk G _ h2] at hs
  calc (((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ *
        vnorm (fun i => ∑ y ∈ G.blk (G.layerIndex x) x, svec G (φ0 - φm) y i)
      ≤ (((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ * ((((L ^ G.layerIndex x) ^ d : ℕ) : ℝ) * W) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = W := by push_cast; field_simp

/-- **The localized Hessian bound** (MASS-RESPONSE (2.1)).  With `W` the sup bound of
`w̄ = φ̄⁰ - φ̄ᵐ`, bond differences of `w̄` at most `W/ℓ₀` on bonds meeting `D`, block coefficients
at most `2/ℓ₀²`, `‖α‖ ≤ δ₀/ℓ₀²` (`δ₀ ≤ 1`) and `0 ≤ ν ≤ ℓ₀⁻²`, one has
`‖2 · chord‖ ≤ (2 d + 4) |D| ℓ₀⁻² W²`: block `≤ 2`, bonds `≤ 2d` (the bonds meeting `D`, each of
weight at most `1`), multiplier `≤ δ₀`, mass `≤ 1`; this matches the note's constant `2d + 4`. -/
theorem massChangeChord_norm_le_of_pointwise (D : Region G) (a : ℕ → ℝ) {ν : ℝ}
    (Dat : BgData G N) (φ0 φm : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ)
    {W ℓ₀ δ₀ : ℝ} (hW0 : 0 ≤ W) (hℓ : 0 < ℓ₀)
    (hW : ∀ x, vnorm (wExt Dat Dat φm φ0 x) ≤ W)
    (hbond : ∀ (x : Torus d (N₀ * L ^ K)) (μ : Fin d),
      (x ∈ D.sites ∨ x + Pi.single μ 1 ∈ D.sites) →
        vnorm (fun i => wExt Dat Dat φm φ0 (x + Pi.single μ 1) i - wExt Dat Dat φm φ0 x i)
          ≤ W / ℓ₀)
    (hcoef : ∀ x ∈ D.sites,
      |a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2| ≤ 2 / ℓ₀ ^ 2)
    (hα : ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ K)) ∈ D.sites → ‖α x‖ ≤ δ₀ / ℓ₀ ^ 2)
    (hδ₀ : 0 ≤ δ₀) (hδ₁ : δ₀ ≤ 1) (hν0 : 0 ≤ ν) (hν : ν ≤ 1 / ℓ₀ ^ 2) :
    ‖2 * massChangeChord D a ν Dat φ0 φm α‖ ≤
      (2 * d + 4) * (D.sites.card : ℝ) / ℓ₀ ^ 2 * W ^ 2 := by
  classical
  have hℓ2 : 0 < ℓ₀ ^ 2 := by positivity
  set c : ℝ := (D.sites.card : ℝ) with hc
  -- block piece
  have hB : ‖D.blockPair a (fun x i => blockAvg G (φ0 - φm) x i)
      (fun x i => blockAvg G (φ0 - φm) x i)‖ ≤ c * (2 / ℓ₀ ^ 2 * W ^ 2) := by
    unfold Region.blockPair
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (2 / ℓ₀ ^ 2 * W ^ 2) ?_).trans
      (le_of_eq (by rw [nsmul_eq_mul])))
    intro x hx
    rw [norm_mul]
    have h1 : ‖levelCoeff G a x‖ ≤ 2 / ℓ₀ ^ 2 := by
      unfold levelCoeff; rw [Complex.norm_real, Real.norm_eq_abs]; exact hcoef x hx
    have h2 := (norm_sum_mul_le (fun i => blockAvg G (φ0 - φm) x i)
      (fun i => blockAvg G (φ0 - φm) x i)).trans
      (mul_self_le_mul_self (vnorm_nonneg _) (vnorm_blockAvg_le Dat φ0 φm hW0 hW (D.sub_Ω hx)))
    calc ‖levelCoeff G a x‖ * ‖∑ i, blockAvg G (φ0 - φm) x i * blockAvg G (φ0 - φm) x i‖
        ≤ (2 / ℓ₀ ^ 2) * (W * W) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  -- bond piece
  have hBd : ‖D.bondPair (wExt Dat Dat φm φ0) (wExt Dat Dat φm φ0)‖ ≤
      (2 * d * c) * (W / ℓ₀) ^ 2 := by
    unfold Region.bondPair
    have hterm : ∀ (x : Torus d (N₀ * L ^ K)) (μ : Fin d),
        ‖(D.starWeight x μ : ℂ) * ∑ i, (wExt Dat Dat φm φ0 (x + Pi.single μ 1) i -
            wExt Dat Dat φm φ0 x i) * (wExt Dat Dat φm φ0 (x + Pi.single μ 1) i -
            wExt Dat Dat φm φ0 x i)‖ ≤
          if (x, μ) ∈ D.touching then (W / ℓ₀) ^ 2 else 0 := by
      intro x μ
      split_ifs with ht
      · have ht' : x ∈ D.sites ∨ x + Pi.single μ 1 ∈ D.sites := by
          simpa [Region.touching] using ht
        have hw0 : 0 ≤ D.starWeight x μ := by
          unfold Region.starWeight; split_ifs <;> norm_num
        have hw1 : D.starWeight x μ ≤ 1 := by
          unfold Region.starWeight; split_ifs <;> norm_num
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
        have h2 := (norm_sum_mul_le
          (fun i => wExt Dat Dat φm φ0 (x + Pi.single μ 1) i - wExt Dat Dat φm φ0 x i)
          (fun i => wExt Dat Dat φm φ0 (x + Pi.single μ 1) i - wExt Dat Dat φm φ0 x i)).trans
          (mul_self_le_mul_self (vnorm_nonneg _) (hbond x μ ht'))
        calc D.starWeight x μ * _ ≤ 1 * ((W / ℓ₀) * (W / ℓ₀)) :=
              mul_le_mul hw1 h2 (norm_nonneg _) zero_le_one
          _ = _ := by ring
      · have hn : ¬ (x ∈ D.sites ∨ x + Pi.single μ 1 ∈ D.sites) := by
          simpa [Region.touching] using ht
        push Not at hn
        have : D.starWeight x μ = 0 := by
          unfold Region.starWeight; simp [hn.1, hn.2]
        simp [this]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun x _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => hterm x μ)).trans ?_)
    have hsum : ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d,
        (if (x, μ) ∈ D.touching then (W / ℓ₀) ^ 2 else 0) =
        (D.touching.card : ℝ) * (W / ℓ₀) ^ 2 := by
      rw [← Fintype.sum_prod_type' (fun x μ => if (x, μ) ∈ D.touching then (W / ℓ₀) ^ 2 else 0)]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      congr 3
      ext b; simp
    rw [hsum]
    have hcard : (D.touching.card : ℝ) ≤ 2 * d * c := by
      rw [hc]; exact_mod_cast D.card_touching_le
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  -- site piece
  have hS : ‖D.sitePair α (svec G (φ0 - φm)) (svec G (φ0 - φm))‖ ≤
      c * (δ₀ / ℓ₀ ^ 2 * W ^ 2) := by
    unfold Region.sitePair
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (δ₀ / ℓ₀ ^ 2 * W ^ 2) ?_).trans
      (le_of_eq (by rw [nsmul_eq_mul])))
    intro x hx
    rw [norm_mul]
    have h1 : ‖zeroExt (G.Ω 1) α x‖ ≤ δ₀ / ℓ₀ ^ 2 := by
      have hxΩ := D.sub_Ω hx
      unfold zeroExt; rw [dite_eq_left_of_eq_true (eq_true hxΩ)]; exact hα ⟨x, hxΩ⟩ hx
    have h2 := (norm_sum_mul_le (svec G (φ0 - φm) x) (svec G (φ0 - φm) x)).trans
      (mul_self_le_mul_self (vnorm_nonneg _) (vnorm_svec_le Dat φ0 φm hW0 hW x))
    calc ‖zeroExt (G.Ω 1) α x‖ * ‖∑ i, svec G (φ0 - φm) x i * svec G (φ0 - φm) x i‖
        ≤ (δ₀ / ℓ₀ ^ 2) * (W * W) := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  -- mass piece
  have hM : ‖D.massPair (svec G (φ0 - φm)) (svec G (φ0 - φm))‖ ≤ c * W ^ 2 := by
    unfold Region.massPair
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (W ^ 2) ?_).trans
      (le_of_eq (by rw [nsmul_eq_mul])))
    intro x _
    have h2 := (norm_sum_mul_le (svec G (φ0 - φm) x) (svec G (φ0 - φm) x)).trans
      (mul_self_le_mul_self (vnorm_nonneg _) (vnorm_svec_le Dat φ0 φm hW0 hW x))
    nlinarith
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hδ' : δ₀ / ℓ₀ ^ 2 ≤ 1 / ℓ₀ ^ 2 := div_le_div_of_nonneg_right hδ₁ hℓ2.le
  -- assemble
  have e : 2 * massChangeChord D a ν Dat φ0 φm α =
      D.blockPair a (fun x i => blockAvg G (φ0 - φm) x i) (fun x i => blockAvg G (φ0 - φm) x i) +
      D.bondPair (wExt Dat Dat φm φ0) (wExt Dat Dat φm φ0) +
      D.sitePair α (svec G (φ0 - φm)) (svec G (φ0 - φm)) +
      (ν : ℂ) * D.massPair (svec G (φ0 - φm)) (svec G (φ0 - φm)) := by
    unfold massChangeChord; ring
  rw [e]
  have hνM : ‖(ν : ℂ) * D.massPair (svec G (φ0 - φm)) (svec G (φ0 - φm))‖ ≤
      (1 / ℓ₀ ^ 2) * (c * W ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hν0]
    exact mul_le_mul hν hM (norm_nonneg _) (by positivity)
  have t := norm_add₄_le (a := D.blockPair a (fun x i => blockAvg G (φ0 - φm) x i)
      (fun x i => blockAvg G (φ0 - φm) x i))
    (b := D.bondPair (wExt Dat Dat φm φ0) (wExt Dat Dat φm φ0))
    (c := D.sitePair α (svec G (φ0 - φm)) (svec G (φ0 - φm)))
    (d := (ν : ℂ) * D.massPair (svec G (φ0 - φm)) (svec G (φ0 - φm)))
  refine t.trans ?_
  have hS' : c * (δ₀ / ℓ₀ ^ 2 * W ^ 2) ≤ c * (1 / ℓ₀ ^ 2 * W ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδ' (by positivity)) hc0
  have e2 : (W / ℓ₀) ^ 2 = W ^ 2 / ℓ₀ ^ 2 := by rw [div_pow]
  rw [e2] at hBd
  have : (2 * d * c) * (W ^ 2 / ℓ₀ ^ 2) + c * (2 / ℓ₀ ^ 2 * W ^ 2) +
      c * (1 / ℓ₀ ^ 2 * W ^ 2) + (1 / ℓ₀ ^ 2) * (c * W ^ 2) =
      (2 * d + 4) * c / ℓ₀ ^ 2 * W ^ 2 := by ring
  linarith

/-- The arithmetic of the application: `M^d L^{q d} / (L^k)^2 = M^d L^{q (d-2) + 2}` for
`q = k + 1`, `d ≥ 2` (reals, `L ≠ 0`). -/
theorem region_ratio_eq (M Lr k e : ℕ) (hL : 0 < Lr) :
    ((M : ℝ) ^ (e + 2) * (Lr : ℝ) ^ ((k + 1) * (e + 2))) / ((Lr : ℝ) ^ k) ^ 2 =
      (M : ℝ) ^ (e + 2) * (Lr : ℝ) ^ ((k + 1) * e + 2) := by
  have : (Lr : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have h : (k + 1) * (e + 2) = ((k + 1) * e + 2) + 2 * k := by ring
  rw [h, pow_add, ← pow_mul]
  field_simp
  ring

/-- **The Hessian hypothesis of the wall estimate, from pointwise bounds** (T2). With
`W = Km Bh m`, `|D| ≤ Nsite · n`, one gets `hHess` with `CH = (2 d + 4) Nsite / ℓ₀²`. -/
theorem massChange_hHess_of_pointwise (D : Region G) (a : ℕ → ℝ) {ν : ℝ}
    (Dat : BgData G N) (φ0 φm : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ)
    {Km Bh m ℓ₀ δ₀ Nsite n : ℝ} (hW0 : 0 ≤ Km * Bh * m) (hℓ : 0 < ℓ₀)
    (hW : ∀ x, vnorm (wExt Dat Dat φm φ0 x) ≤ Km * Bh * m)
    (hbond : ∀ (x : Torus d (N₀ * L ^ K)) (μ : Fin d),
      (x ∈ D.sites ∨ x + Pi.single μ 1 ∈ D.sites) →
        vnorm (fun i => wExt Dat Dat φm φ0 (x + Pi.single μ 1) i - wExt Dat Dat φm φ0 x i)
          ≤ Km * Bh * m / ℓ₀)
    (hcoef : ∀ x ∈ D.sites,
      |a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2| ≤ 2 / ℓ₀ ^ 2)
    (hα : ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ K)) ∈ D.sites → ‖α x‖ ≤ δ₀ / ℓ₀ ^ 2)
    (hδ₀ : 0 ≤ δ₀) (hδ₁ : δ₀ ≤ 1) (hν0 : 0 ≤ ν) (hν : ν ≤ 1 / ℓ₀ ^ 2)
    (hcard : (D.sites.card : ℝ) ≤ Nsite * n) :
    ‖2 * massChangeChord D a ν Dat φ0 φm α‖ ≤
      ((2 * d + 4) * Nsite / ℓ₀ ^ 2) * n * (Km * Bh * m) ^ 2 := by
  refine (massChangeChord_norm_le_of_pointwise D a Dat φ0 φm α hW0 hℓ hW hbond hcoef hα hδ₀ hδ₁
    hν0 hν).trans ?_
  have h2 : 0 < ℓ₀ ^ 2 := by positivity
  have h3 : (2 * (d : ℝ) + 4) * (D.sites.card : ℝ) ≤ (2 * d + 4) * (Nsite * n) :=
    mul_le_mul_of_nonneg_left hcard (by positivity)
  have h4 := div_le_div_of_nonneg_right h3 h2.le
  have h5 := mul_le_mul_of_nonneg_right h4 (sq_nonneg (Km * Bh * m))
  refine h5.trans (le_of_eq ?_)
  ring

/-- **The wall sum** (MASS-RESPONSE (2.4)). -/
theorem crossing_sum_le (D : Region G) (r : Torus d (N₀ * L ^ K) × Fin d → ℝ) {ρ Ncross : ℝ}
    (hρ : ∀ b ∈ D.crossing, r b ≤ ρ) (hρ0 : 0 ≤ ρ) (hN : (D.crossing.card : ℝ) ≤ Ncross) :
    ∑ b ∈ D.crossing, r b ≤ Ncross * ρ :=
  (Finset.sum_le_card_nsmul _ _ ρ hρ).trans
    (by rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hN hρ0)

/-- **The region bound from the response** (MASS-RESPONSE (2.5)). -/
theorem massChange_region_bound_of_response (D : Region G) {a : ℕ → ℝ} {ν : ℝ} {Dat : BgData G N}
    {φ0 φm : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hEL : IsEL G a ν Dat φm α)
    (hφ0 : ∀ x : G.Ω 1, ∑ i, φ0 (x, i) * φ0 (x, i) = 1)
    {β m Km Bh ℓ₀ δ₀ Nsite n ρ Ncross : ℝ} (hβ : 0 ≤ β) (hW0 : 0 ≤ Km * Bh * m) (hℓ : 0 < ℓ₀)
    (hρ0 : 0 ≤ ρ)
    (hgrad : ∀ b ∈ D.crossing, vnorm (D.outwardDeriv (barField G Dat.Ψ φm) b) ≤ ρ)
    (hresp : ∀ x, vnorm (wExt Dat Dat φm φ0 x) ≤ Km * Bh * m)
    (hbond : ∀ (x : Torus d (N₀ * L ^ K)) (μ : Fin d),
      (x ∈ D.sites ∨ x + Pi.single μ 1 ∈ D.sites) →
        vnorm (fun i => wExt Dat Dat φm φ0 (x + Pi.single μ 1) i - wExt Dat Dat φm φ0 x i)
          ≤ Km * Bh * m / ℓ₀)
    (hcoef : ∀ x ∈ D.sites,
      |a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2| ≤ 2 / ℓ₀ ^ 2)
    (hα : ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ K)) ∈ D.sites → ‖α x‖ ≤ δ₀ / ℓ₀ ^ 2)
    (hδ₀ : 0 ≤ δ₀) (hδ₁ : δ₀ ≤ 1) (hν0 : 0 ≤ ν) (hν : ν ≤ 1 / ℓ₀ ^ 2)
    (hcard : (D.sites.card : ℝ) ≤ Nsite * n) (hNc : (D.crossing.card : ℝ) ≤ Ncross) :
    β * ‖actionRegionC D a ν Dat φ0 - actionRegionC D a ν Dat φm‖ ≤
      (1 / 2) * ((2 * d + 4) * Nsite / ℓ₀ ^ 2) * (Km * Bh) ^ 2 * β * m ^ 2 * n +
        Km * Bh * β * m * (Ncross * ρ) := by
  have h := massChange_wall_bound_of_bounds D hEL hφ0 (β := β) (m := m) (Km := Km) (Bh := Bh)
    (CH := (2 * d + 4) * Nsite / ℓ₀ ^ 2) (n := n) hβ (fun _ => ρ) hgrad hresp
    (massChange_hHess_of_pointwise D a Dat φ0 φm α hW0 hℓ hresp hbond hcoef hα hδ₀ hδ₁ hν0 hν
      hcard)
  have hs : ∑ b ∈ D.crossing, (fun _ => ρ) b ≤ Ncross * ρ :=
    crossing_sum_le D _ (fun _ _ => le_rfl) hρ0 hNc
  refine h.trans ?_
  have hk : 0 ≤ Km * Bh * β * m := by
    have : 0 ≤ Km * Bh * m * β := mul_nonneg hW0 hβ
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hs hk]

/-- **Non-vacuity of the pointwise premises** (T5).  On the one-scale generating set (`k = 1`,
`Ω₁` the whole torus), with `D` the whole torus (nonempty), `N = 1`, zero data, `φᵐ = 0` and
`φ⁰ ≡ 1` (so `φ⁰ ≠ φᵐ`), all pointwise premises of `massChangeChord_norm_le_of_pointwise` hold
with `W = ℓ₀ = 1`, `δ₀ = 0`, `ν = 0`.  (The Euler-Lagrange premise is not part of this statement;
no nonzero-difference `IsEL` pair is constructed here.) -/
theorem massChange_pointwise_premises_nonempty (ϱ : ℝ) :
    ∃ (D : Region (Balaban.Green.oneScaleSet d L N₀ 1 ϱ)) (a : ℕ → ℝ)
      (Dat : BgData (Balaban.Green.oneScaleSet d L N₀ 1 ϱ) 1)
      (φ0 φm : (Balaban.Green.oneScaleSet d L N₀ 1 ϱ).Ω 1 × Fin 1 → ℂ)
      (α : (Balaban.Green.oneScaleSet d L N₀ 1 ϱ).Ω 1 → ℂ),
      D.sites.Nonempty ∧ φ0 ≠ φm ∧
      (∀ x, vnorm (wExt Dat Dat φm φ0 x) ≤ 1) ∧
      (∀ (x : Torus d (N₀ * L ^ 1)) (μ : Fin d),
        (x ∈ D.sites ∨ x + Pi.single μ 1 ∈ D.sites) →
          vnorm (fun i => wExt Dat Dat φm φ0 (x + Pi.single μ 1) i - wExt Dat Dat φm φ0 x i)
            ≤ 1 / 1) ∧
      (∀ x ∈ D.sites, |a ((Balaban.Green.oneScaleSet d L N₀ 1 ϱ).layerIndex x) /
        ((L : ℝ) ^ (Balaban.Green.oneScaleSet d L N₀ 1 ϱ).layerIndex x) ^ 2| ≤ 2 / (1 : ℝ) ^ 2) ∧
      (∀ x : (Balaban.Green.oneScaleSet d L N₀ 1 ϱ).Ω 1,
        (x : Torus d (N₀ * L ^ 1)) ∈ D.sites → ‖α x‖ ≤ 0 / (1 : ℝ) ^ 2) := by
  classical
  let G := Balaban.Green.oneScaleSet d L N₀ 1 ϱ
  have hΩ : G.Ω 1 = Finset.univ := Balaban.Green.oneScaleSet_Ω_of_le ϱ le_rfl
  let D : Region G :=
    { sites := Finset.univ
      sub_Ω := by rw [hΩ]
      blockClosed := fun _ _ _ _ => Finset.mem_univ _ }
  let Dat : BgData G 1 :=
    { Ψ := fun _ _ => 0
      h := fun _ _ => 0
      Ψ_layerConst := fun _ _ _ _ _ _ _ => rfl
      h_layerConst := fun _ _ _ _ _ _ _ => rfl
      Ψ_zero := fun _ _ => rfl
      h_zero := fun _ _ => rfl }
  have hw : ∀ x, wExt Dat Dat (fun _ => (0 : ℂ)) (fun _ => (1 : ℂ)) x = fun _ => (1 : ℂ) := by
    intro x
    have hx : x ∈ G.Ω 1 := by rw [hΩ]; exact Finset.mem_univ _
    funext i
    simp [wExt, barField, hx]
  have hv1 : vnorm (fun _ : Fin 1 => (1 : ℂ)) ≤ 1 := by
    unfold vnorm
    rw [EuclideanSpace.norm_eq]
    simp
  have hv0 : vnorm (fun _ : Fin 1 => (0 : ℂ)) = 0 := by
    unfold vnorm
    have h0 : (WithLp.toLp 2 (fun _ : Fin 1 => (0 : ℂ)) : EuclideanSpace ℂ (Fin 1)) = 0 := rfl
    rw [h0, norm_zero]
  refine ⟨D, fun _ => 0, Dat, fun _ => 1, fun _ => 0, fun _ => 0, Finset.univ_nonempty, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro h
    have h0 : (0 : Torus d (N₀ * L ^ 1)) ∈ G.Ω 1 := by rw [hΩ]; exact Finset.mem_univ _
    have := congrFun h (⟨0, h0⟩, 0)
    simp at this
  · intro x; rw [hw]; exact hv1
  · intro x μ _
    have e : (fun i => wExt Dat Dat (fun _ => (0 : ℂ)) (fun _ => (1 : ℂ)) (x + Pi.single μ 1) i -
        wExt Dat Dat (fun _ => (0 : ℂ)) (fun _ => (1 : ℂ)) x i) = fun _ => (0 : ℂ) := by
      funext i; rw [hw, hw]; simp
    rw [e, hv0]; norm_num
  · intro x _; simp
  · intro x _; simp

end Balaban.LargeField.ActionConv
