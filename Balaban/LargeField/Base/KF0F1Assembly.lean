/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.KF0WalkHalo
public import Balaban.LargeField.Base.KF0TaylorMajorant
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `KF0F1Assembly`: Theorem F.1 for the site and bond functions of the all-plus sector

Part F.2 of `notes/phase1/LF-BASE-KF0.md`.  Assembly of two landed pieces:

* `Balaban/Green/KF0WalkHalo.lean`: walk-indexed terms of the expansion of an analytic function of
  `u = β^{-1/2} K_ν^{-1/2} ψ`, their connected halo, the block count (F.10) and the weighted bound;
* `Balaban/LargeField/Base/KF0TaylorMajorant.lean`: the Taylor coefficients `siteCoeff`,
  `bondCoeff` of the site and bond functions (F.11) with their absolute majorants (F.12).

Contents.

* (T1) On the product cutoff event `sup_y ‖ψ_y‖ ≤ p` the site function and the bond function are the
  sums of absolutely convergent families of walk-indexed terms, and
  `∑_index e^{κ k_s(halo)} sup_cutoff |term| ≤ M(ρ)` with `ρ = e^{κ 3^d} p A_γ / √β`.
* (T2) `kf0HaloTerm`: the sum of the terms with a given halo `H`.  It depends on `ψ` only on `H`,
  vanishes unless `H` is nearest-neighbour connected and contains a point of the anchor set, the
  functions add up to the function, and `∑_H e^{κ k_s(H)} sup_cutoff |F_H| ≤ M(ρ)`.
* (T3) The landed all-plus integrand (Jacobian times the exponential of the interaction exponent)
  equals the exponential of the source constant plus the sum of the regrouped site and bond terms,
  and the total weighted norm tends to `0` as `β → ∞`.
* (T4) An explicit instance.

This file is about the all-plus sector on the product cutoff event only.  The heavy sector, the
gas construction and the one-scale theorem are NOT proved here.
-/

@[expose] public section

namespace Balaban.LargeField.KF0F1

open Finset Balaban.Green Balaban.LargeField

/-! ### Regrouping a summable family by a function with finite range -/

section Regroup

variable {ι σ : Type*} [Fintype σ]

/-- The sum of `t a` over the indices `a` with `halo a = H`. -/
noncomputable def haloPiece (halo : ι → σ) (t : ι → ℝ) (H : σ) : ℝ :=
  ∑' a : halo ⁻¹' {H}, t a

theorem sum_haloPiece_eq {halo : ι → σ} {t : ι → ℝ} {S : ℝ} (hS : HasSum t S) :
    ∑ H, haloPiece halo t H = S :=
  ((hS.tsum_fiberwise halo).unique (hasSum_fintype _)).symm

omit [Fintype σ] in
theorem weighted_haloPiece_le {halo : ι → σ} {t B : ι → ℝ} {w : σ → ℝ} (hB : Summable B)
    (hw : ∀ H, 0 < w H) (h : ∀ a, w (halo a) * |t a| ≤ B a) (H : σ) :
    w H * |haloPiece halo t H| ≤ haloPiece halo B H := by
  have hs : Summable (fun a : halo ⁻¹' {H} => B a) := hB.subtype _
  have hle : ∀ a : halo ⁻¹' {H}, ‖w H * t a‖ ≤ B a := by
    intro a
    have ha : halo a = H := a.2
    have := h a
    rw [ha] at this
    rwa [norm_mul, Real.norm_of_nonneg (hw H).le, Real.norm_eq_abs]
  have := tsum_of_norm_bounded hs.hasSum hle
  rw [tsum_mul_left, norm_mul, Real.norm_of_nonneg (hw H).le, Real.norm_eq_abs] at this
  exact this

end Regroup

/-! ### The cutoff supremum and the generic localization -/

section Generic

variable {d m : ℕ} [NeZero m] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {D : ℕ}

/-- The supremum of `|f ψ|` over the product cutoff event `sup_y ‖ψ_y‖ ≤ p`. -/
noncomputable def cutoffSup (p : ℝ) (f : (Torus d m → W) → ℝ) : ℝ :=
  ⨆ ψ : {ψ : Torus d m → W // ∀ y, ‖ψ y‖ ≤ p}, |f ψ.1|

omit [NeZero m] [NormedSpace ℝ W] in
theorem cutoffSup_nonneg (p : ℝ) (f : (Torus d m → W) → ℝ) : 0 ≤ cutoffSup p f :=
  Real.iSup_nonneg fun _ => abs_nonneg _

omit [NeZero m] [NormedSpace ℝ W] in
theorem le_cutoffSup_of_le {p : ℝ} (hp0 : 0 ≤ p) {f : (Torus d m → W) → ℝ} {c : ℝ}
    (h : ∀ ψ : Torus d m → W, (∀ y, ‖ψ y‖ ≤ p) → |f ψ| ≤ c) : cutoffSup p f ≤ c := by
  have : Nonempty {ψ : Torus d m → W // ∀ y, ‖ψ y‖ ≤ p} := ⟨⟨0, fun y => by simpa using hp0⟩⟩
  exact ciSup_le fun ψ => h ψ.1 ψ.2

/-- The radius `ρ = e^{κ 3^d} p A_γ / √β` of (F.7). -/
noncomputable def kf0Rho (d : ℕ) (g γ κ p β : ℝ) : ℝ :=
  Real.exp (κ * 3 ^ d) * (p * kf0WalkA d g γ / Real.sqrt β)

/-- The `F.8` weighted pointwise bound of one term of the walk series. -/
theorem walkSeriesTerm_weighted_le {ν : ℝ} (hν : 0 < ν) {s m' : ℕ} [NeZero m'] (hs : 0 < s)
    (hm : m = s * m') {κ : ℝ} (hκ : 0 ≤ κ) {γ : ℝ} (hγ : κ * 3 ^ d / s ≤ γ) (β : ℝ) {p : ℝ}
    (x : Fin D → Torus d m) (ℓ : Fin D → W →L[ℝ] ℝ) (hℓ : ∀ j, ‖ℓ j‖ ≤ 1)
    (c : (Fin D → ℕ) → ℝ) (a : KF0WalkSeriesIndex d D) (ψ : Torus d m → W)
    (hp : ∀ y, ‖ψ y‖ ≤ p) :
    Real.exp (κ * kf0BlockCount s m' (kf0WalkSeriesHalo x a)) *
        ‖kf0WalkSeriesTerm d m ν β x ℓ c ψ a‖ ≤
      kf0WalkSeriesBound d ν β γ p (Real.exp (κ * 3 ^ d)) c a := by
  have h := kf0WalkTerm_blockweight_le (m := m) hν hs hm hκ hγ β p
    (fun t : KF0Slot a.1 => x t.1) (fun t => ℓ t.1) (fun t => hℓ t.1) a.2 ψ hp
  rw [card_kf0Slot] at h
  have e : Real.exp (κ * 3 ^ d * ((∑ j, a.1 j : ℕ) : ℝ)) =
      Real.exp (κ * 3 ^ d) ^ (∑ j, a.1 j) := by rw [mul_comm, Real.exp_nat_mul]
  rw [e] at h
  simp only [kf0WalkSeriesTerm, kf0WalkSeriesBound, kf0WalkSeriesHalo, norm_mul]
  calc _ = ‖c a.1‖ *
        (Real.exp (κ * kf0BlockCount s m' (walkHalo (fun t : KF0Slot a.1 => x t.1) a.2)) *
          ‖kf0WalkTerm d m ν β (fun t : KF0Slot a.1 => x t.1) (fun t => ℓ t.1) a.2 ψ‖) := by
        ring
    _ ≤ ‖c a.1‖ * (Real.exp (κ * 3 ^ d) ^ (∑ j, a.1 j) * kf0WalkBound d ν β γ p a.2) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = _ := by ring

/-- **(T1, generic)** The weighted sum over the walk-series index of the cutoff suprema of the
terms is at most the majorant `∑_α ‖c_α‖ ρ^{|α|}`. -/
theorem walkSeries_cutoffSup_summable {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ}
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) {s m' : ℕ} [NeZero m'] (hs : 0 < s)
    (hm : m = s * m') {κ : ℝ} (hκ : 0 ≤ κ) (hγ : κ * 3 ^ d / s ≤ γ) (β : ℝ) {p : ℝ}
    (hp0 : 0 ≤ p) (x : Fin D → Torus d m) (ℓ : Fin D → W →L[ℝ] ℝ) (hℓ : ∀ j, ‖ℓ j‖ ≤ 1)
    (c : (Fin D → ℕ) → ℝ)
    (hM : Summable fun α : Fin D → ℕ => ‖c α‖ * kf0Rho d g γ κ p β ^ (∑ j, α j)) :
    Summable (fun a : KF0WalkSeriesIndex d D =>
      Real.exp (κ * kf0BlockCount s m' (kf0WalkSeriesHalo x a)) *
        cutoffSup p (fun ψ => kf0WalkSeriesTerm d m ν β x ℓ c ψ a)) ∧
    ∑' a : KF0WalkSeriesIndex d D, Real.exp (κ * kf0BlockCount s m' (kf0WalkSeriesHalo x a)) *
        cutoffSup p (fun ψ => kf0WalkSeriesTerm d m ν β x ℓ c ψ a) ≤
      ∑' α : Fin D → ℕ, ‖c α‖ * kf0Rho d g γ κ p β ^ (∑ j, α j) := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  obtain ⟨hB, hB2⟩ := kf0WalkSeriesBound_summable (d := d) (ν := ν) hg hgν hq β hp0
    (Real.exp_pos (κ * 3 ^ d)).le c hM
  have hle : ∀ a : KF0WalkSeriesIndex d D,
      Real.exp (κ * kf0BlockCount s m' (kf0WalkSeriesHalo x a)) *
        cutoffSup p (fun ψ => kf0WalkSeriesTerm d m ν β x ℓ c ψ a) ≤
      kf0WalkSeriesBound d ν β γ p (Real.exp (κ * 3 ^ d)) c a := by
    intro a
    have hw := Real.exp_pos (κ * kf0BlockCount s m' (kf0WalkSeriesHalo x a))
    have : cutoffSup p (fun ψ => kf0WalkSeriesTerm d m ν β x ℓ c ψ a) ≤
        kf0WalkSeriesBound d ν β γ p (Real.exp (κ * 3 ^ d)) c a /
          Real.exp (κ * kf0BlockCount s m' (kf0WalkSeriesHalo x a)) := by
      refine le_cutoffSup_of_le hp0 fun ψ hψ => ?_
      rw [le_div_iff₀' hw]
      have := walkSeriesTerm_weighted_le hν hs hm hκ hγ β x ℓ hℓ c a ψ hψ
      rwa [← Real.norm_eq_abs]
    exact (le_div_iff₀' hw).1 this
  have hnn : ∀ a : KF0WalkSeriesIndex d D,
      0 ≤ Real.exp (κ * kf0BlockCount s m' (kf0WalkSeriesHalo x a)) *
        cutoffSup p (fun ψ => kf0WalkSeriesTerm d m ν β x ℓ c ψ a) := fun a =>
    mul_nonneg (Real.exp_pos _).le (cutoffSup_nonneg _ _)
  have hsum := Summable.of_nonneg_of_le hnn hle hB
  exact ⟨hsum, (hsum.tsum_le_tsum hle hB).trans hB2⟩

/-- **(T1, generic)** On the cutoff event the walk-indexed family is absolutely summable and sums
to the series `∑_α c_α ∏_j (ℓ_j u_{x_j})^{α_j}`, `u = β^{-1/2} K_ν^{-1/2} ψ`. -/
theorem walkSeries_hasSum {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ} (hγ : 0 ≤ γ)
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) {κ : ℝ} (hκ : 0 ≤ κ) (β : ℝ) {p : ℝ}
    (hp0 : 0 ≤ p) (x : Fin D → Torus d m) (ℓ : Fin D → W →L[ℝ] ℝ) (hℓ : ∀ j, ‖ℓ j‖ ≤ 1)
    (c : (Fin D → ℕ) → ℝ)
    (hM : Summable fun α : Fin D → ℕ => ‖c α‖ * kf0Rho d g γ κ p β ^ (∑ j, α j))
    (ψ : Torus d m → W) (hp : ∀ y, ‖ψ y‖ ≤ p) :
    Summable (fun a => ‖kf0WalkSeriesTerm d m ν β x ℓ c ψ a‖) ∧
      HasSum (kf0WalkSeriesTerm d m ν β x ℓ c ψ)
        (∑' α : Fin D → ℕ, c α * ∏ j, (ℓ j ((Real.sqrt β)⁻¹ •
          matAct (kf0C d m ν) ψ (x j))) ^ (α j)) :=
  kf0WalkSeriesTerm_hasSum hg hgν hγ hq β hp0
    (Real.one_le_exp (mul_nonneg hκ (by positivity))) x ℓ hℓ c hM ψ hp

/-! ### (T2) The halo pieces -/

/-- `F_H`: the sum of the walk-series terms whose halo is the finite site set `H`. -/
noncomputable def kf0HaloTerm (d m : ℕ) [NeZero m] (ν β : ℝ) (x : Fin D → Torus d m)
    (ℓ : Fin D → W →L[ℝ] ℝ) (c : (Fin D → ℕ) → ℝ) (H : Finset (Torus d m))
    (ψ : Torus d m → W) : ℝ :=
  haloPiece (kf0WalkSeriesHalo x) (fun a => kf0WalkSeriesTerm d m ν β x ℓ c ψ a) H

/-- `F_H ψ` depends on `ψ` only on `H`. -/
theorem kf0HaloTerm_congr (ν β : ℝ) (x : Fin D → Torus d m) (ℓ : Fin D → W →L[ℝ] ℝ)
    (c : (Fin D → ℕ) → ℝ) (H : Finset (Torus d m)) {ψ ψ' : Torus d m → W}
    (h : ∀ b ∈ H, ψ b = ψ' b) :
    kf0HaloTerm d m ν β x ℓ c H ψ = kf0HaloTerm d m ν β x ℓ c H ψ' := by
  unfold kf0HaloTerm haloPiece
  refine tsum_congr fun a => ?_
  have ha : kf0WalkSeriesHalo x a.1 = H := a.2
  simp only [kf0WalkSeriesTerm]
  rw [kf0WalkTerm_congr ν β (fun s : KF0Slot a.1.1 => x s.1) (fun s => ℓ s.1) a.1.2
    (ψ := ψ) (ψ' := ψ') (fun b hb => h b (by rw [← ha]; exact hb))]

omit [NeZero m] in
/-- The halo of an index with a nonempty slot contains the corresponding anchor and is
nearest-neighbour connected when the anchors are equal or adjacent. -/
theorem kf0WalkSeriesHalo_spec (x : Fin D → Torus d m)
    (hU : ∀ i j, x i = x j ∨ ∃ μ : Fin d, x j = x i + Pi.single μ 1 ∨ x i = x j + Pi.single μ 1)
    (a : KF0WalkSeriesIndex d D) :
    NNConnected (kf0WalkSeriesHalo x a) ∧ ∀ j, a.1 j ≠ 0 → x j ∈ kf0WalkSeriesHalo x a := by
  refine ⟨walkHalo_nnConnected (fun s : KF0Slot a.1 => x s.1) a.2 (fun i j => hU i.1 j.1), ?_⟩
  intro j hj
  exact anchor_mem_walkHalo (fun s : KF0Slot a.1 => x s.1) a.2 ⟨j, ⟨0, Nat.pos_of_ne_zero hj⟩⟩

/-- `F_H = 0` unless `H` is nearest-neighbour connected and contains a point of the anchor set
(for coefficient families with `c 0 = 0`). -/
theorem kf0HaloTerm_eq_zero (ν β : ℝ) (x : Fin D → Torus d m) (ℓ : Fin D → W →L[ℝ] ℝ)
    (c : (Fin D → ℕ) → ℝ) (hc0 : c 0 = 0)
    (hU : ∀ i j, x i = x j ∨ ∃ μ : Fin d, x j = x i + Pi.single μ 1 ∨ x i = x j + Pi.single μ 1)
    (H : Finset (Torus d m)) (hH : ¬ (NNConnected H ∧ ∃ j, x j ∈ H)) (ψ : Torus d m → W) :
    kf0HaloTerm d m ν β x ℓ c H ψ = 0 := by
  unfold kf0HaloTerm haloPiece
  refine (tsum_congr (g := fun _ => (0 : ℝ)) fun a => ?_).trans tsum_zero
  have ha : kf0WalkSeriesHalo x a.1 = H := a.2
  by_cases h0 : a.1.1 = 0
  · have : c a.1.1 = 0 := by rw [h0]; exact hc0
    simp [kf0WalkSeriesTerm, this]
  · exfalso
    obtain ⟨j, hj⟩ := Function.ne_iff.1 h0
    obtain ⟨h1, h2⟩ := kf0WalkSeriesHalo_spec x hU a.1
    exact hH ⟨ha ▸ h1, j, ha ▸ h2 j hj⟩

/-- The halo pieces add up to the walk-series sum on the cutoff event. -/
theorem sum_kf0HaloTerm {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ} (hγ : 0 ≤ γ)
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) {κ : ℝ} (hκ : 0 ≤ κ) (β : ℝ) {p : ℝ}
    (hp0 : 0 ≤ p) (x : Fin D → Torus d m) (ℓ : Fin D → W →L[ℝ] ℝ) (hℓ : ∀ j, ‖ℓ j‖ ≤ 1)
    (c : (Fin D → ℕ) → ℝ)
    (hM : Summable fun α : Fin D → ℕ => ‖c α‖ * kf0Rho d g γ κ p β ^ (∑ j, α j))
    (ψ : Torus d m → W) (hp : ∀ y, ‖ψ y‖ ≤ p) :
    ∑ H, kf0HaloTerm d m ν β x ℓ c H ψ =
      ∑' α : Fin D → ℕ, c α * ∏ j, (ℓ j ((Real.sqrt β)⁻¹ •
          matAct (kf0C d m ν) ψ (x j))) ^ (α j) :=
  sum_haloPiece_eq (walkSeries_hasSum hg hgν hγ hq hκ β hp0 x ℓ hℓ c hM ψ hp).2

/-- **(F.8, generic)** `∑_H e^{κ k_s(H)} sup_cutoff |F_H| ≤ ∑_α ‖c_α‖ ρ^{|α|}`. -/
theorem weighted_kf0HaloTerm_le {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ}
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) {s m' : ℕ} [NeZero m'] (hs : 0 < s)
    (hm : m = s * m') {κ : ℝ} (hκ : 0 ≤ κ) (hγ : κ * 3 ^ d / s ≤ γ) (β : ℝ) {p : ℝ}
    (hp0 : 0 ≤ p) (x : Fin D → Torus d m) (ℓ : Fin D → W →L[ℝ] ℝ) (hℓ : ∀ j, ‖ℓ j‖ ≤ 1)
    (c : (Fin D → ℕ) → ℝ)
    (hM : Summable fun α : Fin D → ℕ => ‖c α‖ * kf0Rho d g γ κ p β ^ (∑ j, α j)) :
    ∑ H : Finset (Torus d m), Real.exp (κ * kf0BlockCount s m' H) *
        cutoffSup p (kf0HaloTerm d m ν β x ℓ c H) ≤
      ∑' α : Fin D → ℕ, ‖c α‖ * kf0Rho d g γ κ p β ^ (∑ j, α j) := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  obtain ⟨hB, hB2⟩ := kf0WalkSeriesBound_summable (d := d) (ν := ν) hg hgν hq β hp0
    (Real.exp_pos (κ * 3 ^ d)).le c hM
  set B := kf0WalkSeriesBound d ν β γ p (Real.exp (κ * 3 ^ d)) c with hBdef
  set w : Finset (Torus d m) → ℝ := fun H => Real.exp (κ * kf0BlockCount s m' H) with hw
  have hwpos : ∀ H, 0 < w H := fun H => Real.exp_pos _
  have hH : ∀ H, w H * cutoffSup p (kf0HaloTerm d m ν β x ℓ c H) ≤
      haloPiece (kf0WalkSeriesHalo x) B H := by
    intro H
    have : cutoffSup p (kf0HaloTerm d m ν β x ℓ c H) ≤
        haloPiece (kf0WalkSeriesHalo x) B H / w H := by
      refine le_cutoffSup_of_le hp0 fun ψ hψ => ?_
      rw [le_div_iff₀' (hwpos H)]
      unfold kf0HaloTerm
      exact weighted_haloPiece_le hB hwpos (fun a => by
        have := walkSeriesTerm_weighted_le hν hs hm hκ hγ β x ℓ hℓ c a ψ hψ
        simpa only [Real.norm_eq_abs] using this) H
    exact (le_div_iff₀' (hwpos H)).1 this
  calc _ ≤ ∑ H, haloPiece (kf0WalkSeriesHalo x) B H := Finset.sum_le_sum fun H _ => hH H
    _ = ∑' a, B a := sum_haloPiece_eq hB.hasSum
    _ ≤ _ := hB2



/-! ### The polydisc bound and the coefficient at the origin -/

section Polydisc

omit [NormedSpace ℝ W] in
theorem kf0WalkA_pos {d : ℕ} {g γ : ℝ} (hg : 0 < g)
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) : 0 < kf0WalkA d g γ :=
  div_pos (inv_pos.2 (Real.sqrt_pos.2 hg)) (by linarith)

theorem kf0Rho_pos {g γ κ p β : ℝ} (hg : 0 < g) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1)
    (hp : 0 < p) (hβ : 0 < β) : 0 < kf0Rho d g γ κ p β :=
  mul_pos (Real.exp_pos _) (div_pos (mul_pos hp (kf0WalkA_pos (d := d) hg hq))
    (Real.sqrt_pos.2 hβ))

/-- On the cutoff event `‖u_y‖ ≤ ρ`, `u = β^{-1/2} K_ν^{-1/2} ψ`. -/
theorem norm_u_le_kf0Rho {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ} (hγ : 0 ≤ γ)
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) {κ : ℝ} (hκ : 0 ≤ κ) (β : ℝ) {p : ℝ}
    (hp0 : 0 ≤ p) (ψ : Torus d m → W) (hψ : ∀ y, ‖ψ y‖ ≤ p) (y : Torus d m) :
    ‖(Real.sqrt β)⁻¹ • matAct (kf0C d m ν) ψ y‖ ≤ kf0Rho d g γ κ p β := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  obtain ⟨hs, hb⟩ := kf0_substitution_weighted (d := d) (m := m) (ν := ν) hg hgν hq β ψ hp0 hψ y
  have hle : ∀ q : ℕ × Torus d m, ‖kf0WalkCoeff d m ν β q.1 y q.2 • ψ q.2‖ ≤
      Real.exp (γ * q.1) * ‖kf0WalkCoeff d m ν β q.1 y q.2 • ψ q.2‖ := fun q => by
    have : 1 ≤ Real.exp (γ * q.1) := Real.one_le_exp (mul_nonneg hγ (Nat.cast_nonneg _))
    nlinarith [norm_nonneg (kf0WalkCoeff d m ν β q.1 y q.2 • ψ q.2)]
  have h1 := tsum_of_norm_bounded hs.hasSum hle
  rw [(kf0_substitution_hasSum hν β ψ y).tsum_eq] at h1
  refine h1.trans (hb.trans ?_)
  unfold kf0Rho
  have h0 : 0 ≤ p * kf0WalkA d g γ / Real.sqrt β :=
    div_nonneg (mul_nonneg hp0 (kf0WalkA_pos (d := d) hg hq).le) (Real.sqrt_nonneg _)
  have := Real.one_le_exp (mul_nonneg hκ (by positivity : (0 : ℝ) ≤ 3 ^ d))
  nlinarith

omit [NeZero m] [NormedSpace ℝ W] in
/-- The coefficient at the origin is the value at `0`. -/
theorem coeff_zero_of_hasSum {c : (Fin D → ℕ) → ℝ} {F : ℝ}
    (h : HasSum (fun α => c α * ∏ i, (0 : ℝ) ^ α i) F) : c 0 = F := by
  have h1 : HasSum (fun α => c α * ∏ i, (0 : ℝ) ^ α i) (c 0 * ∏ i, (0 : ℝ) ^ (0 : Fin D → ℕ) i) :=
    hasSum_single 0 fun α hα => by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hα
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (zero_pow hi), mul_zero]
  simpa using h1.unique h

end Polydisc

end Generic


/-! ### The tangent coordinates -/

section Tangent

open SphereChart

variable {N n : ℕ} {h : EuclideanSpace ℝ (Fin N)}

/-- The `j`-th coordinate functional `w ↦ ⟨e_j, w⟩` of the orthonormal basis `e` of `h^⊥`. -/
noncomputable def tcoord (e : OrthonormalBasis (Fin n) ℝ (perp h)) (j : Fin n) :
    perp h →L[ℝ] ℝ := innerSL ℝ (e j)

theorem norm_tcoord_le (e : OrthonormalBasis (Fin n) ℝ (perp h)) (j : Fin n) :
    ‖tcoord e j‖ ≤ 1 := by
  simp [tcoord, innerSL_apply_norm]

theorem tcoord_apply (e : OrthonormalBasis (Fin n) ℝ (perp h)) (j : Fin n) (w : perp h) :
    tcoord e j w = inner ℝ (e j) w := by
  simp [tcoord]

theorem sum_sq_tcoord (e : OrthonormalBasis (Fin n) ℝ (perp h)) (w : perp h) :
    ∑ j, tcoord e j w ^ 2 = ‖w‖ ^ 2 := by
  rw [← e.sum_sq_norm_inner_right w]
  simp [tcoord_apply]

theorem sum_lin_tcoord (e : OrthonormalBasis (Fin n) ℝ (perp h)) (c : Fin N → ℝ) (w : perp h) :
    ∑ j, (∑ i, c i * ((e j : perp h) : EuclideanSpace ℝ (Fin N)) i) * tcoord e j w =
      ∑ i, c i * (w : EuclideanSpace ℝ (Fin N)) i := by
  have hw := e.sum_repr' w
  have key : ∀ i, (w : EuclideanSpace ℝ (Fin N)) i =
      ∑ j, inner ℝ (e j) w * ((e j : perp h) : EuclideanSpace ℝ (Fin N)) i := by
    intro i
    have := congrArg (fun w : perp h => (w : EuclideanSpace ℝ (Fin N)) i) hw
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    rw [← this]
    simp
  simp_rw [Finset.sum_mul, tcoord_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [key i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Existence of an orthonormal basis of `h^⊥` indexed by `Fin (N - 1)`. -/
theorem nonempty_tangent_basis (hh : ‖h‖ = 1) :
    Nonempty (OrthonormalBasis (Fin (N - 1)) ℝ (perp h)) :=
  ⟨(stdOrthonormalBasis ℝ (perp h)).reindex
    (finCongr (by have := finrank_perp h hh; omega))⟩

end Tangent


/-! ### The site and bond functions of the landed chart -/

section Functions

open SphereChart Balaban.LargeField.KF0Taylor

variable {d N ℓ n : ℕ} [NeZero ℓ] {h : EuclideanSpace ℝ (Fin N)}

/-- The tangent field `v = K_ν^{-1/2} ψ` of the landed chart. -/
noncomputable abbrev tfield (d ℓ : ℕ) [NeZero ℓ] (ν : ℝ) (ψ : Torus d ℓ → perp h) :
    Torus d ℓ → perp h := matAct (kf0SqrtR d ℓ ν) ψ

/-- The normal part `g_x · h` of the source at `x`. -/
def f1Nrm (g : Torus d ℓ → Fin N → ℝ) (h : EuclideanSpace ℝ (Fin N)) (x : Torus d ℓ) : ℝ :=
  ∑ i, g x i * h i

/-- The tangent components `b_j = g_x · e_j` of the source at `x`. -/
noncomputable def f1Lin (e : OrthonormalBasis (Fin n) ℝ (perp h)) (g : Torus d ℓ → Fin N → ℝ)
    (x : Torus d ℓ) : Fin n → ℝ :=
  fun j => ∑ i, g x i * ((e j : perp h) : EuclideanSpace ℝ (Fin N)) i

/-- **The site function** of the all-plus sector at `x` (F.11) on the chart variable
`v = K_ν^{-1/2} ψ`: the site profile (Jacobian term, mass term, normal source) plus the tangent
source `β^{-1/2} ∑_i g_{x,i} v_{x,i}`. -/
noncomputable def f1SiteValue (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d ℓ → Fin N → ℝ) (ψ : Torus d ℓ → perp h) (x : Torus d ℓ) : ℝ :=
  siteProfile β ν (f1Nrm g h x) (‖tfield d ℓ ν ψ x‖ ^ 2 / β) +
    (Real.sqrt β)⁻¹ * ∑ i, g x i * ((tfield d ℓ ν ψ x : perp h) : EuclideanSpace ℝ (Fin N)) i

/-- **The bond function** of the all-plus sector for the forward bond `(x, x + e_μ)` (F.11). -/
noncomputable def f1BondValue (β ν : ℝ) (ψ : Torus d ℓ → perp h) (x : Torus d ℓ) (μ : Fin d) :
    ℝ :=
  bondProfile β (‖tfield d ℓ ν ψ (x + Pi.single μ 1)‖ ^ 2 / β) (‖tfield d ℓ ν ψ x‖ ^ 2 / β)

/-- The anchors of the bond function: `n` copies of `y₁` then `n` copies of `y₂`. -/
noncomputable def bondAnchor (n : ℕ) (y₁ y₂ : Torus d ℓ) : Fin (n + n) → Torus d ℓ :=
  Fin.append (fun _ : Fin n => y₁) (fun _ : Fin n => y₂)

/-- The coordinate functionals of the two sites of a bond. -/
noncomputable def bondEll (e : OrthonormalBasis (Fin n) ℝ (perp h)) :
    Fin (n + n) → perp h →L[ℝ] ℝ :=
  Fin.append (tcoord e) (tcoord e)

theorem norm_bondEll_le (e : OrthonormalBasis (Fin n) ℝ (perp h)) (j : Fin (n + n)) :
    ‖bondEll e j‖ ≤ 1 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa [bondEll] using norm_tcoord_le e i
  · have : bondEll e (Fin.natAdd n i) = tcoord e i := Fin.append_right _ _ _
    rw [this]; exact norm_tcoord_le e i

omit [NeZero ℓ] in
theorem bondAnchor_adj (n : ℕ) (x : Torus d ℓ) (μ : Fin d) (i j : Fin (n + n)) :
    bondAnchor n (x + Pi.single μ 1) x i = bondAnchor n (x + Pi.single μ 1) x j ∨
      ∃ μ' : Fin d, bondAnchor n (x + Pi.single μ 1) x j =
          bondAnchor n (x + Pi.single μ 1) x i + Pi.single μ' 1 ∨
        bondAnchor n (x + Pi.single μ 1) x i =
          bondAnchor n (x + Pi.single μ 1) x j + Pi.single μ' 1 := by
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
  refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
  simp only [bondAnchor, Fin.append_left, Fin.append_right]
  all_goals first
    | exact Or.inl rfl
    | exact Or.inl trivial
    | exact Or.inr ⟨μ, Or.inr rfl⟩
    | exact Or.inr ⟨μ, Or.inl rfl⟩

/-- The site function is the Taylor function `siteFn` of the coordinates `ℓ_j u_x`. -/
theorem f1SiteValue_eq {β : ℝ} (hβ : 0 < β) {ν : ℝ} (hν : 0 < ν)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (g : Torus d ℓ → Fin N → ℝ)
    (ψ : Torus d ℓ → perp h) (x : Torus d ℓ) :
    f1SiteValue β ν h g ψ x = siteFn β ν (f1Nrm g h x) (f1Lin e g x)
      (fun j => tcoord e j ((Real.sqrt β)⁻¹ • matAct (kf0C d ℓ ν) ψ x)) := by
  have hC : matAct (kf0C d ℓ ν) ψ x = tfield d ℓ ν ψ x := by
    rw [kf0C_eq_kf0SqrtR hν]
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  unfold siteFn f1SiteValue
  rw [hC]
  congr 1
  · congr 1
    rw [sum_sq_tcoord, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), mul_pow,
      inv_pow, Real.sq_sqrt hβ.le]
    ring
  · have := sum_lin_tcoord e (fun i => g x i) ((Real.sqrt β)⁻¹ • tfield d ℓ ν ψ x)
    simp only [f1Lin]
    rw [this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Submodule.coe_smul, PiLp.smul_apply, smul_eq_mul]
    ring

/-- The bond function is the Taylor function `bondFn` of the coordinates of the two sites. -/
theorem f1BondValue_eq {β : ℝ} (hβ : 0 < β) {ν : ℝ} (hν : 0 < ν)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (ψ : Torus d ℓ → perp h) (x : Torus d ℓ)
    (μ : Fin d) :
    f1BondValue β ν ψ x μ = bondFn β (bondFst n) (bondSnd n)
      (fun i => bondEll e i ((Real.sqrt β)⁻¹ •
        matAct (kf0C d ℓ ν) ψ (bondAnchor n (x + Pi.single μ 1) x i))) := by
  have hC : ∀ y, matAct (kf0C d ℓ ν) ψ y = tfield d ℓ ν ψ y := by
    intro y; rw [kf0C_eq_kf0SqrtR hν]
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hq : ∀ y, ∑ j, tcoord e j ((Real.sqrt β)⁻¹ • tfield d ℓ ν ψ y) ^ 2 =
      ‖tfield d ℓ ν ψ y‖ ^ 2 / β := by
    intro y
    rw [sum_sq_tcoord, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), mul_pow,
      inv_pow, Real.sq_sqrt hβ.le]
    ring
  unfold bondFn f1BondValue
  congr 1
  · rw [bondFst, Finset.sum_image (fun a _ b _ hab => Fin.castAdd_injective n n hab)]
    simp only [bondEll, bondAnchor, Fin.append_left, hC]
    exact (hq _).symm
  · rw [bondSnd, Finset.sum_image (fun a _ b _ hab => Fin.natAdd_injective n n hab)]
    simp only [bondEll, bondAnchor, Fin.append_right, hC]
    exact (hq _).symm

end Functions


/-! ### (T1), (T2) for the site function and the bond function -/

section LocalizeFunctions

open SphereChart Balaban.LargeField.KF0Taylor

variable {d N ℓ n : ℕ} [NeZero ℓ] {h : EuclideanSpace ℝ (Fin N)}

theorem maj_series {D : ℕ} {c : (Fin D → ℕ) → ℝ} {ρ M : ℝ} (hc : Maj c ρ M) :
    Summable (fun α : Fin D → ℕ => ‖c α‖ * ρ ^ (∑ j, α j)) ∧
      ∑' α : Fin D → ℕ, ‖c α‖ * ρ ^ (∑ j, α j) ≤ M := by
  obtain ⟨h1, h2⟩ := hc
  simpa only [Real.norm_eq_abs, mdeg] using And.intro h1 h2

theorem siteCoeff_zero {D : ℕ} (β ν a : ℝ) (b : Fin D → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : (D : ℝ) * ρ ^ 2 ≤ 1 / 4) : siteCoeff β ν a b 0 = 0 := by
  have := siteCoeff_hasSum β ν a b hρ hx (fun _ => 0) (fun i => by simpa using hρ.le)
  rw [coeff_zero_of_hasSum this]
  simp [siteFn, siteProfile, kf0LogFn, kf0SqrtFn]

theorem bondCoeff_zero {D : ℕ} (β : ℝ) (S₁ S₂ : Finset (Fin D)) {ρ : ℝ} (hρ : 0 < ρ)
    (hx₁ : (S₁.card : ℝ) * ρ ^ 2 ≤ 1 / 4) (hx₂ : (S₂.card : ℝ) * ρ ^ 2 ≤ 1 / 4) :
    bondCoeff β S₁ S₂ 0 = 0 := by
  have := bondCoeff_hasSum β S₁ S₂ hρ hx₁ hx₂ (fun _ => 0) (fun i => by simpa using hρ.le)
  rw [coeff_zero_of_hasSum this]
  simp [bondFn, bondProfile, kf0SqrtFn]

/-- The walk-indexed terms of the site function at `x`. -/
noncomputable abbrev f1SiteWalk (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (g : Torus d ℓ → Fin N → ℝ) (x : Torus d ℓ) (ψ : Torus d ℓ → perp h) :
    KF0WalkSeriesIndex d n → ℝ :=
  kf0WalkSeriesTerm d ℓ ν β (fun _ : Fin n => x) (tcoord e)
    (siteCoeff β ν (f1Nrm g h x) (f1Lin e g x)) ψ

/-- The walk-indexed terms of the bond function of `(x, x + e_μ)`. -/
noncomputable abbrev f1BondWalk (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (x : Torus d ℓ) (μ : Fin d) (ψ : Torus d ℓ → perp h) :
    KF0WalkSeriesIndex d (n + n) → ℝ :=
  kf0WalkSeriesTerm d ℓ ν β (bondAnchor n (x + Pi.single μ 1) x) (bondEll e)
    (bondCoeff β (bondFst n) (bondSnd n)) ψ

/-- `F^{site}_{x,H}`: the sum of the site terms with halo `H`. -/
noncomputable def f1SiteHalo (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (g : Torus d ℓ → Fin N → ℝ) (x : Torus d ℓ) (H : Finset (Torus d ℓ))
    (ψ : Torus d ℓ → perp h) : ℝ :=
  kf0HaloTerm d ℓ ν β (fun _ : Fin n => x) (tcoord e)
    (siteCoeff β ν (f1Nrm g h x) (f1Lin e g x)) H ψ

/-- `F^{bond}_{(x,μ),H}`: the sum of the bond terms with halo `H`. -/
noncomputable def f1BondHalo (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (x : Torus d ℓ) (μ : Fin d) (H : Finset (Torus d ℓ)) (ψ : Torus d ℓ → perp h) : ℝ :=
  kf0HaloTerm d ℓ ν β (bondAnchor n (x + Pi.single μ 1) x) (bondEll e)
    (bondCoeff β (bondFst n) (bondSnd n)) H ψ

/-- **(T2, dependence)** `F^{site}_{x,H}` depends on `ψ` only on `H`. -/
theorem f1SiteHalo_congr (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (g : Torus d ℓ → Fin N → ℝ) (x : Torus d ℓ) (H : Finset (Torus d ℓ))
    {ψ ψ' : Torus d ℓ → perp h} (hψ : ∀ b ∈ H, ψ b = ψ' b) :
    f1SiteHalo e β ν g x H ψ = f1SiteHalo e β ν g x H ψ' :=
  kf0HaloTerm_congr ν β _ _ _ H hψ

/-- **(T2, dependence)** `F^{bond}_{(x,μ),H}` depends on `ψ` only on `H`. -/
theorem f1BondHalo_congr (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (x : Torus d ℓ) (μ : Fin d) (H : Finset (Torus d ℓ))
    {ψ ψ' : Torus d ℓ → perp h} (hψ : ∀ b ∈ H, ψ b = ψ' b) :
    f1BondHalo e β ν x μ H ψ = f1BondHalo e β ν x μ H ψ' :=
  kf0HaloTerm_congr ν β _ _ _ H hψ

/-- **(T1, site function)** On the product cutoff event `sup_y ‖ψ_y‖ ≤ p` the site function at
`x` is the sum of the absolutely convergent family of walk-indexed terms, and
`∑_index e^{κ k_s(halo)} sup_cutoff |term| ≤ n² (G ρ + ρ² + β ρ⁴)`, `ρ = e^{κ 3^d} p A_γ/√β`,
`G = ∑_j |b_j| + |g_x · h|`. -/
theorem site_walk_localization {β ν g γ κ p : ℝ} (hβ : 0 < β) (hg : 0 < g) (hgν : g ≤ ν)
    (hν1 : ν ≤ 1) (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) {s m' : ℕ}
    [NeZero m'] (hs : 0 < s) (hℓ : ℓ = s * m') (hκ : 0 ≤ κ) (hγκ : κ * 3 ^ d / s ≤ γ)
    (hp : 0 < p) (hn : 1 ≤ n) (hρ1 : kf0Rho d g γ κ p β ≤ 1)
    (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (src : Torus d ℓ → Fin N → ℝ) (x : Torus d ℓ) :
    (∀ ψ : Torus d ℓ → perp h, (∀ y, ‖ψ y‖ ≤ p) →
      Summable (fun a => ‖f1SiteWalk e β ν src x ψ a‖) ∧
        HasSum (f1SiteWalk e β ν src x ψ) (f1SiteValue β ν h src ψ x)) ∧
    Summable (fun a : KF0WalkSeriesIndex d n =>
      Real.exp (κ * kf0BlockCount s m' (kf0WalkSeriesHalo (fun _ : Fin n => x) a)) *
        cutoffSup p (fun ψ => f1SiteWalk e β ν src x ψ a)) ∧
    ∑' a : KF0WalkSeriesIndex d n,
        Real.exp (κ * kf0BlockCount s m' (kf0WalkSeriesHalo (fun _ : Fin n => x) a)) *
          cutoffSup p (fun ψ => f1SiteWalk e β ν src x ψ a) ≤
      (n : ℝ) ^ 2 * (((∑ j, |f1Lin e src x j|) + |f1Nrm src h x|) * kf0Rho d g γ κ p β +
        kf0Rho d g γ κ p β ^ 2 + β * kf0Rho d g γ κ p β ^ 4) := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  have hρpos := kf0Rho_pos (d := d) (κ := κ) hg hq hp hβ
  have hMaj := siteCoeff_maj_C hβ.le hν.le hν1 hn (f1Nrm src h x) (f1Lin e src x) hρpos hρ1 hρ
  obtain ⟨hM, hM2⟩ := maj_series hMaj
  have hℓ1 : ∀ j, ‖tcoord e j‖ ≤ 1 := norm_tcoord_le e
  refine ⟨fun ψ hψ => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := walkSeries_hasSum (d := d) (m := ℓ) hg hgν hγ hq hκ β hp.le
      (fun _ : Fin n => x) (tcoord e) hℓ1 (siteCoeff β ν (f1Nrm src h x) (f1Lin e src x)) hM ψ hψ
    refine ⟨h1, ?_⟩
    have hz : ∀ j, |tcoord e j ((Real.sqrt β)⁻¹ • matAct (kf0C d ℓ ν) ψ x)| ≤
        kf0Rho d g γ κ p β := fun j =>
      (le_trans (by simpa [Real.norm_eq_abs] using
        (tcoord e j).le_opNorm ((Real.sqrt β)⁻¹ • matAct (kf0C d ℓ ν) ψ x))
        (mul_le_of_le_one_left (norm_nonneg _) (norm_tcoord_le e j))).trans
        (norm_u_le_kf0Rho hg hgν hγ hq hκ β hp.le ψ hψ x)
    have hsum := siteCoeff_hasSum β ν (f1Nrm src h x) (f1Lin e src x) hρpos
      (by simpa using hρ) (fun j => tcoord e j ((Real.sqrt β)⁻¹ • matAct (kf0C d ℓ ν) ψ x)) hz
    have := h2
    rw [hsum.tsum_eq] at this
    rwa [f1SiteValue_eq hβ hν e src ψ x]
  · obtain ⟨h1, h2⟩ := walkSeries_cutoffSup_summable (d := d) (m := ℓ) hg hgν hq hs hℓ hκ hγκ β
      hp.le (fun _ : Fin n => x) (tcoord e) hℓ1
      (siteCoeff β ν (f1Nrm src h x) (f1Lin e src x)) hM
    exact ⟨h1, h2.trans hM2⟩

/-- **(T2, site function)** Regrouping by equal halo.  On the cutoff event the site function is the
finite sum of the `F^{site}_{x,H}`; `F_H = 0` unless `H` is connected and contains `x`; and
`∑_H e^{κ k_s(H)} sup_cutoff |F_H| ≤ n² (G ρ + ρ² + β ρ⁴)`. -/
theorem site_halo_decomposition {β ν g γ κ p : ℝ} (hβ : 0 < β) (hg : 0 < g) (hgν : g ≤ ν)
    (hν1 : ν ≤ 1) (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) {s m' : ℕ}
    [NeZero m'] (hs : 0 < s) (hℓ : ℓ = s * m') (hκ : 0 ≤ κ) (hγκ : κ * 3 ^ d / s ≤ γ)
    (hp : 0 < p) (hn : 1 ≤ n) (hρ1 : kf0Rho d g γ κ p β ≤ 1)
    (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (src : Torus d ℓ → Fin N → ℝ) (x : Torus d ℓ) :
    (∀ ψ : Torus d ℓ → perp h, (∀ y, ‖ψ y‖ ≤ p) →
      ∑ H, f1SiteHalo e β ν src x H ψ = f1SiteValue β ν h src ψ x) ∧
    (∀ (H : Finset (Torus d ℓ)), ¬ (NNConnected H ∧ x ∈ H) →
      ∀ ψ : Torus d ℓ → perp h, f1SiteHalo e β ν src x H ψ = 0) ∧
    ∑ H : Finset (Torus d ℓ), Real.exp (κ * kf0BlockCount s m' H) *
        cutoffSup p (f1SiteHalo e β ν src x H) ≤
      (n : ℝ) ^ 2 * (((∑ j, |f1Lin e src x j|) + |f1Nrm src h x|) * kf0Rho d g γ κ p β +
        kf0Rho d g γ κ p β ^ 2 + β * kf0Rho d g γ κ p β ^ 4) := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  have hρpos := kf0Rho_pos (d := d) (κ := κ) hg hq hp hβ
  have hMaj := siteCoeff_maj_C hβ.le hν.le hν1 hn (f1Nrm src h x) (f1Lin e src x) hρpos hρ1 hρ
  obtain ⟨hM, hM2⟩ := maj_series hMaj
  have hℓ1 : ∀ j, ‖tcoord e j‖ ≤ 1 := norm_tcoord_le e
  refine ⟨fun ψ hψ => ?_, fun H hH ψ => ?_, ?_⟩
  · have := (site_walk_localization hβ hg hgν hν1 hγ hq hs hℓ hκ hγκ hp hn hρ1 hρ e src x).1 ψ hψ
    exact sum_haloPiece_eq this.2
  · refine kf0HaloTerm_eq_zero ν β _ _ _ (siteCoeff_zero _ _ _ _ hρpos (by simpa using hρ))
      (fun i j => Or.inl rfl) H ?_ ψ
    rintro ⟨h1, j, hj⟩
    exact hH ⟨h1, hj⟩
  · exact (weighted_kf0HaloTerm_le (d := d) (m := ℓ) hg hgν hq hs hℓ hκ hγκ β hp.le
      (fun _ : Fin n => x) (tcoord e) hℓ1
      (siteCoeff β ν (f1Nrm src h x) (f1Lin e src x)) hM).trans hM2


omit [NeZero ℓ] in
theorem bondAnchor_mem {n : ℕ} {y₁ y₂ : Torus d ℓ} {H : Finset (Torus d ℓ)}
    (h : ∃ j, bondAnchor n y₁ y₂ j ∈ H) : y₁ ∈ H ∨ y₂ ∈ H := by
  obtain ⟨j, hj⟩ := h
  revert hj
  refine Fin.addCases (fun a hj => ?_) (fun a hj => ?_) j
  · left; simpa [bondAnchor] using hj
  · right
    have : bondAnchor n y₁ y₂ (Fin.natAdd n a) = y₂ := Fin.append_right _ _ _
    rwa [this] at hj

/-- **(T1, bond function)** On the product cutoff event the bond function of `(x, x + e_μ)` is
the sum of the absolutely convergent family of walk-indexed terms, and
`∑_index e^{κ k_s(halo)} sup_cutoff |term| ≤ 2 n² β ρ⁴`. -/
theorem bond_walk_localization {β ν g γ κ p : ℝ} (hβ : 0 < β) (hg : 0 < g) (hgν : g ≤ ν)
    (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) {s m' : ℕ}
    [NeZero m'] (hs : 0 < s) (hℓ : ℓ = s * m') (hκ : 0 ≤ κ) (hγκ : κ * 3 ^ d / s ≤ γ)
    (hp : 0 < p) (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (x : Torus d ℓ) (μ : Fin d) :
    (∀ ψ : Torus d ℓ → perp h, (∀ y, ‖ψ y‖ ≤ p) →
      Summable (fun a => ‖f1BondWalk e β ν x μ ψ a‖) ∧
        HasSum (f1BondWalk e β ν x μ ψ) (f1BondValue β ν ψ x μ)) ∧
    Summable (fun a : KF0WalkSeriesIndex d (n + n) =>
      Real.exp (κ * kf0BlockCount s m'
          (kf0WalkSeriesHalo (bondAnchor n (x + Pi.single μ 1) x) a)) *
        cutoffSup p (fun ψ => f1BondWalk e β ν x μ ψ a)) ∧
    ∑' a : KF0WalkSeriesIndex d (n + n),
        Real.exp (κ * kf0BlockCount s m'
            (kf0WalkSeriesHalo (bondAnchor n (x + Pi.single μ 1) x) a)) *
          cutoffSup p (fun ψ => f1BondWalk e β ν x μ ψ a) ≤
      2 * (n : ℝ) ^ 2 * β * kf0Rho d g γ κ p β ^ 4 := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  have hρpos := kf0Rho_pos (d := d) (κ := κ) hg hq hp hβ
  have hMaj := bondCoeff_maj_pair hβ.le n hρpos hρ
  obtain ⟨hM, hM2⟩ := maj_series hMaj
  have hℓ1 : ∀ j, ‖bondEll e j‖ ≤ 1 := norm_bondEll_le e
  refine ⟨fun ψ hψ => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := walkSeries_hasSum (d := d) (m := ℓ) hg hgν hγ hq hκ β hp.le
      (bondAnchor n (x + Pi.single μ 1) x) (bondEll e) hℓ1
      (bondCoeff β (bondFst n) (bondSnd n)) hM ψ hψ
    refine ⟨h1, ?_⟩
    have hz : ∀ j, |bondEll e j ((Real.sqrt β)⁻¹ •
        matAct (kf0C d ℓ ν) ψ (bondAnchor n (x + Pi.single μ 1) x j))| ≤
        kf0Rho d g γ κ p β := fun j =>
      (le_trans (by simpa [Real.norm_eq_abs] using
        (bondEll e j).le_opNorm ((Real.sqrt β)⁻¹ •
          matAct (kf0C d ℓ ν) ψ (bondAnchor n (x + Pi.single μ 1) x j)))
        (mul_le_of_le_one_left (norm_nonneg _) (norm_bondEll_le e j))).trans
        (norm_u_le_kf0Rho hg hgν hγ hq hκ β hp.le ψ hψ _)
    have hsum := bondCoeff_hasSum_pair β n hρpos hρ (fun j => bondEll e j ((Real.sqrt β)⁻¹ •
        matAct (kf0C d ℓ ν) ψ (bondAnchor n (x + Pi.single μ 1) x j))) hz
    have := h2
    rw [hsum.tsum_eq] at this
    rwa [f1BondValue_eq hβ hν e ψ x μ]
  · obtain ⟨h1, h2⟩ := walkSeries_cutoffSup_summable (d := d) (m := ℓ) hg hgν hq hs hℓ hκ hγκ β
      hp.le (bondAnchor n (x + Pi.single μ 1) x) (bondEll e) hℓ1
      (bondCoeff β (bondFst n) (bondSnd n)) hM
    exact ⟨h1, h2.trans hM2⟩

/-- **(T2, bond function)** Regrouping by equal halo; `F_H = 0` unless `H` is connected and meets
`{x, x + e_μ}`. -/
theorem bond_halo_decomposition {β ν g γ κ p : ℝ} (hβ : 0 < β) (hg : 0 < g) (hgν : g ≤ ν)
    (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) {s m' : ℕ}
    [NeZero m'] (hs : 0 < s) (hℓ : ℓ = s * m') (hκ : 0 ≤ κ) (hγκ : κ * 3 ^ d / s ≤ γ)
    (hp : 0 < p) (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (x : Torus d ℓ) (μ : Fin d) :
    (∀ ψ : Torus d ℓ → perp h, (∀ y, ‖ψ y‖ ≤ p) →
      ∑ H, f1BondHalo e β ν x μ H ψ = f1BondValue β ν ψ x μ) ∧
    (∀ (H : Finset (Torus d ℓ)),
      ¬ (NNConnected H ∧ (x + Pi.single μ 1 ∈ H ∨ x ∈ H)) →
      ∀ ψ : Torus d ℓ → perp h, f1BondHalo e β ν x μ H ψ = 0) ∧
    ∑ H : Finset (Torus d ℓ), Real.exp (κ * kf0BlockCount s m' H) *
        cutoffSup p (f1BondHalo e β ν x μ H) ≤
      2 * (n : ℝ) ^ 2 * β * kf0Rho d g γ κ p β ^ 4 := by
  have hρpos := kf0Rho_pos (d := d) (κ := κ) hg hq hp hβ
  have hMaj := bondCoeff_maj_pair hβ.le n hρpos hρ
  obtain ⟨hM, hM2⟩ := maj_series hMaj
  have hℓ1 : ∀ j, ‖bondEll e j‖ ≤ 1 := norm_bondEll_le e
  refine ⟨fun ψ hψ => ?_, fun H hH ψ => ?_, ?_⟩
  · have := (bond_walk_localization hβ hg hgν hγ hq hs hℓ hκ hγκ hp hρ e x μ).1 ψ hψ
    exact sum_haloPiece_eq this.2
  · refine kf0HaloTerm_eq_zero ν β _ _ _ (bondCoeff_zero _ _ _ hρpos
      (by rw [card_bondFst]; exact hρ) (by rw [card_bondSnd]; exact hρ))
      (bondAnchor_adj n x μ) H ?_ ψ
    rintro ⟨h1, hj⟩
    exact hH ⟨h1, bondAnchor_mem hj⟩
  · exact (weighted_kf0HaloTerm_le (d := d) (m := ℓ) hg hgν hq hs hℓ hκ hγκ β hp.le
      (bondAnchor n (x + Pi.single μ 1) x) (bondEll e) hℓ1
      (bondCoeff β (bondFst n) (bondSnd n)) hM).trans hM2


/-- On the cutoff event in the small regime every tangent variable `v_x = (K_ν^{-1/2} ψ)_x`
lies strictly inside the chart domain `‖v_x‖² < β`. -/
theorem tfield_norm_sq_lt {β ν g γ κ p : ℝ} (hβ : 0 < β) (hg : 0 < g) (hgν : g ≤ ν)
    (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (hκ : 0 ≤ κ) (hp : 0 < p)
    (hn : 1 ≤ n) (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (ψ : Torus d ℓ → perp h) (hψ : ∀ y, ‖ψ y‖ ≤ p) (x : Torus d ℓ) :
    ‖tfield d ℓ ν ψ x‖ ^ 2 < β := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hu := norm_u_le_kf0Rho hg hgν hγ hq hκ β hp.le ψ hψ x
  have hC : matAct (kf0C d ℓ ν) ψ x = tfield d ℓ ν ψ x := by rw [kf0C_eq_kf0SqrtR hν]
  rw [hC, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)] at hu
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hρ0 : 0 ≤ kf0Rho d g γ κ p β := (kf0Rho_pos (d := d) (κ := κ) hg hq hp hβ).le
  have hρ2 : kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (kf0Rho d g γ κ p β)]
  have hρ12 : kf0Rho d g γ κ p β ≤ 1 / 2 := by nlinarith
  have h1 : ‖tfield d ℓ ν ψ x‖ ≤ Real.sqrt β / 2 := by
    have : ‖tfield d ℓ ν ψ x‖ ≤ Real.sqrt β * kf0Rho d g γ κ p β := by
      have := mul_le_mul_of_nonneg_left hu hs.le
      rwa [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at this
    nlinarith
  have h2 : ‖tfield d ℓ ν ψ x‖ ^ 2 ≤ (Real.sqrt β / 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [div_pow, Real.sq_sqrt hβ.le] at h2
  linarith

/-- **(T3, identity)** On the product cutoff event, in the small regime, the landed all-plus
integrand (the chart Jacobian times the exponential of the interaction exponent, at the tangent
field `K_ν^{-1/2} ψ`) is exactly the exponential of the source constant plus the sum over sites
of the regrouped site terms plus the sum over forward bonds of the regrouped bond terms. -/
theorem f1_integrand_eq {β ν g γ κ p : ℝ} (hβ : 0 < β) (hg : 0 < g) (hgν : g ≤ ν)
    (hν1 : ν ≤ 1) (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) {s m' : ℕ}
    [NeZero m'] (hs : 0 < s) (hℓ : ℓ = s * m') (hκ : 0 ≤ κ) (hγκ : κ * 3 ^ d / s ≤ γ)
    (hp : 0 < p) (hn : 1 ≤ n) (hρ1 : kf0Rho d g γ κ p β ≤ 1)
    (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (src : Torus d ℓ → Fin N → ℝ)
    (ψ : Torus d ℓ → perp h) (hψ : ∀ y, ‖ψ y‖ ≤ p) :
    chartJac β (fun x => ((tfield d ℓ ν ψ x : perp h) : EuclideanSpace ℝ (Fin N))) *
        Real.exp (chartInteractionExponent β ν h src (tfield d ℓ ν ψ)) =
      Real.exp (sourceConst src h + ∑ x, ∑ H, f1SiteHalo e β ν src x H ψ +
        ∑ x, ∑ μ : Fin d, ∑ H, f1BondHalo e β ν x μ H ψ) := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  have hv := tfield_norm_sq_lt (h := h) hβ hg hgν hγ hq hκ hp hn hρ ψ hψ
  rw [chartJac_mul_exp_chartInteractionExponent ν src (tfield d ℓ ν ψ) hv]
  congr 1
  have hsite : ∀ x, ∑ H, f1SiteHalo e β ν src x H ψ = f1SiteValue β ν h src ψ x := fun x =>
    (site_halo_decomposition hβ hg hgν hν1 hγ hq hs hℓ hκ hγκ hp hn hρ1 hρ e src x).1 ψ hψ
  have hbond : ∀ x μ, ∑ H, f1BondHalo e β ν x μ H ψ = f1BondValue β ν ψ x μ := fun x μ =>
    (bond_halo_decomposition hβ hg hgν hγ hq hs hℓ hκ hγκ hp hρ e x μ).1 ψ hψ
  simp only [hsite, hbond, f1SiteValue, f1BondValue, f1Nrm, Finset.sum_add_distrib, sourceTangent,
    Finset.mul_sum]
  ring


/-! ### (T3) Smallness (F.13) -/

open Filter in
/-- **(T3, smallness)** For fixed `d, N, n ≥ 1, κ, s, b, a`, and `ν ∈ [ν_*, 1]` (`g = ν_* ≤ ν`),
with the cutoff `p = b log(β a)` and a source `src` whose size is bounded by `G`: for every
`ε > 0` there is `β₁` such that for all `β ≥ β₁` the small-regime hypotheses hold and the total
weighted norm per anchor satisfies `B_β^{site} ≤ ε`, `B_β^{bond} ≤ ε`. -/
theorem f1_weighted_small {ν g γ κ a b G : ℝ} (hg : 0 < g) (hgν : g ≤ ν) (hν1 : ν ≤ 1)
    (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) {s m' : ℕ} [NeZero m']
    (hs : 0 < s) (hℓ : ℓ = s * m') (hκ : 0 ≤ κ) (hγκ : κ * 3 ^ d / s ≤ γ) (ha : 0 < a)
    (hb : 0 < b) (hn : 1 ≤ n) (e : OrthonormalBasis (Fin n) ℝ (perp h))
    (src : Torus d ℓ → Fin N → ℝ)
    (hG : ∀ x, (∑ j, |f1Lin e src x j|) + |f1Nrm src h x| ≤ G) {ε : ℝ} (hε : 0 < ε) :
    ∃ β₁ : ℝ, ∀ β ≥ β₁, 0 < β ∧ 0 < b * Real.log (β * a) ∧
      kf0Rho d g γ κ (b * Real.log (β * a)) β ≤ 1 ∧
      (n : ℝ) * kf0Rho d g γ κ (b * Real.log (β * a)) β ^ 2 ≤ 1 / 4 ∧
      (∀ x : Torus d ℓ, ∑ H : Finset (Torus d ℓ), Real.exp (κ * kf0BlockCount s m' H) *
          cutoffSup (b * Real.log (β * a)) (f1SiteHalo e β ν src x H) ≤ ε) ∧
      (∀ (x : Torus d ℓ) (μ : Fin d), ∑ H : Finset (Torus d ℓ),
          Real.exp (κ * kf0BlockCount s m' H) *
          cutoffSup (b * Real.log (β * a)) (f1BondHalo e β ν x μ H) ≤ ε) := by
  set θ : ℝ := Real.exp (κ * 3 ^ d) with hθ
  set A : ℝ := kf0WalkA d g γ with hA
  have hθpos : 0 < θ := Real.exp_pos _
  have hApos : 0 < A := kf0WalkA_pos (d := d) hg hq
  have hc : 0 < θ * b * A := mul_pos (mul_pos hθpos hb) hApos
  have hρeq : ∀ β : ℝ, kf0Rho d g γ κ (b * Real.log (β * a)) β = rhoBeta θ b A a β := by
    intro β; unfold kf0Rho rhoBeta; ring
  obtain ⟨β₂, hβ₂⟩ := eventually_atTop.1 (((rhoBeta_eventually_small hc ha n).and
    (eventually_gt_atTop (1 / a))).and (eventually_gt_atTop 0))
  obtain ⟨β₃, hβ₃⟩ := smallness_eps ha ((n : ℝ) ^ 2 * G * (θ * b * A)) ((n : ℝ) ^ 2 * (θ * b * A) ^ 2)
    ((n : ℝ) ^ 2 * (θ * b * A) ^ 4) hε
  obtain ⟨β₄, hβ₄⟩ := smallness_eps ha 0 0 (2 * (n : ℝ) ^ 2 * (θ * b * A) ^ 4) hε
  refine ⟨max β₂ (max β₃ β₄), fun β hβ => ?_⟩
  have h2 := hβ₂ β (le_trans (le_max_left _ _) hβ)
  have h3 := hβ₃ β (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hβ)
  have h4 := hβ₄ β (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hβ)
  obtain ⟨⟨⟨hρ0, hρ1, hρ⟩, hβa⟩, hβ0⟩ := h2
  have hβa' : 1 < β * a := by
    have := (div_lt_iff₀ ha).1 hβa
    linarith
  have hp : 0 < b * Real.log (β * a) := mul_pos hb (Real.log_pos hβa')
  rw [← hρeq] at hρ1 hρ
  refine ⟨hβ0, hp, hρ1, hρ, fun x => ?_, fun x μ => ?_⟩
  · refine (site_halo_decomposition hβ0 hg hgν hν1 hγ hq hs hℓ hκ hγκ hp hn hρ1 hρ e src x).2.2.trans ?_
    have hρpos : 0 < kf0Rho d g γ κ (b * Real.log (β * a)) β := by rw [hρeq]; exact hρ0
    have h5 : (n : ℝ) ^ 2 * (((∑ j, |f1Lin e src x j|) + |f1Nrm src h x|) *
        kf0Rho d g γ κ (b * Real.log (β * a)) β + kf0Rho d g γ κ (b * Real.log (β * a)) β ^ 2 +
        β * kf0Rho d g γ κ (b * Real.log (β * a)) β ^ 4) ≤ (n : ℝ) ^ 2 * (G *
        kf0Rho d g γ κ (b * Real.log (β * a)) β + kf0Rho d g γ κ (b * Real.log (β * a)) β ^ 2 +
        β * kf0Rho d g γ κ (b * Real.log (β * a)) β ^ 4) := by
      gcongr
      exact hG x
    refine h5.trans ?_
    rw [hρeq, site_bound_rhoBeta θ b A a G β hβ0]
    have := (abs_lt.1 h3).2
    nlinarith [this]
  · refine (bond_halo_decomposition hβ0 hg hgν hγ hq hs hℓ hκ hγκ hp hρ e x μ).2.2.trans ?_
    rw [hρeq]
    have e1 : 2 * (n : ℝ) ^ 2 * β * rhoBeta θ b A a β ^ 4 =
        2 * (n : ℝ) ^ 2 * (β * rhoBeta θ b A a β ^ 4) := by ring
    rw [e1, bond_bound_rhoBeta θ b A a β hβ0]
    have := (abs_lt.1 h4).2
    nlinarith [this]


/-! ### (T4) An explicit instance -/

section Instance

open SphereChart

/-- `ρ ≤ 6/100` for `d = 3`, `g = 7/72`, `γ = 1/100`, `κ = 1/300`, `p = 1`, `β = 10^8`. -/
theorem f1_instance_rho : kf0Rho 3 (7 / 72) (1 / 100) (1 / 300) 1 (10 ^ 8) ≤ 6 / 100 := by
  have hA := kf0_instance_A_le
  have hApos : 0 < kf0WalkA 3 (7 / 72) (1 / 100) :=
    kf0WalkA_pos (d := 3) (by norm_num) kf0_instance_hq
  have hsq : Real.sqrt ((10 : ℝ) ^ 8) = 10 ^ 4 := by
    rw [show (10 : ℝ) ^ 8 = (10 ^ 4) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hexp : Real.exp (1 / 300 * (3 : ℝ) ^ 3) ≤ 11 / 10 := by
    have h := Real.exp_bound_div_one_sub_of_interval (x := 1 / 300 * (3 : ℝ) ^ 3)
      (by norm_num) (by norm_num)
    refine h.trans ?_
    norm_num
  unfold kf0Rho
  rw [hsq]
  have h1 : 1 * kf0WalkA 3 (7 / 72) (1 / 100) / 10 ^ 4 ≤ 535 / 10 ^ 4 := by
    rw [one_mul]
    exact div_le_div_of_nonneg_right hA (by norm_num)
  have h2 : 0 ≤ 1 * kf0WalkA 3 (7 / 72) (1 / 100) / (10 : ℝ) ^ 4 := by positivity
  calc _ ≤ 11 / 10 * (535 / 10 ^ 4) :=
        mul_le_mul hexp h1 h2 (by norm_num)
    _ ≤ 6 / 100 := by norm_num

/-- **(T4)** Non-vacuity.  `d = 3`, `N = 2`, side `18 = 9 · 2`, `s = 9`, `κ = 1/300`, `γ = 1/100`,
`ν = 1`, `g = 7/72`, `β = 10^8`, cutoff `p = 1`, `h = e₀`, source `0`: the site function at any
site is the finite sum of the halo pieces on the cutoff event, the pieces vanish unless the halo
is connected and contains the site, and the weighted norm is at most `1400`. -/
theorem f1_instance
    (e : OrthonormalBasis (Fin (2 - 1)) ℝ (perp (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))))
    (x : Torus 3 18) :
    (∀ ψ : Torus 3 18 → perp (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)), (∀ y, ‖ψ y‖ ≤ 1) →
      ∑ H, f1SiteHalo e (10 ^ 8) 1 (fun _ _ => (0 : ℝ)) x H ψ =
        f1SiteValue (10 ^ 8) 1 (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
          (fun _ _ => (0 : ℝ)) ψ x) ∧
    (∀ (H : Finset (Torus 3 18)), ¬ (NNConnected H ∧ x ∈ H) →
      ∀ ψ : Torus 3 18 → perp (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)),
        f1SiteHalo e (10 ^ 8) 1 (fun _ _ => (0 : ℝ)) x H ψ = 0) ∧
    ∑ H : Finset (Torus 3 18), Real.exp (1 / 300 * kf0BlockCount 9 2 H) *
        cutoffSup 1 (f1SiteHalo e (10 ^ 8) 1 (fun _ _ => (0 : ℝ)) x H) ≤ 1400 := by
  have hρ := f1_instance_rho
  have hρpos : 0 < kf0Rho 3 (7 / 72) (1 / 100) (1 / 300) 1 (10 ^ 8) :=
    kf0Rho_pos (d := 3) (by norm_num) kf0_instance_hq one_pos (by norm_num)
  have hρ1 : kf0Rho 3 (7 / 72) (1 / 100) (1 / 300) 1 (10 ^ 8) ≤ 1 := by linarith
  have hρ2 : ((2 - 1 : ℕ) : ℝ) * kf0Rho 3 (7 / 72) (1 / 100) (1 / 300) 1 (10 ^ 8) ^ 2 ≤ 1 / 4 := by
    norm_num
    nlinarith
  obtain ⟨h1, h2, h3⟩ := site_halo_decomposition (d := 3) (N := 2) (ℓ := 18) (n := 2 - 1)
    (h := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (β := 10 ^ 8) (ν := 1) (g := 7 / 72)
    (γ := 1 / 100) (κ := 1 / 300) (p := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) kf0_instance_hq (s := 9) (m' := 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) one_pos (by norm_num) hρ1 hρ2 e (fun _ _ => (0 : ℝ)) x
  refine ⟨h1, h2, h3.trans ?_⟩
  have hz : ∀ j, f1Lin e (fun (_ : Torus 3 18) (_ : Fin 2) => (0 : ℝ)) x j = 0 := fun j => by
    simp [f1Lin]
  simp only [hz, f1Nrm, zero_mul, Finset.sum_const_zero, abs_zero, add_zero]
  have hρ0 := hρpos.le
  have h4 : kf0Rho 3 (7 / 72) (1 / 100) (1 / 300) 1 (10 ^ 8) ^ 2 ≤ (6 / 100) ^ 2 :=
    pow_le_pow_left₀ hρ0 hρ 2
  have h5 : kf0Rho 3 (7 / 72) (1 / 100) (1 / 300) 1 (10 ^ 8) ^ 4 ≤ (6 / 100) ^ 4 :=
    pow_le_pow_left₀ hρ0 hρ 4
  norm_num at h4 h5 ⊢
  nlinarith

/-- The instance is not vacuous: an orthonormal tangent basis exists. -/
theorem f1_instance_basis_nonempty :
    Nonempty (OrthonormalBasis (Fin (2 - 1)) ℝ
      (perp (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))) :=
  nonempty_tangent_basis (by simp)

end Instance

end LocalizeFunctions

end Balaban.LargeField.KF0F1
