/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocCount

/-!
# The summed bound (W5) of the local form from the coefficient bounds (A6-3, item (L4))

For the local form `W` of a family of rooted terms (`localFormOf`), with coefficient bounds
`‖coef_C(τ_a)‖ ≤ b_a e^{-(κ-1)|C|}` (the rooted Lemma AE), a weight `ω` of the regions with
`ω(R ∪ ⋃_{i ∈ C} B_i) ≤ ω(R) θ^{|C|}` (in the application `ω = e^{a · cellCount}`,
`θ = e^{a p}`, `p` the number of cells meeting a box), and `q = θ e^{-(κ-1)}`:

  `∑_{Y ∋ x} ‖W_Y‖ ω(Y) ≤ ∑_{a : x ∈ R_a} (‖τ_a(φ₀)‖ + b_a ∏_{i root of a} (1 + A_i)) ω(R_a)
     + ∑_{i₀ : x ∈ B_{i₀}} ∑_a b_a ω(R_a) ∑_{l root of a} (∑_{K ∋ i₀, l} q^{|K|}) ∏_{i root of a} (1 + A_i)`,

`A_i = ∑_{K ∋ i animal} q^{|K|}` (`sum_norm_localFormOf_le_of_coef`).
-/

@[expose] public section

namespace Balaban.Green

open Finset Balaban.Localization

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {A : Type*} [Fintype A]

open Classical in
/-- **(W5) from the coefficient bounds.** See the module docstring. -/
theorem sum_norm_localFormOf_le_of_coef {τ : A → (Λ × Fin N → ℂ) → ℂ} {RA : A → Finset Λ}
    {PB : ι → Finset Λ} {φ₀ : Λ × Fin N → ℂ} {T : (ι → ℂ) → Λ × Fin N → Λ × Fin N → ℂ}
    (w : Λ × Fin N → ℂ) (x : Λ) {κ θ : ℝ} (hθ : 0 ≤ θ) {b : A → ℝ} (hb : ∀ a, 0 ≤ b a)
    (hcoef : ∀ a C, C.Nonempty → IsRootedFamily (blockPatch N PB) (blockSites N (RA a)) C →
      ‖rootedCoef (τ a) φ₀ T w C‖ ≤ b a * Real.exp (-(κ - 1) * C.card))
    (ω : Finset Λ → ℝ) (hω0 : ∀ Y, 0 ≤ ω Y)
    (hω : ∀ a C, ω (rootRegion (RA a) PB C) ≤ ω (RA a) * θ ^ C.card) :
    ∑ Y ∈ Finset.univ.filter (fun Y : Finset Λ => x ∈ Y), ‖localFormOf τ RA PB φ₀ T Y w‖ * ω Y ≤
      ∑ a, (if x ∈ RA a then (‖τ a φ₀‖ + b a *
          ∏ i ∈ rootCells (blockPatch N PB) (blockSites N (RA a)),
            (1 + ∑ K ∈ animalsAt (blockPatch N PB) i,
              ∏ _l ∈ K, θ * Real.exp (-(κ - 1)))) * ω (RA a) else 0) +
      ∑ i₀ ∈ Finset.univ.filter (fun i : ι => x ∈ PB i), ∑ a, b a * ω (RA a) *
        ∑ l ∈ rootCells (blockPatch N PB) (blockSites N (RA a)),
          (∑ K ∈ (animalsAt (blockPatch N PB) l).filter (fun K => i₀ ∈ K),
            ∏ _m ∈ K, θ * Real.exp (-(κ - 1))) *
          ∏ i ∈ rootCells (blockPatch N PB) (blockSites N (RA a)),
            (1 + ∑ K ∈ animalsAt (blockPatch N PB) i, ∏ _l ∈ K, θ * Real.exp (-(κ - 1))) := by
  set P := blockPatch N PB with hP
  set q : ℝ := θ * Real.exp (-(κ - 1)) with hq
  have hq0 : 0 ≤ q := mul_nonneg hθ (Real.exp_pos _).le
  set Pr : A → ℝ := fun a => ∏ i ∈ rootCells P (blockSites N (RA a)),
    (1 + ∑ K ∈ animalsAt P i, ∏ _l ∈ K, q) with hPr
  -- the weight of a family is a product
  have hprodq : ∀ C : Finset ι, Real.exp (-(κ - 1) * C.card) * θ ^ C.card = ∏ _c ∈ C, q := by
    intro C
    rw [Finset.prod_const, hq, mul_pow, ← Real.exp_nat_mul, mul_comm]
    ring_nf
  -- the bound of one term of the C-sum
  have hterm : ∀ a, ∀ C ∈ Finset.univ.filter (fun C : Finset ι => C.Nonempty ∧
      IsRootedFamily P (blockSites N (RA a)) C ∧ x ∈ rootRegion (RA a) PB C),
      ‖rootedCoef (τ a) φ₀ T w C‖ * ω (rootRegion (RA a) PB C) ≤
        b a * ω (RA a) * ∏ _c ∈ C, q := by
    intro a C hC
    obtain ⟨hne, hrt, -⟩ := (Finset.mem_filter.1 hC).2
    calc ‖rootedCoef (τ a) φ₀ T w C‖ * ω (rootRegion (RA a) PB C)
        ≤ (b a * Real.exp (-(κ - 1) * C.card)) * (ω (RA a) * θ ^ C.card) :=
          mul_le_mul (hcoef a C hne hrt) (hω a C) (hω0 _)
            (mul_nonneg (hb a) (Real.exp_pos _).le)
      _ = b a * ω (RA a) * (Real.exp (-(κ - 1) * C.card) * θ ^ C.card) := by ring
      _ = _ := by rw [hprodq]
  -- splitting the families by the position of `x`
  have hsplit : ∀ a, ∑ C ∈ Finset.univ.filter (fun C : Finset ι => C.Nonempty ∧
      IsRootedFamily P (blockSites N (RA a)) C ∧ x ∈ rootRegion (RA a) PB C), ∏ _c ∈ C, q ≤
      (if x ∈ RA a then Pr a else 0) +
        ∑ i₀ ∈ Finset.univ.filter (fun i : ι => x ∈ PB i),
          ∑ C ∈ Finset.univ.filter (fun C : Finset ι =>
            IsRootedFamily P (blockSites N (RA a)) C ∧ i₀ ∈ C), ∏ _c ∈ C, q := by
    intro a
    have hpt : ∀ C ∈ Finset.univ.filter (fun C : Finset ι => C.Nonempty ∧
        IsRootedFamily P (blockSites N (RA a)) C ∧ x ∈ rootRegion (RA a) PB C),
        ∏ _c ∈ C, q ≤ (if x ∈ RA a then ∏ _c ∈ C, q else 0) +
          ∑ i₀ ∈ Finset.univ.filter (fun i : ι => x ∈ PB i),
            (if i₀ ∈ C then ∏ _c ∈ C, q else 0) := by
      intro C hC
      obtain ⟨-, -, hx⟩ := (Finset.mem_filter.1 hC).2
      have hP0 : 0 ≤ ∏ _c ∈ C, q := Finset.prod_nonneg fun _ _ => hq0
      have hS0 : 0 ≤ ∑ i₀ ∈ Finset.univ.filter (fun i : ι => x ∈ PB i),
          (if i₀ ∈ C then ∏ _c ∈ C, q else 0) :=
        Finset.sum_nonneg fun i _ => ite_nonneg hP0 le_rfl
      rcases Finset.mem_union.1 hx with hxR | hxC
      · simp only [hxR, ↓reduceIte]; linarith
      · obtain ⟨i₀, hi₀, hxi⟩ := Finset.mem_biUnion.1 hxC
        have h1 : ∏ _c ∈ C, q ≤ ∑ i ∈ Finset.univ.filter (fun i : ι => x ∈ PB i),
            (if i ∈ C then ∏ _c ∈ C, q else 0) := by
          refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun i =>
            if i ∈ C then ∏ _c ∈ C, q else 0) (fun i _ => ite_nonneg hP0 le_rfl)
            (Finset.mem_filter.2 ⟨Finset.mem_univ _, hxi⟩))
          simp [hi₀]
        have h2 : 0 ≤ (if x ∈ RA a then ∏ _c ∈ C, q else 0) := ite_nonneg hP0 le_rfl
        linarith
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · by_cases hxR : x ∈ RA a
      · simp only [hxR, ↓reduceIte]
        refine le_trans ?_ (sum_rooted_prod_le (P := P) (blockSites N (RA a)) (fun _ => q)
          fun _ => hq0)
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun C hC => ?_) fun C _ _ =>
          Finset.prod_nonneg fun _ _ => hq0
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hC).2.2.1⟩
      · simp [hxR]
    · rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun i₀ _ => ?_
      rw [← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun C hC => ?_) fun C _ _ =>
        Finset.prod_nonneg fun _ _ => hq0
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hC
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 h1).2.2.1, h2⟩
  refine (sum_norm_localFormOf_le_weight w x ω hω0).trans ?_
  -- the bound for every term
  have hA : ∀ a, (if x ∈ RA a then ‖τ a φ₀‖ * ω (RA a) else 0) +
      ∑ C ∈ Finset.univ.filter (fun C : Finset ι => C.Nonempty ∧
        IsRootedFamily (blockPatch N PB) (blockSites N (RA a)) C ∧ x ∈ rootRegion (RA a) PB C),
        ‖rootedCoef (τ a) φ₀ T w C‖ * ω (rootRegion (RA a) PB C) ≤
      (if x ∈ RA a then (‖τ a φ₀‖ + b a * Pr a) * ω (RA a) else 0) +
        ∑ i₀ ∈ Finset.univ.filter (fun i : ι => x ∈ PB i), b a * ω (RA a) *
          ∑ l ∈ rootCells P (blockSites N (RA a)),
            (∑ K ∈ (animalsAt P l).filter (fun K => i₀ ∈ K), ∏ _m ∈ K, q) * Pr a := by
    intro a
    have hbw : 0 ≤ b a * ω (RA a) := mul_nonneg (hb a) (hω0 _)
    have h1 := Finset.sum_le_sum (hterm a)
    rw [← Finset.mul_sum] at h1
    have h2 := mul_le_mul_of_nonneg_left (hsplit a) hbw
    have h3 : ∀ i₀, ∑ C ∈ Finset.univ.filter (fun C : Finset ι =>
        IsRootedFamily P (blockSites N (RA a)) C ∧ i₀ ∈ C), ∏ _c ∈ C, q ≤
        ∑ l ∈ rootCells P (blockSites N (RA a)),
          (∑ K ∈ (animalsAt P l).filter (fun K => i₀ ∈ K), ∏ _m ∈ K, q) * Pr a := fun i₀ =>
      sum_rooted_mem_prod_le_leaders (P := P) (blockSites N (RA a)) (fun _ => q) (fun _ => hq0) i₀
    have h4 : b a * ω (RA a) * ∑ i₀ ∈ Finset.univ.filter (fun i : ι => x ∈ PB i),
        ∑ C ∈ Finset.univ.filter (fun C : Finset ι =>
          IsRootedFamily P (blockSites N (RA a)) C ∧ i₀ ∈ C), ∏ _c ∈ C, q ≤
        ∑ i₀ ∈ Finset.univ.filter (fun i : ι => x ∈ PB i), b a * ω (RA a) *
          ∑ l ∈ rootCells P (blockSites N (RA a)),
            (∑ K ∈ (animalsAt P l).filter (fun K => i₀ ∈ K), ∏ _m ∈ K, q) * Pr a := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i₀ _ => mul_le_mul_of_nonneg_left (h3 i₀) hbw
    by_cases hxR : x ∈ RA a
    · simp only [hxR, ↓reduceIte] at h2 ⊢
      rw [mul_add] at h2
      nlinarith
    · simp only [hxR, ↓reduceIte, zero_add] at h2 ⊢
      linarith
  refine (Finset.sum_le_sum fun a _ => hA a).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_comm (s := Finset.univ)]

end Balaban.Green
