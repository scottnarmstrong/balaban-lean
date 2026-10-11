/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.ThermoLimit

/-!
# Bounds on the limits and the consequences of Root-F's statement

Conditional on the clauses of Root-F; consumed by the Root-C provider.

* `abs_limit_onePoint_sub_le`, `abs_limit_twoPoint_le`: the bounds of Proposition 1.5 pass to the
  limits of Theorem 4.1 (CORRELATIONS.md, Theorem 4.1 (3));
* `onePoint_close_of_rootF` (Corollary 1.6): from the statement of Root-F, for every `ε > 0`
  there are `L, M, β₀` such that for `β ≥ β₀`, `ν ∈ (0, 1]` and unit `h` the one-point function on
  every admissible torus is within `ε` of `h`.
-/

@[expose] public section

open scoped Classical

namespace Balaban.Correlations

open Balaban Finset

variable {d N L M kf : ℕ} {β ν : ℝ} {h : EuclideanSpace ℝ (Fin N)} {κ c₉ δ : ℝ}
  {T : RootFFamily d N}

/-- Along the tori with side divisible by `(M L)^n`, a uniform bound passes to the limit. -/
theorem abs_sub_le_of_limit {q : ℕ} {f : (ℓ : ℕ) → [NeZero ℓ] → ℝ} {m c B : ℝ}
    (hlim : ∀ ε > 0, ∃ n0 : ℕ, ∀ (ℓ : ℕ) [NeZero ℓ], q ^ n0 ∣ ℓ → |f ℓ - m| < ε)
    (hb : ∀ n0 : ℕ, ∃ (ℓ : ℕ) (hℓ : NeZero ℓ), q ^ n0 ∣ ℓ ∧ |@f ℓ hℓ - c| ≤ B) :
    |m - c| ≤ B := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨n0, hn0⟩ := hlim ε hε
  obtain ⟨ℓ, hℓ, hdvd, hB⟩ := hb n0
  have := @hn0 ℓ hℓ hdvd
  calc |m - c| = |(@f ℓ hℓ - c) - (@f ℓ hℓ - m)| := by ring_nf
    _ ≤ |@f ℓ hℓ - c| + |@f ℓ hℓ - m| := abs_sub _ _
    _ < B + ε := by linarith

theorem abs_limit_onePoint_sub_le [NeZero N] (hcl : RootFClauses d N L M β ν h kf κ c₉ δ T)
    (hd : 3 ≤ d) (hδ : 0 < δ) (hL : 2 ≤ L) (hM : 1 ≤ M) (hc₉ : 0 ≤ c₉)
    (hκ : kappaStar d ≤ κ) (x : Fin d → ℤ) (i : Fin N) {m : ℝ}
    (hm : ∀ ε > 0, ∃ n0 : ℕ, ∀ (ℓ : ℕ) [NeZero ℓ], (M * L) ^ n0 ∣ ℓ →
      |onePoint d N ℓ β ν h (embedZ ℓ x) i - m| < ε) :
    |m - h i| ≤ 3 * c₉ := by
  have hq : 0 < M * L := by nlinarith
  refine abs_sub_le_of_limit (f := fun ℓ _ => onePoint d N ℓ β ν h (embedZ ℓ x) i) hm
    fun n0 => ?_
  set n := max n0 (kf + 1) with hn
  have hz : NeZero ((M * L) ^ n) := ⟨(pow_pos hq n).ne'⟩
  refine ⟨(M * L) ^ n, hz, pow_dvd_pow _ (le_max_left _ _), ?_⟩
  have hdiv : M * L ^ (kf + 1) ∣ (M * L) ^ n := admissible_of_dvd_pow (le_max_right _ _) dvd_rfl
  exact abs_onePoint_sub_le (hcl.1 _ hdiv) hdiv hd hδ hL hc₉ hκ _ i

theorem torusDist_embedZ {ℓ R : ℕ} [NeZero ℓ] (hℓ : 4 * R ≤ ℓ) {x y : Fin d → ℤ}
    (hxy : ∀ μ, (x μ - y μ).natAbs < R) :
    torusDist (embedZ ℓ x) (embedZ ℓ y) = Finset.univ.sup fun μ => (x μ - y μ).natAbs := by
  unfold torusDist
  congr 1
  funext μ
  have hw : (x - y) ∈ boxZ d R := mem_boxZ.2 fun μ => by
    rw [Int.abs_eq_natAbs]
    simpa using (by exact_mod_cast hxy μ : (((x μ - y μ).natAbs : ℕ) : ℤ) < R)
  have := valMinAbs_embedZ hℓ hw μ
  unfold torusNorm
  have e : embedZ ℓ x μ - embedZ ℓ y μ = embedZ ℓ (x - y) μ := by simp [embedZ]
  rw [e, this]
  rfl

/-- Proposition 1.5 (b) passes to the limit. -/
theorem exists_abs_limit_twoPoint_le (d L M : ℕ) (δ κ : ℝ) (hd : 3 ≤ d) (hδ : 0 < δ)
    (hL : 2 ≤ L) (hM : 1 ≤ M) (hκ : kappaStar d ≤ κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ)
      (c₉ : ℝ) (T : RootFFamily d N), RootFClauses d N L M β ν h kf κ c₉ δ T → 0 ≤ c₉ →
      0 < ν → (L : ℝ) ^ kf * Real.sqrt ν ≤ L →
      ∀ (x y : Fin d → ℤ) (i k : Fin N) (G : ℝ),
        (∀ ε > 0, ∃ n0 : ℕ, ∀ (ℓ : ℕ) [NeZero ℓ], (M * L) ^ n0 ∣ ℓ →
          |twoPointTruncated d N ℓ β ν h (embedZ ℓ x) (embedZ ℓ y) i k - G| < ε) →
        |G| ≤ C * c₉ *
          (1 + ((Finset.univ.sup fun μ => (x μ - y μ).natAbs : ℕ) : ℝ)) ^
            (-(((d : ℝ) - 2) / 2 + δ)) *
          Real.exp (-(κ / (4 * (M : ℝ) * (L : ℝ) ^ 2) * Real.sqrt ν *
            ((Finset.univ.sup fun μ => (x μ - y μ).natAbs : ℕ) : ℝ))) := by
  obtain ⟨C, hC, hbound⟩ := exists_abs_twoPointTruncated_le d L M δ κ hd hδ hL hM hκ
  refine ⟨C, hC, fun N _ β ν h kf c₉ T hcl hc₉ hν hkf x y i k G hG => ?_⟩
  have hq : 2 ≤ M * L := by nlinarith
  set D : ℕ := Finset.univ.sup fun μ => (x μ - y μ).natAbs with hD
  have hxy : ∀ μ, (x μ - y μ).natAbs < D + 1 := fun μ =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun μ => (x μ - y μ).natAbs) (Finset.mem_univ μ))
  have key := abs_sub_le_of_limit (f := fun ℓ _ => twoPointTruncated d N ℓ β ν h (embedZ ℓ x)
    (embedZ ℓ y) i k) (c := 0) (B := C * c₉ *
          (1 + (D : ℝ)) ^ (-(((d : ℝ) - 2) / 2 + δ)) *
          Real.exp (-(κ / (4 * (M : ℝ) * (L : ℝ) ^ 2) * Real.sqrt ν * (D : ℝ)))) hG ?_
  · simpa using key
  intro n0
  set n := max n0 (max (kf + 1) (4 * (D + 1))) with hn
  have hdiv : M * L ^ (kf + 1) ∣ (M * L) ^ n :=
    admissible_of_dvd_pow ((le_max_left _ _).trans (le_max_right _ _)) dvd_rfl
  have hz : NeZero ((M * L) ^ n) := ⟨(pow_pos (by omega) n).ne'⟩
  refine ⟨(M * L) ^ n, hz, pow_dvd_pow _ (le_max_left _ _), ?_⟩
  have h4 : 4 * (D + 1) ≤ (M * L) ^ n :=
    four_mul_le_of_dvd_pow hq (pow_pos (by omega) n)
      (le_trans (le_max_right _ _) (le_max_right _ _)) dvd_rfl
  have := hbound N β ν h kf c₉ T ((M * L) ^ n) (hcl.1 _ hdiv) hdiv hc₉ hν hkf
    (embedZ _ x) (embedZ _ y) i k
  rw [torusDist_embedZ h4 hxy] at this
  simpa using this

/-- Corollary 1.6: from the statement of Root-F, the one-point function is within `ε` of `h` on
every admissible torus, for `β` large, uniformly in `ν ∈ (0, 1]` and the unit vector `h`. -/
theorem onePoint_close_of_rootF [NeZero N] (hRoot : RootFStatement d N) (hd : 3 ≤ d) :
    ∀ ε > 0, ∃ L M : ℕ, 2 ≤ L ∧ 1 ≤ M ∧ ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
      ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
      ∃ kf : ℕ, ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ →
        ∀ (x : Torus d ℓ) (i : Fin N), |onePoint d N ℓ β ν h x i - h i| ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := hRoot
  have hκ : 0 < max (kappaStar d) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨L, M, hL, hM, β₀, H'⟩ := H _ hκ (ε / 3) (by positivity)
  refine ⟨L, M, hL, hM, β₀, fun β hβ ν hν hν1 h hh => ?_⟩
  obtain ⟨kf, -, -, T, hT⟩ := H' β hβ ν hν hν1 h hh
  refine ⟨kf, fun ℓ _ hdiv x i => ?_⟩
  have := abs_onePoint_sub_le (hT.1 ℓ hdiv) hdiv hd hδ hL (by positivity)
    (le_max_left _ _) x i
  linarith

end Balaban.Correlations
