/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RootParams
public import Balaban.Flow.StopIndex
public import Balaban.Fluctuation.SharpChartTest
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Links of the constants of Root-F

* For every `d ≥ 3`, `δ = min((d-2)/8, 1/8)` (the core `exists_rootParams_of_delta` holds at any `δ`)
  is `γ - α₁` of a class `Consts` with `γ ≤ 1/4` (the hypothesis of `chartTest_sharp_three`),
  `0 < α₁ < 1 - 2γ`, `P.κ = κ`, `P.c₉ = c₉`; `δ < 1/4` holds for every `d`.
* Under `RunningHyp`, the stopping index `kStop` satisfies the clauses on `k_f`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Green
open Balaban.SmallField.Def6 (Consts)

/-- **The constants of Root-F with the class exponents and `k_f = kStop`** (every `d ≥ 3`).  `δ` is
`γ - α₁` with `γ ≤ 1/4` and `0 < α₁ < 1 - 2γ`; for each `κ, c₉` the class constants `P` are
admissible at the chosen `L` with `P.κ = κ`, `P.c₉ = c₉`, `P.γ = γ`, `P.α₁ = α₁`; and for every
running sequence with `ν ≤ 1` the stopping index `kStop` satisfies the clauses on `k_f`. -/
theorem exists_rootParams_consts_all (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ((d : ℝ) - 2) / 4 ∧
    ∃ γ α₁ : ℝ, 0 < γ ∧ γ ≤ 1 / 4 ∧ 0 < α₁ ∧ α₁ < 1 - 2 * γ ∧ γ - α₁ = δ ∧
    ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
    ∃ L M : ℕ, 2 ≤ L ∧ 6 ≤ L ∧ Odd L ∧ 1 ≤ M ∧
    ∃ (_ : NeZero L) (κmin : ℝ) (T : StepTowerThetaG d L N κmin),
      T.m₀ = 1 ∧ M = L ^ (T.m₁ + 1) ∧
      (∀ q J K : ℕ, 1 ≤ q → 5 < q * L ^ T.m₀ * L ^ (J - K)) ∧
      c1 d L * κ ≤ 3 / 2 * T.κdec ∧
      4 * (pdB d L * Real.exp (pdH d * max κ 1)) ≤ (M : ℝ) ∧
      8 * max κ 1 * 7 ^ d ≤ pdEps d L * (M : ℝ) ∧
      (∃ P : Consts, P.Admissible d L ∧ P.γ = γ ∧ P.α₁ = α₁ ∧ P.κ = κ ∧ P.c₉ = c₉ ∧
        P.m₀ = T.m₀) ∧
    ∀ C C' B p R : ℝ, 0 < C → 0 < C' → 0 < R →
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ) ≤ c₉ * β₀ ^ 2 ∧
    ∀ β : ℝ, β₀ ≤ β →
      (C * C' * Real.exp (3 / 2 * T.κdec) * (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ) / c₉) ^
          (1 / ((((d : ℝ) - 2) / 2 + δ) / ((d : ℝ) - 2))) ≤ β ∧
      (B * p / R) ^ 2 + 1 ≤ β ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
    (∃ kf : ℕ, (L : ℝ) ^ kf * Real.sqrt ν ≤ L ∧ 1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν) ∧
    ∀ (a ε : ℝ) (bR nR : ℕ → ℝ) (hR : LargeField.RunningHyp d L β ν a ε bR nR),
      (L : ℝ) ^ LargeField.StopIndex.kStop hR * Real.sqrt ν ≤ L ∧
        1 / 2 ≤ (L : ℝ) ^ (LargeField.StopIndex.kStop hR + 1) * Real.sqrt ν := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set δ : ℝ := min (((d : ℝ) - 2) / 8) (1 / 8) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1' : δ < 1 / 4 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδ1 : δ < ((d : ℝ) - 2) / 4 := by
    have := min_le_left (((d : ℝ) - 2) / 8) (1 / 8)
    have h2 : 0 < ((d : ℝ) - 2) := by linarith
    linarith
  have H := exists_rootParams_of_delta d N hd hN δ
  set α₁ : ℝ := (1 / 4 - δ) / 2 with hα₁
  have hα₁0 : 0 < α₁ := by rw [hα₁]; linarith
  refine ⟨δ, hδ0, hδ1, δ + α₁, α₁, by linarith, by rw [hα₁]; linarith, hα₁0,
    by rw [hα₁]; linarith, by ring, ?_⟩
  intro κ hκ c₉ hc₉
  obtain ⟨L, M, h2, h6, hodd, hM, hnz, κmin, T, hm, hMT, h5, hrate, hMB, hMκ, hrest⟩ :=
    H κ hκ c₉ hc₉
  refine ⟨L, M, h2, h6, hodd, hM, hnz, κmin, T, hm, hMT, h5, hrate, hMB, hMκ, ?_, ?_⟩
  · have hL : (0 : ℝ) < (L : ℝ) ^ 2 := by
      have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
      positivity
    refine ⟨⟨δ + α₁, α₁, κ, 0, 1, c₉, 1, 1, 7 / 16 * ((L : ℝ) ^ 2)⁻¹, fun _ => 1, T.m₀⟩,
      ⟨?_, ?_, ?_, ?_, ?_, hκ, ?_, ?_, ?_, le_rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
    · show 0 < δ + α₁; linarith
    · show δ + α₁ < 1 / 2; linarith
    · exact hα₁0
    · show α₁ < 1 - 2 * (δ + α₁); linarith
    · exact one_pos
    · show 0 < 7 / 16 * ((L : ℝ) ^ 2)⁻¹; positivity
    · show 7 / 16 * ((L : ℝ) ^ 2)⁻¹ ≤ 7 / 8 * ((L : ℝ) ^ 2)⁻¹
      have : 0 < ((L : ℝ) ^ 2)⁻¹ := inv_pos.2 hL
      linarith
    · exact one_pos
  · intro C C' B p R hC hC' hR
    obtain ⟨β₀, h3, hβ₀, hβ⟩ := hrest C C' B p R hC hC' hR
    refine ⟨β₀, h3, hβ₀, fun β hβ₁ => ?_⟩
    obtain ⟨hA, hB, hν⟩ := hβ β hβ₁
    refine ⟨hA, hB, fun ν hν0 hν1 h hh => ⟨hν ν hν0 hν1 h hh, ?_⟩⟩
    intro a ε bR nR hRun
    exact LargeField.StopIndex.kStop_rootF_scale hRun hν1

/-- **The constants of Root-F with the class exponents and `k_f = kStop`** (`d = 3`); the
instance `d = 3` of `exists_rootParams_consts_all`. -/
theorem exists_rootParams_consts (N : ℕ) (hN : 2 ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧ δ < (((3 : ℕ) : ℝ) - 2) / 4 ∧
    ∃ γ α₁ : ℝ, 0 < γ ∧ γ ≤ 1 / 4 ∧ 0 < α₁ ∧ α₁ < 1 - 2 * γ ∧ γ - α₁ = δ ∧
    ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
    ∃ L M : ℕ, 2 ≤ L ∧ 6 ≤ L ∧ Odd L ∧ 1 ≤ M ∧
    ∃ (_ : NeZero L) (κmin : ℝ) (T : StepTowerThetaG 3 L N κmin),
      T.m₀ = 1 ∧ M = L ^ (T.m₁ + 1) ∧
      (∀ q J K : ℕ, 1 ≤ q → 5 < q * L ^ T.m₀ * L ^ (J - K)) ∧
      c1 3 L * κ ≤ 3 / 2 * T.κdec ∧
      4 * (pdB 3 L * Real.exp (pdH 3 * max κ 1)) ≤ (M : ℝ) ∧
      8 * max κ 1 * 7 ^ 3 ≤ pdEps 3 L * (M : ℝ) ∧
      (∃ P : Consts, P.Admissible 3 L ∧ P.γ = γ ∧ P.α₁ = α₁ ∧ P.κ = κ ∧ P.c₉ = c₉ ∧
        P.m₀ = T.m₀) ∧
    ∀ C C' B p R : ℝ, 0 < C → 0 < C' → 0 < R →
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      (L : ℝ) ^ ((((3 : ℕ) : ℝ) - 2) / 2 + δ) ≤ c₉ * β₀ ^ 2 ∧
    ∀ β : ℝ, β₀ ≤ β →
      (C * C' * Real.exp (3 / 2 * T.κdec) * (L : ℝ) ^ ((((3 : ℕ) : ℝ) - 2) / 2 + δ) / c₉) ^
          (1 / (((((3 : ℕ) : ℝ) - 2) / 2 + δ) / (((3 : ℕ) : ℝ) - 2))) ≤ β ∧
      (B * p / R) ^ 2 + 1 ≤ β ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
    (∃ kf : ℕ, (L : ℝ) ^ kf * Real.sqrt ν ≤ L ∧ 1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν) ∧
    ∀ (a ε : ℝ) (bR nR : ℕ → ℝ) (hR : LargeField.RunningHyp 3 L β ν a ε bR nR),
      (L : ℝ) ^ LargeField.StopIndex.kStop hR * Real.sqrt ν ≤ L ∧
        1 / 2 ≤ (L : ℝ) ^ (LargeField.StopIndex.kStop hR + 1) * Real.sqrt ν := by
  exact exists_rootParams_consts_all 3 N le_rfl hN

end Balaban.Inhabited
