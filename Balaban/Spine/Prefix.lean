/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RootFInputs
public import Balaban.LargeField.Counter.LamBounds
public import Balaban.Flow.RunningCoefficients
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The prefix input is satisfiable

`prefixInput_exists`: for every `L ≥ 3` and every `0 < δ < 1/2` there are constants of the prefix
(as functions of `κ, c₉`) satisfying `PrefixInput`. The witness takes `m₀ = 1`, `m₁ = 3`,
`M = c = L⁴`, `M₁ = 1`, the kernel constant `a = 5/4`, the Def-6 exponents `γ = (1+2δ)/4`,
`α₁ = (1-2δ)/4` (so `γ - α₁ = δ`), `κ_flow = 3^{d+1} L^{2d+1} (κ+1)` and
`c₉^{flow} = (c₉/2) e^{-κ_flow}`. The typing is `prefixTyping d L` (`R_base = 32`,
`θ_± = (d-2) log L`, `α = 1`, `p₀ = d + 2`, `p₂ = 2d + 3`, `p_R = 4d + 4`, `c_v = 5 M^d`,
`c_H = d² log L`, `c₀ = 10`), the budget constants are `c₁ = c₂ = 0`, `H₀ = 2` and `ϱ = R₀(d, L)`
(`bgR0`). The clauses of `PrefixInput` are jointly satisfiable at every
`L ≥ 3`; no clause forces `L = 7`.  The core `prefixInput_exists_of` takes the radius constant
`α₀` and the flow constant `c₈` as parameters (the ties of the new level, `Spine/NewLevelTies.lean`,
ask both small).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.SmallField

/-- The typing constants of the witness of `PrefixInput`, before `C_ν` is fixed. -/
noncomputable def prefixTyping0 (d L m₁ : ℕ) : Typing where
  d := d
  L := L
  M := L ^ (1 + m₁)
  Rb := 32
  θp := thetaOf d L
  θm := thetaOf d L
  α := 1
  p0 := d + 2
  p2 := 2 * d + 3
  pR := 4 * d + 4
  A2 := 1
  A3 := 1
  A3' := 1
  CR := 0
  Cν := 0
  cv := ((L ^ (1 + m₁) : ℕ) : ℝ) ^ d * 5
  cH := (d : ℝ) ^ 2 * Real.log L
  sS := 4
  sP := 5
  c0 := 10

/-- **The typing of the witness of `PrefixInput`** (`C_ν = C_r`). -/
noncomputable def prefixTyping (d L m₁ : ℕ) : Typing :=
  { prefixTyping0 d L m₁ with Cν := (prefixTyping0 d L m₁).Cr }

@[simp] theorem prefixTyping_L (d L m₁ : ℕ) : (prefixTyping d L m₁).L = L := rfl

theorem thetaOf_pos {d L : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ L) : 0 < thetaOf d L := by
  unfold thetaOf
  have h1 : (0 : ℝ) < ((d - 2 : ℕ) : ℝ) := by
    have : 0 < d - 2 := by omega
    exact_mod_cast this
  have h2 : 0 < Real.log (L : ℝ) := Real.log_pos (by exact_mod_cast hL)
  positivity

/-- The typing of the witness is `Typing.Ok` for every `d ≥ 3`, `L ≥ 3`. -/
theorem prefixTyping_ok {d L m₁ : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) : (prefixTyping d L m₁).Ok where
  three_le_d := hd
  two_le_L := by show 2 ≤ L; omega
  one_le_M := by show 1 ≤ L ^ (1 + m₁); exact Nat.one_le_pow _ _ (by omega)
  two_le_Rb := by show (2 : ℝ) ≤ 32; norm_num
  θm_pos := thetaOf_pos hd (by omega)
  θm_le_θp := le_refl _
  α_pos := by show (0 : ℝ) < 1; norm_num
  A2_pos := by show (0 : ℝ) < 1; norm_num
  A3_pos := by show (0 : ℝ) < 1; norm_num
  A3'_pos := by show (0 : ℝ) < 1; norm_num
  CR_nonneg := le_refl _
  Cν_pos := by
    show 0 < (prefixTyping0 d L m₁).Cr
    have hθ := thetaOf_pos hd (show 2 ≤ L by omega)
    have hl : 0 < (prefixTyping0 d L m₁).logL := Real.log_pos (by
      show (1 : ℝ) < (L : ℝ)
      exact_mod_cast (by omega : 1 < L))
    have h1 : 0 ≤ (prefixTyping0 d L m₁).cStar := by
      unfold Typing.cStar
      have : (0 : ℝ) ≤ (prefixTyping0 d L m₁).θp / ((prefixTyping0 d L m₁).α * (prefixTyping0 d L m₁).logL) :=
        div_nonneg hθ.le (mul_nonneg (by show (0 : ℝ) ≤ 1; norm_num) hl.le)
      linarith
    have h2 : 0 ≤ (prefixTyping0 d L m₁).cPrime := by
      unfold Typing.cPrime
      exact mul_nonneg h1 (by show (0 : ℝ) ≤ 1 + 3 * thetaOf d L; linarith)
    unfold Typing.Cr
    have : (0 : ℝ) ≤ 2 * (prefixTyping0 d L m₁).A2 * (prefixTyping0 d L m₁).cPrime ^ (prefixTyping0 d L m₁).p2 :=
      mul_nonneg (by show (0 : ℝ) ≤ 2 * 1; norm_num) (pow_nonneg h2 _)
    linarith
  one_le_cv := by
    show (1 : ℝ) ≤ ((L ^ (1 + m₁) : ℕ) : ℝ) ^ d * 5
    have : (1 : ℝ) ≤ ((L ^ (1 + m₁) : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow _ _ (by omega)
    have := one_le_pow₀ (n := d) this
    linarith
  cH_nonneg := by
    show (0 : ℝ) ≤ (d : ℝ) ^ 2 * Real.log L
    exact mul_nonneg (sq_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L)))
  p2_ge := le_rfl
  pR_gt := by show 2 * d + 3 + 2 * d < 4 * d + 4; omega
  p0_gt := by show 2 * d + 3 < 2 * (d + 2); omega
  c0_sS := by
    show ((4 : ℕ) : ℝ) + 1 ≤ ((10 : ℕ) : ℝ) * (1 - 1 / (L : ℝ))
    have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
    have : 1 / (L : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hL3
    push_cast
    linarith
  c0_sP := by show 5 + 1 ≤ 10; norm_num
  Cr_le := le_refl _

/-- **Core of `prefixInput_exists`: the witness at any radius constant `α₀ > 0` and any flow
constant `0 < c₈` with `c₈ q ≤ (1 - q)/20`, `q = L^{-2γ}`, `γ = (1 + 2δ)/4`.**  The constants of the
witness have `L` as block size, `γ = (1 + 2δ)/4`, and the given `α₀`, `c₈`. -/
theorem prefixInput_exists_of (d L : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ < 1 / 2) {α₀ c₈ : ℝ} (hα₀ : 0 < α₀) (hc₈ : 0 < c₈)
    (hc₈q : c₈ * Flow.rate (L : ℝ) ((1 + 2 * δ) / 4) ≤
      1 / 20 * (1 - Flow.rate (L : ℝ) ((1 + 2 * δ) / 4))) :
    ∃ (Ty : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts) (C7 : ℝ → ℝ → Consts7)
      (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts) (M1 c : ℝ → ℝ → ℕ) (ϱ : ℝ → ℝ → ℝ),
      PrefixInput d δ Ty P6 C7 PB cs₀ M1 c ϱ ∧ ∀ κ c₉ : ℝ, (Ty κ c₉).L = L ∧
        (P6 κ c₉).γ = (1 + 2 * δ) / 4 ∧ (P6 κ c₉).α₀ = α₀ ∧ (P6 κ c₉).c₈ = c₈ := by
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hL2 : (9 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have hLpos : (0 : ℝ) < (L : ℝ) ^ 2 := by linarith
  have hinv : ((L : ℝ) ^ 2)⁻¹ ≤ 1 / 9 := by
    rw [inv_le_comm₀ hLpos (by norm_num)]; norm_num; exact hL2
  have hinv0 : 0 < ((L : ℝ) ^ 2)⁻¹ := inv_pos.2 hLpos
  have h14 : 14 ≤ L ^ 3 := by
    calc 14 ≤ 3 ^ 3 := by norm_num
      _ ≤ L ^ 3 := Nat.pow_le_pow_left hL _
  obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt (Background.bgR0 d L) (by linarith : (1 : ℝ) < L)
  have hMs : L ^ (1 + (2 + s)) = L ^ 3 * L ^ s := by
    rw [← pow_add]; congr 1; omega
  have hsep : Background.bgR0 d L ≤ minSep L (L ^ s) := by
    have h1 : (1 : ℝ) ≤ 5 * L := by linarith
    have h2 : (0 : ℝ) ≤ (L : ℝ) ^ s := by positivity
    unfold minSep
    push_cast
    nlinarith
  have hq0 : 0 < Flow.rate (L : ℝ) ((1 + 2 * δ) / 4) :=
    Flow.rate_pos (by linarith) _
  have hq1 : Flow.rate (L : ℝ) ((1 + 2 * δ) / 4) < 1 :=
    Flow.rate_lt_one (by linarith) (by linarith)
  refine ⟨fun _ _ => prefixTyping d L (2 + s),
    fun κ c₉ => ⟨(1 + 2 * δ) / 4, (1 - 2 * δ) / 4,
      ((3 : ℝ) ^ (d + 1) * (L : ℝ) ^ (2 * d + 1) * (κ + 1) + Balaban.Fluctuation.aEnt d L + 2), 0,
      c₈,
      c₉ / 2 * Real.exp (-((3 : ℝ) ^ (d + 1) * (L : ℝ) ^ (2 * d + 1) * (κ + 1) + Balaban.Fluctuation.aEnt d L + 2)), α₀, 1,
      7 / 8 * ((L : ℝ) ^ 2)⁻¹, fun _ => 1, 1⟩,
    fun _ _ => ⟨2 + s, 1, 0, 1, 0⟩, fun _ _ => ⟨0, 0, 2, fun _ => 1⟩,
    fun _ _ => ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, 0,
      fun _ => 0, fun _ => 0, 5 / 4, 0, 1⟩,
    fun _ _ => L ^ s, fun _ _ => L ^ 3, fun _ _ => Background.bgR0 d L, ?_,
    fun _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩
  intro κ hκ c₉ hc₉
  have : NeZero L := ⟨by omega⟩
  have haE := Balaban.Fluctuation.aEnt_nonneg d L
  have hκf : 0 < (3 : ℝ) ^ (d + 1) * (L : ℝ) ^ (2 * d + 1) * (κ + 1) +
      Balaban.Fluctuation.aEnt d L + 2 := by positivity
  refine ⟨hL, by norm_num, by norm_num, ?_, hMs, h14, Nat.one_le_pow _ _ (by omega), rfl, ?_, ?_, by norm_num,
    le_rfl, ?_, ?_, ?_, ?_, le_rfl, ?_, by norm_num, hsep, ?_⟩
  · have h1 : (8 : ℝ) / 9 ≤ 1 - ((L : ℝ) ^ 2)⁻¹ := by linarith
    have h2 : (64 : ℝ) / 81 ≤ (1 - ((L : ℝ) ^ 2)⁻¹) ^ 2 := by nlinarith
    show (9 : ℝ) / 10 ≤ 5 / 4 * (1 - ((L : ℝ) ^ 2)⁻¹) ^ 2
    nlinarith
  · refine ⟨?_, ?_, ?_, ?_, hα₀, hκf, mul_pos (by norm_num) hinv0, ?_, hc₈, le_rfl⟩ <;>
      (try simp only [prefixTyping_L]) <;> linarith
  · show 0 < c₉ / 2 * Real.exp _
    positivity
  · show δ ≤ (1 + 2 * δ) / 4 - (1 - 2 * δ) / 4
    linarith
  · show (3 : ℝ) ^ (d + 1) * (L : ℝ) ^ (2 * d + 1) * (κ + 1) ≤ _
    linarith
  · exact le_rfl
  · have hlog : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L))
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    refine ⟨prefixTyping_ok hd hL, ⟨le_rfl, le_rfl⟩, ?_, by show (0 : ℝ) < 2; norm_num,
      le_rfl, ?_, ?_⟩
    · show (d : ℝ) * ((d : ℝ) - 2) / 2 * Real.log L ≤ (d : ℝ) ^ 2 * Real.log L
      apply mul_le_mul_of_nonneg_right _ hlog
      nlinarith
    · show L ≤ L ^ (1 + (2 + s))
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ (1 + (2 + s)) := Nat.pow_le_pow_right (by omega) (by omega)
    · show ((L ^ (1 + (2 + s)) : ℕ) : ℝ) ^ d * (2 + 0 + 3) ≤ ((L ^ (1 + (2 + s)) : ℕ) : ℝ) ^ d * 5
      norm_num
  · exact hc₈q
  · show Balaban.Fluctuation.aEnt d L + 1 < (3 : ℝ) ^ (d + 1) * (L : ℝ) ^ (2 * d + 1) * (κ + 1) +
      Balaban.Fluctuation.aEnt d L + 2
    have : 0 < (3 : ℝ) ^ (d + 1) * (L : ℝ) ^ (2 * d + 1) * (κ + 1) := by positivity
    linarith

/-- **`PrefixInput` is satisfiable** at every `d ≥ 3`, every `L ≥ 3` and every `0 < δ < 1/2`. -/
theorem prefixInput_exists (d L : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ < 1 / 2) :
    ∃ (Ty : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts) (C7 : ℝ → ℝ → Consts7)
      (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts) (M1 c : ℝ → ℝ → ℕ) (ϱ : ℝ → ℝ → ℝ),
      PrefixInput d δ Ty P6 C7 PB cs₀ M1 c ϱ := by
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hq0 : 0 < Flow.rate (L : ℝ) ((1 + 2 * δ) / 4) := Flow.rate_pos (by linarith) _
  have hq1 : Flow.rate (L : ℝ) ((1 + 2 * δ) / 4) < 1 :=
    Flow.rate_lt_one (by linarith) (by linarith)
  obtain ⟨Ty, P6, C7, PB, cs₀, M1, c, ϱ, h, -⟩ := prefixInput_exists_of d L hd hL hδ hδ'
    (α₀ := 1) (c₈ := (1 - Flow.rate (L : ℝ) ((1 + 2 * δ) / 4)) /
      (20 * Flow.rate (L : ℝ) ((1 + 2 * δ) / 4))) one_pos (div_pos (by linarith) (by positivity))
    (le_of_eq (by field_simp))
  exact ⟨Ty, P6, C7, PB, cs₀, M1, c, ϱ, h⟩
