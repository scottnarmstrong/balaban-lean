/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.Prefix
public import Balaban.Inhabited.NewLevelLocalFamilyBirth

/-!
# The ties of the new level (the constants of the class chain in the prefix)

The provider of the new level on the local generating sets (row (iii) of A4-1b,
`StepTowerG.newLevel_localFamilies_birth_of`) runs the class chain at a base tower `T₀` and asks
conditions on constants that do not depend on `β` or on the scale: the block size large (T1,
`L^{(d-2)/2-γ} ≥ 16`), the radius constant `α₀` small (the smallness of `ε_1` of the chain and
T2), the flow constant `c₈` small (T3 and the flow conditions of the birth masses), the base tower
with its numerics and `λ ε_1 ≤ T₀.t`, the separation of the generating sets `ϱ = rhoSepG d L m₁` with
`m₁` the block exponent of the tower, and the cell exponent `m₀` large against the cube exponent
`s = hatScale L m₁ ϱ` of the local sets (ruling R13).  They are fixed with the constants of the
prefix (LFR §I.1.4), before `β₀`; they depend on the number `N` of components, which is not a
parameter of `PrefixInput`, so they form a separate input `NewLevelTiesInput` beside it.

* `NewLevelTies`, `NewLevelTiesInput`;
* `exists_rhoSepG_le_minSep`, `exists_hatScale_bound`: the cube exponent of `rhoSepG d L m₁` is
  bounded independently of `m₁`;
* `prefixInput_newLevelTies_exists`: `PrefixInput` and `NewLevelTiesInput` hold together for every
  `L ≥ 3` with `L^{(d-2)/2-γ} ≥ 16` (the witness of `prefixInput_exists_of` with `m₀` large, the
  base tower of `exists_collarBase_newLevel`, `m₁` its block exponent, `ϱ = rhoSepG d L m₁`, `α₀` and
  `c₈` small); `exists_large_L`: such `L` exist.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.SmallField Balaban.SmallField.Def6 Balaban.Background Balaban.Localization
  Balaban.Fluctuation Balaban.Inhabited Balaban.Inhabited.LevelStep Balaban.SmallField.GsSpec
  Balaban.LargeField.Def7 Balaban.Multiscale

/-- **The ties of the new level** at the block size `L`, the Def-6 constants `P` (`γ`, `α₀`, `c₈`,
`m₀`), the block exponent `m₁` and the separation `ϱ`, for `N` components: the conditions on
constants of the class chain and of the new level on the local generating sets that do not depend on
`β` or on the scale.  `τ₁ = exp(3 (c₈/4) q²/(1 - q)) - 1`, `q = L^{-2γ}`, is the defect of the birth
masses along the flow; `ε₁ = P.eps d L 1`. -/
structure NewLevelTies (d N L : ℕ) [NeZero L] (P : Def6.Consts) (m₁ : ℕ) (ϱ : ℝ) : Prop where
  /-- (T1) the block size is large: `L^{-α} ≤ 1/16`, `α = (d-2)/2 - γ` -/
  large_L : (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - P.γ)) ≤ 1 / 16
  /-- the base tower of the class chain, with the closeness ratio `K₂ Q ≤ 1/16`, the numerics of the
  new level, the block exponent `m₁` and room for the step radii `λ ε_{k+1}`, `λ ≤ 17/16` -/
  tower : ∃ (κmin : ℝ) (T₀ : StepTowerG d L N κmin) (κdec : ℝ),
    CollarBase d L N P.m₀ ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - P.γ))) T₀ κdec ∧
    xiK2 d L N * ((N : ℝ) * composedCloseBound d L N T₀.m₁ T₀.BG T₀.κ (xiC1 d)
      (4 * (d : ℝ) * (L : ℝ) ^ 3 + L)) ≤ 1 / 16 ∧
    Nonempty (NewLevelNumerics d L N T₀.m₁ T₀.c T₀.BG T₀.κ T₀.t T₀.c₂ T₀.BG₂ T₀.δc
      (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) ((2 * bgK1 d L N + 2) * xiC1 d * T₀.t)) ∧
    T₀.m₁ = m₁ ∧ 17 / 16 * P.eps d L 1 ≤ T₀.t
  /-- the separation of the generating sets of the chain -/
  sep : ϱ = rhoSepG d L m₁
  /-- the cell exponent `m₀ ≥ d` -/
  m₀_ge : d ≤ P.m₀
  /-- the cubes of the local sets are finer than the cells (ruling R13) -/
  hat_lt : hatScale L m₁ ϱ < P.m₀
  /-- the margin of the local sets inside the cells (`ClassHatCond`) -/
  hat_margin : (((5 * L + 13) * L ^ hatScale L m₁ ϱ + L / 2 * L ^ P.m₀ : ℕ) : ℝ) +
      (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) * L ≤ (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (P.m₀ + 1)
  /-- `α₀` small: the smallness of `ε_1` in the charts of the old terms -/
  eps_small : (4 * d + 6) * ((2 * d + 1) * P.eps d L 1) ≤ 1
  /-- `α₀` small: the radius of the background theorem -/
  eps_c1 : 4 * (xiC1 d * P.eps d L 1) ≤ bgC1 d L N
  /-- (T2) `α₀` small: the quadratic term of the (DL-gap) -/
  eps_quad : ((N : ℝ) + 1) * cK2 d L N * P.eps d L 1 ≤ 1 / 8
  /-- `c₈` small: the defect of the birth masses -/
  tau_small : Real.exp (3 * (P.c₈ / 4 * (Flow.rate (L : ℝ) P.γ ^ 2 /
    (1 - Flow.rate (L : ℝ) P.γ)))) - 1 ≤ 1 / 14
  /-- (T3) `c₈` small: the mass factor of the (DL-gap) -/
  tau_K : (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * (2 * (Real.exp (3 * (P.c₈ / 4 *
    (Flow.rate (L : ℝ) P.γ ^ 2 / (1 - Flow.rate (L : ℝ) P.γ)))) - 1)) ≤ 1 / 9
  /-- `c₈` small: the rate condition `c₈ q ≤ 1 - q` of the flow of the birth masses -/
  c8_rate : P.c₈ * Flow.rate (L : ℝ) P.γ ≤ 1 - Flow.rate (L : ℝ) P.γ
  /-- the radius of the mass response at the unit witness -/
  rm : ∃ rm : ℝ, 2 * (Real.exp (3 * (P.c₈ / 4 * (Flow.rate (L : ℝ) P.γ ^ 2 /
      (1 - Flow.rate (L : ℝ) P.γ)))) - 1) < rm ∧ rm ≤ 1 / 16 ∧
    bgK1 d L N * (xiC1 d * P.eps d L 1) + 3 * rm ≤ deltaStar d L N ∧
    8 * P.eps d L 1 * rm ≤ deltaStar d L N

/-- **The ties of the new level as an input of the spine** (beside `PrefixInput`): for every
`κ, c₉ > 0` the constants of the prefix satisfy `NewLevelTies` with `N` components. -/
def NewLevelTiesInput (d N : ℕ) (T : ℝ → ℝ → LargeField.Typing) (P6 : ℝ → ℝ → Def6.Consts)
    (C7 : ℝ → ℝ → Consts7) (ϱ : ℝ → ℝ → ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∀ [NeZero (T κ c₉).L],
    NewLevelTies d N (T κ c₉).L (P6 κ c₉) (C7 κ c₉).m₁ (ϱ κ c₉)

theorem NewLevelTies.congr_L {d N L L' : ℕ} [NeZero L] [NeZero L'] (h : L = L')
    {P : Def6.Consts} {m₁ : ℕ} {ϱ : ℝ} (H : NewLevelTies d N L P m₁ ϱ) :
    NewLevelTies d N L' P m₁ ϱ := by
  subst h; exact H

/-- **The chain's separation is below the minimal separation at one cube exponent, uniformly in
the block exponent**: `rhoSepG d L m₁ ≤ L^{m₁} C(d, L)`, so one exponent `s` with
`5 L^{s+1} ≥ C(d, L)` serves every `m₁`. -/
theorem exists_rhoSepG_le_minSep {d L : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ s₀ : ℕ, ∀ m₁ : ℕ, rhoSepG d L m₁ ≤ LargeField.minSep L (L ^ (m₁ + s₀)) := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  set C : ℝ := bgR0 d L + 4 * d * L + 4 * d * (L : ℝ) ^ 3 + 1 +
    2 * d * Real.log L / (agmonRate d / 16) with hC
  obtain ⟨s₀, hs₀⟩ := pow_unbounded_of_one_lt C hL1
  refine ⟨s₀, fun m₁ => ?_⟩
  have ht := rhoSepG_tail_nonneg (d := d) hd hL
  have hb := bgR0_nonneg_G (d := d) (L := L)
  have hLm : (1 : ℝ) ≤ (L : ℝ) ^ m₁ := one_le_pow₀ hL1.le
  have hrho : rhoSepG d L m₁ ≤ C * (L : ℝ) ^ m₁ := by
    unfold rhoSepG
    rw [hC]
    have h1 : bgR0 d L ≤ bgR0 d L * (L : ℝ) ^ m₁ := le_mul_of_one_le_right hb hLm
    have h2 : (1 : ℝ) ≤ 1 * (L : ℝ) ^ m₁ := by linarith
    have h3 : 2 * (d : ℝ) * Real.log L / (agmonRate d / 16) ≤
        2 * (d : ℝ) * Real.log L / (agmonRate d / 16) * (L : ℝ) ^ m₁ :=
      le_mul_of_one_le_right ht hLm
    nlinarith
  unfold LargeField.minSep
  push_cast
  have hLs : (L : ℝ) ^ (m₁ + s₀) = (L : ℝ) ^ m₁ * (L : ℝ) ^ s₀ := pow_add _ _ _
  rw [hLs]
  have h0 : (0 : ℝ) ≤ (L : ℝ) ^ m₁ := by positivity
  have h5 : (L : ℝ) ^ s₀ ≤ 5 * (L : ℝ) * (L : ℝ) ^ s₀ := by
    have : (0 : ℝ) ≤ (L : ℝ) ^ s₀ := by positivity
    nlinarith
  calc rhoSepG d L m₁ ≤ C * (L : ℝ) ^ m₁ := hrho
    _ ≤ (L : ℝ) ^ s₀ * (L : ℝ) ^ m₁ := mul_le_mul_of_nonneg_right hs₀.le h0
    _ ≤ 5 * (L : ℝ) * ((L : ℝ) ^ m₁ * (L : ℝ) ^ s₀) := by nlinarith

/-- **The cube exponent of the chain's separation is bounded uniformly in the block exponent**
(`exists_rhoSepG_le_minSep`). -/
theorem exists_hatScale_bound {d L : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ s₀ : ℕ, ∀ m₁ : ℕ, hatScale L m₁ (rhoSepG d L m₁) ≤ s₀ := by
  obtain ⟨s₀, hs₀⟩ := exists_rhoSepG_le_minSep hd hL
  exact ⟨s₀, fun m₁ => hatScale_le (hs₀ m₁)⟩

/-- `exp x - 1 ≤ 2 x` for `0 ≤ x ≤ 1`. -/
theorem exp_sub_one_le_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Real.exp x - 1 ≤ 2 * x := by
  have h := Real.abs_exp_sub_one_le (x := x) (by rw [abs_of_nonneg hx0]; exact hx1)
  rw [abs_of_nonneg hx0] at h
  exact (le_abs_self _).trans h

/-- **The block sizes of the new level exist**: for every `d ≥ 3` and `0 < δ < 1/2` there is
`L ≥ 3` with `L^{-((d-2)/2 - γ)} ≤ 1/16`, `γ = (1 + 2δ)/4`. -/
theorem exists_large_L {d : ℕ} (hd : 3 ≤ d) {δ : ℝ} (hδ' : δ < 1 / 2) :
    ∃ L : ℕ, 3 ≤ L ∧ (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - (1 + 2 * δ) / 4)) ≤ 1 / 16 := by
  set α : ℝ := ((d : ℝ) - 2) / 2 - (1 + 2 * δ) / 4 with hα
  have h3d : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hα0 : 0 < α := by rw [hα]; linarith
  refine ⟨⌈(16 : ℝ) ^ (1 / α)⌉₊ + 3, by omega, ?_⟩
  have h16 : (0 : ℝ) < (16 : ℝ) ^ (1 / α) := by positivity
  have hle : (16 : ℝ) ^ (1 / α) ≤ ((⌈(16 : ℝ) ^ (1 / α)⌉₊ + 3 : ℕ) : ℝ) := by
    push_cast
    have := Nat.le_ceil ((16 : ℝ) ^ (1 / α))
    linarith
  have h1 : ((16 : ℝ) ^ (1 / α)) ^ α = 16 := by
    rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hα0.ne', Real.rpow_one]
  have h2 : (16 : ℝ) ≤ (((⌈(16 : ℝ) ^ (1 / α)⌉₊ + 3 : ℕ) : ℝ)) ^ α :=
    calc (16 : ℝ) = ((16 : ℝ) ^ (1 / α)) ^ α := h1.symm
      _ ≤ _ := Real.rpow_le_rpow h16.le hle hα0.le
  rw [Real.rpow_neg (by positivity)]
  have h0 : (0 : ℝ) < (((⌈(16 : ℝ) ^ (1 / α)⌉₊ + 3 : ℕ) : ℝ)) ^ α := by positivity
  rw [inv_le_comm₀ h0 (by norm_num)]
  linarith

/-- **Core of `prefixInput_newLevelTies_exists`, with the gap `R₀(d, L) < L^{m₀-3}` of the cell
exponent, the block size `L` of the typing, the choice `M₁ = L^{m₀+m₁-3}`, `c = L³` and the room
`hatScale + 3 ≤ m₀` of the cube exponent exposed**: `PrefixInput` and the ties of the new level hold together (hard rule 10 for
`NewLevelTiesInput`): for `d ≥ 3`, `N ≥ 2`, `0 < δ < 1/2` and every block size `L ≥ 3` with
`L^{-((d-2)/2 - γ)} ≤ 1/16`, `γ = (1 + 2δ)/4` (`exists_large_L`), the witness of
`prefixInput_exists_of` with the cell exponent `m₀` large (`m₀ ≥ d`, above the cube exponent and with
the margin of the local sets), the base tower of `exists_collarBase_newLevel` at `m₀` (`m₁` its block
exponent, `ϱ = rhoSepG d L m₁`), the radius constant `α₀` and the flow constant `c₈` small satisfies
`PrefixInput` and `NewLevelTiesInput`. -/
theorem prefixInput_newLevelTies_exists_gap (d N L : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N) (hL : 3 ≤ L)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hLq : (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - (1 + 2 * δ) / 4)) ≤ 1 / 16) :
    ∃ (Ty : ℝ → ℝ → LargeField.Typing) (P6 : ℝ → ℝ → Def6.Consts) (C7 : ℝ → ℝ → Consts7)
      (PB : ℝ → ℝ → LargeField.BudgetConsts) (cs₀ : ℝ → ℝ → LargeField.OpConsts)
      (M1 c : ℝ → ℝ → ℕ) (ϱ : ℝ → ℝ → ℝ),
      PrefixInput d δ Ty P6 C7 PB cs₀ M1 c ϱ ∧ NewLevelTiesInput d N Ty P6 C7 ϱ ∧
        ∀ κ c₉ : ℝ, (Ty κ c₉).L = L ∧ bgR0 d L < (L : ℝ) ^ ((P6 κ c₉).m₀ - 3) ∧
          M1 κ c₉ = L ^ ((P6 κ c₉).m₀ + (C7 κ c₉).m₁ - 3) ∧ c κ c₉ = L ^ 3 ∧
          hatScale L (C7 κ c₉).m₁ (ϱ κ c₉) + 3 ≤ (P6 κ c₉).m₀ := by
  have : NeZero L := ⟨by omega⟩
  have hd0 : 0 < d := by omega
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have h3d : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set γ : ℝ := (1 + 2 * δ) / 4 with hγ
  set q : ℝ := (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by linarith) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL1 (by rw [hγ]; linarith)
  -- the cube exponent and the cell exponent
  obtain ⟨s₀, hs₀⟩ := exists_hatScale_bound hd hL
  obtain ⟨n₁, hn₁⟩ := pow_unbounded_of_one_lt (bgR0 d L) hL1
  obtain ⟨n₂, hn₂⟩ := pow_unbounded_of_one_lt
    ((((5 * L + 13) * L ^ s₀ : ℕ) : ℝ) + (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) * L) hL1
  set m₀ : ℕ := d + s₀ + 3 + n₁ + n₂ with hm₀
  -- the base tower
  obtain ⟨κmin, T₀, κdec, hT, hQ16, hNLN⟩ :=
    exists_collarBase_newLevel d L N hd hL hN m₀ hq0 hq1 (θ := 1 / 16) (by norm_num)
  set m₁ : ℕ := T₀.m₁ with hm₁
  -- the radius constant
  have hX := one_le_xiC1 d
  have hC1 : 0 < bgC1 d L N := bgC1_pos' hd0
  have hK2 := cK2_pos d L N
  have hDs : 0 < deltaStar d L N := deltaStar_pos d L N hd0
  have hK1 := bgK1_pos d L N
  have hT0 := T₀.t_pos
  have hτl := epsTail_pos 1
  set e : ℝ := min (min (1 / ((4 * d + 6) * (2 * d + 1))) (bgC1 d L N / (4 * xiC1 d)))
    (min (1 / (8 * ((N : ℝ) + 1) * cK2 d L N)) (min (deltaStar d L N / (2 * (bgK1 d L N * xiC1 d)))
      (min (2 * deltaStar d L N) (16 / 17 * T₀.t)))) with he
  have he0 : 0 < e := by
    rw [he]
    refine lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  have he1 : e ≤ 1 / ((4 * d + 6) * (2 * d + 1)) := (min_le_left _ _).trans (min_le_left _ _)
  have he2 : e ≤ bgC1 d L N / (4 * xiC1 d) := (min_le_left _ _).trans (min_le_right _ _)
  have he3 : e ≤ 1 / (8 * ((N : ℝ) + 1) * cK2 d L N) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have he4 : e ≤ deltaStar d L N / (2 * (bgK1 d L N * xiC1 d)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have he5 : e ≤ 2 * deltaStar d L N :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have he6 : e ≤ 16 / 17 * T₀.t :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  set α₀ : ℝ := e / epsTail 1 with hα₀
  have hα₀0 : 0 < α₀ := div_pos he0 hτl
  have heps : epsSeq L (((d : ℝ) - 2) / 2 - γ) α₀ 1 = e * q := by
    show e / epsTail 1 * epsTail 1 * ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ))) ^ 1 = e * q
    rw [pow_one, div_mul_cancel₀ _ hτl.ne']
  set ε : ℝ := e * q with hε
  have hε0 : 0 < ε := mul_pos he0 hq0
  have hεe : ε ≤ e := mul_le_of_le_one_right he0.le hq1.le
  -- the flow constant and the radius of the mass response
  set rm : ℝ := min (1 / 16) (deltaStar d L N / 6) with hrm
  have hrm0 : 0 < rm := lt_min (by norm_num) (by positivity)
  set τs : ℝ := min (1 / 14) (min (1 / (18 * (1 + 16 * ((N : ℝ) + 1) * cK2 d L N))) (rm / 4))
    with hτs
  have hτs0 : 0 < τs := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hτs1 : τs ≤ 1 / 14 := min_le_left _ _
  have hτs2 : τs ≤ 1 / (18 * (1 + 16 * ((N : ℝ) + 1) * cK2 d L N)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hτs3 : τs ≤ rm / 4 := (min_le_right _ _).trans (min_le_right _ _)
  set qf : ℝ := Flow.rate (L : ℝ) γ with hqf
  have hqf0 : 0 < qf := Flow.rate_pos (by linarith) _
  have hqf1 : qf < 1 := Flow.rate_lt_one hL1 (by rw [hγ]; linarith)
  set c₈ : ℝ := min ((1 - qf) / (20 * qf)) (2 / 3 * τs * (1 - qf) / qf ^ 2) with hc₈
  have hc₈0 : 0 < c₈ := lt_min (div_pos (by linarith) (by positivity))
    (div_pos (mul_pos (by positivity) (by linarith)) (by positivity))
  have hc₈q : c₈ * qf ≤ 1 / 20 * (1 - qf) :=
    calc c₈ * qf ≤ (1 - qf) / (20 * qf) * qf :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hqf0.le
      _ = 1 / 20 * (1 - qf) := by field_simp
  set x : ℝ := 3 * (c₈ / 4 * (qf ^ 2 / (1 - qf))) with hx
  have hx0 : 0 ≤ x := by positivity
  have hxτ : x ≤ τs / 2 := by
    have h1q : 0 < 1 - qf := by linarith only [hqf1]
    have hA : 0 ≤ qf ^ 2 / (1 - qf) := by positivity
    have e1 : 3 * (2 / 3 * τs * (1 - qf) / qf ^ 2 / 4 * (qf ^ 2 / (1 - qf))) = τs / 2 := by
      field_simp; ring
    calc x = 3 * (c₈ / 4 * (qf ^ 2 / (1 - qf))) := hx
      _ ≤ 3 * (2 / 3 * τs * (1 - qf) / qf ^ 2 / 4 * (qf ^ 2 / (1 - qf))) := by
          gcongr
          exact min_le_right _ _
      _ = τs / 2 := e1
  have hτ : Real.exp x - 1 ≤ τs := (exp_sub_one_le_two_mul hx0
    (by linarith only [hxτ, hτs1])).trans (by linarith only [hxτ])
  -- the prefix
  have hm : 3 ≤ m₀ + m₁ := by omega
  have hsep : bgR0 d L ≤ LargeField.minSep L (L ^ (m₀ + m₁ - 3)) := by
    unfold LargeField.minSep
    push_cast
    have h1 : (L : ℝ) ^ n₁ ≤ (L : ℝ) ^ (m₀ + m₁ - 3) := pow_le_pow_right₀ hL1.le (by omega)
    have h2 : (0 : ℝ) ≤ (L : ℝ) ^ (m₀ + m₁ - 3) := by positivity
    have h3 : (L : ℝ) ^ (m₀ + m₁ - 3) ≤ 5 * (L : ℝ) * (L : ℝ) ^ (m₀ + m₁ - 3) := by
      have h4 : (1 : ℝ) ≤ 5 * L := by linarith only [hL1]
      calc (L : ℝ) ^ (m₀ + m₁ - 3) = 1 * (L : ℝ) ^ (m₀ + m₁ - 3) := (one_mul _).symm
        _ ≤ 5 * (L : ℝ) * (L : ℝ) ^ (m₀ + m₁ - 3) := mul_le_mul_of_nonneg_right h4 h2
    linarith only [hn₁, h1, h3]
  have hϱ : bgR0 d L ≤ rhoSepG d L m₁ := bgR0_le_rhoSepG m₁ hd hL
  obtain ⟨Ty, P6, C7, PB, cs₀, M1, c, ϱ, hPre, hid⟩ := prefixInput_exists_of_pow d L hd hL hδ hδ'
    hα₀0 hc₈0 hc₈q hm hsep hϱ
  refine ⟨Ty, P6, C7, PB, cs₀, M1, c, ϱ, hPre, fun κ _ c₉ _ _ => ?_, fun κ c₉ => ?_⟩
  rotate_left
  · obtain ⟨hTL, -, -, -, hm0', hm1', hϱ', hM1', hc'⟩ := hid κ c₉
    refine ⟨hTL, ?_, by rw [hM1', hm0', hm1'], hc', ?_⟩
    swap
    · rw [hm0', hm1', hϱ']
      have := hs₀ m₁
      omega
    rw [hm0']
    have h1 : (L : ℝ) ^ n₁ ≤ (L : ℝ) ^ (m₀ - 3) := pow_le_pow_right₀ hL1.le (by omega)
    linarith only [hn₁, h1]
  obtain ⟨hTL, hγ', hα', hc', hm0', hm1', hϱ', -, -⟩ := hid κ c₉
  refine NewLevelTies.congr_L hTL.symm ?_
  have hPε : (P6 κ c₉).eps d L 1 = ε := by
    unfold Consts.eps Consts.alpha
    rw [hγ', hα']
    exact heps
  have hPτ : Real.exp (3 * ((P6 κ c₉).c₈ / 4 * (Flow.rate (L : ℝ) (P6 κ c₉).γ ^ 2 /
      (1 - Flow.rate (L : ℝ) (P6 κ c₉).γ)))) - 1 = Real.exp x - 1 := by
    rw [hc', hγ']
  rw [hm1', hϱ']
  have hhat := hs₀ m₁
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hγ']; exact hLq
  · refine ⟨κmin, T₀, κdec, ?_, hQ16, hNLN, rfl, ?_⟩
    · rw [hm0', hγ']; exact hT
    · rw [hPε]; linarith only [hεe, he6]
  · rw [hm0']; omega
  · rw [hm0']; omega
  · -- the margin of the local sets
    rw [hm0']
    set s := hatScale L m₁ (rhoSepG d L m₁) with hs
    have hLs : (L : ℝ) ^ s ≤ (L : ℝ) ^ s₀ := pow_le_pow_right₀ hL1.le hhat
    have hLn : (L : ℝ) ^ n₂ ≤ (L : ℝ) ^ m₀ := pow_le_pow_right₀ hL1.le (by omega)
    have hdiv : ((L / 2 : ℕ) : ℝ) ≤ (L : ℝ) / 2 := Nat.cast_div_le
    have hsub : ((L - 2 : ℕ) : ℝ) = (L : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
    push_cast
    rw [hsub]
    have hLm0 : (0 : ℝ) ≤ (L : ℝ) ^ m₀ := by positivity
    have hn₂' : ((5 * (L : ℝ) + 13) * (L : ℝ) ^ s₀) + (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) * L <
        (L : ℝ) ^ n₂ := by exact_mod_cast hn₂
    have hpow : (L : ℝ) ^ (m₀ + 1) = (L : ℝ) ^ m₀ * L := pow_succ _ _
    rw [hpow]
    have h5 : (5 * (L : ℝ) + 13) * (L : ℝ) ^ s ≤ (5 * (L : ℝ) + 13) * (L : ℝ) ^ s₀ :=
      mul_le_mul_of_nonneg_left hLs (by positivity)
    have h6 : ((L / 2 : ℕ) : ℝ) * (L : ℝ) ^ m₀ ≤ (L : ℝ) / 2 * (L : ℝ) ^ m₀ :=
      mul_le_mul_of_nonneg_right hdiv hLm0
    have h7 : ((L : ℝ) / 2 + 1) * (L : ℝ) ^ m₀ ≤ ((L : ℝ) - 2) * ((L : ℝ) ^ m₀ * L) := by
      have h8 : (L : ℝ) / 2 + 1 ≤ ((L : ℝ) - 2) * L := by nlinarith only [hLr]
      calc ((L : ℝ) / 2 + 1) * (L : ℝ) ^ m₀ ≤ ((L : ℝ) - 2) * L * (L : ℝ) ^ m₀ :=
            mul_le_mul_of_nonneg_right h8 hLm0
        _ = ((L : ℝ) - 2) * ((L : ℝ) ^ m₀ * L) := by ring
    linarith only [h5, h6, h7, hn₂', hLn]
  · rw [hPε]
    have hp : (0 : ℝ) < (4 * d + 6) * (2 * d + 1) := by positivity
    calc (4 * (d : ℝ) + 6) * ((2 * d + 1) * ε) = (4 * d + 6) * (2 * d + 1) * ε := by ring
      _ ≤ (4 * d + 6) * (2 * d + 1) * (1 / ((4 * d + 6) * (2 * d + 1))) :=
          mul_le_mul_of_nonneg_left (hεe.trans he1) hp.le
      _ = 1 := by field_simp
  · rw [hPε]
    have hp : (0 : ℝ) < 4 * xiC1 d := by linarith only [hX]
    calc 4 * (xiC1 d * ε) = 4 * xiC1 d * ε := by ring
      _ ≤ 4 * xiC1 d * (bgC1 d L N / (4 * xiC1 d)) :=
          mul_le_mul_of_nonneg_left (hεe.trans he2) hp.le
      _ = bgC1 d L N := by field_simp
  · rw [hPε]
    have hp : (0 : ℝ) < ((N : ℝ) + 1) * cK2 d L N := by positivity
    calc ((N : ℝ) + 1) * cK2 d L N * ε ≤ ((N : ℝ) + 1) * cK2 d L N *
          (1 / (8 * ((N : ℝ) + 1) * cK2 d L N)) := mul_le_mul_of_nonneg_left (hεe.trans he3) hp.le
      _ = 1 / 8 := by field_simp
  · rw [hPτ]; linarith only [hτ, hτs1]
  · rw [hPτ]
    have hKm : 0 < 1 + 16 * ((N : ℝ) + 1) * cK2 d L N := by positivity
    calc (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * (2 * (Real.exp x - 1)) ≤
          (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) *
            (2 * (1 / (18 * (1 + 16 * ((N : ℝ) + 1) * cK2 d L N)))) :=
          mul_le_mul_of_nonneg_left (by linarith only [hτ, hτs2]) hKm.le
      _ = 1 / 9 := by field_simp; norm_num
  · rw [hc', hγ']; linarith only [hc₈q, hqf1]
  · refine ⟨rm, ?_, min_le_left _ _, ?_, ?_⟩
    · rw [hPτ]; linarith only [hτ, hτs3, hrm0]
    · rw [hPε]
      have h1 : bgK1 d L N * (xiC1 d * ε) ≤ deltaStar d L N / 2 := by
        have hp : (0 : ℝ) < bgK1 d L N * xiC1 d := mul_pos hK1 (by linarith only [hX])
        calc bgK1 d L N * (xiC1 d * ε) = bgK1 d L N * xiC1 d * ε := by ring
          _ ≤ bgK1 d L N * xiC1 d * (deltaStar d L N / (2 * (bgK1 d L N * xiC1 d))) :=
              mul_le_mul_of_nonneg_left (hεe.trans he4) hp.le
          _ = deltaStar d L N / 2 := by field_simp
      have h2 : rm ≤ deltaStar d L N / 6 := min_le_right _ _
      linarith only [h1, h2]
    · rw [hPε]
      have h2 : rm ≤ 1 / 16 := min_le_left _ _
      have h3 : 8 * ε * rm ≤ 8 * ε * (1 / 16) := mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith only [h3, hεe, he5]

/-- **`PrefixInput` and the ties of the new level hold together** (hard rule 10 for
`NewLevelTiesInput`): for `d ≥ 3`, `N ≥ 2`, `0 < δ < 1/2` and every block size `L ≥ 3` with
`L^{-((d-2)/2 - γ)} ≤ 1/16`, `γ = (1 + 2δ)/4` (`exists_large_L`), the witness of
`prefixInput_exists_of` with the cell exponent `m₀` large (`m₀ ≥ d`, above the cube exponent and with
the margin of the local sets), the base tower of `exists_collarBase_newLevel` at `m₀` (`m₁` its block
exponent, `ϱ = rhoSepG d L m₁`), the radius constant `α₀` and the flow constant `c₈` small satisfies
`PrefixInput` and `NewLevelTiesInput`. -/
theorem prefixInput_newLevelTies_exists (d N L : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N) (hL : 3 ≤ L)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hLq : (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - (1 + 2 * δ) / 4)) ≤ 1 / 16) :
    ∃ (Ty : ℝ → ℝ → LargeField.Typing) (P6 : ℝ → ℝ → Def6.Consts) (C7 : ℝ → ℝ → Consts7)
      (PB : ℝ → ℝ → LargeField.BudgetConsts) (cs₀ : ℝ → ℝ → LargeField.OpConsts)
      (M1 c : ℝ → ℝ → ℕ) (ϱ : ℝ → ℝ → ℝ),
      PrefixInput d δ Ty P6 C7 PB cs₀ M1 c ϱ ∧ NewLevelTiesInput d N Ty P6 C7 ϱ := by
  obtain ⟨Ty, P6, C7, PB, cs₀, M1, c, ϱ, hPre, hNL, -⟩ :=
    prefixInput_newLevelTies_exists_gap d N L hd hN hL hδ hδ' hLq
  exact ⟨Ty, P6, C7, PB, cs₀, M1, c, ϱ, hPre, hNL⟩

end Balaban.RootFSpine
