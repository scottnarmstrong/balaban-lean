/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.LocalGeneratorRadius
public import Balaban.SmallField.LocalGeneratorClassDomain
public import Balaban.SmallField.GsSpecClass
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The radius of the local successor class

The local class of SF3TYPE option (a) has the term generators `𝔹_j(X) = localB j hj X hsep` at
the low index `R₀(d, L)` and its domain is `Ξ^c_j(𝔹_j(X); 1, ε_j)`.  Three facts decide its radius
sequence.

* **The loss of the restriction route cannot be put on the successor alone.**  The inclusion of
  the whole-level chart in the local chart (`localB_xiDom_massless_linear`) multiplies the radius by
  `K = (2 K₁ + 2) C₁`.  Lemma 4.2 of P3 (printed p. 77, condition (4.37)) needs
  `ε' + (K₂ + 1) δ₃ ≤ ε_k` for the radius `ε'` of the new chart and the radius `ε_k` of the input
  terms.  With `ε' = K ε_{k+1}` and the input at `ε_k` this fails for the class sequence of P4 (H.1):
  `ε_k ≤ 2 L^α ε_{k+1}` (`epsSeq_le_two_rpow_mul_succ`) and `2 L^α < K` when `α ≤ 2`
  (`two_rpow_lt_localLoss`), so `K ε_{k+1} + δ > ε_k` (`not_localLoss_eps_succ_le`).
* **The chart test of the landed expansion has the same defect for every class**
  (`not_chartTest_eps_succ`): `C₀² (C₀² ε + δ) ≤ ε_k` with `ε ≥ ε_{k+1}` needs `C₀⁴ ≤ 2 L^α`,
  false at `d = L = 3` (`C₀ = 36`).
* **A local term is analytic at every pair that agrees on `X` with a point of its domain**
  (`SFTermClauses.analyticAt_E_of_agreeOn`, `SFTermClauses.analyticAt_M_of_agreeOn`): the clause
  `localE` makes the term invariant under the translation by the difference of the two pairs.  So
  the whole-level composed pair, which agrees on `X` with the local composed pair of `𝔹_j(X)`
  (`GsSpec.localPairAt_agree`), needs no inclusion of charts
  (`SFTermClausesStrong.analyticAt_E_composedPairAt`).
* `xiC_mono_sigma`: `Ξ^c_n(𝔹; σ, ε) ⊆ Ξ^c_n(𝔹; σ', ε)` for `σ ≤ σ'`, the first piece of a
  composition chain without radius loss (P3 (4.29)).
* **The chart of the expansion maps into the local class domain at the same radius test as for a
  whole-level generator** (`xiCRaw_localB_sub_xiFieldDom`): `C₀² ε ≤ ε_j`, `C₀ = scaledC0 d`.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Multiscale Balaban.Background

/-! ### Monotonicity of the charts in the scale parameter `σ`

The first piece of the composition without radius loss of P3 (4.29): every bound of
`XiBounds`/`XiCBounds` increases with `σ` (`σ ε`, `σ² ε`, `(σ ε)²`, `(σ ε)² / ε`; `val` does not
involve `σ`), so `Ξ^c_n(𝔹; σ, ε) ⊆ Ξ^c_n(𝔹; σ', ε)` for `0 < σ ≤ σ'`.  With a composition at the
scale `σ_j = c L^{j-K} ≤ 1` this gives `Ξ^c_j(𝔹_j; 1, ε)` at the same radius. -/

section SigmaMono

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}

theorem xiBounds_mono_sigma {ν σ σ' ε : ℝ} {n : ℕ} {D : BgData G N} {h₀ : Fin N → ℝ}
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hσ : 0 ≤ σ) (hσσ : σ ≤ σ') (hε0 : 0 ≤ ε)
    (hb : XiBounds G ν n σ ε D h₀ φ α) : XiBounds G ν n σ' ε D h₀ φ α := by
  have h1 : σ * ε ≤ σ' * ε := mul_le_mul_of_nonneg_right hσσ hε0
  have h2 : σ ^ 2 * ε ≤ σ' ^ 2 * ε :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hσ hσσ 2) hε0
  have hp : ∀ x : Torus d (N₀ * L ^ k), 0 < G.spacing x := fun x => by
    have := G.spacing_ge_one x; linarith
  refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x => ?_, fun x hx => ?_,
    fun z hz z' hz' hadj => ?_, fun z => ?_, ?_⟩
  · obtain ⟨g1, g2⟩ := hb.grad x hx μ
    exact ⟨g1.trans_le (div_le_div_of_nonneg_right h1 (hp x).le),
      g2.trans_le (div_le_div_of_nonneg_right h1 (hp x).le)⟩
  · exact (hb.lap x hx).trans_le (div_le_div_of_nonneg_right h2 (by have := hp x; positivity))
  · exact (hb.mult x).trans_le h2
  · exact (hb.close x hx).trans_le h2
  · exact (hb.collarBond z hz z' hz' hadj).trans_le h1
  · exact (hb.mass z).trans_le h1
  · exact hb.hnorm.trans_le (pow_le_pow_left₀ (mul_nonneg hσ hε0) h1 2)

theorem xiCBounds_mono_sigma {ν σ σ' ε : ℝ} {Dr Dc : BgData G N}
    {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φr φc : G.Ω 1 × Fin N → ℂ}
    {αr αc : G.Ω 1 → ℂ} (hσ : 0 ≤ σ) (hσσ : σ ≤ σ') (hε0 : 0 < ε)
    (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc) :
    XiCBounds G ν σ' ε Dr Dc Ψ'' h'' φr φc αr αc := by
  have h1 : σ * ε ≤ σ' * ε := mul_le_mul_of_nonneg_right hσσ hε0.le
  have h2 : σ ^ 2 * ε ≤ σ' ^ 2 * ε :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hσ hσσ 2) hε0.le
  have hp : ∀ x : Torus d (N₀ * L ^ k), 0 < G.spacing x := fun x => by
    have := G.spacing_ge_one x; linarith
  have e : ∀ t : ℝ, (t * ε) ^ 2 / ε = t ^ 2 * ε := fun t => by field_simp
  refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x => ?_, fun x => ?_, fun x hx => ?_,
    fun z hz z' hz' hadj => ?_, fun x hx => ?_, fun x => ?_⟩
  · obtain ⟨g1, g2⟩ := hb.grad x hx μ
    exact ⟨g1.trans_le (div_le_div_of_nonneg_right h1 (hp x).le),
      g2.trans_le (div_le_div_of_nonneg_right h1 (hp x).le)⟩
  · exact (hb.lap x hx).trans_le (div_le_div_of_nonneg_right h2 (by have := hp x; positivity))
  · exact (hb.mult x).trans_le h2
  · exact hb.val x
  · exact (hb.close x hx).trans_le h2
  · exact (hb.collarBond z hz z' hz' hadj).trans_le h1
  · have := hb.hAbs x hx
    rw [e σ] at this
    rw [e σ']
    exact this.trans_le h2
  · exact (hb.hDot x).trans_le (pow_le_pow_left₀ (mul_nonneg hσ hε0.le) h1 2)

/-- **`Ξ^c_n(𝔹; σ, ε) ⊆ Ξ^c_n(𝔹; σ', ε)` for `σ ≤ σ'`.** -/
theorem xiC_mono_sigma {a : ℕ → ℝ} {ν σ σ' ε : ℝ} {n : ℕ}
    {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hσσ : σ ≤ σ')
    (h : XiC G a ν n σ ε Ψ₀ h₀ Ψ'' h'') : XiC G a ν n σ' ε Ψ₀ h₀ Ψ'' h'' := by
  obtain ⟨hσ, hε0, Dr, Dc, hXr, hC, hU, hb⟩ := h
  exact ⟨hσ.trans_le hσσ, hε0, Dr, Dc,
    ⟨hXr.1, hXr.2.1, xiBounds_mono_sigma hσ.le hσσ hε0.le hXr.2.2⟩, hC, hU,
    xiCBounds_mono_sigma hσ.le hσσ hε0 hb⟩

end SigmaMono

end Balaban.SmallField

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation

/-! ### The class sequence against the loss of the restriction route -/

section Radius

/-- `1 + ∑_{m ≥ k} m^{-2} ≤ 1 + ∑_{m ≥ k+1} m^{-2} + 1`: the tails of P4 (H.1) differ by
`k^{-2} ≤ 1`. -/
theorem epsTail_le_succ_add_one (k : ℕ) : epsTail k ≤ epsTail (k + 1) + 1 := by
  unfold epsTail
  have hle : ∀ m : ℕ, (if k ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0) ≤
      (if k + 1 ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0) + (if m = k then (1 : ℝ) else 0) := by
    intro m
    by_cases hmk : m = k
    · subst hmk
      have h1 : ((m : ℝ) ^ 2)⁻¹ ≤ 1 := by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · subst h0; simp
        · have : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hpos)
          exact inv_le_one_of_one_le₀ this
      simp only [le_refl, ↓reduceIte, Nat.not_succ_le_self, zero_add]
      exact h1
    · simp only [hmk, ↓reduceIte, add_zero]
      by_cases h : k + 1 ≤ m
      · have : k ≤ m := by omega
        simp [h, this]
      · have : ¬ k ≤ m := by omega
        simp [h, this]
  have hs1 := summable_epsTail (k + 1)
  have hs2 : Summable fun m : ℕ => (if m = k then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {k}) fun m hm => by
      simp only [Finset.mem_singleton] at hm
      simp [hm]
  have h := Summable.tsum_le_tsum hle (summable_epsTail k) (hs1.add hs2)
  rw [hs1.tsum_add hs2, tsum_ite_eq] at h
  linarith

/-- **The class sequence decreases by at most `2 L^α` per level**: `ε_k ≤ 2 L^α ε_{k+1}` for
`ε_j = α₀ (1 + ∑_{m ≥ j} m^{-2}) L^{-jα}` (P4 (H.1)). -/
theorem epsSeq_le_two_rpow_mul_succ (L : ℕ) [NeZero L] (α α₀ : ℝ) (hα₀ : 0 ≤ α₀) (k : ℕ) :
    epsSeq L α α₀ k ≤ 2 * (L : ℝ) ^ α * epsSeq L α α₀ (k + 1) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hq : 0 < (L : ℝ) ^ (-α) := Real.rpow_pos_of_pos hL _
  have hqq : (L : ℝ) ^ α * (L : ℝ) ^ (-α) = 1 := by
    rw [← Real.rpow_add hL]; simp
  have hT := epsTail_le_succ_add_one k
  have hT1 : 1 ≤ epsTail (k + 1) := by
    unfold epsTail
    have : 0 ≤ ∑' m : ℕ, if k + 1 ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0 :=
      tsum_nonneg fun m => by split_ifs <;> positivity
    linarith
  have hqk : 0 ≤ ((L : ℝ) ^ (-α)) ^ k := by positivity
  unfold epsSeq
  rw [pow_succ]
  have e : 2 * (L : ℝ) ^ α * (α₀ * epsTail (k + 1) * (((L : ℝ) ^ (-α)) ^ k * (L : ℝ) ^ (-α))) =
      2 * α₀ * epsTail (k + 1) * ((L : ℝ) ^ (-α)) ^ k * ((L : ℝ) ^ α * (L : ℝ) ^ (-α)) := by
    ring
  rw [e, hqq, mul_one]
  have h2 : epsTail k ≤ 2 * epsTail (k + 1) := by linarith
  have := mul_le_mul_of_nonneg_left h2 (mul_nonneg hα₀ hqk)
  nlinarith [this]

/-- **The loss constant of the restriction route exceeds `2 L^α` for `α ≤ 2`**: with
`K = (2 K₁ + 2) C₁` (`localB_xiDom_massless_linear`), `K₁ = bgK1 ≥ 500 · 2 d L²`. -/
theorem two_rpow_lt_localLoss {d L N : ℕ} [NeZero L] (hd : 1 ≤ d) (hL : 1 ≤ L) {α : ℝ}
    (hα : α ≤ 2) : 2 * (L : ℝ) ^ α < (2 * bgK1 d L N + 2) * xiC1 d := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow : (L : ℝ) ^ α ≤ (L : ℝ) ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hL1 hα
    simpa [Real.rpow_two] using this
  have hC : 500 ≤ lemma53Const d L := by
    have h1 := cB7_le_const d L
    have h2 := cB7_pos d L
    linarith
  have hK2 := cK2_pos d L N
  have hK1 : 1000 * (L : ℝ) ^ 2 ≤ bgK1 d L N := by
    unfold bgK1
    have hN0 : (0 : ℝ) ≤ (2 * N + 1) * cK2 d L N := by positivity
    have hin : 2 * (L : ℝ) ^ 2 ≤ 1 + L + 2 * d * (L : ℝ) ^ 2 + (2 * N + 1) * cK2 d L N := by
      nlinarith [sq_nonneg (L : ℝ)]
    have hpos : (0 : ℝ) ≤ 2 * (L : ℝ) ^ 2 := by positivity
    calc 1000 * (L : ℝ) ^ 2 = 500 * (2 * (L : ℝ) ^ 2) := by ring
      _ ≤ lemma53Const d L * (2 * (L : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hC hpos
      _ ≤ _ := mul_le_mul_of_nonneg_left hin (by linarith)
  have hx := one_le_xiC1 d
  have hL2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ hL1
  have hpos : 0 ≤ 2 * bgK1 d L N + 2 := by linarith
  have h1 : 2 * bgK1 d L N + 2 ≤ (2 * bgK1 d L N + 2) * xiC1 d := by nlinarith
  linarith

/-- **No constant above `2 L^α` fits between two consecutive class radii**: for the class
sequence (`α₀ > 0`), every level `k`, every `δ ≥ 0` and every `K' > 2 L^α`,
`K' ε_{k+1} + δ ≤ ε_k` is false. -/
theorem not_mul_eps_succ_add_le {d L : ℕ} [NeZero L] (P : Consts) (hα₀ : 0 < P.α₀) {K' : ℝ}
    (hK : 2 * (L : ℝ) ^ P.alpha d < K') (k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ¬ (K' * P.eps d L (k + 1) + δ ≤ P.eps d L k) := by
  intro h
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hpos : 0 < P.eps d L (k + 1) := by
    unfold Consts.eps epsSeq
    have := epsTail_pos (k + 1)
    have : 0 < (L : ℝ) ^ (-P.alpha d) := Real.rpow_pos_of_pos hLpos _
    positivity
  have h1 := epsSeq_le_two_rpow_mul_succ L (P.alpha d) P.α₀ hα₀.le k
  have h3 : 2 * (L : ℝ) ^ P.alpha d * P.eps d L (k + 1) < K' * P.eps d L (k + 1) :=
    mul_lt_mul_of_pos_right hK hpos
  unfold Consts.eps at h h3 hpos
  linarith

/-- **The successor cannot carry the loss of the restriction route over an input at the class
radius**: for the class sequence (`α₀ > 0`, `α ≤ 2`, e.g. `d ≤ 6`), every level `k` and every
`δ ≥ 0`, `K ε_{k+1} + δ ≤ ε_k` is false, `K = (2 K₁ + 2) C₁`.  This is condition (4.37) of P3
(printed p. 77; `ε' + (K₂ + 1) δ₃ ≤ ε_k`) with `ε' = K ε_{k+1}`. -/
theorem not_localLoss_eps_succ_le {d L N : ℕ} [NeZero L] (P : Consts) (hα₀ : 0 < P.α₀)
    (hα : P.alpha d ≤ 2) (hd : 1 ≤ d) (hL : 1 ≤ L) (k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ¬ ((2 * bgK1 d L N + 2) * xiC1 d * P.eps d L (k + 1) + δ ≤ P.eps d L k) :=
  not_mul_eps_succ_add_le P hα₀ (two_rpow_lt_localLoss (N := N) hd hL hα) k hδ

/-- `2 L^α < C₀⁴` (`C₀ = scaledC0 d = 8 d + 12`) when `α ≤ 2`, `1 ≤ L` and `2 L² < C₀⁴`. -/
theorem two_rpow_lt_scaledC0_four {d L : ℕ} {α : ℝ} (hα : α ≤ 2) (hL : 1 ≤ L)
    (hL2 : 2 * (L : ℝ) ^ 2 < scaledC0 d ^ 4) : 2 * (L : ℝ) ^ α < scaledC0 d ^ 4 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hpow : (L : ℝ) ^ α ≤ (L : ℝ) ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hL1 hα
    simpa [Real.rpow_two] using this
  linarith

/-- At `d = L = 3`: `2 · 3² < C₀⁴ = 36⁴`. -/
theorem two_mul_three_sq_lt_scaledC0_four : 2 * ((3 : ℕ) : ℝ) ^ 2 < scaledC0 3 ^ 4 := by
  unfold scaledC0
  norm_num

/-- **The chart test of the landed expansion fails between consecutive class radii.**  The old
terms enter the decoupled expansion through the chart `Ξ^c_j(𝔹_j(X); C₀, C₀² ε + δ)`
(`I5Fan.point_facts`, `InteractionHatE.eTerm_chain`), which lies in the class domain at level `j`
when `C₀² (C₀² ε + δ) ≤ ε_j` (`xiDom_of_xiCData`, `xiCRaw_localB_sub_xiFieldDom`).  For a chart
radius `ε ≥ ε_{k+1}` (the class domain of the new terms must lie in their chart) this is false at
`j = k` as soon as `2 L^α < C₀⁴`, e.g. at `d = L = 3` (`two_mul_three_sq_lt_scaledC0_four`),
for every generator of the class, whole-level or local. -/
theorem not_chartTest_eps_succ {d L : ℕ} [NeZero L] (P : Consts) (hα₀ : 0 < P.α₀)
    (hK : 2 * (L : ℝ) ^ P.alpha d < scaledC0 d ^ 4) (k : ℕ) {ε δ : ℝ}
    (hε : P.eps d L (k + 1) ≤ ε) (hδ : 0 ≤ δ) :
    ¬ (scaledC0 d ^ 2 * (scaledC0 d ^ 2 * ε + δ) ≤ P.eps d L k) := by
  intro h
  have hC : 0 ≤ scaledC0 d ^ 2 := sq_nonneg _
  have h4 : scaledC0 d ^ 4 * P.eps d L (k + 1) + scaledC0 d ^ 2 * δ ≤ P.eps d L k := by
    have : scaledC0 d ^ 4 * P.eps d L (k + 1) ≤ scaledC0 d ^ 4 * ε :=
      mul_le_mul_of_nonneg_left hε (by positivity)
    nlinarith
  exact not_mul_eps_succ_add_le P hα₀ hK k (mul_nonneg hC hδ) h4

/-- `α = (d - 2)/2 - γ ≤ 2` for `d ≤ 6` and `γ ≥ 0` (the case `d = 3` of the fixed tower). -/
theorem _root_.Balaban.SmallField.Def6.Consts.alpha_le_two {d : ℕ} (P : Consts) (hd : d ≤ 6) (hγ : 0 ≤ P.γ) :
    P.alpha d ≤ 2 := by
  unfold Consts.alpha
  have : (d : ℝ) ≤ 6 := by exact_mod_cast hd
  linarith

end Radius

/-! ### Analyticity at pairs agreeing on the polymer -/

section Agree

/-- If `f` is invariant under the translation by `p - q`, analyticity at `p` gives analyticity
at `q`. -/
theorem analyticAt_of_translate {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : V → F} {p q : V}
    (hinv : ∀ r, f (r + (p - q)) = f r) (hp : AnalyticAt ℂ f p) : AnalyticAt ℂ f q := by
  have hT : AnalyticAt ℂ (fun r : V => r + (p - q)) q :=
    analyticAt_id.add analyticAt_const
  have hp' : AnalyticAt ℂ f ((fun r : V => r + (p - q)) q) := by
    show AnalyticAt ℂ f (q + (p - q))
    rwa [add_sub_cancel]
  have := AnalyticAt.comp (g := f) (f := fun r : V => r + (p - q)) (x := q) hp' hT
  have e : (f ∘ fun r : V => r + (p - q)) = f := funext hinv
  rwa [e] at this

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {Dom : FieldDom d L N₁ m₁ k N ϱ} {Tm : Terms d L N₁ m₁ k N ϱ}

/-- **An energy term is analytic, with the same value and bound, at every pair agreeing on `X`
with a point of its domain** (clauses `localE`, `analyticE`, `boundE`). -/
theorem _root_.Balaban.SmallField.Def6v2.SFTermClauses.analyticAt_E_of_agreeOn
    (hT : SFTermClauses P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X)
    (hy : y ∈ X) {Ψ h Ψ' h' : Fld d L N₁ m₁ k N} (hD : Dom.dom j (Tm.gs j X) Ψ h)
    (hag : ∀ x ∈ X, Ψ' x = Ψ x ∧ h' x = h x) :
    AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Tm.E j y X p.1 p.2)
        (Ψ', h') ∧
      Tm.E j y X Ψ' h' = Tm.E j y X Ψ h ∧
      ‖Tm.E j y X Ψ' h'‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X) := by
  have hval : Tm.E j y X Ψ' h' = Tm.E j y X Ψ h := hT.localE j y X Ψ' Ψ h' h hag
  refine ⟨analyticAt_of_translate (p := (Ψ, h)) (fun r => ?_)
    (hT.analyticE j hj1 hjk y X hX hy (Ψ, h) hD), hval, ?_⟩
  · refine hT.localE j y X _ _ _ _ fun x hx => ?_
    obtain ⟨h1, h2⟩ := hag x hx
    refine ⟨?_, ?_⟩
    · funext i
      have := congrFun h1 i
      simp [this]
    · funext i
      have := congrFun h2 i
      simp [this]
  · rw [hval]
    exact hT.boundE j hj1 hjk y X hX hy Ψ h hD

/-- **An observable term is analytic, with the same value and bound, at every pair agreeing on
`X` with a point of its domain** (fixed source `g`, `‖g‖₁ < 1`; clauses `localM`, `analyticM`,
`boundM`). -/
theorem _root_.Balaban.SmallField.Def6v2.SFTermClauses.analyticAt_M_of_agreeOn
    (hT : SFTermClauses P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {x₀ : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X)
    (hx₀ : x₀ ∈ X) {Ψ h Ψ' h' g : Fld d L N₁ m₁ k N} (hD : Dom.dom j (Tm.gs j X) Ψ h)
    (hg : Def6.l1 g < 1) (hag : ∀ x ∈ X, Ψ' x = Ψ x ∧ h' x = h x) :
    AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
        Tm.M j x₀ X p.1 p.2.1 p.2.2) (Ψ', h', g) ∧
      Tm.M j x₀ X Ψ' h' g = Tm.M j x₀ X Ψ h g ∧
      vn (Tm.M j x₀ X Ψ' h' g) <
        P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
          Real.exp (-P.κ * sizeJ P.m₀ j X) := by
  have hval : Tm.M j x₀ X Ψ' h' g = Tm.M j x₀ X Ψ h g :=
    hT.localM j x₀ X Ψ' Ψ h' h g g fun x hx => ⟨(hag x hx).1, (hag x hx).2, rfl⟩
  refine ⟨analyticAt_of_translate (p := (Ψ, h, g)) (fun r => ?_)
    (hT.analyticM j hj1 hjk x₀ X hX hx₀ (Ψ, h, g) ⟨hD, hg⟩), hval, ?_⟩
  · refine hT.localM j x₀ X _ _ _ _ _ _ fun x hx => ?_
    obtain ⟨h1, h2⟩ := hag x hx
    refine ⟨?_, ?_, ?_⟩
    · funext i
      have := congrFun h1 i
      simp [this]
    · funext i
      have := congrFun h2 i
      simp [this]
    · funext i
      simp
  · rw [hval]
    exact hT.boundM j hj1 hjk x₀ X hX hx₀ Ψ h g hD hg

end Agree

/-! ### The whole-level composed pair from the local composed pair -/

section Composed

variable {d L N₁ m₁ K k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {Dom : FieldDom d L N₁ m₁ K N ϱ} {Tm : Terms d L N₁ m₁ K N ϱ}

/-- **Analyticity at the whole-level composed pair from the local composed pair** (P3 (4.29),
Theorem 7.3; no inclusion of charts).  For terms with the strong specification of their sets, if
the local composed pair of `𝔹_j(X) = Tm.gs j X` over the top level `k` lies in the domain of the
class, the term `ℰ^{(j)}(y, X; ·)` is analytic at the whole-level composed pair
`composedPairAt … j D`, with the same value and the bound of (H.4). -/
theorem _root_.Balaban.SmallField.GsSpec.SFTermClausesStrong.analyticAt_E_composedPairAt
    (hT : SFTermClausesStrong P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hk : k ≤ K)
    (a : ℕ → ℝ) (ν : ℝ)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N)
    {y : CTorus d L N₁ m₁ K} {X : Set (CTorus d L N₁ m₁ K)} (hX : IsPolyDom P.m₀ j X)
    (hy : y ∈ X)
    (hD : Dom.dom j (Tm.gs j X) (localPairAt a ν hk (Tm.gs j X) D).1
      (localPairAt a ν hk (Tm.gs j X) D).2) :
    AnalyticAt ℂ (fun p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N => Tm.E j y X p.1 p.2)
        (composedPairAt a ν hk j D) ∧
      Tm.E j y X (composedPairAt a ν hk j D).1 (composedPairAt a ν hk j D).2 =
        Tm.E j y X (localPairAt a ν hk (Tm.gs j X) D).1 (localPairAt a ν hk (Tm.gs j X) D).2 ∧
      ‖Tm.E j y X (composedPairAt a ν hk j D).1 (composedPairAt a ν hk j D).2‖ ≤
        P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X) := by
  have hjK : j ≤ K := hjk.trans hk
  have hS := hT.gsStrong j hj1 hjK X hX
  have hag : ∀ x ∈ X, (composedPairAt a ν hk j D).1 x = (localPairAt a ν hk (Tm.gs j X) D).1 x ∧
      (composedPairAt a ν hk j D).2 x = (localPairAt a ν hk (Tm.gs j X) D).2 x := by
    intro x hx
    have h := fun i => localPairAt_agree hj1 hjk hk a ν hS D hx i
    simp only [composedPairAt, hjk, dite_true]
    exact ⟨(funext fun i => (h i).1).symm, (funext fun i => (h i).2).symm⟩
  exact hT.toSFTermClauses.analyticAt_E_of_agreeOn hj1 hjK hX hy hD hag

end Composed

/-! ### The chart of the expansion in the local class domain -/

section Chart

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]
  {j : ℕ} {hj : j ≤ k} {X : Set (CTorus d L N₁ m₁ k)}
  {hsep : bgR0 d L ≤ minSep L (L ^ m₁)}

/-- **The chart `Ξ^c_j(𝔹_j(X); C₀, ε)` of the expansion lies in the local class domain at the
radius test of a whole-level generator** (`C₀² ε ≤ ε_j`, `C₀ = scaledC0 d`; W715's
`localB_xiFieldDom_of_xiCData` read on raw data).  This is the hypothesis `hchart` of
`classOldDecLocal_expansion` for a term generator `𝔹_j(X) = localB j hj X hsep`. -/
theorem xiCRaw_localB_sub_xiFieldDom {A : ℕ → ℝ} {μ ε : ℝ} {εseq : ℕ → ℝ}
    (hε : scaledC0 d ^ 2 * ε ≤ εseq j) :
    ∀ r ∈ XiCRaw (localB j hj X hsep) A μ j (scaledC0 d) ε,
      (xiFieldDom A μ εseq : FieldDom d L N₁ m₁ k N (bgR0 d L)).dom j
        (localB j hj X hsep) r.1 r.2 := by
  rintro r ⟨D, hD, rfl⟩
  exact localB_xiFieldDom_of_xiCData hε hD

end Chart

end Balaban.SmallField.GsSpec
