/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepActivityClassChart
public import Balaban.Localization.I5FluctFacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The chart test without radius loss (P3 (4.37))

The landed chain of Lemma DL composes twice with the constant `C₀ = scaledC0 d` of (Ξ3) and
rescales twice, so the argument of an old term lies in its class domain at level `j` only under
`C₀² (C₀² ε + K₂ δ₃ + K₂ δ_fl) ≤ ε_j`; with a chart radius `ε ≥ ε_{k+1}` this is false at `j = k`
(`GsSpec.not_chartTest_eps_succ`, `not_chartTest_newest`).  P3 Lemma 4.1 (4.29) composes without
loss: the weight `a(𝔹_j, 𝔹'_k) = ℓ/ℓ' ≤ 1` of (4.30) is bounded by `1`.  In Lean this is the
composition constant `b = 1` of `xiC_compose_of_one_le` (the strict collar bonds
`xiBounds_adj_lt`, `xiCBounds_adj_lt` make `c = 1` admissible, no `σ`-monotonicity is needed), and
the chain at `b = 1` is `point_facts_of_one_le`, `point_facts_fl_of_one_le`.

* `point_facts_xiDom_of_le`, `point_facts_fl_xiDom_of_le`: **the corrected chart test**.  For
  realizable data `Θ ∈ Ξ^c_K(𝔹_{k+1}; 1, ε')` the argument of an old term (the composed datum of
  `𝔹_j(X)`) lies in the class domain `Ξ^c_j(𝔹_j(X); 1, ε_j)` (`XiDom`) as soon as
  `ε' + K₂' δ₃ ≤ ε_j` (background part), resp. `ε' + K₂' δ₃ + K₂' δ_fl ≤ ε_j` (with the
  fluctuation), `K₂' = xiK2 d L N`: condition (4.37) of P3 (printed p. 76).
* `Consts.eps_succ_add_margin_le`, `chartTest_sharp_eps_succ`: with the class sequence
  `ε_j = P.eps d L j` the corrected test at the radius `ε' = ε_{k+1}` and level `j = k` holds when
  `K₂' (δ₃ + δ_fl) ≤ (1 - L^{-α}) ε_k`, since `ε_{k+1} ≤ L^{-α} ε_k` (P3 p. 76: `L^{-α} ε_k`
  against `ε_k - ε_{k+1}`).
* `eps_margin_pos`, `exists_chartTest_sharp_eps_succ`: the margin `(1 - L^{-α}) ε_k` is positive
  for `α > 0`, `L ≥ 2`, `α₀ > 0`, so the test is satisfiable with positive `δ₃ = δ_fl`.
* `three_rpow_neg_alpha_le`, `chartTest_sharp_three`: at `d = L = 3` (`α = 1/2 - γ`) and
  `γ ≤ 1/4`, `3^{-α} ≤ 4/5`, so the test at `ε' = ε_{k+1}` holds when `K₂' (δ₃ + δ_fl) ≤ ε_k / 5`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Finset Matrix

section Test

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

/-- **The corrected chart test, background part** (P3 (4.35)-(4.37)).  For realizable data
`Θ = D ∈ Ξ^c_K(𝔹_{k+1}; 1, ε')` and `s` in the polydisc, the composite of Lemma DL is computed
through `F₁`, `F_k`, and the argument of an old term, the composed datum of `𝔹_j(X)`, lies in the
class domain `Ξ^c_j(𝔹_j(X); 1, ε_j)` whenever `ε' + K₂' δ₃ ≤ ε_j`. -/
theorem point_facts_xiDom_of_le (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Fk : RawData d L (N₁ * L ^ m₁) K N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
      s ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D) {εj : ℝ}
    (hε : eps + xiK2 d L N * δ₃ ≤ εj) :
    ∃ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ),
      IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α ∧ F₁ (s, rawOf D) = (φ, α) ∧
      D1raw Gp Gk (compWeight L a₁) F₁ (s, rawOf D) =
        rawOf (composeData hB.hP (compWeight L a₁) φ D) ∧
      D2raw Gk Gj (compWeight L a₁) Fk (rawOf (composeData hB.hP (compWeight L a₁) φ D)) =
        rawOf (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) (composeData hB.hP (compWeight L a₁) φ D))
          (composeData hB.hP (compWeight L a₁) φ D)) ∧
      XiDom Gj (compWeight L a₁) ν j εj
        (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) (composeData hB.hP (compWeight L a₁) φ D))
          (composeData hB.hP (compWeight L a₁) φ D)).Ψ
        (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) (composeData hB.hP (compWeight L a₁) φ D))
          (composeData hB.hP (compWeight L a₁) φ D)).h := by
  have hC0 : (1 : ℝ) ≤ scaledC0 d := one_le_scaledC0 d
  obtain ⟨φ, α, hI, hFeq, -, hD1, hD2, hX⟩ := point_facts_of_one_le le_rfl hC0 hB hF₁ hFk hs hs1 hD
  have hε' : (1 : ℝ) ^ 2 * (1 ^ 2 * eps + xiK2 d L N * δ₃) ≤ εj := by
    simpa using hε
  exact ⟨φ, α, hI, hFeq, hD1, hD2, Fluctuation.xiDom_of_xiCData_of_one_le le_rfl hε' hX⟩

/-- **The corrected chart test with the fluctuation** (P3 (4.37)).  For realizable data
`Θ = D ∈ Ξ^c_K(𝔹_{k+1}; 1, ε')`, `s` in the polydisc and a layer-constant fluctuation `ψ'` with
`|ψ'| < δ₁`, the composite of Lemma DL with the fluctuation is computed through `F₁`, `Sol`, `F_k`,
and the argument of an old term lies in the class domain `Ξ^c_j(𝔹_j(X); 1, ε_j)` whenever
`ε' + K₂' δ₃ + K₂' δ_fl ≤ ε_j`.  The landed test was `C₀² (C₀² ε' + K₂' δ₃ + K₂' δ_fl) ≤ ε_j`. -/
theorem point_facts_fl_xiDom_of_le (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Fk : RawData d L (N₁ * L ^ m₁) K N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
      s ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D)
    {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ} (hψ : ∀ x ∈ dataSites Hm, vn (ψ' x) < δ₁)
    (hψc : IsLayerConstant Hm ψ') {εj : ℝ}
    (hε : eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl ≤ εj) :
    ∃ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ),
      IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α ∧ F₁ (s, rawOf D) = (φ, α) ∧
      (Sol (s, flEdat Gp Hm (φ, α) D.Ψ ψ')).1 = δφ ∧
      D1rawFl Gp Gk Hm (compWeight L a₁) F₁ Sol s (rawOf D, ψ') =
        rawOf (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc) ∧
      D2raw Gk Gj (compWeight L a₁) Fk
          (rawOf (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)) =
        rawOf (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc))
          (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)) ∧
      XiDom Gj (compWeight L a₁) ν j εj
        (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc))
          (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)).Ψ
        (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc))
          (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)).h := by
  have hC0 : (1 : ℝ) ≤ scaledC0 d := one_le_scaledC0 d
  obtain ⟨φ, α, δφ, hI, hFeq, -, hSolφ, -, hD1, hD2, hX⟩ :=
    point_facts_fl_of_one_le le_rfl hC0 hB hF hF₁ hFk hSol hs hs1 hD hψ hψc
  have hε' : (1 : ℝ) ^ 2 * (1 ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) ≤ εj := by
    simpa using hε
  exact ⟨φ, α, δφ, hI, hFeq, hSolφ, hD1, hD2, Fluctuation.xiDom_of_xiCData_of_one_le le_rfl hε' hX⟩

end Test

end Balaban.Localization

namespace Balaban.SmallField.Def6

open Balaban.SmallField

/-! ### The corrected test between consecutive class radii -/

section Radius

variable {d L : ℕ}

/-- `ε_{k+1} + (1 - L^{-α}) ε_k ≤ ε_k` for the class sequence (the gap (E), P3 p. 76). -/
theorem Consts.eps_succ_add_margin_le (P : Consts) (hα₀ : 0 ≤ P.α₀) (k : ℕ) :
    P.eps d L (k + 1) + (1 - (L : ℝ) ^ (-P.alpha d)) * P.eps d L k ≤ P.eps d L k := by
  have h := Consts.eps_gapE d L P hα₀ k
  have e : (1 - (1 - (L : ℝ) ^ (-P.alpha d))) * P.eps d L k + (1 - (L : ℝ) ^ (-P.alpha d)) *
      P.eps d L k = P.eps d L k := by ring
  linarith

/-- **The corrected chart test holds at the radius `ε_{k+1}` and the level `k`**: for the class
sequence, `ε_{k+1} + K₂' δ₃ + K₂' δ_fl ≤ ε_k` as soon as
`K₂' δ₃ + K₂' δ_fl ≤ (1 - L^{-α}) ε_k`.  (The landed test `C₀² (C₀² ε_{k+1} + …) ≤ ε_k` is false,
`GsSpec.not_chartTest_eps_succ`.) -/
theorem chartTest_sharp_eps_succ (P : Consts) (hα₀ : 0 ≤ P.α₀) (k : ℕ) {K₂ δ₃ δfl : ℝ}
    (hδ : K₂ * δ₃ + K₂ * δfl ≤ (1 - (L : ℝ) ^ (-P.alpha d)) * P.eps d L k) :
    P.eps d L (k + 1) + K₂ * δ₃ + K₂ * δfl ≤ P.eps d L k := by
  have := Consts.eps_succ_add_margin_le (d := d) (L := L) P hα₀ k
  linarith

/-- **The margin of the corrected test is positive**: `0 < (1 - L^{-α}) ε_k` for `α > 0`,
`L ≥ 2` and `α₀ > 0`. -/
theorem eps_margin_pos [NeZero L] (P : Consts) (hα₀ : 0 < P.α₀) (hα : 0 < P.alpha d) (hL : 2 ≤ L)
    (k : ℕ) : 0 < (1 - (L : ℝ) ^ (-P.alpha d)) * P.eps d L k := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have h1 : (L : ℝ) ^ (-P.alpha d) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith)
  have h2 := eps_pos (d := d) (L := L) hα₀ k
  have : 0 < 1 - (L : ℝ) ^ (-P.alpha d) := by linarith
  positivity

/-- **The corrected chart test is satisfiable between consecutive class radii**: for `α > 0`,
`L ≥ 2`, `α₀ > 0` and every `K₂' ≥ 0` there is `δ > 0` with `ε_{k+1} + K₂' δ + K₂' δ ≤ ε_k`. -/
theorem exists_chartTest_sharp_eps_succ [NeZero L] (P : Consts) (hα₀ : 0 < P.α₀)
    (hα : 0 < P.alpha d) (hL : 2 ≤ L) (k : ℕ) {K₂ : ℝ} (hK₂ : 0 ≤ K₂) :
    ∃ δ : ℝ, 0 < δ ∧ P.eps d L (k + 1) + K₂ * δ + K₂ * δ ≤ P.eps d L k := by
  have hm := eps_margin_pos (d := d) P hα₀ hα hL k
  set m := (1 - (L : ℝ) ^ (-P.alpha d)) * P.eps d L k with hmdef
  refine ⟨m / (2 * (K₂ + 1)), by positivity, chartTest_sharp_eps_succ P hα₀.le k ?_⟩
  have e : K₂ * (m / (2 * (K₂ + 1))) + K₂ * (m / (2 * (K₂ + 1))) = K₂ / (K₂ + 1) * m := by
    field_simp
    ring
  rw [e]
  have h1 : K₂ / (K₂ + 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  nlinarith

/-- At `d = L = 3` and `γ ≤ 1/4` (`α = 1/2 - γ ≥ 1/4`): `3^{-α} ≤ 4/5`. -/
theorem three_rpow_neg_alpha_le (P : Consts) (hγ : P.γ ≤ 1 / 4) :
    ((3 : ℕ) : ℝ) ^ (-P.alpha 3) ≤ 4 / 5 := by
  have hα : (1 : ℝ) / 4 ≤ P.alpha 3 := by
    unfold Consts.alpha
    push_cast
    linarith
  have h3 : (1 : ℝ) ≤ ((3 : ℕ) : ℝ) := by norm_num
  have h1 : ((3 : ℕ) : ℝ) ^ (-P.alpha 3) ≤ ((3 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le h3 (by linarith)
  have h0 : (0 : ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have h4 : (((3 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) ^ (4 : ℕ) = 1 / 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h2 : ((3 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 4 / 5 := by
    by_contra hcon
    push Not at hcon
    have := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
    rw [h4] at this
    norm_num at this
  linarith

/-- **The corrected chart test at `d = L = 3`**: for `γ ≤ 1/4` and `α₀ ≥ 0`,
`ε_{k+1} + K₂' δ₃ + K₂' δ_fl ≤ ε_k` as soon as `K₂' δ₃ + K₂' δ_fl ≤ ε_k / 5`.  (The landed test
needed `C₀⁴ = 36⁴ ≤ ε_k / ε_{k+1}`.) -/
theorem chartTest_sharp_three (P : Consts) (hα₀ : 0 ≤ P.α₀) (hγ : P.γ ≤ 1 / 4) (k : ℕ)
    {K₂ δ₃ δfl : ℝ} (hδ : K₂ * δ₃ + K₂ * δfl ≤ P.eps 3 3 k / 5) :
    P.eps 3 3 (k + 1) + K₂ * δ₃ + K₂ * δfl ≤ P.eps 3 3 k := by
  refine chartTest_sharp_eps_succ P hα₀ k ?_
  have h1 := three_rpow_neg_alpha_le P hγ
  have h2 : 0 ≤ P.eps 3 3 k := by
    unfold Consts.eps epsSeq
    have := epsTail_pos k
    have : (0 : ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-P.alpha 3) := Real.rpow_nonneg (by norm_num) _
    positivity
  have h3 : P.eps 3 3 k / 5 ≤ (1 - ((3 : ℕ) : ℝ) ^ (-P.alpha 3)) * P.eps 3 3 k := by
    nlinarith
  exact hδ.trans h3

end Radius

end Balaban.SmallField.Def6
