/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.NewLevelZeroSourceBgCanon
public import Balaban.Fluctuation.InteractionHatE

/-!
# The settings of the old terms on a background generating set (`NewLevelOldTermsBgSetting`)

P3 Lemma 4.2 at `Gb` for the old terms of the new level (route R-LOC, L4-3).  An old term whose
generating set `𝔹_k(X)` (`Gk`) has its data sites in the top layer of `Gb` has on `Gb` the
background and fluctuation settings of the step (`BgSetting`, `FlSetting`), with the fluctuation set
`H⁻` of `Gb` (`Ω_k(H⁻) = Ω_k(Gb)`, no layer `k + 1`): the composite dependency sets read only the
layer index of the data site, which is the step's (`k + 1` on `Gb`, `k` on `H⁻`), the spacing of
`Gb` is at most the step's, and `Gk ≺ Gb`, `Gk ≺ H⁻` because the data sites of `Gk` lie in the top
layer of `Gb`.  Hence the old-term functional `eTermFun` recomputed on `Gb` is analytic and bounded
on the realizable triples of `Gb` (`eTermFun_analytic_of_one_le`, `eTermFun_bound_of_one_le`).

* `composeDep_eq_of_layerIndex`: the composite dependency set reads only the layer index;
* `precedes_of_Omega1_top`, `precedes_fl_of_top`: `Gk ≺ Gb` and `Gk ≺ H⁻`;
* `bgSetting_of_top`, `flSetting_of_top_gen` (`flSetting_of_top`): the settings on `Gb`;
* `eTermFun_analytic_bound_of_top_gen` (`eTermFun_analytic_bound_of_top`): analyticity and bound of
  the old-term functional on `Gb`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
  Finset

section Dep

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' ϱ'' : ℝ}

/-- **The composite dependency set reads only the layer index of the second generating set.** -/
theorem composeDep_eq_of_layerIndex {G : GeneratingSet d L N₀ K ϱ}
    {G' : GeneratingSet d L N₀ K ϱ'} {G'' : GeneratingSet d L N₀ K ϱ''}
    {x : Torus d (N₀ * L ^ K)} (h : G'.layerIndex x = G''.layerIndex x) :
    composeDep G G' x = composeDep G G'' x := by
  unfold composeDep
  rw [h]
  rfl

end Dep

section Setting

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱb ϱm ϱd : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
  {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱd}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}

/-- **A generating set whose first domain lies in the top layer of `Gb` precedes `Gb`.** -/
theorem precedes_of_Omega1_top (htop : ∀ x ∈ Gk.Ω 1, x ∈ Gb.Ω (k + 1)) : Precedes Gk Gb := by
  intro i hi hik x hx
  exact Gb.Ω_antitone hi hik (by omega) (htop x (Gk.Ω_antitone le_rfl hi (by omega) hx))

/-- **The fluctuation set of `Gb` follows the old term's generating set**: if `Gk ≺ H⁻` for a
level-`k` set `H⁻` of the step and the first domain of `Gk` lies in the top layer of `Gb`, then
`Gk ≺ H⁻_b` for every `H⁻_b` with `Ω_k(H⁻_b) = Ω_k(Gb)`. -/
theorem precedes_fl_of_top (hk1 : 1 ≤ k) (hPm : Precedes Gk Hm) (hG : IsLevel Hm k)
    (hdk : Gd.Ω k = Gb.Ω k) (htop : ∀ x ∈ Gk.Ω 1, x ∈ Gb.Ω (k + 1)) : Precedes Gk Gd := by
  intro i hi hik x hx
  rcases Nat.lt_or_ge i (k + 1) with hlt | hge
  · have hxk : x ∈ Gd.Ω k := by
      rw [hdk]
      exact Gb.Ω_antitone hk1 (Nat.le_succ k) (by omega)
        (htop x (Gk.Ω_antitone le_rfl hi (by omega) hx))
    exact Gd.Ω_antitone hi (by omega) (by omega) hxk
  · have hy := hPm i hi hik hx
    have hi' : i = k + 1 := by omega
    subst hi'
    have h1 := Hm.layerIndex_eq (by omega) le_rfl (mem_layer_top hy)
    rw [(hG x).2] at h1
    omega

/-- **The background setting of an old term on `Gb`**: the step's `BgSetting` of the old term
gives the one on `Gb` when the data sites of `Gk` lie in the top layer of `Gb`, for `Gb` with
`DGSetting`, the background hypotheses and `r₀ M₁ ≤ ϱ_b - 1`. -/
theorem bgSetting_of_top (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hG' : IsLevel Gp (k + 1)) (Sb : DGSetting Gb (compWeight L a₁) ν)
    (HBb : BgHyp d L (k + 1) ϱb (compWeight L a₁) ν) (hrb : r₀ * (L : ℝ) ^ m₁ ≤ ϱb - 1)
    (htop : ∀ x ∈ dataSites Gk, x ∈ Gb.Ω (k + 1)) :
    BgSetting N Gb Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j where
  hS := hB.hS
  Sp := Sb
  ha₁ := hB.ha₁
  HBp := HBb
  HBk := hB.HBk
  HBj := hB.HBj
  hP := precedes_of_Omega1_top fun x hx => htop x ((mem_dataSites Gk).2 (Or.inl hx))
  hq := hB.hq
  colk := fun z hz => Gb.Ω_antitone le_rfl (by omega) (by omega)
    (htop z ((mem_dataSites Gk).2 (Or.inr hz)))
  colj := hB.colj
  hκ := hB.hκ
  hM := hB.hM
  num := hB.num
  dsX₀ := hB.dsX₀
  hN := fun x hx hxb y hy => by
    refine hB.hN x hx (hG' x).1 y (lt_of_lt_of_le hy ?_)
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    have hr0 : 0 ≤ r₀ * (L : ℝ) ^ m₁ :=
      mul_nonneg (le_trans (by positivity) hB.hr₀) (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ hr0
    unfold GeneratingSet.spacing
    rw [(hG' x).2]
    exact pow_le_pow_right₀ hL1 (Gb.layerIndex_spec hxb).2.1
  hr := hrb
  hr₀ := hB.hr₀
  dep := fun x hx y hy => by
    refine hB.dep x hx y ?_
    rwa [composeDep_eq_of_layerIndex (G'' := Gp) (by
      rw [Gb.layerIndex_eq (by omega) le_rfl (mem_layer_top (htop x hx)), (hG' x).2])] at hy
  hj := hB.hj

/-- **The fluctuation setting of an old term on `Gb`**: the step's `FlSetting` of the old term
(fluctuation set `H⁻` of level `k`, any constants `(Kc', Cx', c₂')` of its cover) gives the one on
`Gb` with its fluctuation set `H⁻_b` (`Ω_k(H⁻_b) = Ω_k(Gb)`, no layer `k + 1`) and the constants
`(Kc, Cx, c₂)` of the `FlCore` of `(Gb, H⁻_b)`, when the data sites of `Gk` lie in the top layer of
`Gb`. -/
theorem flSetting_of_top_gen {Kc Cx c₂ Kc' Cx' c₂' BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc' Cx' c₂' BG₂ δ₁ δfl X₁f) (hG : IsLevel Hm k)
    (hk1 : 1 ≤ k) (hC : FlCore N Gb Gd a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hdk : Gd.Ω k = Gb.Ω k) (hdtop : Gd.Ω (k + 1) = ∅)
    (htop : ∀ x ∈ dataSites Gk, x ∈ Gb.Ω (k + 1)) :
    FlSetting N Gb Gk Gd a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f where
  hS2 := hC.hS2
  SM := hC.SM
  hM2 := hC.hM2
  hPm := precedes_fl_of_top hk1 hF.hPm hG hdk fun x hx =>
    htop x ((mem_dataSites Gk).2 (Or.inl hx))
  hPmp := hC.hPmp
  depm := fun x hx y hy => by
    refine hF.depm x hx y ?_
    rwa [composeDep_eq_of_layerIndex (G'' := Hm) (by
      rw [(blockLayers_of_top hk1 hdk hdtop (htop x hx)).1.2, (hG x).2])] at hy
  num := hF.num

/-- **The fluctuation setting of an old term on `Gb`**: the step's `FlSetting` of the old term
(fluctuation set `H⁻` of level `k`) gives the one on `Gb` with its fluctuation set `H⁻_b`
(`Ω_k(H⁻_b) = Ω_k(Gb)`, no layer `k + 1`, `FlCore` of `(Gb, H⁻_b)`) when the data sites of `Gk`
lie in the top layer of `Gb` (the instance of `flSetting_of_top_gen` at the step's constants). -/
theorem flSetting_of_top {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f) (hG : IsLevel Hm k)
    (hk1 : 1 ≤ k) (hC : FlCore N Gb Gd a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hdk : Gd.Ω k = Gb.Ω k) (hdtop : Gd.Ω (k + 1) = ∅)
    (htop : ∀ x ∈ dataSites Gk, x ∈ Gb.Ω (k + 1)) :
    FlSetting N Gb Gk Gd a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f :=
  flSetting_of_top_gen hF hG hk1 hC hdk hdtop htop

/-- **(AE1) input of the old terms on `Gb`, general constants of the step's cover**: the statement
of `eTermFun_analytic_bound_of_top` for a step `FlSetting` with any constants `(Kc', Cx', c₂')` of
its cover (`flSetting_of_top_gen`). -/
theorem eTermFun_analytic_bound_of_top_gen {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) (hG' : IsLevel Gp (k + 1))
    {Kc Cx c₂ Kc' Cx' c₂' BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc' Cx' c₂' BG₂ δ₁ δfl X₁f) (hG : IsLevel Hm k)
    (hk1 : 1 ≤ k) (Sb : DGSetting Gb (compWeight L a₁) ν)
    (HBb : BgHyp d L (k + 1) ϱb (compWeight L a₁) ν) (hrb : r₀ * (L : ℝ) ^ m₁ ≤ ϱb - 1)
    (hC : FlCore N Gb Gd a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hdk : Gd.Ω k = Gb.Ω k) (hdtop : Gd.Ω (k + 1) = ∅)
    (htop : ∀ x ∈ dataSites Gk, x ∈ Gb.Ω (k + 1))
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ} {B : ℝ}
    (hE : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ‖E r‖ ≤ B) :
    AnalyticOnNhd ℂ (fun t : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) × (Gd.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) =>
      eTermFun Gb Gk Gj Gd (compWeight L a₁) Fk E t.1 t.2.1 t.2.2)
      (FlRealLC Gb Gd a₁ ν BG κ eps X₁f BG₂ δ₁) ∧
    ∀ t ∈ FlRealLC Gb Gd a₁ ν BG κ eps X₁f BG₂ δ₁,
      ‖eTermFun Gb Gk Gj Gd (compWeight L a₁) Fk E t.1 t.2.1 t.2.2‖ ≤ B := by
  have hB' := bgSetting_of_top hB hG' Sb HBb hrb htop
  have hF' := flSetting_of_top_gen hF hG hk1 hC hdk hdtop htop
  exact ⟨eTermFun_analytic_of_one_le hb₁ hbC hB' hF' hFkan hFk hE,
    fun t ht => eTermFun_bound_of_one_le hb₁ hbC hB' hF' hFk hEb ht⟩

/-- **(AE1) input of the old terms on `Gb`**: the old-term functional `eTermFun` recomputed on
`Gb` (with the fluctuation set `H⁻_b`) is analytic and bounded on the realizable triples of `Gb`
(`eTermFun_analytic_of_one_le`, `eTermFun_bound_of_one_le` with `bgSetting_of_top`,
`flSetting_of_top`), when the data sites of the old term's generating set lie in the top layer of
`Gb` and the term `E` is analytic and bounded on its chart (the instance of
`eTermFun_analytic_bound_of_top_gen` at the step's constants). -/
theorem eTermFun_analytic_bound_of_top {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) (hG' : IsLevel Gp (k + 1))
    {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f) (hG : IsLevel Hm k)
    (hk1 : 1 ≤ k) (Sb : DGSetting Gb (compWeight L a₁) ν)
    (HBb : BgHyp d L (k + 1) ϱb (compWeight L a₁) ν) (hrb : r₀ * (L : ℝ) ^ m₁ ≤ ϱb - 1)
    (hC : FlCore N Gb Gd a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hdk : Gd.Ω k = Gb.Ω k) (hdtop : Gd.Ω (k + 1) = ∅)
    (htop : ∀ x ∈ dataSites Gk, x ∈ Gb.Ω (k + 1))
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ} {B : ℝ}
    (hE : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ‖E r‖ ≤ B) :
    AnalyticOnNhd ℂ (fun t : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) × (Gd.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) =>
      eTermFun Gb Gk Gj Gd (compWeight L a₁) Fk E t.1 t.2.1 t.2.2)
      (FlRealLC Gb Gd a₁ ν BG κ eps X₁f BG₂ δ₁) ∧
    ∀ t ∈ FlRealLC Gb Gd a₁ ν BG κ eps X₁f BG₂ δ₁,
      ‖eTermFun Gb Gk Gj Gd (compWeight L a₁) Fk E t.1 t.2.1 t.2.2‖ ≤ B :=
  eTermFun_analytic_bound_of_top_gen hb₁ hbC hB hG' hF hG hk1 Sb HBb hrb hC hdk hdtop htop hFkan hFk
    hE hEb

end Setting

end Balaban.Fluctuation
