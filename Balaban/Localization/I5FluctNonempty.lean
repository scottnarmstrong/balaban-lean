/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5Fluct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# Inhabitation of the hypotheses of Theorem I-5 with the fluctuation

* `flNum_nonempty`: the numerical conditions `FlNum` hold for all sufficiently small
  `ε', δ₃, δ₁` (and `δfl = N (5 K₂' δ₁ + δ₁)`);
* `rowInHat_self`: for the pair `(coverOf G, G)` the rows of the operator stay in the thickened
  cube (the landed `row_mem_hat`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Filter Topology

section Num

variable {d L N : ℕ} [NeZero L]

theorem ev_lt {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ} (h : f 0 < c) :
    ∀ᶠ t in 𝓝 (0 : ℝ), f t < c :=
  hf.continuousAt.eventually_lt continuousAt_const h

/-- **Inhabitation of `FlNum`**: the conditions hold for `ε' = δ₃ = δ₁ = t` and
`δfl = N (5 K₂' t + t)` for all small `t > 0`. -/
theorem flNum_nonempty (hd : 0 < d) (BG : ℝ) {BG₂ : ℝ} (hBG₂ : 0 ≤ BG₂) (κ : ℝ) :
    ∃ t : ℝ, 0 < t ∧ Nonempty (FlNum d L N BG BG₂ κ t t t
      (N * (5 * (cK2' d L N (famConst d L BG₂ κ) * t) + t))) := by
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hBG₂ κ hd; linarith
  have hk0 := cK2'_nonneg (d := d) (L := L) (N := N) hB0
  have hD1 : 0 < deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8) :=
    deltaStar'_pos hB0 (by have := gamma1_pos hd; positivity)
  have hC1 : 0 < bgC1 d L N := bgC1_pos' hd
  have hC0 : 0 < bgC0 d L N := bgC0_pos d L N hd
  have hDs : 0 < deltaStar d L N := deltaStar_pos (d := d) (L := L) (N := N) hd
  have hK1 : 0 < bgK1 d L N := bgK1_pos d L N
  have hT : 0 < thm73C1 d L N := by
    unfold thm73C1
    have := compC4_ge d
    positivity
  set k := cK2' d L N (famConst d L BG₂ κ) with hk
  set D1 := deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8) with hD1def
  have e1 := ev_lt (f := fun t : ℝ => t) (by fun_prop) (c := D1) (by simpa using hD1)
  have e2 := ev_lt (f := fun t : ℝ => 2 * (K4 d L N BG κ * (xiC1 d * t))) (by fun_prop) (c := D1)
    (by simpa using hD1)
  have e3 := ev_lt (f := fun t : ℝ => 2 * (K4 d L N BG κ * (xiC1 d * t))) (by fun_prop) (c := 1)
    (by simp)
  have e4 := ev_lt (f := fun t : ℝ => (3 + K4 d L N BG κ) * (xiC1 d * t)) (by fun_prop)
    (c := 1 / 2) (by simp)
  have e5 := ev_lt (f := fun t : ℝ => N * (5 * (k * t) + t)) (by fun_prop) (c := 1) (by simp)
  have e6 := ev_lt (f := fun t : ℝ => xiC1 d * (scaledC0 d ^ 2 * t + xiK2 d L N * t) +
    5 * (N * (5 * (k * t) + t))) (by fun_prop) (c := bgC1 d L N) (by simpa using hC1)
  have e7 := ev_lt (f := fun t : ℝ => N * (5 * (k * t) + t)) (by fun_prop) (c := deltaStar d L N)
    (by simpa using hDs)
  have e8 := ev_lt (f := fun t : ℝ => bgK1 d L N * (xiC1 d * (scaledC0 d ^ 2 * t +
    xiK2 d L N * t))) (by fun_prop) (c := deltaStar d L N) (by simpa using hDs)
  have e9 := ev_lt (f := fun t : ℝ => bgK1 d L N * (xiC1 d * (scaledC0 d ^ 2 * t +
    xiK2 d L N * t)) + cK2 d L N * (N * (5 * (k * t) + t))) (by fun_prop) (c := bgC0 d L N)
    (by simpa using hC0)
  have e10 := ev_lt (f := fun t : ℝ => (4 * d + 6) * ((2 * d + 1) * (scaledC0 d ^ 2 * t +
    xiK2 d L N * t + xiK2 d L N * (N * (5 * (k * t) + t))))) (by fun_prop) (c := 1) (by simp)
  have e11 := ev_lt (f := fun t : ℝ => xiC1 d * (scaledC0 d ^ 2 * t + xiK2 d L N * t +
    xiK2 d L N * (N * (5 * (k * t) + t)))) (by fun_prop) (c := thm73C1 d L N) (by simpa using hT)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < D1 ∧
      2 * (K4 d L N BG κ * (xiC1 d * t)) < D1 ∧ 2 * (K4 d L N BG κ * (xiC1 d * t)) < 1 ∧
      (3 + K4 d L N BG κ) * (xiC1 d * t) < 1 / 2 ∧ (N : ℝ) * (5 * (k * t) + t) < 1 ∧
      xiC1 d * (scaledC0 d ^ 2 * t + xiK2 d L N * t) + 5 * (N * (5 * (k * t) + t)) < bgC1 d L N ∧
      (N : ℝ) * (5 * (k * t) + t) < deltaStar d L N ∧
      bgK1 d L N * (xiC1 d * (scaledC0 d ^ 2 * t + xiK2 d L N * t)) < deltaStar d L N ∧
      bgK1 d L N * (xiC1 d * (scaledC0 d ^ 2 * t + xiK2 d L N * t)) +
        cK2 d L N * (N * (5 * (k * t) + t)) < bgC0 d L N ∧
      (4 * d + 6) * ((2 * d + 1) * (scaledC0 d ^ 2 * t + xiK2 d L N * t +
        xiK2 d L N * (N * (5 * (k * t) + t)))) < 1 ∧
      xiC1 d * (scaledC0 d ^ 2 * t + xiK2 d L N * t + xiK2 d L N * (N * (5 * (k * t) + t))) <
        thm73C1 d L N := by
    have wk : ∀ {p : ℝ → Prop}, (∀ᶠ t in 𝓝 (0 : ℝ), p t) → ∀ᶠ t in 𝓝[>] (0 : ℝ), p t :=
      fun h => eventually_nhdsWithin_of_eventually_nhds h
    exact hpos.and ((wk e1).and ((wk e2).and ((wk e3).and ((wk e4).and ((wk e5).and ((wk e6).and
      ((wk e7).and ((wk e8).and ((wk e9).and ((wk e10).and (wk e11)))))))))))
  obtain ⟨t, ht0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hall.exists
  have hk' : 0 ≤ (N : ℝ) * (5 * (k * t) + t) := by positivity
  exact ⟨t, ht0, ⟨{
    δ₁_pos := ht0
    δ₁_le := h1.le
    B_le := h2.le
    B_one := h3.le
    phi_lt := h4
    flb := le_rfl
    δfl_nn := hk'
    δfl_le_one := h5.le
    c1_f := h6.le
    star_f := h7.le
    K1s_f := h8.le
    sm_f := h9
    small₃ := h10.le
    th₃ := h11.le }⟩⟩

end Num

section Geom

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- For the pair `(coverOf G, G)` the rows of the operator stay in the thickened cube. -/
theorem rowInHat_self {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
    (S : DGSetting G a ν) : RowInHat (coverOf G) G a ν :=
  fun z hz α _ hx _ hy => (Dec2.coverLocal_self S).row_mem_hat z hz α hx hy

/-- **Inhabitation of `FlSetting`**: for the self pair `Gk = Hm = Gp`, `(C, H⁻) = (coverOf Gp, Gp)`
(for which `FootLocal` is landed), `X₁ = ⊤`, all sufficiently small `ε' = δ₃ = δ₁`. -/
theorem flSetting_nonempty {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a₁ ν : ℝ}
    (S : DGSetting Gp (compWeight L a₁) ν) (BG : ℝ) {c₂ BG₂ : ℝ}
    (hS2 : Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c₂ BG₂)
    {κ : ℝ} (hM2 : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) :
    ∃ t : ℝ, 0 < t ∧ Nonempty (FlSetting N Gp Gp Gp a₁ ν κ BG t t (Dec2.selfKc d L) (Cchi d L)
      c₂ BG₂ t (N * (5 * (cK2' d L N (famConst d L BG₂ κ) * t) + t)) Finset.univ) := by
  obtain ⟨t, ht, ⟨hn⟩⟩ := flNum_nonempty (d := d) (L := L) (N := N) (by have := S.hd; omega) BG
    hS2.fam.2.1 κ
  obtain ⟨hSM⟩ := Dec2.footLocal_nonempty S
  exact ⟨t, ht, ⟨{
    hS2 := hS2
    SM := hSM
    hM2 := hM2
    hPm := fun i _ _ => Finset.Subset.refl _
    hPmp := fun i _ _ => Finset.Subset.refl _
    depm := fun _ _ _ _ => Finset.mem_univ _
    num := hn }⟩⟩

end Geom

end Balaban.Localization
