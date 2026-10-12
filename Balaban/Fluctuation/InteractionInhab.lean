/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Interaction
public import Balaban.Localization.I5FluctNonempty
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# Inhabitation of the hypotheses of Proposition 3.3 (hard rule 10)

* `flCore_nonempty`: `FlCore` holds for the self pair `Gk = Hm = Gp` (for which `FootLocal` is
  landed) and all sufficiently small `ε' = δ₁`;
* `blockMargin_univ`: `BlockMargin` holds with `X₁ = ⊤` for every set of sites that the interaction
  boxes of the cover contain;
* `locInt_nonempty`: `LocInt` is inhabited (empty set of labels).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Filter
  Topology

section Inhab

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **Inhabitation of `FlCore`**: for the self pair, all sufficiently small `ε' = δ₁`. -/
theorem flCore_nonempty {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a₁ ν : ℝ}
    (S : DGSetting Gp (compWeight L a₁) ν) (HBp : BgHyp d L K ϱ (compWeight L a₁) ν)
    {c BG : ℝ} (hS : DecSpecs d L c BG) {κ : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {c₂ BG₂ : ℝ}
    (hS2 : Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c₂ BG₂)
    (hM2 : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) :
    ∃ t : ℝ, 0 < t ∧ Nonempty (FlCore N Gp Gp a₁ ν c BG κ t (Dec2.selfKc d L) (Cchi d L) c₂ BG₂ t) := by
  have hd : 0 < d := by have := S.hd; omega
  have hBG := hS.fam.2.1
  have hBG₂ := hS2.fam.2.1
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hBG₂ κ hd; linarith
  have hD1 : 0 < deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8) :=
    deltaStar'_pos hB0 (by have := gamma1_pos hd; positivity)
  have hc7 : 0 < c7 d L N BG κ := c7_pos (d := d) (L := L) (N := N) (κ := κ) hd hBG
  have hK4 : 0 < K4 d L N BG κ := K4_pos hBG hd
  have hc1 := one_le_xiC1 d
  set D1 := deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8) with hD1def
  have e1 := ev_lt (f := fun t : ℝ => t) (by fun_prop) (c := D1) (by simpa using hD1)
  have e2 := ev_lt (f := fun t : ℝ => 2 * (K4 d L N BG κ * (xiC1 d * t))) (by fun_prop) (c := D1)
    (by simpa using hD1)
  have e3 := ev_lt (f := fun t : ℝ => 2 * (K4 d L N BG κ * (xiC1 d * t))) (by fun_prop) (c := 1)
    (by simp)
  have e4 := ev_lt (f := fun t : ℝ => (3 + K4 d L N BG κ) * (xiC1 d * t)) (by fun_prop)
    (c := 1 / 2) (by simp)
  have e5 := ev_lt (f := fun t : ℝ => (4 * d + 6) * ((2 * d + 1) * t)) (by fun_prop) (c := 1)
    (by simp)
  have e6 := ev_lt (f := fun t : ℝ => xiC1 d * t) (by fun_prop) (c := c7 d L N BG κ)
    (by simpa using hc7)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < D1 ∧ 2 * (K4 d L N BG κ * (xiC1 d * t)) < D1 ∧
      2 * (K4 d L N BG κ * (xiC1 d * t)) < 1 ∧ (3 + K4 d L N BG κ) * (xiC1 d * t) < 1 / 2 ∧
      (4 * d + 6) * ((2 * d + 1) * t) < 1 ∧ xiC1 d * t < c7 d L N BG κ := by
    have wk : ∀ {p : ℝ → Prop}, (∀ᶠ t in 𝓝 (0 : ℝ), p t) → ∀ᶠ t in 𝓝[>] (0 : ℝ), p t :=
      fun h => eventually_nhdsWithin_of_eventually_nhds h
    exact hpos.and ((wk e1).and ((wk e2).and ((wk e3).and ((wk e4).and ((wk e5).and (wk e6))))))
  obtain ⟨t, ht0, h1, h2, h3, h4, h5, h6⟩ := hall.exists
  obtain ⟨hSM⟩ := Dec2.footLocal_nonempty S
  exact ⟨t, ht0, ⟨{
    hS := hS, Sp := S, HBp := HBp, hκ := hκ, hM := hM, eps_pos := ht0, small1 := h5.le,
    c7le := h6.le, hS2 := hS2, SM := hSM, hM2 := hM2, hPmp := fun i _ _ => Finset.Subset.refl _,
    δ₁_pos := ht0, δ₁_le := h1.le, B_le := h2.le, B_one := h3.le, phi_lt := h4 }⟩⟩

/-- **`BlockMargin` for the trivial region `X₁ = ⊤`**: every site of the multiplier support that lies
in an interaction box of the cover has the margin. -/
theorem blockMargin_univ {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {Zα : Set (CTorus d L N₁ m₁ K)}
    (hcov : ∀ x ∈ Zα, x ∈ Gp.Ω 1 → ∃ z ∈ cubeIdx Gp, x ∈ intBox z) :
    BlockMargin Gp (Finset.univ : Finset (CTorus d L N₁ m₁ K)) Zα := by
  intro x hx hxΩ
  obtain ⟨z, hz, hxz⟩ := hcov x hx hxΩ
  refine ⟨z, hz, hxz, fun P _ hP => ?_, fun y _ => Finset.mem_univ _⟩
  unfold DecCover.parCubes at hP
  rw [Finset.mem_filter] at hP
  exact hP.2 (fun y _ => Finset.mem_univ y)

end Inhab

end Balaban.Localization

namespace Balaban.Fluctuation

/-- **`LocInt` is inhabited** (the empty expansion of the zero function). -/
theorem locInt_nonempty {Λ F ι : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ] (S : Set Λ)
    (XW : Set (F × F)) (Rσ : ℝ) (AgΘ : ι → Λ → Λ → Prop) (AgF : ι → F → F → Prop) :
    Nonempty (LocInt S XW Rσ (∅ : Finset ι) (fun _ _ _ _ _ => 0) (fun _ _ _ _ => 0) (fun _ => 0)
      AgΘ AgF) :=
  ⟨{ sum := fun _ _ _ _ _ _ => by simp
     analytic := fun _ hY => absurd hY (Finset.notMem_empty _)
     bound := fun _ hY => absurd hY (Finset.notMem_empty _)
     loc := fun _ hY => absurd hY (Finset.notMem_empty _)
     zero := fun _ hY => absurd hY (Finset.notMem_empty _) }⟩

end Balaban.Fluctuation
