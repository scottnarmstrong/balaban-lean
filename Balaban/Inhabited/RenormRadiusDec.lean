/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRenSol
public import Balaban.Inhabited.StepTowerCoreMono
public import Balaban.Inhabited.StepTowerRadius
public import Balaban.Inhabited.RenormLocC2ZeroTower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Decoupling, solution map and endpoint at the tower for a class radius `e ≤ t`

The landed wrappers `renDec_sharp_scale_of_tower`, `renDec_pertClass_scale_of_tower`,
`renDec_one_unique_sharp_scale_of_tower`, `exists_isRenSol_scale_of_tower` and
`renEndpoint_scale_of_tower` are stated at the class radius `t` of the tower.  Here the same
statements are proved with the class radius `e`, for every `0 < e ≤ t`: the domain is
`XiCOneReal … ν e`, the lifted datum is `renZeta e ξ · Ψ` (in `renEdat ν e` and in
`IsRenSol … ν e e`), the bounds carry `e` in place of `t`, and the constant of Lemma 3.5 (ii) is
`B = 8 e`.  The polydisc radius `r₀`, the cut radius `exp κ`, the constants `K₄`, `K₁`, `K₂`,
`K₂'`, `renCK`, `rho4` and the generating sets are those of the tower.  No occurrence of `t` is
left in these five statements: every printed `t` of the landed ones is a renormalization radius.

The proofs re-invoke the abstract theorems (which take any positive `ε`) with the core of the tower
at the radii `(e, e)` (`StepTowerRen.flCore_scale_mono`) and the margins at `e`
(`StepTowerRen.ren_margins_of_le`, `StepTowerRenEnd.end_margin_of_le`,
`StepTowerRenSol.margins_of_le`).  After each `_at` theorem, the landed theorem of the same name without `_at` is stated and proved
as its corollary at `e = t`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover Filter Topology

section General

/-- **The four margins of `StepTowerRen` at any radius `e ≤ t`** (same `r₀`). -/
theorem StepTowerRenG.ren_margins_of_le {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenG d L N κmin) {e : ℝ}
    (het : e ≤ R.t) :
    2 * (K4 d L N R.BG R.κ * (xiC1 d * e)) <
        deltaStar' d L N (famConst d L R.BG R.κ) (gamma1 d / 8) ∧
      2 * (K4 d L N R.BG R.κ * (xiC1 d * e)) + 3 * R.r₀ ≤ 1 ∧
      2 * (K4 d L N R.BG R.κ * (xiC1 d * e)) + 3 * R.r₀ ≤
        deltaStar' d L N (famConst d L R.BG R.κ) (gamma1 d / 8) ∧
      (3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * e * R.r₀ ≤
        deltaStar' d L N (famConst d L R.BG R.κ) (gamma1 d / 8) := by
  obtain ⟨hC₀⟩ := R.core
  have hK4 := K4_pos (L := L) (N := N) (κ := R.κ) hC₀.hS.fam.2.1 (by have := R.hd; omega : 0 < d)
  have hK1 := bgK1_pos d L N
  have hX : 0 ≤ xiC1 d := by unfold xiC1; positivity
  have hKX : 0 ≤ K4 d L N R.BG R.κ * xiC1 d := by positivity
  have hc : 0 ≤ 3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d) := by positivity
  have h1 : K4 d L N R.BG R.κ * (xiC1 d * e) ≤ K4 d L N R.BG R.κ * (xiC1 d * R.t) := by
    have := mul_le_mul_of_nonneg_left het hKX; linarith
  have h3 : (3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * e * R.r₀ ≤
      (3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * R.t * R.r₀ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left het hc) R.r₀_pos.le
  exact ⟨by linarith [R.ren_margin], by linarith [R.D₀_le_one], by linarith [R.D₀_le_star],
    h3.trans R.D₁_le_star⟩

/-- **The endpoint margin of `StepTowerRenEnd` at any radius `e ≤ t`** (same `r₀`). -/
theorem StepTowerRenEndG.end_margin_of_le {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenEndG d L N κmin) {e : ℝ}
    (het : e ≤ R.t) :
    cK2' d L N (famConst d L R.BG R.κ) *
        ((3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * e * R.r₀) ≤
      c6 d L N := by
  obtain ⟨hC₀⟩ := R.core
  have hd : 0 < d := by have := R.hd; omega
  have hK4 := K4_pos (L := L) (N := N) (κ := R.κ) hC₀.hS.fam.2.1 hd
  have hK1 := bgK1_pos d L N
  have hX : 0 ≤ xiC1 d := by unfold xiC1; positivity
  have hB1 := famConst_ge_one (L := L) hC₀.hS.fam.2.1 R.κ hd
  have hK2 : 0 ≤ cK2' d L N (famConst d L R.BG R.κ) :=
    cK2'_nonneg (d := d) (L := L) (N := N) (B := famConst d L R.BG R.κ) (by linarith)
  have hc : 0 ≤ 3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d) := by positivity
  have h3 : (3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * e * R.r₀ ≤
      (3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * R.t * R.r₀ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left het hc) R.r₀_pos.le
  exact (mul_le_mul_of_nonneg_left h3 hK2).trans R.end_margin

/-- **The two constant inequalities at the shared class constant, at the bound `B = 8 e`**:
`1 ≤ renCK` and (CB) `K₂' b_* e ≤ renCK K₂ (8 e)`, for every `e ≥ 0`. -/
theorem StepTowerRenG.renCK_facts_at {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenG d L N κmin) {e : ℝ} (he : 0 ≤ e) :
    1 ≤ renCK d L N R.BG R.κ ∧
    cK2' d L N (famConst d L R.BG R.κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * e) ≤
      renCK d L N R.BG R.κ * cK2 d L N * (8 * e) := by
  refine ⟨R.renCK_facts.1, ?_⟩
  have h := renCK_mul_ge (d := d) (L := L) (N := N) (BG := R.BG) (κ := R.κ)
  have := mul_le_mul_of_nonneg_right h he
  linarith

/-- **`renDec_sharp` at every scale of the tower, at the class radius `e ≤ t`.** -/
theorem renDec_sharp_scale_of_towerG_at {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenG d L N κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    (X₁ : Set (CTorus d L N₁ R.m₁ (k + 1))) :
    ∃ F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) → (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) →
        (((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))).Ω 1 × Fin N → ℂ) × (((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))).Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ)) ×
          (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) => F p.1 p.2)
        (expDom (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) N, XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ →
        ∀ s ∈ polydisc (0 : RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ),
        ∀ (s' : DecParams (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))) (E : Edat (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) N),
          s' = extParams (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ (s ∘ (renLabelEquiv (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁).symm) →
          E = renEdat ν e D (decBgField (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (rho4 d L N R.BG R.κ) s' D)
            (decBgMult (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (rho4 d L N R.BG R.κ) s' D) ξ →
          (F (rawOf D, ξ) s).1 = dphi (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (decG (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν s') E.2.1 E.1
              (pertSource (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
          DecFixed (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν s' false E.2.1 E.1
              (pertSource (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
          Small (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (F (rawOf D, ξ) s).2 (c6' d L N (famConst d L R.BG R.κ) (gamma1 d / 8)) ∧
          Small (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (F (rawOf D, ξ) s).2 (cK2' d L N (famConst d L R.BG R.κ) *
            ((3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * e * ‖ξ‖)) ∧
          SupBounds (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (F (rawOf D, ξ) s).1 (cK2' d L N (famConst d L R.BG R.κ) *
            ((3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * e * ‖ξ‖)) ∧
          (ξ = 0 → (F (rawOf D, ξ) s).2 = 0 ∧ (F (rawOf D, ξ) s).1 = 0) := by
  obtain ⟨-, h1, h2, h3⟩ := R.ren_margins_of_le het
  exact renDec_sharp (R.toStepTowerG.flCore_scale_mono k hk N₁ hN hν0 hν he het he het) R.r₀_pos R.r₀_le X₁
    h1 h2 h3

/-- **`renDec_sharp` at every scale of the tower with margins**: no margin hypothesis is left. -/
theorem renDec_sharp_scale_of_towerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenG d L N κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (X₁ : Set (CTorus d L N₁ R.m₁ (k + 1))) :
    ∃ F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) → (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) →
        (((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))).Ω 1 × Fin N → ℂ) × (((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))).Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ)) ×
          (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) => F p.1 p.2)
        (expDom (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) N, XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ →
        ∀ s ∈ polydisc (0 : RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ),
        ∀ (s' : DecParams (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))) (E : Edat (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) N),
          s' = extParams (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ (s ∘ (renLabelEquiv (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁).symm) →
          E = renEdat ν R.t D (decBgField (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (rho4 d L N R.BG R.κ) s' D)
            (decBgMult (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (rho4 d L N R.BG R.κ) s' D) ξ →
          (F (rawOf D, ξ) s).1 = dphi (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (decG (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν s') E.2.1 E.1
              (pertSource (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
          DecFixed (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν s' false E.2.1 E.1
              (pertSource (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
          Small (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (F (rawOf D, ξ) s).2 (c6' d L N (famConst d L R.BG R.κ) (gamma1 d / 8)) ∧
          Small (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (F (rawOf D, ξ) s).2 (cK2' d L N (famConst d L R.BG R.κ) *
            ((3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * R.t * ‖ξ‖)) ∧
          SupBounds (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (F (rawOf D, ξ) s).1 (cK2' d L N (famConst d L R.BG R.κ) *
            ((3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * R.t * ‖ξ‖)) ∧
          (ξ = 0 → (F (rawOf D, ξ) s).2 = 0 ∧ (F (rawOf D, ξ) s).1 = 0) :=
  renDec_sharp_scale_of_towerG_at R k hk N₁ hN hν0 hν R.t_pos le_rfl X₁

/-- **`renDec_pertClass` at every scale of the tower, at the class radius `e ≤ t`**, at the
shared constant `c_K = renCK` and `B = 8 e`: the constant inequality (CB) is `renCK_mul_ge` times
`e`. -/
theorem renDec_pertClass_scale_of_towerG_at {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenG d L N κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    (X₁ : Set (CTorus d L N₁ R.m₁ (k + 1))) :
    ∃ F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) × ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ)) ×
          (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) => F p.1 p.2)
        (expDom (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) N,
        XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < R.r₀ →
        ∀ s ∈ polydisc (0 : RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ)
          (fun _ => Real.exp R.κ),
          SupBounds (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (F (rawOf D, ξ) s).1
            (renCK d L N R.BG R.κ * (cK2 d L N * (8 * e * ‖ξ‖))) ∧
          ((F (rawOf D, ξ) s).1,
            decBgMult (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (rho4 d L N R.BG R.κ)
              (extParams (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁
                (s ∘ (renLabelEquiv (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁).symm)) D +
              (F (rawOf D, ξ) s).2) ∈
            pertClass (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
              (renCK d L N R.BG R.κ * (cK2 d L N * (8 * e * ‖ξ‖)))
              (bgK1 d L N * (xiC1 d * e) + renCK d L N R.BG R.κ * cK2 d L N * (8 * e) * R.r₀ + 2)
              (renMassU ν ξ) := by
  obtain ⟨hcK, hCB⟩ := R.renCK_facts_at he.le
  obtain ⟨-, h1, h2, h3⟩ := R.ren_margins_of_le het
  exact renDec_pertClass (R.toStepTowerG.flCore_scale_mono k hk N₁ hN hν0 hν he het he het) R.r₀_pos R.r₀_le X₁
    h1 h2 h3 (B := 8 * e) (cK := renCK d L N R.BG R.κ) (by positivity) hcK hCB

/-- **`renDec_pertClass` at every scale of the tower** at the shared constant `c_K = renCK` and
`B = 8 t`: the constant inequality (CB) is `renCK_mul_ge` times `t`. -/
theorem renDec_pertClass_scale_of_towerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenG d L N κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (X₁ : Set (CTorus d L N₁ R.m₁ (k + 1))) :
    ∃ F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) × ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ)) ×
          (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) => F p.1 p.2)
        (expDom (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) N,
        XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < R.r₀ →
        ∀ s ∈ polydisc (0 : RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ)
          (fun _ => Real.exp R.κ),
          SupBounds (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (F (rawOf D, ξ) s).1
            (renCK d L N R.BG R.κ * (cK2 d L N * (8 * R.t * ‖ξ‖))) ∧
          ((F (rawOf D, ξ) s).1,
            decBgMult (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (rho4 d L N R.BG R.κ)
              (extParams (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁
                (s ∘ (renLabelEquiv (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁).symm)) D +
              (F (rawOf D, ξ) s).2) ∈
            pertClass (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
              (renCK d L N R.BG R.κ * (cK2 d L N * (8 * R.t * ‖ξ‖)))
              (bgK1 d L N * (xiC1 d * R.t) + renCK d L N R.BG R.κ * cK2 d L N * (8 * R.t) * R.r₀ + 2)
              (renMassU ν ξ) :=
  renDec_pertClass_scale_of_towerG_at R k hk N₁ hN hν0 hν R.t_pos le_rfl X₁

/-- **`renDec_one_unique_sharp` at every scale of the tower, at the class radius `e ≤ t`**: the
cut family at `s = 1` is the renormalized solution `F` at the radius `e` (any `IsRenSol … e e`
solution map of radius `rF ≥ r₀`). -/
theorem renDec_one_unique_sharp_scale_of_towerG_at {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenEndG d L N κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    (X₁ : Set (CTorus d L N₁ R.m₁ (k + 1))) {rF B : ℝ}
    {F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
      ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) × ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ)}
    (hF : IsRenSol (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e e rF B F)
    (hrF : R.r₀ ≤ rF) :
    ∃ Fcut : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) × ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ)) ×
          (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) => Fcut p.1 p.2)
        (expDom (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) N,
        XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ) := by
  obtain ⟨-, h1, h2, h3⟩ := R.ren_margins_of_le het
  exact renDec_one_unique_sharp (R.toStepTowerG.flCore_scale_mono k hk N₁ hN hν0 hν he het he het) R.r₀_pos
    R.r₀_le X₁ hF hrF h1 h2 h3 (R.end_margin_of_le het)

/-- **`renDec_one_unique_sharp` at every scale of the tower with the endpoint margin**: the cut
family at `s = 1` is the renormalized solution `F` (any `IsRenSol` solution map of radius
`rF ≥ r₀`), with no margin hypothesis. -/
theorem renDec_one_unique_sharp_scale_of_towerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenEndG d L N κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (X₁ : Set (CTorus d L N₁ R.m₁ (k + 1))) {rF B : ℝ}
    {F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
      ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) × ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ)}
    (hF : IsRenSol (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t R.t rF B F)
    (hrF : R.r₀ ≤ rF) :
    ∃ Fcut : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) × ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ)) ×
          (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) => Fcut p.1 p.2)
        (expDom (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) N,
        XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ) :=
  renDec_one_unique_sharp_scale_of_towerG_at R k hk N₁ hN hν0 hν R.t_pos le_rfl X₁ hF hrF

/-- **`IsRenSol` at every scale of the tower, at the class radius `e ≤ t`**: the renormalized
solution with lifted datum `renZeta e ξ · Ψ` on the class of radius `e`, at radius `r₀` and bound
`B = 8 e`. -/
theorem exists_isRenSol_scale_of_towerG_at {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenSolG d L N κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t) :
    ∃ F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
      ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) × ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e e R.r₀
        (8 * e) F := by
  have hC := R.toStepTowerG.flCore_scale_mono k hk N₁ hN hν0 hν he het he het
  have hHB := bgHyp_lvG (k := k) R.hd R.hL (bgR0_le_rhoSepG R.m₁ R.hd R.hL) hν0 hν
  obtain ⟨-, -, -, -, -, -, hK, hζ⟩ := R.margins_of_le het
  exact exists_isRenSol hHB he R.r₀_le hC.small1
    (hC.c7le.trans (c7_le_bgC1 d L N R.BG R.κ)) hK hζ

/-- **`IsRenSol` at every scale of the tower**: the renormalized solution at radius `r₀` and
bound `B = 8 t`. -/
theorem exists_isRenSol_scale_of_towerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenSolG d L N κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) :
    ∃ F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
      ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) × ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t R.t R.r₀
        (8 * R.t) F :=
  exists_isRenSol_scale_of_towerG_at R k hk N₁ hN hν0 hν R.t_pos le_rfl

/-- **The endpoint at every scale of the tower, at the class radius `e ≤ t`**: one solution map
`F` of `IsRenSol … e e r₀ (8 e)` and the cut family whose value at `s = 1` is `F`. -/
theorem renEndpoint_scale_of_towerG_at {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenSolG d L N κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    (X₁ : Set (CTorus d L N₁ R.m₁ (k + 1))) :
    ∃ (F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) × ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ))
      (Fcut : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) × ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ)),
      IsRenSol (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e e R.r₀
        (8 * e) F ∧
      AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ)) ×
          (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) => Fcut p.1 p.2)
        (expDom (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) N,
        XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν e D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ) := by
  obtain ⟨F, hF⟩ := exists_isRenSol_scale_of_towerG_at R k hk N₁ hN hν0 hν he het
  obtain ⟨Fcut, h1, h2⟩ := renDec_one_unique_sharp_scale_of_towerG_at R.toStepTowerRenEndG k hk N₁
    hN hν0 hν he het X₁ hF le_rfl
  exact ⟨F, Fcut, hF, h1, h2⟩

/-- **The endpoint at every scale of the tower with the solution margins**: no hypothesis besides
the tower and the scale conditions. -/
theorem renEndpoint_scale_of_towerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenSolG d L N κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (X₁ : Set (CTorus d L N₁ R.m₁ (k + 1))) :
    ∃ (F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) × ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ))
      (Fcut : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) × ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ)),
      IsRenSol (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t R.t R.r₀
        (8 * R.t) F ∧
      AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ)) ×
          (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) => Fcut p.1 p.2)
        (expDom (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) N,
        XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ) :=
  renEndpoint_scale_of_towerG_at R k hk N₁ hN hν0 hν R.t_pos le_rfl X₁

end General

/-- **The four margins of `StepTowerRen` at any radius `e ≤ t`** (same `r₀`). -/
theorem StepTowerRen.ren_margins_of_le {κmin : ℝ} (R : StepTowerRen κmin) {e : ℝ}
    (het : e ≤ R.t) :
    2 * (K4 3 3 2 R.BG R.κ * (xiC1 3 * e)) <
        deltaStar' 3 3 2 (famConst 3 3 R.BG R.κ) (gamma1 3 / 8) ∧
      2 * (K4 3 3 2 R.BG R.κ * (xiC1 3 * e)) + 3 * R.r₀ ≤ 1 ∧
      2 * (K4 3 3 2 R.BG R.κ * (xiC1 3 * e)) + 3 * R.r₀ ≤
        deltaStar' 3 3 2 (famConst 3 3 R.BG R.κ) (gamma1 3 / 8) ∧
      (3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * e * R.r₀ ≤
        deltaStar' 3 3 2 (famConst 3 3 R.BG R.κ) (gamma1 3 / 8) :=
  R.toG.ren_margins_of_le het

/-- **The endpoint margin of `StepTowerRenEnd` at any radius `e ≤ t`** (same `r₀`). -/
theorem StepTowerRenEnd.end_margin_of_le {κmin : ℝ} (R : StepTowerRenEnd κmin) {e : ℝ}
    (het : e ≤ R.t) :
    cK2' 3 3 2 (famConst 3 3 R.BG R.κ) *
        ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * e * R.r₀) ≤
      c6 3 3 2 :=
  R.toG.end_margin_of_le het

/-- **The two constant inequalities at the shared class constant, at the bound `B = 8 e`**:
`1 ≤ renCK` and (CB) `K₂' b_* e ≤ renCK K₂ (8 e)`, for every `e ≥ 0`. -/
theorem StepTowerRen.renCK_facts_at {κmin : ℝ} (R : StepTowerRen κmin) {e : ℝ} (he : 0 ≤ e) :
    1 ≤ renCK 3 3 2 R.BG R.κ ∧
    cK2' 3 3 2 (famConst 3 3 R.BG R.κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * e) ≤
      renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * e) :=
  R.toG.renCK_facts_at he

/-- **`renDec_sharp` at every scale of the tower, at the class radius `e ≤ t`.** -/
theorem renDec_sharp_scale_of_tower_at {κmin : ℝ} (R : StepTowerRen κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    (X₁ : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) → (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) →
        (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2 → ℂ) × (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ)) ×
          (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) => F p.1 p.2)
        (expDom (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2, XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ →
        ∀ s ∈ polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ),
        ∀ (s' : DecParams (lvTop N₁ R.m₁ k (rhoSep R.m₁))) (E : Edat (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2),
          s' = extParams (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ (s ∘ (renLabelEquiv (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁).symm) →
          E = renEdat ν e D (decBgField (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (rho4 3 3 2 R.BG R.κ) s' D)
            (decBgMult (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (rho4 3 3 2 R.BG R.κ) s' D) ξ →
          (F (rawOf D, ξ) s).1 = dphi (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (decG (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν s') E.2.1 E.1
              (pertSource (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
          DecFixed (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν s' false E.2.1 E.1
              (pertSource (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
          Small (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (F (rawOf D, ξ) s).2 (c6' 3 3 2 (famConst 3 3 R.BG R.κ) (gamma1 3 / 8)) ∧
          Small (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (F (rawOf D, ξ) s).2 (cK2' 3 3 2 (famConst 3 3 R.BG R.κ) *
            ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * e * ‖ξ‖)) ∧
          SupBounds (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (F (rawOf D, ξ) s).1 (cK2' 3 3 2 (famConst 3 3 R.BG R.κ) *
            ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * e * ‖ξ‖)) ∧
          (ξ = 0 → (F (rawOf D, ξ) s).2 = 0 ∧ (F (rawOf D, ξ) s).1 = 0) := by
  have h := renDec_sharp_scale_of_towerG_at R.toG k hk N₁ hN hν0 (by simpa using hν) he het X₁
  rw [rhoSepG_three] at h
  exact h

/-- **`renDec_sharp` at every scale of the tower with margins**: no margin hypothesis is left. -/
theorem renDec_sharp_scale_of_tower {κmin : ℝ} (R : StepTowerRen κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (X₁ : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) → (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) →
        (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2 → ℂ) × (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ)) ×
          (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) => F p.1 p.2)
        (expDom (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2, XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ →
        ∀ s ∈ polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ),
        ∀ (s' : DecParams (lvTop N₁ R.m₁ k (rhoSep R.m₁))) (E : Edat (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2),
          s' = extParams (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ (s ∘ (renLabelEquiv (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁).symm) →
          E = renEdat ν R.t D (decBgField (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (rho4 3 3 2 R.BG R.κ) s' D)
            (decBgMult (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (rho4 3 3 2 R.BG R.κ) s' D) ξ →
          (F (rawOf D, ξ) s).1 = dphi (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (decG (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν s') E.2.1 E.1
              (pertSource (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
          DecFixed (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν s' false E.2.1 E.1
              (pertSource (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
          Small (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (F (rawOf D, ξ) s).2 (c6' 3 3 2 (famConst 3 3 R.BG R.κ) (gamma1 3 / 8)) ∧
          Small (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (F (rawOf D, ξ) s).2 (cK2' 3 3 2 (famConst 3 3 R.BG R.κ) *
            ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * R.t * ‖ξ‖)) ∧
          SupBounds (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (F (rawOf D, ξ) s).1 (cK2' 3 3 2 (famConst 3 3 R.BG R.κ) *
            ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * R.t * ‖ξ‖)) ∧
          (ξ = 0 → (F (rawOf D, ξ) s).2 = 0 ∧ (F (rawOf D, ξ) s).1 = 0) :=
  renDec_sharp_scale_of_tower_at R k hk N₁ hN hν0 hν R.t_pos le_rfl X₁

/-- **`renDec_pertClass` at every scale of the tower, at the class radius `e ≤ t`**, at the
shared constant `c_K = renCK` and `B = 8 e`: the constant inequality (CB) is `renCK_mul_ge` times
`e`. -/
theorem renDec_pertClass_scale_of_tower_at {κmin : ℝ} (R : StepTowerRen κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    (X₁ : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ)) ×
          (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) => F p.1 p.2)
        (expDom (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2,
        XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < R.r₀ →
        ∀ s ∈ polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ)
          (fun _ => Real.exp R.κ),
          SupBounds (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (F (rawOf D, ξ) s).1
            (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * e * ‖ξ‖))) ∧
          ((F (rawOf D, ξ) s).1,
            decBgMult (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (rho4 3 3 2 R.BG R.κ)
              (extParams (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁
                (s ∘ (renLabelEquiv (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁).symm)) D +
              (F (rawOf D, ξ) s).2) ∈
            pertClass (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * e * ‖ξ‖)))
              (bgK1 3 3 2 * (xiC1 3 * e) + renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * e) * R.r₀ + 2)
              (renMassU ν ξ) := by
  have h := renDec_pertClass_scale_of_towerG_at R.toG k hk N₁ hN hν0 (by simpa using hν) he het X₁
  rw [rhoSepG_three] at h
  exact h

/-- **`renDec_pertClass` at every scale of the tower** at the shared constant `c_K = renCK` and
`B = 8 t`: the constant inequality (CB) is `renCK_mul_ge` times `t`. -/
theorem renDec_pertClass_scale_of_tower {κmin : ℝ} (R : StepTowerRen κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (X₁ : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ)) ×
          (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) => F p.1 p.2)
        (expDom (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2,
        XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < R.r₀ →
        ∀ s ∈ polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ)
          (fun _ => Real.exp R.κ),
          SupBounds (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (F (rawOf D, ξ) s).1
            (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * R.t * ‖ξ‖))) ∧
          ((F (rawOf D, ξ) s).1,
            decBgMult (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (rho4 3 3 2 R.BG R.κ)
              (extParams (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁
                (s ∘ (renLabelEquiv (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁).symm)) D +
              (F (rawOf D, ξ) s).2) ∈
            pertClass (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * R.t * ‖ξ‖)))
              (bgK1 3 3 2 * (xiC1 3 * R.t) + renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * R.t) * R.r₀ + 2)
              (renMassU ν ξ) :=
  renDec_pertClass_scale_of_tower_at R k hk N₁ hN hν0 hν R.t_pos le_rfl X₁

/-- **`renDec_one_unique_sharp` at every scale of the tower, at the class radius `e ≤ t`**: the
cut family at `s = 1` is the renormalized solution `F` at the radius `e` (any `IsRenSol … e e`
solution map of radius `rF ≥ r₀`). -/
theorem renDec_one_unique_sharp_scale_of_tower_at {κmin : ℝ} (R : StepTowerRenEnd κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    (X₁ : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) {rF B : ℝ}
    {F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
      ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ)}
    (hF : IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e e rF B F)
    (hrF : R.r₀ ≤ rF) :
    ∃ Fcut : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ)) ×
          (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) => Fcut p.1 p.2)
        (expDom (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2,
        XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ) := by
  revert hrF hF F rF B
  rw [← rhoSepG_three (m₁ := R.m₁)]
  intro rF B F hF hrF
  exact renDec_one_unique_sharp_scale_of_towerG_at R.toG k hk N₁ hN hν0 (by simpa using hν) he het
    X₁ hF hrF

/-- **`renDec_one_unique_sharp` at every scale of the tower with the endpoint margin**: the cut
family at `s = 1` is the renormalized solution `F` (any `IsRenSol` solution map of radius
`rF ≥ r₀`), with no margin hypothesis. -/
theorem renDec_one_unique_sharp_scale_of_tower {κmin : ℝ} (R : StepTowerRenEnd κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (X₁ : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) {rF B : ℝ}
    {F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
      ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ)}
    (hF : IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t R.t rF B F)
    (hrF : R.r₀ ≤ rF) :
    ∃ Fcut : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ)) ×
          (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) => Fcut p.1 p.2)
        (expDom (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2,
        XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ) :=
  renDec_one_unique_sharp_scale_of_tower_at R k hk N₁ hN hν0 hν R.t_pos le_rfl X₁ hF hrF

/-- **`IsRenSol` at every scale of the tower, at the class radius `e ≤ t`**: the renormalized
solution with lifted datum `renZeta e ξ · Ψ` on the class of radius `e`, at radius `r₀` and bound
`B = 8 e`. -/
theorem exists_isRenSol_scale_of_tower_at {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
      ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e e R.r₀
        (8 * e) F := by
  have h := exists_isRenSol_scale_of_towerG_at R.toG k hk N₁ hN hν0 (by simpa using hν) he het
  rw [rhoSepG_three] at h
  exact h

/-- **`IsRenSol` at every scale of the tower**: the renormalized solution at radius `r₀` and
bound `B = 8 t`. -/
theorem exists_isRenSol_scale_of_tower {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
      ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t R.t R.r₀
        (8 * R.t) F :=
  exists_isRenSol_scale_of_tower_at R k hk N₁ hN hν0 hν R.t_pos le_rfl

/-- **The endpoint at every scale of the tower, at the class radius `e ≤ t`**: one solution map
`F` of `IsRenSol … e e r₀ (8 e)` and the cut family whose value at `s = 1` is `F`. -/
theorem renEndpoint_scale_of_tower_at {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    (X₁ : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) :
    ∃ (F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ))
      (Fcut : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ)),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e e R.r₀
        (8 * e) F ∧
      AnalyticOnNhd ℂ (fun p : (RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ)) ×
          (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) => Fcut p.1 p.2)
        (expDom (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2,
        XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ) := by
  have h := renEndpoint_scale_of_towerG_at R.toG k hk N₁ hN hν0 (by simpa using hν) he het X₁
  rw [rhoSepG_three] at h
  exact h

/-- **The endpoint at every scale of the tower with the solution margins**: no hypothesis besides
the tower and the scale conditions. -/
theorem renEndpoint_scale_of_tower {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (X₁ : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) :
    ∃ (F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ))
      (Fcut : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ)),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t R.t R.r₀
        (8 * R.t) F ∧
      AnalyticOnNhd ℂ (fun p : (RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ)) ×
          (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) => Fcut p.1 p.2)
        (expDom (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2,
        XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ) :=
  renEndpoint_scale_of_tower_at R k hk N₁ hN hν0 hν R.t_pos le_rfl X₁

end Balaban.Inhabited
