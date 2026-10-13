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
`StepTowerRenSol.margins_of_le`).  After each theorem, an `example` checks that the landed
statement is the case `e = t`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover Filter Topology

/-- **The four margins of `StepTowerRen` at any radius `e ≤ t`** (same `r₀`). -/
theorem StepTowerRen.ren_margins_of_le {κmin : ℝ} (R : StepTowerRen κmin) {e : ℝ}
    (het : e ≤ R.t) :
    2 * (K4 3 3 2 R.BG R.κ * (xiC1 3 * e)) <
        deltaStar' 3 3 2 (famConst 3 3 R.BG R.κ) (gamma1 3 / 8) ∧
      2 * (K4 3 3 2 R.BG R.κ * (xiC1 3 * e)) + 3 * R.r₀ ≤ 1 ∧
      2 * (K4 3 3 2 R.BG R.κ * (xiC1 3 * e)) + 3 * R.r₀ ≤
        deltaStar' 3 3 2 (famConst 3 3 R.BG R.κ) (gamma1 3 / 8) ∧
      (3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * e * R.r₀ ≤
        deltaStar' 3 3 2 (famConst 3 3 R.BG R.κ) (gamma1 3 / 8) := by
  obtain ⟨hC₀⟩ := R.core
  have hK4 := K4_pos (L := 3) (N := 2) (κ := R.κ) hC₀.hS.fam.2.1 (by norm_num : 0 < 3)
  have hK1 := bgK1_pos 3 3 2
  have hX : 0 ≤ xiC1 3 := by unfold xiC1; positivity
  have hKX : 0 ≤ K4 3 3 2 R.BG R.κ * xiC1 3 := by positivity
  have hc : 0 ≤ 3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3) := by positivity
  have h1 : K4 3 3 2 R.BG R.κ * (xiC1 3 * e) ≤ K4 3 3 2 R.BG R.κ * (xiC1 3 * R.t) := by
    have := mul_le_mul_of_nonneg_left het hKX; linarith
  have h3 : (3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * e * R.r₀ ≤
      (3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * R.t * R.r₀ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left het hc) R.r₀_pos.le
  exact ⟨by linarith [R.ren_margin], by linarith [R.D₀_le_one], by linarith [R.D₀_le_star],
    h3.trans R.D₁_le_star⟩

/-- **The endpoint margin of `StepTowerRenEnd` at any radius `e ≤ t`** (same `r₀`). -/
theorem StepTowerRenEnd.end_margin_of_le {κmin : ℝ} (R : StepTowerRenEnd κmin) {e : ℝ}
    (het : e ≤ R.t) :
    cK2' 3 3 2 (famConst 3 3 R.BG R.κ) *
        ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * e * R.r₀) ≤
      c6 3 3 2 := by
  obtain ⟨hC₀⟩ := R.core
  have hd : 0 < 3 := by norm_num
  have hK4 := K4_pos (L := 3) (N := 2) (κ := R.κ) hC₀.hS.fam.2.1 hd
  have hK1 := bgK1_pos 3 3 2
  have hX : 0 ≤ xiC1 3 := by unfold xiC1; positivity
  have hB1 := famConst_ge_one (L := 3) hC₀.hS.fam.2.1 R.κ hd
  have hK2 : 0 ≤ cK2' 3 3 2 (famConst 3 3 R.BG R.κ) :=
    cK2'_nonneg (d := 3) (L := 3) (N := 2) (B := famConst 3 3 R.BG R.κ) (by linarith)
  have hc : 0 ≤ 3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3) := by positivity
  have h3 : (3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * e * R.r₀ ≤
      (3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * R.t * R.r₀ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left het hc) R.r₀_pos.le
  exact (mul_le_mul_of_nonneg_left h3 hK2).trans R.end_margin

/-- **The two constant inequalities at the shared class constant, at the bound `B = 8 e`**:
`1 ≤ renCK` and (CB) `K₂' b_* e ≤ renCK K₂ (8 e)`, for every `e ≥ 0`. -/
theorem StepTowerRen.renCK_facts_at {κmin : ℝ} (R : StepTowerRen κmin) {e : ℝ} (he : 0 ≤ e) :
    1 ≤ renCK 3 3 2 R.BG R.κ ∧
    cK2' 3 3 2 (famConst 3 3 R.BG R.κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * e) ≤
      renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * e) := by
  refine ⟨R.renCK_facts.1, ?_⟩
  have h := renCK_mul_ge (d := 3) (L := 3) (N := 2) (BG := R.BG) (κ := R.κ)
  have := mul_le_mul_of_nonneg_right h he
  linarith

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
  obtain ⟨-, h1, h2, h3⟩ := R.ren_margins_of_le het
  exact renDec_sharp (R.flCore_scale_mono k hk N₁ hN hν0 hν he het he het) R.r₀_pos R.r₀_le X₁
    h1 h2 h3

/-- The landed `renDec_sharp_scale_of_tower` is the case `e = t`. -/
example {κmin : ℝ} (R : StepTowerRen κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    (X₁ : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) :
    type_of% (renDec_sharp_scale_of_tower R k hk N₁ hN hν0 hν X₁) :=
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
  obtain ⟨hcK, hCB⟩ := R.renCK_facts_at he.le
  obtain ⟨-, h1, h2, h3⟩ := R.ren_margins_of_le het
  exact renDec_pertClass (R.flCore_scale_mono k hk N₁ hN hν0 hν he het he het) R.r₀_pos R.r₀_le X₁
    h1 h2 h3 (B := 8 * e) (cK := renCK 3 3 2 R.BG R.κ) (by positivity) hcK hCB

/-- The landed `renDec_pertClass_scale_of_tower` is the case `e = t`. -/
example {κmin : ℝ} (R : StepTowerRen κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    (X₁ : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) :
    type_of% (renDec_pertClass_scale_of_tower R k hk N₁ hN hν0 hν X₁) :=
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
  obtain ⟨-, h1, h2, h3⟩ := R.ren_margins_of_le het
  exact renDec_one_unique_sharp (R.flCore_scale_mono k hk N₁ hN hν0 hν he het he het) R.r₀_pos
    R.r₀_le X₁ hF hrF h1 h2 h3 (R.end_margin_of_le het)

/-- The landed `renDec_one_unique_sharp_scale_of_tower` is the case `e = t`. -/
example {κmin : ℝ} (R : StepTowerRenEnd κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    (X₁ : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) {rF B : ℝ}
    {F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
      ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ)}
    (hF : IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t R.t rF B F)
    (hrF : R.r₀ ≤ rF) :
    type_of% (renDec_one_unique_sharp_scale_of_tower R k hk N₁ hN hν0 hν X₁ hF hrF) :=
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
  have hC := R.flCore_scale_mono k hk N₁ hN hν0 hν he het he het
  have hHB := bgHyp_lv (k := k) R.m₁ hν0 hν
  obtain ⟨-, -, -, -, -, -, hK, hζ⟩ := R.margins_of_le het
  exact exists_isRenSol hHB he R.r₀_le hC.small1
    (hC.c7le.trans (c7_le_bgC1 3 3 2 R.BG R.κ)) hK hζ

/-- The landed `exists_isRenSol_scale_of_tower` is the case `e = t`. -/
example {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    type_of% (exists_isRenSol_scale_of_tower R k hk N₁ hN hν0 hν) :=
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
  obtain ⟨F, hF⟩ := exists_isRenSol_scale_of_tower_at R k hk N₁ hN hν0 hν he het
  obtain ⟨Fcut, h1, h2⟩ := renDec_one_unique_sharp_scale_of_tower_at R.toStepTowerRenEnd k hk N₁
    hN hν0 hν he het X₁ hF le_rfl
  exact ⟨F, Fcut, hF, h1, h2⟩

/-- The landed `renEndpoint_scale_of_tower` is the case `e = t`. -/
example {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    (X₁ : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) :
    type_of% (renEndpoint_scale_of_tower R k hk N₁ hN hν0 hν X₁) :=
  renEndpoint_scale_of_tower_at R k hk N₁ hN hν0 hν R.t_pos le_rfl X₁

end Balaban.Inhabited
