/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedDecBall
public import Balaban.Fluctuation.MarkedFluctRows
public import Balaban.Fluctuation.MarkedHatRows
public import Balaban.Fluctuation.HatEngineFan
public import Balaban.Fluctuation.ScaleUniform
public import Balaban.Fluctuation.Prop33SymmV
public import Balaban.Inhabited.MarkedSharpCountWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Instances of the fan-level theorems at the zero-class witness step

PLACEHOLDER DOC (replaced below).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6

set_option hygiene false in
/-- Local tactic: the tower data of `tower_core_fixed` and `tower_C_items` shared by the instances
(names `m₁ c BG κ t c₂ BG₂ κdec κ0 δc δ hC hMX hdm hα hsmX hκpos β₀t hβ₀t hitems`). -/
local macro "fan_setup" : tactic => `(tactic| (
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0⟩ := tower_core_fixed 2
  have hκdec0 : 0 ≤ κdec := by linarith
  have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  have hκpos : 0 < κ := by
    have : 0 < κdec := by linarith
    have h5 : (0 : ℝ) < 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec := by positivity
    linarith
  obtain ⟨β₀t, hβ₀t, hitems⟩ := tower_C_items (A₁ := 1) one_pos 2 m₁ h4 hbig κ ht0 hδ hsm hδ'0
    hδ'a hδ'b hδ'c))

open Classical in
/-- **Instance of `hatPsiF_mem_flBallLC` at the witness step.** -/
theorem fanChain_ball :
    ∃ (m₁ : ℕ) (BG κ t δ β₀ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < κ ∧
      ∀ β : ℝ, β₀ ≤ β → ∃ cψ : ℝ, 0 < cψ ∧
        XiCData (wStep m₁ β δ).G' (compWeight 3 1) nuW (1 + 1) 1 t (wStep m₁ β δ).D' ∧
        (∃ s : DecParams (wStep m₁ β δ).G', ∀ P, ‖s P‖ < Real.exp κ) ∧
        ∃ F₁ : DecParams (wStep m₁ β δ).G' × RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2 →
            ((wStep m₁ β δ).G'.Ω 1 × Fin 2 → ℂ) × ((wStep m₁ β δ).G'.Ω 1 → ℂ),
          F1Spec (wStep m₁ β δ).G' 1 nuW BG κ F₁ ∧
          ∀ s : DecParams (wStep m₁ β δ).G', (∀ P, ‖s P‖ < Real.exp κ) →
            ∀ D : BgData (wStep m₁ β δ).G' 2, XiCData (wStep m₁ β δ).G' (compWeight 3 1) nuW
              (1 + 1) 1 t D → ∀ ψh : unitPts (wStep m₁ β δ).G' × Fin 2 → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
            hatPsiF (wStep m₁ β δ).G' 1 nuW (wStep m₁ β δ).hG'
              ((((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) F₁ s (rawOf D) ψh ∈
              FlBallLC (Hm m₁ (rhoSep m₁)) t := by
  classical
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0⟩ := tower_core_fixed 2
  have hκdec0 : 0 ≤ κdec := by linarith
  have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  have hκpos : 0 < κ := by
    have : 0 < κdec := by linarith
    have h5 : (0 : ℝ) < 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec := by positivity
    linarith
  obtain ⟨β₀t, hβ₀t, hitems⟩ := tower_C_items (A₁ := 1) one_pos 2 m₁ h4 hbig κ ht0 hδ hsm hδ'0
    hδ'a hδ'b hδ'c
  refine ⟨m₁, BG, κ, t, δ, β₀t, hβ₀t, ht0, hκpos, ?_⟩
  intro β hβ
  obtain ⟨hp, hcψ0, hr0, hδ₁, hc, hlt, ⟨R0⟩⟩ := hitems β hβ
  have hxi1 : xiC1 3 * t ≤ 1 := by
    have h1 := hC.c7le
    have h2 := c7_le_bgC1 3 3 2 BG κ
    have h3 := bgC1_le_small 3 3 2 (by norm_num)
    linarith
  have hD : XiCData (wStep m₁ β δ).G' (compWeight 3 1) nuW (1 + 1) 1 t (wStep m₁ β δ).D' := by
    refine ⟨fun _ => unitVec hN2, unitVec hN2, 0, 0,
      exists_xiC (bgHypNu m₁) (Gp m₁ (rhoSep m₁)) hN2 (by unfold nuW; norm_num) ht0, ?_, ?_⟩
    · intro x hx i
      have := unitBg_Ψ_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)).Ψ x i = _
      rw [this]; simp
    · intro x hx i
      have := unitBg_h_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)).h x i = _
      rw [this]; simp
  obtain ⟨F₁, hF₁⟩ := f1Spec_exists hC
  refine ⟨towerCpsi κ t β, hcψ0, hD, ⟨fun _ => 1, fun P => ?_⟩, F₁, hF₁, ?_⟩
  · simpa using Real.one_lt_exp_iff.2 hκpos
  · intro s hs D hDD ψh hψh
    exact hatPsiF_mem_flBallLC hC le_rfl isLevel_Hm (wStep m₁ β δ).hG' _ hcψ0.le hMX hdm hα hsmX
      hδ₁ hF₁ hs hDD hψh

open Classical in
/-- **Instance of `markedHatPsiF_mem_flBallLC` at the witness step.**  The hat variable is bounded
by the cutoff `p₁ = pLog 1 2 β`; the marked parameters range over `|u| ≤ 2` and `|t| ≤ t₁` with
`t₁ = 8 p₁ / c_ψ > 0` (so a non-trivial disc of `t`), where the radius inequality is the one of
`marked_radius_and_derivative_at_witness`. -/
theorem fanChain_markedBall :
    ∃ (m₁ : ℕ) (BG κ t δ β₀ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < κ ∧
      ∀ β : ℝ, β₀ ≤ β → ∃ t₁ : ℝ, 0 < t₁ ∧
        ∃ F₁ : DecParams (wStep m₁ β δ).G' × RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2 →
            ((wStep m₁ β δ).G'.Ω 1 × Fin 2 → ℂ) × ((wStep m₁ β δ).G'.Ω 1 → ℂ),
          F1Spec (wStep m₁ β δ).G' 1 nuW BG κ F₁ ∧
          ∀ (z : Torus 3 (9 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))),
          ∀ s : DecParams (wStep m₁ β δ).G', (∀ P, ‖s P‖ < Real.exp κ) →
            ∀ D : BgData (wStep m₁ β δ).G' 2, XiCData (wStep m₁ β δ).G' (compWeight 3 1) nuW
              (1 + 1) 1 t D → ∀ ψh : unitPts (wStep m₁ β δ).G' × Fin 2 → ℂ,
              (∀ p, ‖ψh p‖ ≤ pLog 1 2 β) → ∀ u τ : ℂ, ‖u‖ ≤ 2 → ‖τ‖ ≤ t₁ →
            markedHatPsiF (wStep m₁ β δ).a₁ (wStep m₁ β δ).ν (wStep m₁ β δ).hG'
              ((((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) F₁
              ((wStep m₁ β δ).blockU z) u τ s (rawOf D) ψh ∈
              FlBallLC (Hm m₁ (rhoSep m₁)) t := by
  classical
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0⟩ := tower_core_fixed 2
  have hκdec0 : 0 ≤ κdec := by linarith
  have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  have hκpos : 0 < κ := by
    have : 0 < κdec := by linarith
    have h5 : (0 : ℝ) < 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec := by positivity
    linarith
  obtain ⟨β₀t, hβ₀t, hitems⟩ := tower_C_items (A₁ := 1) one_pos 2 m₁ h4 hbig κ ht0 hδ hsm hδ'0
    hδ'a hδ'b hδ'c
  refine ⟨m₁, BG, κ, t, δ, β₀t, hβ₀t, ht0, hκpos, ?_⟩
  intro β hβ
  obtain ⟨hp, hcψ0, hr0, hδ₁, hc, hlt, ⟨R0⟩⟩ := hitems β hβ
  obtain ⟨F₁, hF₁⟩ := f1Spec_exists hC
  set p₁ := pLog 1 2 β with hp₁def
  set cψ := towerCpsi κ t β with hcψdef
  set W : ℝ := Real.sqrt ((2 : ℕ) : ℝ) *
    (‖(((hatStep m₁ β p₁ δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) 1) κ) with hW
  have ha : 0 < compWeight 3 (1 : ℝ) 1 :=
    lt_of_lt_of_le (by norm_num) (hC.HBp.weights 1 le_rfl (by norm_num)).1
  have hCs := covSupConstC_nonneg (N := 2) (d := 3) (L := 3) (by norm_num) (by norm_num) ha κ
  have hW0 : 0 ≤ W := by
    rw [hW]; positivity
  have hWc : W * cψ < t := by rw [hW]; nlinarith [hδ₁]
  set t₁ : ℝ := 8 * p₁ / cψ with ht₁
  have ht₁0 : 0 < t₁ := by positivity
  have hmain : (2 + towerR κ t β p₁) * (2 + t₁) * p₁ ≤ cψ := by
    have e : (2 + towerR κ t β p₁) * (2 + t₁) * p₁ = cψ - 16 * p₁ ^ 2 / cψ := by
      unfold towerR
      rw [ht₁]
      field_simp
      ring
    rw [e]
    have : 0 ≤ 16 * p₁ ^ 2 / cψ := by positivity
    linarith
  have hrad : (2 + t₁) * (W * p₁) < t := by
    have hr' : 0 ≤ towerR κ t β p₁ := hr0.le
    have h2 : (2 + t₁) * (W * p₁) ≤ (2 + towerR κ t β p₁) * (2 + t₁) * (W * p₁) := by
      have : 0 ≤ (2 + t₁) * (W * p₁) := by positivity
      have h3 : 1 ≤ 2 + towerR κ t β p₁ := by linarith
      calc (2 + t₁) * (W * p₁) = 1 * ((2 + t₁) * (W * p₁)) := by ring
        _ ≤ (2 + towerR κ t β p₁) * ((2 + t₁) * (W * p₁)) := mul_le_mul_of_nonneg_right h3 this
        _ = _ := by ring
    refine lt_of_le_of_lt h2 ?_
    calc (2 + towerR κ t β p₁) * (2 + t₁) * (W * p₁)
        = ((2 + towerR κ t β p₁) * (2 + t₁) * p₁) * W := by ring
      _ ≤ cψ * W := mul_le_mul_of_nonneg_right hmain hW0
      _ = W * cψ := by ring
      _ < t := hWc
  refine ⟨t₁, ht₁0, F₁, hF₁, ?_⟩
  intro z s hs D hDD ψh hψh u τ hu hτ
  refine markedHatPsiF_mem_flBallLC hC le_rfl isLevel_Hm (wStep m₁ β δ).hG' _ (cψ := p₁) hp.le
    hMX hdm hα hsmX hF₁ hs hDD hψh _ ?_
  have hn : ‖u‖ + ‖τ‖ ≤ 2 + t₁ := add_le_add hu hτ
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right hn (by have := hp.le; positivity)) ?_
  have e : Real.sqrt ((2 : ℕ) : ℝ) *
      (‖(((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
        (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) 1) κ * p₁)) = W * p₁ := by
    rw [hW]; ring
  rw [e]; exact hrad


section Geometry

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- On a whole-lattice generating set the whole torus is a nearest-neighbour component of the
decoupling region `V(∅) = X₁ = univ`. -/
theorem fanChain_isNnComp_univ (hG : IsLevel Gp (k + 1)) :
    IsNnComp (((Vset (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))) ∅).filter
      fun x => x ∈ Gp.Ω 1)) Finset.univ := by
  classical
  have hfil : ((Vset (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))) ∅).filter
      fun x => x ∈ Gp.Ω 1) = Finset.univ := by
    ext x
    simp [Vset, hG.Ω_one]
  rw [hfil]
  exact ⟨subset_rfl, fun _ _ y _ _ => Finset.mem_univ y⟩

theorem fanChain_cellUnion_univ :
    IsCellUnion (L ^ (k + 1)) ((Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))) :
      Set (CTorus d L N₁ m₁ (k + 1))) :=
  fun _ _ y _ => by simp

/-- No parameter cube meets the complement of `X₁ = univ`: the cut is the constant `1`. -/
theorem fanChain_parCubes_univ :
    parCubes Gp (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))) = ∅ := by
  classical
  ext P
  simp [parCubes]

end Geometry

open Classical in
/-- **Instances of `hatPsiF_rows` and `markedHatPsiF_rows` at the witness step** (whole torus:
`N₁ = 9`, `X₁ = Y = univ`, no marked cubes, the cut `s ≡ 1`).  Reflexive: on the whole torus the
agreement hypotheses force the two configurations to coincide. -/
theorem fanChain_rows :
    ∃ (m₁ : ℕ) (BG κ t δ β₀ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < κ ∧
      ∀ β : ℝ, β₀ ≤ β → ∃ F₁ : DecParams (wStep m₁ β δ).G' × RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2 →
            ((wStep m₁ β δ).G'.Ω 1 × Fin 2 → ℂ) × ((wStep m₁ β δ).G'.Ω 1 → ℂ),
          F1Spec (wStep m₁ β δ).G' 1 nuW BG κ F₁ ∧
          ∀ D D' : BgData (wStep m₁ β δ).G' 2,
            XiCData (wStep m₁ β δ).G' (compWeight 3 1) nuW (1 + 1) 1 t D →
            XiCData (wStep m₁ β δ).G' (compWeight 3 1) nuW (1 + 1) 1 t D' →
            (∀ z, D.Ψ z = D'.Ψ z ∧ (z ∈ (wStep m₁ β δ).G'.Ω 1 → D.h z = D'.h z)) →
            ∀ ψh ψh' : unitPts (wStep m₁ β δ).G' × Fin 2 → ℂ,
              (∀ b' : unitPts (wStep m₁ β δ).G', ∀ i, ψh (b', i) = ψh' (b', i)) →
            (∀ y : CTorus 3 3 9 m₁ (1 + 1),
              hatPsiF (wStep m₁ β δ).G' 1 nuW (wStep m₁ β δ).hG'
                ((((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) F₁ (fun _ => 1) (rawOf D) ψh y =
              hatPsiF (wStep m₁ β δ).G' 1 nuW (wStep m₁ β δ).hG'
                ((((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) F₁ (fun _ => 1) (rawOf D') ψh' y) ∧
            (∀ (Z : Finset (unitPts (wStep m₁ β δ).G')) (u τ : ℂ) (y : CTorus 3 3 9 m₁ (1 + 1)),
              markedHatPsiF (wStep m₁ β δ).a₁ (wStep m₁ β δ).ν (wStep m₁ β δ).hG'
                ((((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) F₁ Z u τ (fun _ => 1)
                (rawOf D) ψh y =
              markedHatPsiF (wStep m₁ β δ).a₁ (wStep m₁ β δ).ν (wStep m₁ β δ).hG'
                ((((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) F₁ Z u τ (fun _ => 1)
                (rawOf D') ψh' y) := by
  classical
  fan_setup
  refine ⟨m₁, BG, κ, t, δ, β₀t, hβ₀t, ht0, hκpos, ?_⟩
  intro β hβ
  obtain ⟨F₁, hF₁⟩ := f1Spec_exists hC
  refine ⟨F₁, hF₁, ?_⟩
  intro D D' hD hD' hdata ψh ψh' hh
  have hs : ∀ P, ‖(fun _ : ↥(cubeIdx (wStep m₁ β δ).G') => (1 : ℂ)) P‖ < Real.exp κ := fun P => by
    simpa using Real.one_lt_exp_iff.2 hκpos
  have hs1 : ∀ P ∈ cubeIdx (wStep m₁ β δ).G',
      P ∉ parCubes (wStep m₁ β δ).G' (Finset.univ : Finset (CTorus 3 3 9 m₁ (1 + 1))) →
      extS (wStep m₁ β δ).G' (fun _ => 1) P = 1 ∧ extS (wStep m₁ β δ).G' (fun _ => 1) P = 1 :=
    fun P hP _ => by simp [extS, hP]
  have hs0 : ∀ P ∈ parCubes (wStep m₁ β δ).G' (Finset.univ : Finset (CTorus 3 3 9 m₁ (1 + 1))),
      P ∉ (∅ : Finset (ℕ × CTorus 3 3 9 m₁ (1 + 1))) →
      extS (wStep m₁ β δ).G' (fun _ => 1) P = 0 ∧ extS (wStep m₁ β δ).G' (fun _ => 1) P = 0 :=
    fun P hP _ => by rw [fanChain_parCubes_univ] at hP; exact absurd hP (by simp)
  have hY := fanChain_isNnComp_univ (wStep m₁ β δ).hG'
  have hag : ∀ P ∈ (∅ : Finset (ℕ × CTorus 3 3 9 m₁ (1 + 1))),
      SubI (wStep m₁ β δ).G' (cubeP P) Finset.univ →
      extS (wStep m₁ β δ).G' (fun _ => 1) P = extS (wStep m₁ β δ).G' (fun _ => 1) P :=
    fun P hP => absurd hP (by simp)
  have hdata' : ∀ z ∈ (Finset.univ : Finset (CTorus 3 3 9 m₁ (1 + 1))),
      D.Ψ z = D'.Ψ z ∧ (z ∈ (wStep m₁ β δ).G'.Ω 1 → D.h z = D'.h z) := fun z _ => hdata z
  have hh' : ∀ b' : unitPts (wStep m₁ β δ).G', UnitOut (wStep m₁ β δ).G' Finset.univ b' →
      ∀ i, ψh (b', i) = ψh' (b', i) := fun b' _ => hh b'
  have hconn : HatConn (wStep m₁ β δ).G' := hatConn
  refine ⟨fun y => ?_, fun Z u τ y => ?_⟩
  · exact hatPsiF_rows hC le_rfl (wStep m₁ β δ).hG' _ hconn hMX hdm hα hsmX hF₁ hs hs hD hD'
      hY hs1 hs0 hag fanChain_cellUnion_univ (fun P hP => absurd hP (by simp)) hdata' ψh ψh' hh'
      y (Finset.mem_univ y)
  · exact markedHatPsiF_rows hC le_rfl (wStep m₁ β δ).hG' _ hconn hMX hdm hα hsmX hF₁ hs hs hD hD'
      hY hs1 hs0 hag fanChain_cellUnion_univ (fun P hP => absurd hP (by simp)) hdata' ψh ψh' hh'
      Z u τ y (Finset.mem_univ y)


set_option quotPrecheck false in
/-- The top level generating set of the witness step. -/
local notation "Gw[" m "," b "," e "]" => (wStep m b e).G'
set_option quotPrecheck false in
/-- The factor `cc = β_k^{-1/2}` of the witness step. -/
local notation "ccw[" m "," b "," e "]" => ((((wStep m b e).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))

open Classical in
/-- **Instance of `fluct_correction_rows_of_agree_on_component` at the witness step** (whole
torus, `X₁ = Y = univ`, no marked cubes, the cut `s ≡ 1`; reflexive for the same reason as
`fanChain_rows`).  The decoupled backgrounds `(φ, α), (φ₂, α₂)` and the fixed points `δα, δα'` of
the fluctuation problem (`DecFixed`, small) exist for every pair of data and hat variables with
`|ψ̂| ≤ c_ψ`; the bounds `Hh, Hh'` of Theorem I-4a are discharged inside, from the strict
inequalities of `point_facts_core`. -/
theorem fanChain_fluct_rows :
    ∃ (m₁ : ℕ) (BG BG₂ κ t δ β₀ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < κ ∧
      ∀ β : ℝ, β₀ ≤ β → ∃ cψ : ℝ, 0 < cψ ∧
        ∃ F₁ : DecParams Gw[m₁, β, δ] × RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2 →
            (Gw[m₁, β, δ].Ω 1 × Fin 2 → ℂ) × (Gw[m₁, β, δ].Ω 1 → ℂ),
          F1Spec Gw[m₁, β, δ] 1 nuW BG κ F₁ ∧
          ∀ D D' : BgData Gw[m₁, β, δ] 2,
            XiCData Gw[m₁, β, δ] (compWeight 3 1) nuW (1 + 1) 1 t D →
            XiCData Gw[m₁, β, δ] (compWeight 3 1) nuW (1 + 1) 1 t D' →
            (∀ z, D.Ψ z = D'.Ψ z ∧ (z ∈ Gw[m₁, β, δ].Ω 1 → D.h z = D'.h z)) →
            ∀ ψh ψh' : unitPts Gw[m₁, β, δ] × Fin 2 → ℂ,
              (∀ p, ‖ψh p‖ ≤ cψ) → (∀ p, ‖ψh' p‖ ≤ cψ) →
              (∀ b' : unitPts Gw[m₁, β, δ], ∀ i, ψh (b', i) = ψh' (b', i)) →
            ∃ (φ φ₂ : Gw[m₁, β, δ].Ω 1 × Fin 2 → ℂ) (α α₂ : Gw[m₁, β, δ].Ω 1 → ℂ)
              (δα δα' : (Hm m₁ (rhoSep m₁)).Ω 1 → ℂ),
              IsDecBg Gw[m₁, β, δ] (compWeight 3 1) nuW (rho4 3 3 2 BG κ) (fun _ => 1) D φ α ∧
              IsDecBg Gw[m₁, β, δ] (compWeight 3 1) nuW (rho4 3 3 2 BG κ) (fun _ => 1) D' φ₂ α₂ ∧
              Dec2.DecFixed (coverOf Gw[m₁, β, δ]) (Hm m₁ (rhoSep m₁)) (compWeight 3 1) nuW
                (fun _ => 1) false (flAlpha Gw[m₁, β, δ] (Hm m₁ (rhoSep m₁)) α)
                (barField Gw[m₁, β, δ] D.Ψ φ)
                (pertSource (Hm m₁ (rhoSep m₁)) (compWeight 3 1)
                  (hatPsiF Gw[m₁, β, δ] 1 nuW (wStep m₁ β δ).hG' ccw[m₁, β, δ] F₁ (fun _ => 1)
                    (rawOf D) ψh) 0) δα ∧
              Small (Hm m₁ (rhoSep m₁)) δα (c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) ∧
              Dec2.DecFixed (coverOf Gw[m₁, β, δ]) (Hm m₁ (rhoSep m₁)) (compWeight 3 1) nuW
                (fun _ => 1) false (flAlpha Gw[m₁, β, δ] (Hm m₁ (rhoSep m₁)) α₂)
                (barField Gw[m₁, β, δ] D'.Ψ φ₂)
                (pertSource (Hm m₁ (rhoSep m₁)) (compWeight 3 1)
                  (hatPsiF Gw[m₁, β, δ] 1 nuW (wStep m₁ β δ).hG' ccw[m₁, β, δ] F₁ (fun _ => 1)
                    (rawOf D') ψh') 0) δα' ∧
              Small (Hm m₁ (rhoSep m₁)) δα' (c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) ∧
              ((∀ x : (Hm m₁ (rhoSep m₁)).Ω 1, (x : CTorus 3 3 9 m₁ (1 + 1)) ∈
                  Dec2.SYF (coverOf Gw[m₁, β, δ]) (Hm m₁ (rhoSep m₁)) (compWeight 3 1) nuW
                    Finset.univ ∅ Finset.univ → δα x = δα' x) ∧
              (∀ y : (Hm m₁ (rhoSep m₁)).Ω 1, (y : CTorus 3 3 9 m₁ (1 + 1)) ∈
                  (Finset.univ : Finset (CTorus 3 3 9 m₁ (1 + 1))) → ∀ i : Fin 2,
                dphi (Hm m₁ (rhoSep m₁))
                  (Dec2.decG (coverOf Gw[m₁, β, δ]) (Hm m₁ (rhoSep m₁)) (compWeight 3 1) nuW
                    (fun _ => 1))
                  (flAlpha Gw[m₁, β, δ] (Hm m₁ (rhoSep m₁)) α) (barField Gw[m₁, β, δ] D.Ψ φ)
                  (pertSource (Hm m₁ (rhoSep m₁)) (compWeight 3 1)
                    (hatPsiF Gw[m₁, β, δ] 1 nuW (wStep m₁ β δ).hG' ccw[m₁, β, δ] F₁ (fun _ => 1)
                      (rawOf D) ψh) 0) δα (y, i) =
                dphi (Hm m₁ (rhoSep m₁))
                  (Dec2.decG (coverOf Gw[m₁, β, δ]) (Hm m₁ (rhoSep m₁)) (compWeight 3 1) nuW
                    (fun _ => 1))
                  (flAlpha Gw[m₁, β, δ] (Hm m₁ (rhoSep m₁)) α₂) (barField Gw[m₁, β, δ] D'.Ψ φ₂)
                  (pertSource (Hm m₁ (rhoSep m₁)) (compWeight 3 1)
                    (hatPsiF Gw[m₁, β, δ] 1 nuW (wStep m₁ β δ).hG' ccw[m₁, β, δ] F₁ (fun _ => 1)
                      (rawOf D') ψh') 0) δα' (y, i))) := by
  classical
  fan_setup
  refine ⟨m₁, BG, BG₂, κ, t, δ, β₀t, hβ₀t, ht0, hκpos, ?_⟩
  intro β hβ
  obtain ⟨hp, hcψ0, hr0, hδ₁, hc, hlt, ⟨R0⟩⟩ := hitems β hβ
  obtain ⟨F₁, hF₁⟩ := f1Spec_exists hC
  obtain ⟨Sol, hSolspec⟩ := solSpec_exists hC
  refine ⟨towerCpsi κ t β, hcψ0, F₁, hF₁, ?_⟩
  intro D D' hD hD' hdata ψh ψh' hψh hψh' hh
  have hs : ∀ P, ‖(fun _ : ↥(cubeIdx (wStep m₁ β δ).G') => (1 : ℂ)) P‖ < Real.exp κ := fun P => by
    simpa using Real.one_lt_exp_iff.2 hκpos
  have hs1 : ∀ P ∈ cubeIdx (wStep m₁ β δ).G',
      P ∉ parCubes (wStep m₁ β δ).G' (Finset.univ : Finset (CTorus 3 3 9 m₁ (1 + 1))) →
      extS (wStep m₁ β δ).G' (fun _ => 1) P = 1 ∧ extS (wStep m₁ β δ).G' (fun _ => 1) P = 1 :=
    fun P hP _ => by simp [extS, hP]
  have hs0 : ∀ P ∈ parCubes (wStep m₁ β δ).G' (Finset.univ : Finset (CTorus 3 3 9 m₁ (1 + 1))),
      P ∉ (∅ : Finset (ℕ × CTorus 3 3 9 m₁ (1 + 1))) →
      extS (wStep m₁ β δ).G' (fun _ => 1) P = 0 ∧ extS (wStep m₁ β δ).G' (fun _ => 1) P = 0 :=
    fun P hP _ => by rw [fanChain_parCubes_univ] at hP; exact absurd hP (by simp)
  have hY := fanChain_isNnComp_univ (wStep m₁ β δ).hG'
  have hag : ∀ P ∈ (∅ : Finset (ℕ × CTorus 3 3 9 m₁ (1 + 1))),
      SubI (wStep m₁ β δ).G' (cubeP P) Finset.univ →
      extS (wStep m₁ β δ).G' (fun _ => 1) P = extS (wStep m₁ β δ).G' (fun _ => 1) P :=
    fun P hP => absurd hP (by simp)
  have hdata' : ∀ z ∈ (Finset.univ : Finset (CTorus 3 3 9 m₁ (1 + 1))),
      D.Ψ z = D'.Ψ z ∧ (z ∈ (wStep m₁ β δ).G'.Ω 1 → D.h z = D'.h z) := fun z _ => hdata z
  have hh' : ∀ b' : unitPts (wStep m₁ β δ).G', UnitOut (wStep m₁ β δ).G' Finset.univ b' →
      ∀ i, ψh (b', i) = ψh' (b', i) := fun b' _ => hh b'
  have hconn : HatConn (wStep m₁ β δ).G' := hatConn
  have hrow : RowInHat (coverOf (wStep m₁ β δ).G') (Hm m₁ (rhoSep m₁)) (compWeight 3 1) nuW :=
    rowInHat_level (dgSettingNu h4) isLevel_Hm isLevel_Gp
  have hψ := (hatPsiF_mem_flBallLC hC le_rfl isLevel_Hm (wStep m₁ β δ).hG' _ hcψ0.le hMX hdm hα
    hsmX hδ₁ hF₁ hs hD hψh).1
  have hψ₂ := (hatPsiF_mem_flBallLC hC le_rfl isLevel_Hm (wStep m₁ β δ).hG' _ hcψ0.le hMX hdm hα
    hsmX hδ₁ hF₁ hs hD' hψh').1
  obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ :=
    point_facts_core (X₁f := Finset.univ) hC hF₁ hSolspec hs (fun _ _ _ => rfl) hD hψ
  obtain ⟨φ₂, α₂, δφ₂, δα₂, hI₂, hFeq₂, hstrict₂, hSeq₂, hmem₂⟩ :=
    point_facts_core (X₁f := Finset.univ) hC hF₁ hSolspec hs (fun _ _ _ => rfl) hD' hψ₂
  obtain ⟨-, hfix, hs6, -⟩ := hSolspec ((fun _ => 1), flEdat _ _ (φ, α) D.Ψ _) hs hstrict
  obtain ⟨-, hfix₂, hs6₂, -⟩ := hSolspec ((fun _ => 1), flEdat _ _ (φ₂, α₂) D'.Ψ _) hs hstrict₂
  erw [congrArg Prod.snd hSeq] at hfix hs6
  erw [congrArg Prod.snd hSeq₂] at hfix₂ hs6₂
  have hOp := hC.SM.toCoverBase.toOpSetting.toGreen
  have hd0 : 0 < 3 := by norm_num
  have hB0 : 0 ≤ 2 * (K4 3 3 2 BG κ * (xiC1 3 * t)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le
      (mul_nonneg (by have := one_le_xiC1 3; linarith) ht0.le))
  have Hh := StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict
  have Hh₂ := StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict₂
  have hflc := fluct_correction_rows_of_agree_on_component hC le_rfl (wStep m₁ β δ).hG'
    isLevel_Hm _ hconn hrow hMX hdm hα hsmX hF₁ hs hs hD hD' hY hs1 hs0 hag
    fanChain_cellUnion_univ (fun P hP => absurd hP (by simp)) hdata' ψh ψh' hh' hI hI₂ Hh Hh₂ hfix
    hs6 hfix₂ hs6₂
  exact ⟨φ, φ₂, α, α₂, _, _, hI, hI₂, hfix, hs6, hfix₂, hs6₂, hflc⟩


/-- Real-number arithmetic of the marked radius: with `r = c_ψ/(2 p₁) - 4 ≥ 0`, `t₁ = 8 p₁/c_ψ` and
`W c_ψ < t`, one has `(2 + t₁) (W p₁) < t`. -/
theorem fanChain_radius_real {cψ p₁ W t r t₁ : ℝ} (hcψ : 0 < cψ) (hp : 0 < p₁)
    (hr : r = cψ / (2 * p₁) - 4) (hr0 : 0 ≤ r) (hW0 : 0 ≤ W) (hWc : W * cψ < t)
    (ht₁ : t₁ = 8 * p₁ / cψ) : (2 + t₁) * (W * p₁) < t := by
  have hmain : (2 + r) * (2 + t₁) * p₁ ≤ cψ := by
    have e : (2 + r) * (2 + t₁) * p₁ = cψ - 16 * p₁ ^ 2 / cψ := by
      rw [hr, ht₁]
      field_simp
      ring
    rw [e]
    have : 0 ≤ 16 * p₁ ^ 2 / cψ := by positivity
    linarith
  have ht₁0 : 0 < t₁ := by rw [ht₁]; positivity
  have h2 : (2 + t₁) * (W * p₁) ≤ (2 + r) * (2 + t₁) * (W * p₁) := by
    have h0 : 0 ≤ (2 + t₁) * (W * p₁) := by positivity
    have h3 : 1 ≤ 2 + r := by linarith
    calc (2 + t₁) * (W * p₁) = 1 * ((2 + t₁) * (W * p₁)) := by ring
      _ ≤ (2 + r) * ((2 + t₁) * (W * p₁)) := mul_le_mul_of_nonneg_right h3 h0
      _ = _ := by ring
  refine lt_of_le_of_lt h2 ?_
  calc (2 + r) * (2 + t₁) * (W * p₁) = ((2 + r) * (2 + t₁) * p₁) * W := by ring
    _ ≤ cψ * W := mul_le_mul_of_nonneg_right hmain hW0
    _ = W * cψ := by ring
    _ < t := hWc

open Classical in
/-- **Instance of `fluct_correction_rows_marked_of_ball` at the witness step** (whole
torus, `X₁ = Y = univ`, no marked cubes, the cut `s ≡ 1`; reflexive for the same reason as
`fanChain_rows`).  The decoupled backgrounds `(φ, α), (φ₂, α₂)` and the fixed points `δα, δα'` of
the fluctuation problem (`DecFixed`, small) exist for every pair of data and hat variables with
`|ψ̂| ≤ c_ψ`; the bounds `Hh, Hh'` of Theorem I-4a are discharged inside, from the strict
inequalities of `point_facts_core`. -/
theorem fanChain_fluct_rows_marked :
    ∃ (m₁ : ℕ) (BG BG₂ κ t δ β₀ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < κ ∧
      ∀ β : ℝ, β₀ ≤ β → ∃ t₁ : ℝ, 0 < t₁ ∧
        ∃ F₁ : DecParams Gw[m₁, β, δ] × RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2 →
            (Gw[m₁, β, δ].Ω 1 × Fin 2 → ℂ) × (Gw[m₁, β, δ].Ω 1 → ℂ),
          F1Spec Gw[m₁, β, δ] 1 nuW BG κ F₁ ∧
          ∀ D D' : BgData Gw[m₁, β, δ] 2,
            XiCData Gw[m₁, β, δ] (compWeight 3 1) nuW (1 + 1) 1 t D →
            XiCData Gw[m₁, β, δ] (compWeight 3 1) nuW (1 + 1) 1 t D' →
            (∀ z, D.Ψ z = D'.Ψ z ∧ (z ∈ Gw[m₁, β, δ].Ω 1 → D.h z = D'.h z)) →
            ∀ ψh ψh' : unitPts Gw[m₁, β, δ] × Fin 2 → ℂ,
              (∀ p, ‖ψh p‖ ≤ pLog 1 2 β) → (∀ p, ‖ψh' p‖ ≤ pLog 1 2 β) →
            ∀ (Z : Finset (unitPts Gw[m₁, β, δ])) (u τ : ℂ), ‖u‖ ≤ 2 → ‖τ‖ ≤ t₁ →
              (∀ b' : unitPts Gw[m₁, β, δ], ∀ i, ψh (b', i) = ψh' (b', i)) →
            ∃ (φ φ₂ : Gw[m₁, β, δ].Ω 1 × Fin 2 → ℂ) (α α₂ : Gw[m₁, β, δ].Ω 1 → ℂ)
              (δα δα' : (Hm m₁ (rhoSep m₁)).Ω 1 → ℂ),
              IsDecBg Gw[m₁, β, δ] (compWeight 3 1) nuW (rho4 3 3 2 BG κ) (fun _ => 1) D φ α ∧
              IsDecBg Gw[m₁, β, δ] (compWeight 3 1) nuW (rho4 3 3 2 BG κ) (fun _ => 1) D' φ₂ α₂ ∧
              Dec2.DecFixed (coverOf Gw[m₁, β, δ]) (Hm m₁ (rhoSep m₁)) (compWeight 3 1) nuW
                (fun _ => 1) false (flAlpha Gw[m₁, β, δ] (Hm m₁ (rhoSep m₁)) α)
                (barField Gw[m₁, β, δ] D.Ψ φ)
                (pertSource (Hm m₁ (rhoSep m₁)) (compWeight 3 1)
                  (markedHatPsiF (wStep m₁ β δ).a₁ (wStep m₁ β δ).ν (wStep m₁ β δ).hG' ccw[m₁, β, δ] F₁ Z u τ (fun _ => 1)
                    (rawOf D) ψh) 0) δα ∧
              Small (Hm m₁ (rhoSep m₁)) δα (c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) ∧
              Dec2.DecFixed (coverOf Gw[m₁, β, δ]) (Hm m₁ (rhoSep m₁)) (compWeight 3 1) nuW
                (fun _ => 1) false (flAlpha Gw[m₁, β, δ] (Hm m₁ (rhoSep m₁)) α₂)
                (barField Gw[m₁, β, δ] D'.Ψ φ₂)
                (pertSource (Hm m₁ (rhoSep m₁)) (compWeight 3 1)
                  (markedHatPsiF (wStep m₁ β δ).a₁ (wStep m₁ β δ).ν (wStep m₁ β δ).hG' ccw[m₁, β, δ] F₁ Z u τ (fun _ => 1)
                    (rawOf D') ψh') 0) δα' ∧
              Small (Hm m₁ (rhoSep m₁)) δα' (c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) ∧
              ((∀ x : (Hm m₁ (rhoSep m₁)).Ω 1, (x : CTorus 3 3 9 m₁ (1 + 1)) ∈
                  Dec2.SYF (coverOf Gw[m₁, β, δ]) (Hm m₁ (rhoSep m₁)) (compWeight 3 1) nuW
                    Finset.univ ∅ Finset.univ → δα x = δα' x) ∧
              (∀ y : (Hm m₁ (rhoSep m₁)).Ω 1, (y : CTorus 3 3 9 m₁ (1 + 1)) ∈
                  (Finset.univ : Finset (CTorus 3 3 9 m₁ (1 + 1))) → ∀ i : Fin 2,
                dphi (Hm m₁ (rhoSep m₁))
                  (Dec2.decG (coverOf Gw[m₁, β, δ]) (Hm m₁ (rhoSep m₁)) (compWeight 3 1) nuW
                    (fun _ => 1))
                  (flAlpha Gw[m₁, β, δ] (Hm m₁ (rhoSep m₁)) α) (barField Gw[m₁, β, δ] D.Ψ φ)
                  (pertSource (Hm m₁ (rhoSep m₁)) (compWeight 3 1)
                    (markedHatPsiF (wStep m₁ β δ).a₁ (wStep m₁ β δ).ν (wStep m₁ β δ).hG' ccw[m₁, β, δ] F₁ Z u τ (fun _ => 1)
                    (rawOf D) ψh) 0) δα (y, i) =
                dphi (Hm m₁ (rhoSep m₁))
                  (Dec2.decG (coverOf Gw[m₁, β, δ]) (Hm m₁ (rhoSep m₁)) (compWeight 3 1) nuW
                    (fun _ => 1))
                  (flAlpha Gw[m₁, β, δ] (Hm m₁ (rhoSep m₁)) α₂) (barField Gw[m₁, β, δ] D'.Ψ φ₂)
                  (pertSource (Hm m₁ (rhoSep m₁)) (compWeight 3 1)
                    (markedHatPsiF (wStep m₁ β δ).a₁ (wStep m₁ β δ).ν (wStep m₁ β δ).hG' ccw[m₁, β, δ] F₁ Z u τ (fun _ => 1)
                    (rawOf D') ψh') 0) δα' (y, i))) := by
  classical
  fan_setup
  refine ⟨m₁, BG, BG₂, κ, t, δ, β₀t, hβ₀t, ht0, hκpos, ?_⟩
  intro β hβ
  obtain ⟨hp, hcψ0, hr0, hδ₁, hc, hlt, ⟨R0⟩⟩ := hitems β hβ
  obtain ⟨F₁, hF₁⟩ := f1Spec_exists hC
  obtain ⟨Sol, hSolspec⟩ := solSpec_exists hC
  set p₁ := pLog 1 2 β with hp₁def
  set cψ := towerCpsi κ t β with hcψdef
  set W : ℝ := Real.sqrt ((2 : ℕ) : ℝ) *
    (‖(((hatStep m₁ β p₁ δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) 1) κ) with hW
  have ha : 0 < compWeight 3 (1 : ℝ) 1 :=
    lt_of_lt_of_le (by norm_num) (hC.HBp.weights 1 le_rfl (by norm_num)).1
  have hCs := covSupConstC_nonneg (N := 2) (d := 3) (L := 3) (by norm_num) (by norm_num) ha κ
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hWc : W * cψ < t := by rw [hW]; nlinarith [hδ₁]
  have hrad := fanChain_radius_real hcψ0 hp (r := towerR κ t β p₁) rfl hr0.le hW0 hWc
    (t₁ := 8 * p₁ / cψ) rfl
  have ht₁0 : 0 < 8 * p₁ / cψ := by positivity
  refine ⟨8 * p₁ / cψ, ht₁0, F₁, hF₁, ?_⟩
  intro D D' hD hD' hdata ψh ψh' hψh hψh' Z u τ hu hτ hh
  have hs : ∀ P, ‖(fun _ : ↥(cubeIdx (wStep m₁ β δ).G') => (1 : ℂ)) P‖ < Real.exp κ := fun P => by
    simpa using Real.one_lt_exp_iff.2 hκpos
  have hs1 : ∀ P ∈ cubeIdx (wStep m₁ β δ).G',
      P ∉ parCubes (wStep m₁ β δ).G' (Finset.univ : Finset (CTorus 3 3 9 m₁ (1 + 1))) →
      extS (wStep m₁ β δ).G' (fun _ => 1) P = 1 ∧ extS (wStep m₁ β δ).G' (fun _ => 1) P = 1 :=
    fun P hP _ => by simp [extS, hP]
  have hs0 : ∀ P ∈ parCubes (wStep m₁ β δ).G' (Finset.univ : Finset (CTorus 3 3 9 m₁ (1 + 1))),
      P ∉ (∅ : Finset (ℕ × CTorus 3 3 9 m₁ (1 + 1))) →
      extS (wStep m₁ β δ).G' (fun _ => 1) P = 0 ∧ extS (wStep m₁ β δ).G' (fun _ => 1) P = 0 :=
    fun P hP _ => by rw [fanChain_parCubes_univ] at hP; exact absurd hP (by simp)
  have hY := fanChain_isNnComp_univ (wStep m₁ β δ).hG'
  have hag : ∀ P ∈ (∅ : Finset (ℕ × CTorus 3 3 9 m₁ (1 + 1))),
      SubI (wStep m₁ β δ).G' (cubeP P) Finset.univ →
      extS (wStep m₁ β δ).G' (fun _ => 1) P = extS (wStep m₁ β δ).G' (fun _ => 1) P :=
    fun P hP => absurd hP (by simp)
  have hdata' : ∀ z ∈ (Finset.univ : Finset (CTorus 3 3 9 m₁ (1 + 1))),
      D.Ψ z = D'.Ψ z ∧ (z ∈ (wStep m₁ β δ).G'.Ω 1 → D.h z = D'.h z) := fun z _ => hdata z
  have hh' : ∀ b' : unitPts (wStep m₁ β δ).G', UnitOut (wStep m₁ β δ).G' Finset.univ b' →
      ∀ i, ψh (b', i) = ψh' (b', i) := fun b' _ => hh b'
  have hconn : HatConn (wStep m₁ β δ).G' := hatConn
  have hrow : RowInHat (coverOf (wStep m₁ β δ).G') (Hm m₁ (rhoSep m₁)) (compWeight 3 1) nuW :=
    rowInHat_level (dgSettingNu h4) isLevel_Hm isLevel_Gp
  have hδu : ∀ (ψ : unitPts (wStep m₁ β δ).G' × Fin 2 → ℂ), True →
      (‖u‖ + ‖τ‖) * (Real.sqrt ((2 : ℕ) : ℝ) * (‖((((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))‖ *
        (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) 1) κ * p₁))) < t := by
    intro _ _
    have hn : ‖u‖ + ‖τ‖ ≤ 2 + 8 * p₁ / cψ := add_le_add hu hτ
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right hn (by have := hp.le; positivity)) ?_
    have e : Real.sqrt ((2 : ℕ) : ℝ) *
        (‖(((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
          (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) 1) κ * p₁)) = W * p₁ := by
      rw [hW]; ring
    rw [e]; exact hrad
  have hψ := (markedHatPsiF_mem_flBallLC hC le_rfl isLevel_Hm (wStep m₁ β δ).hG' _ (cψ := p₁)
    hp.le hMX hdm hα hsmX hF₁ hs hD hψh Z (hδu ψh trivial)).1
  have hψ₂ := (markedHatPsiF_mem_flBallLC hC le_rfl isLevel_Hm (wStep m₁ β δ).hG' _ (cψ := p₁)
    hp.le hMX hdm hα hsmX hF₁ hs hD' hψh' Z (hδu ψh' trivial)).1
  obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ :=
    point_facts_core (X₁f := Finset.univ) hC hF₁ hSolspec hs (fun _ _ _ => rfl) hD hψ
  obtain ⟨φ₂, α₂, δφ₂, δα₂, hI₂, hFeq₂, hstrict₂, hSeq₂, hmem₂⟩ :=
    point_facts_core (X₁f := Finset.univ) hC hF₁ hSolspec hs (fun _ _ _ => rfl) hD' hψ₂
  obtain ⟨-, hfix, hs6, -⟩ := hSolspec ((fun _ => 1), flEdat _ _ (φ, α) D.Ψ _) hs hstrict
  obtain ⟨-, hfix₂, hs6₂, -⟩ := hSolspec ((fun _ => 1), flEdat _ _ (φ₂, α₂) D'.Ψ _) hs hstrict₂
  erw [congrArg Prod.snd hSeq] at hfix hs6
  erw [congrArg Prod.snd hSeq₂] at hfix₂ hs6₂
  have hOp := hC.SM.toCoverBase.toOpSetting.toGreen
  have hd0 : 0 < 3 := by norm_num
  have hB0 : 0 ≤ 2 * (K4 3 3 2 BG κ * (xiC1 3 * t)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le
      (mul_nonneg (by have := one_le_xiC1 3; linarith) ht0.le))
  have Hh := StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict
  have Hh₂ := StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict₂
  have hflc := fluct_correction_rows_marked_of_ball hC le_rfl (wStep m₁ β δ).hG'
    isLevel_Hm _ hconn hrow hMX hdm hα hsmX hF₁ hs hs hD hD' hY hs1 hs0 hag
    fanChain_cellUnion_univ (fun P hP => absurd hP (by simp)) hdata' ψh ψh' hh' Z u τ hI hI₂ Hh Hh₂
    hfix hs6 hfix₂ hs6₂
  exact ⟨φ, φ₂, α, α₂, _, _, hI, hI₂, hfix, hs6, hfix₂, hs6₂, hflc⟩

end Balaban.Inhabited
