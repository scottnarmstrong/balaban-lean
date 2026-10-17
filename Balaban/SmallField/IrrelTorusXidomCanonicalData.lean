/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomCanonical
import Balaban.SmallField.IrrelTorusBoundId
import Mathlib.Tactic.Linarith

/-!
# Anisotropic data for the chosen composition realization

This is the canonical-witness form of the level-site anisotropic lemma. Its second-difference
bound comes from the same `XiCData` realization as its field, with no independent `hsec` premise.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField.GsSpec Balaban.SmallField.Def6

variable {d L N₁ m₁ k N j : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
  {G' : GeneratingSet d L (N₁ * L ^ m₁) k ϱ'}
  {a₁ ν s e ε θh : ℝ} {D : BgData G' N}

/-- The exact chosen `XiCData` composition, including its constant field coordinate, is in the
anisotropic tube. The same-mass chart membership remains the explicit class-chart premise. -/
theorem xiCData_dataHypAniso_of_levelGS_canonical
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hj1 : 1 ≤ j) (hjk : j < k)
    (H' : BgHyp d L k ϱ' (compWeight L a₁) ν)
    (hprec : Precedes (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k) (ϱ := ϱ) j hjk.le) G')
    (ha₁ : 0 < a₁) (hs : 0 < s) (hs1 : s ≤ 1)
    (hjs : (L : ℝ) ^ j = s * (L : ℝ) ^ k)
    (hgap : ScaleGap (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k) (ϱ := ϱ) j hjk.le) G' s)
    (hcol : ∀ z ∈ collar (levelGS (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk.le), z ∈ G'.Ω 1 ∧ 1 ≤ s * G'.spacing z)
    (hsmall : (4 * d + 6) * (xiC1 d * e) ≤ 1)
    (hc1 : xiC1 d * e ≤ bgC1 d L N)
    (hD : XiCData G' (compWeight L a₁) ν k 1 e D)
    (hθh0 : 0 < θh) (hθh1 : θh < 1)
    (hν : 0 < ν * ((L : ℝ) ^ j) ^ 2)
    (hτ1 : scaledC0 d * s ≤ 1)
    (hντ : ν * ((L : ℝ) ^ j) ^ 2 ≤ (scaledC0 d * s) ^ 2)
    (hζ1 : xiC1 d * e ≤ 1 / 200) (hee : e ≤ ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (y : CTorus d L N₁ m₁ k) (ψ : Site d → Spin N) (b : Spin N),
        (∀ x, ψ x = composeField
          (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k) (ϱ := ϱ) j hjk.le)
          G' (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D.Ψ
          (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)) →
        b = (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • D.h y) →
        ∀ {Dom : Set ((Site d → Spin N) × Spin N)},
          (ψ, b) ∈ Dom ∧ ((fun _ => ψ 0), b) ∈ Dom →
          DataHypAniso Dom (ν * ((L : ℝ) ^ j) ^ 2)
            (16 * scaledC0 d * xiC1 d * s) ε
            (xiSigma d L N B θh * s ^ (2 - θh) * e) ψ b := by
  have he : 0 < e := by
    obtain ⟨_, _, _, _, hX, _⟩ := hD
    exact hX.2.1
  have hsmallFour : (4 * d + 6) * ((2 * d + 1) * e) ≤ 1 := by
    have hcoef : (2 * (d : ℝ) + 1) ≤ xiC1 d := by
      have := one_le_xiC1 d
      unfold xiC1
      nlinarith
    refine le_trans ?_ hsmall
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hcoef he.le) (by positivity)
  obtain ⟨B, hB0, hB⟩ := xiCData_second_diff_levelGS_pullback hd hL hj1 hjk.le
    ha₁ H' hprec hgap hs hs1 hθh0 hθh1 hsmallFour hc1 D hD
  have hL2 : 2 ≤ L := by omega
  obtain ⟨Ψ0, h0, Ψ'', h'', φr, hReal, HS⟩ :=
    xiCData_scaledComposition_canonical hL2 hj1 hjk H' hprec ha₁ hs hs1 hjs
      hgap hcol hsmall hD
  refine ⟨B, hB0, ?_⟩
  intro y ψ b hψ hb Dom hchart
  let G := levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
    (k := k) (ϱ := ϱ) j hjk.le
  let f : Site d → CTorus d L N₁ m₁ k :=
    fun x => y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x
  have hψ' : ∀ x i, ψ x i =
      (reR G G' a₁ φr Ψ0 (f x) i : ℂ) +
        dPsi G G' a₁ φr
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) Ψ0 Ψ'' (f x) i := by
    intro x i
    have hF : composeField G G' (compWeight L a₁)
        (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D.Ψ (f x) i =
        ccv G G' a₁ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D)
          Ψ0 Ψ'' (f x) i := by
      rw [composeField_congr_data hprec (compWeight L a₁)
        (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D)
        (fun z hz i => hReal.1 z hz i) (f x) i]
      rfl
    have hR : crv G G' a₁ φr Ψ0 (f x) i =
        (reR G G' a₁ φr Ψ0 (f x) i : ℂ) :=
      congrFun (HS.real_crv (f x)).eq_ofReal i
    calc
      ψ x i = composeField G G' (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D.Ψ (f x) i :=
        congrFun (hψ x) i
      _ = ccv G G' a₁ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D)
          Ψ0 Ψ'' (f x) i := hF
      _ = _ := by rw [← hR]; simp [dPsi]
  have hb' : b = (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) •
      fun i => (h0 i : ℂ) + hRes G h'' (f 0) i) := by
    have hmem : y ∈ G'.Ω 1 := hprec.mem_Ω1 (by simp [levelGS_Ω, hj1])
    have hf0 : f 0 = y := by simp [f, Def6v2.ibase_zero]
    rw [hb]
    congr 1
    funext i
    rw [hReal.2 y hmem i]
    rw [hf0]
    rw [hRes_of_mem h'' (by simp [G, levelGS_Ω, hj1] : y ∈ G.Ω 1)]
  have hK₂ : 0 ≤ xiSigma d L N B θh * s ^ (2 - θh) * e := by
    have hSigma : 0 ≤ xiSigma d L N B θh := by
      unfold xiSigma
      have := bgK1_pos d L N
      have := lemma53Const_pos d L
      have := cHold_nonneg d L
      have := one_le_xiC1 d
      positivity
    positivity
  exact HypS.dataHypAniso_of_levelGS hL2 hj1 hjk HS y f rfl ψ b hψ' hb'
    hν hτ1 hντ hζ1 hee hchart hK₂ (hB y ψ hψ)

end Balaban.SmallField
