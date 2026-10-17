/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomGeometry
import Balaban.Fluctuation.RenormExpLemma35
import Mathlib.Tactic.Linarith

/-!
# P1 (3.107) in the pulled-back Site supremum norm
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField.GsSpec Balaban.SmallField.Def6 Matrix Finset

/-- The componentwise second-difference estimate for a composed `XiC` realization gives
the `Site` supremum-norm estimate on the whole level lattice. -/
theorem xiC_second_diff_levelGS_pullback
    {d L N₁ m₁ k N j : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {G' : GeneratingSet d L (N₁ * L ^ m₁) k ϱ'}
    {a₁ ν θ ε' θh : ℝ} (ha₁ : 0 < a₁)
    (hBg : BgHyp d L k ϱ' (compWeight L a₁) ν)
    (hprec : Precedes (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k) (ϱ := ϱ) j hjk) G')
    (hgap : ScaleGap (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k) (ϱ := ϱ) j hjk) G' θ)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθh0 : 0 < θh) (hθh1 : θh < 1)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε') ≤ 1)
    (hc1 : xiC1 d * ε' ≤ bgC1 d L N)
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : CTorus d L N₁ m₁ k → Fin N → ℂ}
    (hXi : XiC G' (compWeight L a₁) ν k 1 ε' Ψ₀ h₀ Ψ'' h'') :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ Dc : BgData G' N,
      RealizesC Dc Ψ₀ h₀ Ψ'' h'' ∧
      ∀ (y : CTorus d L N₁ m₁ k) (ψ : Site d → Spin N),
        (∀ s, ψ s = composeField
            (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k) (ϱ := ϱ) j hjk)
            G' (compWeight L a₁)
            (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc.Ψ
            (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)) →
        ∀ x μ μ', ‖ψ (x + Pi.single μ 1 + Pi.single μ' 1) -
          ψ (x + Pi.single μ 1) - ψ (x + Pi.single μ' 1) + ψ x‖ ≤
            xiSigma d L N B θh * θ ^ (2 - θh) * ε' := by
  obtain ⟨B, hB0, hB⟩ := xiC_second_diff hd hL
  let G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ := levelGS j hjk
  obtain ⟨Dc, hDc, hsecond⟩ := hB hθh0 hθh1 G G' ha₁ hBg hprec hgap
    hθ0 hθ1 hsmall hc1 hXi
  refine ⟨B, hB0, Dc, hDc, ?_⟩
  intro y ψ hψ x μ μ'
  let F : CTorus d L N₁ m₁ k → Spin N := composeField G G' (compWeight L a₁)
    (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc.Ψ
  let f : Site d → CTorus d L N₁ m₁ k :=
    fun s => y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s
  have hmem : ∀ z : CTorus d L N₁ m₁ k, z ∈ G.layer j := by
    intro z
    exact (GeneratingSet.mem_layer G).2 ⟨by simp [G, levelGS_Ω],
      by simp [G, levelGS_Ω]⟩
  have hfμ : f (x + Pi.single μ 1) = f x +
      Pi.single μ ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k)) := by
    simp only [f, ibase_add_single, add_assoc]
  have hfμ' : f (x + Pi.single μ' 1) = f x +
      Pi.single μ' ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k)) := by
    simp only [f, ibase_add_single, add_assoc]
  have hfμμ' : f (x + Pi.single μ 1 + Pi.single μ' 1) =
      f x + Pi.single μ ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k)) +
        Pi.single μ' ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k)) := by
    calc
      _ = f (x + Pi.single μ 1) +
          Pi.single μ' ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k)) := by
            simp only [f]
            rw [ibase_add_single]
            abel
      _ = _ := by rw [hfμ]
  apply (pi_norm_le_iff_of_nonneg ?_).2
  · intro i
    have hi := hsecond hj1 hjk μ μ' (hmem (f x))
      (hmem (f x + Pi.single μ ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k))))
      (hmem (f x + Pi.single μ' ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k))))
      (hmem (f x + Pi.single μ ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k)) +
        Pi.single μ' ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k)))) i
    simpa only [hψ, F, f, hfμ, hfμ', hfμμ', Pi.sub_apply, Pi.add_apply] using hi
  · have hε : 0 ≤ ε' := hXi.2.1.le
    have hθ : 0 ≤ θ ^ (2 - θh) := Real.rpow_nonneg hθ0.le _
    have hSigma : 0 ≤ xiSigma d L N B θh := by
      unfold xiSigma
      have := bgK1_pos d L N
      have := lemma53Const_pos d L
      have := cHold_nonneg d L
      have := one_le_xiC1 d
      have hBdiv : 0 ≤ B / θh := div_nonneg hB0 hθh0.le
      positivity
    exact mul_nonneg (mul_nonneg hSigma hθ) hε

/-- The estimate applies to any chosen realization of the complex chart. Uniqueness of
`RealizesC` identifies it with the realization selected by `xiC_second_diff`. -/
theorem xiC_second_diff_levelGS_pullback_realization
    {d L N₁ m₁ k N j : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {G' : GeneratingSet d L (N₁ * L ^ m₁) k ϱ'}
    {a₁ ν θ ε' θh : ℝ} (ha₁ : 0 < a₁)
    (hBg : BgHyp d L k ϱ' (compWeight L a₁) ν)
    (hprec : Precedes (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k) (ϱ := ϱ) j hjk) G')
    (hgap : ScaleGap (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k) (ϱ := ϱ) j hjk) G' θ)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθh0 : 0 < θh) (hθh1 : θh < 1)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε') ≤ 1)
    (hc1 : xiC1 d * ε' ≤ bgC1 d L N)
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : CTorus d L N₁ m₁ k → Fin N → ℂ}
    (hXi : XiC G' (compWeight L a₁) ν k 1 ε' Ψ₀ h₀ Ψ'' h'')
    (Dc : BgData G' N) (hDc : RealizesC Dc Ψ₀ h₀ Ψ'' h'') :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (y : CTorus d L N₁ m₁ k) (ψ : Site d → Spin N),
        (∀ s, ψ s = composeField
            (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k) (ϱ := ϱ) j hjk)
            G' (compWeight L a₁)
            (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc.Ψ
            (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)) →
        ∀ x μ μ', ‖ψ (x + Pi.single μ 1 + Pi.single μ' 1) -
          ψ (x + Pi.single μ 1) - ψ (x + Pi.single μ' 1) + ψ x‖ ≤
            xiSigma d L N B θh * θ ^ (2 - θh) * ε' := by
  obtain ⟨B, hB0, Dc', hDc', hsec⟩ := xiC_second_diff_levelGS_pullback
    hd hL hj1 hjk ha₁ hBg hprec hgap hθ0 hθ1 hθh0 hθh1 hsmall hc1 hXi
  have he : Dc' = Dc := Balaban.Fluctuation.realizesC_unique hDc' hDc
  subst Dc'
  exact ⟨B, hB0, hsec⟩


end Balaban.SmallField
