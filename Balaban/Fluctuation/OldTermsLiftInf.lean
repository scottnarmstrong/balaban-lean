/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftFamily
public import Balaban.SmallField.IrrelTorusDefectInverse

/-!
# Infinite-volume polymer shapes at inherited levels

An integer shape is eventually small on both torus sequences. Polymerhood on either
one transfers to the other through the old physical torus equivalence and the landed
two-torus transfer theorem.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.SmallField.Def6 Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

private theorem zsmall_mono {R R' Q Q' : ℕ} {X' : Finset (Fin d → ℤ)}
    (hR : R ≤ R') (hQ : Q' ≤ Q) (h : ZSmall R Q X') : ZSmall R' Q' X' := by
  intro z hz μ
  have hs := h z hz μ
  have hR' : (R : ℤ) ≤ R' := by exact_mod_cast hR
  have hQ' : (Q' : ℤ) ≤ Q := by exact_mod_cast hQ
  omega

private theorem oldBlockSide_le_large (n j : ℕ) :
    n * L ^ m₁ * L ^ (k - j) ≤
      (L * n) * L ^ m₁ * L ^ (k - j) := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hn : n ≤ L * n := by nlinarith
  gcongr

omit [NeZero L] in
private theorem torusSeq_dvd_L_mul (m₀ n : ℕ) :
    L ^ m₀ ∣ L * torusSeq L m₀ n := by
  obtain ⟨q, hq⟩ := torusSeq_dvd (L := L) m₀ n
  refine ⟨L * q, ?_⟩
  rw [hq]
  ring

/-- The infinite-volume polymer predicate agrees at each inherited level. -/
theorem oldInfPoly_iff_newInfPoly {m₀ j : ℕ} (hjk : j ≤ k)
    (X' : Finset (Fin d → ℤ)) :
    InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X' ↔
      InfPoly (L := L) (m₁ := m₁) (k := k + 1) m₀ j X' := by
  let Q := L * L ^ (m₀ + m₁)
  have hsmall : ∀ᶠ n in atTop,
      ZSmall (torusSeq L m₀ n * L ^ m₁ * L ^ (k - j)) Q X' :=
    eventually_zsmall_margin (L := L) (m₁ := m₁) (k := k) m₀ j Q X'
  constructor
  · intro hOld
    apply (infPoly_iff (L := L) (m₁ := m₁) (k := k + 1) m₀ j X').2
    have hp := (infPoly_iff (L := L) (m₁ := m₁) (k := k) m₀ j X').1 hOld
    filter_upwards [hp, hsmall] with n hpoly hs
    have hN : L ^ m₀ ∣ torusSeq L m₀ n := torusSeq_dvd m₀ n
    have hNL : L ^ m₀ ∣ L * torusSeq L m₀ n := torusSeq_dvd_L_mul m₀ n
    have hsL : ZSmall ((L * torusSeq L m₀ n) * L ^ m₁ * L ^ (k - j)) 0 X' :=
      zsmall_mono (oldBlockSide_le_large (L := L) (m₁ := m₁) (k := k)
        (torusSeq L m₀ n) j) (Nat.zero_le _) hs
    have hpL := isPolyDom_transfer (N₁ := torusSeq L m₀ n)
      (N₂ := L * torusSeq L m₀ n) hjk hN hNL hs hsL hpoly
    have hnew := (oldTorusEquiv_isPolyDom_iff (N₁ := torusSeq L m₀ n)
      (m₁ := m₁) (k := k)).1 hpL
    simpa only [liftOldPoly_Ypoly (N₁ := torusSeq L m₀ n) (m₁ := m₁) hjk X'] using hnew
  · intro hNew
    apply (infPoly_iff (L := L) (m₁ := m₁) (k := k) m₀ j X').2
    have hp := (infPoly_iff (L := L) (m₁ := m₁) (k := k + 1) m₀ j X').1 hNew
    filter_upwards [hp, hsmall] with n hpoly hs
    have hN : L ^ m₀ ∣ torusSeq L m₀ n := torusSeq_dvd m₀ n
    have hNL : L ^ m₀ ∣ L * torusSeq L m₀ n := torusSeq_dvd_L_mul m₀ n
    have hpL : IsPolyDom (L := L) (N₁ := L * torusSeq L m₀ n)
        (m₁ := m₁) (k := k) m₀ j
        (Ypoly (L := L) (N₁ := L * torusSeq L m₀ n) (m₁ := m₁) (k := k) j X') := by
      rw [← oldTorusEquiv_symm_image_Ypoly (N₁ := torusSeq L m₀ n)
        (m₁ := m₁) hjk X']
      exact oldPoly_of_newPoly hpoly
    have hsL : ZSmall ((L * torusSeq L m₀ n) * L ^ m₁ * L ^ (k - j)) Q X' :=
      zsmall_mono (oldBlockSide_le_large (L := L) (m₁ := m₁) (k := k)
        (torusSeq L m₀ n) j) le_rfl hs
    have hs0 : ZSmall (torusSeq L m₀ n * L ^ m₁ * L ^ (k - j)) 0 X' :=
      zsmall_mono le_rfl (Nat.zero_le _) hs
    exact isPolyDom_transfer (N₁ := L * torusSeq L m₀ n)
      (N₂ := torusSeq L m₀ n) hjk hNL hN hsL hs0 hpL

end Balaban.Fluctuation
