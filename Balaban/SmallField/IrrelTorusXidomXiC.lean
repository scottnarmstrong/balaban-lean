/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomChart

/-!
# Anisotropic data directly from a complex step chart

The source chart provides the real and complex composition fields and the sharp square estimate.
The same-mass chart inclusion and level-j second difference remain explicit premises.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField.Def6 Balaban.SmallField.GsSpec

variable {d L N₁ m₁ k N j : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
  {G' : GeneratingSet d L (N₁ * L ^ m₁) k ϱ'}
  {a : ℕ → ℝ} {a₁ ν s e ε K₂ : ℝ}
  {Ψ0 : CTorus d L N₁ m₁ k → Fin N → ℝ} {h0 : Fin N → ℝ}
  {Ψ'' h'' : CTorus d L N₁ m₁ k → Fin N → ℂ}

/-- The complex chart at the upper scale yields a level-lattice anisotropic datum. The
two hypotheses after choosing the composition witness are precisely the same-mass class chart
and P1's second-difference estimate. -/
theorem xiC_dataHypAniso_of_levelGS
    (hL : 2 ≤ L) (hj1 : 1 ≤ j) (hjk : j < k)
    (H' : BgHyp d L k ϱ' a ν)
    (hprec : Precedes (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
      (ϱ := ϱ) j hjk.le) G')
    (ha₁ : 0 < a₁) (hs : 0 < s) (hs1 : s ≤ 1)
    (hjs : (L : ℝ) ^ j = s * (L : ℝ) ^ k)
    (hgap : ScaleGap (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
      (ϱ := ϱ) j hjk.le) G' s)
    (hcol : ∀ z ∈ collar (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k) (ϱ := ϱ) j hjk.le), z ∈ G'.Ω 1 ∧ 1 ≤ s * G'.spacing z)
    (hsmall : (4 * d + 6) * (xiC1 d * e) ≤ 1)
    (hX : XiC G' a ν k 1 e Ψ0 h0 Ψ'' h'')
    (y : CTorus d L N₁ m₁ k) (f : Site d → CTorus d L N₁ m₁ k)
    (hf : f = fun x => y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)
    (hν : 0 < ν * ((L : ℝ) ^ j) ^ 2)
    (hτ1 : scaledC0 d * s ≤ 1)
    (hντ : ν * ((L : ℝ) ^ j) ^ 2 ≤ (scaledC0 d * s) ^ 2)
    (hζ1 : xiC1 d * e ≤ 1 / 200) (hee : e ≤ ε)
    (hK₂ : 0 ≤ K₂) :
    ∃ φr φc : G'.Ω 1 × Fin N → ℂ,
      ScaledPsiC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
        (ϱ := ϱ) j hjk.le) ν (scaledC0 d * s) (xiC1 d * e) j
        (reR (levelGS (ϱ := ϱ) j hjk.le) G' a₁ φr Ψ0) h0
        (dPsi (levelGS (ϱ := ϱ) j hjk.le) G' a₁ φr φc Ψ0 Ψ'')
        (hRes (levelGS (ϱ := ϱ) j hjk.le) h'') ∧
      ∀ (ψ : Site d → Spin N) (b : Spin N),
        (∀ x i, ψ x i =
          (reR (levelGS (ϱ := ϱ) j hjk.le) G' a₁ φr Ψ0 (f x) i : ℂ) +
          dPsi (levelGS (ϱ := ϱ) j hjk.le) G' a₁ φr φc Ψ0 Ψ'' (f x) i) →
        b = (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) •
          fun i => (h0 i : ℂ) + hRes (levelGS (ϱ := ϱ) j hjk.le) h'' (f 0) i) →
        ∀ {Dom : Set ((Site d → Spin N) × Spin N)},
          (ψ, b) ∈ Dom ∧ ((fun _ => ψ 0), b) ∈ Dom →
          (∀ x μ μ', ‖ψ (x + Pi.single μ 1 + Pi.single μ' 1) -
            ψ (x + Pi.single μ 1) - ψ (x + Pi.single μ' 1) + ψ x‖ ≤ K₂) →
          DataHypAniso Dom (ν * ((L : ℝ) ^ j) ^ 2)
            (16 * scaledC0 d * xiC1 d * s) ε K₂ ψ b := by
  have hnj : ∀ x ∈
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
        (ϱ := ϱ) j hjk.le).Ω 1,
      (levelGS (ϱ := ϱ) j hjk.le).layerIndex x ≤ j := by
    intro x hx
    rw [levelGS_layerIndex hj1 hjk.le]
  obtain ⟨φr, φc, H, _, hsharp⟩ := xiC_scaledComposition_square_sharp H'
    hprec hL ha₁ hs hs1 hjs hnj hgap hcol hsmall hX
  refine ⟨φr, φc, H, ?_⟩
  intro ψ b hψ hb Dom hchart hsec
  have he : 0 < e := hX.2.1
  exact ScaledPsiC.dataHypAniso_of_levelGS_scaled hL hj1 hjk H y f hf ψ b
    hψ hb (fun x => hsharp (f x) (by rw [hf]; simp [levelGS_Ω, hj1]))
    hν hs hτ1 hντ he hζ1 hee hchart hK₂ hsec

end Balaban.SmallField
