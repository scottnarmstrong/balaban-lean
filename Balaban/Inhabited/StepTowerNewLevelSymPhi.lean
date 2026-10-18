/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelSymInt
public import Balaban.Inhabited.StepTowerNewLevelSymData
public import Balaban.Inhabited.StepTowerNewLevelSymOld
public import Balaban.Inhabited.StepTowerNewLevelSymCov

/-!
# The exponent `Φ₁` of the new level under a lattice symmetry (`StepTowerNewLevelSymPhi`)

`Φ₁(ψ') = -β_k V^{(k)}(ψ') + δℰ_k(ψ')` (P4 (2.56)) at the block datum `θ = D` is transported by a
lattice symmetry `σ` of the full level group: `Φ₁^{σ D}(y ∘ u⁻¹) = Φ₁^{D}(y)` (`Phi1H_sym`).  The
interaction part is `interactionV_sym` with the transported tangent (`compTangent_sym`); the old
energy part is `EcompAtC_sym`, which needs the old composed pairs of the shifted data and of their
transports to lie in the domain of the level sets (the clause `eucEloc` holds there only).
-/

@[expose] public section

namespace Balaban.Inhabited.StepSym

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.Localization.DecEquiv Balaban.Localization.DetUnitIncidence Matrix

section Phi

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable (C : StepClass d L N₁ m₁ k N ϱ)
variable (Sy : LatSymm S.G' S.G' σ) (Sk : LatSymm (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) σ)
  (hU : UnitBlockPres σ)

include Sy Sk in
theorem compTangent_sym (D : BgData S.G' N)
    (E : BgData (stepG d L N₁ m₁ k ϱ) N) :
    compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) (Sy.sym D)) (Sy.sym D) (Sk.sym E) =
      symSite σ (compTangent S.hG S.hG' (le_refl (k + 1)) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) D E) := by
  have hb := (Sy.bgFieldC_sym S.a S.ν (bgC0 d L N) D).1
  have hc := composeData_sym_pair Sk Sy (S.hG.precedes S.hG' (le_refl (k + 1)))
    (S.hG.precedes S.hG' (le_refl (k + 1))) S.a (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) D
  rw [hb]
  funext x i
  unfold compTangent
  rw [hc]
  rfl

variable {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}

include Sy Sk hU in
/-- **`Φ₁` is covariant under a lattice symmetry**: `Φ₁^{σ D}(y ∘ u⁻¹) = Φ₁^{D}(y)`, for block data
`D` of the old class `C` whose old composed pairs at the shifts `ψ^{(k)} + y` and `ψ^{(k)}` and at
their transports lie in the domain of the level sets (the clause `eucEloc` of the old class). -/
theorem Phi1H_sym (hcl : SFTermClauses P Dom C.Tm) (hm : P.m₀ = C.m₀)
    (hσ : σ ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1))
    (D : BgData S.G' N) (y : S.EC)
    (hd1 : ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
      Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + y))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + y))).2)
    (hd1' : ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
      Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          (Sk.sym ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + y)))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          (Sk.sym ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + y)))).2)
    (hd0 : ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
      Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH (S.withDatumH D).psi0H)).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH (S.withDatumH D).psi0H)).2)
    (hd0' : ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
      Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          (Sk.sym ((S.withDatumH D).dataUCH (S.withDatumH D).psi0H))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          (Sk.sym ((S.withDatumH D).dataUCH (S.withDatumH D).psi0H))).2) :
    (S.withDatumH (Sy.sym D)).Phi1H C
        (fun r => y ((unitAct S.G' Sy hU).symm r.1, r.2)) = (S.withDatumH D).Phi1H C y := by
  have hD' : ∀ D : BgData S.G' N, (S.withDatumH D).D' = D := fun _ => rfl
  have hpsi : (S.withDatumH (Sy.sym D)).psi0H +
      (fun r => y ((unitAct S.G' Sy hU).symm r.1, r.2)) =
      fun r => ((S.withDatumH D).psi0H + y) ((unitAct S.G' Sy hU).symm r.1, r.2) := by
    rw [psi0H_sym Sy Sk hU D]; rfl
  have hdat := dataUCH_sym Sy Sk hU D ((S.withDatumH D).psi0H + y)
  have hdat0 := dataUCH_sym Sy Sk hU D (S.withDatumH D).psi0H
  have hpsi0 : (S.withDatumH (Sy.sym D)).psi0H =
      fun r => (S.withDatumH D).psi0H ((unitAct S.G' Sy hU).symm r.1, r.2) :=
    psi0H_sym Sy Sk hU D
  unfold StepSettingH.Phi1H
  rw [hpsi, hdat, hpsi0, hdat0]
  simp only [hD']
  have hmult := (Sy.bgFieldC_sym S.a S.ν (bgC0 d L N) D).2
  have hfld := (Sy.bgFieldC_sym S.a S.ν (bgC0 d L N) D).1
  have hfldk := (Sk.bgFieldC_sym S.a S.ν (bgC0 d L N) ((S.withDatumH D).dataUCH
    ((S.withDatumH D).psi0H + y))).1
  have hI := interactionV_sym Sk Sy (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) D) (bgFieldC S.G' S.a S.ν (bgC0 d L N) D)
    (compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) D ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + y)))
    (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + y)) -
      (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ (bgFieldC S.G' S.a S.ν (bgC0 d L N) D))
  have hE1 := EcompAtC_sym (P := P) (Dom := Dom) (Tm := C.Tm) (a := S.a) (ν := S.ν) hcl hσ Sk
    ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + y)) hd1 hd1'
  have hE0 := EcompAtC_sym (P := P) (Dom := Dom) (Tm := C.Tm) (a := S.a) (ν := S.ν) hcl hσ Sk
    ((S.withDatumH D).dataUCH (S.withDatumH D).psi0H) hd0 hd0'
  rw [hm] at hE1 hE0
  have hrest := restrictφ_sym Sk Sy (S.hG.precedes S.hG' (le_refl (k + 1)))
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) D)
  rw [compTangent_sym Sy Sk D, hE1, hE0]
  have hsub : ∀ X Y : (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ, Sk.fld X - Sk.fld Y = Sk.fld (X - Y) :=
    fun _ _ => rfl
  rw [hmult, hfld, hfldk, hrest, hsub, hI]

end Phi
end Balaban.Inhabited.StepSym
