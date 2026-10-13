/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.LocalGeneratorAmbientGeometry
public import Balaban.SmallField.LocalGeneratorClassDomain
public import Balaban.LargeField.GlobalGenRegional

/-!
# Raw data of a proper local generator

The physical whole-level pair is a field on the whole torus. A datum of a proper local
generator is zero outside its data sites. Thus the two raw fields cannot be globally equal
when the whole-level pair belongs to its complex union domain.
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField
  Balaban.SmallField Balaban.SmallField.Def6 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  {j : ℕ} {hj : j ≤ k} {X : Set (CTorus d L N₁ m₁ k)}
  {hsep : ϱ ≤ minSep L (L ^ m₁)}

/-- Global equality of a raw spin field with a local datum forces that field to vanish
outside the local data sites. -/
theorem raw_eq_localB_zero_outside {Ψ : CTorus d L N₁ m₁ k → Fin N → ℂ}
    (D : BgData (localB j hj X hsep) N) (hΨ : D.Ψ = Ψ)
    {x : CTorus d L N₁ m₁ k} (hx : x ∉ dataSites (localB j hj X hsep)) (i : Fin N) :
    Ψ x i = 0 := by
  rw [← hΨ]
  exact congrFun (D.Ψ_zero x hx) i

/-- A datum in the whole-level complex union domain has a nonzero spin vector at every site.
Consequently, on a proper local generator it cannot be the full raw spin field of a local datum. -/
theorem no_localB_raw_eq_of_ambient_union (hd : 0 < d) (hj1 : 1 ≤ j)
    {Damb : BgData
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') j hj) N}
    {μ : ℝ} (hAmb : InUnionDomainC _ (bgC0 d L N) (bgC1 d L N) μ Damb)
    {x : CTorus d L N₁ m₁ k} (hx : x ∉ dataSites (localB j hj X hsep)) :
    ¬ ∃ Dloc : BgData (localB j hj X hsep) N, Dloc.Ψ = Damb.Ψ := by
  rintro ⟨Dloc, hΨ⟩
  have hxamb : x ∈ dataSites
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') j hj) :=
    (mem_dataSites _).2 (Or.inl (by simp [levelGS, hj1]))
  exact GlobalGenRegional.no_zero_on_dataSites_of_inUnionDomainC hd _ hAmb hxamb
    (fun i => raw_eq_localB_zero_outside Dloc hΨ hx i)

/-- In particular, no choice of local chart radius can make a whole-level chart datum the
globally equal raw datum of a proper local generator. -/
theorem no_localB_xiCData_of_ambient_xiCData (hd : 0 < d) (hj1 : 1 ≤ j)
    {A : ℕ → ℝ} {μ σ ε εloc : ℝ}
    {Damb : BgData
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') j hj) N}
    (hAmb : XiCData _ A μ j σ ε Damb)
    {x : CTorus d L N₁ m₁ k} (hx : x ∉ dataSites (localB j hj X hsep)) :
    ¬ ∃ Dloc : BgData (localB j hj X hsep) N,
        Dloc.Ψ = Damb.Ψ ∧ Dloc.h = Damb.h ∧
          XiCData (localB j hj X hsep) A μ j (scaledC0 d) εloc Dloc := by
  rintro ⟨Dloc, hΨ, _, _⟩
  exact no_localB_raw_eq_of_ambient_union hd hj1 (xiCData_unionC hAmb) hx ⟨Dloc, hΨ⟩

end Balaban.SmallField.GsSpec
