/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2

/-!
# The fine torus at two successive scale descriptions

At fixed physical circumference, the scale-`k` description with side parameter `L * N₁`
and the scale-`k + 1` description with side parameter `N₁` have the same fine sites.
The equivalence below is induced by equality of the two moduli.  It is the geometric
starting point for transporting the old class terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.Multiscale

variable {d L N₁ m₁ k N : ℕ}

/-- Equality of the physical fine side in the two descriptions. -/
theorem oldSide_eq_newSide :
    ((L * N₁) * L ^ m₁) * L ^ k = (N₁ * L ^ m₁) * L ^ (k + 1) := by
  rw [pow_succ]
  ring

/-- The identity of fine sites after rewriting the modulus of the torus. -/
def oldTorusEquiv :
    CTorus d L (L * N₁) m₁ k ≃ CTorus d L N₁ m₁ (k + 1) :=
  Equiv.cast (congrArg (Torus d) (oldSide_eq_newSide (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)))

/-- Pull a fine field forward to the scale-`k + 1` description. -/
def liftOldField (f : Fld d L (L * N₁) m₁ k N) :
    Fld d L N₁ m₁ (k + 1) N :=
  fun x => f (oldTorusEquiv.symm x)

/-- Pull a fine field back to the scale-`k` description. -/
def lowerNewField (f : Fld d L N₁ m₁ (k + 1) N) :
    Fld d L (L * N₁) m₁ k N :=
  fun x => f (oldTorusEquiv x)

theorem lowerNewField_liftOldField (f : Fld d L (L * N₁) m₁ k N) :
    lowerNewField (liftOldField f) = f := by
  funext x
  simp [lowerNewField, liftOldField]

theorem liftOldField_lowerNewField (f : Fld d L N₁ m₁ (k + 1) N) :
    liftOldField (lowerNewField f) = f := by
  funext x
  simp [lowerNewField, liftOldField]

/-- Transport a polymer by the physical-site equivalence. -/
def liftOldPoly (X : Set (CTorus d L (L * N₁) m₁ k)) :
    Set (CTorus d L N₁ m₁ (k + 1)) := oldTorusEquiv '' X

theorem mem_liftOldPoly {X : Set (CTorus d L (L * N₁) m₁ k)}
    {x : CTorus d L N₁ m₁ (k + 1)} :
    x ∈ liftOldPoly X ↔ oldTorusEquiv.symm x ∈ X := by
  simp [liftOldPoly]

/-- Transport a finite collection of fine sites. -/
def liftOldSites (X : Finset (CTorus d L (L * N₁) m₁ k)) :
    Finset (CTorus d L N₁ m₁ (k + 1)) := X.map oldTorusEquiv.toEmbedding

theorem mem_liftOldSites {X : Finset (CTorus d L (L * N₁) m₁ k)}
    {x : CTorus d L N₁ m₁ (k + 1)} :
    x ∈ liftOldSites X ↔ oldTorusEquiv.symm x ∈ X := by
  simp [liftOldSites]

/-- The equivalence is the existing lattice cast at the equality of physical sides. -/
private theorem equivCast_eq_castT {n m : ℕ} (h : n = m) (x : Torus d n) :
    Equiv.cast (congrArg (Torus d) h) x = castT h x := by
  cases h
  rfl

theorem oldTorusEquiv_apply (x : CTorus d L (L * N₁) m₁ k) :
    oldTorusEquiv x = castT (oldSide_eq_newSide (L := L) (N₁ := N₁)
      (m₁ := m₁) (k := k)) x := by
  exact equivCast_eq_castT _ x

/-- The coordinate residue is unchanged by the physical-site identification. -/
theorem oldTorusEquiv_val (x : CTorus d L (L * N₁) m₁ k) (i : Fin d) :
    ((oldTorusEquiv x) i).val = (x i).val := by
  rw [oldTorusEquiv_apply]
  exact castT_val _ x i

/-- The old and new descriptions have the same `j`-blocks of fine sites. -/
theorem oldTorusEquiv_jBlock_iff [NeZero L] [NeZero N₁] {j : ℕ} (hj : j ≤ k)
    (x x' : CTorus d L (L * N₁) m₁ k) :
    jBlock d L (N₁ * L ^ m₁) (k + 1) j (oldTorusEquiv x) =
        jBlock d L (N₁ * L ^ m₁) (k + 1) j (oldTorusEquiv x') ↔
      jBlock d L ((L * N₁) * L ^ m₁) k j x =
        jBlock d L ((L * N₁) * L ^ m₁) k j x' := by
  have hnew := side_eq (N₀ := N₁ * L ^ m₁) (L := L) (k := k + 1) (j := j)
    (Nat.le_succ_of_le hj)
  have hold := side_eq (N₀ := (L * N₁) * L ^ m₁) (L := L) (k := k) (j := j) hj
  simp only [jBlock]
  rw [blockMap_eq_iff_val hnew, blockMap_eq_iff_val hold]
  simp only [oldTorusEquiv_val]

/-- Transport a generating set, adding an empty highest layer at the successor scale. -/
noncomputable def liftOldGS [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (G : GeneratingSet d L ((L * N₁) * L ^ m₁) k ϱ) :
    GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ where
  Ω := fun j => if j ≤ k then liftOldSites (G.Ω j) else ∅
  top := by simp
  subset := by
    intro j hj hjK
    by_cases hjk : j < k
    · have hjk' : j + 1 ≤ k := by omega
      simp only [ite_eq_left hjk', ite_eq_left (Nat.le_of_lt hjk)]
      intro x hx
      exact mem_liftOldSites.mpr
        (G.subset j hj (Nat.le_of_lt hjk) (mem_liftOldSites.mp hx))
    · have hjk' : ¬ j + 1 ≤ k := by omega
      simp [hjk']
  blockUnion := by
    intro j hj hjK x x' hxx
    by_cases hjk : j ≤ k
    · have hblock := (oldTorusEquiv_jBlock_iff (N₁ := N₁) (m₁ := m₁) (k := k) hjk
        (oldTorusEquiv.symm x) (oldTorusEquiv.symm x')).mp (by simpa using hxx)
      simpa [hjk, mem_liftOldSites] using G.blockUnion j hj hjk _ _ hblock
    · simp [hjk]
  separation := by
    intro j hj hjK x hx y hy
    by_cases hjk : j < k
    · have hjk1 : j + 1 ≤ k := by omega
      have hxold : oldTorusEquiv.symm x ∉ G.Ω j := by
        simpa [Nat.le_of_lt hjk, mem_liftOldSites] using hx
      have hyold : oldTorusEquiv.symm y ∈ G.Ω (j + 1) := by
        simpa [hjk1, mem_liftOldSites] using hy
      have hdist := G.separation j hj hjk _ hxold _ hyold
      rw [← torusDist_castT (oldSide_eq_newSide (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k)) (oldTorusEquiv.symm x) (oldTorusEquiv.symm y)] at hdist
      rw [← oldTorusEquiv_apply, ← oldTorusEquiv_apply] at hdist
      simpa using hdist
    · have hjk' : ¬ j + 1 ≤ k := by omega
      simp [hjk'] at hy

theorem liftOldGS_Ω [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (G : GeneratingSet d L ((L * N₁) * L ^ m₁) k ϱ) {j : ℕ} (hj : j ≤ k) :
    (liftOldGS G).Ω j = liftOldSites (G.Ω j) := by
  simp [liftOldGS, hj]

theorem liftOldGS_Ω_top [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (G : GeneratingSet d L ((L * N₁) * L ^ m₁) k ϱ) :
    (liftOldGS G).Ω (k + 1) = ∅ := by
  simp [liftOldGS]

theorem liftOldGS_mem_Ω [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (G : GeneratingSet d L ((L * N₁) * L ^ m₁) k ϱ) {j : ℕ} (hj : j ≤ k)
    (x : CTorus d L (L * N₁) m₁ k) :
    oldTorusEquiv x ∈ (liftOldGS G).Ω j ↔ x ∈ G.Ω j := by
  rw [liftOldGS_Ω G hj, mem_liftOldSites]
  simp

theorem liftOldGS_mem_layer [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (G : GeneratingSet d L ((L * N₁) * L ^ m₁) k ϱ) {j : ℕ} (hj : j ≤ k)
    (x : CTorus d L (L * N₁) m₁ k) :
    oldTorusEquiv x ∈ (liftOldGS G).layer j ↔ x ∈ G.layer j := by
  rw [GeneratingSet.mem_layer, GeneratingSet.mem_layer, liftOldGS_mem_Ω G hj]
  by_cases hj' : j < k
  · rw [liftOldGS_mem_Ω G (by omega)]
  · have hjk : j = k := by omega
    subst j
    simp [liftOldGS_Ω_top, G.top]

theorem liftOldGS_layerIndex [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (G : GeneratingSet d L ((L * N₁) * L ^ m₁) k ϱ)
    (x : CTorus d L (L * N₁) m₁ k) (hx : x ∈ G.Ω 1) :
    (liftOldGS G).layerIndex (oldTorusEquiv x) = G.layerIndex x := by
  obtain ⟨hj1, hjk, hmem⟩ := G.layerIndex_spec hx
  apply (liftOldGS G).layerIndex_eq hj1 (Nat.le_succ_of_le hjk)
  exact (liftOldGS_mem_layer G hjk x).2 hmem

/-- Relabel the inherited term functions and their generating sets on the physical torus.
The newly born level is zero here; a successor construction supplies its own terms. -/
noncomputable def liftOldTerms [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (Tm : Terms d L (L * N₁) m₁ k N ϱ) : Terms d L N₁ m₁ (k + 1) N ϱ where
  E j y X Ψ h := if j ≤ k then
      Tm.E j (oldTorusEquiv.symm y) (oldTorusEquiv.symm '' X)
        (lowerNewField Ψ) (lowerNewField h) else 0
  M j x X Ψ h g := if j ≤ k then
      Tm.M j (oldTorusEquiv.symm x) (oldTorusEquiv.symm '' X)
        (lowerNewField Ψ) (lowerNewField h) (lowerNewField g) else 0
  gs j X := liftOldGS (Tm.gs j (oldTorusEquiv.symm '' X))

theorem liftOldTerms_E [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (Tm : Terms d L (L * N₁) m₁ k N ϱ) {j : ℕ} (hj : j ≤ k)
    (y : CTorus d L N₁ m₁ (k + 1)) (X : Set (CTorus d L N₁ m₁ (k + 1)))
    (Ψ h : Fld d L N₁ m₁ (k + 1) N) :
    (liftOldTerms Tm).E j y X Ψ h = Tm.E j (oldTorusEquiv.symm y)
      (oldTorusEquiv.symm '' X) (lowerNewField Ψ) (lowerNewField h) := by
  simp [liftOldTerms, hj]

theorem liftOldTerms_M [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (Tm : Terms d L (L * N₁) m₁ k N ϱ) {j : ℕ} (hj : j ≤ k)
    (x : CTorus d L N₁ m₁ (k + 1)) (X : Set (CTorus d L N₁ m₁ (k + 1)))
    (Ψ h g : Fld d L N₁ m₁ (k + 1) N) :
    (liftOldTerms Tm).M j x X Ψ h g = Tm.M j (oldTorusEquiv.symm x)
      (oldTorusEquiv.symm '' X) (lowerNewField Ψ) (lowerNewField h)
      (lowerNewField g) := by
  simp [liftOldTerms, hj]

/-- Local dependence of an inherited energy term survives the site relabeling. -/
theorem liftOldTerms_localE [NeZero L] [NeZero N₁] {ϱ : ℝ}
    {P : Consts} {Dom : FieldDom d L (L * N₁) m₁ k N ϱ}
    {Tm : Terms d L (L * N₁) m₁ k N ϱ} (hcl : SFTermClauses P Dom Tm)
    (j : ℕ) (y : CTorus d L N₁ m₁ (k + 1))
    (X : Set (CTorus d L N₁ m₁ (k + 1)))
    (Ψ Ψ' h h' : Fld d L N₁ m₁ (k + 1) N)
    (hagree : ∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) :
    (liftOldTerms Tm).E j y X Ψ h = (liftOldTerms Tm).E j y X Ψ' h' := by
  by_cases hj : j ≤ k
  · simp only [liftOldTerms_E Tm hj]
    apply hcl.localE
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    simpa [lowerNewField] using hagree x hx
  · simp [liftOldTerms, hj]

/-- Local dependence of an inherited observable term survives the site relabeling. -/
theorem liftOldTerms_localM [NeZero L] [NeZero N₁] {ϱ : ℝ}
    {P : Consts} {Dom : FieldDom d L (L * N₁) m₁ k N ϱ}
    {Tm : Terms d L (L * N₁) m₁ k N ϱ} (hcl : SFTermClauses P Dom Tm)
    (j : ℕ) (x : CTorus d L N₁ m₁ (k + 1))
    (X : Set (CTorus d L N₁ m₁ (k + 1)))
    (Ψ Ψ' h h' g g' : Fld d L N₁ m₁ (k + 1) N)
    (hagree : ∀ z ∈ X, Ψ z = Ψ' z ∧ h z = h' z ∧ g z = g' z) :
    (liftOldTerms Tm).M j x X Ψ h g = (liftOldTerms Tm).M j x X Ψ' h' g' := by
  by_cases hj : j ≤ k
  · simp only [liftOldTerms_M Tm hj]
    apply hcl.localM
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    simpa [lowerNewField] using hagree w hw
  · simp [liftOldTerms, hj]

/-- Apply the physical-torus relabeling coherently to every member of an old family. -/
noncomputable def liftOldTermsFam [NeZero L] {m₁ k N : ℕ} {ϱ : ℝ}
    (Tm : ∀ (N₂ : ℕ) [NeZero N₂], Terms d L N₂ m₁ k N ϱ) :
    ∀ (N₂ : ℕ) [NeZero N₂], Terms d L N₂ m₁ (k + 1) N ϱ :=
  fun N₂ _ => liftOldTerms (Tm (L * N₂))

theorem liftOldTermsFam_apply [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (Tm : ∀ (N₂ : ℕ) [NeZero N₂], Terms d L N₂ m₁ k N ϱ) :
    liftOldTermsFam Tm N₁ = liftOldTerms (Tm (L * N₁)) := rfl

end Balaban.Fluctuation
