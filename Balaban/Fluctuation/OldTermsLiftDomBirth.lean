/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftDomXi
public import Balaban.Fluctuation.OldTermsLiftClause
public import Balaban.Fluctuation.OldTermsLiftCov
public import Balaban.Fluctuation.OldTermsLiftBasic
public import Balaban.Fluctuation.OldTermsLiftAnalytic
public import Balaban.Fluctuation.LocalClassInherit
public import Balaban.SmallField.Def6v2Birth

/-!
# Inherited terms on the birth-mass domains

Under author ruling R6 the level-`j` terms keep the domain `birthXiDom` frozen at their birth mass
`ν_j L⁻²ʲ`.  If the ideal kernel sequence is unchanged by the step, the birth domain of level `j` at
scale `k + 1`, evaluated on the transported generating set and pulled back by `oldTorusEquiv`, lies
in the birth domain of level `j` at scale `k`.  Hence the clauses of the inherited levels of
`liftOldTerms` hold on the new birth domain whenever the old terms satisfy them on the old one.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Background

section Ideal

/-- The ideal kernel sequence matched at `k + 1` equals the one matched at `k` as soon as the
quantity `a_k (1 - L^{-2k})` is the same at both scales (it is the constant `a₁ (1 - L⁻²)` along the
free flow). -/
theorem aIdeal_succ_of_mul_eq {L k : ℕ} {a a' : ℝ}
    (h : a' * (1 - ((L : ℝ) ^ (k + 1))⁻¹ ^ 2) = a * (1 - ((L : ℝ) ^ k)⁻¹ ^ 2)) :
    aIdeal L (k + 1) a' = aIdeal L k a := by
  funext n
  unfold aIdeal
  rw [h]

/-- Along the free flow `a_n = compWeight L a₁ n` the ideal kernel sequences of two successive
scales agree. -/
theorem aIdeal_succ_compWeight {L k : ℕ} (hL : 2 ≤ L) (hk : 1 ≤ k) (a₁ : ℝ) :
    aIdeal L (k + 1) (compWeight L a₁ (k + 1)) = aIdeal L k (compWeight L a₁ k) := by
  rw [aIdeal_compWeight hL (by omega), aIdeal_compWeight hL hk]

end Ideal

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The birth domain of an inherited level at scale `k + 1`, pulled back, lies in the one at scale
`k`.**  The kernel sequences agree (`ha`) and the birth mass `ν_j L⁻²ʲ` is nonnegative. -/
theorem birthXiDom_lift_dom {P : Consts} {Rg : Regime L} {a : ℕ → ℝ}
    (ha : aIdeal L (k + 1) (a (k + 1)) = aIdeal L k (a k)) {j : ℕ} (hν : 0 ≤ Rg.ν j)
    (G : GeneratingSet d L ((L * N₁) * L ^ m₁) k ϱ) {Ψ h : Fld d L N₁ m₁ (k + 1) N}
    (hd : (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j (liftOldGS G) Ψ h) :
    (birthXiDom P Rg a (L * N₁) : FieldDom d L (L * N₁) m₁ k N ϱ).dom j G
      (lowerNewField Ψ) (lowerNewField h) := by
  rw [birthXiDom_dom_iff] at hd ⊢
  rw [ha] at hd
  exact liftOldGS_xiDom G (physMass_nonneg L j hν) hd

section Clauses

variable {P : Consts} {Rg : Regime L} {a : ℕ → ℝ}
  (ha : aIdeal L (k + 1) (a (k + 1)) = aIdeal L k (a k))
  {Tm : Terms d L (L * N₁) m₁ k N ϱ}
  (hcl : SFTermClauses P (birthXiDom P Rg a (L * N₁)) Tm)
  {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hν : 0 ≤ Rg.ν j)

include ha hcl hj1 hjk hν

/-- Analyticity of an inherited energy on the new birth domain. -/
theorem liftOldTerms_analyticE_birth {y : CTorus d L N₁ m₁ (k + 1)}
    {X : Set (CTorus d L N₁ m₁ (k + 1))} (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X) :
    AnalyticOnNhd ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        (liftOldTerms Tm).E j y X p.1 p.2)
      {p | (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
        ((liftOldTerms Tm).gs j X) p.1 p.2} :=
  (liftOldTerms_analyticE_on_old_domain hcl hj1 hjk hX hy).mono fun _ hp =>
    birthXiDom_lift_dom ha hν _ hp

/-- Analyticity of an inherited observable on the new birth domain. -/
theorem liftOldTerms_analyticM_birth {x : CTorus d L N₁ m₁ (k + 1)}
    {X : Set (CTorus d L N₁ m₁ (k + 1))} (hX : IsPolyDom P.m₀ j X) (hx : x ∈ X) :
    AnalyticOnNhd ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        (liftOldTerms Tm).M j x X p.1 p.2.1 p.2.2)
      {p | (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
        ((liftOldTerms Tm).gs j X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1} :=
  (liftOldTerms_analyticM_on_old_domain hcl hj1 hjk hX hx).mono fun _ hp =>
    ⟨birthXiDom_lift_dom ha hν _ hp.1, hp.2⟩

/-- The inherited energy bound on the new birth domain. -/
theorem liftOldTerms_boundE_birth {y : CTorus d L N₁ m₁ (k + 1)}
    {X : Set (CTorus d L N₁ m₁ (k + 1))} (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X)
    {Ψ h : Fld d L N₁ m₁ (k + 1) N}
    (hd : (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
      ((liftOldTerms Tm).gs j X) Ψ h) :
    ‖(liftOldTerms Tm).E j y X Ψ h‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X) :=
  liftOldTerms_boundE_on_old_domain hcl hj1 hjk hX hy (birthXiDom_lift_dom ha hν _ hd)

/-- The inherited observable bound on the new birth domain. -/
theorem liftOldTerms_boundM_birth {x : CTorus d L N₁ m₁ (k + 1)}
    {X : Set (CTorus d L N₁ m₁ (k + 1))} (hX : IsPolyDom P.m₀ j X) (hx : x ∈ X)
    {Ψ h g : Fld d L N₁ m₁ (k + 1) N}
    (hd : (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
      ((liftOldTerms Tm).gs j X) Ψ h) (hg : Def6.l1 g < 1) :
    vn ((liftOldTerms Tm).M j x X Ψ h g) <
      P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
        Real.exp (-P.κ * sizeJ P.m₀ j X) :=
  liftOldTerms_boundM_on_old_domain hcl hj1 hjk hX hx (birthXiDom_lift_dom ha hν _ hd) hg

/-- The inherited energy rotation law on the new birth domain. -/
theorem liftOldTerms_rotE_birth {y : CTorus d L N₁ m₁ (k + 1)}
    {X : Set (CTorus d L N₁ m₁ (k + 1))} (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X)
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRot R) {Ψ h : Fld d L N₁ m₁ (k + 1) N}
    (hd : (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
      ((liftOldTerms Tm).gs j X) Ψ h)
    (hRd : (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
      ((liftOldTerms Tm).gs j X) (rotField R Ψ) (rotField R h)) :
    (liftOldTerms Tm).E j y X (rotField R Ψ) (rotField R h) =
      (liftOldTerms Tm).E j y X Ψ h :=
  liftOldTerms_rotE_on_old_domain hcl hj1 hjk hX hy hR (birthXiDom_lift_dom ha hν _ hd)
    (birthXiDom_lift_dom ha hν _ hRd)

/-- The inherited observable rotation law on the new birth domain. -/
theorem liftOldTerms_rotM_birth {x : CTorus d L N₁ m₁ (k + 1)}
    {X : Set (CTorus d L N₁ m₁ (k + 1))} (hX : IsPolyDom P.m₀ j X) (hx : x ∈ X)
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRot R) {Ψ h g : Fld d L N₁ m₁ (k + 1) N}
    (hg : Def6.l1 g < 1) (hRg : Def6.l1 (rotField R g) < 1)
    (hd : (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
      ((liftOldTerms Tm).gs j X) Ψ h)
    (hRd : (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
      ((liftOldTerms Tm).gs j X) (rotField R Ψ) (rotField R h)) :
    (liftOldTerms Tm).M j x X (rotField R Ψ) (rotField R h) (rotField R g) =
      R.mulVec ((liftOldTerms Tm).M j x X Ψ h g) :=
  liftOldTerms_rotM_on_old_domain hcl hj1 hjk hX hx hR hg hRg (birthXiDom_lift_dom ha hν _ hd)
    (birthXiDom_lift_dom ha hν _ hRd)

omit hcl hj1 hjk hν ha in
theorem liftOldTerms_gs_liftOldPoly (j : ℕ) (Y : Set (CTorus d L (L * N₁) m₁ k)) :
    (liftOldTerms Tm).gs j (liftOldPoly Y) = liftOldGS (Tm.gs j Y) := by
  simp [liftOldTerms, liftOldPoly, Set.image_image]

/-- The inherited energy covariance under a conjugated old paving symmetry, on the new birth
domain. -/
theorem liftOldTerms_eucE_birth {y : CTorus d L (L * N₁) m₁ k}
    {X : Set (CTorus d L (L * N₁) m₁ k)} (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X)
    (r : Equiv.Perm (CTorus d L (L * N₁) m₁ k))
    (hr : r ∈ pavingSymGroup (N₁ := L * N₁) (m₁ := m₁) (k := k) (d := d) L P.m₀ j)
    (Ψ h : Fld d L N₁ m₁ (k + 1) N)
    (hd : (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
      ((liftOldTerms Tm).gs j (liftOldPoly X)) Ψ h)
    (hd' : (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
      ((liftOldTerms Tm).gs j (liftOldPoly (r '' X)))
      (actField (oldTorusEquiv.permCongrHom r) Ψ) (actField (oldTorusEquiv.permCongrHom r) h)) :
    (liftOldTerms Tm).E j (blockBase L j ((oldTorusEquiv.permCongrHom r) (oldTorusEquiv y)))
      ((oldTorusEquiv.permCongrHom r) '' liftOldPoly X)
      (actField (oldTorusEquiv.permCongrHom r) Ψ) (actField (oldTorusEquiv.permCongrHom r) h) =
    (liftOldTerms Tm).E j (oldTorusEquiv y) (liftOldPoly X) Ψ h := by
  rw [liftOldTerms_gs_liftOldPoly] at hd hd'
  exact liftOldTerms_eucE_on_old_domain hcl hj1 hjk hX hy r hr Ψ h
    (birthXiDom_lift_dom ha hν _ hd) (birthXiDom_lift_dom ha hν _ hd')

/-- The inherited observable covariance under a conjugated old paving symmetry, on the new birth
domain. -/
theorem liftOldTerms_eucM_birth {x : CTorus d L (L * N₁) m₁ k}
    {X : Set (CTorus d L (L * N₁) m₁ k)} (hX : IsPolyDom P.m₀ j X) (hx : x ∈ X)
    (r : Equiv.Perm (CTorus d L (L * N₁) m₁ k))
    (hr : r ∈ pavingSymGroup (N₁ := L * N₁) (m₁ := m₁) (k := k) (d := d) L P.m₀ j)
    (Ψ h g : Fld d L N₁ m₁ (k + 1) N)
    (hd : (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
      ((liftOldTerms Tm).gs j (liftOldPoly X)) Ψ h)
    (hd' : (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
      ((liftOldTerms Tm).gs j (liftOldPoly (r '' X)))
      (actField (oldTorusEquiv.permCongrHom r) Ψ) (actField (oldTorusEquiv.permCongrHom r) h)) :
    (liftOldTerms Tm).M j ((oldTorusEquiv.permCongrHom r) (oldTorusEquiv x))
      ((oldTorusEquiv.permCongrHom r) '' liftOldPoly X)
      (actField (oldTorusEquiv.permCongrHom r) Ψ) (actField (oldTorusEquiv.permCongrHom r) h)
      (actField (oldTorusEquiv.permCongrHom r) g) =
    (liftOldTerms Tm).M j (oldTorusEquiv x) (liftOldPoly X) Ψ h g := by
  rw [liftOldTerms_gs_liftOldPoly] at hd hd'
  exact liftOldTerms_eucM_on_old_domain hcl hj1 hjk hX hx r hr Ψ h g
    (birthXiDom_lift_dom ha hν _ hd) (birthXiDom_lift_dom ha hν _ hd')

/-- The full-lattice covariance of the inherited local energy sum, on the new birth domain. -/
theorem liftOldTerms_eucEloc_birth (y : CTorus d L (L * N₁) m₁ k)
    (r : Equiv.Perm (CTorus d L (L * N₁) m₁ k))
    (hr : r ∈ fullJSymGroup (N₁ := L * N₁) (m₁ := m₁) (k := k) (d := d) L j)
    (Ψ h : Fld d L N₁ m₁ (k + 1) N)
    (hd : (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
      (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j (Nat.le_succ_of_le hjk)) Ψ h)
    (hd' : (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
      (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j (Nat.le_succ_of_le hjk))
      (actField (oldTorusEquiv.permCongrHom r) Ψ) (actField (oldTorusEquiv.permCongrHom r) h)) :
    Eloc P.m₀ (liftOldTerms Tm) j
      (blockBase L j ((oldTorusEquiv.permCongrHom r) (oldTorusEquiv y)))
      (actField (oldTorusEquiv.permCongrHom r) Ψ) (actField (oldTorusEquiv.permCongrHom r) h) =
    Eloc P.m₀ (liftOldTerms Tm) j (oldTorusEquiv y) Ψ h := by
  rw [← liftOldGS_levelGS (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) hjk] at hd hd'
  exact liftOldTerms_eucEloc_on_old_domain hcl hj1 hjk y r hr Ψ h
    (birthXiDom_lift_dom ha hν _ hd) (birthXiDom_lift_dom ha hν _ hd')

/-- The full-lattice covariance of the inherited local observable sum, on the new birth domain. -/
theorem liftOldTerms_eucMloc_birth (x : CTorus d L (L * N₁) m₁ k)
    (r : Equiv.Perm (CTorus d L (L * N₁) m₁ k))
    (hr : r ∈ fullJSymGroup (N₁ := L * N₁) (m₁ := m₁) (k := k) (d := d) L j)
    (Ψ h g : Fld d L N₁ m₁ (k + 1) N)
    (hd : (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
      (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j (Nat.le_succ_of_le hjk)) Ψ h)
    (hd' : (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
      (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j (Nat.le_succ_of_le hjk))
      (actField (oldTorusEquiv.permCongrHom r) Ψ) (actField (oldTorusEquiv.permCongrHom r) h)) :
    Mloc P.m₀ (liftOldTerms Tm) j ((oldTorusEquiv.permCongrHom r) (oldTorusEquiv x))
      (actField (oldTorusEquiv.permCongrHom r) Ψ) (actField (oldTorusEquiv.permCongrHom r) h)
      (actField (oldTorusEquiv.permCongrHom r) g) =
    Mloc P.m₀ (liftOldTerms Tm) j (oldTorusEquiv x) Ψ h g := by
  rw [← liftOldGS_levelGS (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) hjk] at hd hd'
  exact liftOldTerms_eucMloc_on_old_domain hcl hj1 hjk x r hr Ψ h g
    (birthXiDom_lift_dom ha hν _ hd) (birthXiDom_lift_dom ha hν _ hd')

end Clauses

end Balaban.Fluctuation
