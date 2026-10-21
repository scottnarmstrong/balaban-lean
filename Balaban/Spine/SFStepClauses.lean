/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.InheritedBound
public import Balaban.Fluctuation.OldTermsLiftDomBirthFamily
public import Balaban.Fluctuation.LocalClassInherit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The small-field clauses of the successor of a class member

The small-field half of LF-3 (LFR Theorem IV.1.1 (e), (h); P4 Theorem 1, P5 Theorem 1) splits into
the levels `j ≤ k`, inherited from the input on the birth domains of ruling R6, and the new level
`k + 1`. `sfSucc_clauses` proves the clauses (D2), (D8), (D9) of `IsRepPre2` at the scale `k + 1`
for small-field data `sf'` that inherit the running constants and the terms of `sf` at the levels
`j ≤ k`, from the clauses of the input class and the clauses of the new level alone:

* the term clauses, the strong specification of the generating sets and torus independence of the
  new level, stated on `newLevelTerms` (the levels `j > k` of a family, with vanishing terms and the
  whole-level generating sets below);
* (H.6) and (H.5) at `k + 1`; the reality of the density exponent (H.1) at `k + 1`
  (`exists_isSF2_of_real`); P5 H4 for `ℛ^{(k+1)}` with `½ β_{k+1}^{-m-1}`; (D8) of the new level and
  of `ℛ^{(k+1)}`.

The inherited levels are the landed bridges `sfTermClauses_splice_birth`, `gsStrong_splice`,
`torusIndep_splice`, `renorm_splice_birth` (general `d, L, N`, birth domains), with the old clauses
moved to the domain of the new data by `sfTermClauses_congr_le` and (D8) of the inherited terms by
`liftOldTermsFam_M_eq_of_d8`.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation
  Balaban.Localization Balaban.Background Balaban.Multiscale

namespace Balaban.RootFSpine

section NewLevel

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The new level of a family of terms of scale `k + 1`**: the terms `ℰ^{(j)}`, `ℳ^{(j)}` of the
levels `j > k` of `T`, with vanishing terms and the whole-level generating sets `levelGS j` at the
levels `j ≤ k`. The clauses of `SFTermClauses` on it are those of the levels `j > k` of `T`. -/
noncomputable def newLevelTerms (T : Terms d L N₁ m₁ (k + 1) N ϱ) : Terms d L N₁ m₁ (k + 1) N ϱ where
  E j := if j ≤ k then 0 else T.E j
  M j := if j ≤ k then 0 else T.M j
  gs j X := if h : j ≤ k then levelGS j (h.trans k.le_succ) else T.gs j X

variable (T : Terms d L N₁ m₁ (k + 1) N ϱ)

theorem newLevelTerms_E {j : ℕ} (hj : ¬ j ≤ k) : (newLevelTerms T).E j = T.E j := by
  simp [newLevelTerms, hj]

theorem newLevelTerms_M {j : ℕ} (hj : ¬ j ≤ k) : (newLevelTerms T).M j = T.M j := by
  simp [newLevelTerms, hj]

theorem newLevelTerms_gs {j : ℕ} (hj : ¬ j ≤ k) : (newLevelTerms T).gs j = T.gs j := by
  funext X
  simp [newLevelTerms, hj]

theorem newLevelTerms_E_le {j : ℕ} (hj : j ≤ k) : (newLevelTerms T).E j = 0 := by
  simp [newLevelTerms, hj]

theorem newLevelTerms_M_le {j : ℕ} (hj : j ≤ k) : (newLevelTerms T).M j = 0 := by
  simp [newLevelTerms, hj]

theorem newLevelTerms_gs_le {j : ℕ} (hj : j ≤ k) (X : Set (CTorus d L N₁ m₁ (k + 1))) :
    (newLevelTerms T).gs j X = levelGS j (hj.trans k.le_succ) := by
  simp [newLevelTerms, hj]

end NewLevel

section Congr

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The term clauses of scale `k` read the field domain only at the levels `j ≤ k`. -/
theorem sfTermClauses_congr_le {P : Consts} {Dom Dom' : FieldDom d L N₁ m₁ k N ϱ}
    {Tm : Terms d L N₁ m₁ k N ϱ} (hcl : SFTermClauses P Dom Tm)
    (hsub : ∀ j, j ≤ k → ∀ G Ψ h, Dom'.dom j G Ψ h → Dom.dom j G Ψ h) :
    SFTermClauses P Dom' Tm := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -, -, h13, h14⟩ :=
    hcl.inherit_le le_rfl hsub (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  exact ⟨h1, h2, h3, h4, h5, h6, fun j hj1 hjk => h7 j hj1 hjk hjk, h8, h9,
    fun j hj1 hjk => h10 j hj1 hjk hjk, hcl.localE, hcl.localM, h13, h14⟩

end Congr

section Density

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **A member of `IsSF2` from the term clauses and the reality of the density**: if the exponent of
(H.1) has a real exponential at the real fields of `Dom.phys` inside the small-field region `Xi`,
the real function `χ_k exp[expo2]` (at the unique realizing datum, `realizes_unique`) is a density
of the class. -/
theorem exists_isSF2_of_real {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ}
    {Dom : FieldDom d L N₁ m₁ k N ϱ} {Tm : Terms d L N₁ m₁ k N ϱ} {Ek : ℝ}
    (hterms : SFTermClauses P Dom Tm)
    (hgs : ∀ j, 1 ≤ j → ∀ hjk : j ≤ k, ∀ X, IsPolyDom P.m₀ j X →
      GsSpec.GsSpecStrong j hjk X (Tm.gs j X))
    (hreal : ∀ (Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ)
      (g : CTorus d L N₁ m₁ k → Fin N → ℝ) (D : BgData (topGS d L N₁ m₁ k ϱ) N),
      h₀ ∈ Dom.phys → Realizes D Ψ₀ h₀ → Def6.l1 (fun x i => (g x i : ℂ)) < 1 →
      Xi (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg.sfBgMass k) k 1
        (P.p (β k) / Real.sqrt (β k)) Ψ₀ h₀ →
      (Complex.exp (expo2 P Rg β a Tm Ek D (fun x i => (g x i : ℂ)))).im = 0) :
    ∃ ρ : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ,
      IsSF2 P Rg β a Dom Tm ρ Ek := by
  refine ⟨fun Ψ₀ h₀ g => if hD : ∃ D : BgData (topGS d L N₁ m₁ k ϱ) N, Realizes D Ψ₀ h₀ then
      (if Xi (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg.sfBgMass k) k 1
          (P.p (β k) / Real.sqrt (β k)) Ψ₀ h₀ then
        (Complex.exp (expo2 P Rg β a Tm Ek hD.choose (fun x i => (g x i : ℂ)))).re else 0)
      else 0, ⟨fun Ψ₀ h₀ g D hph hR hg => ?_, hterms, hgs⟩⟩
  have hD : ∃ D : BgData (topGS d L N₁ m₁ k ϱ) N, Realizes D Ψ₀ h₀ := ⟨D, hR⟩
  have hDc : hD.choose = D := realizes_unique hD.choose_spec hR
  simp only [hD, dite_eq_left, hDc]
  by_cases hX : Xi (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg.sfBgMass k) k 1
      (P.p (β k) / Real.sqrt (β k)) Ψ₀ h₀
  · rw [ite_eq_left hX, ite_eq_left hX]
    exact Complex.ext (by simp) (by simpa using (hreal Ψ₀ h₀ g D hph hR hg hX).symm)
  · rw [ite_eq_right hX, ite_eq_right hX]
    simp

end Density

section Lift

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

omit [NeZero L] in
/-- The integer point of `ℤ^d` read on the old torus is the old-torus preimage of the integer
point read on the new torus. -/
theorem oldTorusEquiv_symm_intPt {N₂ : ℕ} (x : Fin d → ℤ) :
    (oldTorusEquiv (d := d) (L := L) (N₁ := N₂) (m₁ := m₁) (k := k)).symm
        (fun μ => ((x μ : ℤ) : ZMod (N₂ * L ^ m₁ * L ^ (k + 1)))) =
      fun μ => ((x μ : ℤ) : ZMod ((L * N₂) * L ^ m₁ * L ^ k)) := by
  rw [Equiv.symm_apply_eq, oldTorusEquiv_apply]
  exact (castT_intTorus (oldSide_eq_newSide (L := L) (N₁ := N₂) (m₁ := m₁) (k := k)) x).symm

/-- **The small-field half of (D8) at an inherited level**: the observable terms `ℳ^{(j)}`,
`j ≤ k`, of the pulled-back family `liftOldTermsFam sf.Tm` agree on two tori of scale `k + 1` for
polymers that wind around neither, if those of `sf` satisfy `D8SF` at scale `k` (the old tori are
`L N₂`, `L N₃`, with the same block side at the level `j`). -/
theorem liftOldTermsFam_M_eq_of_d8 {m₀ : ℕ} {sf : SFData d L m₁ k N ϱ} (hD8 : D8SF m₀ sf)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (x : Fin d → ℤ) (X' : Finset (Fin d → ℤ))
    (ψ h g : InfFld d N) (N₂ N₃ : ℕ) [NeZero N₂] [NeZero N₃]
    (hnw₂ : NonWind L N₂ m₁ (k + 1) j X') (hnw₃ : NonWind L N₃ m₁ (k + 1) j X')
    (hp₂ : IsPolyDom (L := L) (N₁ := N₂) (m₁ := m₁) (k := k + 1) m₀ j
      (Ypoly (L := L) (N₁ := N₂) (m₁ := m₁) (k := k + 1) j X'))
    (hp₃ : IsPolyDom (L := L) (N₁ := N₃) (m₁ := m₁) (k := k + 1) m₀ j
      (Ypoly (L := L) (N₁ := N₃) (m₁ := m₁) (k := k + 1) j X')) :
    (liftOldTermsFam sf.Tm N₂).M j (fun μ => ((x μ : ℤ) : ZMod _)) (Ypoly j X')
        (pullFld j ψ) (pullFld j h) (pullFld j g) =
      (liftOldTermsFam sf.Tm N₃).M j (fun μ => ((x μ : ℤ) : ZMod _)) (Ypoly j X')
        (pullFld j ψ) (pullFld j h) (pullFld j g) := by
  have hpo₂ : IsPolyDom (L := L) (N₁ := L * N₂) (m₁ := m₁) (k := k)
      m₀ j (Ypoly (L := L) (N₁ := L * N₂) (m₁ := m₁) (k := k) j X') := by
    rw [← oldTorusEquiv_symm_image_Ypoly (N₁ := N₂) (m₁ := m₁) hjk X']
    exact oldPoly_of_newPoly hp₂
  have hpo₃ : IsPolyDom (L := L) (N₁ := L * N₃) (m₁ := m₁) (k := k)
      m₀ j (Ypoly (L := L) (N₁ := L * N₃) (m₁ := m₁) (k := k) j X') := by
    rw [← oldTorusEquiv_symm_image_Ypoly (N₁ := N₃) (m₁ := m₁) hjk X']
    exact oldPoly_of_newPoly hp₃
  rw [liftOldTermsFam_apply, liftOldTermsFam_apply, liftOldTerms_M, liftOldTerms_M,
    oldTorusEquiv_symm_intPt, oldTorusEquiv_symm_intPt,
    oldTorusEquiv_symm_image_Ypoly hjk, oldTorusEquiv_symm_image_Ypoly hjk,
    lowerNewField_pullFld hjk, lowerNewField_pullFld hjk, lowerNewField_pullFld hjk,
    lowerNewField_pullFld hjk, lowerNewField_pullFld hjk, lowerNewField_pullFld hjk]
  exact hD8.M_eq j hj1 hjk x X' ψ h g (L * N₂) (L * N₃)
    ((oldNonWind_iff_newNonWind hjk X').2 hnw₂) ((oldNonWind_iff_newNonWind hjk X').2 hnw₃)
    hpo₂ hpo₃

end Lift

section Succ

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **The core of the small-field clauses of the successor** (the part of `sfSucc_clauses` that does
not depend on the class of the input): from the pieces of the input class that the inherited
levels read (admissibility, the coefficient bounds `Pc` at the scale `k` for the window of `a_k`,
`ν_k ≤ 9/10`, the term clauses on the read tori, torus independence, the renormalization
conditions) and the data of the successor, the successor has the term clauses `IsSF2` on the read
tori, torus independence, the renormalization conditions at all scales `≤ k + 1` and (D8). The
classes `D2SF2` (`Pc = P6`) and `SFFlat2` (`Pc = massOne P6`) are the two instances. -/
theorem sfSucc_core {P6 Pc : Def6.Consts} {k0 : ℕ} {a β ν : ℝ}
    {sf : SFData d L m₁ k N ϱ} {sf' : SFData d L m₁ (k + 1) N ϱ}
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ) (hk1 : 1 ≤ k) 
    (hadm : P6.Admissible d L) (hC : Def6.CoeffBounds d L k Pc sf.β sf.ν sf.a)
    (hνk910 : sf.ν k ≤ 9 / 10)
    {ρsf : ∀ (N₁ : ℕ) [NeZero N₁], (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) →
      (Fin N → ℝ) → (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
    (htorOld : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ →
      IsSF2 P6 (⟨k0, sf.ν⟩ : Regime L) sf.β sf.a (sfDom P6 k0 sf N₂) (sf.Tm N₂) (ρsf N₂) (sf.E N₂))
    (hTIold : TorusIndep P6.m₀ sf.Tm)
    (hrenOld : ∀ j, 1 ≤ j → j ≤ k → RenormCondAlong (d := d) (L := L) (m₁ := m₁) (N := N)
      (ϱ := ϱ) P6.m₀ k (sf.ν k) sf.Tm j (torusSeq L P6.m₀) (fun n => torusSeq_ne_zero P6.m₀ n))
    (hD8 : D8SF P6.m₀ sf)
    (hfree : ∀ j, 1 ≤ j → j ≤ k → sf.a j = compWeight L a j)
    (hrun : RunningHypTo d L β ν a (1 / 20) sf.β sf.ν k)
    (hcst : ∀ j, j ≤ k → sf'.β j = sf.β j ∧ sf'.ν j = sf.ν j ∧ sf'.z j = sf.z j ∧
      sf'.a j = sf.a j)
    (hfree' : sf'.a (k + 1) = compWeight L a (k + 1))
    (hTm : ∀ (N₂ : ℕ) [NeZero N₂] (j : ℕ), j ≤ k →
      (sf'.Tm N₂).E j = (liftOldTermsFam sf.Tm N₂).E j ∧
        (sf'.Tm N₂).M j = (liftOldTermsFam sf.Tm N₂).M j ∧
        (sf'.Tm N₂).gs j = (liftOldTermsFam sf.Tm N₂).gs j)
    (hnew : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ →
      SFTermClauses P6 (sfDom P6 k0 sf' N₂) (newLevelTerms (sf'.Tm N₂)))
    (hgsnew : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ → ∀ (X : Set (CTorus d L N₂ m₁ (k + 1))),
      IsPolyDom P6.m₀ (k + 1) X → GsSpec.GsSpecStrong (k + 1) le_rfl X ((sf'.Tm N₂).gs (k + 1) X))
    (hTInew : TorusIndep P6.m₀ (fun N₂ _ => newLevelTerms (sf'.Tm N₂)))
    (hR' : RenormCondAlong P6.m₀ (k + 1) (sf'.ν (k + 1)) sf'.Tm (k + 1) (torusSeq L P6.m₀)
      (fun n => torusSeq_ne_zero P6.m₀ n))
    (hreal : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ → ∀ (Ψ₀ : CTorus d L N₂ m₁ (k + 1) → Fin N → ℝ) (h₀ : Fin N → ℝ)
      (g : CTorus d L N₂ m₁ (k + 1) → Fin N → ℝ) (D : BgData (topGS d L N₂ m₁ (k + 1) ϱ) N),
      Realizes D Ψ₀ h₀ → Def6.l1 (fun x i => (g x i : ℂ)) < 1 →
      Xi (topGS d L N₂ m₁ (k + 1) ϱ) (aIdeal L (k + 1) (sf'.a (k + 1)))
        ((⟨k0, sf'.ν⟩ : Regime L).sfBgMass (k + 1)) (k + 1) 1
        (P6.p (sf'.β (k + 1)) / Real.sqrt (sf'.β (k + 1))) Ψ₀ h₀ →
      (Complex.exp (expo2 P6 ⟨k0, sf'.ν⟩ sf'.β sf'.a (sf'.Tm N₂) (sf'.E N₂) D
        (fun x i => (g x i : ℂ)))).im = 0)
    (hD8new : D8SF P6.m₀ { sf' with Tm := fun N₂ _ => newLevelTerms (sf'.Tm N₂) }) :
    (∃ ρ' : ∀ (N₁ : ℕ) [NeZero N₁], (Localization.CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ) →
      (Fin N → ℝ) → (Localization.CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ) → ℝ,
      ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ →
        IsSF2 P6 (⟨k0, sf'.ν⟩ : Regime L) sf'.β sf'.a (sfDom P6 k0 sf' N₂) (sf'.Tm N₂) (ρ' N₂)
          (sf'.E N₂)) ∧
      TorusIndep P6.m₀ sf'.Tm ∧
      (∀ j, 1 ≤ j → j ≤ k + 1 →
        RenormCondAlong (d := d) (L := L) (m₁ := m₁) (N := N) (ϱ := ϱ) P6.m₀ (k + 1)
          ((⟨k0, sf'.ν⟩ : Regime L).ν (k + 1)) sf'.Tm j (torusSeq L P6.m₀)
          (fun n => torusSeq_ne_zero P6.m₀ n)) ∧ D8SF P6.m₀ sf' := by
  have hL2 : 2 ≤ L := by omega
  have hak : sf'.a k = sf.a k := (hcst k le_rfl).2.2.2
  have hνk : sf'.ν k = sf.ν k := (hcst k le_rfl).2.1
  have ha : aIdeal L (k + 1) (sf'.a (k + 1)) = aIdeal L k (sf'.a k) := by
    rw [hfree', hak, hfree k hk1 le_rfl]
    exact aIdeal_succ_compWeight hL2 hk1 a
  obtain ⟨-, -, -, hν0, -, -, -, -, -, hnu⟩ := hrun
  have hνpos : ∀ j, j ≤ k → 0 < sf.ν j := fun j hj => by
    obtain ⟨δ, hδ0, -, hνj⟩ := hnu j hj
    rw [hνj]; positivity
  have hν : ∀ j, 1 ≤ j → j ≤ k → 0 ≤ (⟨k0, sf'.ν⟩ : Regime L).ν j := fun j _ hj => by
    show 0 ≤ sf'.ν j
    rw [(hcst j hj).2.1]; exact (hνpos j hj).le
  -- the old term clauses on the domain of the new data (the domains agree at the levels `≤ k`)
  have hcl : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ →
      SFTermClauses P6 (birthXiDom P6 ⟨k0, sf'.ν⟩ sf'.a N₂) (sf.Tm N₂) := fun N₂ _ hN =>
    sfTermClauses_congr_le (htorOld N₂ hN).terms fun j hj G Ψ h hdom =>
      (birthXiDom_dom_congr P6 (by rw [hak]) (hcst j hj).2.1 G Ψ h).1 hdom
  -- the terms at the scale `k + 1`
  have hterms : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ →
      SFTermClauses P6 (sfDom P6 k0 sf' N₂) (sf'.Tm N₂) := fun N₂ _ hN =>
    sfTermClauses_splice_birth (Tm := sf.Tm (L * N₂)) (Tnew := newLevelTerms (sf'.Tm N₂)) ha hν
      (hcl (L * N₂) (readTorus_mul hN)) (hnew N₂ hN)
      (fun j hj => (hTm N₂ j hj).1) (fun j hj => (hTm N₂ j hj).2.1)
      (fun j hj => (hTm N₂ j hj).2.2) (fun j hj => (newLevelTerms_E _ hj).symm)
      (fun j hj => (newLevelTerms_M _ hj).symm) (fun j hj => (newLevelTerms_gs _ hj).symm)
  have hgs : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ → ∀ j, 1 ≤ j → ∀ hjk : j ≤ k + 1, ∀ X,
      IsPolyDom P6.m₀ j X → GsSpec.GsSpecStrong j hjk X ((sf'.Tm N₂).gs j X) := fun N₂ _ hN =>
    gsStrong_splice (Tm := sf.Tm (L * N₂)) (Tnew := newLevelTerms (sf'.Tm N₂))
      (htorOld (L * N₂) (readTorus_mul hN)).gsStrong
      (fun j hj1 hjk X hX => by
        by_cases h : j ≤ k
        · rw [newLevelTerms_gs_le _ h]
          exact GsSpec.levelGS_strong hj1 hjk X
        · obtain rfl : j = k + 1 := by omega
          rw [newLevelTerms_gs _ h]
          exact hgsnew N₂ hN X hX)
      (fun j hj => (hTm N₂ j hj).2.2) (fun j hj => (newLevelTerms_gs _ hj).symm)
  have htor : ∀ (N₂ : ℕ) [NeZero N₂], ∃ ρ, ReadTorus L P6.m₀ N₂ →
      IsSF2 P6 ⟨k0, sf'.ν⟩ sf'.β sf'.a (sfDom P6 k0 sf' N₂) (sf'.Tm N₂) ρ (sf'.E N₂) := by
    intro N₂ _
    by_cases hN : ReadTorus L P6.m₀ N₂
    · obtain ⟨ρ, hρ⟩ := exists_isSF2_of_real (hterms N₂ hN) (hgs N₂ hN)
        fun Ψ₀ h₀ g D _ hR hg hX => hreal N₂ hN Ψ₀ h₀ g D hR hg hX
      exact ⟨ρ, fun _ => hρ⟩
    · exact ⟨fun _ _ _ => 0, fun h => absurd h hN⟩
  have hBg : ∀ j, 1 ≤ j → j ≤ k →
      BgHyp d L k ϱ (aIdeal L k (sf'.a k)) (physMass L j ((⟨k0, sf'.ν⟩ : Regime L).ν j)) := by
    intro j hj1 hjk
    have hC := hC
    obtain ⟨δj, hδj0, hδj, hνj⟩ := hnu j hjk
    obtain ⟨δk, hδk0, hδk, hνk'⟩ := hnu k le_rfl
    have hcap : physMass L j (sf.ν j) * ((L : ℝ) ^ k) ^ 2 ≤ 1 := by
      rw [hνj]
      refine physMass_cap_of_top hL hν0 hδj0 hδj hδk0 hδk ?_
      rw [← hνk']
      show sf.ν k ≤ 9 / 10
      exact hνk910
    show BgHyp d L k ϱ (aIdeal L k (sf'.a k)) (physMass L j (sf'.ν j))
    rw [hak, (hcst j hjk).2.1]
    exact ⟨hd, hL, hϱ, fun _ hi hik => aIdeal_mem hL hC.a_ge hC.a_lt hi hik,
      by unfold physMass; exact mul_nonneg (hνpos j hjk).le (sq_nonneg _), hcap⟩
  have hren : ∀ j, 1 ≤ j → j ≤ k + 1 →
      RenormCondAlong P6.m₀ (k + 1) ((⟨k0, sf'.ν⟩ : Regime L).ν (k + 1)) sf'.Tm j
        (torusSeq L P6.m₀) (fun n => torusSeq_ne_zero P6.m₀ n) :=
    renorm_splice_birth (Tm := sf.Tm) (Tnew := sf'.Tm) (fun n => torusSeq_ne_zero P6.m₀ n)
      (oldSideSeq_tendsto_atTop (L := L)) (fun n => torusSeq_old_side P6.m₀ n)
      (ReadTorus L P6.m₀) (fun n => torusSeq_dvd P6.m₀ n)
      (fun N₂ _ hN => hcl (L * N₂) (readTorus_mul hN)) hBg
      (fun j _ _ => eps_pos_of_admissible hadm j) hTIold
      (fun j hj1 hjk => by
        show RenormCondAlong P6.m₀ k (sf'.ν k) sf.Tm j (torusSeq L P6.m₀)
          (fun n => torusSeq_ne_zero P6.m₀ n)
        rw [hνk]; exact hrenOld j hj1 hjk)
      (by show 0 < sf'.ν k; rw [hνk]; exact hνpos k le_rfl) hR'
      (fun N₂ _ j hj => (hTm N₂ j hj).1) (fun _ _ _ _ => rfl)
  have hTI : TorusIndep P6.m₀ sf'.Tm :=
    torusIndep_splice (Tm := sf.Tm) (Tnew := fun N₂ _ => newLevelTerms (sf'.Tm N₂))
      hTIold hTInew (fun N₂ _ j hj => (hTm N₂ j hj).1)
      (fun N₂ _ j hj => (newLevelTerms_E _ hj).symm)
  refine ⟨?_, hTI, hren, ?_⟩
  · choose ρ' hρ' using htor
    exact ⟨ρ', hρ'⟩
  · refine ⟨fun j hj1 hjk x X' ψ h g N₂ N₃ _ _ hnw₂ hnw₃ hp₂ hp₃ => ?_, hD8new.R_eq⟩
    by_cases hj : j ≤ k
    · rw [(hTm N₂ j hj).2.1, (hTm N₃ j hj).2.1]
      exact liftOldTermsFam_M_eq_of_d8 hD8 hj1 hj x X' ψ h g N₂ N₃ hnw₂ hnw₃ hp₂ hp₃
    · have h1 := hD8new.M_eq j hj1 hjk x X' ψ h g N₂ N₃ hnw₂ hnw₃ hp₂ hp₃
      simp only [newLevelTerms_M _ hj] at h1
      exact h1

/-- **The small-field clauses of the successor at the scale `k + 1`** (the small-field half of
LF-3: LFR Theorem IV.1.1 (e), (h); P4 Theorem 1, P5 Theorem 1). Let `sf` be the small-field data of a
member of `ℛ_k` and `sf'` data of scale `k + 1` that inherit the running constants, the kernel
coefficients and the terms of the levels `j ≤ k` (pulled back along `oldTorusEquiv`, ruling R6),
whose new level satisfies the term clauses, the strong specification of its generating sets and
torus independence, whose coefficients satisfy (H.6) and (H.5) at `k + 1`, whose density exponent is
real, whose terms `ℛ^{(k+1)}_n` satisfy P5 H4 with `½ β_{k+1}^{-m-1}`, and whose new level and
`ℛ^{(k+1)}` are torus coherent. Then `sf'` satisfies (D2) of `IsRepPre2` (the class `IsSFFamily2` on
the birth domains and P5 H4), (D8) and (D9) at `k + 1`. The inherited levels are the landed
`sfTermClauses_splice_birth`, `gsStrong_splice`, `torusIndep_splice`, `renorm_splice_birth` and
`liftOldTermsFam_M_eq_of_d8`. -/
theorem sfSucc_clauses {P6 : Def6.Consts} {k0 : ℕ} {a β ν : ℝ}
    {sf : SFData d L m₁ k N ϱ} {sf' : SFData d L m₁ (k + 1) N ϱ}
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ) (hk1 : 1 ≤ k) (hk0 : k + 1 ≤ k0)
    (hD2 : D2SF2 P6 k0 sf (fun _ => 1)) (hD8 : D8SF P6.m₀ sf)
    (hfree : ∀ j, 1 ≤ j → j ≤ k → sf.a j = compWeight L a j)
    (hrun : RunningHypTo d L β ν a (1 / 20) sf.β sf.ν k)
    (hcst : ∀ j, j ≤ k → sf'.β j = sf.β j ∧ sf'.ν j = sf.ν j ∧ sf'.z j = sf.z j ∧
      sf'.a j = sf.a j)
    (hfree' : sf'.a (k + 1) = compWeight L a (k + 1))
    (hTm : ∀ (N₂ : ℕ) [NeZero N₂] (j : ℕ), j ≤ k →
      (sf'.Tm N₂).E j = (liftOldTermsFam sf.Tm N₂).E j ∧
        (sf'.Tm N₂).M j = (liftOldTermsFam sf.Tm N₂).M j ∧
        (sf'.Tm N₂).gs j = (liftOldTermsFam sf.Tm N₂).gs j)
    (hnew : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ →
      SFTermClauses P6 (sfDom P6 k0 sf' N₂) (newLevelTerms (sf'.Tm N₂)))
    (hgsnew : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ → ∀ (X : Set (CTorus d L N₂ m₁ (k + 1))),
      IsPolyDom P6.m₀ (k + 1) X → GsSpec.GsSpecStrong (k + 1) le_rfl X ((sf'.Tm N₂).gs (k + 1) X))
    (hTInew : TorusIndep P6.m₀ (fun N₂ _ => newLevelTerms (sf'.Tm N₂)))
    (hC' : CoeffBounds d L (k + 1) P6 sf'.β sf'.ν sf'.a)
    (hR' : RenormCondAlong P6.m₀ (k + 1) (sf'.ν (k + 1)) sf'.Tm (k + 1) (torusSeq L P6.m₀)
      (fun n => torusSeq_ne_zero P6.m₀ n))
    (hreal : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ → ∀ (Ψ₀ : CTorus d L N₂ m₁ (k + 1) → Fin N → ℝ) (h₀ : Fin N → ℝ)
      (g : CTorus d L N₂ m₁ (k + 1) → Fin N → ℝ) (D : BgData (topGS d L N₂ m₁ (k + 1) ϱ) N),
      Realizes D Ψ₀ h₀ → Def6.l1 (fun x i => (g x i : ℂ)) < 1 →
      Xi (topGS d L N₂ m₁ (k + 1) ϱ) (aIdeal L (k + 1) (sf'.a (k + 1)))
        ((⟨k0, sf'.ν⟩ : Regime L).sfBgMass (k + 1)) (k + 1) 1
        (P6.p (sf'.β (k + 1)) / Real.sqrt (sf'.β (k + 1))) Ψ₀ h₀ →
      (Complex.exp (expo2 P6 ⟨k0, sf'.ν⟩ sf'.β sf'.a (sf'.Tm N₂) (sf'.E N₂) D
        (fun x i => (g x i : ℂ)))).im = 0)
    (hRt : ∀ (N₂ : ℕ) [NeZero N₂],
      RTermsH4 (ϱ := ϱ) P6 sf'.β sf'.ν sf'.a N₂ (sf'.Rt N₂) (preFac (P6.m₀ + m₁)))
    (hD8new : D8SF P6.m₀ { sf' with Tm := fun N₂ _ => newLevelTerms (sf'.Tm N₂) }) :
    D2SF2 P6 k0 sf' (preFac (P6.m₀ + m₁)) ∧ D8SF P6.m₀ sf' ∧ D9Coeff P6 k0 sf' := by
  obtain ⟨ρsf, hfam⟩ := hD2.sfClass
  have h910 : sf.ν k ≤ 9 / 10 := by
    have h1 := hfam.coeff.nu_le
    have h2 := hfam.admissible.νbar_le
    have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
    have : ((L : ℝ) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
    linarith
  obtain ⟨⟨ρ', hρ'⟩, hTI, hren, hD8'⟩ := sfSucc_core (hd := hd) (hL := hL) (hϱ := hϱ) (hk1 := hk1)
    (hadm := hfam.admissible) (hC := hfam.coeff) (hνk910 := h910)
    (htorOld := fun N₂ _ hN => hfam.torus N₂ hN) (hTIold := hfam.torusIndep)
    (hrenOld := hfam.renorm) (hD8 := hD8) (hfree := hfree) (hrun := hrun) (hcst := hcst)
    (hfree' := hfree') (hTm := hTm) (hnew := hnew) (hgsnew := hgsnew) (hTInew := hTInew)
    (hR' := hR') (hreal := hreal) (hD8new := hD8new)
  exact ⟨⟨⟨ρ', ⟨hfam.admissible, hC', hρ', hTI, hren⟩⟩, hRt⟩, hD8',
    ⟨hC'.beta_gt, hC'.nu_pos, hC'.nu_le, hk0⟩⟩

end Succ

end Balaban.RootFSpine
