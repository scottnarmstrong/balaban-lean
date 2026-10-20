/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftDomBirthClauses
public import Balaban.Fluctuation.OldTermsLiftFamily
public import Balaban.Fluctuation.OldTermsLiftMomentClass
public import Balaban.Inhabited.StepTowerChainDomNbhd

/-!
# The family clauses of inherited terms on the birth domains

The clauses of `IsSFFamily2` that concern the family of terms rather than one torus: torus
independence, the strong specification of the local generating sets, and the renormalization
conditions.  They hold at the levels `j ≤ k` of a family `T'` that agrees with the pulled-back old
family `liftOldTermsFam Tm` there, and at the level `k + 1` they are those of the new family.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.Background Filter

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {m₀ : ℕ}

section TorusIndep

variable {Tm : ∀ (N₂ : ℕ) [NeZero N₂], Terms d L N₂ m₁ k N ϱ}
  {Tnew T' : ∀ (N₂ : ℕ) [NeZero N₂], Terms d L N₂ m₁ (k + 1) N ϱ}

/-- **Torus independence of the spliced family**: levels `j ≤ k` from the old family, level
`k + 1` from the new family. -/
theorem torusIndep_splice (hT : TorusIndep m₀ Tm) (hTn : TorusIndep m₀ Tnew)
    (hE : ∀ (N₂ : ℕ) [NeZero N₂] (j : ℕ), j ≤ k → (T' N₂).E j = (liftOldTermsFam Tm N₂).E j)
    (hE' : ∀ (N₂ : ℕ) [NeZero N₂] (j : ℕ), ¬ j ≤ k → (T' N₂).E j = (Tnew N₂).E j) :
    TorusIndep m₀ T' where
  E_eq := by
    intro j hj1 hjk y X' hy ψ h N₂ N₃ _ _ hnw₂ hnw₃ hp₂ hp₃
    by_cases hj : j ≤ k
    · rw [hE N₂ j hj, hE N₃ j hj]
      exact liftOldTermsFam_E_eq_of_torusIndep hT hj1 hj y X' hy ψ h N₂ N₃ hnw₂ hnw₃ hp₂ hp₃
    · rw [hE' N₂ j hj, hE' N₃ j hj]
      exact hTn.E_eq j hj1 hjk y X' hy ψ h N₂ N₃ hnw₂ hnw₃ hp₂ hp₃

end TorusIndep

section GsStrong

variable {N₁ : ℕ} [NeZero N₁] {P : Consts}
  {Tm : Terms d L (L * N₁) m₁ k N ϱ} {Tnew T' : Terms d L N₁ m₁ (k + 1) N ϱ}

/-- **The strong specification of the local generating sets of the spliced terms.** -/
theorem gsStrong_splice
    (hold : ∀ j, 1 ≤ j → ∀ hjk : j ≤ k, ∀ X, IsPolyDom P.m₀ j X →
      GsSpecStrong j hjk X (Tm.gs j X))
    (hnew : ∀ j, 1 ≤ j → ∀ hjk : j ≤ k + 1, ∀ X, IsPolyDom P.m₀ j X →
      GsSpecStrong j hjk X (Tnew.gs j X))
    (hgs : ∀ j, j ≤ k → T'.gs j = (liftOldTerms Tm).gs j)
    (hgs' : ∀ j, ¬ j ≤ k → T'.gs j = Tnew.gs j) :
    ∀ j, 1 ≤ j → ∀ hjk : j ≤ k + 1, ∀ X, IsPolyDom P.m₀ j X →
      GsSpecStrong j hjk X (T'.gs j X) := by
  intro j hj1 hjk X hX
  by_cases h : j ≤ k
  · rw [hgs j h]
    have hback : IsPolyDom (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k)
        P.m₀ j (oldTorusEquiv.symm '' X) := by
      apply (oldTorusEquiv_isPolyDom_iff (N₁ := N₁) (m₁ := m₁) (k := k)).2
      simpa [liftOldPoly, Set.image_image] using hX
    have hstrong := liftOldGS_gsStrong hj1 h (hold j hj1 h _ hback)
    simpa [liftOldTerms, liftOldPoly, Set.image_image] using hstrong
  · rw [hgs' j h]; exact hnew j hj1 hjk X hX

end GsStrong

section Renorm

variable {Tm : ∀ (N₂ : ℕ) [NeZero N₂], Terms d L N₂ m₁ k N ϱ}
  {T T' : ∀ (N₂ : ℕ) [NeZero N₂], Terms d L N₂ m₁ k N ϱ}

/-- The renormalization conditions at a level depend only on the energy terms of that level. -/
theorem renormCond_congr_level {νk : ℝ} {j : ℕ} {idx : ℕ → ℕ} {hidx : ∀ n, idx n ≠ 0}
    (hE : ∀ (N₂ : ℕ) [NeZero N₂], (T N₂).E j = (T' N₂).E j)
    (hR : RenormCondAlong m₀ k νk T j idx hidx) : RenormCondAlong m₀ k νk T' j idx hidx := by
  have hEl : ElocInf m₀ T' j = ElocInf m₀ T j := by
    funext y ψ h
    unfold ElocInf Einf Eseq
    simp only [hE]
  have hmom : ∀ (t : ℕ) [NeZero t] (i₀ i₁ : Fin N),
      momentSum m₀ (T' t) j i₀ i₁ = momentSum m₀ (T t) j i₀ i₁ := by
    intro t _ i₀ i₁
    unfold momentSum Edens Eloc
    simp only [hE]
  refine ⟨fun i₀ => ?_, fun i₀ hν => ?_, fun i₀ => ?_, fun i₀ i₁ hne => ?_⟩
  · rw [hEl]; exact hR.val i₀
  · rw [hEl]; exact hR.dh i₀ hν
  · rw [hEl]; exact hR.dpsi i₀
  · have := hR.moment i₀ i₁ hne
    simpa only [hmom] using this

end Renorm

section RenormSplice

variable {P : Consts} {Rg : Regime L} {a : ℕ → ℝ}
  {Tm : ∀ (N₂ : ℕ) [NeZero N₂], Terms d L N₂ m₁ k N ϱ}
  {T' : ∀ (N₂ : ℕ) [NeZero N₂], Terms d L N₂ m₁ (k + 1) N ϱ}

/-- **The renormalization conditions at an inherited level of the spliced family.**  The reference
pairs lie in the birth domain of their own level (a neighbourhood of the constant field,
`exists_birthXiDom_ball`), so no domain premise on the reference field is needed. -/
theorem renormCond_splice_birth_of_le {idx idx' φ : ℕ → ℕ} {hidx : ∀ n, idx n ≠ 0}
    (hidx' : ∀ n, idx' n ≠ 0) (hφ : Filter.Tendsto φ Filter.atTop Filter.atTop)
    (hrel : ∀ n, L * idx' n = idx (φ n)) (SelN : ℕ → Prop) (hSel : ∀ n, SelN (idx' n))
    (hCl : ∀ (N₂ : ℕ) [NeZero N₂], SelN N₂ →
      SFTermClauses P (birthXiDom P Rg a (L * N₂)) (Tm (L * N₂)))
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (physMass L j (Rg.ν j)))
    (hε : 0 < P.eps d L j) (hT : TorusIndep P.m₀ Tm)
    (hR : RenormCondAlong P.m₀ k (Rg.ν k) Tm j idx hidx) (hν : 0 < Rg.ν k) (νK : ℝ)
    (hE : ∀ (N₂ : ℕ) [NeZero N₂], (T' N₂).E j = (liftOldTermsFam Tm N₂).E j) :
    RenormCondAlong P.m₀ (k + 1) νK T' j idx' hidx' := by
  refine renormCond_congr_level (fun N₂ _ => (hE N₂).symm)
    (liftOldTermsFam_renormCond_of_clauses hidx' hφ hrel SelN hSel hCl ?_ hT hR hν hj1 hjk νK)
  intro N₂ _ hN i₀ X hX
  obtain ⟨ρ, hρ, hball⟩ := Balaban.Inhabited.exists_birthXiDom_ball (N₁ := L * N₂) (N := N)
    (ϱ := ϱ) P Rg a i₀ hjk hBg hε
  exact hball _ ((hCl N₂ hN).gs_spec j hj1 hjk X hX).2 _
    (fun x i => by simp [constFld, hρ.le]) (fun _ _ _ => rfl)

/-- **The `renorm` clause of `IsSFFamily2On` at scale `k + 1` for the spliced family**: the levels
`j ≤ k` are inherited, the level `k + 1` comes from the new family. -/
theorem renorm_splice_birth {idx idx' φ : ℕ → ℕ} {hidx : ∀ n, idx n ≠ 0}
    (hidx' : ∀ n, idx' n ≠ 0) (hφ : Filter.Tendsto φ Filter.atTop Filter.atTop)
    (hrel : ∀ n, L * idx' n = idx (φ n)) (SelN : ℕ → Prop) (hSel : ∀ n, SelN (idx' n))
    {Tnew : ∀ (N₂ : ℕ) [NeZero N₂], Terms d L N₂ m₁ (k + 1) N ϱ}
    (hCl : ∀ (N₂ : ℕ) [NeZero N₂], SelN N₂ →
      SFTermClauses P (birthXiDom P Rg a (L * N₂)) (Tm (L * N₂)))
    (hBg : ∀ j, 1 ≤ j → j ≤ k →
      BgHyp d L k ϱ (aIdeal L k (a k)) (physMass L j (Rg.ν j)))
    (hε : ∀ j, 1 ≤ j → j ≤ k → 0 < P.eps d L j) (hT : TorusIndep P.m₀ Tm)
    (hR : ∀ j, 1 ≤ j → j ≤ k → RenormCondAlong P.m₀ k (Rg.ν k) Tm j idx hidx) (hν : 0 < Rg.ν k)
    (hRn : RenormCondAlong P.m₀ (k + 1) (Rg.ν (k + 1)) Tnew (k + 1) idx' hidx')
    (hE : ∀ (N₂ : ℕ) [NeZero N₂] (j : ℕ), j ≤ k → (T' N₂).E j = (liftOldTermsFam Tm N₂).E j)
    (hE' : ∀ (N₂ : ℕ) [NeZero N₂] (j : ℕ), ¬ j ≤ k → (T' N₂).E j = (Tnew N₂).E j) :
    ∀ j, 1 ≤ j → j ≤ k + 1 → RenormCondAlong P.m₀ (k + 1) (Rg.ν (k + 1)) T' j idx' hidx' := by
  intro j hj1 hjk
  by_cases h : j ≤ k
  · exact renormCond_splice_birth_of_le hidx' hφ hrel SelN hSel hCl hj1 h (hBg j hj1 h)
      (hε j hj1 h) hT (hR j hj1 h) hν _ (fun N₂ _ => hE N₂ j h)
  · have hj : j = k + 1 := by omega
    subst hj
    exact renormCond_congr_level (fun N₂ _ => (hE' N₂ _ h).symm) hRn

end RenormSplice

end Balaban.Fluctuation
