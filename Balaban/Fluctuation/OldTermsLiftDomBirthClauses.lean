/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftDomBirth
public import Balaban.Fluctuation.OldTermsLiftPaving

/-!
# The term clauses of inherited terms on the birth domains

The pullback `liftOldTerms Tm` of the terms of scale `k` has no meaning at the new level `k + 1`
(the successor step supplies that slice).  Terms that agree with `liftOldTerms Tm` on the levels
`j ≤ k` and with the new terms `Tnew` on the levels `j > k` satisfy all clauses of
`SFTermClauses` on the birth domain of scale `k + 1`, if `Tm` satisfies them on the birth domain of
scale `k`, `Tnew` satisfies them on the new birth domain, and the ideal kernel sequences of the
two scales agree.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Background

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

section Congr

variable {m₀ : ℕ} {T T' : Terms d L N₁ m₁ k N ϱ}

theorem Eloc_congr_level {j : ℕ} (hE : T.E j = T'.E j) (y : CTorus d L N₁ m₁ k)
    (ψ h : Fld d L N₁ m₁ k N) : Eloc m₀ T j y ψ h = Eloc m₀ T' j y ψ h := by
  unfold Eloc; rw [hE]

theorem Mloc_congr_level {j : ℕ} (hM : T.M j = T'.M j) (x : CTorus d L N₁ m₁ k)
    (ψ h g : Fld d L N₁ m₁ k N) : Mloc m₀ T j x ψ h g = Mloc m₀ T' j x ψ h g := by
  unfold Mloc; rw [hM]

end Congr

section Splice

omit [NeZero L] [NeZero N₁] in
theorem deconj_paving {m₀ j : ℕ} {r : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ j) :
    ∃ r0 ∈ pavingSymGroup (N₁ := L * N₁) (m₁ := m₁) (k := k) (d := d) L m₀ j,
      (oldTorusEquiv (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)).permCongrHom r0 = r := by
  rw [← oldTorusEquiv_pavingSymGroup] at hr
  obtain ⟨r0, h0, h⟩ := Subgroup.mem_map.1 hr
  exact ⟨r0, h0, h⟩

omit [NeZero L] [NeZero N₁] in
theorem deconj_full {j : ℕ} {r : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (hr : r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L j) :
    ∃ r0 ∈ fullJSymGroup (N₁ := L * N₁) (m₁ := m₁) (k := k) (d := d) L j,
      (oldTorusEquiv (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)).permCongrHom r0 = r := by
  rw [← oldTorusEquiv_fullJSymGroup] at hr
  obtain ⟨r0, h0, h⟩ := Subgroup.mem_map.1 hr
  exact ⟨r0, h0, h⟩

omit [NeZero L] [NeZero N₁] in
theorem exists_liftOldPoly (X : Set (CTorus d L N₁ m₁ (k + 1))) :
    ∃ X0 : Set (CTorus d L (L * N₁) m₁ k), X = liftOldPoly X0 :=
  ⟨oldTorusEquiv.symm '' X, by simp [liftOldPoly, Set.image_image]⟩


variable {P : Consts} {Rg : Regime L} {a : ℕ → ℝ}
  {Tm : Terms d L (L * N₁) m₁ k N ϱ}
  {Tnew T' : Terms d L N₁ m₁ (k + 1) N ϱ}

/-- **All clauses of `SFTermClauses` on the birth domain of scale `k + 1` for terms spliced from
the pulled-back old terms (levels `≤ k`) and the new terms (levels `> k`).** -/
theorem sfTermClauses_splice_birth
    (ha : aIdeal L (k + 1) (a (k + 1)) = aIdeal L k (a k))
    (hν : ∀ j, 1 ≤ j → j ≤ k → 0 ≤ Rg.ν j)
    (hcl : SFTermClauses P (birthXiDom P Rg a (L * N₁)) Tm)
    (hnew : SFTermClauses P (birthXiDom P Rg a N₁) Tnew)
    (hE : ∀ j, j ≤ k → T'.E j = (liftOldTerms Tm).E j)
    (hM : ∀ j, j ≤ k → T'.M j = (liftOldTerms Tm).M j)
    (hgs : ∀ j, j ≤ k → T'.gs j = (liftOldTerms Tm).gs j)
    (hE' : ∀ j, ¬ j ≤ k → T'.E j = Tnew.E j)
    (hM' : ∀ j, ¬ j ≤ k → T'.M j = Tnew.M j)
    (hgs' : ∀ j, ¬ j ≤ k → T'.gs j = Tnew.gs j) :
    SFTermClauses P (birthXiDom P Rg a N₁) T' where
  gs_spec := by
    intro j hj1 hjk X hX
    by_cases h : j ≤ k
    · rw [hgs j h]; exact liftOldTerms_gs_spec hcl hj1 h hX
    · rw [hgs' j h]; exact hnew.gs_spec j hj1 hjk X hX
  analyticE := by
    intro j hj1 hjk y X hX hy
    by_cases h : j ≤ k
    · rw [hgs j h, hE j h]
      exact liftOldTerms_analyticE_birth ha hcl hj1 h (hν j hj1 h) hX hy
    · rw [hgs' j h, hE' j h]; exact hnew.analyticE j hj1 hjk y X hX hy
  analyticM := by
    intro j hj1 hjk x X hX hx
    by_cases h : j ≤ k
    · rw [hgs j h, hM j h]
      exact liftOldTerms_analyticM_birth ha hcl hj1 h (hν j hj1 h) hX hx
    · rw [hgs' j h, hM' j h]; exact hnew.analyticM j hj1 hjk x X hX hx
  rotE := by
    intro j hj1 hjk y X hX hy R hR Ψ h₁ hd hRd
    by_cases h : j ≤ k
    · rw [hgs j h] at hd hRd; rw [hE j h]
      exact liftOldTerms_rotE_birth ha hcl hj1 h (hν j hj1 h) hX hy hR hd hRd
    · rw [hgs' j h] at hd hRd; rw [hE' j h]
      exact hnew.rotE j hj1 hjk y X hX hy R hR Ψ h₁ hd hRd
  pavingGS := by
    intro j hj1 hjk X hX r hr i
    by_cases h : j ≤ k
    · rw [hgs j h]
      obtain ⟨r0, hr0, rfl⟩ := deconj_paving hr
      obtain ⟨X0, rfl⟩ := exists_liftOldPoly X
      exact liftOldTerms_pavingGS hcl hj1 h ((oldTorusEquiv_isPolyDom_iff).2 hX) r0 hr0 i
    · rw [hgs' j h]; exact hnew.pavingGS j hj1 hjk X hX r hr i
  eucE := by
    intro j hj1 hjk y X hX hy r hr Ψ h₁ hd hd'
    by_cases h : j ≤ k
    · rw [hgs j h] at hd hd'; rw [hE j h]
      obtain ⟨r0, hr0, rfl⟩ := deconj_paving hr
      obtain ⟨X0, rfl⟩ := exists_liftOldPoly X
      obtain ⟨y0, rfl⟩ := oldTorusEquiv.surjective y
      have hX0 := (oldTorusEquiv_isPolyDom_iff).2 hX
      refine liftOldTerms_eucE_birth ha hcl hj1 h (hν j hj1 h) hX0
        (by simpa [liftOldPoly] using hy) r0 hr0 Ψ h₁ hd
        (by rw [liftOldPoly_act]; exact hd')
    · rw [hgs' j h] at hd hd'; rw [hE' j h]
      exact hnew.eucE j hj1 hjk y X hX hy r hr Ψ h₁ hd hd'
  eucEloc := by
    intro j hj1 hjk y r hr Ψ h₁ hd hd'
    by_cases h : j ≤ k
    · rw [Eloc_congr_level (hE j h), Eloc_congr_level (hE j h)]
      obtain ⟨r0, hr0, rfl⟩ := deconj_full hr
      obtain ⟨y0, rfl⟩ := oldTorusEquiv.surjective y
      exact liftOldTerms_eucEloc_birth ha hcl hj1 h (hν j hj1 h) y0 r0 hr0 Ψ h₁ hd hd'
    · rw [Eloc_congr_level (hE' j h), Eloc_congr_level (hE' j h)]
      exact hnew.eucEloc j hj1 hjk y r hr Ψ h₁ hd hd'
  rotM := by
    intro j hj1 hjk x X hX hx R hR Ψ h₁ g hg hRg hd hRd
    by_cases h : j ≤ k
    · rw [hgs j h] at hd hRd; rw [hM j h]
      exact liftOldTerms_rotM_birth ha hcl hj1 h (hν j hj1 h) hX hx hR hg hRg hd hRd
    · rw [hgs' j h] at hd hRd; rw [hM' j h]
      exact hnew.rotM j hj1 hjk x X hX hx R hR Ψ h₁ g hg hRg hd hRd
  eucM := by
    intro j hj1 hjk x X hX hx r hr Ψ h₁ g hd hd'
    by_cases h : j ≤ k
    · rw [hgs j h] at hd hd'; rw [hM j h]
      obtain ⟨r0, hr0, rfl⟩ := deconj_paving hr
      obtain ⟨X0, rfl⟩ := exists_liftOldPoly X
      obtain ⟨x0, rfl⟩ := oldTorusEquiv.surjective x
      have hX0 := (oldTorusEquiv_isPolyDom_iff).2 hX
      exact liftOldTerms_eucM_birth ha hcl hj1 h (hν j hj1 h) hX0
        (by simpa [liftOldPoly] using hx) r0 hr0 Ψ h₁ g hd
        (by rw [liftOldPoly_act]; exact hd')
    · rw [hgs' j h] at hd hd'; rw [hM' j h]
      exact hnew.eucM j hj1 hjk x X hX hx r hr Ψ h₁ g hd hd'
  eucMloc := by
    intro j hj1 hjk x r hr Ψ h₁ g hd hd'
    by_cases h : j ≤ k
    · rw [Mloc_congr_level (hM j h), Mloc_congr_level (hM j h)]
      obtain ⟨r0, hr0, rfl⟩ := deconj_full hr
      obtain ⟨x0, rfl⟩ := oldTorusEquiv.surjective x
      exact liftOldTerms_eucMloc_birth ha hcl hj1 h (hν j hj1 h) x0 r0 hr0 Ψ h₁ g hd hd'
    · rw [Mloc_congr_level (hM' j h), Mloc_congr_level (hM' j h)]
      exact hnew.eucMloc j hj1 hjk x r hr Ψ h₁ g hd hd'
  localE := by
    intro j y X Ψ Ψ' h₁ h₂ hag
    by_cases h : j ≤ k
    · rw [hE j h]; exact liftOldTerms_localE hcl j y X Ψ Ψ' h₁ h₂ hag
    · rw [hE' j h]; exact hnew.localE j y X Ψ Ψ' h₁ h₂ hag
  localM := by
    intro j x X Ψ Ψ' h₁ h₂ g g' hag
    by_cases h : j ≤ k
    · rw [hM j h]; exact liftOldTerms_localM hcl j x X Ψ Ψ' h₁ h₂ g g' hag
    · rw [hM' j h]; exact hnew.localM j x X Ψ Ψ' h₁ h₂ g g' hag
  boundE := by
    intro j hj1 hjk y X hX hy Ψ h₁ hd
    by_cases h : j ≤ k
    · rw [hgs j h] at hd; rw [hE j h]
      exact liftOldTerms_boundE_birth ha hcl hj1 h (hν j hj1 h) hX hy hd
    · rw [hgs' j h] at hd; rw [hE' j h]
      exact hnew.boundE j hj1 hjk y X hX hy Ψ h₁ hd
  boundM := by
    intro j hj1 hjk x X hX hx Ψ h₁ g hd hg
    by_cases h : j ≤ k
    · rw [hgs j h] at hd; rw [hM j h]
      exact liftOldTerms_boundM_birth ha hcl hj1 h (hν j hj1 h) hX hx hd hg
    · rw [hgs' j h] at hd; rw [hM' j h]
      exact hnew.boundM j hj1 hjk x X hX hx Ψ h₁ g hd hg

end Splice

end Balaban.Fluctuation
