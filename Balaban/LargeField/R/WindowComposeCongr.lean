/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowComposeGeom
public import Balaban.LargeField.R.WindowComposeChain
public import Balaban.LargeField.R.RRemovedHidRead

/-!
# The sum of the main actions of the pieces does not read the node variables (blocker 4, item S7)

`notes/phase1/LF4R-PLAN.md` §9.3, item S7.  `Atot_congr`: the sum `∑ 𝒜_{j+1}(c; ψ)` of the main actions of the
pieces of a quiet window (the exponent of `window_chain_le_action`) takes the same value at two window
configurations `(o₁, x₁)`, `(o₂, x₂)` whose outputs agree off the Gaussian blocks of `Z` and whose variables
agree off the node variables `Nd` of the window (`mainActionLoc_congr_window`, W958; the blocks of `V_c` that are
not Gaussian blocks of `c` are not nodes: `gaussBlocks_not_mem_Vblk`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory ENNReal

section Congr

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

/-- **The restriction to an ancestor agrees at the large-field variables that are not nodes.** -/
theorem rho_agree {k1 m' : ℕ} (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
    (hρ : ∀ s (hs : k1 ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
    (Nd : Set ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hNd : ∀ p, p ∈ Nd ↔ p.1.1.2.1 = VarKind.large ∧ nd ⟨(p.1.1.1 : ℕ), p.1.1.2.2⟩)
    (x₁ x₂ : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (hxag : ∀ p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A, p ∉ Nd →
      VarVal.toEuc (x₁ p) = VarVal.toEuc (x₂ p))
    {s : ℕ} (hs : k1 ≤ s) {P : H.Comp s} (hd : H.Desc s (m' + 1) P Z)
    (p : ↥(locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
    (hn : ¬ nd ⟨(p.1.1.1 : ℕ), p.1.1.2.2⟩) :
    VarVal.toEuc (ρ s hs P hd x₁ p) = VarVal.toEuc (ρ s hs P hd x₂ p) := by
  rw [hρ, hρ]
  refine hxag _ fun hp => hn ?_
  exact ((hNd _).mp hp).2


/-- Restricting to the new variables does not change the agreement of the fields at the blocks that are not
nodes. -/
theorem newRestrict_subVarField_congr {a : LocalHistory S n M K} {k : ℕ}
    {A : Set (InternalVars a (k + 1))} (h : newVars a k ⊆ A) (x₁ x₂ : SubCfg N a (k + 1) A)
    (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hag : ∀ p : ↥A, ¬ nd ⟨(p.1.1.1 : ℕ), p.1.1.2.2⟩ → VarVal.toEuc (x₁ p) = VarVal.toEuc (x₂ p))
    (q : ℕ) (y : BlockAt S n M K q) (hy : ¬ nd ⟨q, y⟩) :
    subVarField N (newRestrict a h x₁) q y = subVarField N (newRestrict a h x₂) q y := by
  refine subVarField_congr _ _ q y fun p _ hs hb => ?_
  refine hag ⟨p.1, h p.2⟩ ?_
  have : (⟨(p.1.1.1 : ℕ), p.1.1.2.2⟩ : Σ s, BlockAt S n M K s) = ⟨q, y⟩ := Sigma.ext hs hb
  rw [this]; exact hy

open Classical in
/-- **One piece `(j, P, c)` of the window does not read the nodes.** -/
theorem piece_main_congr {k1 m' : ℕ} (hMS : M = S.M) (hk1p : 1 ≤ k1) (hm : m' + 1 ≤ K)
    {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
    (hρ : ∀ s (hs : k1 ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
    (Nd : Set ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (hNd : ∀ p, p ∈ Nd ↔ p.1.1.2.1 = VarKind.large ∧ nd ⟨(p.1.1.1 : ℕ), p.1.1.2.2⟩)
    (x₁ x₂ : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (hxag : ∀ p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A, p ∉ Nd →
      VarVal.toEuc (x₁ p) = VarVal.toEuc (x₂ p))
    (hv : EuclideanSpace ℝ (Fin N)) (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
    (c : ↥(H.parts (j.1 + 1) P.1)) :
    mainActionLoc geo (H.locRH (j.1 + 1) c.1) j.1 c.1.1
            (locComp_mem H (by have := (Finset.mem_Ico.mp j.2).2; omega) c.1)
            (by have := (Finset.mem_Ico.mp j.2).2; omega) cs (locRH_rem (j.1 + 1) c.1)
            (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
              (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x₁))
            (newRestrict (H.localHistory M K (j.1 + 1) c.1)
              (newVars_sub_locOp_A geo cs SD KD
                ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2))))
              (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                (desc_of_parts c.2 (mem_ancFin.mp P.2)) x₁)) hv =
    mainActionLoc geo (H.locRH (j.1 + 1) c.1) j.1 c.1.1
            (locComp_mem H (by have := (Finset.mem_Ico.mp j.2).2; omega) c.1)
            (by have := (Finset.mem_Ico.mp j.2).2; omega) cs (locRH_rem (j.1 + 1) c.1)
            (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
              (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x₂))
            (newRestrict (H.localHistory M K (j.1 + 1) c.1)
              (newVars_sub_locOp_A geo cs SD KD
                ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2))))
              (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                (desc_of_parts c.2 (mem_ancFin.mp P.2)) x₂)) hv := by
  have hj := Finset.mem_Ico.mp j.2
  have hd := desc_of_parts c.2 (mem_ancFin.mp P.2)
  have hjK : j.1 + 1 ≤ K := by omega
  refine mainActionLoc_congr_window geo cs nd hnd (by omega) (by omega) hjK c.1 _ _ _ _ hv ?_ ?_
  · intro y hy
    refine subVarField_congr _ _ (j.1 + 1) y.1 fun p _ hs hb => ?_
    refine rho_agree geo cs SD KD hm hq ρ hρ Nd nd hNd x₁ x₂ hxag _ _ p ?_
    have hpy : (⟨(p.1.1.1 : ℕ), p.1.1.2.2⟩ : Σ s, BlockAt S n M K s) = ⟨j.1 + 1, y.1⟩ := Sigma.ext hs hb
    rw [hpy]
    intro hnd1
    obtain ⟨-, -, c'', hc'', hy'⟩ := (hnd j.1 y.1).mp hnd1
    by_cases hcc : c.1 = c''
    · subst hcc; exact hy hy'
    · exact gaussBlocks_not_mem_Vblk hMS hjK hcc y.2 hy'
  · intro q y hy
    refine newRestrict_subVarField_congr _ _ _ nd (fun p hn => ?_) q y hy
    exact rho_agree geo cs SD KD hm hq ρ hρ Nd nd hNd x₁ x₂ hxag _ _ p hn

open Classical in
/-- **The sum of the main actions of the pieces does not read the nodes of the window** (S1 for all pieces).
Two window configurations `(o₁, x₁)`, `(o₂, x₂)` with outputs equal off the Gaussian blocks of `Z` and variables
equal off the nodes have the same sum `∑ 𝒜_{j+1}(c; ψ)` over the pieces of the window. -/
theorem Atot_congr {k1 m' : ℕ} (hMS : M = S.M) (hk1p : 1 ≤ k1) (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
    (hρ : ∀ s (hs : k1 ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
    (Nd : Set ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (hNd : ∀ p, p ∈ Nd ↔ p.1.1.2.1 = VarKind.large ∧ nd ⟨(p.1.1.1 : ℕ), p.1.1.2.2⟩)
    (o₁ o₂ : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x₁ x₂ : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (hoo : ∀ y : Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1),
      y.1 ∉ gaussBlocks (H.localHistory M K (m' + 1) Z) m' → o₁ y = o₂ y)
    (hxag : ∀ p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A, p ∉ Nd →
      VarVal.toEuc (x₁ p) = VarVal.toEuc (x₂ p))
    (hv : EuclideanSpace ℝ (Fin N)) :
    (mainActionLoc geo (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hm Z) hm cs
        (locRH_rem (m' + 1) Z) o₁ (newRestrict (H.localHistory M K (m' + 1) Z)
          (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x₁) hv +
      ∑ j : ↥(Finset.Ico k1 m'), ∑ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
        ∑ c : ↥(H.parts (j.1 + 1) P.1),
          mainActionLoc geo (H.locRH (j.1 + 1) c.1) j.1 c.1.1
            (locComp_mem H (by have := (Finset.mem_Ico.mp j.2).2; omega) c.1)
            (by have := (Finset.mem_Ico.mp j.2).2; omega) cs (locRH_rem (j.1 + 1) c.1)
            (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
              (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x₁))
            (newRestrict (H.localHistory M K (j.1 + 1) c.1)
              (newVars_sub_locOp_A geo cs SD KD
                ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2))))
              (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                (desc_of_parts c.2 (mem_ancFin.mp P.2)) x₁)) hv) =
    (mainActionLoc geo (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hm Z) hm cs
        (locRH_rem (m' + 1) Z) o₂ (newRestrict (H.localHistory M K (m' + 1) Z)
          (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x₂) hv +
      ∑ j : ↥(Finset.Ico k1 m'), ∑ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
        ∑ c : ↥(H.parts (j.1 + 1) P.1),
          mainActionLoc geo (H.locRH (j.1 + 1) c.1) j.1 c.1.1
            (locComp_mem H (by have := (Finset.mem_Ico.mp j.2).2; omega) c.1)
            (by have := (Finset.mem_Ico.mp j.2).2; omega) cs (locRH_rem (j.1 + 1) c.1)
            (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
              (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x₂))
            (newRestrict (H.localHistory M K (j.1 + 1) c.1)
              (newVars_sub_locOp_A geo cs SD KD
                ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2))))
              (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                (desc_of_parts c.2 (mem_ancFin.mp P.2)) x₂)) hv) := by
  have hndZ : ∀ p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A,
      ¬ nd ⟨(p.1.1.1 : ℕ), p.1.1.2.2⟩ → p ∉ Nd := fun p hn hp => hn ((hNd p).mp hp).2
  refine congrArg₂ (· + ·) ?_ ?_
  · refine mainActionLoc_congr_window geo cs nd hnd (by omega) le_rfl hm Z o₁ o₂ _ _ hv hoo ?_
    intro q y hy
    exact newRestrict_subVarField_congr _ x₁ x₂ nd (fun p hn => hxag p (hndZ p hn)) q y hy
  · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun c _ =>
      piece_main_congr geo cs SD KD hMS hk1p hm hq nd hnd ρ hρ Nd hNd x₁ x₂ hxag hv j P c

end Congr

end Balaban.LargeField
