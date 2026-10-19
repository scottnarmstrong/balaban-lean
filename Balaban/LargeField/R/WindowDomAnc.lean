/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDomChi

/-!
# The domain conditions down the lineage of the window (blocker 4)

The weight of the operator of `Z` is the product of the weights of the step kernel of `Z` and of the
operators of its old parts (`locOp_absW_level`), evaluated at the output `ψ_k` read from the variables
of `Z` and at the restriction of the variables.  Hence a nonzero weight of the operator of `Z` at the
window point gives a nonzero weight of the operator of every ancestor `c` of scale `j + 1`
(`k₁ ≤ j < m'`) at the point `(ancOut c P (ρ x), ρ x)` read from the variables of its successor `P`
(`locOp_absW_ne_zero_anc`), and `chiDomAt_anc_of_locOp_kernel_ne_zero` gives `ChiDomAt` there.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

section Anc

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

/-- A nonzero weight of a kernel is a nonzero kernel value. -/
theorem lfKernel_K_ne_zero_of_absW_ne_zero {O X H' ι : Type*} [MeasurableSpace O] [MeasurableSpace X]
    [Fintype ι] (T : LFKernel O X H' ι) {o : O} {x : X} {h : H'} {g : ι → ℂ}
    (hw : T.absW o x h g ≠ 0) : T.K o x h ≠ 0 := by
  intro h0
  apply hw
  unfold LFKernel.absW
  rw [h0, zero_mul, ENNReal.ofReal_zero]

variable (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ}
  {lamHat : ℕ → ℝ} (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
/-- **A nonzero weight of the operator of `Z` gives a nonzero weight of the operator of every ancestor
`c` of scale `j + 1`, `k₁ ≤ j < m'`, at the point read from the variables of its successor `P`.** -/
theorem locOp_absW_ne_zero_anc (k1 : ℕ) :
    ∀ (m' : ℕ) (_ : k1 ≤ m') (hm : m' + 1 ≤ K) (Z : H.Comp (m' + 1))
      (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
      (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
        SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
          (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
        SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
      (_ : ∀ s (hs : k1 ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
        x ⟨_, locOp_A_incl geo cs SD KD hm hd
          (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
      (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
      (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ),
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.absW o x hv g ≠ 0 →
      ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
        (c : ↥(H.parts (j.1 + 1) P.1)),
        (locOp geo cs SD KD hH lab (j.1 + 1)
          ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm) c.1).T.absW
          (ancOut c.1 P.1 (ρ (j.1 + 1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1
            (mem_ancFin.mp P.2) x))
          (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
            (desc_of_parts c.2 (mem_ancFin.mp P.2)) x) hv g ≠ 0 := by
  intro m' hk1
  induction m', hk1 using Nat.le_induction with
  | base =>
    intro hm Z hq ρ hρ o x hv g hne j
    exfalso
    simpa using j.2
  | succ m' hk1 ih =>
    intro hm Z hq ρ hρ o x hv g hne j P c
    have hnk := hq (m' + 1 + 1) (by omega) Z (Desc.refl Z)
    rw [locOp_absW_level geo cs SD KD hm hnk o x hv g] at hne
    obtain ⟨-, hprod⟩ := mul_ne_zero_iff.1 hne
    obtain ⟨j0, hj0⟩ := j
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj0
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj2 with hlt | heq
    · -- the successor lies below a part `Y` of `Z`
      obtain ⟨P0, hP0⟩ := P
      have hdP : H.Desc (j0 + 1 + 1) (m' + 1 + 1) P0 Z := mem_ancFin.mp hP0
      obtain ⟨Y, hY, hdY⟩ := (desc_succ_iff (show j0 + 1 + 1 ≤ m' + 1 by omega)).mp hdP
      have hqY : ∀ s, k1 < s → ∀ Y' : H.Comp s, H.Desc s (m' + 1) Y' Y → ¬ IsKept H s Y' :=
        fun s hs Y' h' => hq s hs Y' (Desc.trans h' (Desc.single ((H.mem_parts _ _ _).mp hY).1
          ((H.mem_parts _ _ _).mp hY).2))
      obtain ⟨ρY, hρY⟩ := exists_rho geo cs SD KD (lab := lab) (hH := hH) k1 m' (by omega) Y hqY
      have hYne := Finset.prod_ne_zero_iff.1 hprod ⟨Y, hY⟩ (Finset.mem_univ _)
      have key := ih (by omega) Y hqY ρY hρY (ancOut Y Z x)
        (ancRestrict hm hY (locOp_A_anc geo cs SD KD hm hnk hY) x) hv g hYne ⟨j0, Finset.mem_Ico.mpr ⟨hj1, hlt⟩⟩
        ⟨P0, mem_ancFin.mpr hdY⟩ c
      have hcompat : ∀ (s : ℕ) (hs : k1 ≤ s) (P' : H.Comp s)
          (hdY' : H.Desc s (m' + 1) P' Y) (hd : H.Desc s (m' + 1 + 1) P' Z),
          ρ s hs P' hd x = ρY s hs P' hdY'
            (ancRestrict hm hY (locOp_A_anc geo cs SD KD hm hnk hY) x) :=
        fun s hs P' hdY' hd => funext fun p => by rw [hρ, hρY]; rfl
      rw [hcompat (j0 + 1 + 1) (by omega) P0 hdY hdP, hcompat (j0 + 1) (by omega) c.1
        (desc_of_parts c.2 hdY) (desc_of_parts c.2 hdP)]
      exact key
    · -- the successor is `Z` itself
      subst heq
      obtain ⟨P0, hP0⟩ := P
      obtain rfl : P0 = Z := Finset.mem_singleton.mp
        ((Finset.ext_iff.mp (ancFin_self (j0 + 1 + 1) Z) P0).mp hP0)
      have e1 : ρ (j0 + 1 + 1) (by omega) P0 (Desc.refl P0) x = x :=
        funext fun p => by rw [hρ]; rfl
      have e2 : ρ (j0 + 1) (by omega) c.1 (desc_of_parts c.2 (Desc.refl P0)) x =
          ancRestrict hm c.2 (locOp_A_anc geo cs SD KD hm hnk c.2) x :=
        funext fun p => by rw [hρ]; rfl
      rw [e1, e2]
      exact Finset.prod_ne_zero_iff.1 hprod c (Finset.mem_univ _)

open Classical in
/-- **`ChiDomAt` at every ancestor of the window**: a nonzero kernel of the operator of `Z` at the window
point gives the domain condition for the operator of every ancestor `c` of scale `j + 1`
(`k₁ ≤ j < m'`) at the point read from the variables of its successor `P`. -/
theorem chiDomAt_anc_of_locOp_kernel_ne_zero (k1 m' : ℕ) (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
    (Z : H.Comp (m' + 1))
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
    (hρ : ∀ s (hs : k1 ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (hv : EuclideanSpace ℝ (Fin N))
    (hK : (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.K o x hv ≠ 0)
    (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
    (c : ↥(H.parts (j.1 + 1) P.1)) :
    ChiDomAt geo cs H (j.1 + 1) c.1
      (ancOut c.1 P.1 (ρ (j.1 + 1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1
        (mem_ancFin.mp P.2) x))
      (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
        (desc_of_parts c.2 (mem_ancFin.mp P.2)) x) :=
  chiDomAt_of_locOp_kernel_ne_zero geo cs SD KD ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
    c.1 _ _ hv (lfKernel_K_ne_zero_of_absW_ne_zero _
      (locOp_absW_ne_zero_anc geo cs SD KD k1 m' hk1 hm Z hq ρ hρ o x hv 0
        (absW_ne_zero_of_K_ne_zero _ hK 0) j P c))

open Classical in
/-- **`ChiDomAt` at every component of the lineage at the point read from the variables of `Z`**: for a
component `P` of the lineage at a scale `j + 2` with `k₁ ≤ j < m'` there is an output `oP` with
`ChiDomAt` for the operator of `P` at `(oP, ρ x)`: for `P = Z` it is `o`, otherwise `P` is a part of its
successor in the lineage and `chiDomAt_anc_of_locOp_kernel_ne_zero` applies. -/
theorem chiDomAt_exists_of_ancFin (k1 m' : ℕ) (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
    (Z : H.Comp (m' + 1))
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
    (hρ : ∀ s (hs : k1 ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (hv : EuclideanSpace ℝ (Fin N))
    (hK : (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.K o x hv ≠ 0)
    (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z)) :
    ∃ oP : OutT N R (H.localHistory M K (j.1 + 1 + 1) P.1) (j.1 + 1 + 1),
      ChiDomAt geo cs H (j.1 + 1 + 1) P.1 oP
        (ρ (j.1 + 1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1
          (mem_ancFin.mp P.2) x) := by
  obtain ⟨j0, hj0⟩ := j
  obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj0
  obtain ⟨P0, hP0⟩ := P
  have hd : H.Desc (j0 + 1 + 1) (m' + 1) P0 Z := mem_ancFin.mp hP0
  rcases Nat.lt_succ_iff_lt_or_eq.1 (hd.le : j0 + 1 + 1 ≤ m' + 1) with hlt | heq
  · obtain ⟨hrem, P1, hs1, hd1⟩ := Desc.first hd (by omega)
    have hc : P0 ∈ H.parts (j0 + 1 + 1) P1 := (H.mem_parts _ _ _).mpr ⟨hrem, hs1⟩
    have hj' : j0 + 1 ∈ Finset.Ico k1 m' := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    exact ⟨_, chiDomAt_anc_of_locOp_kernel_ne_zero geo cs SD KD k1 m' hk1 hm Z hq ρ hρ o x hv hK
      ⟨j0 + 1, hj'⟩ ⟨P1, mem_ancFin.mpr hd1⟩ ⟨P0, hc⟩⟩
  · have hm1 : j0 + 1 = m' := by omega
    subst hm1
    obtain rfl : P0 = Z := Finset.mem_singleton.mp
      ((Finset.ext_iff.mp (ancFin_self (j0 + 1 + 1) Z) P0).mp hP0)
    have e1 : ρ (j0 + 1 + 1) (by omega) P0 hd x = x := funext fun p => by rw [hρ]; rfl
    rw [e1]
    exact ⟨o, chiDomAt_of_locOp_kernel_ne_zero geo cs SD KD hm P0 o x hv hK⟩

end Anc

end Balaban.LargeField
