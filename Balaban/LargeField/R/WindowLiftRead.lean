/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedWindowAnc
public import Balaban.LargeField.Operators.DomainIdentity

/-!
# The large-field variable of a descendant, read on a block near an ancestor

P7 p. 501 (2.14) with P6 p. 7 (2.16): the data of the piece of a component `Y` of `Z^pre_s`, a
descendant of the window component `Z` at scale `m`, read the variables `ψ_j` of the configuration
of `Z` restricted to `Y` (`ρ`).  On a block of scale `j < s` whose `π_s`-cube lies in `Y`, or is
not over the lineage of `Z`, the large-field variable of the restriction is the large-field
variable of the configuration of `Z`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

section Lin

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K}

/-- The lineage of a descendant lies in the lineage of the component. -/
theorem lin_subset_of_desc {a s m : ℕ} {Y : H.Comp s} {Z : H.Comp m} (hd : H.Desc s m Y Z) :
    ((H.lin a s Y : Finset (Torus S.d (n a))) : Set (Torus S.d (n a))) ⊆
      ((H.lin a m Z : Finset (Torus S.d (n a))) : Set (Torus S.d (n a))) := by
  intro e he
  obtain ⟨Y', hd', he'⟩ := mem_lin.mp (Finset.mem_coe.mp he)
  exact Finset.mem_coe.mpr (mem_lin.mpr ⟨Y', hd'.trans hd, he'⟩)

/-- On the fine set of a descendant `Y` the lineages of `Y` and of `Z` agree. -/
theorem mem_lin_desc_iff {a s m : ℕ} (has : a ≤ s) (hsK : s ≤ K) {Y : H.Comp s} {Z : H.Comp m}
    (hd : H.Desc s m Y Z) {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : cubeMap n S.L M K s x ∈ Y.1) :
    cubeMap n S.L M K a x ∈ ((H.lin a m Z : Finset (Torus S.d (n a))) : Set _) ↔
      cubeMap n S.L M K a x ∈ ((H.lin a s Y : Finset (Torus S.d (n a))) : Set _) := by
  constructor
  · intro h
    obtain ⟨Y'', hd'', hxY''⟩ := mem_lin.mp (Finset.mem_coe.mp h)
    obtain ⟨W, h1, -⟩ := Desc.split has hd.le hd''
    have hxW : cubeMap n S.L M K s x ∈ W.1 := cubeMap_mem_of_desc H.F.hnn hsK h1 hxY''
    have hWY : W = Y := Subtype.ext (comp_eq_of_mem W.2 Y.2 hxW hx)
    subst hWY
    exact Finset.mem_coe.mpr (mem_lin.mpr ⟨Y'', h1, hxY''⟩)
  · exact fun h => lin_subset_of_desc hd h

/-- The large-field variable sets of a descendant and of the component agree on the fine set of the
descendant. -/
theorem varSet_large_iff_desc {s m : ℕ} (hmK : m ≤ K) {Y : H.Comp s} {Z : H.Comp m}
    (hd : H.Desc s m Y Z) {j : ℕ} (hj : j < s) {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : cubeMap n S.L M K s x ∈ Y.1) :
    x ∈ varSet (H.localHistory M K s Y) j .large ↔ x ∈ varSet (H.localHistory M K m Z) j .large := by
  have hsm := hd.le
  have hsK : s ≤ K := hsm.trans hmK
  have hxZ : cubeMap n S.L M K m x ∈ Z.1 := cubeMap_mem_of_desc H.F.hnn hmK hd hx
  have hlin := mem_lin_desc_iff (M := M) (a := j + 1) (by omega) hsK hd hx
  have h1 : x ∈ (H.localHistory M K s Y).Z (j + 1) ↔ x ∈ (H.localHistory M K m Z).Z (j + 1) := by
    rw [localHistory_Z Y hsK (by omega), localHistory_Z Z hmK (by omega)]
    exact hlin.symm
  have h2 : x ∈ (H.localHistory M K s Y).Omega j ↔ x ∈ (H.localHistory M K m Z).Omega j := by
    show (cubeMap n S.L M K (j + 1) x ∈ ((H.locRH s Y).step j).Omega ∧ cubeMap n S.L M K s x ∈ Y.1) ↔
      (cubeMap n S.L M K (j + 1) x ∈ ((H.locRH m Z).step j).Omega ∧ cubeMap n S.L M K m x ∈ Z.1)
    rw [mem_locOmega_iff' hsK Y hj, mem_locOmega_iff' hmK Z (by omega), hlin]
    simp [hx, hxZ]
  show (x ∈ (H.localHistory M K s Y).Z (j + 1) ∧ x ∉ (H.localHistory M K s Y).Omega j) ↔
    (x ∈ (H.localHistory M K m Z).Z (j + 1) ∧ x ∉ (H.localHistory M K m Z).Omega j)
  rw [h1, h2]

end Lin

section Read

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

/-- **The new large-field variable of a descendant, read from the configuration of the component.**
Let `Y` be a component of `Z^pre_{k+1}` that is not kept and a descendant of `Z`, `ρx` the
restriction of a configuration `x` of the variables of `Z` to those of `Y`.  On a block `b` of
scale `k` whose `π_{k+1}`-cube lies in `Y` or is not over the lineage of `Z`, the variable `ψ_k` of
`ρx` is the variable `ψ_k` of `x`. -/
theorem subVarField_desc_eq {k m : ℕ} (hmK : m ≤ K) {Y : H.Comp (k + 1)} {Z : H.Comp m}
    (hd : H.Desc (k + 1) m Y Z)
    (hq : ∀ t, k + 1 < t → ∀ Y' : H.Comp t, H.Desc t m Y' Z → ¬ IsKept H t Y')
    (hnk : ¬ IsKept H (k + 1) Y)
    (ρx : SubCfg N (H.localHistory M K (k + 1) Y) (k + 1)
      (locOp geo cs SD KD hH lab (k + 1) (hd.le.trans hmK) Y).A)
    (x : SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A)
    (hρx : ∀ p : ↥(locOp geo cs SD KD hH lab (k + 1) (hd.le.trans hmK) Y).A, ρx p =
      x ⟨_, locOp_A_incl geo cs SD KD hmK hd hq p.1 p.2⟩)
    (b : BlockAt S n M K k) {x0 : Torus S.d (M * n K * S.L ^ K)}
    (hx0 : jBlock S.d S.L (M * n K) K k x0 = b)
    (hcase : cubeMap n S.L M K (k + 1) x0 ∈ Y.1 ∨
      cubeMap n S.L M K (k + 1) x0 ∉ ((H.lin (k + 1) m Z : Finset (Torus S.d (n (k + 1)))) : Set _)) :
    subVarField N ρx k b = subVarField N x k b := by
  classical
  have hsm := hd.le
  have hsK : k + 1 ≤ K := hsm.trans hmK
  unfold subVarField
  by_cases hex : ∃ (hj' : k < k + 1) (hb : BlockSub (S := S) (n := n) (M := M) (K := K) k b
        (varSet (H.localHistory M K (k + 1) Y) k .large)),
      mkVar (H.localHistory M K (k + 1) Y) (k + 1) k .large b hj' hb ∈
        (locOp geo cs SD KD hH lab (k + 1) hsK Y).A
  · obtain ⟨hj', hb, hA⟩ := hex
    have hb' : BlockSub (S := S) (n := n) (M := M) (K := K) k b
        (varSet (H.localHistory M K m Z) k .large) :=
      fun x1 hx1 => varSet_desc_mono hmK hd (Nat.lt_succ_self k) .large (hb x1 hx1)
    have hA' := locOp_A_incl geo cs SD KD hmK hd hq _ hA
    have hex' : ∃ (hj'' : k < m) (hb'' : BlockSub (S := S) (n := n) (M := M) (K := K) k b
        (varSet (H.localHistory M K m Z) k .large)),
      mkVar (H.localHistory M K m Z) m k .large b hj'' hb'' ∈
        (locOp geo cs SD KD hH lab m hmK Z).A := ⟨by omega, hb', hA'⟩
    have hP : ∃ (hj' : k < k + 1) (hb : BlockSub (S := S) (n := n) (M := M) (K := K) k b
        (varSet (H.localHistory M K (k + 1) Y) k .large)),
      mkVar (H.localHistory M K (k + 1) Y) (k + 1) k .large b hj' hb ∈
        (locOp geo cs SD KD hH lab (k + 1) hsK Y).A := ⟨hj', hb, hA⟩
    simp only [hP, hex', ↓reduceDIte]
    rw [hρx ⟨_, hA⟩]
    exact toEuc_eq_of_val_eq x ⟨_, _⟩ ⟨_, _⟩ rfl
  · simp only [hex, ↓reduceDIte]
    split_ifs with h2
    swap
    · rfl
    exfalso
    obtain ⟨hj'', hb'', hA''⟩ := h2
    have hz0 : x0 ∈ varSet (H.localHistory M K m Z) k .large := hb'' x0 hx0
    rcases hcase with hin | hout
    · apply hex
      refine ⟨Nat.lt_succ_self k, fun x1 hx1 => ?_, ?_⟩
      · have hcube : cubeMap n S.L M K (k + 1) x1 = cubeMap n S.L M K (k + 1) x0 :=
          cubeMap_eq_of_jBlock_eq (Nat.le_succ k) hsK H.F.hnn (hx1.trans hx0.symm)
        have hin1 : cubeMap n S.L M K (k + 1) x1 ∈ Y.1 := hcube ▸ hin
        exact (varSet_large_iff_desc hmK hd (Nat.lt_succ_self k) hin1).mpr (hb'' x1 hx1)
      · exact newVars_sub_locOp_A geo cs SD KD hsK hnk (show _ ∈ newVars _ k from rfl)
    · apply hout
      have h1 : x0 ∈ (H.localHistory M K m Z).Z (k + 1) := hz0.1
      rw [localHistory_Z Z hmK (by omega)] at h1
      exact h1

end Read

end Balaban.LargeField
