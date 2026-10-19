/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedWindowAnc
public import Balaban.LargeField.R.WindowGaussTree
public import Balaban.Gaussian.StepKernelIntegral
public import Balaban.LargeField.R.DeltaPsiEdge

/-!
# The Gaussian factors of the quiet steps read from the variables of the top component (W918)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, item (b).  Along a quiet window of the component
`Z` of scale `m` every variable of an ancestor is a variable of `Z` (`inclVar_mem`); the field
`ψ_j(y)` read from the restriction `ρ x` to an ancestor is the field read from `x`
(`subVarField_rho`), and the Gaussian factor of a quiet step of an ancestor `c` is, in the variables of
`Z`, the product over the Gaussian blocks `y` of `c` of `z^N g_{c_j}(z ψ_{j+1}(y) - L^{-d} ∑ ψ_j(y'))`
(`gaussProd_read`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section Read

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

/-- **Fields read through the restriction to an ancestor.**  Let `ρY` be the restriction of the
configuration `x` of the variables of `Z` to the variables of the ancestor `Y` (`hρY`).  A large-field
variable `ψ_{j'}(y)` of the ancestor is read from `ρY` and from `x` alike. -/
theorem subVarField_rho {s m : ℕ} (hm : m ≤ K) {Z : H.Comp m} {Y : H.Comp s} (hd : H.Desc s m Y Z)
    (hq : ∀ t, s < t → ∀ Y' : H.Comp t, H.Desc t m Y' Z → ¬ IsKept H t Y')
    (x : SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hm Z).A)
    (ρY : SubCfg N (H.localHistory M K s Y) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) Y).A)
    (hρY : ∀ p, ρY p = x ⟨_, locOp_A_incl geo cs SD KD hm hd hq p.1 p.2⟩)
    {j' : ℕ} (y : BlockAt S n M K j') (hj : j' < s)
    (hb : BlockSub (S := S) (n := n) (M := M) (K := K) j' y
      (varSet (H.localHistory M K s Y) j' .large))
    (hA : mkVar (H.localHistory M K s Y) s j' .large y hj hb ∈
      (locOp geo cs SD KD hH lab s (hd.le.trans hm) Y).A) :
    subVarField N ρY j' y = subVarField N x j' y := by
  classical
  have hjm : j' < m := lt_of_lt_of_le hj hd.le
  have hbZ := inclVar_mem hm hd (mkVar (H.localHistory M K s Y) s j' .large y hj hb)
  have hAZ := locOp_A_incl geo cs SD KD hm hd hq _ hA
  have hex1 : ∃ hj' : j' < s, ∃ hb' : BlockSub (S := S) (n := n) (M := M) (K := K) j' y
      (varSet (H.localHistory M K s Y) j' .large),
      mkVar (H.localHistory M K s Y) s j' .large y hj' hb' ∈
        (locOp geo cs SD KD hH lab s (hd.le.trans hm) Y).A := ⟨hj, hb, hA⟩
  have hex2 : ∃ hj' : j' < m, ∃ hb' : BlockSub (S := S) (n := n) (M := M) (K := K) j' y
      (varSet (H.localHistory M K m Z) j' .large),
      mkVar (H.localHistory M K m Z) m j' .large y hj' hb' ∈
        (locOp geo cs SD KD hH lab m hm Z).A := ⟨hjm, hbZ, hAZ⟩
  have e1 : subVarField N ρY j' y =
      VarVal.toEuc (ρY ⟨mkVar (H.localHistory M K s Y) s j' .large y hj hb, hA⟩) := by
    simp only [subVarField, hex1, dite_true]
  have e2 : subVarField N x j' y =
      VarVal.toEuc (x ⟨mkVar (H.localHistory M K m Z) m j' .large y hjm hbZ, hAZ⟩) := by
    simp only [subVarField, hex2, dite_true]
  rw [e1, e2]
  have hpt : (⟨_, locOp_A_incl geo cs SD KD hm hd hq
        (mkVar (H.localHistory M K s Y) s j' .large y hj hb) hA⟩ :
      ↥(locOp geo cs SD KD hH lab m hm Z).A) =
      ⟨mkVar (H.localHistory M K m Z) m j' .large y hjm hbZ, hAZ⟩ := by
    apply Subtype.ext
    rfl
  have h1 := congrArg VarVal.toEuc (hρY ⟨mkVar (H.localHistory M K s Y) s j' .large y hj hb, hA⟩)
  have h2 := congrArg (fun a => VarVal.toEuc (x a)) hpt
  exact h1.trans h2

/-- A child block of a block contained in a set is contained in it. -/
theorem blockSub_child {j : ℕ} (hj : j + 1 ≤ K) {y : BlockAt S n M K (j + 1)}
    {B : Set (Torus S.d (M * n K * S.L ^ K))}
    (hy : BlockSub (S := S) (n := n) (M := M) (K := K) (j + 1) y B) {y' : BlockAt S n M K j}
    (hy' : blockMap S.L (M * n K * S.L ^ (K - (j + 1))) y' = y) :
    BlockSub (S := S) (n := n) (M := M) (K := K) j y' B := by
  intro x hx
  refine hy x ?_
  rw [jBlock_succ_eq_blockMap (k := K) (N₀ := M * n K) (L := S.L) hj x]
  show blockMap S.L (M * n K * S.L ^ (K - (j + 1))) (jBlock S.d S.L (M * n K) K j x) = y
  rw [show jBlock S.d S.L (M * n K) K j x = y' from hx, hy']

/-- Reading through `restrictSub`. -/
theorem subVarField_restrictSub {a : LocalHistory S n M K} {k : ℕ} {A B : Set (InternalVars a k)}
    (h : A ⊆ B) (x : SubCfg N a k B) {j : ℕ} (y : BlockAt S n M K j) (hj : j < k)
    (hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y (varSet a j .large))
    (hA : mkVar a k j .large y hj hb ∈ A) :
    subVarField N (restrictSub h x) j y = subVarField N x j y := by
  classical
  have hex1 : ∃ hj' : j < k, ∃ hb' : BlockSub (S := S) (n := n) (M := M) (K := K) j y
      (varSet a j .large), mkVar a k j .large y hj' hb' ∈ A := ⟨hj, hb, hA⟩
  have hex2 : ∃ hj' : j < k, ∃ hb' : BlockSub (S := S) (n := n) (M := M) (K := K) j y
      (varSet a j .large), mkVar a k j .large y hj' hb' ∈ B := ⟨hj, hb, h hA⟩
  simp only [subVarField, hex1, hex2, dite_true]
  rfl

/-- **(R1) The output of an old part read from the variables of the top component**: the field
`ψ_{j+1}(y)` of the output of `c` at a Gaussian block `y`, read from the restriction `ρP` to the
successor `P` of `c`, is `ψ_{j+1}(y)` read from the variables `x` of `Z`. -/
theorem outField_anc_read {k1 m j : ℕ} (hk1 : k1 ≤ j) (hm : m ≤ K) {Z : H.Comp m}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s m Y Z → ¬ IsKept H s Y)
    {P : H.Comp (j + 1 + 1)} (hdP : H.Desc (j + 1 + 1) m P Z) {c : H.Comp (j + 1)}
    (hc : c ∈ H.parts (j + 1) P)
    (x : SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hm Z).A)
    (ρP : SubCfg N (H.localHistory M K (j + 1 + 1) P) (j + 1 + 1)
      (locOp geo cs SD KD hH lab (j + 1 + 1) (hdP.le.trans hm) P).A)
    (hρP : ∀ p, ρP p = x ⟨_, locOp_A_incl geo cs SD KD hm hdP
      (fun t ht Y' h' => hq t (by omega) Y' h') p.1 p.2⟩)
    {y : BlockAt S n M K (j + 1)} (hy : y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j) :
    outField N (ancOut (N := N) (R := R) c P ρP) y = subVarField N x (j + 1) y := by
  classical
  have hK : j + 1 + 1 ≤ K := hdP.le.trans hm
  have hzb := gaussBlocks_zblk (hK := (by omega : j + 1 ≤ K)) c hy
  have hV := ZBlk_mem_Vblk (R := R) (by omega : j + 1 ≤ K) c y hzb
  have hb := outBlock_large hK P hc y hzb
  have hA : mkVar (H.localHistory M K (j + 1 + 1) P) (j + 1 + 1) (j + 1) .large y (by omega) hb ∈
      (locOp geo cs SD KD hH lab (j + 1 + 1) hK P).A :=
    newVars_sub_locOp_A geo cs SD KD hK (fun hk => hq _ (by omega) P hdP hk) rfl
  simp only [outField, hV, dite_true]
  show subVarField N ρP (j + 1) y = _
  exact (subVarField_rho geo cs SD KD hm hdP (fun t ht Y' h' => hq t (by omega) Y' h') x ρP hρP y
    (by omega) hb hA)

open Classical in
/-- **(R2) The coarsened field of a quiet step of an ancestor read from the variables of the top
component**: at a Gaussian block `y` of `c`, `(Qψ_j)(y) = L^{-d} ∑_{y' child of y} ψ_j(y')` with
`ψ_j(y')` read from the variables `x` of `Z`. -/
theorem qCoarseK_anc_read {k1 m j : ℕ} (hk1 : k1 ≤ j) (hm : m ≤ K) {Z : H.Comp m}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s m Y Z → ¬ IsKept H s Y)
    {c : H.Comp (j + 1)} (hdc : H.Desc (j + 1) m c Z)
    (x : SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hm Z).A)
    (ρC : SubCfg N (H.localHistory M K (j + 1) c) (j + 1)
      (locOp geo cs SD KD hH lab (j + 1) (hdc.le.trans hm) c).A)
    (hρC : ∀ p, ρC p = x ⟨_, locOp_A_incl geo cs SD KD hm hdc
      (fun t ht Y' h' => hq t (by omega) Y' h') p.1 p.2⟩)
    {y : BlockAt S n M K (j + 1)} (hy : y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j) :
    qCoarseK N (newRestrict (H.localHistory M K (j + 1) c)
        (newVars_sub_locOp_A geo cs SD KD (hdc.le.trans hm)
          (fun hk => hq (j + 1) (by omega) c hdc hk)) ρC) y =
      ((S.L : ℝ) ^ S.d)⁻¹ • ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K j =>
        blockMap S.L (M * n K * S.L ^ (K - (j + 1))) y' = y), subVarField N x j y' := by
  unfold qCoarseK
  congr 1
  refine Finset.sum_congr rfl fun y' hy' => ?_
  have hch := (Finset.mem_filter.mp hy').2
  have hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y'
      (varSet (H.localHistory M K (j + 1) c) j .large) :=
    blockSub_child (hdc.le.trans hm) hy hch
  have hAnew : mkVar (H.localHistory M K (j + 1) c) (j + 1) j .large y' (by omega) hb ∈
      newVars (H.localHistory M K (j + 1) c) j := rfl
  have hA := newVars_sub_locOp_A geo cs SD KD (hH := hH) (lab := lab) (hdc.le.trans hm)
    (fun hk => hq (j + 1) (by omega) c hdc hk) hAnew
  unfold newRestrict
  rw [subVarField_restrictSub _ ρC y' (by omega) hb hAnew]
  exact subVarField_rho geo cs SD KD hm hdc (fun t ht Y' h' => hq t (by omega) Y' h') x ρC hρC y'
    (by omega) hb hA

open Classical in
/-- **(b) The Gaussian product of a quiet step of an ancestor in the variables of `Z`**: for the
ancestor `c` of scale `j + 1` (with successor `P`), the product `gaussProd` over its Gaussian blocks is the product of
`z^N g_{c_j}(z ψ_{j+1}(y) - L^{-d} ∑_{y'} ψ_j(y'))` with all fields read from the variables `x` of `Z`. -/
theorem gaussProd_anc_read {k1 m j : ℕ} (hk1 : k1 ≤ j) (hm : m ≤ K) {Z : H.Comp m}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s m Y Z → ¬ IsKept H s Y)
    {P : H.Comp (j + 1 + 1)} (hdP : H.Desc (j + 1 + 1) m P Z) {c : H.Comp (j + 1)}
    (hc : c ∈ H.parts (j + 1) P)
    (x : SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hm Z).A)
    (ρP : SubCfg N (H.localHistory M K (j + 1 + 1) P) (j + 1 + 1)
      (locOp geo cs SD KD hH lab (j + 1 + 1) (hdP.le.trans hm) P).A)
    (hρP : ∀ p, ρP p = x ⟨_, locOp_A_incl geo cs SD KD hm hdP
      (fun t ht Y' h' => hq t (by omega) Y' h') p.1 p.2⟩)
    (ρC : SubCfg N (H.localHistory M K (j + 1) c) (j + 1)
      (locOp geo cs SD KD hH lab (j + 1) ((desc_of_parts hc hdP).le.trans hm) c).A)
    (hρC : ∀ p, ρC p = x ⟨_, locOp_A_incl geo cs SD KD hm (desc_of_parts hc hdP)
      (fun t ht Y' h' => hq t (by omega) Y' h') p.1 p.2⟩) :
    gaussProd N (H.localHistory M K (j + 1) c) j cs (ancOut (N := N) (R := R) c P ρP)
        (newRestrict (H.localHistory M K (j + 1) c)
          (newVars_sub_locOp_A geo cs SD KD ((desc_of_parts hc hdP).le.trans hm)
            (fun hk => hq (j + 1) (by omega) c (desc_of_parts hc hdP) hk)) ρC) =
      ∏ y : ↥(gaussBlocks (H.localHistory M K (j + 1) c) j), cs.z (j + 1) ^ N *
        gaussDens (cs.beta j * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
          (cs.z (j + 1) • subVarField N x (j + 1) y.1 - ((S.L : ℝ) ^ S.d)⁻¹ •
            ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K j =>
              blockMap S.L (M * n K * S.L ^ (K - (j + 1))) y' = y.1), subVarField N x j y') := by
  unfold gaussProd
  refine Finset.prod_congr (by ext; simp) fun y _ => ?_
  rw [gaussT_eq_gaussDens, outField_anc_read geo cs SD KD hk1 hm hq hdP hc x ρP hρP y.2,
    qCoarseK_anc_read geo cs SD KD hk1 hm hq (desc_of_parts hc hdP) x ρC hρC y.2]

open Classical in
/-- **(b) for the top step**: the Gaussian product of the step kernel of `Z` itself (scale `m' + 1`),
with the output field `ψ_{m'+1}(y)` the output `o`. -/
theorem gaussProd_top_read {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A) :
    gaussProd N (H.localHistory M K (m' + 1) Z) m' cs o
        (newRestrict (H.localHistory M K (m' + 1) Z)
          (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x) =
      ∏ y : ↥(gaussBlocks (H.localHistory M K (m' + 1) Z) m'), cs.z (m' + 1) ^ N *
        gaussDens (cs.beta m' * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
          (cs.z (m' + 1) • outField N o y.1 - ((S.L : ℝ) ^ S.d)⁻¹ •
            ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K m' =>
              blockMap S.L (M * n K * S.L ^ (K - (m' + 1))) y' = y.1), subVarField N x m' y') := by
  unfold gaussProd
  refine Finset.prod_congr (by ext; simp) fun y _ => ?_
  have := qCoarseK_anc_read geo cs SD KD (hH := hH) (lab := lab) hk1 hm hq (Desc.refl Z) x x
    (fun p => rfl) y.2
  rw [gaussT_eq_gaussDens, this]

end Read

end Balaban.LargeField
