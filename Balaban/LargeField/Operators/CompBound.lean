module

public import Balaban.LargeField.Operators.LocOp
public import Balaban.LargeField.Operators.KerBound
public import Balaban.LargeField.Operators.PiTools
public import Balaban.LargeField.Operators.GaussChange

/-!
# Composition of the bounds (1.26) (Part II, Lemma II.5.13, version 1.2; block K3)

**The bound (1.26) for a package.**  `PkgBound a k P κ` is the bound (1.26) of Definition II.5.2 for
the operator package `P` (`OpPkg`) of a localized history `a` at scale `k`: the integral of
`K e^{Re b}` over the output variables `ψ_k` on `T^{(k)} ∩ Z` (`ZBlk`, the blocks of `Z_k`) and
the internal variables is at most `e^{-κ}`, **for every value of the parameters**, the outputs on
`V ∖ Z` (`OutPar`), every `h` and every `‖g‖_{ℓ¹} < 1`.  The statement integrates only the
outputs on `T^{(k)} ∩ Z`, as in the source; the outputs on `V ∖ Z` are parameters, exactly as in
`GaussStepSpec` (the `par` of the majorants).    The case `F ≡ 1` is
equivalent to the general case by the support property `OpPkg.vanish`.

**Lemma II.5.13.**  `preOp_pkgBound`: if the operators of the old parts satisfy (1.26) with the
exponents `κ_k(Y)` and the step data satisfy (S1)-(S2) in the form of `StepData.gauss`
(Gaussian structure with witness functions `F^w`, Gaussian measures `m^w` = `mWit`, majorants
`S^w` of the new′ variables uniform in the old ones), then the pre-operator `preOp` satisfies (1.26)
with exponent `κ^{(k)}(Z') + ∑_Y κ_k(Y)`.

The proof follows the order of integration of the source (audit P2-06): (1) the Gaussian variables
`ψ_{k+1}` on `Ω^c_{k+1} ∩ Z'` are integrated first (`lintegral_out_split`: the change of variables
`u = z_{k+1} ψ_{k+1} - Qψ_k` gives the number `m^w`, whatever the other variables are);
(2) the weight of the step kernel is bounded by the majorants `S^w` (`absW_step_le`); (3) for fixed
new′ variables the ancestors act on disjoint sets of old variables (`ancMap`, a bijection of
`Σ_Y (outputs of Y ⊕ internal variables of Y)` onto the variables of `Z'` that are not new′;
`measurePreserving_anc`), the margins `V_Y ∖ Y` of the outputs of `Y` being new′ variables or
parameters (`margin_not_ZBlk`, by the disjointness of the `V_Y`), so that the bound (1.26) for
one ancestor at a time applies (`lintegral_anc_le`); (4) the new′ variables are integrated against
the majorants (`term_le`, `preOp_pkgBound`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory ENNReal

section Bound

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- The bound (1.26) for the package of an operator. -/
abbrev PkgBound (a : LocalHistory S n M K) (k : ℕ) (P : OpPkg N R a k) (κ : ℝ) : Prop :=
  KerBound a k P.T κ

/-! ### Blocks, cubes and the components of the lineage -/

section Geometry

variable {H : RegionHistory S n R k0 K}

theorem blockCube_eq_cubeMap (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {j : ℕ} (hjK : j ≤ K)
    {y : BlockAt S n M K j} {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : Multiscale.jBlock S.d S.L (M * n K) K j x = y) :
    blockCube S n M K j y = cubeMap n S.L M K j x := by
  rw [← hx]; exact cubeMap_jBlock hnn hjK x

/-- A scale-`j` block lies in the fine set of a set of cubes of the next scale iff its cube's
coarsening does. -/
theorem blockSub_fineSet_succ_iff (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {j : ℕ} (hjK : j + 1 ≤ K)
    (A : Set (Torus S.d (n (j + 1)))) (y : BlockAt S n M K j) :
    BlockSub (S := S) (n := n) (M := M) (K := K) j y (fineSet (S := S) (n := n) M K (j + 1) A) ↔
      blockMap S.L (n (j + 1)) (blockCube S n M K j y) ∈ A := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := exists_site_in_block (S := S) (n := n) (M := M) (by omega) y
    have h1 := h x hx
    have h2 : cubeMap n S.L M K (j + 1) x ∈ A := h1
    rwa [← cubeMap_succ hnn hjK x, ← blockCube_eq_cubeMap hnn (by omega) hx] at h2
  · intro h x hx
    show cubeMap n S.L M K (j + 1) x ∈ A
    rwa [← cubeMap_succ hnn hjK x, ← blockCube_eq_cubeMap hnn (by omega) hx]

theorem mem_lin_succ_iff {k : ℕ} {Z' : H.Comp (k + 1)} {c : Torus S.d (n k)} :
    c ∈ H.lin k (k + 1) Z' ↔ ∃ Y ∈ H.parts k Z', c ∈ Y.1 := by
  rw [mem_lin]
  constructor
  · rintro ⟨Y, hd, hc⟩
    obtain ⟨c', hc', hd'⟩ := (desc_succ_iff le_rfl).mp hd
    have : c' = Y := hd'.unique (Desc.refl Y) |>.symm ▸ rfl
    exact ⟨Y, this ▸ hc', hc⟩
  · rintro ⟨Y, hY, hc⟩
    exact ⟨Y, (desc_succ_iff le_rfl).mpr ⟨Y, hY, Desc.refl Y⟩, hc⟩


theorem ZBlk_self_iff {k : ℕ} (hkK : k ≤ K) (Y : H.Comp k) (y : BlockAt S n M K k) :
    ZBlk (H.localHistory M K k Y) k y ↔ blockCube S n M K k y ∈ (Y.1 : Set (Torus S.d (n k))) := by
  have hnn := H.F.hnn
  unfold ZBlk
  show BlockSub (S := S) (n := n) (M := M) (K := K) k y
    (fineSet (S := S) (n := n) M K k ((H.locRH k Y).step k).Z ∩
      fineSet (S := S) (n := n) M K k (Y.1 : Set (Torus S.d (n k)))) ↔ _
  rw [locRH_Z Y le_rfl (by omega), lin_self, blockSub_inter, blockSub_fineSet_iff hnn hkK]
  simp

theorem ZBlk_pre_iff {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) (y : BlockAt S n M K k) :
    ZBlk (H.localHistory M K (k + 1) Z') k y ↔
      ∃ Y ∈ H.parts k Z', blockCube S n M K k y ∈ (Y.1 : Set (Torus S.d (n k))) := by
  have hnn := H.F.hnn
  have hkK : k ≤ K := by omega
  unfold ZBlk
  show BlockSub (S := S) (n := n) (M := M) (K := K) k y
    (fineSet (S := S) (n := n) M K k ((H.locRH (k + 1) Z').step k).Z ∩
      fineSet (S := S) (n := n) M K (k + 1) (Z'.1 : Set (Torus S.d (n (k + 1))))) ↔ _
  rw [locRH_Z Z' (Nat.le_succ k) hkK, blockSub_inter, blockSub_fineSet_iff hnn hkK,
    blockSub_fineSet_succ_iff hnn hK]
  constructor
  · rintro ⟨h1, -⟩
    obtain ⟨Y, hY, hc⟩ := mem_lin_succ_iff.mp (Finset.mem_coe.mp h1)
    exact ⟨Y, hY, hc⟩
  · rintro ⟨Y, hY, hc⟩
    refine ⟨Finset.mem_coe.mpr (mem_lin_succ_iff.mpr ⟨Y, hY, hc⟩), ?_⟩
    obtain ⟨hrem, hs⟩ := (H.mem_parts k Y Z').mp hY
    exact hs ⟨_, hc, rfl⟩


theorem ZBlk_mem_Vblk {k : ℕ} (hkK : k ≤ K) (Z : H.Comp k) (y : BlockAt S n M K k)
    (hy : ZBlk (H.localHistory M K k Z) k y) : y ∈ Vblk R (H.localHistory M K k Z) k := by
  have hc := (ZBlk_self_iff hkK Z y).mp hy
  have h1 : blockCube S n M K k y ∈ Zcubes (H.localHistory M K k Z) k := Zcubes_loc_top (by omega) Z hc
  exact subset_nbhd 1 _ (subset_nbhd _ _ h1)

/-- The old output blocks are large-field variables of scale `k` of the new component. -/
theorem outBlock_large {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) {Y : H.Comp k}
    (hY : Y ∈ H.parts k Z') (y : BlockAt S n M K k)
    (hy : ZBlk (H.localHistory M K k Y) k y) :
    BlockSub (S := S) (n := n) (M := M) (K := K) k y
      (varSet (H.localHistory M K (k + 1) Z') k .large) := by
  have hnn := H.F.hnn
  have hkK : k ≤ K := by omega
  have hL : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne _)
  have hc : blockCube S n M K k y ∈ (Y.1 : Set (Torus S.d (n k))) := (ZBlk_self_iff hkK Y y).mp hy
  obtain ⟨hrem, hs⟩ := (H.mem_parts k Y Z').mp hY
  have hcZ' : blockMap S.L (n (k + 1)) (blockCube S n M K k y) ∈
      (Z'.1 : Set (Torus S.d (n (k + 1)))) := by
    exact hs ⟨_, hc, rfl⟩
  intro x hx
  have hxc : cubeMap n S.L M K (k + 1) x = blockMap S.L (n (k + 1)) (blockCube S n M K k y) := by
    rw [← cubeMap_succ hnn hK x, ← blockCube_eq_cubeMap hnn hkK hx]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show cubeMap n S.L M K (k + 1) x ∈ ((H.locRH (k + 1) Z').step (k + 1)).Z
    rw [locRH_Z Z' le_rfl (by omega), lin_self, hxc]; exact hcZ'
  · show cubeMap n S.L M K (k + 1) x ∈ (Z'.1 : Set (Torus S.d (n (k + 1))))
    rw [hxc]; exact hcZ'
  · rintro ⟨h1, -⟩
    have h1' : blockMap S.L (n (k + 1)) (blockCube S n M K k y) ∈
        ((H.locRH (k + 1) Z').step k).Omega := by
      have : cubeMap n S.L M K (k + 1) x ∈ ((H.locRH (k + 1) Z').step k).Omega := h1
      rwa [hxc] at this
    have hz : blockCube S n M K k y ∈ ((H.locRH (k + 1) Z').step k).Z := by
      rw [locRH_Z Z' (Nat.le_succ k) hkK]
      exact Finset.mem_coe.mpr (mem_lin_succ_iff.mpr ⟨Y, hY, hc⟩)
    exact ((H.locRH (k + 1) Z').step k).not_mem_Z_of_mem_Omega hL (hnn k (by omega)) h1' hz


/-- Sites of a block lie in `Z_k` of the localization of `Z'` according to the block only. -/
theorem site_mem_Z_iff {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) {y : BlockAt S n M K k}
    {x : Torus S.d (M * n K * S.L ^ K)} (hx : Multiscale.jBlock S.d S.L (M * n K) K k x = y) :
    x ∈ (H.localHistory M K (k + 1) Z').Z k ↔ ZBlk (H.localHistory M K (k + 1) Z') k y := by
  have hnn := H.F.hnn
  have hkK : k ≤ K := by omega
  rw [ZBlk_pre_iff hK Z' y]
  have hc := blockCube_eq_cubeMap hnn hkK hx
  have hc1 : cubeMap n S.L M K (k + 1) x = blockMap S.L (n (k + 1)) (cubeMap n S.L M K k x) :=
    (cubeMap_succ hnn hK x).symm
  show (cubeMap n S.L M K k x ∈ ((H.locRH (k + 1) Z').step k).Z ∧
      cubeMap n S.L M K (k + 1) x ∈ (Z'.1 : Set (Torus S.d (n (k + 1))))) ↔ _
  rw [← hc, locRH_Z Z' (Nat.le_succ k) hkK, hc1, ← hc]
  constructor
  · rintro ⟨h1, -⟩
    exact mem_lin_succ_iff.mp (Finset.mem_coe.mp h1)
  · rintro ⟨Y, hY, hc'⟩
    refine ⟨Finset.mem_coe.mpr (mem_lin_succ_iff.mpr ⟨Y, hY, hc'⟩), ?_⟩
    obtain ⟨hrem, hs⟩ := (H.mem_parts k Y Z').mp hY
    exact hs ⟨_, hc', rfl⟩

theorem ZBlk_of_not_blockSub_compl {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    {y : BlockAt S n M K k}
    (h : ¬ BlockSub (S := S) (n := n) (M := M) (K := K) k y
      ((H.localHistory M K (k + 1) Z').Z k)ᶜ) :
    ZBlk (H.localHistory M K (k + 1) Z') k y := by
  have hkK : k ≤ K := by omega
  by_contra hz
  apply h
  intro x hx hxm
  exact hz ((site_mem_Z_iff hK Z' hx).mp hxm)

theorem not_blockSub_compl_of_ZBlk {k : ℕ} (hkK : k ≤ K) {a : LocalHistory S n M K}
    {y : BlockAt S n M K k} (hz : ZBlk a k y) :
    ¬ BlockSub (S := S) (n := n) (M := M) (K := K) k y (a.Z k)ᶜ := by
  intro h
  obtain ⟨x, hx⟩ := exists_site_in_block (S := S) (n := n) (M := M) hkK y
  exact h x hx (hz x hx)

end Geometry


/-! ### The index set of the ancestors' variables inside those of the component -/

section Index

variable {H : RegionHistory S n R k0 K} {k : ℕ}

/-- The index set of the integrated output variables `ψ_k` on `T^{(k)} ∩ Y` of an old part. -/
abbrev OutIdx (R : ℕ → ℝ) (Y : H.Comp k) : Type :=
  {y : BlockAt S n M K k // y ∈ Vblk R (H.localHistory M K k Y) k ∧
    ZBlk (H.localHistory M K k Y) k y}

/-- The large-field variable of scale `k` of the new component at an output block of an old part. -/
noncomputable def oldVar (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) {Y : H.Comp k} (hY : Y ∈ H.parts k Z')
    (y : OutIdx (K := K) (M := M) R Y) : InternalVars (H.localHistory M K (k + 1) Z') (k + 1) :=
  mkVar _ (k + 1) k .large y.1 (Nat.lt_succ_self k) (outBlock_large hK Z' hY y.1 y.2.2)

theorem oldVar_val (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) {Y : H.Comp k} (hY : Y ∈ H.parts k Z')
    (y : OutIdx (K := K) (M := M) R Y) : (oldVar hK Z' hY y).1.1.val = k := rfl

theorem oldVar_not_newPrime (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) {Y : H.Comp k}
    (hY : Y ∈ H.parts k Z') (y : OutIdx (K := K) (M := M) R Y) :
    oldVar hK Z' hY y ∉ newPrimeVars (H.localHistory M K (k + 1) Z') k := by
  rintro ⟨-, h | h⟩
  · exact VarKind.noConfusion h
  · exact not_blockSub_compl_of_ZBlk (by omega)
      ((ZBlk_pre_iff hK Z' y.1).mpr ⟨Y, hY, (ZBlk_self_iff (by omega) Y y.1).mp y.2.2⟩) h


variable {N : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
  (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)

/-- The index set of the variables of the ancestors in `preVars`: output blocks and internal
variables of each old part. -/
abbrev AncIdx : Type :=
  Σ Y : ↥(H.parts k Z'), OutIdx (K := K) (M := M) R Y.1 ⊕ ↥(sub Y.1 Y.2).A

/-- The new′ variables, as a predicate on the index set of `preVars`. -/
def IsNP (p : ↥(preVars hK Z' sub)) : Prop :=
  p.1 ∈ newPrimeVars (H.localHistory M K (k + 1) Z') k

theorem ancInc_not_newVars (Y : H.Comp k) (hY : Y ∈ H.parts k Z')
    (q : InternalVars (H.localHistory M K k Y) k) :
    ancInc hK hY q ∉ newVars (H.localHistory M K (k + 1) Z') k := by
  intro h
  have h1 : (ancInc hK hY q).1.1.val = k := h
  have h2 : (ancInc hK hY q).1.1.val = q.1.1.val := rfl
  have := q.1.1.2
  omega

/-- The map from the ancestors' index set to the variables of the component. -/
noncomputable def ancMap : AncIdx (K := K) (M := M) Z' sub →
    {p : ↥(preVars hK Z' sub) // ¬ IsNP hK Z' sub p}
  | ⟨Y, Sum.inl y⟩ => ⟨⟨oldVar hK Z' Y.2 y, preVars_new hK Z' sub (oldVar_val hK Z' Y.2 y)⟩,
      oldVar_not_newPrime hK Z' Y.2 y⟩
  | ⟨Y, Sum.inr q⟩ => ⟨⟨ancInc hK Y.2 q.1, preVars_anc hK Z' sub Y.1 Y.2 q.1 q.2⟩,
      fun h => ancInc_not_newVars hK Z' Y.1 Y.2 q.1 (newPrimeVars_sub _ _ h)⟩


theorem one_le_of_comp (Y : H.Comp k) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0; exact (H.F.isEmpty_comp_zero.false Y).elim
  · exact h0

theorem comp_eq_of_cube {Y Y' : H.Comp k} {c : Torus S.d (n k)} (h : c ∈ Y.1) (h' : c ∈ Y'.1) :
    Y = Y' := Subtype.ext (comp_eq_of_mem Y.2 Y'.2 h h')

theorem oldVar_inj {Y Y' : H.Comp k} (hY : Y ∈ H.parts k Z') (hY' : Y' ∈ H.parts k Z')
    (y : OutIdx (K := K) (M := M) R Y) (y' : OutIdx (K := K) (M := M) R Y')
    (h : oldVar hK Z' hY y = oldVar hK Z' hY' y') : y.1 = y'.1 := by
  have h1 := congrArg Subtype.val h
  simp only [oldVar, mkVar, Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq] at h1
  exact h1

theorem ancMap_injective : Function.Injective (ancMap (K := K) (M := M) hK Z' sub) := by
  have hnn := H.F.hnn
  rintro ⟨Y, s⟩ ⟨Y', s'⟩ h
  have h1 := congrArg (fun p => p.1.1) h
  simp only [ancMap] at h1
  rcases s with y | q <;> rcases s' with y' | q'
  · -- both output blocks
    have hy := oldVar_inj hK Z' Y.2 Y'.2 y y' h1
    have hYY : Y = Y' := by
      refine Subtype.ext (comp_eq_of_cube (c := blockCube S n M K k y.1) ?_ ?_)
      · exact (ZBlk_self_iff (by omega) Y.1 y.1).mp y.2.2
      · rw [hy]; exact (ZBlk_self_iff (by omega) Y'.1 y'.1).mp y'.2.2
    subst hYY
    have : y = y' := Subtype.ext hy
    subst this
    rfl
  · exfalso
    have h2 := congrArg (fun p : InternalVars (H.localHistory M K (k + 1) Z') (k + 1) =>
      p.1.1.val) h1
    have h3 := q'.1.1.1.2
    simp only [oldVar_val, ancInc] at h2
    simp only [Fin.val_castSucc] at h2
    omega
  · exfalso
    have h2 := congrArg (fun p : InternalVars (H.localHistory M K (k + 1) Z') (k + 1) =>
      p.1.1.val) h1
    have h3 := q.1.1.1.2
    simp only [oldVar_val, ancInc] at h2
    simp only [Fin.val_castSucc] at h2
    omega
  · have hq := congrArg Subtype.val h1
    simp only [ancInc, Sigma.mk.injEq] at hq
    rcases q with ⟨⟨⟨j, κ, b⟩, hb⟩, hqA⟩
    rcases q' with ⟨⟨⟨j', κ', b'⟩, hb'⟩, hqA'⟩
    obtain ⟨hj, hh⟩ := hq
    have hj' : j = j' := Fin.castSucc_injective _ hj
    subst hj'
    have hh' : (κ, b) = (κ', b') := eq_of_heq hh
    simp only [Prod.mk.injEq] at hh'
    obtain ⟨rfl, rfl⟩ := hh'
    have hYY : Y = Y' := by
      by_contra hne
      have hne' : Y.1 ≠ Y'.1 := fun h => hne (Subtype.ext h)
      exact (locOp_factor (H := H) (one_le_of_comp Y.1) (by omega) hne').2 j.val
        (by have := j.2; omega) b κ κ ⟨hb, hb'⟩
    subst hYY
    rfl


theorem ancMap_surjective : Function.Surjective (ancMap (K := K) (M := M) hK Z' sub) := by
  rintro ⟨⟨p, hp⟩, hnp⟩
  rcases hp with hnew | ⟨Y, hY, q, hqA, rfl⟩
  · obtain ⟨⟨⟨j, hjlt⟩, κ, b⟩, hb⟩ := p
    have hj : j = k := hnew
    subst hj
    cases κ with
    | fluct => exact absurd ⟨hnew, Or.inl rfl⟩ hnp
    | large =>
      have hnb : ¬ BlockSub (S := S) (n := n) (M := M) (K := K) j b
          ((H.localHistory M K (j + 1) Z').Z j)ᶜ := fun h => hnp ⟨hnew, Or.inr h⟩
      have hz := ZBlk_of_not_blockSub_compl hK Z' hnb
      obtain ⟨Y, hY, hc⟩ := (ZBlk_pre_iff hK Z' b).mp hz
      have hzY : ZBlk (H.localHistory M K j Y) j b := (ZBlk_self_iff (by omega) Y b).mpr hc
      exact ⟨⟨⟨Y, hY⟩, Sum.inl ⟨b, ZBlk_mem_Vblk (by omega) Y b hzY, hzY⟩⟩, rfl⟩
  · exact ⟨⟨⟨Y, hY⟩, Sum.inr ⟨q, hqA⟩⟩, rfl⟩

theorem ancMap_bijective : Function.Bijective (ancMap (K := K) (M := M) hK Z' sub) :=
  ⟨ancMap_injective hK Z' sub, ancMap_surjective hK Z' sub⟩


/-! ### The regrouping of the variables of the ancestors -/

/-- The coordinate types of the regrouped configuration: Lebesgue variables for the output blocks,
the types of the variables for the internal ones. -/
def WT : AncIdx (K := K) (M := M) (R := R) Z' sub → Type
  | ⟨_, Sum.inl _⟩ => EuclideanSpace ℝ (Fin N)
  | ⟨_, Sum.inr q⟩ => VarVal N q.1.isSpin

noncomputable instance (s : AncIdx (K := K) (M := M) (R := R) Z' sub) :
    MeasurableSpace (WT Z' sub s) :=
  match s with
  | ⟨_, Sum.inl _⟩ => inferInstanceAs (MeasurableSpace (EuclideanSpace ℝ (Fin N)))
  | ⟨_, Sum.inr q⟩ => inferInstanceAs (MeasurableSpace (VarVal N q.1.isSpin))

/-- The reference measures of the regrouped coordinates. -/
noncomputable def νT (s : AncIdx (K := K) (M := M) (R := R) Z' sub) : Measure (WT Z' sub s) :=
  match s with
  | ⟨_, Sum.inl _⟩ => (volume : Measure (EuclideanSpace ℝ (Fin N)))
  | ⟨_, Sum.inr q⟩ => varMeasure N q.1.isSpin

instance (s : AncIdx (K := K) (M := M) (R := R) Z' sub) : SigmaFinite (νT Z' sub s) :=
  match s with
  | ⟨_, Sum.inl _⟩ => inferInstanceAs (SigmaFinite (volume : Measure (EuclideanSpace ℝ (Fin N))))
  | ⟨_, Sum.inr q⟩ => inferInstanceAs (SigmaFinite (varMeasure N q.1.isSpin))


theorem measurePreserving_toEuc_false (b : Bool) (hb : b = false) :
    MeasurePreserving (@VarVal.toEuc N b) (varMeasure N b)
      (volume : Measure (EuclideanSpace ℝ (Fin N))) := by
  subst hb
  exact MeasurePreserving.id _

theorem isSpin_oldVar (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) {Y : H.Comp k}
    (hY : Y ∈ H.parts k Z') (y : OutIdx (K := K) (M := M) R Y) :
    (oldVar hK Z' hY y).isSpin = false := by
  have h1 := one_le_of_comp Y
  unfold InternalVars.isSpin
  have h2 : ¬ ((oldVar hK Z' hY y).1.1.val = 0 ∧ (oldVar hK Z' hY y).1.2.1 = VarKind.large) := by
    rintro ⟨h3, -⟩
    have h4 := oldVar_val hK Z' hY y
    omega
  exact decide_eq_false h2

noncomputable def ancG : AncIdx (K := K) (M := M) (R := R) Z' sub ≃
    {p : ↥(preVars hK Z' sub) // ¬ IsNP hK Z' sub p} :=
  Equiv.ofBijective (ancMap hK Z' sub) (ancMap_bijective hK Z' sub)

/-- The coordinate maps from the variables of the component to the regrouped coordinates. -/
noncomputable def ancPhi : ∀ s : AncIdx (K := K) (M := M) (R := R) Z' sub,
    VarVal N (ancG hK Z' sub s).1.1.isSpin → WT Z' sub s
  | ⟨_, Sum.inl _⟩ => fun v => VarVal.toEuc v
  | ⟨_, Sum.inr _⟩ => fun v => v

theorem measurePreserving_ancPhi (s : AncIdx (K := K) (M := M) (R := R) Z' sub) :
    MeasurePreserving (ancPhi hK Z' sub s) (varMeasure N (ancG hK Z' sub s).1.1.isSpin)
      (νT Z' sub s) := by
  rcases s with ⟨Y, y | q⟩
  · exact measurePreserving_toEuc_false _ (isSpin_oldVar hK Z' Y.2 y)
  · exact MeasurePreserving.id _



open Classical in
theorem measurePreserving_anc :
    MeasurePreserving (PiTools.decompMap (W := WT Z' sub) (ancG hK Z' sub) (ancPhi hK Z' sub))
      (Measure.pi fun i : {p : ↥(preVars hK Z' sub) // ¬ IsNP hK Z' sub p} =>
        varMeasure N i.1.1.isSpin)
      (Measure.pi fun Y : ↥(H.parts k Z') =>
        (Measure.pi fun _ : OutIdx (K := K) (M := M) R Y.1 =>
          (volume : Measure (EuclideanSpace ℝ (Fin N)))).prod
        (Measure.pi fun q : ↥(sub Y.1 Y.2).A => varMeasure N q.1.isSpin)) :=
  by
  have h := PiTools.measurePreserving_decompMap (ancG hK Z' sub)
    (fun i : {p : ↥(preVars hK Z' sub) // ¬ IsNP hK Z' sub p} => varMeasure N i.1.1.isSpin)
    (νT Z' sub) (ancPhi hK Z' sub) (measurePreserving_ancPhi hK Z' sub)
  convert h using 3
  rfl


/-! ### Reading the variables of the component from the split configuration -/

open Classical in
/-- The combination of a configuration of the new′ variables and a configuration of the others. -/
noncomputable def combCfg
    (z : ∀ p : {p : ↥(preVars hK Z' sub) // IsNP hK Z' sub p}, VarVal N p.1.1.isSpin)
    (w : ∀ p : {p : ↥(preVars hK Z' sub) // ¬ IsNP hK Z' sub p}, VarVal N p.1.1.isSpin) :
    SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun p : ↥(preVars hK Z' sub) => VarVal N p.1.isSpin)
    (IsNP hK Z' sub)).symm (z, w)

open Classical in
theorem combCfg_pos (z : ∀ p : {p : ↥(preVars hK Z' sub) // IsNP hK Z' sub p}, VarVal N p.1.1.isSpin)
    (w : ∀ p : {p : ↥(preVars hK Z' sub) // ¬ IsNP hK Z' sub p}, VarVal N p.1.1.isSpin)
    (p : ↥(preVars hK Z' sub)) (hp : IsNP hK Z' sub p) :
    combCfg hK Z' sub z w p = z ⟨p, hp⟩ := by
  unfold combCfg
  simp [MeasurableEquiv.piEquivPiSubtypeProd, hp]

open Classical in
theorem combCfg_neg (z : ∀ p : {p : ↥(preVars hK Z' sub) // IsNP hK Z' sub p}, VarVal N p.1.1.isSpin)
    (w : ∀ p : {p : ↥(preVars hK Z' sub) // ¬ IsNP hK Z' sub p}, VarVal N p.1.1.isSpin)
    (p : ↥(preVars hK Z' sub)) (hp : ¬ IsNP hK Z' sub p) :
    combCfg hK Z' sub z w p = w ⟨p, hp⟩ := by
  unfold combCfg
  simp [MeasurableEquiv.piEquivPiSubtypeProd, hp]


section Reading

include hK

open Classical in
/-- The value of the new′ variable `ψ_k(b)` (zero if `b` is not such a variable). -/
noncomputable def readNP
    (z : ∀ p : {p : ↥(preVars hK Z' sub) // IsNP hK Z' sub p}, VarVal N p.1.1.isSpin)
    (b : BlockAt S n M K k) : EuclideanSpace ℝ (Fin N) :=
  if h : ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) k b
      (varSet (H.localHistory M K (k + 1) Z') k .large),
    ∃ hP : mkVar (H.localHistory M K (k + 1) Z') (k + 1) k .large b (Nat.lt_succ_self k) hb ∈
      preVars hK Z' sub, IsNP hK Z' sub ⟨_, hP⟩ then
    VarVal.toEuc (z ⟨⟨_, h.2.1⟩, h.2.2⟩)
  else 0

/-- A block of the margin of an old part is not an output block of another old part. -/
theorem margin_not_ZBlk (Y : H.Comp k) (hY : Y ∈ H.parts k Z') (b : BlockAt S n M K k)
    (hV : b ∈ Vblk R (H.localHistory M K k Y) k) (hnz : ¬ ZBlk (H.localHistory M K k Y) k b) :
    ¬ ZBlk (H.localHistory M K (k + 1) Z') k b := by
  intro hz
  obtain ⟨Y', hY', hc⟩ := (ZBlk_pre_iff hK Z' b).mp hz
  by_cases hYY : Y' = Y
  · subst hYY
    exact hnz ((ZBlk_self_iff (by omega) Y' b).mpr hc)
  · have hz' : ZBlk (H.localHistory M K k Y') k b := (ZBlk_self_iff (by omega) Y' b).mpr hc
    have hV' := ZBlk_mem_Vblk (by omega) Y' b hz'
    exact (Set.disjoint_left.mp (locOp_factor (H := H) (one_le_of_comp Y) (by omega) hYY).1) hV' hV

open Classical in
theorem subVarField_comb
    (z : ∀ p : {p : ↥(preVars hK Z' sub) // IsNP hK Z' sub p}, VarVal N p.1.1.isSpin)
    (w : ∀ p : {p : ↥(preVars hK Z' sub) // ¬ IsNP hK Z' sub p}, VarVal N p.1.1.isSpin)
    (b : BlockAt S n M K k) (hnz : ¬ ZBlk (H.localHistory M K (k + 1) Z') k b) :
    subVarField N (combCfg hK Z' sub z w) k b = readNP hK Z' sub z b := by
  unfold subVarField readNP
  by_cases h : ∃ hj : k < k + 1, ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) k b
      (varSet (H.localHistory M K (k + 1) Z') k .large),
      mkVar (H.localHistory M K (k + 1) Z') (k + 1) k .large b hj hb ∈ preVars hK Z' sub
  · obtain ⟨hj, hb, hP⟩ := h
    by_cases hnp : IsNP hK Z' sub ⟨_, hP⟩
    · have h2 : ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) k b
          (varSet (H.localHistory M K (k + 1) Z') k .large),
          ∃ hP : mkVar (H.localHistory M K (k + 1) Z') (k + 1) k .large b (Nat.lt_succ_self k) hb
            ∈ preVars hK Z' sub, IsNP hK Z' sub ⟨_, hP⟩ := ⟨hb, hP, hnp⟩
      have h1 : ∃ hj : k < k + 1, ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) k b
          (varSet (H.localHistory M K (k + 1) Z') k .large),
          mkVar (H.localHistory M K (k + 1) Z') (k + 1) k .large b hj hb ∈ preVars hK Z' sub :=
        ⟨hj, hb, hP⟩
      simp only [h1, h2, ↓reduceDIte]
      congr 1
      exact combCfg_pos hK Z' sub z w _ hnp
    · exfalso
      obtain ⟨s, hs⟩ := ancMap_surjective hK Z' sub ⟨⟨_, hP⟩, hnp⟩
      rcases s with ⟨Y', y | q⟩
      · have h1 := congrArg (fun r => r.1.1) hs
        simp only [ancMap] at h1
        have h2 := congrArg Subtype.val h1
        simp only [oldVar, mkVar, Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq] at h2
        exact hnz ((ZBlk_pre_iff hK Z' b).mpr ⟨Y'.1, Y'.2, by
          rw [← h2.2.2]; exact (ZBlk_self_iff (by omega) Y'.1 y.1).mp y.2.2⟩)
      · have h1 := congrArg (fun r => r.1.1.1.1.val) hs
        simp only [ancMap, ancInc, Fin.val_castSucc, mkVar] at h1
        have := q.1.1.1.2
        omega
  · have hn2 : ¬ ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) k b
        (varSet (H.localHistory M K (k + 1) Z') k .large),
        ∃ hP : mkVar (H.localHistory M K (k + 1) Z') (k + 1) k .large b (Nat.lt_succ_self k) hb
          ∈ preVars hK Z' sub, IsNP hK Z' sub ⟨_, hP⟩ := by
      rintro ⟨hb, hP, -⟩
      exact h ⟨Nat.lt_succ_self k, hb, hP⟩
    simp only [h, hn2, ↓reduceDIte]


/-- The parameters (outputs of an old part outside its own region) read from the new′ variables. -/
noncomputable def parOf
    (z : ∀ p : {p : ↥(preVars hK Z' sub) // IsNP hK Z' sub p}, VarVal N p.1.1.isSpin)
    (Y : ↥(H.parts k Z')) : OutPar N R (H.localHistory M K k Y.1) k :=
  fun y => readNP hK Z' sub z y.1

open Classical in
theorem ancRestrict_comb
    (z : ∀ p : {p : ↥(preVars hK Z' sub) // IsNP hK Z' sub p}, VarVal N p.1.1.isSpin)
    (w : ∀ p : {p : ↥(preVars hK Z' sub) // ¬ IsNP hK Z' sub p}, VarVal N p.1.1.isSpin)
    (Y : ↥(H.parts k Z')) :
    ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) (combCfg hK Z' sub z w) =
      (PiTools.decompMap (W := WT Z' sub) (ancG hK Z' sub) (ancPhi hK Z' sub) w Y).2 := by
  funext q
  exact combCfg_neg hK Z' sub z w _ _

open Classical in
theorem ancOut_comb
    (z : ∀ p : {p : ↥(preVars hK Z' sub) // IsNP hK Z' sub p}, VarVal N p.1.1.isSpin)
    (w : ∀ p : {p : ↥(preVars hK Z' sub) // ¬ IsNP hK Z' sub p}, VarVal N p.1.1.isSpin)
    (Y : ↥(H.parts k Z')) :
    ancOut (N := N) (R := R) Y.1 Z' (combCfg hK Z' sub z w) =
      mergeOut (H.localHistory M K k Y.1) k
        (PiTools.decompMap (W := WT Z' sub) (ancG hK Z' sub) (ancPhi hK Z' sub) w Y).1
        (parOf hK Z' sub z Y) := by
  funext y
  unfold ancOut mergeOut parOf
  by_cases h : ZBlk (H.localHistory M K k Y.1) k y.1
  · simp only [h, ↓reduceDIte]
    have h1 : ∃ hj : k < k + 1, ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) k y.1
        (varSet (H.localHistory M K (k + 1) Z') k .large),
        mkVar (H.localHistory M K (k + 1) Z') (k + 1) k .large y.1 hj hb ∈ preVars hK Z' sub :=
      ⟨Nat.lt_succ_self k, outBlock_large hK Z' Y.2 y.1 h,
        preVars_new hK Z' sub (oldVar_val hK Z' Y.2 ⟨y.1, y.2, h⟩)⟩
    unfold subVarField
    simp only [h1, ↓reduceDIte]
    exact congrArg VarVal.toEuc (combCfg_neg hK Z' sub z w
      ⟨oldVar hK Z' Y.2 ⟨y.1, y.2, h⟩, preVars_new hK Z' sub (oldVar_val hK Z' Y.2 ⟨y.1, y.2, h⟩)⟩
      (oldVar_not_newPrime hK Z' Y.2 ⟨y.1, y.2, h⟩))
  · simp only [h, ↓reduceDIte]
    exact subVarField_comb hK Z' sub z w y.1 (margin_not_ZBlk hK Z' Y.1 Y.2 y.1 y.2 h)


open Classical in
/-- The reading of the new′ variables as a configuration of `newPrimeVars`. -/
noncomputable def rhoCfg
    (z : ∀ p : {p : ↥(preVars hK Z' sub) // IsNP hK Z' sub p}, VarVal N p.1.1.isSpin) :
    SubCfg N (H.localHistory M K (k + 1) Z') (k + 1)
      (newPrimeVars (H.localHistory M K (k + 1) Z') k) :=
  fun p' => z ⟨⟨p'.1, preVars_new hK Z' sub (newPrimeVars_sub _ _ p'.2)⟩, p'.2⟩

theorem restrict_comb
    (z : ∀ p : {p : ↥(preVars hK Z' sub) // IsNP hK Z' sub p}, VarVal N p.1.1.isSpin)
    (w : ∀ p : {p : ↥(preVars hK Z' sub) // ¬ IsNP hK Z' sub p}, VarVal N p.1.1.isSpin) :
    restrictSub (newPrimeVars_sub (H.localHistory M K (k + 1) Z') k)
      (newRestrict (N := N) (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub)
        (combCfg hK Z' sub z w)) = rhoCfg hK Z' sub z := by
  funext p'
  exact combCfg_pos hK Z' sub z w ⟨p'.1, preVars_new hK Z' sub (newPrimeVars_sub _ _ p'.2)⟩ p'.2


/-- The relabelling of the new′ variables. -/
def npEquiv : ↥(newPrimeVars (H.localHistory M K (k + 1) Z') k) ≃
    {p : ↥(preVars hK Z' sub) // IsNP hK Z' sub p} where
  toFun p' := ⟨⟨p'.1, preVars_new hK Z' sub (newPrimeVars_sub _ _ p'.2)⟩, p'.2⟩
  invFun q := ⟨q.1.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

open Classical in
theorem measurePreserving_rhoCfg :
    MeasurePreserving (rhoCfg hK Z' sub (N := N))
      (Measure.pi fun i : {p : ↥(preVars hK Z' sub) // IsNP hK Z' sub p} =>
        varMeasure N i.1.1.isSpin)
      (subMeasure N (H.localHistory M K (k + 1) Z') (k + 1)
        (newPrimeVars (H.localHistory M K (k + 1) Z') k)) := by
  have h := PiTools.measurePreserving_reindex (npEquiv hK Z' sub)
    (β := fun p' : ↥(newPrimeVars (H.localHistory M K (k + 1) Z') k) => VarVal N p'.1.isSpin)
    (γ := fun i : {p : ↥(preVars hK Z' sub) // IsNP hK Z' sub p} => VarVal N i.1.1.isSpin)
    (fun i => varMeasure N i.1.1.isSpin) (fun p' => varMeasure N p'.1.isSpin)
    (fun _ v => v) (fun _ => MeasurePreserving.id _)
  exact h


open Classical in
theorem inner_le (κ : ↥(H.parts k Z') → ℝ)
    (hanc : ∀ Y : ↥(H.parts k Z'), PkgBound (H.localHistory M K k Y.1) k (sub Y.1 Y.2) (κ Y))
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N))
    (z : ∀ p : {p : ↥(preVars hK Z' sub) // IsNP hK Z' sub p}, VarVal N p.1.1.isSpin) :
    ∫⁻ w, ∏ Y : ↥(H.parts k Z'), (sub Y.1 Y.2).T.absW
        (ancOut Y.1 Z' (combCfg hK Z' sub z w))
        (ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) (combCfg hK Z' sub z w)) hv g
      ∂(Measure.pi fun i : {p : ↥(preVars hK Z' sub) // ¬ IsNP hK Z' sub p} =>
        varMeasure N i.1.1.isSpin) ≤
      ∏ Y : ↥(H.parts k Z'), ENNReal.ofReal (Real.exp (-κ Y)) := by
  set At : ∀ Y : ↥(H.parts k Z'), ((OutIdx (K := K) (M := M) R Y.1 → EuclideanSpace ℝ (Fin N)) ×
      (∀ q : ↥(sub Y.1 Y.2).A, VarVal N q.1.isSpin)) → ℝ≥0∞ := fun Y v =>
    (sub Y.1 Y.2).T.absW (mergeOut (H.localHistory M K k Y.1) k v.1 (parOf hK Z' sub z Y)) v.2 hv g
    with hAt
  have hAtm : ∀ Y, Measurable (At Y) := fun Y =>
    ((sub Y.1 Y.2).T.measurable_absW hv g).comp
      (((measurable_mergeOut (H.localHistory M K k Y.1) k (parOf hK Z' sub z Y)).comp
        measurable_fst).prodMk measurable_snd)
  have e1 : ∀ w, ∏ Y : ↥(H.parts k Z'), (sub Y.1 Y.2).T.absW
        (ancOut Y.1 Z' (combCfg hK Z' sub z w))
        (ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) (combCfg hK Z' sub z w)) hv g =
      ∏ Y, At Y (PiTools.decompMap (W := WT Z' sub) (ancG hK Z' sub) (ancPhi hK Z' sub) w Y) := by
    intro w
    refine Finset.prod_congr rfl fun Y _ => ?_
    rw [ancOut_comb, ancRestrict_comb]
  simp_rw [e1]
  rw [(measurePreserving_anc hK Z' sub).lintegral_comp
    (f := fun v : (∀ Y : ↥(H.parts k Z'), _) => ∏ Y, At Y (v Y))
    (Finset.measurable_prod _ fun Y _ => (hAtm Y).comp (measurable_pi_apply Y))]
  refine le_of_eq_of_le (PiTools.lintegral_fintype_prod_eq_prod _ At hAtm
    (μ := fun Y : ↥(H.parts k Z') =>
      (Measure.pi fun _ : OutIdx (K := K) (M := M) R Y.1 =>
        (volume : Measure (EuclideanSpace ℝ (Fin N)))).prod
      (Measure.pi fun q : ↥(sub Y.1 Y.2).A => varMeasure N q.1.isSpin))) ?_
  refine Finset.prod_le_prod fun Y _ => ?_
  refine (le_of_eq (lintegral_prod (At Y) (hAtm Y).aemeasurable
    (μ := Measure.pi fun _ : OutIdx (K := K) (M := M) R Y.1 =>
        (volume : Measure (EuclideanSpace ℝ (Fin N))))
    (ν := Measure.pi fun q : ↥(sub Y.1 Y.2).A => varMeasure N q.1.isSpin))).trans ?_
  exact hanc Y hv g hg (parOf hK Z' sub z Y)

open Classical in
/-- **Integration of the old variables** (Lemma II.5.13 (3)): for the new′ variables fixed, the
ancestors act on disjoint sets of old variables, so the integral of the product of their weights
is at most `e^{-∑ κ_Y}` by the bound (1.26) for each of them. -/
theorem lintegral_anc_le (κ : ↥(H.parts k Z') → ℝ)
    (hanc : ∀ Y : ↥(H.parts k Z'), PkgBound (H.localHistory M K k Y.1) k (sub Y.1 Y.2) (κ Y))
    (F : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1)
      (newPrimeVars (H.localHistory M K (k + 1) Z') k) → ℝ≥0∞) (hF : Measurable F)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N)) :
    ∫⁻ x, F (restrictSub (newPrimeVars_sub (H.localHistory M K (k + 1) Z') k)
        (newRestrict (N := N) (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x)) *
      ∏ Y : ↥(H.parts k Z'), (sub Y.1 Y.2).T.absW (ancOut Y.1 Z' x)
        (ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) x) hv g
        ∂(subMeasure N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub)) ≤
      (∏ Y : ↥(H.parts k Z'), ENNReal.ofReal (Real.exp (-κ Y))) *
        ∫⁻ x', F x' ∂(subMeasure N (H.localHistory M K (k + 1) Z') (k + 1)
          (newPrimeVars (H.localHistory M K (k + 1) Z') k)) := by
  set Pi : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub) → ℝ≥0∞ :=
    fun x => ∏ Y : ↥(H.parts k Z'), (sub Y.1 Y.2).T.absW (ancOut Y.1 Z' x)
      (ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) x) hv g with hPi
  have hPim : Measurable Pi := Finset.measurable_prod _ fun Y _ =>
    ((sub Y.1 Y.2).T.measurable_absW hv g).comp
      ((measurable_ancOut (R := R) Y.1 Z' _).prodMk
        (measurable_ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2)))
  set Φ : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub) → ℝ≥0∞ :=
    fun x => F (restrictSub (newPrimeVars_sub (H.localHistory M K (k + 1) Z') k)
        (newRestrict (N := N) (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x)) * Pi x
    with hΦ
  have hΦm : Measurable Φ :=
    (hF.comp ((measurable_restrictSub _).comp (measurable_newRestrict _ _))).mul hPim
  have hsplit := PiTools.lintegral_split
    (α := fun p : ↥(preVars hK Z' sub) => VarVal N p.1.isSpin)
    (fun p => varMeasure N p.1.isSpin) (IsNP hK Z' sub) Φ hΦm
  have hcomb : ∀ z, Measurable fun w => combCfg hK Z' sub z w := fun z =>
    (MeasurableEquiv.measurable _).comp measurable_prodMk_left
  refine le_of_eq_of_le hsplit ?_
  calc ∫⁻ z, ∫⁻ w, Φ (combCfg hK Z' sub z w)
        ∂(Measure.pi fun i : {p : ↥(preVars hK Z' sub) // ¬ IsNP hK Z' sub p} =>
          varMeasure N i.1.1.isSpin)
        ∂(Measure.pi fun i : {p : ↥(preVars hK Z' sub) // IsNP hK Z' sub p} =>
          varMeasure N i.1.1.isSpin)
      = ∫⁻ z, F (rhoCfg hK Z' sub z) * ∫⁻ w, Pi (combCfg hK Z' sub z w)
          ∂(Measure.pi fun i : {p : ↥(preVars hK Z' sub) // ¬ IsNP hK Z' sub p} =>
            varMeasure N i.1.1.isSpin)
          ∂(Measure.pi fun i : {p : ↥(preVars hK Z' sub) // IsNP hK Z' sub p} =>
            varMeasure N i.1.1.isSpin) := by
        refine lintegral_congr fun z => ?_
        simp only [hΦ, restrict_comb]
        exact lintegral_const_mul _ (hPim.comp (hcomb z))
    _ ≤ ∫⁻ z, F (rhoCfg hK Z' sub z) * ∏ Y : ↥(H.parts k Z'), ENNReal.ofReal (Real.exp (-κ Y))
          ∂(Measure.pi fun i : {p : ↥(preVars hK Z' sub) // IsNP hK Z' sub p} =>
            varMeasure N i.1.1.isSpin) :=
        lintegral_mono fun z => mul_le_mul_right (inner_le hK Z' sub κ hanc hv g hg z) _
    _ = (∏ Y : ↥(H.parts k Z'), ENNReal.ofReal (Real.exp (-κ Y))) *
          ∫⁻ z, F (rhoCfg hK Z' sub z)
          ∂(Measure.pi fun i : {p : ↥(preVars hK Z' sub) // IsNP hK Z' sub p} =>
            varMeasure N i.1.1.isSpin) := by
        simp_rw [mul_comm _ (∏ Y : ↥(H.parts k Z'), ENNReal.ofReal (Real.exp (-κ Y)))]
        exact lintegral_const_mul _ (hF.comp (measurePreserving_rhoCfg hK Z' sub).measurable)
    _ = _ := by rw [(measurePreserving_rhoCfg hK Z' sub).lintegral_comp hF]

end Reading

end Index

/-! ### The blocks of the new component: Gaussian blocks, new outputs, parameters -/

section TopBlocks

variable {H : RegionHistory S n R k0 K}

/-- A `(k+1)`-block of `Z'` is Gaussian iff its cube is in `Z'` and not in `Ω_{k+1}`. -/
theorem gaussBlocks_iff {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) (y : BlockAt S n M K (k + 1)) :
    y ∈ gaussBlocks (H.localHistory M K (k + 1) Z') k ↔
      blockCube S n M K (k + 1) y ∈ (Z'.1 : Set (Torus S.d (n (k + 1)))) ∧
        blockCube S n M K (k + 1) y ∉ ((H.locRH (k + 1) Z').step k).Omega := by
  have hnn := H.F.hnn
  obtain ⟨x0, hx0⟩ := exists_site_in_block (S := S) (n := n) (M := M) hK y
  have hsite : ∀ x, Multiscale.jBlock S.d S.L (M * n K) K (k + 1) x = y →
      cubeMap n S.L M K (k + 1) x = blockCube S n M K (k + 1) y := fun x hx =>
    (blockCube_eq_cubeMap hnn hK hx).symm
  constructor
  · intro h
    have h1 := h x0 hx0
    obtain ⟨⟨h2, h3⟩, h4⟩ := h1
    refine ⟨?_, fun hc => h4 ⟨?_, ?_⟩⟩
    · have : cubeMap n S.L M K (k + 1) x0 ∈ (Z'.1 : Set (Torus S.d (n (k + 1)))) := h3
      rwa [hsite x0 hx0] at this
    · show cubeMap n S.L M K (k + 1) x0 ∈ ((H.locRH (k + 1) Z').step k).Omega
      rwa [hsite x0 hx0]
    · show cubeMap n S.L M K (k + 1) x0 ∈ (Z'.1 : Set (Torus S.d (n (k + 1))))
      rw [hsite x0 hx0]
      have : cubeMap n S.L M K (k + 1) x0 ∈ (Z'.1 : Set (Torus S.d (n (k + 1)))) := h3
      rwa [hsite x0 hx0] at this
  · rintro ⟨h1, h2⟩ x hx
    have hc := hsite x hx
    refine ⟨⟨?_, ?_⟩, fun ho => h2 ?_⟩
    · show cubeMap n S.L M K (k + 1) x ∈ ((H.locRH (k + 1) Z').step (k + 1)).Z
      rw [locRH_Z Z' le_rfl (by omega), lin_self, hc]; exact h1
    · show cubeMap n S.L M K (k + 1) x ∈ (Z'.1 : Set (Torus S.d (n (k + 1))))
      rw [hc]; exact h1
    · have : cubeMap n S.L M K (k + 1) x ∈ ((H.locRH (k + 1) Z').step k).Omega := ho.1
      rwa [hc] at this


theorem newOutP_iff {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) (y : BlockAt S n M K (k + 1)) :
    newOutP (H.localHistory M K (k + 1) Z') k y ↔
      blockCube S n M K (k + 1) y ∈ (Z'.1 : Set (Torus S.d (n (k + 1)))) ∧
        blockCube S n M K (k + 1) y ∈ ((H.locRH (k + 1) Z').step k).Omega := by
  have hnn := H.F.hnn
  obtain ⟨x0, hx0⟩ := exists_site_in_block (S := S) (n := n) (M := M) hK y
  have hsite : ∀ x, Multiscale.jBlock S.d S.L (M * n K) K (k + 1) x = y →
      cubeMap n S.L M K (k + 1) x = blockCube S n M K (k + 1) y := fun x hx =>
    (blockCube_eq_cubeMap hnn hK hx).symm
  constructor
  · rintro ⟨h1, h2⟩
    have h3 := h2 x0 hx0
    have h4 := h1 x0 hx0
    refine ⟨?_, ?_⟩
    · have : cubeMap n S.L M K (k + 1) x0 ∈ (Z'.1 : Set (Torus S.d (n (k + 1)))) := h4.2
      rwa [hsite x0 hx0] at this
    · have : cubeMap n S.L M K (k + 1) x0 ∈ ((H.locRH (k + 1) Z').step k).Omega := h3.1
      rwa [hsite x0 hx0] at this
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have hc := hsite x hx
      refine ⟨?_, ?_⟩
      · show cubeMap n S.L M K (k + 1) x ∈ ((H.locRH (k + 1) Z').step (k + 1)).Z
        rw [locRH_Z Z' le_rfl (by omega), lin_self, hc]; exact h1
      · show cubeMap n S.L M K (k + 1) x ∈ (Z'.1 : Set (Torus S.d (n (k + 1))))
        rw [hc]; exact h1
    · have hc := hsite x hx
      refine ⟨?_, ?_⟩
      · show cubeMap n S.L M K (k + 1) x ∈ ((H.locRH (k + 1) Z').step k).Omega
        rw [hc]; exact h2
      · show cubeMap n S.L M K (k + 1) x ∈ (Z'.1 : Set (Torus S.d (n (k + 1))))
        rw [hc]; exact h1

theorem gaussBlocks_zblk {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    {y : BlockAt S n M K (k + 1)} (hy : y ∈ gaussBlocks (H.localHistory M K (k + 1) Z') k) :
    ZBlk (H.localHistory M K (k + 1) Z') (k + 1) y :=
  (ZBlk_self_iff hK Z' y).mpr ((gaussBlocks_iff hK Z' y).mp hy).1

theorem newOutP_zblk {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    {y : BlockAt S n M K (k + 1)} (hy : newOutP (H.localHistory M K (k + 1) Z') k y) :
    ZBlk (H.localHistory M K (k + 1) Z') (k + 1) y :=
  (ZBlk_self_iff hK Z' y).mpr ((newOutP_iff hK Z' y).mp hy).1

theorem zblk_gauss_or_new {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    {y : BlockAt S n M K (k + 1)} (hy : ZBlk (H.localHistory M K (k + 1) Z') (k + 1) y) :
    y ∈ gaussBlocks (H.localHistory M K (k + 1) Z') k ∨
      newOutP (H.localHistory M K (k + 1) Z') k y := by
  have h1 := (ZBlk_self_iff hK Z' y).mp hy
  by_cases h : blockCube S n M K (k + 1) y ∈ ((H.locRH (k + 1) Z').step k).Omega
  · exact Or.inr ((newOutP_iff hK Z' y).mpr ⟨h1, h⟩)
  · exact Or.inl ((gaussBlocks_iff hK Z' y).mpr ⟨h1, h⟩)

theorem not_gauss_of_newOut {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    {y : BlockAt S n M K (k + 1)} (hy : newOutP (H.localHistory M K (k + 1) Z') k y) :
    y ∉ gaussBlocks (H.localHistory M K (k + 1) Z') k := fun h =>
  ((gaussBlocks_iff hK Z' y).mp h).2 ((newOutP_iff hK Z' y).mp hy).2

end TopBlocks

/-! ### The output variables: Gaussian integral over the Gaussian blocks -/

section Out

variable {H : RegionHistory S n R k0 K} {k : ℕ}

noncomputable instance (a : LocalHistory S n M K) (k : ℕ) : Fintype ↥(gaussBlocks a k) :=
  Fintype.ofFinite _

/-- The relabelling of the Gaussian blocks as outputs on `Z'` satisfying `Q`. -/
def eqGauss (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) :
    ↥(gaussBlocks (H.localHistory M K (k + 1) Z') k) ≃
      {i : {y : BlockAt S n M K (k + 1) // y ∈ Vblk R (H.localHistory M K (k + 1) Z') (k + 1) ∧
          ZBlk (H.localHistory M K (k + 1) Z') (k + 1) y} //
        gaussBlocks (H.localHistory M K (k + 1) Z') k i.1} where
  toFun b := ⟨⟨b.1, ZBlk_mem_Vblk hK Z' b.1 (gaussBlocks_zblk hK Z' b.2),
    gaussBlocks_zblk hK Z' b.2⟩, b.2⟩
  invFun i := ⟨i.1.1, i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The relabelling of the new′ output blocks as the outputs on `Z'` that are not Gaussian. -/
def eqNew (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) :
    {y : BlockAt S n M K (k + 1) // y ∈ Vblk R (H.localHistory M K (k + 1) Z') (k + 1) ∧
        newOutP (H.localHistory M K (k + 1) Z') k y} ≃
      {i : {y : BlockAt S n M K (k + 1) // y ∈ Vblk R (H.localHistory M K (k + 1) Z') (k + 1) ∧
          ZBlk (H.localHistory M K (k + 1) Z') (k + 1) y} //
        ¬ gaussBlocks (H.localHistory M K (k + 1) Z') k i.1} where
  toFun b := ⟨⟨b.1, b.2.1, newOutP_zblk hK Z' b.2.2⟩, not_gauss_of_newOut hK Z' b.2.2⟩
  invFun i := ⟨i.1.1, i.1.2.1, (zblk_gauss_or_new hK Z' i.1.2.2).resolve_left i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl


theorem outField_mergeOut_of_zblk (a : LocalHistory S n M K) (k : ℕ) (oz : OutZ N R a k)
    (par : OutPar N R a k) {y : BlockAt S n M K k} (hV : y ∈ Vblk R a k) (hz : ZBlk a k y) :
    outField N (mergeOut a k oz par) y = oz ⟨y, hV, hz⟩ := by
  classical
  unfold outField mergeOut
  simp [hV, hz]

theorem measurable_gaussT_left (N : ℕ) (c : ℝ) (w : EuclideanSpace ℝ (Fin N)) :
    Measurable fun ϑ : EuclideanSpace ℝ (Fin N) => gaussT N c ϑ w := by
  unfold gaussT
  fun_prop

theorem gaussT_sub (N : ℕ) (c : ℝ) (ϑ w : EuclideanSpace ℝ (Fin N)) :
    gaussT N c ϑ w = gaussT N c (ϑ - w) 0 := by
  unfold gaussT
  simp

/-- The Gaussian change of variables `u = z o - q` for the product of Gaussians and a function of
the differences. -/
theorem lintegral_gauss_shift {β : Type*} [Fintype β] (N : ℕ) (c z : ℝ) (hz : 0 < z) (hc : 0 ≤ c)
    (q : β → EuclideanSpace ℝ (Fin N)) (F : (β → EuclideanSpace ℝ (Fin N)) → ℝ)
    (hF : Measurable F) :
    ∫⁻ u : β → EuclideanSpace ℝ (Fin N), ENNReal.ofReal ((∏ y, z ^ N * gaussT N c (z • u y) (q y)) *
        F (fun y => z • u y - q y)) ∂(Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) =
      ∫⁻ u : β → EuclideanSpace ℝ (Fin N), ENNReal.ofReal (∏ y, gaussT N c (u y) 0) *
        ENNReal.ofReal (F u) ∂(Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) := by
  set h0 : (β → EuclideanSpace ℝ (Fin N)) → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (∏ y, gaussT N c (v y) 0) * ENNReal.ofReal (F v) with hh0
  have hh0m : Measurable h0 := by
    refine Measurable.mul (ENNReal.measurable_ofReal.comp ?_) (ENNReal.measurable_ofReal.comp hF)
    exact Finset.measurable_prod _ fun y _ =>
      (measurable_gaussT_left N c 0).comp (measurable_pi_apply y)
  have hpt : ∀ u : β → EuclideanSpace ℝ (Fin N),
      ENNReal.ofReal ((∏ y, z ^ N * gaussT N c (z • u y) (q y)) * F (fun y => z • u y - q y)) =
        ENNReal.ofReal (z ^ (N * Fintype.card β)) * h0 (fun y => z • u y - q y) := by
    intro u
    simp only [hh0]
    have e : (∏ y, z ^ N * gaussT N c (z • u y) (q y)) =
        z ^ (N * Fintype.card β) * ∏ y, gaussT N c (z • u y - q y) 0 := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul]
      simp_rw [gaussT_sub N c (z • u _) (q _)]
    rw [e, mul_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul]
    exact Finset.prod_nonneg fun y _ => gaussT_nonneg N c hc _ _
  have hmeas : Measurable fun u : β → EuclideanSpace ℝ (Fin N) =>
      h0 (fun y => z • u y - q y) :=
    hh0m.comp (measurable_pi_iff.mpr fun y => by fun_prop)
  simp_rw [hpt]
  rw [lintegral_const_mul _ hmeas]
  exact lintegral_affine_pi N β hz q h0 hh0m

open Classical in
theorem lintegral_out_split (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) (cs : OpConsts)
    (hz : 0 < cs.z (k + 1)) (hc : 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (F : (↥(gaussBlocks (H.localHistory M K (k + 1) Z') k) → EuclideanSpace ℝ (Fin N)) → ℝ)
    (hF : Measurable F)
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k)
    (par : OutPar N R (H.localHistory M K (k + 1) Z') (k + 1))
    (h : OutPart N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
      (newOutP (H.localHistory M K (k + 1) Z') k) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ oz : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1),
        ENNReal.ofReal (gaussProd N (H.localHistory M K (k + 1) Z') k cs
            (mergeOut (H.localHistory M K (k + 1) Z') (k + 1) oz par) x *
          F (fun y => gaussArg N (cs.z (k + 1))
            (mergeOut (H.localHistory M K (k + 1) Z') (k + 1) oz par) x y.1)) *
        h (restrictOutPart (mergeOut (H.localHistory M K (k + 1) Z') (k + 1) oz par)
          (newOutP (H.localHistory M K (k + 1) Z') k))
      ∂(outPartMeasure N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
        (ZBlk (H.localHistory M K (k + 1) Z') (k + 1))) =
      (∫⁻ u, ENNReal.ofReal (∏ y, gaussT N (cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
          (u y) 0) * ENNReal.ofReal (F u)
        ∂(Measure.pi fun _ : ↥(gaussBlocks (H.localHistory M K (k + 1) Z') k) =>
          (volume : Measure (EuclideanSpace ℝ (Fin N))))) *
        ∫⁻ o, h o ∂(outPartMeasure N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
          (newOutP (H.localHistory M K (k + 1) Z') k)) := by
  have hzN : (0 : ℝ) ≤ cs.z (k + 1) ^ N := by positivity
  set c : ℝ := cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2) with hcdef
  set q : ↥(gaussBlocks (H.localHistory M K (k + 1) Z') k) → EuclideanSpace ℝ (Fin N) :=
    fun y => qCoarseK N x y.1 with hq
  set Gu : (↥(gaussBlocks (H.localHistory M K (k + 1) Z') k) → EuclideanSpace ℝ (Fin N)) →
      ℝ≥0∞ := fun u => ENNReal.ofReal ((∏ y, cs.z (k + 1) ^ N *
        gaussT N c (cs.z (k + 1) • u y) (q y)) * F (fun y => cs.z (k + 1) • u y - q y)) with hGu
  have hGm : Measurable Gu := by
    refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)
    · refine Finset.measurable_prod _ fun y _ => measurable_const.mul ?_
      exact (measurable_gaussT_left N c (q y)).comp (by fun_prop)
    · exact hF.comp (measurable_pi_iff.mpr fun y => by fun_prop)
  have hint : ∀ oz : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1),
      ENNReal.ofReal (gaussProd N (H.localHistory M K (k + 1) Z') k cs
            (mergeOut (H.localHistory M K (k + 1) Z') (k + 1) oz par) x *
          F (fun y => gaussArg N (cs.z (k + 1))
            (mergeOut (H.localHistory M K (k + 1) Z') (k + 1) oz par) x y.1)) *
        h (restrictOutPart (mergeOut (H.localHistory M K (k + 1) Z') (k + 1) oz par)
          (newOutP (H.localHistory M K (k + 1) Z') k)) =
      Gu (fun b => oz (eqGauss hK Z' b).1) * h (fun b => oz (eqNew hK Z' b).1) := by
    intro oz
    congr 1
    · simp only [hGu]
      congr 1
      congr 1
      · unfold gaussProd
        refine Finset.prod_congr (by ext y; simp) fun y _ => ?_
        rw [outField_mergeOut_of_zblk _ _ oz par (ZBlk_mem_Vblk hK Z' y.1 (gaussBlocks_zblk hK Z' y.2))
          (gaussBlocks_zblk hK Z' y.2)]
        rfl
      · congr 1
        funext y
        unfold gaussArg
        rw [outField_mergeOut_of_zblk _ _ oz par (ZBlk_mem_Vblk hK Z' y.1 (gaussBlocks_zblk hK Z' y.2))
          (gaussBlocks_zblk hK Z' y.2)]
        rfl
    · congr 1
      funext b
      unfold restrictOutPart mergeOut
      simp [newOutP_zblk hK Z' b.2.2]
      rfl
  simp_rw [hint]
  refine Eq.trans (PiTools.lintegral_mul_split (volume : Measure (EuclideanSpace ℝ (Fin N)))
    (fun i : {y : BlockAt S n M K (k + 1) // y ∈ Vblk R (H.localHistory M K (k + 1) Z') (k + 1) ∧
          ZBlk (H.localHistory M K (k + 1) Z') (k + 1) y} =>
      gaussBlocks (H.localHistory M K (k + 1) Z') k i.1) (eqGauss hK Z') (eqNew hK Z') Gu hGm h hh) ?_
  congr 1
  exact lintegral_gauss_shift N c _ hz hc q F hF

end Out

/-! ### The weight of the pre-operator and the step bound -/

section Weights

variable {H : RegionHistory S n R k0 K} {k : ℕ}

theorem absW_preKernel (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (T₀ : LFKernel (OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
      (NewCfg N (H.localHistory M K (k + 1) Z') k) (EuclideanSpace ℝ (Fin N))
      (GIdx S n M K N))
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub))
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) :
    (preKernel hK Z' sub T₀).absW o x hv g =
      T₀.absW o (newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x) hv g *
        ∏ Y : ↥(H.parts k Z'), (sub Y.1 Y.2).T.absW (ancOut Y.1 Z' x)
          (ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) x) hv g := by
  unfold LFKernel.absW
  rw [preKernel_K, preKernel_b, Complex.add_re, Complex.re_sum, Real.exp_add, Real.exp_sum]
  rw [← ENNReal.ofReal_prod_of_nonneg
    (fun Y _ => mul_nonneg ((sub Y.1 Y.2).T.K_nonneg _ _ _) (Real.exp_pos _).le),
    ← ENNReal.ofReal_mul (mul_nonneg (T₀.K_nonneg _ _ _) (Real.exp_pos _).le)]
  congr 1
  rw [Finset.prod_mul_distrib]
  ring


open Classical in
/-- Pointwise domination of the weight of the step kernel by the Gaussian factors times the
majorants of the new′ variables (Lemma II.5.13 (2)). -/
theorem absW_step_le (a : LocalHistory S n M K) (k : ℕ) (cs : OpConsts)
    (hz : 0 ≤ cs.z (k + 1)) (hc : 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (T : LFKernel (OutT N R a (k + 1)) (NewCfg N a k) (EuclideanSpace ℝ (Fin N))
      (GIdx S n M K N)) (wit : GaussWit N R a k)
    (Sw : wit.W → OutPart N (Vblk R a (k + 1)) (newOutP a k) →
      SubCfg N a (k + 1) (newPrimeVars a k) → OutPart N (Vblk R a (k + 1)) (parOutP a k) →
      EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → ℝ≥0∞)
    (hK : ∀ o x hv, T.K o x hv = gaussProd N a k cs o x *
      ∑ w, wit.F w (fun y => gaussArg N (cs.z (k + 1)) o x y.1) * wit.Kt w o x hv)
    (hF : ∀ w u, 0 ≤ wit.F w u) (hKt : ∀ w o x hv, 0 ≤ wit.Kt w o x hv)
    (hSw : ∀ w o x hv g, g ∈ l1Ball (GIdx S n M K N) →
      ENNReal.ofReal (wit.Kt w o x hv * Real.exp (T.b o x hv g).re) ≤
        Sw w (restrictOutPart o (newOutP a k)) (restrictSub (newPrimeVars_sub a k) x)
          (restrictOutPart o (parOutP a k)) hv g)
    (o : OutT N R a (k + 1)) (x : NewCfg N a k) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N)) :
    T.absW o x hv g ≤ ∑ w, ENNReal.ofReal (gaussProd N a k cs o x *
        wit.F w (fun y => gaussArg N (cs.z (k + 1)) o x y.1)) *
      Sw w (restrictOutPart o (newOutP a k)) (restrictSub (newPrimeVars_sub a k) x)
        (restrictOutPart o (parOutP a k)) hv g := by
  have hgp := gaussProd_nonneg N a k cs hz hc o x
  unfold LFKernel.absW
  rw [hK, Finset.mul_sum, Finset.sum_mul]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_le_sum fun w _ => ?_
    have h1 : gaussProd N a k cs o x *
        (wit.F w (fun y => gaussArg N (cs.z (k + 1)) o x y.1) * wit.Kt w o x hv) *
          Real.exp (T.b o x hv g).re =
        (gaussProd N a k cs o x * wit.F w (fun y => gaussArg N (cs.z (k + 1)) o x y.1)) *
          (wit.Kt w o x hv * Real.exp (T.b o x hv g).re) := by ring
    rw [h1, ENNReal.ofReal_mul (mul_nonneg hgp (hF w _))]
    exact mul_le_mul_right (hSw w o x hv g hg) _
  · intro w _
    exact mul_nonneg (mul_nonneg hgp (mul_nonneg (hF w _) (hKt w o x hv))) (Real.exp_pos _).le


section Measurability

theorem measurable_qCoarseK {a : LocalHistory S n M K} {k : ℕ} {A : Set (InternalVars a (k + 1))}
    (y : BlockAt S n M K (k + 1)) : Measurable fun x : SubCfg N a (k + 1) A => qCoarseK N x y := by
  unfold qCoarseK
  exact (Finset.measurable_sum _ fun y' _ =>
    measurable_subVarField (a := a) (k := k + 1) (A := A) k y').const_smul (((S.L : ℝ) ^ S.d)⁻¹)

theorem measurable_gaussT_pair (N : ℕ) (c : ℝ) {α : Type*} [MeasurableSpace α]
    {f g : α → EuclideanSpace ℝ (Fin N)} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun p => gaussT N c (f p) (g p) := by
  unfold gaussT
  exact measurable_const.mul (Real.measurable_exp.comp
    (measurable_const.mul ((measurable_norm.comp (hf.sub hg)).pow_const 2)))

theorem measurable_gaussArg_pair (z : ℝ) {a : LocalHistory S n M K} {k : ℕ}
    {V : Set (BlockAt S n M K (k + 1))} {A : Set (InternalVars a (k + 1))}
    (y : BlockAt S n M K (k + 1)) :
    Measurable fun p : OutConfig N V × SubCfg N a (k + 1) A => gaussArg N z p.1 p.2 y := by
  unfold gaussArg
  exact (((measurable_outField N V y).comp measurable_fst).const_smul z).sub
    ((measurable_qCoarseK (a := a) (k := k) (A := A) y).comp measurable_snd)

theorem measurable_gaussProd_pair (a : LocalHistory S n M K) (k : ℕ) (cs : OpConsts)
    {V : Set (BlockAt S n M K (k + 1))} :
    Measurable fun p : OutConfig N V × NewCfg N a k => gaussProd N a k cs p.1 p.2 := by
  classical
  unfold gaussProd
  refine Finset.measurable_prod _ fun y _ => measurable_const.mul ?_
  have hm : Measurable fun p : OutConfig N V × NewCfg N a k =>
      cs.z (k + 1) • outField N p.1 y.1 :=
    ((measurable_outField N V y.1).comp measurable_fst).const_smul (cs.z (k + 1))
  exact measurable_gaussT_pair N _ hm
    ((measurable_qCoarseK (a := a) (k := k) (A := newVars a k) y.1).comp measurable_snd)

theorem measurable_gaussFactor (a : LocalHistory S n M K) (k : ℕ) (cs : OpConsts)
    {V : Set (BlockAt S n M K (k + 1))}
    (F : (↥(gaussBlocks a k) → EuclideanSpace ℝ (Fin N)) → ℝ) (hF : Measurable F) :
    Measurable fun p : OutConfig N V × NewCfg N a k =>
      ENNReal.ofReal (gaussProd N a k cs p.1 p.2 *
        F (fun y => gaussArg N (cs.z (k + 1)) p.1 p.2 y.1)) := by
  refine ENNReal.measurable_ofReal.comp ((measurable_gaussProd_pair a k cs).mul ?_)
  exact hF.comp (measurable_pi_iff.mpr fun y =>
    measurable_gaussArg_pair (cs.z (k + 1)) y.1)

end Measurability

end Weights

/-! ### The composition of the bounds -/

section Main

variable {H : RegionHistory S n R k0 K} {k : ℕ}

/-- The parameters as an element of `OutPart … (parOutP …)` (the same thing, with the
type of the step data). -/
def parC (a : LocalHistory S n M K) (k : ℕ) (par : OutPar N R a (k + 1)) :
    OutPart N (Vblk R a (k + 1)) (parOutP a k) := par

theorem measurable_restrictOutPart {α : Type} {V : Set α} (P : α → Prop) :
    Measurable (fun o : OutConfig N V => restrictOutPart o P) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

theorem restrict_merge_par (a : LocalHistory S n M K) (k : ℕ) (oz : OutZ N R a (k + 1))
    (par : OutPar N R a (k + 1)) :
    restrictOutPart (mergeOut a (k + 1) oz par) (parOutP a k) = parC a k par := by
  classical
  funext y
  unfold restrictOutPart mergeOut
  have : ¬ ZBlk a (k + 1) y.1 := y.2.2
  simp only [this, ↓reduceDIte]
  rfl

theorem measurable_slice_right {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (F : α → β → γ) (hF : Measurable fun p : α × β => F p.1 p.2) (y : β) :
    Measurable fun a => F a y := hF.comp measurable_prodMk_right

/-- The Gaussian factor of a witness, as a function of the output and the variables. -/
noncomputable def Afn {H : RegionHistory S n R k0 K} {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (cs : OpConsts) (wit : GaussWit N R (H.localHistory M K (k + 1) Z') k) (w : wit.W)
    (par : OutPar N R (H.localHistory M K (k + 1) Z') (k + 1))
    (oz : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub)) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussProd N (H.localHistory M K (k + 1) Z') k cs
            (mergeOut (H.localHistory M K (k + 1) Z') (k + 1) oz par)
            (newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x) *
          wit.F w (fun y => gaussArg N (cs.z (k + 1))
            (mergeOut (H.localHistory M K (k + 1) Z') (k + 1) oz par)
            (newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x) y.1))

/-- The majorant of the new′ variables, as a function of the output and the variables. -/
noncomputable def Bfn {H : RegionHistory S n R k0 K} {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (Sw : OutPart N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
        (newOutP (H.localHistory M K (k + 1) Z') k) →
      SubCfg N (H.localHistory M K (k + 1) Z') (k + 1)
        (newPrimeVars (H.localHistory M K (k + 1) Z') k) →
      OutPart N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
        (parOutP (H.localHistory M K (k + 1) Z') k) →
      EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → ℝ≥0∞)
    (par : OutPar N R (H.localHistory M K (k + 1) Z') (k + 1)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (oz : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub)) : ℝ≥0∞ :=
  Sw (restrictOutPart (mergeOut (H.localHistory M K (k + 1) Z') (k + 1) oz par)
              (newOutP (H.localHistory M K (k + 1) Z') k))
            (restrictSub (newPrimeVars_sub (H.localHistory M K (k + 1) Z') k)
              (newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x))
            (parC _ k par) hv g

/-- The product of the weights of the old parts. -/
noncomputable def Pfn {H : RegionHistory S n R k0 K} {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub)) : ℝ≥0∞ :=
  ∏ Y : ↥(H.parts k Z'), (sub Y.1 Y.2).T.absW (ancOut Y.1 Z' x)
    (ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) x) hv g

theorem measurable_Afn {H : RegionHistory S n R k0 K} {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (cs : OpConsts) (wit : GaussWit N R (H.localHistory M K (k + 1) Z') k) (w : wit.W)
    (hFm : Measurable (wit.F w)) (par : OutPar N R (H.localHistory M K (k + 1) Z') (k + 1)) :
    Measurable fun p : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1) ×
      SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub) =>
      Afn hK Z' sub cs wit w par p.1 p.2 := by
  have hm1 : Measurable fun p : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1) ×
      SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub) =>
      mergeOut (H.localHistory M K (k + 1) Z') (k + 1) p.1 par :=
    (measurable_mergeOut (H.localHistory M K (k + 1) Z') (k + 1) par).comp measurable_fst
  have hm2 : Measurable fun p : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1) ×
      SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub) =>
      newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) p.2 :=
    (measurable_newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub)).comp
      measurable_snd
  have h1 := (measurable_gaussFactor (N := N) (V := Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
    (H.localHistory M K (k + 1) Z') k cs (wit.F w) hFm)
  have h2 := hm1.prodMk hm2
  have h3 := h1.comp h2
  exact h3

theorem measurable_Bfn {H : RegionHistory S n R k0 K} {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (Sw : OutPart N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
        (newOutP (H.localHistory M K (k + 1) Z') k) →
      SubCfg N (H.localHistory M K (k + 1) Z') (k + 1)
        (newPrimeVars (H.localHistory M K (k + 1) Z') k) →
      OutPart N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
        (parOutP (H.localHistory M K (k + 1) Z') k) →
      EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → ℝ≥0∞)
    (par : OutPar N R (H.localHistory M K (k + 1) Z') (k + 1)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ)
    (hSwm : Measurable fun q : OutPart N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
        (newOutP (H.localHistory M K (k + 1) Z') k) ×
        SubCfg N (H.localHistory M K (k + 1) Z') (k + 1)
          (newPrimeVars (H.localHistory M K (k + 1) Z') k) => Sw q.1 q.2 (parC _ k par) hv g) :
    Measurable fun p : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1) ×
      SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub) =>
      Bfn hK Z' sub Sw par hv g p.1 p.2 := by
  have hm1 : Measurable fun p : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1) ×
      SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub) =>
      mergeOut (H.localHistory M K (k + 1) Z') (k + 1) p.1 par :=
    (measurable_mergeOut (H.localHistory M K (k + 1) Z') (k + 1) par).comp measurable_fst
  have hm2 : Measurable fun p : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1) ×
      SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub) =>
      newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) p.2 :=
    (measurable_newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub)).comp
      measurable_snd
  have h1 := (measurable_restrictOutPart (N := N) (V := Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
    (newOutP (H.localHistory M K (k + 1) Z') k)).comp hm1
  have h2 := (measurable_restrictSub (N := N) (newPrimeVars_sub (H.localHistory M K (k + 1) Z') k)).comp hm2
  exact hSwm.comp (h1.prodMk h2)

theorem measurable_Pfn {H : RegionHistory S n R k0 K} {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) :
    Measurable (Pfn hK Z' sub hv g) :=
  Finset.measurable_prod _ fun Y _ =>
    ((sub Y.1 Y.2).T.measurable_absW hv g).comp
      ((measurable_ancOut (R := R) Y.1 Z' _).prodMk
        (measurable_ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2)))

theorem measurable_Fw {H : RegionHistory S n R k0 K} {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (cs : OpConsts) (wit : GaussWit N R (H.localHistory M K (k + 1) Z') k) (w : wit.W)
    (hFm : Measurable (wit.F w))
    (Sw : OutPart N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
        (newOutP (H.localHistory M K (k + 1) Z') k) →
      SubCfg N (H.localHistory M K (k + 1) Z') (k + 1)
        (newPrimeVars (H.localHistory M K (k + 1) Z') k) →
      OutPart N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
        (parOutP (H.localHistory M K (k + 1) Z') k) →
      EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → ℝ≥0∞)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    (par : OutPar N R (H.localHistory M K (k + 1) Z') (k + 1))
    (hSwm : Measurable fun q : OutPart N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
        (newOutP (H.localHistory M K (k + 1) Z') k) ×
        SubCfg N (H.localHistory M K (k + 1) Z') (k + 1)
          (newPrimeVars (H.localHistory M K (k + 1) Z') k) => Sw q.1 q.2 (parC _ k par) hv g) :
    Measurable fun p : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1) ×
      SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub) =>
      Afn hK Z' sub cs wit w par p.1 p.2 * Bfn hK Z' sub Sw par hv g p.1 p.2 *
        Pfn hK Z' sub hv g p.2 :=
  ((measurable_Afn hK Z' sub cs wit w hFm par).mul (measurable_Bfn hK Z' sub Sw par hv g hSwm)).mul
    ((measurable_Pfn hK Z' sub hv g).comp measurable_snd)

open Classical in
/-- One witness of the Gaussian structure: integrate the Gaussian variables, then the old
variables (ancestor bounds), then the new′ variables. -/
theorem term_le (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (cs : OpConsts) (hz : 0 < cs.z (k + 1))
    (hc : 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (κ : ↥(H.parts k Z') → ℝ)
    (hanc : ∀ Y : ↥(H.parts k Z'), PkgBound (H.localHistory M K k Y.1) k (sub Y.1 Y.2) (κ Y))
    (wit : GaussWit N R (H.localHistory M K (k + 1) Z') k) (w : wit.W)
    (hFm : Measurable (wit.F w))
    (Sw : OutPart N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
        (newOutP (H.localHistory M K (k + 1) Z') k) →
      SubCfg N (H.localHistory M K (k + 1) Z') (k + 1)
        (newPrimeVars (H.localHistory M K (k + 1) Z') k) →
      OutPart N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
        (parOutP (H.localHistory M K (k + 1) Z') k) →
      EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → ℝ≥0∞)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N))
    (par : OutPar N R (H.localHistory M K (k + 1) Z') (k + 1))
    (hSwm : Measurable fun q : OutPart N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
        (newOutP (H.localHistory M K (k + 1) Z') k) ×
        SubCfg N (H.localHistory M K (k + 1) Z') (k + 1)
          (newPrimeVars (H.localHistory M K (k + 1) Z') k) => Sw q.1 q.2 (parC _ k par) hv g) :
    ∫⁻ oz : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1),
        ∫⁻ x, Afn hK Z' sub cs wit w par oz x * Bfn hK Z' sub Sw par hv g oz x *
          Pfn hK Z' sub hv g x
          ∂(subMeasure N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub))
        ∂(outPartMeasure N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
          (ZBlk (H.localHistory M K (k + 1) Z') (k + 1))) ≤
      mWit N (cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (H.localHistory M K (k + 1) Z') k
          wit.F w *
        ((∏ Y : ↥(H.parts k Z'), ENNReal.ofReal (Real.exp (-κ Y))) *
          ∫⁻ q, Sw q.1 q.2 (parC _ k par) hv g
            ∂((outPartMeasure N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
              (newOutP (H.localHistory M K (k + 1) Z') k)).prod
              (subMeasure N (H.localHistory M K (k + 1) Z') (k + 1)
                (newPrimeVars (H.localHistory M K (k + 1) Z') k)))) := by
  have hA := measurable_Afn hK Z' sub cs wit w hFm par
  have hB := measurable_Bfn hK Z' sub Sw par hv g hSwm
  have hAB := measurable_Fw hK Z' sub cs wit w hFm Sw hv g par hSwm
  rw [lintegral_lintegral_swap (f := fun (oz : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub)) =>
      Afn hK Z' sub cs wit w par oz x * Bfn hK Z' sub Sw par hv g oz x * Pfn hK Z' sub hv g x)
    hAB.aemeasurable]
  have hinner : ∀ x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub),
      ∫⁻ oz : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1),
        Afn hK Z' sub cs wit w par oz x * Bfn hK Z' sub Sw par hv g oz x *
          Pfn hK Z' sub hv g x
        ∂(outPartMeasure N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
          (ZBlk (H.localHistory M K (k + 1) Z') (k + 1))) =
      mWit N (cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (H.localHistory M K (k + 1) Z') k
          wit.F w *
        ((∫⁻ o, Sw o (restrictSub (newPrimeVars_sub (H.localHistory M K (k + 1) Z') k)
              (newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x))
              (parC _ k par) hv g
            ∂(outPartMeasure N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
              (newOutP (H.localHistory M K (k + 1) Z')  k))) *
          Pfn hK Z' sub hv g x) := by
    intro x
    have hAs : Measurable fun oz : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1) =>
        Afn hK Z' sub cs wit w par oz x :=
      measurable_slice_right (fun oz x => Afn hK Z' sub cs wit w par oz x) hA x
    have hBs : Measurable fun oz : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1) =>
        Bfn hK Z' sub Sw par hv g oz x :=
      measurable_slice_right (fun oz x => Bfn hK Z' sub Sw par hv g oz x) hB x
    refine Eq.trans (lintegral_mul_const (Pfn hK Z' sub hv g x) (hAs.mul hBs)) ?_
    rw [← mul_assoc]
    congr 1
    exact lintegral_out_split hK Z' cs hz hc (wit.F w) hFm
      (newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x) par
      (fun o => Sw o (restrictSub (newPrimeVars_sub (H.localHistory M K (k + 1) Z') k)
        (newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x))
        (parC _ k par) hv g)
      (hSwm.comp measurable_prodMk_right)
  have hF : Measurable fun x' : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1)
      (newPrimeVars (H.localHistory M K (k + 1) Z') k) =>
      ∫⁻ o, Sw o x' (parC _ k par) hv g
        ∂(outPartMeasure N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
          (newOutP (H.localHistory M K (k + 1) Z' ) k)) :=
    hSwm.lintegral_prod_left'
  have hmx : Measurable fun x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1)
      (preVars hK Z' sub) =>
      (∫⁻ o, Sw o (restrictSub (newPrimeVars_sub (H.localHistory M K (k + 1) Z') k)
          (newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x))
          (parC _ k par) hv g
        ∂(outPartMeasure N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
          (newOutP (H.localHistory M K (k + 1) Z')  k))) * Pfn hK Z' sub hv g x :=
    (hF.comp ((measurable_restrictSub _).comp (measurable_newRestrict _ _))).mul
      (measurable_Pfn hK Z' sub hv g)
  calc _ = ∫⁻ x, mWit N (cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
            (H.localHistory M K (k + 1) Z') k wit.F w *
          ((∫⁻ o, Sw o (restrictSub (newPrimeVars_sub (H.localHistory M K (k + 1) Z') k)
              (newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x))
              (parC _ k par) hv g
            ∂(outPartMeasure N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
              (newOutP (H.localHistory M K (k + 1) Z')  k))) * Pfn hK Z' sub hv g x)
          ∂(subMeasure N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub)) :=
        lintegral_congr hinner
    _ = mWit N (cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (H.localHistory M K (k + 1) Z') k
          wit.F w *
        ∫⁻ x, (∫⁻ o, Sw o (restrictSub (newPrimeVars_sub (H.localHistory M K (k + 1) Z') k)
              (newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x))
              (parC _ k par) hv g
            ∂(outPartMeasure N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
              (newOutP (H.localHistory M K (k + 1) Z')  k))) * Pfn hK Z' sub hv g x
          ∂(subMeasure N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub)) :=
        lintegral_const_mul _ hmx
    _ ≤ mWit N (cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (H.localHistory M K (k + 1) Z') k
          wit.F w *
        ((∏ Y : ↥(H.parts k Z'), ENNReal.ofReal (Real.exp (-κ Y))) *
          ∫⁻ x', (∫⁻ o, Sw o x' (parC _ k par) hv g
            ∂(outPartMeasure N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
              (newOutP (H.localHistory M K (k + 1) Z' ) k)))
            ∂(subMeasure N (H.localHistory M K (k + 1) Z') (k + 1)
              (newPrimeVars (H.localHistory M K (k + 1) Z') k))) :=
        mul_le_mul_right (lintegral_anc_le hK Z' sub κ hanc _ hF hv g hg) _
    _ = _ := by
        rw [lintegral_prod_symm _ hSwm.aemeasurable]

theorem measurable_slice_left {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (F : α → β → γ) (hF : Measurable fun p : α × β => F p.1 p.2) (a : α) :
    Measurable fun y => F a y := hF.comp measurable_prodMk_left

variable (geo : Geo S n R M) (cs : OpConsts) {κs : ℕ → LocalHistory S n M K → ℝ}
  (SD : StepData k0 geo cs N κs)

open Classical in
/-- **Lemma II.5.13 (composition of bounds; (D5) for a step), version 1.2.**  If the operators
of the old parts satisfy (1.26) with exponents `κ_k(Y)` and the step data satisfy (S1)-(S2) (the
Gaussian structure with witness functions, `StepData.gauss`), then the pre-operator satisfies (1.26)
with exponent `κ^{(k)}(Z') + ∑_Y κ_k(Y)`.  Here `0 < z_{k+1}` and `0 ≤ β_k a L^{d-2}`
are the signs of the running constants. -/
theorem preOp_pkgBound (hH : H.Admissible) (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (hz : 0 < cs.z (k + 1)) (hc : 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (κ : ↥(H.parts k Z') → ℝ)
    (hanc : ∀ Y : ↥(H.parts k Z'), PkgBound (H.localHistory M K k Y.1) k (sub Y.1 Y.2) (κ Y)) :
    PkgBound (H.localHistory M K (k + 1) Z') (k + 1) (preOp geo cs SD hH hK Z' sub)
      (κs k (H.localHistory M K (k + 1) Z') + ∑ Y : ↥(H.parts k Z'), κ Y) := by
  intro hv g hg par
  obtain ⟨hF01, hFm, hKt0, -, hKK, Sw, hSwm, hSwle, hSwtot⟩ := SD.gauss H hH k Z'
  have hpt : ∀ (oz : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1))
      (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub)),
      (preOp geo cs SD hH hK Z' sub).T.absW (mergeOut (H.localHistory M K (k + 1) Z') (k + 1) oz par)
        x hv g ≤ ∑ w, Afn hK Z' sub cs (SD.wit k (H.localHistory M K (k + 1) Z')) w par oz x *
          Bfn hK Z' sub (Sw w) par hv g oz x * Pfn hK Z' sub hv g x := by
    intro oz x
    have h1 := absW_step_le (H.localHistory M K (k + 1) Z') k cs hz.le hc
      (SD.ker k (H.localHistory M K (k + 1) Z')) (SD.wit k (H.localHistory M K (k + 1) Z')) Sw hKK
      (fun w u => (hF01 w u).1) hKt0 hSwle
      (mergeOut (H.localHistory M K (k + 1) Z') (k + 1) oz par)
      (newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x) hv g hg
    rw [restrict_merge_par] at h1
    show (preKernel hK Z' sub (SD.ker k (H.localHistory M K (k + 1) Z'))).absW _ x hv g ≤ _
    rw [absW_preKernel, ← Finset.sum_mul]
    exact mul_le_mul_left h1 _
  have hmw : ∀ w, Measurable fun p : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1) ×
      SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub) =>
      Afn hK Z' sub cs (SD.wit k (H.localHistory M K (k + 1) Z')) w par p.1 p.2 *
        Bfn hK Z' sub (Sw w) par hv g p.1 p.2 * Pfn hK Z' sub hv g p.2 := fun w =>
    measurable_Fw hK Z' sub cs (SD.wit k (H.localHistory M K (k + 1) Z')) w (hFm w) (Sw w)
      hv g par (hSwm w (parC _ k par) hv g)
  have hsum : ∀ oz : OutZ N R (H.localHistory M K (k + 1) Z') (k + 1),
      ∫⁻ x, ∑ w, Afn hK Z' sub cs (SD.wit k (H.localHistory M K (k + 1) Z')) w par oz x *
          Bfn hK Z' sub (Sw w) par hv g oz x * Pfn hK Z' sub hv g x
        ∂(subMeasure N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub)) =
      ∑ w, ∫⁻ x, Afn hK Z' sub cs (SD.wit k (H.localHistory M K (k + 1) Z')) w par oz x *
          Bfn hK Z' sub (Sw w) par hv g oz x * Pfn hK Z' sub hv g x
        ∂(subMeasure N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub)) := fun oz =>
    lintegral_finsetSum _ fun w _ => measurable_slice_left
      (fun oz x => Afn hK Z' sub cs (SD.wit k (H.localHistory M K (k + 1) Z')) w par oz x *
          Bfn hK Z' sub (Sw w) par hv g oz x * Pfn hK Z' sub hv g x) (hmw w) oz
  calc _ ≤ ∫⁻ oz, ∑ w, ∫⁻ x, Afn hK Z' sub cs (SD.wit k (H.localHistory M K (k + 1) Z')) w par oz x *
          Bfn hK Z' sub (Sw w) par hv g oz x * Pfn hK Z' sub hv g x
        ∂(subMeasure N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub))
        ∂(outPartMeasure N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
          (ZBlk (H.localHistory M K (k + 1) Z') (k + 1))) := by
        refine lintegral_mono fun oz => ?_
        rw [← hsum oz]
        exact lintegral_mono fun x => hpt oz x
    _ = ∑ w, ∫⁻ oz, ∫⁻ x, Afn hK Z' sub cs (SD.wit k (H.localHistory M K (k + 1) Z')) w par oz x *
          Bfn hK Z' sub (Sw w) par hv g oz x * Pfn hK Z' sub hv g x
        ∂(subMeasure N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub))
        ∂(outPartMeasure N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
          (ZBlk (H.localHistory M K (k + 1) Z') (k + 1))) :=
        lintegral_finsetSum _ fun w _ => (hmw w).lintegral_prod_right'
    _ ≤ ∑ w, mWit N (cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (H.localHistory M K (k + 1) Z') k
          (SD.wit k (H.localHistory M K (k + 1) Z')).F w *
        ((∏ Y : ↥(H.parts k Z'), ENNReal.ofReal (Real.exp (-κ Y))) *
          ∫⁻ q, Sw w q.1 q.2 (parC _ k par) hv g
            ∂((outPartMeasure N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
              (newOutP (H.localHistory M K (k + 1) Z') k)).prod
              (subMeasure N (H.localHistory M K (k + 1) Z') (k + 1)
                (newPrimeVars (H.localHistory M K (k + 1) Z') k)))) :=
        Finset.sum_le_sum fun w _ => term_le hK Z' sub cs hz hc κ hanc
          (SD.wit k (H.localHistory M K (k + 1) Z')) w (hFm w) (Sw w) hv g hg par
          (hSwm w (parC _ k par) hv g)
    _ = (∏ Y : ↥(H.parts k Z'), ENNReal.ofReal (Real.exp (-κ Y))) *
          ∑ w, mWit N (cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (H.localHistory M K (k + 1) Z') k
            (SD.wit k (H.localHistory M K (k + 1) Z')).F w *
          ∫⁻ q, Sw w q.1 q.2 (parC _ k par) hv g
            ∂((outPartMeasure N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
              (newOutP (H.localHistory M K (k + 1) Z') k)).prod
              (subMeasure N (H.localHistory M K (k + 1) Z') (k + 1)
                (newPrimeVars (H.localHistory M K (k + 1) Z') k))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => by ring
    _ ≤ (∏ Y : ↥(H.parts k Z'), ENNReal.ofReal (Real.exp (-κ Y))) *
          ENNReal.ofReal (Real.exp (-κs k (H.localHistory M K (k + 1) Z'))) :=
        mul_le_mul_right (hSwtot (parC _ k par) hv g hg) _
    _ = _ := by
        rw [mul_comm, ← ENNReal.ofReal_prod_of_nonneg (fun Y _ => (Real.exp_pos _).le),
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_sum, ← Real.exp_add]
        congr 2
        rw [Finset.sum_neg_distrib]
        ring

end Main

end Bound

end Balaban.LargeField
