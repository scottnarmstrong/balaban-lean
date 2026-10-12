module

public import Balaban.LargeField.Operators.QuietSymm
public import Balaban.LargeField.Operators.StepData

/-!
# Euclidean symmetries and the quiet kernel: the reading maps and the Gaussian factor

Let `σ` be a `TorusSym` and `hI : HistImage σ a a'`.  For corresponding output and internal
configurations (`RelOut`, `RelSub`):

* `TorusSym.eb_blockMap`: the block permutations commute with the coarsening of blocks;
* `qCoarseK_euclid`, `gaussArg_euclid`, `gaussProd_euclid`: the Gaussian factor of the quiet kernel
  is invariant;
* `subMultiscaleField_euclid`, `subFluctField_euclid`: the multiscale and fluctuation fields at the
  image block are the fields at the block.
-/

@[expose] public section

namespace Balaban.LargeField
open MeasureTheory Balaban RegionHistory

set_option linter.unusedSectionVars false

section Lay1

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {k : ℕ} (σ : TorusSym S n M K)

theorem jBlock_succ_blockMap {j : ℕ} (hj : j + 1 ≤ K) (x : Torus S.d (M * n K * S.L ^ K)) :
    Multiscale.jBlock S.d S.L (M * n K) K (j + 1) x =
      blockMap S.L (M * n K * S.L ^ (K - (j + 1)))
        (Multiscale.jBlock S.d S.L (M * n K) K j x) := by
  unfold Multiscale.jBlock
  rw [blockMap_comp (Multiscale.side_eq (show j ≤ K by omega)) (by
    have : K - j = (K - (j + 1)) + 1 := by omega
    rw [this, pow_succ]; ring), pow_succ]


theorem TorusSym.eb_blockMap {j : ℕ} (hj : j + 1 ≤ K) (y : BlockAt S n M K j) :
    σ.eb (j + 1) (blockMap S.L (M * n K * S.L ^ (K - (j + 1))) y) =
      blockMap S.L (M * n K * S.L ^ (K - (j + 1))) (σ.eb j y) := by
  obtain ⟨x, rfl⟩ := exists_site_in_block (S := S) (n := n) (M := M) (show j ≤ K by omega) y
  have h1 := σ.jblock (j + 1) hj x
  rw [jBlock_succ_blockMap hj, jBlock_succ_blockMap hj, σ.jblock j (by omega)] at h1
  exact h1.symm

variable {σ} {a a' : LocalHistory S n M K}

theorem HistImage.gaussBlocks_eq (hI : HistImage σ a a') (hk : k + 1 ≤ K) :
    gaussBlocks a' k = σ.eb (k + 1) '' gaussBlocks a k := by
  have hset : a'.Z (k + 1) \ a'.Omega k = σ.ef '' (a.Z (k + 1) \ a.Omega k) := by
    rw [hI.Z, hI.Omega, Set.image_sdiff σ.ef.injective]
  ext y'
  constructor
  · intro h
    refine ⟨(σ.eb (k + 1)).symm y', ?_, by simp⟩
    show BlockSub (S := S) (n := n) (M := M) (K := K) (k + 1) _ _
    rw [← σ.blockSub_image hk]
    have h' : BlockSub (S := S) (n := n) (M := M) (K := K) (k + 1) y' (σ.ef '' (a.Z (k + 1) \ a.Omega k)) := by
      rw [← hset]; exact h
    simpa using h'
  · rintro ⟨y, hy, rfl⟩
    show BlockSub (S := S) (n := n) (M := M) (K := K) (k + 1) (σ.eb (k + 1) y) _
    rw [hset]
    exact (σ.blockSub_image hk _ _).mpr hy


theorem HistImage.mem_gaussBlocks_iff (hI : HistImage σ a a') (hk : k + 1 ≤ K)
    (y : BlockAt S n M K (k + 1)) : σ.eb (k + 1) y ∈ gaussBlocks a' k ↔ y ∈ gaussBlocks a k := by
  rw [hI.gaussBlocks_eq hk]
  exact (σ.eb (k + 1)).injective.mem_set_image

section Rel1

variable {A : Set (InternalVars a (k + 1))} {A' : Set (InternalVars a' (k + 1))}

theorem qCoarseK_euclid {hI : HistImage σ a a'} (hk : k + 1 ≤ K) {x : SubCfg N a (k + 1) A}
    {x' : SubCfg N a' (k + 1) A'} (h : RelSub hI hk x x') (y : BlockAt S n M K (k + 1)) :
    qCoarseK N x' (σ.eb (k + 1) y) = qCoarseK N x y := by
  classical
  unfold qCoarseK
  congr 1
  refine Finset.sum_equiv (σ.eb k).symm (fun y' => ?_) (fun y' _ => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨z, rfl⟩ := (σ.eb k).surjective y'
    rw [Equiv.symm_apply_apply, ← σ.eb_blockMap hk]
    exact (σ.eb (k + 1)).injective.eq_iff
  · have := h.read_large k ((σ.eb k).symm y')
    rwa [Equiv.apply_symm_apply] at this

theorem gaussArg_euclid {hI : HistImage σ a a'} (hk : k + 1 ≤ K) (z : ℝ)
    {V V' : Set (BlockAt S n M K (k + 1))} {o : OutConfig N V} {o' : OutConfig N V'}
    (ho : RelOut σ o o') {x : SubCfg N a (k + 1) A}
    {x' : SubCfg N a' (k + 1) A'} (h : RelSub hI hk x x') (y : BlockAt S n M K (k + 1)) :
    gaussArg N z o' x' (σ.eb (k + 1) y) = gaussArg N z o x y := by
  unfold gaussArg
  rw [ho y, qCoarseK_euclid hk h]

end Rel1

theorem gaussProd_euclid {hI : HistImage σ a a'} (hk : k + 1 ≤ K) (cs : OpConsts)
    {V V' : Set (BlockAt S n M K (k + 1))} {o : OutConfig N V} {o' : OutConfig N V'}
    (ho : RelOut σ o o') {x : NewCfg N a k} {x' : NewCfg N a' k}
    (h : RelVal hI hk x x') :
    gaussProd N a' k cs o' x' = gaussProd N a k cs o x := by
  classical
  unfold gaussProd
  refine Fintype.prod_equiv
    (Equiv.subtypeEquiv (σ.eb (k + 1)).symm (fun y' => ?_)) _ _ (fun y' => ?_)
  · constructor
    · intro hy
      rw [← hI.mem_gaussBlocks_iff hk, Equiv.apply_symm_apply]; exact hy
    · intro hy
      have := (hI.mem_gaussBlocks_iff hk ((σ.eb (k + 1)).symm y')).mpr hy
      rwa [Equiv.apply_symm_apply] at this
  · obtain ⟨y', hy'⟩ := y'
    obtain ⟨y, rfl⟩ := (σ.eb (k + 1)).surjective y'
    simp only [Equiv.subtypeEquiv_apply, Equiv.symm_apply_apply]
    rw [ho y, qCoarseK_euclid hk ⟨subCorr_newVars hI hk, h⟩ y]


section Fields

variable {k : ℕ} {A : Set (InternalVars a k)} {A' : Set (InternalVars a' k)}

theorem HistImage.blockSub_omega_iff (hI : HistImage σ a a') {j : ℕ} (hj : j ≤ K) (i : ℕ)
    (y : BlockAt S n M K j) :
    BlockSub (S := S) (n := n) (M := M) (K := K) j (σ.eb j y) (a'.Omega i) ↔
      BlockSub (S := S) (n := n) (M := M) (K := K) j y (a.Omega i) := by
  rw [hI.Omega i]; exact σ.blockSub_image hj y _

theorem subMultiscaleField_euclid {hI : HistImage σ a a'} (hk : k ≤ K)
    {V V' : Set (BlockAt S n M K k)} {o : OutConfig N V} {o' : OutConfig N V'}
    (ho : RelOut σ o o') {x : SubCfg N a k A} {x' : SubCfg N a' k A'}
    (h : RelSub hI hk x x') (j : ℕ) (y : BlockAt S n M K j) :
    subMultiscaleField N a' k V' x' o' j (σ.eb j y) = subMultiscaleField N a k V x o j y := by
  classical
  unfold subMultiscaleField
  by_cases hj : j < k
  · have hjK : j ≤ K := by omega
    simp only [hj, ↓reduceIte]
    have hc : (j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j (σ.eb j y) (a'.Omega (j - 1))) ↔
        (j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j y (a.Omega (j - 1))) := by
      rw [hI.blockSub_omega_iff hjK]
    by_cases hc' : j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j y (a.Omega (j - 1))
    · simp only [hc'.imp_right id, hc.mpr hc', ↓reduceIte]
      exact h.read_large j y
    · simp only [hc', hc.not.mpr hc', ↓reduceIte]
  · simp only [hj, ↓reduceIte]
    by_cases hjk : j = k
    · subst hjk
      simp only [↓reduceDIte]
      have hc : (j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j (σ.eb j y) (a'.Omega (j - 1))) ↔
          (j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j y (a.Omega (j - 1))) := by
        rw [hI.blockSub_omega_iff hk]
      by_cases hc' : j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j y (a.Omega (j - 1))
      · simp only [hc.mpr hc', hc', ↓reduceIte]
        exact ho y
      · simp only [hc.not.mpr hc', hc', ↓reduceIte]
    · simp only [hjk, ↓reduceDIte]

theorem RelSub.read_fluct {hI : HistImage σ a a'} {hk : k ≤ K} {x : SubCfg N a k A}
    {x' : SubCfg N a' k A'} (h : RelSub hI hk x x') (j : ℕ) (y : BlockAt S n M K j) :
    subFluctVarField N x' j (σ.eb j y) = subFluctVarField N x j y := by
  classical
  by_cases hjk : j < k
  · have hj : j ≤ K := hjk.le.trans hk
    have hiff : (∃ (hj : j < k), ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (varSet a j .fluct), mkVar a k j .fluct y hj hb ∈ A) ↔
        (∃ (hj : j < k), ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) j (σ.eb j y)
          (varSet a' j .fluct), mkVar a' k j .fluct (σ.eb j y) hj hb ∈ A') := by
      constructor
      · rintro ⟨hj', hb, hm⟩
        have hb' : BlockSub (S := S) (n := n) (M := M) (K := K) j (σ.eb j y) (varSet a' j .fluct) := by
          rw [hI.varSet]; exact (σ.blockSub_image hj _ _).mpr hb
        exact ⟨hj', hb', (h.1 _).mp hm⟩
      · rintro ⟨hj', hb', hm⟩
        have hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y (varSet a j .fluct) := by
          rw [hI.varSet] at hb'; exact (σ.blockSub_image hj _ _).mp hb'
        exact ⟨hj', hb, (h.1 (mkVar a k j .fluct y hj' hb)).mpr hm⟩
    unfold subFluctVarField
    by_cases hP : ∃ (hj : j < k), ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (varSet a j .fluct), mkVar a k j .fluct y hj hb ∈ A
    · have hP' := hiff.mp hP
      simp only [hP, hP', ↓reduceDIte]
      exact h.2 (mkVar a k j .fluct y hP.1 hP.2.1) hP.2.2 hP'.2.2
    · have hP' : ¬ (∃ (hj : j < k), ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) j (σ.eb j y)
          (varSet a' j .fluct), mkVar a' k j .fluct (σ.eb j y) hj hb ∈ A') := fun h' => hP (hiff.mpr h')
      simp only [hP, hP', ↓reduceDIte]
  · unfold subFluctVarField
    have h1 : ¬ ∃ (hj : j < k), ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (varSet a j .fluct), mkVar a k j .fluct y hj hb ∈ A := fun ⟨hj, _⟩ => hjk hj
    have h2 : ¬ ∃ (hj : j < k), ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) j (σ.eb j y)
          (varSet a' j .fluct), mkVar a' k j .fluct (σ.eb j y) hj hb ∈ A' := fun ⟨hj, _⟩ => hjk hj
    simp only [h1, h2, ↓reduceDIte]


theorem subFluctField_euclid {hI : HistImage σ a a'} (hk : k ≤ K)
    {x : SubCfg N a k A} {x' : SubCfg N a' k A'}
    (h : RelSub hI hk x x') (j : ℕ) (y : BlockAt S n M K j) :
    subFluctField N a' k x' j (σ.eb j y) = subFluctField N a k x j y := by
  exact h.read_fluct j y

end Fields

end Lay1
end Balaban.LargeField
