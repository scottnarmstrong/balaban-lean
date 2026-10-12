module

public import Balaban.LargeField.R.WindowRegSetBond
public import Balaban.LargeField.R.WindowRegSetPath
public import Balaban.LargeField.R.WindowRegSet
import Mathlib.Tactic.Linarith

/-!
# The bond bound on the regularity set of the actual window (COLLAR-FIX §2, inner face)

## T1: dictionary between the window and `ChiDomProp`

* `ChiDomProp a k B Zc δ p0 Cpsi ψ ψ'` (`Characteristic/OperatorDomain.lean`) lives on the *horizon torus*
  `Torus d (M n_K L^K)`: `a : LocalHistory S n M K`, `B : GeneratingSet d L (M n_K) K ϱ`,
  `ψ : MultiField S n M K N`, `BlockAt S n M K q = Torus d (M n_K L^(K-q))`.
* The window `windowOfHistory H Z g hkK hW` lives on the `k`-torus `Torus d (M n_k L^k)`
  (`GeneratingSet d L (M n_k) k (winSep g)`), as do `regSetT`, `regSetTExt`
  (`BlockAt S n M k q`), `H.locFine Z M q` and `H.locGen Z M hkK`.
* The landed `RegionHistory.localHistory H M K k Z` takes the horizon `K` as an *explicit* argument
  (`fineSet M K j`), independently of the horizon of `H`.  Taking `K := k` gives
  `a = H.localHistory M k k Z : LocalHistory S n M k` on exactly the window's torus.  So the
  mismatch is case (b): at the window's own horizon the two tori coincide **definitionally**; there
  is no cast and no `torusCast` (the history-horizon `K` of `H`, `k ≤ K`, enters only through the
  record `H.locRH k Z`, which stops at `k`).  The transport to a larger horizon `K > k` is not needed
  for the window and is not stated.
* `BlockV d L (M n_k) k` (the block type of the collar files) and `BlockPt S n M k` are both
  `Σ j, Torus d (M n_k L^(k-j))`; `windowFieldOfMulti` is the curried-to-uncurried map
  `ψ ↦ fun b => ψ b.1 b.2`, a definitional identity on values.

## Results

* `regCubes_cubeSub`, `regCubes_mem_lhOmegaSim` (T2): the two conditions of the first clause of
  `ChiDomProp` for a cube of `regCubes`;
* `windowFieldOfMulti` (T3);
* `windowOfHistory_hTband_of_chiDom` (T4, T5): the bond bound for `y ∈ regSetT` and any block `y'`
  adjacent to `y` (in particular every `y' ∈ regSetTExt`), for the layer-`k₁` blocks of the window
  generating set `𝔹_k`.  The bond bound is a statement about blocks of `𝔹_k` (`genBlocksIn`), so the two
  blocks are premised to be blocks of the layer `k₁` of `𝔹_k` (`IsLayerBlock`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background Finset RegionHistory

section Field

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M k N : ℕ}

/-- **T3.** The multiscale field `ψ : MultiField S n M k N` as a function on the blocks `BlockV` of the
window torus (the type of the collar files); the two block types are definitionally equal. -/
def windowFieldOfMulti (ψ : MultiField S n M k N) :
    BlockV S.d S.L (M * n k) k → EuclideanSpace ℝ (Fin N) :=
  fun b => ψ b.1 b.2

@[simp] theorem windowFieldOfMulti_apply (ψ : MultiField S n M k N) (q : ℕ)
    (b : BlockAt S n M k q) : windowFieldOfMulti ψ ⟨q, b⟩ = ψ q b := rfl

end Field

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) {k : ℕ} (Z : H.Comp k) {M : ℕ} [NeZero M] [NeZero S.L]

/-- **T2, first condition.**  Every cube of `regCubes` at scale `q ≤ k` lies in `Z_q` of the localized
history at the window's horizon `k`. -/
theorem regCubes_cubeSub (hkK : k ≤ K) {q : ℕ} (hqk : q ≤ k) {y : Torus S.d (n q)}
    (hy : y ∈ regCubes H Z q) :
    CubeSub (S := S) (n := n) M k q y ((H.localHistory M k k Z).Z q) := by
  rw [regCubes_eq] at hy
  intro x hx
  have hxq : x ∈ H.locFine Z M q := by rw [mem_locFine, hx]; exact hy.1
  refine ⟨hxq, ?_⟩
  exact (mem_locFine_k hkK).1 (locFine_mono hkK hqk le_rfl hxq)

/-- **T2, second condition.**  Every cube of `regCubes` at scale `q` with `1 ≤ q ≤ k` lies in
`Ω^∼_q` of the localized history. -/
theorem regCubes_mem_lhOmegaSim (hkK : k ≤ K) {q : ℕ} (hq1 : 1 ≤ q) (hqk : q ≤ k)
    {y : Torus S.d (n q)} (hy : y ∈ regCubes H Z q) :
    y ∈ lhOmegaSim (H.localHistory M k k Z) k q := by
  have hcs := regCubes_cubeSub H Z hkK hqk hy (M := M)
  rw [regCubes_eq] at hy
  unfold lhOmegaSim lhOmegaNb
  have hne : q ≠ k + 1 := by omega
  simp only [hne, ↓reduceIte]
  refine subset_nbhd _ _ ?_
  intro x hx
  obtain ⟨i, rfl⟩ : ∃ i, q = i + 1 := ⟨q - 1, by omega⟩
  refine Or.inl ⟨?_, (hcs x hx).2⟩
  show cubeMap n S.L M k (i + 1) x ∈ ((H.locRH k Z).step i).Omega
  rw [hx]; exact hy.2

end RegionHistory

section Bond

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M k : ℕ} [NeZero M] [NeZero S.L]

/-- `y` is a block of the layer `q` of the generating set `B` (it contains a site of the layer). -/
def IsLayerBlock {ϱ : ℝ} (B : GeneratingSet S.d S.L (M * n k) k ϱ) (q : ℕ)
    (b : BlockAt S n M k q) : Prop :=
  ∃ x ∈ B.layer q, jBlock S.d S.L (M * n k) k q x = b

/-- Adjacent `q`-blocks have cubes at index distance `≤ 1`. -/
theorem blockCube_mem_nbhd_of_adjT (hnn : ∀ i, i < k → n i = S.L * n (i + 1)) {q : ℕ} (hqk : q ≤ k)
    {b b' : BlockAt S n M k q} (h : AdjT b b') :
    blockCube S n M k q b' ∈ nbhd 1 {blockCube S n M k q b} := by
  obtain ⟨x, x', hx, hx', hadj⟩ := blockAdj_of_adjT (M := M) (K := k) hqk h
  have e1 := cubeMap_jBlock hnn hqk x
  have e2 := cubeMap_jBlock hnn hqk x'
  have hx1 : jBlock S.d S.L (M * n k) k q x = b := hx
  have hx2 : jBlock S.d S.L (M * n k) k q x' = b' := hx'
  rw [hx1] at e1
  rw [hx2] at e2
  refine mem_nbhd.2 ⟨_, rfl, ?_⟩
  rw [e1, e2, supDist_comm]
  exact cubeMap_adj hnn hqk hadj

end Bond

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) {k : ℕ} (Z : H.Comp k) {M : ℕ} [NeZero M] [NeZero S.L]

/-- **The bond bound on `T`, for any generating set `B` of the window torus** (Definition II.3.4 (1.24)
at `j = q - 1`, Lemma III.4.5; COLLAR-FIX §2): if the configuration lies in the support of the
retained domain indicator at the history `a = H.localHistory M k k Z`, then for `y ∈ regSetT` and any
block `y'` adjacent to `y`, both blocks of the layer `q = j + 1` of `B`,
`‖ψ_q(y) - ψ_q(y')‖ ≤ C_reg δ_q`. -/
theorem regSetT_bond_of_chiDom (hkK : k ≤ K) {ϱ : ℝ}
    (B : GeneratingSet S.d S.L (M * n k) k ϱ) {N : ℕ} (Zc : Set (Torus S.d (M * n k * S.L ^ k)))
    (δ p0 : ℕ → ℝ) (Cpsi : ℝ) (ψ ψ' : MultiField S n M k N)
    (hdom : ChiDomProp (H.localHistory M k k Z) k B Zc δ p0 Cpsi ψ ψ') {j : ℕ} (hjk : j + 1 ≤ k)
    {ε : ℝ} (hδ : IsAdmDelta S.d S.L ε j (j + 1) δ)
    {y y' : BlockAt S n M k (j + 1)} (hy : y ∈ regSetT H Z M (j + 1)) (hly : IsLayerBlock B (j + 1) y)
    (hly' : IsLayerBlock B (j + 1) y') (hadj : AdjT y y') :
    ‖ψ (j + 1) y - ψ (j + 1) y'‖ ≤
      (3 * S.d * S.L * Real.exp ε * (S.L : ℝ) ^ (((S.d : ℝ) - 2) / 2)) * δ (j + 1) := by
  have hnn := hnn_k H hkK
  have hyc : blockCube S n M k (j + 1) y ∈ regCubes H Z (j + 1) := hy
  obtain ⟨x, hxl, hxy⟩ := hly
  obtain ⟨x', hxl', hxy'⟩ := hly'
  refine bond_le_Creg_of_chiDomProp (H.localHistory M k k Z) k B Zc δ p0 Cpsi ψ ψ' hdom
    (by omega) (regCubes_cubeSub H Z hkK hjk hyc) (regCubes_mem_lhOmegaSim H Z hkK (by omega) hjk hyc)
    hjk ⟨x, hxl, hxy, ?_⟩ ⟨x', hxl', hxy', ?_⟩ hadj hδ
  · have e := cubeMap_jBlock hnn hjk x
    rw [hxy] at e
    rw [← e]
    exact subset_nbhd _ _ rfl
  · have e := cubeMap_jBlock hnn hjk x'
    rw [hxy'] at e
    rw [← e]
    exact blockCube_mem_nbhd_of_adjT hnn hjk hadj

/-- `regSetT_bond_of_chiDom` at a scale `q` with `1 ≤ q ≤ k` and `IsAdmDelta (q-1) q`. -/
theorem regSetT_bond_of_chiDom_q (hkK : k ≤ K) {ϱ : ℝ}
    (B : GeneratingSet S.d S.L (M * n k) k ϱ) {N : ℕ} (Zc : Set (Torus S.d (M * n k * S.L ^ k)))
    (δ p0 : ℕ → ℝ) (Cpsi : ℝ) (ψ ψ' : MultiField S n M k N)
    (hdom : ChiDomProp (H.localHistory M k k Z) k B Zc δ p0 Cpsi ψ ψ') {q : ℕ} (hq1 : 1 ≤ q)
    (hqk : q ≤ k) {ε : ℝ} (hδ : IsAdmDelta S.d S.L ε (q - 1) q δ)
    {y y' : BlockAt S n M k q} (hy : y ∈ regSetT H Z M q) (hly : IsLayerBlock B q y)
    (hly' : IsLayerBlock B q y') (hadj : AdjT y y') :
    ‖ψ q y - ψ q y'‖ ≤
      (3 * S.d * S.L * Real.exp ε * (S.L : ℝ) ^ (((S.d : ℝ) - 2) / 2)) * δ q := by
  obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hδ
  exact regSetT_bond_of_chiDom H Z hkK B Zc δ p0 Cpsi ψ ψ' hdom hqk hδ hy hly hly' hadj

variable {g : Geo S n R M} (hkK : k ≤ K) (hW : H.RipeWindow k Z)

/-- **T4 / T5.  `hTband` for the actual window** (COLLAR-FIX §2; Definition II.5.6, Lemma III.4.5):
if the configuration `(ψ, ψ')` lies in the support of the retained characteristic functions
(`ChiDomProp` at `a = H.localHistory M k k Z`, `B = 𝔹_k` of the window), then for `y ∈ regSetT` and
`y' ∈ regSetTExt` adjacent, both blocks of the layer `k₁` of `𝔹_k`,
`‖ψ_{k₁}(y) - ψ_{k₁}(y')‖ ≤ C_reg δ_{k₁}`, with `C_reg = 3dL e^ε L^{(d-2)/2}`.

Pairs covered (T5): the proof uses only `y ∈ regSetT` (an interior block, whose cube lies in the
support) and the adjacency `y ~ y'`; the membership `y' ∈ regSetTExt` is not used, so every neighbour
of an interior block is covered (the first exit block, and other interior blocks).  Two exit blocks are
never a pair of this form (`y ∈ regSetT` is interior).  The reversed pair (`y ∈ regSetTExt`,
`y' ∈ regSetT`) follows by `norm_sub_rev` and `AdjT` symmetry (`windowOfHistory_hTband_of_chiDom_symm`). -/
theorem windowOfHistory_hTband_of_chiDom {N : ℕ} (Zc : Set (Torus S.d (M * n k * S.L ^ k)))
    (δ p0 : ℕ → ℝ) (Cpsi : ℝ) (ψ ψ' : MultiField S n M k N)
    (hdom : ChiDomProp (H.localHistory M k k Z) k (windowOfHistory H Z g hkK hW).full Zc δ p0 Cpsi ψ ψ')
    {ε : ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k - 1) (S.k1 k) δ)
    {y y' : BlockAt S n M k (S.k1 k)} (hy : y ∈ regSetT H Z M (S.k1 k))
    (_hy' : y' ∈ regSetTExt H Z M (S.k1 k))
    (hly : IsLayerBlock (windowOfHistory H Z g hkK hW).full (S.k1 k) y)
    (hly' : IsLayerBlock (windowOfHistory H Z g hkK hW).full (S.k1 k) y') (hadj : AdjT y y') :
    ‖windowFieldOfMulti ψ ⟨S.k1 k, y⟩ - windowFieldOfMulti ψ ⟨S.k1 k, y'⟩‖ ≤
      (3 * S.d * S.L * Real.exp ε * (S.L : ℝ) ^ (((S.d : ℝ) - 2) / 2)) * δ (S.k1 k) := by
  exact regSetT_bond_of_chiDom_q H Z hkK _ Zc δ p0 Cpsi ψ ψ' hdom (hW.k1_pos hkK) (k1_le hW) hδ
    hy hly hly' hadj

/-- The reversed pair of `windowOfHistory_hTband_of_chiDom` (`y' ∈ regSetT`, `y` adjacent to it). -/
theorem windowOfHistory_hTband_of_chiDom_symm {N : ℕ} (Zc : Set (Torus S.d (M * n k * S.L ^ k)))
    (δ p0 : ℕ → ℝ) (Cpsi : ℝ) (ψ ψ' : MultiField S n M k N)
    (hdom : ChiDomProp (H.localHistory M k k Z) k (windowOfHistory H Z g hkK hW).full Zc δ p0 Cpsi ψ ψ')
    {ε : ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k - 1) (S.k1 k) δ)
    {y y' : BlockAt S n M k (S.k1 k)} (hy' : y' ∈ regSetT H Z M (S.k1 k))
    (hly : IsLayerBlock (windowOfHistory H Z g hkK hW).full (S.k1 k) y)
    (hly' : IsLayerBlock (windowOfHistory H Z g hkK hW).full (S.k1 k) y') (hadj : AdjT y y') :
    ‖windowFieldOfMulti ψ ⟨S.k1 k, y⟩ - windowFieldOfMulti ψ ⟨S.k1 k, y'⟩‖ ≤
      (3 * S.d * S.L * Real.exp ε * (S.L : ℝ) ^ (((S.d : ℝ) - 2) / 2)) * δ (S.k1 k) := by
  rw [windowFieldOfMulti_apply, windowFieldOfMulti_apply, norm_sub_rev]
  exact regSetT_bond_of_chiDom_q H Z hkK _ Zc δ p0 Cpsi ψ ψ' hdom (hW.k1_pos hkK) (k1_le hW) hδ
    hy' hly' hly (adjT_symm' hadj)

end RegionHistory

end Balaban.LargeField
