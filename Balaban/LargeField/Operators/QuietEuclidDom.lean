module

public import Balaban.LargeField.Region.SymmLat
public import Balaban.LargeField.Region.SymmLevel
public import Balaban.LargeField.Operators.QuietSymmEuclid
public import Balaban.LargeField.Operators.Quiet
import Mathlib.Tactic.Ring

/-!
# Lattice covariance of the domain conditions (`χ^new`, `Ω^{∼r}`)

For a lattice symmetry `σ` and corresponding localized histories (`HistImage σ a a'`):

* the cube sets `Ω^{∼r}_j`, `(Ω^c_j)^{∼r}`, `lhOmegaSim` and the sets `quietA1`-`quietA4` of the quiet
  kernel correspond under the cube actions `σ.ec j` (`HistImage.omegaNb_eq`, ...);
* the conditions `Ψ̃(Y; δ)` of the domain are covariant (`psiTilde_image`), the block sets
  `genBlocksIn`, `scaleBlocksIn` correspond (`genBlocksIn_image`, `scaleBlocksIn_image`);
* hence `χ^new_k` is covariant (`chiNew_euclid`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory

section Sets

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]
  (σ : TorusSym S n M K)

theorem TorusSym.fineSet_image {j : ℕ} (hj : j ≤ K) (A : Set (Torus S.d (n j))) :
    σ.ef '' fineSet (S := S) (n := n) M K j A = fineSet (S := S) (n := n) M K j (σ.ec j '' A) := by
  ext x'
  obtain ⟨x, rfl⟩ := σ.ef.surjective x'
  rw [(σ.ef.injective).mem_set_image]
  show _ ∈ fineSet M K j A ↔ cubeMap n S.L M K j (σ.ef x) ∈ σ.ec j '' A
  rw [σ.cube j hj, (σ.ec j).injective.mem_set_image]
  rfl

variable {σ} {a a' : LocalHistory S n M K}

theorem TorusSym.cubeSet_eq {j : ℕ} (hj : j ≤ K)
    (B : Set (Torus S.d (M * n K * S.L ^ K))) :
    {y | CubeSub (S := S) (n := n) M K j y (σ.ef '' B)} =
      σ.ec j '' {y | CubeSub (S := S) (n := n) M K j y B} := by
  ext y'
  obtain ⟨y, rfl⟩ := (σ.ec j).surjective y'
  rw [(σ.ec j).injective.mem_set_image]
  exact σ.cubeSub_image hj y B

theorem HistImage.lhOmegaNb_eq (hI : HistImage σ a a') (k r : ℕ) {j : ℕ} (hj : j ≤ K) :
    lhOmegaNb a' k r j = σ.ec j '' lhOmegaNb a k r j := by
  unfold lhOmegaNb
  split_ifs with h
  · simp
  · rw [hI.lhOmega_eq, σ.cubeSet_eq hj, σ.nbhd_image]

theorem HistImage.omegaNb_eq (hI : HistImage σ a a') (k r : ℕ) {j : ℕ} (hj : j ≤ K) :
    omegaNb a' k r j = σ.ec j '' omegaNb a k r j := by
  unfold omegaNb
  split_ifs with h
  · simp
  · rw [hI.Omega, σ.cubeSet_eq hj, σ.nbhd_image]

theorem HistImage.omegaCNb_eq (hI : HistImage σ a a') (r : ℕ) {j : ℕ} (hj : j ≤ K) :
    omegaCNb a' r j = σ.ec j '' omegaCNb a r j := by
  unfold omegaCNb
  rw [hI.Z, hI.Omega, ← Set.image_sdiff σ.ef.injective, σ.cubeSet_eq hj, σ.nbhd_image]

end Sets

section Quiet

theorem cubeFin_image {S : Setting} {m : ℕ} [NeZero m] (e : Equiv.Perm (Torus S.d m))
    (A : Set (Torus S.d m)) :
    cubeFin (S := S) (e '' A) = (cubeFin (S := S) A).map e.toEmbedding := by
  classical
  ext y
  simp only [cubeFin, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv,
    Set.mem_image_equiv]

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]
  (σ : LatTorusSym S n M K) {a a' : LocalHistory S n M K}
  (hI : HistImage σ.toTorusSym a a') (hnn : ∀ i, i < K → n i = S.L * n (i + 1))
include hI hnn

theorem HistImage.quietA1_eq {k : ℕ} (hk : k + 1 ≤ K) :
    quietA1 a' k = σ.ec k '' quietA1 a k := by
  ext y'
  obtain ⟨y, rfl⟩ := (σ.ec k).surjective y'
  rw [(σ.ec k).injective.mem_set_image]
  show (CubeSub (S := S) (n := n) M K k (σ.ec k y) (a'.Z (k + 1) \ a'.Z k) ∧
      blockMap S.L (n (k + 1)) (σ.ec k y) ∉ omegaNb a' (k + 1) 3 (k + 1)) ↔
    CubeSub (S := S) (n := n) M K k y (a.Z (k + 1) \ a.Z k) ∧
      blockMap S.L (n (k + 1)) y ∉ omegaNb a (k + 1) 3 (k + 1)
  rw [hI.Z, hI.Z, ← Set.image_sdiff σ.ef.injective, σ.cubeSub_image (by omega),
    ← σ.ec_blockMap hnn hk, hI.omegaNb_eq _ _ hk, (σ.ec (k + 1)).injective.mem_set_image]

theorem HistImage.quietA2_eq {k : ℕ} (hk : k + 1 ≤ K) :
    quietA2 a' k = σ.ec (k + 1) '' quietA2 a k := by
  ext y'
  obtain ⟨y, rfl⟩ := (σ.ec (k + 1)).surjective y'
  rw [(σ.ec (k + 1)).injective.mem_set_image]
  show (CubeSub (S := S) (n := n) M K (k + 1) (σ.ec (k + 1) y) (a'.Z (k + 1) \ a'.Omega k) ∧
      σ.ec (k + 1) y ∈ omegaNb a' (k + 1) 3 (k + 1)) ↔
    CubeSub (S := S) (n := n) M K (k + 1) y (a.Z (k + 1) \ a.Omega k) ∧
      y ∈ omegaNb a (k + 1) 3 (k + 1)
  rw [hI.Z, hI.Omega, ← Set.image_sdiff σ.ef.injective, σ.cubeSub_image hk,
    hI.omegaNb_eq _ _ hk, (σ.ec (k + 1)).injective.mem_set_image]

theorem HistImage.quietA3_eq {k : ℕ} (hk : k + 1 ≤ K) :
    quietA3 a' k = σ.ec (k + 1) '' quietA3 a k := by
  ext y'
  obtain ⟨y, rfl⟩ := (σ.ec (k + 1)).surjective y'
  rw [(σ.ec (k + 1)).injective.mem_set_image]
  show (CubeSub (S := S) (n := n) M K (k + 1) (σ.ec (k + 1) y) (a'.Omega k) ∧
      σ.ec (k + 1) y ∈ omegaCNb a' 3 (k + 1)) ↔
    CubeSub (S := S) (n := n) M K (k + 1) y (a.Omega k) ∧ y ∈ omegaCNb a 3 (k + 1)
  rw [hI.Omega, σ.cubeSub_image hk, hI.omegaCNb_eq _ hk, (σ.ec (k + 1)).injective.mem_set_image]

theorem HistImage.quietA4_eq {k : ℕ} (hk : k + 1 ≤ K) :
    quietA4 a' k = σ.ec (k + 1) '' quietA4 a k := by
  ext y'
  obtain ⟨y, rfl⟩ := (σ.ec (k + 1)).surjective y'
  rw [(σ.ec (k + 1)).injective.mem_set_image]
  show (CubeSub (S := S) (n := n) M K (k + 1) (σ.ec (k + 1) y) (a'.Z (k + 1)) ∧
      σ.ec (k + 1) y ∉ omegaCNb a' 3 (k + 1)) ↔
    CubeSub (S := S) (n := n) M K (k + 1) y (a.Z (k + 1)) ∧ y ∉ omegaCNb a 3 (k + 1)
  rw [hI.Z, σ.cubeSub_image hk, hI.omegaCNb_eq _ hk, (σ.ec (k + 1)).injective.mem_set_image]

end Quiet


section Adjacency

variable {d L N₀ k : ℕ} [NeZero L] [NeZero N₀]

theorem AffIso.adj_iff (A : AffIso d (N₀ * L ^ k)) (x y : Torus d (N₀ * L ^ k)) :
    Adj (A.toFun x) (A.toFun y) ↔ Adj x y := by
  let S := A.nbr
  have hs : ∀ (x : Torus d (N₀ * L ^ k)) (μ : Fin d), A.toFun (x + Pi.single μ 1) =
      if A.flip μ then A.toFun x - Pi.single (A.perm μ) 1 else A.toFun x + Pi.single (A.perm μ) 1 :=
    fun x μ => A.toFun_add_single x μ
  have hss : ∀ (x : Torus d (N₀ * L ^ k)) (μ : Fin d), A.toFun (x - Pi.single μ 1) =
      if A.flip μ then A.toFun x + Pi.single (A.perm μ) 1 else A.toFun x - Pi.single (A.perm μ) 1 :=
    fun x μ => S.step_sub x μ
  have inj := A.toFun_injective
  constructor
  · rintro ⟨ν, h | h⟩
    · obtain ⟨μ, rfl⟩ : ∃ μ, A.perm μ = ν := ⟨A.perm.symm ν, by simp⟩
      by_cases hf : A.flip μ
      · have := hss x μ
        simp only [hf, ↓reduceIte] at this
        have : y = x - Pi.single μ 1 := inj (by rw [h, this])
        exact ⟨μ, Or.inr (by rw [this]; abel)⟩
      · have := hs x μ
        simp only [hf, Bool.false_eq_true, ↓reduceIte] at this
        exact ⟨μ, Or.inl (inj (by rw [h, this]))⟩
    · obtain ⟨μ, rfl⟩ : ∃ μ, A.perm μ = ν := ⟨A.perm.symm ν, by simp⟩
      by_cases hf : A.flip μ
      · have := hss y μ
        simp only [hf, ↓reduceIte] at this
        have : x = y - Pi.single μ 1 := inj (by rw [h, this])
        exact ⟨μ, Or.inl (by rw [this]; abel)⟩
      · have := hs y μ
        simp only [hf, Bool.false_eq_true, ↓reduceIte] at this
        exact ⟨μ, Or.inr (inj (by rw [h, this]))⟩
  · rintro ⟨μ, h | h⟩
    · refine ⟨A.perm μ, ?_⟩
      have := hs x μ
      rw [← h] at this
      by_cases hf : A.flip μ
      · simp only [hf, ↓reduceIte] at this
        right; rw [this]; abel
      · simp only [hf, Bool.false_eq_true, ↓reduceIte] at this
        left; exact this
    · refine ⟨A.perm μ, ?_⟩
      have := hs y μ
      rw [← h] at this
      by_cases hf : A.flip μ
      · simp only [hf, ↓reduceIte] at this
        left; rw [this]; abel
      · simp only [hf, Bool.false_eq_true, ↓reduceIte] at this
        right; exact this

end Adjacency


section Blocks

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {ϱ : ℝ}

/-- The action of a symmetry on the blocks (with their scale). -/
def blockPtMap (σ : TorusSym S n M K) (b : BlockPt S n M K) : BlockPt S n M K :=
  ⟨b.1, σ.eb b.1 b.2⟩

theorem blockPtMap_injective (σ : TorusSym S n M K) : Function.Injective (blockPtMap σ) := by
  rintro ⟨j, y⟩ ⟨j', y'⟩ h
  simp only [blockPtMap] at h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
  have := (σ.eb _).injective (eq_of_heq h2)
  rw [this]

theorem LatTorusSym.adj_iff (σ : LatTorusSym S n M K) (x y : Torus S.d (M * n K * S.L ^ K)) :
    Adj (σ.ef x) (σ.ef y) ↔ Adj x y := by
  rw [σ.ef_aff, σ.ef_aff]
  exact AffIso.adj_iff σ.aff x y

theorem LatTorusSym.blockAdj_iff (σ : LatTorusSym S n M K) {b b' : BlockPt S n M K}
    (hb : b.1 ≤ K) (hb' : b'.1 ≤ K) :
    BlockAdj (blockPtMap σ.toTorusSym b) (blockPtMap σ.toTorusSym b') ↔ BlockAdj b b' := by
  constructor
  · rintro ⟨x, x', hx, hx', hadj⟩
    simp only [blockPtMap] at hx hx'
    refine ⟨σ.ef.symm x, σ.ef.symm x', ?_, ?_, ?_⟩
    · have := σ.jblock b.1 hb (σ.ef.symm x)
      rw [Equiv.apply_symm_apply, hx] at this
      exact (σ.eb b.1).injective this.symm
    · have := σ.jblock b'.1 hb' (σ.ef.symm x')
      rw [Equiv.apply_symm_apply, hx'] at this
      exact (σ.eb b'.1).injective this.symm
    · rw [← σ.adj_iff]; simpa using hadj
  · rintro ⟨x, x', hx, hx', hadj⟩
    refine ⟨σ.ef x, σ.ef x', ?_, ?_, (σ.adj_iff x x').2 hadj⟩
    · show Multiscale.jBlock S.d S.L (M * n K) K b.1 (σ.ef x) = σ.eb b.1 b.2
      rw [σ.jblock b.1 hb, hx]
    · show Multiscale.jBlock S.d S.L (M * n K) K b'.1 (σ.ef x') = σ.eb b'.1 b'.2
      rw [σ.jblock b'.1 hb', hx']

theorem psiTilde_image (σ : LatTorusSym S n M K) (ψ ψ' : MultiField S n M K N)
    (hψ : ∀ j y, ψ' j (σ.eb j y) = ψ j y) {Y : Set (BlockPt S n M K)} (hY : ∀ b ∈ Y, b.1 ≤ K)
    (δ : ℝ) : PsiTildeMulti ψ' (blockPtMap σ.toTorusSym '' Y) δ ↔ PsiTildeMulti ψ Y δ := by
  unfold PsiTildeMulti
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun b hb b' hb' hl hadj => ?_, fun b hb => ?_⟩
    · have := h1 (blockPtMap σ.toTorusSym b) ⟨b, hb, rfl⟩ (blockPtMap σ.toTorusSym b')
        ⟨b', hb', rfl⟩ hl ((σ.blockAdj_iff (hY b hb) (hY b' hb')).2 hadj)
      simpa [blockPtMap, hψ] using this
    · have := h2 (blockPtMap σ.toTorusSym b) ⟨b, hb, rfl⟩
      simpa [blockPtMap, hψ] using this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩ hl hadj
      have := h1 b hb b' hb' hl ((σ.blockAdj_iff (hY b hb) (hY b' hb')).1 hadj)
      simpa [blockPtMap, hψ] using this
    · rintro _ ⟨b, hb, rfl⟩
      have := h2 b hb
      simpa [blockPtMap, hψ] using this

end Blocks


section GenBlocks

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {ϱ : ℝ} (σ : LatTorusSym S n M K)
  {B B' : GeneratingSet S.d S.L (M * n K) K ϱ}
  (hB : ∀ j, B'.Ω j = (B.Ω j).map σ.ef.toEmbedding)
include hB

theorem LatTorusSym.mem_layer_iff (j : ℕ) (x : Torus S.d (M * n K * S.L ^ K)) :
    σ.ef x ∈ B'.layer j ↔ x ∈ B.layer j := by
  rw [GeneratingSet.mem_layer, GeneratingSet.mem_layer, hB j, hB (j + 1), Finset.mem_map_equiv,
    Finset.mem_map_equiv, Equiv.symm_apply_apply]

theorem genBlocksIn_image {j' : ℕ} (hj' : j' ≤ K) (W : Set (Torus S.d (n j'))) :
    genBlocksIn B' j' (σ.ec j' '' W) = blockPtMap σ.toTorusSym '' genBlocksIn B j' W := by
  ext ⟨j, y'⟩
  constructor
  · rintro ⟨h1, hK, x', hx', hjb, hc⟩
    obtain ⟨x, rfl⟩ := σ.ef.surjective x'
    refine ⟨⟨j, Multiscale.jBlock S.d S.L (M * n K) K j x⟩, ⟨h1, hK, x,
      (σ.mem_layer_iff hB j x).1 hx', rfl, ?_⟩, ?_⟩
    · rw [σ.cube j' hj', (σ.ec j').injective.mem_set_image] at hc
      exact hc
    · simp only [blockPtMap]
      rw [← σ.jblock j hK, hjb]
  · rintro ⟨⟨j0, y0⟩, ⟨h1, hK, x, hx, hjb, hc⟩, h⟩
    simp only [blockPtMap] at h
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
    have h2 := eq_of_heq h2
    refine ⟨h1, hK, σ.ef x, (σ.mem_layer_iff hB _ x).2 hx, ?_, ?_⟩
    · show Multiscale.jBlock S.d S.L (M * n K) K j0 (σ.ef x) = y'
      rw [σ.jblock j0 hK, hjb, h2]
    · rw [σ.cube j' hj']
      exact ⟨_, hc, rfl⟩

theorem scaleBlocksIn_image {j : ℕ} (hj : j ≤ K) (W : Set (Torus S.d (n j))) :
    scaleBlocksIn (S := S) (n := n) (M := M) (K := K) j (σ.ec j '' W) =
      blockPtMap σ.toTorusSym '' scaleBlocksIn j W := by
  ext ⟨j0, y'⟩
  constructor
  · rintro ⟨y1, h1, x', hjb, hc⟩
    obtain ⟨x, rfl⟩ := σ.ef.surjective x'
    obtain ⟨rfl, h1'⟩ := Sigma.mk.inj_iff.mp h1
    have h1' := eq_of_heq h1'
    refine ⟨⟨j0, Multiscale.jBlock S.d S.L (M * n K) K j0 x⟩, ⟨_, rfl, x, rfl, ?_⟩, ?_⟩
    · rw [σ.cube j0 hj, (σ.ec j0).injective.mem_set_image] at hc
      exact hc
    · simp only [blockPtMap]
      rw [h1', ← hjb, ← σ.jblock j0 hj]
  · rintro ⟨⟨j1, y1⟩, ⟨y2, h1, x, hjb, hc⟩, h⟩
    simp only [blockPtMap] at h
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
    have h2 := eq_of_heq h2
    obtain ⟨rfl, h1'⟩ := Sigma.mk.inj_iff.mp h1
    have h1' := eq_of_heq h1'
    refine ⟨y', rfl, σ.ef x, ?_, ?_⟩
    · show Multiscale.jBlock S.d S.L (M * n K) K j1 (σ.ef x) = y'
      rw [σ.jblock j1 hj, hjb, ← h2, h1']
    · rw [σ.cube j1 hj]
      exact ⟨_, hc, rfl⟩

end GenBlocks


theorem forall_perm_iff {α : Type*} (e : Equiv.Perm α) {Q P : α → Prop}
    (h : ∀ y, Q (e y) ↔ P y) : (∀ y', Q y') ↔ ∀ y, P y := by
  constructor
  · intro H y; exact (h y).1 (H (e y))
  · intro H y'
    obtain ⟨y, rfl⟩ := e.surjective y'
    exact (h y).2 (H y)

section ChiNew

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {ϱ : ℝ} (σ : LatTorusSym S n M K) {a a' : LocalHistory S n M K}
  (hI : HistImage σ.toTorusSym a a') {B B' : GeneratingSet S.d S.L (M * n K) K ϱ}
  (hB : ∀ j, B'.Ω j = (B.Ω j).map σ.ef.toEmbedding)
  {Zc Zc' : Set (Torus S.d (M * n K * S.L ^ K))} (hZ : Zc' = σ.ef '' Zc)
  {k : ℕ} (hk : k + 1 ≤ K) (δ p0 : ℕ → ℝ) (Cpsi : ℝ)
  {ψ ψ' φ φ' : MultiField S n M K N}
  (hψ : ∀ j y, ψ' j (σ.eb j y) = ψ j y) (hφ : ∀ j y, φ' j (σ.eb j y) = φ j y)

theorem cubeMap_ef_eq_iff {j : ℕ} (hj : j ≤ K) (x : Torus S.d (M * n K * S.L ^ K))
    (y : Torus S.d (n j)) :
    cubeMap n S.L M K j (σ.ef x) = σ.ec j y ↔ cubeMap n S.L M K j x = y := by
  rw [σ.cube j hj, (σ.ec j).injective.eq_iff]

include hI hB hZ hk hψ hφ

/-- **Covariance of the conditions of `χ^new_k`.** -/
theorem chiNewProp_iff :
    ChiNewProp a' k B' Zc' δ p0 Cpsi ψ' φ' ↔ ChiNewProp a k B Zc δ p0 Cpsi ψ φ := by
  subst hZ
  unfold ChiNewProp
  refine and_congr ?_ (and_congr ?_ ?_)
  · refine forall_perm_iff (σ.ec (k + 1)) (fun y => ?_)
    unfold lhOmegaSim
    rw [hI.Z, σ.cubeSub_image hk, hI.lhOmegaNb_eq _ _ hk, (σ.ec (k + 1)).injective.mem_set_image]
    refine imp_congr_right fun _ => imp_congr_right fun _ => ?_
    rw [← Set.image_singleton (f := σ.ec (k + 1)), σ.nbhd_image, genBlocksIn_image σ hB hk]
    exact psiTilde_image σ ψ ψ' hψ (fun b hb => hb.2.1) _
  · refine forall_congr' fun j => imp_congr_right fun hj1 => imp_congr_right fun hj => ?_
    have hjK : j ≤ K := by omega
    refine forall_perm_iff (σ.ec j) (fun y => ?_)
    rw [σ.cubeSub_image hjK]
    refine imp_congr_right fun _ => ?_
    have h1 : (∀ x', cubeMap n S.L M K j x' = σ.ec j y → x' ∉ a'.Z j) ↔
        (∀ x, cubeMap n S.L M K j x = y → x ∉ a.Z j) := by
      rw [hI.Z]
      refine forall_perm_iff σ.ef (fun x => ?_)
      rw [cubeMap_ef_eq_iff σ hjK, σ.ef.injective.mem_set_image]
    rw [h1]
    refine imp_congr_right fun _ => ?_
    have h2 : (∀ x', cubeMap n S.L M K j x' = σ.ec j y →
        cubeMap n S.L M K (j + 1) x' ∉ lhOmegaSim a' (k + 1) (j + 1)) ↔
        (∀ x, cubeMap n S.L M K j x = y →
        cubeMap n S.L M K (j + 1) x ∉ lhOmegaSim a (k + 1) (j + 1)) := by
      rcases hj with rfl | rfl
      · unfold lhOmegaSim
        refine forall_perm_iff σ.ef (fun x => ?_)
        rw [cubeMap_ef_eq_iff σ hjK, σ.cube _ hk, hI.lhOmegaNb_eq _ _ hk,
          (σ.ec _).injective.mem_set_image]
      · have e1 : ∀ (b : LocalHistory S n M K) (x : Torus S.d (M * n K * S.L ^ K)),
            cubeMap n S.L M K (k + 1 + 1) x ∉ lhOmegaSim b (k + 1) (k + 1 + 1) := by
          intro b x
          simp [lhOmegaSim, lhOmegaNb]
        exact ⟨fun _ x _ => e1 a x, fun _ x' _ => e1 a' x'⟩
    rw [h2]
    have h3 : scaleBlocksIn (S := S) (n := n) (M := M) (K := K) j (nbhd 1 {σ.ec j y}) =
        blockPtMap σ.toTorusSym '' scaleBlocksIn j (nbhd 1 {y}) := by
      have e : ({σ.ec j y} : Set (Torus S.d (n j))) = σ.ec j '' {y} := Set.image_singleton.symm
      rw [e, σ.nbhd_image]
      exact scaleBlocksIn_image σ hB hjK _
    rw [h3]
    refine imp_congr_right fun _ => ?_
    exact psiTilde_image σ ψ ψ' hψ (fun b hb => by obtain ⟨y0, hb, _⟩ := hb; rw [hb]; exact hjK) _
  · refine forall_perm_iff (σ.eb k) (fun y => ?_)
    rw [hI.Omega, hI.OmegaDD, ← Set.image_sdiff σ.ef.injective, σ.blockSub_image (by omega),
      hφ]

/-- **Covariance of `χ^new_k`.** -/
theorem chiNew_euclid :
    chiNew a' k B' Zc' δ p0 Cpsi (ψ', φ') = chiNew a k B Zc δ p0 Cpsi (ψ, φ) :=
  charFn_congr_apply (chiNewProp_iff σ hI hB hZ hk δ p0 Cpsi hψ hφ)

end ChiNew

end Balaban.LargeField
