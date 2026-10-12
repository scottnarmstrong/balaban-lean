module

public import Balaban.LargeField.Operators.Setup

/-!
# Euclidean symmetries acting on localized histories and their variables

A *Euclidean symmetry* `σ` of the torus that preserves the cubes (`TorusSym`) is a bijection of the
fine sites compatible with the block maps of all scales (`jblock`, `cube`) and with the lattice
metric of the cube tori (`dist`): lattice translations by multiples of the cube side, permutations
of the coordinates and reflections mapping cubes to cubes.  It acts on localized histories (by
the images of their records, `IsImage`), on the blocks (`eb`), hence on the internal variables
(`symVar`) and on the output variables, and on the external field `g`.  Configurations of the
variables of two localized histories `a`, `a' = σ a` correspond if the variable at the image
block has the value of the variable at the block (`RelSub`, `RelOut`, `RelG`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

/-- A Euclidean symmetry of the fine torus preserving the blocks of every scale (up to `K`),
the cubes, and the lattice metric of the cube tori. -/
structure TorusSym (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (M K : ℕ) [NeZero M]
    [NeZero S.L] where
  /-- the action on the sites -/
  ef : Equiv.Perm (Torus S.d (M * n K * S.L ^ K))
  /-- the action on the `j`-blocks -/
  eb : ∀ j, Equiv.Perm (BlockAt S n M K j)
  /-- the action on the cubes of `𝕋_j` -/
  ec : ∀ j, Equiv.Perm (Torus S.d (n j))
  jblock : ∀ j, j ≤ K → ∀ x, Multiscale.jBlock S.d S.L (M * n K) K j (ef x) =
    eb j (Multiscale.jBlock S.d S.L (M * n K) K j x)
  cube : ∀ j, j ≤ K → ∀ x, cubeMap n S.L M K j (ef x) = ec j (cubeMap n S.L M K j x)
  dist : ∀ j (x y : Torus S.d (n j)), supDist (ec j x) (ec j y) = supDist x y

section Sym

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (σ : TorusSym S n M K)

theorem TorusSym.blockSub_image {j : ℕ} (hj : j ≤ K) (y : BlockAt S n M K j)
    (B : Set (Torus S.d (M * n K * S.L ^ K))) :
    BlockSub (S := S) (n := n) (M := M) (K := K) j (σ.eb j y) (σ.ef '' B) ↔
      BlockSub (S := S) (n := n) (M := M) (K := K) j y B := by
  constructor
  · intro h x hx
    obtain ⟨x', hx', e⟩ := h (σ.ef x) (by rw [σ.jblock j hj, hx])
    exact (σ.ef.injective e) ▸ hx'
  · intro h x' hx'
    refine ⟨σ.ef.symm x', h _ ?_, by simp⟩
    have := σ.jblock j hj (σ.ef.symm x')
    rw [Equiv.apply_symm_apply, hx'] at this
    exact (σ.eb j).injective this.symm

theorem TorusSym.cubeSub_image {j : ℕ} (hj : j ≤ K) (y : Torus S.d (n j))
    (B : Set (Torus S.d (M * n K * S.L ^ K))) :
    CubeSub (S := S) (n := n) M K j (σ.ec j y) (σ.ef '' B) ↔ CubeSub (S := S) (n := n) M K j y B := by
  constructor
  · intro h x hx
    obtain ⟨x', hx', e⟩ := h (σ.ef x) (by rw [σ.cube j hj, hx])
    exact (σ.ef.injective e) ▸ hx'
  · intro h x' hx'
    refine ⟨σ.ef.symm x', h _ ?_, by simp⟩
    have := σ.cube j hj (σ.ef.symm x')
    rw [Equiv.apply_symm_apply, hx'] at this
    exact (σ.ec j).injective this.symm

/-- `a'` is the image of the localized history `a` under `σ`. -/
structure HistImage (σ : TorusSym S n M K) (a a' : LocalHistory S n M K) : Prop where
  Z : ∀ j, a'.Z j = σ.ef '' a.Z j
  P : ∀ j, a'.P j = σ.ef '' a.P j
  Q : ∀ j, a'.Q j = σ.ef '' a.Q j
  R : ∀ j, a'.R j = σ.ef '' a.R j
  Sset : ∀ j, a'.Sset j = σ.ef '' a.Sset j
  OmegaPrime : ∀ j, a'.OmegaPrime j = σ.ef '' a.OmegaPrime j
  Omega : ∀ j, a'.Omega j = σ.ef '' a.Omega j
  OmegaDD : ∀ j, a'.OmegaDD j = σ.ef '' a.OmegaDD j

variable {σ} {a a' : LocalHistory S n M K}

theorem HistImage.varSet (hI : HistImage σ a a') (j : ℕ) (κ : VarKind) :
    varSet a' j κ = σ.ef '' varSet a j κ := by
  cases κ with
  | large =>
    show a'.Z (j + 1) \ a'.Omega j = σ.ef '' (a.Z (j + 1) \ a.Omega j)
    rw [hI.Z, hI.Omega, Set.image_sdiff σ.ef.injective]
  | fluct =>
    show a'.Omega j \ a'.OmegaDD j = σ.ef '' (a.Omega j \ a.OmegaDD j)
    rw [hI.Omega, hI.OmegaDD, Set.image_sdiff σ.ef.injective]

variable {k : ℕ}

theorem symVar_mem (hI : HistImage σ a a') (hk : k ≤ K) (p : InternalVars a k) :
    BlockSub (S := S) (n := n) (M := M) (K := K) (↑p.1.1) (σ.eb p.1.1 p.1.2.2)
      (varSet a' (↑p.1.1) p.1.2.1) := by
  have hj : (p.1.1 : ℕ) ≤ K := (Nat.le_of_lt p.1.1.2).trans hk
  rw [hI.varSet]
  exact (σ.blockSub_image hj _ _).mpr p.2

/-- The action of `σ` on the internal variables (`k ≤ K`). -/
def symVar (hI : HistImage σ a a') (hk : k ≤ K) (p : InternalVars a k) :
    InternalVars a' k :=
  ⟨⟨p.1.1, p.1.2.1, σ.eb p.1.1 p.1.2.2⟩, symVar_mem hI hk p⟩

theorem symVar_injective (hI : HistImage σ a a') (hk : k ≤ K) :
    Function.Injective (symVar hI hk) := by
  rintro ⟨⟨j, κ, y⟩, hp⟩ ⟨⟨j', κ', y'⟩, hq⟩ h
  have h' := congrArg Subtype.val h
  change (⟨j, κ, σ.eb j y⟩ : (j : Fin k) × VarKind × BlockAt S n M K j) =
    ⟨j', κ', σ.eb j' y'⟩ at h'
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h'
  obtain ⟨rfl, h3⟩ := Prod.mk.inj (eq_of_heq h2)
  have := (σ.eb _).injective h3
  subst this
  rfl

theorem symVar_surjective (hI : HistImage σ a a') (hk : k ≤ K) :
    Function.Surjective (symVar hI hk) := by
  rintro ⟨⟨j, κ, y⟩, hp⟩
  have hj : (j : ℕ) ≤ K := (Nat.le_of_lt j.2).trans hk
  have hp' : BlockSub (S := S) (n := n) (M := M) (K := K) (↑j) y (σ.ef '' varSet a j κ) := by
    rw [← hI.varSet]; exact hp
  have hy : σ.eb j ((σ.eb j).symm y) = y := by simp
  rw [← hy] at hp'
  refine ⟨⟨⟨j, κ, (σ.eb j).symm y⟩, (σ.blockSub_image hj _ _).mp hp'⟩, ?_⟩
  apply Subtype.ext
  change (⟨j, κ, σ.eb j ((σ.eb j).symm y)⟩ : (j : Fin k) × VarKind × BlockAt S n M K j) = ⟨j, κ, y⟩
  rw [hy]

/-! ### The sets `V` -/

theorem HistImage.zcubes_eq (hI : HistImage σ a a') {j : ℕ} (hj : j ≤ K) :
    Zcubes a' j = σ.ec j '' Zcubes a j := by
  ext y'
  constructor
  · intro h
    refine ⟨(σ.ec j).symm y', ?_, by simp⟩
    show CubeSub (S := S) (n := n) M K j ((σ.ec j).symm y') (a.Z j)
    rw [← σ.cubeSub_image hj]
    have h' : CubeSub (S := S) (n := n) M K j y' (σ.ef '' a.Z j) := by rw [← hI.Z j]; exact h
    simpa using h'
  · rintro ⟨y, hy, rfl⟩
    show CubeSub (S := S) (n := n) M K j (σ.ec j y) (a'.Z j)
    rw [hI.Z j]
    exact (σ.cubeSub_image hj _ _).mpr hy

theorem TorusSym.nbhd_image (j m : ℕ) (X : Set (Torus S.d (n j))) :
    nbhd m (σ.ec j '' X) = σ.ec j '' nbhd m X := by
  ext y'
  rw [mem_nbhd]
  constructor
  · rintro ⟨x', ⟨x, hx, rfl⟩, hd⟩
    refine ⟨(σ.ec j).symm y', mem_nbhd.2 ⟨x, hx, ?_⟩, by simp⟩
    have := σ.dist j ((σ.ec j).symm y') x
    rw [← this]
    simpa using hd
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hd⟩ := mem_nbhd.1 hy
    exact ⟨σ.ec j x, ⟨x, hx, rfl⟩, by rw [σ.dist]; exact hd⟩

theorem TorusSym.thick_image (j r : ℕ) (X : Set (Torus S.d (n j))) :
    thick r (σ.ec j '' X) = σ.ec j '' thick r X := σ.nbhd_image j (r + 1) X

theorem HistImage.vcubes_eq (hI : HistImage σ a a') (R : ℕ → ℝ) {k : ℕ} (hk : k ≤ K) :
    Vcubes R a' k = σ.ec k '' Vcubes R a k := by
  unfold Vcubes
  rw [hI.zcubes_eq hk, σ.thick_image, σ.nbhd_image]

/-- The cube of the image of a block is the image of the cube. -/
theorem TorusSym.blockCube_eb (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {j : ℕ} (hj : j ≤ K)
    (y : BlockAt S n M K j) : blockCube S n M K j (σ.eb j y) = σ.ec j (blockCube S n M K j y) := by
  obtain ⟨x, hx⟩ := exists_site_in_block (S := S) (n := n) (M := M) hj y
  have h1 := cubeMap_jBlock (S := S) (n := n) (M := M) hnn hj x
  have h2 := cubeMap_jBlock (S := S) (n := n) (M := M) hnn hj (σ.ef x)
  rw [σ.jblock j hj, hx] at h2
  rw [h2, σ.cube j hj, ← h1, hx]

theorem HistImage.mem_Vblk (hI : HistImage σ a a') (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (R : ℕ → ℝ)
    {k : ℕ} (hk : k ≤ K) (y : BlockAt S n M K k) :
    σ.eb k y ∈ Vblk R a' k ↔ y ∈ Vblk R a k := by
  show blockCube S n M K k (σ.eb k y) ∈ Vcubes R a' k ↔ blockCube S n M K k y ∈ Vcubes R a k
  rw [σ.blockCube_eb hnn hk, hI.vcubes_eq R hk]
  exact (σ.ec k).injective.mem_set_image

/-! ### Corresponding configurations -/

section Rel

variable {A : Set (InternalVars a k)} {A' : Set (InternalVars a' k)}

/-- The output configurations `o` (of `V`) and `o'` (of `V'`) correspond under `σ`: the variable
at the image block has the value of the variable at the block. -/
def RelOut (σ : TorusSym S n M K) {V V' : Set (BlockAt S n M K k)} (o : OutConfig N V)
    (o' : OutConfig N V') : Prop :=
  ∀ y, outField N o' (σ.eb k y) = outField N o y

/-- The sets of variables `A` of `a` and `A'` of `a' = σ a` correspond under `σ`. -/
def SubCorr (hI : HistImage σ a a') (hk : k ≤ K) (A : Set (InternalVars a k))
    (A' : Set (InternalVars a' k)) : Prop :=
  ∀ p, p ∈ A ↔ symVar hI hk p ∈ A'

/-- The values of the configurations `x` and `x'` correspond under `σ`: the variable at the image
block has the value of the variable at the block. -/
def RelVal (hI : HistImage σ a a') (hk : k ≤ K) (x : SubCfg N a k A) (x' : SubCfg N a' k A') :
    Prop :=
  ∀ (p : InternalVars a k) (hp : p ∈ A) (hp' : symVar hI hk p ∈ A'),
    VarVal.toEuc (x' ⟨symVar hI hk p, hp'⟩) = VarVal.toEuc (x ⟨p, hp⟩)

/-- The internal configurations `x` (of the variables `A` of `a`) and `x'` (of the variables `A'`
of `a' = σ a`) correspond under `σ`: `A'` is the image of `A` and the variable at the image block
has the value of the variable at the block. -/
def RelSub (hI : HistImage σ a a') (hk : k ≤ K) (x : SubCfg N a k A) (x' : SubCfg N a' k A') :
    Prop :=
  SubCorr hI hk A A' ∧ RelVal hI hk x x'

/-- The external fields `g` and `g'` correspond under `σ`: `g'(σ z) = g(z)`. -/
def RelG (σ : TorusSym S n M K) (g g' : GIdx S n M K N → ℂ) : Prop :=
  ∀ z i, g' (σ.ef z, i) = g (z, i)

theorem subCorr_newVars (hI : HistImage σ a a') (hk : k + 1 ≤ K) :
    SubCorr hI hk (newVars a k) (newVars a' k) := fun _ => Iff.rfl

theorem symVar_mkVar (hI : HistImage σ a a') (hk : k ≤ K) (j : ℕ) (κ : VarKind)
    (y : BlockAt S n M K j) (hj : j < k)
    (hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y (varSet a j κ))
    (hb' : BlockSub (S := S) (n := n) (M := M) (K := K) j (σ.eb j y) (varSet a' j κ)) :
    symVar hI hk (mkVar a k j κ y hj hb) = mkVar a' k j κ (σ.eb j y) hj hb' := rfl

theorem RelSub.read_large {hI : HistImage σ a a'} {hk : k ≤ K} {x : SubCfg N a k A}
    {x' : SubCfg N a' k A'} (h : RelSub hI hk x x') (j : ℕ) (y : BlockAt S n M K j) :
    subVarField N x' j (σ.eb j y) = subVarField N x j y := by
  classical
  by_cases hjk : j < k
  · have hj : j ≤ K := hjk.le.trans hk
    have hiff : (∃ (hj : j < k), ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (varSet a j .large), mkVar a k j .large y hj hb ∈ A) ↔
        (∃ (hj : j < k), ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) j (σ.eb j y)
          (varSet a' j .large), mkVar a' k j .large (σ.eb j y) hj hb ∈ A') := by
      constructor
      · rintro ⟨hj', hb, hm⟩
        have hb' : BlockSub (S := S) (n := n) (M := M) (K := K) j (σ.eb j y) (varSet a' j .large) := by
          rw [hI.varSet]; exact (σ.blockSub_image hj _ _).mpr hb
        exact ⟨hj', hb', (h.1 _).mp hm⟩
      · rintro ⟨hj', hb', hm⟩
        have hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y (varSet a j .large) := by
          rw [hI.varSet] at hb'; exact (σ.blockSub_image hj _ _).mp hb'
        exact ⟨hj', hb, (h.1 (mkVar a k j .large y hj' hb)).mpr hm⟩
    unfold subVarField
    by_cases hP : ∃ (hj : j < k), ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (varSet a j .large), mkVar a k j .large y hj hb ∈ A
    · have hP' := hiff.mp hP
      simp only [hP, hP', ↓reduceDIte]
      exact h.2 (mkVar a k j .large y hP.1 hP.2.1) hP.2.2 hP'.2.2
    · have hP' : ¬ (∃ (hj : j < k), ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) j (σ.eb j y)
          (varSet a' j .large), mkVar a' k j .large (σ.eb j y) hj hb ∈ A') := fun h' => hP (hiff.mpr h')
      simp only [hP, hP', ↓reduceDIte]
  · unfold subVarField
    have h1 : ¬ ∃ (hj : j < k), ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (varSet a j .large), mkVar a k j .large y hj hb ∈ A := fun ⟨hj, _⟩ => hjk hj
    have h2 : ¬ ∃ (hj : j < k), ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) j (σ.eb j y)
          (varSet a' j .large), mkVar a' k j .large (σ.eb j y) hj hb ∈ A' := fun ⟨hj, _⟩ => hjk hj
    simp only [h1, h2, ↓reduceDIte]

end Rel

end Sym

end Balaban.LargeField
