module

public import Balaban.Background.Def5
public import Balaban.LargeField.Geometry.Distance
public import Balaban.LargeField.Region.Generating
import Mathlib.Tactic.Linarith

/-!
# Exact factorization of the local background (Part II, Lemma II.2.6)

A generating set `G` is the *union of separated pieces* `Gs i` (`PieceDecomp`): the layers of `G`
are the unions of the layers of the pieces, and the data sites `Ω₁ ∪ C(Ω₁)` of distinct pieces
are at sup-distance `≥ 2` (Lemma II.2.5 (b): `genBoundaryLocal_far`). Then no bond of the torus
joins two pieces, no collar site of a piece lies in another piece, and every block of every
layer lies in one piece, so the Euler-Lagrange system (EL) is block diagonal:

* `isEL_local_iff`: `(φ, α)` solves (EL) for `G` with data `D` iff its restriction to each piece
  solves (EL) for the piece with the restricted data;
* `bgFieldC_local_eq`: whenever the `∃!` branch defining `bgFieldC` for `G` applies, its
  restriction to a piece is `bgFieldC` of the piece with the restricted data.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

set_option linter.unusedSectionVars false

variable {ι : Type*} {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-- The generating set `G` is the union of the pieces `Gs i`, which are separated: the layers
of `G` are the unions of the layers of the pieces and the data sites of distinct pieces are at
sup-distance `≥ 2`. -/
structure PieceDecomp (G : GeneratingSet d L N₀ k ϱ) (Gs : ι → GeneratingSet d L N₀ k ϱ') :
    Prop where
  one_le : 1 ≤ k
  layers : ∀ x n, 1 ≤ n → n ≤ k → (x ∈ G.Ω n ↔ ∃ i, x ∈ (Gs i).Ω n)
  separated : ∀ i j, i ≠ j → ∀ u ∈ dataSites (Gs i), ∀ w ∈ dataSites (Gs j), 2 ≤ supDist u w

/-! ### Adjacency and the lattice Laplacian -/

theorem Adj.supDist_le_one {x y : Torus d (N₀ * L ^ k)} (h : Adj x y) : supDist x y ≤ 1 := by
  have h2 := supDist_le_torusDist x y
  have h3 := Multiscale.Adj.torusDist_le h
  have : (supDist x y : ℝ) ≤ 1 := h2.trans h3
  exact_mod_cast this

theorem latticeLaplacian_eq_zero_of_far {x y : Torus d (N₀ * L ^ k)} (ν : ℝ)
    (h : 2 ≤ supDist x y) : latticeLaplacian d (N₀ * L ^ k) ν x y = 0 := by
  have hne : x ≠ y := fun hxy => by
    rw [hxy, supDist_self] at h; omega
  have hadj : ∀ μ : Fin d, y ≠ x + Pi.single μ 1 ∧ x ≠ y + Pi.single μ 1 := by
    intro μ
    constructor
    · intro hy
      have : Adj x y := ⟨μ, Or.inl hy⟩
      have := Adj.supDist_le_one this
      omega
    · intro hx
      have : Adj x y := ⟨μ, Or.inr hx⟩
      have := Adj.supDist_le_one this
      omega
  simp only [latticeLaplacian, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hne,
    ite_false, smul_zero, zero_sub, Matrix.sum_apply, Matrix.add_apply, Matrix.transpose_apply,
    shiftMatrix]
  rw [neg_eq_zero]
  refine Finset.sum_eq_zero fun μ _ => ?_
  simp [(hadj μ).1, (hadj μ).2]

/-! ### Pieces: membership, layers, collars -/

section Pieces

variable {G : GeneratingSet d L N₀ k ϱ} {Gs : ι → GeneratingSet d L N₀ k ϱ'}
  (hD : PieceDecomp G Gs)

include hD

theorem PieceDecomp.mem_of_mem {i : ι} {x : Torus d (N₀ * L ^ k)} (h : x ∈ (Gs i).Ω 1) :
    x ∈ G.Ω 1 :=
  (hD.layers x 1 le_rfl hD.one_le).2 ⟨i, h⟩

theorem PieceDecomp.exists_piece {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    ∃ i, x ∈ (Gs i).Ω 1 :=
  (hD.layers x 1 le_rfl hD.one_le).1 hx

theorem PieceDecomp.piece_unique {i j : ι} {x : Torus d (N₀ * L ^ k)} (hi : x ∈ (Gs i).Ω 1)
    (hj : x ∈ (Gs j).Ω 1) : i = j := by
  by_contra hne
  have := hD.separated i j hne x ((mem_dataSites _).2 (Or.inl hi)) x
    ((mem_dataSites _).2 (Or.inl hj))
  rw [supDist_self] at this
  omega

/-- The inclusion `Ω₁(Gs i) ⊆ Ω₁(G)` as a map of subtypes. -/
def PieceDecomp.incl (i : ι) (x : (Gs i).Ω 1) : G.Ω 1 := ⟨x.1, hD.mem_of_mem x.2⟩

theorem PieceDecomp.incl_injective (i : ι) : Function.Injective (hD.incl i) := by
  intro x y h
  have := congrArg Subtype.val h
  exact Subtype.ext this

/-- The layers of `G` and of the piece containing `x` agree at `x`. -/
theorem PieceDecomp.mem_Ω_iff {i : ι} {x : Torus d (N₀ * L ^ k)} (hx : x ∈ (Gs i).Ω 1) {m : ℕ}
    (hm1 : 1 ≤ m) (hmk : m ≤ k + 1) : x ∈ G.Ω m ↔ x ∈ (Gs i).Ω m := by
  by_cases hm : m ≤ k
  · rw [hD.layers x m hm1 hm]
    constructor
    · rintro ⟨j, hj⟩
      have hj1 : x ∈ (Gs j).Ω 1 := (Gs j).Ω_antitone le_rfl hm1 (by omega) hj
      rw [hD.piece_unique hx hj1]
      exact hj
    · exact fun h => ⟨i, h⟩
  · have : m = k + 1 := by omega
    subst this
    rw [G.top, (Gs i).top]

theorem PieceDecomp.mem_layer_iff {i : ι} {x : Torus d (N₀ * L ^ k)} (hx : x ∈ (Gs i).Ω 1)
    {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k) : x ∈ G.layer n ↔ x ∈ (Gs i).layer n := by
  rw [GeneratingSet.mem_layer, GeneratingSet.mem_layer, hD.mem_Ω_iff hx hn1 (by omega),
    hD.mem_Ω_iff hx (by omega : 1 ≤ n + 1) (by omega)]

theorem PieceDecomp.layerIndex_eq {i : ι} {x : Torus d (N₀ * L ^ k)} (hx : x ∈ (Gs i).Ω 1) :
    G.layerIndex x = (Gs i).layerIndex x := by
  obtain ⟨h1, h2, h3⟩ := (Gs i).layerIndex_spec hx
  exact G.layerIndex_eq h1 h2 ((hD.mem_layer_iff hx h1 h2).2 h3)

theorem PieceDecomp.spacing_eq {i : ι} {x : Torus d (N₀ * L ^ k)} (hx : x ∈ (Gs i).Ω 1) :
    G.spacing x = (Gs i).spacing x := by
  unfold GeneratingSet.spacing
  rw [hD.layerIndex_eq hx]

/-- A neighbour of a site of a piece is in `Ω₁(G)` iff it is in the piece. -/
theorem PieceDecomp.adj_mem_iff {i : ι} {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ (Gs i).Ω 1)
    (hadj : Adj x x') : x' ∈ G.Ω 1 ↔ x' ∈ (Gs i).Ω 1 := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := hD.exists_piece h
    by_cases hij : i = j
    · rw [hij]; exact hj
    · exfalso
      have := hD.separated i j hij x ((mem_dataSites _).2 (Or.inl hx)) x'
        ((mem_dataSites _).2 (Or.inl hj))
      have := Adj.supDist_le_one hadj
      omega
  · exact hD.mem_of_mem

theorem PieceDecomp.mem_collar_iff {i : ι} {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ (Gs i).Ω 1)
    (hadj : Adj x x') : x' ∈ collar G ↔ x' ∈ collar (Gs i) := by
  have h1 : x' ∈ collar G ↔ x' ∉ G.Ω 1 := by
    constructor
    · exact fun h => ((mem_collar G).1 h).1
    · exact fun h => mem_collar_of_adj G (hD.mem_of_mem hx) h hadj
  have h2 : x' ∈ collar (Gs i) ↔ x' ∉ (Gs i).Ω 1 := by
    constructor
    · exact fun h => ((mem_collar _).1 h).1
    · exact fun h => mem_collar_of_adj (Gs i) hx h hadj
  rw [h1, h2, hD.adj_mem_iff hx hadj]

end Pieces

/-! ### The operator is block diagonal -/

theorem avgMatrix_apply (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (x y : Torus d (N₀ * L ^ k)) :
    avgMatrix G a x y =
      ∑ j ∈ Icc 1 k, (a j / ((L : ℝ) ^ j) ^ 2) * layerProjMatrix G j x y := by
  simp [avgMatrix, Matrix.sum_apply]

theorem dirichletOperator_apply (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (α : G.Ω 1 → ℂ) (x y : G.Ω 1) :
    dirichletOperator G a ν α x y =
      ((latticeLaplacian d (N₀ * L ^ k) ν x.1 y.1 : ℝ) : ℂ) + ((avgMatrix G a x.1 y.1 : ℝ) : ℂ) +
        (if x = y then α x else 0) := by
  simp [dirichletOperator, Green.restrictOp, fullMatrix, Matrix.diagonal_apply]

section Operator

variable {G : GeneratingSet d L N₀ k ϱ} {Gs : ι → GeneratingSet d L N₀ k ϱ'}
  (hD : PieceDecomp G Gs) (a : ℕ → ℝ) (ν : ℝ)

include hD

theorem PieceDecomp.avgMatrix_eq {i : ι} {x y : Torus d (N₀ * L ^ k)} (hx : x ∈ (Gs i).Ω 1)
    (hy : y ∈ (Gs i).Ω 1) : avgMatrix G a x y = avgMatrix (Gs i) a x y := by
  rw [avgMatrix_apply, avgMatrix_apply]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 hj
  unfold layerProjMatrix
  simp only [hD.mem_layer_iff hx hj1 hjk, hD.mem_layer_iff hy hj1 hjk]

theorem PieceDecomp.avgMatrix_eq_zero {i : ι} {x y : Torus d (N₀ * L ^ k)} (hx : x ∈ (Gs i).Ω 1)
    (hy' : y ∉ (Gs i).Ω 1) : avgMatrix G a x y = 0 := by
  rw [avgMatrix_apply]
  refine Finset.sum_eq_zero fun j hj => ?_
  obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 hj
  unfold layerProjMatrix
  by_cases h : x ∈ G.layer j ∧ y ∈ G.layer j
  · simp only [h, and_self, ite_true]
    unfold blockProjMatrix
    by_cases hb : blockMap (L ^ j) (N₀ * L ^ (k - j)) x = blockMap (L ^ j) (N₀ * L ^ (k - j)) y
    · exfalso
      have hxj := (hD.mem_layer_iff hx hj1 hjk).1 h.1
      have hy2 : y ∈ (Gs i).Ω j :=
        ((Gs i).blockUnion j hj1 hjk x y hb).1 ((GeneratingSet.mem_layer _).1 hxj).1
      exact hy' ((Gs i).Ω_antitone le_rfl hj1 (by omega) hy2)
    · simp [hb]
  · simp [h]

/-- On a piece the operator of `G` is the operator of the piece. -/
theorem PieceDecomp.dirichletOperator_eq (α : G.Ω 1 → ℂ) {i : ι} (x y : (Gs i).Ω 1) :
    dirichletOperator G a ν α (hD.incl i x) (hD.incl i y) =
      dirichletOperator (Gs i) a ν (fun z => α (hD.incl i z)) x y := by
  rw [dirichletOperator_apply, dirichletOperator_apply]
  have e : (hD.incl i x = hD.incl i y) ↔ x = y :=
    ⟨fun h => hD.incl_injective i h, fun h => by rw [h]⟩
  have h1 : avgMatrix G a (hD.incl i x).1 (hD.incl i y).1 = avgMatrix (Gs i) a x.1 y.1 :=
    hD.avgMatrix_eq a x.2 y.2
  simp only [e]
  rw [h1]
  rfl

/-- Between different pieces the operator vanishes. -/
theorem PieceDecomp.dirichletOperator_eq_zero (α : G.Ω 1 → ℂ) {i : ι} (x : (Gs i).Ω 1)
    (y : G.Ω 1) (hy : y.1 ∉ (Gs i).Ω 1) : dirichletOperator G a ν α (hD.incl i x) y = 0 := by
  rw [dirichletOperator_apply]
  obtain ⟨j, hj⟩ := hD.exists_piece y.2
  have hij : i ≠ j := fun h => hy (h ▸ hj)
  have hfar := hD.separated i j hij x.1 ((mem_dataSites _).2 (Or.inl x.2)) y.1
    ((mem_dataSites _).2 (Or.inl hj))
  have h1 := latticeLaplacian_eq_zero_of_far (L := L) (N₀ := N₀) (k := k) ν hfar
  have h2 := hD.avgMatrix_eq_zero a x.2 hy
  have h3 : hD.incl i x ≠ y := fun h => hy (by rw [← h]; exact x.2)
  simp only [PieceDecomp.incl] at h1 h2 h3 ⊢
  simp [h1, h2, h3]

theorem PieceDecomp.mulVec_eq (α : G.Ω 1 → ℂ) (u : G.Ω 1 → ℂ) {i : ι} (x : (Gs i).Ω 1) :
    (dirichletOperator G a ν α *ᵥ u) (hD.incl i x) =
      (dirichletOperator (Gs i) a ν (fun z => α (hD.incl i z)) *ᵥ
        (fun z => u (hD.incl i z))) x := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  have hsub : ∑ y : G.Ω 1, dirichletOperator G a ν α (hD.incl i x) y * u y =
      ∑ y ∈ (Finset.univ : Finset ((Gs i).Ω 1)).image (hD.incl i),
        dirichletOperator G a ν α (hD.incl i x) y * u y := by
    refine (Finset.sum_subset (Finset.subset_univ
      ((Finset.univ : Finset ((Gs i).Ω 1)).image (hD.incl i))) fun y _ hy => ?_).symm
    have : y.1 ∉ (Gs i).Ω 1 := fun h =>
      hy (Finset.mem_image.2 ⟨⟨y.1, h⟩, Finset.mem_univ _, Subtype.ext rfl⟩)
    rw [hD.dirichletOperator_eq_zero a ν α x y this, zero_mul]
  rw [hsub, Finset.sum_image (fun a _ b _ h => hD.incl_injective i h)]
  exact Finset.sum_congr rfl fun y _ => by rw [hD.dirichletOperator_eq a ν α x y]

end Operator

/-! ### Restriction of data and the factorization of (EL) -/

section Data

variable {G : GeneratingSet d L N₀ k ϱ} {Gs : ι → GeneratingSet d L N₀ k ϱ'}
  (hD : PieceDecomp G Gs)

include hD

theorem PieceDecomp.isLayerConstant {β : Type*} {Ψ : Torus d (N₀ * L ^ k) → β}
    (hΨ : IsLayerConstant G Ψ) (i : ι) : IsLayerConstant (Gs i) Ψ := by
  intro n hn1 hnk x hx x' hx'
  have hx1 : x ∈ (Gs i).Ω 1 := (Gs i).layer_subset hn1 hnk hx
  exact hΨ n hn1 hnk x ((hD.mem_layer_iff hx1 hn1 hnk).2 hx) x'
    (GeneratingSet.mem_blk.2 (GeneratingSet.mem_blk.1 hx'))

/-- The restriction of data for `G` to the piece `Gs i` (clipped to the data sites of the piece). -/
noncomputable def PieceDecomp.restrict (i : ι) (D : BgData G N) : BgData (Gs i) N :=
  BgData.clip (Gs i) D.Ψ D.h (hD.isLayerConstant D.Ψ_layerConst i)
    (hD.isLayerConstant D.h_layerConst i)

theorem PieceDecomp.restrict_Ψ (i : ι) (D : BgData G N) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ dataSites (Gs i)) : (hD.restrict i D).Ψ x = D.Ψ x := by
  classical
  simp [PieceDecomp.restrict, BgData.clip, hx]

theorem PieceDecomp.restrict_h (i : ι) (D : BgData G N) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ (Gs i).Ω 1) : (hD.restrict i D).h x = D.h x := by
  classical
  simp [PieceDecomp.restrict, BgData.clip, hx]

theorem PieceDecomp.boundaryTerm_eq (D : BgData G N) {i : ι} (x : (Gs i).Ω 1) (l : Fin N) :
    boundaryTerm G D.Ψ (hD.incl i x, l) = boundaryTerm (Gs i) (hD.restrict i D).Ψ (x, l) := by
  unfold boundaryTerm
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h1 : Adj x.1 (x.1 + Pi.single μ 1) := ⟨μ, Or.inl rfl⟩
  have h2 : Adj x.1 (x.1 - Pi.single μ 1) := ⟨μ, Or.inr (by simp)⟩
  have c1 := hD.mem_collar_iff x.2 h1
  have c2 := hD.mem_collar_iff x.2 h2
  have e : ∀ y : Torus d (N₀ * L ^ k), (y ∈ collar G ↔ y ∈ collar (Gs i)) →
      (if y ∈ collar G then D.Ψ y l else 0) =
        (if y ∈ collar (Gs i) then (hD.restrict i D).Ψ y l else 0) := by
    intro y hy
    by_cases h : y ∈ collar (Gs i)
    · simp [hy.2 h, h, hD.restrict_Ψ i D ((mem_dataSites _).2 (Or.inr h))]
    · have h' : y ∉ collar G := fun hh => h (hy.1 hh)
      simp [h', h]
  show ((if x.1 + Pi.single μ 1 ∈ collar G then D.Ψ (x.1 + Pi.single μ 1) l else 0) +
      (if x.1 - Pi.single μ 1 ∈ collar G then D.Ψ (x.1 - Pi.single μ 1) l else 0)) = _
  rw [e _ c1, e _ c2]

theorem PieceDecomp.source_eq (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) {i : ι} (x : (Gs i).Ω 1)
    (l : Fin N) :
    source G a ν D (hD.incl i x, l) = source (Gs i) a ν (hD.restrict i D) (x, l) := by
  unfold source qStar
  rw [hD.boundaryTerm_eq D x l]
  have hli : G.layerIndex x.1 = (Gs i).layerIndex x.1 := hD.layerIndex_eq x.2
  have hx : x.1 ∈ dataSites (Gs i) := (mem_dataSites _).2 (Or.inl x.2)
  show _ + _ + _ = _
  simp only [PieceDecomp.incl, hli, hD.restrict_Ψ i D hx, hD.restrict_h i D x.2]

/-- The equation of (EL) at a site of a piece. -/
theorem PieceDecomp.eq_at_iff (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ)
    (α : G.Ω 1 → ℂ) {i : ι} (x : (Gs i).Ω 1) (l : Fin N) :
    ((liftOp N (dirichletOperator G a ν α) *ᵥ φ) (hD.incl i x, l) =
        source G a ν D (hD.incl i x, l)) ↔
      ((liftOp N (dirichletOperator (Gs i) a ν (fun z => α (hD.incl i z))) *ᵥ
          (fun p : (Gs i).Ω 1 × Fin N => φ (hD.incl i p.1, p.2))) (x, l) =
        source (Gs i) a ν (hD.restrict i D) (x, l)) := by
  rw [liftOp_mulVec, liftOp_mulVec, hD.mulVec_eq a ν α (fun y => φ (y, l)) x,
    hD.source_eq a ν D x l]

/-- **Lemma II.2.6 (b)**: `(φ, α)` solves (EL) for the union iff its restrictions solve (EL) for
the pieces with the restricted data. -/
theorem isEL_local_iff (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ)
    (α : G.Ω 1 → ℂ) :
    IsEL G a ν D φ α ↔ ∀ i : ι, IsEL (Gs i) a ν (hD.restrict i D)
      (fun p : (Gs i).Ω 1 × Fin N => φ (hD.incl i p.1, p.2)) (fun z => α (hD.incl i z)) := by
  constructor
  · intro h i
    refine ⟨?_, fun x => h.2 (hD.incl i x)⟩
    funext ⟨x, l⟩
    exact (hD.eq_at_iff a ν D φ α x l).1 (congrFun h.1 (hD.incl i x, l))
  · intro h
    refine ⟨?_, fun y => ?_⟩
    · funext ⟨y, l⟩
      obtain ⟨i, hi⟩ := hD.exists_piece y.2
      have hy : y = hD.incl i ⟨y.1, hi⟩ := Subtype.ext rfl
      rw [hy]
      exact (hD.eq_at_iff a ν D φ α ⟨y.1, hi⟩ l).2 (congrFun (h i).1 (⟨y.1, hi⟩, l))
    · obtain ⟨i, hi⟩ := hD.exists_piece y.2
      have hy : y = hD.incl i ⟨y.1, hi⟩ := Subtype.ext rfl
      rw [hy]
      exact (h i).2 ⟨y.1, hi⟩

end Data

/-! ### Small solutions and `bgFieldC` -/

section Small

variable {G : GeneratingSet d L N₀ k ϱ} {Gs : ι → GeneratingSet d L N₀ k ϱ'}
  (hD : PieceDecomp G Gs)

include hD

/-- **Lemma II.2.6 (b)**: small solutions factorize. -/
theorem isSmallSolution_local_iff (a : ℕ → ℝ) (ν c₀ : ℝ) (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) :
    IsSmallSolution G a ν c₀ D φ α ↔ ∀ i : ι, IsSmallSolution (Gs i) a ν c₀ (hD.restrict i D)
      (fun p : (Gs i).Ω 1 × Fin N => φ (hD.incl i p.1, p.2)) (fun z => α (hD.incl i z)) := by
  constructor
  · intro h i
    refine ⟨(isEL_local_iff hD a ν D φ α).1 h.1 i, fun x => ?_⟩
    have h2 : G.spacing x.1 ^ 2 * ‖α (hD.incl i x)‖ < c₀ := h.2 (hD.incl i x)
    rw [hD.spacing_eq x.2] at h2
    exact h2
  · intro h
    refine ⟨(isEL_local_iff hD a ν D φ α).2 fun i => (h i).1, fun y => ?_⟩
    obtain ⟨i, hi⟩ := hD.exists_piece y.2
    have hy : y = hD.incl i ⟨y.1, hi⟩ := Subtype.ext rfl
    have h2 : (Gs i).spacing y.1 ^ 2 * ‖α (hD.incl i ⟨y.1, hi⟩)‖ < c₀ := (h i).2 ⟨y.1, hi⟩
    rw [← hD.spacing_eq hi] at h2
    rw [hy]
    exact h2

/-- The field equal to `φ'` on the piece `i` and to `φ` elsewhere. -/
noncomputable def glueField (Gs : ι → GeneratingSet d L N₀ k ϱ') (i : ι)
    (φ : G.Ω 1 × Fin N → ℂ) (φ' : (Gs i).Ω 1 × Fin N → ℂ) : G.Ω 1 × Fin N → ℂ := by
  classical
  exact fun y => if h : y.1.1 ∈ (Gs i).Ω 1 then φ' (⟨y.1.1, h⟩, y.2) else φ y

/-- The multiplier equal to `α'` on the piece `i` and to `α` elsewhere. -/
noncomputable def glueMult (Gs : ι → GeneratingSet d L N₀ k ϱ') (i : ι) (α : G.Ω 1 → ℂ)
    (α' : (Gs i).Ω 1 → ℂ) : G.Ω 1 → ℂ := by
  classical
  exact fun y => if h : y.1 ∈ (Gs i).Ω 1 then α' ⟨y.1, h⟩ else α y

theorem PieceDecomp.glue_incl (i : ι) (φ : G.Ω 1 × Fin N → ℂ) (φ' : (Gs i).Ω 1 × Fin N → ℂ)
    (z : (Gs i).Ω 1) (l : Fin N) : glueField Gs i φ φ' (hD.incl i z, l) = φ' (z, l) := by
  classical
  simp [glueField, PieceDecomp.incl, z.2]

theorem PieceDecomp.glueα_incl (i : ι) (α : G.Ω 1 → ℂ) (α' : (Gs i).Ω 1 → ℂ)
    (z : (Gs i).Ω 1) : glueMult Gs i α α' (hD.incl i z) = α' z := by
  classical
  simp [glueMult, PieceDecomp.incl, z.2]

theorem PieceDecomp.glue_incl_ne {i j : ι} (hij : j ≠ i) (φ : G.Ω 1 × Fin N → ℂ)
    (φ' : (Gs i).Ω 1 × Fin N → ℂ) (z : (Gs j).Ω 1) (l : Fin N) :
    glueField Gs i φ φ' (hD.incl j z, l) = φ (hD.incl j z, l) := by
  classical
  have : z.1 ∉ (Gs i).Ω 1 := fun h => hij (hD.piece_unique z.2 h)
  simp [glueField, PieceDecomp.incl, this]

theorem PieceDecomp.glueα_incl_ne {i j : ι} (hij : j ≠ i) (α : G.Ω 1 → ℂ)
    (α' : (Gs i).Ω 1 → ℂ) (z : (Gs j).Ω 1) :
    glueMult Gs i α α' (hD.incl j z) = α (hD.incl j z) := by
  classical
  have : z.1 ∉ (Gs i).Ω 1 := fun h => hij (hD.piece_unique z.2 h)
  simp [glueMult, PieceDecomp.incl, this]

/-- **Lemma II.2.6 (b), (c)** (exact factorization of the local background): if the `∃!` branch
defining `bgFieldC` for the union `G` applies, then on each piece it is `bgFieldC` of the piece
with the restricted data (the restriction exists and is unique for the piece). -/
theorem bgFieldC_local_eq (a : ℕ → ℝ) (ν c₀ : ℝ) (D : BgData G N)
    (H : ∃! s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ), IsSmallSolution G a ν c₀ D s.1 s.2)
    (i : ι) (x : (Gs i).Ω 1) (l : Fin N) :
    bgFieldC G a ν c₀ D (hD.incl i x, l) =
      bgFieldC (Gs i) a ν c₀ (hD.restrict i D) (x, l) := by
  obtain ⟨⟨φ, α⟩, hs, hu⟩ := H
  have hu' : ∀ φ' α', IsSmallSolution G a ν c₀ D φ' α' → φ' = φ ∧ α' = α := fun φ' α' h => by
    have := hu (φ', α') h
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have e1 := (bgFieldC_eq hs hu').1
  have hsi := (isSmallSolution_local_iff hD a ν c₀ D φ α).1 hs i
  have hui : ∀ φ' α', IsSmallSolution (Gs i) a ν c₀ (hD.restrict i D) φ' α' →
      φ' = (fun p : (Gs i).Ω 1 × Fin N => φ (hD.incl i p.1, p.2)) ∧
        α' = (fun z => α (hD.incl i z)) := by
    intro φ' α' h'
    have hg : IsSmallSolution G a ν c₀ D (glueField Gs i φ φ') (glueMult Gs i α α') := by
      refine (isSmallSolution_local_iff hD a ν c₀ D _ _).2 fun j => ?_
      by_cases hj : j = i
      · subst hj
        have e2 : (fun p : (Gs j).Ω 1 × Fin N => glueField Gs j φ φ' (hD.incl j p.1, p.2)) = φ' := by
          funext p; exact hD.glue_incl j φ φ' p.1 p.2
        have e3 : (fun z => glueMult Gs j α α' (hD.incl j z)) = α' := by
          funext z; exact hD.glueα_incl j α α' z
        rw [e2, e3]; exact h'
      · have e2 : (fun p : (Gs j).Ω 1 × Fin N => glueField Gs i φ φ' (hD.incl j p.1, p.2)) =
            (fun p : (Gs j).Ω 1 × Fin N => φ (hD.incl j p.1, p.2)) := by
          funext p; exact hD.glue_incl_ne hj φ φ' p.1 p.2
        have e3 : (fun z => glueMult Gs i α α' (hD.incl j z)) = (fun z => α (hD.incl j z)) := by
          funext z; exact hD.glueα_incl_ne hj α α' z
        rw [e2, e3]
        exact (isSmallSolution_local_iff hD a ν c₀ D φ α).1 hs j
    have hge := hu' _ _ hg
    refine ⟨?_, ?_⟩
    · funext p
      have := congrFun hge.1 (hD.incl i p.1, p.2)
      rw [hD.glue_incl i φ φ' p.1 p.2] at this
      exact this
    · funext z
      have := congrFun hge.2 (hD.incl i z)
      rw [hD.glueα_incl i α α' z] at this
      exact this
  have e4 := (bgFieldC_eq hsi hui).1
  rw [e1, e4]

end Small

/-! ### The layerwise union of a finite family of generating sets -/

section Union

variable [Fintype ι] (Gs : ι → GeneratingSet d L N₀ k ϱ)

/-- The layerwise union `Ω_n = ⋃_i Ω_n(Gs i)` of a finite family of generating sets with the same
separation constant (the family `𝔹^loc` of Definition II.2.4 (v)). -/
noncomputable def unionGenSet : GeneratingSet d L N₀ k ϱ where
  Ω n := Finset.univ.biUnion fun i => (Gs i).Ω n
  top := by
    ext x
    simp [(Gs _).top]
  subset := fun j h1 h2 => Finset.biUnion_mono fun i _ => (Gs i).subset j h1 h2
  blockUnion := by
    intro j hj1 hjk x x' hxx'
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact exists_congr fun i => (Gs i).blockUnion j hj1 hjk x x' hxx'
  separation := by
    intro j hj1 hjk x hx y hy
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at hx hy
    obtain ⟨i, hi⟩ := hy
    exact (Gs i).separation j hj1 hjk x (hx i) y hi

theorem unionGenSet_Ω (n : ℕ) :
    (unionGenSet Gs).Ω n = Finset.univ.biUnion fun i => (Gs i).Ω n := rfl

/-- The union of pieces with separated data sites is a `PieceDecomp`. -/
theorem unionGenSet_decomp (hk : 1 ≤ k)
    (hsep : ∀ i j, i ≠ j → ∀ u ∈ dataSites (Gs i), ∀ w ∈ dataSites (Gs j), 2 ≤ supDist u w) :
    PieceDecomp (unionGenSet Gs) Gs where
  one_le := hk
  layers := fun x n _ _ => by simp [unionGenSet_Ω]
  separated := hsep

end Union

end Balaban.LargeField
