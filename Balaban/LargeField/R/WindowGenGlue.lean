module

public import Balaban.Multiscale.GeneratingSet
public import Balaban.LargeField.R.WindowGenSingle

/-!
# The window generating set (Part III, Definition III.2.1)

`𝔹_{k₁,k} = (𝔹_{k₁}(W) ∩ Z_{k₁}) ∪ (𝔹_k ∩ Z^c_{k₁} ∩ Z) ∪ (𝔹_k(U_k) ∩ Z^c ∩ U_k^∼)`:
the layer `Ω_n` is the union of the layers `Ω_n` of three generating sets, each restricted to a
region.

* `GluePieces`, `GluePieces.glue`: the generating set whose layers are the unions
  `⋃_i (Ω^i_n ∩ A_i)`, under the hypotheses `GluePieces.Hyp` of each piece separately: the
  restricted layers are unions of `n`-blocks, and the part of each piece in its region is at
  distance `> ϱ L^n` from the complement of the region (so that, with the separation of the piece
  itself, the glued family satisfies (S));
* `WindowPieces`, `windowGenSet`: the three pieces and regions of Definition III.2.1;
  `windowGenSet_Ω` is the formula for the layers;
* `WindowPieces.example`, `nonempty_windowPieces_hyp`: the hypotheses are inhabited.

The verification of `WindowPieces.Hyp` for the pieces of a ripe component (single-box check box by
box, Lemma III.1.2 (e)-(f), Lemma I.3.16) belongs to the geometry of the window and is not part of
this file.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Finset

section Glue

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {ι : Type*} [Fintype ι]

/-- Generating sets `G_i` on the same torus with regions `A_i`. -/
structure GluePieces (d L N₀ k : ℕ) [NeZero N₀] [NeZero L] (ϱ : ℝ) (ι : Type*) where
  gen : ι → GeneratingSet d L N₀ k ϱ
  region : ι → Finset (Torus d (N₀ * L ^ k))

namespace GluePieces

variable (P : GluePieces d L N₀ k ϱ ι)

open Classical in
/-- The layers `Ω_n = ⋃_i (Ω^i_n ∩ A_i)` of the glued family. -/
noncomputable def layer (n : ℕ) : Finset (Torus d (N₀ * L ^ k)) :=
  Finset.univ.biUnion fun i => (P.gen i).Ω n ∩ P.region i

theorem mem_layer {n : ℕ} {x : Torus d (N₀ * L ^ k)} :
    x ∈ P.layer n ↔ ∃ i, x ∈ (P.gen i).Ω n ∧ x ∈ P.region i := by
  classical
  simp [layer]

/-- The hypotheses on each piece (not on pairs of pieces): the restricted layers are unions of
blocks, and a point of the restricted layer `n + 1` is at distance `> ϱ L^n` from the complement of
the region. -/
structure Hyp : Prop where
  blockUnion : ∀ i n, 1 ≤ n → n ≤ k →
    IsBlockUnion L N₀ k n ((P.gen i).Ω n ∩ P.region i)
  margin : ∀ i n, 1 ≤ n → n < k → ∀ y ∈ (P.gen i).Ω (n + 1), y ∈ P.region i →
    ∀ x, x ∉ P.region i → ϱ * (L : ℝ) ^ n < Green.torusDist d (N₀ * L ^ k) x y

/-- The glued generating set. -/
noncomputable def glue (h : P.Hyp) : GeneratingSet d L N₀ k ϱ where
  Ω := P.layer
  top := by
    ext x
    simp [mem_layer, (P.gen _).top]
  subset := by
    intro j hj1 hjk x hx
    obtain ⟨i, hi1, hi2⟩ := (mem_layer P).1 hx
    exact (mem_layer P).2 ⟨i, (P.gen i).subset j hj1 hjk hi1, hi2⟩
  blockUnion := by
    intro j hj1 hjk x x' hxx'
    simp only [mem_layer]
    constructor
    · rintro ⟨i, hi1, hi2⟩
      refine ⟨i, ?_⟩
      have := (h.blockUnion i j hj1 hjk x x' hxx').1 (Finset.mem_inter.2 ⟨hi1, hi2⟩)
      exact Finset.mem_inter.1 this
    · rintro ⟨i, hi1, hi2⟩
      refine ⟨i, ?_⟩
      have := (h.blockUnion i j hj1 hjk x x' hxx').2 (Finset.mem_inter.2 ⟨hi1, hi2⟩)
      exact Finset.mem_inter.1 this
  separation := by
    intro j hj1 hjk x hx y hy
    obtain ⟨i, hi1, hi2⟩ := (mem_layer P).1 hy
    by_cases hxi : x ∈ P.region i
    · have : x ∉ (P.gen i).Ω j := fun hxj => hx ((mem_layer P).2 ⟨i, hxj, hxi⟩)
      exact (P.gen i).separation j hj1 hjk x this y hi1
    · exact h.margin i j hj1 hjk y hi1 hi2 x hxi

theorem glue_Ω (h : P.Hyp) (n : ℕ) : (P.glue h).Ω n = P.layer n := rfl

end GluePieces

end Glue

section Window

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The data of Definition III.2.1: the generating sets `𝔹_{k₁}(W)` (`core`), `𝔹_k` (`full`) and
`𝔹_k(U_k)` (`bdry`) on the level-`k` torus, and the fine sets `Z_{k₁}` (`Zk1`), `Z` and `U_k^∼`
(`Unb`). -/
structure WindowPieces (d L N₀ k : ℕ) [NeZero N₀] [NeZero L] (ϱ : ℝ) where
  core : GeneratingSet d L N₀ k ϱ
  full : GeneratingSet d L N₀ k ϱ
  bdry : GeneratingSet d L N₀ k ϱ
  Zk1 : Finset (Torus d (N₀ * L ^ k))
  Z : Finset (Torus d (N₀ * L ^ k))
  Unb : Finset (Torus d (N₀ * L ^ k))

namespace WindowPieces

variable (W : WindowPieces d L N₀ k ϱ)

open Classical in
/-- The three pieces with their regions `Z_{k₁}`, `Z^c_{k₁} ∩ Z`, `Z^c ∩ U_k^∼`. -/
noncomputable def pieces : GluePieces d L N₀ k ϱ (Fin 3) where
  gen := ![W.core, W.full, W.bdry]
  region := ![W.Zk1, W.Z \ W.Zk1, W.Unb \ W.Z]

/-- The hypotheses of `GluePieces.Hyp` for the three pieces of Definition III.2.1. -/
abbrev Hyp : Prop := W.pieces.Hyp

/-- **Definition III.2.1** (the window generating set, P7 (2.13), local):
`𝔹_{k₁,k} = (𝔹_{k₁}(W) ∩ Z_{k₁}) ∪ (𝔹_k ∩ Z^c_{k₁} ∩ Z) ∪ (𝔹_k(U_k) ∩ Z^c ∩ U_k^∼)`, as a
generating set with the separation `ϱ` of the pieces. -/
noncomputable def windowGenSet (h : W.Hyp) : GeneratingSet d L N₀ k ϱ := W.pieces.glue h

/-- The layers of the window generating set. -/
theorem windowGenSet_Ω (h : W.Hyp) (n : ℕ) :
    (W.windowGenSet h).Ω n =
      (W.core.Ω n ∩ W.Zk1) ∪ (W.full.Ω n ∩ (W.Z \ W.Zk1)) ∪ (W.bdry.Ω n ∩ (W.Unb \ W.Z)) := by
  classical
  ext x
  show x ∈ W.pieces.layer n ↔ _
  rw [GluePieces.mem_layer]
  simp only [Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro ⟨i, h1, h2⟩
    fin_cases i
    · exact Or.inl (Or.inl ⟨h1, h2⟩)
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · exact Or.inr ⟨h1, h2⟩
  · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
    · exact ⟨0, h1, h2⟩
    · exact ⟨1, h1, h2⟩
    · exact ⟨2, h1, h2⟩

/-- An admissible choice of pieces: all three generating sets are the single-scale one, with the
regions `∅`, `Z`, `∅`. -/
noncomputable def sample : WindowPieces d L N₀ k ϱ where
  core := singleGen d L N₀ k ϱ
  full := singleGen d L N₀ k ϱ
  bdry := singleGen d L N₀ k ϱ
  Zk1 := ∅
  Z := Finset.univ
  Unb := ∅

open Classical in
/-- The hypotheses of Definition III.2.1 are inhabited. -/
theorem sample_hyp : (sample : WindowPieces d L N₀ k ϱ).Hyp := by
  have hU : ∀ (S : Finset (Torus d (N₀ * L ^ k))) (n : ℕ), (∀ x, x ∈ S) → IsBlockUnion L N₀ k n S :=
    fun S n h x x' _ => by simp [h x, h x']
  refine ⟨?_, ?_⟩
  · intro i n hn1 hnk
    fin_cases i
    · intro x x' _
      simp [pieces, sample]
    · refine hU _ _ fun x => ?_
      simp [pieces, sample, singleGen_Ω hnk]
    · intro x x' _
      simp [pieces, sample]
  · intro i n hn1 hnk y _ hy x hx
    fin_cases i
    · simp [pieces, sample] at hy
    · simp [pieces, sample] at hx
    · simp [pieces, sample] at hy

end WindowPieces

theorem nonempty_windowPieces_hyp :
    ∃ W : WindowPieces d L N₀ k ϱ, W.Hyp := ⟨_, WindowPieces.sample_hyp⟩

end Window

end Balaban.LargeField
