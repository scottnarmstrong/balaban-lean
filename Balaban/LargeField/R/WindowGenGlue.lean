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
  restricted layers are unions of `n`-blocks, and a point of the restricted layer `n + 1` of a
  piece is, from each point outside its region, either at distance `> ϱ L^n` or already in the
  glued layer `n` (so that, with the separation of the piece itself, the glued family satisfies
  (S));
* `WindowPieces`, `windowGenSet`: the three pieces and regions of Definition III.2.1;
  `windowGenSet_Ω` is the formula for the layers;
* `WindowPieces.example`, `nonempty_windowPieces_hyp`: the hypotheses are inhabited.

The verification of `WindowPieces.Hyp` for the pieces of a ripe component (single-box check box by
box, Lemma III.1.2 (e)-(f), Lemma I.3.16) is `windowOfHistory_hyp` in `WindowOfHistory`.
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
blocks, and a point `y` of the restricted layer `n + 1` of a piece is, for every `x` outside the
region of the piece, either already in the glued layer `n` or at distance `> ϱ L^n` from `x`.

The alternative `x ∈ P.layer n` is what LFR Lemma III.2.1 needs: only the separation (S) of the
glued family is required, and a point of the glued layer `n` is not constrained by (S). The strong
form (distance `> ϱ L^n` from every point outside the region) is false for the actual window:
`windowOfHistory_strongMargin_false_of_boundary_pair` (W184) shows the core piece fills the sites of
`Z_{k₁}` next to its complement. `GluePieces.Hyp.of_strong` shows the strong form implies this one. -/
structure Hyp : Prop where
  blockUnion : ∀ i n, 1 ≤ n → n ≤ k →
    IsBlockUnion L N₀ k n ((P.gen i).Ω n ∩ P.region i)
  margin : ∀ i n, 1 ≤ n → n < k → ∀ y ∈ (P.gen i).Ω (n + 1), y ∈ P.region i →
    ∀ x, x ∉ P.region i → x ∈ P.layer n ∨ ϱ * (L : ℝ) ^ n < Green.torusDist d (N₀ * L ^ k) x y

theorem Hyp.of_strong
    (hb : ∀ i n, 1 ≤ n → n ≤ k → IsBlockUnion L N₀ k n ((P.gen i).Ω n ∩ P.region i))
    (hm : ∀ i n, 1 ≤ n → n < k → ∀ y ∈ (P.gen i).Ω (n + 1), y ∈ P.region i →
      ∀ x, x ∉ P.region i → ϱ * (L : ℝ) ^ n < Green.torusDist d (N₀ * L ^ k) x y) : P.Hyp :=
  ⟨hb, fun i n h1 h2 y hy hyr x hx => Or.inr (hm i n h1 h2 y hy hyr x hx)⟩

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
    · exact (h.margin i j hj1 hjk y hi1 hi2 x hxi).resolve_left hx

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

/-- The layers of the glued three pieces (no hypothesis needed). -/
theorem pieces_layer (n : ℕ) :
    W.pieces.layer n =
      (W.core.Ω n ∩ W.Zk1) ∪ (W.full.Ω n ∩ (W.Z \ W.Zk1)) ∪ (W.bdry.Ω n ∩ (W.Unb \ W.Z)) := by
  classical
  ext x
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

/-- The layers of the window generating set. -/
theorem windowGenSet_Ω (h : W.Hyp) (n : ℕ) :
    (W.windowGenSet h).Ω n =
      (W.core.Ω n ∩ W.Zk1) ∪ (W.full.Ω n ∩ (W.Z \ W.Zk1)) ∪ (W.bdry.Ω n ∩ (W.Unb \ W.Z)) :=
  W.pieces_layer n

/-- **`WindowPieces.Hyp` from the geometry of the window** (Lemma III.1.2 (f), Lemma III.2.1): for
`k₁ ≤ k`, if `Z_{k₁} ⊆ Z`, `Z_{k₁} ∩ Ω_{k₁+1}(𝔹_k) = ∅`, `Ω_m(𝔹_k(U_k)) ∩ (U_k^∼ ∖ Z) ⊆ Ω_m(𝔹_k)`,
`Ω_1(𝔹_k(U_k)) ⊆ U_k^∼`, `Ω_m(𝔹_{k₁}(W)) ⊆ Ω_m(𝔹_k)`, the sites off `Z_{k₁}` are in
`Ω_{k₁}(𝔹_{k₁}(W))`, the sites of `Z` are in `Ω_k(𝔹_k(U_k))`, `Ω_m(𝔹_{k₁}(W)) = ∅` for `m > k₁`, the
sites of `Z_{k₁}` are at distance `> ϱ L^{k₁}` from `Ω_{k₁+1}(𝔹_k)`, and the three regions are unions
of the blocks of the scales that occur, then the margin clause (in its glued form) and the block-union
clause of `GluePieces.Hyp` hold for the three pieces.  (The separation of each piece is used to turn
"close" into "in the layer `n` of the same piece".) -/
theorem hyp_of_geometry {k1 : ℕ} (hk1 : 1 ≤ k1) (hk1k : k1 ≤ k)
    (hZ : W.Zk1 ⊆ W.Z)
    (hZk1top : ∀ x ∈ W.Zk1, x ∉ W.full.Ω (k1 + 1))
    (hbdry : ∀ m, 1 ≤ m → m ≤ k → W.bdry.Ω m ∩ (W.Unb \ W.Z) ⊆ W.full.Ω m)
    (hsupp : ∀ x ∈ W.bdry.Ω 1, x ∈ W.Unb)
    (hcore : ∀ m, 1 ≤ m → m ≤ k → W.core.Ω m ⊆ W.full.Ω m)
    (hcoreCover : ∀ x, x ∉ W.Zk1 → x ∈ W.core.Ω k1)
    (hbdryCover : ∀ x ∈ W.Z, x ∈ W.bdry.Ω k)
    (hcoreGt : ∀ m, k1 < m → ∀ x, x ∉ W.core.Ω m)
    (hfar : k1 < k → ∀ x ∈ W.Zk1, ∀ y ∈ W.full.Ω (k1 + 1),
      ϱ * (L : ℝ) ^ k1 < Green.torusDist d (N₀ * L ^ k) x y)
    (hbZk1 : ∀ m, 1 ≤ m → m ≤ k1 → IsBlockUnion L N₀ k m W.Zk1)
    (hbZ : ∀ m, 1 ≤ m → m ≤ k → IsBlockUnion L N₀ k m W.Z)
    (hbUnb : ∀ m, 1 ≤ m → m ≤ k → IsBlockUnion L N₀ k m W.Unb) : W.Hyp := by
  classical
  have hbd : ∀ z ∈ W.Z, ∀ m, 1 ≤ m → m ≤ k → z ∈ W.bdry.Ω m := fun z hz m h1 h2 =>
    W.bdry.Ω_antitone h1 h2 (by omega) (hbdryCover z hz)
  have hfullGt : ∀ m, k1 < m → m ≤ k + 1 → ∀ x ∈ W.full.Ω m, x ∉ W.Zk1 := fun m hm hm' x hx hxz =>
    hZk1top x hxz (W.full.Ω_antitone (by omega) (by omega) hm' hx)
  have hbu0 : ∀ n, 1 ≤ n → n ≤ k → IsBlockUnion L N₀ k n (W.core.Ω n ∩ W.Zk1) := by
    intro n h1 hn x x' h
    by_cases hnk1 : n ≤ k1
    · simp only [Finset.mem_inter]
      rw [W.core.blockUnion n h1 hn x x' h, hbZk1 n h1 hnk1 x x' h]
    · constructor <;> intro hx <;> exact absurd (Finset.mem_inter.1 hx).1 (hcoreGt n (by omega) _)
  have hbu1 : ∀ n, 1 ≤ n → n ≤ k → IsBlockUnion L N₀ k n (W.full.Ω n ∩ (W.Z \ W.Zk1)) := by
    intro n h1 hn x x' h
    by_cases hnk1 : n ≤ k1
    · simp only [Finset.mem_inter, Finset.mem_sdiff]
      rw [W.full.blockUnion n h1 hn x x' h, hbZ n h1 hn x x' h, hbZk1 n h1 hnk1 x x' h]
    · have hf := W.full.blockUnion n h1 hn x x' h
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro ⟨a, b, c⟩
        exact ⟨hf.1 a, (hbZ n h1 hn x x' h).1 b, hfullGt n (by omega) (by omega) _ (hf.1 a)⟩
      · rintro ⟨a, b, c⟩
        exact ⟨hf.2 a, (hbZ n h1 hn x x' h).2 b, hfullGt n (by omega) (by omega) x (hf.2 a)⟩
  have hbu2 : ∀ n, 1 ≤ n → n ≤ k → IsBlockUnion L N₀ k n (W.bdry.Ω n ∩ (W.Unb \ W.Z)) := by
    intro n h1 hn x x' h
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    rw [W.bdry.blockUnion n h1 hn x x' h, hbUnb n h1 hn x x' h, hbZ n h1 hn x x' h]
  have m0 : ∀ n, 1 ≤ n → n < k → ∀ y ∈ W.core.Ω (n + 1), y ∈ W.Zk1 → ∀ x, x ∉ W.Zk1 →
      x ∈ W.pieces.layer n ∨ ϱ * (L : ℝ) ^ n < Green.torusDist d (N₀ * L ^ k) x y := by
    intro n hn1 hnk y hy hyZ x hx
    by_cases hd : ϱ * (L : ℝ) ^ n < Green.torusDist d (N₀ * L ^ k) x y
    · exact Or.inr hd
    refine Or.inl ?_
    have hxc : x ∈ W.core.Ω n := by
      by_contra hn; exact hd (W.core.separation n hn1 hnk x hn y hy)
    have hxf : x ∈ W.full.Ω n := hcore n hn1 hnk.le hxc
    rw [pieces_layer]
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    by_cases hxZ : x ∈ W.Z
    · exact Or.inl (Or.inr ⟨hxf, hxZ, hx⟩)
    · have hxb : x ∈ W.bdry.Ω n := by
        by_contra hn
        exact hd (W.bdry.separation n hn1 hnk x hn y (hbd y (hZ hyZ) (n + 1) (by omega) (by omega)))
      exact Or.inr ⟨hxb, hsupp x (W.bdry.Ω_antitone le_rfl hn1 (by omega) hxb), hxZ⟩
  have m1 : ∀ n, 1 ≤ n → n < k → ∀ y ∈ W.full.Ω (n + 1), y ∈ W.Z \ W.Zk1 →
      ∀ x, x ∉ W.Z \ W.Zk1 →
      x ∈ W.pieces.layer n ∨ ϱ * (L : ℝ) ^ n < Green.torusDist d (N₀ * L ^ k) x y := by
    intro n hn1 hnk y hy hyr x hx
    obtain ⟨hyZ, hyk⟩ := Finset.mem_sdiff.1 hyr
    by_cases hd : ϱ * (L : ℝ) ^ n < Green.torusDist d (N₀ * L ^ k) x y
    · exact Or.inr hd
    refine Or.inl ?_
    have hxf : x ∈ W.full.Ω n := by
      by_contra hn; exact hd (W.full.separation n hn1 hnk x hn y hy)
    rw [pieces_layer]
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    by_cases hxk : x ∈ W.Zk1
    · rcases lt_trichotomy n k1 with hlt | heq | hgt
      · have hyc : y ∈ W.core.Ω (n + 1) :=
          W.core.Ω_antitone (by omega) (by omega) (by omega) (hcoreCover y hyk)
        have hxc : x ∈ W.core.Ω n := by
          by_contra hn; exact hd (W.core.separation n hn1 hnk x hn y hyc)
        exact Or.inl (Or.inl ⟨hxc, hxk⟩)
      · subst heq; exact absurd (hfar hnk x hxk y hy) hd
      · exact absurd hxk (hfullGt n hgt (by omega) x hxf)
    · by_cases hxZ : x ∈ W.Z
      · exact Or.inl (Or.inr ⟨hxf, hxZ, hxk⟩)
      · have hxb : x ∈ W.bdry.Ω n := by
          by_contra hn
          exact hd (W.bdry.separation n hn1 hnk x hn y (hbd y hyZ (n + 1) (by omega) (by omega)))
        exact Or.inr ⟨hxb, hsupp x (W.bdry.Ω_antitone le_rfl hn1 (by omega) hxb), hxZ⟩
  have m2 : ∀ n, 1 ≤ n → n < k → ∀ y ∈ W.bdry.Ω (n + 1), y ∈ W.Unb \ W.Z →
      ∀ x, x ∉ W.Unb \ W.Z →
      x ∈ W.pieces.layer n ∨ ϱ * (L : ℝ) ^ n < Green.torusDist d (N₀ * L ^ k) x y := by
    intro n hn1 hnk y hy hyr x hx
    obtain ⟨hyU, hyZ⟩ := Finset.mem_sdiff.1 hyr
    by_cases hd : ϱ * (L : ℝ) ^ n < Green.torusDist d (N₀ * L ^ k) x y
    · exact Or.inr hd
    refine Or.inl ?_
    have hxb : x ∈ W.bdry.Ω n := by
      by_contra hn; exact hd (W.bdry.separation n hn1 hnk x hn y hy)
    have hxU : x ∈ W.Unb := hsupp x (W.bdry.Ω_antitone le_rfl hn1 (by omega) hxb)
    have hxZ : x ∈ W.Z := by
      by_contra h; exact hx (Finset.mem_sdiff.2 ⟨hxU, h⟩)
    have hyf : y ∈ W.full.Ω (n + 1) := hbdry (n + 1) (by omega) (by omega) (Finset.mem_inter.2 ⟨hy, hyr⟩)
    have hxf : x ∈ W.full.Ω n := by
      by_contra hn; exact hd (W.full.separation n hn1 hnk x hn y hyf)
    rw [pieces_layer]
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    by_cases hxk : x ∈ W.Zk1
    · rcases lt_trichotomy n k1 with hlt | heq | hgt
      · have hyc : y ∈ W.core.Ω (n + 1) :=
          W.core.Ω_antitone (by omega) (by omega) (by omega) (hcoreCover y fun h => hyZ (hZ h))
        have hxc : x ∈ W.core.Ω n := by
          by_contra hn; exact hd (W.core.separation n hn1 hnk x hn y hyc)
        exact Or.inl (Or.inl ⟨hxc, hxk⟩)
      · subst heq; exact absurd (hfar hnk x hxk y hyf) hd
      · exact absurd hxk (hfullGt n hgt (by omega) x hxf)
    · exact Or.inl (Or.inr ⟨hxf, hxZ, hxk⟩)
  refine ⟨?_, ?_⟩
  · intro i n h1 hn
    fin_cases i
    · exact hbu0 n h1 hn
    · exact hbu1 n h1 hn
    · exact hbu2 n h1 hn
  · intro i n h1 hn y hy hyr x hx
    fin_cases i
    · exact m0 n h1 hn y hy hyr x hx
    · exact m1 n h1 hn y hy hyr x hx
    · exact m2 n h1 hn y hy hyr x hx

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
  refine GluePieces.Hyp.of_strong _ ?_ ?_
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
