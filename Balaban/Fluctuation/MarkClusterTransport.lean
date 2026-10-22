/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MarkedCubesLocal
public import Balaban.Polymer.ClusterRelabel

/-!
# Transport of the local cluster terms between two regions (Theorem 3.4)

The local term `G*(Y₀, S)` of the cluster expansion with one mark is determined by the combinatorics
of the cubes, the activities and the measure.  An equivalence `e` of the cubes of two regions
(for instance cubes of `Ω` and of `Ω'` related by a lattice symmetry, or two histories agreeing near
the support), a bijection `σ` of the labels compatible with `e` on the supports of the labels, and a
measure-preserving equivalence `T` of the configuration spaces that carries the activities and the
mark of the first system to those of the second, leave the local term unchanged.

* `Gst_transport`: **the core**, `G₂*(e Y₀, e S) = G₁*(Y₀, S)`;
* `Gst_equiv` of `MarkClusterEquiv.lean`, the invariance under a change of the variables of one
  system, is the instance `e = id`, `σ = id`;
* `blocksOf_map_of_siteEquiv`: the compatibility of `e` and `σ` with the supports of the labels,
  from a bijection `f` of the sites carrying the cubes of one region to those of the other.
-/

@[expose] public section

open MeasureTheory

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer

section Transport

variable {d L : ℕ} [NeZero L] {N₁ m₁ K m₀ j : ℕ} [NeZero N₁] {Ω : Set (CTorus d L N₁ m₁ K)}
  {N₁' m₁' K' m₀' j' : ℕ} [NeZero N₁'] {Ω' : Set (CTorus d L N₁' m₁' K')}
  {Lb Lb' : Type*} [Fintype Lb] [Fintype Lb']

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω
local notation "𝔅'" => CubeB (L := L) (N₁ := N₁') (m₁ := m₁') (K := K') m₀' j' Ω'

open Classical in
theorem presum_transport {Ωb : 𝔅 → Type*} {Ωb' : 𝔅' → Type*}
    (Lab : CubeLabels m₀ j Ω Lb) (Lab' : CubeLabels m₀' j' Ω' Lb') (e : 𝔅 ≃ 𝔅') (σ : Lb ≃ Lb')
    (hσ : ∀ y, blocksOf m₀' j' Ω' (Lab'.ysite (σ y)) = (blocksOf m₀ j Ω (Lab.ysite y)).map e.toEmbedding)
    (H : Lb → (∀ b, Ωb b) → ℂ) (H' : Lb' → (∀ b, Ωb' b) → ℂ) (Φ : ∀ b, Ωb b)
    (Φ' : ∀ b, Ωb' b) (hH : ∀ y, H' (σ y) Φ' = H y Φ) (t : NePoly 𝔅) :
    presum Lab' H' (NePoly.mapEquiv e t) Φ' = presum Lab H t Φ := by
  unfold presum
  symm
  refine Finset.sum_equiv σ (fun y => ?_) (fun y _ => (hH y).symm)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hσ, NePoly.mapEquiv_val, Finset.map_inj]

/-- **Transport of the local term** `G*(Y₀, S)`: an equivalence `e` of the cubes of two regions, a
bijection `σ` of the labels with `blocksOf (σ y) = e (blocksOf y)`, and a measure-preserving
equivalence `T` of the configuration spaces carrying the activities `H` and the mark `G` of the first
system to those of the second (on a set `Q` of full measure) give `G₂*(e S₀, e S) = G₁*(S₀, S)`. -/
theorem Gst_transport {Ωb : 𝔅 → Type*} {Ωb' : 𝔅' → Type*} [∀ b, MeasurableSpace (Ωb b)]
    [∀ b, MeasurableSpace (Ωb' b)] (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (μ' : ∀ b, Measure (Ωb' b)) [∀ b, IsProbabilityMeasure (μ' b)]
    (Lab : CubeLabels m₀ j Ω Lb) (Lab' : CubeLabels m₀' j' Ω' Lb') (e : 𝔅 ≃ 𝔅') (σ : Lb ≃ Lb')
    (hσ : ∀ y, blocksOf m₀' j' Ω' (Lab'.ysite (σ y)) = (blocksOf m₀ j Ω (Lab.ysite y)).map e.toEmbedding)
    (T : (∀ b, Ωb b) ≃ᵐ (∀ b, Ωb' b)) (hT : MeasurePreserving T (Measure.pi μ) (Measure.pi μ'))
    {Q : Set (∀ b, Ωb b)} (hQ : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Q)
    (H : Lb → (∀ b, Ωb b) → ℂ) (H' : Lb' → (∀ b, Ωb' b) → ℂ) (S₀ : Finset 𝔅)
    (G : (∀ b, Ωb b) → ℂ) (G' : (∀ b, Ωb' b) → ℂ) (S : Finset 𝔅)
    (hH : ∀ y, ∀ Φ ∈ Q, H' (σ y) (T Φ) = H y Φ) (hG : ∀ Φ ∈ Q, G' (T Φ) = G Φ) :
    Gst μ' Lab' H' (S₀.map e.toEmbedding) G' (S.map e.toEmbedding) = Gst μ Lab H S₀ G S := by
  classical
  have hF : Ff (shareBlock (Subtype.val : NePoly 𝔅' → Finset 𝔅')) Subtype.val
      (marksK μ' Subtype.val (presum Lab' H') (gMark (S₀.map e.toEmbedding) G')) (S.map e.toEmbedding) =
      Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
      (marksK μ Subtype.val (presum Lab H) (gMark S₀ G)) S := by
    funext l
    unfold Ff
    refine PY_relabel (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅))
      (shareBlock (Subtype.val : NePoly 𝔅' → Finset 𝔅')) _ _ (NePoly.mapEquiv e) e
      (fun x y => ?_) (fun x => rfl) (fun x => ?_) S
    · unfold shareBlock
      simp only [NePoly.mapEquiv_val, Finset.disjoint_map]
    · exact marksK_relabel μ μ' (NePoly.mapEquiv e) e T hT (fun x => rfl) hQ
        (fun Φ hΦ t => presum_transport Lab Lab' e σ hσ H H' Φ (T Φ) (fun y => hH y Φ hΦ) t)
        (fun Φ hΦ i t => by
          simp only [gMark, NePoly.mapEquiv_val, Finset.map_inj, hG Φ hΦ]) x l
  unfold Gst
  rw [hF]

/-- **The compatibility of a bijection of the cubes with the supports of the labels**: if a bijection
`f` of the sites carries the box of each cube `b` to the box of `e b`, then `blocksOf` of the image
of a set of sites is the image of `blocksOf`. -/
theorem blocksOf_map_of_siteEquiv (e : 𝔅 ≃ 𝔅') (f : CTorus d L N₁ m₁ K ≃ CTorus d L N₁' m₁' K')
    (hbox : ∀ b : 𝔅, box (e b).1 (cellSide L m₀' m₁' j') = f '' box b.1 (cellSide L m₀ m₁ j))
    (Y : Set (CTorus d L N₁ m₁ K)) :
    blocksOf m₀' j' Ω' (f '' Y) = (blocksOf m₀ j Ω Y).map e.toEmbedding := by
  ext b'
  obtain ⟨b, rfl⟩ := e.surjective b'
  rw [mem_blocksOf, Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_blocksOf, hbox]
  exact Set.image_subset_image_iff f.injective

end Transport

end Balaban.Fluctuation
