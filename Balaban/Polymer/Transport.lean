module

public import Balaban.Polymer.Local

/-!
# Transport of local terms

PE (f).  The local term `P(Y)` only depends on the polymers supported in `Y`, on their
incompatibility relation, and on their activities.  If a bijection `ψ` between the polymers
supported in `Y` and those supported in `Y'` carries supports by `e`, preserves incompatibility
and activities, then `P'(e Y) = P(Y)` (`PY_transport`).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

variable {P : Type*} [Fintype P] {inc : P → P → Prop} {B : Type*} {supp : P → Finset B}
  {P' : Type*} [Fintype P'] {inc' : P' → P' → Prop} {B' : Type*} {supp' : P' → Finset B'}

/-- Transport of a local term along a bijection of the polymers supported in `Y` and `Y'`, where
`Y' = e '' Y` and `e` is injective on `Y`. -/
theorem PY_transport {K : P → ℂ} {K' : P' → ℂ} (Y : Finset B) (Y' : Finset B') (e : B → B')
    (he : Set.InjOn e (Y : Set B)) (hY' : ∀ b', b' ∈ Y' ↔ ∃ b ∈ Y, e b = b')
    (ψ : {x : P // supp x ⊆ Y} ≃ {x' : P' // supp' x' ⊆ Y'})
    (hsupp : ∀ x b', b' ∈ supp' (ψ x).1 ↔ ∃ b ∈ supp x.1, e b = b')
    (hinc : ∀ x y, lnk inc' (ψ x).1 (ψ y).1 ↔ lnk inc x.1 y.1)
    (hK : ∀ x, K' (ψ x).1 = K x.1) :
    PY inc' supp' K' Y' = PY inc supp K Y := by
  unfold PY
  refine tsum_congr (fun n => ?_)
  unfold Pterm
  congr 1
  have hsub : ∀ X : Fin (n + 1) → P, unionOf supp X = Y → ∀ i, supp (X i) ⊆ Y := fun X hX i => by
    rw [← hX]; exact Finset.subset_biUnion_of_mem (fun i => supp (X i)) (Finset.mem_univ i)
  have hsub' : ∀ X : Fin (n + 1) → P', unionOf supp' X = Y' → ∀ i,
      supp' (X i) ⊆ Y' := fun X hX i => by
    rw [← hX]; exact Finset.subset_biUnion_of_mem (fun i => supp' (X i)) (Finset.mem_univ i)
  symm
  refine Finset.sum_bij (fun X hX => fun i => (ψ ⟨X i, hsub X (Finset.mem_filter.mp hX).2 i⟩).1)
    ?_ ?_ ?_ ?_
  · intro X hX
    rw [Finset.mem_filter] at hX ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    ext b'
    rw [hY']
    simp only [unionOf, Finset.mem_biUnion, Finset.mem_univ, true_and, hsupp]
    constructor
    · rintro ⟨i, a, ha, rfl⟩
      exact ⟨a, hsub X hX.2 i ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      rw [← hX.2] at ha
      simp only [unionOf, Finset.mem_biUnion, Finset.mem_univ, true_and] at ha
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, a, hi, rfl⟩
  · intro X hX X₂ hX₂ h
    funext i
    have := congrFun h i
    have h2 := ψ.injective (Subtype.ext this)
    exact congrArg Subtype.val h2
  · intro X' hX'
    rw [Finset.mem_filter] at hX'
    have hX'2 := hsub' X' hX'.2
    refine ⟨fun i => (ψ.symm ⟨X' i, hX'2 i⟩).1, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Finset.Subset.antisymm
      · intro b hb
        simp only [unionOf, Finset.mem_biUnion, Finset.mem_univ, true_and] at hb
        obtain ⟨i, hi⟩ := hb
        exact (ψ.symm ⟨X' i, hX'2 i⟩).2 hi
      · intro b hb
        have : e b ∈ unionOf supp' X' := by rw [hX'.2]; exact (hY' _).mpr ⟨b, hb, rfl⟩
        simp only [unionOf, Finset.mem_biUnion, Finset.mem_univ, true_and] at this ⊢
        obtain ⟨i, hi⟩ := this
        refine ⟨i, ?_⟩
        have h1 := hsupp (ψ.symm ⟨X' i, hX'2 i⟩) (e b)
        simp only [Equiv.apply_symm_apply] at h1
        obtain ⟨b', hb', hbb⟩ := h1.mp hi
        have hb'Y : b' ∈ Y := (ψ.symm ⟨X' i, hX'2 i⟩).2 hb'
        have : b' = b := he hb'Y hb hbb
        rw [← this]; exact hb'
    · funext i
      simp
  · intro X hX
    rw [Finset.mem_filter] at hX
    set X' : Fin (n + 1) → P' := fun i => (ψ ⟨X i, hsub X hX.2 i⟩).1 with hX'
    have hg : clusterGraph inc X = clusterGraph inc' X' := by
      ext i j
      rw [clusterGraph_adj, clusterGraph_adj]
      exact and_congr_right (fun _ => (hinc ⟨X i, hsub X hX.2 i⟩ ⟨X j, hsub X hX.2 j⟩).symm)
    have hu : clusterUrsell inc X Finset.univ = clusterUrsell inc' X' Finset.univ := by
      unfold clusterUrsell; rw [hg]
    rw [hu]
    congr 1
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [hX']
    exact (hK ⟨X i, hsub X hX.2 i⟩).symm

end Balaban.Polymer
