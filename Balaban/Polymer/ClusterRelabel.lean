/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.Marked
public import Balaban.Polymer.MayerMarked

/-!
# Relabelling invariance of the cluster sum and of the Mayer activities

Bijections of the blocks `e : B₁ ≃ B₂` and of the polymers (or terms) compatible with the supports
and the incompatibility relation carry the local terms `P(Y)` (`PY_relabel`), the activities of the
Mayer layer (`polyAct_relabel`, `mayerK_relabel`) and the marked activities of the first system to those
of the second.  Together with a measure-preserving equivalence of the configuration spaces this is the
transport of the cluster expansion between two regions (`Gst_transport`,
`Fluctuation/MarkClusterTransport.lean`).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory

namespace Balaban.Polymer

section Ursell

variable {P₁ P₂ : Type*} (inc₁ : P₁ → P₁ → Prop) (inc₂ : P₂ → P₂ → Prop)

theorem clusterUrsell_relabel (φ : P₁ → P₂) (hinc : ∀ x y, inc₂ (φ x) (φ y) ↔ inc₁ x y)
    {ι : Type*} (X : ι → P₁) (S : Finset ι) :
    clusterUrsell inc₂ (φ ∘ X) S = clusterUrsell inc₁ X S := by
  unfold clusterUrsell
  have : clusterGraph inc₂ (φ ∘ X) = clusterGraph inc₁ X := by
    ext i j
    simp only [clusterGraph, SimpleGraph.fromRel_adj, Function.comp_apply, hinc]
  rw [this]

end Ursell

section PY

variable {P₁ P₂ B₁ B₂ : Type*} [Fintype P₁] [Fintype P₂] [Fintype B₁] [Fintype B₂]
  (inc₁ : P₁ → P₁ → Prop) (inc₂ : P₂ → P₂ → Prop) (supp₁ : P₁ → Finset B₁) (supp₂ : P₂ → Finset B₂)

omit [Fintype B₁] [Fintype B₂] in
/-- **The cluster terms are invariant under a bijection of the polymers and of the blocks** that
preserves the incompatibility, the supports and the activities. -/
theorem Pterm_relabel (φ : P₁ ≃ P₂) (e : B₁ ≃ B₂) (hinc : ∀ x y, inc₂ (φ x) (φ y) ↔ inc₁ x y)
    (hsupp : ∀ x, supp₂ (φ x) = (supp₁ x).map e.toEmbedding) {K₁ : P₁ → ℂ} {K₂ : P₂ → ℂ}
    (hK : ∀ x, K₂ (φ x) = K₁ x) (Y : Finset B₁) (n : ℕ) :
    Pterm inc₂ supp₂ K₂ (Y.map e.toEmbedding) n = Pterm inc₁ supp₁ K₁ Y n := by
  unfold Pterm
  congr 1
  symm
  refine Finset.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin (n + 1))) φ) (fun X => ?_)
    (fun X _ => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hu : unionOf supp₂ (fun i => φ (X i)) = (unionOf supp₁ X).map e.toEmbedding := by
      unfold unionOf
      ext b
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_map_equiv, hsupp]
    have : unionOf supp₂ ((Equiv.arrowCongr (Equiv.refl (Fin (n + 1))) φ) X) =
        (unionOf supp₁ X).map e.toEmbedding := hu
    rw [this]
    exact (Finset.map_inj).symm
  · have h1 := clusterUrsell_relabel inc₁ inc₂ φ hinc X Finset.univ
    have h2 : (Equiv.arrowCongr (Equiv.refl (Fin (n + 1))) φ) X = φ ∘ X := by
      funext i; simp
    rw [h2, h1]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [hK]

omit [Fintype B₁] [Fintype B₂] in
theorem PY_relabel (φ : P₁ ≃ P₂) (e : B₁ ≃ B₂) (hinc : ∀ x y, inc₂ (φ x) (φ y) ↔ inc₁ x y)
    (hsupp : ∀ x, supp₂ (φ x) = (supp₁ x).map e.toEmbedding) {K₁ : P₁ → ℂ} {K₂ : P₂ → ℂ}
    (hK : ∀ x, K₂ (φ x) = K₁ x) (Y : Finset B₁) :
    PY inc₂ supp₂ K₂ (Y.map e.toEmbedding) = PY inc₁ supp₁ K₁ Y := by
  unfold PY
  exact tsum_congr fun n => Pterm_relabel inc₁ inc₂ supp₁ supp₂ φ e hinc hsupp hK Y n

end PY

section Mayer

variable {E₁ E₂ B₁ B₂ : Type*}
  (cs₁ : E₁ → Finset B₁) (cs₂ : E₂ → Finset B₂) (ψ : E₁ ≃ E₂) (e : B₁ ≃ B₂)

/-- The nonempty block sets transported by a bijection of the blocks. -/
def NePoly.mapEquiv (e : B₁ ≃ B₂) : NePoly B₁ ≃ NePoly B₂ where
  toFun Y := ⟨Y.1.map e.toEmbedding, Finset.map_nonempty.2 Y.2⟩
  invFun Y := ⟨Y.1.map e.symm.toEmbedding, Finset.map_nonempty.2 Y.2⟩
  left_inv Y := Subtype.ext (by ext b; simp)
  right_inv Y := Subtype.ext (by ext b; simp)

theorem NePoly.mapEquiv_val (Y : NePoly B₁) : (NePoly.mapEquiv e Y).1 = Y.1.map e.toEmbedding :=
  rfl

variable {cs₁ cs₂ e}

theorem contact_relabel (hcs : ∀ x, cs₂ (ψ x) = (cs₁ x).map e.toEmbedding) (a b : E₁) :
    Contact cs₂ (ψ a) (ψ b) ↔ Contact cs₁ a b := by
  unfold Contact
  rw [hcs, hcs, Finset.disjoint_map]

theorem reach_relabel (hcs : ∀ x, cs₂ (ψ x) = (cs₁ x).map e.toEmbedding) (D : Finset E₁)
    (a b : E₁) : Reach cs₂ (D.map ψ.toEmbedding) (ψ a) (ψ b) ↔ Reach cs₁ D a b := by
  constructor
  · intro h
    have key : ∀ x y, Relation.ReflTransGen
        (fun x y => x ∈ D.map ψ.toEmbedding ∧ y ∈ D.map ψ.toEmbedding ∧ Contact cs₂ x y) x y →
        Reach cs₁ D (ψ.symm x) (ψ.symm y) := by
      intro x y hxy
      induction hxy with
      | refl => exact Reach.refl _ _ _
      | @tail b c _ hbc ih =>
        obtain ⟨hb, hy, hc⟩ := hbc
        have mem : ∀ x, x ∈ D.map ψ.toEmbedding → ψ.symm x ∈ D := fun x hx => by
          obtain ⟨d, hd, rfl⟩ := Finset.mem_map.1 hx
          simpa using hd
        refine ih.trans _ (Reach.single _ (mem _ hb) (mem _ hy) ?_)
        have := (contact_relabel ψ hcs (ψ.symm b) (ψ.symm c)).1
        simpa using this (by simpa using hc)
    simpa using key _ _ h
  · intro h
    refine Relation.ReflTransGen.lift ψ (fun x y hxy => ?_) a b h
    obtain ⟨hx, hy, hc⟩ := hxy
    exact ⟨Finset.mem_map_of_mem _ hx, Finset.mem_map_of_mem _ hy, (contact_relabel ψ hcs x y).2 hc⟩

theorem unionCs_relabel (hcs : ∀ x, cs₂ (ψ x) = (cs₁ x).map e.toEmbedding) (C : Finset E₁)
    [DecidableEq B₁] [DecidableEq B₂] :
    unionCs cs₂ (C.map ψ.toEmbedding) = (unionCs cs₁ C).map e.toEmbedding := by
  ext b
  simp only [unionCs, Finset.mem_biUnion, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hb⟩
    rw [hcs, Finset.mem_map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨a, ⟨x, hx, ha⟩, rfl⟩
  · rintro ⟨a, ⟨x, hx, ha⟩, rfl⟩
    exact ⟨ψ x, ⟨x, hx, rfl⟩, by rw [hcs]; exact Finset.mem_map_of_mem _ ha⟩

theorem connSet_relabel (hcs : ∀ x, cs₂ (ψ x) = (cs₁ x).map e.toEmbedding) (C : Finset E₁) :
    ConnSet cs₂ (C.map ψ.toEmbedding) ↔ ConnSet cs₁ C := by
  unfold ConnSet
  rw [Finset.map_nonempty]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h s hs s' hs'
    exact (reach_relabel ψ hcs C s s').1 (h _ (Finset.mem_map_of_mem _ hs) _
      (Finset.mem_map_of_mem _ hs'))
  · intro h s hs s' hs'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hs
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 hs'
    exact (reach_relabel ψ hcs C a b).2 (h a ha b hb)

theorem mem_Cfam_relabel [Fintype E₁] [Fintype E₂] [DecidableEq B₁] [DecidableEq B₂]
    (hcs : ∀ x, cs₂ (ψ x) = (cs₁ x).map e.toEmbedding) (C : Finset E₁) (Y : Finset B₁) :
    C.map ψ.toEmbedding ∈ Cfam cs₂ (fun _ : Finset E₂ => True) (Y.map e.toEmbedding) ↔
      C ∈ Cfam cs₁ (fun _ : Finset E₁ => True) Y := by
  rw [mem_Cfam, mem_Cfam, connSet_relabel ψ hcs, unionCs_relabel ψ hcs, Finset.map_inj]

theorem polyAct_relabel [Fintype E₁] [Fintype E₂] [Fintype B₁] [Fintype B₂]
    (hcs : ∀ x, cs₂ (ψ x) = (cs₁ x).map e.toEmbedding) {w₁ : E₁ → ℂ} {w₂ : E₂ → ℂ}
    (hw : ∀ x, w₂ (ψ x) = w₁ x) (Y : NePoly B₁) :
    polyAct cs₂ (fun _ : Finset E₂ => True) w₂ (NePoly.mapEquiv e Y) =
      polyAct cs₁ (fun _ : Finset E₁ => True) w₁ Y := by
  unfold polyAct
  rw [NePoly.mapEquiv_val]
  symm
  refine Finset.sum_nbij' (fun C => C.map ψ.toEmbedding) (fun C => C.map ψ.symm.toEmbedding)
    (fun C hC => (mem_Cfam_relabel ψ hcs C Y.1).2 hC) (fun C hC => ?_) (fun C _ => ?_)
    (fun C _ => ?_) (fun C _ => ?_)
  · have : C = (C.map ψ.symm.toEmbedding).map ψ.toEmbedding := by
      ext x; simp
    rw [this] at hC
    exact (mem_Cfam_relabel ψ hcs _ Y.1).1 hC
  · ext x; simp
  · ext x; simp
  · rw [Finset.prod_map]
    exact Finset.prod_congr rfl fun x _ => (hw x).symm

end Mayer

section Measure

variable {T₁ T₂ B₁ B₂ : Type*} [Fintype T₁] [Fintype T₂] [Fintype B₁] [Fintype B₂]
  {Ω₁ : B₁ → Type*} {Ω₂ : B₂ → Type*} [∀ b, MeasurableSpace (Ω₁ b)]
  [∀ b, MeasurableSpace (Ω₂ b)] (μ₁ : ∀ b, Measure (Ω₁ b)) (μ₂ : ∀ b, Measure (Ω₂ b))
  {sup₁ : T₁ → Finset B₁} {sup₂ : T₂ → Finset B₂} (ψ : T₁ ≃ T₂) (e : B₁ ≃ B₂)
  (T : (∀ b, Ω₁ b) ≃ᵐ (∀ b, Ω₂ b)) (hT : MeasurePreserving T (Measure.pi μ₁) (Measure.pi μ₂))

include hT

/-- **The activities of the Mayer layer are invariant under a measure-preserving equivalence of
the configuration spaces** that carries the terms of one system to those of the other. -/
theorem mayerK_relabel (hsup : ∀ x, sup₂ (ψ x) = (sup₁ x).map e.toEmbedding)
    {H₁ : T₁ → (∀ b, Ω₁ b) → ℂ} {H₂ : T₂ → (∀ b, Ω₂ b) → ℂ} {Q : Set (∀ b, Ω₁ b)}
    (hQ : ∀ᵐ Φ ∂(Measure.pi μ₁), Φ ∈ Q) (hH : ∀ Φ ∈ Q, ∀ t, H₂ (ψ t) (T Φ) = H₁ t Φ)
    (Y : NePoly B₁) :
    mayerK μ₂ sup₂ H₂ (NePoly.mapEquiv e Y) = mayerK μ₁ sup₁ H₁ Y := by
  unfold mayerK
  rw [← hT.integral_comp' (g := fun Φ => mayerAct sup₂ H₂ (NePoly.mapEquiv e Y) Φ)]
  refine integral_congr_ae ?_
  filter_upwards [hQ] with Φ hΦ
  unfold mayerAct
  exact polyAct_relabel ψ hsup (fun x => by simp only [hH Φ hΦ x]) Y

variable {ι : Type*} [Fintype ι]

/-- The activities with marks are invariant likewise. -/
theorem marksK_relabel (hsup : ∀ x, sup₂ (ψ x) = (sup₁ x).map e.toEmbedding)
    {a₁ : T₁ → (∀ b, Ω₁ b) → ℂ} {a₂ : T₂ → (∀ b, Ω₂ b) → ℂ}
    {g₁ : ι → T₁ → (∀ b, Ω₁ b) → ℂ} {g₂ : ι → T₂ → (∀ b, Ω₂ b) → ℂ} {Q : Set (∀ b, Ω₁ b)}
    (hQ : ∀ᵐ Φ ∂(Measure.pi μ₁), Φ ∈ Q) (ha : ∀ Φ ∈ Q, ∀ t, a₂ (ψ t) (T Φ) = a₁ t Φ)
    (hg : ∀ Φ ∈ Q, ∀ i t, g₂ i (ψ t) (T Φ) = g₁ i t Φ) (Y : NePoly B₁) (l : ι → ℂ) :
    marksK μ₂ sup₂ a₂ g₂ (NePoly.mapEquiv e Y) l = marksK μ₁ sup₁ a₁ g₁ Y l := by
  unfold marksK
  refine mayerK_relabel μ₁ μ₂ ψ e T hT hsup hQ (fun Φ hΦ t => ?_) Y
  unfold Hlam
  simp only [ha Φ hΦ, hg Φ hΦ]

end Measure

end Balaban.Polymer
