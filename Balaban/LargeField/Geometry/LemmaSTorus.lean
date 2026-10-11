module

public import Balaban.LargeField.Geometry.TorusLift
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lemma S on the cube torus (Part I, Lemma I.3.13, torus version)

Let `Q = box a s` be a box of `𝕋_k` with `2 s_i < n` (a small box), `Q^{∼-1} = nbhdNeg 1 Q` its
interior and `∂Q = Q ∖ Q^{∼-1}`. Via the injective lift `boxLift a` (Lemma I.2.10 (e)) the nn paths
inside `Q` correspond to nn paths in `ℤ^d` inside the integer box, and `Q^{∼-1}` to its interior.

* `exists_shell_path_iff_not_enclosed_torus`: for `A ∪ {x} ⊆ Q^{∼-1}`, `x` is joined to `∂Q` by an nn
  path in `Q ∖ A` iff the lift of `x` is not enclosed by the lift of `A` (the W31 theorem
  `Balaban.LatticeGeom.exists_shell_path_iff_not_enclosed` through the lift).
* `torus_path_to_shell_of_boxes` (Lemma S (c)): for pairwise `*`-separated boxes inside `Q^{∼-1}`,
  every point of `Q^{∼-1}` outside them is joined to `∂Q` by an nn path in `Q` avoiding them.
* `torus_enclosed_by_single_component` (Lemma S (a)) and `torus_enclosed_component_diam`
  (Lemma S (b)).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban

variable {d n : ℕ} [NeZero n] {a : Torus d n} {s : Fin d → ℕ}

/-- nn-connectivity inside `S` on the torus. -/
def TConn (S : Set (Torus d n)) : Torus d n → Torus d n → Prop :=
  Relation.ReflTransGen fun p q => p ∈ S ∧ q ∈ S ∧ NNAdj p q

/-- **Interior under the lift**: for `y ∈ Q`, `y ∈ Q^{∼-1}` iff the lift of `y` lies in the interior
of the integer box. -/
theorem mem_nbhdNeg_box_iff (hs : ∀ i, 1 ≤ s i ∧ 2 * s i < n) {y : Torus d n} (hy : y ∈ box a s) :
    y ∈ nbhdNeg 1 (box a s) ↔ boxLift a y ∈ LatticeGeom.boxInterior
      (fun i => ((a i).val : ℤ)) (fun i => ((a i).val : ℤ) + s i - 1) := by
  have hs2 : ∀ i, 2 * s i < n := fun i => (hs i).2
  have hp := (mem_box_iff hs2).mp hy
  rw [mem_nbhdNeg]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i => ?_⟩
    · show ((a i).val : ℤ) + 1 ≤ ((a i).val : ℤ) + pos (a i) (y i)
      by_contra hlt
      have h0 : pos (a i) (y i) = 0 := by omega
      have hz := h (Function.update y i (y i - 1)) (by
        refine supDist_le_iff.mpr fun j => ?_
        by_cases hj : j = i
        · subst hj
          simp only [Function.update_self, sub_sub_cancel]
          exact (cycNorm_le_iff _ _).mpr ⟨1, by simp, by simp⟩
        · simp [Function.update, hj, cycNorm])
      have := (mem_box_iff hs2).mp hz i
      simp only [Function.update_self] at this
      have e : y i = a i := by have := eq_add_pos (a i) (y i); rwa [h0, Nat.cast_zero, add_zero] at this
      have e2 : pos (a i) (a i - 1) = n - 1 := by
        unfold pos
        rw [sub_sub_cancel_left]
        have : ((n - 1 : ℕ) : ZMod n) = -1 := by
          rw [Nat.cast_sub (NeZero.one_le), ZMod.natCast_self]; simp
        rw [← this, ZMod.val_natCast_of_lt (by have := NeZero.pos n; omega)]
      rw [e, e2] at this
      have := hs2 i
      omega
    · show ((a i).val : ℤ) + pos (a i) (y i) ≤ ((a i).val : ℤ) + s i - 1 - 1
      by_contra hlt
      have h0 : pos (a i) (y i) = s i - 1 := by have := hp i; have := (hs i).1; omega
      have hz := h (Function.update y i (y i + 1)) (by
        refine supDist_le_iff.mpr fun j => ?_
        by_cases hj : j = i
        · subst hj
          simp only [Function.update_self]
          exact (cycNorm_le_iff _ _).mpr ⟨-1, by simp, by simp⟩
        · simp [Function.update, hj, cycNorm])
      have := (mem_box_iff hs2).mp hz i
      simp only [Function.update_self] at this
      have e : y i + 1 = a i + ((s i : ℕ) : ZMod n) := by
        have h1 := eq_add_pos (a i) (y i)
        rw [h0] at h1
        rw [h1]
        have : (((s i - 1 : ℕ)) : ZMod n) + 1 = ((s i : ℕ) : ZMod n) := by
          rw [← Nat.cast_succ]; congr 1; have := (hs i).1; omega
        rw [add_assoc, this]
      rw [e, pos_add_natCast _ (by have := hs2 i; omega)] at this
      omega
  · intro hint z hz
    have hz' : ∀ i, z i ∈ cycInt (a i) (s i) := fun i => by
      rw [mem_cycInt_iff (by have := hs2 i; omega)]
      obtain ⟨t, ht, hte⟩ := (cycNorm_le_iff (n := n) (y i - z i) 1).mp
        (by simpa using supDist_le_iff.mp hz i)
      have ht' := abs_le.mp ht
      have h1 : ((a i).val : ℤ) + 1 ≤ ((a i).val : ℤ) + pos (a i) (y i) := hint.1 i
      have h2 : ((a i).val : ℤ) + pos (a i) (y i) ≤ ((a i).val : ℤ) + s i - 1 - 1 := hint.2 i
      have e : z i = a i + (((pos (a i) (y i) : ℤ) - t).toNat : ℕ) := by
        have h3 : ((((pos (a i) (y i) : ℤ) - t).toNat : ℕ) : ℤ) = (pos (a i) (y i) : ℤ) - t := by
          omega
        have h4 : ((((pos (a i) (y i) : ℤ) - t).toNat : ℕ) : ZMod n) =
            ((pos (a i) (y i) : ℤ) : ZMod n) - (t : ZMod n) := by
          rw [← Int.cast_natCast, h3]; push_cast; rfl
        rw [h4, hte]
        push_cast
        rw [natCast_pos]; ring
      rw [e, pos_add_natCast _ (by have := hs2 i; omega)]
      omega
    exact hz'

omit [NeZero n] in
theorem nbhdNeg_subset (m : ℕ) (X : Set (Torus d n)) : nbhdNeg m X ⊆ X := by
  intro y hy
  exact mem_nbhdNeg.mp hy y (by simp [supDist_self])

/-- nn-connectivity inside `S ⊆ Q` on the torus is nn-connectivity of the lift in `ℤ^d`. -/
theorem tconn_iff_conn (hs : ∀ i, 2 * s i < n) {S : Set (Torus d n)} (hS : S ⊆ box a s)
    (x z : Torus d n) :
    TConn S x z ↔ LatticeGeom.Conn (boxLift a '' S) (boxLift a x) (boxLift a z) := by
  constructor
  · intro h
    induction h with
    | refl => exact LatticeGeom.Conn.refl _
    | @tail w w' _ hstep ih =>
      exact ih.tail ⟨w', hstep.2.1, rfl⟩ ⟨w, hstep.1, rfl⟩
        ((nnAdj_boxLift_iff hs (hS hstep.1) (hS hstep.2.1)).mp hstep.2.2)
  · intro h
    have key : ∀ c, LatticeGeom.Conn (boxLift a '' S) (boxLift a x) c →
        ∃ w, boxLift a w = c ∧ TConn S x w := by
      intro c hc
      induction hc with
      | refl => exact ⟨x, rfl, Relation.ReflTransGen.refl⟩
      | @tail b c' _ hstep ih =>
        obtain ⟨w, rfl, hw⟩ := ih
        obtain ⟨⟨p, hp, hpb⟩, ⟨q, hq, rfl⟩, hnn⟩ := hstep
        have hpw : p = w := boxLift_injective a hpb
        subst hpw
        exact ⟨q, rfl, hw.tail ⟨hp, hq, (nnAdj_boxLift_iff hs (hS hp) (hS hq)).mpr hnn⟩⟩
    obtain ⟨w, hw, hxw⟩ := key _ h
    rwa [boxLift_injective a hw] at hxw

/-- **Lemma S, torus form**: for `A ∪ {x} ⊆ Q^{∼-1}` (`Q` a small box), `x` is joined to
`∂Q = Q ∖ Q^{∼-1}` by an nn path in `Q ∖ A` iff the lift of `x` is not enclosed by the lift of
`A` (W31: `Balaban.LatticeGeom.exists_shell_path_iff_not_enclosed`). -/
theorem exists_shell_path_iff_not_enclosed_torus (hs : ∀ i, 1 ≤ s i ∧ 2 * s i < n)
    {A : Set (Torus d n)} (hA : A ⊆ nbhdNeg 1 (box a s)) {x : Torus d n}
    (hx : x ∈ nbhdNeg 1 (box a s)) (hxA : x ∉ A) :
    (∃ z ∈ box a s, z ∉ nbhdNeg 1 (box a s) ∧ TConn (box a s \ A) x z) ↔
      ¬ LatticeGeom.Enclosed (boxLift a '' A) (boxLift a x) := by
  have hs2 : ∀ i, 2 * s i < n := fun i => (hs i).2
  have hQ := nbhdNeg_subset 1 (box a s)
  have hAint : boxLift a '' A ⊆ LatticeGeom.boxInterior (fun i => ((a i).val : ℤ))
      (fun i => ((a i).val : ℤ) + s i - 1) := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_nbhdNeg_box_iff hs (hQ (hA hy))).mp (hA hy)
  have hxint := (mem_nbhdNeg_box_iff hs (hQ hx)).mp hx
  rw [← LatticeGeom.exists_shell_path_iff_not_enclosed _ _ hAint hxint
    (fun h => hxA (by obtain ⟨y, hy, hyx⟩ := h; rwa [← boxLift_injective a hyx]))]
  have himg : boxLift a '' (box a s \ A) = Set.Icc (fun i => ((a i).val : ℤ))
      (fun i => ((a i).val : ℤ) + s i - 1) \ boxLift a '' A := by
    rw [(boxLift_injective a).injOn.image_sdiff, boxLift_image hs2,
      Set.inter_eq_right.mpr (fun y hy => hQ (hA hy))]
  constructor
  · rintro ⟨z, hz, hzn, hc⟩
    refine ⟨boxLift a z, boxLift_mem_Icc hs2 hz, ?_, ?_⟩
    · rwa [← mem_nbhdNeg_box_iff hs hz]
    · rw [← himg]; exact (tconn_iff_conn hs2 Set.sdiff_subset x z).mp hc
  · rintro ⟨z', hz', hzn, hc⟩
    obtain ⟨z, hz, rfl⟩ := exists_box_of_mem_Icc hs2 hz'
    refine ⟨z, hz, ?_, ?_⟩
    · rwa [mem_nbhdNeg_box_iff hs hz]
    · rw [← himg] at hc
      exact (tconn_iff_conn hs2 Set.sdiff_subset x z).mpr hc

end Balaban.LargeField
