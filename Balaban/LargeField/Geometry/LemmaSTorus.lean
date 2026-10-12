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

/-- The lift of a sub-box `box c t ⊆ box a s` (`2 t_i < n`) is the integer box
`[ι c, ι c + t - 1]`. -/
theorem boxLift_image_subbox (hs : ∀ i, 2 * s i < n) {c : Torus d n} {t : Fin d → ℕ}
    (ht1 : ∀ i, 1 ≤ t i) (ht2 : ∀ i, 2 * t i < n) (hsub : box c t ⊆ box a s) :
    boxLift a '' box c t = Set.Icc (boxLift a c) (fun i => boxLift a c i + t i - 1) := by
  have hc : c ∈ box a s := hsub fun i => ⟨0, ht1 i, by simp⟩
  have hpc := (mem_box_iff hs).mp hc
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hpy := (mem_box_iff hs).mp (hsub hy)
    refine ⟨fun i => ?_, fun i => ?_⟩ <;>
    · obtain ⟨k, hk, hyk⟩ := hy i
      have e : ((pos (a i) (y i) : ℤ) : ZMod n) = (((pos (a i) (c i) : ℤ) + k : ℤ) : ZMod n) := by
        push_cast; rw [natCast_pos, natCast_pos, hyk]; ring
      have := int_eq_of_cast_eq e (by
        have := hpy i; have := hpc i; have := hs i; have := ht2 i
        rw [abs_lt]; constructor <;> omega)
      simp only [boxLift]
      omega
  · intro hz
    have hz1 : ∀ i, boxLift a c i ≤ z i := hz.1
    have hz2 : ∀ i, z i ≤ boxLift a c i + t i - 1 := hz.2
    have hy : (fun i => (z i : ZMod n)) ∈ box c t := fun i => by
      refine ⟨(z i - boxLift a c i).toNat, by have := hz1 i; have := hz2 i; omega, ?_⟩
      have h3 : (((z i - boxLift a c i).toNat : ℕ) : ℤ) = z i - boxLift a c i := by
        have := hz1 i; omega
      have h4 : ((((z i - boxLift a c i).toNat : ℕ) : ℤ) : ZMod n) =
          ((z i - boxLift a c i : ℤ) : ZMod n) := by rw [h3]
      rw [Int.cast_natCast] at h4
      rw [h4]; push_cast; rw [boxLift_cast]; ring
    refine ⟨_, hy, ?_⟩
    funext i
    have hyQ := (mem_box_iff hs).mp (hsub hy) i
    have e : ((boxLift a (fun i => (z i : ZMod n)) i : ℤ) : ZMod n) = (z i : ZMod n) := by
      rw [boxLift_cast]
    have hcQ := (mem_box_iff hs).mp hc i
    refine int_eq_of_cast_eq e ?_
    have := hz1 i; have := hz2 i; have := hs i; have := ht2 i
    simp only [boxLift] at *
    rw [abs_lt]; constructor <;> omega

/-- The lift of the `*`-component of a point of `T ⊆ Q` is the `*`-component of its lift. -/
theorem boxLift_image_starComp (hs : ∀ i, 2 * s i < n) {T : Set (Torus d n)} (hT : T ⊆ box a s)
    {p : Torus d n} (hp : p ∈ T) :
    boxLift a '' starComp T p = LatticeGeom.starComp (boxLift a '' T) (boxLift a p) := by
  ext c
  constructor
  · rintro ⟨b, ⟨hbT, hl⟩, rfl⟩
    show LatticeGeom.StarConn _ _ _
    clear hbT
    induction hl with
    | refl => exact Relation.ReflTransGen.refl
    | @tail w w' _ hstep ih =>
      exact ih.tail ⟨⟨w, hstep.1, rfl⟩, ⟨w', hstep.2.1, rfl⟩,
        (starNear_boxLift_iff hs (hT hstep.1) (hT hstep.2.1)).mp (by
          have := hstep.2.2; omega)⟩
  · intro hc
    have key : ∀ c, LatticeGeom.StarConn (boxLift a '' T) (boxLift a p) c →
        ∃ w, boxLift a w = c ∧ w ∈ T ∧ Linked 2 T p w := by
      intro c hc
      induction hc with
      | refl => exact ⟨p, rfl, hp, Linked.refl _⟩
      | @tail b c' _ hstep ih =>
        obtain ⟨w, rfl, hwT, hw⟩ := ih
        obtain ⟨⟨p', hp', hpb⟩, ⟨q, hq, rfl⟩, hnn⟩ := hstep
        have hpw : p' = w := boxLift_injective a hpb
        subst hpw
        refine ⟨q, rfl, hq, hw.trans (Linked.single hp' hq ?_)⟩
        have := (starNear_boxLift_iff hs (hT hp') (hT hq)).mpr hnn
        omega
    obtain ⟨w, rfl, hwT, hw⟩ := key c hc
    exact ⟨w, ⟨hwT, hw⟩, rfl⟩

variable {ι : Type*} [Finite ι]

/-- **Lemma S (c), torus form**: a union of pairwise `*`-separated sub-boxes of `Q^{∼-1}` (of side
`< n/2`) encloses no point: every `x ∈ Q^{∼-1}` outside them is joined to `∂Q` by an nn path in
`Q` avoiding them. -/
theorem torus_path_to_shell_of_boxes (hd : 2 ≤ d) (hs : ∀ i, 1 ≤ s i ∧ 2 * s i < n)
    {c : ι → Torus d n} {t : ι → Fin d → ℕ} (ht1 : ∀ j i, 1 ≤ t j i) (ht2 : ∀ j i, 2 * t j i < n)
    (hsub : ∀ j, box (c j) (t j) ⊆ nbhdNeg 1 (box a s))
    (hsep : ∀ j k, j ≠ k → ∀ y ∈ box (c j) (t j), ∀ y' ∈ box (c k) (t k), 2 ≤ supDist y y')
    {x : Torus d n} (hx : x ∈ nbhdNeg 1 (box a s)) (hxA : x ∉ ⋃ j, box (c j) (t j)) :
    ∃ z ∈ box a s, z ∉ nbhdNeg 1 (box a s) ∧ TConn (box a s \ ⋃ j, box (c j) (t j)) x z := by
  have hs2 : ∀ i, 2 * s i < n := fun i => (hs i).2
  have hQ := nbhdNeg_subset 1 (box a s)
  have hsubQ : ∀ j, box (c j) (t j) ⊆ box a s := fun j => (hsub j).trans hQ
  have hA : (⋃ j, box (c j) (t j)) ⊆ nbhdNeg 1 (box a s) := Set.iUnion_subset hsub
  have := (exists_shell_path_iff_not_enclosed_torus hs hA hx hxA).mpr
  apply this
  rw [Set.image_iUnion]
  simp only [fun j => boxLift_image_subbox hs2 (ht1 j) (ht2 j) (hsubQ j)]
  refine LatticeGeom.not_enclosed_boxes hd (fun j => boxLift a (c j))
    (fun j i => boxLift a (c j) i + t j i - 1) ?_ _
  intro j k hjk u hu v hv hnear
  have hu' : u ∈ boxLift a '' box (c j) (t j) := by
    rwa [boxLift_image_subbox hs2 (ht1 j) (ht2 j) (hsubQ j)]
  have hv' : v ∈ boxLift a '' box (c k) (t k) := by
    rwa [boxLift_image_subbox hs2 (ht1 k) (ht2 k) (hsubQ k)]
  obtain ⟨y, hy, rfl⟩ := hu'
  obtain ⟨y', hy', rfl⟩ := hv'
  have h1 := (starNear_boxLift_iff hs2 (hsubQ j hy) (hsubQ k hy')).mpr hnear
  have := hsep j k hjk y hy y' hy'
  omega

omit [Finite ι] in
/-- Common setup of Lemma S (a), (b) on the torus: the lifts of a family of pairwise
`*`-separated subsets of `Q^{∼-1}` are `*`-separated subsets of `ℤ^d`. -/
theorem starSeparated_boxLift (hs : ∀ i, 2 * s i < n) {A : ι → Set (Torus d n)}
    (hA : ∀ j, A j ⊆ box a s)
    (hsep : ∀ j k, j ≠ k → ∀ y ∈ A j, ∀ y' ∈ A k, 2 ≤ supDist y y') :
    LatticeGeom.StarSeparated fun j => boxLift a '' A j := by
  rintro j k hjk _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ hnear
  have := (starNear_boxLift_iff hs (hA j hy) (hA k hy')).mpr hnear
  have := hsep j k hjk y hy y' hy'
  omega

/-- **Lemma S (a), torus form**: if `x ∈ Q^{∼-1}` is not joined to `∂Q` by an nn path in
`Q ∖ ⋃_j A_j` (`A_j ⊆ Q^{∼-1}` pairwise `*`-separated), then for one `*`-component
`K = starComp (A_j) p` of one `A_j`, `x` is not joined to `∂Q` by an nn path in `Q ∖ K`. -/
theorem torus_enclosed_by_single_component (hd : 2 ≤ d) (hs : ∀ i, 1 ≤ s i ∧ 2 * s i < n)
    {A : ι → Set (Torus d n)} (hA : ∀ j, A j ⊆ nbhdNeg 1 (box a s))
    (hsep : ∀ j k, j ≠ k → ∀ y ∈ A j, ∀ y' ∈ A k, 2 ≤ supDist y y')
    {x : Torus d n} (hx : x ∈ nbhdNeg 1 (box a s)) (hxA : x ∉ ⋃ j, A j)
    (hno : ¬ ∃ z ∈ box a s, z ∉ nbhdNeg 1 (box a s) ∧ TConn (box a s \ ⋃ j, A j) x z) :
    ∃ j, ∃ p ∈ A j, ¬ ∃ z ∈ box a s, z ∉ nbhdNeg 1 (box a s) ∧
      TConn (box a s \ starComp (A j) p) x z := by
  have hs2 : ∀ i, 2 * s i < n := fun i => (hs i).2
  have hQ := nbhdNeg_subset 1 (box a s)
  have hAQ : ∀ j, A j ⊆ box a s := fun j => (hA j).trans hQ
  have hU : (⋃ j, A j) ⊆ nbhdNeg 1 (box a s) := Set.iUnion_subset hA
  have henc : LatticeGeom.Enclosed (⋃ j, boxLift a '' A j) (boxLift a x) := by
    have := (exists_shell_path_iff_not_enclosed_torus hs hU hx hxA).not.mp hno
    rwa [not_not, Set.image_iUnion] at this
  obtain ⟨j, a', ha', hK⟩ := LatticeGeom.enclosed_by_single_component hd
    (fun j => (Set.toFinite _ : (boxLift a '' A j).Finite))
    (starSeparated_boxLift hs2 hAQ hsep) henc
  obtain ⟨p, hp, rfl⟩ := ha'
  refine ⟨j, p, hp, ?_⟩
  rw [← boxLift_image_starComp hs2 (hAQ j) hp] at hK
  have hKA : starComp (A j) p ⊆ A j := fun b hb => hb.1
  refine (exists_shell_path_iff_not_enclosed_torus hs (hKA.trans (hA j)) hx
    (fun h => hxA (Set.mem_iUnion.mpr ⟨j, hKA h⟩))).not.mpr (not_not.mpr hK) 

/-- **Lemma S (b), torus form**: if moreover a sub-box `Q' = box c t ⊆ Q ∖ ⋃_j A_j` (`2 t_i < n`)
contains `x`, the `*`-component `K` has, for every coordinate `i`, two points at index distance
`≥ t_i + 1` (sup-diameter `≥ side(Q') + 1`). -/
theorem torus_enclosed_component_diam (hd : 2 ≤ d) (hs : ∀ i, 1 ≤ s i ∧ 2 * s i < n)
    {A : ι → Set (Torus d n)} (hA : ∀ j, A j ⊆ nbhdNeg 1 (box a s))
    (hsep : ∀ j k, j ≠ k → ∀ y ∈ A j, ∀ y' ∈ A k, 2 ≤ supDist y y')
    {x : Torus d n} (hx : x ∈ nbhdNeg 1 (box a s)) (hxA : x ∉ ⋃ j, A j)
    (hno : ¬ ∃ z ∈ box a s, z ∉ nbhdNeg 1 (box a s) ∧ TConn (box a s \ ⋃ j, A j) x z)
    {c : Torus d n} {t : Fin d → ℕ} (ht1 : ∀ i, 1 ≤ t i) (ht2 : ∀ i, 2 * t i < n)
    (hQ' : box c t ⊆ box a s \ ⋃ j, A j) (hxQ' : x ∈ box c t) :
    ∃ j, ∃ p ∈ A j, (¬ ∃ z ∈ box a s, z ∉ nbhdNeg 1 (box a s) ∧
      TConn (box a s \ starComp (A j) p) x z) ∧
      ∀ i, ∃ y ∈ starComp (A j) p, ∃ z ∈ starComp (A j) p, t i + 1 ≤ supDist y z := by
  have hs2 : ∀ i, 2 * s i < n := fun i => (hs i).2
  have hQ := nbhdNeg_subset 1 (box a s)
  have hAQ : ∀ j, A j ⊆ box a s := fun j => (hA j).trans hQ
  have hU : (⋃ j, A j) ⊆ nbhdNeg 1 (box a s) := Set.iUnion_subset hA
  have hsubQ : box c t ⊆ box a s := fun y hy => (hQ' hy).1
  have henc : LatticeGeom.Enclosed (⋃ j, boxLift a '' A j) (boxLift a x) := by
    have := (exists_shell_path_iff_not_enclosed_torus hs hU hx hxA).not.mp hno
    rwa [not_not, Set.image_iUnion] at this
  have himg := boxLift_image_subbox hs2 ht1 ht2 hsubQ
  have hQc : Set.Icc (boxLift a c) (fun i => boxLift a c i + t i - 1) ⊆
      (⋃ j, boxLift a '' A j)ᶜ := by
    rw [← himg]
    rintro _ ⟨y, hy, rfl⟩ hmem
    obtain ⟨j, w, hw, hwy⟩ := Set.mem_iUnion.mp hmem
    have := boxLift_injective a hwy
    subst this
    exact (hQ' hy).2 (Set.mem_iUnion.mpr ⟨j, hw⟩)
  obtain ⟨j, a', ha', hK, hdiam⟩ := LatticeGeom.enclosed_component_diam hd
    (fun j => (Set.toFinite _ : (boxLift a '' A j).Finite))
    (starSeparated_boxLift hs2 hAQ hsep) henc (boxLift a c) (fun i => boxLift a c i + t i - 1) hQc
    (by rw [← himg]; exact ⟨x, hxQ', rfl⟩)
  obtain ⟨p, hp, rfl⟩ := ha'
  refine ⟨j, p, hp, ?_, fun i => ?_⟩
  · rw [← boxLift_image_starComp hs2 (hAQ j) hp] at hK
    have hKA : starComp (A j) p ⊆ A j := fun b hb => hb.1
    exact (exists_shell_path_iff_not_enclosed_torus hs (hKA.trans (hA j)) hx
      (fun h => hxA (Set.mem_iUnion.mpr ⟨j, hKA h⟩))).not.mpr (not_not.mpr hK)
  · obtain ⟨y', hy', z', hz', hle⟩ := hdiam i
    rw [← boxLift_image_starComp hs2 (hAQ j) hp] at hy' hz'
    obtain ⟨y, hy, rfl⟩ := hy'
    obtain ⟨z, hz, rfl⟩ := hz'
    refine ⟨y, hy, z, hz, ?_⟩
    have hyA := (hAQ j) hy.1
    have hzA := (hAQ j) hz.1
    by_contra hlt
    push Not at hlt
    have := (supDist_le_iff_boxLift hs2 hyA hzA (supDist y z)).mp le_rfl i
    rw [abs_le] at this
    omega

end Balaban.LargeField
