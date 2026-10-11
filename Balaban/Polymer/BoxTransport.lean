module

public import Balaban.Polymer.Transport
public import Balaban.Polymer.Support
public import Balaban.Polymer.BlockTorus
public import Balaban.Polymer.FrozenTorus

/-!
# Torus independence of the local terms

PE (f) for block tori.  Blocks of the torus `Torus d m` whose centred coordinates
(`ZMod.valMinAbs`) are bounded by `r < (m - 1) / 2` form a box without wrap-around: there the
nearest-neighbour structure is that of `ℤ^d`.  `boxMap m m'` identifies the boxes of two tori, and
`PY_boxMap` shows that the local terms of a set of blocks `Y` in the box agree on the two tori as
soon as the activities of the polymers inside `Y` agree under the identification.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

section Animal

variable {B B' : Type*}

/-- Partial isomorphisms preserve connected sets. -/
theorem isAnimal_image [DecidableEq B'] (H : SimpleGraph B) (H' : SimpleGraph B') (e : B → B') (Z : Finset B)
    (hadj : ∀ a ∈ Z, ∀ b ∈ Z, H.Adj a b → H'.Adj (e a) (e b)) (hZ : IsAnimal H Z) :
    IsAnimal H' (Z.image e) := by
  rw [isAnimal_iff] at hZ ⊢
  refine ⟨hZ.1.image e, fun x hx y hy => ?_⟩
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  refine Relation.ReflTransGen.lift e (r := fun a b => a ∈ Z ∧ b ∈ Z ∧ H.Adj a b)
    (p := fun a b => a ∈ Z.image e ∧ b ∈ Z.image e ∧ H'.Adj a b) ?_ _ _ (hZ.2 a ha b hb)
  intro a b ⟨ha, hb, hab⟩
  exact ⟨Finset.mem_image_of_mem e ha, Finset.mem_image_of_mem e hb, hadj a ha b hb hab⟩

end Animal

variable (d : ℕ)

/-- Blocks with centred coordinates in `[-r, r]`. -/
def InBox (r m : ℕ) (c : Balaban.Torus d m) : Prop := ∀ μ, |(c μ).valMinAbs| ≤ r

variable {d}

/-- The identification of the boxes of two tori through centred representatives. -/
def boxMap (m m' : ℕ) (c : Balaban.Torus d m) : Balaban.Torus d m' :=
  fun μ => (((c μ).valMinAbs : ℤ) : ZMod m')

section Box

variable {r m m' : ℕ}

theorem valMinAbs_intCast_of_abs_le {m : ℕ} (hm : 2 * r + 1 < m) {z : ℤ}
    (hz : |z| ≤ r) : ((z : ℤ) : ZMod m).valMinAbs = z := by
  have : NeZero m := ⟨by omega⟩
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  rw [abs_le] at hz
  constructor <;> omega

theorem valMinAbs_boxMap (hm' : 2 * r + 1 < m') {c : Balaban.Torus d m} (hc : InBox d r m c)
    (μ : Fin d) : (boxMap m m' c μ).valMinAbs = (c μ).valMinAbs :=
  valMinAbs_intCast_of_abs_le hm' (hc μ)

theorem inBox_boxMap (hm' : 2 * r + 1 < m') {c : Balaban.Torus d m} (hc : InBox d r m c) :
    InBox d r m' (boxMap m m' c) := fun μ => by
  rw [valMinAbs_boxMap hm' hc]; exact hc μ

theorem boxMap_boxMap (hm' : 2 * r + 1 < m') {c : Balaban.Torus d m}
    (hc : InBox d r m c) : boxMap m' m (boxMap m m' c) = c := by
  funext μ
  show (((boxMap m m' c μ).valMinAbs : ℤ) : ZMod m) = c μ
  rw [valMinAbs_boxMap hm' hc, ZMod.coe_valMinAbs]

theorem int_eq_of_cast_eq (hm : 2 * r + 1 < m) {z w : ℤ} (hz : |z| ≤ r) (hw : |w| ≤ r)
    (h : ((w : ℤ) : ZMod m) = ((z : ℤ) : ZMod m) + 1) : w = z + 1 := by
  have h1 : ((w : ℤ) : ZMod m) = (((z + 1 : ℤ)) : ZMod m) := by push_cast; exact h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  rw [abs_le] at hz hw
  have := Int.eq_zero_of_abs_lt_dvd h1 (by rw [abs_lt]; omega)
  omega

theorem step_iff (hm : 2 * r + 1 < m) {a b : Balaban.Torus d m} (ha : InBox d r m a)
    (hb : InBox d r m b) (μ : Fin d) :
    b = a + Pi.single μ 1 ↔
      (fun ν => (b ν).valMinAbs) = (fun ν => (a ν).valMinAbs) + Pi.single μ 1 := by
  constructor
  · intro h
    funext ν
    by_cases hν : ν = μ
    · subst hν
      have := int_eq_of_cast_eq hm (ha ν) (hb ν) (by
        rw [ZMod.coe_valMinAbs, ZMod.coe_valMinAbs, h]; simp)
      simpa using this
    · have : b ν = a ν := by rw [h]; simp [Pi.single_eq_of_ne hν]
      simp [this, Pi.single_eq_of_ne hν]
  · intro h
    funext ν
    have h1 := congrFun h ν
    have h2 : (b ν) = ((b ν).valMinAbs : ZMod m) := (ZMod.coe_valMinAbs _).symm
    have h3 : (a ν) = ((a ν).valMinAbs : ZMod m) := (ZMod.coe_valMinAbs _).symm
    rw [h2, h1]
    simp only [Pi.add_apply]
    push_cast
    by_cases hν : ν = μ <;> simp [hν]

theorem adj_boxMap (hm : 2 * r + 1 < m) (hm' : 2 * r + 1 < m') {a b : Balaban.Torus d m}
    (ha : InBox d r m a) (hb : InBox d r m b) :
    (blockGraph d m).Adj a b ↔ (blockGraph d m').Adj (boxMap m m' a) (boxMap m m' b) := by
  have hne : a ≠ b ↔ boxMap m m' a ≠ boxMap m m' b := by
    constructor
    · intro h h'
      apply h
      have := congrArg (boxMap m' m) h'
      rwa [boxMap_boxMap hm' ha, boxMap_boxMap hm' hb] at this
    · intro h h'; exact h (by rw [h'])
  have hstep : ∀ (a b : Balaban.Torus d m), InBox d r m a → InBox d r m b → ∀ μ,
      (b = a + Pi.single μ 1 ↔ boxMap m m' b = boxMap m m' a + Pi.single μ 1) := by
    intro a b ha hb μ
    rw [step_iff hm ha hb, step_iff hm' (inBox_boxMap hm' ha) (inBox_boxMap hm' hb)]
    have e1 : (fun ν => (boxMap m m' b ν).valMinAbs) = fun ν => (b ν).valMinAbs :=
      funext (valMinAbs_boxMap hm' hb)
    have e2 : (fun ν => (boxMap m m' a ν).valMinAbs) = fun ν => (a ν).valMinAbs :=
      funext (valMinAbs_boxMap hm' ha)
    rw [e1, e2]
  show (a ≠ b ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1) ↔ _
  show _ ↔ (boxMap m m' a ≠ boxMap m m' b ∧ ∃ μ : Fin d,
    boxMap m m' b = boxMap m m' a + Pi.single μ 1 ∨ boxMap m m' a = boxMap m m' b + Pi.single μ 1)
  rw [hne]
  refine and_congr_right (fun _ => exists_congr (fun μ => or_congr (hstep a b ha hb μ)
    (hstep b a hb ha μ)))

theorem isAnimal_image_boxMap (hm : 2 * r + 1 < m) (hm' : 2 * r + 1 < m')
    {Z : Finset (Balaban.Torus d m)} (hZ : ∀ c ∈ Z, InBox d r m c)
    (h : IsAnimal (blockGraph d m) Z) :
    IsAnimal (blockGraph d m') (Z.image (boxMap m m')) :=
  isAnimal_image _ _ _ Z (fun a ha b hb hab => (adj_boxMap hm hm' (hZ a ha) (hZ b hb)).mp hab) h

end Box

section Transport

variable {r m m' : ℕ}

section Equiv

variable (hm : 2 * r + 1 < m) (hm' : 2 * r + 1 < m') (Y : Finset (Balaban.Torus d m))
  (hY : ∀ c ∈ Y, InBox d r m c)

include hm' hY in
theorem boxMap_left (c : Balaban.Torus d m) (hc : c ∈ Y) :
    boxMap m' m (boxMap m m' c) = c := boxMap_boxMap hm' (hY c hc)

include hm' hY in
theorem inBox_of_mem_image (a : Balaban.Torus d m') (ha : a ∈ Y.image (boxMap m m')) :
    InBox d r m' a := by
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
  exact inBox_boxMap hm' (hY c hc)

/-- The forward map of the polymers supported in `Y`. -/
def boxFwd (Z : {x : BlockPolymer (blockGraph d m) // x.1 ⊆ Y}) :
    {x' : BlockPolymer (blockGraph d m') // x'.1 ⊆ Y.image (boxMap m m')} :=
  ⟨⟨Z.1.1.image (boxMap m m'),
    isAnimal_image_boxMap hm hm' (fun c hc => hY c (Z.2 hc)) Z.1.2⟩,
    Finset.image_subset_image Z.2⟩

/-- The backward map of the polymers supported in `Y.image (boxMap m m')`. -/
def boxBwd (Z' : {x' : BlockPolymer (blockGraph d m') // x'.1 ⊆ Y.image (boxMap m m')}) :
    {x : BlockPolymer (blockGraph d m) // x.1 ⊆ Y} :=
  ⟨⟨Z'.1.1.image (boxMap m' m),
    isAnimal_image_boxMap hm' hm (fun c hc => inBox_of_mem_image hm' Y hY c (Z'.2 hc)) Z'.1.2⟩, by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp (Z'.2 ha)
    rw [boxMap_left hm' Y hY c' hc']; exact hc'⟩

theorem boxBwd_boxFwd (Z : {x : BlockPolymer (blockGraph d m) // x.1 ⊆ Y}) :
    boxBwd hm hm' Y hY (boxFwd hm hm' Y hY Z) = Z := by
  apply Subtype.ext; apply Subtype.ext
  change (Z.1.1.image (boxMap m m')).image (boxMap m' m) = Z.1.1
  rw [Finset.image_image]
  conv_rhs => rw [← Finset.image_id (s := Z.1.1)]
  exact Finset.image_congr (fun c hc => boxMap_left hm' Y hY c (Z.2 hc))

theorem boxFwd_boxBwd (Z' : {x' : BlockPolymer (blockGraph d m') // x'.1 ⊆ Y.image (boxMap m m')}) :
    boxFwd hm hm' Y hY (boxBwd hm hm' Y hY Z') = Z' := by
  apply Subtype.ext; apply Subtype.ext
  change (Z'.1.1.image (boxMap m' m)).image (boxMap m m') = Z'.1.1
  rw [Finset.image_image]
  conv_rhs => rw [← Finset.image_id (s := Z'.1.1)]
  refine Finset.image_congr (fun a ha => ?_)
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (Z'.2 ha)
  show boxMap m m' (boxMap m' m (boxMap m m' c)) = boxMap m m' c
  rw [boxMap_left hm' Y hY c hc]

/-- The bijection between the polymers supported in `Y` and in its image. -/
def boxEquiv :
    {x : BlockPolymer (blockGraph d m) // x.1 ⊆ Y} ≃
      {x' : BlockPolymer (blockGraph d m') // x'.1 ⊆ Y.image (boxMap m m')} where
  toFun := boxFwd hm hm' Y hY
  invFun := boxBwd hm hm' Y hY
  left_inv := boxBwd_boxFwd hm hm' Y hY
  right_inv := boxFwd_boxBwd hm hm' Y hY

include hm' hY in
theorem boxMap_injOn : Set.InjOn (boxMap m m') (Y : Set (Balaban.Torus d m)) :=
  fun a ha b hb h => by
    rw [← boxMap_left hm' Y hY a ha, ← boxMap_left hm' Y hY b hb, h]

end Equiv

/-- The local terms of a set `Y` of blocks in the box agree on two tori when the activities of the
polymers inside `Y` agree under the identification `boxMap`. -/
theorem PY_boxMap [NeZero m] [NeZero m'] (hm : 2 * r + 1 < m) (hm' : 2 * r + 1 < m') (Y : Finset (Balaban.Torus d m))
    (hY : ∀ c ∈ Y, InBox d r m c)
    (K : BlockPolymer (blockGraph d m) → ℂ) (K' : BlockPolymer (blockGraph d m') → ℂ)
    (hK : ∀ (Z : Finset (Balaban.Torus d m)) (hZY : Z ⊆ Y) (hZ : IsAnimal (blockGraph d m) Z),
      K ⟨Z, hZ⟩ = K' ⟨Z.image (boxMap m m'),
        isAnimal_image_boxMap hm hm' (fun c hc => hY c (hZY hc)) hZ⟩) :
    PY (overlap (blockGraph d m')) (fun Z => Z.1) K' (Y.image (boxMap m m')) =
      PY (overlap (blockGraph d m)) (fun Z => Z.1) K Y := by
  have hinj := boxMap_injOn hm' Y hY
  refine PY_transport (inc := overlap (blockGraph d m)) (inc' := overlap (blockGraph d m'))
    (supp := fun Z => Z.1) (supp' := fun Z => Z.1) Y (Y.image (boxMap m m')) (boxMap m m') hinj
    (fun b' => Finset.mem_image) (boxEquiv hm hm' Y hY) (fun x b' => ?_) ?_ ?_
  · change b' ∈ x.1.1.image (boxMap m m') ↔ _
    exact Finset.mem_image
  · intro x y
    rw [lnk_overlap, lnk_overlap]
    change ¬ Disjoint (x.1.1.image (boxMap m m')) (y.1.1.image (boxMap m m')) ↔ _
    unfold overlap
    constructor
    · intro h hd
      apply h
      rw [Finset.disjoint_left] at hd ⊢
      intro a ha ha'
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨c', hc', hcc⟩ := Finset.mem_image.mp ha'
      have := hinj (x.2 hc) (y.2 hc') hcc.symm
      subst this
      exact hd hc hc'
    · intro h hd
      apply h
      rw [Finset.disjoint_left] at hd ⊢
      intro c hc hc'
      exact hd (Finset.mem_image_of_mem _ hc) (Finset.mem_image_of_mem _ hc')
  · intro x
    exact (hK x.1.1 x.2 x.1.2).symm

/-- Torus independence in the frozen language: the polymer `X` of `Torus d (s * m)` formed by the
blocks `Y` in the box and its image in `Torus d (s * m')` have the same local term when the
activities of the polymers inside agree under the identification of the boxes. -/
theorem frozenPY_boxMap {s : ℕ} [NeZero s] [NeZero m] [NeZero m'] (hm : 2 * r + 1 < m)
    (hm' : 2 * r + 1 < m') (Y : Finset (Balaban.Torus d m)) (hY : ∀ c ∈ Y, InBox d r m c)
    (K : Finset (Balaban.Torus d (s * m)) → ℂ) (K' : Finset (Balaban.Torus d (s * m')) → ℂ)
    (hK : ∀ (Z : Finset (Balaban.Torus d m)), Z ⊆ Y → IsAnimal (blockGraph d m) Z →
      K (siteSet d s m Z) = K' (siteSet d s m' (Z.image (boxMap m m')))) :
    frozenPY d s m' K' (siteSet d s m' (Y.image (boxMap m m'))) =
      frozenPY d s m K (siteSet d s m Y) := by
  unfold frozenPY
  rw [image_siteSet, image_siteSet]
  exact PY_boxMap hm hm' Y hY _ _ (fun Z hZY hZ => hK Z hZY hZ)

end Transport

end Balaban.Polymer
