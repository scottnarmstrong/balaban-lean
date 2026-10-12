/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6Terms

/-!
# Def-6: the paving symmetries preserve `𝒟_j` (the former class field `pavingPoly`)

For `r` in the symmetry group `pavingSymGroup` of the fixed `M`-paving (translations by the cell
side, reflections `x_μ ↦ s - 1 - x_μ`, coordinate exchanges) and `j ≤ k`, `L^{m₀} ∣ N₁` (the cells
tile the torus): `X ∈ 𝒟_j → r X ∈ 𝒟_j` (`isPolyDom_image_of_mem_pavingSymGroup`).  It is proved
from the definition of `IsPolyDom` through `GoodMap`, a permutation of the torus that preserves
adjacency and maps aligned boxes onto aligned boxes.
-/


@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Finset

section Generic

variable {d n : ℕ} [NeZero n]

theorem aligned_iff {s : ℕ} (hs : s ∣ n) (b : Torus d n) :
    Aligned s b ↔ ∀ μ, ZMod.castHom hs (ZMod s) (b μ) = 0 := by
  unfold Aligned
  refine forall_congr' fun μ => ?_
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

/-- A permutation of the torus that preserves adjacency and sends aligned boxes of side `a`
onto aligned boxes of side `a`. -/
structure GoodMap (s a : ℕ) (e : Equiv.Perm (Torus d n)) : Prop where
  nbr : ∀ x y, Nbr x y → Nbr (e x) (e y)
  boxes : ∀ b, Aligned s b → ∃ b', Aligned s b' ∧ e '' box b a = box b' a

omit [NeZero n] in
theorem GoodMap.one (s a : ℕ) : GoodMap (d := d) (n := n) s a 1 :=
  ⟨fun _ _ h => h, fun b hb => ⟨b, hb, by simp⟩⟩

omit [NeZero n] in
theorem GoodMap.mul {s a : ℕ} {e₁ e₂ : Equiv.Perm (Torus d n)} (h₁ : GoodMap s a e₁)
    (h₂ : GoodMap s a e₂) : GoodMap s a (e₁ * e₂) := by
  refine ⟨fun x y h => h₁.nbr _ _ (h₂.nbr _ _ h), fun b hb => ?_⟩
  obtain ⟨b₂, hb₂, h2⟩ := h₂.boxes b hb
  obtain ⟨b₁, hb₁, h1⟩ := h₁.boxes b₂ hb₂
  refine ⟨b₁, hb₁, ?_⟩
  rw [← h1, ← h2, ← Set.image_comp]
  rfl

omit [NeZero n] in
theorem GoodMap.isPolyDom {s a : ℕ} {e : Equiv.Perm (Torus d n)} (he : GoodMap s a e)
    {X : Set (Torus d n)}
    (hX : X.Nonempty ∧ (∃ 𝒦 : Set (Torus d n), (∀ b ∈ 𝒦, Aligned s b ∧ box b a ⊆ X) ∧
        ∀ z ∈ X, ∃ b ∈ 𝒦, z ∈ box b a) ∧
      ∀ x ∈ X, ∀ y ∈ X, Relation.ReflTransGen (fun p q => p ∈ X ∧ q ∈ X ∧ Nbr p q) x y) :
    (e '' X).Nonempty ∧ (∃ 𝒦 : Set (Torus d n), (∀ b ∈ 𝒦, Aligned s b ∧ box b a ⊆ e '' X) ∧
        ∀ z ∈ e '' X, ∃ b ∈ 𝒦, z ∈ box b a) ∧
      ∀ x ∈ e '' X, ∀ y ∈ e '' X,
        Relation.ReflTransGen (fun p q => p ∈ e '' X ∧ q ∈ e '' X ∧ Nbr p q) x y := by
  obtain ⟨hne, ⟨𝒦, hK1, hK2⟩, hc⟩ := hX
  refine ⟨hne.image _, ⟨{b' | Aligned s b' ∧ ∃ b ∈ 𝒦, e '' box b a = box b' a}, ?_, ?_⟩, ?_⟩
  · rintro b' ⟨hb', b, hb, hbb⟩
    exact ⟨hb', by rw [← hbb]; exact Set.image_mono (hK1 b hb).2⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨b, hb, hzb⟩ := hK2 z hz
    obtain ⟨b', hb', hbb⟩ := he.boxes b (hK1 b hb).1
    refine ⟨b', ⟨hb', b, hb, hbb⟩, ?_⟩
    rw [← hbb]; exact ⟨z, hzb, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    refine (hc x hx y hy).lift e ?_
    rintro p q ⟨hp, hq, hpq⟩
    exact ⟨⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩, he.nbr _ _ hpq⟩


omit [NeZero n] in
theorem nbr_of_step {e : Equiv.Perm (Torus d n)}
    (h : ∀ (x : Torus d n) (ν : Fin d), ∃ l : Fin d,
      e (x + Pi.single ν 1) = e x + Pi.single l 1 ∨ e x = e (x + Pi.single ν 1) + Pi.single l 1)
    (x y : Torus d n) (hxy : Nbr x y) : Nbr (e x) (e y) := by
  obtain ⟨ν, hν | hν⟩ := hxy
  · obtain ⟨l, hl⟩ := h x ν
    exact ⟨l, by rw [hν]; exact hl⟩
  · obtain ⟨l, hl | hl⟩ := h y ν
    · exact ⟨l, Or.inr (by rw [hν]; exact hl)⟩
    · exact ⟨l, Or.inl (by rw [hν]; exact hl)⟩

section Translation

variable {s : ℕ} (hs : s ∣ n)

theorem good_addRight (a : ℕ) (t : Torus d n) (ht : ∀ μ, ZMod.castHom hs (ZMod s) (t μ) = 0) :
    GoodMap s a (Equiv.addRight t) := by
  refine ⟨nbr_of_step fun x ν => ⟨ν, Or.inl ?_⟩, fun b hb => ⟨b + t, ?_, ?_⟩⟩
  · simp only [Equiv.coe_addRight]; abel
  · rw [aligned_iff hs] at hb ⊢
    intro μ; rw [Pi.add_apply, map_add, hb μ, ht μ, add_zero]
  · ext x
    simp only [Set.mem_image, Equiv.coe_addRight, Localization.box, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, by abel⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨b + natT w, ⟨w, hw, rfl⟩, by abel⟩

end Translation


section Flip

variable (μ : Fin d) (c : ZMod n) (e : Equiv.Perm (Torus d n))

omit [NeZero n] in
theorem flip_box_sub (he : ∀ x, e x = Function.update x μ (c - 1 - x μ)) (a : ℕ) (b : Torus d n)
    (x : Torus d n) (hx : x ∈ Localization.box b a) :
    e x ∈ Localization.box (Function.update b μ (c - b μ - a)) a := by
  obtain ⟨w, hw, rfl⟩ := hx
  refine ⟨Function.update w μ (a - 1 - w μ), fun i => ?_, ?_⟩
  · by_cases h : i = μ
    · subst h; have := hw i; simp only [Function.update_self]; omega
    · rw [Function.update_of_ne h]; exact hw i
  · have hwμ : w μ < a := hw μ
    have hc : ((a - 1 - w μ : ℕ) : ZMod n) = a - 1 - w μ := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    ext i
    rw [he]
    by_cases h : i = μ
    · subst h
      simp only [Function.update_self, Pi.add_apply, natT_apply, hc]
      ring
    · simp [Function.update_of_ne h]

theorem good_flip (hs : ∀ x, e x = Function.update x μ (c - 1 - x μ)) {s a : ℕ} (hsn : s ∣ n)
    (hc : ZMod.castHom hsn (ZMod s) c = 0) (ha : s ∣ a)
    (hinv : ∀ x, e (e x) = x) :
    GoodMap s a e := by
  have hφa : ZMod.castHom hsn (ZMod s) (a : ZMod n) = 0 := by
    rw [map_natCast]; exact (ZMod.natCast_eq_zero_iff _ _).2 ha
  refine ⟨nbr_of_step fun x ν => ?_, fun b hb => ⟨Function.update b μ (c - b μ - a), ?_, ?_⟩⟩
  · by_cases h : ν = μ
    · subst h
      refine ⟨ν, Or.inr ?_⟩
      ext i
      rw [hs, hs]
      by_cases hi : i = ν
      · subst hi; simp; ring
      · simp [Function.update_of_ne hi, Pi.single_eq_of_ne hi]
    · refine ⟨ν, Or.inl ?_⟩
      ext i
      rw [hs, hs]
      by_cases hi : i = μ
      · subst hi; simp [Pi.single_eq_of_ne (Ne.symm h)]
      · by_cases hj : i = ν
        · subst hj; simp [Function.update_of_ne hi]
        · simp [Function.update_of_ne hi, Pi.single_eq_of_ne hj]
  · rw [aligned_iff hsn] at hb ⊢
    intro i
    by_cases h : i = μ
    · subst h; simp only [Function.update_self, map_sub, hc, hb i, hφa]; ring
    · rw [Function.update_of_ne h]; exact hb i
  · apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact flip_box_sub μ c e hs a b x hx
    · intro y hy
      have hbb : Function.update (Function.update b μ (c - b μ - a)) μ
          (c - (Function.update b μ (c - b μ - a)) μ - a) = b := by
        ext i; by_cases h : i = μ
        · subst h; simp; ring
        · simp [Function.update_of_ne h]
      have := flip_box_sub μ c e hs a _ y hy
      rw [hbb] at this
      exact ⟨e y, this, hinv y⟩

end Flip

section Swap

theorem good_swap {s a : ℕ} (μ ν : Fin d) (e : Equiv.Perm (Torus d n)) (hsn : s ∣ n)
    (he : ∀ x, e x = x ∘ Equiv.swap μ ν) : GoodMap s a e := by
  have hsw : ∀ (x : Torus d n) (l : Fin d), e (x + Pi.single l 1) =
      e x + Pi.single (Equiv.swap μ ν l) 1 := by
    intro x l
    ext i
    rw [he, he]
    simp only [Function.comp_apply, Pi.add_apply]
    congr 1
    by_cases h : Equiv.swap μ ν i = l
    · have : i = Equiv.swap μ ν l := by rw [← h]; simp
      simp [this]
    · have : i ≠ Equiv.swap μ ν l := fun h' => h (by rw [h']; simp)
      simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne this]
  refine ⟨nbr_of_step fun x l => ⟨_, Or.inl (hsw x l)⟩, fun b hb => ⟨b ∘ Equiv.swap μ ν, ?_, ?_⟩⟩
  · rw [aligned_iff hsn] at hb ⊢
    intro i; exact hb _
  · ext y
    constructor
    · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨w ∘ Equiv.swap μ ν, fun i => hw _, ?_⟩
      ext i
      rw [he]; simp [natT]
    · rintro ⟨w, hw, rfl⟩
      refine ⟨b + natT (w ∘ Equiv.swap μ ν), ⟨_, fun i => hw _, rfl⟩, ?_⟩
      ext i
      rw [he]; simp [natT]

end Swap

end Generic

section Concrete

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

theorem goodMap_generators {m₀ j : ℕ} (hN : L ^ m₀ ∣ N₁) (hj : j ≤ k) :
    ∀ g ∈ ({g | ∃ μ, g = transBy (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (cellSide L m₀ m₁ j) μ} ∪
      {g | ∃ μ, g = flipBy (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (cellSide L m₀ m₁ j) μ} ∪
      {g | ∃ μ ν, g = swapJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) μ ν} :
      Set (Equiv.Perm (CTorus d L N₁ m₁ k))),
    (GoodMap (cellSide L m₀ m₁ j) (L * cellSide L m₀ m₁ j) g ∧
      GoodMap (cellSide L m₀ m₁ j) (L * cellSide L m₀ m₁ j) g⁻¹) := by
  have hsn : cellSide L m₀ m₁ j ∣ (N₁ * L ^ m₁) * L ^ k := cellSide_dvd hN hj
  have ha : cellSide L m₀ m₁ j ∣ L * cellSide L m₀ m₁ j := dvd_mul_left _ _
  have hcs : ZMod.castHom hsn (ZMod (cellSide L m₀ m₁ j))
      ((cellSide L m₀ m₁ j : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ k)) = 0 := by
    rw [map_natCast]; exact ZMod.natCast_self _
  rintro g ((⟨μ, rfl⟩ | ⟨μ, rfl⟩) | ⟨μ, ν, rfl⟩)
  · have ht : ∀ i, ZMod.castHom hsn (ZMod (cellSide L m₀ m₁ j))
        (((cellSide L m₀ m₁ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) i) = 0 := by
      intro i
      simp only [Pi.smul_apply, map_nsmul]
      rw [nsmul_eq_mul]
      by_cases h : i = μ
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    refine ⟨good_addRight hsn _ _ ht, ?_⟩
    have : (transBy (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (cellSide L m₀ m₁ j) μ)⁻¹ =
        Equiv.addRight (-((cellSide L m₀ m₁ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k))) := by
      ext x; simp [transBy, Equiv.Perm.inv_def]
    rw [this]
    refine good_addRight hsn _ _ fun i => ?_
    rw [Pi.neg_apply, map_neg, ht i, neg_zero]
  · have hf : GoodMap (cellSide L m₀ m₁ j) (L * cellSide L m₀ m₁ j)
        (flipBy (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (cellSide L m₀ m₁ j) μ) := by
      refine good_flip μ _ _ (fun x => rfl) hsn hcs ha fun x => ?_
      ext i
      by_cases h : i = μ
      · subst h; simp [flipBy]
      · simp [flipBy, Function.update_of_ne h]
    exact ⟨hf, hf⟩
  · have hf : GoodMap (cellSide L m₀ m₁ j) (L * cellSide L m₀ m₁ j)
        (swapJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) μ ν) :=
      good_swap μ ν _ hsn (fun x => rfl)
    exact ⟨hf, hf⟩

theorem pavingSymGroup_goodMap {m₀ j : ℕ} (hN : L ^ m₀ ∣ N₁) (hj : j ≤ k)
    {r : Equiv.Perm (CTorus d L N₁ m₁ k)} (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L m₀ j) :
    GoodMap (cellSide L m₀ m₁ j) (L * cellSide L m₀ m₁ j) r := by
  have key : GoodMap (cellSide L m₀ m₁ j) (L * cellSide L m₀ m₁ j) r ∧
      GoodMap (cellSide L m₀ m₁ j) (L * cellSide L m₀ m₁ j) r⁻¹ := by
    refine Subgroup.closure_induction (p := fun r _ =>
      GoodMap (cellSide L m₀ m₁ j) (L * cellSide L m₀ m₁ j) r ∧
        GoodMap (cellSide L m₀ m₁ j) (L * cellSide L m₀ m₁ j) r⁻¹) ?_ ?_ ?_ ?_ hr
    · exact fun g hg => goodMap_generators hN hj g hg
    · exact ⟨GoodMap.one _ _, by rw [inv_one]; exact GoodMap.one _ _⟩
    · intro x y _ _ hx hy
      exact ⟨hx.1.mul hy.1, by rw [mul_inv_rev]; exact hy.2.mul hx.2⟩
    · intro x _ hx
      exact ⟨hx.2, by rw [inv_inv]; exact hx.1⟩
  exact key.1

/-- **`pavingPoly`**: the paving symmetries (translations by the cell side, reflections and
coordinate exchanges) map polymers of `𝒟_j` to polymers of `𝒟_j`, when the cell side divides the
torus size. -/
theorem isPolyDom_image_of_mem_pavingSymGroup {m₀ j : ℕ} (hN : L ^ m₀ ∣ N₁) (hj : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j X)
    {r : Equiv.Perm (CTorus d L N₁ m₁ k)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L m₀ j) :
    IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j (r '' X) := by
  obtain ⟨hne, ⟨𝒦, h1, h2⟩, hc⟩ := hX
  exact (pavingSymGroup_goodMap hN hj hr).isPolyDom ⟨hne, ⟨𝒦, h1, h2⟩, hc⟩

end Concrete

end Balaban.SmallField.Def6
