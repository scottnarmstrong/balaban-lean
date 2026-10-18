/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerSitesCell
public import Balaban.Polymer.Support
public import Balaban.Polymer.BlockTorus
public import Mathlib.Data.ZMod.ValMinAbs

/-!
# Fine polymers are the preimages of connected sets of cells (blocker 7)

On the torus `ℤ/n`, `n = D K`, a set of fine sites is a polymer of blocks of side `D`
(`Balaban.IsPolymer`) iff it is the preimage of a connected set `Y` of cells of the block torus
`ℤ/K` (`isPolymer_preimage_iff`: `IsAnimal (blockGraph d K) Y`), the preimage of the cell map
`x ↦ (x_μ.val / D)_μ`.  This is the correspondence between the polymers of Root-F and the sets `X ∈ P ℓ`
of the tower.
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Polymer

section Animal

variable {d D K n : ℕ}

set_option hygiene false in
local notation "pic[" x "]" => (fun j₀ => ((((x j₀).val / D : ℕ)) : ZMod K))

/-- The cell index of `u + t` in `ℤ/(D K)`: the cell of the integer `u.val + t`, modulo `K`. -/
theorem cellc_add_nat [NeZero n] (hn : n = D * K) (u : ZMod n) (t : ℕ) :
    ((((u + (t : ZMod n)).val / D : ℕ)) : ZMod K) = ((((u.val + t) / D : ℕ)) : ZMod K) := by
  subst hn
  have h1 : (u + (t : ZMod (D * K))) = ((u.val + t : ℕ) : ZMod (D * K)) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [h1, ZMod.val_natCast, Nat.mod_mul_right_div_self, ZMod.natCast_mod]

/-- Crossing a block boundary: the cell index of `u + 1` is that of `u` or one more. -/
theorem cellc_succ [NeZero n] (hn : n = D * K) (u : ZMod n) :
    ((((u + 1).val / D : ℕ)) : ZMod K) = (((u.val / D : ℕ)) : ZMod K) ∨
    ((((u + 1).val / D : ℕ)) : ZMod K) = (((u.val / D : ℕ)) : ZMod K) + 1 := by
  have h := cellc_add_nat hn u 1
  simp only [Nat.cast_one] at h
  rw [h, Nat.succ_div]
  split_ifs <;> simp

/-- Moving by a full block increases the cell index by one. -/
theorem cellc_add_side [NeZero n] (hn : n = D * K) (hD : 0 < D) (u : ZMod n) :
    ((((u + (D : ZMod n)).val / D : ℕ)) : ZMod K) = (((u.val / D : ℕ)) : ZMod K) + 1 := by
  rw [cellc_add_nat hn u D, Nat.add_div_right _ hD]
  simp

/-- The cell map is unchanged by changing a coordinate within its cell. -/
theorem pic_update {z : Fin d → ZMod n} {μ : Fin d} {w : ZMod n}
    (h : (((w.val / D : ℕ)) : ZMod K) = (((z μ).val / D : ℕ) : ZMod K)) :
    pic[Function.update z μ w] = pic[z] := by
  funext ν
  by_cases hν : ν = μ
  · subst hν; simpa using h
  · simp [Function.update_of_ne hν]

/-- Every cell has a site. -/
theorem exists_site [NeZero n] [NeZero K] (hn : n = D * K) (hD : 0 < D) (b : Fin d → ZMod K) :
    ∃ x : Fin d → ZMod n, pic[x] = b := by
  subst hn
  refine ⟨fun μ => ((D * (b μ).val : ℕ) : ZMod (D * K)), ?_⟩
  funext μ
  have hlt : D * (b μ).val < D * K := Nat.mul_lt_mul_of_pos_left (ZMod.val_lt (b μ)) hD
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.mul_div_cancel_left _ hD]
  exact ZMod.natCast_zmod_val _

theorem walk_up [NeZero n] (hn : n = D * K) (S : Finset (Fin d → ZMod n))
    (hS : ∀ x ∈ S, ∀ y, pic[y] = pic[x] → y ∈ S) :
    ∀ (t : ℕ) (z : Fin d → ZMod n) (μ : Fin d), z ∈ S → ((z μ).val + t) / D = (z μ).val / D →
      Relation.ReflTransGen
        (fun a b => a ∈ S ∧ b ∈ S ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1)
        z (Function.update z μ (z μ + (t : ZMod n))) := by
  intro t
  induction t with
  | zero =>
    intro z μ hz _
    simp only [Nat.cast_zero, add_zero, Function.update_eq_self]
    exact Relation.ReflTransGen.refl
  | succ t ih =>
    intro z μ hz h
    have h1 : ((z μ).val + t) / D = (z μ).val / D :=
      le_antisymm (h ▸ Nat.div_le_div_right (by omega)) (Nat.div_le_div_right (by omega))
    have hp := ih z μ hz h1
    have hz_t : Function.update z μ (z μ + (t : ZMod n)) ∈ S :=
      hS z hz _ (pic_update (by rw [cellc_add_nat hn, h1]))
    have hz_t1 : Function.update z μ (z μ + ((t + 1 : ℕ) : ZMod n)) ∈ S :=
      hS z hz _ (pic_update (by rw [cellc_add_nat hn, h]))
    have e : Function.update z μ (z μ + ((t + 1 : ℕ) : ZMod n)) =
        Function.update z μ (z μ + (t : ZMod n)) + Pi.single μ 1 := by
      funext ν
      by_cases hν : ν = μ
      · subst hν; simp; ring
      · simp [hν]
    rw [e] at hz_t1 ⊢
    exact hp.tail ⟨hz_t, hz_t1, μ, Or.inl rfl⟩

theorem rtg_symm_fine (S : Finset (Fin d → ZMod n)) {x y : Fin d → ZMod n}
    (h : Relation.ReflTransGen
      (fun a b => a ∈ S ∧ b ∈ S ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1) x y) :
    Relation.ReflTransGen
      (fun a b => a ∈ S ∧ b ∈ S ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih =>
    obtain ⟨ha, hb, μ, hμ | hμ⟩ := hab
    · exact Relation.ReflTransGen.head ⟨hb, ha, μ, Or.inr hμ⟩ ih
    · exact Relation.ReflTransGen.head ⟨hb, ha, μ, Or.inl hμ⟩ ih

/-- A coordinate can be changed to any other value of the same cell through sites of the cell. -/
theorem walk_coord [NeZero n] (hn : n = D * K) (S : Finset (Fin d → ZMod n))
    (hS : ∀ x ∈ S, ∀ y, pic[y] = pic[x] → y ∈ S) (z : Fin d → ZMod n) (μ : Fin d) (w : ZMod n)
    (hz : z ∈ S) (hw : (((w.val / D : ℕ)) : ZMod K) = (((z μ).val / D : ℕ) : ZMod K)) :
    Relation.ReflTransGen
      (fun a b => a ∈ S ∧ b ∈ S ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1)
      z (Function.update z μ w) := by
  have hD : 0 < D := by
    by_contra h0
    exact NeZero.ne n (by rw [hn, show D = 0 by omega, zero_mul])
  have hK : 0 < K := by
    by_contra h0
    exact NeZero.ne n (by rw [hn, show K = 0 by omega, mul_zero])
  have hlt : (z μ).val / D = w.val / D := by
    have h1 : (z μ).val / D < K := by
      rw [Nat.div_lt_iff_lt_mul hD]; exact lt_of_lt_of_eq (ZMod.val_lt (z μ)) (by rw [hn, mul_comm])
    have h2 : w.val / D < K := by
      rw [Nat.div_lt_iff_lt_mul hD]; exact lt_of_lt_of_eq (ZMod.val_lt w) (by rw [hn, mul_comm])
    have := (ZMod.natCast_eq_natCast_iff' _ _ K).1 (by simpa using hw.symm)
    rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
  rcases le_total (z μ).val w.val with hle | hle
  · have hw' : w = z μ + (((w.val - (z μ).val : ℕ)) : ZMod n) := by
      have : ((w.val : ℕ) : ZMod n) =
          ((z μ).val : ZMod n) + (((w.val - (z μ).val : ℕ)) : ZMod n) := by
        rw [← Nat.cast_add, Nat.add_sub_cancel' hle]
      rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
    have := walk_up hn S hS (w.val - (z μ).val) z μ hz (by
      rw [Nat.add_sub_cancel' hle]; exact hlt.symm)
    rwa [← hw'] at this
  · have hz' : Function.update z μ w ∈ S := hS z hz _ (pic_update hw)
    have hw' : z μ = w + (((z μ).val - w.val : ℕ) : ZMod n) := by
      have : (((z μ).val : ℕ) : ZMod n) =
          (w.val : ZMod n) + ((((z μ).val - w.val : ℕ)) : ZMod n) := by
        rw [← Nat.cast_add, Nat.add_sub_cancel' hle]
      rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
    have := walk_up hn S hS ((z μ).val - w.val) (Function.update z μ w) μ hz' (by
      simp only [Function.update_self]
      rw [Nat.add_sub_cancel' hle]; exact hlt)
    simp only [Function.update_self, Function.update_idem] at this
    rw [← hw', Function.update_eq_self] at this
    exact rtg_symm_fine S this

/-- Two sites of the same cell are joined by a path of nearest-neighbour steps in the cell. -/
theorem walk_cell [NeZero n] (hn : n = D * K) (S : Finset (Fin d → ZMod n))
    (hS : ∀ x ∈ S, ∀ y, pic[y] = pic[x] → y ∈ S) {x x' : Fin d → ZMod n} (hx : x ∈ S)
    (hx' : pic[x'] = pic[x]) :
    Relation.ReflTransGen
      (fun a b => a ∈ S ∧ b ∈ S ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1)
      x x' := by
  classical
  have key : ∀ s : Finset (Fin d), Relation.ReflTransGen
      (fun a b => a ∈ S ∧ b ∈ S ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1)
      x (fun ν => if ν ∈ s then x' ν else x ν) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using Relation.ReflTransGen.refl
    | insert μ s hμ ih =>
      have hzS : (fun ν => if ν ∈ s then x' ν else x ν) ∈ S := by
        refine hS x hx _ (funext fun ν => ?_)
        by_cases hν : ν ∈ s
        · simp only [hν, ite_true]; exact congrFun hx' ν
        · simp [hν]
      have step := walk_coord hn S hS _ μ (x' μ) hzS (by have := congrFun hx' μ; simpa [hμ] using this)
      have e : Function.update (fun ν => if ν ∈ s then x' ν else x ν) μ (x' μ) =
          fun ν => if ν ∈ insert μ s then x' ν else x ν := by
        funext ν
        by_cases hν : ν = μ
        · subst hν; simp
        · simp [hν]
      rw [e] at step
      exact ih.trans step
  simpa using key Finset.univ

/-- Crossing a block boundary: from a site of a cell `b ∈ S` there is a path to a site of the next
cell in direction `μ`, if that cell is in `S`. -/
theorem walk_next [NeZero n] (hn : n = D * K) (S : Finset (Fin d → ZMod n))
    (hS : ∀ x ∈ S, ∀ y, pic[y] = pic[x] → y ∈ S) {x : Fin d → ZMod n} (hx : x ∈ S) (μ : Fin d)
    (hmem : ∀ y, pic[y] = pic[x] + Pi.single μ 1 → y ∈ S) (hD : 0 < D) :
    ∃ x' : Fin d → ZMod n, pic[x'] = pic[x] + Pi.single μ 1 ∧
      Relation.ReflTransGen
        (fun a b => a ∈ S ∧ b ∈ S ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1)
        x x' := by
  classical
  have hex : ∃ i : ℕ, ((x μ).val + i) / D ≠ (x μ).val / D :=
    ⟨D, by rw [Nat.add_div_right _ hD]; omega⟩
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := by
    refine ⟨Nat.find hex - 1, ?_⟩
    have : Nat.find hex ≠ 0 := fun h0 => by
      have := Nat.find_spec hex
      rw [h0] at this; simp at this
    omega
  have hmin : ((x μ).val + j) / D = (x μ).val / D := by
    have := Nat.find_min hex (show j < Nat.find hex by omega)
    simpa using this
  have hsucc : ((x μ).val + (j + 1)) / D = (x μ).val / D + 1 := by
    have hspec := Nat.find_spec hex
    rw [hj] at hspec
    rw [← add_assoc, Nat.succ_div, hmin] at hspec ⊢
    split_ifs at hspec ⊢ with h1
    · rfl
    · exact absurd rfl hspec
  have hwalk := walk_up hn S hS j x μ hx hmin
  set z := Function.update x μ (x μ + (j : ZMod n)) with hz
  have hzS : z ∈ S := hS x hx _ (pic_update (by rw [cellc_add_nat hn, hmin]))
  have hpic : pic[Function.update x μ (x μ + ((j + 1 : ℕ) : ZMod n))] =
      pic[x] + Pi.single μ 1 := by
    funext ν
    by_cases hν : ν = μ
    · subst hν
      simp only [Function.update_self, Pi.add_apply, Pi.single_eq_same]
      rw [cellc_add_nat hn, hsucc]; push_cast; rfl
    · simp [hν]
  refine ⟨_, hpic, hwalk.tail ⟨hzS, hmem _ hpic, μ, Or.inl ?_⟩⟩
  funext ν
  by_cases hν : ν = μ
  · subst hν; simp [hz]; ring
  · simp [hz, hν]

theorem pic_add_single [NeZero n] (hn : n = D * K) (w : Fin d → ZMod n) (μ : Fin d) :
    pic[(w + Pi.single μ 1 : Fin d → ZMod n)] = pic[w] ∨
      pic[(w + Pi.single μ 1 : Fin d → ZMod n)] = pic[w] + Pi.single μ 1 := by
  rcases cellc_succ hn (w μ) with h | h
  · left
    funext ν
    by_cases hν : ν = μ
    · subst hν; simpa using h
    · simp [hν]
  · right
    funext ν
    by_cases hν : ν = μ
    · subst hν; simpa using h
    · simp [hν]

/-- **Polymers are preimages of animals.**  A set of fine sites of the torus `ℤ/(D K)` that is the
preimage under the cell map of a set `Y` of cells is a polymer of blocks of side `D` iff `Y` is
connected in the nearest-neighbour graph of the block torus `ℤ/K`. -/
theorem isPolymer_preimage_iff [NeZero n] [NeZero K] (hn : n = D * K) (hD : 0 < D)
    (Y : Finset (Fin d → ZMod K)) :
    IsPolymer d n D (Finset.univ.filter fun x : Fin d → ZMod n => pic[x] ∈ Y) ↔
      IsAnimal (blockGraph d K) Y := by
  classical
  set S : Finset (Fin d → ZMod n) := Finset.univ.filter fun x => pic[x] ∈ Y with hSdef
  have hS : ∀ x ∈ S, ∀ y, pic[y] = pic[x] → y ∈ S := fun x hx y hy => by
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hy]; exact hx
  have hmemS : ∀ y, y ∈ S ↔ pic[y] ∈ Y := fun y => by simp [hSdef]
  rw [isAnimal_iff]
  constructor
  · rintro ⟨hne, -, hconn⟩
    refine ⟨?_, fun b hb b' hb' => ?_⟩
    · obtain ⟨x, hx⟩ := hne
      exact ⟨_, (hmemS x).1 hx⟩
    · obtain ⟨x, rfl⟩ := exists_site hn hD b
      obtain ⟨x', rfl⟩ := exists_site hn hD b'
      have key : ∀ w, Relation.ReflTransGen
          (fun a b => a ∈ S ∧ b ∈ S ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1)
          x w → Relation.ReflTransGen
          (fun a b => a ∈ Y ∧ b ∈ Y ∧ (blockGraph d K).Adj a b) pic[x] pic[w] := by
        intro w hw
        induction hw with
        | refl => exact Relation.ReflTransGen.refl
        | @tail w₁ w₂ _ hab ih =>
          obtain ⟨h1, h2, μ, hμ | hμ⟩ := hab
          · by_cases heq : pic[w₂] = pic[w₁]
            · rw [heq]; exact ih
            · have hc := pic_add_single hn w₁ μ
              rw [← hμ] at hc
              exact ih.tail ⟨(hmemS _).1 h1, (hmemS _).1 h2, fun h => heq h.symm,
                μ, hc.resolve_left heq |> Or.inl⟩
          · by_cases heq : pic[w₂] = pic[w₁]
            · rw [heq]; exact ih
            · have hc := pic_add_single hn w₂ μ
              rw [← hμ] at hc
              exact ih.tail ⟨(hmemS _).1 h1, (hmemS _).1 h2, fun h => heq h.symm,
                μ, hc.resolve_left (fun h => heq h.symm) |> Or.inr⟩
      exact key x' ((hconn _ ((hmemS x).2 hb) _ ((hmemS x').2 hb')))
  · rintro ⟨hne, hconn⟩
    refine ⟨?_, fun x hx y hy => ?_, ?_⟩
    · obtain ⟨b, hb⟩ := hne
      obtain ⟨x, hx⟩ := exists_site hn hD b
      exact ⟨x, (hmemS x).2 (hx ▸ hb)⟩
    · exact (hmemS y).2 (by
        have : pic[y] = pic[x] := funext fun μ => by rw [hy μ]
        rw [this]; exact (hmemS x).1 hx)
    · intro x hx y hy
      have lift : ∀ w, Relation.ReflTransGen
          (fun a b => a ∈ Y ∧ b ∈ Y ∧ (blockGraph d K).Adj a b) pic[x] w →
          ∃ x', pic[x'] = w ∧ Relation.ReflTransGen
            (fun a b => a ∈ S ∧ b ∈ S ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1)
            x x' := by
        intro w hw
        induction hw with
        | refl => exact ⟨x, rfl, Relation.ReflTransGen.refl⟩
        | @tail b c _ hbc ih =>
          obtain ⟨x₁, hx₁, path⟩ := ih
          obtain ⟨hbY, hcY, -, μ, hμ | hμ⟩ := hbc
          · obtain ⟨x', hx', hp⟩ := walk_next hn S hS ((hmemS x₁).2 (hx₁ ▸ hbY)) μ
              (fun y hy => (hmemS y).2 (by rw [hy, hx₁, ← hμ]; exact hcY)) hD
            exact ⟨x', by rw [hx', hx₁, hμ], path.trans hp⟩
          · obtain ⟨y, hy⟩ := exists_site hn hD c
            have hyS : y ∈ S := (hmemS y).2 (hy ▸ hcY)
            obtain ⟨y', hy', hp⟩ := walk_next hn S hS hyS μ
              (fun z hz => (hmemS z).2 (by rw [hz, hy, ← hμ]; exact hbY)) hD
            have h1 : pic[y'] = pic[x₁] := by rw [hy', hy, ← hμ, hx₁]
            have h2 := walk_cell hn S hS ((hmemS x₁).2 (hx₁ ▸ hbY)) h1
            exact ⟨y, hy, path.trans (h2.trans (rtg_symm_fine S hp))⟩
      obtain ⟨x', hx', hp⟩ := lift _ (hconn _ ((hmemS x).1 hx) _ ((hmemS y).1 hy))
      exact hp.trans (walk_cell hn S hS ((hmemS x').2 (hx' ▸ (hmemS y).1 hy)) hx'.symm)

/-- The set of cells of the tower, `cellsOf`, written with centred representatives of the cells
(`valMinAbs`), is the preimage of the set of cells `Y`: it is a polymer of blocks of side `D` iff
`Y` is an animal of the block torus. -/
theorem isPolymer_cellsOf_iff [NeZero n] [NeZero K] (hn : n = D * K) (hD : 0 < D)
    (Y : Finset (Fin d → ZMod K)) :
    IsPolymer d n D (Finset.univ.filter fun x : Fin d → ZMod n =>
        (fun μ => ((((x μ).val / D : ℕ)) : ZMod K).valMinAbs) ∈
          Y.image (fun b μ => (b μ).valMinAbs)) ↔ IsAnimal (blockGraph d K) Y := by
  classical
  rw [← isPolymer_preimage_iff hn hD Y]
  have : (Finset.univ.filter fun x : Fin d → ZMod n =>
        (fun μ => ((((x μ).val / D : ℕ)) : ZMod K).valMinAbs) ∈
          Y.image (fun b μ => (b μ).valMinAbs)) =
      Finset.univ.filter fun x : Fin d → ZMod n => pic[x] ∈ Y := by
    refine Finset.filter_congr fun x _ => ?_
    constructor
    · intro h
      obtain ⟨b, hb, he⟩ := Finset.mem_image.1 h
      have : b = pic[x] := funext fun μ => ZMod.valMinAbs_inj.1 (congrFun he μ)
      rwa [← this]
    · intro h
      exact Finset.mem_image.2 ⟨_, h, rfl⟩
  rw [this]

/-- A set of fine sites is a polymer of blocks of side `D` iff it is the preimage under the cell map
of an animal of the block torus. -/
theorem isPolymer_iff_exists_animal [NeZero n] [NeZero K] (hn : n = D * K) (hD : 0 < D)
    (X : Finset (Fin d → ZMod n)) :
    IsPolymer d n D X ↔ ∃ Y : Finset (Fin d → ZMod K), IsAnimal (blockGraph d K) Y ∧
      X = Finset.univ.filter fun x : Fin d → ZMod n => pic[x] ∈ Y := by
  classical
  constructor
  · intro h
    refine ⟨X.image fun x j₀ => ((((x j₀).val / D : ℕ)) : ZMod K), ?_, ?_⟩
    · rw [← isPolymer_preimage_iff hn hD]
      convert h using 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨x, hx, hxy⟩
        refine h.2.1 x hx y fun μ => ?_
        have h1 := congrFun hxy μ
        have hK : ∀ z : ZMod n, z.val / D < K := fun z => by
          rw [Nat.div_lt_iff_lt_mul hD]
          exact lt_of_lt_of_eq (ZMod.val_lt z) (by rw [hn, mul_comm])
        have := (ZMod.natCast_eq_natCast_iff' _ _ K).1 h1
        rwa [Nat.mod_eq_of_lt (hK _), Nat.mod_eq_of_lt (hK _)] at this
      · intro hy; exact ⟨y, hy, rfl⟩
    · ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hy; exact ⟨y, hy, rfl⟩
      · rintro ⟨x, hx, hxy⟩
        refine h.2.1 x hx y fun μ => ?_
        have h1 := congrFun hxy μ
        have hK : ∀ z : ZMod n, z.val / D < K := fun z => by
          rw [Nat.div_lt_iff_lt_mul hD]
          exact lt_of_lt_of_eq (ZMod.val_lt z) (by rw [hn, mul_comm])
        have := (ZMod.natCast_eq_natCast_iff' _ _ K).1 h1
        rwa [Nat.mod_eq_of_lt (hK _), Nat.mod_eq_of_lt (hK _)] at this
  · rintro ⟨Y, hY, rfl⟩
    exact (isPolymer_preimage_iff hn hD Y).2 hY

/-- The set of cells of a polymer (centred representatives) is the image of an animal `Y` of the
block torus, as in the description of `P ℓ` of the tower, and the polymer is the set of fine sites
whose centred cell lies in it. -/
theorem exists_animal_of_isPolymer [NeZero n] [NeZero K] (hn : n = D * K) (hD : 0 < D)
    {X : Finset (Fin d → ZMod n)} (h : IsPolymer d n D X) :
    ∃ Y : Finset (Fin d → ZMod K), IsAnimal (blockGraph d K) Y ∧
      X.image (fun x μ => ((((x μ).val / D : ℕ)) : ZMod K).valMinAbs) =
        Y.image (fun b μ => (b μ).valMinAbs) ∧
      X = Finset.univ.filter fun x : Fin d → ZMod n =>
        (fun μ => ((((x μ).val / D : ℕ)) : ZMod K).valMinAbs) ∈
          Y.image (fun b μ => (b μ).valMinAbs) := by
  classical
  obtain ⟨Y, hY, rfl⟩ := (isPolymer_iff_exists_animal hn hD X).1 h
  refine ⟨Y, hY, ?_, ?_⟩
  · ext z
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, hx, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨x, rfl⟩ := exists_site hn hD b
      exact ⟨x, hb, rfl⟩
  · ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx; exact ⟨_, hx, rfl⟩
    · rintro ⟨b, hb, he⟩
      have : b = pic[x] := funext fun μ => ZMod.valMinAbs_inj.1 (congrFun he μ)
      rwa [← this]

end Animal

end Balaban.Polymer.TwoTorusStep
