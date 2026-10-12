/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.PolymerGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lifted cells and the cost of linking face-adjacent cells (GRAPH-GM-2 §3, (3.3))

A cell is an integer box `c = base + [0, side)^d` of `ℤ^d`; a cell of the torus is the image of
such a box (the lift is part of the data, so adjacency across the seam of the torus is adjacency of
suitable lifts).  `ZFaceAdj c c'` says that the two boxes share a `(d-1)`-dimensional face portion.

* `ZWalk R x y ℓ`: a nearest-neighbour walk of `ℓ` bonds inside `R ⊂ ℤ^d`; `zwalk_box` joins two
  points of an integer box by a walk of `ℓ¹`-length (coordinate staircase).
* `zcell_walk`: the centres of two face-adjacent cells with nested alignment (`side' ∣ side` or
  `side ∣ side'`, the bases divisible by their sides) are joined inside the union of the two
  cells by a walk with `2 ℓ ≤ (d+1) max(side, side') + 1`, i.e. scaled length `≤ (d+1)/2` as in
  GRAPH-GM-2 (3.3), up to the parity half-bond.
-/

@[expose] public section

namespace Balaban.Localization

open Finset

section Walk

variable {d : ℕ}

/-- Nearest neighbours in `ℤ^d`. -/
def ZStep (a b : Fin d → ℤ) : Prop :=
  ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1

/-- A nearest-neighbour walk of `ℓ` bonds inside `R ⊂ ℤ^d`. -/
inductive ZWalk (R : Set (Fin d → ℤ)) : (Fin d → ℤ) → (Fin d → ℤ) → ℕ → Prop
  | refl {x : Fin d → ℤ} (hx : x ∈ R) : ZWalk R x x 0
  | step {x y z : Fin d → ℤ} {ℓ : ℕ} (hx : x ∈ R) (h : ZStep x y) (w : ZWalk R y z ℓ) :
      ZWalk R x z (ℓ + 1)

theorem ZWalk.mem_left {R : Set (Fin d → ℤ)} {x y : Fin d → ℤ} {ℓ : ℕ} (h : ZWalk R x y ℓ) :
    x ∈ R := by
  cases h with
  | refl hx => exact hx
  | step hx _ _ => exact hx

theorem ZWalk.mem_right {R : Set (Fin d → ℤ)} {x y : Fin d → ℤ} {ℓ : ℕ} (h : ZWalk R x y ℓ) :
    y ∈ R := by
  induction h with
  | refl hx => exact hx
  | step _ _ _ ih => exact ih

theorem ZWalk.trans {R : Set (Fin d → ℤ)} {x y z : Fin d → ℤ} {ℓ ℓ' : ℕ} (h : ZWalk R x y ℓ)
    (h' : ZWalk R y z ℓ') : ZWalk R x z (ℓ + ℓ') := by
  induction h with
  | refl _ => simpa using h'
  | @step x y' z' ℓ hx hs w ih =>
    have := ZWalk.step hx hs (ih h')
    rwa [show ℓ + 1 + ℓ' = ℓ + ℓ' + 1 by ring]

theorem ZStep.symm {a b : Fin d → ℤ} (h : ZStep a b) : ZStep b a := by
  obtain ⟨μ, h | h⟩ := h
  · exact ⟨μ, Or.inr h⟩
  · exact ⟨μ, Or.inl h⟩

theorem ZWalk.symm {R : Set (Fin d → ℤ)} {x y : Fin d → ℤ} {ℓ : ℕ} (h : ZWalk R x y ℓ) :
    ZWalk R y x ℓ := by
  induction h with
  | refl hx => exact ZWalk.refl hx
  | @step x y z ℓ hx hs w ih =>
    have h1 : ZWalk R y x 1 := ZWalk.step w.mem_left hs.symm (ZWalk.refl hx)
    have := ih.trans h1
    exact this

theorem ZWalk.mono {R R' : Set (Fin d → ℤ)} (hR : R ⊆ R') {x y : Fin d → ℤ} {ℓ : ℕ}
    (h : ZWalk R x y ℓ) : ZWalk R' x y ℓ := by
  induction h with
  | refl hx => exact ZWalk.refl (hR hx)
  | step hx hs _ ih => exact ZWalk.step (hR hx) hs ih

/-- The integer box `[lo, hi]`. -/
def ZIcc (lo hi : Fin d → ℤ) : Set (Fin d → ℤ) := {x | ∀ μ, lo μ ≤ x μ ∧ x μ ≤ hi μ}

/-- **Coordinate staircase**: two points of an integer box are joined inside it by a walk of
`ℓ¹`-length. -/
theorem zwalk_box (lo hi y : Fin d → ℤ) (hy : y ∈ ZIcc lo hi) :
    ∀ (n : ℕ) (x : Fin d → ℤ), x ∈ ZIcc lo hi → ∑ μ, (x μ - y μ).natAbs = n →
      ZWalk (ZIcc lo hi) x y n := by
  intro n
  induction n with
  | zero =>
    intro x hx he
    have : x = y := by
      funext μ
      have := (Finset.sum_eq_zero_iff.1 he) μ (Finset.mem_univ _)
      omega
    subst this
    exact ZWalk.refl hx
  | succ n ih =>
    intro x hx he
    have : ∃ μ, x μ ≠ y μ := by
      by_contra hcon
      push Not at hcon
      simp [hcon] at he
    obtain ⟨μ, hμ⟩ := this
    obtain ⟨s, hs, hs'⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
        (x μ + s - y μ).natAbs + 1 = (x μ - y μ).natAbs := by
      rcases lt_or_gt_of_ne hμ with h | h
      · exact ⟨1, Or.inl rfl, by omega⟩
      · exact ⟨-1, Or.inr rfl, by omega⟩
    set x' := Function.update x μ (x μ + s) with hx'
    have hx'mem : x' ∈ ZIcc lo hi := by
      intro ν
      by_cases hν : ν = μ
      · subst hν
        have h1 := hx ν
        have h2 := hy ν
        simp only [hx', Function.update_self]
        rcases hs with rfl | rfl <;> omega
      · simp only [hx', Function.update_of_ne hν]
        exact hx ν
    have hsum : ∑ ν, (x' ν - y ν).natAbs = n := by
      have h3 : ∑ ν, (x' ν - y ν).natAbs =
          (x μ + s - y μ).natAbs + ∑ ν ∈ Finset.univ.erase μ, (x ν - y ν).natAbs := by
        rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin d)) (fun ν => (x' ν - y ν).natAbs)
          (Finset.mem_univ μ)]
        congr 1
        · simp [hx']
        · refine Finset.sum_congr rfl fun ν hν => ?_
          simp [hx', Function.update_of_ne (Finset.ne_of_mem_erase hν)]
      have h2 := Finset.add_sum_erase (Finset.univ : Finset (Fin d))
        (fun ν => (x ν - y ν).natAbs) (Finset.mem_univ μ)
      omega
    have hstep : ZStep x x' := by
      refine ⟨μ, ?_⟩
      rcases hs with rfl | rfl
      · left
        funext ν
        by_cases hν : ν = μ
        · subst hν; simp [hx']
        · simp [hx', hν]
      · right
        funext ν
        by_cases hν : ν = μ
        · subst hν; simp [hx']
        · simp [hx', hν]
    exact ZWalk.step hx hstep (ih x' hx'mem hsum)

end Walk

section Cells

variable {d : ℕ}

/-- An integer cell: the box `base + [0, side)^d`. -/
structure ZCell (d : ℕ) where
  /-- the lower corner -/
  base : Fin d → ℤ
  /-- the side -/
  side : ℕ
  deriving DecidableEq

/-- The sites of the integer cell. -/
def ZCell.pts (c : ZCell d) : Set (Fin d → ℤ) :=
  {x | ∀ μ, c.base μ ≤ x μ ∧ x μ < c.base μ + c.side}

/-- The centre point of a cell (the lower corner shifted by `⌊side / 2⌋`). -/
def ZCell.rep (c : ZCell d) : Fin d → ℤ := fun μ => c.base μ + ((c.side / 2 : ℕ) : ℤ)

/-- **Physical face adjacency** of two cells: they are disjoint and share a `(d-1)`-dimensional
face portion: in one coordinate `μ` the cells abut, and in every other coordinate their
projections overlap. -/
def ZFaceAdj (c c' : ZCell d) : Prop :=
  ∃ μ : Fin d, (c'.base μ = c.base μ + c.side ∨ c'.base μ + c'.side = c.base μ) ∧
    ∀ ν, ν ≠ μ → c.base ν < c'.base ν + c'.side ∧ c'.base ν < c.base ν + c.side

theorem ZFaceAdj.symm {c c' : ZCell d} (h : ZFaceAdj c c') : ZFaceAdj c' c := by
  obtain ⟨μ, h1, h2⟩ := h
  refine ⟨μ, ?_, fun ν hν => ?_⟩
  · rcases h1 with h1 | h1
    · right; omega
    · left; omega
  · exact ⟨(h2 ν hν).2, (h2 ν hν).1⟩

theorem ZCell.rep_mem (c : ZCell d) (h : 0 < c.side) : c.rep ∈ c.pts := by
  intro μ
  simp only [ZCell.rep]
  have : ((c.side / 2 : ℕ) : ℤ) < c.side := by omega
  constructor <;> omega

theorem ZCell.pts_subset_Icc (c : ZCell d) :
    c.pts ⊆ ZIcc c.base (fun μ => c.base μ + c.side - 1) := by
  intro x hx μ
  have := hx μ
  dsimp only at this ⊢
  constructor <;> omega

theorem ZCell.Icc_subset_box (c : ZCell d) :
    ZIcc c.base (fun μ => c.base μ + c.side - 1) ⊆ c.pts := by
  intro x hx μ
  have := hx μ
  dsimp only at this ⊢
  constructor <;> omega

/-- **Tangential nesting** (alignment): if `side' ∣ side`, the bases are divisible by their
sides and the intervals overlap, the interval of `c'` lies inside that of `c`. -/
theorem tangential_nest {b s b' s' : ℤ} (hs : 0 < s') (hdvd : s' ∣ s) (hb : s ∣ b) (hb' : s' ∣ b')
    (h1 : b < b' + s') (h2 : b' < b + s) : b ≤ b' ∧ b' + s' ≤ b + s := by
  obtain ⟨k, hk⟩ := hdvd
  obtain ⟨m, hm⟩ := hb
  obtain ⟨m', hm'⟩ := hb'
  have hbs' : s' ∣ b := ⟨k * m, by rw [hm, hk]; ring⟩
  obtain ⟨j, hj⟩ := hbs'
  -- b = s' j, b' = s' m', s = s' k
  have hb1 : s' * j < s' * m' + s' := by rw [← hj, ← hm']; exact h1
  have hb2 : s' * m' < s' * j + s := by rw [← hj, ← hm']; exact h2
  have h3 : j < m' + 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have h4 : m' < j + k := by
    by_contra hcon
    push Not at hcon
    rw [hk] at hb2
    nlinarith
  rw [hj, hm']
  constructor
  · nlinarith
  · rw [hk]; nlinarith

/-- **Linking two face-adjacent cells** (GRAPH-GM-2 (3.3)).  If `c'` is not larger than `c`
(`side' ∣ side`), the bases are divisible by the sides and the cells are face-adjacent, then the
centres of the cells are joined inside `c ∪ c'` by a walk of `ℓ` bonds with
`2 ℓ ≤ (d + 1) side + 1`. -/
theorem zcell_walk_aux (c c' : ZCell d) (hs : 0 < c.side) (hs' : 0 < c'.side)
    (hdvd : (c'.side : ℤ) ∣ c.side) (hb : ∀ μ, (c.side : ℤ) ∣ c.base μ)
    (hb' : ∀ μ, (c'.side : ℤ) ∣ c'.base μ) (hadj : ZFaceAdj c c') :
    ∃ ℓ, 2 * ℓ ≤ (d + 1) * c.side + 1 ∧ ZWalk (c.pts ∪ c'.pts) c.rep c'.rep ℓ := by
  classical
  obtain ⟨μ, hn, ht⟩ := hadj
  have hss : c'.side ≤ c.side := by
    have := Int.le_of_dvd (by exact_mod_cast hs) hdvd
    exact_mod_cast this
  have hnest : ∀ ν, ν ≠ μ → c.base ν ≤ c'.base ν ∧ c'.base ν + c'.side ≤ c.base ν + c.side :=
    fun ν hν => tangential_nest (by exact_mod_cast hs') hdvd (hb ν) (hb' ν) (ht ν hν).1 (ht ν hν).2
  set z : Fin d → ℤ := Function.update c'.rep μ (c.rep μ) with hz
  -- first leg inside `c`
  have hzc : z ∈ ZIcc c.base (fun ν => c.base ν + c.side - 1) := by
    intro ν
    by_cases hν : ν = μ
    · subst hν
      simp only [hz, Function.update_self, ZCell.rep]
      have : ((c.side / 2 : ℕ) : ℤ) < c.side := by omega
      constructor <;> omega
    · simp only [hz, Function.update_of_ne hν, ZCell.rep]
      have := hnest ν hν
      have : ((c'.side / 2 : ℕ) : ℤ) < c'.side := by omega
      constructor <;> omega
  have hrc : c.rep ∈ ZIcc c.base (fun ν => c.base ν + c.side - 1) :=
    c.pts_subset_Icc (c.rep_mem hs)
  have hA := zwalk_box c.base (fun ν => c.base ν + c.side - 1) z hzc _ c.rep hrc rfl
  -- bound on the first leg
  have hAb : ∑ ν, (c.rep ν - z ν).natAbs ≤ (d - 1) * (c.side / 2) := by
    have h2 := Finset.add_sum_erase (Finset.univ : Finset (Fin d))
      (fun ν => (c.rep ν - z ν).natAbs) (Finset.mem_univ μ)
    have h0 : (c.rep μ - z μ).natAbs = 0 := by simp [hz]
    have h3 : ∑ ν ∈ Finset.univ.erase μ, (c.rep ν - z ν).natAbs ≤
        ∑ _ν ∈ Finset.univ.erase μ, c.side / 2 := by
      refine Finset.sum_le_sum fun ν hν => ?_
      have hν' := Finset.ne_of_mem_erase hν
      have := hnest ν hν'
      simp only [hz, Function.update_of_ne hν', ZCell.rep]
      omega
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at h3
    omega
  -- the slab for the second leg
  set lo' : Fin d → ℤ := fun ν => if ν = μ then min (c.base μ) (c'.base μ) else c'.base ν
    with hlo
  set hi' : Fin d → ℤ := fun ν => if ν = μ then
    max (c.base μ + c.side - 1) (c'.base μ + c'.side - 1) else c'.base ν + c'.side - 1 with hhi
  have hslab : ZIcc lo' hi' ⊆ c.pts ∪ c'.pts := by
    intro q hq
    by_cases hq1 : c.base μ ≤ q μ ∧ q μ < c.base μ + c.side
    · left
      intro ν
      by_cases hν : ν = μ
      · subst hν; exact hq1
      · have := hq ν
        have h4 := hnest ν hν
        simp only [hlo, hhi, hν, ↓reduceIte] at this
        constructor <;> omega
    · right
      intro ν
      by_cases hν : ν = μ
      · subst hν
        have := hq ν
        simp only [hlo, hhi, ↓reduceIte] at this
        rcases hn with hn | hn <;> constructor <;> omega
      · have := hq ν
        simp only [hlo, hhi, hν, ↓reduceIte] at this
        constructor <;> omega
  have hz2 : z ∈ ZIcc lo' hi' := by
    intro ν
    by_cases hν : ν = μ
    · subst hν
      simp only [hz, hlo, hhi, Function.update_self, ↓reduceIte, ZCell.rep]
      have : ((c.side / 2 : ℕ) : ℤ) < c.side := by omega
      constructor <;> omega
    · simp only [hz, hlo, hhi, Function.update_of_ne hν, hν, ↓reduceIte, ZCell.rep]
      have : ((c'.side / 2 : ℕ) : ℤ) < c'.side := by omega
      constructor <;> omega
  have hr2 : c'.rep ∈ ZIcc lo' hi' := by
    intro ν
    by_cases hν : ν = μ
    · subst hν
      simp only [hlo, hhi, ↓reduceIte, ZCell.rep]
      have : ((c'.side / 2 : ℕ) : ℤ) < c'.side := by omega
      constructor <;> omega
    · simp only [hlo, hhi, hν, ↓reduceIte, ZCell.rep]
      have : ((c'.side / 2 : ℕ) : ℤ) < c'.side := by omega
      constructor <;> omega
  have hB := zwalk_box lo' hi' c'.rep hr2 _ z hz2 rfl
  have hBb : ∑ ν, (z ν - c'.rep ν).natAbs = (c.rep μ - c'.rep μ).natAbs := by
    rw [Finset.sum_eq_single μ]
    · simp [hz]
    · intro ν _ hν
      simp [hz, Function.update_of_ne hν]
    · simp
  rw [hBb] at hB
  have hBc : 2 * (c.rep μ - c'.rep μ).natAbs ≤ c.side + c'.side + 1 := by
    simp only [ZCell.rep]
    rcases hn with hn | hn <;> omega
  refine ⟨_, ?_, (hA.mono ?_).trans (hB.mono ?_)⟩
  · have h5 : 2 * (c.side / 2) ≤ c.side := Nat.mul_div_le _ _
    have h6 : 2 * ((d - 1) * (c.side / 2)) ≤ (d - 1) * c.side := by
      rw [mul_left_comm]; exact Nat.mul_le_mul_left _ h5
    have h7 : (d - 1) * c.side + c.side = d * c.side := by
      have hd0 : 0 < d := Fin.pos μ
      rw [← Nat.succ_mul]; congr 1; omega
    have hf : 2 * (∑ ν, (c.rep ν - z ν).natAbs + (c.rep μ - c'.rep μ).natAbs) ≤
        d * c.side + c'.side + 1 := by omega
    calc _ ≤ d * c.side + c'.side + 1 := hf
      _ ≤ (d + 1) * c.side + 1 := by nlinarith
  · exact (ZCell.Icc_subset_box c).trans Set.subset_union_left
  · exact hslab

/-- **Linking two face-adjacent layered cells**, either one possibly the larger: the centres are
joined inside the union by a walk with `2 ℓ ≤ (d+1) max(side, side') + 1`. -/
theorem zcell_walk (c c' : ZCell d) (hs : 0 < c.side) (hs' : 0 < c'.side)
    (hnest : (c'.side : ℤ) ∣ c.side ∨ (c.side : ℤ) ∣ c'.side)
    (hb : ∀ μ, (c.side : ℤ) ∣ c.base μ) (hb' : ∀ μ, (c'.side : ℤ) ∣ c'.base μ)
    (hadj : ZFaceAdj c c') :
    ∃ ℓ, 2 * ℓ ≤ (d + 1) * max c.side c'.side + 1 ∧ ZWalk (c.pts ∪ c'.pts) c.rep c'.rep ℓ := by
  rcases hnest with h | h
  · obtain ⟨ℓ, h1, h2⟩ := zcell_walk_aux c c' hs hs' h hb hb' hadj
    exact ⟨ℓ, h1.trans (by have := le_max_left c.side c'.side; nlinarith), h2⟩
  · obtain ⟨ℓ, h1, h2⟩ := zcell_walk_aux c' c hs' hs h hb' hb hadj.symm
    refine ⟨ℓ, h1.trans (by have := le_max_right c.side c'.side; nlinarith), ?_⟩
    have := h2.symm
    rwa [Set.union_comm] at this

end Cells

end Balaban.Localization
