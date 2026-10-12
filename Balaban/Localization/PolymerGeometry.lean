/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Cover
public import Balaban.Localization.Geometry
public import Balaban.Localization.Peierls
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polymer geometry: cells, boxes and the sets `D(P)`, `Y[𝒞]` (LOCALIZATION.md §4.2)

Sites are the points of a torus `Torus d n`.  A *box* `box b s` is the set of sites
`b + w`, `w ∈ [0, s)^d` (coordinatewise natural numbers).  A *cell* of side `a` is a box `box b a`
with *aligned* base `b` (all coordinates of `b` are divisible by `a`); `cbase a z` is the base of
the cell containing `z`.  For a layer `n` the side of the cells (`π_n`-cubes) is `a_n = L ^ (n + m₀ + m₁)`
and a `π'_n`-cube is a box `box b (L a_n)` with aligned base.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset

section Arith

variable {d n : ℕ}

/-- The torus element with natural coordinates `w`. -/
def natT (w : Fin d → ℕ) : Torus d n := fun μ => ((w μ : ℕ) : ZMod n)

@[simp] theorem natT_apply (w : Fin d → ℕ) (μ : Fin d) :
    (natT w : Torus d n) μ = ((w μ : ℕ) : ZMod n) := rfl

theorem natT_add (w w' : Fin d → ℕ) : (natT (w + w') : Torus d n) = natT w + natT w' := by
  funext μ; simp [natT]

theorem natT_zero : (natT (0 : Fin d → ℕ) : Torus d n) = 0 := by
  funext μ; simp [natT]

theorem natT_sub {w w' : Fin d → ℕ} (h : ∀ μ, w' μ ≤ w μ) :
    (natT (w - w') : Torus d n) = natT w - natT w' := by
  funext μ; simp [natT, Nat.cast_sub (h μ)]

/-- The box `b + [0, s)^d`. -/
def box (b : Torus d n) (s : ℕ) : Set (Torus d n) :=
  {x | ∃ w : Fin d → ℕ, (∀ μ, w μ < s) ∧ x = b + natT w}

/-- `b` is aligned to the grid of side `a`. -/
def Aligned (a : ℕ) (b : Torus d n) : Prop := ∀ μ, (b μ).val % a = 0

/-- The base of the cell of side `a` containing `z`. -/
def cbase (a : ℕ) (z : Torus d n) : Torus d n := fun μ => ((a * ((z μ).val / a) : ℕ) : ZMod n)

theorem mem_box_self (b : Torus d n) {s : ℕ} (hs : 0 < s) : b ∈ box b s :=
  ⟨0, fun _ => hs, by simp [natT_zero]⟩

theorem mem_box_add (b : Torus d n) {s : ℕ} {w : Fin d → ℕ} (hw : ∀ μ, w μ < s) :
    b + natT w ∈ box b s := ⟨w, hw, rfl⟩

theorem box_mono (b : Torus d n) {s s' : ℕ} (h : s ≤ s') : box b s ⊆ box b s' :=
  fun _ ⟨w, hw, hx⟩ => ⟨w, fun μ => lt_of_lt_of_le (hw μ) h, hx⟩

theorem val_add_natT [NeZero n] (a : ℕ) (ha : a ∣ n) (b : Torus d n) (w : Fin d → ℕ) (μ : Fin d) :
    ((b + natT w : Torus d n) μ).val % a = ((b μ).val + w μ) % a := by
  have h1 : ((b + natT w : Torus d n) μ).val = ((b μ).val + w μ % n) % n := by
    simp [ZMod.val_add, ZMod.val_natCast]
  rw [h1, Nat.mod_mod_of_dvd _ ha]
  rw [Nat.add_mod, Nat.mod_mod_of_dvd _ ha, ← Nat.add_mod]

theorem aligned_add_natT [NeZero n] {a : ℕ} (ha : a ∣ n) {b : Torus d n} (hb : Aligned a b)
    {w : Fin d → ℕ} (hw : ∀ μ, w μ % a = 0) : Aligned a (b + natT w) := by
  intro μ
  rw [val_add_natT a ha, Nat.add_mod, hb μ, hw μ]; simp

theorem mod_of_aligned_add [NeZero n] {a : ℕ} (ha : a ∣ n) {b : Torus d n} (hb : Aligned a b)
    {w : Fin d → ℕ} (μ : Fin d) : ((b + natT w : Torus d n) μ).val % a = w μ % a := by
  rw [val_add_natT a ha, Nat.add_mod, hb μ, zero_add, Nat.mod_mod]

theorem cbase_eq_sub [NeZero n] (a : ℕ) (z : Torus d n) :
    cbase a z = z - natT (fun μ => (z μ).val % a) := by
  funext μ
  have h1 : (z μ).val % a ≤ (z μ).val := Nat.mod_le _ _
  have h2 : a * ((z μ).val / a) = (z μ).val - (z μ).val % a := by
    have := Nat.div_add_mod (z μ).val a
    omega
  simp only [cbase, natT, Pi.sub_apply, h2, Nat.cast_sub h1, ZMod.natCast_zmod_val]

theorem aligned_cbase [NeZero n] {a : ℕ} (z : Torus d n) : Aligned a (cbase a z) := by
  intro μ
  have hlt : a * ((z μ).val / a) < n := by
    calc a * ((z μ).val / a) ≤ (z μ).val := Nat.mul_div_le _ _
      _ < n := ZMod.val_lt _
  have : ((cbase a z) μ).val = a * ((z μ).val / a) := by
    simp only [cbase]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  rw [this]; exact Nat.mul_mod_right _ _

theorem mem_box_cbase [NeZero n] {a : ℕ} (ha : 0 < a) (z : Torus d n) : z ∈ box (cbase a z) a := by
  refine ⟨fun μ => (z μ).val % a, fun μ => Nat.mod_lt _ ha, ?_⟩
  rw [cbase_eq_sub]; abel

theorem cbase_add [NeZero n] {a : ℕ} (ha : a ∣ n) {b : Torus d n} (hb : Aligned a b) (w : Fin d → ℕ) :
    cbase a (b + natT w) = b + natT (fun μ => w μ - w μ % a) := by
  rw [cbase_eq_sub]
  have h : (fun μ => ((b + natT w : Torus d n) μ).val % a) = fun μ => w μ % a :=
    funext fun μ => mod_of_aligned_add ha hb μ
  rw [h]
  have hle : ∀ μ, (fun μ => w μ % a) μ ≤ w μ := fun μ => Nat.mod_le _ _
  have : (fun μ => w μ - w μ % a) = w - fun μ => w μ % a := rfl
  rw [this, natT_sub hle, add_sub_assoc]

theorem cbase_eq_of_mem_box [NeZero n] {a : ℕ} (ha : a ∣ n) {c : Torus d n} (hc : Aligned a c) {y : Torus d n}
    (hy : y ∈ box c a) : cbase a y = c := by
  obtain ⟨w, hw, rfl⟩ := hy
  rw [cbase_add ha hc]
  have : (fun μ => w μ - w μ % a) = 0 := funext fun μ => by
    simp [Nat.mod_eq_of_lt (hw μ)]
  rw [this, natT_zero, add_zero]

end Arith

/-! ### The lattice and monotone chains -/

section Lattice

variable {d n : ℕ}

/-- Nearest-neighbour relation of the torus (possibly reflexive on tiny tori). -/
def Nbr (x y : Torus d n) : Prop := ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ x = y + Pi.single μ 1

theorem Nbr.symm {x y : Torus d n} (h : Nbr x y) : Nbr y x := by
  obtain ⟨μ, h | h⟩ := h
  · exact ⟨μ, Or.inr h⟩
  · exact ⟨μ, Or.inl h⟩

/-- The nearest-neighbour graph of the torus. -/
def latGraph (d n : ℕ) : SimpleGraph (Torus d n) where
  Adj a b := a ≠ b ∧ Nbr a b
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem natT_single (μ : Fin d) : (natT (Pi.single μ 1) : Torus d n) = Pi.single μ 1 := by
  funext ν
  by_cases h : ν = μ
  · subst h; simp [natT]
  · simp [natT, Pi.single_eq_of_ne h]

/-- Monotone chains in `ℕ ^ d`: if every elementary step below `w₀` is a `ρ 1`-step, then
`f 0` and `f w₀` are joined by a `ρ (∑ w₀)`-chain. -/
theorem chain_of_steps {X : Type*} (ρ : ℕ → X → X → Prop)
    (f : (Fin d → ℕ) → X) (hrefl : ρ 0 (f 0) (f 0))
    (htrans : ∀ {m m' x y z}, ρ m x y → ρ m' y z → ρ (m + m') x z) :
    ∀ (m : ℕ) (w₀ : Fin d → ℕ), ∑ μ, w₀ μ = m →
      (∀ w μ, w + Pi.single μ 1 ≤ w₀ → ρ 1 (f w) (f (w + Pi.single μ 1))) →
        ρ m (f 0) (f w₀) := by
  intro m
  induction m with
  | zero =>
    intro w₀ hm _
    have : w₀ = 0 := by
      funext μ
      have := (Finset.sum_eq_zero_iff.1 hm) μ (Finset.mem_univ _)
      simpa using this
    subst this
    exact hrefl
  | succ m ih =>
    intro w₀ hm hstep
    have hne : ∃ μ, 0 < w₀ μ := by
      by_contra h
      push Not at h
      have : ∑ μ, w₀ μ = 0 := Finset.sum_eq_zero fun μ _ => by have := h μ; omega
      omega
    obtain ⟨μ, hμ⟩ := hne
    set w₁ : Fin d → ℕ := w₀ - Pi.single μ 1 with hw₁
    have hw₀ : w₀ = w₁ + Pi.single μ 1 := by
      funext ν
      by_cases h : ν = μ
      · subst h; simp [hw₁]; omega
      · simp [hw₁, Pi.single_eq_of_ne h]
    have hle : w₁ ≤ w₀ := by
      intro ν; simp [hw₁]
    have hsum : ∑ ν, w₁ ν = m := by
      have h1 : ∑ ν, w₀ ν = ∑ ν, w₁ ν + 1 := by
        conv_lhs => rw [hw₀]
        simp [Finset.sum_add_distrib]
      omega
    have h1 := ih w₁ hsum (fun w ν hw => hstep w ν (hw.trans hle))
    have h2 := hstep w₁ μ (by rw [← hw₀])
    rw [← hw₀] at h2
    exact htrans h1 h2

theorem rtg_symm {α : Type*} {r : α → α → Prop} (h : ∀ a b, r a b → r b a) {x y : α}
    (hxy : Relation.ReflTransGen r x y) : Relation.ReflTransGen r y x := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (h _ _ hbc)).trans ih

/-- A box is connected from its corner: every point `b + w'` with `w' ≤ w` lying in the region `R`
is joined to `b` by lattice steps inside `R`. -/
theorem reach_box (b : Torus d n) (w : Fin d → ℕ) (R : Set (Torus d n))
    (hR : ∀ w' : Fin d → ℕ, (∀ μ, w' μ ≤ w μ) → b + natT w' ∈ R) :
    Relation.ReflTransGen (fun x y => (latGraph d n).Adj x y ∧ x ∈ R ∧ y ∈ R) b (b + natT w) := by
  have key := chain_of_steps (d := d)
    (fun (_ : ℕ) (x y : Torus d n) =>
      Relation.ReflTransGen (fun x y => (latGraph d n).Adj x y ∧ x ∈ R ∧ y ∈ R) x y)
    (fun w' => b + natT w') Relation.ReflTransGen.refl (fun h h' => h.trans h')
    (∑ μ, w μ) w rfl ?_
  · simpa [natT_zero] using key
  · intro w' μ hw'
    have h1 : b + natT w' ∈ R := hR w' (fun ν => le_trans (by
      have := hw' ν; simp only [Pi.add_apply] at this; omega) le_rfl)
    have h2 : b + natT (w' + Pi.single μ 1) ∈ R := hR _ (fun ν => by
      have := hw' ν; simpa using this)
    have hn : Nbr (b + natT w') (b + natT (w' + Pi.single μ 1)) := by
      refine ⟨μ, Or.inl ?_⟩
      rw [natT_add, natT_single, add_assoc]
    by_cases he : b + natT w' = b + natT (w' + Pi.single μ 1)
    · rw [← he]
    · exact Relation.ReflTransGen.single ⟨⟨he, hn⟩, h1, h2⟩

end Lattice

/-! ### The sets `D(P)` -/

section Polymer

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- The side `a_n = M ℓ_n = L ^ (n + m₀ + m₁)` of a `π_n`-cube. -/
def cellSide (L m₀ m₁ n : ℕ) : ℕ := L ^ (n + m₀ + m₁)

theorem cellSide_pos (m₀ m₁ n : ℕ) : 0 < cellSide L m₀ m₁ n :=
  pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _

omit [NeZero N₁] [NeZero L] in
theorem cellSide_dvd {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) {n : ℕ} (hn : n ≤ K) :
    cellSide L m₀ m₁ n ∣ (N₁ * L ^ m₁) * L ^ K := by
  obtain ⟨c, hc⟩ := hN
  have : (N₁ * L ^ m₁) * L ^ K = L ^ (n + m₀ + m₁) * (c * L ^ (K - n)) := by
    rw [hc]
    have : L ^ K = L ^ n * L ^ (K - n) := by rw [← pow_add]; congr 1; omega
    rw [this]; ring
  rw [this]; exact Dvd.intro _ rfl

/-- The parameter cube `P` of the centre `q = (n, y0)`: the cell of side `L ^ (n + m₁)` of `y0`. -/
def Pset (m₁ : ℕ) (q : ℕ × CTorus d L N₁ m₁ K) : Set (CTorus d L N₁ m₁ K) :=
  {x | SameCell (L ^ (q.1 + m₁)) x q.2}

omit [NeZero N₁] [NeZero L] in
theorem self_mem_Pset (q : ℕ × CTorus d L N₁ m₁ K) : q.2 ∈ Pset m₁ q := SameCell.refl _ _

/-- The cell `□(P)` of side `a_n` containing `P`. -/
def cellOf (L m₀ m₁ : ℕ) (q : ℕ × CTorus d L N₁ m₁ K) : Set (CTorus d L N₁ m₁ K) :=
  box (cbase (cellSide L m₀ m₁ q.1) q.2) (cellSide L m₀ m₁ q.1)

theorem Pset_subset_cellOf (m₀ : ℕ) (q : ℕ × CTorus d L N₁ m₁ K) :
    Pset m₁ q ⊆ cellOf L m₀ m₁ q := by
  intro x hx
  have hdvd : L ^ (q.1 + m₁) ∣ cellSide L m₀ m₁ q.1 := by
    unfold cellSide
    exact pow_dvd_pow L (by omega)
  have h := SameCell.mono hdvd hx
  have hb : cbase (cellSide L m₀ m₁ q.1) x = cbase (cellSide L m₀ m₁ q.1) q.2 := by
    funext μ; simp only [cbase]; rw [h μ]
  unfold cellOf
  rw [← hb]
  exact mem_box_cbase (cellSide_pos m₀ m₁ q.1) x

variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)

/-- The `π'_n`-cubes `□'` (aligned boxes of side `L a_n`) with `□(P) ⊆ □' ⊆ Λ_n`, given by their
bases. -/
def Dcubes (q : ℕ × CTorus d L N₁ m₁ K) : Set (CTorus d L N₁ m₁ K) :=
  {b | Aligned (cellSide L m₀ m₁ q.1) b ∧ cellOf L m₀ m₁ q ⊆ box b (L * cellSide L m₀ m₁ q.1) ∧
    box b (L * cellSide L m₀ m₁ q.1) ⊆ ↑(G.layer q.1)}

/-- `D(P)`: the union of the `π'_n`-cubes `□' ⊇ □(P)` inside `Λ_n` (the sites). -/
def Dsites (q : ℕ × CTorus d L N₁ m₁ K) : Set (CTorus d L N₁ m₁ K) :=
  ⋃ b ∈ Dcubes G m₀ q, box b (L * cellSide L m₀ m₁ q.1)

open Classical in
/-- The `π_n`-cubes of `D(P)`, as the aligned bases (cell labels) of its cells. -/
noncomputable def Dbases (q : ℕ × CTorus d L N₁ m₁ K) : Finset (CTorus d L N₁ m₁ K) :=
  Finset.univ.filter fun b => Aligned (cellSide L m₀ m₁ q.1) b ∧ b ∈ Dsites G m₀ q

variable {G m₀}

theorem Dsites_subset_layer (q : ℕ × CTorus d L N₁ m₁ K) : Dsites G m₀ q ⊆ ↑(G.layer q.1) := by
  intro x hx
  simp only [Dsites, Set.mem_iUnion] at hx
  obtain ⟨b, hb, hx⟩ := hx
  exact hb.2.2 hx

theorem cellOf_subset_Dsites {q : ℕ × CTorus d L N₁ m₁ K} {b : CTorus d L N₁ m₁ K}
    (hb : b ∈ Dcubes G m₀ q) : cellOf L m₀ m₁ q ⊆ Dsites G m₀ q := by
  intro x hx
  simp only [Dsites, Set.mem_iUnion]
  exact ⟨b, hb, hb.2.1 hx⟩

/-- `Λ_n` is a union of `π'_n`-cubes (each component of `Λ_n` lies in `𝒟_n`). -/
def LayerUnion (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ) : Prop :=
  ∀ n, 1 ≤ n → n ≤ K → ∀ z ∈ G.layer n, ∃ b, Aligned (cellSide L m₀ m₁ n) b ∧
    z ∈ box b (L * cellSide L m₀ m₁ n) ∧ box b (L * cellSide L m₀ m₁ n) ⊆ ↑(G.layer n)

/-- The cell of a point of an aligned cube lies in the cube. -/
theorem cell_subset_cube {a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K) (ha0 : 0 < a)
    {b z : CTorus d L N₁ m₁ K} (hb : Aligned a b) (hz : z ∈ box b (L * a)) :
    box (cbase a z) a ⊆ box b (L * a) := by
  obtain ⟨w, hw, rfl⟩ := hz
  rw [cbase_add ha hb]
  rintro x ⟨r, hr, rfl⟩
  refine ⟨(fun μ => w μ - w μ % a) + r, fun μ => ?_, ?_⟩
  · have h1 : w μ - w μ % a = a * (w μ / a) := by
      have := Nat.div_add_mod (w μ) a; omega
    have h2 : w μ / a < L := by
      rw [Nat.div_lt_iff_lt_mul ha0]; exact hw μ
    simp only [Pi.add_apply]
    rw [h1]
    have := hr μ
    nlinarith
  · rw [natT_add, add_assoc]

theorem exists_Dcubes (hU : LayerUnion G m₀) (hN : L ^ m₀ ∣ N₁) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) : ∃ b, b ∈ Dcubes G m₀ q := by
  obtain ⟨⟨h1, h2⟩, hl, -⟩ := (mem_cubeIdx G).1 hq
  obtain ⟨b, hb, hz, hsub⟩ := hU q.1 h1 h2 q.2 hl
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN h2
  refine ⟨b, hb, ?_, hsub⟩
  exact cell_subset_cube hdvd (cellSide_pos m₀ m₁ q.1) hb hz

/-- Two aligned points of one aligned cube differ by `a q` with `|q μ| < L`. -/
theorem aligned_diff {a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K) (ha0 : 0 < a)
    {b' b c : CTorus d L N₁ m₁ K} (hb' : Aligned a b') (hb : Aligned a b) (hc : Aligned a c)
    (hbm : b ∈ box b' (L * a)) (hcm : c ∈ box b' (L * a)) :
    ∃ q : Fin d → ℤ, (∀ μ, -(L : ℤ) < q μ ∧ q μ < L) ∧
      b = c + fun μ => (((a : ℤ) * q μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) := by
  obtain ⟨w, hw, hbw⟩ := hbm
  obtain ⟨w0, hw0, hcw⟩ := hcm
  have hwa : ∀ μ, w μ % a = 0 := fun μ => by
    have := mod_of_aligned_add ha hb' (w := w) μ
    rw [← hbw] at this
    rw [← this]; exact hb μ
  have hwa0 : ∀ μ, w0 μ % a = 0 := fun μ => by
    have := mod_of_aligned_add ha hb' (w := w0) μ
    rw [← hcw] at this
    rw [← this]; exact hc μ
  refine ⟨fun μ => ((w μ / a : ℕ) : ℤ) - ((w0 μ / a : ℕ) : ℤ), fun μ => ⟨?_, ?_⟩, ?_⟩
  · have : w0 μ / a < L := by
      rw [Nat.div_lt_iff_lt_mul ha0]; exact hw0 μ
    have h0 : (0 : ℤ) ≤ ((w μ / a : ℕ) : ℤ) := Nat.cast_nonneg _
    have : ((w0 μ / a : ℕ) : ℤ) < L := by exact_mod_cast this
    linarith
  · have : w μ / a < L := by
      rw [Nat.div_lt_iff_lt_mul ha0]; exact hw μ
    have h0 : (0 : ℤ) ≤ ((w0 μ / a : ℕ) : ℤ) := Nat.cast_nonneg _
    have : ((w μ / a : ℕ) : ℤ) < L := by exact_mod_cast this
    linarith
  · funext μ
    have e1 : (w μ : ℕ) = a * (w μ / a) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (hwa μ))).symm
    have e2 : (w0 μ : ℕ) = a * (w0 μ / a) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (hwa0 μ))).symm
    have hb1 : b μ = b' μ + (w μ : ZMod _) := by rw [hbw]; simp [natT]
    have hc1 : c μ = b' μ + (w0 μ : ZMod _) := by rw [hcw]; simp [natT]
    simp only [Pi.add_apply]
    rw [hb1, hc1]
    have gen : ∀ u u0 : ℕ, (((a : ℤ) * ((u : ℤ) - (u0 : ℤ)) : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) =
        ((a * u : ℕ) : ZMod _) - ((a * u0 : ℕ) : ZMod _) := fun u u0 => by push_cast; ring
    rw [gen, ← e1, ← e2]; ring

open Classical in
/-- `D(P)` consists of at most `G₀ = (2L+1)^d` cubes of `π_n`. -/
theorem card_Dbases_le (hN : L ^ m₀ ∣ N₁) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q.1 ≤ K) :
    (Dbases G m₀ q).card ≤ (2 * L + 1) ^ d := by
  set a := cellSide L m₀ m₁ q.1 with ha
  have hdvd : a ∣ (N₁ * L ^ m₁) * L ^ K := cellSide_dvd hN hq
  have ha0 : 0 < a := cellSide_pos m₀ m₁ q.1
  set c0 := cbase a q.2 with hc0
  have hc0al : Aligned a c0 := aligned_cbase _
  let g : (Fin d → ℤ) → CTorus d L N₁ m₁ K := fun r =>
    c0 + fun μ => (((a : ℤ) * r μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ K))
  have hsub : Dbases G m₀ q ⊆ (Fintype.piFinset fun _ : Fin d => Finset.Ioo (-(L : ℤ)) L).image g := by
    intro b hb
    simp only [Dbases, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨hbal, hbD⟩ := hb
    simp only [Dsites, Set.mem_iUnion] at hbD
    obtain ⟨b', hb', hbm⟩ := hbD
    have hc0m : c0 ∈ box b' (L * a) :=
      hb'.2.1 (mem_box_self c0 ha0)
    obtain ⟨r, hr, hbr⟩ := aligned_diff hdvd ha0 hb'.1 hbal hc0al hbm hc0m
    rw [Finset.mem_image]
    refine ⟨r, ?_, hbr.symm⟩
    rw [Fintype.mem_piFinset]
    intro μ
    rw [Finset.mem_Ioo]; exact hr μ
  calc (Dbases G m₀ q).card ≤ _ := Finset.card_le_card hsub
    _ ≤ (Fintype.piFinset fun _ : Fin d => Finset.Ioo (-(L : ℤ)) L).card := Finset.card_image_le
    _ = ∏ _μ : Fin d, (Finset.Ioo (-(L : ℤ)) L).card := Fintype.card_piFinset _
    _ ≤ ∏ _μ : Fin d, (2 * L + 1) := by
        refine Finset.prod_le_prod fun μ _ => ?_
        rw [Int.card_Ioo]; omega
    _ = (2 * L + 1) ^ d := by simp

end Polymer

/-! ### `Y[𝒞]`, (GM1) and connectedness -/

section Cover

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}
variable {ι : Type*} (c : ι → ℕ × CTorus d L N₁ m₁ K)

variable (G m₀) in
/-- `Y[𝒞] = X₁ ∪ ⋃_{P ∈ 𝒞} D(P)` (sites); `c i` is the centre of the parameter cube `P_i`. -/
def Ysites (X₁ : Set (CTorus d L N₁ m₁ K)) (C : Finset ι) : Set (CTorus d L N₁ m₁ K) :=
  X₁ ∪ ⋃ i ∈ C, Dsites G m₀ (c i)

/-- `Y(𝒞)`: the component of `X₁ ∪ ⋃_{P ∈ 𝒞} P` containing `X₁` (with the patches `P_i = Pset (c i)`
and the nearest-neighbour graph of the torus). -/
def compY (X₁ : Set (CTorus d L N₁ m₁ K)) (C : Finset ι) : Set (CTorus d L N₁ m₁ K) :=
  componentOf (latGraph d ((N₁ * L ^ m₁) * L ^ K)) X₁ (patchUnion X₁ (fun i => Pset m₁ (c i)) C)

/-- **(GM1).**  The number of `π_n`-cubes of `Y[𝒞] ∖ X₁` in layer `n` is at most
`G₀ |𝒞_n|`, `G₀ = (2L+1)^d`.  (Cubes of `π_n` are identified with their aligned bases; `X₁b` is the
finite set of bases of the cubes of `X₁`.)  This is the landed `card_layer_biUnion_le` for the
construction `Dbases`. -/
theorem gm1 [DecidableEq ι] (hN : L ^ m₀ ∣ N₁) (hc : ∀ i, c i ∈ cubeIdx G)
    (X₁b : Finset (CTorus d L N₁ m₁ K)) (C : Finset ι) (n : ℕ) :
    (((X₁b ∪ C.biUnion fun i => Dbases G m₀ (c i)) \ X₁b).filter
        (fun b => G.layerIndex b = n)).card ≤
      (2 * L + 1) ^ d * (C.filter (fun i => (c i).1 = n)).card := by
  classical
  refine card_layer_biUnion_le (fun i => Dbases G m₀ (c i)) ((2 * L + 1) ^ d)
    (fun i => card_Dbases_le hN (((mem_cubeIdx G).1 (hc i)).1.2)) G.layerIndex (fun i => (c i).1)
    ?_ X₁b C n
  intro i b hb
  obtain ⟨⟨h1, h2⟩, -, -⟩ := (mem_cubeIdx G).1 (hc i)
  simp only [Dbases, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact G.layerIndex_eq h1 h2 (Dsites_subset_layer (c i) hb.2)

variable {c}

theorem Pset_subset_Dsites (hU : LayerUnion G m₀) (hN : L ^ m₀ ∣ N₁)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) : Pset m₁ q ⊆ Dsites G m₀ q := by
  obtain ⟨b, hb⟩ := exists_Dcubes hU hN hq
  exact (Pset_subset_cellOf m₀ q).trans (cellOf_subset_Dsites hb)

theorem patchUnion_subset_Ysites (hU : LayerUnion G m₀) (hN : L ^ m₀ ∣ N₁)
    (hc : ∀ i, c i ∈ cubeIdx G) (X₁ : Set (CTorus d L N₁ m₁ K)) (C : Finset ι) :
    patchUnion X₁ (fun i => Pset m₁ (c i)) C ⊆ Ysites G m₀ c X₁ C := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hx⟩ := hx
    refine Or.inr ?_
    simp only [Set.mem_iUnion]
    exact ⟨i, hi, Pset_subset_Dsites hU hN (hc i) hx⟩

omit [NeZero N₁] [NeZero L] in
/-- `X₁ ⊆ Y(𝒞) ⊆ Y[𝒞]`. -/
theorem subset_compY (X₁ : Set (CTorus d L N₁ m₁ K)) (C : Finset ι) :
    X₁ ⊆ compY c X₁ C := subset_componentOf _ _ _

theorem compY_subset_Ysites (hU : LayerUnion G m₀) (hN : L ^ m₀ ∣ N₁)
    (hc : ∀ i, c i ∈ cubeIdx G) (X₁ : Set (CTorus d L N₁ m₁ K)) (C : Finset ι) :
    compY c X₁ C ⊆ Ysites G m₀ c X₁ C :=
  (componentOf_subset _ (fun _ hx => Or.inl hx)).trans (patchUnion_subset_Ysites hU hN hc X₁ C)

theorem subset_Ysites (X₁ : Set (CTorus d L N₁ m₁ K)) (C : Finset ι) :
    X₁ ⊆ Ysites G m₀ c X₁ C := fun _ hx => Or.inl hx

/-- Two points of a box contained in a region `R` are joined inside `R`. -/
theorem chain_in_box {n : ℕ} (b : Torus d n) (s : ℕ) (R : Set (Torus d n)) (hR : box b s ⊆ R)
    {x y : Torus d n} (hx : x ∈ box b s) (hy : y ∈ box b s) :
    Relation.ReflTransGen (fun x y => (latGraph d n).Adj x y ∧ x ∈ R ∧ y ∈ R) x y := by
  have hsymm : ∀ x y, (latGraph d n).Adj x y ∧ x ∈ R ∧ y ∈ R → (latGraph d n).Adj y x ∧ y ∈ R ∧ x ∈ R :=
    fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  obtain ⟨w, hw, rfl⟩ := hx
  obtain ⟨w', hw', rfl⟩ := hy
  have h1 := reach_box b w R (fun v hv => hR ⟨v, fun μ => lt_of_le_of_lt (hv μ) (hw μ), rfl⟩)
  have h2 := reach_box b w' R (fun v hv => hR ⟨v, fun μ => lt_of_le_of_lt (hv μ) (hw' μ), rfl⟩)
  exact (rtg_symm hsymm h1).trans h2

/-- **Connectedness of `Y[𝒞]`.**  For a connected family, every point of `Y[𝒞]` is joined to `X₁`
inside `Y[𝒞]`: `Y[𝒞]` is the component of itself containing `X₁`.  Together with
`subset_compY`, `compY_subset_Ysites` this gives `Y[𝒞] ⊇ Y(𝒞) ⊇ X₁`. -/
theorem componentOf_Ysites (hU : LayerUnion G m₀) (hN : L ^ m₀ ∣ N₁) (hc : ∀ i, c i ∈ cubeIdx G)
    (X₁ : Set (CTorus d L N₁ m₁ K)) {C : Finset ι}
    (hconn : IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c X₁) C) :
    componentOf (latGraph d ((N₁ * L ^ m₁) * L ^ K)) X₁ (Ysites G m₀ c X₁ C) =
      Ysites G m₀ c X₁ C := by
  apply Set.Subset.antisymm (componentOf_subset _ (subset_Ysites (G := G) (m₀ := m₀) (c := c) X₁ C))
  intro z hz
  rcases hz with hz | hz
  · exact subset_componentOf _ _ _ hz
  · simp only [Set.mem_iUnion] at hz
    obtain ⟨i, hi, hz⟩ := hz
    obtain ⟨b', hb', hzb⟩ := by simpa only [Dsites, Set.mem_iUnion] using hz
    set R := Ysites G m₀ c X₁ C with hR
    have hbox : box b' (L * cellSide L m₀ m₁ (c i).1) ⊆ R := by
      intro x hx
      refine Or.inr ?_
      simp only [Set.mem_iUnion]
      exact ⟨i, hi, by simp only [Dsites, Set.mem_iUnion]; exact ⟨b', hb', hx⟩⟩
    have hq : (c i).2 ∈ box b' (L * cellSide L m₀ m₁ (c i).1) :=
      hb'.2.1 (Pset_subset_cellOf m₀ (c i) (self_mem_Pset (c i)))
    have hch := chain_in_box b' _ R hbox hq hzb
    have hq2 : (c i).2 ∈ compY c X₁ C := hconn i hi (self_mem_Pset (c i))
    obtain ⟨y, hy, hyq⟩ : ∃ y ∈ X₁, Relation.ReflTransGen (fun a b =>
      (latGraph d ((N₁ * L ^ m₁) * L ^ K)).Adj a b ∧ a ∈ patchUnion X₁ (fun i => Pset m₁ (c i)) C ∧
        b ∈ patchUnion X₁ (fun i => Pset m₁ (c i)) C) y (c i).2 := hq2
    refine ⟨y, hy, ?_⟩
    refine Relation.ReflTransGen.trans ?_ hch
    refine Relation.ReflTransGen.mono (fun a b hab => ⟨hab.1, ?_, ?_⟩) y _ hyq
    · exact patchUnion_subset_Ysites hU hN hc X₁ C hab.2.1
    · exact patchUnion_subset_Ysites hU hN hc X₁ C hab.2.2

/-- `Y[𝒞]` is connected when `X₁` is. -/
theorem Ysites_preconnected (hU : LayerUnion G m₀) (hN : L ^ m₀ ∣ N₁) (hc : ∀ i, c i ∈ cubeIdx G)
    (X₁ : Set (CTorus d L N₁ m₁ K)) {C : Finset ι}
    (hconn : IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c X₁) C)
    (hX : ∀ x ∈ X₁, ∀ y ∈ X₁, Relation.ReflTransGen
      (fun a b => (latGraph d ((N₁ * L ^ m₁) * L ^ K)).Adj a b ∧ a ∈ X₁ ∧ b ∈ X₁) x y) :
    ∀ x ∈ Ysites G m₀ c X₁ C, ∀ y ∈ Ysites G m₀ c X₁ C, Relation.ReflTransGen
      (fun a b => (latGraph d ((N₁ * L ^ m₁) * L ^ K)).Adj a b ∧ a ∈ Ysites G m₀ c X₁ C ∧
        b ∈ Ysites G m₀ c X₁ C) x y := by
  intro x hx y hy
  have e := componentOf_Ysites hU hN hc X₁ hconn
  rw [← e] at hx hy
  obtain ⟨x0, hx0, hx0x⟩ := hx
  obtain ⟨y0, hy0, hy0y⟩ := hy
  have hsymm : ∀ a b, ((latGraph d ((N₁ * L ^ m₁) * L ^ K)).Adj a b ∧
      a ∈ Ysites G m₀ c X₁ C ∧ b ∈ Ysites G m₀ c X₁ C) → ((latGraph d ((N₁ * L ^ m₁) * L ^ K)).Adj b a ∧
      b ∈ Ysites G m₀ c X₁ C ∧ a ∈ Ysites G m₀ c X₁ C) := fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  have h1 := rtg_symm hsymm hx0x
  have h2 : Relation.ReflTransGen
      (fun a b => (latGraph d ((N₁ * L ^ m₁) * L ^ K)).Adj a b ∧ a ∈ Ysites G m₀ c X₁ C ∧
        b ∈ Ysites G m₀ c X₁ C) x0 y0 :=
    Relation.ReflTransGen.mono (fun a b hab => ⟨hab.1, Or.inl hab.2.1, Or.inl hab.2.2⟩) x0 y0
      (hX x0 hx0 y0 hy0)
  exact (h1.trans h2).trans hy0y

end Cover

end Balaban.Localization
