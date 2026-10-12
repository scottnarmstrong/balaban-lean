/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2FpGeometry
public import Balaban.Localization.PolymerGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The local block bound at a charged parameter cube (VMOD-7 §2, (2.1)–(2.3))

Cyclic nearness `CycLt R x y` (a representative of the coordinate difference of absolute value
`< R` in every coordinate), nearest-neighbour walks `NNWalk`, and the cell index `cellIdx b` of a
torus with the cyclic Moore neighbourhood `moore b p` (at most `3 ^ d` cells).

* `cycLt_footprint_param` (2.1): the footprint of a centre incident to the parameter cube `P` is
  within cyclic distance `(L + 13/2) L^(m + m₁)` of every site of `P`.  Its premises are exactly the
  cited inclusions: the footprint lies in `hatBox z` (VMOD-4 (4.3)), the scale `n` of `P ∈ 𝒬(z)`
  satisfies `n ≤ m + 1` (VMOD-2 (1.9)), and `M₁ = L ^ m₁ ≥ 4 L ^ 2`.  **These two inclusions are
  not landed as Lean theorems; they are hypotheses of this internal lemma.**
* `cellIdx_mem_moore` (2.2): all those footprint sites lie in the Moore neighbourhood of the cell
  of a site of `P`.
* `star_bound` (2.3): one footprint witness in each occupied cell is joined to a site of `P` by a
  nearest-neighbour walk of length `≤ d · b_K`, so the star costs at most `d · 3 ^ d · b_K`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Finset

section Cyc

variable {d n : ℕ}

/-- Cyclic nearness: in every coordinate some representative of the difference has absolute
value `< R`. -/
def CycLt (R : ℝ) (x y : Torus d n) : Prop :=
  ∀ μ, ∃ k : ℤ, |((x μ).val : ℝ) + k * (n : ℝ) - ((y μ).val : ℝ)| < R

theorem CycLt.mono {R R' : ℝ} {x y : Torus d n} (h : CycLt R x y) (hR : R ≤ R') : CycLt R' x y :=
  fun μ => (h μ).imp fun _ hk => lt_of_lt_of_le hk hR

theorem CycLt.symm {R : ℝ} {x y : Torus d n} (h : CycLt R x y) : CycLt R y x := fun μ => by
  obtain ⟨k, hk⟩ := h μ
  refine ⟨-k, ?_⟩
  rw [← abs_neg]
  convert hk using 2
  push_cast
  ring

theorem CycLt.trans {R R' : ℝ} {x y z : Torus d n} (h : CycLt R x y) (h' : CycLt R' y z) :
    CycLt (R + R') x z := fun μ => by
  obtain ⟨k, hk⟩ := h μ
  obtain ⟨k', hk'⟩ := h' μ
  refine ⟨k + k', ?_⟩
  have h1 := abs_sub_lt_iff.1 hk
  have h2 := abs_sub_lt_iff.1 hk'
  rw [abs_sub_lt_iff]
  push_cast
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem cycLt_of_sameCell {a : ℕ} (ha : 0 < a) {x y : Torus d n} (h : SameCell a x y) :
    CycLt (a : ℝ) x y := fun μ => by
  refine ⟨0, ?_⟩
  have hx := Nat.div_add_mod (x μ).val a
  have hy := Nat.div_add_mod (y μ).val a
  have hxm := Nat.mod_lt (x μ).val ha
  have hym := Nat.mod_lt (y μ).val ha
  rw [h μ] at hx
  have e : ((x μ).val : ℤ) - (y μ).val = ((x μ).val % a : ℕ) - ((y μ).val % a : ℕ) := by
    omega
  have e' : ((x μ).val : ℝ) - (y μ).val = (((x μ).val % a : ℕ) : ℝ) - (((y μ).val % a : ℕ) : ℝ) := by
    exact_mod_cast e
  have hxm' : (((x μ).val % a : ℕ) : ℝ) < a := by exact_mod_cast hxm
  have hym' : (((y μ).val % a : ℕ) : ℝ) < a := by exact_mod_cast hym
  have h0x : (0 : ℝ) ≤ (((x μ).val % a : ℕ) : ℝ) := Nat.cast_nonneg _
  have h0y : (0 : ℝ) ≤ (((y μ).val % a : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_lt]
  push_cast
  constructor <;> linarith

end Cyc

section Moore

variable {d n : ℕ}

/-- The cell index of a site for cells of side `b` (coordinates modulo the number `n / b` of
cells). -/
def cellIdx (b : ℕ) (x : Torus d n) : Fin d → ZMod (n / b) :=
  fun μ => (((x μ).val / b : ℕ) : ZMod (n / b))

/-- The cyclic Moore neighbourhood of the cell of `p`: at most `3 ^ d` cells. -/
def moore (b : ℕ) (p : Torus d n) : Finset (Fin d → ZMod (n / b)) :=
  open Classical in
  (Finset.univ : Finset (Fin d → Fin 3)).image
    (fun δ => fun μ => cellIdx b p μ + (((δ μ : Fin 3) : ℕ) : ZMod (n / b)) - 1)

theorem card_moore_le (b : ℕ) (p : Torus d n) : (moore b p).card ≤ 3 ^ d := by
  classical
  unfold moore
  refine (Finset.card_image_le).trans ?_
  simp

/-- One coordinate of the Moore bound. -/
theorem coord_moore {b c xv pv : ℕ} (hb : 0 < b) (k : ℤ)
    (h : |(xv : ℤ) + k * ((b * c : ℕ) : ℤ) - pv| < b) :
    ∃ δ : Fin 3, ((xv / b : ℕ) : ZMod c) = ((pv / b : ℕ) : ZMod c) + (((δ : Fin 3) : ℕ) : ZMod c) - 1 := by
  have hx := Nat.div_add_mod xv b
  have hp := Nat.div_add_mod pv b
  have hxm := Nat.mod_lt xv hb
  have hpm := Nat.mod_lt pv hb
  set s := xv / b with hs
  set q := pv / b with hq
  set r' := xv % b
  set r := pv % b
  set j : ℤ := (s : ℤ) - q + k * c with hj
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have habs := abs_lt.1 h
  have heq : (b : ℤ) * j = ((xv : ℤ) + k * ((b * c : ℕ) : ℤ) - pv) + r - r' := by
    have hx' : (xv : ℤ) = b * s + r' := by exact_mod_cast hx.symm
    have hp' : (pv : ℤ) = b * q + r := by exact_mod_cast hp.symm
    rw [hj]; push_cast; rw [hx', hp']; ring
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hr0' : (0 : ℤ) ≤ r' := by positivity
  have hrb : (r : ℤ) < b := by exact_mod_cast hpm
  have hrb' : (r' : ℤ) < b := by exact_mod_cast hxm
  have hj1 : -2 < j := by
    by_contra hcon
    replace hcon := not_lt.1 hcon
    nlinarith
  have hj2 : j < 2 := by
    by_contra hcon
    replace hcon := not_lt.1 hcon
    nlinarith
  refine ⟨⟨(j + 1).toNat, by omega⟩, ?_⟩
  have hcast : (((j + 1).toNat : ℕ) : ZMod c) = ((j + 1 : ℤ) : ZMod c) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  have e1 : ((s : ℤ) : ZMod c) = ((q : ℤ) : ZMod c) + (j : ZMod c) - (k : ZMod c) * (c : ZMod c) := by
    have : (s : ℤ) = q + j - k * c := by rw [hj]; ring
    rw [this]; push_cast; ring
  simp only [ZMod.natCast_self, mul_zero, sub_zero] at e1
  show ((s : ℕ) : ZMod c) = _
  rw [hcast]
  have : ((s : ℕ) : ZMod c) = ((s : ℤ) : ZMod c) := by simp
  rw [this, e1]
  push_cast
  ring

/-- **(2.2), cells**: a site cyclically within `b` of `p` lies in the Moore neighbourhood of the cell
of `p`. -/
theorem cellIdx_mem_moore [NeZero n] {b : ℕ} (hb : 0 < b) (hbn : b ∣ n) {x p : Torus d n}
    (h : CycLt (b : ℝ) x p) : cellIdx b x ∈ moore b p := by
  classical
  obtain ⟨c, hc⟩ := hbn
  have hcc : n / b = c := by rw [hc]; exact Nat.mul_div_cancel_left c hb
  unfold moore
  rw [Finset.mem_image]
  have hco : ∀ μ, ∃ δ : Fin 3, cellIdx b x μ = cellIdx b p μ + (((δ : Fin 3) : ℕ) : ZMod (n / b)) - 1 := by
    intro μ
    obtain ⟨k, hk⟩ := h μ
    have hk' : |((x μ).val : ℤ) + k * ((b * c : ℕ) : ℤ) - (p μ).val| < b := by
      have : |(((((x μ).val : ℤ) + k * ((b * c : ℕ) : ℤ) - (p μ).val : ℤ)) : ℝ)| < (b : ℝ) := by
        have hn : (((b * c : ℕ) : ℤ) : ℝ) = (n : ℝ) := by rw [← hc]; push_cast; rfl
        push_cast at hk hn ⊢
        rw [hn]
        exact hk
      rw [← Int.cast_abs] at this
      exact_mod_cast this
    have key := coord_moore (c := c) hb k hk'
    obtain ⟨δ, hδ⟩ := key
    refine ⟨δ, ?_⟩
    unfold cellIdx
    revert hδ
    rw [hcc]
    exact id
  choose δ hδ using hco
  exact ⟨δ, Finset.mem_univ _, funext fun μ => (hδ μ).symm⟩

end Moore

section Walk

variable {d n : ℕ}

/-- Nearest-neighbour adjacency on `Torus d n` (the relation `Adj` of `PathMetric`). -/
def NNAdj (x y : Torus d n) : Prop :=
  ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ x = y + Pi.single μ 1

/-- `NNWalk x y ℓ`: a nearest-neighbour walk from `x` to `y` of `ℓ` fine bonds. -/
inductive NNWalk : Torus d n → Torus d n → ℕ → Prop
  | refl (x : Torus d n) : NNWalk x x 0
  | step {x y z : Torus d n} {ℓ : ℕ} : NNAdj x y → NNWalk y z ℓ → NNWalk x z (ℓ + 1)

/-- Coordinate geodesics: a walk from `x` to `x + e` of length `∑ |e μ|`. -/
theorem nnWalk_shift : ∀ (N : ℕ) (x : Torus d n) (e : Fin d → ℤ), ∑ μ, (e μ).natAbs = N →
    NNWalk x (x + fun μ => ((e μ : ℤ) : ZMod n)) N := by
  intro N
  induction N with
  | zero =>
    intro x e he
    have : ∀ μ, e μ = 0 := fun μ => by
      have := (Finset.sum_eq_zero_iff.1 he) μ (Finset.mem_univ _)
      omega
    have h0 : (fun μ => ((e μ : ℤ) : ZMod n)) = 0 := funext fun μ => by simp [this μ]
    rw [h0, add_zero]
    exact NNWalk.refl x
  | succ N ih =>
    intro x e he
    have : ∃ μ, e μ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      simp [hcon] at he
    obtain ⟨μ, hμ⟩ := this
    obtain ⟨s, hs, hs'⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (e μ - s).natAbs + 1 = (e μ).natAbs := by
      rcases lt_or_gt_of_ne hμ with h | h
      · exact ⟨-1, Or.inr rfl, by omega⟩
      · exact ⟨1, Or.inl rfl, by omega⟩
    set e' := Function.update e μ (e μ - s) with he'
    have hsum : ∑ ν, (e' ν).natAbs = N := by
      have h1 := Finset.sum_update_of_mem (s := Finset.univ) (Finset.mem_univ μ)
        (fun ν => (e ν).natAbs) 0
      have h2 := Finset.add_sum_erase (Finset.univ : Finset (Fin d)) (fun ν => (e ν).natAbs)
        (Finset.mem_univ μ)
      have h3 : ∑ ν, (e' ν).natAbs = (e μ - s).natAbs + ∑ ν ∈ Finset.univ.erase μ, (e ν).natAbs := by
        rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin d)) (fun ν => (e' ν).natAbs)
          (Finset.mem_univ μ)]
        congr 1
        · simp [he']
        · refine Finset.sum_congr rfl fun ν hν => ?_
          simp [he', Function.update_of_ne (Finset.ne_of_mem_erase hν)]
      omega
    have hstep : NNAdj x (x + Pi.single μ (s : ZMod n)) := by
      refine ⟨μ, ?_⟩
      rcases hs with rfl | rfl
      · left; simp
      · right
        funext ν
        by_cases hν : ν = μ
        · subst hν; simp
        · simp [hν]
    have hrest := ih (x + Pi.single μ (s : ZMod n)) e' hsum
    have heq : x + Pi.single μ (s : ZMod n) + (fun ν => ((e' ν : ℤ) : ZMod n)) =
        x + fun ν => ((e ν : ℤ) : ZMod n) := by
      funext ν
      by_cases hν : ν = μ
      · subst hν; simp [he']
      · simp [hν, he']
    rw [heq] at hrest
    exact NNWalk.step hstep hrest

/-- A site cyclically within `b` of `p` is joined to `p` by a walk of length `≤ d b`. -/
theorem exists_nnWalk_of_cycLt [NeZero n] {b : ℕ} {x p : Torus d n} (h : CycLt (b : ℝ) x p) :
    ∃ ℓ, ℓ ≤ d * b ∧ NNWalk p x ℓ := by
  choose k hk using h
  set e : Fin d → ℤ := fun μ => ((x μ).val : ℤ) + k μ * (n : ℤ) - (p μ).val with he
  have hle : ∀ μ, (e μ).natAbs ≤ b := fun μ => by
    have h1 : |((e μ : ℤ) : ℝ)| < b := by
      simpa [he] using hk μ
    have h2 : ((e μ).natAbs : ℝ) < b := by
      rw [Nat.cast_natAbs, Int.cast_abs]; exact h1
    exact_mod_cast h2.le
  have hw := nnWalk_shift _ p e rfl
  have hx : p + (fun μ => ((e μ : ℤ) : ZMod n)) = x := by
    funext μ
    simp [he]
  rw [hx] at hw
  refine ⟨_, ?_, hw⟩
  calc ∑ μ, (e μ).natAbs ≤ ∑ _μ : Fin d, b := Finset.sum_le_sum fun μ _ => hle μ
    _ = d * b := by simp

end Walk

section Footprint

open Balaban.Localization.Dec2 Balaban.Background

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

omit [NeZero N₁] [NeZero L] in
theorem inBox_cycLt {j : ℕ} {y0 x y : CTorus d L N₁ m₁ K} {R : ℝ} (hx : InBox m₁ j y0 R x)
    (hy : InBox m₁ j y0 R y) : CycLt (R + R) x y := fun μ => by
  obtain ⟨p, hp⟩ := hx μ
  obtain ⟨q, hq⟩ := hy μ
  refine ⟨p - q, ?_⟩
  have h1 := abs_lt.1 hp
  have h2 := abs_lt.1 hq
  have e : ((x μ).val : ℝ) + ((p - q : ℤ) : ℝ) * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) - ((y μ).val : ℝ) =
      (((x μ).val : ℝ) + p * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
        ((y0 μ).val + ((L : ℝ) ^ (j + m₁) - 1) / 2)) -
      (((y μ).val : ℝ) + q * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
        ((y0 μ).val + ((L : ℝ) ^ (j + m₁) - 1) / 2)) := by
    push_cast; ring
  show |((x μ).val : ℝ) + ((p - q : ℤ) : ℝ) * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) - ((y μ).val : ℝ)| < R + R
  rw [e, abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **(2.1)** Every site of the footprint of a centre `z` and every site of a parameter cube
`P ∈ 𝒬(z)` are cyclically within `(L + 13/2) L^(m + m₁)` (`m` the scale of `z`).  The premises
`hfoot` (footprint in `hatBox z`: VMOD-4 (4.3)), `hPn` (scale comparison `n ≤ m + 1`: VMOD-2
(1.9)) and `hM₁` (`M₁ = L^m₁ ≥ 4 L²`) are the cited inclusions; they are hypotheses of this internal
lemma. -/
theorem cycLt_footprint_param {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {a : ℕ → ℝ} {ν : ℝ} {z P : ℕ × CTorus d L N₁ m₁ K}
    (hfoot : ∀ t ∈ footprint H a ν z, t ∈ hatBox z) (hP : P ∈ C.Qset z)
    (hPn : P.1 ≤ z.1 + 1) (hM₁ : 4 * L ^ 2 ≤ L ^ m₁)
    {t p : CTorus d L N₁ m₁ K} (ht : t ∈ footprint H a ν z) (hp : p ∈ cubeP P) :
    CycLt (((L : ℝ) + 13 / 2) * (L : ℝ) ^ (z.1 + m₁)) t p := by
  obtain ⟨-, y, hySC, hyB⟩ := C.mem_Qset.1 hP
  have htB : InBox m₁ z.1 z.2 (hatRad L m₁ z.1) t := mem_boxSet.1 (hfoot t ht)
  have h1 := inBox_cycLt htB hyB
  have hSC : SameCell (L ^ (P.1 + m₁)) y p := fun μ => (hySC μ).trans ((mem_cubeP.1 hp) μ).symm
  have hpos : 0 < L ^ (P.1 + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have h2 := cycLt_of_sameCell hpos hSC
  refine (h1.trans h2).mono ?_
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hM : (4 : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ m₁ := by exact_mod_cast hM₁
  have hpow : (L : ℝ) ^ (P.1 + m₁) ≤ (L : ℝ) * (L : ℝ) ^ (z.1 + m₁) := by
    calc (L : ℝ) ^ (P.1 + m₁) ≤ (L : ℝ) ^ (z.1 + 1 + m₁) :=
          pow_le_pow_right₀ hL1 (by omega)
      _ = (L : ℝ) * (L : ℝ) ^ (z.1 + m₁) := by ring
  have hLm : (0 : ℝ) ≤ (L : ℝ) ^ z.1 := by positivity
  have hsq : (L : ℝ) ^ 2 * (L : ℝ) ^ z.1 * 4 ≤ (L : ℝ) ^ (z.1 + m₁) := by
    rw [pow_add]
    nlinarith [mul_le_mul_of_nonneg_right hM hLm]
  have hrad : hatRad L m₁ z.1 + hatRad L m₁ z.1 ≤ 13 / 2 * (L : ℝ) ^ (z.1 + m₁) := by
    unfold hatRad
    nlinarith
  push_cast
  nlinarith

end Footprint

section Star

variable {d n : ℕ}

/-- **(2.3), generic form**: if every site of `F` is cyclically within `b` of `p`, one witness in
each occupied cell of the Moore neighbourhood is joined to `p` by a walk of at most `d b` bonds;
at most `3 ^ d` cells are occupied, so the total length is `≤ d 3 ^ d b`. -/
theorem star_bound_generic [NeZero n] {b : ℕ} (hb : 0 < b) (hbn : b ∣ n) (p : Torus d n)
    (F : Set (Torus d n)) (hF : ∀ t ∈ F, CycLt (b : ℝ) t p) :
    ∃ (O : Finset (Fin d → ZMod (n / b))) (w : (Fin d → ZMod (n / b)) → Torus d n)
      (ℓ : (Fin d → ZMod (n / b)) → ℕ),
      O.card ≤ 3 ^ d ∧ (∀ t ∈ F, cellIdx b t ∈ O) ∧
      (∀ c ∈ O, w c ∈ F ∧ cellIdx b (w c) = c ∧ ℓ c ≤ d * b ∧ NNWalk p (w c) (ℓ c)) ∧
      ∑ c ∈ O, ℓ c ≤ d * 3 ^ d * b := by
  classical
  set O := (moore b p).filter (fun c => ∃ t ∈ F, cellIdx b t = c) with hO
  have hex : ∀ c : Fin d → ZMod (n / b), ∃ (w : Torus d n) (ℓ : ℕ),
      c ∈ O → (w ∈ F ∧ cellIdx b w = c ∧ ℓ ≤ d * b ∧ NNWalk p w ℓ) := by
    intro c
    by_cases hc : c ∈ O
    · obtain ⟨t, htF, htc⟩ := (Finset.mem_filter.1 hc).2
      obtain ⟨ℓ, hℓ, hw⟩ := exists_nnWalk_of_cycLt (hF t htF)
      exact ⟨t, ℓ, fun _ => ⟨htF, htc, hℓ, hw⟩⟩
    · exact ⟨p, 0, fun h => absurd h hc⟩
  choose w ℓ hwℓ using hex
  refine ⟨O, w, ℓ, ?_, ?_, fun c hc => hwℓ c hc, ?_⟩
  · exact (Finset.card_filter_le _ _).trans (card_moore_le b p)
  · intro t ht
    exact Finset.mem_filter.2 ⟨cellIdx_mem_moore hb hbn (hF t ht), t, ht, rfl⟩
  · calc ∑ c ∈ O, ℓ c ≤ O.card • (d * b) :=
          Finset.sum_le_card_nsmul _ _ _ fun c hc => (hwℓ c hc).2.2.1
      _ ≤ 3 ^ d * (d * b) := by
          rw [smul_eq_mul]
          exact Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans (card_moore_le b p))
      _ = d * 3 ^ d * b := by ring

end Star

section Block

open Balaban.Localization.Dec2 Balaban.Background

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ)
  (X₁ : Finset (CTorus d L N₁ m₁ K)) (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K))

/-- A centre `z` is incident to the charged parameter cube `P` in the incidence graph. -/
def Incident (z P : ℕ × CTorus d L N₁ m₁ K) : Prop :=
  EligC C X₁ 𝒞 z ∧ LiveI H z ∧ P ∈ C.Qset z ∧ P ∈ 𝒞

/-- `Incident` is adjacency of the centre vertex and the parameter vertex in `incGraph`. -/
theorem incGraph_adj_iff (z P : ℕ × CTorus d L N₁ m₁ K) :
    (incGraph C H a ν X₁ 𝒞).Adj (Sum.inr (Sum.inl z)) (Sum.inr (Sum.inr P)) ↔
      Incident C H X₁ 𝒞 z P := by
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact absurd h (by simp [incRel])
  · intro h
    exact ⟨by simp, Or.inl h⟩

/-- All footprint sites of all centres incident to `P`. -/
def incidentFootprint (P : ℕ × CTorus d L N₁ m₁ K) : Set (CTorus d L N₁ m₁ K) :=
  {t | ∃ z, Incident C H X₁ 𝒞 z P ∧ t ∈ footprint H a ν z}

variable {C H a ν X₁ 𝒞}

/-- **(2.1)+(2.2) cyclic closeness at the scale `b_K = M L^K`.**  Premises as in
`cycLt_footprint_param`, plus `m ≤ K` for the centres and `L^m₀ ≥ L + 9`. -/
theorem cycLt_incidentFootprint {m₀ : ℕ} (hfoot : ∀ z ∈ C.cubeIdx, ∀ t ∈ footprint H a ν z,
      t ∈ hatBox z)
    (hscale : ∀ z ∈ C.cubeIdx, z.1 ≤ K) (hnear : ∀ z ∈ C.cubeIdx, ∀ P ∈ C.Qset z, P.1 ≤ z.1 + 1)
    (hM₁ : 4 * L ^ 2 ≤ L ^ m₁) (hm₀ : L + 9 ≤ L ^ m₀) {P : ℕ × CTorus d L N₁ m₁ K}
    {t p : CTorus d L N₁ m₁ K} (ht : t ∈ incidentFootprint C H a ν X₁ 𝒞 P) (hp : p ∈ cubeP P) :
    CycLt ((cellSide L m₀ m₁ K : ℕ) : ℝ) t p := by
  obtain ⟨z, ⟨hE, -, hPz, -⟩, htz⟩ := ht
  have hz : z ∈ C.cubeIdx := hE.1
  have h1 := cycLt_footprint_param (C := C) (hfoot z hz) hPz (hnear z hz P hPz) hM₁ htz hp
  refine h1.mono ?_
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hm : (L : ℝ) + 9 ≤ (L : ℝ) ^ m₀ := by exact_mod_cast hm₀
  have hpow : (L : ℝ) ^ (z.1 + m₁) ≤ (L : ℝ) ^ (K + m₁) :=
    pow_le_pow_right₀ hL1 (by have := hscale z hz; omega)
  have hpos : (0 : ℝ) < (L : ℝ) ^ (K + m₁) := by positivity
  have hcs : ((cellSide L m₀ m₁ K : ℕ) : ℝ) = (L : ℝ) ^ m₀ * (L : ℝ) ^ (K + m₁) := by
    unfold cellSide
    push_cast
    rw [← pow_add]
    congr 1
    ring
  rw [hcs]
  have h2 : ((L : ℝ) + 13 / 2) * (L : ℝ) ^ (z.1 + m₁) ≤ ((L : ℝ) + 13 / 2) * (L : ℝ) ^ (K + m₁) :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  nlinarith

/-- **(2.2) The local block bound.**  Every footprint site of every centre incident to the charged
parameter cube `P` lies in the cyclic Moore neighbourhood (at most `3 ^ d` cells) of the `π_K` cell of
any site `p ∈ P`. -/
theorem cellIdx_incidentFootprint_mem_moore {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
    (hfoot : ∀ z ∈ C.cubeIdx, ∀ t ∈ footprint H a ν z, t ∈ hatBox z)
    (hscale : ∀ z ∈ C.cubeIdx, z.1 ≤ K) (hnear : ∀ z ∈ C.cubeIdx, ∀ P ∈ C.Qset z, P.1 ≤ z.1 + 1)
    (hM₁ : 4 * L ^ 2 ≤ L ^ m₁) (hm₀ : L + 9 ≤ L ^ m₀) {P : ℕ × CTorus d L N₁ m₁ K}
    {t p : CTorus d L N₁ m₁ K} (ht : t ∈ incidentFootprint C H a ν X₁ 𝒞 P) (hp : p ∈ cubeP P) :
    cellIdx (cellSide L m₀ m₁ K) t ∈ moore (cellSide L m₀ m₁ K) p :=
  cellIdx_mem_moore (cellSide_pos m₀ m₁ K) (cellSide_dvd hN le_rfl)
    (cycLt_incidentFootprint hfoot hscale hnear hM₁ hm₀ ht hp)

/-- **(2.3) The ambient star bound per charge.**  For a charged parameter cube `P` and `p ∈ P`:
there are at most `3 ^ d` occupied `π_K` cells; each contains a footprint witness joined to `p` by a
nearest-neighbour walk of at most `d b_K` fine bonds (`b_K = M L^K = cellSide L m₀ m₁ K`), so the star
costs at most `d 3 ^ d b_K` bonds, i.e. `d 3 ^ d` after normalization by `b_K`. -/
theorem star_bound {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
    (hfoot : ∀ z ∈ C.cubeIdx, ∀ t ∈ footprint H a ν z, t ∈ hatBox z)
    (hscale : ∀ z ∈ C.cubeIdx, z.1 ≤ K) (hnear : ∀ z ∈ C.cubeIdx, ∀ P ∈ C.Qset z, P.1 ≤ z.1 + 1)
    (hM₁ : 4 * L ^ 2 ≤ L ^ m₁) (hm₀ : L + 9 ≤ L ^ m₀) {P : ℕ × CTorus d L N₁ m₁ K}
    {p : CTorus d L N₁ m₁ K} (hp : p ∈ cubeP P) :
    ∃ (O : Finset (Fin d → ZMod ((N₁ * L ^ m₁ * L ^ K) / cellSide L m₀ m₁ K)))
      (w : (Fin d → ZMod ((N₁ * L ^ m₁ * L ^ K) / cellSide L m₀ m₁ K)) → CTorus d L N₁ m₁ K)
      (ℓ : (Fin d → ZMod ((N₁ * L ^ m₁ * L ^ K) / cellSide L m₀ m₁ K)) → ℕ),
      O.card ≤ 3 ^ d ∧
      (∀ t ∈ incidentFootprint C H a ν X₁ 𝒞 P, cellIdx (cellSide L m₀ m₁ K) t ∈ O) ∧
      (∀ c ∈ O, w c ∈ incidentFootprint C H a ν X₁ 𝒞 P ∧ cellIdx (cellSide L m₀ m₁ K) (w c) = c ∧
        ℓ c ≤ d * cellSide L m₀ m₁ K ∧ NNWalk p (w c) (ℓ c)) ∧
      ∑ c ∈ O, ℓ c ≤ d * 3 ^ d * cellSide L m₀ m₁ K :=
  star_bound_generic (cellSide_pos m₀ m₁ K) (cellSide_dvd hN le_rfl) p _
    fun _ ht => cycLt_incidentFootprint hfoot hscale hnear hM₁ hm₀ ht hp

omit [NeZero N₁] [NeZero L] in
/-- `NNAdj` is the adjacency `Adj` of the path metric on the cube torus. -/
theorem nnAdj_iff_adj (x y : CTorus d L N₁ m₁ K) : NNAdj x y ↔ Adj x y := Iff.rfl

end Block

end Balaban.Localization
