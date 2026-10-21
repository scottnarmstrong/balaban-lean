/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseBgLocalityAlg
public import Balaban.Fluctuation.DetCauchyActivity
public import Balaban.Fluctuation.LocalSetDetCrossGeom
public import Balaban.Fluctuation.HoleStepGeom
import Mathlib.Tactic.Linarith

/-!
# The hull of a rooted family of cells (size of the labels of the chart activities)

A rooted family `Cs` of cells of the decoupling cover (`IsRootedFamily (cellPatch C D) S Cs`, the
cells joined to the seed set `S` by chains of cells with overlapping patches) is covered by balls:
a cell is within `9 L^{k+1+m₁}` of the patches of the centres whose footprint contains it
(`supDist_boxNbhd_le`).  The cells of side `L^{k+1+m₁}` that meet these balls and the ball about the
seed form a set of patches `labelJ`, with at most `(2ρs / L^{k+1+m₁} + 2)^d + 20^d |Cs|` elements
(`card_labelJ_le`: the number of cells that meet a ball of radius `R` is at most `(2R/s + 2)^d`,
`card_ballCells_le`).  The union of the balls is nearest-neighbour connected through the root
(`supBall_chain`, `rootConnected_of_siteChains`), so the patches are connected to the root cube
(`rootConnected_labelJ`) and the hull of the root cube and the patches is a polymer of size at most
`2 d L` times the number of patches that contains the seed ball (`labelHull_spec`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Localization Balaban.LargeField Balaban.Fluctuation Balaban.SmallField.Def6 Finset

section Sites

variable {d n : ℕ} [NeZero n]


open Classical in
/-- The bases of the cells of side `s` that meet the sup-distance ball of radius `R` about `c`. -/
noncomputable def ballCells (s : ℕ) (c : Torus d n) (R : ℕ) : Finset (Torus d n) :=
  Finset.univ.filter fun b => ∃ y, supDist c y ≤ R ∧ cbase s y = b

theorem mem_ballCells {s : ℕ} {c : Torus d n} {R : ℕ} {b : Torus d n} :
    b ∈ ballCells s c R ↔ ∃ y, supDist c y ≤ R ∧ cbase s y = b := by
  classical
  simp [ballCells]

theorem cbase_mem_ballCells {s : ℕ} {c y : Torus d n} {R : ℕ} (h : supDist c y ≤ R) :
    cbase s y ∈ ballCells s c R := mem_ballCells.2 ⟨y, h, rfl⟩

/-- A point at sup-distance `≤ R` from `c` is `c + t` for an integer vector of size `≤ R`. -/
theorem exists_int_of_supDist {c y : Torus d n} {R : ℕ} (h : supDist c y ≤ R) :
    ∃ t : Fin d → ℤ, (∀ μ, |t μ| ≤ R) ∧ y = c + fun μ => ((t μ : ℤ) : ZMod n) := by
  have h' := supDist_le_iff.1 h
  choose t ht1 ht2 using fun μ => (cycNorm_le_iff _ _).1 (h' μ)
  refine ⟨fun μ => -t μ, fun μ => by simpa using ht1 μ, ?_⟩
  funext μ
  simp only [Pi.add_apply, Int.cast_neg, ht2 μ]
  ring

theorem card_ballCells_le {s : ℕ} (hs : s ∣ n) (hs0 : 0 < s) (c : Torus d n) (R : ℕ) :
    (ballCells s c R).card ≤ (2 * R / s + 2) ^ d := by
  classical
  set z : Torus d n := c - natT (fun _ => R) with hz
  set b0 : Torus d n := cbase s z with hb
  have hsub : ballCells s c R ⊆ (Fintype.piFinset fun _ : Fin d => Finset.range (2 * R / s + 2)).image
      (fun q : Fin d → ℕ => b0 + natT (fun μ => s * q μ)) := by
    intro b hb'
    obtain ⟨y, hy, rfl⟩ := mem_ballCells.1 hb'
    obtain ⟨t, ht, hyt⟩ := exists_int_of_supDist hy
    set w : Fin d → ℕ := fun μ => (R + t μ).toNat with hw
    have hw1 : ∀ μ, w μ ≤ 2 * R := fun μ => by
      have := abs_le.1 (ht μ); simp only [hw]; omega
    have hy2 : y = z + natT w := by
      funext μ
      have h1 : ((w μ : ℕ) : ℤ) = R + t μ := by
        have := abs_le.1 (ht μ); simp only [hw]; omega
      rw [hyt]
      simp only [hz, Pi.add_apply, Pi.sub_apply, natT_apply]
      have : ((w μ : ℕ) : ZMod n) = (((R + t μ : ℤ)) : ZMod n) := by
        rw [← h1]; simp
      rw [this]; push_cast; ring
    set r : Fin d → ℕ := fun μ => (z μ).val % s with hr
    have hzr : z = b0 + natT r := by rw [hb, cbase_eq_sub]; abel
    set q : Fin d → ℕ := fun μ => (r μ + w μ) / s with hq
    set r' : Fin d → ℕ := fun μ => (r μ + w μ) % s with hr'
    have hsplit : natT (r + w) = (natT (fun μ => s * q μ) : Torus d n) + natT r' := by
      rw [← natT_add]; congr 1; funext μ
      simp only [Pi.add_apply, hq, hr']
      exact (Nat.div_add_mod _ _).symm
    have hyb : y = (b0 + natT (fun μ => s * q μ)) + natT r' := by
      rw [hy2, hzr, add_assoc, ← natT_add, add_assoc, ← hsplit]
    have hal : Aligned s (b0 + natT (fun μ => s * q μ)) := by
      intro μ
      rw [val_add_natT s hs]
      have : (b0 μ).val % s = 0 := aligned_cbase z μ
      rw [Nat.add_mul_mod_self_left]; exact this
    have hmem : y ∈ Localization.box (b0 + natT (fun μ => s * q μ)) s :=
      ⟨r', fun μ => Nat.mod_lt _ hs0, hyb⟩
    rw [cbase_eq_of_mem_box hs hal hmem]
    refine Finset.mem_image.2 ⟨q, Fintype.mem_piFinset.2 fun μ => Finset.mem_range.2 ?_, rfl⟩
    have hrs : r μ < s := Nat.mod_lt _ hs0
    have hlt : r μ + w μ < s * (2 * R / s + 2) := by
      have h2 := Nat.div_add_mod (2 * R) s
      have h3 := Nat.mod_lt (2 * R) hs0
      have := hw1 μ
      nlinarith
    exact (Nat.div_lt_iff_lt_mul hs0).2 (by linarith)
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp [Fintype.card_piFinset]

theorem supDist_add_int_le {c : Torus d n} {R : ℕ} (t : Fin d → ℤ) (ht : ∀ μ, |t μ| ≤ R) :
    supDist c (c + fun μ => ((t μ : ℤ) : ZMod n)) ≤ R := by
  refine supDist_le_iff.2 fun μ => (cycNorm_le_iff _ _).2 ⟨-t μ, by simpa using ht μ, ?_⟩
  simp

/-- Nearest-neighbour steps inside the ball join its centre to each of its points. -/
theorem supBall_chain {c y : Torus d n} {R : ℕ} (h : supDist c y ≤ R) :
    Relation.ReflTransGen (fun a b : Torus d n => supDist c a ≤ R ∧ supDist c b ≤ R ∧ Nbr a b) c y := by
  classical
  obtain ⟨t, ht, rfl⟩ := exists_int_of_supDist h
  suffices H : ∀ N : ℕ, ∀ t : Fin d → ℤ, (∀ μ, |t μ| ≤ R) → ∑ μ, (t μ).natAbs = N →
      Relation.ReflTransGen (fun a b : Torus d n => supDist c a ≤ R ∧ supDist c b ≤ R ∧ Nbr a b)
        c (c + fun μ => ((t μ : ℤ) : ZMod n)) from H _ t ht rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro t ht hN
  by_cases h0 : ∀ μ, t μ = 0
  · have : (fun μ => ((t μ : ℤ) : ZMod n)) = 0 := funext fun μ => by simp [h0 μ]
    rw [this, add_zero]
  · push Not at h0
    obtain ⟨μ, hμ⟩ := h0
    obtain ⟨ε, hε, hlt⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (t μ - ε).natAbs < (t μ).natAbs := by
      rcases lt_or_gt_of_ne hμ with h | h
      · exact ⟨-1, Or.inr rfl, by omega⟩
      · exact ⟨1, Or.inl rfl, by omega⟩
    set t' : Fin d → ℤ := Function.update t μ (t μ - ε) with ht'
    have htμ : (t μ).natAbs ≤ R := by
      have := ht μ; rw [Int.abs_eq_natAbs] at this; exact_mod_cast this
    have ht'b : ∀ ν, |t' ν| ≤ R := by
      intro ν
      by_cases h : ν = μ
      · subst h
        simp only [ht', Function.update_self]
        rw [Int.abs_eq_natAbs]; exact_mod_cast hlt.le.trans htμ
      · simp only [ht', Function.update_of_ne h]; exact ht ν
    have hsum : ∑ ν, (t' ν).natAbs < ∑ ν, (t ν).natAbs := by
      refine Finset.sum_lt_sum (fun ν _ => ?_) ⟨μ, Finset.mem_univ _, ?_⟩
      · by_cases h : ν = μ
        · subst h; simp only [ht', Function.update_self]; exact hlt.le
        · simp [ht', Function.update_of_ne h]
      · simpa [ht'] using hlt
    have hchain := ih _ (by omega) t' ht'b rfl
    refine hchain.tail ⟨supDist_add_int_le t' ht'b, supDist_add_int_le t ht, μ, ?_⟩
    have hy : (c + fun ν => ((t ν : ℤ) : ZMod n)) =
        (c + fun ν => ((t' ν : ℤ) : ZMod n)) + (ε : ZMod n) • Pi.single μ 1 := by
      funext ν
      by_cases h : ν = μ
      · subst h; simp [ht']; ring
      · simp [ht', h]
    rcases hε with rfl | rfl
    · left; rw [hy]; simp
    · right; rw [hy]; funext ν; by_cases h : ν = μ <;> simp [h]


end Sites

section Hull

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {m₀ : ℕ}


omit [NeZero L] [NeZero N₁] in
theorem near_one_of_nbr {x y : Balaban.Localization.CTorus d L N₁ m₁ K} (h : Nbr x y) : Near 1 1 x y := by
  classical
  obtain ⟨μ, h | h⟩ := h
  · refine ⟨Pi.single μ 1, fun ν => ?_, ?_⟩
    · by_cases h' : ν = μ <;> simp [h']
    · rw [h]; congr 1; funext ν; by_cases h' : ν = μ <;> simp [h']
  · refine ⟨-Pi.single μ 1, fun ν => ?_, ?_⟩
    · by_cases h' : ν = μ <;> simp [h']
    · rw [h]; funext ν; by_cases h' : ν = μ <;> simp [h']

theorem rootConnected_of_siteChains (z : RootIdx d L N₁ m₁ K)
    (J : Finset (ℕ × Balaban.Localization.CTorus d L N₁ m₁ K)) (T : Set (Balaban.Localization.CTorus d L N₁ m₁ K))
    {r : Balaban.Localization.CTorus d L N₁ m₁ K} (hr : r ∈ rootSet m₀ z)
    (hcov : ∀ x ∈ T, x ∈ rootSet m₀ z ∨ ∃ P ∈ J, x ∈ Pset m₁ P)
    (hmeet : ∀ P ∈ J, ∃ x ∈ Pset m₁ P, x ∈ T)
    (hconn : ∀ x ∈ T, Relation.ReflTransGen (fun a b => a ∈ T ∧ b ∈ T ∧ Nbr a b) r x) :
    RootConnected m₀ z J := by
  set step : Option (ℕ × Balaban.Localization.CTorus d L N₁ m₁ K) → Option (ℕ × Balaban.Localization.CTorus d L N₁ m₁ K) → Prop :=
    fun A B => JNode J A ∧ JNode J B ∧ MooreTouch (nodeSet m₀ z A) (nodeSet m₀ z B) with hstep
  have claim : ∀ x ∈ T, ∃ A, JNode J A ∧ x ∈ nodeSet m₀ z A ∧ Relation.ReflTransGen step none A := by
    intro x hx
    have := hconn x hx
    induction this with
    | refl => exact ⟨none, Or.inl rfl, hr, Relation.ReflTransGen.refl⟩
    | tail hab hbc ih =>
      rename_i a b
      obtain ⟨A, hA, haA, hrA⟩ := ih hbc.1
      rcases hcov b hbc.2.1 with hb | ⟨P, hP, hb⟩
      · exact ⟨none, Or.inl rfl, hb, Relation.ReflTransGen.refl⟩
      · exact ⟨some P, Or.inr ⟨P, hP, rfl⟩, hb,
          hrA.tail ⟨hA, Or.inr ⟨P, hP, rfl⟩, a, haA, b, hb, near_one_of_nbr hbc.2.2⟩⟩
  intro P hP
  obtain ⟨x, hxP, hxT⟩ := hmeet P hP
  obtain ⟨A, hA, hxA, hrA⟩ := claim x hxT
  exact hrA.tail ⟨hA, Or.inr ⟨P, hP, rfl⟩, x, hxA, x, hxP,
    ⟨0, fun _ => by simp, by funext μ; simp⟩⟩


section Rooted

variable {k : ℕ} (C : DecCover d L N₁ m₁ (k + 1))

theorem pow_le_side {j : ℕ} (hj : j ≤ k + 1) : (L : ℝ) ^ (j + m₁) ≤ (L : ℝ) ^ (k + 1 + m₁) := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact pow_le_pow_right₀ hL (by omega)

theorem hatRad_le {j : ℕ} (hj : j ≤ k + 1) (hm : 4 * L ^ 2 ≤ L ^ m₁) :
    hatRad L m₁ j + (L : ℝ) ^ (j + m₁) / 2 ≤ 4 * (L : ℝ) ^ (k + 1 + m₁) := by
  have hm' : (4 : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ m₁ := by exact_mod_cast hm
  have hlam : (L : ℝ) ^ (j + m₁) = (L : ℝ) ^ j * (L : ℝ) ^ m₁ := pow_add _ _ _
  have hLj : (0 : ℝ) ≤ (L : ℝ) ^ j := by positivity
  have h1 := mul_le_mul_of_nonneg_left hm' hLj
  have h2 := pow_le_side (L := L) (m₁ := m₁) (k := k) hj
  unfold hatRad
  rw [hlam] at h2 ⊢
  nlinarith

/-- A centre of the footprint of `q` has its base within `5 L^{k+1+m₁}` of the base of `q`. -/
theorem supDist_base_le_of_mem_Qset {q i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hm : 4 * L ^ 2 ≤ L ^ m₁) (hq1 : q.1 ≤ k + 1) (hi1 : i.1 ≤ k + 1) (hi : i ∈ C.Qset q) :
    supDist i.2 q.2 ≤ 5 * L ^ (k + 1 + m₁) := by
  obtain ⟨-, w, hw, hwq⟩ := (DecCover.mem_Qset C).1 hi
  have hR : (0 : ℝ) ≤ hatRad L m₁ q.1 := by unfold hatRad; positivity
  have h1 := supDist_le_of_inBox hR hwq
  have h2 : supDist w i.2 ≤ L ^ (k + 1 + m₁) := supDist_le_of_sameCell_cube hi1 hw
  have h3 := supDist_triangle i.2 w q.2
  rw [supDist_comm i.2 w] at h3
  have h3' : (supDist i.2 q.2 : ℝ) ≤ (supDist w i.2 : ℝ) + (supDist w q.2 : ℝ) := by exact_mod_cast h3
  have h2' : (supDist w i.2 : ℝ) ≤ (L : ℝ) ^ (k + 1 + m₁) := by exact_mod_cast h2
  have h4 := hatRad_le (L := L) (m₁ := m₁) (k := k) hq1 hm
  have : (supDist i.2 q.2 : ℝ) ≤ 5 * (L : ℝ) ^ (k + 1 + m₁) := by linarith
  exact_mod_cast this

/-- The interaction box of a centre lies within `3 L^{k+1+m₁}` of its base. -/
theorem supDist_intBox_le {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hq1 : q.1 ≤ k + 1)
    {x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ intBox q) :
    supDist x q.2 ≤ 3 * L ^ (k + 1 + m₁) := by
  have hR : (0 : ℝ) ≤ 5 / 2 * (L : ℝ) ^ (q.1 + m₁) := by positivity
  have h1 := supDist_le_of_inBox hR (mem_intBox.1 hx)
  have h5 := pow_le_side (L := L) (m₁ := m₁) (k := k) hq1
  have : (supDist x q.2 : ℝ) ≤ 3 * (L : ℝ) ^ (k + 1 + m₁) := by linarith
  exact_mod_cast this

/-- The `D`-neighbourhood of the box of a centre whose footprint contains `i` lies within
`9 L^{k+1+m₁}` of the base of `i`. -/
theorem supDist_boxNbhd_le {D : ℕ} (hD : D ≤ L ^ (k + 1 + m₁)) (hm : 4 * L ^ 2 ≤ L ^ m₁)
    {q i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hq1 : q.1 ≤ k + 1) (hi1 : i.1 ≤ k + 1)
    (hi : i ∈ C.Qset q) {y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hy : y ∈ boxNbhd D q) :
    supDist i.2 y ≤ 9 * L ^ (k + 1 + m₁) := by
  obtain ⟨x, hx, hxy⟩ := hy
  have h1 := supDist_base_le_of_mem_Qset C hm hq1 hi1 hi
  have h2 := supDist_intBox_le hq1 hx
  have h3 := supDist_triangle i.2 q.2 x
  rw [supDist_comm q.2 x] at h3
  have h4 := supDist_triangle i.2 x y
  omega

open Classical in
/-- **The patches of a rooted family and of its seed.**  The cells of side `L^{k+1+m₁}` that meet the
ball of radius `ρs` about `x`, and those that meet the ball of radius `9 L^{k+1+m₁}` about the base
of a cell of `Cs`. -/
noncomputable def labelJ (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) (ρs : ℕ)
    (Cs : Finset ↥C.cubeIdx) : Finset (ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) :=
  ((ballCells (L ^ (k + 1 + m₁)) x ρs).image fun b => (k + 1, b)) ∪
    Cs.biUnion fun i => (ballCells (L ^ (k + 1 + m₁)) i.1.2 (9 * L ^ (k + 1 + m₁))).image
      fun b => (k + 1, b)

variable {C}

theorem labelJ_layer {x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} {ρs : ℕ} {Cs : Finset ↥C.cubeIdx} :
    ∀ P ∈ labelJ C x ρs Cs, P.1 ≤ k + 1 := by
  classical
  intro P hP
  simp only [labelJ, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hP
  rcases hP with ⟨b, -, rfl⟩ | ⟨i, -, b, -, rfl⟩ <;> exact le_rfl

theorem card_labelJ_le (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) (ρs : ℕ)
    (Cs : Finset ↥C.cubeIdx) :
    (labelJ C x ρs Cs).card ≤ (2 * ρs / L ^ (k + 1 + m₁) + 2) ^ d + Cs.card * 20 ^ d := by
  classical
  have hs0 : 0 < L ^ (k + 1 + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hdvd : L ^ (k + 1 + m₁) ∣ N₁ * L ^ m₁ * L ^ (k + 1) :=
    ⟨N₁, by rw [show k + 1 + m₁ = m₁ + (k + 1) by omega, pow_add]; ring⟩
  refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
  · exact Finset.card_image_le.trans (card_ballCells_le hdvd hs0 x ρs)
  · refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (20 ^ d) fun i _ => ?_).trans (by simp)
    refine Finset.card_image_le.trans ((card_ballCells_le hdvd hs0 _ _).trans ?_)
    have : 2 * (9 * L ^ (k + 1 + m₁)) / L ^ (k + 1 + m₁) = 18 := by
      rw [show 2 * (9 * L ^ (k + 1 + m₁)) = 18 * L ^ (k + 1 + m₁) by ring]
      exact Nat.mul_div_cancel _ hs0
    rw [this]

theorem mem_Pset_cbase (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) :
    x ∈ Pset m₁ ((k + 1, cbase (L ^ (k + 1 + m₁)) x) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) :=
  sameCell_cbase (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _) x

/-- **A rooted family is connected to the root for Moore adjacency.**  If the family `Cs` is rooted
(in the sense of `IsRootedFamily`) at a set `S` of sites within `ρs` of `x`, then the root cube of `x`
and the patches `labelJ C x ρs Cs` are connected for Moore adjacency. -/
theorem rootConnected_labelJ {D : ℕ} (hD : D ≤ L ^ (k + 1 + m₁)) (hm : 4 * L ^ 2 ≤ L ^ m₁)
    (hlay : ∀ q ∈ C.cubeIdx, q.1 ≤ k + 1) (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1))
    {ρs : ℕ} {S : Set (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    (hS : ∀ y ∈ S, supDist x y ≤ ρs) {Cs : Finset ↥C.cubeIdx}
    (hroot : Green.IsRootedFamily (cellPatch C D) S Cs) :
    RootConnected m₀ (blockIndex x) (labelJ C x ρs Cs) := by
  classical
  set s := L ^ (k + 1 + m₁) with hs
  set T : Set (Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) :=
    {y | supDist x y ≤ ρs} ∪ ⋃ i ∈ Cs, {y | supDist i.1.2 y ≤ 9 * s} with hT
  set stepT : Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → Prop :=
    fun a b => a ∈ T ∧ b ∈ T ∧ Nbr a b with hstepT
  have hsymm : ∀ a b, stepT a b → stepT b a := fun a b h => ⟨h.2.1, h.1, h.2.2.symm⟩
  have ballx : ∀ y, supDist x y ≤ ρs → Relation.ReflTransGen stepT x y := fun y hy =>
    Relation.ReflTransGen.mono (fun a b h => ⟨Or.inl h.1, Or.inl h.2.1, h.2.2⟩) _ _ (supBall_chain hy)
  have balli : ∀ i ∈ Cs, ∀ y, supDist i.1.2 y ≤ 9 * s → Relation.ReflTransGen stepT i.1.2 y :=
    fun i hi y hy =>
      Relation.ReflTransGen.mono (fun a b h => ⟨Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, h.1⟩),
        Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, h.2.1⟩), h.2.2⟩) _ _ (supBall_chain hy)
  have hpatch : ∀ (i : ↥C.cubeIdx) (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)),
      y ∈ cellPatch C D i → supDist i.1.2 y ≤ 9 * s := by
    intro i y hy
    obtain ⟨q, hq, hiq, hyq⟩ := hy
    exact supDist_boxNbhd_le C hD hm (hlay q hq) (hlay i.1 i.2) hiq hyq
  have key : ∀ j i : ↥C.cubeIdx, Relation.ReflTransGen (Green.CellAdj (cellPatch C D) Cs) j i →
      j ∈ Cs → (cellPatch C D j ∩ S).Nonempty → ∀ y, supDist i.1.2 y ≤ 9 * s →
        Relation.ReflTransGen stepT x y := by
    intro j i hji hj hne
    obtain ⟨y0, hy0⟩ := hne
    induction hji with
    | refl =>
      intro y hy
      exact ((ballx y0 (hS y0 hy0.2)).trans
        (rtg_symm hsymm (balli j hj y0 (hpatch j y0 hy0.1)))).trans (balli j hj y hy)
    | @tail b c _ hab ih =>
      intro y hy
      obtain ⟨hb, hc, y', hy'b, hy'c⟩ := hab
      exact ((ih y' (hpatch b y' hy'b)).trans
        (rtg_symm hsymm (balli c hc y' (hpatch c y' hy'c)))).trans (balli c hc y hy)
  refine rootConnected_of_siteChains (blockIndex x) _ T (r := x) (mem_rootSet_blockIndex x) ?_ ?_ ?_
  · intro y hy
    refine Or.inr ?_
    rcases hy with hy | hy
    · exact ⟨_, Finset.mem_union_left _ (Finset.mem_image.2 ⟨cbase s y, cbase_mem_ballCells hy, rfl⟩),
        mem_Pset_cbase y⟩
    · obtain ⟨i, hi, hy⟩ := Set.mem_iUnion₂.1 hy
      exact ⟨_, Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, hi,
        Finset.mem_image.2 ⟨cbase s y, cbase_mem_ballCells hy, rfl⟩⟩), mem_Pset_cbase y⟩
  · intro P hP
    simp only [labelJ, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hP
    rcases hP with ⟨b, hb, rfl⟩ | ⟨i, hi, b, hb, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := mem_ballCells.1 hb
      exact ⟨y, mem_Pset_cbase y, Or.inl hy⟩
    · obtain ⟨y, hy, rfl⟩ := mem_ballCells.1 hb
      exact ⟨y, mem_Pset_cbase y, Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, hy⟩)⟩
  · intro y hy
    rcases hy with hy | hy
    · exact ballx y hy
    · obtain ⟨i, hi, hy⟩ := Set.mem_iUnion₂.1 hy
      obtain ⟨j, hj, hjS, hji⟩ := hroot i hi
      exact key j i hji hj hjS y hy

theorem seed_subset_hullSet {x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} {ρs : ℕ}
    {Cs : Finset ↥C.cubeIdx} {y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hy : supDist x y ≤ ρs) : y ∈ hullSet m₀ (blockIndex x) (labelJ C x ρs Cs) := by
  classical
  refine Or.inr (Set.mem_iUnion₂.2 ⟨_, Finset.mem_union_left _
    (Finset.mem_image.2 ⟨cbase (L ^ (k + 1 + m₁)) y, cbase_mem_ballCells hy, rfl⟩), mem_Pset_cbase y⟩)

/-- **The hull of a rooted family.**  Under the hypotheses of `rootConnected_labelJ`, the hull of the
root cube of `x` and the patches `labelJ C x ρs Cs` is a polymer of `𝒟_{k+1}` that contains the ball
of radius `ρs` about `x`, and its size is at most `2 d L` times the number of patches, hence at most
`2 d L ((2ρs/L^{k+1+m₁}+2)^d + 20^d |Cs|)`. -/
theorem labelHull_spec {D : ℕ} (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L) (hD : D ≤ L ^ (k + 1 + m₁))
    (hm : 4 * L ^ 2 ≤ L ^ m₁) (hlay : ∀ q ∈ C.cubeIdx, q.1 ≤ k + 1)
    (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) {ρs : ℕ}
    {S : Set (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    (hS : ∀ y ∈ S, supDist x y ≤ ρs) {Cs : Finset ↥C.cubeIdx}
    (hroot : Green.IsRootedFamily (cellPatch C D) S Cs) :
    IsPolyDom m₀ (k + 1) (sitesOf (hullOf m₀ (blockIndex x) (labelJ C x ρs Cs))) ∧
    (∀ y, supDist x y ≤ ρs → y ∈ sitesOf (hullOf m₀ (blockIndex x) (labelJ C x ρs Cs))) ∧
    sizeJ m₀ (k + 1) (sitesOf (hullOf m₀ (blockIndex x) (labelJ C x ρs Cs))) ≤
      (2 * d * L : ℝ) * (((2 * ρs / L ^ (k + 1 + m₁) + 2) ^ d : ℕ) + (Cs.card * 20 ^ d : ℕ)) := by
  have hconn := rootConnected_labelJ (m₀ := m₀) hD hm hlay x hS hroot
  have hpoly := isPolyDom_hullOf hN hL (blockIndex x) (labelJ C x ρs Cs) labelJ_layer hconn
  refine ⟨hpoly, fun y hy => subset_sitesOf_piHull hN _ (seed_subset_hullSet hy), ?_⟩
  rw [← dExt_eq_sizeJ_of_isPolyDom hpoly]
  have h1 := dExt_hullOf_le hN hL (blockIndex x) (labelJ C x ρs Cs) labelJ_layer hconn
  have h2 : ((labelJ C x ρs Cs).card : ℝ) ≤ (((2 * ρs / L ^ (k + 1 + m₁) + 2) ^ d : ℕ) + (Cs.card * 20 ^ d : ℕ)) := by
    exact_mod_cast card_labelJ_le x ρs Cs
  have h3 : (0 : ℝ) ≤ 2 * d * L := by positivity
  linarith [mul_le_mul_of_nonneg_left h2 h3]

end Rooted

end Hull

end Balaban.LargeField.Base
