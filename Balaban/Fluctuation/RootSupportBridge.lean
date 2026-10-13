/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkFibreSitesOf
public import Balaban.Frozen.Geometry.IsPolymer
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# From the step's site domains to the root's polymers

Three bridge lemmas between the objects of one fluctuation step (finite sets `T′` of cubes,
their site set `sitesOf T′`, the size `sizeJ`) and the objects of the frozen root
(`IsPolymer`, the decay `exp (-κ |X| / (M L^j)^d)`), with no use of the tower or of the induction:

* `sitesOf_isPolymer`: a site domain with `IsPolyDom` is a polymer in the sense of `IsPolymer`
  of block side `L^(m₁+1) * L^K`;
* `mem_sitesOf_of_rootCube_blockIndex`: a site lies in every domain containing its root cube;
* `rootRate_of_sizeJ`, `rootRate_of_dExt`: the decay `exp (-lam * sizeJ)` implies the root's
  decay when `lam ≥ c1 d L * κ`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField Balaban.SmallField.Def6

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ

omit [NeZero L] [NeZero N₁] in
theorem cellSide_one_eq : cellSide L 1 m₁ K = L ^ (m₁ + 1) * L ^ K := by
  unfold cellSide; rw [← pow_add]; congr 1; omega

/-- The block-closure clause: two sites with equal coordinate quotients by the cell side lie in
the same aligned cell. -/
theorem mem_sitesOf_of_quotients (hN : L ∣ N₁) (T : Finset 𝔅) {x y : CTorus d L N₁ m₁ K}
    (hx : x ∈ sitesOf T)
    (hxy : ∀ μ, (x μ).val / (L ^ (m₁ + 1) * L ^ K) = (y μ).val / (L ^ (m₁ + 1) * L ^ K)) :
    y ∈ sitesOf T := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) (m₀ := 1) (by simpa using hN) (le_refl K)
  have ha0 : 0 < cellSide L 1 m₁ K := cellSide_pos (L := L) 1 m₁ K
  obtain ⟨b, hb, hmem⟩ := mem_sitesOf.1 hx
  have e1 := cbase_eq_of_mem_box hdvd b.2.1 hmem
  have e2 : cbase (cellSide L 1 m₁ K) y = cbase (cellSide L 1 m₁ K) x := by
    funext μ
    simp only [cbase]
    rw [cellSide_one_eq, ← hxy μ]
  refine mem_sitesOf.2 ⟨b, hb, ?_⟩
  have := mem_box_cbase ha0 y
  rwa [e2, e1] at this

open Classical in
/-- **T1.** A site domain with `IsPolyDom` is a polymer of the frozen definition `IsPolymer`
(block side `L^(m₁+1) * L^K`, torus length `(N₁ * L^m₁) * L^K`, which is the type
`CTorus d L N₁ m₁ K` on the nose). -/
theorem sitesOf_isPolymer (hN : L ∣ N₁) (T : Finset 𝔅) (hpoly : IsPolyDom 1 K (sitesOf T)) :
    IsPolymer d ((N₁ * L ^ m₁) * L ^ K) (L ^ (m₁ + 1) * L ^ K)
      (Finset.univ.filter (· ∈ sitesOf T)) := by
  obtain ⟨hne, -, hconn⟩ := hpoly
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x, by simpa using hx⟩
  · intro x hx y hxy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact mem_sitesOf_of_quotients hN T hx hxy
  · intro x hx y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    have hc := hconn x hx y hy
    induction hc with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      exact Relation.ReflTransGen.tail (ih hbc.1)
        ⟨by simpa using hbc.1, by simpa using hbc.2.1, hbc.2.2⟩

/-- **T2.** The observable site lies in every domain that contains its root cube. -/
theorem mem_sitesOf_of_rootCube_blockIndex (T : Finset 𝔅)
    (y : CTorus d L N₁ m₁ K) (h : rootCube (m₀ := 1) (blockIndex y) ∈ T) : y ∈ sitesOf T := by
  have ha0 : 0 < cellSide L 1 m₁ K := cellSide_pos (L := L) 1 m₁ K
  have hLK : 0 < L ^ K := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨c, hc⟩ := (pow_dvd_cellSide (L := L) (m₀ := 1) (m₁ := m₁) (K := K))
  have hv : ∀ μ, (rootSite (blockIndex y) μ).val = L ^ K * ((y μ).val / L ^ K) := by
    intro μ
    have hlt : (y μ).val / L ^ K < N₁ * L ^ m₁ * L ^ (K - K) := by
      rw [Nat.sub_self, pow_zero, mul_one]
      exact (Nat.div_lt_iff_lt_mul hLK).2 (ZMod.val_lt (y μ))
    rw [rootSite_val]
    congr 1
    simp only [blockIndex]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  have e : cbase (cellSide L 1 m₁ K) y =
      (rootCube (m₀ := 1) (blockIndex y)).1 := by
    show _ = cbase (cellSide L 1 m₁ K) (rootSite (blockIndex y))
    funext μ
    simp only [cbase]
    congr 2
    rw [hv μ]
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0, mul_zero] at hc; omega
      · exact h0
    rw [hc, Nat.mul_div_mul_left _ _ hLK, Nat.div_div_eq_div_mul]
  refine mem_sitesOf.2 ⟨_, h, ?_⟩
  rw [← e]
  exact mem_box_cbase ha0 y

/-- **T3.** The step's decay `exp (-lam * sizeJ)` implies the root's decay
`exp (-κ |Y| / a^d)`, `a = cellSide L 1 m₁ j`, when `lam ≥ c1 d L * κ`. -/
theorem rootRate_of_sizeJ {j : ℕ} (hN : L ∣ N₁) (hj : j ≤ K)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsDj 1 j Y) {κ lam B : ℝ} (hκ : 0 < κ)
    (hlam : c1 d L * κ ≤ lam) (hB : 0 ≤ B) :
    B * Real.exp (-lam * sizeJ 1 j Y) ≤
      B * Real.exp lam *
        Real.exp (-κ * (Y.ncard : ℝ) / ((cellSide L 1 m₁ j : ℕ) : ℝ) ^ d) := by
  have hG := G1_card (m₀ := 1) (by simpa using hN) hj hY
  have hs : 0 ≤ sizeJ 1 j Y := treeLenCovOne_nonneg 1 j Y
  have ha : (0 : ℝ) < ((cellSide L 1 m₁ j : ℕ) : ℝ) ^ d := by
    have := cellSide_pos (L := L) 1 m₁ j
    positivity
  have hc : 0 ≤ c1 d L := by unfold c1; positivity
  have h1 : κ * (Y.ncard : ℝ) / ((cellSide L 1 m₁ j : ℕ) : ℝ) ^ d ≤ lam * (1 + sizeJ 1 j Y) := by
    rw [div_le_iff₀ ha]
    have h2 : κ * (Y.ncard : ℝ) ≤ κ * (c1 d L * ((cellSide L 1 m₁ j : ℕ) : ℝ) ^ d *
        (1 + treeLenCovOne 1 j Y)) := mul_le_mul_of_nonneg_left hG hκ.le
    have h3 : c1 d L * κ * (1 + sizeJ 1 j Y) ≤ lam * (1 + sizeJ 1 j Y) :=
      mul_le_mul_of_nonneg_right hlam (by linarith)
    have h4 : κ * (c1 d L * ((cellSide L 1 m₁ j : ℕ) : ℝ) ^ d * (1 + treeLenCovOne 1 j Y)) =
        (c1 d L * κ * (1 + sizeJ 1 j Y)) * ((cellSide L 1 m₁ j : ℕ) : ℝ) ^ d := by
      unfold sizeJ; ring
    calc κ * (Y.ncard : ℝ) ≤ _ := h2
      _ = _ := h4
      _ ≤ (lam * (1 + sizeJ 1 j Y)) * ((cellSide L 1 m₁ j : ℕ) : ℝ) ^ d :=
          mul_le_mul_of_nonneg_right h3 ha.le
  have h5 : -lam * sizeJ 1 j Y ≤ lam + -κ * (Y.ncard : ℝ) / ((cellSide L 1 m₁ j : ℕ) : ℝ) ^ d := by
    have : -κ * (Y.ncard : ℝ) / ((cellSide L 1 m₁ j : ℕ) : ℝ) ^ d =
        -(κ * (Y.ncard : ℝ) / ((cellSide L 1 m₁ j : ℕ) : ℝ) ^ d) := by ring
    rw [this]; nlinarith
  calc B * Real.exp (-lam * sizeJ 1 j Y)
      ≤ B * Real.exp (lam + -κ * (Y.ncard : ℝ) / ((cellSide L 1 m₁ j : ℕ) : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h5) hB
    _ = _ := by rw [Real.exp_add]; ring

open Classical in
/-- **T3, cube-set form.**  With `X` the finite site set of `T`, block side `M L^K`,
`M = L^(m₁+1)`. -/
theorem rootRate_of_dExt (hN : L ∣ N₁) (T : Finset 𝔅) (hpoly : IsPolyDom 1 K (sitesOf T))
    {κ lam B : ℝ} (hκ : 0 < κ) (hlam : c1 d L * κ ≤ lam) (hB : 0 ≤ B) :
    B * Real.exp (-lam * dExt T) ≤
      B * Real.exp lam *
        Real.exp (-κ * ((Finset.univ.filter (· ∈ sitesOf T)).card : ℝ) /
          ((L ^ (m₁ + 1) * L ^ K : ℕ) : ℝ) ^ d) := by
  obtain ⟨hDj, hd⟩ := (markFibre_sitesOf.{0} (m₀ := 1) (by simpa using hN)).1 T hpoly
  have h := rootRate_of_sizeJ (m₁ := m₁) hN le_rfl hDj hκ hlam hB
  have hcard : ((Finset.univ.filter (· ∈ sitesOf T)).card : ℝ) = ((sitesOf T).ncard : ℝ) := by
    rw [← Set.ncard_coe_finset]
    congr 2
    ext x; simp
  rw [hd, hcard, ← Nat.cast_pow] at *
  rw [hcard, ← cellSide_one_eq]
  rw [hd]
  exact h

open Classical in
/-- The map `T ↦ (Finset.univ.filter (· ∈ sitesOf T))` is injective. -/
theorem filter_sitesOf_injective (hN : L ∣ N₁) :
    Function.Injective (fun T : Finset 𝔅 => Finset.univ.filter (· ∈ sitesOf T)) := by
  intro T T' h
  refine (markFibre_sitesOf.{0} (m₀ := 1) (by simpa using hN)).2.1 T T' ?_
  ext x
  have := congrArg (x ∈ ·) h
  simpa using this

omit [NeZero N₁] in
/-- Admissibility of the root: `M L^K ∣ ℓ` for `ℓ = (N₁ L^m₁) L^K`, `M = L^(m₁+1)`
is exactly `L ∣ N₁`. -/
theorem admissible_iff_dvd :
    L ^ (m₁ + 1) * L ^ K ∣ (N₁ * L ^ m₁) * L ^ K ↔ L ∣ N₁ := by
  have hK : 0 < L ^ K := Nat.pos_of_ne_zero (NeZero.ne _)
  have hm : 0 < L ^ m₁ := Nat.pos_of_ne_zero (NeZero.ne _)
  rw [Nat.mul_dvd_mul_iff_right hK, pow_succ, mul_comm (L ^ m₁) L,
    Nat.mul_dvd_mul_iff_right hm]

end Balaban.Fluctuation
