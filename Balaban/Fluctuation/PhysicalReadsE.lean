/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionHatE
public import Balaban.Localization.FootprintMargin
public import Balaban.Localization.DecoupledBackgroundLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The approximate field read by the old energy terms (E-read)

Let `Gp` be a whole-lattice generating set of level `n` (`IsLevel Gp n`, block side `ℓ = L ^ n`),
`Gk` the generating set of the data sites, and `x` a data site of `Gk`.  A site `u` of
`composeDep Gk Gp x` (that is `x`, or a site of the `Gk`-block or of the `Gp`-block of `x`) is in
every coordinate at lift distance at most `ℓ - 1` from `x`; a site `v` read by the approximate
field of `Gp` at `u` is at lift distance at most `2 ℓ - 1` from `u`.  So `v` is at lift distance
at most `3 ℓ - 2` from `x` in every coordinate, hence at `ℓ¹` torus distance at most `d (3 ℓ - 2)`,
which is smaller than `r₀ L ^ m₁ ℓ` because `r₀ ≥ 4 d L ^ 3`.  The ball hypothesis `hN` of
`BgSetting` then places `v` in `X₁`.

* `composeDep_coord_bound`: the coordinate bound `ℓ - 1` for `composeDep`;
* `approxDep_composeDep_subset_X1`: **(E-read)**, `approxDep Gp u ⊆ X₁` for `u ∈ composeDep Gk Gp x`;
* `approxDep_composeDep_hm_subset_X1`: the same for the composite sites `composeDep Gk Hm x` of the
  fluctuation (`FlSetting`);
* `approxField_composeDep_congr`: two background data sets that agree on `X₁` give the same
  approximate field at every composite site.

Only this support inclusion and the resulting congruence of the approximate field are proved here.
The sharp locality of the expansion of the `E` terms (`eterm_expansion_hat`) and the other three
summands of the interaction are separate packages.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

section Coord

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}

/-- A lift distance `≤ r` in a coordinate bounds the coordinate of the `ℓ¹` torus distance. -/
theorem natAbs_cycRep_le_of_coordNear {S : ℕ} [NeZero S] {r : ℝ} {a b : ZMod S}
    (h : CoordNear S r a b) : ((Green.cycRep (a - b)).natAbs : ℝ) ≤ r := by
  obtain ⟨p, hp⟩ := h
  have hk : (((a.val : ℤ) + p * (S : ℤ) - (b.val : ℤ) : ℤ) : ZMod S) = a - b := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_self]
    ring
  have h1 := Green.natAbs_cycRep_le_of_cast (a - b) _ hk
  have h2 : ((Green.cycRep (a - b)).natAbs : ℝ) ≤
      (((a.val : ℤ) + p * (S : ℤ) - (b.val : ℤ)).natAbs : ℝ) := by exact_mod_cast h1
  refine h2.trans (le_trans (le_of_eq ?_) hp)
  rw [Nat.cast_natAbs]
  push_cast
  rfl

/-- **Coordinate bound for `composeDep`.**  If the layer indices of `x` in `G` and `G'` (when
`x ∈ G.Ω 1`) are at most `n ≤ K`, every site of `composeDep G G' x` is, in each coordinate, at lift
distance at most `L ^ n - 1` from `x` (the sites of a block of side `L ^ j`, `j ≤ n`, differ by at
most `L ^ j - 1`). -/
theorem composeDep_coord_bound {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'} {n : ℕ} (hnK : n ≤ K)
    {x u : Torus d (N₁ * L ^ m₁ * L ^ K)} (hu : u ∈ composeDep G G' x)
    (h1 : x ∈ G.Ω 1 → G.layerIndex x ≤ n) (h2 : x ∈ G.Ω 1 → G'.layerIndex x ≤ n) (μ : Fin d) :
    CoordNear (N₁ * L ^ m₁ * L ^ K) ((L : ℝ) ^ n - 1) (u μ) (x μ) := by
  classical
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hl : (1 : ℝ) ≤ (L : ℝ) ^ n := one_le_pow₀ hL1
  unfold composeDep at hu
  by_cases hx : x ∈ G.Ω 1
  · simp only [hx, ↓reduceIte] at hu
    have hblk : ∀ {H : ℕ} (hH : H ≤ n), jBlock d L (N₁ * L ^ m₁) K H u =
        jBlock d L (N₁ * L ^ m₁) K H x →
        CoordNear (N₁ * L ^ m₁ * L ^ K) ((L : ℝ) ^ n - 1) (u μ) (x μ) := fun {H} hH hb =>
      (jBlock_coord_bound (hH.trans hnK) hb μ).mono
        (by have := pow_le_pow_right₀ hL1 hH; linarith)
    rw [Finset.mem_insert, Finset.mem_union] at hu
    rcases hu with rfl | hb | hb
    · exact CoordNear.refl (by linarith) _
    · exact hblk (h1 hx) (GeneratingSet.mem_blk.1 hb)
    · exact hblk (h2 hx) (GeneratingSet.mem_blk.1 hb)
  · simp only [hx, ↓reduceIte, Finset.mem_singleton] at hu
    subst hu
    exact CoordNear.refl (by linarith) _

end Coord

section Radius

/-- The numerical comparison for the ball of `hN`: `d (3 ℓ - 2) < r₀ L ^ m₁ ℓ` when
`r₀ ≥ 4 d L ^ 3`, `d ≥ 1`, `L ≥ 1`, `ℓ ≥ 1`; the slack is `r₀ L ^ m₁ ℓ - d (3 ℓ - 2) ≥ d ℓ + 2 d`. -/
theorem radius_lt {d L m₁ : ℕ} {r₀ ℓ : ℝ} (hd : 1 ≤ (d : ℝ)) (hL : (1 : ℝ) ≤ L) (hℓ : 1 ≤ ℓ)
    (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀) :
    (d : ℝ) * (3 * ℓ - 2) < r₀ * (L : ℝ) ^ m₁ * ℓ := by
  have hL3 : (1 : ℝ) ≤ (L : ℝ) ^ 3 := one_le_pow₀ hL
  have hLm : (1 : ℝ) ≤ (L : ℝ) ^ m₁ := one_le_pow₀ hL
  have h4 : 4 * (d : ℝ) ≤ r₀ := by nlinarith
  have h5 : r₀ ≤ r₀ * (L : ℝ) ^ m₁ := by nlinarith
  have h6 : 4 * (d : ℝ) * ℓ ≤ r₀ * (L : ℝ) ^ m₁ * ℓ := by nlinarith
  nlinarith

end Radius

section Read

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁} {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}

/-- **The read set of the approximate field at a nearby site lies in `X₁`.**  For a data site `x`
of `Gk` and a site `u` at lift distance `≤ ℓ - 1` from `x` in every coordinate (`ℓ = L ^ n`,
`Gp` of level `n`), every site read by the approximate field of `Gp` at `u` lies in `X₁`. -/
theorem approxDep_subset_X1_of_near
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) {n : ℕ} (hG : IsLevel Gp n)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ dataSites Gk) {u : CTorus d L N₁ m₁ K}
    (hu : ∀ μ, CoordNear (N₁ * L ^ m₁ * L ^ K) ((L : ℝ) ^ n - 1) (u μ) (x μ)) :
    approxDep Gp u ⊆ X₁f := by
  intro v hv
  have hd : (1 : ℝ) ≤ d := by
    have := hB.HBp.hd
    exact_mod_cast (by omega : 1 ≤ d)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hl : (1 : ℝ) ≤ (L : ℝ) ^ n := one_le_pow₀ hL1
  have hx0 : x ∈ X₀ := hB.dsX₀ x hx
  have hxΩ : x ∈ Gp.Ω 1 := (hG x).1
  refine hB.hN x hx0 hxΩ v ?_
  have hsp : Gp.spacing x = (L : ℝ) ^ n := by
    unfold GeneratingSet.spacing; rw [(hG x).2]
  rw [hsp]
  have hcoord : ∀ μ, ((Green.cycRep (x μ - v μ)).natAbs : ℝ) ≤ 3 * (L : ℝ) ^ n - 2 := by
    intro μ
    have h := ((approxDep_coord_bound hG hv μ).symm.trans (hu μ)).symm
    have h' := h.mono (r' := 3 * (L : ℝ) ^ n - 2) (by linarith)
    exact natAbs_cycRep_le_of_coordNear h'
  have hsum : Green.torusDist d (N₁ * L ^ m₁ * L ^ K) x v ≤ d * (3 * (L : ℝ) ^ n - 2) := by
    unfold Green.torusDist
    calc _ ≤ ∑ _μ : Fin d, (3 * (L : ℝ) ^ n - 2) := Finset.sum_le_sum fun μ _ => hcoord μ
      _ = _ := by simp; ring
  exact lt_of_le_of_lt hsum (radius_lt hd hL1 hl hB.hr₀)

/-- **(E-read).**  For `Gp` of level `n` and a data site `x` of `Gk`, every site `u` of the
composite dependency set `composeDep Gk Gp x` has all its approximate-field reads
`approxDep Gp u` in `X₁`. -/
theorem approxDep_composeDep_subset_X1
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) {n : ℕ} (hG : IsLevel Gp n)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ dataSites Gk) {u : CTorus d L N₁ m₁ K}
    (hu : u ∈ composeDep Gk Gp x) : approxDep Gp u ⊆ X₁f := by
  refine approxDep_subset_X1_of_near hB hG hx fun μ => ?_
  refine composeDep_coord_bound hG.bounds.2 hu (fun hxk => ?_) (fun _ => ?_) μ
  · have := hB.hP.layerIndex_le hxk
    rwa [(hG x).2] at this
  · exact (hG x).2.le

/-- **(E-read) for the fluctuation composite sites** `composeDep Gk Hm x` (`FlSetting`). -/
theorem approxDep_composeDep_hm_subset_X1
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f) {n : ℕ}
    (hG : IsLevel Gp n) {x : CTorus d L N₁ m₁ K} (hx : x ∈ dataSites Gk)
    {u : CTorus d L N₁ m₁ K} (hu : u ∈ composeDep Gk Hm x) : approxDep Gp u ⊆ X₁f := by
  refine approxDep_subset_X1_of_near hB hG hx fun μ => ?_
  have hHm : x ∈ Gk.Ω 1 → Hm.layerIndex x ≤ n := fun hxk => by
    have := hF.hPmp.layerIndex_le (hF.hPm.mem_Ω1 hxk)
    rwa [(hG x).2] at this
  refine composeDep_coord_bound hG.bounds.2 hu (fun hxk => ?_) (fun hxk => hHm hxk) μ
  exact (hF.hPm.layerIndex_le hxk).trans (hHm hxk)

/-- Two background data sets (`Ψ`, `h`) that agree on `X₁` give the same approximate field of
`Gp` at every composite site `u ∈ composeDep Gk Gp x` of a data site `x`. -/
theorem approxField_composeDep_congr
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) {n : ℕ} (hG : IsLevel Gp n)
    {a : ℕ → ℝ} {Ψ Ψ₂ h h₂ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hag : ∀ y ∈ X₁f, Ψ y = Ψ₂ y ∧ h y = h₂ y) {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ dataSites Gk) {u : CTorus d L N₁ m₁ K} (hu : u ∈ composeDep Gk Gp x) :
    approxField Gp a ν Ψ h u = approxField Gp a ν Ψ₂ h₂ u :=
  approxField_congr fun y hy =>
    ⟨(hag y (approxDep_composeDep_subset_X1 hB hG hx hu hy)).1,
      fun _ => (hag y (approxDep_composeDep_subset_X1 hB hG hx hu hy)).2⟩

/-- The same for the composite sites `composeDep Gk Hm x` of the fluctuation. -/
theorem approxField_composeDep_hm_congr
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f) {n : ℕ}
    (hG : IsLevel Gp n) {a : ℕ → ℝ} {Ψ Ψ₂ h h₂ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hag : ∀ y ∈ X₁f, Ψ y = Ψ₂ y ∧ h y = h₂ y) {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ dataSites Gk) {u : CTorus d L N₁ m₁ K} (hu : u ∈ composeDep Gk Hm x) :
    approxField Gp a ν Ψ h u = approxField Gp a ν Ψ₂ h₂ u :=
  approxField_congr fun y hy =>
    ⟨(hag y (approxDep_composeDep_hm_subset_X1 hB hF hG hx hu hy)).1,
      fun _ => (hag y (approxDep_composeDep_hm_subset_X1 hB hF hG hx hu hy)).2⟩

/-- **(E-read) in the component `Y₁`.**  Since `X₁ ⊆ Y(𝒞)` (`subset_compY`), the reads also lie in
the component of `X₁ ∪ ⋃ P_i` containing `X₁`. -/
theorem approxDep_composeDep_subset_compY
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) {n : ℕ} (hG : IsLevel Gp n)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ dataSites Gk) {u : CTorus d L N₁ m₁ K}
    (hu : u ∈ composeDep Gk Gp x) {ι : Type*} (c' : ι → ℕ × CTorus d L N₁ m₁ K)
    (C : Finset ι) {v : CTorus d L N₁ m₁ K} (hv : v ∈ approxDep Gp u) :
    v ∈ compY c' (↑X₁f : Set (CTorus d L N₁ m₁ K)) C :=
  subset_compY (↑X₁f : Set (CTorus d L N₁ m₁ K)) C
    (Finset.mem_coe.2 (approxDep_composeDep_subset_X1 hB hG hx hu hv))

end Read

end Balaban.Localization
