/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionLevelPair
public import Balaban.Fluctuation.Theorem42Geom
public import Balaban.Localization.SupportMargin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The local cover of the pair of consecutive full levels, on every torus

The zero-class activity theorem `stepActivityBound_zeroClass_direct_scaled` (and its forms
`…_scaled_beta`, `…_scaled_uniform`) is stated for a step at any scale `k` and any torus
`CTorus d L N₁ m₁ (k + 1)`.  The landed witness discharges its cover hypotheses with one cover cube
that fills the torus (`LevelPair.X1_eq_univ`, valid because `9 · 3^{m₁} · 3² = 3 · cellSide`).  This
file proves the cover hypotheses block by block and site by site on every torus.

## Inventory: the hypotheses of the scaled activity theorem discharged at the witness with `N₁ = 9` or `k = 1`

Index sets: `z : Torus d (N₁ L^{m₁} L^{(k+1)-(k+1)})` (the blocks `B_{k+1}(z)`),
`s : CTorus d L N₁ m₁ (k+1) × Fin N` (the source sites).  `G' = S.G'`, `Hm = stepG d L N₁ m₁ k ϱ`.

| hypothesis | statement | at the witness |
|---|---|---|
| `hcovV` | `∀ z, CovSetup G' m₀ (jV z) (XV z) (𝒦XV z)` | `LevelPair.covSetup`: `X = box 0 (3 a_1)`, `𝒦 = {0}` for every `z` (`Gp_layerUnion`, `cov_nest`: `N₁ = 9`, `K = 2`) |
| `hX₁V` | `∀ z, ↑(X₁V z) = X1 G' m₀ (jV z) (𝒦XV z)` | `X₁ = 𝕋`, `X1_eq_univ` (`box_univ`: the torus is `3` cells wide) |
| `hoptV` | `∀ z, ∃ W₀ E₀, ConnStruct W₀ E₀ ∧ ↑W₀ ⊆ XV z ∧ MeetsOne m₀ (jV z) (𝒦XV z) W₀ ∧ bondCost (scaleW L m₀ m₁ (jV z)) E₀ = treeLenCovOne m₀ (jV z) (XV z)` | `LevelPair.hopt` |
| `hΔV` | `∀ z, treeLenCovOne m₀ (jV z) (XV z) = 0` | `LevelPair.treeLen_zero` |
| `hlogV` | `log ((2L+1)^d (L^{m₀})^d) ≤ (κ/2 - 1)/2` | numeric at `m₀ = 1` (no `k`, `N₁`) |
| `hZV` | `∀ z, readSites Hm k z ⊆ ↑(X₁V z)` | trivial, `X₁ = 𝕋` |
| `hmarV` | `∀ z, BlockMargin G' (X₁V z) ↑(blockSites d L N₁ m₁ (k+1) k z)` | `blockMargin_univ`, `mem_some_intBox` |
| `hZν` | `∀ z, ↑(blockSites d L N₁ m₁ (k+1) k z) ⊆ ↑(X₁V z)` | trivial, `X₁ = 𝕋` |
| `hcovF`, `hX₁F`, `hoptF`, `hΔF`, `hlogF` | the same five statements with `s` in place of `z` | the same cube for every `s` |
| `hyF` | `∀ s, s.1 ∈ X₁F s` | trivial, `X₁ = 𝕋` |
| `hC` | `FlCore N G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁` | `tower_core_rates` at the pair of the witness, `ν = 1/81` |
| `hconn`, `hrow`, `hG`, `H` | `HatConn G'`, `RowInHat (coverOf G') Hm a ν`, `IsLevel Hm k`, `BgHyp d L (k+1) ϱ a ν` | `LevelPair.hatConn`, `rowInHat_level`, `isLevel_Hm`, `bgHypNu` (`k = 1`, `N₁ = 9`) |
| `hδ₁` | `√N ‖β_k^{-1/2}‖ (covSupConstC d L N (a_k) κ · c_ψ) < δ₁` | `tower_C_items` (`β_k = 3β`, weight `a_1`) |
| `hc`, `hp`, `hpρ`, `hlt`, `hr` | `(R_σ R₁ + r) ρ < c_ψ`, `0 < p₁ ≤ ρ`, `p₁ < p⁺`, `0 < r` | `tower_C_items` |
| `R0`, `hbase` | `S.RayData p⁺`, `InUnionDomainC Hm c₀ c₂ ν (S.dataU S.psi0)` | `rayData_hatStep_pp` (`k = 1`, `N₁ = 9`, `ν = 1/81`) |
| `hD`, `hBh` | `XiCData G' a ν (k+1) 1 eps S.D'`; `‖D.h x i‖ ≤ Bh` on that set | unit datum; `hBh_of_xi` with `Bh = 1 + 2/ν` |
| `hεb`, `hDA` | the amplitude with `β_k` and `r`; the smallness of `R_σ ε_U` | `tower_amp_exists` (`β_k = 3β`), `amplitude_le` |

The rows `hcovV`–`hyF` are proved here for every `k` and `N₁`.  The rows `hconn`, `hrow`, `hG`, `H`
are in `LevelStepSetting`; the remaining rows are in `LevelRayTower` and `ScaleActivityFinal`.

## The local cover

Notation: `a_n = cellSide L m₀ m₁ n = L^{n+m₀+m₁}` is the side of a `π_n`-cell, a `π'_n`-cube is an
aligned box of side `L a_n`, `M = L^{K+m₁}` is the side of a cover cube of the top layer `K`.
For a site `x` of a torus whose generating set `G` is a whole-lattice set of the top level `K`:

* `LocalCover.cube m₀ j x` (the set `X`): the `π'_j`-cube at the corner of the `π_K`-cell of `x`
  (`j < K`); it lies in that cell.  `LocalCover.fam m₀ x = {X}` is the chosen family.
* `LocalCover.covSetup`: `CovSetup G m₀ j X {X}`.
* `LocalCover.X1_eq`: `X₁ = ⋃ 𝒬₀` is `LocalCover.nbhd m₀ x`, the box of `2L - 1` cells of `π_K`
  per direction around the cell of `x` (`iUnion_cubes_eq_cellNbhd`).  It has at most
  `((2L-1) a_K)^d` sites (`card_nbhdF_le`), whatever the torus.
* `LocalCover.hopt`, `LocalCover.treeLen_eq_zero`: the optimal structure is one point and
  `d^cov_j(X) = 0` (`hopt_box`).
* `LocalCover.blockMargin`: for `m₀ ≥ 1`, every set of sites in the cell has `BlockMargin` in `X₁`.
  The proof: a site lies in the support of some `χ_q`, hence within `3/2 M` of the centre of the
  cube `q`; the thickened cube of `q` has half-width `hatRad ≤ 13/4 M`, and a cover cube meeting it
  adds one cube side `M`; in total at most `23/4 M ≤ 6 M ≤ (L - 1) a_K` (`hatRad_add_le`), the
  distance from the cell to the complement of `X₁`.
* `LocalCover.readSites_subset_nbhdF`, `LocalCover.blockSites_subset_nbhdF`: the read sites of a
  block `B_{n+1}(z)`, `n < K`, lie in `X₁` of the block.
* `LocalCover.levelLocalCover`: all of these for the pair `(𝔹_{k+1}, 𝔹_k)`, in the form consumed by
  the activity theorem.

## Size conditions

The only condition on the torus is `L^{m₀} ∣ N₁` with `m₀ ≥ 1` (it is a field of `CovSetup`; the
cover scale `m₀ = 1` gives `L ∣ N₁`), besides `5 < N₁` in `DGSetting`.  No torus is excluded for
wrap-around: every statement is an inclusion of boxes given by offsets from a base point, and on a
torus with at most `2L - 1` cells of `π_K` per direction the region `X₁` is the whole torus
(`LocalCover.nbhd_eq_univ`; the witness `N₁ = 9`, `L = 3`, `m₀ = 1` has `3` cells).  The proof of
the margin uses `m₀ ≥ 1`.  At `m₀ = 0`, `L = 3` the region `X₁` of this construction extends `2 M`
beyond the cube of the site, while a thickened cube extends `2 M + 3 L² L^K` beyond its cube, so
the argument does not apply there.

No constant is produced: the conclusions contain `m₀` and nothing depending on `k` or `N₁`.

What is proved: the cover hypotheses of the potential part and of the source part, for a
whole-lattice generating set of the top level, on every torus.  What is not proved here: the
cover data of old-energy and observable terms of a general class (`BgSetting`, `FlSetting`
margins), which are empty for the zero class.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

/-! ### Boxes on a torus -/

section Arith

variable {d n : ℕ}

/-- A box of side `s` based at `b + v` lies in the box of side `s'` based at `b` when
`v + s ≤ s'`. -/
theorem box_add_subset (b : Torus d n) (v : Fin d → ℕ) {s s' : ℕ} (h : ∀ μ, v μ + s ≤ s') :
    box (b + natT v) s ⊆ box b s' := by
  rintro x ⟨w, hw, rfl⟩
  refine ⟨v + w, fun μ => ?_, by rw [natT_add, add_assoc]⟩
  have h1 := h μ
  have h2 := hw μ
  simp only [Pi.add_apply]
  omega

/-- Subtracting a vector of multiples of `a` preserves alignment. -/
theorem aligned_sub_natT [NeZero n] {a : ℕ} (ha : a ∣ n) {b : Torus d n} (hb : Aligned a b)
    {w : Fin d → ℕ} (hw : ∀ μ, w μ % a = 0) : Aligned a (b - natT w) := by
  intro μ
  have h := val_add_natT a ha (b - natT w) w μ
  rw [sub_add_cancel, Nat.add_mod, hw μ, add_zero, Nat.mod_mod] at h
  rw [← h]
  exact hb μ

/-- **The neighbourhood of a cell**: the box of `2L - 1` cells of side `c` per direction whose
central cell is the cell of base `B` (`L - 1` cells on each side). -/
def cellNbhd (L c : ℕ) (B : Torus d n) : Set (Torus d n) :=
  box (B - natT fun _ => (L - 1) * c) ((L - 1) * c + L * c)

/-- The cell lies in its neighbourhood. -/
theorem cell_subset_cellNbhd {L : ℕ} (hL : 1 ≤ L) (c : ℕ) (B : Torus d n) :
    box B c ⊆ cellNbhd L c B := by
  have h := box_add_subset (B - natT fun _ => (L - 1) * c) (fun _ => (L - 1) * c) (s := c)
    (s' := (L - 1) * c + L * c) (fun _ => by
      have : c ≤ L * c := Nat.le_mul_of_pos_left c hL
      omega)
  rwa [sub_add_cancel] at h

/-- A point of the cell moved by an integer vector of sup norm at most `(L - 1) c` stays in the
neighbourhood of the cell. -/
theorem add_intTorus_mem_cellNbhd {L c : ℕ} (hL : 1 ≤ L) {B x : Torus d n} (hx : x ∈ box B c)
    (w : Fin d → ℤ) (hw : ∀ μ, |w μ| ≤ (((L - 1) * c : ℕ) : ℤ)) :
    x + (intTorus w : Torus d n) ∈ cellNbhd L c B := by
  obtain ⟨u, hu, rfl⟩ := hx
  have hLc : L * c = (L - 1) * c + c := by
    conv_lhs => rw [show L = L - 1 + 1 by omega]
    rw [Nat.succ_mul]
  refine ⟨fun μ => ((u μ : ℤ) + w μ + (((L - 1) * c : ℕ) : ℤ)).toNat, fun μ => ?_, ?_⟩
  · have h1 := abs_le.1 (hw μ)
    have h2 := hu μ
    show ((u μ : ℤ) + w μ + (((L - 1) * c : ℕ) : ℤ)).toNat < (L - 1) * c + L * c
    rw [hLc]
    omega
  · funext μ
    have h1 := abs_le.1 (hw μ)
    have h0 : 0 ≤ (u μ : ℤ) + w μ + (((L - 1) * c : ℕ) : ℤ) := by omega
    have e : ((((u μ : ℤ) + w μ + (((L - 1) * c : ℕ) : ℤ)).toNat : ℕ) : ZMod n) =
        (((u μ : ℤ) + w μ + (((L - 1) * c : ℕ) : ℤ) : ℤ) : ZMod n) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
    simp only [Pi.add_apply, Pi.sub_apply, natT_apply, intTorus_apply, e]
    push_cast
    ring

/-- **The union of the aligned `L c`-cubes containing a set of one cell is the neighbourhood of the
cell.**  Let `c ∣ n`, `B` aligned, and let the box `box q s` (`s > 0`) lie in the cell `box B c`.
The aligned cubes `box b (L c)` containing `box q s` are exactly those containing the cell, and
their union is `cellNbhd L c B`. -/
theorem iUnion_cubes_eq_cellNbhd [NeZero n] {L c s : ℕ} (hc : c ∣ n) (hc0 : 0 < c) (hL : 1 ≤ L)
    {B q : Torus d n} (hB : Aligned c B) (hs : 0 < s) (hq : box q s ⊆ box B c) :
    (⋃ b ∈ {b : Torus d n | Aligned c b ∧ box q s ⊆ box b (L * c)}, box b (L * c)) =
      cellNbhd L c B := by
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨b, ⟨hb, hqb⟩, hyb⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨v, hv, hqv⟩ := hqb (mem_box_self q hs)
    have hBq : cbase c q = B := cbase_eq_of_mem_box hc hB (hq (mem_box_self q hs))
    rw [hqv, cbase_add hc hb] at hBq
    obtain ⟨w, hw, rfl⟩ := hyb
    have hv'le : ∀ μ, v μ - v μ % c ≤ (L - 1) * c := by
      intro μ
      have h1 : v μ - v μ % c = c * (v μ / c) := by
        have := Nat.div_add_mod (v μ) c; omega
      have h2 : v μ / c < L := by
        rw [Nat.div_lt_iff_lt_mul hc0]; exact hv μ
      rw [h1]
      calc c * (v μ / c) ≤ c * (L - 1) := Nat.mul_le_mul_left _ (by omega)
        _ = (L - 1) * c := Nat.mul_comm _ _
    refine ⟨fun μ => (L - 1) * c - (v μ - v μ % c) + w μ, fun μ => ?_, ?_⟩
    · have h1 := hw μ
      have h2 := hv'le μ
      show (L - 1) * c - (v μ - v μ % c) + w μ < (L - 1) * c + L * c
      omega
    · rw [← hBq]
      funext μ
      simp only [Pi.add_apply, Pi.sub_apply, natT_apply]
      rw [Nat.cast_add, Nat.cast_sub (hv'le μ)]
      ring
  · rintro y ⟨t, ht, rfl⟩
    set B' : Torus d n := B - natT fun _ => (L - 1) * c with hB'def
    have hB' : Aligned c B' := aligned_sub_natT hc hB (fun _ => Nat.mul_mod_left _ _)
    set σ : Fin d → ℕ := fun μ => min (t μ / c) (L - 1) with hσ
    have hσle : ∀ μ, σ μ ≤ L - 1 := fun μ => min_le_right _ _
    have hσt : ∀ μ, σ μ * c ≤ t μ := fun μ =>
      (Nat.mul_le_mul_right c (min_le_left _ _)).trans (Nat.div_mul_le_self _ _)
    set b : Torus d n := B' + natT fun μ => σ μ * c with hbdef
    have hb : Aligned c b := aligned_add_natT hc hB' (fun μ => Nat.mul_mod_left _ _)
    have hBb : B = b + natT fun μ => (L - 1 - σ μ) * c := by
      funext μ
      have h1 : (L - 1) * c = σ μ * c + (L - 1 - σ μ) * c := by
        rw [← Nat.add_mul]; congr 1; have := hσle μ; omega
      have h2 : (((L - 1) * c : ℕ) : ZMod n) =
          ((σ μ * c : ℕ) : ZMod n) + (((L - 1 - σ μ) * c : ℕ) : ZMod n) := by
        rw [← Nat.cast_add, ← h1]
      simp only [hbdef, hB'def, Pi.add_apply, Pi.sub_apply, natT_apply, h2]
      ring
    refine Set.mem_iUnion₂.2 ⟨b, ⟨hb, ?_⟩, ?_⟩
    · refine hq.trans ?_
      rw [hBb]
      refine box_add_subset b _ (fun μ => ?_)
      calc (L - 1 - σ μ) * c + c = (L - 1 - σ μ + 1) * c := by rw [Nat.succ_mul]
        _ ≤ L * c := Nat.mul_le_mul_right _ (by have := hσle μ; omega)
    · refine ⟨fun μ => t μ - σ μ * c, fun μ => ?_, ?_⟩
      · have h1 := ht μ
        have h2 := hσt μ
        by_cases h : t μ / c ≤ L - 1
        · have e : σ μ = t μ / c := min_eq_left h
          have h3 : t μ - σ μ * c = t μ % c := by
            rw [e]; have := Nat.div_add_mod (t μ) c
            have h4 : t μ / c * c = c * (t μ / c) := Nat.mul_comm _ _
            omega
          have h5 : t μ % c < c := Nat.mod_lt _ hc0
          have h6 : c ≤ L * c := Nat.le_mul_of_pos_left c hL
          show t μ - σ μ * c < L * c
          omega
        · have e : σ μ = L - 1 := min_eq_right (by omega)
          have h6 : 0 < L * c := Nat.mul_pos (by omega) hc0
          show t μ - σ μ * c < L * c
          rw [e]; omega
      · funext μ
        simp only [hbdef, Pi.add_apply, natT_apply]
        rw [Nat.cast_sub (hσt μ)]
        ring

/-- A box whose side is at least the side of the torus is the whole torus. -/
theorem box_eq_univ_of_le [NeZero n] (b : Torus d n) {s : ℕ} (h : n ≤ s) : box b s = Set.univ := by
  refine Set.eq_univ_of_forall fun x =>
    ⟨fun μ => ((x - b) μ).val, fun μ => lt_of_lt_of_le (ZMod.val_lt _) h, ?_⟩
  funext μ
  simp [natT_apply]

open Classical in
/-- A box of side `s` has at most `s ^ d` sites. -/
theorem card_box_le [NeZero n] (b : Torus d n) (s : ℕ) :
    (Finset.univ.filter fun y : Torus d n => y ∈ box b s).card ≤ s ^ d := by
  have hsub : (Finset.univ.filter fun y : Torus d n => y ∈ box b s) ⊆
      (Fintype.piFinset fun _ : Fin d => Finset.range s).image
        (fun w : Fin d → ℕ => b + natT w) := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := (Finset.mem_filter.1 hy).2
    exact Finset.mem_image.2 ⟨w, Fintype.mem_piFinset.2 fun μ => Finset.mem_range.2 (hw μ), rfl⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Fintype.piFinset fun _ : Fin d => Finset.range s).card := Finset.card_image_le
    _ = s ^ d := by simp

end Arith

/-! ### Boxes of the cover and integer shifts -/

section Shift

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

/-- Two points of periodic boxes about the same centre differ by an integer vector bounded by the
sum of the half-widths. -/
theorem exists_int_of_inBox {j : ℕ} {y0 x y : CTorus d L N₁ m₁ K} {R R' : ℝ}
    (hx : InBox m₁ j y0 R x) (hy : InBox m₁ j y0 R' y) :
    ∃ w : Fin d → ℤ, y = x + (intTorus w : CTorus d L N₁ m₁ K) ∧ ∀ μ, |(w μ : ℝ)| < R + R' := by
  choose p hp using hx
  choose p' hp' using hy
  have hS0 : ((((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) = 0 := by
    rw [Int.cast_natCast]; exact ZMod.natCast_self _
  refine ⟨fun μ => ((y μ).val : ℤ) + p' μ * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ) -
    (((x μ).val : ℤ) + p μ * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ)), ?_, fun μ => ?_⟩
  · funext μ
    simp only [Pi.add_apply, intTorus_apply, Int.cast_sub, Int.cast_add, Int.cast_mul, hS0,
      mul_zero, add_zero, Int.cast_natCast, ZMod.natCast_zmod_val]
    ring
  · have h1 := abs_lt.1 (hp μ)
    have h2 := abs_lt.1 (hp' μ)
    rw [abs_lt]
    push_cast at h1 h2 ⊢
    constructor <;> linarith

omit [NeZero N₁] [NeZero L] in
/-- **The margin arithmetic.**  For `L ≥ 3`, `4 L² ≤ L^{m₁}` and `m₀ ≥ 1`: the half-width of a
thickened interaction cube of the top layer, plus the half-width `3/2 M` of the support of a
partition function, plus one cube side `M = L^{K+m₁}`, is at most `L - 1` cells of `π_K`. -/
theorem hatRad_add_le {m₀ : ℕ} (hL : 3 ≤ L) (hM : 4 * L ^ 2 ≤ L ^ m₁) (hm₀ : 1 ≤ m₀) (K : ℕ) :
    hatRad L m₁ K + 3 / 2 * (L : ℝ) ^ (K + m₁) + (L : ℝ) ^ (K + m₁) ≤
      (((L - 1) * cellSide L m₀ m₁ K : ℕ) : ℝ) := by
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hM' : (4 : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ m₁ := by exact_mod_cast hM
  have hK0 : (0 : ℝ) < (L : ℝ) ^ K := by positivity
  have hMK : (L : ℝ) ^ (K + m₁) = (L : ℝ) ^ K * (L : ℝ) ^ m₁ := pow_add _ _ _
  have hc : ((cellSide L m₀ m₁ K : ℕ) : ℝ) = (L : ℝ) ^ m₀ * (L : ℝ) ^ (K + m₁) := by
    unfold cellSide
    push_cast
    rw [← pow_add]
    congr 1
    omega
  have hm : (L : ℝ) ≤ (L : ℝ) ^ m₀ := by
    calc (L : ℝ) = (L : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (L : ℝ) ^ m₀ := pow_le_pow_right₀ (by linarith) hm₀
  have hL1 : (((L - 1 : ℕ)) : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [Nat.cast_mul, hL1, hc]
  unfold hatRad
  have hMpos : 0 < (L : ℝ) ^ (K + m₁) := by positivity
  have h3 : 3 * (L : ℝ) ^ 2 * (L : ℝ) ^ K ≤ 3 / 4 * (L : ℝ) ^ (K + m₁) := by
    rw [hMK]; nlinarith
  have h4 : 3 * (L : ℝ) ^ (K + m₁) ≤ (L : ℝ) ^ m₀ * (L : ℝ) ^ (K + m₁) := by nlinarith
  have h5 : 6 * (L : ℝ) ^ (K + m₁) ≤ ((L : ℝ) - 1) * ((L : ℝ) ^ m₀ * (L : ℝ) ^ (K + m₁)) := by
    have h2 : (2 : ℝ) ≤ (L : ℝ) - 1 := by linarith
    nlinarith
  linarith

end Shift

/-! ### The local cover of a whole-lattice set of the top level -/

section Level

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- A whole-lattice generating set of the top level `K` is a union of `π'_K`-cubes. -/
theorem layerUnion_of_isLevel (hG : IsLevel G K) (m₀ : ℕ) : LayerUnion G m₀ := by
  intro n hn1 hnK z hz
  have hzK : z ∈ G.layer K := hG.mem_layer z
  have hn : n = K := by
    by_contra hne
    exact G.layer_disjoint hn1 hnK (by omega) le_rfl hne hz hzK
  rw [hn]
  exact ⟨cbase (cellSide L m₀ m₁ K) z, aligned_cbase z,
    box_mono _ (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne L)))
      (mem_box_cbase (cellSide_pos m₀ m₁ K) z),
    fun x _ => Finset.mem_coe.2 (hG.mem_layer x)⟩

namespace LocalCover

/-- The base of the `π_K`-cell (side `L^{K+m₀+m₁}`) of the site `x`. -/
def corner (m₀ : ℕ) (x : CTorus d L N₁ m₁ K) : CTorus d L N₁ m₁ K :=
  cbase (cellSide L m₀ m₁ K) x

/-- **The localization cube `X` of the site `x`**: the `π'_j`-cube at the corner of the `π_K`-cell
of `x`. -/
def cube (m₀ j : ℕ) (x : CTorus d L N₁ m₁ K) : Set (CTorus d L N₁ m₁ K) :=
  box (corner m₀ x) (L * cellSide L m₀ m₁ j)

/-- **The chosen family `𝒦_X`**: the single cube `X`. -/
def fam (m₀ : ℕ) (x : CTorus d L N₁ m₁ K) : Set (CTorus d L N₁ m₁ K) := {corner m₀ x}

/-- **The region `X₁` of the site `x`**: the `2L - 1` cells of `π_K` per direction around the
cell of `x` (a set of fixed size in units of the cover; the whole torus only if the torus has at
most `2L - 1` cells per direction). -/
def nbhd (m₀ : ℕ) (x : CTorus d L N₁ m₁ K) : Set (CTorus d L N₁ m₁ K) :=
  cellNbhd L (cellSide L m₀ m₁ K) (corner m₀ x)

open Classical in
/-- The region `X₁` as a finite set. -/
noncomputable def nbhdF (m₀ : ℕ) (x : CTorus d L N₁ m₁ K) : Finset (CTorus d L N₁ m₁ K) :=
  Finset.univ.filter fun y => y ∈ nbhd m₀ x

theorem coe_nbhdF (m₀ : ℕ) (x : CTorus d L N₁ m₁ K) :
    (↑(nbhdF m₀ x) : Set (CTorus d L N₁ m₁ K)) = nbhd m₀ x := by
  ext y
  simp [nbhdF]

theorem aligned_corner (m₀ : ℕ) (x : CTorus d L N₁ m₁ K) :
    Aligned (cellSide L m₀ m₁ K) (corner m₀ x) := aligned_cbase x

theorem aligned_corner_of_le (m₀ : ℕ) {j : ℕ} (hj : j ≤ K) (x : CTorus d L N₁ m₁ K) :
    Aligned (cellSide L m₀ m₁ j) (corner m₀ x) := fun μ =>
  Nat.mod_eq_zero_of_dvd (dvd_trans (pow_dvd_pow L (by omega))
    (Nat.dvd_of_mod_eq_zero (aligned_corner m₀ x μ)))

/-- The site lies in its cell. -/
theorem mem_cell (m₀ : ℕ) (x : CTorus d L N₁ m₁ K) :
    x ∈ box (corner m₀ x) (cellSide L m₀ m₁ K) := mem_box_cbase (cellSide_pos m₀ m₁ K) x

omit [NeZero N₁] in
/-- The cube `X` lies in the cell of the site (`j < K`). -/
theorem cube_subset_cell (m₀ : ℕ) {j : ℕ} (hj : j + 1 ≤ K) (x : CTorus d L N₁ m₁ K) :
    cube m₀ j x ⊆ box (corner m₀ x) (cellSide L m₀ m₁ K) :=
  box_mono _ (cellSide_succ_le (Nat.pos_of_ne_zero (NeZero.ne L)) hj m₀ m₁)

/-- The site lies in its region `X₁`. -/
theorem mem_nbhdF_self (m₀ : ℕ) (x : CTorus d L N₁ m₁ K) : x ∈ nbhdF m₀ x := by
  have h := cell_subset_cellNbhd (Nat.pos_of_ne_zero (NeZero.ne L)) _ _ (mem_cell m₀ x)
  rw [← Finset.mem_coe, coe_nbhdF]
  exact h

/-- **The region `X₁` has a size independent of the torus**: at most
`((2L - 1) L^{K+m₀+m₁})^d` sites, that is `((2L - 1) L^{m₀})^d` cubes of the cover. -/
theorem card_nbhdF_le (m₀ : ℕ) (x : CTorus d L N₁ m₁ K) :
    (nbhdF m₀ x).card ≤ ((L - 1) * cellSide L m₀ m₁ K + L * cellSide L m₀ m₁ K) ^ d := by
  classical
  exact card_box_le _ _

/-- **Small tori**: if the torus has at most `2L - 1` cells of `π_K` per direction
(`N₁ ≤ (2L - 1) L^{m₀}`), the region `X₁` is the whole torus (this is the case `N₁ = 9`,
`L = 3`, `m₀ = 1` of the landed witness). -/
theorem nbhd_eq_univ {m₀ : ℕ} (h : N₁ ≤ (2 * L - 1) * L ^ m₀) (x : CTorus d L N₁ m₁ K) :
    nbhd m₀ x = Set.univ := by
  have hL : 1 ≤ L := Nat.pos_of_ne_zero (NeZero.ne L)
  refine box_eq_univ_of_le _ ?_
  calc N₁ * L ^ m₁ * L ^ K ≤ (2 * L - 1) * L ^ m₀ * L ^ m₁ * L ^ K :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)
    _ = (L - 1) * cellSide L m₀ m₁ K + L * cellSide L m₀ m₁ K := by
        unfold cellSide
        rw [← Nat.add_mul, show L - 1 + L = 2 * L - 1 by omega, pow_add, pow_add]
        ring

/-- **`CovSetup` for the local cube**, on every torus: `X` is one `π'_j`-cube (`j < K`), the chosen
family is `{X}`, and `X` lies in a `π'_K`-cube of the top layer. -/
theorem covSetup {m₀ : ℕ} (hG : IsLevel G K) (hN : L ^ m₀ ∣ N₁) {j : ℕ} (hj : j + 1 ≤ K)
    (x : CTorus d L N₁ m₁ K) : CovSetup G m₀ j (cube m₀ j x) (fam m₀ x) where
  hU := layerUnion_of_isLevel hG m₀
  hN := hN
  hjK := hj
  chosen := Balaban.Fluctuation.chosenOne_box (corner m₀ x) (aligned_corner_of_le m₀ (by omega) x)
  nest := by
    intro b hb
    rw [Set.mem_singleton_iff.1 hb]
    exact ⟨corner m₀ x, aligned_corner m₀ x,
      box_mono _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right
        (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega))),
      fun y _ => Finset.mem_coe.2 (hG.mem_layer y)⟩

/-- **The region `X₁` of the local cube is the neighbourhood of the cell**:
`X₁ = ⋃ 𝒬₀` is the box of `2L - 1` cells of `π_K` per direction around the cell of `x`.  No
condition on the size of the torus: if the torus has at most `2L - 1` cells per direction this box
is the whole torus. -/
theorem X1_eq {m₀ : ℕ} (hG : IsLevel G K) (hN : L ^ m₀ ∣ N₁) {j : ℕ} (hj : j + 1 ≤ K)
    (x : CTorus d L N₁ m₁ K) : X1 G m₀ j (fam m₀ x) = nbhd m₀ x := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hc := cellSide_dvd (L := L) (m₁ := m₁) (K := K) hN (le_refl K)
  have hQ : Q0 G m₀ j (fam m₀ x) = {b | Aligned (cellSide L m₀ m₁ K) b ∧
      box (corner m₀ x) (L * cellSide L m₀ m₁ j) ⊆ box b (L * cellSide L m₀ m₁ K)} := by
    ext b
    simp only [Q0, fam, Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_eq_left]
    constructor
    · rintro ⟨h1, -, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨h1, fun y _ => Finset.mem_coe.2 (hG.mem_layer y), h3⟩
  unfold X1
  rw [hQ]
  exact iUnion_cubes_eq_cellNbhd hc (cellSide_pos m₀ m₁ K) hL (aligned_corner m₀ x)
    (Nat.mul_pos hL (cellSide_pos m₀ m₁ j)) (cube_subset_cell m₀ hj x)

theorem coe_nbhdF_eq_X1 {m₀ : ℕ} (hG : IsLevel G K) (hN : L ^ m₀ ∣ N₁) {j : ℕ} (hj : j + 1 ≤ K)
    (x : CTorus d L N₁ m₁ K) :
    (↑(nbhdF m₀ x) : Set (CTorus d L N₁ m₁ K)) = X1 G m₀ j (fam m₀ x) := by
  rw [coe_nbhdF, X1_eq hG hN hj]

/-- **The optimal structure of the local cube**: the single point `corner`, with no bond. -/
theorem hopt (m₀ : ℕ) {j : ℕ} (hj : j ≤ K) (x : CTorus d L N₁ m₁ K) :
    ∃ (W₀ : Finset (CTorus d L N₁ m₁ K)) (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ cube m₀ j x) ∧ MeetsOne m₀ j (fam m₀ x) W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j (cube m₀ j x) :=
  Balaban.Fluctuation.hopt_box (corner m₀ x) (aligned_corner_of_le m₀ hj x)

/-- **The covering size of the local cube is `0`.** -/
theorem treeLen_eq_zero (m₀ : ℕ) {j : ℕ} (hj : j ≤ K) (x : CTorus d L N₁ m₁ K) :
    treeLenCovOne m₀ j (cube m₀ j x) = 0 :=
  Balaban.Fluctuation.treeLenCovOne_box (corner m₀ x) (aligned_corner_of_le m₀ hj x)

/-- **`BlockMargin` for the local region.**  Let `G` be a whole-lattice set of the top level with
`DGSetting`, and `m₀ ≥ 1`.  Every set `Zα` of sites contained in one `π_K`-cell has the margin
against the cover in the region `X₁` of that cell: each site lies in an interaction cube whose
thickened cube, and all cover cubes meeting it, lie in `X₁`. -/
theorem blockMargin {a : ℕ → ℝ} {ν : ℝ} (S : DGSetting G a ν) (hG : IsLevel G K) {m₀ : ℕ}
    (hm₀ : 1 ≤ m₀) (x₀ : CTorus d L N₁ m₁ K) {Zα : Set (CTorus d L N₁ m₁ K)}
    (hZ : Zα ⊆ box (corner m₀ x₀) (cellSide L m₀ m₁ K)) :
    BlockMargin G (nbhdF m₀ x₀) Zα := by
  classical
  intro x hx hxΩ
  have hL1 : 1 ≤ L := by have := S.hL; omega
  have hs : ∑ q ∈ cubeIdx G, chi G q x = 1 := (Dec2.coverGeom_self S).sum_chi x hxΩ
  obtain ⟨q, hq, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := cubeIdx G)
    (f := fun q => chi G q x) (by rw [hs]; norm_num)
  have hin := inBox_of_chi_ne_zero hne
  have hqK : q.1 = K := level_eq_of_mem_cubeIdx hG hq
  have hnum := hatRad_add_le (m₀ := m₀) S.hL S.hM hm₀ K
  have hMpos : (0 : ℝ) < (L : ℝ) ^ (K + m₁) := by
    have : (0 : ℝ) < L := by exact_mod_cast hL1
    positivity
  have key : ∀ (y : CTorus d L N₁ m₁ K) (R : ℝ), InBox m₁ q.1 q.2 R y →
      R ≤ hatRad L m₁ K + (L : ℝ) ^ (K + m₁) → y ∈ nbhdF m₀ x₀ := by
    intro y R hy hR
    obtain ⟨w, rfl, hw⟩ := exists_int_of_inBox hin hy
    rw [← Finset.mem_coe, coe_nbhdF]
    refine add_intTorus_mem_cellNbhd hL1 (hZ hx) w (fun μ => ?_)
    have h1 := hw μ
    rw [hqK] at h1
    have h2 : |(w μ : ℝ)| < (((L - 1) * cellSide L m₀ m₁ K : ℕ) : ℝ) := by linarith
    have h3 : ((|w μ| : ℤ) : ℝ) < (((L - 1) * cellSide L m₀ m₁ K : ℕ) : ℝ) := by
      rw [Int.cast_abs]; exact h2
    have h4 : |w μ| < (((L - 1) * cellSide L m₀ m₁ K : ℕ) : ℤ) := by exact_mod_cast h3
    exact h4.le
  refine ⟨q, hq, mem_intBox.2 (hin.mono ?_), fun P hP hpar => ?_, fun y hy => ?_⟩
  · have : (0 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := by positivity
    linarith
  · unfold DecCover.parCubes at hpar
    rw [Finset.mem_filter] at hpar
    apply hpar.2
    intro y hy
    obtain ⟨hPi, y', hy', hbox⟩ := (coverOf G).mem_Qset.1 hP
    have hPK : P.1 = K := level_eq_of_mem_cubeIdx hG hPi
    have hsc : SameCell (L ^ (P.1 + m₁)) y y' := (mem_cubeP.1 hy).trans hy'.symm
    obtain ⟨w, rfl, hw⟩ := exists_int_of_sameCell (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _) hsc
    refine key _ _ (hbox.add_int w (B := (L : ℝ) ^ (K + m₁)) (fun μ => ?_)) ?_
    · have := hw μ
      rw [hPK] at this
      push_cast at this
      exact this.le
    · rw [hqK]
  · refine key y _ (mem_boxSet.1 hy) ?_
    rw [hqK]
    linarith

end LocalCover

end Level

/-! ### Blocks and read sites -/

section Blocks

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}

namespace LocalCover

/-- A site of the block `B_{n+1}(z)`: its corner. -/
def blockSite (n : ℕ) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) : CTorus d L N₁ m₁ K :=
  fun μ => ((L ^ (n + 1) * (z μ).val : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K))

theorem jBlock_blockSite {n : ℕ} (hn : n + 1 ≤ K)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) :
    jBlock d L (N₁ * L ^ m₁) K (n + 1) (blockSite n z) = z := by
  funext μ
  have hL : 0 < L ^ (n + 1) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hside := side_eq (N₀ := N₁ * L ^ m₁) (L := L) hn
  have hlt : L ^ (n + 1) * (z μ).val < (N₁ * L ^ m₁) * L ^ K := by
    rw [hside]
    exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) hL
  have hval : (blockSite n z μ).val = L ^ (n + 1) * (z μ).val := by
    unfold blockSite
    exact ZMod.val_natCast_of_lt hlt
  unfold jBlock
  rw [blockMap_apply]
  unfold blockCoord
  rw [hval, Nat.mul_div_cancel_left _ hL, ZMod.natCast_zmod_val]

theorem blockSite_mem {n : ℕ} (hn : n + 1 ≤ K) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) :
    blockSite n z ∈ blockSites d L N₁ m₁ K n z := by
  simp [blockSites, jBlock_blockSite hn z]

/-- A block `B_{n+1}(z)` (`n < K`) lies in one `π_K`-cell. -/
theorem blockSites_subset_cell (m₀ : ℕ) {n : ℕ} (hn : n + 1 ≤ K)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) :
    (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)) ⊆
      box (corner m₀ (blockSite n z)) (cellSide L m₀ m₁ K) := by
  intro x hx
  have hx' : jBlock d L (N₁ * L ^ m₁) K (n + 1) x = z := by
    simpa [blockSites] using hx
  have hsc : SameCell (L ^ (n + 1)) x (blockSite n z) :=
    sameCell_of_jBlock_eq hn (hx'.trans (jBlock_blockSite hn z).symm)
  have hsc' : SameCell (cellSide L m₀ m₁ K) x (blockSite n z) :=
    SameCell.mono (pow_dvd_pow L (by omega)) hsc
  have h := (sameCell_iff_cbase_eq (cellSide_pos (L := L) m₀ m₁ K)).1 hsc'
  unfold corner
  rw [← h]
  exact mem_box_cbase (cellSide_pos m₀ m₁ K) x

/-- The block lies in the region `X₁` of its cell. -/
theorem blockSites_subset_nbhdF (m₀ : ℕ) {n : ℕ} (hn : n + 1 ≤ K)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) :
    (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)) ⊆ ↑(nbhdF m₀ (blockSite n z)) := by
  rw [coe_nbhdF]
  exact (blockSites_subset_cell m₀ hn z).trans
    (cell_subset_cellNbhd (Nat.pos_of_ne_zero (NeZero.ne L)) _ _)

/-- **The sites read by the block energy lie in the region `X₁` of the block** (`L ≥ 2`): the
block, its right neighbours, and the `n`-blocks through the block. -/
theorem readSites_subset_nbhdF (Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm) (hL : 2 ≤ L) (m₀ : ℕ)
    {n : ℕ} (hn : n + 1 ≤ K) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) :
    readSites Hm n z ⊆ ↑(nbhdF m₀ (blockSite n z)) := by
  have hL1 : 1 ≤ L := by omega
  rw [coe_nbhdF]
  rintro y ⟨x, hx, hy⟩
  have hxc := blockSites_subset_cell m₀ hn z (Finset.mem_coe.2 hx)
  rcases hy with rfl | ⟨μ, rfl⟩ | hy
  · exact cell_subset_cellNbhd hL1 _ _ hxc
  · have hw : (x + Pi.single μ 1 : CTorus d L N₁ m₁ K) =
        x + (intTorus (Pi.single μ (1 : ℤ)) : CTorus d L N₁ m₁ K) := by
      congr 1
      funext ν'
      by_cases h' : ν' = μ <;> simp [intTorus_apply, h']
    rw [hw]
    refine add_intTorus_mem_cellNbhd hL1 hxc _ (fun ν' => ?_)
    have hc : 1 ≤ (L - 1) * cellSide L m₀ m₁ K :=
      Nat.mul_pos (by omega) (cellSide_pos m₀ m₁ K)
    have h1 : |(Pi.single μ (1 : ℤ) : Fin d → ℤ) ν'| ≤ 1 := by
      by_cases h' : ν' = μ <;> simp [h']
    have h2 : (1 : ℤ) ≤ (((L - 1) * cellSide L m₀ m₁ K : ℕ) : ℤ) := by exact_mod_cast hc
    exact h1.trans h2
  · have hsc : SameCell (L ^ n) y x := sameCell_of_jBlock_eq (by omega) (Hm.mem_blk.1 hy)
    have hsc' : SameCell (cellSide L m₀ m₁ K) y x :=
      SameCell.mono (pow_dvd_pow L (by omega)) hsc
    have h := (sameCell_iff_cbase_eq (cellSide_pos (L := L) m₀ m₁ K)).1 hsc'
    have hN : cellSide L m₀ m₁ K ∣ cellSide L m₀ m₁ K := dvd_rfl
    refine cell_subset_cellNbhd hL1 _ _ ?_
    have hyc : y ∈ box (cbase (cellSide L m₀ m₁ K) y) (cellSide L m₀ m₁ K) :=
      mem_box_cbase (cellSide_pos m₀ m₁ K) y
    rw [h] at hyc
    have hxb : cbase (cellSide L m₀ m₁ K) x = corner m₀ (blockSite n z) := by
      have hsx : SameCell (cellSide L m₀ m₁ K) x (blockSite n z) := by
        have hx' : jBlock d L (N₁ * L ^ m₁) K (n + 1) x = z := by
          simpa [blockSites] using hx
        exact SameCell.mono (pow_dvd_pow L (by omega))
          (sameCell_of_jBlock_eq hn (hx'.trans (jBlock_blockSite hn z).symm))
      exact (sameCell_iff_cbase_eq (cellSide_pos (L := L) m₀ m₁ K)).1 hsx
    rw [hxb] at hyc
    exact hyc

/-- **The local cover of the pair of consecutive full levels, on every torus** (the cover
hypotheses of the localization engine for the potential part, block by block, and for the source
part, site by site).  Let `Gp` be a whole-lattice generating set of the top level `k + 1` of the
torus `CTorus d L N₁ m₁ (k + 1)` with `DGSetting`, `Hm` any generating set of that torus,
`m₀ ≥ 1` and `L^{m₀} ∣ N₁`.  For every block `B_{k+1}(z)`, with `x_z = blockSite k z`:

* `X = cube m₀ k x_z` is one `π'_k`-cube and `𝒦_X = {X}`: `CovSetup`;
* `X₁ = nbhdF m₀ x_z` is the `2L - 1` cells of `π_{k+1}` per direction around the cell of the block
  (`X1_eq`), and equals `X1 Gp m₀ k 𝒦_X`;
* the optimal structure exists and `d^cov_k(X) = 0`;
* the sites read by the block energy, and the block itself, lie in `X₁`;
* the block has the margin `BlockMargin` in `X₁`.

For every source site `s`, the same with `x = s.1`, and `s.1 ∈ X₁`.  No constant appears and
nothing depends on `k` or `N₁`: the cover scale `m₀` is the only parameter, and the region `X₁`
has at most `((2L - 1) L^{k+1+m₀+m₁})^d` sites (`card_nbhdF_le`). -/
theorem levelLocalCover {k N : ℕ} {a : ℕ → ℝ} {ν : ℝ}
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm) (S : DGSetting Gp a ν)
    (hG' : IsLevel Gp (k + 1)) {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁) :
    (∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      CovSetup Gp m₀ k (cube m₀ k (blockSite k z)) (fam m₀ (blockSite k z)) ∧
      (↑(nbhdF m₀ (blockSite k z)) : Set (CTorus d L N₁ m₁ (k + 1))) =
        X1 Gp m₀ k (fam m₀ (blockSite k z)) ∧
      (∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
        (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
        ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ cube m₀ k (blockSite k z)) ∧
          MeetsOne m₀ k (fam m₀ (blockSite k z)) W₀ ∧
          bondCost (scaleW L m₀ m₁ k) E₀ = treeLenCovOne m₀ k (cube m₀ k (blockSite k z))) ∧
      treeLenCovOne m₀ k (cube m₀ k (blockSite k z)) = 0 ∧
      readSites Hm k z ⊆ ↑(nbhdF m₀ (blockSite k z)) ∧
      BlockMargin Gp (nbhdF m₀ (blockSite k z))
        (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ∧
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
        ↑(nbhdF m₀ (blockSite k z))) ∧
    (∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N,
      CovSetup Gp m₀ k (cube m₀ k s.1) (fam m₀ s.1) ∧
      (↑(nbhdF m₀ s.1) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ k (fam m₀ s.1) ∧
      (∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
        (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
        ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ cube m₀ k s.1) ∧ MeetsOne m₀ k (fam m₀ s.1) W₀ ∧
          bondCost (scaleW L m₀ m₁ k) E₀ = treeLenCovOne m₀ k (cube m₀ k s.1)) ∧
      treeLenCovOne m₀ k (cube m₀ k s.1) = 0 ∧ s.1 ∈ nbhdF m₀ s.1) := by
  have hL2 : 2 ≤ L := by have := S.hL; omega
  refine ⟨fun z => ⟨covSetup hG' hN le_rfl _, coe_nbhdF_eq_X1 hG' hN le_rfl _,
    hopt m₀ (Nat.le_succ k) _, treeLen_eq_zero m₀ (Nat.le_succ k) _,
    readSites_subset_nbhdF Hm hL2 m₀ le_rfl z,
    blockMargin S hG' hm₀ _ (blockSites_subset_cell m₀ le_rfl z),
    blockSites_subset_nbhdF m₀ le_rfl z⟩,
    fun s => ⟨covSetup hG' hN le_rfl _, coe_nbhdF_eq_X1 hG' hN le_rfl _,
      hopt m₀ (Nat.le_succ k) _, treeLen_eq_zero m₀ (Nat.le_succ k) _, mem_nbhdF_self m₀ _⟩⟩

end LocalCover

end Blocks

end Balaban.Localization
