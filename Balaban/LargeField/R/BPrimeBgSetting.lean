/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatSetGeom
public import Balaban.Fluctuation.LevelLocalCover
public import Balaban.Fluctuation.LocalClassDensityFamilySetCast
public import Balaban.Localization.TreeLengthDiam
public import Balaban.Localization.P6PairCover
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The local chain `𝔹_j(X̂) ≺ 𝔹_{K-1}(Z) ≺ G'` of Theorem I-5 under a top set of level `K`

Theorem I-5 (`i5_background`) recomputes, for a term of a level-`j` polymer `X`, the background of a
top set `G'` (level `K`, the torus `CTorus d L N₁ m₁ K`) on a local set `𝔹_{K-1}(Z)` around `X̂` and
composes it on the generating set `𝔹_j(X̂)` of the term (ruling R13, `X̂ = hatSet m₀ j X`); its
hypotheses on the three sets are the structure `BgSetting`.  This file builds that structure for
every top set `G'` whose top layer `Ω_K(G')` contains the sites within `L a_K` of `X`
(`a_K = cellSide L m₀ m₁ K`), from conditions on the constants only.

The sets live on a finer cube torus (`N₁' L^{m₁'} = N₁ L^{m₁}`): `X̂'` is `X̂`, `Z'` the sites at
`𝒞_{K-1}`-cube-index distance `≤ 5 L` from `X̂'`, `Gk = castG (𝔹_{K-1}(Z'))`,
`Gj = castG (𝔹_j(X̂'))` (the generating set of a class polymer, `HatSpec.eq_castLocalB`),
`X₀ = dataSites Gk` and `X₁f = X1 G' m₀ j 𝒦_X`.

* `cell_subset_of_covSetup`: a set with a covering setup is a union of cells of `𝒟_j`;
* `X1_subset_X1_of_deep`: the cubes `𝒬₀` of a whole-lattice set are cubes of `G'` near `X`;
* `covSetup_toLevel`: a covering setup for `G'` is one for a whole-lattice set;
* `hatChain_near`: every data site of `Gk` is within `D + ⌊L/2⌋ a_j` of `X`;
* `bgSetting_hat`: the core;
* `bgSetting_hat_of_isLevel`: the instance of a whole-lattice top set (`IsLevel G' K`);
* `cubeAligned_levelGS`, `supSep_levelGS`, `dgSetting_levelGS`, `bgSetting_hat_levelGS`: the
  whole-torus top set `𝔹_K = levelGS K` of the class's Def-6 torus.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.GsSpec Balaban.Fluctuation Finset

section Geometry

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}

/-- **A set with a covering setup is a union of cells of `𝒟_j`**: the chosen `π'_j`-cubes are
aligned unions of cells contained in `X` and cover `X`. -/
theorem cell_subset_of_covSetup {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ j : ℕ}
    {X 𝒦X : Set (Localization.CTorus d L N₁ m₁ K)} (hcov : CovSetup Gp m₀ j X 𝒦X) :
    ∀ z ∈ X, Localization.box (cbase (cellSide L m₀ m₁ j) z) (cellSide L m₀ m₁ j) ⊆ X := by
  intro z hz
  obtain ⟨q, hq, hzq⟩ := hcov.chosen.2 z hz
  obtain ⟨hqa, hqX⟩ := hcov.chosen.1 q hq
  exact (cell_subset_cube (cellSide_dvd hcov.hN (by have := hcov.hjK; omega))
    (cellSide_pos m₀ m₁ j) hqa hzq).trans hqX

/-- **The cubes `𝒬₀` of a whole-lattice set are cubes of `G'` near `X`.**  Every cube of `𝒬₀`
contains a chosen cube of `X`, so it lies within the sup distance `L a_K` of a site of `X`; if
those sites lie in `Ω_K(G')`, the cube is one of the cubes `𝒬₀` of `G'`. -/
theorem X1_subset_X1_of_deep {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {Gl : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'} {m₀ j : ℕ}
    {X 𝒦X : Set (Localization.CTorus d L N₁ m₁ K)}
    (hch : ChosenOne m₀ j X 𝒦X)
    (hdeep : ∀ z w : Localization.CTorus d L N₁ m₁ K, w ∈ X → supDist z w ≤ L * cellSide L m₀ m₁ K →
      z ∈ Gp.Ω K) :
    X1 Gl m₀ j 𝒦X ⊆ X1 Gp m₀ j 𝒦X := by
  intro y hy
  obtain ⟨b, hb, hyb⟩ := Set.mem_iUnion₂.1 hy
  obtain ⟨hba, -, q, hq, hqb⟩ := hb
  refine Set.mem_iUnion₂.2 ⟨b, ⟨hba, ?_, q, hq, hqb⟩, hyb⟩
  intro z hz
  have hqq : q ∈ Localization.box q (L * cellSide L m₀ m₁ j) :=
    mem_box_self q (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ j))
  have hqX : q ∈ X := (hch.1 q hq).2 hqq
  have hzq : supDist z q ≤ L * cellSide L m₀ m₁ K :=
    (Localization.supDist_le_of_mem_box hz (hqb hqq)).trans (Nat.sub_le _ _)
  rw [Finset.mem_coe, GeneratingSet.mem_layer, Gp.top]
  exact ⟨hdeep z q hqX hzq, Finset.notMem_empty z⟩

/-- **A covering setup for a top set is one for a whole-lattice set** of the same level. -/
theorem covSetup_toLevel {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {Gl : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'} {m₀ j : ℕ}
    {X 𝒦X : Set (Localization.CTorus d L N₁ m₁ K)}
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hlev : IsLevel Gl K) : CovSetup Gl m₀ j X 𝒦X where
  hU := layerUnion_of_isLevel hlev m₀
  hN := hcov.hN
  hjK := hcov.hjK
  chosen := hcov.chosen
  nest := fun b hb => by
    obtain ⟨b', h1, h2, -⟩ := hcov.nest b hb
    exact ⟨b', h1, h2, fun z _ => Finset.mem_coe.2 (hlev.mem_layer z)⟩

end Geometry

section Chain

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ : ℝ}

/-- **The data sites of `Gk = castG (𝔹_{k'}(Z'))` are near `X`**: every data site is within the sup
distance `D = (5 L + 1) L^{m₁'} L^{k'} + 11 L^{m₁'} L^{k'} + 1` of a site of `X̂`, which is within
`⌊L/2⌋ a_j` of a site of `X` (`X` a union of cells of `𝒟_j`). -/
theorem hatChain_near {N₁' m₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hL : 2 ≤ L)
    {k' : ℕ} (hk' : k' ≤ K) {m₀ j : ℕ} {X : Set (Localization.CTorus d L N₁ m₁ K)}
    (hcell : ∀ z ∈ X, Localization.box (cbase (cellSide L m₀ m₁ j) z) (cellSide L m₀ m₁ j) ⊆ X)
    {Xh Z' : Set (Localization.CTorus d L N₁' m₁' K)}
    (hXh : ∀ x' : Localization.CTorus d L N₁' m₁' K,
      x' ∈ Xh ↔ (torusCast x' : Localization.CTorus d L N₁ m₁ K) ∈ hatSet m₀ j X)
    (hZ' : ∀ z' : Localization.CTorus d L N₁' m₁' K, z' ∈ Z' ↔ ∃ y' ∈ Xh,
      supDist (fineCubeIdx (L ^ m₁') N₁' L K k' (torusCast z' : Torus d (L ^ m₁' * N₁' * L ^ K)))
        (fineCubeIdx (L ^ m₁') N₁' L K k' (torusCast y' : Torus d (L ^ m₁' * N₁' * L ^ K))) ≤
        5 * L)
    (hs₁ : ϱ₁ ≤ minSep L (L ^ m₁')) :
    ∀ x ∈ dataSites (castG hc (localB k' hk' Z' hs₁)),
      ∃ z w : Localization.CTorus d L N₁ m₁ K, w ∈ X ∧
      supDist x z ≤ (5 * L + 1) * (L ^ m₁' * L ^ k') + (11 * L ^ m₁' * L ^ k' + 1) ∧
      supDist z w ≤ L / 2 * cellSide L m₀ m₁ j := by
  intro x hx
  have hceq : N₁' * L ^ m₁' * L ^ K = N₁ * L ^ m₁ * L ^ K := by rw [hc]
  obtain ⟨y', hy'Z, hxy'⟩ := dataSites_castG_range hc (localB k' hk' Z' hs₁) Z'
    (11 * L ^ m₁' * L ^ k' + 1) (fun x hx => localB_dataSites_range hL hx) hx
  obtain ⟨w', hw'Y, hz'w'⟩ := Zset_dist_le hk' hZ' y' hy'Z
  obtain ⟨w, hwX, hww⟩ := exists_near_of_mem_hatSet hcell _ ((hXh w').1 hw'Y)
  refine ⟨torusCast w', w, hwX, ?_, hww⟩
  refine (supDist_triangle _ (torusCast y' : Localization.CTorus d L N₁ m₁ K) _).trans ?_
  rw [supDist_torusCast_val hceq, add_comm]
  exact Nat.add_le_add hz'w' hxy'

/-- **`BgSetting` for the local chain `𝔹_j(X̂) ≺ 𝔹_{K-1}(Z) ≺ G'` under a top set `G'` of level
`K`** (Theorem I-5 with ruling R13).  Let `G'` be a generating set of the torus
`CTorus d L N₁ m₁ K`, `K = k' + 1`, with the standing hypotheses `DGSetting` and the bounds `BgHyp`
of the background, `(X, 𝒦_X)` a covering setup of index `m₀` at a level `1 ≤ j ≤ k'`, and assume
that `Ω_K(G')` contains the sites within the sup distance `L a_K` of `X`.  On the finer cube torus
(`N₁' L^{m₁'} = N₁ L^{m₁}`, `L^{m₁'} ≤ L^{m₁} c₁`) let `X̂'` be `X̂ = hatSet m₀ j X` and `Z'` the
sites at `𝒞_{k'}`-cube-index distance `≤ 5 L` from `X̂'`.  Then, for indices
`bgR0 ≤ ϱ₁, ϱ₂ ≤ 5 L^{m₁'+1}`, the numerical conditions of the chain and the margin
`(5 L + 13) c₁ + ⌊L/2⌋ L^{m₀} + r₀ L ≤ (L - 2) L^{m₀+1}` (that of the class chain,
`NewLevelTies.hat_margin`), the structure `BgSetting` holds for `Gk = castG (𝔹_{k'}(Z'))`,
`Gj = castG (𝔹_j(X̂'))`, `X₀ = dataSites Gk` and every `X₁f` with `X₁f = X1 G' m₀ j 𝒦_X`. -/
theorem bgSetting_hat {N₁' m₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) {k' : ℕ}
    (hkK : k' + 1 = K) {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a₁ ν c BG κ r₀ eps δ₃ : ℝ}
    (hS : DecSpecs d L c BG) (Sp : DGSetting Gp (compWeight L a₁) ν) (ha₁ : 0 < a₁)
    (HBp : BgHyp d L K ϱ (compWeight L a₁) ν) (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (num : ChainNum d L N m₁ BG κ r₀ eps δ₃)
    (hr : r₀ * (L : ℝ) ^ m₁ ≤ ϱ - 1) (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀)
    (hϱ₁ : bgR0 d L ≤ ϱ₁) (hϱ₂ : bgR0 d L ≤ ϱ₂) (hs₁ : ϱ₁ ≤ minSep L (L ^ m₁'))
    (hs₂ : ϱ₂ ≤ minSep L (L ^ m₁')) {m₀ c₁ : ℕ} (hm1 : L ^ m₁' ≤ L ^ m₁ * c₁)
    (hm : (((5 * L + 13) * c₁ + L / 2 * L ^ m₀ : ℕ) : ℝ) + r₀ * L ≤
      (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (m₀ + 1))
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k') {X 𝒦X : Set (Localization.CTorus d L N₁ m₁ K)}
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hdeep : ∀ z w : Localization.CTorus d L N₁ m₁ K, w ∈ X → supDist z w ≤ L * cellSide L m₀ m₁ K →
      z ∈ Gp.Ω K)
    {Xh Z' : Set (Localization.CTorus d L N₁' m₁' K)}
    (hXh : ∀ x' : Localization.CTorus d L N₁' m₁' K,
      x' ∈ Xh ↔ (torusCast x' : Localization.CTorus d L N₁ m₁ K) ∈ hatSet m₀ j X)
    (hZ' : ∀ z' : Localization.CTorus d L N₁' m₁' K, z' ∈ Z' ↔ ∃ y' ∈ Xh,
      supDist (fineCubeIdx (L ^ m₁') N₁' L K k' (torusCast z' : Torus d (L ^ m₁' * N₁' * L ^ K)))
        (fineCubeIdx (L ^ m₁') N₁' L K k' (torusCast y' : Torus d (L ^ m₁' * N₁' * L ^ K))) ≤
        5 * L)
    {X₁f : Finset (Localization.CTorus d L N₁ m₁ K)}
    (hX₁ : (↑X₁f : Set (Localization.CTorus d L N₁ m₁ K)) = X1 Gp m₀ j 𝒦X) :
    BgSetting N Gp (castG hc (localB k' (by omega) Z' hs₁)) (castG hc (localB j (by omega) Xh hs₂))
      a₁ ν c BG κ r₀ eps δ₃ (dataSites (castG hc (localB k' (by omega) Z' hs₁))) X₁f j := by
  subst hkK
  have hL : 2 ≤ L := by have := HBp.hL; omega
  -- `Gj ≺ Gk` and the collar of `Gj` in `Ω₁(Gk)`
  have hZtop := Zset_hZ (d := d) (L := L) (N₁ := N₁') (m₁ := m₁') (k := k' + 1) (ϱ₂ := ϱ₁)
    (Nat.le_succ k') hZ' (h₂ := hs₁)
  have hq' := localB_precedes_localB hL hjk (Nat.le_succ k') (by omega : j ≤ k' + 1) hZtop
    (h₁ := hs₂)
  have hcol' := localB_collar_subset hL hj1 hjk (Nat.le_succ k') (by omega : j ≤ k' + 1) hZtop
    (h₁ := hs₂)
  -- the distances of the chain
  have hnear := hatChain_near hc hL (Nat.le_succ k') (cell_subset_of_covSetup hcov) hXh hZ' hs₁
  have hnat : L / 2 * cellSide L m₀ m₁ j +
      ((5 * L + 1) * (L ^ m₁' * L ^ k') + (11 * L ^ m₁' * L ^ k' + 1)) ≤
      L ^ (m₁ + k') * ((5 * L + 13) * c₁ + L / 2 * L ^ m₀) := by
    have hpos : 1 ≤ L ^ m₁' * L ^ k' :=
      Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
        (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
    have h1 : (5 * L + 1) * (L ^ m₁' * L ^ k') + (11 * L ^ m₁' * L ^ k' + 1) ≤
        (5 * L + 13) * (L ^ m₁' * L ^ k') := by
      have : (5 * L + 13) * (L ^ m₁' * L ^ k') =
          (5 * L + 1) * (L ^ m₁' * L ^ k') + 12 * (L ^ m₁' * L ^ k') := by ring
      rw [this, show 11 * L ^ m₁' * L ^ k' = 11 * (L ^ m₁' * L ^ k') by ring]
      omega
    have h2 : (5 * L + 13) * (L ^ m₁' * L ^ k') ≤ L ^ (m₁ + k') * ((5 * L + 13) * c₁) := by
      have e : L ^ (m₁ + k') * ((5 * L + 13) * c₁) = (5 * L + 13) * ((L ^ m₁ * c₁) * L ^ k') := by
        rw [pow_add]; ring
      rw [e]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hm1)
    have h3 : L / 2 * cellSide L m₀ m₁ j ≤ L ^ (m₁ + k') * (L / 2 * L ^ m₀) := by
      have e : L ^ (m₁ + k') * (L / 2 * L ^ m₀) = L / 2 * L ^ (k' + m₀ + m₁) := by
        rw [show k' + m₀ + m₁ = (m₁ + k') + m₀ by ring, pow_add]; ring
      rw [e]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L))
        (by omega))
    rw [Nat.mul_add]
    omega
  have hr' := margin_arith_gen (L := L) (m₁ := m₁) (k := k') (m₀ := m₀) hL hnat hm
  have hr₀0 : (0 : ℝ) ≤ r₀ := le_trans (by positivity) hr₀
  have hR0 : 0 ≤ r₀ * (L : ℝ) ^ m₁ * (L : ℝ) ^ (k' + 1) := by positivity
  -- every data site of `Gk` lies in the top layer of `Gp`
  have hdeepGk : ∀ x ∈ dataSites (castG hc (localB k' (Nat.le_succ k') Z' hs₁)),
      x ∈ Gp.Ω (k' + 1) := by
    intro x hx
    obtain ⟨z, w, hwX, hxz, hzw⟩ := hnear x hx
    refine hdeep x w hwX ((supDist_triangle x z w).trans ?_)
    have h1 : ((L / 2 * cellSide L m₀ m₁ j +
        ((5 * L + 1) * (L ^ m₁' * L ^ k') + (11 * L ^ m₁' * L ^ k' + 1)) : ℕ) : ℝ) ≤
        (((L - 2) * cellSide L m₀ m₁ (k' + 1) : ℕ) : ℝ) := by
      push_cast at hr' ⊢; linarith
    have h2 := (Nat.cast_le (α := ℝ)).1 h1
    have h3 : (L - 2) * cellSide L m₀ m₁ (k' + 1) ≤ L * cellSide L m₀ m₁ (k' + 1) :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    omega
  -- the margin of the data sites against `X₁`
  have hlev := isLevel_levelGS (d := d) (L := L) (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k := k' + 1)
    (by omega : 1 ≤ k' + 1) le_rfl
  have hcovl := covSetup_toLevel hcov hlev
  have hmar : ∀ x ∈ dataSites (castG hc (localB k' (Nat.le_succ k') Z' hs₁)),
      ∀ y : Localization.CTorus d L N₁ m₁ (k' + 1),
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k' + 1)) x y <
        r₀ * (L : ℝ) ^ m₁ * (L : ℝ) ^ (k' + 1) → y ∈ X₁f := by
    intro x hx y hy
    obtain ⟨z, w, hwX, hxz, hzw⟩ := hnear x hx
    have hy1 := mem_X1_of_chain hlev hL hcovl hxz hzw hwX hy (by push_cast at hr' ⊢; linarith)
    rw [← Finset.mem_coe, hX₁]
    exact X1_subset_X1_of_deep hcov.chosen hdeep hy1
  exact
    { hS := hS
      Sp := Sp
      ha₁ := ha₁
      HBp := HBp
      HBk := { HBp with hϱ := hϱ₁ }
      HBj := { HBp with hϱ := hϱ₂ }
      hP := fun i hi1 hik x hx => Gp.Ω_antitone hi1 hik (by omega)
        (hdeepGk x ((mem_dataSites _).2 (Or.inl
          ((castG hc (localB k' (Nat.le_succ k') Z' hs₁)).Ω_antitone le_rfl hi1 (by omega) hx))))
      hq := precedes_castG hc hq'
      colk := fun z hz => Gp.Ω_antitone le_rfl (by omega) (by omega)
        (hdeepGk z ((mem_dataSites _).2 (Or.inr hz)))
      colj := collar_castG_subset hc hcol'
      hκ := hκ
      hM := hM
      num := num
      dsX₀ := fun _ hx => hx
      hN := fun x hx hx1 y hy => hmar x hx y (lt_of_lt_of_le hy
        (mul_le_mul_of_nonneg_left (spacing_le Gp hx1) (by positivity)))
      hr := hr
      hr₀ := hr₀
      dep := fun x hx y hy => hmar x hx y
        (torusDist_lt_of_mem_composeDep (by have := HBp.hd; omega) hr₀ hy)
      hj := by omega }

end Chain

section Level

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ : ℝ}

/-- **`BgSetting` for the local chain under a whole-lattice top set** (`IsLevel G' K`: every site
in the top layer, e.g. `𝔹_K = levelGS K` or the small-field set of the whole torus): the instance
of `bgSetting_hat` whose position condition holds because `Ω_K(G')` is the torus. -/
theorem bgSetting_hat_of_isLevel {N₁' m₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    {k' : ℕ} (hkK : k' + 1 = K) {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (hlev : IsLevel Gp K)
    {a₁ ν c BG κ r₀ eps δ₃ : ℝ}
    (hS : DecSpecs d L c BG) (Sp : DGSetting Gp (compWeight L a₁) ν) (ha₁ : 0 < a₁)
    (HBp : BgHyp d L K ϱ (compWeight L a₁) ν) (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (num : ChainNum d L N m₁ BG κ r₀ eps δ₃)
    (hr : r₀ * (L : ℝ) ^ m₁ ≤ ϱ - 1) (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀)
    (hϱ₁ : bgR0 d L ≤ ϱ₁) (hϱ₂ : bgR0 d L ≤ ϱ₂) (hs₁ : ϱ₁ ≤ minSep L (L ^ m₁'))
    (hs₂ : ϱ₂ ≤ minSep L (L ^ m₁')) {m₀ c₁ : ℕ} (hm1 : L ^ m₁' ≤ L ^ m₁ * c₁)
    (hm : (((5 * L + 13) * c₁ + L / 2 * L ^ m₀ : ℕ) : ℝ) + r₀ * L ≤
      (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (m₀ + 1))
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k') {X 𝒦X : Set (Localization.CTorus d L N₁ m₁ K)}
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    {Xh Z' : Set (Localization.CTorus d L N₁' m₁' K)}
    (hXh : ∀ x' : Localization.CTorus d L N₁' m₁' K,
      x' ∈ Xh ↔ (torusCast x' : Localization.CTorus d L N₁ m₁ K) ∈ hatSet m₀ j X)
    (hZ' : ∀ z' : Localization.CTorus d L N₁' m₁' K, z' ∈ Z' ↔ ∃ y' ∈ Xh,
      supDist (fineCubeIdx (L ^ m₁') N₁' L K k' (torusCast z' : Torus d (L ^ m₁' * N₁' * L ^ K)))
        (fineCubeIdx (L ^ m₁') N₁' L K k' (torusCast y' : Torus d (L ^ m₁' * N₁' * L ^ K))) ≤
        5 * L)
    {X₁f : Finset (Localization.CTorus d L N₁ m₁ K)}
    (hX₁ : (↑X₁f : Set (Localization.CTorus d L N₁ m₁ K)) = X1 Gp m₀ j 𝒦X) :
    BgSetting N Gp (castG hc (localB k' (by omega) Z' hs₁)) (castG hc (localB j (by omega) Xh hs₂))
      a₁ ν c BG κ r₀ eps δ₃ (dataSites (castG hc (localB k' (by omega) Z' hs₁))) X₁f j :=
  bgSetting_hat hc hkK hS Sp ha₁ HBp hκ hM num hr hr₀ hϱ₁ hϱ₂ hs₁ hs₂ hm1 hm hj1 hjk hcov
    (fun z _ _ _ => ((GeneratingSet.mem_layer _).1 (hlev.mem_layer z)).1) hXh hZ' hX₁

/-- **Cube alignment of the whole-lattice set `𝔹_n = levelGS n`**: its domains are the torus or
empty. -/
theorem cubeAligned_levelGS (h2 : 2 ≤ m₁) {n : ℕ} (hn : n ≤ K) :
    CubeAligned (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) n hn) m₁ where
  two_le := h2
  dvd := dvd_mul_left _ _
  union := fun i _ _ x x' _ => by
    show x ∈ (if i ≤ n then Finset.univ else ∅) ↔ x' ∈ (if i ≤ n then Finset.univ else ∅)
    split_ifs <;> simp

/-- **Sup-separation of the whole-torus set `𝔹_K = levelGS K`**: every domain below the top is the
torus, so the condition is empty. -/
theorem supSep_levelGS :
    SupSep (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) K le_rfl) m₁ := by
  intro i _ hiK x hx
  exfalso
  apply hx
  show x ∈ (if i ≤ K then Finset.univ else ∅)
  simp [hiK.le]

/-- **The standing hypotheses `DGSetting` for the whole-torus set `𝔹_K = levelGS K`**, from the
conditions on the constants: `d, L ≥ 3`, `m₁ ≥ 2`, `4 L² ≤ L^{m₁}`, the cover separation
`4 d L L^{m₁} ≤ ϱ`, the Agmon separation of `ϱ`, the weights, the mass bounds and `N₁ > 5`. -/
theorem dgSetting_levelGS {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (h2 : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hcs : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1)) (hw : IsAdmissibleWeights K a)
    (hν : 0 ≤ ν) (hνL : ν * ((L : ℝ) ^ K) ^ 2 ≤ 1) (hbig : 5 < N₁) :
    DGSetting (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) K le_rfl) a ν where
  hd := hd
  hL := hL
  aligned := cubeAligned_levelGS h2 le_rfl
  hM := hM
  cover_sep := hcs
  sep := hsep
  weights := hw
  mass := hν
  massLe := hνL
  big := hbig

/-- **`BgSetting` for the local chain under the whole-torus set `𝔹_K = levelGS K`** of the class's
Def-6 torus at the torus level `K` (the last integral's stage 1, `Θ = lift ψ_K`): the instance of
`bgSetting_hat_of_isLevel` with `DGSetting` from the constants (`dgSetting_levelGS`). -/
theorem bgSetting_hat_levelGS {N₁' m₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    {k' : ℕ} (hkK : k' + 1 = K) {a₁ ν c BG κ r₀ eps δ₃ : ℝ} (hS : DecSpecs d L c BG)
    (h2 : 2 ≤ m₁) (hM4 : 4 * L ^ 2 ≤ L ^ m₁) (hcs : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1)) (hbig : 5 < N₁) (ha₁ : 0 < a₁)
    (HBp : BgHyp d L K ϱ (compWeight L a₁) ν) (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (num : ChainNum d L N m₁ BG κ r₀ eps δ₃)
    (hr : r₀ * (L : ℝ) ^ m₁ ≤ ϱ - 1) (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀)
    (hϱ₁ : bgR0 d L ≤ ϱ₁) (hϱ₂ : bgR0 d L ≤ ϱ₂) (hs₁ : ϱ₁ ≤ minSep L (L ^ m₁'))
    (hs₂ : ϱ₂ ≤ minSep L (L ^ m₁')) {m₀ c₁ : ℕ} (hm1 : L ^ m₁' ≤ L ^ m₁ * c₁)
    (hm : (((5 * L + 13) * c₁ + L / 2 * L ^ m₀ : ℕ) : ℝ) + r₀ * L ≤
      (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (m₀ + 1))
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k') {X 𝒦X : Set (Localization.CTorus d L N₁ m₁ K)}
    (hcov : CovSetup (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) K le_rfl)
      m₀ j X 𝒦X)
    {Xh Z' : Set (Localization.CTorus d L N₁' m₁' K)}
    (hXh : ∀ x' : Localization.CTorus d L N₁' m₁' K,
      x' ∈ Xh ↔ (torusCast x' : Localization.CTorus d L N₁ m₁ K) ∈ hatSet m₀ j X)
    (hZ' : ∀ z' : Localization.CTorus d L N₁' m₁' K, z' ∈ Z' ↔ ∃ y' ∈ Xh,
      supDist (fineCubeIdx (L ^ m₁') N₁' L K k' (torusCast z' : Torus d (L ^ m₁' * N₁' * L ^ K)))
        (fineCubeIdx (L ^ m₁') N₁' L K k' (torusCast y' : Torus d (L ^ m₁' * N₁' * L ^ K))) ≤
        5 * L)
    {X₁f : Finset (Localization.CTorus d L N₁ m₁ K)}
    (hX₁ : (↑X₁f : Set (Localization.CTorus d L N₁ m₁ K)) =
      X1 (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) K le_rfl) m₀ j 𝒦X) :
    BgSetting N (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) K le_rfl)
      (castG hc (localB k' (by omega) Z' hs₁)) (castG hc (localB j (by omega) Xh hs₂))
      a₁ ν c BG κ r₀ eps δ₃ (dataSites (castG hc (localB k' (by omega) Z' hs₁))) X₁f j :=
  bgSetting_hat_of_isLevel hc hkK (isLevel_levelGS (by omega) le_rfl) hS
    (dgSetting_levelGS HBp.hd HBp.hL h2 hM4 hcs hsep HBp.weights HBp.mass HBp.massLe hbig) ha₁
    HBp hκ hM num hr hr₀ hϱ₁ hϱ₂ hs₁ hs₂ hm1 hm hj1 hjk hcov hXh hZ' hX₁

end Level

end Balaban.LargeField
