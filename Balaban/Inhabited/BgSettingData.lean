/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5Inhabited
public import Balaban.Fluctuation.PhysicalReadsE
public import Balaban.Fluctuation.InteractionLevelPair
public import Balaban.Inhabited.BgSettingDataNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `BgSetting` with a non-empty set of data sites

**Survey (why the landed witness is vacuous).**  In `nonempty_i5Witness` the old generating set is
`G0 m₁ ρ = levelGS 0`: all its domains `Ω_i`, `i ≥ 1`, are empty (level `0`).  So `Ω₁ = ∅`, the
collar is empty and `dataSites = Ω₁ ∪ collar = ∅`; every statement over data sites (the support
lemma `approxDep_composeDep_subset_X1`, the locality of the old energy terms, the fields `dsX₀`,
`dep` of `BgSetting`) is vacuous there.

**The smallest change.**  `Precedes Gk Gp` only asks `Ω_i(Gk) ⊆ Ω_i(Gp)` for `1 ≤ i ≤ K`, and
`colk` only asks `collar Gk ⊆ Ω₁(Gp)`.  With `Gp` a full-level set (`Ω₁ = 𝕋`) both hold for every
`Gk`.  Taking `Gk = Gp` or `Gk = levelGS 1` is allowed, but then `dataSites Gk = 𝕋`, `X₀ ⊇ 𝕋`, and
`hN` (balls around the points of `X₀ ∩ Ω₁(Gp) = X₀`) forces `X₁ = 𝕋`, which makes E-read true for
a trivial reason.  We therefore use a *sparse* `Gk`: `Ω₁(Gk)` is one `1`-block (the block of the
origin), `Ω_i(Gk) = ∅` for `i ≥ 2`, which satisfies all axioms of a generating set (separation is
vacuous because `Ω₂ = ∅`).  Its data sites are the block together with the collar, at `ℓ¹` distance
at most `10` from the origin.

**The torus.**  The ball of `hN` has `ℓ¹` radius `r₀ L^{m₁} L^K = 324 ℓ` with `ℓ = L^{K+m₁}` and
`r₀ = 4 d L³ = 324` (the least value allowed by `hr₀`).  The `ℓ¹` diameter of the torus of side
`N₁ ℓ` is `d N₁ ℓ / 2`, so a proper `X₁` needs about `N₁ > 216`; the landed side `N₁ = 6` forces
`X₁ = 𝕋` whatever `X₀ ≠ ∅` is.  We take `N₁ = 240`.  The chosen family `𝒦_X` is the set of
`ℓ`-aligned points at `ℓ¹` distance at most `328 ℓ` from the origin; `X₁ = X1 Gp 0 1 𝒦_X` then
contains the ball and misses the antipodal point `(120 ℓ, 120 ℓ, 120 ℓ)`.

**Remarks on the fields.**  No field of `BgSetting` is unsatisfiable once `dataSites Gk ≠ ∅`.  The
fields `hr`, `hr₀` are independent of the torus (`r₀ L^{m₁} = 324 · 3^{m₁} ≤ ρ - 1`).  The field
`hN` is what forces the size of the torus: on the landed side `N₁ = 6` the ball of radius
`r₀ L^{m₁} L^K` wraps onto the whole torus, so `X₁ = 𝕋` for any non-empty `X₀`.
`Precedes Gk Gp` holds for `Gk` of level `k` and `Gp` of level `k + 1` by `IsLevel.precedes`; here
`Gk` is sparse and `Precedes Gk Gp` follows from `Ω_i(Gp) = 𝕋` for `i ≤ K`.

* `bgSetting_data`: a `BgSetting` for these sets with all nineteen fields proved;
* `bgSetting_data_eRead`: the instance of E-read at the origin and a neighbouring site, with
  `approxDep Gp u` containing `u` and the block base `0 ≠ u`;
* `bgFlSetting_data`, `bgFlSetting_data_eRead`: the same with `FlSetting` for `Hm` the level-`1` set
  (`FlCore` taken from `flCore_level_eventually`, joint constants from `joint_num_exists`).
-/

@[expose] public section

namespace Balaban.Inhabited
namespace BgSettingData

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.I5Inhabited

/-- The side `N₁ = 240` of the coarse torus. -/
abbrev T (m₁ : ℕ) : Type := CTorus 3 3 240 m₁ 2

/-! ### The generating sets -/

section Sets

variable (m₁ : ℕ) (ρ : ℝ)

/-- The new generating set `𝔹_{k+1}`: whole lattice, level `2`. -/
noncomputable abbrev GpD : GeneratingSet 3 3 (240 * 3 ^ m₁) 2 ρ :=
  Def6.levelGS (d := 3) (L := 3) (N₁ := 240) (m₁ := m₁) (ϱ := ρ) 2 le_rfl

/-- The empty generating set (level `0`), used for `Gj`. -/
noncomputable abbrev G0D : GeneratingSet 3 3 (240 * 3 ^ m₁) 2 ρ :=
  Def6.levelGS (d := 3) (L := 3) (N₁ := 240) (m₁ := m₁) (ϱ := ρ) 0 (Nat.zero_le _)

open Classical in
/-- The old generating set: `Ω₁` is the `1`-block of the origin, `Ω_i = ∅` for `i ≥ 2`. -/
noncomputable def GkD : GeneratingSet 3 3 (240 * 3 ^ m₁) 2 ρ where
  Ω := fun i => if i = 1 then Finset.univ.filter fun x =>
      jBlock 3 3 (240 * 3 ^ m₁) 2 1 x = jBlock 3 3 (240 * 3 ^ m₁) 2 1 0 else ∅
  top := by simp
  subset := fun j hj hjk => by
    have : j ≠ 0 := by omega
    simp [this]
  blockUnion := fun j hj hjk x x' h => by
    by_cases h1 : j = 1
    · subst h1
      simp only [ite_true, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [h]
    · simp [h1]
  separation := fun j hj hjk x hx y hy => by
    have : j ≠ 0 := by omega
    simp [this] at hy

variable {m₁ ρ}

theorem mem_GkD_Ω_one {x : T m₁} :
    x ∈ (GkD m₁ ρ).Ω 1 ↔ jBlock 3 3 (240 * 3 ^ m₁) 2 1 x = jBlock 3 3 (240 * 3 ^ m₁) 2 1 0 := by
  simp [GkD]

theorem GkD_Ω_ne {i : ℕ} (h : i ≠ 1) : (GkD m₁ ρ).Ω i = ∅ := by simp [GkD, h]

theorem GpD_Ω (i : ℕ) : (GpD m₁ ρ).Ω i = if i ≤ 2 then Finset.univ else ∅ := rfl

theorem isLevel_GpD : IsLevel (GpD m₁ ρ) 2 := isLevel_levelGS (by norm_num) le_rfl

theorem GpD_layer_two : (GpD m₁ ρ).layer 2 = Finset.univ := by
  ext x
  simp [GeneratingSet.layer, GpD_Ω]

theorem G0D_Ω (i : ℕ) (hi : 1 ≤ i) : (G0D m₁ ρ).Ω i = ∅ := by
  simp only [G0D, Def6.levelGS]
  have : ¬ i ≤ 0 := by omega
  simp [this]

theorem G0D_collar : collar (G0D m₁ ρ) = ∅ := by
  ext x
  simp [mem_collar, G0D_Ω _ le_rfl]

theorem GkD_layerIndex {x : T m₁} (hx : x ∈ (GkD m₁ ρ).Ω 1) : (GkD m₁ ρ).layerIndex x = 1 := by
  refine GeneratingSet.layerIndex_eq _ le_rfl (by norm_num) ?_
  rw [GeneratingSet.mem_layer]
  exact ⟨hx, by rw [GkD_Ω_ne (by norm_num)]; simp⟩

theorem origin_mem_GkD : (0 : T m₁) ∈ (GkD m₁ ρ).Ω 1 := mem_GkD_Ω_one.2 rfl

theorem dataSites_GkD_nonempty : (dataSites (GkD m₁ ρ)).Nonempty :=
  ⟨0, (mem_dataSites _).2 (Or.inl origin_mem_GkD)⟩

end Sets

/-! ### Distances -/

section Dist

/-- Sites of one `j`-block are at `ℓ¹` distance at most `3 · 3^j`. -/
theorem dist_jBlock_le {m₁ j : ℕ} (hj : j ≤ 2) {x y : T m₁}
    (h : jBlock 3 3 (240 * 3 ^ m₁) 2 j x = jBlock 3 3 (240 * 3 ^ m₁) 2 j y) :
    Green.torusDist 3 (240 * 3 ^ m₁ * 3 ^ 2) x y ≤ 3 * 3 ^ j := by
  have := Green.torusDist_le_of_blockMap_eq (d := 3) (side_eq (L := 3) (N₀ := 240 * 3 ^ m₁)
    (k := 2) hj) (pow_pos (by norm_num : 0 < 3) j) h
  simpa using this

/-- Points of a box of side `s` are at `ℓ¹` distance at most `3 s` of its base point. -/
theorem dist_box_le {m₁ s : ℕ} {b z : T m₁} (hz : z ∈ box b s) :
    Green.torusDist 3 (240 * 3 ^ m₁ * 3 ^ 2) z b ≤ 3 * s := by
  obtain ⟨w, hw, rfl⟩ := hz
  unfold Green.torusDist
  have : (3 : ℝ) * s = ∑ _i : Fin 3, (s : ℝ) := by simp
  rw [this]
  refine Finset.sum_le_sum fun μ _ => ?_
  have h := Green.natAbs_cycRep_le_of_cast ((b + natT w : T m₁) μ - b μ) (w μ : ℤ) (by
    simp [natT_apply])
  have : ((w μ : ℤ)).natAbs = w μ := Int.natAbs_natCast _
  rw [this] at h
  exact_mod_cast (h.trans (hw μ).le)

theorem dist_dataSites_le {m₁ : ℕ} {ρ : ℝ} {x : T m₁} (hx : x ∈ dataSites (GkD m₁ ρ)) :
    Green.torusDist 3 (240 * 3 ^ m₁ * 3 ^ 2) x 0 ≤ 10 := by
  rw [mem_dataSites, mem_collar] at hx
  rcases hx with h | ⟨-, z, hz, hadj⟩
  · have := dist_jBlock_le (m₁ := m₁) (j := 1) (by norm_num) (mem_GkD_Ω_one.1 h)
    linarith
  · have h1 := dist_jBlock_le (m₁ := m₁) (j := 1) (by norm_num) (mem_GkD_Ω_one.1 hz)
    have h2 := Adj.torusDist_le (d := 3) (L := 3) (N₀ := 240 * 3 ^ m₁) (k := 2) hadj.symm
    have h3 := Green.torusDist_triangle_gen (d := 3) (m := 240 * 3 ^ m₁ * 3 ^ 2) x z 0
    norm_num at h1
    linarith

end Dist

/-! ### The region `X₁` -/

section Region

/-- The chosen family `𝒦_X`: the `ℓ`-aligned points at `ℓ¹` distance at most `328 ℓ` from the
origin, `ℓ = 3^{K + m₁}`. -/
def KX (m₁ : ℕ) : Set (T m₁) :=
  {q | Aligned (cellSide 3 0 m₁ 2) q ∧
    Green.torusDist 3 (240 * 3 ^ m₁ * 3 ^ 2) q 0 ≤ 328 * (cellSide 3 0 m₁ 2 : ℝ)}

variable {m₁ : ℕ} {ρ : ℝ}

theorem cellSide_two (m₁ : ℕ) : cellSide 3 0 m₁ 2 = 3 ^ m₁ * 9 := by
  unfold cellSide; ring

theorem cellSide_one (m₁ : ℕ) : cellSide 3 0 m₁ 1 = 3 ^ m₁ * 3 := by
  unfold cellSide; ring

theorem le_cellSide (h4 : 4 ≤ m₁) : (10 : ℝ) ≤ (cellSide 3 0 m₁ 2 : ℝ) := by
  have : 3 ^ 4 ≤ 3 ^ m₁ := Nat.pow_le_pow_right (by norm_num) h4
  rw [cellSide_two]
  have : (81 : ℝ) ≤ ((3 ^ m₁ : ℕ) : ℝ) := by exact_mod_cast this
  push_cast at this ⊢
  linarith

/-- **The ball of `hN` lies in `X₁`.** -/
theorem ball_subset_X1 (h4 : 4 ≤ m₁) {x y : T m₁}
    (hx : Green.torusDist 3 (240 * 3 ^ m₁ * 3 ^ 2) x 0 ≤ 10)
    (hy : Green.torusDist 3 (240 * 3 ^ m₁ * 3 ^ 2) x y < 324 * (cellSide 3 0 m₁ 2 : ℝ)) :
    y ∈ X1 (GpD m₁ ρ) 0 1 (KX m₁) := by
  have hl := le_cellSide h4
  have hpos : 0 < cellSide 3 0 m₁ 2 := cellSide_pos 0 m₁ 2
  set b : T m₁ := cbase (cellSide 3 0 m₁ 2) y with hb
  have hyb : y ∈ box b (cellSide 3 0 m₁ 2) := mem_box_cbase hpos y
  have hdyb := dist_box_le hyb
  have hcell : (3 : ℝ) * (cellSide 3 0 m₁ 2 : ℝ) = ((3 * cellSide 3 0 m₁ 2 : ℕ) : ℝ) := by
    push_cast; ring
  have hbK : b ∈ KX m₁ := by
    refine ⟨aligned_cbase y, ?_⟩
    have t1 := Green.torusDist_triangle_gen (d := 3) (m := 240 * 3 ^ m₁ * 3 ^ 2) b y 0
    have t2 := Green.torusDist_triangle_gen (d := 3) (m := 240 * 3 ^ m₁ * 3 ^ 2) y x 0
    have c1 := Green.torusDist_comm_gen (d := 3) (m := 240 * 3 ^ m₁ * 3 ^ 2) y b
    have c2 := Green.torusDist_comm_gen (d := 3) (m := 240 * 3 ^ m₁ * 3 ^ 2) y x
    linarith
  refine Set.mem_iUnion₂.2 ⟨b, ⟨aligned_cbase y, ?_, b, hbK, ?_⟩, ?_⟩
  · rw [GpD_layer_two]; intro z _; simp
  · refine box_mono _ ?_
    rw [cellSide_two, cellSide_one]
    omega
  · exact box_mono _ (by omega) hyb

/-- **`X₁` is proper**: the point `(120 ℓ, 120 ℓ, 120 ℓ)` is not in it. -/
theorem antipode_not_mem_X1 :
    (fun _ => ((120 * cellSide 3 0 m₁ 2 : ℕ) : ZMod (240 * 3 ^ m₁ * 3 ^ 2)) : T m₁) ∉
      X1 (GpD m₁ ρ) 0 1 (KX m₁) := by
  intro hmem
  obtain ⟨b, ⟨-, -, q, hq, hsub⟩, hy⟩ := Set.mem_iUnion₂.1 hmem
  have hpos : 0 < cellSide 3 0 m₁ 2 := cellSide_pos 0 m₁ 2
  have hq1 : q ∈ box q (3 * cellSide 3 0 m₁ 1) :=
    mem_box_self _ (Nat.mul_pos (by norm_num) (cellSide_pos 0 m₁ 1))
  have hqb := dist_box_le (hsub hq1)
  have hyb := dist_box_le hy
  set y : T m₁ := (fun _ => ((120 * cellSide 3 0 m₁ 2 : ℕ) : ZMod (240 * 3 ^ m₁ * 3 ^ 2)))
  have hS : 240 * 3 ^ m₁ * 3 ^ 2 = 240 * cellSide 3 0 m₁ 2 := by rw [cellSide_two]; ring
  have hy0 : Green.torusDist 3 (240 * 3 ^ m₁ * 3 ^ 2) y 0 = 360 * (cellSide 3 0 m₁ 2 : ℝ) := by
    unfold Green.torusDist
    have : ∀ μ : Fin 3, ((Green.cycRep (y μ - (0 : T m₁) μ)).natAbs : ℝ) =
        120 * (cellSide 3 0 m₁ 2 : ℝ) := by
      intro μ
      have hv : (y μ - (0 : T m₁) μ).val = 120 * cellSide 3 0 m₁ 2 := by
        simp only [y, Pi.zero_apply, sub_zero]
        exact ZMod.val_natCast_of_lt (by rw [hS]; omega)
      unfold Green.cycRep
      have hle : 120 * cellSide 3 0 m₁ 2 ≤ 240 * 3 ^ m₁ * 3 ^ 2 / 2 := by rw [hS]; omega
      rw [hv]
      simp only [hle, ite_true]
      simp
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num; ring
  have t1 := Green.torusDist_triangle_gen (d := 3) (m := 240 * 3 ^ m₁ * 3 ^ 2) y b 0
  have t2 := Green.torusDist_triangle_gen (d := 3) (m := 240 * 3 ^ m₁ * 3 ^ 2) b q 0
  have c1 := Green.torusDist_comm_gen (d := 3) (m := 240 * 3 ^ m₁ * 3 ^ 2) b q
  have hqK := hq.2
  have e1 : ((3 * cellSide 3 0 m₁ 2 : ℕ) : ℝ) = 3 * (cellSide 3 0 m₁ 2 : ℝ) := by push_cast; ring
  rw [e1] at hyb
  rw [e1] at hqb
  have hposR : (0 : ℝ) < (cellSide 3 0 m₁ 2 : ℝ) := by exact_mod_cast hpos
  linarith

end Region

/-! ### The setting -/

section Setting

variable {m₁ : ℕ} {ρ : ℝ}

theorem GpD_cubeAligned (h : 2 ≤ m₁) : CubeAligned (GpD m₁ ρ) m₁ where
  two_le := h
  dvd := dvd_mul_left _ _
  union := fun j _ hj x x' _ => by simp [GpD_Ω, hj]

theorem dgSetting_GpD (h4 : 4 ≤ m₁) : DGSetting (GpD m₁ (rhoSep m₁)) (compWeight 3 1) 0 where
  hd := le_rfl
  hL := le_rfl
  aligned := GpD_cubeAligned (by omega)
  hM := by
    calc 4 * 3 ^ 2 = 36 := by norm_num
      _ ≤ 3 ^ 4 := by norm_num
      _ ≤ 3 ^ m₁ := Nat.pow_le_pow_right (by norm_num) h4
  cover_sep := by
    have := rhoSep_ge m₁
    have : (0:ℝ) ≤ 3 ^ m₁ := by positivity
    have := rhoSep_tail_nonneg
    push_cast
    nlinarith
  sep := by
    have h := rhoSep_ge m₁
    have ha := agmon3_pos
    have hq : 6 * Real.log 3 / (agmonRate 3 / 16) ≤ rhoSep m₁ - 1 := by
      have : (0:ℝ) ≤ 3 ^ m₁ := by positivity
      linarith
    rw [div_le_iff₀ (by positivity)] at hq
    push_cast
    nlinarith
  weights := isAdmissibleWeights_compWeight le_rfl (by norm_num) (by norm_num) _
  mass := le_rfl
  massLe := by simp
  big := by norm_num

/-- The spacing of the level-`2` set is `L^2 = 9`. -/
theorem spacing_GpD (x : T m₁) : (GpD m₁ ρ).spacing x = 9 := by
  unfold GeneratingSet.spacing; rw [(isLevel_GpD x).2]; norm_num

theorem ball_of_dataSite (h4 : 4 ≤ m₁) {x y : T m₁} (hx : x ∈ dataSites (GkD m₁ ρ))
    (hy : Green.torusDist 3 (240 * 3 ^ m₁ * 3 ^ 2) x y < 324 * (cellSide 3 0 m₁ 2 : ℝ)) :
    y ∈ X1 (GpD m₁ ρ) 0 1 (KX m₁) :=
  ball_subset_X1 h4 (dist_dataSites_le hx) hy

/-- The composite sites of a data site are within `ℓ¹` distance `27` of it. -/
theorem dist_composeDep_le {x u : T m₁} (hx : x ∈ dataSites (GkD m₁ ρ))
    (hu : u ∈ composeDep (GkD m₁ ρ) (GpD m₁ ρ) x) :
    Green.torusDist 3 (240 * 3 ^ m₁ * 3 ^ 2) x u ≤ 27 := by
  classical
  unfold composeDep at hu
  by_cases hxΩ : x ∈ (GkD m₁ ρ).Ω 1
  · simp only [hxΩ, ↓reduceIte, Finset.mem_insert, Finset.mem_union,
      GeneratingSet.mem_blk] at hu
    rcases hu with rfl | hb | hb
    · rw [Green.torusDist_self_eq_zero]; norm_num
    · rw [GkD_layerIndex hxΩ] at hb
      have := dist_jBlock_le (m₁ := m₁) (j := 1) (by norm_num) hb.symm
      norm_num at this; linarith
    · rw [(isLevel_GpD x).2] at hb
      have := dist_jBlock_le (m₁ := m₁) (j := 2) (by norm_num) hb.symm
      norm_num at this; linarith
  · simp only [hxΩ, ↓reduceIte, Finset.mem_singleton] at hu
    subst hu
    rw [Green.torusDist_self_eq_zero]; norm_num


/-- The region `X₁f = X1 Gp 0 1 𝒦_X` as a finset. -/
noncomputable def X1f (m₁ : ℕ) (ρ : ℝ) : Finset (T m₁) :=
  (Set.toFinite (X1 (GpD m₁ ρ) 0 1 (KX m₁))).toFinset

theorem mem_X1f {m₁ : ℕ} {ρ : ℝ} {y : T m₁} : y ∈ X1f m₁ ρ ↔ y ∈ X1 (GpD m₁ ρ) 0 1 (KX m₁) :=
  Set.Finite.mem_toFinset _

theorem coe_X1f (m₁ : ℕ) (ρ : ℝ) : (↑(X1f m₁ ρ) : Set (T m₁)) = X1 (GpD m₁ ρ) 0 1 (KX m₁) :=
  Set.Finite.coe_toFinset _

/-- **`BgSetting` with data sites.**  `Gp` is the whole-lattice set of level `2`, `Gk` has `Ω₁` one
`1`-block (so `dataSites Gk` is non-empty), `Gj` is empty, `X₀ = dataSites Gk`, and
`X₁f = X1 Gp 0 1 𝒦_X` on the torus of side `240 · 3^{m₁} · 9`; all nineteen fields hold with
`r₀ = 324 = 4 d L³`. -/
theorem bgSetting_data_of {m₁ : ℕ} (h4 : 4 ≤ m₁) {c BG eps δ₃ : ℝ} (hS : DecSpecs 3 3 c BG)
    (hm : c * Real.exp ((N0 3 3 : ℝ) * 100000) ≤ (3 : ℝ) ^ m₁)
    (hnum : ChainNum 3 3 2 m₁ BG 100000 324 eps δ₃) :
    BgSetting 2 (GpD m₁ (rhoSep m₁)) (GkD m₁ (rhoSep m₁)) (G0D m₁ (rhoSep m₁)) 1 0 c BG 100000
      324 eps δ₃ (dataSites (GkD m₁ (rhoSep m₁))) (X1f m₁ (rhoSep m₁)) 1 := by
  have hBH := bgHyp_rho m₁
  exact {
    hS := hS
    Sp := dgSetting_GpD h4
    ha₁ := one_pos
    HBp := hBH
    HBk := hBH
    HBj := hBH
    hP := fun i hi hik x _ => by
      have : i ≤ 2 := hik
      simp [GpD_Ω, this]
    hq := fun i hi _ => by rw [G0D_Ω i hi]; exact Finset.empty_subset _
    colk := fun z _ => by simp [GpD_Ω]
    colj := fun z hz => by rw [G0D_collar] at hz; simp at hz
    hκ := by norm_num
    hM := by exact_mod_cast hm
    num := hnum
    dsX₀ := fun x hx => hx
    hN := fun x hx _ y hy => by
      rw [mem_X1f]
      refine ball_of_dataSite h4 hx ?_
      rw [spacing_GpD] at hy
      have : (324 : ℝ) * 3 ^ m₁ * 9 = 324 * (cellSide 3 0 m₁ 2 : ℝ) := by
        rw [cellSide_two]; push_cast; ring
      simp only [Nat.cast_ofNat] at hy
      linarith
    hr := by
      have : (0:ℝ) ≤ 36 * 3 ^ m₁ := by positivity
      have := rhoSep_tail_nonneg
      have := rhoSep_ge m₁
      push_cast
      nlinarith
    hr₀ := by norm_num
    dep := fun x hx y hy => by
      rw [mem_X1f]
      refine ball_of_dataSite h4 hx ?_
      have h27 := dist_composeDep_le hx hy
      have := le_cellSide h4
      linarith
    hj := by norm_num }

theorem bgSetting_data :
    ∃ (m₁ : ℕ) (ρ c BG κ eps δ₃ : ℝ), 4 ≤ m₁ ∧
      BgSetting 2 (GpD m₁ ρ) (GkD m₁ ρ) (G0D m₁ ρ) 1 0 c BG κ 324 eps δ₃
        (dataSites (GkD m₁ ρ)) (X1f m₁ ρ) 1 := by
  obtain ⟨c, BG, hS⟩ := decSpecs_exists (d := 3) (L := 3) (by norm_num) (by norm_num)
  have hBG : 0 ≤ BG := hS.fam.2.1
  obtain ⟨m₁, h4, hm⟩ := exists_m₁ (c * Real.exp ((N0 3 3 : ℝ) * 100000))
  obtain ⟨eps, δ₃, hnum⟩ := chainNum_exists 3 3 2 m₁ (by norm_num) hBG 100000 324
  exact ⟨m₁, rhoSep m₁, c, BG, 100000, eps, δ₃, h4, bgSetting_data_of h4 hS hm hnum⟩

/-- `X₁f` is a proper subset of the torus. -/
theorem X1f_ne_univ (m₁ : ℕ) (ρ : ℝ) : X1f m₁ ρ ≠ Finset.univ := fun h =>
  antipode_not_mem_X1 (m₁ := m₁) (ρ := ρ) (mem_X1f.1 (h ▸ Finset.mem_univ _))

end Setting

/-! ### The instance of E-read -/

section ERead

variable {m₁ : ℕ} {ρ : ℝ}

theorem one_lt_side (m₁ : ℕ) : 1 < 240 * 3 ^ m₁ * 3 ^ 2 := by
  have h : 1 ≤ 3 ^ m₁ := Nat.one_le_pow _ _ (by norm_num)
  nlinarith

/-- The site `(1, 1, 1)`. -/
def one3 (m₁ : ℕ) : T m₁ := natT (fun _ => 1)

theorem one3_val (m₁ : ℕ) (μ : Fin 3) : (one3 m₁ μ).val = 1 := by
  unfold one3
  simp only [natT_apply]
  exact ZMod.val_natCast_of_lt (one_lt_side m₁)

theorem one3_ne_zero (m₁ : ℕ) : one3 m₁ ≠ 0 := fun h => by
  have := one3_val m₁ 0
  rw [h] at this
  simp at this

theorem ownBase_one3 (m₁ : ℕ) : ownBase 2 (one3 m₁) = (0 : T m₁) := by
  funext μ
  unfold ownBase
  rw [one3_val]
  simp

theorem zero_mem_approxDep_one3 : (0 : T m₁) ∈ approxDep (GpD m₁ ρ) (one3 m₁) := by
  classical
    unfold approxDep
    refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(2, ownBase 2 (one3 m₁)), ?_, ?_⟩)
    · refine (mem_active _).2 ⟨own_mem_blockIdx _ (by norm_num) le_rfl
        ((isLevel_GpD (ρ := ρ)).mem_layer _), ?_⟩
      have := bump_ge_of_jBlock_eq (d := 3) (L := 3) (N₀ := 240 * 3 ^ m₁) (k := 2) (m := 2)
        le_rfl (ownBase_isBase (one3 m₁)) (ownBase_jBlock (one3 m₁)).symm
      exact ne_of_gt (lt_of_lt_of_le (by positivity) this)
    · exact ownBase_one3 m₁

/-- **E-read, non-vacuously.**  For any `BgSetting` on the sets of this file, at the data site
`0` and the composite site `u = (1,1,1)` (a site of the `2`-block of `0`), the approximate field of
`Gp` at `u` reads `u` itself and the base `0` of its own block (so `approxDep Gp u` has at least
two elements), and all reads lie in `X₁f`. -/
theorem eRead_instance {c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (T m₁)}
    (hB : BgSetting 2 (GpD m₁ ρ) (GkD m₁ ρ) (G0D m₁ ρ) 1 0 c BG κ r₀ eps δ₃ X₀ X₁f 1) :
    ∃ x u : T m₁, x ∈ dataSites (GkD m₁ ρ) ∧ u ∈ composeDep (GkD m₁ ρ) (GpD m₁ ρ) x ∧
      u ≠ x ∧ x ∈ approxDep (GpD m₁ ρ) u ∧ u ∈ approxDep (GpD m₁ ρ) u ∧
      approxDep (GpD m₁ ρ) u ⊆ X₁f := by
  classical
  have hx : (0 : T m₁) ∈ dataSites (GkD m₁ ρ) := (mem_dataSites _).2 (Or.inl origin_mem_GkD)
  have hu : one3 m₁ ∈ composeDep (GkD m₁ ρ) (GpD m₁ ρ) 0 := by
    unfold composeDep
    simp only [origin_mem_GkD, ↓reduceIte, Finset.mem_insert, Finset.mem_union,
      GeneratingSet.mem_blk]
    right; right
    rw [(isLevel_GpD (0 : T m₁)).2]
    have := ownBase_jBlock (d := 3) (L := 3) (N₀ := 240 * 3 ^ m₁) (k := 2) (n := 2) (one3 m₁)
    rw [ownBase_one3] at this
    exact this.symm
  have hmem := zero_mem_approxDep_one3 (m₁ := m₁) (ρ := ρ)
  exact ⟨0, one3 m₁, hx, hu, one3_ne_zero m₁, hmem,
    by unfold approxDep; exact Finset.mem_insert_self _ _,
    approxDep_composeDep_subset_X1 hB isLevel_GpD hx hu⟩

/-- **The joint statement:** a `BgSetting` with non-empty data sites, a full-level `Gp` and a proper
`X₁f`, together with the non-vacuous E-read instance. -/
theorem bgSetting_data_eRead :
    ∃ (m₁ : ℕ) (ρ c BG κ eps δ₃ : ℝ),
      BgSetting 2 (GpD m₁ ρ) (GkD m₁ ρ) (G0D m₁ ρ) 1 0 c BG κ 324 eps δ₃
        (dataSites (GkD m₁ ρ)) (X1f m₁ ρ) 1 ∧
      IsLevel (GpD m₁ ρ) 2 ∧ (dataSites (GkD m₁ ρ)).Nonempty ∧ X1f m₁ ρ ≠ Finset.univ ∧
      ∃ x u : T m₁, x ∈ dataSites (GkD m₁ ρ) ∧ u ∈ composeDep (GkD m₁ ρ) (GpD m₁ ρ) x ∧
        u ≠ x ∧ x ∈ approxDep (GpD m₁ ρ) u ∧ approxDep (GpD m₁ ρ) u ⊆ X1f m₁ ρ := by
  obtain ⟨m₁, ρ, c, BG, κ, eps, δ₃, -, hB⟩ := bgSetting_data
  obtain ⟨x, u, hx, hu, hne, h1, -, h3⟩ := eRead_instance hB
  exact ⟨m₁, ρ, c, BG, κ, eps, δ₃, hB, isLevel_GpD, dataSites_GkD_nonempty, X1f_ne_univ m₁ ρ,
    x, u, hx, hu, hne, h1, h3⟩

end ERead

/-! ### The fluctuation side -/

section Fluct

variable {m₁ : ℕ} {ρ : ℝ}

variable (m₁ ρ) in
/-- The fluctuation set `𝔹_k`: whole lattice, level `1`. -/
noncomputable abbrev HmD : GeneratingSet 3 3 (240 * 3 ^ m₁) 2 ρ :=
  Def6.levelGS (d := 3) (L := 3) (N₁ := 240) (m₁ := m₁) (ϱ := ρ) 1 (by norm_num)

theorem isLevel_HmD : IsLevel (HmD m₁ ρ) 1 := isLevel_levelGS le_rfl (by norm_num)

theorem opSetting_HmD (h4 : 4 ≤ m₁) : Dec2.OpSetting (HmD m₁ (rhoSep m₁)) (compWeight 3 1) 0 :=
  { hd := (dgSetting_GpD h4).hd, hL := (dgSetting_GpD h4).hL, mass := (dgSetting_GpD h4).mass,
    massLe := (dgSetting_GpD h4).massLe, weights := (dgSetting_GpD h4).weights,
    sep := (dgSetting_GpD h4).sep }

theorem precedes_GkD_HmD : Precedes (GkD m₁ ρ) (HmD m₁ ρ) := by
  intro i hi hik x hx
  by_cases h1 : i = 1
  · subst h1; simp [Def6.levelGS]
  · rw [GkD_Ω_ne h1] at hx; simp at hx

theorem dist_composeDep_hm_le {x u : T m₁} (hx : x ∈ dataSites (GkD m₁ ρ))
    (hu : u ∈ composeDep (GkD m₁ ρ) (HmD m₁ ρ) x) :
    Green.torusDist 3 (240 * 3 ^ m₁ * 3 ^ 2) x u ≤ 9 := by
  classical
  unfold composeDep at hu
  by_cases hxΩ : x ∈ (GkD m₁ ρ).Ω 1
  · simp only [hxΩ, ↓reduceIte, Finset.mem_insert, Finset.mem_union,
      GeneratingSet.mem_blk] at hu
    rcases hu with rfl | hb | hb
    · rw [Green.torusDist_self_eq_zero]; norm_num
    · rw [GkD_layerIndex hxΩ] at hb
      have := dist_jBlock_le (m₁ := m₁) (j := 1) (by norm_num) hb.symm
      norm_num at this; linarith
    · rw [(isLevel_HmD x).2] at hb
      have := dist_jBlock_le (m₁ := m₁) (j := 1) (by norm_num) hb.symm
      norm_num at this; linarith
  · simp only [hxΩ, ↓reduceIte, Finset.mem_singleton] at hu
    subst hu
    rw [Green.torusDist_self_eq_zero]; norm_num

/-- **`BgSetting` and `FlSetting` together, with data sites.**  `Gp` level `2`, `Hm` level `1`
(the physical pair `𝔹_{k+1} ≻ 𝔹_k`), `Gk` the sparse set with `Ω₁` a `1`-block, the same
`X₁f`, and the same `ε'`, `δ₃`. -/
theorem bgFlSetting_data :
    ∃ (m₁ : ℕ) (ρ c BG κ eps δ₃ c₂ BG₂ δ₁ δfl : ℝ),
      BgSetting 2 (GpD m₁ ρ) (GkD m₁ ρ) (G0D m₁ ρ) 1 0 c BG κ 324 eps δ₃
        (dataSites (GkD m₁ ρ)) (X1f m₁ ρ) 1 ∧
      FlSetting 2 (GpD m₁ ρ) (GkD m₁ ρ) (HmD m₁ ρ) 1 0 κ BG eps δ₃ (levelKc 3 3) (Cchi 3 3)
        c₂ BG₂ δ₁ δfl (X1f m₁ ρ) := by
  obtain ⟨c, BG, hS⟩ := decSpecs_exists (d := 3) (L := 3) (by norm_num) (by norm_num)
  obtain ⟨c₂, BG₂, hS2⟩ := Dec2.decSpecs_exists (d := 3) (L := 3) (Kc := levelKc 3 3)
    (Cx := Cchi 3 3) (by norm_num) (by norm_num) (levelKc_nonneg 3 3) (Cchi_nonneg 3 3)
  obtain ⟨m₁, h4, hm⟩ := exists_m₁ (max (c * Real.exp ((N0 3 3 : ℝ) * 100000))
    (c₂ * Real.exp ((N0 3 3 : ℝ) * 100000)))
  have hm1 : c * Real.exp ((N0 3 3 : ℝ) * 100000) ≤ (3 : ℝ) ^ m₁ := (le_max_left _ _).trans hm
  have hm2 : c₂ * Real.exp ((N0 3 3 : ℝ) * 100000) ≤ (3 : ℝ) ^ m₁ := (le_max_right _ _).trans hm
  obtain ⟨eps, δ₃, δfl, hnum, hfl⟩ := joint_num_exists 3 3 2 m₁ (by norm_num) hS.fam.2.1
    hS2.fam.2.1 100000 324
  have hev := flCore_level_eventually (N := 2) (dgSetting_GpD h4) (opSetting_HmD h4)
    isLevel_HmD isLevel_GpD (bgHyp_rho m₁) hS (κ := 100000) (by norm_num)
    (by exact_mod_cast hm1) hS2 (by exact_mod_cast hm2)
  obtain ⟨t, ⟨hC⟩, -⟩ := (hev.and (self_mem_nhdsWithin : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
    0 < t)).exists
  refine ⟨m₁, rhoSep m₁, c, BG, 100000, eps, δ₃, c₂, BG₂, eps, δfl,
    bgSetting_data_of h4 hS hm1 hnum, ?_⟩
  exact {
    hS2 := hS2
    SM := hC.SM
    hM2 := by exact_mod_cast hm2
    hPm := precedes_GkD_HmD
    hPmp := isLevel_HmD.precedes isLevel_GpD (by norm_num)
    depm := fun x hx y hy => by
      rw [mem_X1f]
      refine ball_of_dataSite h4 hx ?_
      have h9 := dist_composeDep_hm_le hx hy
      have := le_cellSide h4
      linarith
    num := hfl }

/-- **E-read for the fluctuation composite sites**, on the pair above: the conclusion of
`approxDep_composeDep_hm_subset_X1` at the origin and the site `(1,1,1)`, which lies in the
`1`-block of the origin and has `approxDep Gp` with at least two elements. -/
theorem eReadHm_instance {c BG κ r₀ eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X₀ X₁f : Finset (T m₁)}
    (hB : BgSetting 2 (GpD m₁ ρ) (GkD m₁ ρ) (G0D m₁ ρ) 1 0 c BG κ r₀ eps δ₃ X₀ X₁f 1)
    (hF : FlSetting 2 (GpD m₁ ρ) (GkD m₁ ρ) (HmD m₁ ρ) 1 0 κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f) :
    ∃ x u : T m₁, x ∈ dataSites (GkD m₁ ρ) ∧ u ∈ composeDep (GkD m₁ ρ) (HmD m₁ ρ) x ∧
      u ≠ x ∧ x ∈ approxDep (GpD m₁ ρ) u ∧ approxDep (GpD m₁ ρ) u ⊆ X₁f := by
  classical
  have hx : (0 : T m₁) ∈ dataSites (GkD m₁ ρ) := (mem_dataSites _).2 (Or.inl origin_mem_GkD)
  have hu : one3 m₁ ∈ composeDep (GkD m₁ ρ) (HmD m₁ ρ) 0 := by
    unfold composeDep
    simp only [origin_mem_GkD, ↓reduceIte, Finset.mem_insert, Finset.mem_union,
      GeneratingSet.mem_blk]
    right; right
    rw [(isLevel_HmD (0 : T m₁)).2]
    have := ownBase_jBlock (d := 3) (L := 3) (N₀ := 240 * 3 ^ m₁) (k := 2) (n := 1) (one3 m₁)
    have h0 : ownBase 1 (one3 m₁) = (0 : T m₁) := by
      funext μ
      unfold ownBase
      rw [one3_val]
      simp
    rw [h0] at this
    exact this.symm
  exact ⟨0, one3 m₁, hx, hu, one3_ne_zero m₁, zero_mem_approxDep_one3,
    approxDep_composeDep_hm_subset_X1 hB hF isLevel_GpD hx hu⟩

/-- The fluctuation E-read instance holds on the joint witness. -/
theorem bgFlSetting_data_eRead :
    ∃ (m₁ : ℕ) (ρ c BG κ eps δ₃ c₂ BG₂ δ₁ δfl : ℝ),
      BgSetting 2 (GpD m₁ ρ) (GkD m₁ ρ) (G0D m₁ ρ) 1 0 c BG κ 324 eps δ₃
        (dataSites (GkD m₁ ρ)) (X1f m₁ ρ) 1 ∧
      FlSetting 2 (GpD m₁ ρ) (GkD m₁ ρ) (HmD m₁ ρ) 1 0 κ BG eps δ₃ (levelKc 3 3) (Cchi 3 3)
        c₂ BG₂ δ₁ δfl (X1f m₁ ρ) ∧ X1f m₁ ρ ≠ Finset.univ ∧
      ∃ x u : T m₁, x ∈ dataSites (GkD m₁ ρ) ∧ u ∈ composeDep (GkD m₁ ρ) (HmD m₁ ρ) x ∧
        u ≠ x ∧ x ∈ approxDep (GpD m₁ ρ) u ∧ approxDep (GpD m₁ ρ) u ⊆ X1f m₁ ρ := by
  obtain ⟨m₁, ρ, c, BG, κ, eps, δ₃, c₂, BG₂, δ₁, δfl, hB, hF⟩ := bgFlSetting_data
  obtain ⟨x, u, h1, h2, h3, h4, h5⟩ := eReadHm_instance hB hF
  exact ⟨m₁, ρ, c, BG, κ, eps, δ₃, c₂, BG₂, δ₁, δfl, hB, hF, X1f_ne_univ m₁ ρ, x, u, h1, h2, h3,
    h4, h5⟩

end Fluct

end BgSettingData
end Balaban.Inhabited
