/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionInhab
public import Balaban.Localization.I5Inhabited
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# The pair of consecutive whole-lattice levels (Proposition 3.3; VACUITY-AUDIT-3, P1)

`interaction_expansion` is stated for the pair `(H⁻, 𝔹_{k+1}) = (Hm, Gp)` with `IsLevel Hm n` and
`IsLevel Gp (n + 1)`: the fluctuation problem of `𝔹_k` (level `n`) is decoupled by the cover of
`𝔹_{k+1}` (level `n + 1`).  The self pair `Hm = Gp` cannot have both levels.  This file proves that
the pair of consecutive levels satisfies the hypotheses on the pair:

* `foldSetting_level`, `cubeBlockBounds_level_exists`: (NC3) for the operator of the level-`n` set
  on the cubes of the cover of the level-`(n + 1)` set (a cube of level `n + 1` is a union of
  `n`-blocks; the reflection estimates of `NC3.lean` apply to it);
* `coverGeom_level`, `coverBase_level`, `footLocal_level`: `CoverBase` and `FootLocal` of
  `(coverOf Gp, Hm)`, with the constants `levelKc d L` and `Cchi d L`;
* `rowInHat_level`: the rows of the operator of `Hm` at the points of a cover cube stay in the
  thickened cube;
* `flCore_level_nonempty`: `FlCore` holds for the pair for all sufficiently small `ε' = δ₁`;
* `interaction_levelPair_witness`: at `d = L = 3`, `K = 2`, `n = 1`, `N₁ = 9`, `m₀ = 1`, the
  hypotheses of `interaction_expansion` on the pair and on the covers of the potential part
  (`FlCore`, `IsLevel`, `BgHyp`, `HatConn`, `RowInHat`, `CovSetup` with `X₁ = 𝕋`, the tree-length
  witness, `d^cov = 0`, `readSites ⊆ X₁`, `BlockMargin`, the `κ`-inequalities and the smallness of
  `δ₁` with `R = 2`) hold jointly.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Reflection Filter Topology

section Fold

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L N₀ k ϱ} {Hm : GeneratingSet d L N₀ k ϱm} {n : ℕ}

/-- A site of a whole-lattice generating set of level `n` lies in no `Ω_i`, `n < i ≤ k + 1`. -/
theorem isLevel_not_mem_Ω (hG : IsLevel Hm n) {i : ℕ} (hi : n + 1 ≤ i) (hik : i ≤ k + 1)
    (x : Torus d (N₀ * L ^ k)) : x ∉ Hm.Ω i := fun hx =>
  ((GeneratingSet.mem_layer Hm).1 (hG.mem_layer x)).2
    (Hm.Ω_antitone (by omega) hi hik hx)

/-- **The reflection setting of a cube for the operator of a finer whole-lattice level**: a cube
with the reflection setting for `Gp` at a fold level `q ≥ n` has it for `Hm` of level `n`
(`Ω₁(Hm)` is the whole torus and `Ω_{q+1}(Hm) = ∅`). -/
theorem foldSetting_level (hG : IsLevel Hm n) {q s : ℕ} {c : Fin d → ℕ}
    (hF : FoldSetting Gp q s c) (hnq : n ≤ q) : FoldSetting Hm q s c where
  one_le_q := hF.one_le_q
  q_le := hF.q_le
  s_pos := hF.s_pos
  side := hF.side
  dvd := hF.dvd
  mem_Ω := fun x _ => (hG x).1
  collar := fun _ _ _ => ⟨(hG _).1, (hG _).1⟩
  noTop := fun x _ => isLevel_not_mem_Ω hG (by omega) (by have := hF.q_le; omega) x

end Fold

section Pair

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {n : ℕ} {a : ℕ → ℝ} {ν : ℝ}

/-- The cubes of the cover of a whole-lattice set of level `n + 1` have level `n + 1`. -/
theorem cubeIdx_level (hG' : IsLevel Gp (n + 1)) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx Gp) : q.1 = n + 1 := by
  obtain ⟨⟨hm1, hmK⟩, hl, -⟩ := (mem_cubeIdx Gp).1 hq
  have := Gp.layerIndex_eq hm1 hmK hl
  rw [(hG' q.2).2] at this
  exact this.symm

/-- **(NC3) for the pair of consecutive levels**: the block bounds of the cube operator of the
level-`n` set `Hm` on the cubes of the cover of the level-`(n + 1)` set `Gp`. -/
theorem cubeBlockBounds_level_exists (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ ϱm : ℝ}
      (Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm)
      {n : ℕ} {a : ℕ → ℝ} {ν : ℝ}, DGSetting Gp a ν → Dec2.OpSetting Hm a ν → IsLevel Hm n →
      IsLevel Gp (n + 1) → ∀ {α : Hm.Ω 1 → ℂ}, AdmPot Hm α →
      ∀ {q : ℕ × CTorus d L N₁ m₁ K}, q ∈ cubeIdx Gp → CubeBlockBounds Hm a ν α q Kc := by
  obtain ⟨K1, hK1, hP⟩ := pointwise_cut_cube (d := d) (L := L) hd hL
  obtain ⟨K2, hK2, hLp⟩ := laplacian_cut_cube (d := d) (L := L) hd hL
  obtain ⟨K3, hK3, hV⟩ := value_cut_cube (d := d) (L := L) hd hL
  refine ⟨K1 + K2 + K3, by positivity, ?_⟩
  intro N₁ m₁ K _ ϱ ϱm Gp Hm n a ν S SH hG hG' α hα q hq
  have hρ1 : 1 ≤ ϱm := SH.one_lt_rho.le
  have hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱm - 1)) := SH.sep_pow (le_of_eq rfl)
  have hq1 := cubeIdx_level hG' hq
  have hn1 := hG.bounds.1
  have hm : 2 ≤ q.1 := by omega
  refine ⟨fun {j'} {y'} hj'1 hj'k hy' hy'b f hsupp {Mf} hMf0 hMf => ?_⟩
  have hF0 : 0 ≤ (L : ℝ) ^ (2 * j') * Mf := by positivity
  have mono : ∀ (K0 : ℝ) (D : ℝ), K0 ≤ K1 + K2 + K3 → 0 ≤ D → ∀ (X : ℝ), 0 ≤ X →
      K0 * D * X ≤ (K1 + K2 + K3) * D * X := by
    intro K0 D h hD X hX
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hD) hX
  have hc := alignedCube_box S hq
  have : NeZero (5 * L ^ (q.1 + m₁ - min K (q.1 + 1))) :=
    ⟨Nat.mul_ne_zero (by norm_num) (pow_ne_zero _ (NeZero.ne L))⟩
  have hF := foldSetting_level hG (hc.foldSetting hm) (by have := hG'.bounds.2; omega)
  have hcb : cubeOf (N₁ * L ^ m₁) L K (min K (q.1 + 1)) (5 * L ^ (q.1 + m₁ - min K (q.1 + 1)))
      (boxCorner q) = intBox q := by
    rw [hc.cubeOf_eq, ← box_eq_cubeSet S.big hq]
  have hyc : y' ∈ cubeOf (N₁ * L ^ m₁) L K (min K (q.1 + 1))
      (5 * L ^ (q.1 + m₁ - min K (q.1 + 1))) (boxCorner q) := by rw [hcb]; exact hy'b
  refine ⟨fun {x} hxΩ hxb => ?_, fun {x} hxΩ hxb hxe μ => ?_, fun {x} hxΩ hxb hxe => ?_⟩
  · have key := hV Hm hF SH.mass SH.massLe SH.weights α hα hρ1 hsep hj'1 hj'k hy' hyc f hsupp hMf0
      hMf (x := x) (by rw [hcb]; exact hxb)
    rw [hcb] at key
    exact key.trans (mono K3 _ (by linarith) (decay_nonneg _ _) _ hF0)
  · have key := hP Hm hF SH.mass SH.massLe SH.weights α hα hρ1 hsep hj'1 hj'k hy' hyc f hsupp hMf0
      hMf (x := x) (by rw [hcb]; exact hxb) (fun ν' => by rw [hcb]; exact hxe ν')
    rw [hcb] at key
    have h1 := grad_le_of_sum (cubeSol Hm a ν (intBox q) α f) (spacing_pos Hm (x := x)).le x μ
    exact (h1.trans key).trans (mono K1 _ (by linarith) (decay_nonneg _ _) _ hF0)
  · have key := hLp Hm hF SH.mass SH.massLe SH.weights α hα hρ1 hsep hj'1 hj'k hy' hyc f hsupp hMf0
      hMf (x := x) (by rw [hcb]; exact hxb) (fun μ => by rw [hcb]; exact hxe μ)
    rw [hcb] at key
    exact key.trans (mono K2 _ (by linarith) (decay_nonneg _ _) _ hF0)

open Classical in
/-- The constant of (NC3) for the pair of consecutive levels (`cubeBlockBounds_level_exists`). -/
noncomputable def levelKc (d L : ℕ) [NeZero L] : ℝ :=
  if h : 3 ≤ d ∧ 3 ≤ L then Classical.choose (cubeBlockBounds_level_exists (d := d) (L := L) h.1 h.2)
  else 0

theorem levelKc_nonneg (d L : ℕ) [NeZero L] : 0 ≤ levelKc d L := by
  unfold levelKc
  split_ifs with h
  · exact (Classical.choose_spec (cubeBlockBounds_level_exists (d := d) (L := L) h.1 h.2)).1
  · exact le_rfl

variable (S : DGSetting Gp a ν) (SH : Dec2.OpSetting Hm a ν) (hG : IsLevel Hm n)
  (hG' : IsLevel Gp (n + 1))
include S SH hG hG'

theorem cubeBlockBounds_level {α : Hm.Ω 1 → ℂ} (hα : AdmPot Hm α) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx Gp) : CubeBlockBounds Hm a ν α q (levelKc d L) := by
  unfold levelKc
  split_ifs with h
  · exact (Classical.choose_spec (cubeBlockBounds_level_exists (d := d) (L := L) h.1 h.2)).2
      Gp Hm S SH hG hG' hα hq
  · exact absurd ⟨S.hd, S.hL⟩ h

/-- **The geometry of the pair `(coverOf Gp, Hm)` of consecutive levels** (`CoverGeom`). -/
theorem coverGeom_level : Dec2.CoverGeom (coverOf Gp) Hm a ν (Cchi d L) := by
  have SG := Dec2.coverGeom_self S
  have hPmp : Precedes Hm Gp := hG.precedes hG' (by have := hG'.bounds.2; omega)
  have hK : n + 1 ≤ K := hG'.bounds.2
  have hsp : ∀ x ∈ Hm.Ω 1, Hm.spacing x ≤ Gp.spacing x := fun x hx =>
    spacing_le_of_prec hPmp hx
  have hδ : 0 ≤ Cchi d L / (L : ℝ) ^ m₁ := by have := Cchi_nonneg d L; positivity
  exact {
    toOpSettingCore := SH.toOpSettingCore
    blockAligned := fun q hq j hj1 hjK x x' hx hbl => by
      have hj : j = n := by rw [← Hm.layerIndex_eq hj1 hjK hx, (hG x).2]
      subst hj
      have hbl' : jBlock d L (N₁ * L ^ m₁) K (j + 1) x' = jBlock d L (N₁ * L ^ m₁) K (j + 1) x :=
        jBlock_eq_of_le (Nat.le_succ j) hK hbl
      exact SG.blockAligned q hq (j + 1) (by omega) hK x x' (hG'.mem_layer x) hbl'
    chi_unit := fun q hq x z hx hz => SG.chi_unit q hq (hPmp.mem_Ω1 hx) hz
    sum_chi := fun x hx => SG.sum_chi x (hPmp.mem_Ω1 hx)
    chi_smooth := fun q hq => by
      have h := SG.chi_smooth q hq
      refine ⟨fun x hx μ => ?_, fun x hx => ?_⟩
      · obtain ⟨h1, h2⟩ := h.grad x (hPmp.mem_Ω1 hx) μ
        have hle : Cchi d L / (L : ℝ) ^ m₁ / Gp.spacing x ≤ Cchi d L / (L : ℝ) ^ m₁ / Hm.spacing x :=
          div_le_div_of_nonneg_left hδ (spacing_pos' Hm x) (hsp x hx)
        exact ⟨h1.trans hle, h2.trans hle⟩
      · have hs2 : Hm.spacing x ^ 2 ≤ Gp.spacing x ^ 2 :=
          pow_le_pow_left₀ (spacing_pos' Hm x).le (hsp x hx) 2
        have hle : Cchi d L / (L : ℝ) ^ m₁ / Gp.spacing x ^ 2 ≤
            Cchi d L / (L : ℝ) ^ m₁ / Hm.spacing x ^ 2 :=
          div_le_div_of_nonneg_left hδ (pow_pos (spacing_pos' Hm x) 2) hs2
        exact (h.lap x (hPmp.mem_Ω1 hx)).trans hle
    inner_near := fun q hq x hx y hy hnear => by
      refine SG.inner_near q hq (hPmp.mem_Ω1 hx) hy ?_
      rcases hnear with h | h
      · exact Or.inl h
      · right
        rw [(hG x).2] at h
        rw [(hG' x).2]
        exact h.mono (pow_dvd_pow L (Nat.le_succ n))
    card_box := fun x hx => SG.card_box x (hPmp.mem_Ω1 hx)
    card_qset := SG.card_qset }

/-- **`CoverBase` for the pair of consecutive levels.** -/
theorem coverBase_level : Dec2.CoverBase (coverOf Gp) Hm a ν (levelKc d L) (Cchi d L) where
  toCoverGeom := coverGeom_level S SH hG hG'
  massLe := SH.massLe
  nc hα _ hq := cubeBlockBounds_level S SH hG hG' hα hq

/-- **`FootLocal` for the pair of consecutive levels.** -/
theorem footLocal_level : Dec2.FootLocal (coverOf Gp) Hm a ν (levelKc d L) (Cchi d L) where
  toCoverBase := coverBase_level S SH hG hG'
  chi_core := (Dec2.footLocalGeom_coverOf Gp).chi_core

omit SH in
/-- **The rows of the operator of `Hm` at the points of a cover cube of `Gp` stay in the thickened
cube** (the `n`-blocks of `Hm` lie in the `(n + 1)`-blocks of `Gp`). -/
theorem rowInHat_level : RowInHat (coverOf Gp) Hm a ν := by
  classical
  intro z hz α x hx y h
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast S.hL
  have hLr : (1 : ℝ) ≤ L := by linarith
  have hLj : (1 : ℝ) ≤ (L : ℝ) ^ z.1 := one_le_pow₀ hLr
  have hbig : (1 : ℝ) ≤ 3 * (L : ℝ) ^ 2 * (L : ℝ) ^ z.1 := by nlinarith
  by_contra hyH
  apply h
  apply dirichlet_entry_eq_zero (G := Hm) α
  · intro hyx
    exact hyH (hyx ▸ box_subset_hatBox z hx)
  · intro μ
    constructor
    · intro hyx
      have hw : ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) =
          (x : CTorus d L N₁ m₁ K) + (intTorus (Pi.single μ (1 : ℤ)) : CTorus d L N₁ m₁ K) := by
        congr 1
        funext ν'
        by_cases h' : ν' = μ <;> simp [intTorus_apply, h']
      refine hyH (hyx ▸ ?_)
      rw [hw]
      refine inBox_hat_of_add_int hx _ (B := 1) (fun ν' => ?_) (by linarith)
      by_cases h' : ν' = μ <;> simp [h']
    · intro hyx
      have hw : ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) =
          (x : CTorus d L N₁ m₁ K) + (intTorus (Pi.single μ (-1 : ℤ)) : CTorus d L N₁ m₁ K) := by
        funext ν'
        by_cases h' : ν' = μ <;> simp [intTorus_apply, h', sub_eq_add_neg]
      refine hyH (hyx ▸ ?_)
      rw [hw]
      refine inBox_hat_of_add_int hx _ (B := 1) (fun ν' => ?_) (by linarith)
      by_cases h' : ν' = μ <;> simp [h']
  · intro hy
    have hy' := Hm.mem_blk.1 hy
    have hK : n + 1 ≤ K := hG'.bounds.2
    have hxl : (x : CTorus d L N₁ m₁ K) ∈ Gp.layer (n + 1) := hG'.mem_layer x
    have hnle := layer_le_of_mem_box S.cover_sep (by have := S.hL; omega) hz (by omega) hK hxl hx
    rw [(hG x).2] at hy'
    have hcell : SameCell (L ^ n) (y : CTorus d L N₁ m₁ K) x :=
      sameCell_of_jBlock_eq (by omega) hy'
    have hlpos : 0 < L ^ n := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
    obtain ⟨w, hw, hwb⟩ := exists_int_of_sameCell hlpos hcell
    refine hyH ?_
    rw [hw]
    refine inBox_hat_of_add_int hx w (B := (L : ℝ) ^ (z.1 + 1)) (fun ν' => ?_) ?_
    · have h1 := hwb ν'
      have h3 : (((L ^ n : ℕ)) : ℝ) = (L : ℝ) ^ n := by push_cast; rfl
      rw [h3] at h1
      exact h1.le.trans (pow_le_pow_right₀ hLr (by omega))
    · have : (L : ℝ) ^ (z.1 + 1) = L * (L : ℝ) ^ z.1 := by ring
      rw [this]
      nlinarith

end Pair

section Core

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}

/-- **`FlCore` for the pair of consecutive levels** `IsLevel Hm n`, `IsLevel Gp (n + 1)` holds for all
sufficiently small `ε' = δ₁ = t > 0`. -/
theorem flCore_level_eventually {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm} {n : ℕ} {a₁ ν : ℝ}
    (S : DGSetting Gp (compWeight L a₁) ν) (SH : Dec2.OpSetting Hm (compWeight L a₁) ν)
    (hG : IsLevel Hm n) (hG' : IsLevel Gp (n + 1)) (HBp : BgHyp d L K ϱ (compWeight L a₁) ν)
    {c BG : ℝ} (hS : DecSpecs d L c BG) {κ : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {c₂ BG₂ : ℝ}
    (hS2 : Dec2.DecSpecs d L (levelKc d L) (Cchi d L) c₂ BG₂)
    (hM2 : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Nonempty (FlCore N Gp Hm a₁ ν c BG κ t (levelKc d L) (Cchi d L) c₂ BG₂ t) := by
  have hd : 0 < d := by have := S.hd; omega
  have hBG := hS.fam.2.1
  have hBG₂ := hS2.fam.2.1
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hBG₂ κ hd; linarith
  have hD1 : 0 < deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8) :=
    deltaStar'_pos hB0 (by have := gamma1_pos hd; positivity)
  have hc7 : 0 < c7 d L N BG κ := c7_pos (d := d) (L := L) (N := N) (κ := κ) hd hBG
  have hK4 : 0 < K4 d L N BG κ := K4_pos hBG hd
  have hc1 := one_le_xiC1 d
  set D1 := deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8) with hD1def
  have e1 := ev_lt (f := fun t : ℝ => t) (by fun_prop) (c := D1) (by simpa using hD1)
  have e2 := ev_lt (f := fun t : ℝ => 2 * (K4 d L N BG κ * (xiC1 d * t))) (by fun_prop) (c := D1)
    (by simpa using hD1)
  have e3 := ev_lt (f := fun t : ℝ => 2 * (K4 d L N BG κ * (xiC1 d * t))) (by fun_prop) (c := 1)
    (by simp)
  have e4 := ev_lt (f := fun t : ℝ => (3 + K4 d L N BG κ) * (xiC1 d * t)) (by fun_prop)
    (c := 1 / 2) (by simp)
  have e5 := ev_lt (f := fun t : ℝ => (4 * d + 6) * ((2 * d + 1) * t)) (by fun_prop) (c := 1)
    (by simp)
  have e6 := ev_lt (f := fun t : ℝ => xiC1 d * t) (by fun_prop) (c := c7 d L N BG κ)
    (by simpa using hc7)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have wk : ∀ {p : ℝ → Prop}, (∀ᶠ t in 𝓝 (0 : ℝ), p t) → ∀ᶠ t in 𝓝[>] (0 : ℝ), p t :=
    fun h => eventually_nhdsWithin_of_eventually_nhds h
  filter_upwards [hpos, wk e1, wk e2, wk e3, wk e4, wk e5, wk e6] with t ht0 h1 h2 h3 h4 h5 h6
  exact ⟨{
    hS := hS, Sp := S, HBp := HBp, hκ := hκ, hM := hM, eps_pos := ht0, small1 := h5.le,
    c7le := h6.le, hS2 := hS2, SM := footLocal_level S SH hG hG', hM2 := hM2,
    hPmp := hG.precedes hG' hG'.bounds.2,
    δ₁_pos := ht0, δ₁_le := h1.le, B_le := h2.le, B_one := h3.le, phi_lt := h4 }⟩

/-- **Inhabitation of `FlCore` for the pair of consecutive levels** `IsLevel Hm n`,
`IsLevel Gp (n + 1)` (hard rule 10, VACUITY-AUDIT-3 P1): some `ε' = δ₁ = t > 0`. -/
theorem flCore_level_nonempty {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm} {n : ℕ} {a₁ ν : ℝ}
    (S : DGSetting Gp (compWeight L a₁) ν) (SH : Dec2.OpSetting Hm (compWeight L a₁) ν)
    (hG : IsLevel Hm n) (hG' : IsLevel Gp (n + 1)) (HBp : BgHyp d L K ϱ (compWeight L a₁) ν)
    {c BG : ℝ} (hS : DecSpecs d L c BG) {κ : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {c₂ BG₂ : ℝ}
    (hS2 : Dec2.DecSpecs d L (levelKc d L) (Cchi d L) c₂ BG₂)
    (hM2 : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) :
    ∃ t : ℝ, 0 < t ∧
      Nonempty (FlCore N Gp Hm a₁ ν c BG κ t (levelKc d L) (Cchi d L) c₂ BG₂ t) :=
  ((flCore_level_eventually (N := N) S SH hG hG' HBp hS hκ hM hS2 hM2).and
    self_mem_nhdsWithin).exists.imp fun _ h => ⟨h.2, h.1⟩

end Core

/-! ### A joint witness at `d = L = 3`, `K = 2`, `n = 1` -/

namespace LevelPair

open I5Inhabited

section Geometry

variable (m₁ : ℕ) (ϱ : ℝ)

/-- `𝔹_{k+1}`: the whole-lattice set of level `2` on the torus `ℤ_{9·3^{m₁}·3²}^3`. -/
noncomputable abbrev Gp : GeneratingSet 3 3 (9 * 3 ^ m₁) 2 ϱ :=
  Def6.levelGS (d := 3) (L := 3) (N₁ := 9) (m₁ := m₁) (ϱ := ϱ) 2 le_rfl

/-- `𝔹_k`: the whole-lattice set of level `1`. -/
noncomputable abbrev Hm : GeneratingSet 3 3 (9 * 3 ^ m₁) 2 ϱ :=
  Def6.levelGS (d := 3) (L := 3) (N₁ := 9) (m₁ := m₁) (ϱ := ϱ) 1 (by norm_num)

variable {m₁ ϱ}

theorem Gp_Ω (i : ℕ) : (Gp m₁ ϱ).Ω i = if i ≤ 2 then Finset.univ else ∅ := rfl

theorem isLevel_Gp : IsLevel (Gp m₁ ϱ) 2 := isLevel_levelGS (by norm_num) le_rfl

theorem isLevel_Hm : IsLevel (Hm m₁ ϱ) 1 := isLevel_levelGS le_rfl (by norm_num)

theorem Gp_layer_two : (Gp m₁ ϱ).layer 2 = Finset.univ := by
  ext x
  simp [GeneratingSet.layer, Gp_Ω]

theorem Gp_cubeAligned (h : 2 ≤ m₁) : CubeAligned (Gp m₁ ϱ) m₁ where
  two_le := h
  dvd := dvd_mul_left _ _
  union := fun j _ hj x x' _ => by simp [Gp_Ω, hj]

theorem Gp_layerUnion : LayerUnion (Gp m₁ ϱ) 1 := by
  intro n hn1 hnK z hz
  have hn : n = 2 ∨ n = 1 := by omega
  rcases hn with rfl | rfl
  · refine ⟨cbase (cellSide 3 1 m₁ 2) z, aligned_cbase z,
      box_mono _ (Nat.le_mul_of_pos_left _ (by norm_num)) (mem_box_cbase (cellSide_pos 1 m₁ 2) z), ?_⟩
    rw [Gp_layer_two]; intro x _; simp
  · exfalso
    simp [GeneratingSet.layer, Gp_Ω] at hz

/-- The box of side `3 · cellSide 3 1 m₁ 2` is the whole torus. -/
theorem box_univ (b : CTorus 3 3 9 m₁ 2) :
    box b (3 * cellSide 3 1 m₁ 2) = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  have hside : 9 * 3 ^ m₁ * 3 ^ 2 = 3 * cellSide 3 1 m₁ 2 := by
    unfold cellSide; ring
  refine ⟨fun μ => ((x - b) μ).val, fun μ => ?_, ?_⟩
  · rw [← hside]; exact ZMod.val_lt _
  · funext μ
    simp [natT_apply]

theorem cov_nest : ∀ b ∈ ({0} : Set (CTorus 3 3 9 m₁ 2)), ∃ b', Aligned (cellSide 3 1 m₁ 2) b' ∧
    box b (3 * cellSide 3 1 m₁ 1) ⊆ box b' (3 * cellSide 3 1 m₁ 2) ∧
    box b' (3 * cellSide 3 1 m₁ 2) ⊆ ((Gp m₁ ϱ).layer 2 : Set (CTorus 3 3 9 m₁ 2)) := by
  intro b hb
  refine ⟨b, ?_, ?_, ?_⟩
  · rw [Set.mem_singleton_iff] at hb; subst hb; intro μ; simp
  · refine box_mono _ ?_
    unfold cellSide
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  · rw [Gp_layer_two]; intro x _; simp

/-- The region `X` of the old term: one cube of `π'_1`. -/
noncomputable abbrev Xr : Set (CTorus 3 3 9 m₁ 2) := box (0 : CTorus 3 3 9 m₁ 2) (3 * cellSide 3 1 m₁ 1)

theorem covSetup : CovSetup (Gp m₁ ϱ) 1 1 Xr {0} where
  hU := Gp_layerUnion
  hN := by norm_num
  hjK := by norm_num
  chosen := ⟨fun b hb => by
      rw [Set.mem_singleton_iff] at hb; subst hb
      exact ⟨fun μ => by simp, subset_rfl⟩,
    fun z hz => ⟨0, rfl, hz⟩⟩
  nest := cov_nest

/-- **`X₁ = 𝕋`**: the `π'_K`-cube containing the cube of `X` is the whole torus. -/
theorem X1_eq_univ : X1 (Gp m₁ ϱ) 1 1 ({0} : Set (CTorus 3 3 9 m₁ 2)) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion₂.2 ⟨0, ⟨fun μ => by simp, ?_, 0, rfl, ?_⟩, ?_⟩
  · rw [Gp_layer_two]; intro y _; simp
  · rw [box_univ]; exact Set.subset_univ _
  · rw [box_univ]; exact Set.mem_univ x

theorem treeLen_zero : treeLenCovOne (L := 3) (N₁ := 9) (m₁ := m₁) (K := 2) (d := 3) 1 1 Xr = 0 := by
  have h0 : (0 : CTorus 3 3 9 m₁ 2) ∈ Xr := mem_box_self _ (Nat.mul_pos (by norm_num) (cellSide_pos 1 m₁ 1))
  have hCS : ConnStruct ({0} : Finset (CTorus 3 3 9 m₁ 2)) ∅ := by
    refine ⟨⟨0, by simp⟩, by simp, ?_⟩
    intro x hx y hy
    simp only [Finset.mem_singleton] at hx hy
    subst hx; subst hy; exact Relation.ReflTransGen.refl
  have hM : MeetsOne 1 1 ({0} : Set (CTorus 3 3 9 m₁ 2)) {0} := by
    intro b hb
    rw [Set.mem_singleton_iff] at hb; subst hb
    exact ⟨0, by simp, h0⟩
  have hc : ChosenOne 1 1 (Xr (m₁ := m₁)) {0} := (covSetup (m₁ := m₁) (ϱ := 0)).chosen
  have hle : treeLenCovOne 1 1 (Xr (m₁ := m₁)) ≤ 0 := by
    refine csInf_le ⟨0, ?_⟩ ⟨{0}, {0}, ∅, hc, hCS, by simpa using h0, hM, by simp [bondCost]⟩
    rintro x ⟨𝒦, W, E, -, -, -, -, rfl⟩
    refine Finset.sum_nonneg fun p _ => ?_
    unfold scaleW; positivity
  exact le_antisymm hle (treeLenCovOne_nonneg 1 1 _)

theorem hopt :
    ∃ (W₀ : Finset (CTorus 3 3 9 m₁ 2)) (E₀ : Finset (CTorus 3 3 9 m₁ 2 × CTorus 3 3 9 m₁ 2)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ Xr (m₁ := m₁)) ∧ MeetsOne 1 1 ({0} : Set (CTorus 3 3 9 m₁ 2)) W₀ ∧
        bondCost (scaleW 3 1 m₁ 1) E₀ = treeLenCovOne 1 1 (Xr (m₁ := m₁)) := by
  have h0 : (0 : CTorus 3 3 9 m₁ 2) ∈ Xr := mem_box_self _ (Nat.mul_pos (by norm_num) (cellSide_pos 1 m₁ 1))
  refine ⟨{0}, ∅, ⟨⟨0, by simp⟩, by simp, ?_⟩, by simpa using h0, ?_, ?_⟩
  · intro x hx y hy
    simp only [Finset.mem_singleton] at hx hy
    subst hx; subst hy; exact Relation.ReflTransGen.refl
  · intro b hb
    rw [Set.mem_singleton_iff] at hb; subst hb
    exact ⟨0, by simp, h0⟩
  · rw [treeLen_zero]; simp [bondCost]

theorem hatConn : HatConn (Gp m₁ ϱ) := by
  intro q _
  have : hatI (Gp m₁ ϱ) q = hatBox q := by
    unfold hatI
    refine Finset.filter_true_of_mem fun x _ => ?_
    simp [Gp_Ω]
  rw [this]
  unfold hatBox
  refine boxSet_connected q.2 ?_
  unfold hatRad
  have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (q.1 + m₁) := one_le_pow₀ (by norm_num)
  have : (0 : ℝ) ≤ 3 * (3 : ℝ) ^ 2 * (3 : ℝ) ^ q.1 := by positivity
  push_cast
  linarith

theorem dgSetting {m₁ : ℕ} (h4 : 4 ≤ m₁) :
    DGSetting (Gp m₁ (rhoSep m₁)) (compWeight 3 1) 0 where
  hd := le_rfl
  hL := le_rfl
  aligned := Gp_cubeAligned (by omega)
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

/-- The operator side for `𝔹_k` (the same separation, mass and weights). -/
theorem opSetting {m₁ : ℕ} (h4 : 4 ≤ m₁) :
    Dec2.OpSetting (Hm m₁ (rhoSep m₁)) (compWeight 3 1) 0 :=
  { hd := (dgSetting h4).hd, hL := (dgSetting h4).hL, mass := (dgSetting h4).mass,
    massLe := (dgSetting h4).massLe, weights := (dgSetting h4).weights, sep := (dgSetting h4).sep }

/-- Every site lies in an interaction cube of the cover of `𝔹_{k+1}`. -/
theorem mem_some_intBox {m₁ : ℕ} (h4 : 4 ≤ m₁) (x : CTorus 3 3 9 m₁ 2) :
    ∃ z ∈ cubeIdx (Gp m₁ (rhoSep m₁)), x ∈ intBox z := by
  classical
  have hs := (Dec2.coverGeom_self (dgSetting h4)).sum_chi x (isLevel_Gp x).1
  obtain ⟨q, hq, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := cubeIdx (Gp m₁ (rhoSep m₁)))
    (f := fun q => chi (Gp m₁ (rhoSep m₁)) q x) (by
      have : ∑ q ∈ cubeIdx (Gp m₁ (rhoSep m₁)), chi (Gp m₁ (rhoSep m₁)) q x = 1 := hs
      rw [this]; norm_num)
  refine ⟨q, hq, mem_intBox.2 ((inBox_of_chi_ne_zero hne).mono ?_)⟩
  have : (0 : ℝ) ≤ (3 : ℝ) ^ (q.1 + m₁) := by positivity
  push_cast
  linarith

end Geometry

/-- **The pair hypotheses of `interaction_expansion` hold jointly at a pair of consecutive
levels** (`d = L = 3`, `K = 2`, `n = 1`, `N₁ = 9`, `a₁ = 1`, `ν = 0`, `m₀ = 1`, `N` arbitrary):
`𝔹_k = levelGS 1`, `𝔹_{k+1} = levelGS 2`, `FlCore` with the constants `levelKc 3 3`,
`Cchi 3 3`, `IsLevel` of both, `BgHyp` of `𝔹_k`, `HatConn`, `RowInHat`, and the cover data of
every block `z` of the potential part (the same cover for every `z`): `CovSetup` with the region
`X₁ = 𝕋`, the tree-length witness `hopt`, `d^cov_j(X) = 0`, the `κ`-inequalities with
`κ_dec = 3`, `κ₀ = 0`, the read sites in `X₁`, `BlockMargin`, and the smallness conditions `hRs`,
`hsmall`, `hnum`, `hnum'` of `interaction_expansion` with `R = 2`. -/
theorem interaction_levelPair_witness (N : ℕ) :
    ∃ (m₁ : ℕ) (ϱ c BG κ eps c₂ BG₂ δ₁ κdec κ₀ : ℝ),
      FlCore N (Gp m₁ ϱ) (Hm m₁ ϱ) 1 0 c BG κ eps (levelKc 3 3) (Cchi 3 3) c₂ BG₂ δ₁ ∧
      IsLevel (Hm m₁ ϱ) 1 ∧ IsLevel (Gp m₁ ϱ) (1 + 1) ∧
      BgHyp 3 3 2 ϱ (compWeight 3 1) 0 ∧ HatConn (Gp m₁ ϱ) ∧
      RowInHat (coverOf (Gp m₁ ϱ)) (Hm m₁ ϱ) (compWeight 3 1) 0 ∧
      CovSetup (Gp m₁ ϱ) 1 1 Xr ({0} : Set (CTorus 3 3 9 m₁ 2)) ∧
      (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)) =
        X1 (Gp m₁ ϱ) 1 1 ({0} : Set (CTorus 3 3 9 m₁ 2)) ∧
      (∃ (W₀ : Finset (CTorus 3 3 9 m₁ 2)) (E₀ : Finset (CTorus 3 3 9 m₁ 2 × CTorus 3 3 9 m₁ 2)),
        ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ Xr (m₁ := m₁)) ∧ MeetsOne 1 1 ({0} : Set (CTorus 3 3 9 m₁ 2)) W₀ ∧
          bondCost (scaleW 3 1 m₁ 1) E₀ = treeLenCovOne 1 1 (Xr (m₁ := m₁))) ∧
      treeLenCovOne 1 1 (Xr (m₁ := m₁)) = 0 ∧
      0 ≤ κ₀ ∧ 3 * κ₀ + 3 ≤ κdec ∧ 4 * 3 * ((((2 * 3 + 1) ^ 3 : ℕ)) : ℝ) * κdec ≤ κ ∧
      1 ≤ (κ / 2 - 1) / 2 ∧
      Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ 1) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2 ∧
      (∀ z : Torus 3 (9 * 3 ^ m₁ * 3 ^ (2 - (1 + 1))),
        readSites (Hm m₁ ϱ) 1 z ⊆ ↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2))) ∧
      (∀ z : Torus 3 (9 * 3 ^ m₁ * 3 ^ (2 - (1 + 1))),
        BlockMargin (Gp m₁ ϱ) (Finset.univ : Finset (CTorus 3 3 9 m₁ 2))
          (↑(blockSites 3 3 9 m₁ 2 1 z) : Set (CTorus 3 3 9 m₁ 2))) ∧
      2 * δ₁ ≤ deltaStar 3 3 N ∧ cK2 3 3 N * (2 * δ₁) < bgC0 3 3 N / 2 ∧
      cK2 3 3 N * δ₁ ≤ c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8) ∧
      cK2' 3 3 N (famConst 3 3 BG₂ κ) * δ₁ ≤ c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8) := by
  obtain ⟨c, BG, hS⟩ := decSpecs_exists (d := 3) (L := 3) (by norm_num) (by norm_num)
  obtain ⟨c₂, BG₂, hS2⟩ := Dec2.decSpecs_exists (d := 3) (L := 3) (Kc := levelKc 3 3)
    (Cx := Cchi 3 3) (by norm_num) (by norm_num) (levelKc_nonneg 3 3) (Cchi_nonneg 3 3)
  obtain ⟨m₁, h4, hm⟩ := exists_m₁ (max (c * Real.exp ((N0 3 3 : ℝ) * 100000))
    (c₂ * Real.exp ((N0 3 3 : ℝ) * 100000)))
  have S := dgSetting h4
  have SH := opSetting h4
  have hev := flCore_level_eventually (N := N) S SH isLevel_Hm isLevel_Gp (bgHyp_rho m₁)
    hS (κ := 100000) (by norm_num) ((le_max_left _ _).trans (by exact_mod_cast hm)) hS2
    ((le_max_right _ _).trans (by exact_mod_cast hm))
  have hB0 : 0 ≤ famConst 3 3 BG₂ 100000 := by
    have := famConst_ge_one (L := 3) hS2.fam.2.1 100000 (d := 3) (by norm_num); linarith
  have hc6 : 0 < c6' 3 3 N (famConst 3 3 BG₂ 100000) (gamma1 3 / 8) :=
    c6'_pos hB0 (by have := gamma1_pos (d := 3) (by norm_num); positivity)
  have hDs : 0 < deltaStar 3 3 N := deltaStar_pos (d := 3) (L := 3) (N := N) (by norm_num)
  have hC0 : 0 < bgC0 3 3 N := bgC0_pos 3 3 N (by norm_num)
  have wk : ∀ {p : ℝ → Prop}, (∀ᶠ t in 𝓝 (0 : ℝ), p t) → ∀ᶠ t in 𝓝[>] (0 : ℝ), p t :=
    fun h => eventually_nhdsWithin_of_eventually_nhds h
  have e1 := ev_lt (f := fun t : ℝ => 2 * t) (by fun_prop) (c := deltaStar 3 3 N) (by simpa using hDs)
  have e2 := ev_lt (f := fun t : ℝ => cK2 3 3 N * (2 * t)) (by fun_prop) (c := bgC0 3 3 N / 2)
    (by simp; positivity)
  have e3 := ev_lt (f := fun t : ℝ => cK2 3 3 N * t) (by fun_prop)
    (c := c6' 3 3 N (famConst 3 3 BG₂ 100000) (gamma1 3 / 8)) (by simpa using hc6)
  have e4 := ev_lt (f := fun t : ℝ => cK2' 3 3 N (famConst 3 3 BG₂ 100000) * t) (by fun_prop)
    (c := c6' 3 3 N (famConst 3 3 BG₂ 100000) (gamma1 3 / 8)) (by simpa using hc6)
  obtain ⟨t, ⟨hC⟩, g1, g2, g3, g4⟩ := (hev.and ((wk e1).and ((wk e2).and ((wk e3).and
    (wk e4))))).exists
  have h343 : Real.log (9261 : ℝ) ≤ 9261 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  refine ⟨m₁, rhoSep m₁, c, BG, 100000, t, c₂, BG₂, t, 3, 0, hC, isLevel_Hm, isLevel_Gp,
    bgHyp_rho m₁, hatConn, rowInHat_level S isLevel_Hm isLevel_Gp, covSetup, ?_, hopt,
    treeLen_zero, le_rfl, by norm_num, by norm_num, by norm_num, ?_,
    fun z _ _ => Finset.mem_coe.2 (Finset.mem_univ _),
    fun z => blockMargin_univ fun x _ _ => mem_some_intBox h4 x, g1.le, g2, g3.le, g4.le⟩
  · rw [Finset.coe_univ, X1_eq_univ]
  · norm_num at h343 ⊢
    linarith

end LevelPair

end Balaban.Localization
