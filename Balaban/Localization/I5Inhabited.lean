/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5
public import Balaban.Localization.I5Fan
public import Balaban.SmallField.Def6Terms
public import Balaban.Localization.CompWeightAdmissible
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity


/-!
# The hypotheses of `i5_background` are jointly satisfiable at positive scale

`I5Witness` bundles the full hypothesis set of `Balaban.Localization.i5_background` for
`d = L = 3`, `N₁ = 6`, `K = 2`, `j = 1`, `m₀ = 0`, `N = 2`, `ν = 0`, `a₁ = 1`: a compatible cover
`CovSetup` (`X` a level-one cube, `𝒦_X = {0}`, `j + 1 = K`), `BgSetting`, `HatConn`, the
tree-length witness `hopt` (`W₀ = {0}`, no bonds), the large-`κ` inequalities and an `𝓔` (here
`𝓔 ≡ 0`) with its analyticity and bound hypotheses.  `Gp` is the whole-lattice set `𝔹_2`
(`Def6.levelGS`), `Gk`, `Gj` have empty positive layers.  `nonempty_i5Witness` proves the bundle is
inhabited and `I5Witness.background` applies `i5_background` to it.
-/

@[expose] public section

namespace Balaban.Localization
namespace I5Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Filter Topology

theorem composedCloseBound_linear (d L N m₁ : ℕ) [NeZero L] (BG κ r₀ eps : ℝ) :
    composedCloseBound d L N m₁ BG κ (xiC1 d * eps) r₀ =
      eps * composedCloseBound d L N m₁ BG κ (xiC1 d) r₀ := by
  unfold composedCloseBound closeConst
  ring

/-- The smallness conditions of `ChainNum` are satisfiable. -/
theorem chainNum_exists (d L N m₁ : ℕ) [NeZero L] (hd : 0 < d) {BG : ℝ} (hBG : 0 ≤ BG) (κ r₀ : ℝ) :
    ∃ eps δ₃ : ℝ, ChainNum d L N m₁ BG κ r₀ eps δ₃ := by
  set A : ℝ := N * composedCloseBound d L N m₁ BG κ (xiC1 d) r₀ with hA
  have hA0 : 0 ≤ A := by
    have := composedCloseBound_nonneg (d := d) (L := L) (N := N) (m₁ := m₁) (κ := κ) (r₀ := r₀)
      hBG (by have := one_le_xiC1 d; linarith) hd
    positivity
  have hT : 0 < thm73C1 d L N := by
    unfold thm73C1
    have := bgC1_pos' (d := d) (L := L) (N := N) hd
    have := bgK1_pos d L N
    have : (8:ℝ) ≤ compC4 d := compC4_ge d
    positivity
  have hc7 := c7_pos (d := d) (L := L) (N := N) (κ := κ) hd hBG
  have hC1 := bgC1_pos' (d := d) (L := L) (N := N) hd
  have hC0 := bgC0_pos d L N hd
  have hds := deltaStar_pos (d := d) (L := L) (N := N) hd
  set C0 := scaledC0 d with hC0def
  set K2 := xiK2 d L N with hK2def
  have key : ∀ᶠ e : ℝ in 𝓝 0,
      (4 * d + 6) * ((2 * d + 1) * e) < 1 ∧ xiC1 d * e < thm73C1 d L N ∧
      xiC1 d * e < c7 d L N BG κ ∧
      (4 * d + 6) * ((2 * d + 1) * (C0 ^ 2 * e)) < 1 ∧ A * e < 1 ∧
      xiC1 d * (C0 ^ 2 * e) + 5 * (A * e) < bgC1 d L N ∧ A * e < deltaStar d L N ∧
      bgK1 d L N * (xiC1 d * (C0 ^ 2 * e)) < deltaStar d L N ∧
      bgK1 d L N * (xiC1 d * (C0 ^ 2 * e)) + cK2 d L N * (A * e) < bgC0 d L N ∧
      (4 * d + 6) * ((2 * d + 1) * (C0 ^ 2 * e + K2 * (A * e))) < 1 ∧
      xiC1 d * (C0 ^ 2 * e + K2 * (A * e)) < thm73C1 d L N := by
    refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simp) |>.and ?_
    refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hT) |>.and ?_
    refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hc7) |>.and ?_
    refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simp) |>.and ?_
    refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simp) |>.and ?_
    refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hC1) |>.and ?_
    refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hds) |>.and ?_
    refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hds) |>.and ?_
    refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hC0) |>.and ?_
    refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simp) |>.and ?_
    exact ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hT)
  have hpos : ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < e := self_mem_nhdsWithin
  obtain ⟨e, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, he⟩ :=
    ((key.filter_mono nhdsWithin_le_nhds).and hpos).exists
  refine ⟨e, A * e, he, h1.le, h2.le, h3.le, h4.le, by positivity, h5.le, h6.le, h7.le, h8.le, h9, h10.le, h11.le, ?_⟩
  rw [composedCloseBound_linear]
  rw [hA]; nlinarith

/-! ### The geometry -/

section Geometry

variable (m₁ : ℕ) (ϱ : ℝ)

/-- The generating set `𝔹_2` of the torus `ℤ_{6·3^{m₁}·3²}^3` (`Ω_1 = Ω_2 = 𝕋`). -/
noncomputable abbrev GP : GeneratingSet 3 3 (6 * 3 ^ m₁) 2 ϱ :=
  Def6.levelGS (d := 3) (L := 3) (N₁ := 6) (m₁ := m₁) (ϱ := ϱ) 2 le_rfl

/-- The generating set with empty positive layers. -/
noncomputable abbrev G0 : GeneratingSet 3 3 (6 * 3 ^ m₁) 2 ϱ :=
  Def6.levelGS (d := 3) (L := 3) (N₁ := 6) (m₁ := m₁) (ϱ := ϱ) 0 (Nat.zero_le _)

variable {m₁ ϱ}

theorem GP_Ω (i : ℕ) : (GP m₁ ϱ).Ω i = if i ≤ 2 then Finset.univ else ∅ := rfl

theorem G0_Ω (i : ℕ) (hi : 1 ≤ i) : (G0 m₁ ϱ).Ω i = ∅ := by
  simp only [G0, Def6.levelGS]
  have : ¬ i ≤ 0 := by omega
  simp [this]

theorem GP_layer_two : (GP m₁ ϱ).layer 2 = Finset.univ := by
  ext x
  simp [GeneratingSet.layer, GP_Ω]

theorem G0_collar : collar (G0 m₁ ϱ) = ∅ := by
  ext x
  simp [mem_collar, G0_Ω _ le_rfl]

theorem G0_dataSites : dataSites (G0 m₁ ϱ) = ∅ := by
  ext x
  simp [mem_dataSites, G0_Ω _ le_rfl, G0_collar]

theorem GP_cubeAligned (h : 2 ≤ m₁) : CubeAligned (GP m₁ ϱ) m₁ where
  two_le := h
  dvd := dvd_mul_left _ _
  union := fun j _ hj x x' _ => by simp [GP_Ω, hj]

theorem GP_layerUnion (m₀ : ℕ) : LayerUnion (GP m₁ ϱ) m₀ := by
  intro n hn1 hnK z hz
  have hn : n = 2 ∨ n = 1 := by omega
  rcases hn with rfl | rfl
  · refine ⟨cbase (cellSide 3 m₀ m₁ 2) z, aligned_cbase z,
      box_mono _ (Nat.le_mul_of_pos_left _ (by norm_num)) (mem_box_cbase (cellSide_pos m₀ m₁ 2) z), ?_⟩
    rw [GP_layer_two]; intro x _; simp
  · exfalso
    simp [GeneratingSet.layer, GP_Ω] at hz


theorem cov_nest (m₀ : ℕ) : ∀ b ∈ ({0} : Set (CTorus 3 3 6 m₁ 2)), ∃ b', Aligned (cellSide 3 m₀ m₁ 2) b' ∧
    box b (3 * cellSide 3 m₀ m₁ 1) ⊆ box b' (3 * cellSide 3 m₀ m₁ 2) ∧
    box b' (3 * cellSide 3 m₀ m₁ 2) ⊆ ((GP m₁ ϱ).layer 2 : Set (CTorus 3 3 6 m₁ 2)) := by
  intro b hb
  refine ⟨b, ?_, ?_, ?_⟩
  · rw [Set.mem_singleton_iff] at hb; subst hb; intro μ; simp
  · refine box_mono _ ?_
    unfold cellSide
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  · rw [GP_layer_two]; intro x _; simp

theorem GP_covSetup :
    CovSetup (GP m₁ ϱ) 0 1 (box (0 : CTorus 3 3 6 m₁ 2) (3 * cellSide 3 0 m₁ 1)) {0} where
  hU := GP_layerUnion 0
  hN := by simp
  hjK := by norm_num
  chosen := ⟨fun b hb => by
      rw [Set.mem_singleton_iff] at hb; subst hb
      exact ⟨fun μ => by simp, subset_rfl⟩,
    fun z hz => ⟨0, rfl, hz⟩⟩
  nest := cov_nest 0


theorem GP_hopt :
    ∃ (W₀ : Finset (CTorus 3 3 6 m₁ 2)) (E₀ : Finset (CTorus 3 3 6 m₁ 2 × CTorus 3 3 6 m₁ 2)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ box (0 : CTorus 3 3 6 m₁ 2) (3 * cellSide 3 0 m₁ 1)) ∧
        MeetsOne 0 1 ({0} : Set (CTorus 3 3 6 m₁ 2)) W₀ ∧
        bondCost (scaleW 3 0 m₁ 1) E₀ =
          treeLenCovOne 0 1 (box (0 : CTorus 3 3 6 m₁ 2) (3 * cellSide 3 0 m₁ 1)) := by
  have h0 : (0 : CTorus 3 3 6 m₁ 2) ∈ box (0 : CTorus 3 3 6 m₁ 2) (3 * cellSide 3 0 m₁ 1) :=
    mem_box_self _ (Nat.mul_pos (by norm_num) (cellSide_pos 0 m₁ 1))
  have hCS : ConnStruct ({0} : Finset (CTorus 3 3 6 m₁ 2)) ∅ := by
    refine ⟨⟨0, by simp⟩, by simp, ?_⟩
    intro x hx y hy
    simp only [Finset.mem_singleton] at hx hy
    subst hx; subst hy; exact Relation.ReflTransGen.refl
  have hM : MeetsOne 0 1 ({0} : Set (CTorus 3 3 6 m₁ 2)) {0} := by
    intro b hb
    rw [Set.mem_singleton_iff] at hb; subst hb
    exact ⟨0, by simp, h0⟩
  refine ⟨{0}, ∅, hCS, by simpa using h0, hM, ?_⟩
  have hc : ChosenOne 0 1 (box (0 : CTorus 3 3 6 m₁ 2) (3 * cellSide 3 0 m₁ 1)) {0} :=
    (GP_covSetup (m₁ := m₁) (ϱ := 0)).chosen
  have hle : treeLenCovOne 0 1 (box (0 : CTorus 3 3 6 m₁ 2) (3 * cellSide 3 0 m₁ 1)) ≤ 0 := by
    refine csInf_le ⟨0, ?_⟩ ⟨{0}, {0}, ∅, hc, hCS, by simpa using h0, hM, by simp [bondCost]⟩
    rintro x ⟨𝒦, W, E, -, -, -, -, rfl⟩
    refine Finset.sum_nonneg fun p _ => ?_
    unfold scaleW; positivity
  have := treeLenCovOne_nonneg (L := 3) (N₁ := 6) (m₁ := m₁) (K := 2) (d := 3) 0 1
    (box (0 : CTorus 3 3 6 m₁ 2) (3 * cellSide 3 0 m₁ 1))
  simp only [bondCost, Finset.sum_empty]
  linarith

theorem GP_hatConn : HatConn (GP m₁ ϱ) := by
  intro q _
  have : hatI (GP m₁ ϱ) q = hatBox q := by
    unfold hatI
    refine Finset.filter_true_of_mem fun x _ => ?_
    simp [GP_Ω]
  rw [this]
  unfold hatBox
  refine boxSet_connected q.2 ?_
  unfold hatRad
  have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (q.1 + m₁) := one_le_pow₀ (by norm_num)
  have : (0 : ℝ) ≤ 3 * (3 : ℝ) ^ 2 * (3 : ℝ) ^ q.1 := by positivity
  push_cast
  linarith

end Geometry

/-! ### The numerical parameters -/

theorem exists_m₁ (x : ℝ) : ∃ m : ℕ, 4 ≤ m ∧ x ≤ (3 : ℝ) ^ m := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 3)
  exact ⟨max n 4, le_max_right _ _, hn.le.trans (pow_le_pow_right₀ (by norm_num) (le_max_left _ _))⟩

/-- The separation constant. -/
noncomputable def rhoSep (m₁ : ℕ) : ℝ :=
  bgR0 3 3 + 36 * 3 ^ m₁ + 324 * 3 ^ m₁ + 1 + 6 * Real.log 3 / (agmonRate 3 / 16)

theorem agmon3_pos : 0 < agmonRate 3 := agmonRate_pos (by norm_num)

theorem rhoSep_tail_nonneg : 0 ≤ 6 * Real.log 3 / (agmonRate 3 / 16) := by
  have := agmon3_pos
  have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  positivity

theorem bgHyp_rho (m₁ : ℕ) : BgHyp 3 3 2 (rhoSep m₁) (compWeight 3 1) 0 where
  hd := le_rfl
  hL := le_rfl
  hϱ := by
    have := rhoSep_tail_nonneg
    unfold rhoSep
    have : (0:ℝ) ≤ 3 ^ m₁ := by positivity
    linarith
  weights := isAdmissibleWeights_compWeight le_rfl (by norm_num) (by norm_num) _
  mass := le_rfl
  massLe := by simp


theorem bgR0_nonneg_aux : 0 ≤ bgR0 3 3 := by
  unfold bgR0; exact le_trans (by norm_num) (le_max_left _ _)

theorem rhoSep_ge (m₁ : ℕ) : 36 * 3 ^ m₁ + 324 * 3 ^ m₁ + 1 +
    6 * Real.log 3 / (agmonRate 3 / 16) ≤ rhoSep m₁ := by
  have := bgR0_nonneg_aux
  unfold rhoSep; linarith

theorem dgSetting_rho {m₁ : ℕ} (h4 : 4 ≤ m₁) :
    DGSetting (GP m₁ (rhoSep m₁)) (compWeight 3 1) 0 where
  hd := le_rfl
  hL := le_rfl
  aligned := GP_cubeAligned (by omega)
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


/-- **The joint hypotheses of `i5_background` at positive scale** (`d = L = 3`, `N₁ = 6`, `K = 2`,
`j = 1`, `m₀ = 0`, `N = 2`, `ν = 0`, `a₁ = 1`): the compatible cover `CovSetup`, the background
setting `BgSetting`, `HatConn`, the tree-length witness `hopt`, the large-`κ` inequalities and an
`𝓔` with its analyticity and bound hypotheses. -/
structure I5Witness where
  m₁ : ℕ
  ϱ : ℝ
  ϱ₁ : ℝ
  ϱ₂ : ℝ
  Gp : GeneratingSet 3 3 (6 * 3 ^ m₁) 2 ϱ
  Gk : GeneratingSet 3 3 (6 * 3 ^ m₁) 2 ϱ₁
  Gj : GeneratingSet 3 3 (6 * 3 ^ m₁) 2 ϱ₂
  c : ℝ
  BG : ℝ
  κ : ℝ
  r₀ : ℝ
  eps : ℝ
  δ₃ : ℝ
  X₀ : Finset (CTorus 3 3 6 m₁ 2)
  X₁f : Finset (CTorus 3 3 6 m₁ 2)
  X : Set (CTorus 3 3 6 m₁ 2)
  𝒦X : Set (CTorus 3 3 6 m₁ 2)
  hB : BgSetting 2 Gp Gk Gj 1 0 c BG κ r₀ eps δ₃ X₀ X₁f 1
  hcov : CovSetup Gp 0 1 X 𝒦X
  hX₁ : (↑X₁f : Set (CTorus 3 3 6 m₁ 2)) = X1 Gp 0 1 𝒦X
  hconn : HatConn Gp
  hopt : ∃ (W₀ : Finset (CTorus 3 3 6 m₁ 2)) (E₀ : Finset (CTorus 3 3 6 m₁ 2 × CTorus 3 3 6 m₁ 2)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne 0 1 𝒦X W₀ ∧
        bondCost (scaleW 3 0 m₁ 1) E₀ = treeLenCovOne 0 1 X
  κdec : ℝ
  κ₀ : ℝ
  Eb : ℝ
  hκ₀ : 0 ≤ κ₀
  hκdec : 3 * κ₀ + 3 ≤ κdec
  hκ : 4 * (3 : ℕ) * ((((2 * 3 + 1) ^ 3 : ℕ)) : ℝ) * κdec ≤ κ
  h1 : 1 ≤ (κ / 2 - 1) / 2
  hlog : Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ 0) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2
  hEb : 0 ≤ Eb
  E : RawData 3 3 (6 * 3 ^ m₁) 2 2 → ℂ
  hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight 3 1) 0 1 (scaledC0 3)
      (scaledC0 3 ^ 2 * eps + xiK2 3 3 2 * δ₃))
  hEbd : ∀ r ∈ XiCRaw Gj (compWeight 3 1) 0 1 (scaledC0 3)
      (scaledC0 3 ^ 2 * eps + xiK2 3 3 2 * δ₃),
      ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne 0 1 X)


namespace I5Witness

variable (W : I5Witness)

/-- The hypotheses of `i5_background` hold for `W`, so its conclusion applies. -/
theorem background :
    ∃ Ev : Set (CTorus 3 3 6 W.m₁ 2) → RawData 3 3 (6 * 3 ^ W.m₁) 2 2 → ℂ,
      (∀ D : BgData W.Gp 2, XiCData W.Gp (compWeight 3 1) 0 2 1 W.eps D →
        W.E (rawOf (composeData W.hB.hq (compWeight 3 1)
          (bgFieldC W.Gk (compWeight 3 1) 0 (bgC0 3 3 2)
            (composeData W.hB.hP (compWeight 3 1)
              (bgFieldC W.Gp (compWeight 3 1) 0 (bgC0 3 3 2) D) D))
          (composeData W.hB.hP (compWeight 3 1)
            (bgFieldC W.Gp (compWeight 3 1) 0 (bgC0 3 3 2) D) D))) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx W.Gp (↑W.X₁f : Set (CTorus 3 3 6 W.m₁ 2)) => i.1.1)
          W.Gp 0 (X1 W.Gp 0 1 W.𝒦X), Ev Y (rawOf D)) ∧
      (∀ Y, ∀ u ∈ XiCRaw W.Gp (compWeight 3 1) 0 2 1 W.eps,
        ∀ u' ∈ XiCRaw W.Gp (compWeight 3 1) 0 2 1 W.eps,
        agreeOn (thickSet W.Gp Y) u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw W.Gp (compWeight 3 1) 0 2 1 W.eps,
        ‖Ev Y u‖ ≤ W.Eb * Real.exp (-W.κ₀ * treeLenCovOne 0 1 W.X -
          2 * W.κdec * treeLenCov W.Gp 0 Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw W.Gp (compWeight 3 1) 0 2 1 W.eps)) :=
  i5_background W.hB W.hcov W.hX₁ W.hconn W.hopt W.hκ₀ W.hκdec W.hκ W.h1 W.hlog W.hEb
    W.hEan W.hEbd

end I5Witness


/-- **The joint hypotheses of `i5_background` are satisfiable at positive scale.** -/
theorem nonempty_i5Witness : Nonempty I5Witness := by
  obtain ⟨c, BG, hS⟩ := decSpecs_exists (d := 3) (L := 3) (by norm_num) (by norm_num)
  have hBG : 0 ≤ BG := hS.fam.2.1
  obtain ⟨m₁, h4, hm⟩ := exists_m₁ (c * Real.exp ((N0 3 3 : ℝ) * 100000))
  obtain ⟨eps, δ₃, hnum⟩ := chainNum_exists 3 3 2 m₁ (by norm_num) hBG 100000 324
  set ρ := rhoSep m₁ with hρ
  have hDG := dgSetting_rho h4
  have hBH := bgHyp_rho m₁
  have hgeq := rhoSep_ge m₁
  have hB : BgSetting 2 (GP m₁ ρ) (G0 m₁ ρ) (G0 m₁ ρ) 1 0 c BG 100000 324 eps δ₃ ∅
      (Set.toFinite (X1 (GP m₁ ρ) 0 1 ({0} : Set (CTorus 3 3 6 m₁ 2)))).toFinset 1 := {
    hS := hS
    Sp := hDG
    ha₁ := one_pos
    HBp := hBH
    HBk := hBH
    HBj := hBH
    hP := by
      intro i hi _
      rw [G0_Ω i hi]; exact Finset.empty_subset _
    hq := by
      intro i hi _
      simp [G0_Ω i hi]
    colk := by intro z hz; rw [G0_collar] at hz; simp at hz
    colj := by intro z hz; rw [G0_collar] at hz; simp at hz
    hκ := by norm_num
    hM := by
      exact_mod_cast hm
    num := hnum
    dsX₀ := by intro x hx; rw [G0_dataSites] at hx; simp at hx
    hN := by intro x hx; simp at hx
    hr := by
      have : (0:ℝ) ≤ 36 * 3 ^ m₁ := by positivity
      have := rhoSep_tail_nonneg
      push_cast
      nlinarith
    hr₀ := by norm_num
    dep := by intro x hx; rw [G0_dataSites] at hx; simp at hx
    hj := by norm_num }
  refine ⟨⟨m₁, ρ, ρ, ρ, GP m₁ ρ, G0 m₁ ρ, G0 m₁ ρ, c, BG, 100000, 324, eps, δ₃, ∅,
    (Set.toFinite (X1 (GP m₁ ρ) 0 1 ({0} : Set (CTorus 3 3 6 m₁ 2)))).toFinset,
    box (0 : CTorus 3 3 6 m₁ 2) (3 * cellSide 3 0 m₁ 1), {0},
    hB, GP_covSetup, Set.Finite.coe_toFinset _, GP_hatConn, GP_hopt, 3, 0, 0, le_rfl,
    by norm_num, by norm_num, by norm_num, ?_, le_rfl, fun _ => 0,
    analyticOnNhd_const, fun r _ => by simp⟩⟩
  have h343 : Real.log (343 : ℝ) ≤ 343 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  norm_num at h343 ⊢
  linarith

end I5Inhabited
end Balaban.Localization
