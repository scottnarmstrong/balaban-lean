/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalSetDetCrossGeom
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The cross lemma for the decoupled background at the cut points

`H` is the step's level set (`IsLevel H (k + 1)`), `H'` a generating set (a local generating set
`𝔹_{k+1}(Y)`) whose top domain contains a set `R` of sites; both carry the standing hypotheses
`FlCore` of the chart with the same constants `a₁, ν, c, BG, κ, eps`.  At cut points `1_I`, `1_{I'}`
with the same cubes (`patches I = patches I'`), all deep in `R` (`LocalSetDetCrossGeom`), and two
data of the charts agreeing on `R`, the decoupled backgrounds agree on the region
`T = Yreg H (1_I)` of the active centres (`decBg_cutPt_cross`): the landed
`Dec2.decBg_component_cross` for the self covers `coverOf H`, `coverOf H'`, with `T` and the set
`Y` of the sites within `5 M₁ L^{k+1}` of the cubes of `I`.  The constants of the decoupled
problem enter through one `Dec2.DecSpecs` at the self-cover constants `(selfKc d L, Cchi d L)` with
the `BG` of the chart (`hS3`, `hM3`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Balaban.LargeField Finset

section Bg

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' ϱm ϱm' : ℝ}
variable {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Hm' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm'}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ Kc' Cx' c₂' BG₂' δ₁' c₃ : ℝ}

omit [NeZero N₁] [NeZero L] in
/-- A site within `r ≤ 8 M₁ L^{k+1}` of a deep base lies in `R`. -/
theorem mem_of_near_deep {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    {P : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hP : ∀ z, supDist z P.2 ≤ 8 * L ^ (k + 1 + m₁) → z ∈ R) {z : CTorus d L N₁ m₁ (k + 1)}
    {r : ℕ} (hz : supDist z P.2 ≤ r) (hr : r ≤ 8 * L ^ (k + 1 + m₁)) : z ∈ R :=
  hP z (hz.trans hr)

omit [NeZero N₁] [NeZero L] in
/-- `L^{k+1} ≤ M₁ L^{k+1}`. -/
theorem pow_le_pow_add_m (hL : 1 ≤ L) : L ^ (k + 1) ≤ L ^ (k + 1 + m₁) :=
  Nat.pow_le_pow_right hL (by omega)

/-- **The decoupled backgrounds of the two generating sets agree at the cut points** on the region
`T = Yreg H (1_I)` of the active centres (multiplier and field), for cut sets with the same cubes,
all deep in `R ⊆ Ω_{k+1}(H')`, and two data of the charts agreeing on `R`. -/
theorem decBg_cutPt_cross (hlev : IsLevel H (k + 1))
    {R : Finset (CTorus d L N₁ m₁ (k + 1))} (hR : ∀ x ∈ R, x ∈ H'.Ω (k + 1))
    (hC : FlCore N H Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N H' Hm' a₁ ν c BG κ eps Kc' Cx' c₂' BG₂' δ₁')
    (hS3 : Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c₃ BG)
    (hM3 : c₃ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {I : Finset (cubeIdx H)} {I' : Finset (cubeIdx H')} (hII' : patches I = patches I')
    (hdeep : ∀ P ∈ patches I, ∀ z, supDist z P.2 ≤ 8 * L ^ (k + 1 + m₁) → z ∈ R)
    {D : BgData H N} {D' : BgData H' N} (hD : XiCData H (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData H' (compWeight L a₁) ν (k + 1) 1 eps D')
    (hdat : ∀ z ∈ R, D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z) :
    (∀ (x : CTorus d L N₁ m₁ (k + 1)) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1),
      x ∈ Yreg H (extS H (cutPt I)) →
        decBgMult H' (compWeight L a₁) ν (rho4 d L N BG κ) (cutPt I') D' ⟨x, hx'⟩ =
          decBgMult H (compWeight L a₁) ν (rho4 d L N BG κ) (cutPt I) D ⟨x, hx⟩) ∧
    (∀ (x : CTorus d L N₁ m₁ (k + 1)) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1),
      x ∈ Yreg H (extS H (cutPt I)) → ∀ i : Fin N,
        decBgField H' (compWeight L a₁) ν (rho4 d L N BG κ) (cutPt I') D' (⟨x, hx'⟩, i) =
          decBgField H (compWeight L a₁) ν (rho4 d L N BG κ) (cutPt I) D (⟨x, hx⟩, i)) := by
  classical
  have hM : 4 * L ^ 2 ≤ L ^ m₁ := hC.Sp.hM
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hLk := pow_le_pow_add_m (k := k) (m₁ := m₁) hL1
  set ℓ : ℕ := L ^ (k + 1 + m₁) with hℓ
  have hℓ1 : 1 ≤ ℓ := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  set T : Finset (CTorus d L N₁ m₁ (k + 1)) := Yreg H (extS H (cutPt I)) with hT
  have hT' : T = Yreg H' (extS H' (cutPt I')) := yreg_cutPt_cross hlev hR hM hII' hdeep
  set Y : Finset (CTorus d L N₁ m₁ (k + 1)) :=
    Finset.univ.filter fun z => ∃ P ∈ patches I, supDist z P.2 ≤ 5 * ℓ with hY
  have hTY : T ⊆ Y := by
    intro x hx
    obtain ⟨P, hP, hxP⟩ := exists_patch_near_of_mem_yreg hlev hM hx
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, P, hP, by omega⟩
  -- sites near `Y` lie in `R`
  have hnear : ∀ y ∈ Y, ∀ z, supDist z y ≤ 3 * ℓ → z ∈ R := by
    intro y hy z hz
    obtain ⟨P, hP, hyP⟩ := (Finset.mem_filter.1 hy).2
    refine mem_of_near_deep (hdeep P hP) ((supDist_triangle z y P.2).trans
      (Nat.add_le_add hz hyP)) (by omega)
  have hYin : ∀ y ∈ Y, y ∈ R := fun y hy => hnear y hy y (by rw [supDist_self]; exact Nat.zero_le _)
  -- the two backgrounds
  have hs : ∀ P, ‖cutPt I P‖ < Real.exp κ := norm_cutPt_lt_exp hC.hκ I
  have hs' : ∀ P, ‖cutPt I' P‖ < Real.exp κ := norm_cutPt_lt_exp hC'.hκ I'
  obtain ⟨φ, α, hI, h1, h2⟩ := exists_isDecBg_of_flCore hC hs hD
  obtain ⟨φ', α', hI', h1', h2'⟩ := exists_isDecBg_of_flCore hC' hs' hD'
  obtain ⟨hδ0, hδ0', hδ1, hνε⟩ := xiC_numerics hC
  obtain ⟨hδ0'', hδ0''', hδ1', hνε'⟩ := xiC_numerics hC'
  -- the active centres are deep
  have hact_deep : ∀ q ∈ cubeIdx H, sProd H (extS H (cutPt I)) q ≠ 0 →
      ∀ z, supDist z q.2 ≤ 8 * ℓ → z ∈ R := fun q hq hne =>
    hdeep q (mem_patches_of_mem_Zs_cutPt (Finset.mem_filter.2 ⟨hq, hne⟩))
  have hact' : ∀ q ∈ cubeIdx H', sProd H' (extS H' (cutPt I')) q ≠ 0 →
      q ∈ cubeIdx H ∧ sProd H (extS H (cutPt I)) q ≠ 0 := by
    intro q hq hne
    have hz : q ∈ Zs H' (extS H' (cutPt I')) := Finset.mem_filter.2 ⟨hq, hne⟩
    rw [← zs_cutPt_cross hlev hR hM hII' hdeep] at hz
    exact Finset.mem_filter.1 hz
  have hhatT : ∀ q ∈ cubeIdx H, sProd H (extS H (cutPt I)) q ≠ 0 → ∀ x ∈ hatBox q, x ∈ T := by
    intro q hq hne x hx
    refine hatI_subset_Yreg_of_active hq hne ?_
    unfold hatI
    exact Finset.mem_filter.2 ⟨hx, (hlev x).1⟩
  have key := Dec2.decBg_component_cross hS3 (Dec2.coverBase_self hC.Sp)
    (Dec2.coverBase_self hC'.Sp) hC.HBp hC'.HBp hC.hκ.le hM3 (fun P => (hs P).le)
    (fun P => (hs' P).le) hδ0 le_rfl hδ0' hδ1 hνε hδ0'' le_rfl hδ0''' hδ1' hνε'
    (xiCData_inDomainC hC.HBp hC.small1 hD) (xiCData_inDomainC hC'.HBp hC'.small1 hD') hTY
    (fun y hy n hn hnK => layer_iff_of_mem_top hlev (hR _ (hYin y hy)) hn hnK)
    (fun q hq hne => subI_or_disjI_of_hatDich hatDich_Yreg hq hne)
    (fun q hq hne => by
      rw [hT']
      exact subI_or_disjI_of_hatDich hatDich_Yreg hq hne)
    (fun q hq hne x _ hx => hhatT q hq hne x (box_subset_hatBox q hx))
    (fun q hq hne x _ hx => by
      obtain ⟨hqc, hne'⟩ := hact' q hq hne
      exact hhatT q hqc hne' x (box_subset_hatBox q hx))
    (fun q hq hne => by
      have hqc : q ∈ cubeIdx H := (Finset.mem_filter.1 hq).1
      have hd := hact_deep q hqc hne
      have hq1 := fst_eq_of_mem_cubeIdx_level hlev hqc
      have hqc' : q ∈ cubeIdx H' :=
        (mem_cubeIdx_iff_of_top hlev (hR _ (hd q.2 (by rw [supDist_self]; exact Nat.zero_le _)))).1
          hqc
      refine ⟨Finset.mem_filter.2 ⟨hqc', fun y hy => hhatT q hqc hne y (box_subset_hatBox q hy)⟩,
        (sProd_cutPt_cross hlev hR hM hII' hqc hd).symm, ?_, fun x₀ hx₀ => ?_⟩
      · intro x₀ hx₀ y hy n hn hnK
        have h0 := supDist_le_of_mem_intBox_top hM hq1 hx₀
        have hy1 : supDist y x₀ ≤ 1 := by
          rcases hy with rfl | ⟨μ, rfl | rfl⟩
          · rw [supDist_self]; exact Nat.zero_le _
          · rw [supDist_comm]; exact supDist_add_single_le x₀ μ
          · rw [supDist_comm]; exact supDist_sub_single_le x₀ μ
        have hyR : y ∈ R := mem_of_near_deep hd ((supDist_triangle y x₀ q.2).trans
          (Nat.add_le_add hy1 h0)) (by omega)
        exact layer_iff_of_mem_top hlev (hR _ hyR) hn hnK
      · exact chi_eq_of_deep hlev hR hd (by
          have := supDist_le_of_mem_intBox_top hM hq1 hx₀; omega) q)
    (fun q hq hne => by
      obtain ⟨hqc, hne'⟩ := hact' q (Finset.mem_filter.1 hq).1 hne
      exact ⟨Finset.mem_filter.2 ⟨hqc, fun y hy => hhatT q hqc hne' y (box_subset_hatBox q hy)⟩,
        hne'⟩)
    (fun x hx _ y hy => by
      obtain ⟨P, hP, hxP⟩ := exists_patch_near_of_mem_yreg hlev hM hx
      refine ⟨(hlev y).1, Finset.mem_filter.2 ⟨Finset.mem_univ _, P, hP, ?_⟩⟩
      have h1 := supDist_le_of_mem_resSites hy
      have h1' : supDist y x ≤ L ^ (k + 1) := by rw [supDist_comm]; exact h1
      have h2 := (supDist_triangle y x P.2).trans (Nat.add_le_add h1' hxP)
      omega)
    (fun y hy _ q hq1 hqK hb n hn hnK => by
      have h1 := supDist_le_of_bump_ne_zero hb
      have h2 : 2 * L ^ q.1 ≤ 2 * ℓ :=
        Nat.mul_le_mul_left 2 ((Nat.pow_le_pow_right hL1 hqK).trans hLk)
      exact layer_iff_of_mem_top hlev (hR _ (hnear y hy q.2 (by
        rw [supDist_comm]; omega))) hn hnK)
    (fun y hy _ z hz => by
      have h1 := supDist_le_of_mem_approxDep hz
      have h2 : 2 * L ^ (k + 1) ≤ 2 * ℓ := Nat.mul_le_mul_left 2 hLk
      exact hdat z (hnear y hy z (by rw [supDist_comm]; omega)))
    ((dec2_isDecBg_iff H _ _ _ _ _ _ _).2 hI) ((dec2_isDecBg_iff H' _ _ _ _ _ _ _).2 hI')
  rw [h1, h2, h1', h2']
  exact ⟨fun x hx hx' hxT => key.1 x hx hx' hxT,
    fun x hx hx' hxT i => key.2 x hx hx' (hTY hxT) i⟩

end Bg

end Balaban.Fluctuation
