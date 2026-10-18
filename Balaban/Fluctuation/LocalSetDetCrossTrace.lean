/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalSetDetCrossCut
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The cross lemma for the rooted trace with its background at the cut points

`H` is the step's level set, `H'` a local generating set whose top domain contains `R`
(`LocalSetDetCrossGeom`, `LocalSetDetCrossCut`).  At cut points `1_I`, `1_{I'}` with the same cubes,
all deep in `R`, for two data of the charts agreeing on `R` and a unit block `y` lying in `R`, the
rooted traces of `y` at the decoupled backgrounds agree (`rootTraceBg_cutPt_cross`):

* if the block of `y` lies in `T = Yreg H (1_I)`, by `decLog_block_cross` for the unit lattices of
  `H` and `H'` matched on the blocks lying in `T` (`T ⊆ R ⊆ Ω_{k+1}(H')`), with the backgrounds of
  `decBg_cutPt_cross`;
* otherwise both are the cut-independent baseline (`decLog_row_eq_baseline_core`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Balaban.LargeField Finset Matrix

section Trace

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' ϱm ϱm' : ℝ}
variable {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Hm' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm'}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ Kc' Cx' c₂' BG₂' δ₁' c₃ : ℝ}

/-- A unit block of `H'` whose sites in `Ω₁(H')` lie in `T` is a unit block of the level set `H`
all of whose sites lie in `T` (the block lies in the top layer of `H'`). -/
theorem unitLabel_level_of_unitLabel (hlev : IsLevel H (k + 1))
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {b : unitPts H'} (hb : unitLabel H' T b) :
    ∃ hb' : (b : UnitTorus d L N₁ m₁ k) ∈ unitPts H, unitLabel H T ⟨b, hb'⟩ := by
  obtain ⟨x, hx, hxb⟩ := (mem_unitPts H').1 b.2
  refine ⟨(mem_unitPts H).2 ⟨x, hlev.mem_layer x, hxb⟩, fun y hy => ?_⟩
  have hyl : (y : CTorus d L N₁ m₁ (k + 1)) ∈ H'.layer (k + 1) :=
    layer_of_unitBlock H' (hxb.trans hy.symm) hx
  exact hb ⟨y, H'.layer_subset (by omega) le_rfl hyl⟩ hy

/-- A unit block of the level set `H` all of whose sites lie in `T ⊆ Ω_{k+1}(H')` is a unit block
of `H'`, all of whose sites in `Ω₁(H')` lie in `T`. -/
theorem unitLabel_of_unitLabel_level {T : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hT : ∀ x ∈ T, x ∈ H'.Ω (k + 1)) (hlev : IsLevel H (k + 1)) {b : unitPts H}
    (hb : unitLabel H T b) :
    ∃ hb' : (b : UnitTorus d L N₁ m₁ k) ∈ unitPts H', unitLabel H' T ⟨b, hb'⟩ := by
  obtain ⟨x, -, hxb⟩ := (mem_unitPts H).1 b.2
  have hxT : x ∈ T := hb ⟨x, (hlev x).1⟩ hxb
  have hxl : x ∈ H'.layer (k + 1) :=
    H'.mem_layer.2 ⟨hT x hxT, by rw [H'.top]; exact Finset.notMem_empty _⟩
  exact ⟨(mem_unitPts H').2 ⟨x, hxl, hxb⟩, fun y hy => hb ⟨y, (hlev y).1⟩ hy⟩

/-- **The rooted traces with their backgrounds of the step and of a local generating set agree at
the cut points** (cut sets with the same cubes, all deep in `R ⊆ Ω_{k+1}(H')`; data agreeing on
`R`; a unit block lying in `R`). -/
theorem rootTraceBg_cutPt_cross (hlev : IsLevel H (k + 1))
    {R : Finset (CTorus d L N₁ m₁ (k + 1))} (hR : ∀ x ∈ R, x ∈ H'.Ω (k + 1))
    (hC : FlCore N H Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N H' Hm' a₁ ν c BG κ eps Kc' Cx' c₂' BG₂' δ₁')
    (hS3 : Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c₃ BG)
    (hM3 : c₃ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hk : 1 ≤ k) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    {I : Finset (cubeIdx H)} {I' : Finset (cubeIdx H')} (hII' : patches I = patches I')
    (hdeep : ∀ P ∈ patches I, ∀ z, supDist z P.2 ≤ 8 * L ^ (k + 1 + m₁) → z ∈ R)
    {D : BgData H N} {D' : BgData H' N} (hD : XiCData H (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData H' (compWeight L a₁) ν (k + 1) 1 eps D')
    (hdat : ∀ z ∈ R, D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z) (y : unitPts H) (y' : unitPts H')
    (hyy : (y : UnitTorus d L N₁ m₁ k) = y')
    (hyR : ∀ x : CTorus d L N₁ m₁ (k + 1), unitBlock x = (y : UnitTorus d L N₁ m₁ k) → x ∈ R) :
    rootTraceBg H (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ H) (unitP H) {y} D (cutPt I) =
      rootTraceBg H' (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ H') (unitP H') {y'} D'
        (cutPt I') := by
  classical
  have hM : 4 * L ^ 2 ≤ L ^ m₁ := hC.Sp.hM
  set T : Finset (CTorus d L N₁ m₁ (k + 1)) := Yreg H (extS H (cutPt I)) with hT
  have hT' : T = Yreg H' (extS H' (cutPt I')) := yreg_cutPt_cross hlev hR hM hII' hdeep
  have hTR : ∀ x ∈ T, x ∈ R := by
    intro x hx
    obtain ⟨P, hP, hxP⟩ := exists_patch_near_of_mem_yreg hlev hM hx
    exact mem_of_near_deep (hdeep P hP) hxP (Nat.mul_le_mul_right _ (by norm_num))
  have hs : ∀ P, ‖cutPt I P‖ < Real.exp κ := norm_cutPt_lt_exp hC.hκ I
  have hs' : ∀ P, ‖cutPt I' P‖ < Real.exp κ := norm_cutPt_lt_exp hC'.hκ I'
  have Hc := covStanding_rootTraceBg hC hk hδc hcap hsm hmar hα hD hs
  have Hc' := covStanding_rootTraceBg hC' hk hδc hcap hsm hmar hα hD' hs'
  obtain ⟨hbgα, hbgφ⟩ := decBg_cutPt_cross hlev hR hC hC' hS3 hM3 hII' hdeep hD hD' hdat
  have hUT : UnionOfTopBlocks H T := unionOfTopBlocks_of_hatDich hC.Sp subset_rfl hatDich_Yreg
  have hUT' : UnionOfTopBlocks H' T := by
    rw [hT']; exact unionOfTopBlocks_of_hatDich hC'.Sp subset_rfl hatDich_Yreg
  unfold rootTraceBg rootTrace
  rw [Finset.sum_singleton, Finset.sum_singleton]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hlab : unitLabel H T y
  · -- the block lies in `T`: the cross lemma for `decLog`
    let e' : {b : unitPts H // unitLabel H T b} → unitPts H' := fun v =>
      ⟨v.1.1, (unitLabel_of_unitLabel_level (fun x hx => hR x (hTR x hx)) hlev v.2).1⟩
    have hei' : Function.Injective e' := by
      intro v w h
      have h1 : ((v.1 : unitPts H) : UnitTorus d L N₁ m₁ k) = (w.1 : unitPts H) :=
        congrArg (fun b : unitPts H' => (b : UnitTorus d L N₁ m₁ k)) h
      exact Subtype.ext (Subtype.ext h1)
    have he' : e' ⟨y, hlab⟩ = y' := Subtype.ext hyy
    rw [← he']
    refine (decLog_block_cross (Dec2.xCover_self (xSetting_of_flCore hC hk))
      (Dec2.xCover_self (xSetting_of_flCore hC' hk))
      (Dec2.FootLocalGeom.of_coverLocalGeom (Dec2.coverLocalGeom_self hC.Sp))
      (Dec2.FootLocalGeom.of_coverLocalGeom (Dec2.coverLocalGeom_self hC'.Sp))
      (Hc.fam 0 le_rfl).pot (Hc'.fam 0 le_rfl).pot
      (fun x hx n hn hnK => layer_iff_of_mem_top hlev (hR _ (hTR x hx)) hn hnK)
      (fun x hx => (Hc.fam x hx.le).isUnit_one_sub) (fun x hx => (Hc'.fam x hx.le).isUnit_one_sub)
      (fun q hq hne => subI_or_disjI_of_hatDich hatDich_Yreg hq hne)
      (fun q hq hne => by rw [hT']; exact subI_or_disjI_of_hatDich hatDich_Yreg hq hne)
      (inner_cutPt_cross hlev hR hM hII' hdeep) (inner'_cutPt_cross hlev hR hM hII' hdeep)
      (fun x hx hx' hxT => (hbgα x hx hx' hxT).symm)
      (fun z hz => by
        have hzΩ : z ∈ H.Ω 1 := (hlev z).1
        have hzΩ' : z ∈ H'.Ω 1 :=
          H'.Ω_antitone le_rfl (by omega) (by omega) (hR _ (hTR z hz))
        funext j
        simp only [barField, hzΩ, hzΩ', ↓reduceDIte]
        exact hbgφ z hzΩ hzΩ' hz j)
      (fun x hx => hRespects_of_hatDich (Hc.fam x hx.le).st hatDich_Yreg)
      (fun x hx => by
        rw [hT']; exact hRespects_of_hatDich (Hc'.fam x hx.le).st hatDich_Yreg)
      (fun x hx => Hc.decM_isUnit' hx.le) (fun x hx => Hc'.decM_isUnit' hx.le)
      (unitLabel H T) (unitLabel H' T) (unitQ H) (unitQ H') (unitP H) (unitP H')
      Subtype.val e' Subtype.val_injective hei' (fun b hb => ⟨⟨b, hb⟩, rfl⟩)
      (fun b hb => by
        obtain ⟨hb', hlab'⟩ := unitLabel_level_of_unitLabel hlev hb
        exact ⟨⟨⟨b, hb'⟩, hlab'⟩, rfl⟩)
      (fun v => v.2) (fun v => (unitLabel_of_unitLabel_level (fun x hx => hR x (hTR x hx))
        hlev v.2).2)
      (unitQ_label_top hUT) (unitQ_label_top hUT') (unitP_label_top hUT) (unitP_label_top hUT')
      (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) ⟨y, hlab⟩ ⟨y, hlab⟩ i i).symm
  · -- the block does not lie in `T`: both are the baseline
    have hlab' : ¬ unitLabel H' T y' := by
      intro h
      apply hlab
      intro z hz
      have hzR := hyR z hz
      exact h ⟨z, H'.Ω_antitone le_rfl (by omega) (by omega) (hR _ hzR)⟩ (hz.trans hyy)
    rw [Hc.decLog_row_eq_baseline_core (unitLabel H T) (unitQ_label_top hUT)
        (unitP_label_top hUT) (p := (y, i)) hlab (y, i),
      Hc'.decLog_row_eq_baseline_core (unitLabel H' T) (by rw [← hT']; exact unitQ_label_top hUT')
        (unitP_label_top hUT') (p := (y', i)) hlab' (y', i)]
    have e1 := one_apply_cross (N := N) (fun _ : Unit => y) (fun _ : Unit => y')
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) () () i i
    have e2 := liftOp_apply_cross (N := N) (P := unitP H) (P' := unitP H') (fun _ : Unit => y)
      (fun _ : Unit => y') (fun _ _ => by simp only [unitP, hyy]) () () i i
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at e1 e2 ⊢
    rw [e1, e2]

end Trace

end Balaban.Fluctuation
