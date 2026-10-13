/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RenormLabelNonempty
public import Balaban.Inhabited.StepTowerRenEnd
public import Balaban.Inhabited.RenormRadiusDec
public import Balaban.Fluctuation.RenormC1Analytic
public import Balaban.Fluctuation.RenormC1Local
public import Balaban.Fluctuation.RenormRowAgree
public import Balaban.Fluctuation.RenormLocFibre
import Mathlib.Tactic.Linarith

/-!
# Instances of the renormalization localization with a proper root neighbourhood

The earlier instances of `renC1Cut_analytic`, `renC1_local_cut`, `renDec_row_agree` and of the
fibre and domain-parameter lemmas live on the torus of `levelPair`, where the root neighbourhood
`X₁` is the whole torus and the label type `RenLabel` is empty.  Here the same theorems are
instantiated on the torus of `lvTop 18 m₁ 1 (rhoSep m₁)` (scale `k = 1`, `N₁ = 18`, `d = L = 3`),
for a block root `z` and `X₁ = X1 … 1 1 (fam 1 (blockSite 1 z))`, which is a proper subset of the
torus: the label type has at least `27` elements (`renLabel_card_ge`).  The tower is a
`StepTowerRen κmin`.  The mass `ν` is any number with `0 ≤ ν` and `ν * 3 ^ 4 ≤ 1`; the statements
for `ν = 0` follow.

The second part (`renParams_cut_ne_one`) records that cutting one label `i₀` (the far cube
adjacent to `X₁`) changes the vector of decoupling parameters, and that the connected family
`{i₀}` gives the second element of the cover `renYs`.

These are satisfiability checks of the hypotheses of the landed theorems, not physical conclusions.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover

section Setting

variable {κmin : ℝ} (R : StepTowerRen κmin)

local notation "Gt" => lvTop 18 R.m₁ 1 (rhoSep R.m₁)
local notation "Gl" => lvLow 18 R.m₁ 1 (rhoSep R.m₁)

/-- The proper root neighbourhood `X₁` of the block root `z`. -/
local notation "Xr" z => X1 (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) 1 1 (fam 1 (blockSite 1 z))

/-- The `FlCore` of the tower at the scale `k = 1`, `N₁ = 18`. -/
theorem renProper_flCore {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (1 + 1)) ≤ 1) :
    FlCore 2 Gt Gl 1 ν R.c R.BG R.κ R.t (levelKc 3 3) (Cchi 3 3) R.c₂ R.BG₂ R.t :=
  R.flCore_scale 1 le_rfl 18 (by norm_num) hν0 hν

/-- **T1 (i).  The cut functional on a proper `X₁`.**  At `k = 1`, `N₁ = 18`, for every block root
`z`: the label type of `X₁` is nonempty with at least `27` elements, and `renC1Cut_analytic`
holds for the polydisc of the `≥ 27` coordinates. -/
theorem renC1Cut_analytic_proper {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (1 + 1)) ≤ 1)
    (z : Torus 3 (18 * 3 ^ R.m₁ * 3 ^ (1 + 1 - (1 + 1))))
    (B : Finset (Torus 3 (18 * 3 ^ R.m₁ * 3 ^ (1 + 1)))) :
    27 ≤ Fintype.card (RenLabel Gt (Xr z)) ∧
    ∃ F : RawData 3 3 (18 * 3 ^ R.m₁) (1 + 1) 2 × (Fin 3 → ℂ) → (RenLabel Gt (Xr z) → ℂ) → ℂ,
      AnalyticOnNhd ℂ (fun p : (RawData 3 3 (18 * 3 ^ R.m₁) (1 + 1) 2 × (Fin 3 → ℂ)) ×
          (RenLabel Gt (Xr z) → ℂ) => F p.1 p.2)
        (expDom Gt (XiCOneReal Gt (compWeight 3 1) ν R.t) R.r₀ ×ˢ
          polydisc (0 : RenLabel Gt (Xr z) → ℂ) (fun _ => Real.exp R.κ)) ∧
      (∀ D : BgData Gt 2, XiCOneReal Gt (compWeight 3 1) ν R.t D → ∀ ξ : Fin 3 → ℂ,
        ∀ s ∈ polydisc (0 : RenLabel Gt (Xr z) → ℂ) (fun _ => Real.exp R.κ),
          F (rawOf D, ξ) s = renC1Cut Gt (compWeight 3 1) ν R.t (rho4 3 3 2 R.BG R.κ) (Xr z) B D ξ s) ∧
      (∀ D : BgData Gt 2, XiCOneReal Gt (compWeight 3 1) ν R.t D → ∀ ξ : Fin 3 → ℂ,
        renC1Cut Gt (compWeight 3 1) ν R.t (rho4 3 3 2 R.BG R.κ) (Xr z) B D ξ 1 =
          renC1On Gt (compWeight 3 1) ν R.t B D.Ψ D.h
            (bgFieldC Gt (compWeight 3 1) ν (bgC0 3 3 2) D) ξ) := by
  have hC := renProper_flCore R hν0 hν
  refine ⟨renLabel_card_ge z (by norm_num) (by norm_num), ?_⟩
  obtain ⟨F, hF1, hF2⟩ := renC1Cut_analytic hC R.r₀ (Xr z) B
  exact ⟨F, hF1, hF2, fun D hD ξ => renC1Cut_one 1 ν R.t hC hD (Xr z) B ξ⟩

/-- The decoupling parameters of the cut vector `s`. -/
local notation "Ex[" z "," s "]" =>
  extParams (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) (X1 (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) 1 1 (fam 1 (blockSite 1 z)))
    (s ∘ Equiv.symm (renLabelEquiv (lvTop 18 R.m₁ 1 (rhoSep R.m₁))
      (X1 (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) 1 1 (fam 1 (blockSite 1 z)))))

/-- **T1 (ii).  The locality of the cut functional on a proper `X₁`.** -/
theorem renC1_local_cut_proper {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (1 + 1)) ≤ 1)
    (z : Torus 3 (18 * 3 ^ R.m₁ * 3 ^ (1 + 1 - (1 + 1)))) (εζ : ℝ) :
    27 ≤ Fintype.card (RenLabel Gt (Xr z)) ∧
    LocalityAEOn (Real.exp R.κ)
      {u : BgData Gt 2 × (Fin 3 → ℂ) | XiCOneReal Gt (compWeight 3 1) ν R.t u.1}
      (fun i : RenLabel Gt (Xr z) => Pset R.m₁ (renCube Gt (Xr z) i))
      (compY (renCube Gt (Xr z)) (Xr z))
      (RenC1Ag (renCube Gt (Xr z)) (Xr z))
      (fun u s => renC1On Gt (compWeight 3 1) ν εζ (blockSites 3 3 18 R.m₁ (1 + 1) 1 z)
        u.1.Ψ u.1.h
        (decBgField Gt (compWeight 3 1) ν (rho4 3 3 2 R.BG R.κ) (Ex[z, s]) u.1) u.2) :=
  ⟨renLabel_card_ge z (by norm_num) (by norm_num),
    renC1_local_cut (renProper_flCore R hν0 hν) hatConn_lvTop isLevel_lvTop (m₀ := 1) le_rfl
      (by norm_num) z εζ (fun u hu => hu)⟩

/-- **T1 (iii).  The row-data agreement with a cut family of two distinct labels on a proper
`X₁`.**  There is a family `C` of labels with `2 ≤ |C|`, data of `XiCOneReal` exist, and for every
pair of data of `XiCOneReal` agreeing as in `RenC1Ag`, and every pair of cut vectors supported in
`C`, of norm `< e^κ` and equal on the cubes whose patch lies in `compY`, the tuples of mode P
satisfy `DataAgreeRows` on `S_Y`. -/
theorem renDec_row_agree_proper {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (1 + 1)) ≤ 1)
    (z : Torus 3 (18 * 3 ^ R.m₁ * 3 ^ (1 + 1 - (1 + 1)))) (εζ : ℝ) :
    (∃ D : BgData Gt 2, XiCOneReal Gt (compWeight 3 1) ν R.t D) ∧
    ∃ C : Finset (RenLabel Gt (Xr z)), 2 ≤ C.card ∧
      ∀ u u' : BgData Gt 2 × (Fin 3 → ℂ),
        XiCOneReal Gt (compWeight 3 1) ν R.t u.1 → XiCOneReal Gt (compWeight 3 1) ν R.t u'.1 →
        ∀ s s' : RenLabel Gt (Xr z) → ℂ,
        s ∈ supN C (Real.exp R.κ) → s' ∈ supN C (Real.exp R.κ) →
        (∀ i ∈ C, Pset R.m₁ (renCube Gt (Xr z) i) ⊆ compY (renCube Gt (Xr z)) (Xr z) C →
          s i = s' i) →
        RenC1Ag (renCube Gt (Xr z)) (Xr z) C u u' →
        DataAgreeRows Gt (compWeight 3 1) ν 2
          (SY Gt (nbhdF 1 (blockSite 1 z)) (C.image (renCube Gt (Xr z)))
            (finOf (compY (renCube Gt (Xr z)) (Xr z) C)))
          (fun x => decBgMult Gt (compWeight 3 1) ν (rho4 3 3 2 R.BG R.κ) (Ex[z, s]) u.1 x +
            (renMassU ν u.2 - (ν : ℂ)))
          (fun x => decBgMult Gt (compWeight 3 1) ν (rho4 3 3 2 R.BG R.κ) (Ex[z, s']) u'.1 x +
            (renMassU ν u'.2 - (ν : ℂ)))
          (barField Gt u.1.Ψ (decBgField Gt (compWeight 3 1) ν (rho4 3 3 2 R.BG R.κ) (Ex[z, s]) u.1))
          (barField Gt u'.1.Ψ
            (decBgField Gt (compWeight 3 1) ν (rho4 3 3 2 R.BG R.κ) (Ex[z, s']) u'.1))
          (fun x => renZeta εζ u.2 • u.1.Ψ x) (fun x => renZeta εζ u'.2 • u'.1.Ψ x)
          (fun p => (renMassU ν u.2 - (ν : ℂ)) * (u.1.h p.1 p.2 -
            decBgField Gt (compWeight 3 1) ν (rho4 3 3 2 R.BG R.κ) (Ex[z, s]) u.1 p))
          (fun p => (renMassU ν u'.2 - (ν : ℂ)) * (u'.1.h p.1 p.2 -
            decBgField Gt (compWeight 3 1) ν (rho4 3 3 2 R.BG R.κ) (Ex[z, s']) u'.1 p)) := by
  have hC := renProper_flCore R hν0 hν
  have hHB := bgHyp_lv (k := 1) R.m₁ hν0 hν
  have hSD := dgSetting_lv (N₁ := 18) (k := 1) R.m₁_four (by norm_num) hν0 hν
  obtain ⟨hV, -⟩ := renLoc_fin_domains (N := 2) (lvLow 18 R.m₁ 1 (rhoSep R.m₁)) hSD
    isLevel_lvTop (m₀ := 1) le_rfl (by norm_num)
  obtain ⟨hcov, hX₁, -⟩ := hV z
  have hPS : PolySetup Gt 1 (Xr z) := hcov.polySetup
  have hcard := renLabel_card_ge (ϱ := rhoSep R.m₁) (m₁ := R.m₁) (k := 1) z (by norm_num)
    (by norm_num)
  obtain ⟨C, -, hC2⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (RenLabel Gt (Xr z))))
    (n := 2) (by rw [Finset.card_univ]; omega)
  refine ⟨?_, C, hC2.ge, fun u u' hu hu' s s' hs hs' hag hAg => ?_⟩
  · refine exists_xiCOneReal hHB Gt (by norm_num) ?_ R.t_pos
    norm_num at hν ⊢
    linarith
  · exact renDec_row_agree hC hatConn_lvTop isLevel_lvTop hX₁ hPS εζ
      (S := {u : BgData Gt 2 × (Fin 3 → ℂ) | XiCOneReal Gt (compWeight 3 1) ν R.t u.1})
      (fun u hu => hu) C hu hu' hs hs' hag hAg

/-- **T1 (iv).  The sharp bound at the tower with a proper `X₁`.**  `renDec_sharp_scale_of_tower`
at `k = 1`, `N₁ = 18` for the root neighbourhood `X₁` of the block root `z`, together with the
size of the label type. -/
theorem renDec_sharp_proper {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (1 + 1)) ≤ 1)
    (z : Torus 3 (18 * 3 ^ R.m₁ * 3 ^ (1 + 1 - (1 + 1)))) :
    27 ≤ Fintype.card (RenLabel Gt (Xr z)) ∧
    ∃ F : RawData 3 3 (18 * 3 ^ R.m₁) (1 + 1) 2 × (Fin 3 → ℂ) → (RenLabel Gt (Xr z) → ℂ) →
        ((Gt).Ω 1 × Fin 2 → ℂ) × ((Gt).Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData 3 3 (18 * 3 ^ R.m₁) (1 + 1) 2 × (Fin 3 → ℂ)) ×
          (RenLabel Gt (Xr z) → ℂ) => F p.1 p.2)
        (expDom Gt (XiCOneReal Gt (compWeight 3 1) ν R.t) R.r₀ ×ˢ
          polydisc (0 : RenLabel Gt (Xr z) → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData Gt 2, XiCOneReal Gt (compWeight 3 1) ν R.t D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ →
        ∀ s ∈ polydisc (0 : RenLabel Gt (Xr z) → ℂ) (fun _ => Real.exp R.κ),
        ∀ (s' : DecParams Gt) (E : Edat Gt 2), s' = Ex[z, s] →
          E = renEdat ν R.t D (decBgField Gt (compWeight 3 1) ν (rho4 3 3 2 R.BG R.κ) s' D)
            (decBgMult Gt (compWeight 3 1) ν (rho4 3 3 2 R.BG R.κ) s' D) ξ →
          (F (rawOf D, ξ) s).1 = dphi Gt (decG Gt (compWeight 3 1) ν s') E.2.1 E.1
              (pertSource Gt (compWeight 3 1) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
          DecFixed Gt (compWeight 3 1) ν s' false E.2.1 E.1
              (pertSource Gt (compWeight 3 1) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
          Small Gt (F (rawOf D, ξ) s).2 (c6' 3 3 2 (famConst 3 3 R.BG R.κ) (gamma1 3 / 8)) ∧
          Small Gt (F (rawOf D, ξ) s).2 (cK2' 3 3 2 (famConst 3 3 R.BG R.κ) *
            ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * R.t * ‖ξ‖)) ∧
          SupBounds Gt (F (rawOf D, ξ) s).1 (cK2' 3 3 2 (famConst 3 3 R.BG R.κ) *
            ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * R.t * ‖ξ‖)) ∧
          (ξ = 0 → (F (rawOf D, ξ) s).2 = 0 ∧ (F (rawOf D, ξ) s).1 = 0) := by
  refine ⟨renLabel_card_ge z (by norm_num) (by norm_num), ?_⟩
  obtain ⟨F, hF1, hF2⟩ := renDec_sharp_scale_of_tower R 1 le_rfl 18 (by norm_num) hν0 hν (Xr z)
  exact ⟨F, hF1, hF2⟩

end Setting

section Cut

variable {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}

/-- **The far label.**  The label of the cube based at the corner of the root cell moved by
`(9 s, 0, 0)`, `s = 3^{k+1+m₁}`: the cube adjacent to `X₁` used in `renYs_second_element`. -/
def renFarLabel (z : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1)))) (h3 : 3 ∣ N₁)
    (h15 : 15 < N₁) :
    RenLabel (lvTop N₁ m₁ k ϱ) (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))) :=
  ⟨renFarCube z (Pi.single 0 (9 * 3 ^ (k + 1 + m₁))),
    renFarCube_mem z _ (fun μ => by
      by_cases h : μ = 0
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]),
    renFarCube_disjoint z h3 h15 _ (fun μ => by
      by_cases h : μ = 0
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]) 0 (by simp) (by simp; omega)⟩

/-- The cut vector of one label: `0` at `i₀` and `1` elsewhere. -/
noncomputable def renCutVec {G : GeneratingSet 3 3 (N₁ * 3 ^ m₁) (k + 1) ϱ}
    {X₁ : Set (CTorus 3 3 N₁ m₁ (k + 1))} (i₀ : RenLabel G X₁) : RenLabel G X₁ → ℂ :=
  Function.update (fun _ => 1) i₀ 0

/-- **T2 (parameters).**  The decoupling parameters of the cut vector that is `0` at the label
`i₀` and `1` elsewhere equal `0` at the cube of `i₀` and `1` at every other cube; in particular
they differ from the all-ones parameter vector. -/
theorem extParams_renCutVec {G : GeneratingSet 3 3 (N₁ * 3 ^ m₁) (k + 1) ϱ}
    {X₁ : Set (CTorus 3 3 N₁ m₁ (k + 1))} (i₀ : RenLabel G X₁) :
    extParams G X₁ (renCutVec i₀ ∘ Equiv.symm (renLabelEquiv G X₁)) ⟨i₀.1, i₀.2.1⟩ = 0 ∧
    (∀ P : ↥(cubeIdx G), P.1 ≠ i₀.1 →
      extParams G X₁ (renCutVec i₀ ∘ Equiv.symm (renLabelEquiv G X₁)) P = 1) ∧
    extParams G X₁ (renCutVec i₀ ∘ Equiv.symm (renLabelEquiv G X₁)) ≠ fun _ => 1 := by
  classical
  have h0 : extParams G X₁ (renCutVec i₀ ∘ Equiv.symm (renLabelEquiv G X₁))
      ⟨i₀.1, i₀.2.1⟩ = 0 := by
    have := extParams_par (G := G) (renCutVec i₀ ∘ Equiv.symm (renLabelEquiv G X₁))
      (renLabelEquiv G X₁ i₀)
    rw [show ((renLabelEquiv G X₁) i₀).1 = ⟨i₀.1, i₀.2.1⟩ from rfl] at this
    rw [this]
    show renCutVec i₀ ((renLabelEquiv G X₁).symm (renLabelEquiv G X₁ i₀)) = 0
    rw [Equiv.symm_apply_apply]
    simp [renCutVec]
  refine ⟨h0, fun P hP => ?_, fun h => ?_⟩
  · by_cases hd : Disjoint (Pset m₁ P.1) X₁
    · have := extParams_par (G := G) (renCutVec i₀ ∘ Equiv.symm (renLabelEquiv G X₁)) ⟨P, hd⟩
      rw [show (⟨P, hd⟩ : ParIdx G X₁).1 = P from rfl] at this
      rw [this]
      have hne : (⟨P.1, P.2, hd⟩ : RenLabel G X₁) ≠ i₀ := fun he => hP (congrArg Subtype.val he)
      show renCutVec i₀ ⟨P.1, P.2, hd⟩ = 1
      unfold renCutVec
      simp only [Function.update]
      exact dite_eq_right_iff.2 fun h => absurd h hne
    · exact extParams_nonpar _ P hd
  · have := congrFun h ⟨i₀.1, i₀.2.1⟩
    rw [h0] at this
    exact zero_ne_one this

/-- **T2 (the second element of the Y-family).**  For the far label `i₀` (`15 < N₁`, `3 ∣ N₁`),
the domain `Y = Y[{i₀}]` of the connected family `{i₀}` belongs to `renYs` and strictly contains
`X₁`.  (This is the support of the term of the expansion in the single variable `s_{i₀}`: the
coefficient of `s_{i₀}` in the cut family is indexed by this `Y`, cf. `renYs_second_element`.) -/
theorem renFarLabel_Y {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}
    (z : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1)))) (h3 : 3 ∣ N₁) (h15 : 15 < N₁) :
    finOf (Ysites (lvTop N₁ m₁ k ϱ) 1
        (renCube (lvTop N₁ m₁ k ϱ) (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))))
        (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))) {renFarLabel (ϱ := ϱ) z h3 h15}) ∈
        renYs (renCube (lvTop N₁ m₁ k ϱ) (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))))
          (lvTop N₁ m₁ k ϱ) 1 (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))) ∧
      finOf (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))) ⊆
        finOf (Ysites (lvTop N₁ m₁ k ϱ) 1
          (renCube (lvTop N₁ m₁ k ϱ) (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))))
          (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))) {renFarLabel (ϱ := ϱ) z h3 h15}) ∧
      finOf (Ysites (lvTop N₁ m₁ k ϱ) 1
          (renCube (lvTop N₁ m₁ k ϱ) (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))))
          (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))) {renFarLabel (ϱ := ϱ) z h3 h15}) ≠
        finOf (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))) := by
  classical
  set G := lvTop N₁ m₁ k ϱ with hG
  set X := X1 G 1 k (fam 1 (blockSite k z)) with hX
  set i₀ := renFarLabel (ϱ := ϱ) z h3 h15 with hi₀
  have hs : 0 < 3 ^ (k + 1 + m₁) := by positivity
  have ho : ∀ μ, (Pi.single 0 (9 * 3 ^ (k + 1 + m₁)) : Fin 3 → ℕ) μ % 3 ^ (k + 1 + m₁) = 0 := by
    intro μ
    by_cases h : μ = 0
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hmem := i₀.2.1
  have hdis : Disjoint (Pset m₁ (renCube G X i₀)) X := i₀.2.2
  have hbox := renFar_pset_eq_box (N₁ := N₁) (m₁ := m₁) (k := k) z _ ho
  set y0 := (renFarCube z (Pi.single 0 (9 * 3 ^ (k + 1 + m₁)))).2 with hy0
  have hP : Pset m₁ (renCube G X i₀) = box y0 (3 ^ (k + 1 + m₁)) := hbox
  refine ⟨?_, ?_, ?_⟩
  · apply finOf_mem_renYs
    unfold polymerDomains
    rw [Finset.mem_image]
    refine ⟨{i₀}, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i hi x hx
    rw [Finset.mem_singleton] at hi
    subst hi
    have hx' : x ∈ box y0 (3 ^ (k + 1 + m₁)) := by rw [← hP]; exact hx
    have hbV : y0 - Pi.single 0 1 ∈ patchUnion X (fun i => Pset m₁ (renCube G X i)) {i₀} :=
      Or.inl (renFar_pred_mem z h3)
    have hy0V : y0 ∈ patchUnion X (fun i => Pset m₁ (renCube G X i)) {i₀} :=
      Or.inr (by simp only [Set.mem_iUnion, Finset.mem_singleton]; exact ⟨i₀, rfl, self_mem_Pset _⟩)
    have hboxV : box y0 (3 ^ (k + 1 + m₁)) ⊆
        patchUnion X (fun i => Pset m₁ (renCube G X i)) {i₀} := by
      intro y hy
      refine Or.inr ?_
      simp only [Set.mem_iUnion, Finset.mem_singleton]
      exact ⟨i₀, rfl, by rw [hP]; exact hy⟩
    refine ⟨y0 - Pi.single 0 1, renFar_pred_mem z h3, ?_⟩
    have h1 : Relation.ReflTransGen (fun a b => (latGraph 3 ((N₁ * 3 ^ m₁) * 3 ^ (k + 1))).Adj a b ∧
        a ∈ patchUnion X (fun i => Pset m₁ (renCube G X i)) {i₀} ∧
        b ∈ patchUnion X (fun i => Pset m₁ (renCube G X i)) {i₀}) (y0 - Pi.single 0 1) y0 := by
      by_cases he : y0 - Pi.single 0 1 = y0
      · rw [he]
      · exact Relation.ReflTransGen.single ⟨⟨he, ⟨0, Or.inl (by simp)⟩⟩, hbV, hy0V⟩
    exact h1.trans (chain_in_box y0 _ _ hboxV (mem_box_self _ hs) hx')
  · exact Finset.coe_subset.1 (by
      rw [coe_finOf, coe_finOf]; exact subset_Ysites (G := G) (m₀ := 1) (c := renCube G X) X {i₀})
  · intro h
    have h1 : y0 ∈ Ysites G 1 (renCube G X) X {i₀} := by
      refine Or.inr ?_
      simp only [Set.mem_iUnion, Finset.mem_singleton]
      exact ⟨i₀, rfl, Pset_subset_Dsites (layerUnion_of_isLevel isLevel_lvTop 1)
        (by simpa using h3) hmem (self_mem_Pset _)⟩
    have h2 : y0 ∈ finOf (Ysites G 1 (renCube G X) X {i₀}) := by
      rw [← Finset.mem_coe, coe_finOf]; exact h1
    rw [h, ← Finset.mem_coe, coe_finOf] at h2
    exact Set.disjoint_left.1 hdis (self_mem_Pset _) h2

end Cut

section Cut18

variable {κmin : ℝ} (R : StepTowerRen κmin)

/-- **T2 at the tower scale** (`k = 1`, `N₁ = 18`).  For the far label `i₀` of the root `z`:
the decoupling parameters of the cut vector `0` at `i₀`, `1` elsewhere, are `0` at the cube of `i₀`
and `1` at every other cube, so they differ from the all-ones vector (the decoupled operator
`decG` is built from them); and the connected family `{i₀}` gives the element `Y[{i₀}] ⊋ X₁` of
`renYs`. -/
theorem renProper_cut_matters (z : Torus 3 (18 * 3 ^ R.m₁ * 3 ^ (1 + 1 - (1 + 1)))) :
    let i₀ := renFarLabel (ϱ := rhoSep R.m₁) z (by norm_num : 3 ∣ 18) (by norm_num : 15 < 18)
    extParams (lvTop 18 R.m₁ 1 (rhoSep R.m₁))
        (X1 (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) 1 1 (fam 1 (blockSite 1 z)))
        (renCutVec i₀ ∘ Equiv.symm (renLabelEquiv (lvTop 18 R.m₁ 1 (rhoSep R.m₁))
          (X1 (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) 1 1 (fam 1 (blockSite 1 z))))) ⟨i₀.1, i₀.2.1⟩ = 0 ∧
    extParams (lvTop 18 R.m₁ 1 (rhoSep R.m₁))
        (X1 (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) 1 1 (fam 1 (blockSite 1 z)))
        (renCutVec i₀ ∘ Equiv.symm (renLabelEquiv (lvTop 18 R.m₁ 1 (rhoSep R.m₁))
          (X1 (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) 1 1 (fam 1 (blockSite 1 z))))) ≠ (fun _ => 1) ∧
    (finOf (Ysites (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) 1
        (renCube (lvTop 18 R.m₁ 1 (rhoSep R.m₁))
          (X1 (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) 1 1 (fam 1 (blockSite 1 z))))
        (X1 (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) 1 1 (fam 1 (blockSite 1 z))) {i₀}) ∈
        renYs (renCube (lvTop 18 R.m₁ 1 (rhoSep R.m₁))
          (X1 (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) 1 1 (fam 1 (blockSite 1 z))))
          (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) 1
          (X1 (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) 1 1 (fam 1 (blockSite 1 z)))) := by
  intro i₀
  obtain ⟨h1, -, h3⟩ := extParams_renCutVec i₀
  exact ⟨h1, h3, (renFarLabel_Y z (by norm_num) (by norm_num)).1⟩

end Cut18

end Balaban.Inhabited
