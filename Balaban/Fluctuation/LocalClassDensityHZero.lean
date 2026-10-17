/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityHCont
public import Balaban.Inhabited.OffFibreE1Family
public import Balaban.Inhabited.E0CoeffFamilyG
public import Balaban.Inhabited.StepTowerScale
import Mathlib.Tactic.Linarith

/-!
# The energy coefficient family with its value at every datum of the chart (blocker 6, item (3))

The identity `hDz` on the whole class domain needs the cube-set expansion of the density at every
datum of the chart, any field (`LocalClassDensityHCont`).  For the tower `T` (`d = L = 3`, `N = 2`)
and the class with zero old terms this holds:

* `e0CoeffFamily_raw_fromTower`: one analytic representative bundle `Jr` and, for every root `z`, a
  coefficient family `e = dz + c` (the determinant terms `dz` of `detExpansionLocC_scale_fromTower`
  through `detParamFamily`, the mark coefficients `c` of `e1CoeffFamily_raw_fromTower`), analytic on
  `physV`, local on the thickening of the cubes, bounded by
  `cdet e^{-κ'' d_Ext} + K₀ e^{-κ' d_Ext}`, supported on rooted polymer sets, with
  `E0locJ z (rawOf D) = Σ_C e (rawOf D, 0) C` and `E0locH z = Σ_C e (rawOf D, 0) C` (the new local
  density of the block datum `D`) at **every** datum `D` of the chart, whatever its field.  The
  landed `e0CoeffFamily_value_fromTower` has this value only for `D.h ≡ h₀`.
* `JointRep.densE0_rootSite_eq_sum`: from such a value identity at every datum of the chart, the
  same identity for the density `densE0 Jr` of the class domain at the root sites:
  `densE0 (rootSite z) q = Σ_C e z (clipRaw q, 0) C` for every pair `q` of `Ξ^c_{k+1}(𝔹; 1, ε)`,
  `ε ≤ eps` (with `e0CoeffFamily_raw_fromTower`: the input `hval` of
  `finsum_polysAt_eq_of_rootedSum` for the zero class on the whole class domain).
-/

@[expose] public section

namespace Balaban.Fluctuation.StepSetting.JointRep

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp) (C : StepClass d L N₁ m₁ k N ϱ)

open Classical in
/-- **The input `hval` of `finsum_polysAt_eq_of_rootedSum` on the whole class domain**: if for every
root `z` the representative `E0locJ z` is the sum of a cube-set family `e z` at the raw datum of
every datum of the chart (any field), then at every pair `q` of the class domain
`Ξ^c_{k+1}(𝔹; 1, ε)`, `ε ≤ eps`, the density at the root site is the sum of the family at the
cut-off of `q`. -/
theorem densE0_rootSite_eq_sum {m₀ : ℕ}
    (e : RootIdx d L N₁ m₁ (k + 1) → physParam N S →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ)
    (hval : ∀ z (D : BgData S.G' N), XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      Jr.E0locJ C z (rawOf D) = ∑ T, e z ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), 0) T)
    {ε : ℝ} (hε : ε ≤ eps) {q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hq : XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2) (z : RootIdx d L N₁ m₁ (k + 1)) :
    Jr.densE0 C (rootSite z) q = ∑ T,
      (if h : clipRaw S.G' q ∈ rawSub N S.G' then e z ((⟨clipRaw S.G' q, h⟩ : rawSub N S.G'), 0) T
        else 0) := by
  obtain ⟨D, hD, hcl⟩ := clipRaw_mem_xiCRaw_of_xiDom hε hq
  have hmem : clipRaw S.G' q ∈ rawSub N S.G' := hcl ▸ rawOf_mem_rawSub D
  have hsub : (⟨clipRaw S.G' q, hmem⟩ : rawSub N S.G') = ⟨rawOf D, rawOf_mem_rawSub D⟩ :=
    Subtype.ext hcl
  simp only [hmem, ↓reduceDIte, hsub]
  unfold densE0
  rw [blockIndex_rootSite, hcl]
  exact hval z D hD

end Balaban.Fluctuation.StepSetting.JointRep

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit

open Classical in
/-- **The energy coefficient family of the zero class with its value at every datum of the chart**
(any field).  See the module doc-string. -/
theorem e0CoeffFamily_raw_fromTower {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < (T.step k hk N₁ ν β p₁).p₁ →
        p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      StepScaleData T k hk N₁ ν β p₁ →
      ∃ Jr : (T.step k hk N₁ ν β p₁).JointRep T.t (2 * p₁),
        ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
        ∃ e : physParam 2 (T.step k hk N₁ ν β p₁) →
            Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
              (K := k + 1) 1 (k + 1) Set.univ) → ℂ,
          (∀ C, AnalyticOnNhd ℂ (fun θ => e θ C)
              (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t) ∧
            (∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t,
              ∀ θ' ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t,
              physRestrict (N := 2) (thickSet (T.step k hk N₁ ν β p₁).G'
                  (Yhat Set.univ (sitesOf C))) (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
                physRestrict (thickSet (T.step k hk N₁ ν β p₁).G' (Yhat Set.univ (sitesOf C)))
                  (physIncl 2 (T.step k hk N₁ ν β p₁) θ') → e θ C = e θ' C) ∧
            (∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t,
              ‖e θ C‖ ≤ 27 * covBLogMax 3 3 T.κ /
                  (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)) *
                  Real.exp (-((T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) / 18) *
                    dExt C) +
                K0 3 3 T.κ0 * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, e θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C))) ∧
          ∀ D : BgData (T.step k hk N₁ ν β p₁).G' 2,
            XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
              (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D →
            Jr.E0locJ (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z (rawOf D) =
                ∑ C, e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'),
                  (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) C ∧
              ((T.step k hk N₁ ν β p₁).withDatumH D).E0locH
                  (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z =
                ∑ C, e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'),
                  (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) C := by
  obtain ⟨β₀, h3, H⟩ := e1CoeffFamily_raw_fromTower T hHull hA p
  refine ⟨β₀, h3, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp hp₁ Dt
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, Jr, -, -, -, hz⟩ :=
    H k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp hp₁ Dt
  refine ⟨Jr, fun z => ?_⟩
  obtain ⟨c, -, hcC, hcv⟩ := hz z
  obtain ⟨E, -⟩ := (detExpansionLocC_scale_fromTower T k hk N₁ h3N hN hν0.le hν β p₁).1 z
  obtain ⟨dz, hdz1, hdz2⟩ := detParamFamily (N := 2) E (bgHyp_lv (k := k) T.m₁ hν0.le hν)
  refine ⟨fun θ C => dz θ C + c θ C, fun C => ⟨?_, ?_, ?_, ?_⟩, fun D hX => ?_⟩
  · exact (hdz2 C).1.add (hcC C).1
  · intro θ hθ θ' hθ' h
    have hsub : sitesOf C ⊆ thickSet (T.step k hk N₁ ν β p₁).G' (Yhat Set.univ (sitesOf C)) :=
      fun x hx => Or.inl (by rw [Yhat_univ]; exact hx)
    have h' : physRestrict (N := 2) (sitesOf C) (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf C) (physIncl 2 (T.step k hk N₁ ν β p₁) θ') :=
      funext fun x => congrFun h ⟨x.1, hsub x.2⟩
    show dz θ C + c θ C = dz θ' C + c θ' C
    rw [(hdz2 C).2.1 θ hθ θ' hθ' h, (hcC C).2.1 θ hθ θ' hθ' h']
  · intro θ hθ
    exact (norm_add_le _ _).trans (add_le_add ((hdz2 C).2.2.1 θ hθ) ((hcC C).2.2.1 θ hθ))
  · intro θ hθ
    by_cases h0 : dz θ C = 0
    · have hc0 : c θ C ≠ 0 := by
        intro h1
        exact hθ (show dz θ C + c θ C = 0 by rw [h0, h1, add_zero])
      exact ⟨((hcC C).2.2.2 θ hc0).1, ((hcC C).2.2.2 θ hc0).2.1⟩
    · exact (hdz2 C).2.2.2 θ h0
  · have hroot : Jr.rootTraceJ z (rawOf D) =
        ∑ C, dz ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'),
          (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) C := by
      unfold StepSetting.JointRep.rootTraceJ
      rw [Jr.F₀_eq D hX, E.sum_eq D hX]
      exact Finset.sum_congr rfl fun C _ => (hdz1 D hX _ C).symm
    have hE1 : Jr.E1locJ (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z (rawOf D) =
        ∑ C, c ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'),
          (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) C :=
      (hcv D hX).symm
    have hJ : Jr.E0locJ (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z (rawOf D) =
        ∑ C, (dz ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'),
          (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) C +
          c ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'),
          (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) C) := by
      unfold StepSetting.JointRep.E0locJ
      rw [hroot, hE1, Finset.sum_add_distrib]
    refine ⟨hJ, ?_⟩
    have hβpos : 0 < (T.step k hk N₁ ν β p₁).β :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) (h3.trans hβ)
    have hle : (T.step k hk N₁ ν β p₁).p₁ ≤ 2 * p₁ := by
      have hp' : 0 < p₁ := hp
      change p₁ ≤ 2 * p₁
      linarith
    rw [← Jr.E0locJ_datum (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
      ((T.step k hk N₁ ν β p₁).withDatumH D) hX Dt.core T.large_block T.dom_margin
      T.coer_margin T.δc_small hβpos hp hle
      (fun s _ x _ j _ => StepSetting.analyticAt_Edens_zeroClass j _) z]
    exact hJ

end Balaban.Inhabited
