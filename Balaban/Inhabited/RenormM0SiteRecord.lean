/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CoeffFamilyLocExp
public import Balaban.Inhabited.RenormE1SiteRecord
public import Balaban.Inhabited.ObsFamilyJoint
import Mathlib.Tactic.Positivity

/-!
# The physical observable at the renormalized datum as a localized expansion on site domains

For the step `S` of a tower with renormalization data `R`, a fixed source `g` and an abstract
coefficient family `c` with analyticity, exact locality on `sitesOf C`, the bound, the support and
the value identity `M0C = √β_U ∑ c` at every chart datum with constant field, the observable
`M0C` divided by `√β_U`, at the renormalized datum, is a localized expansion on the fibre over the
site sets, at class radius `t / 2`.  Nothing is assumed about the tower's own family; the locality
is a hypothesis on `c`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover

open Classical in
/-- **The observable at the renormalized datum is a localized expansion on site domains, for any
step setting `S` whose renormalized datum at class radius `t / 2` lies in the chart of radius `t`
(`hchart`) and whose block coupling is positive.**  The tower records are the instances at the
step of the tower. -/
theorem renM0_siteRecord_of_chart_rho {d L N N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) {t r : ℝ}
    (hchart : ∀ D : BgData S.G' N, XiCOneReal S.G' S.a S.ν (t / 2) D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r →
      XiCData S.G' S.a S.ν (k + 1) 1 t (renThetaDatum S (t / 2) D ξ))
    (hbU : 0 < S.betaU)
    {κ B : ℝ} (hB : 0 ≤ B)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    (g : Fld d L N₁ m₁ (k + 1) N) (q : ℝ) {ρ : ℝ} (hq : q ≤ ρ) (hg : ∑ x, ∑ j, ‖g x j‖ < q)
    (c : physParam N (S) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physVRho (S) (S).a₁ (S).ν t ρ))
    (hloc : ∀ T, ∀ θ ∈ physVRho (S) (S).a₁ (S).ν t ρ,
      ∀ θ' ∈ physVRho (S) (S).a₁ (S).ν t ρ,
      physRestrict (sitesOf T) (physIncl N (S) θ) =
        physRestrict (sitesOf T) (physIncl N (S) θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physVRho (S) (S).a₁ (S).ν t ρ,
      ∀ T, IsPolyDom m₀ (k + 1) (sitesOf T) → ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physVRho (S) (S).a₁ (S).ν t ρ,
      ∀ T, c θ T ≠ 0 → IsPolyDom m₀ (k + 1) (sitesOf T))
    (hval : ∀ (D' : BgData (S).G' N)
        (hDh : ∀ y i, D'.h y i = ((S).h₀ i : ℂ)),
      XiCData (S).G' (S).a
        (S).ν (k + 1) 1 t D' →
      ((S).withDatum D' hDh).M0C
          (zeroClass d L N₁ m₁ k N ϱ) g y i =
        (((S).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          ∑ C, c (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C) :
    ∃ term, IsLocExp (N := N) (S).G'
      (fun D => XiCOneReal (S).G'
          (S).a (S).ν (t / 2) D ∧
        ∀ x i, D.h x i = (((S).h₀ i : ℝ) : ℂ))
      r
      (Finset.univ.image fun T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (K := k + 1) m₀ (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => x ∈ sitesOf T))
      (renDY (S).G' m₀) κ B
      (fun D ξ => if hD : ∀ x i, D.h x i = (((S).h₀ i : ℝ) : ℂ)
        then ((((S).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ))⁻¹ *
          ((S).withDatum
            (renThetaDatum (S) (t / 2) D ξ) hD).M0C
              (zeroClass d L N₁ m₁ k N ϱ) g y i else 0)
      term := by
  have hg1 : g ∈ l1BallRho d L N₁ m₁ (k + 1) N ρ := lt_of_lt_of_le hg hq
  have hne : (((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hbU _).ne'
  obtain ⟨P, hP⟩ := exists_rawProj (N := N) S.G'
  have h := isLocExp_of_coeffFamily_renTheta_rho S hN (t / 2) _ hB c han hloc hbd hsupp g hg1
    (fun D hD ξ hξ => hchart D hD ξ hξ) P hP
  have h' := h.mono_dom (Dom' := fun D => XiCOneReal (S).G'
          (S).a (S).ν (t / 2) D ∧
        ∀ x i, D.h x i = (((S).h₀ i : ℝ) : ℂ))
    (fun D hD => hD.1)
  refine ⟨_, { h' with sum_eq := ?_ }⟩
  intro D hD ξ hξ
  have hx := hchart D hD.1 ξ hξ
  rw [dite_eq_left_of_eq_true (eq_true hD.2)]
  rw [hval (renThetaDatum (S) (t / 2) D ξ) hD.2 hx,
    ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  exact h'.sum_eq D hD ξ hξ

open Classical in
/-- The landed statement: the case `ρ = 1`. -/
theorem renM0_siteRecord_of_chart {d L N N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) {t r : ℝ}
    (hchart : ∀ D : BgData S.G' N, XiCOneReal S.G' S.a S.ν (t / 2) D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r →
      XiCData S.G' S.a S.ν (k + 1) 1 t (renThetaDatum S (t / 2) D ξ))
    (hbU : 0 < S.betaU)
    {κ B : ℝ} (hB : 0 ≤ B)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    (g : Fld d L N₁ m₁ (k + 1) N) (q : ℝ) (hq : q ≤ 1) (hg : ∑ x, ∑ j, ‖g x j‖ < q)
    (c : physParam N (S) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physV (S)
      (S).a₁ (S).ν t))
    (hloc : ∀ T, ∀ θ ∈ physV (S)
        (S).a₁ (S).ν t,
      ∀ θ' ∈ physV (S)
        (S).a₁ (S).ν t,
      physRestrict (sitesOf T) (physIncl N (S) θ) =
        physRestrict (sitesOf T) (physIncl N (S) θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physV (S)
        (S).a₁ (S).ν t,
      ∀ T, IsPolyDom m₀ (k + 1) (sitesOf T) → ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physV (S)
        (S).a₁ (S).ν t,
      ∀ T, c θ T ≠ 0 → IsPolyDom m₀ (k + 1) (sitesOf T))
    (hval : ∀ (D' : BgData (S).G' N)
        (hDh : ∀ y i, D'.h y i = ((S).h₀ i : ℂ)),
      XiCData (S).G' (S).a
        (S).ν (k + 1) 1 t D' →
      ((S).withDatum D' hDh).M0C
          (zeroClass d L N₁ m₁ k N ϱ) g y i =
        (((S).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          ∑ C, c (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C) :
    ∃ term, IsLocExp (N := N) (S).G'
      (fun D => XiCOneReal (S).G'
          (S).a (S).ν (t / 2) D ∧
        ∀ x i, D.h x i = (((S).h₀ i : ℝ) : ℂ))
      r
      (Finset.univ.image fun T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (K := k + 1) m₀ (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => x ∈ sitesOf T))
      (renDY (S).G' m₀) κ B
      (fun D ξ => if hD : ∀ x i, D.h x i = (((S).h₀ i : ℝ) : ℂ)
        then ((((S).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ))⁻¹ *
          ((S).withDatum
            (renThetaDatum (S) (t / 2) D ξ) hD).M0C
              (zeroClass d L N₁ m₁ k N ϱ) g y i else 0)
      term :=
  renM0_siteRecord_of_chart_rho (ρ := 1) (d := d) (L := L) (N := N) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) (S := S) (m₀ := m₀) (hN := hN) (t := t) (r := r) (hchart := hchart) (hbU := hbU) (κ := κ) (B := B) (hB := hB) (y := y) (i := i) (g := g) (q := q) (hq := hq) (hg := hg) (c := c) (han := han) (hloc := hloc) (hbd := hbd) (hsupp := hsupp) (hval := hval)
open Classical in
/-- **The observable at the renormalized datum is a localized expansion on site domains, general
tower.** -/
theorem StepTowerThetaG.renM0_siteRecord_of_family_rho {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerThetaG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) (hβ : 0 < β)
    {κ B : ℝ} (hB : 0 ≤ B)
    (y : CTorus d L N₁ R.m₁ (k + 1)) (i : Fin N)
    (g : Fld d L N₁ R.m₁ (k + 1) N) (q : ℝ) {ρ : ℝ} (hq : q ≤ ρ) (hg : ∑ x, ∑ j, ‖g x j‖ < q)
    (c : physParam N (R.step k hk N₁ ν β p₁) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physVRho (R.step k hk N₁ ν β p₁) (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t ρ))
    (hloc : ∀ T, ∀ θ ∈ physVRho (R.step k hk N₁ ν β p₁) (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t ρ,
      ∀ θ' ∈ physVRho (R.step k hk N₁ ν β p₁) (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t ρ,
      physRestrict (sitesOf T) (physIncl N (R.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl N (R.step k hk N₁ ν β p₁) θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physVRho (R.step k hk N₁ ν β p₁) (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t ρ,
      ∀ T, IsPolyDom m₀ (k + 1) (sitesOf T) → ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physVRho (R.step k hk N₁ ν β p₁) (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t ρ,
      ∀ T, c θ T ≠ 0 → IsPolyDom m₀ (k + 1) (sitesOf T))
    (hval : ∀ (D' : BgData (R.step k hk N₁ ν β p₁).G' N)
        (hDh : ∀ y i, D'.h y i = ((R.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.step k hk N₁ ν β p₁).G' (R.step k hk N₁ ν β p₁).a
        (R.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
          (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) g y i =
        (((R.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          ∑ C, c (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C) :
    ∃ term, IsLocExp (N := N) (R.step k hk N₁ ν β p₁).G'
      (fun D => XiCOneReal (R.step k hk N₁ ν β p₁).G'
          (R.step k hk N₁ ν β p₁).a (R.step k hk N₁ ν β p₁).ν (R.t / 2) D ∧
        ∀ x i, D.h x i = (((R.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ))
      R.r₀
      (Finset.univ.image fun T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := R.m₁)
          (K := k + 1) m₀ (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus d L N₁ R.m₁ (k + 1) => x ∈ sitesOf T))
      (renDY (R.step k hk N₁ ν β p₁).G' m₀) κ B
      (fun D ξ => if hD : ∀ x i, D.h x i = (((R.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)
        then ((((R.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ))⁻¹ *
          ((R.step k hk N₁ ν β p₁).withDatum
            (renThetaDatum (R.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).M0C
              (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) g y i else 0)
      term := by
  have hbU : 0 < (R.step k hk N₁ ν β p₁).betaU := by
    rw [show (R.step k hk N₁ ν β p₁).betaU = β * (L : ℝ) ^ (k * (d - 2)) from
      hatStepKG_betaU (d := d) (L := L) (N₁ := N₁) R.hN (by have := R.hd; omega)
        k R.m₁ (rhoSepG d L R.m₁) hk ν β p₁ R.δ]
    have := R.hL
    positivity
  exact renM0_siteRecord_of_chart_rho (R.step k hk N₁ ν β p₁) hN
    (fun D hD ξ hξ => R.renDatum_half_mem_xiCData k hk N₁ hν0 hν β p₁ D hD ξ hξ) hbU hB y i g q hq
    hg c han hloc hbd hsupp hval

open Classical in
/-- The landed statement: the case `ρ = 1`. -/
theorem StepTowerThetaG.renM0_siteRecord_of_family {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerThetaG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) (hβ : 0 < β)
    {κ B : ℝ} (hB : 0 ≤ B)
    (y : CTorus d L N₁ R.m₁ (k + 1)) (i : Fin N)
    (g : Fld d L N₁ R.m₁ (k + 1) N) (q : ℝ) (hq : q ≤ 1) (hg : ∑ x, ∑ j, ‖g x j‖ < q)
    (c : physParam N (R.step k hk N₁ ν β p₁) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physV (R.step k hk N₁ ν β p₁)
      (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t))
    (hloc : ∀ T, ∀ θ ∈ physV (R.step k hk N₁ ν β p₁)
        (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t,
      ∀ θ' ∈ physV (R.step k hk N₁ ν β p₁)
        (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t,
      physRestrict (sitesOf T) (physIncl N (R.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl N (R.step k hk N₁ ν β p₁) θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physV (R.step k hk N₁ ν β p₁)
        (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t,
      ∀ T, IsPolyDom m₀ (k + 1) (sitesOf T) → ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physV (R.step k hk N₁ ν β p₁)
        (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t,
      ∀ T, c θ T ≠ 0 → IsPolyDom m₀ (k + 1) (sitesOf T))
    (hval : ∀ (D' : BgData (R.step k hk N₁ ν β p₁).G' N)
        (hDh : ∀ y i, D'.h y i = ((R.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.step k hk N₁ ν β p₁).G' (R.step k hk N₁ ν β p₁).a
        (R.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
          (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) g y i =
        (((R.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          ∑ C, c (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C) :
    ∃ term, IsLocExp (N := N) (R.step k hk N₁ ν β p₁).G'
      (fun D => XiCOneReal (R.step k hk N₁ ν β p₁).G'
          (R.step k hk N₁ ν β p₁).a (R.step k hk N₁ ν β p₁).ν (R.t / 2) D ∧
        ∀ x i, D.h x i = (((R.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ))
      R.r₀
      (Finset.univ.image fun T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := R.m₁)
          (K := k + 1) m₀ (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus d L N₁ R.m₁ (k + 1) => x ∈ sitesOf T))
      (renDY (R.step k hk N₁ ν β p₁).G' m₀) κ B
      (fun D ξ => if hD : ∀ x i, D.h x i = (((R.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)
        then ((((R.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ))⁻¹ *
          ((R.step k hk N₁ ν β p₁).withDatum
            (renThetaDatum (R.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).M0C
              (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) g y i else 0)
      term :=
  StepTowerThetaG.renM0_siteRecord_of_family_rho (ρ := 1) (d := d) (L := L) (N := N) (κmin := κmin) (R := R) (k := k) (hk := hk) (N₁ := N₁) (m₀ := m₀) (hN := hN) (ν := ν) (hν0 := hν0) (hν := hν) (β := β) (p₁ := p₁) (hβ := hβ) (κ := κ) (B := B) (hB := hB) (y := y) (i := i) (g := g) (q := q) (hq := hq) (hg := hg) (c := c) (han := han) (hloc := hloc) (hbd := hbd) (hsupp := hsupp) (hval := hval)
open Classical in
/-- **The observable at the renormalized datum is a localized expansion on site domains.** -/
theorem renM0_siteRecord_of_family_rho {κmin : ℝ} (R : StepTowerTheta κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) (hβ : 0 < β)
    {κ B : ℝ} (hB : 0 ≤ B)
    (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2)
    (g : Fld 3 3 N₁ R.m₁ (k + 1) 2) (q : ℝ) {ρ : ℝ} (hq : q ≤ ρ) (hg : ∑ x, ∑ j, ‖g x j‖ < q)
    (c : physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) →
      Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physVRho (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t ρ))
    (hloc : ∀ T, ∀ θ ∈ physVRho (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t ρ,
      ∀ θ' ∈ physVRho (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t ρ,
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physVRho (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t ρ,
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physVRho (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t ρ,
      ∀ T, c θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hval : ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g y i =
        (((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          ∑ C, c (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C) :
    ∃ term, IsLocExp (N := 2) (R.toStepTower.step k hk N₁ ν β p₁).G'
      (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
          (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν (R.t / 2) D ∧
        ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ))
      R.r₀
      (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T))
      (renDY (R.toStepTower.step k hk N₁ ν β p₁).G' 1) κ B
      (fun D ξ => if hD : ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)
        then ((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ))⁻¹ *
          ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
            (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).M0C
              (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g y i else 0)
      term := by
  have h3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  have hbU : 0 < (R.toStepTower.step k hk N₁ ν β p₁).betaU := by
    rw [show (R.toStepTower.step k hk N₁ ν β p₁).betaU = β * 3 ^ k from
      hatStepK_betaU k R.m₁ hk ν β p₁ R.toStepTower.δ]
    positivity
  exact renM0_siteRecord_of_chart_rho (R.toStepTower.step k hk N₁ ν β p₁) h3
    (fun D hD ξ hξ => R.renDatum_half_mem_xiCData k hk N₁ hν0 hν β p₁ D hD ξ hξ) hbU hB y i g q hq
    hg c han hloc hbd hsupp hval

open Classical in
/-- The landed statement: the case `ρ = 1`. -/
theorem renM0_siteRecord_of_family {κmin : ℝ} (R : StepTowerTheta κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) (hβ : 0 < β)
    {κ B : ℝ} (hB : 0 ≤ B)
    (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2)
    (g : Fld 3 3 N₁ R.m₁ (k + 1) 2) (q : ℝ) (hq : q ≤ 1) (hg : ∑ x, ∑ j, ‖g x j‖ < q)
    (c : physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) →
      Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physV (R.toStepTower.step k hk N₁ ν β p₁)
      (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t))
    (hloc : ∀ T, ∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
      ∀ θ' ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
      ∀ T, c θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hval : ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g y i =
        (((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          ∑ C, c (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C) :
    ∃ term, IsLocExp (N := 2) (R.toStepTower.step k hk N₁ ν β p₁).G'
      (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
          (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν (R.t / 2) D ∧
        ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ))
      R.r₀
      (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T))
      (renDY (R.toStepTower.step k hk N₁ ν β p₁).G' 1) κ B
      (fun D ξ => if hD : ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)
        then ((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ))⁻¹ *
          ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
            (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).M0C
              (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g y i else 0)
      term :=
  renM0_siteRecord_of_family_rho (ρ := 1) (κmin := κmin) (R := R) (k := k) (hk := hk) (N₁ := N₁) (h3N := h3N) (ν := ν) (hν0 := hν0) (hν := hν) (β := β) (p₁ := p₁) (hβ := hβ) (κ := κ) (B := B) (hB := hB) (y := y) (i := i) (g := g) (q := q) (hq := hq) (hg := hg) (c := c) (han := han) (hloc := hloc) (hbd := hbd) (hsupp := hsupp) (hval := hval)
open Classical in
/-- **The observable at the renormalized datum over the union family of the record, general tower.**  The site family of `renM0_siteRecord_of_family` is extended by zero to `renYs ∪ site sets`, the index family of `locDφ` at `(y, i)`. -/
theorem StepTowerThetaG.renM0_siteRecord_union_of_family_rho {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerThetaG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) (hβ : 0 < β)
    {κ B : ℝ} (hB : 0 ≤ B)
    (y : CTorus d L N₁ R.m₁ (k + 1)) (i : Fin N)
    (g : Fld d L N₁ R.m₁ (k + 1) N) (q : ℝ) {ρ : ℝ} (hq : q ≤ ρ) (hg : ∑ x, ∑ j, ‖g x j‖ < q)
    (c : physParam N (R.step k hk N₁ ν β p₁) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physVRho (R.step k hk N₁ ν β p₁) (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t ρ))
    (hloc : ∀ T, ∀ θ ∈ physVRho (R.step k hk N₁ ν β p₁) (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t ρ,
      ∀ θ' ∈ physVRho (R.step k hk N₁ ν β p₁) (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t ρ,
      physRestrict (sitesOf T) (physIncl N (R.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl N (R.step k hk N₁ ν β p₁) θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physVRho (R.step k hk N₁ ν β p₁) (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t ρ,
      ∀ T, IsPolyDom m₀ (k + 1) (sitesOf T) → ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physVRho (R.step k hk N₁ ν β p₁) (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t ρ,
      ∀ T, c θ T ≠ 0 → IsPolyDom m₀ (k + 1) (sitesOf T))
    (hval : ∀ (D' : BgData (R.step k hk N₁ ν β p₁).G' N)
        (hDh : ∀ y i, D'.h y i = ((R.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.step k hk N₁ ν β p₁).G' (R.step k hk N₁ ν β p₁).a
        (R.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
          (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) g y i =
        (((R.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          ∑ C, c (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C) :
    ∃ term, IsLocExp (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
      (fun D => XiCOneReal (R.step k hk N₁ ν β p₁).G'
          (R.step k hk N₁ ν β p₁).a (R.step k hk N₁ ν β p₁).ν (R.t / 2) D ∧
        ∀ x i, D.h x i = (((R.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ))
      R.r₀
      (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) m₀ k (fam m₀ y))) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) m₀
          (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) m₀ k (fam m₀ y)) ∪
        Finset.univ.image fun T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := R.m₁)
          (K := k + 1) m₀ (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus d L N₁ R.m₁ (k + 1) => x ∈ sitesOf T))
      (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) m₀) κ B
      (fun D ξ => if hD : ∀ x i, D.h x i = (((R.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)
        then ((((R.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ))⁻¹ *
          ((R.step k hk N₁ ν β p₁).withDatum
            (renThetaDatum (R.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).M0C
              (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) g y i else 0)
      term := by
  obtain ⟨term, h⟩ := R.renM0_siteRecord_of_family_rho k hk N₁ hN hν0 hν β p₁ hβ hB y i g q hq hg c
    han hloc hbd hsupp hval
  exact ⟨_, h.extend Finset.subset_union_right hB⟩

open Classical in
/-- The landed statement: the case `ρ = 1`. -/
theorem StepTowerThetaG.renM0_siteRecord_union_of_family {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerThetaG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) (hβ : 0 < β)
    {κ B : ℝ} (hB : 0 ≤ B)
    (y : CTorus d L N₁ R.m₁ (k + 1)) (i : Fin N)
    (g : Fld d L N₁ R.m₁ (k + 1) N) (q : ℝ) (hq : q ≤ 1) (hg : ∑ x, ∑ j, ‖g x j‖ < q)
    (c : physParam N (R.step k hk N₁ ν β p₁) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physV (R.step k hk N₁ ν β p₁)
      (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t))
    (hloc : ∀ T, ∀ θ ∈ physV (R.step k hk N₁ ν β p₁)
        (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t,
      ∀ θ' ∈ physV (R.step k hk N₁ ν β p₁)
        (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t,
      physRestrict (sitesOf T) (physIncl N (R.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl N (R.step k hk N₁ ν β p₁) θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physV (R.step k hk N₁ ν β p₁)
        (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t,
      ∀ T, IsPolyDom m₀ (k + 1) (sitesOf T) → ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physV (R.step k hk N₁ ν β p₁)
        (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t,
      ∀ T, c θ T ≠ 0 → IsPolyDom m₀ (k + 1) (sitesOf T))
    (hval : ∀ (D' : BgData (R.step k hk N₁ ν β p₁).G' N)
        (hDh : ∀ y i, D'.h y i = ((R.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.step k hk N₁ ν β p₁).G' (R.step k hk N₁ ν β p₁).a
        (R.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
          (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) g y i =
        (((R.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          ∑ C, c (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C) :
    ∃ term, IsLocExp (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
      (fun D => XiCOneReal (R.step k hk N₁ ν β p₁).G'
          (R.step k hk N₁ ν β p₁).a (R.step k hk N₁ ν β p₁).ν (R.t / 2) D ∧
        ∀ x i, D.h x i = (((R.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ))
      R.r₀
      (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) m₀ k (fam m₀ y))) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) m₀
          (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) m₀ k (fam m₀ y)) ∪
        Finset.univ.image fun T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := R.m₁)
          (K := k + 1) m₀ (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus d L N₁ R.m₁ (k + 1) => x ∈ sitesOf T))
      (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) m₀) κ B
      (fun D ξ => if hD : ∀ x i, D.h x i = (((R.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)
        then ((((R.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ))⁻¹ *
          ((R.step k hk N₁ ν β p₁).withDatum
            (renThetaDatum (R.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).M0C
              (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) g y i else 0)
      term :=
  StepTowerThetaG.renM0_siteRecord_union_of_family_rho (ρ := 1) (d := d) (L := L) (N := N) (κmin := κmin) (R := R) (k := k) (hk := hk) (N₁ := N₁) (m₀ := m₀) (hN := hN) (ν := ν) (hν0 := hν0) (hν := hν) (β := β) (p₁ := p₁) (hβ := hβ) (κ := κ) (B := B) (hB := hB) (y := y) (i := i) (g := g) (q := q) (hq := hq) (hg := hg) (c := c) (han := han) (hloc := hloc) (hbd := hbd) (hsupp := hsupp) (hval := hval)
open Classical in
/-- **The observable at the renormalized datum over the union family of the record.**  The site family of `renM0_siteRecord_of_family` is extended by zero to `renYs ∪ site sets`, the index family of `locDφ` at `(y, i)`. -/
theorem renM0_siteRecord_union_of_family_rho {κmin : ℝ} (R : StepTowerTheta κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) (hβ : 0 < β)
    {κ B : ℝ} (hB : 0 ≤ B)
    (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2)
    (g : Fld 3 3 N₁ R.m₁ (k + 1) 2) (q : ℝ) {ρ : ℝ} (hq : q ≤ ρ) (hg : ∑ x, ∑ j, ‖g x j‖ < q)
    (c : physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) →
      Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physVRho (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t ρ))
    (hloc : ∀ T, ∀ θ ∈ physVRho (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t ρ,
      ∀ θ' ∈ physVRho (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t ρ,
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physVRho (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t ρ,
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physVRho (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t ρ,
      ∀ T, c θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hval : ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g y i =
        (((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          ∑ C, c (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C) :
    ∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
      (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
          (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν (R.t / 2) D ∧
        ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ))
      R.r₀
      (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 y))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 y)) ∪
        Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T))
      (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κ B
      (fun D ξ => if hD : ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)
        then ((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ))⁻¹ *
          ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
            (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).M0C
              (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g y i else 0)
      term := by
  obtain ⟨term, h⟩ := renM0_siteRecord_of_family_rho R k hk N₁ h3N hν0 hν β p₁ hβ hB y i g q hq hg c
    han hloc hbd hsupp hval
  exact ⟨_, h.extend Finset.subset_union_right hB⟩

open Classical in
/-- The landed statement: the case `ρ = 1`. -/
theorem renM0_siteRecord_union_of_family {κmin : ℝ} (R : StepTowerTheta κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) (hβ : 0 < β)
    {κ B : ℝ} (hB : 0 ≤ B)
    (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2)
    (g : Fld 3 3 N₁ R.m₁ (k + 1) 2) (q : ℝ) (hq : q ≤ 1) (hg : ∑ x, ∑ j, ‖g x j‖ < q)
    (c : physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) →
      Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physV (R.toStepTower.step k hk N₁ ν β p₁)
      (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t))
    (hloc : ∀ T, ∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
      ∀ θ' ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
      ∀ T, c θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hval : ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g y i =
        (((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          ∑ C, c (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C) :
    ∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
      (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
          (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν (R.t / 2) D ∧
        ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ))
      R.r₀
      (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 y))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 y)) ∪
        Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T))
      (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) κ B
      (fun D ξ => if hD : ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)
        then ((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ))⁻¹ *
          ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
            (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).M0C
              (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g y i else 0)
      term :=
  renM0_siteRecord_union_of_family_rho (ρ := 1) (κmin := κmin) (R := R) (k := k) (hk := hk) (N₁ := N₁) (h3N := h3N) (ν := ν) (hν0 := hν0) (hν := hν) (β := β) (p₁ := p₁) (hβ := hβ) (κ := κ) (B := B) (hB := hB) (y := y) (i := i) (g := g) (q := q) (hq := hq) (hg := hg) (c := c) (han := han) (hloc := hloc) (hbd := hbd) (hsupp := hsupp) (hval := hval)
end Balaban.Inhabited
