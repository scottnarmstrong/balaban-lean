/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RawAgreeSites
public import Balaban.Fluctuation.RenormThetaDatum
public import Balaban.Inhabited.StepTowerRadius
import Mathlib.Tactic.Positivity

/-!
# A coefficient family on cube sets as a localized expansion

A family `c : physParam N S → Finset 𝔅 → ℂ` of coefficients indexed by finite sets `T` of cubes,
analytic in the parameter on the admissible set `physV`, bounded by `B exp(-κ dExt T)`, supported on
polymer cube sets, and local on the sites `sitesOf T` (a hypothesis on the family) is regrouped, along
the injective map `T ↦ sitesOf T`, into a localized expansion `IsLocExp` indexed by the finite
family of site domains with the size functional `renDY`.

* `isLocExp_of_coeffFamily`: evaluation through an analytic map `Φ` into the parameter space;
* `exists_rawProj`: a continuous linear retraction of the raw data onto the relative subspace;
* `isLocExp_of_coeffFamily_datum`: evaluation at the datum itself with a fixed source `g₀`;
* `isLocExp_of_coeffFamily_renTheta`: evaluation at the renormalized datum `((1 + ζ(ξ)) Ψ, h)`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Multiscale

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

section Generic

variable (S : StepSetting d L N₁ m₁ k N ϱ) {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ

open Classical in
/-- **A coefficient family on cube sets is a localized expansion on site domains.**  The family
`c θ T` is analytic in `θ` on `physV`, local on `sitesOf T`, bounded by `B exp(-κ dExt T)` on polymer
cube sets and zero off them; `Φ` is analytic on `expDom`, maps it into `physV` and respects
restriction to every set of sites.  The domains are the site sets of all cube sets. -/
theorem isLocExp_of_coeffFamily (hN : L ^ m₀ ∣ N₁) {a₁ ν eps r κ B : ℝ}
    (Dom : BgData S.G' N → Prop) (hB : 0 ≤ B)
    (c : physParam N S → Finset 𝔅 → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physV S a₁ ν eps))
    (hloc : ∀ T, ∀ θ ∈ physV S a₁ ν eps, ∀ θ' ∈ physV S a₁ ν eps,
      physRestrict (sitesOf T) (physIncl N S θ) = physRestrict (sitesOf T) (physIncl N S θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physV S a₁ ν eps, ∀ T, IsPolyDom m₀ (k + 1) (sitesOf T) →
      ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physV S a₁ ν eps, ∀ T, c θ T ≠ 0 → IsPolyDom m₀ (k + 1) (sitesOf T))
    (Φ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ) → physParam N S)
    (hΦan : AnalyticOnNhd ℂ Φ (expDom S.G' Dom r))
    (hΦdom : ∀ q ∈ expDom S.G' Dom r, Φ q ∈ physV S a₁ ν eps)
    (hΦloc : ∀ Y : Finset (CTorus d L N₁ m₁ (k + 1)), ∀ q ∈ expDom S.G' Dom r,
      ∀ q' ∈ expDom S.G' Dom r, q.2 = q'.2 → RawAgree Y q.1 q'.1 →
        physRestrict (↑Y : Set (CTorus d L N₁ m₁ (k + 1))) (physIncl N S (Φ q)) =
          physRestrict (↑Y : Set (CTorus d L N₁ m₁ (k + 1))) (physIncl N S (Φ q'))) :
    IsLocExp S.G' Dom r
      (Finset.univ.image fun T : Finset 𝔅 =>
        (Finset.univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => x ∈ sitesOf T))
      (renDY S.G' m₀) κ B
      (fun D ξ => ∑ T : Finset 𝔅, c (Φ ((D.Ψ, D.h), ξ)) T)
      (fun Y q => ∑ T ∈ Finset.univ.filter
        (fun T' : Finset 𝔅 => sitesOf T' = (↑Y : Set (CTorus d L N₁ m₁ (k + 1)))), c (Φ q) T) := by
  have hcoe : ∀ T : Finset 𝔅, (↑(Finset.univ.filter fun x : CTorus d L N₁ m₁ (k + 1) =>
      x ∈ sitesOf T) : Set (CTorus d L N₁ m₁ (k + 1))) = sitesOf T := by
    intro T; ext x; simp
  have hinj := (markFibre_sitesOf.{0} (d := d) (m₁ := m₁) (K := k + 1) (m₀ := m₀) hN).2.1
  -- the regrouping data at a parameter in `physV`
  have key : ∀ θ ∈ physV S a₁ ν eps,
      (∀ Y ∈ (Finset.univ.image fun T : Finset 𝔅 =>
        (Finset.univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => x ∈ sitesOf T)),
        ‖∑ T ∈ Finset.univ.filter
          (fun T' : Finset 𝔅 => sitesOf T' = (↑Y : Set (CTorus d L N₁ m₁ (k + 1)))), c θ T‖ ≤
          B * Real.exp (-κ * renDY S.G' m₀ Y)) ∧
      ∑ T : Finset 𝔅, c θ T = ∑ Y ∈ (Finset.univ.image fun T : Finset 𝔅 =>
        (Finset.univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => x ∈ sitesOf T)),
        ∑ T ∈ Finset.univ.filter
          (fun T' : Finset 𝔅 => sitesOf T' = (↑Y : Set (CTorus d L N₁ m₁ (k + 1)))), c θ T := by
    intro θ hθ
    obtain ⟨-, hbound, hsum⟩ := (markFibre_sitesOf.{0} (d := d) (m₁ := m₁) (K := k + 1) (m₀ := m₀) hN).2.2.2 (E := ℂ)
      (fun T => c θ T) B κ hB (fun T hT => hbd θ hθ T hT)
      (fun T hT => by
        by_contra h
        exact hT (hsupp θ hθ T h))
    refine ⟨?_, ?_⟩
    · intro Y hY
      obtain ⟨T, -, rfl⟩ := Finset.mem_image.1 hY
      rw [renDY_eq_sizeJ_sitesOf S.hG' T _ (hcoe T), hcoe T]
      exact hbound _
    · rw [hsum, Finset.sum_image (fun T _ T' _ h => by
        have := hinj T T' h; exact this), Finset.sum_image (fun T _ T' _ h => hinj T T' (by
        rw [← hcoe T, ← hcoe T', h]))]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [hcoe T]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro D hD ξ hξ
    exact (key _ (hΦdom _ ⟨D, hD, rfl, hξ⟩)).2
  · intro Y _
    refine Finset.analyticOnNhd_fun_sum _ fun T _ => ?_
    exact (han T).comp hΦan (fun q hq => hΦdom q hq)
  · intro Y _ q hq q' hq' h2 hag
    refine Finset.sum_congr rfl fun T hT => ?_
    have hT' : sitesOf T = (↑Y : Set (CTorus d L N₁ m₁ (k + 1))) := (Finset.mem_filter.1 hT).2
    refine hloc T _ (hΦdom q hq) _ (hΦdom q' hq') ?_
    rw [hT']
    exact hΦloc Y q hq q' hq' h2 hag
  · intro Y _ q hq
    exact (key _ (hΦdom q hq)).1 Y ‹_›

/-- **A continuous linear retraction onto the relative subspace.**  The raw data form a
finite-dimensional space, so the closed subspace `rawSub` has a closed complement. -/
theorem exists_rawProj (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) :
    ∃ P : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] ↥(rawSub N G),
      ∀ p : ↥(rawSub N G), P p = p := by
  obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional_quotient
    (Submodule.closed_of_finiteDimensional (rawSub N G))
  exact ⟨P, hP⟩

open Classical in
/-- **The datum itself** (T1).  Evaluate the family at the datum `(rawOf D, g₀)` with a fixed source
`g₀`, through any continuous linear retraction `P` of the raw data onto `rawSub` (`exists_rawProj`);
on `expDom` the retraction is the identity, so the value is `c (⟨rawOf D, _⟩, g₀) T`.  The term is
`q ↦ ∑_{sitesOf T = Y} c (P q.1, g₀) T`. -/
theorem isLocExp_of_coeffFamily_datum (hN : L ^ m₀ ∣ N₁) {a₁ ν eps r κ B : ℝ}
    (Dom : BgData S.G' N → Prop) (hB : 0 ≤ B)
    (c : physParam N S → Finset 𝔅 → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physV S a₁ ν eps))
    (hloc : ∀ T, ∀ θ ∈ physV S a₁ ν eps, ∀ θ' ∈ physV S a₁ ν eps,
      physRestrict (sitesOf T) (physIncl N S θ) = physRestrict (sitesOf T) (physIncl N S θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physV S a₁ ν eps, ∀ T, IsPolyDom m₀ (k + 1) (sitesOf T) →
      ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physV S a₁ ν eps, ∀ T, c θ T ≠ 0 → IsPolyDom m₀ (k + 1) (sitesOf T))
    (g₀ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (hDom : ∀ D, Dom D → (rawOf D, g₀) ∈ physSΛ S a₁ ν eps)
    (P : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] ↥(rawSub N S.G'))
    (hP : ∀ p : ↥(rawSub N S.G'), P p = p) :
    IsLocExp S.G' Dom r
      (Finset.univ.image fun T : Finset 𝔅 =>
        (Finset.univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => x ∈ sitesOf T))
      (renDY S.G' m₀) κ B
      (fun D _ => ∑ T : Finset 𝔅, c (⟨rawOf D, rawOf_mem_rawSub D⟩, g₀) T)
      (fun Y q => ∑ T ∈ Finset.univ.filter
        (fun T' : Finset 𝔅 => sitesOf T' = (↑Y : Set (CTorus d L N₁ m₁ (k + 1)))),
          c (P q.1, g₀) T) := by
  have hPD : ∀ D : BgData S.G' N, P (rawOf D) = ⟨rawOf D, rawOf_mem_rawSub D⟩ :=
    fun D => hP ⟨rawOf D, rawOf_mem_rawSub D⟩
  have hmem : ∀ D : BgData S.G' N, Dom D →
      ((⟨rawOf D, rawOf_mem_rawSub D⟩ : ↥(rawSub N S.G')), g₀) ∈ physV S a₁ ν eps :=
    fun D hD => hDom D hD
  have h := isLocExp_of_coeffFamily S hN (r := r) (κ := κ) Dom hB c han hloc hbd hsupp
    (fun q => (P q.1, g₀))
    (fun q _ => AnalyticAt.prod
      (show AnalyticAt ℂ (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ) => P q.1) q from
        (P.comp (ContinuousLinearMap.fst ℂ _ _)).analyticAt q) analyticAt_const)
    (by
      rintro q ⟨D, hD, h1, -⟩
      have e : q.1 = rawOf D := h1
      show (P q.1, g₀) ∈ physV S a₁ ν eps
      rw [e, hPD]; exact hmem D hD)
    (by
      rintro Y q ⟨D, hD, h1, -⟩ q' ⟨D', hD', h1', -⟩ - hag
      have e : q.1 = rawOf D := h1
      have e' : q'.1 = rawOf D' := h1'
      show physRestrict _ (physIncl N S (P q.1, g₀)) = physRestrict _ (physIncl N S (P q'.1, g₀))
      rw [e, e', hPD, hPD]
      rw [e, e'] at hag
      rw [physRestrict_physIncl_eq_iff_rawAgree]
      exact ⟨hag, fun _ _ => rfl⟩)
  refine { h with sum_eq := fun D hD ξ hξ => ?_ }
  rw [← h.sum_eq D hD ξ hξ]
  refine Finset.sum_congr rfl fun T _ => ?_
  show c (_, g₀) T = c (P (D.Ψ, D.h), g₀) T
  rw [show ((D.Ψ, D.h) : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D from rfl, hPD]

open Classical in
/-- **The renormalized datum** (T3).  Evaluate the family at `(P ((1 + ζ(ξ)) Ψ, h), g₀)`.  The chart
hypothesis `hchart` says that the renormalized datum lies in the chart `XiCData` at radius `eps`
for `Dom D` and `‖ξ‖ < r` (for the tower this is `StepTowerTheta.renDatum_half_mem_xiCData`). -/
theorem isLocExp_of_coeffFamily_renTheta (hN : L ^ m₀ ∣ N₁) {a₁ ν eps r κ B : ℝ}
    (εren : ℝ) (Dom : BgData S.G' N → Prop) (hB : 0 ≤ B)
    (c : physParam N S → Finset 𝔅 → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physV S a₁ ν eps))
    (hloc : ∀ T, ∀ θ ∈ physV S a₁ ν eps, ∀ θ' ∈ physV S a₁ ν eps,
      physRestrict (sitesOf T) (physIncl N S θ) = physRestrict (sitesOf T) (physIncl N S θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physV S a₁ ν eps, ∀ T, IsPolyDom m₀ (k + 1) (sitesOf T) →
      ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physV S a₁ ν eps, ∀ T, c θ T ≠ 0 → IsPolyDom m₀ (k + 1) (sitesOf T))
    (g₀ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (hg₀ : g₀ ∈ l1Ball d L N₁ m₁ (k + 1) N)
    (hchart : ∀ D, Dom D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r →
      XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps (renThetaDatum S εren D ξ))
    (P : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] ↥(rawSub N S.G'))
    (hP : ∀ p : ↥(rawSub N S.G'), P p = p) :
    IsLocExp S.G' Dom r
      (Finset.univ.image fun T : Finset 𝔅 =>
        (Finset.univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => x ∈ sitesOf T))
      (renDY S.G' m₀) κ B
      (fun D ξ => ∑ T : Finset 𝔅,
        c (⟨rawOf (renThetaDatum S εren D ξ), rawOf_mem_rawSub _⟩, g₀) T)
      (fun Y q => ∑ T ∈ Finset.univ.filter
        (fun T' : Finset 𝔅 => sitesOf T' = (↑Y : Set (CTorus d L N₁ m₁ (k + 1)))),
          c (P ((fun x i => (1 + renZeta εren q.2) * q.1.1 x i), q.1.2), g₀) T) := by
  have hPD : ∀ (D : BgData S.G' N) (ξ : Fin 3 → ℂ),
      P ((fun x i => (1 + renZeta εren ξ) * D.Ψ x i), D.h) =
        ⟨rawOf (renThetaDatum S εren D ξ), rawOf_mem_rawSub _⟩ :=
    fun D ξ => hP ⟨rawOf (renThetaDatum S εren D ξ), rawOf_mem_rawSub _⟩
  have h := isLocExp_of_coeffFamily S hN (r := r) (κ := κ) Dom hB c han hloc hbd hsupp
    (fun q => (P ((fun x i => (1 + renZeta εren q.2) * q.1.1 x i), q.1.2), g₀))
    (fun q _ => AnalyticAt.prod
      (show AnalyticAt ℂ (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ) =>
        P ((fun x i => (1 + renZeta εren q.2) * q.1.1 x i), q.1.2)) q from
        (P.analyticAt _).comp (analyticOnNhd_renThetaRaw εren Set.univ q trivial))
      analyticAt_const)
    (by
      rintro q ⟨D, hD, h1, h2⟩
      have e : q.1 = (D.Ψ, D.h) := h1
      show (P ((fun x i => (1 + renZeta εren q.2) * q.1.1 x i), q.1.2), g₀) ∈ physV S a₁ ν eps
      rw [e]
      simp only
      rw [hPD]
      exact ⟨⟨renThetaDatum S εren D q.2, hchart D hD q.2 h2, rfl⟩, hg₀⟩)
    (by
      rintro Y q ⟨D, hD, h1, -⟩ q' ⟨D', hD', h1', -⟩ h2 hag
      have e : q.1 = (D.Ψ, D.h) := h1
      have e' : q'.1 = (D'.Ψ, D'.h) := h1'
      show physRestrict _ (physIncl N S (P ((fun x i => (1 + renZeta εren q.2) * q.1.1 x i),
          q.1.2), g₀)) = physRestrict _ (physIncl N S (P ((fun x i =>
          (1 + renZeta εren q'.2) * q'.1.1 x i), q'.1.2), g₀))
      rw [e, e']
      simp only
      rw [hPD, hPD, physRestrict_physIncl_eq_iff_rawAgree]
      refine ⟨?_, fun _ _ => rfl⟩
      rw [← h2]
      rw [e, e'] at hag
      have := renThetaRaw_rawAgree (N := N) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) εren q.2 Y hag
      exact this)
  refine { h with sum_eq := fun D hD ξ hξ => ?_ }
  rw [← h.sum_eq D hD ξ hξ]
  refine Finset.sum_congr rfl fun T _ => ?_
  show c (_, g₀) T = c (P ((fun x i => (1 + renZeta εren ξ) * D.Ψ x i), D.h), g₀) T
  rw [hPD]

end Generic

section Tower

open Balaban.Inhabited

variable {κmin : ℝ}

open Classical in
/-- **The renormalized datum at the tower.**  For the step `S` of a tower with renormalization data
`R`: class radius `R.t / 2`, chart radius `R.t`, polydisc radius `R.r₀`.  The chart hypothesis of
`isLocExp_of_coeffFamily_renTheta` is `StepTowerTheta.renDatum_half_mem_xiCData`. -/
theorem isLocExp_of_coeffFamily_renTheta_tower (R : StepTowerTheta κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) {m₀ : ℕ} (hN : 3 ^ m₀ ∣ N₁)
    {κ B : ℝ} (hB : 0 ≤ B)
    (c : physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) →
      Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) m₀ (k + 1)
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
      ∀ T, IsPolyDom m₀ (k + 1) (sitesOf T) → ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
      ∀ T, c θ T ≠ 0 → IsPolyDom m₀ (k + 1) (sitesOf T))
    (g₀ : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 → ℂ) (hg₀ : g₀ ∈ l1Ball 3 3 N₁ R.m₁ (k + 1) 2)
    (P : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 →L[ℂ]
      ↥(rawSub 2 (R.toStepTower.step k hk N₁ ν β p₁).G'))
    (hP : ∀ p : ↥(rawSub 2 (R.toStepTower.step k hk N₁ ν β p₁).G'), P p = p) :
    IsLocExp (R.toStepTower.step k hk N₁ ν β p₁).G'
      (XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
        (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν (R.t / 2))
      R.r₀
      (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) m₀ (k + 1) Set.univ) => (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) =>
        x ∈ sitesOf T))
      (renDY (R.toStepTower.step k hk N₁ ν β p₁).G' m₀) κ B
      (fun D ξ => ∑ T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) m₀ (k + 1) Set.univ), c (⟨rawOf (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ),
        rawOf_mem_rawSub _⟩, g₀) T)
      (fun Y q => ∑ T ∈ Finset.univ.filter (fun T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) m₀ (k + 1) Set.univ) => sitesOf T' =
        (↑Y : Set (CTorus 3 3 N₁ R.m₁ (k + 1)))),
          c (P ((fun x i => (1 + renZeta (R.t / 2) q.2) * q.1.1 x i), q.1.2), g₀) T) :=
  isLocExp_of_coeffFamily_renTheta (R.toStepTower.step k hk N₁ ν β p₁) hN (R.t / 2) _ hB c han hloc
    hbd hsupp g₀ hg₀
    (fun D hD ξ hξ => R.renDatum_half_mem_xiCData k hk N₁ hν0 hν β p₁ D hD ξ hξ) P hP

end Tower

end Balaban.Fluctuation
