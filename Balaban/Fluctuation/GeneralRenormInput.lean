/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CoeffFamilyLocExp
public import Balaban.Fluctuation.LocExpUnion
public import Balaban.Fluctuation.RenormExpInputOn

/-!
# The renormalization input for a class member: the old-term differences

For a member of the class with nonzero inherited terms, the old-term differences `oldE`, `oldM` of
`RenormExpInputOn` are the differences, between the renormalized datum `((1 + ζ(ξ)) Ψ, h)` and the
unrenormalized datum (`ξ = 0`), of the inherited energy (resp. observable) contributions.  Such a
contribution is a coefficient family over cube sets; it is regrouped into a localized expansion
(`isLocExp_of_coeffFamily_renTheta`), and the difference vanishes at `ξ = 0` by construction.

* `IsLocExp.sub_at_zero`: an expansion `f` on a polydisc gives an expansion of `f D ξ - f D 0`,
  with twice the bound and terms vanishing at `ξ = 0`;
* `exists_oldDiff_locExp_of_coeffFamily`: the field `expOld` (resp. `expOldM`) for the difference of a
  coefficient family at the renormalized datum, with the nonzero budget `2 B`;
* `renormExpInputOn_class_of_fields`: the record `RenormExpInputOn` with these old-term fields;
* `thm31g_Eu_class_of_fields`, `thm31h_class_of_fields`: the consequences `thm31g_Eu_on`,
  `thm31h_on` with the nonzero budgets `2 B ε_R / r₀`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Multiscale

section Generic

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {Dom : BgData G N → Prop} {r κ B : ℝ}
  {Ys : Finset (Finset (Torus d (N₀ * L ^ k)))}
  {dY : Finset (Torus d (N₀ * L ^ k)) → ℝ} {f : BgData G N → (Fin 3 → ℂ) → E}
  {term : Finset (Torus d (N₀ * L ^ k)) → RawData d L N₀ k N × (Fin 3 → ℂ) → E}

/-- **The difference with the value at `ξ = 0`.**  An expansion of `f` on the polydisc of radius
`r > 0` gives an expansion of `f D ξ - f D 0` with the bound `2 B` and terms vanishing at `ξ = 0`. -/
theorem IsLocExp.sub_at_zero (h : IsLocExp G Dom r Ys dY κ B f term) (hr : 0 < r) :
    IsLocExp G Dom r Ys dY κ (2 * B) (fun D ξ => f D ξ - f D 0)
      (fun Y q => term Y q - term Y (q.1, 0)) ∧
    ∀ Y ∈ Ys, ∀ D : BgData G N, Dom D →
      (fun Y (q : RawData d L N₀ k N × (Fin 3 → ℂ)) => term Y q - term Y (q.1, 0)) Y
        ((D.Ψ, D.h), 0) = 0 := by
  have hmem : ∀ q ∈ expDom G Dom r, (q.1, (0 : Fin 3 → ℂ)) ∈ expDom G Dom r := by
    rintro q ⟨D, hD, h1, -⟩
    exact ⟨D, hD, h1, by simpa using hr⟩
  refine ⟨?_, fun Y _ D _ => by simp⟩
  refine
    { sum_eq := fun D hD ξ hξ => ?_
      analytic := fun Y hY => ?_
      local_ := fun Y hY q hq q' hq' h2 hag => ?_
      bound := fun Y hY q hq => ?_ }
  · rw [h.sum_eq D hD ξ hξ, h.sum_eq D hD 0 (by simpa using hr), ← Finset.sum_sub_distrib]
  · refine (h.analytic Y hY).sub ((h.analytic Y hY).comp ?_ hmem)
    exact fun q _ => AnalyticAt.prod analyticAt_fst analyticAt_const
  · rw [h.local_ Y hY q hq q' hq' h2 hag,
      h.local_ Y hY _ (hmem q hq) _ (hmem q' hq') rfl hag]
  · have h1 := h.bound Y hY q hq
    have h2 := h.bound Y hY _ (hmem q hq)
    calc ‖term Y q - term Y (q.1, 0)‖ ≤ ‖term Y q‖ + ‖term Y (q.1, 0)‖ := norm_sub_le _ _
      _ ≤ B * Real.exp (-κ * dY Y) + B * Real.exp (-κ * dY Y) := add_le_add h1 h2
      _ = 2 * B * Real.exp (-κ * dY Y) := by ring

end Generic

section Record

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {a : ℕ → ℝ} {ν ε r₀ cK B : ℝ}
  {F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
  {ι : Type*} {blk : ι → Finset (Torus d (N₀ * L ^ k))}
  {Ys : ι → Finset (Finset (Torus d (N₀ * L ^ k)))}
  {YsM : G.Ω 1 × Fin N → Finset (Finset (Torus d (N₀ * L ^ k)))}
  {dY : Finset (Torus d (N₀ * L ^ k)) → ℝ} {κa κE κM κO κOM Kloc H BM BO BOM : ℝ}
  {E0θ : ι → BgData G N → (Fin 3 → ℂ) → ℂ}
  {M0θ : G.Ω 1 × Fin N → BgData G N → (Fin 3 → ℂ) → ℂ} {Dom : BgData G N → Prop}

/-- **The record `RenormExpInputOn` for a class member (nonzero old terms).**  Besides the data of
`renormPhysicalZero_expInput_core`, the inherited energy contributions `fE z` and observable
contributions `fM p` (at the renormalized datum) have localized expansions on `Dom`; the old-term
differences of the record are `fE z D ξ - fE z D 0` and `fM p D ξ - fM p D 0`, with the budgets
`2 BO` and `2 BOM`. -/
theorem renormExpInputOn_class_of_fields
    (sub : ∀ D : BgData G N, Dom D → XiCOneReal G a ν ε D)
    (locC1 : ∀ z, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa Kloc
      (fun D _ => bgClass G ν (cK * ε) D) (fun D φ ξ => renC1On G a ν ε (blk z) D.Ψ D.h φ ξ)
      (fun D _ => bgFieldC G a ν (bgC0 d L N) D))
    (locC2 : ∀ z, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa Kloc
      (fun _ ξ => pertClass G (cK * (cK2 d L N * (B * ‖ξ‖)))
        (bgK1 d L N * (xiC1 d * ε) + cK * cK2 d L N * B * r₀ + 2) (renMassU ν ξ))
      (fun _ v ξ => renC2On G a (blk z) ξ (renMassU ν ξ) v.2 v.1)
      (fun D ξ => ((F ((D.Ψ, D.h), ξ)).1, bgMultC G a ν (bgC0 d L N) D + (F ((D.Ψ, D.h), ξ)).2)))
    (locDφ : ∀ p, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (YsM p) dY κa Kloc
      (fun _ ξ => {v | SupBounds G v (cK * (cK2 d L N * (B * ‖ξ‖)))}) (fun _ v _ => v p)
      (fun D ξ => (F ((D.Ψ, D.h), ξ)).1))
    (hdY : ∀ Y, 0 ≤ dY Y) (hr₀ : 0 < r₀)
    (hE : ∀ z, ∃ term, IsLocExp (N := N) G Dom r₀ (Ys z) dY κE H (E0θ z) term)
    (hκE : κa ≤ κE) (hH : 0 ≤ H)
    (hM : ∀ p, ∃ term, IsLocExp (N := N) G Dom r₀ (YsM p) dY κM BM (M0θ p) term)
    (hκM : κa ≤ κM) (hBM : 0 ≤ BM)
    (fE : ι → BgData G N → (Fin 3 → ℂ) → ℂ)
    (hOE : ∀ z, ∃ term, IsLocExp (N := N) G Dom r₀ (Ys z) dY κO BO (fE z) term)
    (hκO : κa ≤ κO) (hBO : 0 ≤ BO)
    (fM : G.Ω 1 × Fin N → BgData G N → (Fin 3 → ℂ) → ℂ)
    (hOM : ∀ p, ∃ term, IsLocExp (N := N) G Dom r₀ (YsM p) dY κOM BOM (fM p) term)
    (hκOM : κa ≤ κOM) (hBOM : 0 ≤ BOM) :
    RenormExpInputOn G a ν ε r₀ cK B F blk Ys YsM dY κa κa Kloc H (2 * BO) BM (2 * BOM) E0θ
      (fun z D ξ => fE z D ξ - fE z D 0) M0θ (fun p D ξ => fM p D ξ - fM p D 0) Dom where
  sub := sub
  locC1 := locC1
  locC2 := locC2
  expE0 z := (hE z).imp fun _ h => h.mono_rate hκE hH (fun Y _ => hdY Y)
  expOld z := by
    obtain ⟨t, h⟩ := hOE z
    exact ⟨_, ((h.mono_rate hκO hBO (fun Y _ => hdY Y)).sub_at_zero hr₀).1,
      ((h.mono_rate hκO hBO (fun Y _ => hdY Y)).sub_at_zero hr₀).2⟩
  locDφ := locDφ
  expM0 p := (hM p).imp fun _ h => h.mono_rate hκM hBM (fun Y _ => hdY Y)
  expOldM p := by
    obtain ⟨t, h⟩ := hOM p
    exact ⟨_, ((h.mono_rate hκOM hBOM (fun Y _ => hdY Y)).sub_at_zero hr₀).1,
      ((h.mono_rate hκOM hBOM (fun Y _ => hdY Y)).sub_at_zero hr₀).2⟩

/-- **Theorem 3.1 (g), `ℰ_u(z)`, for a class member**: the new energy plus the old-energy
difference, with the nonzero budget `H + 2 BO ε_R / r₀`. -/
theorem thm31g_Eu_class_of_fields
    {fE : ι → BgData G N → (Fin 3 → ℂ) → ℂ}
    {oldM : G.Ω 1 × Fin N → BgData G N → (Fin 3 → ℂ) → ℂ}
    (I : RenormExpInputOn G a ν ε r₀ cK B F blk Ys YsM dY κa κa Kloc H (2 * BO) BM BOM E0θ
      (fun z D ξ => fE z D ξ - fE z D 0) M0θ oldM Dom)
    (hr₀ : 0 < r₀) {εR : ℝ} (hεR : εR ≤ r₀) (z : ι) :
    ∃ term, IsLocExp (N := N) G Dom εR (Ys z) dY κa (H + 2 * BO * (εR / r₀))
      (fun D ξ => E0θ z D ξ + (fE z D ξ - fE z D 0)) term :=
  thm31g_Eu_on I hr₀ hεR z

/-- **Theorem 3.1 (h), for a class member**: the new observable, the cut-off solution and the
old-observable difference, with the nonzero budget `BM + K_loc c_K K₂ B ε_R + 2 BOM ε_R / r₀`. -/
theorem thm31h_class_of_fields
    {oldE : ι → BgData G N → (Fin 3 → ℂ) → ℂ}
    {fM : G.Ω 1 × Fin N → BgData G N → (Fin 3 → ℂ) → ℂ}
    (I : RenormExpInputOn G a ν ε r₀ cK B F blk Ys YsM dY κa κa Kloc H BO BM (2 * BOM) E0θ
      oldE M0θ (fun p D ξ => fM p D ξ - fM p D 0) Dom)
    (hK : 0 ≤ Kloc) (hB0 : 0 ≤ B) (hcK : 1 ≤ cK) (hr₀ : 0 < r₀) {εR : ℝ} (hεR : εR ≤ r₀)
    (p : G.Ω 1 × Fin N) :
    ∃ term, IsLocExp (N := N) G Dom εR (YsM p) dY κa
      (BM + Kloc * (cK * cK2 d L N * B) * εR ^ 1 + 2 * BOM * (εR / r₀))
      (fun D ξ => M0θ p D ξ + (F ((D.Ψ, D.h), ξ)).1 p + (fM p D ξ - fM p D 0)) term :=
  thm31h_on I hK hB0 hcK hr₀ hεR p

end Record

section Family

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ

open Classical in
/-- **The inherited contribution at the renormalized datum, as an expansion on a cover.**  A
coefficient family `c` over cube sets (the regrouped inherited energy of a root, or the inherited
observable at a site, for the fixed source `g₀`) is, evaluated at the renormalized datum, a localized
expansion over every family `Ys'` of domains containing the site sets of all cube sets.  This is the
hypothesis `hOE` (resp. `hOM`) of `renormExpInputOn_class_of_fields`. -/
theorem exists_locExp_renTheta_of_coeffFamily (hN : L ^ m₀ ∣ N₁) {a₁ ν eps r κ B : ℝ}
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
    (hP : ∀ p : ↥(rawSub N S.G'), P p = p)
    {Ys' : Finset (Finset (CTorus d L N₁ m₁ (k + 1)))}
    (hYs : (Finset.univ.image fun T : Finset 𝔅 =>
        (Finset.univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => x ∈ sitesOf T)) ⊆ Ys') :
    ∃ term, IsLocExp S.G' Dom r Ys' (renDY S.G' m₀) κ B
      (fun D ξ => ∑ T : Finset 𝔅,
        c (⟨rawOf (renThetaDatum S εren D ξ), rawOf_mem_rawSub _⟩, g₀) T) term :=
  ⟨_, (isLocExp_of_coeffFamily_renTheta S hN εren Dom hB c han hloc hbd hsupp g₀ hg₀ hchart P
    hP).extend hYs hB⟩

end Family

end Balaban.Fluctuation
