/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusEv

/-!
# The coefficients of the marked functional on two tori

`coef_FFmarked_twoTorus` is the coefficient form of `evDec_twoTorus` (`TwoTorusEv`): the
correspondence of the coefficients of the marked functional on the families `C`, `C'` that
correspond under the box map, which `evTerm_boxMap_of_eq` asks for.  The statement of
`evDec_twoTorus` is unchanged; this file restates its inner block with the coefficient correspondence
as the conclusion, since the recentred transport of `TwoTorusGapClose` needs it at translated
sets, where the term identity alone is not enough.

-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background

section Coef

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "ρ₁" => R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)

/-- **The coefficients of the marked functional on two tori** (the coefficient form of `evDec_twoTorus`).  Under the hypotheses of `evDec_twoTorus` (the margin `hnF` of the reindexing of the families is not needed), with the analyticity of the first functional in the cut parameters stated directly (`hFan`), the coefficients of `FFmarked` of the second torus at a family `C'` and of the first torus at the family `C` agree whenever `C'` is the image of `C` under the box map.  The proof is that of the inner block of `evDec_twoTorus`: `coef_relabel_injOn` and `FFmarked_twoTorus` at the cut points of `C`. -/
theorem coef_FFmarked_twoTorus
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (HA) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (HB) (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {m₀ j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {X' 𝒦X' : Set (CTorus d L N₁' m₁ (k + 1))}
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup (GA) m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ j 𝒦X)
    (hcov' : CovSetup (GB) m₀ j X' 𝒦X')
    (hX₁' : (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ j 𝒦X')
    {Φ : (((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) → ((HA).Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : (((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) → ((HB).Ω 1 × Fin N → ℂ) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Rα Rδ Rψ : Set (CTorus d L N₁ m₁ (k + 1))} (hBM : BlockMargin (GA) X₁f Rα)
    (hRδ : Rδ ⊆ ↑X₁f) (hRψ : Rψ ⊆ ↑X₁f)
    (hΦ : ∀ (t : (((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) × ((HA).Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))
      (t' : (((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) × ((HB).Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ))),
      (∀ (y : (GA).Ω 1) (y' : (GB).Ω 1), (y : CTorus d L N₁ m₁ (k + 1)) ∈ Rα →
        (y' : CTorus d L N₁' m₁ (k + 1)) = bm (y : CTorus d L N₁ m₁ (k + 1)) →
          t'.1.2 y' = t.1.2 y) →
      (∀ (w : (HA).Ω 1) (w' : (HB).Ω 1), (w : CTorus d L N₁ m₁ (k + 1)) ∈ Rδ →
        (w' : CTorus d L N₁' m₁ (k + 1)) = bm (w : CTorus d L N₁ m₁ (k + 1)) →
        ∀ i, t'.2.1 (w', i) = t.2.1 (w, i)) →
      (∀ x ∈ Rψ, t'.2.2.2 (bm x) = t.2.2.2 x) →
      Φ' t'.1 t'.2.1 t'.2.2 = Φ t.1 t.2.1 t.2.2)
    {R : ℕ} (hX₁R : ∀ x ∈ X₁f, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf D) (rawOf D'))
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    (hhat : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, ψh' (unitPt hGB (bm x), i) = ψh (unitPt hGA x, i))
    {Zm : Finset (unitPts (GA))} {Zm' : Finset (unitPts (GB))}
    (hZm : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      (unitPt hGB (bm x) ∈ Zm' ↔ unitPt hGA x ∈ Zm))
    {um tm : ℂ} (hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (hFan : AnalyticOnNhd ℂ (FFmarked X₁f a₁ ν hGA cc F₁ Sol Φ Zm um tm (rawOf D, ψh))
      (polydisc (0 : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ))) :
    ∀ C ∈ connFams (fun i : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) (GA) m₀
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) Y,
      ∀ C' : Finset (ParIdx (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1)))),
        (∀ i ∈ C, ∃ i' ∈ C', i'.1.1 = Prod.map id bm i.1.1) →
        (∀ i' ∈ C', ∃ i ∈ C, i'.1.1 = Prod.map id bm i.1.1) →
        coef (FFmarked (X₁f.image bm) a₁ ν hGB cc F₁' Sol' Φ' Zm' um tm (rawOf D', ψh')) C' =
          coef (FFmarked X₁f a₁ ν hGA cc F₁ Sol Φ Zm um tm (rawOf D, ψh)) C := by
  classical
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hHA : IsLevel (HA) k := isLevel_levelGS hk (Nat.le_succ k)
  have hKm : L ^ (k + 1) ≤ L ^ (k + 1 + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_add_right _ _)
  intro C hCm C' h2 h1
  have hYC := ((mem_connFams (fun i : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
    i.1.1)).1 hCm).2
  have hCR : ∀ i ∈ C, ∀ x ∈ Pset m₁ i.1.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    intro i hi x hx
    apply hYR
    rw [← hYC]
    right
    simp only [Set.mem_iUnion]
    exact ⟨i, hi, Pset_subset_Dsites hcov.hU hcov.hN i.1.2 hx⟩
  by_cases hCe : C = ∅
  · subst hCe
    have hC'e : C' = ∅ := Finset.eq_empty_of_forall_notMem fun i' hi' => by
      obtain ⟨i, hi, -⟩ := h1 i' hi'
      simp at hi
    subst hC'e
    rw [coef_empty_eq, coef_empty_eq]
    exact FFmarked_twoTorus hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁
      hF₁' hSol hSol' hcov hX₁ hcov' hX₁' hBM hRδ hRψ hΦ hX₁R ∅ (fun i hi => by simp at hi) hn hn'
      hnS hnS' ⟨fun i _ => rfl, fun i => by simpa using Real.exp_pos κ⟩ (fun _ _ => rfl)
      (fun i hi => by simp at hi) hD hD' hraw hψh hψh' hhat hZm hum
  · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_of_ne_empty hCe
    obtain ⟨i₀', -, -⟩ := h2 i₀ hi₀
    choose f hf using h2
    set e : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) →
        ParIdx (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) :=
      fun i => if hi : i ∈ C then f i hi else i₀' with he_def
    have he : ∀ i ∈ C, e i ∈ C' ∧ (e i).1.1 = Prod.map id bm i.1.1 := by
      intro i hi
      simp only [he_def, hi, ↓reduceDIte]
      exact hf i hi
    have hcen : ∀ i ∈ C, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) i.1.1.2 :=
      fun i hi => hCR i hi _ (self_mem_Pset _)
    have hinj : Set.InjOn e ↑C := by
      intro i hi i₂ hi₂ hii
      have hc : Prod.map id bm i.1.1 = Prod.map id bm i₂.1.1 := by
        rw [← (he i hi).2, ← (he i₂ hi₂).2, hii]
      exact Subtype.ext (Subtype.ext (injOn_idxMap (N₁' := N₁') (ρ := R) (by omega)
        (hcen i hi) (hcen i₂ hi₂) hc))
    have hCimg : C.image e = C' := by
      ext i'
      constructor
      · intro h
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h
        exact (he i hi).1
      · intro hi'
        obtain ⟨i, hi, hc⟩ := h1 i' hi'
        exact Finset.mem_image.2 ⟨i, hi, Subtype.ext (Subtype.ext ((he i hi).2.trans hc.symm))⟩
    rw [← hCimg]
    refine coef_relabel_injOn hE1 e hinj hFan (fun s hs s' hs' hss => ?_)
    refine FFmarked_twoTorus hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁
      hF₁' hSol hSol' hcov hX₁ hcov' hX₁' hBM hRδ hRψ hΦ hX₁R C hCR hn hn' hnS hnS' hs
      (fun i' hi' => hs' i' ?_) (fun i hi i' hc => ?_) hD hD' hraw hψh hψh' hhat hZm hum
    · intro hmem
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hmem
      exact hi' i hi (he i hi).2
    · have : i' = e i := Subtype.ext (Subtype.ext (hc.trans (he i hi).2.symm))
      rw [this]
      exact hss i hi



end Coef


end Balaban.Polymer.TwoTorusStep
