/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassLatPaving
public import Balaban.Fluctuation.LocalClassTau
public import Balaban.Fluctuation.LocalClassLatData

/-!
# The parameter maps of the local terms of `Y` and `σ Y` correspond

The parameter map of the local terms (`LocalClassTau.lean`) is
`σ_Y w = τ_Y (extParams 𝔹_{k+1} X₁ w)`: the parameters of the ambient level set `𝔹_{k+1}` kept at
the cubes of the cover of `𝔹_{k+1}(Y⁺)` with base in its top layer, `0` at the others.

`localB_tauExt_sym`: for a paving symmetry `σ` with its symmetry bundle `(CS, PS)` of the ambient
level set (`nonempty_fullSymm_of_mem_pavingSymGroup`), the maps of `Y` and `σ Y` agree at a centre
`P` of the cover of `𝔹_{k+1}(Y⁺)` and a centre `P'` of the cover of `𝔹_{k+1}((σ Y)⁺)` of the same
layer whose cube contains `σ P.2`, for the parameters `w'` of `σ X₁` and `w' ∘ κ`, `κ` the
relabelling `parEquiv CS PS` of the parameters.  This is the hypothesis `hww` of
`localB_eTermHat_evTerm_paving`.

`localB_eTermHat_evTerm_paving_tau`: the instance of `localB_eTermHat_evTerm_paving` for this
parameter map, the ambient symmetry being the bundle `FullSymm` of the level set.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.GsSpec Balaban.LargeField Balaban.Fluctuation Balaban.Localization.DecEquiv
  Finset

section Tau

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- Two cube bases of the same cell coincide. -/
theorem cubeBase_eq_of_sameCell {K j : ℕ} {y y' : CTorus d L N₁ m₁ K} (hy : CubeBase m₁ j y)
    (hy' : CubeBase m₁ j y') (h : SameCell (L ^ (j + m₁)) y y') : y = y' := by
  funext μ
  apply ZMod.val_injective
  have e1 := Nat.div_add_mod (y μ).val (L ^ (j + m₁))
  have e2 := Nat.div_add_mod (y' μ).val (L ^ (j + m₁))
  rw [hy μ] at e1
  rw [hy' μ] at e2
  rw [← e1, ← e2, h μ]

/-- **The parameter maps of `Y` and `σ Y` correspond** (the hypothesis `hww` of
`localB_eTermHat_evTerm_paving` for `σ_Y w = τ_Y (extParams 𝔹_{k+1} X₁ w)`). -/
theorem localB_tauExt_sym {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hG : IsLevel Ga (k + 1)) (hk : k + 1 ≤ k + 1) {Yp Yp₂ : Set (CTorus d L N₁ m₁ (k + 1))}
    {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (hΩ : ∀ i, 1 ≤ i → i ≤ k + 1 + 1 → ∀ x,
      σ x ∈ (localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω i ↔
        x ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω i)
    (hca₂ : CubeAligned (localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) m₁)
    {m₀ : ℕ} (CS : CoverSymm (coverOf Ga) σ) (PS : PolymerSymm Ga m₀ σ CS.τ)
    (X₁ : Set (CTorus d L N₁ m₁ (k + 1))) (w' : ParIdx Ga (σ '' X₁) → ℂ)
    (P P' : ℕ × CTorus d L N₁ m₁ (k + 1))
    (hP : P ∈ (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx)
    (hP' : P' ∈ (coverOf (localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))).cubeIdx)
    (h1 : P'.1 = P.1) (hc : SameCell (L ^ (P.1 + m₁)) (σ P.2) P'.2) :
    Dec2.extS (coverOf (localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))))
        (fun P'' : ↥(coverOf (localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))).cubeIdx =>
          if P''.1.2 ∈ (localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) then
            Dec2.extS (coverOf Ga) (extParams Ga (σ '' X₁) w') P''.1 else 0) P' =
      Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
        (fun P'' : ↥(coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx =>
          if P''.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) then
            Dec2.extS (coverOf Ga) (extParams Ga X₁ (w' ∘ parEquiv CS PS rfl)) P''.1 else 0) P := by
  classical
  have hPm := (mem_cubeIdx _).1 hP
  have hP'm := (mem_cubeIdx _).1 hP'
  have eo : ∀ {C : DecCover d L N₁ m₁ (k + 1)} (s : Dec2.DecParams C)
      {Q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hQ : Q ∈ C.cubeIdx), Dec2.extS C s Q = s ⟨Q, hQ⟩ :=
    fun s Q hQ => by unfold Dec2.extS; simp [hQ]
  rw [eo _ hP', eo _ hP]
  dsimp only
  have hiff : P'.2 ∈ (localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) ↔
      P.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) := by
    rw [← hΩ (k + 1) (by omega) (by omega)]
    have hc' : SameCell (L ^ (k + 1 + m₁)) (σ P.2) P'.2 :=
      SameCell.mono (pow_dvd_pow L (by omega)) hc
    exact (hca₂.union (k + 1) (by omega) le_rfl _ _ hc').symm
  by_cases h : P.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
  · have h' := hiff.2 h
    simp only [h, h', ↓reduceIte]
    -- the centre `P` is a cube of the ambient level set at the top layer
    have hP1 : P.1 = k + 1 := by
      have hl := hPm.2.1
      rw [GeneratingSet.mem_layer] at hl
      by_contra hne
      have hlt : P.1 < k + 1 := lt_of_le_of_ne hPm.1.2 hne
      exact hl.2 ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω_antitone
        (i := P.1 + 1) (j := k + 1) (by omega) (by omega) (by omega) h)
    have hPa : P ∈ cubeIdx Ga := by
      rw [mem_cubeIdx]
      refine ⟨hPm.1, ?_, hPm.2.2⟩
      rw [hP1]
      exact hG.mem_layer _
    have hτP : CS.τ P = P' := by
      have hτm : CS.τ P ∈ cubeIdx Ga := (CS.idx P).2 hPa
      have hτ1 : (CS.τ P).1 = k + 1 := fst_eq_of_mem_cubeIdx hG hτm
      have hτb := ((mem_cubeIdx Ga).1 hτm).2.2
      have hps : σ P.2 ∈ Pset m₁ (CS.τ P) := (PS.pset P hPa P.2).2 (self_mem_Pset P)
      have e : (CS.τ P).1 + m₁ = P.1 + m₁ := by omega
      have e' : (CS.τ P).1 = P.1 := by omega
      have hc2 : SameCell (L ^ (P.1 + m₁)) (CS.τ P).2 P'.2 := by
        have h0 : SameCell (L ^ ((CS.τ P).1 + m₁)) (σ P.2) (CS.τ P).2 := hps
        rw [e] at h0
        exact h0.symm.trans hc
      have hb' : CubeBase m₁ P.1 P'.2 := by rw [← h1]; exact hP'm.2.2
      have hb2 : CubeBase m₁ P.1 (CS.τ P).2 := by rw [e'] at hτb; exact hτb
      exact Prod.ext (by rw [hτ1, h1, hP1]) (cubeBase_eq_of_sameCell hb2 hb' hc2)
    rw [extParams_sym CS PS rfl w']
    refine (CoverSymm.extS_par CS _ P').trans ?_
    rw [← hτP, Equiv.symm_apply_apply]
  · have h' : P'.2 ∉ (localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) :=
      fun hh => h (hiff.1 hh)
    simp only [h, h', ↓reduceIte]

end Tau


section PavingTau

open Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Analysis
  Balaban.Localization.DetDecCov Balaban.Localization.DetUnitIncidence MeasureTheory Matrix

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]
variable {ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gk Gk₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj Gj₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm Hm₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a₁ ν : ℝ} {N : ℕ}

/-- **Lattice covariance under the paving group of the term of the local class with the parameter
map `σ_Y = τ_Y ∘ extParams`** (`LocalClassTau.lean`) over the ambient level set `𝔹_{k+1}`: the
instance of `localB_eTermHat_evTerm_paving` in which the symmetry of the ambient expansion is the
bundle `FullSymm` of the level set (`nonempty_fullSymm_of_mem_pavingSymGroup`), the indices are the
parameter cubes `ParIdx 𝔹_{k+1} X₁`, `ParIdx 𝔹_{k+1} (σ X₁)` relabelled by `parEquiv`, and the
correspondence of the parameter maps is `localB_tauExt_sym`.  Remaining inputs: the old-term
covariance `hEr`, the images `K'`, `γ'` (`hKγ`), the `Ω`-images of `𝔹_k`, `𝔹_j`, `H⁻`. -/
theorem localB_eTermHat_evTerm_paving_tau {ϱa : ℝ} {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa}
    (hG : IsLevel Ga (k + 1)) {m₀ : ℕ} (hNm : L ^ m₀ ∣ N₁)
    (X₁ : Set (CTorus d L N₁ m₁ (k + 1))) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) (hk : k + 1 ≤ k + 1)
    (Yp Yp₂ : Set (CTorus d L N₁ m₁ (k + 1))) (hN₁ : 5 < N₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG) (hk1 : 1 ≤ k)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    (HBp : BgHyp d L (k + 1) (minSep L (L ^ m₁)) (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν)
    {κ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ (4 * d * (L : ℝ) ^ 3 + L) eps δ₃)
    {j : ℕ} (hj : j ≤ k + 1) {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁) {Bd : ℝ}
    (hP : Precedes Gk (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1) (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 →
      ∀ y : CTorus d L N₁ m₁ (k + 1), Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ * (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).spacing x → y ∈ X₁f)
    (hF : FlSetting N (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Gk Hm a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    (hHm : Hm.Ω (k + 1) = ∅)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hE : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    {F₁ : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) × ((GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N,
      InUnionDomainC (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))) (D : BgData (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {σp : (ParIdx Ga X₁ → ℂ) → Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))}
    (hσp : ∀ w P, σp w P = if P.1.2 ∈ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) then
      Dec2.extS (coverOf Ga) (extParams Ga X₁ w) P.1 else 0) (hσan : ∀ w, AnalyticAt ℂ σp w)
    (hσκ : ∀ w ∈ polydisc (0 : ParIdx Ga X₁ → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σp w P‖ < Real.exp κ)
    (hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx),
      P ∉ (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).parCubes X₁f → σp w ⟨P, hP⟩ = 1)
    {γ : Measure (unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)} {K : Set (unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)}
    (hKc : IsCompact K) (hKb : ∀ ψ ∈ K, ∀ r, |ψ r| ≤ cψ) (hγ : γ K < ⊤)
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ‖E r‖ ≤ Bd)
    (hP₂ : Precedes Gk₂ (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) (hq₂ : Precedes Gj₂ Gk₂)
    (colk₂ : ∀ z ∈ collar Gk₂, z ∈ (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω 1) (colj₂ : ∀ z ∈ collar Gj₂, z ∈ Gk₂.Ω 1)
    {X₀₂ X₁f₂ : Finset (CTorus d L N₁ m₁ (k + 1))} (dsX₀₂ : ∀ x ∈ dataSites Gk₂, x ∈ X₀₂)
    (hN₂ : ∀ x ∈ X₀₂, x ∈ (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω 1 →
      ∀ y : CTorus d L N₁ m₁ (k + 1), Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ * (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).spacing x → y ∈ X₁f₂)
    (hF₂ : FlSetting N (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) Gk₂ Hm₂ a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f₂)
    (hHm₂ : Hm₂.Ω (k + 1) = ∅)
    {Fk₂ : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk₂.Ω 1 × Fin N → ℂ) × (Gk₂.Ω 1 → ℂ)}
    (hFkan₂ : AnalyticOnNhd ℂ Fk₂ {p | ∃ D : BgData Gk₂ N,
      InUnionDomainC Gk₂ (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk₂ : ∀ D : BgData Gk₂ N, InUnionDomainC Gk₂ (bgC0 d L N) (bgC1 d L N) ν D →
      Fk₂ (rawOf D) = (bgFieldC Gk₂ (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk₂ (compWeight L a₁) ν (bgC0 d L N) D))
    {E₂ : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hE₂ : AnalyticOnNhd ℂ E₂ (XiCRaw Gj₂ (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    {F₁₂ : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) × ((GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁an₂ : AnalyticOnNhd ℂ F₁₂ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) N,
      InUnionDomainC (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁₂ : ∀ (s : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))))) (D : BgData (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁₂ (s, rawOf D) = (φ, α))
    {Sol₂ : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) × Edat Hm₂ N → (Hm₂.Ω 1 × Fin N → ℂ) × (Hm₂.Ω 1 → ℂ)}
    (hSolan₂ : AnalyticOnNhd ℂ Sol₂ {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm₂ N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol₂ : ∀ p : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) × Edat Hm₂ N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm₂ N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₂ p).1 = dphi Hm₂ (Dec2.decG (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) Hm₂ (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm₂ (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ p).2 ∧
        Dec2.DecFixed (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) Hm₂ (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm₂ (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ p).2 ∧
        Small Hm₂ (Sol₂ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm₂ (Sol₂ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm₂ (Sol₂ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm₂.Ω 1 → ℂ, Small Hm₂ δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) Hm₂ (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm₂ (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ p).2))
    {σp₂ : (ParIdx Ga (σ '' X₁) → ℂ) → Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))))}
    (hσp₂ : ∀ w P, σp₂ w P = if P.1.2 ∈ (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) then
      Dec2.extS (coverOf Ga) (extParams Ga (σ '' X₁) w) P.1 else 0) (hσan₂ : ∀ w, AnalyticAt ℂ σp₂ w)
    (hσκ₂ : ∀ w ∈ polydisc (0 : ParIdx Ga (σ '' X₁) → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σp₂ w P‖ < Real.exp κ)
    (hσ1₂ : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))).cubeIdx),
      P ∉ (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))).parCubes X₁f₂ → σp₂ w ⟨P, hP⟩ = 1)
    {γ₂ : Measure (unitPts (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)} {K₂ : Set (unitPts (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)}
    (hKc₂ : IsCompact K₂) (hKb₂ : ∀ ψ ∈ K₂, ∀ r, |ψ r| ≤ cψ) (hγ₂ : γ₂ K₂ < ⊤)
    (hEb₂ : ∀ r ∈ XiCRaw Gj₂ (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ‖E₂ r‖ ≤ Bd)
    (hσ : σ ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))
    (hYp : (∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (GsSpec.torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (GsSpec.torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁)))
    (hYp₂ : (∀ z, z ∈ Yp₂ ↔ ∃ x ∈ σ '' Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (GsSpec.torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (GsSpec.torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁)))
    (hΩk : ∀ i, ((Gk₂.Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1))) =
      σ '' ((Gk.Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1)))) (hΩj : ∀ i, ((Gj₂.Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1))) =
      σ '' ((Gj.Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1)))) (hΩm : ∀ i, ((Hm₂.Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1))) =
      σ '' ((Hm.Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1))))
    (hEr : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), E₂ (symRaw σ r) = E r)
    (hKγ : ∀ u : unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) ≃ unitPts (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))),
      (∀ (y : unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (x : CTorus d L N₁ m₁ (k + 1)),
        unitBlock (σ x) = (u y : UnitTorus d L N₁ m₁ k) ↔ unitBlock x = (y : UnitTorus d L N₁ m₁ k)) →
      (∀ ψ : unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ,
        (fun r : unitPts (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) × Fin N => ψ ((u.prodCongr (Equiv.refl (Fin N))).symm r)) ∈ K₂ ↔
          ψ ∈ K) ∧
      Measure.map (fun (ψ : unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ) (r : unitPts (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) × Fin N) =>
        ψ ((u.prodCongr (Equiv.refl (Fin N))).symm r)) γ = γ₂)
    {εseq : ℕ → ℝ} (hεseq : εseq (k + 1) ≤ eps)
    (Gf : RawData d L (N₁ * L ^ m₁) (k + 1) N → (ParIdx Ga X₁ → ℂ) → ℂ)
    (hGf : ∀ (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ParIdx Ga X₁ → ℂ), Gf Θ w =
      ∫ ψ in K,
            eTermFun (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj Hm
              (compWeight L a₁) Fk E (F₁ (σp w, Θ))
        (Sol (σp w, flEdat (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Hm (F₁ (σp w, Θ)) Θ.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁ (σp w, Θ)).2 (Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (σp w))
                (barField (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁
                  (σp w, Θ)).1) (unitQ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁ (σp w, Θ)).2 (Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (σp w))
                (barField (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁
                  (σp w, Θ)).1) (unitQ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ)
    (Gf₂ : RawData d L (N₁ * L ^ m₁) (k + 1) N → (ParIdx Ga (σ '' X₁) → ℂ) → ℂ)
    (hGf₂ : ∀ (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ParIdx Ga (σ '' X₁) → ℂ), Gf₂ Θ w =
      ∫ ψ in K₂,
            eTermFun (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) Gk₂ Gj₂ Hm₂
              (compWeight L a₁) Fk₂ E₂ (F₁₂ (σp₂ w, Θ))
        (Sol₂ (σp₂ w, flEdat (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) Hm₂ (F₁₂ (σp₂ w, Θ)) Θ.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁₂ (σp₂ w, Θ)).2 (Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) (σp₂ w))
                (barField (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁₂
                  (σp₂ w, Θ)).1) (unitQ (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁₂ (σp₂ w, Θ)).2 (Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) (σp₂ w))
                (barField (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁₂
                  (σp₂ w, Θ)).1) (unitQ (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ₂)
    (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hp : (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) p.1 p.2) :
    evTerm (fun i : ParIdx Ga (σ '' X₁) => i.1.1) Ga m₀ (σ '' X₁) Gf₂ (σ '' Y) (clipRaw (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) (actField σ p.1, actField σ p.2)) =
      evTerm (fun i : ParIdx Ga X₁ => i.1.1) Ga m₀ X₁ Gf Y (clipRaw (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) p) := by
  have hL : 3 ≤ L := HBp.hL
  have hm₁ : 2 ≤ m₁ := by
    by_contra h
    push Not at h
    have hL2 : L ^ m₁ ≤ L ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  obtain ⟨F⟩ := nonempty_fullSymm_of_mem_pavingSymGroup hG hNm hσ
  have hΩ := mem_Ω_iff_of_image (localB_collar_pavingGS hk (le_refl (minSep L (L ^ m₁))) hσ hYp
    hYp₂)
  have hca₂ := localB_cubeAligned hk Yp₂ (le_refl (minSep L (L ^ m₁))) hm₁
  have hσf : σp = fun w P => if P.1.2 ∈ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) then
      Dec2.extS (coverOf Ga) (extParams Ga X₁ w) P.1 else 0 := funext fun w => funext (hσp w)
  have hσf₂ : σp₂ = fun w P => if P.1.2 ∈ (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) then
      Dec2.extS (coverOf Ga) (extParams Ga (σ '' X₁) w) P.1 else 0 :=
    funext fun w => funext (hσp₂ w)
  refine localB_eTermHat_evTerm_paving (cI := fun i : ParIdx Ga X₁ => i.1.1)
    (cI' := fun i : ParIdx Ga (σ '' X₁) => i.1.1) (X₁ := X₁) Y hb₁ hbC hk Yp Yp₂ hN₁ hMM hag hS
    hk1 ha₁ ha₂ HBp HBk HBj hκ hM hMX hnum hj hmarD hαD hsm cc hcψ hδ₁ hP hq colk colj dsX₀ hN
    hF hHm hFkan hFk hE hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hKc hKb hγ hEb hP₂ hq₂ colk₂ colj₂
    dsX₀₂ hN₂ hF₂ hHm₂ hFkan₂ hFk₂ hE₂ hF₁an₂ hF₁₂ hSolan₂ hSol₂ hσan₂ hσκ₂ hσ1₂ hKc₂ hKb₂ hγ₂
    hEb₂ hσ hYp hYp₂ hΩk hΩj hΩm F.lat F.polymer (parEquiv F.cover F.polymer rfl)
    (fun _ => rfl) (fun i => i.1.2) (fun w' P P' hP hP' h1 hc => ?_) hEr hKγ hεseq Gf hGf Gf₂ hGf₂
    p hp
  rw [hσf, hσf₂]
  exact localB_tauExt_sym hG hk hΩ hca₂ F.cover F.polymer X₁ w' P P' hP hP' h1 hc

end PavingTau

end Balaban.Localization
