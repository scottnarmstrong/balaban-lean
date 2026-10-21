/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FrozenLFStep
public import Balaban.Spine.BaseFlat
public import Balaban.Spine.InheritedBound
public import Balaban.LargeField.R.CoefBirth

/-!
# The coefficient data of the images of the steps, from one generic statement

`D1CorrLim` (the coefficient data `v^{(j)}_{1,2}` of P5 (1.8) as thermodynamic limits, P1 (3.110))
exists for every small-field datum that is a member of the second-version class on the birth domains:
`d1CorrLim_of_d2sf2` (pre-`R`, (D2)) and `d1CorrLim_of_sfflat2` (frozen, (D2♭), with the mass cap of
the birth masses).  The levels `j ≤ k` of the image are read on the birth domains with the factor
`e²` between the birth mass of the level and the ideal mass of the current scale, so the old limits
are not transferred: the same statement covers the inherited levels and the new level.  The three
inputs of the spine that ask for the coefficient data are instances:

* `lfCorrInput_of_prefix` (`LFCorrInput`) from (D2) of the image;
* `frozenCorrInput_of_prefix` (`FrozenCorrInput`) from (D2♭) of the image and the mass bound;
* `baseCorrInput_of_canon` (`BaseCorrInput`, regime (A)) and `baseCorrInput_flat_of_canon`
  (regime (B)) for a first-step map whose source form and coefficient data are the canonical ones
  `corrSrc`, `corrVc` (a constraint on the provider's map).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6v2

section Generic

variable {d N : ℕ} {δ : ℝ} {T : ℝ → ℝ → Typing} {P6 : ℝ → ℝ → Def6.Consts}
  {C7 : ℝ → ℝ → Consts7} {PB : ℝ → ℝ → BudgetConsts} {cs₀ : ℝ → ℝ → OpConsts}
  {M1 c : ℝ → ℝ → ℕ} {rH ϱ : ℝ → ℝ → ℝ}

/-- The numerical facts of the prefix that the coefficient limit reads: `d ≥ 3`, `L ≥ 3`,
`ϱ ≥ R₀(d, L)` and the entropy tie `a_ent + 1 < κ_flow`. -/
theorem prefix_corr_facts (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ) {κ : ℝ} (hκ : 0 < κ)
    {c₉ : ℝ} (hc₉ : 0 < c₉) :
    3 ≤ d ∧ 3 ≤ (T κ c₉).L ∧ Background.bgR0 d (T κ c₉).L ≤ ϱ κ c₉ ∧
      Fluctuation.aEnt d (T κ c₉).L + 1 < (P6 κ c₉).κ := by
  obtain ⟨hL3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTy, hϱ, -, -, -, hE⟩ :=
    hP κ hκ c₉ hc₉
  exact ⟨hTy.1.three_le_d, hL3, hϱ, hE⟩

/-- **(D2) gives the coefficient data** (the generic statement, pre-`R`). -/
theorem corr_of_d2sf2 (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ) {κ : ℝ} (hκ : 0 < κ)
    {c₉ : ℝ} (hc₉ : 0 < c₉) [NeZero (T κ c₉).L] {k : ℕ}
    {sf : SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉)} {k0 : ℕ} {fac : ℕ → ℝ}
    (h : D2SF2 (P6 κ c₉) k0 sf fac) (hν : ∀ j, 1 ≤ j → j ≤ k → 0 ≤ sf.ν j)
    (hv : EuclideanSpace ℝ (Fin N)) (hhv : ‖hv‖ = 1) :
    ∃ (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d (T κ c₉).L N₁ (C7 κ c₉).m₁ k N)
      (vc : CorrCoef d), D1CorrLim (P6 κ c₉).m₀ sf St hv vc := by
  obtain ⟨hd, hL, hϱ, hE⟩ := prefix_corr_facts hP hκ hc₉
  exact ⟨_, _, d1CorrLim_of_d2sf2 h hd hL hϱ hE hν hv hhv⟩

/-- **(D2♭) gives the coefficient data** (the generic statement, frozen). -/
theorem corr_of_sfflat2 (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ) {κ : ℝ} (hκ : 0 < κ)
    {c₉ : ℝ} (hc₉ : 0 < c₉) [NeZero (T κ c₉).L] {k : ℕ}
    {sf : SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉)} {k0 : ℕ}
    (h : SFFlat2 (P6 κ c₉) k0 sf) (hν : ∀ j, 1 ≤ j → j ≤ k → 0 ≤ sf.ν j)
    (hcap : ∀ j, 1 ≤ j → j ≤ k → physMass (T κ c₉).L j (sf.ν j) * (((T κ c₉).L : ℝ) ^ k) ^ 2 ≤ 1)
    (hv : EuclideanSpace ℝ (Fin N)) (hhv : ‖hv‖ = 1) :
    ∃ (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d (T κ c₉).L N₁ (C7 κ c₉).m₁ k N)
      (vc : CorrCoef d), D1CorrLim (P6 κ c₉).m₀ sf St hv vc := by
  obtain ⟨hd, hL, hϱ, hE⟩ := prefix_corr_facts hP hκ hc₉
  exact ⟨_, _, d1CorrLim_of_sfflat2 h hd hL hϱ hE hν hcap hv hhv⟩

/-- The masses of a run that satisfies (I.2) up to `k` are positive. -/
theorem run_nu_pos {L : ℕ} {β ν a ε : ℝ} {βs νs : ℕ → ℝ} {k : ℕ}
    (h : RunningHypTo d L β ν a ε βs νs k) {j : ℕ} (hj : j ≤ k) : 0 < νs j := by
  obtain ⟨δj, hδ0, -, hν⟩ := h.nu_eq j hj
  rw [hν]
  have := h.hν
  have hL : (0 : ℝ) < L := by have := h.hL; exact_mod_cast (by omega : 0 < L)
  positivity

/-- **`LFCorrInput`** is an instance of `corr_of_d2sf2`. -/
theorem lfCorrInput_of_prefix (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
      SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
        SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉)) :
    LFCorrInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ := by
  intro κ hκ c₉ hc₉
  refine ⟨0, fun β _ ν hν hνL h hh kf hkf _ _ k hk1 hkk ρ νk rec hD2 _ _ _ hΦ _ => ?_⟩
  refine corr_of_d2sf2 hP hκ hc₉ hD2 (fun j hj1 hjk => ?_) h hh
  by_cases hj : j ≤ k
  · rw [(hΦ j hj).2.1]
    exact (run_nu_pos rec.run hj).le
  · obtain ⟨ρsf, hF⟩ := hD2.sfClass
    have : j = k + 1 := by omega
    subst this
    exact hF.coeff.nu_pos.le

/-- The caps of the birth masses of a run that satisfies (I.2) up to the top scale, with the mass
bound `ν_K ≤ 9/10` there. -/
theorem cap_of_run_top {L K : ℕ} (hL : 3 ≤ L) {β ν a : ℝ} {βs νs : ℕ → ℝ}
    (h : RunningHypTo d L β ν a (1 / 20) βs νs K) (h9 : νs K ≤ 9 / 10) {j : ℕ} (hj : j ≤ K) :
    physMass L j (νs j) * ((L : ℝ) ^ K) ^ 2 ≤ 1 := by
  obtain ⟨δj, hδj0, hδj, hνj⟩ := h.nu_eq j hj
  obtain ⟨δk, hδk0, hδk, hνk⟩ := h.nu_eq K le_rfl
  rw [hνj]
  exact physMass_cap_of_top hL h.hν hδj0 hδj hδk0 hδk (by rw [← hνk]; exact h9)

/-- **`FrozenCorrInput`** is an instance of `corr_of_sfflat2`. -/
theorem frozenCorrInput_of_prefix (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
      SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
        SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉)) :
    FrozenCorrInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ := by
  intro κ hκ c₉ hc₉
  refine ⟨0, fun β _ ν hν hνL h hh kf hkf _ _ k hk1 hk0 hk ρ νk hM6 hkK R geo cs P F St vc hF
    hνk hSF _ _ _ hΦ _ => ?_⟩
  obtain ⟨hd, hL3, hϱ, hE⟩ := prefix_corr_facts hP hκ hc₉
  obtain ⟨hgeo, h1, h2, h3, h4, h5, h6, h7, hrep, hβ0, hν0, hνk', hrun, hcoh, hX⟩ := hF
  have hνpos : 0 < νk := hνk' ▸ run_nu_pos hrun le_rfl
  have hrunΦ : RunningHypTo d (T κ c₉).L β ν (cs₀ κ c₉).aKer (1 / 20) (Φ κ c₉ β ν k F.sf).β
      (Φ κ c₉ β ν k F.sf).ν k := by
    refine ⟨hrun.hd, hrun.hL, hrun.hβ, hrun.hν, hrun.ha1, hrun.ha2, hrun.hε0, hrun.hε,
      fun j hj => ?_, fun j hj => ?_⟩
    · rw [(hΦ j hj).1]; exact hrun.beta_eq j hj
    · rw [(hΦ j hj).2.1]; exact hrun.nu_eq j hj
  have hFR := flowRateInput_of_prefix hP κ hκ c₉ hc₉
  have hCΦ := hSF.coeff
  have hrun' := runningHypTo_succ_of_coeffBounds_core (P := massOne (P6 κ c₉))
    hSF.admissible.γ_pos hSF.admissible.c₈_pos hFR hCΦ
    (by rw [(hΦ 0 (Nat.zero_le _)).1]; exact hβ0)
    (by rw [(hΦ 0 (Nat.zero_le _)).2.1]; exact hν0) hrunΦ
  have hνkΦ : 0 < (Φ κ c₉ β ν k F.sf).ν k := by
    rw [(hΦ k le_rfl).2.1, hνk']; exact hνpos
  have hmass := nu_succ_le_of_coeffBounds (P := massOne (P6 κ c₉)) hrun.hL hSF.admissible.γ_pos
    hFR hCΦ hνkΦ
  rw [(hΦ k le_rfl).2.1, hνk'] at hmass
  have h9 : (Φ κ c₉ β ν k F.sf).ν (k + 1) ≤ 9 / 10 := by nlinarith
  refine corr_of_sfflat2 hP hκ hc₉ hSF (fun j hj1 hjk => ?_) (fun j hj1 hjk => ?_) h hh
  · by_cases hj : j ≤ k
    · rw [(hΦ j hj).2.1]; exact (run_nu_pos hrun hj).le
    · have : j = k + 1 := by omega
      subst this; exact hCΦ.nu_pos.le
  · exact cap_of_run_top hL3 hrun' h9 hjk

/-- **`BaseCorrInput` in regime (A)** for a first-step map whose source form and coefficient data
are the canonical ones (`corrSrc`, `corrVc`): a constraint on the provider's map, as for the
canonical histories. -/
theorem baseCorrInput_of_canon (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (Γ : BaseMap d N T C7 cs₀ ϱ)
    (hS : BaseSFInput d N T P6 C7 cs₀ ϱ (fun k => 1 ≤ k) Γ)
    (hΓ : ∀ κ c₉ β ν h kf [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
      (Γ κ c₉ β ν h kf).St = corrSrc (Γ κ c₉ β ν h kf).sf ∧
        (Γ κ c₉ β ν h kf).vc = corrVc (P6 κ c₉).m₀ (Γ κ c₉ β ν h kf).sf) :
    BaseCorrInput d N T P6 C7 cs₀ ϱ (fun k => 1 ≤ k) Γ := by
  intro κ hκ c₉ hc₉
  obtain ⟨b, hb⟩ := hS κ hκ c₉ hc₉
  refine ⟨b, fun β hβ ν hν hνL h hh kf hkf _ _ hk1 => ?_⟩
  obtain ⟨hD2, -, -, -, hβ0, hν0, hrun0, -⟩ := hb β hβ ν hν hνL h hh kf hkf hk1
  obtain ⟨hSt, hvc⟩ := hΓ κ c₉ β ν h kf
  rw [hSt, hvc]
  obtain ⟨hd, hL, hϱ, hE⟩ := prefix_corr_facts hP hκ hc₉
  refine d1CorrLim_of_d2sf2 hD2 hd hL hϱ hE (fun j hj1 hjk => ?_) h hh
  obtain ⟨ρsf, hF⟩ := hD2.sfClass
  have : j = 1 := by omega
  subst this
  exact hF.coeff.nu_pos.le

/-- **`BaseCorrInput` in regime (B)** (as `baseCorrInput_of_canon`, from (D2♭)). -/
theorem baseCorrInput_flat_of_canon (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (Γ : BaseMap d N T C7 cs₀ ϱ) (hS : BaseFlatSFInput d N T P6 C7 cs₀ ϱ Γ)
    (hΓ : ∀ κ c₉ β ν h kf [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
      (Γ κ c₉ β ν h kf).St = corrSrc (Γ κ c₉ β ν h kf).sf ∧
        (Γ κ c₉ β ν h kf).vc = corrVc (P6 κ c₉).m₀ (Γ κ c₉ β ν h kf).sf) :
    BaseCorrInput d N T P6 C7 cs₀ ϱ (fun k => k = 0) Γ := by
  intro κ hκ c₉ hc₉
  obtain ⟨b, hb⟩ := hS κ hκ c₉ hc₉
  refine ⟨b, fun β hβ ν hν hνL h hh kf hkf _ _ hk0 => ?_⟩
  obtain ⟨hSF, -, -, -, hβ0, hν0, hrun0, -⟩ := hb β hβ ν hν hνL h hh kf hkf hk0
  obtain ⟨hSt, hvc⟩ := hΓ κ c₉ β ν h kf
  rw [hSt, hvc]
  obtain ⟨hd, hL3, hϱ, hE⟩ := prefix_corr_facts hP hκ hc₉
  set G := Γ κ c₉ β ν h kf
  have hFR := flowRateInput_of_prefix hP κ hκ c₉ hc₉
  have hrun1 := runningHypTo_succ_of_coeffBounds_core (k := 0) (P := massOne (P6 κ c₉))
    hSF.admissible.γ_pos hSF.admissible.c₈_pos hFR hSF.coeff hβ0 hν0 hrun0
  have hνpos : 0 < G.sf.ν 0 := run_nu_pos hrun0 le_rfl
  have hmass := nu_succ_le_of_coeffBounds (k := 0) (P := massOne (P6 κ c₉)) hrun0.hL
    hSF.admissible.γ_pos hFR hSF.coeff hνpos
  rw [hν0] at hmass
  have h9 : G.sf.ν 1 ≤ 9 / 10 := by
    have : ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 := hνL
    nlinarith
  refine d1CorrLim_of_sfflat2 hSF hd hL3 hϱ hE (fun j hj1 hjk => ?_) (fun j hj1 hjk => ?_) h hh
  · have : j = 1 := by omega
    subst this; exact hSF.coeff.nu_pos.le
  · exact cap_of_run_top hL3 hrun1 h9 hjk

end Generic

end Balaban.RootFSpine
