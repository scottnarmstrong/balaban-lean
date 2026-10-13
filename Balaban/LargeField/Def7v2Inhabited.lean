/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7v2Variants
public import Balaban.LargeField.Def7Inhabited
public import Balaban.SmallField.Def6v2Inhabited
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Def-7 v2: inhabitation (hard rule 10) -- DRAFT

**Draft, pending Roland's answer to Q13.**  The witness of `Def7Inhabited` (`d = L = 3`, `N = 2`,
`K = k = 1`, `M = 27`, `m₁ = 3`, `wP6 = witnessConsts 1`), adapted to the second version:

* the small-field data `wSF2 ν`: the same running coefficients (`β_n = β 3^n`, `ν_n = ν 9^n`,
  `a ≡ 5/4`) with the terms `pinTerms … (fun _ => 0)` (zero terms, a member of Def-6 v2 on the wide
  domain: `isSF2_pinTerms`; the landed witness uses `zeroFam`, which is not a member of `IsSF2`);
* `wIsRep2`, `wIsRepPre2`, `wIsRepFlat2`, `wIsRepFam2`, `wIsRepFamPre2`;
* `wIsRep2_mass_split`: for `β ν 27 ≤ 1` the regime index is `k₀ = kZero(β, ν) ≥ 1`, so at `k = 1 ≤ k₀`
  the large-field solver mass `cs.mu 1` is `0` while the physical (small-field action) mass
  `cs.muAct 1 = 9ν/9 > 0`: **the witness is at a parameter choice with `k₀ ≥ 1`, the case where
  the second version differs from the landed class** (the landed `sfActMass` would be `0`);
* `nonempty_*` for every new structure and bundled `Prop`.

**Not inhabited here:** `IsRep2WithInterface` (module `Def7v2Class`): its (D9) forces `k ≤ k₀`, where
the interface clause has no witness (the chord of zero terms is a positive quantity whose bound
(3.5) is an open estimate; `Def7v2Interface`, `IsRepA`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Def7v2.Wit

open MeasureTheory Balaban RegionHistory Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Background Balaban.LargeField.Def7
  Balaban.LargeField.Def7.Wit Filter Topology

/-! ### The small-field data -/

theorem wCoef_zero {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] (κ : ℝ) (j : ℕ)
    (X : Set (Localization.CTorus d L N₁ m₁ k)) :
    wCoef κ (fun _ => 0) j X = 0 := by
  unfold wCoef; split_ifs <;> simp

/-- The terms of the witness: the zero field-dependent terms `pinTerms … 0`. -/
noncomputable abbrev wTm (m₁ N₁ : ℕ) [NeZero N₁] : Terms 3 3 N₁ m₁ 1 2 (bgR0 3 3) :=
  pinTerms 3 3 N₁ m₁ 1 2 (bgR0 3 3) (witnessConsts 1).κ (fun _ => 0)

/-- **The small-field data of the second-version witness.** -/
noncomputable def wSF2 (ν : ℝ) (m₁ : ℕ) : SFData 3 3 m₁ 1 2 (bgR0 3 3) where
  β := wβs
  ν := wνs ν
  z := fun _ => 1
  a := witnessa
  E := fun _ => 0
  Tm := fun N₁ _ => wTm m₁ N₁
  Rt := fun _ _ _ _ _ _ _ => 0
  corr := fun _ _ _ _ _ _ _ => 0

theorem wIsSFFamily2 (ν : ℝ) (hν0 : 0 < ν) (hν : ν * 9 ≤ 7 / 72) (m₁ k0 : ℕ) :
    IsSFFamily2 (d := 3) (L := 3) (m₁ := m₁) (k := 1) (N := 2) (ϱ := bgR0 3 3)
      (witnessConsts 1) (⟨k0, wνs ν⟩ : Regime 3) wβs witnessa
      (fun _ _ => xiFieldDom (aIdeal 3 1 (witnessa 1)) (physMass 3 1 (wνs ν 1))
        ((witnessConsts 1).eps 3 3))
      (fun N₁ _ => wTm m₁ N₁)
      (fun N₁ _ => rho2 (witnessConsts 1) ⟨k0, wνs ν⟩ wβs witnessa (wTm m₁ N₁) 0)
      (fun _ => 0) where
  admissible := witnessConsts_admissible one_pos
  coeff := wcoeff ν hν0 hν
  torus := fun N₁ _ => isSF2_pinTerms le_rfl (witnessConsts_admissible one_pos).κ_pos.le
    (fun _ => le_rfl) (fun j => by simpa using (witness_c9_pos 1 j).le) (witness_c9_pos 1)
    (fun j hj => absurd rfl hj)
    (bgHyp_of_class2 (witnessConsts_admissible one_pos) (wcoeff ν hν0 hν) le_rfl le_rfl le_rfl)
  torusIndep := torusIndep_pinTerms _ _ _
  renorm := fun _ _ _ => renormCond_pinTerms _ _ _ _ _ _

theorem wSF2_rTerms (ν : ℝ) (m₁ : ℕ) (fac : ℕ → ℝ) (hfac : ∀ nn, 0 ≤ fac nn) (N₁ : ℕ)
    [NeZero N₁] :
    RTermsH4 (ϱ := bgR0 3 3) (witnessConsts 1) wβs (wνs ν) witnessa N₁ ((wSF2 ν m₁).Rt N₁) fac :=
  wSF_rTerms ν m₁ fac hfac N₁

/-- (D2) of the second version for the witness. -/
theorem wSF2_D2 (ν : ℝ) (hν0 : 0 < ν) (hν : ν * 9 ≤ 7 / 72) (k0 m₁ : ℕ) (fac : ℕ → ℝ)
    (hfac : ∀ nn, 0 ≤ fac nn) : D2SF2 (witnessConsts 1) k0 (wSF2 ν m₁) fac where
  sfClass := ⟨_, wIsSFFamily2 ν hν0 hν m₁ k0⟩
  rTerms := fun N₁ _ => wSF2_rTerms ν m₁ fac hfac N₁

/-- (D8), small-field part, for the witness (all terms vanish). -/
theorem wSF2_D8 (ν : ℝ) (m₁ : ℕ) : D8SF (witnessConsts 1).m₀ (wSF2 ν m₁) where
  M_eq := by
    intros
    simp [wSF2, wTm, pinTerms, wCoef_zero]
  R_eq := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl

/-- (D9) for the witness. -/
theorem wSF2_D9 (ν : ℝ) (hν0 : 0 < ν) (hν : ν * 9 ≤ 7 / 72) (m₁ k0 : ℕ) (hk0 : 1 ≤ k0) :
    D9Coeff (witnessConsts 1) k0 (wSF2 ν m₁) where
  beta_gt := by
    have := wβ_pos
    simp [witnessConsts, wSF2, wβs]
    positivity
  nu_pos := by simp only [wSF2, wνs]; positivity
  nu_le := by simp only [wSF2, wνs, witnessConsts]; linarith
  k_le := hk0

/-- The coefficient data of the witness are zero: the terms `ℰ` vanish. -/
theorem wD1CorrLim (ν : ℝ) (m₁ : ℕ) (hv : EuclideanSpace ℝ (Fin 2)) :
    D1CorrLim (witnessConsts 1).m₀ (wSF2 ν m₁)
      (fun N₁ _ => sourceOf (wSF2 ν m₁).ν ((wSF2 ν m₁).Tm N₁)) hv
      ⟨fun _ _ => 0, fun _ _ => 0⟩ where
  src_pos := fun _ _ _ _ _ _ _ _ _ _ => rfl
  v1_lim := by
    intro j _ _ z
    have h : ∀ n : ℕ, (haveI : NeZero (torusSeq 3 (witnessConsts 1).m₀ n) :=
        ⟨torusSeq_ne_zero _ n⟩
        v1T (witnessConsts 1).m₀ (sourceOf (wSF2 ν m₁).ν ((wSF2 ν m₁).Tm (torusSeq 3 (witnessConsts 1).m₀ n))) j
          (nuIdeal 3 1 ((wSF2 ν m₁).ν 1) j) (hC hv) 0 (blockPt j z)) = 0 := by
      intro n
      have : NeZero (torusSeq 3 (witnessConsts 1).m₀ n) := ⟨torusSeq_ne_zero _ n⟩
      unfold v1T
      refine finsum_mem_eq_zero_of_forall_eq_zero fun X _ => ?_
      exact v1Loc_zero _ _ _ _
    simp only [h]
    exact tendsto_const_nhds
  v2_lim := by
    intro j _ _ e₂ _ _ z
    have h : ∀ n : ℕ, (haveI : NeZero (torusSeq 3 (witnessConsts 1).m₀ n) :=
        ⟨torusSeq_ne_zero _ n⟩
        v2T (witnessConsts 1).m₀ (sourceOf (wSF2 ν m₁).ν ((wSF2 ν m₁).Tm (torusSeq 3 (witnessConsts 1).m₀ n))) j
          (nuIdeal 3 1 ((wSF2 ν m₁).ν 1) j) (hC hv) (fun i => (e₂ i : ℂ)) 0
          (blockPt j z)) = 0 := by
      intro n
      have : NeZero (torusSeq 3 (witnessConsts 1).m₀ n) := ⟨torusSeq_ne_zero _ n⟩
      unfold v2T
      refine finsum_mem_eq_zero_of_forall_eq_zero fun X _ => ?_
      exact v2Loc_zero _ _ _ _ _
    simp only [h]
    exact tendsto_const_nhds

/-! ### The family and the density -/

/-- The family of representations of the second-version witness. -/
noncomputable def wFam2 (ν : ℝ) (k0 r : ℕ) :
    RepFam wS wR k0 1 27 2 wGeoF (wCs ν k0) (budgetConsts wβ) 1 wC7.m₁ (bgR0 3 3) where
  sf := wSF2 ν 3
  lf := fun nK _ => wRep ν k0 r nK

/-- The coefficient data of the witness. -/
def wVc : CorrCoef 3 := ⟨fun _ _ => 0, fun _ _ => 0⟩

/-- The density of the second-version witness, defined by (D1) v2. -/
noncomputable def wRho2 (ν : ℝ) (k0 r : ℕ) : ∀ (nK : ℕ) [NeZero nK],
    (BlockAt wS (sides wS.L 1 nK) 27 1 1 → EuclideanSpace ℝ (Fin 2)) →
      (GIdx wS (sides wS.L 1 nK) 27 1 2 → ℂ) → ℂ :=
  fun nK _ ψk g => ∑ A ∈ (wRep ν k0 r nK).hist,
    postTerm2 ((wFam2 ν k0 r).ctx wM6 le_rfl nK) wVc (wRep ν k0 r nK) A ψk whv g

/-- The pre-`R` density of the second-version witness. -/
noncomputable def wRhoPre2 (ν : ℝ) (k0 r : ℕ) : ∀ (nK : ℕ) [NeZero nK],
    (BlockAt wS (sides wS.L 1 nK) 27 1 1 → EuclideanSpace ℝ (Fin 2)) →
      (GIdx wS (sides wS.L 1 nK) 27 1 2 → ℂ) → ℂ :=
  fun nK _ ψk g => ∑ A ∈ (wRep ν k0 r nK).hist,
    preTerm2 ((wFam2 ν k0 r).ctx wM6 le_rfl nK) wVc (wRep ν k0 r nK) A ψk whv g

/-- The source data of the witness. -/
noncomputable def wSt (ν : ℝ) : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms 3 3 N₁ wC7.m₁ 1 2 :=
  fun N₁ _ => sourceOf (wSF2 ν 3).ν ((wSF2 ν 3).Tm N₁)

section Clauses

variable (ν : ℝ) (k0 r : ℕ)

theorem wCoh2 : Coh wS wR (kZero wS.d wS.L wβ ν) 27 (wCs ν (kZero wS.d wS.L wβ ν))
    (budgetConsts wβ) wP6 wC7 wβ ν 1 (wSF2 ν 3) where
  M_eq := (wCoh ν).M_eq
  M_pow := (wCoh ν).M_pow
  lam_eq := (wCoh ν).lam_eq
  R_eq := (wCoh ν).R_eq
  k0_eq := (wCoh ν).k0_eq
  a_free := (wCoh ν).a_free
  beta_cs := (wCoh ν).beta_cs
  beta_P := (wCoh ν).beta_P
  z_cs := (wCoh ν).z_cs
  nu_cs := (wCoh ν).nu_cs
  delta_cs := (wCoh ν).delta_cs
  p0_cs := (wCoh ν).p0_cs
  B0_cs := (wCoh ν).B0_cs

theorem wField2 : FieldClauses wS k0 1 (wCs ν k0) (wSF2 ν 3) whv where
  h_unit := whv_norm
  mu_eq := fun _ _ => rfl
  muAct_eq := fun _ _ => rfl

theorem wForm2 (nK : ℕ) [NeZero nK] :
    D1Form2 ((wFam2 ν k0 r).ctx wM6 le_rfl nK) wVc (wRep ν k0 r nK) whv (wRho2 ν k0 r nK) := by
  intro ψk g _
  refine ⟨fun A _ => ?_, rfl⟩
  unfold PostConv2
  refine gConv_of_K_zero _ _ _ (fun c o x hv => ?_) _ _ _ _
  exact locOp_K_zero (wGeoF nK) (wCs ν k0) (wSD_zero ν k0 r nK) (wKD_zero ν k0 r nK) A.adm
    _ 1 le_rfl c.1 o x hv

theorem wFormPre2 (nK : ℕ) [NeZero nK] :
    D1PreForm2 ((wFam2 ν k0 r).ctx wM6 le_rfl nK) wVc (wRep ν k0 r nK) whv
      (wRhoPre2 ν k0 r nK) := by
  intro ψk g _
  refine ⟨fun A _ => ?_, rfl⟩
  unfold PreConv2
  refine gConv_of_K_zero _ _ _ (fun c o x hv => ?_) _ _ _ _
  exact preOpTop_K_zero (wGeoF nK) (wCs ν k0) (wSD_zero ν k0 r nK) A 1 le_rfl c o x hv

/-- (D7) of the pre-`R` class, second version, for the zero boundary terms of the witness, for
every frame of the fine size. -/
theorem wBdry2 (nK : ℕ) [NeZero nK] {m₀ m₁ : ℕ}
    (Fr : FineSizeFrame wS (sides wS.L 1 nK) 27 1 m₀ m₁)
    (Zof : LabHist wS (sides wS.L 1 nK) wR k0 1 →
    Set (Torus wS.d (sides wS.L 1 nK 1))) (aw μs ε ε1 νs : ℕ → ℝ) (fac rate : ℝ)
    (hfac : 0 < fac) (rH : ℝ) :
    D7Bdry2 Fr (sides_hnn wS.L 1 nK) le_rfl (wRep ν k0 r nK) Zof aw μs ε ε1 νs fac rate whv
      rH where
  loc_field := by intros; rfl
  loc_hist := by intros; rfl
  real := by intros; simp [wRep]
  analytic := fun _ _ _ _ _ _ => analyticOnNhd_const
  bound := by
    intros
    simp only [wRep, norm_zero]
    positivity
  rot := by intros; rfl
  euclid := by intros; rfl
  support := by intros; rfl

/-- (D7) of the post-`R` class, second version, for the zero boundary terms of the witness, for
every frame of the fine size. -/
theorem wBdry2Post (nK : ℕ) [NeZero nK] {m₀ m₁ : ℕ}
    (Fr : FineSizeFrame wS (sides wS.L 1 nK) 27 1 m₀ m₁)
    (Zof : LabHist wS (sides wS.L 1 nK) wR k0 1 → Set (Torus wS.d (sides wS.L 1 nK 1)))
    (aw μs ε ε1 νs : ℕ → ℝ) (fac rate : ℝ) (hfac : 0 < fac) (rH : ℝ) :
    D7Bdry2Post Fr (sides_hnn wS.L 1 nK) le_rfl (wRep ν k0 r nK) Zof aw μs ε ε1 νs fac rate whv
      rH where
  loc_field := by intros; rfl
  loc_hist := by intros; rfl
  real := by intros; simp [wRep]
  analytic := fun _ _ _ _ _ _ => analyticOnNhd_const
  bound := by
    intros
    simp only [wRep, norm_zero]
    positivity
  rot := by intros; rfl
  euclid := by intros; rfl
  support := by intros; rfl

end Clauses

/-! ### The witnesses -/

/-- **`IsRep2_1` is inhabited**: for every `0 < ν` with `β ν L^d ≤ 1` (so `k₀(β, ν) ≥ 1`), the
coefficient data `v₁ = v₂ = 0`, any pinned radius `rH`. -/
theorem wIsRep2 (ν : ℝ) (hν0 : 0 < ν) (hν : wβ * ν * 27 ≤ 1) (rH : ℝ) :
    IsRep2 wS wR (kZero wS.d wS.L wβ ν) 1 27 2 wGeoF (wCs ν (kZero wS.d wS.L wβ ν))
      (budgetConsts wβ) wP6 wC7 wβ ν whv rH 1 wM6 le_rfl
      (wFam2 ν (kZero wS.d wS.L wβ ν) (1 + 1)) (wRho2 ν (kZero wS.d wS.L wβ ν) (1 + 1))
      (wSt ν) wVc where
  coh := wCoh2 ν
  field := wField2 ν _
  complete := fun nK _ => wHist_complete _ _ nK
  form := fun nK _ => wForm2 ν _ _ nK
  corr := wD1CorrLim ν 3 whv
  sfData := wSF2_D2 ν hν0 (nine_le_of_mul hν0 hν) _ 3 (fun _ => 1) (fun _ => zero_le_one)
  pin := fun nK _ => wPin ν _ _ (1 + 1) le_rfl nK
  opBound := fun nK _ => wOpBound ν _ _ (1 + 1) nK
  budget := fun nK _ => (wRep ν _ (1 + 1) nK).budget_of_LF2 wS_good
    (budgetSetup wβ ν wβ_gt hν0 wβ_spec.2.2) (wPin ν _ _ (1 + 1) le_rfl nK) (by norm_num)
    le_rfl (one_le_kZero hν0 hν) le_rfl (by norm_num)
  bdry := fun nK _ => wBdry2Post ν _ _ nK _ _ _ _ _ _ _ _ _ one_pos rH
  coherent := wSF2_D8 ν 3
  coeff := wSF2_D9 ν hν0 (nine_le_of_mul hν0 hν) 3 _ (one_le_kZero hν0 hν)

/-- **The case where the second version differs from the landed class**: in the witness of
`wIsRep2` the regime index is `k₀ ≥ 1`, so at the scale `k = 1` the large-field solver mass `cs.mu`
vanishes while the physical mass `cs.muAct` (the mass of the small-field action `sfActMass2`) is
positive; the landed `sfActMass cs 1` is `0`. -/
theorem wIsRep2_mass_split (ν : ℝ) (hν0 : 0 < ν) (hν : wβ * ν * 27 ≤ 1) :
    1 ≤ kZero wS.d wS.L wβ ν ∧ (wCs ν (kZero wS.d wS.L wβ ν)).mu 1 = 0 ∧
      0 < sfActMass2 (wCs ν (kZero wS.d wS.L wβ ν)) 1 ∧
        sfActMass (wCs ν (kZero wS.d wS.L wβ ν)) 1 = 0 := by
  have hk := one_le_kZero hν0 hν
  have hmu : (wCs ν (kZero wS.d wS.L wβ ν)).mu 1 = 0 := by
    show (if 1 ≤ kZero wS.d wS.L wβ ν then 0 else _) = 0
    have hk' : 1 ≤ kZero wS.d wS.L wβ ν := hk
    simp [hk']
  refine ⟨hk, hmu, ?_, hmu⟩
  show 0 < wνs ν 1 / (wS.L : ℝ) ^ (2 * 1)
  have h1 : (0 : ℝ) < wνs ν 1 := by simp only [wνs]; positivity
  have h2 : ((wS.L : ℕ) : ℝ) = 3 := by norm_num [wS, setting, typing, typing0]
  rw [h2]
  positivity

/-- **`IsRep^pre2_1` is inhabited.** -/
theorem wIsRepPre2 (ν : ℝ) (hν0 : 0 < ν) (hν : wβ * ν * 27 ≤ 1) (rH : ℝ) :
    IsRepPre2 wS wR (kZero wS.d wS.L wβ ν) 1 27 2 wGeoF (wCs ν (kZero wS.d wS.L wβ ν))
      (budgetConsts wβ) wP6 wC7 wβ ν whv rH 1 wM6 le_rfl
      (wFam2 ν (kZero wS.d wS.L wβ ν) 1) (wRhoPre2 ν (kZero wS.d wS.L wβ ν) 1)
      (wSt ν) wVc where
  coh := wCoh2 ν
  field := wField2 ν _
  complete := fun nK _ => wHist_complete _ _ nK
  form := fun nK _ => wFormPre2 ν _ _ nK
  corr := wD1CorrLim ν 3 whv
  sfData := wSF2_D2 ν hν0 (nine_le_of_mul hν0 hν) _ 3 (preFac (wP6.m₀ + wC7.m₁))
    (fun nn => by unfold preFac; split_ifs <;> norm_num)
  pin := fun nK _ => wPin ν _ _ 1 (by norm_num) nK
  opBound := fun nK _ => wOpBound ν _ _ 1 nK
  budget := fun nK _ => (wRep ν _ 1 nK).budgetPre_of_LF2 wS_good
    (budgetSetup wβ ν wβ_gt hν0 wβ_spec.2.2) (wPin ν _ _ (1 + 1) le_rfl nK) (by norm_num)
    le_rfl (one_le_kZero hν0 hν) le_rfl
  bdry := fun nK _ => wBdry2 ν _ _ nK _ _ _ _ _ _ _ _ _ one_pos rH
  coherent := wSF2_D8 ν 3
  coeff := wSF2_D9 ν hν0 (nine_le_of_mul hν0 hν) 3 _ (one_le_kZero hν0 hν)

end Balaban.LargeField.Def7v2.Wit
