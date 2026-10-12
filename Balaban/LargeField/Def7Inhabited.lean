module

public import Balaban.LargeField.Def7WitSF
public import Balaban.LargeField.Def7WitData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Def-7: inhabitation (hard rule 10)

Every structure of the Def-7 draft is inhabited at an admissible choice of the parameters:
`d = L = 3`, `N = 2`, `M = 27 = 3^{0+3}`, the horizon `K = 1`, the scale `k = 1`, the large-field
setting `wS` with `Setting.Good` and the hypotheses of Lemma B (`Def7WitLF`), the small-field data
`wSF` (the zero effective action, a member of Def-6, `Def7WitSF`), the zero step and kept data
(`Def7WitData`), zero boundary terms, the complete set of histories `wHist` (`exists_isComplete`)
and the density defined by (D1).  The budget clause (D6) is LF-2 (i) (`Rep.budget_of_LF2`), the
operator bound (D5) holds for the zero kernels, and (D4) holds since no component of `Z^pre_1`
is ripe (`not_ripe_one`).

* `wIsRep`: `IsRep_1` for every `0 < ν ≤ 1/(27β)` (the regime index `k₀ = kZero(β, ν) ≥ 1`);
* `wIsRepPre`: `IsRep^pre_1`; `wIsRepFlat`: `IsRep^♭_1` at `ν₀ = 1/(27β)` (`k₀ = 1`,
  `k̂_f = 1`);
* `wIsRepFam`, `wIsRepFamPre`: the family classes over `0 < ν ≤ ν_*(1)`;
* `nonempty_*`: the `Nonempty` theorems for the data structures and every bundled `Prop`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Def7.Wit

open MeasureTheory Balaban RegionHistory Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Filter Topology

/-- The constants of Def-7 of the witness. -/
def wC7 : Consts7 where
  m₁ := 3
  A0 := 0
  A1 := 0
  B0 := 1
  Bst := 1

/-- The Def-6 constants of the witness. -/
noncomputable abbrev wP6 : Def6.Consts := witnessConsts 1

theorem wM6 : (27 : ℕ) = wS.L ^ (wP6.m₀ + wC7.m₁) := by
  show (27 : ℕ) = 3 ^ (0 + 3)
  norm_num

/-- The running constants of the operators of the witness. -/
noncomputable def wCs (ν : ℝ) (k0 : ℕ) : OpConsts where
  aw := Def6.aIdeal 3 1 (5 / 4)
  mu := bgMass k0 wS.L (wνs ν)
  muAct := fun j => wνs ν j / (wS.L : ℝ) ^ (2 * j)
  nu := wνs ν
  delta := deltaRun 0 wS.p0 (5 / 4) wβs
  p0 := pZero 0 wS.p0 (5 / 4) wβs
  Cpsi := 1
  beta := wβs
  z := fun _ => 1
  aKer := 5 / 4
  Cb := 0
  B0 := 1

/-- The physical field `h = e_0`. -/
noncomputable def whv : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

theorem whv_norm : ‖whv‖ = 1 := by simp [whv]

/-- The geometric typing on every torus. -/
noncomputable def wGeoF : ∀ (nK : ℕ) [NeZero nK], Geo wS (sides wS.L 1 nK) wR 27 := fun _ _ => wGeo _

/-- The frame of the fine size on the torus `n_K = nK` of the witness: `m₀ = 0`, `m₁ = 3`,
`N₁ = L^{m₀} n_K`. -/
noncomputable def wFrame (nK : ℕ) [NeZero nK] : FineSizeFrame wS (sides wS.L 1 nK) 27 1 wP6.m₀ wC7.m₁ :=
  fineFrame wS (sides wS.L 1 nK) 1 wM6

/-- A complete set of histories up to scale `1` (with `R`-records below `r`). -/
noncomputable def wHist (k0 r nK : ℕ) [NeZero nK] : Finset (LabHist wS (sides wS.L 1 nK) wR k0 1) :=
  Classical.choose (exists_isComplete (S := wS) (n := sides wS.L 1 nK) (R := wR) (k0 := k0)
    (K := 1) 1 r)

theorem wHist_complete (k0 r nK : ℕ) [NeZero nK] : IsComplete 1 r (wHist k0 r nK) :=
  Classical.choose_spec (exists_isComplete (S := wS) (n := sides wS.L 1 nK) (R := wR) (k0 := k0)
    (K := 1) 1 r)

/-- The representation of the witness on the torus `n_K = nK`. -/
noncomputable def wRep (ν : ℝ) (k0 r nK : ℕ) [NeZero nK] :
    Rep wS (sides wS.L 1 nK) wR k0 1 27 2 (wGeoF nK) (wCs ν k0) (budgetConsts wβ) 1 where
  hist := wHist k0 r nK
  κK := fun _ _ => 0
  SD := zeroStepData (wGeoF nK) (wCs ν k0) le_rfl rfl _
  KD := zeroKeptData (wGeoF nK) (wCs ν k0) _ _
  B := fun _ _ _ _ _ _ => 0

/-- The family of representations of the witness. -/
noncomputable def wFam (ν : ℝ) (k0 r : ℕ) :
    RepFam wS wR k0 1 27 2 wGeoF (wCs ν k0) (budgetConsts wβ) 1 wC7.m₁ (bgR0 3 3) where
  sf := wSF ν 3
  lf := fun nK _ => wRep ν k0 r nK

/-- The density of the witness, defined by (D1). -/
noncomputable def wRho (ν : ℝ) (k0 r : ℕ) : ∀ (nK : ℕ) [NeZero nK],
    (BlockAt wS (sides wS.L 1 nK) 27 1 1 → EuclideanSpace ℝ (Fin 2)) →
      (GIdx wS (sides wS.L 1 nK) 27 1 2 → ℂ) → ℂ :=
  fun nK _ ψk g => ∑ A ∈ (wRep ν k0 r nK).hist,
    postTerm ((wFam ν k0 r).ctx wM6 le_rfl nK) (wRep ν k0 r nK) A ψk whv g

/-- The pre-`R` density of the witness, defined by (D1) for `IsRep^pre`. -/
noncomputable def wRhoPre (ν : ℝ) (k0 r : ℕ) : ∀ (nK : ℕ) [NeZero nK],
    (BlockAt wS (sides wS.L 1 nK) 27 1 1 → EuclideanSpace ℝ (Fin 2)) →
      (GIdx wS (sides wS.L 1 nK) 27 1 2 → ℂ) → ℂ :=
  fun nK _ ψk g => ∑ A ∈ (wRep ν k0 r nK).hist,
    preTerm ((wFam ν k0 r).ctx wM6 le_rfl nK) (wRep ν k0 r nK) A ψk whv g

/-! ### The clauses -/

section Clauses

variable (ν : ℝ) (k0 r : ℕ)

theorem wSD_zero (nK : ℕ) [NeZero nK] :
    ∀ k a o x hv, ((wRep ν k0 r nK).SD.ker k a).K o x hv = 0 :=
  fun _ _ _ _ _ => rfl

theorem wKD_zero (nK : ℕ) [NeZero nK] :
    ∀ k a ϰ o x hv, ((wRep ν k0 r nK).KD.datum k a ϰ).ker.K o x hv = 0 :=
  fun _ _ _ _ _ _ => rfl

theorem wCoh : Coh wS wR (kZero wS.d wS.L wβ ν) 27 (wCs ν (kZero wS.d wS.L wβ ν))
    (budgetConsts wβ) wP6 wC7 wβ ν 1 (wSF ν 3) where
  M_eq := rfl
  M_pow := wM6
  lam_eq := fun j => setting_lam_eq wβ j
  R_eq := fun _ => rfl
  k0_eq := rfl
  a_free := fun j hj1 hj => by
    obtain rfl : j = 1 := by omega
    exact (compWeight_one (by show 2 ≤ 3; norm_num) _).symm
  beta_cs := fun _ _ => rfl
  beta_P := fun _ _ => rfl
  z_cs := fun _ _ => rfl
  nu_cs := fun _ _ => rfl
  delta_cs := fun _ _ => rfl
  p0_cs := fun _ _ => rfl
  B0_cs := rfl

theorem wField : FieldClauses wS k0 1 (wCs ν k0) (wSF ν 3) whv where
  h_unit := whv_norm
  mu_eq := fun _ _ => rfl
  muAct_eq := fun _ _ => rfl

theorem wForm (nK : ℕ) [NeZero nK] :
    D1Form ((wFam ν k0 r).ctx wM6 le_rfl nK) (wRep ν k0 r nK) whv (wRho ν k0 r nK) := by
  intro ψk g _
  refine ⟨fun A _ => ?_, rfl⟩
  unfold PostConv
  refine gConv_of_K_zero _ _ _ (fun c o x hv => ?_) _ _ _ _
  exact locOp_K_zero (wGeoF nK) (wCs ν k0) (wSD_zero ν k0 r nK) (wKD_zero ν k0 r nK) A.adm
    _ 1 le_rfl c.1 o x hv

theorem wFormPre (nK : ℕ) [NeZero nK] :
    D1PreForm ((wFam ν k0 r).ctx wM6 le_rfl nK) (wRep ν k0 r nK) whv (wRhoPre ν k0 r nK) := by
  intro ψk g _
  refine ⟨fun A _ => ?_, rfl⟩
  unfold PreConv
  refine gConv_of_K_zero _ _ _ (fun c o x hv => ?_) _ _ _ _
  exact preOpTop_K_zero (wGeoF nK) (wCs ν k0) (wSD_zero ν k0 r nK) A 1 le_rfl c o x hv

theorem wPin (top : ℕ) (htop : top ≤ 2) (nK : ℕ) [NeZero nK] : D4Pin top (wRep ν k0 r nK) := by
  intro A _ j hj1 hjt Z hk _
  obtain rfl : j = 1 := by omega
  exact absurd hk.2.2 (not_ripe_one wS_good A.H le_rfl Z)

theorem wOpBound (top : ℕ) (nK : ℕ) [NeZero nK] : D5Bound top le_rfl (wRep ν k0 r nK) := by
  intro A _ j hj
  refine ⟨fun _ c _ => ?_, fun c => ?_⟩
  · exact kerBound_of_K_zero _ _ _
      (locOp_K_zero (wGeoF nK) (wCs ν k0) (wSD_zero ν k0 r nK) (wKD_zero ν k0 r nK) A.adm _ j
        (hj.trans le_rfl) c) _
  · exact kerBound_of_K_zero _ _ _
      (preOpTop_K_zero (wGeoF nK) (wCs ν k0) (wSD_zero ν k0 r nK) A j (hj.trans le_rfl) c) _

theorem wBdry (nK : ℕ) [NeZero nK] (Zof : LabHist wS (sides wS.L 1 nK) wR k0 1 →
    Set (Torus wS.d (sides wS.L 1 nK 1))) (aw μs ε ε1 νs : ℕ → ℝ) (fac rate : ℝ)
    (hfac : 0 < fac) :
    D7Bdry (sides_hnn wS.L 1 nK) le_rfl (wRep ν k0 r nK) Zof aw μs ε ε1 νs fac rate whv where
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

/-- (D7) of the post-`R` class for the zero boundary terms of the witness, for every frame of the
fine size: the bound is `0 < fac · e^{-rate · d7Size}` and the support clause is `0 = 0`. -/
theorem wBdryPost (nK : ℕ) [NeZero nK] {m₀ m₁ : ℕ}
    (Fr : FineSizeFrame wS (sides wS.L 1 nK) 27 1 m₀ m₁)
    (Zof : LabHist wS (sides wS.L 1 nK) wR k0 1 → Set (Torus wS.d (sides wS.L 1 nK 1)))
    (aw μs ε ε1 νs : ℕ → ℝ) (fac rate : ℝ) (hfac : 0 < fac) :
    D7BdryPost Fr (sides_hnn wS.L 1 nK) le_rfl (wRep ν k0 r nK) Zof aw μs ε ε1 νs fac rate
      whv where
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

theorem nine_le_of_mul {ν : ℝ} (hν0 : 0 < ν) (hν : wβ * ν * 27 ≤ 1) : ν * 9 ≤ 7 / 72 := by
  have h := wβ_gt
  nlinarith

/-! ### The witnesses -/

/-- **`IsRep_1` is inhabited**: for every `0 < ν` with `β ν L^d ≤ 1` (so `k₀(β, ν) ≥ 1`). -/
theorem wIsRep (ν : ℝ) (hν0 : 0 < ν) (hν : wβ * ν * 27 ≤ 1) :
    IsRep wS wR (kZero wS.d wS.L wβ ν) 1 27 2 wGeoF (wCs ν (kZero wS.d wS.L wβ ν))
      (budgetConsts wβ) wP6 wC7 wβ ν whv 1 wM6 le_rfl (wFam ν (kZero wS.d wS.L wβ ν) (1 + 1))
      (wRho ν (kZero wS.d wS.L wβ ν) (1 + 1)) where
  coh := wCoh ν
  field := wField ν _
  complete := fun nK _ => wHist_complete _ _ nK
  form := fun nK _ => wForm ν _ _ nK
  sfData := wSF_D2 ν hν0 (nine_le_of_mul hν0 hν) 3 (fun _ => 1) (fun _ => zero_le_one)
  pin := fun nK _ => wPin ν _ _ (1 + 1) le_rfl nK
  opBound := fun nK _ => wOpBound ν _ _ (1 + 1) nK
  budget := fun nK _ => (wRep ν _ (1 + 1) nK).budget_of_LF2 wS_good
    (budgetSetup wβ ν wβ_gt hν0 wβ_spec.2.2) (wPin ν _ _ (1 + 1) le_rfl nK) (by norm_num)
    le_rfl (one_le_kZero hν0 hν) le_rfl (by norm_num)
  bdry := fun nK _ => wBdryPost ν _ _ nK _ _ _ _ _ _ _ _ _ one_pos
  coherent := wSF_D8 ν 3
  coeff := wSF_D9 ν hν0 (nine_le_of_mul hν0 hν) 3 _ (one_le_kZero hν0 hν)

/-- **`IsRep^pre_1` is inhabited.** -/
theorem wIsRepPre (ν : ℝ) (hν0 : 0 < ν) (hν : wβ * ν * 27 ≤ 1) :
    IsRepPre wS wR (kZero wS.d wS.L wβ ν) 1 27 2 wGeoF (wCs ν (kZero wS.d wS.L wβ ν))
      (budgetConsts wβ) wP6 wC7 wβ ν whv 1 wM6 le_rfl (wFam ν (kZero wS.d wS.L wβ ν) 1)
      (wRhoPre ν (kZero wS.d wS.L wβ ν) 1) where
  coh := wCoh ν
  field := wField ν _
  complete := fun nK _ => wHist_complete _ _ nK
  form := fun nK _ => wFormPre ν _ _ nK
  sfData := wSF_D2 ν hν0 (nine_le_of_mul hν0 hν) 3 (preFac (wP6.m₀ + wC7.m₁))
    (fun nn => by unfold preFac; split_ifs <;> norm_num)
  pin := fun nK _ => wPin ν _ _ 1 (by norm_num) nK
  opBound := fun nK _ => wOpBound ν _ _ 1 nK
  budget := fun nK _ => (wRep ν _ 1 nK).budgetPre_of_LF2 wS_good
    (budgetSetup wβ ν wβ_gt hν0 wβ_spec.2.2) (wPin ν _ _ (1 + 1) le_rfl nK) (by norm_num)
    le_rfl (one_le_kZero hν0 hν) le_rfl
  bdry := fun nK _ => wBdry ν _ _ nK _ _ _ _ _ _ _ _ one_pos
  coherent := wSF_D8 ν 3
  coeff := wSF_D9 ν hν0 (nine_le_of_mul hν0 hν) 3 _ (one_le_kZero hν0 hν)

/-- **`IsRep^♭_1` is inhabited**: at `ν₀ = 1/(27β)` (`k₀ = 1`) with `k̂_f = 1`. -/
theorem wIsRepFlat :
    IsRepFlat wS wR (kZero wS.d wS.L wβ wν₀) 1 27 2 wGeoF (wCs wν₀ (kZero wS.d wS.L wβ wν₀))
      (budgetConsts wβ) wP6 wC7 wβ wν₀ whv 1 1 wM6 le_rfl
      (wFam wν₀ (kZero wS.d wS.L wβ wν₀) (1 + 1)) (wRho wν₀ (kZero wS.d wS.L wβ wν₀) (1 + 1)) where
  range := kZero_le_one wν₀_pos (by nlinarith [wν₀_mul])
  coh := wCoh wν₀
  field := wField wν₀ _
  complete := fun nK _ => wHist_complete _ _ nK
  form := fun nK _ => wForm wν₀ _ _ nK
  sfData := (wSF_D2 wν₀ wν₀_pos wν₀_nine 3 (fun _ => 1) (fun _ => zero_le_one)).toFlat
  pin := fun nK _ => wPin wν₀ _ _ (1 + 1) le_rfl nK
  opBound := fun nK _ => wOpBound wν₀ _ _ (1 + 1) nK
  budget := fun nK _ => by
    have hk : kZero wS.d wS.L wβ wν₀ = 1 := kZero_wν₀
    have hl := wS_lam_one_le 1
    have hcH : 0 ≤ wS.cH := wS_ok.cH_nonneg
    refine (wRep wν₀ _ (1 + 1) nK).budgetFlat_of_LF2 wS_good
      (budgetSetup wβ wν₀ wβ_gt wν₀_pos wβ_spec.2.2) (wPin wν₀ _ _ (1 + 1) le_rfl nK)
      (by norm_num) (by rw [hk]) le_rfl ?_ ?_ (by rw [hk]) le_rfl le_rfl (by norm_num)
    · rw [hk]; push_cast; linarith
    · rw [hk]
      have : ((wS.d : ℕ) : ℝ) = 3 := by norm_num [wS, setting, typing, typing0]
      rw [this]
      linarith
  bdry := fun nK _ => wBdryPost wν₀ _ _ nK _ _ _ _ _ _ _ _ _ one_pos
  coherent := wSF_D8 wν₀ 3
  coeff := (wSF_D9 wν₀ wν₀_pos wν₀_nine 3 _ (one_le_kZero wν₀_pos wν₀_mul.le)).toFlat
    (witnessConsts_admissible one_pos)

theorem mul_le_of_nuStar {ν : ℝ} (hν : ν ≤ nuStar wS.d wS.L wβ 1) :
    wβ * ν * 27 ≤ 1 := by
  have hβ := wβ_pos
  have h : nuStar wS.d wS.L wβ 1 = 1 / (27 * wβ) := by
    unfold nuStar
    have : ((wS.L : ℕ) : ℝ) ^ (1 * wS.d) = 27 := by norm_num [wS, setting, typing, typing0]
    rw [this]
    field_simp
  rw [h] at hν
  rw [le_div_iff₀ (by positivity)] at hν
  linarith

theorem wSFLimit (N₁ : ℕ) [NeZero N₁] :
    SFLimit wP6 N₁ (fun ν => (wFam ν (kZero wS.d wS.L wβ ν) (1 + 1)).sf) where
  limE := fun _ _ _ => Eventually.of_forall fun _ _ =>
    ⟨0, by simp only [wFam, wSF, zeroFam, zeroTerms]; exact tendsto_const_nhds⟩
  limM := fun _ _ _ _ _ => Eventually.of_forall fun _ _ =>
    ⟨0, by simp only [wFam, wSF, zeroFam, zeroTerms]; exact tendsto_const_nhds⟩
  limR := fun _ _ _ _ => Eventually.of_forall fun _ _ =>
    ⟨0, by simp only [wFam, wSF]; exact tendsto_const_nhds⟩

theorem wFamCont (r : ℕ) : FamCont wP6 (fun ν => (wFam ν (kZero wS.d wS.L wβ ν) r).sf) where
  runLim := fun j _ =>
    ⟨⟨_, tendsto_const_nhds⟩,
      ⟨0 * 9 ^ j, (((continuous_id.mul continuous_const).tendsto (0 : ℝ)).mono_left
        nhdsWithin_le_nhds)⟩,
      ⟨_, tendsto_const_nhds⟩, ⟨_, tendsto_const_nhds⟩⟩
  vacLim := fun _ => ⟨0, tendsto_const_nhds⟩
  sfLim := fun N₁ _ =>
    { limE := fun _ _ _ => Eventually.of_forall fun _ _ =>
        ⟨0, by simp only [wFam, wSF, zeroFam, zeroTerms]; exact tendsto_const_nhds⟩
      limM := fun _ _ _ _ _ => Eventually.of_forall fun _ _ =>
        ⟨0, by simp only [wFam, wSF, zeroFam, zeroTerms]; exact tendsto_const_nhds⟩
      limR := fun _ _ _ _ => Eventually.of_forall fun _ _ =>
        ⟨0, by simp only [wFam, wSF]; exact tendsto_const_nhds⟩ }

/-- **`IsRepFam_1` is inhabited** (Definition IV.3.1): the family `ν ↦ (wFam ν, wRho ν)`,
`0 < ν ≤ ν_*(1)`, horizon `K(ν) = 1`. -/
theorem wIsRepFam :
    IsRepFam wS wR 27 2 (fun _ => 1) (fun _ => wGeoF) (fun ν => wCs ν (kZero wS.d wS.L wβ ν))
      (fun _ => budgetConsts wβ) wP6 wC7 wβ whv 1 wM6 (fun _ => le_rfl)
      (fun ν => wFam ν (kZero wS.d wS.L wβ ν) (1 + 1))
      (fun ν => wRho ν (kZero wS.d wS.L wβ ν) (1 + 1)) where
  member := fun ν hν0 hν => wIsRep ν hν0 (mul_le_of_nuStar hν)
  cont := wFamCont (1 + 1)

/-- **`IsRepFam^pre_1` is inhabited.** -/
theorem wIsRepFamPre :
    IsRepFamPre wS wR 27 2 (fun _ => 1) (fun _ => wGeoF) (fun ν => wCs ν (kZero wS.d wS.L wβ ν))
      (fun _ => budgetConsts wβ) wP6 wC7 wβ whv 1 wM6 (fun _ => le_rfl)
      (fun ν => wFam ν (kZero wS.d wS.L wβ ν) 1)
      (fun ν => wRhoPre ν (kZero wS.d wS.L wβ ν) 1) where
  member := fun ν hν0 hν => wIsRepPre ν hν0 (mul_le_of_nuStar hν)
  cont := wFamCont 1

end Balaban.LargeField.Def7.Wit

/-! ### `Nonempty` theorems (hard rule 10) -/

namespace Balaban.LargeField.Def7

open Wit Balaban.SmallField Balaban.Background

theorem nonempty_consts7 : Nonempty Consts7 := ⟨wC7⟩

/-- The radius hypothesis of the witness. -/
theorem wRH : RadiusHyp wS.L wS.Rb wS.lam wR where
  mono := fun _ _ h => wS_ok.lam_mono h
  one_le := wS_ok.one_le_lam
  nonneg := fun j => mul_nonneg (by show (0 : ℝ) ≤ 32; norm_num) (sq_nonneg (wS.lam j))
  le := fun _ => le_rfl
  base := by show (4 * ((3 : ℕ) : ℝ) + 20) ≤ 32; norm_num

/-- The steps without large-field cubes on the torus of the witness. -/
noncomputable def wEmptyFlow (k0 nK : ℕ) [NeZero nK] : FlowSteps wS (sides wS.L 1 nK) wR k0 1 where
  ok := wS_ok
  s4 := le_refl _
  s5 := le_refl _
  RH := wRH
  hnn := sides_hnn wS.L 1 nK
  step := fun k => RegionHistory.emptyStep wS (sides wS.L 1 nK) wR k ∅

theorem wEmptyFlow_Zpre (k0 nK : ℕ) [NeZero nK] : ∀ j, (wEmptyFlow k0 nK).Zpre j = ∅
  | 0 => rfl
  | j + 1 => JointWitness.emptyStep_Zpre_empty wS (sides wS.L 1 nK) wR j _ _

/-- The region history without large-field cubes on the torus of the witness. -/
noncomputable def wEmptyHist (k0 nK : ℕ) [NeZero nK] :
    RegionHistory wS (sides wS.L 1 nK) wR k0 1 where
  F := wEmptyFlow k0 nK
  rem := fun _ => ∅
  rem_sub := fun _ => Finset.empty_subset _
  rem_empty := fun _ _ => rfl
  Z_eq := fun k => by
    rw [wEmptyFlow_Zpre]
    simp [wEmptyFlow, RegionHistory.emptyStep]

theorem nonempty_labHist (k0 nK : ℕ) [NeZero nK] :
    Nonempty (LabHist wS (sides wS.L 1 nK) wR k0 1) :=
  ⟨⟨wEmptyHist k0 nK, fun _ c hc => by simp [wEmptyHist] at hc, fun _ _ => 0⟩⟩

theorem nonempty_sfData : Nonempty (SFData 3 3 3 1 2 (bgR0 3 3)) := ⟨wSF wν₀ 3⟩

theorem nonempty_rep : Nonempty (Rep wS (sides wS.L 1 1) wR (kZero wS.d wS.L wβ wν₀) 1 27 2
    (wGeoF 1) (wCs wν₀ (kZero wS.d wS.L wβ wν₀)) (budgetConsts wβ) 1) :=
  ⟨wRep wν₀ _ 2 1⟩

theorem nonempty_repFam : Nonempty (RepFam wS wR (kZero wS.d wS.L wβ wν₀) 1 27 2 wGeoF
    (wCs wν₀ (kZero wS.d wS.L wβ wν₀)) (budgetConsts wβ) 1 wC7.m₁ (bgR0 3 3)) :=
  ⟨wFam wν₀ _ 2⟩

theorem nonempty_sfCtx : Nonempty (SFCtx wS (sides wS.L 1 1) wR 27 1 2 1 wC7.m₁ (bgR0 3 3)) :=
  ⟨(wFam wν₀ (kZero wS.d wS.L wβ wν₀) 2).ctx wM6 le_rfl 1⟩

end Balaban.LargeField.Def7

/-! ### The bundled `Prop`s are inhabited -/

namespace Balaban.LargeField.Def7

open Wit Balaban.SmallField Balaban.SmallField.Def6 Balaban.Background

theorem nonempty_coh : Nonempty (Coh wS wR (kZero wS.d wS.L wβ wν₀) 27
    (wCs wν₀ (kZero wS.d wS.L wβ wν₀)) (budgetConsts wβ) wP6 wC7 wβ wν₀ 1 (wSF wν₀ 3)) :=
  ⟨wCoh wν₀⟩

theorem nonempty_fieldClauses : Nonempty (FieldClauses wS (kZero wS.d wS.L wβ wν₀) 1
    (wCs wν₀ (kZero wS.d wS.L wβ wν₀)) (wSF wν₀ 3) whv) :=
  ⟨wField wν₀ _⟩

theorem nonempty_rTermsH4 : Nonempty (RTermsH4 (ϱ := bgR0 3 3) wP6 wβs (wνs wν₀) witnessa 1
    ((wSF wν₀ 3).Rt 1) (fun _ => 1)) :=
  ⟨wSF_rTerms wν₀ 3 (fun _ => 1) (fun _ => zero_le_one) 1⟩

theorem nonempty_d2SF : Nonempty (D2SF wP6 (wSF wν₀ 3) (fun _ => 1)) :=
  ⟨wSF_D2 wν₀ wν₀_pos wν₀_nine 3 (fun _ => 1) (fun _ => zero_le_one)⟩

theorem nonempty_d7Bdry : Nonempty (D7Bdry (sides_hnn wS.L 1 1) le_rfl
    (wRep wν₀ (kZero wS.d wS.L wβ wν₀) 2 1) (fun A => (A.H.step 1).Z)
    (wFam wν₀ (kZero wS.d wS.L wβ wν₀) 2).weights (wCs wν₀ (kZero wS.d wS.L wβ wν₀)).mu
    (wP6.eps wS.d wS.L) (epsOne wS wP6 wC7) (wCs wν₀ (kZero wS.d wS.L wβ wν₀)).nu wC7.B0 wP6.κ
    whv) :=
  ⟨wBdry wν₀ _ _ 1 _ _ _ _ _ _ _ _ one_pos⟩

theorem nonempty_fineSizeFrame :
    Nonempty (FineSizeFrame wS (sides wS.L 1 1) 27 1 wP6.m₀ wC7.m₁) :=
  ⟨wFrame 1⟩

theorem nonempty_d7BdryPost : Nonempty (D7BdryPost (wFrame 1) (sides_hnn wS.L 1 1) le_rfl
    (wRep wν₀ (kZero wS.d wS.L wβ wν₀) 2 1) (fun A => (A.H.step 1).Z)
    (wFam wν₀ (kZero wS.d wS.L wβ wν₀) 2).weights (wCs wν₀ (kZero wS.d wS.L wβ wν₀)).mu
    (wP6.eps wS.d wS.L) (epsOne wS wP6 wC7) (wCs wν₀ (kZero wS.d wS.L wβ wν₀)).nu wC7.B0 wP6.κ
    whv) :=
  ⟨wBdryPost wν₀ _ _ 1 _ _ _ _ _ _ _ _ _ one_pos⟩

theorem nonempty_d8SF : Nonempty (D8SF wP6.m₀ (wSF wν₀ 3)) := ⟨wSF_D8 wν₀ 3⟩

theorem nonempty_d9Coeff : Nonempty (D9Coeff wP6 1 (wSF wν₀ 3)) :=
  ⟨wSF_D9 wν₀ wν₀_pos wν₀_nine 3 1 le_rfl⟩

theorem nonempty_sfFlat : Nonempty (SFFlat wP6 (wSF wν₀ 3)) :=
  ⟨(wSF_D2 wν₀ wν₀_pos wν₀_nine 3 (fun _ => 1) (fun _ => zero_le_one)).toFlat⟩

theorem nonempty_d9Flat : Nonempty (D9Flat wP6 (wSF wν₀ 3)) :=
  ⟨(wSF_D9 wν₀ wν₀_pos wν₀_nine 3 1 le_rfl).toFlat (witnessConsts_admissible one_pos)⟩

theorem nonempty_sfLimit : Nonempty (SFLimit wP6 1
    (fun ν => (wFam ν (kZero wS.d wS.L wβ ν) (1 + 1)).sf)) :=
  ⟨wSFLimit 1⟩

theorem nonempty_famCont : Nonempty (FamCont wP6
    (fun ν => (wFam ν (kZero wS.d wS.L wβ ν) (1 + 1)).sf)) :=
  ⟨wFamCont (1 + 1)⟩

/-- **`IsRep_k` is inhabited** (hard rule 10). -/
theorem nonempty_isRep : Nonempty (IsRep wS wR (kZero wS.d wS.L wβ wν₀) 1 27 2 wGeoF
    (wCs wν₀ (kZero wS.d wS.L wβ wν₀)) (budgetConsts wβ) wP6 wC7 wβ wν₀ whv 1 wM6 le_rfl
    (wFam wν₀ (kZero wS.d wS.L wβ wν₀) (1 + 1)) (wRho wν₀ (kZero wS.d wS.L wβ wν₀) (1 + 1))) :=
  ⟨wIsRep wν₀ wν₀_pos wν₀_mul.le⟩

/-- **`IsRep^pre_k` is inhabited.** -/
theorem nonempty_isRepPre : Nonempty (IsRepPre wS wR (kZero wS.d wS.L wβ wν₀) 1 27 2 wGeoF
    (wCs wν₀ (kZero wS.d wS.L wβ wν₀)) (budgetConsts wβ) wP6 wC7 wβ wν₀ whv 1 wM6 le_rfl
    (wFam wν₀ (kZero wS.d wS.L wβ wν₀) 1) (wRhoPre wν₀ (kZero wS.d wS.L wβ wν₀) 1)) :=
  ⟨wIsRepPre wν₀ wν₀_pos wν₀_mul.le⟩

/-- **`IsRep^♭_k` is inhabited.** -/
theorem nonempty_isRepFlat : Nonempty (IsRepFlat wS wR (kZero wS.d wS.L wβ wν₀) 1 27 2 wGeoF
    (wCs wν₀ (kZero wS.d wS.L wβ wν₀)) (budgetConsts wβ) wP6 wC7 wβ wν₀ whv 1 1 wM6 le_rfl
    (wFam wν₀ (kZero wS.d wS.L wβ wν₀) (1 + 1)) (wRho wν₀ (kZero wS.d wS.L wβ wν₀) (1 + 1))) :=
  ⟨wIsRepFlat⟩

/-- **`IsRepFam_k` is inhabited.** -/
theorem nonempty_isRepFam : Nonempty (IsRepFam wS wR 27 2 (fun _ => 1) (fun _ => wGeoF)
    (fun ν => wCs ν (kZero wS.d wS.L wβ ν)) (fun _ => budgetConsts wβ) wP6 wC7 wβ whv 1 wM6
    (fun _ => le_rfl) (fun ν => wFam ν (kZero wS.d wS.L wβ ν) (1 + 1))
    (fun ν => wRho ν (kZero wS.d wS.L wβ ν) (1 + 1))) :=
  ⟨wIsRepFam⟩

/-- **`IsRepFam^pre_k` is inhabited.** -/
theorem nonempty_isRepFamPre : Nonempty (IsRepFamPre wS wR 27 2 (fun _ => 1) (fun _ => wGeoF)
    (fun ν => wCs ν (kZero wS.d wS.L wβ ν)) (fun _ => budgetConsts wβ) wP6 wC7 wβ whv 1 wM6
    (fun _ => le_rfl) (fun ν => wFam ν (kZero wS.d wS.L wβ ν) 1)
    (fun ν => wRhoPre ν (kZero wS.d wS.L wβ ν) 1)) :=
  ⟨wIsRepFamPre⟩

/-- The class `𝓡_k(𝖼)` is nonempty. -/
theorem repClass_nonempty : (RepClass wS wR (kZero wS.d wS.L wβ wν₀) 1 27 2 wGeoF
    (wCs wν₀ (kZero wS.d wS.L wβ wν₀)) (budgetConsts wβ) wP6 wC7 wβ wν₀ whv 1 (bgR0 3 3) wM6
    le_rfl).Nonempty :=
  ⟨_, (wIsRep wν₀ wν₀_pos wν₀_mul.le).mem_repClass⟩

end Balaban.LargeField.Def7
