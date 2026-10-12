module

public import Balaban.LargeField.Counter.InstantiationFlow
public import Balaban.LargeField.Budget.LemmaB
public import Balaban.LargeField.Counter.LamStar
public import Balaban.LargeField.Base.BaseRecord
public import Balaban.LargeField.History.LocalRegion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The hypotheses of `flow_counter` and `lemmaB` are jointly satisfiable

The witness of `History/Inhabited.lean` satisfies neither `Setting.Good` (`λ₀ = θ₊ = 1`) nor
`BudgetSetup` (`L = 2 > M = 1`).  Here `d = 3`, `L = M = 2`, `θ_± = log 2`, `c_v = 40`,
`λ_j = log (5β/4) + 1 + j log 2` with `β` large (past the threshold of `exists_lamStar`, the
analytic thresholds and `12`), the flow `β_k = β 2^k`, `ν_k = 4^k/10` (`γ = δ = 1`), and the
history without large-field cubes.  `jointWitness : FlowCounterWitness` packages a
`Setting.Good`, a `FlowSeq` matching it, a `RegionHistory` up to `(k_0, k_f)`, a `BudgetSetup` and all
other hypotheses of `RegionHistory.flow_counter`; `FlowCounterWitness.counter` and
`FlowCounterWitness.lemmaB` apply the two theorems.  The components are empty.
-/

@[expose] public section

namespace Balaban.LargeField
namespace JointWitness


theorem openingIn_empty_univ {d n1 : ℕ} (L : ℕ) [NeZero L] (m : ℕ) :
    openingIn L m (∅ : Set (Torus d n1)) Set.univ = Set.univ := by
  ext y
  simp only [Set.mem_univ, iff_true]
  exact ⟨y, mem_lblock_self (Nat.pos_of_ne_zero (NeZero.ne L)) y, Set.subset_univ _, by
    rw [setDist_eq_top_iff.mpr (Or.inr rfl)]; exact le_top⟩

theorem hullRound_empty {d n : ℕ} [NeZero n] (ω b : ℕ) :
    hullRound ω b (∅ : Set (Torus d n)) = ∅ := by
  ext y
  simp only [hullRound, Set.mem_union, Set.mem_empty_iff_false, false_or, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨Y, hY, -⟩
    obtain ⟨x, hx⟩ := comp_nonempty hY
    have := comp_subset hY hx
    simp [mem_finOf] at this
  · intro h; exact h.elim

theorem hullClosure_empty {d n : ℕ} [NeZero n] (ω b : ℕ) :
    hullClosure ω b (∅ : Set (Torus d n)) = ∅ :=
  Function.iterate_fixed (hullRound_empty ω b) _

theorem emptyStep_Zpre_empty (S : Setting) [NeZero S.L] (n : ℕ → ℕ) [∀ k, NeZero (n k)]
    (R : ℕ → ℝ) (j : ℕ) (ω : ℕ) (crit : Option ℕ) :
    (RegionHistory.emptyStep S n R j ∅).Zpre ω crit = ∅ := by
  have hZ0 : (RegionHistory.emptyStep S n R j ∅).Z0 = ∅ := by
    show (opening S.L _ (Region.FZ (Region.OmegaDD S.L (Region.FDD _ ∅ ∅)
      (Region.Omega S.L ∅ (Region.OmegaPrime S.L _ (Region.Uprime S.L (n (j+1)) _ ∅)))) ∅))ᶜ = ∅
    rw [omegaPrime_of_empty]
    unfold Region.Omega Region.FDD Region.OmegaDD Region.FZ
    simp only [nbhd_empty, Set.union_empty]
    rw [openingIn_empty_univ, openingIn_empty_univ]
    simp [nbhd_empty, opening_empty]
  unfold RegionStep.Zpre Region.Zpre
  rw [hZ0]
  cases crit with
  | none => rfl
  | some b => exact hullClosure_empty ω b



/-- The typing of the joint witness. -/
noncomputable def typing0 : Typing where
  d := 3
  L := 2
  M := 2
  Rb := 28
  θp := Real.log 2
  θm := Real.log 2
  α := 1
  p0 := 5
  p2 := 9
  pR := 16
  A2 := 1
  A3 := 1
  A3' := 1
  CR := 0
  Cν := 0
  cv := 40
  cH := 3 * Real.log 2
  sS := 4
  sP := 5
  c0 := 10

noncomputable def typing : Typing := { typing0 with Cν := typing0.Cr }

theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem log_two_lt_one : Real.log 2 < 1 := by
  have := Real.log_two_lt_d9; linarith

theorem typing_ok : typing.Ok where
  three_le_d := le_refl _
  two_le_L := le_refl _
  one_le_M := by show 1 ≤ 2; norm_num
  two_le_Rb := by show (2 : ℝ) ≤ 28; norm_num
  θm_pos := log_two_pos'
  θm_le_θp := le_refl _
  α_pos := by show (0 : ℝ) < 1; norm_num
  A2_pos := by show (0 : ℝ) < 1; norm_num
  A3_pos := by show (0 : ℝ) < 1; norm_num
  A3'_pos := by show (0 : ℝ) < 1; norm_num
  CR_nonneg := le_refl _
  Cν_pos := by
    show 0 < typing0.Cr
    have hl : 0 < typing0.logL := Real.log_pos (by show (1 : ℝ) < ((2 : ℕ) : ℝ); norm_num)
    have h1 : 0 ≤ typing0.cStar := by
      unfold Typing.cStar
      have : (0 : ℝ) ≤ typing0.θp / (typing0.α * typing0.logL) :=
        div_nonneg log_two_pos'.le (mul_nonneg (by show (0 : ℝ) ≤ 1; norm_num) hl.le)
      linarith
    have h2 : 0 ≤ typing0.cPrime := by
      unfold Typing.cPrime
      exact mul_nonneg h1 (by have := log_two_pos'; show (0 : ℝ) ≤ 1 + 3 * Real.log 2; linarith)
    unfold Typing.Cr
    have : (0 : ℝ) ≤ 2 * typing0.A2 * typing0.cPrime ^ typing0.p2 :=
      mul_nonneg (by show (0 : ℝ) ≤ 2 * 1; norm_num) (pow_nonneg h2 _)
    linarith
  one_le_cv := by show (1 : ℝ) ≤ 40; norm_num
  cH_nonneg := by have := log_two_pos'; show (0 : ℝ) ≤ 3 * Real.log 2; linarith
  p2_ge := by decide
  pR_gt := by decide
  p0_gt := by decide
  c0_sS := by show ((4 : ℕ) : ℝ) + 1 ≤ ((10 : ℕ) : ℝ) * (1 - 1 / ((2 : ℕ) : ℝ)); norm_num
  c0_sP := by decide
  Cr_le := le_refl _

/-- The setting `λ_j = log (5β/4) + 1 + j log 2`. -/
noncomputable def setting (β : ℝ) : Setting where
  toTyping := typing
  lam := fun j => Real.log (β * (5 / 4)) + 1 + (j : ℝ) * Real.log 2

theorem setting_lam (β : ℝ) (j : ℕ) :
    (setting β).lam j = Real.log (β * (5 / 4)) + 1 + (j : ℝ) * Real.log 2 := rfl

theorem log_pos_of (β : ℝ) (hβ : 10 < β) : 0 < Real.log (β * (5 / 4)) :=
  Real.log_pos (by linarith)

theorem setting_ok (β : ℝ) (hβ : 10 < β) : (setting β).Ok where
  toOk := typing_ok
  lam_step := fun j => by
    show Real.log 2 ≤ (setting β).lam (j + 1) - (setting β).lam j ∧
      (setting β).lam (j + 1) - (setting β).lam j ≤ Real.log 2
    rw [setting_lam, setting_lam]
    push_cast; constructor <;> linarith
  one_le_lam0 := by
    have := log_pos_of β hβ
    show (1 : ℝ) ≤ Real.log (β * (5 / 4)) + 1 + ((0 : ℕ) : ℝ) * Real.log 2
    simp; linarith
  θp_le_lam0 := by
    have := log_pos_of β hβ
    have := log_two_lt_one
    show Real.log 2 ≤ Real.log (β * (5 / 4)) + 1 + ((0 : ℕ) : ℝ) * Real.log 2
    simp; linarith

theorem LamStarConditions.mono {T : Typing} {x₀ x₁ : ℝ} (h : LamStarConditions T x₀)
    (hx : x₀ ≤ x₁) : LamStarConditions T x₁ where
  one_le := h.one_le.trans hx
  l0_a := fun x hx' => h.l0_a x (hx.trans hx')
  l0_b := fun x hx' => h.l0_b x (hx.trans hx')
  l0_c := fun x hx' => h.l0_c x (hx.trans hx')
  l0_d := fun x hx' => h.l0_d x (hx.trans hx')
  l0_e := fun x hx' => h.l0_e x (hx.trans hx')
  l1_a := fun x hx' => h.l1_a x (hx.trans hx')
  l1_b := fun x hx' => h.l1_b x (hx.trans hx')
  l2 := fun x hx' => h.l2 x (hx.trans hx')
  l3 := fun x hx' => h.l3 x (hx.trans hx')
  l4 := fun x hx' => h.l4 x (hx.trans hx')
  l5_a := fun x hx' => h.l5_a x (hx.trans hx')
  l5_b := fun x hx' => h.l5_b x (hx.trans hx')
  l6 := fun x hx' => h.l6 x (hx.trans hx')
  l7 := fun x hx' => h.l7 x (hx.trans hx')
  l8_a := fun x hx' => h.l8_a x (hx.trans hx')
  l8_b := fun x hx' => h.l8_b x (hx.trans hx')
  l9 := fun x hx' => h.l9 x (hx.trans hx')
  l10 := fun x hx' => h.l10 x (hx.trans hx')
  l11_a := fun x hx' => h.l11_a x (hx.trans hx')
  l11_b := fun x hx' => h.l11_b x (hx.trans hx')
  l11_c := fun x hx' => h.l11_c x (hx.trans hx')
  l11_d := fun x hx' => h.l11_d x (hx.trans hx')

/-- The threshold `x₀` of `exists_lamStar` for the typing. -/
noncomputable def lamStar : ℝ := (exists_lamStar typing typing_ok).choose

theorem lamStar_spec : LamStarConditions typing lamStar :=
  (exists_lamStar typing typing_ok).choose_spec

theorem setting_good (β : ℝ) (hβ : 10 < β) (hx : lamStar ≤ Real.log (β * (5 / 4)) + 1) :
    (setting β).Good where
  ok := setting_ok β hβ
  lc := LamStarConditions.mono lamStar_spec (by
    have : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
    show lamStar ≤ Real.log (β * (5 / 4)) + 1 + ((0 : ℕ) : ℝ) * Real.log 2
    simp; exact hx)

/-! ### The analytic constants -/

def anaK : AnalyticConsts where
  d := 3
  L := 2
  N := 2
  p0 := 5
  A0 := 0
  H0 := 2
  c2 := 0
  c1BG := 1
  c11 := 1
  C3 := 1
  C4 := 1
  deltaSS := 1
  deltaS := 1

/-- The threshold for the analytic conditions. -/
noncomputable def anaThreshold : ℝ := max (3 / (1 - (2 : ℝ) ^ (-(1 / (2 * (5 : ℝ)))))) 4

theorem anaK_at {x : ℝ} (hx : anaThreshold ≤ x) : AnalyticLamAt anaK x := by
  have h1 : 3 / (1 - (2 : ℝ) ^ (-(1 / (2 * (5 : ℝ))))) ≤ x := (le_max_left _ _).trans hx
  have h2 : (4 : ℝ) ≤ x := (le_max_right _ _).trans hx
  have hl := log_two_lt_one
  have hl0 := log_two_pos'
  have hd : deltaBar anaK.A0 anaK.p0 x = 0 := by simp [deltaBar, anaK]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [anaK] using h1
  · simp only [anaK, thetaOf]
    norm_num
    nlinarith
  · simp only [anaK]; linarith
  · rw [hd]; simp [anaK]
  · rw [hd]; simp [anaK]
  · rw [hd]; simp [anaK]


/-! ### The generic empty history -/

section History

variable (S : Setting) [NeZero S.L]

/-- The torus sides `n_k = L^(K-k)`. -/
noncomputable def sideLen (K k : ℕ) : ℕ := S.L ^ (K - k)

instance sideLen_neZero (K k : ℕ) : NeZero (sideLen S K k) :=
  ⟨pow_ne_zero _ (NeZero.ne _)⟩

/-- The radii `R_k = 0`. -/
def radii : ℕ → ℝ := fun _ => 0

omit [NeZero S.L] in
theorem radiusHyp (ok : S.Ok) (hRb : (4 * S.L + 20 : ℝ) ≤ S.Rb) :
    RadiusHyp S.L S.Rb S.lam radii where
  mono := fun _ _ h => ok.lam_mono h
  one_le := ok.one_le_lam
  nonneg := fun _ => le_rfl
  le := fun j => by
    show (0 : ℝ) ≤ S.Rb * S.lam j ^ 2
    exact mul_nonneg (by linarith [ok.two_le_Rb]) (sq_nonneg _)
  base := hRb

/-- The steps without large-field cubes from the empty region. -/
noncomputable def flowSteps (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
    (hRb : (4 * S.L + 20 : ℝ) ≤ S.Rb) (k0 K : ℕ) : FlowSteps S (sideLen S K) radii k0 K where
  ok := ok
  s4 := h4
  s5 := h5
  RH := radiusHyp S ok hRb
  hnn := fun k hk => by
    unfold sideLen
    rw [show K - k = (K - (k + 1)) + 1 by omega, pow_succ]
    ring
  step := fun k => RegionHistory.emptyStep S (sideLen S K) radii k ∅

theorem flowSteps_Zpre_empty (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
    (hRb : (4 * S.L + 20 : ℝ) ≤ S.Rb) (k0 K : ℕ) :
    ∀ k, (flowSteps S ok h4 h5 hRb k0 K).Zpre k = ∅
  | 0 => rfl
  | k + 1 => emptyStep_Zpre_empty S (sideLen S K) radii k _ _

/-- The region history with no large-field cubes and no removed components. -/
noncomputable def regionHistory (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
    (hRb : (4 * S.L + 20 : ℝ) ≤ S.Rb) (k0 K : ℕ) : RegionHistory S (sideLen S K) radii k0 K where
  F := flowSteps S ok h4 h5 hRb k0 K
  rem := fun _ => ∅
  rem_sub := fun _ => Finset.empty_subset _
  rem_empty := fun _ _ => rfl
  Z_eq := fun k => by
    rw [flowSteps_Zpre_empty]
    simp [flowSteps, RegionHistory.emptyStep]

theorem regionHistory_isEmpty_comp (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
    (hRb : (4 * S.L + 20 : ℝ) ≤ S.Rb) (k0 K k : ℕ) :
    IsEmpty ((regionHistory S ok h4 h5 hRb k0 K).Comp k) := by
  refine ⟨fun c => ?_⟩
  obtain ⟨x, hx⟩ := comp_nonempty c.2
  have := comp_subset c.2 hx
  have hz : (regionHistory S ok h4 h5 hRb k0 K).F.Zp k = ∅ := by
    ext y
    simp [FlowSteps.Zp, regionHistory, flowSteps_Zpre_empty]
  rw [hz] at this
  simp at this

end History

/-! ### The flow -/

/-- The flow data of the witness. -/
noncomputable def flow (β : ℝ) (hβ : 10 < β) : FlowSeq where
  d := 3
  L := 2
  β := β
  ν := 1 / 10
  a := 5 / 4
  γ := fun _ => 1
  δ := fun _ => 1
  hd := le_rfl
  hL := le_rfl
  hβ := by linarith
  hν0 := by norm_num
  hν1 := by norm_num
  ha1 := by norm_num
  ha2 := by norm_num
  hγ := fun _ => by norm_num
  hδ := fun _ => by norm_num
  hγ0 := rfl
  hδ0 := rfl

theorem flow_matches (β : ℝ) (hβ : 10 < β) : (flow β hβ).Matches (setting β) where
  d_eq := rfl
  L_eq := rfl
  lam_eq := fun j => by
    rw [setting_lam]
    simp [FlowSeq.lamHat, flow, FlowSeq.e]
  cH_eq := by
    show 3 * Real.log 2 = ((3 : ℕ) + 3 : ℝ) * (((3 : ℕ) - 2 : ℕ) : ℝ) / 2 * Real.log ((2 : ℕ) : ℝ)
    norm_num

theorem flow_one_le_kf (β : ℝ) (hβ : 10 < β) : 1 ≤ (flow β hβ).kf := by
  by_contra h
  have h0 : (flow β hβ).kf = 0 := by omega
  have hk := (flow β hβ).kf_spec
  rw [h0] at hk
  have : (flow β hβ).nu 0 = 1 / 10 := by simp [FlowSeq.nu, flow]
  rw [this] at hk
  have h2 : ((flow β hβ).L : ℝ) = 2 := by simp [flow]
  rw [h2] at hk
  norm_num at hk

theorem flow_hgen (β : ℝ) (hβ : 10 < β) :
    (flow β hβ).beta (flow β hβ).k0 * (flow β hβ).nu (flow β hβ).k0 ≤ 1 →
      2 * ((flow β hβ).L : ℝ) ^ 2 ≤ (flow β hβ).beta (flow β hβ).k0 := by
  intro h
  exfalso
  have h1 := (flow β hβ).betanu_mono (Nat.zero_le (flow β hβ).k0)
  have h2 : (flow β hβ).beta 0 * (flow β hβ).nu 0 = β / 10 := by
    simp [FlowSeq.beta, FlowSeq.nu, flow]; ring
  linarith

theorem flow_hΛ12 (β : ℝ) (hβ : 10 < β) (h12 : 12 ≤ Real.log (β * (5 / 4)) + 1) :
    (((flow β hβ).d : ℝ) + 3) / 2 ≤
      (setting β).lam (flow β hβ).k0 * (1 - 1 / (2 * Real.log (flow β hβ).L)) := by
  have hlam : 12 ≤ (setting β).lam (flow β hβ).k0 := by
    rw [setting_lam]
    have := log_two_pos'
    have : (0 : ℝ) ≤ ((flow β hβ).k0 : ℝ) * Real.log 2 := by positivity
    linarith
  have hd : (((flow β hβ).d : ℝ) + 3) / 2 = 3 := by simp [flow]
  have hL : Real.log ((flow β hβ).L : ℝ) = Real.log 2 := by simp [flow]
  rw [hd, hL]
  have h6 := Real.log_two_gt_d9
  have hc : 1 / 4 ≤ 1 - 1 / (2 * Real.log 2) := by
    have : 1 / (2 * Real.log 2) ≤ 3 / 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  nlinarith

/-! ### The budget -/

/-- The budget constants. -/
noncomputable def budgetConsts (β : ℝ) : BudgetConsts where
  c1 := 0
  c2 := 0
  H0 := 2
  beta := fun k => β * 2 ^ k

noncomputable def budgetSetup (β : ℝ) (hβ : 10 < β) (ha : anaThreshold ≤ Real.log (β * (5 / 4)) + 1) :
    BudgetSetup (setting β) (budgetConsts β) where
  β := β
  ν := 1 / 10
  a := 5 / 4
  ε := 0
  nuRun := fun k => 1 / 10 * 4 ^ k
  K := anaK
  run :=
    { hd := by show 2 ≤ 3; norm_num
      hL := by show 2 ≤ 2; norm_num
      hβ := by linarith
      hν := by norm_num
      ha1 := by norm_num
      ha2 := by norm_num
      hε0 := le_rfl
      hε := by norm_num
      beta_eq := fun k => ⟨1, one_pos, by simp, by
        show β * 2 ^ k = β * ((2 : ℕ) : ℝ) ^ (k * (3 - 2)) * 1
        simp⟩
      nu_eq := fun k => ⟨1, one_pos, by simp, by
        show 1 / 10 * 4 ^ k = 1 / 10 * ((2 : ℕ) : ℝ) ^ (2 * k) * 1
        rw [pow_mul]; norm_num⟩ }
  lam_eq := fun j => by
    rw [setting_lam]
    simp [lamHat, thetaOf, setting, typing, typing0]
  Kd := rfl
  KL := rfl
  Kp0 := rfl
  KH0 := rfl
  Kc2 := rfl
  lam_cond := fun j => anaK_at (by
    rw [setting_lam]
    have := log_two_pos'
    have : (0 : ℝ) ≤ (j : ℝ) * Real.log 2 := by positivity
    linarith)
  H0_nonneg := by show (0 : ℝ) ≤ 2; norm_num
  c1_nonneg := le_rfl
  L_le_M := by show 2 ≤ 2; exact le_rfl
  cv_ge := by
    show ((2 : ℕ) : ℝ) ^ 3 * (2 + 0 + 3) ≤ 40
    norm_num

/-! ### The joint witness -/

instance (β : ℝ) : NeZero (setting β).L := ⟨by show (2 : ℕ) ≠ 0; norm_num⟩

theorem setting_s4 (β : ℝ) : 4 ≤ (setting β).sS := le_refl _
theorem setting_s5 (β : ℝ) : 5 ≤ (setting β).sP := le_refl _
theorem setting_Rb (β : ℝ) : (4 * (setting β).L + 20 : ℝ) ≤ (setting β).Rb := by
  show (4 * ((2 : ℕ) : ℝ) + 20) ≤ 28; norm_num

/-- A large enough `β`. -/
theorem exists_beta : ∃ β : ℝ, 10 < β ∧ lamStar ≤ Real.log (β * (5 / 4)) + 1 ∧
    anaThreshold ≤ Real.log (β * (5 / 4)) + 1 ∧ 12 ≤ Real.log (β * (5 / 4)) + 1 := by
  set Λ : ℝ := max (max lamStar anaThreshold) 12 with hΛ
  have h1 : lamStar ≤ Λ := (le_max_left _ _).trans (le_max_left _ _)
  have h2 : anaThreshold ≤ Λ := (le_max_right _ _).trans (le_max_left _ _)
  have h3 : 12 ≤ Λ := le_max_right _ _
  have hl : Real.log (Real.exp Λ * (5 / 4)) = Λ + Real.log (5 / 4) := by
    rw [Real.log_mul (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
  have hp : 0 < Real.log (5 / 4 : ℝ) := Real.log_pos (by norm_num)
  have he : Λ + 1 ≤ Real.exp Λ := Real.add_one_le_exp Λ
  refine ⟨Real.exp Λ, by linarith, ?_, ?_, ?_⟩ <;> rw [hl] <;> linarith

/-- The data of a satisfying instance of all hypotheses of `RegionHistory.flow_counter` (and of
`lemmaB`, `toLF2HypBudget`); a witness bundle, not a hypothesis. -/
structure FlowCounterWitness where
  S : Setting
  G : S.Good
  F : FlowSeq
  hS : F.Matches S
  n : ℕ → ℕ
  [nz : ∀ k, NeZero (n k)]
  R : ℕ → ℝ
  H : RegionHistory S n R F.k0 F.kf
  hadm : H.Admissible
  hkf : 1 ≤ F.kf
  hΛ12 : ((F.d : ℝ) + 3) / 2 ≤ S.lam F.k0 * (1 - 1 / (2 * Real.log F.L))
  hgen : F.beta F.k0 * F.nu F.k0 ≤ 1 → 2 * (F.L : ℝ) ^ 2 ≤ F.beta F.k0
  P : BudgetConsts
  B : BudgetSetup S P
  Gp : ∀ k, H.Comp k → ℝ
  G' : ∀ k, H.Comp k → ℝ
  budget : ∀ k, k < F.kf → ∀ Z' : H.Comp (k + 1),
      ∑ c ∈ H.parts k Z', G' k c + S.g k * (Z'.1 ∩ H.newCubes (k + 1)).card -
        S.cv * S.lam (k + 1) * Z'.1.card ≤ Gp (k + 1) Z'
  rg_ripe : ∀ k, 1 ≤ k → k ≤ F.k0 → ∀ c : H.Comp k, c.1 ∉ H.rem k → S.Ripe k (H.bk k c) →
      Gp k c - S.CR * S.lam k ^ (2 * S.d + 1) + S.A3' * S.lam k ^ S.pR ≤ G' k c
  rg_nonripe : ∀ k, 1 ≤ k → k ≤ F.k0 → ∀ c : H.Comp k, c.1 ∉ H.rem k →
      ¬ S.Ripe k (H.bk k c) → G' k c = Gp k c
  rg_frozen : ∀ k, F.k0 < k → ∀ c : H.Comp k, G' k c = Gp k c

attribute [instance] FlowCounterWitness.nz

/-- The chosen `β`. -/
noncomputable def jointBeta : ℝ := exists_beta.choose

theorem jointBeta_spec :
    10 < jointBeta ∧ lamStar ≤ Real.log (jointBeta * (5 / 4)) + 1 ∧
    anaThreshold ≤ Real.log (jointBeta * (5 / 4)) + 1 ∧ 12 ≤ Real.log (jointBeta * (5 / 4)) + 1 :=
  exists_beta.choose_spec

theorem jointBeta_gt : 10 < jointBeta := jointBeta_spec.1

/-- **The joint witness**: all hypotheses of `flow_counter` hold simultaneously. -/
noncomputable def jointWitness : FlowCounterWitness :=
  let β := jointBeta
  let hβ : 10 < β := jointBeta_gt
  let ok := setting_ok β hβ
  let F := flow β hβ
  let H := regionHistory (setting β) ok (setting_s4 β) (setting_s5 β) (setting_Rb β) F.k0 F.kf
  let B := budgetSetup β hβ jointBeta_spec.2.2.1
  have hemp : ∀ k, IsEmpty (H.Comp k) :=
    regionHistory_isEmpty_comp (setting β) ok (setting_s4 β) (setting_s5 β) (setting_Rb β) F.k0 F.kf
  { S := setting β
    G := setting_good β hβ jointBeta_spec.2.1
    F := F
    hS := flow_matches β hβ
    n := sideLen (setting β) F.kf
    R := radii
    H := H
    hadm := fun k c hc => absurd hc (by simp [H, regionHistory])
    hkf := flow_one_le_kf β hβ
    hΛ12 := flow_hΛ12 β hβ jointBeta_spec.2.2.2
    hgen := flow_hgen β hβ
    P := budgetConsts β
    B := B
    Gp := H.Gpre (budgetConsts β) (fun _ _ => 0) (fun _ _ => 0)
    G' := H.Gpost (budgetConsts β) (fun _ _ => 0) (fun _ _ => 0)
    budget := H.lemmaB B ok (fun _ _ => 0) (fun _ _ => 0)
    rg_ripe := fun k _ _ c => (hemp k).elim c
    rg_nonripe := fun k _ _ c => (hemp k).elim c
    rg_frozen := fun k _ c => (hemp k).elim c }

namespace FlowCounterWitness

variable (W : FlowCounterWitness)

/-- The hypotheses of `flow_counter` hold for `W`, so its conclusion applies. -/
theorem counter :
    CounterConclusion
      ((W.H.toLF2Hyp W.hadm W.Gp W.G' W.budget W.rg_ripe W.rg_nonripe W.rg_frozen).toCounterHist
        W.G.ok) W.F.kfhat :=
  W.H.flow_counter W.G W.F W.hS W.hadm W.hkf W.hΛ12 W.hgen W.Gp W.G' W.budget W.rg_ripe
    W.rg_nonripe W.rg_frozen

/-- The hypotheses of `lemmaB` hold for `W`. -/
theorem lemmaB (κ logC : ∀ k, W.H.Comp k → ℝ) :
    ∀ k, k < W.F.kf → ∀ Z' : W.H.Comp (k + 1),
      ∑ c ∈ W.H.parts k Z', W.H.Gpost W.P κ logC k c +
          W.S.g k * (Z'.1 ∩ W.H.newCubes (k + 1)).card -
        W.S.cv * W.S.lam (k + 1) * Z'.1.card ≤ W.H.Gpre W.P κ logC (k + 1) Z' :=
  W.H.lemmaB W.B W.G.ok κ logC

end FlowCounterWitness

theorem jointWitness_isEmpty_comp (k : ℕ) : IsEmpty (jointWitness.H.Comp k) :=
  regionHistory_isEmpty_comp (setting jointBeta) (setting_ok jointBeta jointBeta_gt)
    (setting_s4 _) (setting_s5 _) (setting_Rb _) _ _ k

/-- The hypotheses of `toLF2HypBudget` (with `lemmaB` for the budget) hold for the joint
witness, for arbitrary exponents. -/
noncomputable def jointWitness_lf2Hyp (κK δ : ∀ k, jointWitness.H.Comp k → ℝ) :
    LF2Hyp jointWitness.S jointWitness.n jointWitness.F.k0 jointWitness.F.kf :=
  jointWitness.H.toLF2HypBudget jointWitness.B jointWitness.G.ok jointWitness.hadm κK δ
    (fun k _ _ c => (jointWitness_isEmpty_comp k).elim c)
    (fun k _ _ c => (jointWitness_isEmpty_comp k).elim c)
    (fun k _ c => (jointWitness_isEmpty_comp k).elim c)

theorem nonempty_flowCounterWitness : Nonempty FlowCounterWitness := ⟨jointWitness⟩

end JointWitness
end Balaban.LargeField
