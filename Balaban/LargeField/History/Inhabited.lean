module

public import Balaban.LargeField.History.RegionHistory
public import Balaban.LargeField.Operators.HistGen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The history structures are inhabited

Witnesses that `FlowSteps`, `RegionHistory` and `RegionSeq` (with the finite horizon `K`) are not
vacuous: an explicit admissible typing (`d = 3`, `L = 2`, ...), the scales `n_k = L^(K-k)` and the
steps without large-field cubes (`P = Q = R = S = ∅`), with `Z_k = Z^pre_k` and no removals.
-/

@[expose] public section

namespace Balaban.LargeField

namespace Witness

/-- An explicit admissible typing. -/
noncomputable def typing0 : Typing where
  d := 3
  L := 2
  M := 1
  Rb := 28
  θp := 1
  θm := 1
  α := 1
  p0 := 5
  p2 := 9
  pR := 16
  A2 := 1
  A3 := 1
  A3' := 1
  CR := 0
  Cν := 0
  cv := 1
  cH := 0
  sS := 4
  sP := 5
  c0 := 10

/-- The typing with `C_ν = C_r`. -/
noncomputable def typing : Typing := { typing0 with Cν := typing0.Cr }

theorem typing_ok : typing.Ok where
  three_le_d := le_refl _
  two_le_L := le_refl _
  one_le_M := le_refl _
  two_le_Rb := by show (2 : ℝ) ≤ 28; norm_num
  θm_pos := by show (0 : ℝ) < 1; norm_num
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
        div_nonneg (by show (0 : ℝ) ≤ 1; norm_num) (mul_nonneg (by show (0 : ℝ) ≤ 1; norm_num) hl.le)
      linarith
    have h2 : 0 ≤ typing0.cPrime := by
      unfold Typing.cPrime
      exact mul_nonneg h1 (by show (0 : ℝ) ≤ 1 + 3 * 1; norm_num)
    unfold Typing.Cr
    have : (0 : ℝ) ≤ 2 * typing0.A2 * typing0.cPrime ^ typing0.p2 :=
      mul_nonneg (by show (0 : ℝ) ≤ 2 * 1; norm_num) (pow_nonneg h2 _)
    linarith
  one_le_cv := by show (1 : ℝ) ≤ 1; norm_num
  cH_nonneg := le_refl _
  p2_ge := by decide
  pR_gt := by decide
  p0_gt := by decide
  c0_sS := by show ((4 : ℕ) : ℝ) + 1 ≤ ((10 : ℕ) : ℝ) * (1 - 1 / ((2 : ℕ) : ℝ)); norm_num
  c0_sP := by decide
  Cr_le := le_refl _

/-- The setting: `λ_j = 1 + j`. -/
noncomputable def setting : Setting where
  toTyping := typing
  lam := fun j => 1 + j

theorem setting_ok : setting.Ok where
  toOk := typing_ok
  lam_step := fun j => by
    show (1 : ℝ) ≤ 1 + ((j + 1 : ℕ) : ℝ) - (1 + j) ∧ 1 + ((j + 1 : ℕ) : ℝ) - (1 + j) ≤ 1
    push_cast; constructor <;> linarith
  one_le_lam0 := by show (1 : ℝ) ≤ 1 + ((0 : ℕ) : ℝ); simp
  θp_le_lam0 := by show (1 : ℝ) ≤ 1 + ((0 : ℕ) : ℝ); simp

/-- The torus sides `n_k = L^(K-k)`. -/
noncomputable def sideLen (K k : ℕ) : ℕ := setting.L ^ (K - k)

instance (K : ℕ) : ∀ k, NeZero (sideLen K k) := fun k =>
  ⟨pow_ne_zero _ (by show (2 : ℕ) ≠ 0; norm_num)⟩

/-- The radii `R_k = 0`. -/
def radii : ℕ → ℝ := fun _ => 0

theorem radiusHyp : RadiusHyp setting.L setting.Rb setting.lam radii where
  mono := fun a b hab => by
    show (1 : ℝ) + a ≤ 1 + b
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  one_le := fun j => by
    show (1 : ℝ) ≤ 1 + j
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    linarith
  nonneg := fun _ => le_refl _
  le := fun j => by
    show (0 : ℝ) ≤ 28 * (1 + (j : ℝ)) ^ 2
    positivity
  base := by show (4 * ((2 : ℕ) : ℝ) + 20 : ℝ) ≤ 28; norm_num

theorem sideLen_succ (K : ℕ) {k : ℕ} (hk : k < K) : sideLen K k = setting.L * sideLen K (k + 1) := by
  unfold sideLen
  rw [show K - k = (K - (k + 1)) + 1 by omega, pow_succ]
  ring

/-- The steps without large-field cubes, with `Z_k = Z^pre_k`. -/
noncomputable def regions (k0 K : ℕ) : ∀ k, Set (Torus setting.d (sideLen K k))
  | 0 => ∅
  | k + 1 => (RegionHistory.emptyStep setting (sideLen K) radii k (regions k0 K k)).Zpre
      (setting.omega (k + 1)) (critOpt setting k0 (k + 1))

end Witness

open Witness in
/-- **`FlowSteps` is inhabited** (for every horizon `K` and `k₀`). -/
noncomputable def flowStepsWitness (k0 K : ℕ) : FlowSteps setting (sideLen K) radii k0 K where
  ok := setting_ok
  s4 := le_refl _
  s5 := le_refl _
  RH := radiusHyp
  hnn := fun _ hk => sideLen_succ K hk
  step := fun k => RegionHistory.emptyStep setting (sideLen K) radii k (regions k0 K k)

open Witness in
theorem nonempty_flowSteps (k0 K : ℕ) : Nonempty (FlowSteps setting (sideLen K) radii k0 K) :=
  ⟨flowStepsWitness k0 K⟩

open Witness in
theorem flowStepsWitness_Zpre (k0 K : ℕ) : ∀ k, (flowStepsWitness k0 K).Zpre k = regions k0 K k
  | 0 => rfl
  | k + 1 => by
    show (RegionHistory.emptyStep setting (sideLen K) radii k (regions k0 K k)).Zpre _ _ = _
    rfl

open Witness in
/-- **`RegionHistory` is inhabited**: no removed components. -/
noncomputable def regionHistoryWitness (k0 K : ℕ) : RegionHistory setting (sideLen K) radii k0 K where
  F := flowStepsWitness k0 K
  rem := fun _ => ∅
  rem_sub := fun _ => Finset.empty_subset _
  rem_empty := fun _ _ => rfl
  Z_eq := fun k => by
    rw [flowStepsWitness_Zpre]
    simp [flowStepsWitness, RegionHistory.emptyStep]

open Witness in
theorem nonempty_regionHistory (k0 K : ℕ) :
    Nonempty (RegionHistory setting (sideLen K) radii k0 K) :=
  ⟨regionHistoryWitness k0 K⟩

open Witness in
theorem nonempty_regionSeq (k0 K : ℕ) :
    Nonempty (RegionSeq setting.d setting.L (sideLen K) setting.Rb setting.lam radii
      (critOpt setting k0) K) :=
  ⟨(regionHistoryWitness k0 K).toSeq le_rfl (fun _ => rfl)⟩

end Balaban.LargeField
