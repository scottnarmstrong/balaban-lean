module

public import Balaban.LargeField.Counter.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Growth facts (Part I, Lemma I.5.2 (F1)–(F5))

Window length `n_q` and its increments, the sequences `v, w, σ, τ, E`, the recursion of the
reserve coefficient `σ`, and the comparison of every derived quantity with its auxiliary function
of `λ_j`.
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting

variable {S : Setting}

theorem lt_nq (j : ℕ) : S.lam j / (S.α * S.logL) < S.nq j := by
  unfold Setting.nq
  push_cast
  exact Nat.lt_floor_add_one _

theorem one_le_nq (j : ℕ) : 1 ≤ S.nq j := Nat.le_add_left 1 _

theorem n2_le_of {j n : ℕ} (h : S.L * S.M * S.crit j < S.L ^ n) : S.n2 j ≤ n := by
  unfold Setting.n2
  exact Nat.sInf_le h

end Setting

namespace Setting.Ok

variable {S : Setting} (ok : S.Ok)

include ok

/-! ### (F1): the window length -/

theorem αlogL_pos : 0 < S.α * S.logL := mul_pos ok.α_pos ok.logL_pos

theorem nq_le (j : ℕ) : (S.nq j : ℝ) ≤ S.lam j / (S.α * S.logL) + 1 := by
  unfold Setting.nq
  push_cast
  have : 0 ≤ S.lam j / (S.α * S.logL) := div_nonneg (ok.lam_pos j).le ok.αlogL_pos.le
  linarith [Nat.floor_le this]

theorem nq_mono : Monotone S.nq := by
  intro a b hab
  unfold Setting.nq
  have := Nat.floor_le_floor (div_le_div_of_nonneg_right (ok.lam_mono hab) ok.αlogL_pos.le)
  omega

theorem nq_add_le (a x : ℕ) :
    (S.nq (a + x) : ℝ) ≤ S.nq a + S.θp * x / (S.α * S.logL) + 1 := by
  have h1 := ok.nq_le (a + x)
  have h2 := S.lt_nq a
  have h3 := ok.lam_add_le a x
  have h4 : S.lam (a + x) / (S.α * S.logL) ≤ (S.lam a + x * S.θp) / (S.α * S.logL) :=
    div_le_div_of_nonneg_right h3 ok.αlogL_pos.le
  have h5 : (S.lam a + x * S.θp) / (S.α * S.logL) =
      S.lam a / (S.α * S.logL) + S.θp * x / (S.α * S.logL) := by
    field_simp
  linarith

theorem lam_add_floor (j : ℕ) :
    S.lam (j + ⌊S.lam j / (S.α * S.logL)⌋₊) ≤ S.cStar * S.lam j := by
  have h1 := ok.lam_add_le j ⌊S.lam j / (S.α * S.logL)⌋₊
  have h0 : 0 ≤ S.lam j / (S.α * S.logL) := div_nonneg (ok.lam_pos j).le ok.αlogL_pos.le
  have h2 := Nat.floor_le h0
  have h3 : (⌊S.lam j / (S.α * S.logL)⌋₊ : ℝ) * S.θp ≤ S.lam j / (S.α * S.logL) * S.θp :=
    mul_le_mul_of_nonneg_right h2 ok.θp_pos.le
  have h4 : S.cStar * S.lam j = S.lam j + S.lam j / (S.α * S.logL) * S.θp := by
    unfold Typing.cStar
    field_simp
  linarith

/-- `λ_{j + n_q(j) - 1} ≤ c_* λ_j`. -/
theorem lam_add_nq_sub_one (j : ℕ) : S.lam (j + (S.nq j - 1)) ≤ S.cStar * S.lam j := by
  have : S.nq j - 1 = ⌊S.lam j / (S.α * S.logL)⌋₊ := by
    unfold Setting.nq; omega
  rw [this]
  exact ok.lam_add_floor j

/-- `λ_{j + n_q(j)} ≤ c_* λ_j + θ₊` (F1). -/
theorem lam_add_nq (j : ℕ) : S.lam (j + S.nq j) ≤ S.cStar * S.lam j + S.θp := by
  have h := ok.lam_add_floor j
  have h2 := (ok.lam_step (j + ⌊S.lam j / (S.α * S.logL)⌋₊)).2
  have : j + S.nq j = j + ⌊S.lam j / (S.α * S.logL)⌋₊ + 1 := by
    unfold Setting.nq; omega
  rw [this]
  linarith

theorem lam_add_nq_le (j : ℕ) : S.lam (j + S.nq j) ≤ S.cDPrime * S.lam j := by
  have h := ok.lam_add_nq j
  have h1 := ok.θp_le_lam j
  have h2 : S.θp ≤ S.θp * S.lam j := by
    have := ok.one_le_lam j
    nlinarith [ok.θp_pos]
  unfold Typing.cDPrime
  nlinarith

theorem add_nq_strictMono : StrictMono (fun c => c + S.nq c) := by
  intro a b hab
  have := ok.nq_mono (le_of_lt hab)
  simp only
  omega

/-! ### the smallness length `n_2` -/

theorem exists_pow_gt (j : ℕ) : S.L * S.M * S.crit j < S.L ^ (S.L * S.M * S.crit j) :=
  Nat.lt_pow_self (by have := ok.two_le_L; omega)

theorem lt_pow_n2 (j : ℕ) : S.L * S.M * S.crit j < S.L ^ S.n2 j := by
  unfold Setting.n2
  exact Nat.sInf_mem (s := {n : ℕ | S.L * S.M * S.crit j < S.L ^ n}) ⟨_, ok.exists_pow_gt j⟩

theorem n2_mono : Monotone S.n2 := by
  intro a b hab
  apply S.n2_le_of (j := a)
  have h1 := ok.lt_pow_n2 b
  have h2 := ok.crit_mono hab
  have h3 : S.L * S.M * S.crit a ≤ S.L * S.M * S.crit b := Nat.mul_le_mul_left _ h2
  omega

end Setting.Ok

end Balaban.LargeField
