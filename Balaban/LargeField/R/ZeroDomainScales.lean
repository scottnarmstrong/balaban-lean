module

public import Balaban.LargeField.History.Scale
public import Balaban.LargeField.Counter.Growth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The late scales `k₂`, `k₃` (Part III, Definition III.3.1 and Lemma III.3.2 (a))

With the a priori radii `R̂_j = R_base λ̂_j²` (version 1.2, D-IV.2; `S.lam` is the a priori sequence),
`lateR S j = [R̂_j]` and
`k₂ = min {j ≤ k : L^{-(k-j)} L M [R̂_j] ≥ 1}`, `k₃ = min {j ≤ k : L^{-(k-j)} L [R̂_j] ≥ 8}`,
written without negative powers: `L^{k-j} ≤ L M [R̂_j]`, resp. `8 L^{k-j} ≤ L [R̂_j]`.

`lateScale_geom` is Lemma III.3.2 (a): for a window with core `q` (`q + n_q(q) ≤ k`) and short-spine
epoch `s` (`s + n_2(s) ≤ k`): `q < k₂`, `s < k₂`, `k₂ ≤ k₃ ≤ k`, the sequence
`j ↦ L^{-(k-j)} L M [R̂_j]` is nondecreasing, and
`L^{-n_2} L M [R̂_{k₂}] < 9/8 L`, `L^{-n_3} L [R̂_{k₃}] < 9 L`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

namespace Setting

variable (S : Setting)

/-- `[R̂_j] = ⌊R_base λ̂_j²⌋`. -/
noncomputable def lateR (j : ℕ) : ℕ := ⌊S.Rb * S.lam j ^ 2⌋₊

/-- `k₂ = min {j ≤ k : L^{-(k-j)} L M [R̂_j] ≥ 1}` (Definition III.3.1). -/
noncomputable def kTwo (k : ℕ) : ℕ :=
  sInf {j : ℕ | j ≤ k ∧ S.L ^ (k - j) ≤ S.L * S.M * S.lateR j}

/-- `k₃ = min {j ≤ k : L^{-(k-j)} L [R̂_j] ≥ 8}` (Definition III.3.1, the threshold `8` of Lemma III.5.0). -/
noncomputable def kThree (k : ℕ) : ℕ :=
  sInf {j : ℕ | j ≤ k ∧ 8 * S.L ^ (k - j) ≤ S.L * S.lateR j}

/-- `n_2 = k - k₂` of Definition III.3.1. -/
noncomputable def lateN2 (k : ℕ) : ℕ := k - S.kTwo k

/-- `n_3 = k - k₃` of Definition III.3.1. -/
noncomputable def lateN3 (k : ℕ) : ℕ := k - S.kThree k

variable {S}

namespace Ok

variable (hS : S.Ok)
include hS

theorem lateR_mono : Monotone S.lateR := by
  intro a b hab
  unfold lateR
  apply Nat.floor_le_floor
  have := hS.lam_mono hab
  have h1 := hS.one_le_lam a
  have h2 := hS.two_le_Rb
  gcongr

theorem two_le_lateR (j : ℕ) : 2 ≤ S.lateR j := by
  unfold lateR
  apply Nat.le_floor
  have := hS.one_le_Rb_lam_sq j
  have h1 := hS.one_le_lam j
  have h2 := hS.two_le_Rb
  push_cast
  nlinarith

theorem lateR_le_crit (j : ℕ) : S.lateR j ≤ S.crit j := by
  have h1 : (S.lateR j : ℝ) ≤ S.Rb * S.lam j ^ 2 := Nat.floor_le (by
    have := hS.one_le_Rb_lam_sq j; linarith)
  have h2 := hS.r_le j
  have h3 : (S.Rb * S.lam j ^ 2 : ℝ) ≤ S.r j := by
    unfold Setting.r; exact Nat.le_ceil _
  have h4 : S.r j ≤ S.rho j := by
    unfold Setting.rho; exact Nat.le_mul_of_pos_left _ (hS.one_le_c0)
  have h5 : S.rho j ≤ S.crit j := by unfold Setting.crit; omega
  have : (S.lateR j : ℝ) ≤ S.crit j := by
    have h4' : (S.r j : ℝ) ≤ S.rho j := by exact_mod_cast h4
    have h5' : (S.rho j : ℝ) ≤ S.crit j := by exact_mod_cast h5
    linarith
  exact_mod_cast this

theorem kTwo_mem (k : ℕ) :
    S.kTwo k ∈ {j : ℕ | j ≤ k ∧ S.L ^ (k - j) ≤ S.L * S.M * S.lateR j} := by
  refine Nat.sInf_mem (s := {j : ℕ | j ≤ k ∧ S.L ^ (k - j) ≤ S.L * S.M * S.lateR j}) ⟨k, le_rfl, ?_⟩
  simp only [Nat.sub_self, pow_zero]
  have h1 := hS.two_le_lateR k
  have h2 := hS.two_le_L
  have h3 := hS.one_le_M
  calc 1 ≤ S.lateR k := by omega
    _ ≤ S.L * S.M * S.lateR k := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))

theorem kTwo_le (k : ℕ) : S.kTwo k ≤ k := (hS.kTwo_mem k).1

theorem kTwo_spec (k : ℕ) : S.L ^ (k - S.kTwo k) ≤ S.L * S.M * S.lateR (S.kTwo k) := (hS.kTwo_mem k).2

/-- The condition defining `k₂` is monotone in `j ≤ k`. -/
theorem cond2_mono {k j j' : ℕ} (hjj : j ≤ j') (hj'k : j' ≤ k)
    (h : S.L ^ (k - j) ≤ S.L * S.M * S.lateR j) : S.L ^ (k - j') ≤ S.L * S.M * S.lateR j' := by
  have hL := hS.two_le_L
  calc S.L ^ (k - j') ≤ S.L ^ (k - j) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ S.L * S.M * S.lateR j := h
    _ ≤ S.L * S.M * S.lateR j' := Nat.mul_le_mul_left _ (hS.lateR_mono hjj)

theorem kTwo_le_iff {k j : ℕ} (hjk : j ≤ k) :
    S.kTwo k ≤ j ↔ S.L ^ (k - j) ≤ S.L * S.M * S.lateR j := by
  constructor
  · intro h
    exact hS.cond2_mono h hjk (hS.kTwo_spec k)
  · intro h
    exact Nat.sInf_le ⟨hjk, h⟩

theorem lt_kTwo_iff {k j : ℕ} (hjk : j ≤ k) :
    j < S.kTwo k ↔ S.L * S.M * S.lateR j < S.L ^ (k - j) := by
  rw [← not_le, hS.kTwo_le_iff hjk, not_le]

theorem kThree_mem {k : ℕ} (h3 : 8 ≤ S.L * S.lateR k) :
    S.kThree k ∈ {j : ℕ | j ≤ k ∧ 8 * S.L ^ (k - j) ≤ S.L * S.lateR j} :=
  Nat.sInf_mem (s := {j : ℕ | j ≤ k ∧ 8 * S.L ^ (k - j) ≤ S.L * S.lateR j}) ⟨k, le_rfl, by simpa using h3⟩

theorem cond3_mono {k j j' : ℕ} (hjj : j ≤ j') (hj'k : j' ≤ k)
    (h : 8 * S.L ^ (k - j) ≤ S.L * S.lateR j) : 8 * S.L ^ (k - j') ≤ S.L * S.lateR j' := by
  have hL := hS.two_le_L
  calc 8 * S.L ^ (k - j') ≤ 8 * S.L ^ (k - j) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    _ ≤ S.L * S.lateR j := h
    _ ≤ S.L * S.lateR j' := Nat.mul_le_mul_left _ (hS.lateR_mono hjj)

theorem kThree_le_iff {k j : ℕ} (h3 : 8 ≤ S.L * S.lateR k) (hjk : j ≤ k) :
    S.kThree k ≤ j ↔ 8 * S.L ^ (k - j) ≤ S.L * S.lateR j := by
  constructor
  · intro h
    exact hS.cond3_mono h hjk (hS.kThree_mem h3).2
  · intro h
    exact Nat.sInf_le ⟨hjk, h⟩

theorem lt_kThree_iff {k j : ℕ} (h3 : 8 ≤ S.L * S.lateR k) (hjk : j ≤ k) :
    j < S.kThree k ↔ S.L * S.lateR j < 8 * S.L ^ (k - j) := by
  rw [← not_le, hS.kThree_le_iff h3 hjk, not_le]

theorem kTwo_le_kThree {k : ℕ} (h3 : 8 ≤ S.L * S.lateR k) : S.kTwo k ≤ S.kThree k := by
  rw [hS.kTwo_le_iff (hS.kThree_mem h3).1]
  have h := (hS.kThree_mem h3).2
  have hM := hS.one_le_M
  have hL := hS.two_le_L
  have hpos : 0 < S.L ^ (k - S.kThree k) := Nat.pow_pos (by omega)
  calc S.L ^ (k - S.kThree k) ≤ 8 * S.L ^ (k - S.kThree k) := by omega
    _ ≤ S.L * S.lateR (S.kThree k) := h
    _ ≤ S.L * S.M * S.lateR (S.kThree k) := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))

/-- The a priori radii grow by at most the factor `9/8` per scale (consequence of (Λ18)). -/
theorem lateR_succ_le (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤
      9 / 8 * (S.Rb * S.lam j ^ 2 - 1)) (j : ℕ) :
    (S.lateR (j + 1) : ℝ) ≤ 9 / 8 * S.lateR j := by
  have hRb : (0 : ℝ) ≤ S.Rb := by linarith [hS.two_le_Rb]
  have h1 : (S.lateR (j + 1) : ℝ) ≤ S.Rb * S.lam (j + 1) ^ 2 := Nat.floor_le (by positivity)
  have h2 := (hS.lam_step j).2
  have h3 : S.Rb * S.lam (j + 1) ^ 2 ≤ S.Rb * (S.lam j + S.θp) ^ 2 := by
    have : S.lam (j + 1) ≤ S.lam j + S.θp := by linarith
    have hl : 0 ≤ S.lam (j + 1) := (hS.lam_pos _).le
    gcongr
  have h4 : S.Rb * (S.lam j + S.θp) ^ 2 ≤ S.Rb * (S.lam j + S.θp + 1) ^ 2 := by
    have hz : 0 ≤ S.lam j + S.θp := by linarith [hS.lam_pos j, hS.θp_pos]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz (by linarith) 2) hRb
  have h5 : S.Rb * S.lam j ^ 2 - 1 ≤ (S.lateR j : ℝ) := by
    have := Nat.lt_floor_add_one (S.Rb * S.lam j ^ 2)
    unfold lateR; linarith
  have h6 := h18 j
  nlinarith

end Ok

namespace Good

variable (G : S.Good)
include G

/-- **Lemma III.3.2 (a)** (late scales).  For a window with core `q` (`q + n_q(q) ≤ k`) and short-spine
epoch `s` (`s + n_2(s) ≤ k`), under the standing condition (Λ18) on the a priori radii and
`8 ≤ L [R̂_k]`: `q < k₂`, `s < k₂`, `k₂ ≤ k₃ ≤ k`, the sequence `L^{-(k-j)} L M [R̂_j]` is nondecreasing and
`L^{-n_2} L M [R̂_{k₂}] < 9/8 L`, `L^{-n_3} L [R̂_{k₃}] < 9 L`. -/
theorem lateScale_geom
    (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
    {k q s : ℕ} (hq : q + S.nq q ≤ k) (hs : s + S.n2 s ≤ k) (h3 : 8 ≤ S.L * S.lateR k) :
    (∀ j j' : ℕ, j ≤ j' → j' ≤ k →
      ((S.L * S.M * S.lateR j : ℕ) : ℝ) / (S.L : ℝ) ^ (k - j) ≤
        ((S.L * S.M * S.lateR j' : ℕ) : ℝ) / (S.L : ℝ) ^ (k - j')) ∧
    q < S.kTwo k ∧ s < S.kTwo k ∧ S.kTwo k ≤ S.kThree k ∧ S.kThree k ≤ k ∧
    ((S.L * S.M * S.lateR (S.kTwo k) : ℕ) : ℝ) < 9 / 8 * S.L * (S.L : ℝ) ^ S.lateN2 k ∧
    ((S.L * S.lateR (S.kThree k) : ℕ) : ℝ) < 9 * S.L * (S.L : ℝ) ^ S.lateN3 k := by
  have ok := G.ok
  have hL := ok.two_le_L
  have hLr : (2 : ℝ) ≤ S.L := by exact_mod_cast hL
  -- `q`, `s` below `k₂`
  have hqk : q ≤ k := by omega
  have hsk : s ≤ k := by omega
  have key : ∀ j n, j + n ≤ k → S.n2 j ≤ n → j < S.kTwo k := by
    intro j n hjn hn
    rw [ok.lt_kTwo_iff (by omega)]
    calc S.L * S.M * S.lateR j ≤ S.L * S.M * S.crit j :=
          Nat.mul_le_mul_left _ (ok.lateR_le_crit j)
      _ < S.L ^ S.n2 j := ok.lt_pow_n2 j
      _ ≤ S.L ^ (k - j) := Nat.pow_le_pow_right (by omega) (by omega)
  have hq2 : q < S.kTwo k := key q (S.nq q) hq (G.n2_le_nq q)
  have hs2 : s < S.kTwo k := key s (S.n2 s) hs le_rfl
  have h23 := ok.kTwo_le_kThree h3
  have h3k := (ok.kThree_mem h3).1
  have hk2pos : 1 ≤ S.kTwo k := by omega
  refine ⟨?_, hq2, hs2, h23, h3k, ?_, ?_⟩
  · intro j j' hjj hj'k
    have hpos : (0 : ℝ) < (S.L : ℝ) ^ (k - j') := by positivity
    have hle : (S.L : ℝ) ^ (k - j') ≤ (S.L : ℝ) ^ (k - j) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hm : ((S.L * S.M * S.lateR j : ℕ) : ℝ) ≤ ((S.L * S.M * S.lateR j' : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left _ (ok.lateR_mono hjj)
    exact div_le_div₀ (by positivity) hm hpos hle
  · -- `k₂`
    have hk2 := ok.kTwo_le k
    have hmin := (ok.lt_kTwo_iff (k := k) (j := S.kTwo k - 1) (by omega)).mp (by omega)
    have hstep := ok.lateR_succ_le h18 (S.kTwo k - 1)
    rw [show S.kTwo k - 1 + 1 = S.kTwo k by omega] at hstep
    have e : k - (S.kTwo k - 1) = S.lateN2 k + 1 := by unfold lateN2; omega
    rw [e] at hmin
    have hmin' : ((S.L * S.M * S.lateR (S.kTwo k - 1) : ℕ) : ℝ) < ((S.L ^ (S.lateN2 k + 1) : ℕ) : ℝ) := by
      exact_mod_cast hmin
    push_cast at hmin' ⊢
    have hpos : (0 : ℝ) < S.L * S.M := by
      have : (1 : ℝ) ≤ S.M := by exact_mod_cast ok.one_le_M
      positivity
    calc (S.L : ℝ) * S.M * S.lateR (S.kTwo k) ≤ S.L * S.M * (9 / 8 * S.lateR (S.kTwo k - 1)) :=
          mul_le_mul_of_nonneg_left hstep hpos.le
      _ = 9 / 8 * ((S.L : ℝ) * S.M * S.lateR (S.kTwo k - 1)) := by ring
      _ < 9 / 8 * (S.L : ℝ) ^ (S.lateN2 k + 1) := by linarith
      _ = _ := by ring
  · -- `k₃`
    have hk3 := h3k
    have hk3pos : 1 ≤ S.kThree k := by omega
    have hmin := (ok.lt_kThree_iff h3 (k := k) (j := S.kThree k - 1) (by omega)).mp (by omega)
    have hstep := ok.lateR_succ_le h18 (S.kThree k - 1)
    rw [show S.kThree k - 1 + 1 = S.kThree k by omega] at hstep
    have e : k - (S.kThree k - 1) = S.lateN3 k + 1 := by unfold lateN3; omega
    rw [e] at hmin
    have hmin' : ((S.L * S.lateR (S.kThree k - 1) : ℕ) : ℝ) < ((8 * S.L ^ (S.lateN3 k + 1) : ℕ) : ℝ) := by
      exact_mod_cast hmin
    push_cast at hmin' ⊢
    have hpos : (0 : ℝ) < S.L := by linarith
    calc (S.L : ℝ) * S.lateR (S.kThree k) ≤ S.L * (9 / 8 * S.lateR (S.kThree k - 1)) :=
          mul_le_mul_of_nonneg_left hstep hpos.le
      _ = 9 / 8 * ((S.L : ℝ) * S.lateR (S.kThree k - 1)) := by ring
      _ < 9 / 8 * (8 * (S.L : ℝ) ^ (S.lateN3 k + 1)) := by linarith
      _ = _ := by ring

/-- **Lemma III.5.0 (c), second part**: `L^{-n_3} < 9 / [R̂_{k₃}]`. -/
theorem inv_pow_lateN3_lt
    (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
    {k q s : ℕ} (hq : q + S.nq q ≤ k) (hs : s + S.n2 s ≤ k) (h3 : 8 ≤ S.L * S.lateR k) :
    ((S.L : ℝ) ^ S.lateN3 k)⁻¹ < 9 / (S.lateR (S.kThree k) : ℝ) := by
  have ok := G.ok
  obtain ⟨-, -, -, -, -, -, h⟩ := G.lateScale_geom h18 hq hs h3
  have hL : (0 : ℝ) < S.L := by have := ok.two_le_L; exact_mod_cast (by omega : 0 < S.L)
  have hR : (0 : ℝ) < S.lateR (S.kThree k) := by
    have := ok.two_le_lateR (S.kThree k); exact_mod_cast (by omega : 0 < S.lateR (S.kThree k))
  have hp : (0 : ℝ) < (S.L : ℝ) ^ S.lateN3 k := by positivity
  push_cast at h
  have h2 : (S.lateR (S.kThree k) : ℝ) < 9 * (S.L : ℝ) ^ S.lateN3 k := by
    by_contra hcon
    push Not at hcon
    nlinarith
  rw [inv_lt_comm₀ hp (by positivity), inv_div]
  linarith

end Good

end Setting

end Balaban.LargeField
