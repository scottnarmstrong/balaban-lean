module

public import Balaban.LargeField.History.T4
public import Balaban.LargeField.History.BookLemmas
public import Balaban.LargeField.Counter.Conditions
public import Balaban.LargeField.Counter.Restart
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Scale facts under the conditions on `λ_*`, and the numerical invariant of a book

`Setting.Good` records `Setting.Ok` together with (Λ0)–(Λ11) at `x₀ = λ_0`; since `λ` is
increasing, the conditions hold at every `λ_j`.  `BookInv k b` is the numerical content of
Lemmas I.4.10 and I.4.13 (a), (f4) for one component at scale `k`.
-/

@[expose] public section

namespace Balaban.LargeField

/-- `Ok` together with the conditions (Λ0)–(Λ11) from `λ_0` on. -/
structure Setting.Good (S : Setting) : Prop where
  ok : S.Ok
  lc : LamStarConditions S.toTyping (S.lam 0)

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

theorem lam_ge (j : ℕ) : S.lam 0 ≤ S.lam j := G.ok.lam_mono (Nat.zero_le j)

theorem n2_lt_nq (j : ℕ) : S.n2 j < S.nq j := by
  have h1 := G.ok.n2_le_bar j
  have h2 := G.lc.l0_c (S.lam j) (G.lam_ge j)
  have h3 := S.lt_nq j
  exact_mod_cast lt_of_le_of_lt (h1.trans h2) h3

theorem n2_le_nq (j : ℕ) : S.n2 j ≤ S.nq j := (G.n2_lt_nq j).le

theorem E_add_one_le_tau (j : ℕ) : S.E j + 1 ≤ S.tau j := by
  have h1 := G.ok.E_le j
  have h2 := G.lc.l0_d (S.lam j) (G.lam_ge j)
  unfold Setting.tau
  linarith

theorem E_add_one_le_g (k : ℕ) : S.E (k + 1) + 1 ≤ S.g k := by
  have h1 := G.ok.E_le (k + 1)
  have h2 := G.lc.l0_e (S.lam (k + 1)) (G.lam_ge (k + 1))
  have h3 := G.ok.lam_succ_le_two k
  have h4 : S.lam (k + 1) / 2 ≤ S.lam k := by linarith
  have h5 : (S.lam (k + 1) / 2) ^ (2 * S.p0) ≤ S.lam k ^ (2 * S.p0) :=
    pow_le_pow_left₀ (by have := G.ok.lam_pos (k + 1); positivity) h4 _
  have hA := G.ok.A3_pos
  unfold Setting.g
  nlinarith

theorem tStar_pre {b : Book} (h : b.st = .pre) : S.tStar b = b.s + S.nq b.s := by
  unfold Setting.tStar
  rw [Book.q_pre h]
  have := G.n2_le_nq b.s
  omega

end Setting.Good

/-- The numerical invariant of the bookkeeping of one component at scale `k`
(Lemmas I.4.10 (a), I.4.13 (f4), and the clock facts of Definition I.4.7). -/
structure BookInv (S : Setting) (k : ℕ) (b : Book) : Prop where
  adm : S.Admissible k b
  len_nonneg : 0 ≤ b.len
  pt_len : b.pt → b.len = 0
  pt_clock : b.pt → b.s ≤ k
  np_clock : ¬ b.pt → b.s = k + max 1 ⌈Real.logb S.L (max b.len 1)⌉₊
  len_nu : (b.IsActive ∨ b.IsPending) → b.len ≤ ((b.nu : ℝ) - 1) * S.D k
  f4 : (b.IsActive ∨ b.IsPending) → S.tStar b < (b.q + 1) + S.nq (b.q + 1)
  tstar_ge : k ≤ S.tStar b

theorem clock_shadow_le {L : ℝ} (hL : 2 ≤ L) {k : ℕ} {len len' : ℝ} (hlen' : len' ≤ len / L)
    (hlt : L < len) :
    k + 1 + max 1 ⌈Real.logb L (max len' 1)⌉₊ ≤ k + max 1 ⌈Real.logb L (max len 1)⌉₊ := by
  have hL1 : 1 < L := by linarith
  have hlen1 : 1 ≤ len := by linarith
  rw [max_eq_left hlen1]
  have hx : 1 < Real.logb L len := by
    have := Real.logb_lt_logb hL1 (by linarith) hlt
    rwa [Real.logb_self_eq_one hL1] at this
  have hdiv1 : 1 ≤ len / L := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hmax : max len' 1 ≤ len / L := max_le hlen' hdiv1
  have hlog : Real.logb L (max len' 1) ≤ Real.logb L len - 1 := by
    have := Real.logb_le_logb_of_le hL1 (lt_of_lt_of_le one_pos (le_max_right _ _)) hmax
    rw [Real.logb_div (by linarith) (by linarith), Real.logb_self_eq_one hL1] at this
    exact this
  have hc1 : ⌈Real.logb L (max len' 1)⌉₊ ≤ ⌈Real.logb L len - 1⌉₊ := Nat.ceil_le_ceil hlog
  have hc2 : ⌈Real.logb L len - 1⌉₊ + 1 = ⌈Real.logb L len⌉₊ := by
    have := Nat.ceil_add_one (R := ℝ) (a := Real.logb L len - 1) (by linarith)
    rw [sub_add_cancel] at this
    exact this.symm
  have hc3 : 1 < ⌈Real.logb L len⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast hx)
  omega

end Balaban.LargeField
