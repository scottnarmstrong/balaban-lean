module

public import Balaban.LargeField.Counter.LogAux
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Pure shadows, telescoping of `τ + W`, and overflow (Part I, §I.5.4)
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

/-- Telescoping: `τ_b + W_μ(b) ≤ τ_a + W_μ(a) + (b - a)₊ Ā(λ_b)` for `μ ≤ a`. -/
theorem telescope {μ a : ℕ} (ha : μ ≤ a) (b : ℕ) :
    S.tau b + S.W μ b ≤ S.tau a + S.W μ a + ((b - a : ℕ) : ℝ) * S.Abar (S.lam b) := by
  have hA0 : ∀ j, 0 ≤ S.Abar (S.lam j) := fun j => by
    have := G.ok.A2_pos; have := G.ok.θp_pos; have := G.ok.Cw_nonneg
    have := (G.ok.lam_pos j).le
    unfold Typing.Abar; positivity
  rcases le_total b a with hba | hab
  · have h1 := G.ok.tau_mono hba
    have h2 := G.ok.W_mono_right μ hba
    have : b - a = 0 := by omega
    rw [this]; simp
    linarith
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    induction d with
    | zero => simp
    | succ d ih =>
      have ih' := ih (Nat.le_add_right _ _)
      have h1 := G.ok.A_le (a + d)
      have h2 : S.W μ (a + d + 1) = S.W μ (a + d) + S.w (a + d + 1) := by
        unfold Setting.W
        exact Finset.sum_Icc_succ_top (by omega) _
      have h3 : S.Abar (S.lam (a + d)) ≤ S.Abar (S.lam (a + d + 1)) :=
        G.ok.Abar_mono (G.ok.lam_pos _).le (G.ok.lam_mono (Nat.le_succ _))
      have h4 : (a + (d + 1) - a : ℕ) = d + 1 := by omega
      have h5 : (a + d - a : ℕ) = d := by omega
      rw [h5] at ih'
      rw [h4]
      have e : a + (d + 1) = a + d + 1 := by omega
      rw [e]
      push_cast
      have h6 : (d : ℝ) * S.Abar (S.lam (a + d)) ≤ d * S.Abar (S.lam (a + d + 1)) := by
        gcongr
      nlinarith

/-- Pure shadow: (B.7). -/
theorem case_shadow {k : ℕ} {ι : Type*} {P : Finset ι} {f : ι → Book} {r : ℕ} {b' : Book} {i : ι}
    (hparts : P = {i}) (hr : r = 0) (hle : S.tStar b' ≤ S.tStar (f i))
    (hnu : b'.nu = (f i).nu) (hbank : S.bank b' = S.bank (f i))
    (hlen0 : 0 ≤ (f i).len) : S.B7 k P f r b' := by
  subst hparts; subst hr
  unfold Setting.B7
  simp only [Finset.card_singleton, Finset.sum_singleton]
  have h1 := G.ok.tau_mono hle
  have h2 := G.ok.W_mono_right (k + 1) hle
  have : 0 ≤ S.v (k + 1) / S.L * (f i).len := by
    have := G.ok.v_nonneg (k + 1)
    have := G.ok.cast_L_ge
    positivity
  rw [hnu, hbank]
  simp
  linarith

/-- Case 2c: overflow ((T5)). -/
theorem case_overflow {k : ℕ} {ι : Type*} {P : Finset ι} {f : ι → Book} {b' : Book}
    (hinv : ∀ i ∈ P, BookInv S k (f i)) (hpost : ∀ i ∈ P, k < S.tStar (f i))
    (hact : ∀ i ∈ P, (f i).IsActive ∨ (f i).IsPending) (hcard : 2 ≤ P.card)
    (hcap : S.numax (k + 1) < ∑ i ∈ P, (f i).nu) (hf : RestartFacts S k b')
    (hlen : b'.len ≤ ∑ i ∈ P, (f i).len / S.L + (((P.card + 0 : ℕ) : ℝ) - 1) * S.D (k + 1)) :
    S.B7 k P f 0 b' := by
  have hΦ := (G.restart_Phi hf).2.2
  obtain ⟨-, -, -, hnu, hbank⟩ := hf
  have hsum := G.sum_lower (μ := k + 1) (P := P) (f := f) (fun i hi => hpost i hi)
  have hlenν := G.merge_len_bound hinv hact hlen
  have hν : ∀ i ∈ P, 1 ≤ (f i).nu := by
    intro i hi
    rcases hact i hi with ⟨q, ν, M, h⟩ | ⟨q, ν, h⟩
    · have := (hinv i hi).adm; rw [S.adm_active h] at this; rw [Book.nu_active h]; exact this.2.1
    · have := (hinv i hi).adm; rw [S.adm_pending h] at this; rw [Book.nu_pending h]
      exact this.2.2.1
  have hlenP : ∀ i ∈ P, 0 ≤ (f i).len := fun i hi => (hinv i hi).len_nonneg
  have hsumν : ((∑ i ∈ P, (f i).nu : ℕ) : ℝ) = ∑ i ∈ P, ((f i).nu : ℝ) := by push_cast; rfl
  have hA : 0 ≤ S.v (k + 1) / S.L * ∑ i ∈ P, (f i).len := by
    have := G.ok.v_nonneg (k + 1)
    have : 0 ≤ ∑ i ∈ P, (f i).len := Finset.sum_nonneg hlenP
    have := G.ok.cast_L_ge
    positivity
  -- the sum of the pieces is large
  have hmain : S.tau (S.tStar b') + S.W (k + 1) (S.tStar b') + 1 ≤ ∑ i ∈ P, ((f i).nu : ℝ) := by
    set Λ := Real.logb S.L (max b'.len 1) with hΛ
    have hν' : (S.numax (k + 1) : ℝ) + 1 ≤ ∑ i ∈ P, ((f i).nu : ℝ) := by
      rw [← hsumν]; exact_mod_cast hcap
    by_cases hΛl : Λ ≤ S.lam (k + 1)
    · rw [max_eq_left hΛl] at hΦ
      have h9 := G.lc.l9 (S.lam (k + 1)) (G.lam_ge _)
      have : S.Cν * S.lam (k + 1) ^ S.p2 ≤ S.numax (k + 1) := by
        unfold Setting.numax; exact Nat.le_ceil _
      linarith
    · have hbig := not_le.mp hΛl
      rw [max_eq_right hbig.le] at hΦ
      have hL := G.ok.cast_L_ge
      have hl1 := G.ok.one_le_lam (k + 1)
      have hΛ1 : 1 < Λ := lt_of_le_of_lt hl1 hbig
      have hpow := G.rpow_logb_max b'.len
      rw [← hΛ] at hpow
      have hPw : 1 < (S.L : ℝ) ^ Λ := Real.one_lt_rpow (by linarith) (by linarith)
      have hlen1 : (S.L : ℝ) ^ Λ ≤ ((∑ i ∈ P, (f i).nu : ℕ) : ℝ) * S.D (k + 1) := by
        rw [hpow]
        have hP1 : (1 : ℝ) < max b'.len 1 := by rw [← hpow]; exact hPw
        rcases le_total b'.len 1 with h | h
        · rw [max_eq_right h] at hP1; exact absurd hP1 (lt_irrefl _)
        · rw [max_eq_left h]
          refine hlenν.trans ?_
          have := S.D_nonneg (k + 1)
          nlinarith
      have hΛx : S.lam 0 ≤ Λ := (G.lam_ge (k + 1)).trans hbig.le
      have h4 := G.lc.l4 Λ hΛx
      have hB : 0 < S.Dbar Λ := lt_of_lt_of_le one_pos (G.ok.one_le_Dbar Λ)
      have hDB : S.D (k + 1) ≤ S.Dbar Λ :=
        (G.ok.D_le_bar (k + 1)).trans (G.ok.Dbar_mono (G.ok.lam_pos _).le hbig.le)
      have h5 : (S.L : ℝ) ^ Λ ≤ ((∑ i ∈ P, (f i).nu : ℕ) : ℝ) * S.Dbar Λ :=
        hlen1.trans (by gcongr)
      have h6 : (S.L : ℝ) ^ Λ / (2 * S.Dbar Λ) ≤ ((∑ i ∈ P, (f i).nu : ℕ) : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [show (0 : ℝ) ≤ ((∑ i ∈ P, (f i).nu : ℕ) : ℝ) from Nat.cast_nonneg _]
      rw [hsumν] at h6
      linarith
  unfold Setting.B7
  rw [hnu, hbank]
  have hE : ∀ x, 0 ≤ S.E x := G.ok.E_nonneg
  have hτE := G.E_add_one_le_tau (k + 1)
  have hgm : (0:ℝ) ≤ S.g k * (0:ℕ) := by simp
  have hm : (P.card : ℝ) - 1 ≥ 1 := by
    have : (2 : ℝ) ≤ P.card := by exact_mod_cast hcard
    linarith
  have hEτ : ((P.card : ℝ) - 1) * S.E (k + 1) ≤ ((P.card : ℝ) - 1) * S.tau (k + 1) := by
    gcongr; linarith
  have hsum2 : ∑ i ∈ P, (S.tau (S.tStar (f i)) + S.W (k + 1) (S.tStar (f i)) + (f i).nu +
      S.bank (f i)) ≥ (P.card : ℝ) * S.tau (k + 1) + ∑ i ∈ P, ((f i).nu : ℝ) := by
    have : ∑ i ∈ P, (S.tau (k + 1) + ((f i).nu : ℝ)) ≤ ∑ i ∈ P, (S.tau (S.tStar (f i)) +
        S.W (k + 1) (S.tStar (f i)) + (f i).nu + S.bank (f i)) := by
      apply Finset.sum_le_sum; intro i hi
      have h1 := G.ok.tau_mono (show k + 1 ≤ S.tStar (f i) from hpost i hi)
      have h2 := G.ok.W_nonneg (k + 1) (S.tStar (f i))
      have h4 := G.bank_nonneg (f i)
      linarith
    rw [Finset.sum_add_distrib] at this
    simpa using this
  have htau0 : 0 ≤ S.tau (k + 1) := G.ok.tau_nonneg _
  have hmτ : ((P.card : ℝ) - 1) * S.tau (k + 1) ≤ P.card * S.tau (k + 1) := by nlinarith
  push_cast
  simp only [add_zero, mul_zero]
  linarith [hmain, hsum2, hEτ, hA]

end Setting.Good

end Balaban.LargeField
