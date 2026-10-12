module

public import Balaban.LargeField.Counter.CaseMerge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Case 2b (continued): (B.7) for a merge with a `Pre` part
-/

@[expose] public section

namespace Balaban.LargeField

theorem sum_split {ι : Type*} {P : Finset ι} {h : ι → ℝ} {c : ℝ} {i0 : ι} (hi0 : i0 ∈ P)
    (hc : ∀ j ∈ P, c ≤ h j) : h i0 + ((P.card : ℝ) - 1) * c ≤ ∑ j ∈ P, h j := by
  classical
  have h1 := Finset.add_sum_erase P h hi0
  have h2 : (P.erase i0).card • c ≤ ∑ j ∈ P.erase i0, h j :=
    Finset.card_nsmul_le_sum _ _ _ (fun j hj => hc j (Finset.mem_of_mem_erase hj))
  rw [Finset.card_erase_of_mem hi0] at h2
  have hpos : 1 ≤ P.card := Finset.card_pos.mpr ⟨i0, hi0⟩
  rw [nsmul_eq_mul, Nat.cast_sub hpos] at h2
  simp at h2
  linarith

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

/-- (B.7) for a merge with a `Pre` part when the new spine is short. -/
theorem mergePre_small {k : ℕ} {ι : Type*} {P : Finset ι} {f : ι → Book} {b' : Book} {i0 i1 p : ι}
    (hinv : ∀ i ∈ P, BookInv S k (f i)) (hpost : ∀ i ∈ P, k < S.tStar (f i))
    (hcard : 2 ≤ P.card) (hp : p ∈ P) (hppre : (f p).st = .pre) (hi0 : i0 ∈ P)
    (hmax0 : ∀ j ∈ P, S.tStar (f j) ≤ S.tStar (f i0))
    (hi1 : i1 ∈ P) (hmax1 : ∀ j ∈ P, (f j).len ≤ (f i1).len)
    (hf : RestartFacts S k b')
    (hlen : b'.len ≤ ∑ i ∈ P, (f i).len / S.L + (((P.card + 0 : ℕ) : ℝ) - 1) * S.D (k + 1))
    (hΛ : Real.logb S.L (max b'.len 1) ≤ S.lam (k + 1)) :
    S.B7 k P f 0 b' := by
  have hdelta := G.delta_pre hinv hcard hp hppre hmax0 hi1 hmax1 hf hlen
  obtain ⟨hlam, -, hΦ⟩ := G.restart_Phi hf
  obtain ⟨-, -, -, hnu, hbank⟩ := hf
  rw [max_eq_left hΛ] at hlam hΦ
  have hm : (2 : ℝ) ≤ P.card := by exact_mod_cast hcard
  have hμt : ∀ i ∈ P, k + 1 ≤ S.tStar (f i) := fun i hi => hpost i hi
  have hT0 : k + 1 ≤ S.tStar (f i0) := hμt i0 hi0
  have htel := G.telescope hT0 (S.tStar b')
  -- the bound on `Ā(λ_{t'})`
  have hAb0 : 0 ≤ S.Abar (S.lam (S.tStar b')) := by
    have := G.ok.A2_pos; have := G.ok.θp_pos; have := G.ok.Cw_nonneg
    have := (G.ok.lam_pos (S.tStar b')).le
    unfold Typing.Abar; positivity
  have hAb : S.Abar (S.lam (S.tStar b')) ≤ S.Abar (S.cPrime * S.lam (k + 1)) :=
    G.ok.Abar_mono (G.ok.lam_pos _).le hlam
  have hAb0' : 0 ≤ S.Abar (S.cPrime * S.lam (k + 1)) := hAb0.trans hAb
  have h7 := G.lc.l7 (S.lam (k + 1)) (G.lam_ge _)
  have hEl := G.ok.E_le (k + 1)
  have hK : (S.Gbar (S.lam (k + 1)) + 2 * S.cStar) * S.Abar (S.cPrime * S.lam (k + 1)) +
      S.E (k + 1) ≤ S.tau (k + 1) := by
    unfold Setting.tau; linarith
  have hpay := Ineq.shift_pay (m := (P.card : ℝ)) (Δ := ((S.tStar b' - S.tStar (f i0) : ℕ) : ℝ))
    (K := S.Gbar (S.lam (k + 1)) + 2 * S.cStar) (Ab := S.Abar (S.cPrime * S.lam (k + 1)))
    (E := S.E (k + 1)) (τ := S.tau (k + 1)) (by linarith) hdelta hAb0' hK (G.ok.E_nonneg _)
  have hΔA : ((S.tStar b' - S.tStar (f i0) : ℕ) : ℝ) * S.Abar (S.lam (S.tStar b')) ≤
      ((S.tStar b' - S.tStar (f i0) : ℕ) : ℝ) * S.Abar (S.cPrime * S.lam (k + 1)) := by
    gcongr
  -- the lower bound for the sum
  have hsplit := sum_split (P := P) (i0 := i0)
    (h := fun j => S.tau (S.tStar (f j)) + S.W (k + 1) (S.tStar (f j)) + (f j).nu + S.bank (f j))
    (c := S.tau (k + 1)) hi0 (fun j hj => by
      have h1 := G.ok.tau_mono (hμt j hj)
      have h2 := G.ok.W_nonneg (k + 1) (S.tStar (f j))
      have h3 : (0 : ℝ) ≤ (f j).nu := Nat.cast_nonneg _
      have h4 := G.bank_nonneg (f j)
      show S.tau (k + 1) ≤ _
      linarith)
  have hν0 : (1 : ℝ) ≤ (f i0).nu := by exact_mod_cast (hinv i0 hi0).one_le_nu
  have hU0 := G.bank_nonneg (f i0)
  have hA : 0 ≤ S.v (k + 1) / S.L * ∑ i ∈ P, (f i).len := by
    have := G.ok.v_nonneg (k + 1)
    have : 0 ≤ ∑ i ∈ P, (f i).len := Finset.sum_nonneg (fun i hi => (hinv i hi).len_nonneg)
    have := G.ok.cast_L_ge
    positivity
  unfold Setting.B7
  rw [hnu, hbank]
  push_cast
  simp only [add_zero, Nat.cast_zero, mul_zero] at *
  push_cast at *
  linarith

/-- (B.7) for a merge with a `Pre` part when the new spine is long. -/
theorem mergePre_big {k : ℕ} {ι : Type*} {P : Finset ι} {f : ι → Book} {b' : Book} {i1 : ι}
    (hinv : ∀ i ∈ P, BookInv S k (f i)) (hpost : ∀ i ∈ P, k < S.tStar (f i))
    (hcard : 2 ≤ P.card) (hi1 : i1 ∈ P) (hmax1 : ∀ j ∈ P, (f j).len ≤ (f i1).len)
    (hf : RestartFacts S k b')
    (hlen : b'.len ≤ ∑ i ∈ P, (f i).len / S.L + (((P.card + 0 : ℕ) : ℝ) - 1) * S.D (k + 1))
    (hbig : S.lam (k + 1) < Real.logb S.L (max b'.len 1)) :
    S.B7 k P f 0 b' := by
  have hL := G.ok.cast_L_ge
  have hm : (2 : ℝ) ≤ P.card := by exact_mod_cast hcard
  have hlenP : ∀ j ∈ P, 0 ≤ (f j).len := fun j hj => (hinv j hj).len_nonneg
  have hD0 : 0 ≤ S.D (k + 1) := S.D_nonneg _
  obtain ⟨-, -, hΦ⟩ := G.restart_Phi hf
  obtain ⟨-, -, -, hnu, hbank⟩ := hf
  set Λ := Real.logb S.L (max b'.len 1) with hΛ
  rw [max_eq_right hbig.le] at hΦ
  have hlb := G.len_log_bound (P := P) (f := f) hi1 hmax1 hlenP hD0 (by simpa using hlen)
  rw [← hΛ] at hlb
  have hl1 := G.ok.one_le_lam (k + 1)
  have hΛ1 : 1 < Λ := lt_of_le_of_lt hl1 hbig
  have hΛx : S.lam 0 ≤ Λ := (G.lam_ge (k + 1)).trans hbig.le
  -- the sum of the pieces
  have hsumlow : (P.card : ℝ) * (S.tau (k + 1) + 1) ≤
      ∑ i ∈ P, (S.tau (S.tStar (f i)) + S.W (k + 1) (S.tStar (f i)) + (f i).nu +
        S.bank (f i)) := by
    have := Finset.card_nsmul_le_sum P (fun i => S.tau (S.tStar (f i)) +
        S.W (k + 1) (S.tStar (f i)) + (f i).nu + S.bank (f i)) (S.tau (k + 1) + 1)
      (fun j hj => by
        have h1 := G.ok.tau_mono (show k + 1 ≤ S.tStar (f j) from hpost j hj)
        have h2 := G.ok.W_nonneg (k + 1) (S.tStar (f j))
        have h3 : (1 : ℝ) ≤ (f j).nu := by exact_mod_cast (hinv j hj).one_le_nu
        have h4 := G.bank_nonneg (f j)
        show S.tau (k + 1) + 1 ≤ _
        linarith)
    rw [mul_add, mul_one]
    simpa using this
  set Q := S.v (k + 1) / S.L * ∑ i ∈ P, (f i).len with hQ
  have hA0 : 0 ≤ ∑ i ∈ P, (f i).len := Finset.sum_nonneg hlenP
  have hQ0 : 0 ≤ Q := by
    have := G.ok.v_nonneg (k + 1)
    positivity
  have hΦQ : S.Phi Λ ≤ Q ∨ S.Phi Λ + 1 ≤ (P.card : ℝ) := by
    by_cases hα : Λ / 2 ≤ Real.logb S.L (max (f i1).len 1)
    · left
      have hpos : 0 < Λ / 2 := by linarith
      have hpow := G.rpow_logb_max (f i1).len
      have hge : (S.L : ℝ) ^ (Λ / 2) ≤ (S.L : ℝ) ^ Real.logb S.L (max (f i1).len 1) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hα
      rw [hpow] at hge
      have hone : 1 < (S.L : ℝ) ^ (Λ / 2) := Real.one_lt_rpow (by linarith) hpos
      have hℓ : (S.L : ℝ) ^ (Λ / 2) ≤ (f i1).len := by
        rcases le_total (f i1).len 1 with h | h
        · rw [max_eq_right h] at hge; linarith
        · rw [max_eq_left h] at hge; exact hge
      have hA : (f i1).len ≤ ∑ i ∈ P, (f i).len :=
        Finset.single_le_sum (f := fun i => (f i).len) (fun i hi => hlenP i hi) hi1
      have h8 := G.lc.l8_a Λ hΛx
      have hv := G.ok.one_le_v (k + 1)
      have : (S.L : ℝ) ^ (Λ / 2 - 1) = (S.L : ℝ) ^ (Λ / 2) / S.L :=
        Real.rpow_sub_one (by linarith) _
      have hQ1 : (∑ i ∈ P, (f i).len) / S.L ≤ Q := by
        rw [hQ, div_eq_mul_inv, div_eq_mul_inv]
        have hiL : 0 ≤ (S.L : ℝ)⁻¹ := by positivity
        have := mul_nonneg (mul_nonneg (sub_nonneg.2 hv) hA0) hiL
        nlinarith
      have : (S.L : ℝ) ^ (Λ / 2) / S.L ≤ (∑ i ∈ P, (f i).len) / S.L := by
        gcongr; linarith
      linarith
    · right
      have hlm : Λ / 2 ≤ Real.logb S.L (P.card : ℝ) + Real.logb S.L (1 + S.D (k + 1)) := by
        linarith
      have hmul : Real.logb S.L (P.card : ℝ) + Real.logb S.L (1 + S.D (k + 1)) =
          Real.logb S.L ((P.card : ℝ) * (1 + S.D (k + 1))) := by
        rw [Real.logb_mul (by positivity) (by linarith)]
      rw [hmul, Real.le_logb_iff_rpow_le (by linarith) (by positivity)] at hlm
      have hB : 0 < 1 + S.Dbar Λ := by
        have := G.ok.one_le_Dbar Λ; linarith
      have hDB : S.D (k + 1) ≤ S.Dbar Λ :=
        (G.ok.D_le_bar (k + 1)).trans (G.ok.Dbar_mono (G.ok.lam_pos _).le hbig.le)
      have h8 := G.lc.l8_b Λ hΛx
      have h9 : S.Phi Λ * (2 * (1 + S.Dbar Λ)) ≤ (S.L : ℝ) ^ (Λ / 2) := by
        rwa [le_div_iff₀ (by positivity)] at h8
      have h10 : (S.L : ℝ) ^ (Λ / 2) ≤ (P.card : ℝ) * (1 + S.Dbar Λ) := by
        refine hlm.trans ?_
        gcongr
      have h11 : 2 * S.Phi Λ ≤ P.card := by
        have : S.Phi Λ * (2 * (1 + S.Dbar Λ)) ≤ (P.card : ℝ) * (1 + S.Dbar Λ) := h9.trans h10
        nlinarith
      linarith
  have hfin := Ineq.pre_big (m := (P.card : ℝ)) (E := S.E (k + 1)) (τ := S.tau (k + 1))
    (Φ := S.Phi Λ) (Q := Q) hm (G.ok.E_nonneg _) (G.E_add_one_le_tau _) hQ0 hΦQ
  unfold Setting.B7
  rw [hnu, hbank]
  push_cast
  simp only [add_zero, Nat.cast_zero, mul_zero] at *
  push_cast at *
  nlinarith [hfin, hsumlow, hΦ]

/-- Case 2b: (B.7) for a merge with a `Pre` part ((T3)). -/
theorem case_mergePre {k : ℕ} {ι : Type*} {P : Finset ι} {f : ι → Book} {b' : Book}
    (hinv : ∀ i ∈ P, BookInv S k (f i)) (hpost : ∀ i ∈ P, k < S.tStar (f i))
    (hcard : 2 ≤ P.card) (hpre : ∃ p ∈ P, (f p).st = .pre) (hf : RestartFacts S k b')
    (hlen : b'.len ≤ ∑ i ∈ P, (f i).len / S.L + (((P.card + 0 : ℕ) : ℝ) - 1) * S.D (k + 1)) :
    S.B7 k P f 0 b' := by
  obtain ⟨p, hp, hppre⟩ := hpre
  have hne : P.Nonempty := ⟨p, hp⟩
  obtain ⟨i0, hi0, hmax0⟩ := Finset.exists_max_image P (fun i => S.tStar (f i)) hne
  obtain ⟨i1, hi1, hmax1⟩ := Finset.exists_max_image P (fun i => (f i).len) hne
  by_cases hΛ : Real.logb S.L (max b'.len 1) ≤ S.lam (k + 1)
  · exact G.mergePre_small hinv hpost hcard hp hppre hi0 hmax0 hi1 hmax1 hf hlen hΛ
  · exact G.mergePre_big hinv hpost hcard hi1 hmax1 hf hlen (not_le.mp hΛ)

end Setting.Good

end Balaban.LargeField
