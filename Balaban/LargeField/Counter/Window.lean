module

public import Balaban.LargeField.Counter.CaseCap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The budget invariant (H6′) in the window regime (Part I, §I.5.4–§I.5.5)

`PreH6 H k c` is (H6′)^pre for a component of `Z^pre_k`, `PostH6 H k c` is (H6′) for a component of
`Z_k`.  `pre_step` proves (H6′)^pre at `k + 1` from (H6′) at `k` (the five cases of §I.5.4);
`rstep_budget` proves (H6′) after `R^{(k)}`.
-/

@[expose] public section

namespace Balaban.LargeField

namespace CounterHist

variable {S : Setting} {k0 K : ℕ} {Cp : ℕ → Type} [∀ k, Fintype (Cp k)] [∀ k, DecidableEq (Cp k)]
  (H : CounterHist S k0 K Cp)

/-- (H6′)^pre for a component of `Z^pre_k`. -/
def PreH6 (k : ℕ) (c : Cp k) : Prop :=
  k ≤ S.tStar (H.bk k c) ∧
    S.tau (S.tStar (H.bk k c)) + 2 * S.sigma k * (H.bk k c).len +
      S.W (k + 1) (S.tStar (H.bk k c)) + (H.bk k c).nu + S.bank (H.bk k c) ≤ H.Gp k c

/-- (H6′) for a component of `Z_k`. -/
def PostH6 (k : ℕ) (c : Cp k) : Prop :=
  k < S.tStar (H.pbk k c) ∧
    S.tau (S.tStar (H.pbk k c)) + 2 * S.sigma k * (H.pbk k c).len +
      S.W (k + 1) (S.tStar (H.pbk k c)) + (H.pbk k c).nu + S.bank (H.pbk k c) ≤ H.G k c

end CounterHist

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

/-- The step `k → k+1` of (H6′), window regime. -/
theorem pre_step {k0 K : ℕ} {Cp : ℕ → Type} [∀ k, Fintype (Cp k)] [∀ k, DecidableEq (Cp k)]
    (H : CounterHist S k0 K Cp) {k : ℕ} (hK : k < K) (hk0 : k + 1 ≤ k0) (Z' : Cp (k + 1))
    (hI : ∀ i ∈ H.parts k Z', BookInv S k (H.pbk k i) ∧ k < S.tStar (H.pbk k i))
    (hP : ∀ i ∈ H.parts k Z', H.PostH6 k i) : H.PreH6 (k + 1) Z' := by
  have hrule := Setting.BookRule.toTrue S (H.book_rule k hK Z') hk0
  have hinv : ∀ i ∈ H.parts k Z', BookInv S k (H.pbk k i) := fun i hi => (hI i hi).1
  have hpost : ∀ i ∈ H.parts k Z', k < S.tStar (H.pbk k i) := fun i hi => (hI i hi).2
  have hlenP : ∀ i ∈ H.parts k Z', 0 ≤ (H.pbk k i).len := fun i hi => (hinv i hi).len_nonneg
  have hseed := H.seed_pos k hK Z'
  obtain ⟨hbinv, hcase⟩ := G.step_classify (f := H.pbk k) hinv hpost hseed hrule
  have hlen := hrule.len_gen
  have hB7 : S.B7 k (H.parts k Z') (H.pbk k) (H.newc (k + 1) Z') (H.bk (k + 1) Z') ∧
      k + 1 ≤ S.tStar (H.bk (k + 1) Z') := by
    cases hcase with
    | shadow i hparts hr hle hge hnu hbank =>
      exact ⟨G.case_shadow hparts hr hle hnu hbank (hlenP i (by rw [hparts]; simp)), hge⟩
    | new hr hf =>
      exact ⟨G.case_new hlenP hpost hr hf hlen, by have := hf.2.1; have := hf.1; omega⟩
    | mergePre hr hcard hpre hf =>
      have hlen0 := hlen
      rw [hr] at hlen0
      rw [hr]
      exact ⟨G.case_mergePre hinv hpost hcard hpre hf hlen0, by
        have := hf.2.1; have := hf.1; omega⟩
    | mergeCap hr hcard hnpre hcap hf =>
      have hlen0 := hlen
      rw [hr] at hlen0
      rw [hr]
      have hact : ∀ i ∈ H.parts k Z', (H.pbk k i).IsActive ∨ (H.pbk k i).IsPending := by
        intro i hi
        rcases Book.cases_st (H.pbk k i) with h | h | h
        · exact absurd h (hnpre i hi)
        · exact Or.inr h
        · exact Or.inl h
      refine ⟨G.case_cap hinv hpost hact hcard hcap hf hlen0, ?_⟩
      rw [hf.tStar_eq]
      unfold Setting.t4T
      have := G.ok.Tmin_spec (Setting.t4E (k + 1) (H.parts k Z') (H.pbk k))
        (S.t4t0 (H.parts k Z') (H.pbk k) (H.bk (k + 1) Z').s)
      have h1 := this.1
      have h2 := hf.s_ge
      have h3 : (H.bk (k + 1) Z').s + S.n2 (H.bk (k + 1) Z').s ≤
          S.t4t0 (H.parts k Z') (H.pbk k) (H.bk (k + 1) Z').s := le_max_right _ _
      omega
    | overflow hr hcard hnpre hcap hf =>
      have hlen0 := hlen
      rw [hr] at hlen0
      rw [hr]
      have hact : ∀ i ∈ H.parts k Z', (H.pbk k i).IsActive ∨ (H.pbk k i).IsPending := by
        intro i hi
        rcases Book.cases_st (H.pbk k i) with h | h | h
        · exact absurd h (hnpre i hi)
        · exact Or.inr h
        · exact Or.inl h
      exact ⟨G.case_overflow hinv hpost hact hcard hcap hf hlen0, by
        have := hf.2.1; have := hf.1; omega⟩
  refine ⟨hbinv.tstar_ge, ?_⟩
  have := G.sufficient_B7 (k := k) (P := H.parts k Z') (f := H.pbk k) (r := H.newc (k + 1) Z')
    (b' := H.bk (k + 1) Z') (Gi := fun i => H.G k i) (Gpre := H.Gp (k + 1) Z')
    (vol := H.vol (k + 1) Z') (fun i hi => (hP i hi).2) (H.budget k hK Z')
    (H.vol_bound k hK Z') hlen hseed hB7.2 hB7.1
  exact this

/-- (H6′) after `R^{(k)}` (Part I §I.5.5), `1 ≤ k ≤ k₀`. -/
theorem post_of_pre {k0 K : ℕ} {Cp : ℕ → Type} [∀ k, Fintype (Cp k)] [∀ k, DecidableEq (Cp k)]
    (H : CounterHist S k0 K Cp) {k : ℕ} (hk1 : 1 ≤ k) (hk0 : k ≤ k0) (c : Cp k)
    (hc : c ∉ H.rem k) (hinv : BookInv S k (H.bk k c)) (hpre : H.PreH6 k c) : H.PostH6 k c := by
  have hr := G.rstep_inv (k0 := k0) hk1 hk0 hinv
  by_cases hrip : S.Ripe k (H.bk k c)
  · obtain ⟨hlen0, hnu1, hbank0, htS⟩ := hr.2.2 hrip
    have hpb : H.pbk k c = S.postBook k0 k (H.bk k c) := rfl
    rw [← hpb] at hlen0 hnu1 hbank0 htS
    have hrg := H.rg_ripe k hk1 hk0 c hc hrip
    obtain ⟨-, hpre2⟩ := hpre
    have hT : S.tStar (H.bk k c) = k := hrip.2
    rw [hT] at hpre2
    have hW : S.W (k + 1) k = 0 := S.W_eq_zero_of_lt (Nat.lt_succ_self k)
    have hσ0 := G.ok.sigma_nonneg k
    have hlen := hinv.len_nonneg
    have hτ0 := G.ok.tau_nonneg k
    have hb0 := G.bank_nonneg (H.bk k c)
    have hnu0 : (0 : ℝ) ≤ (H.bk k c).nu := Nat.cast_nonneg _
    have hGp : 0 ≤ H.Gp k c := by
      rw [hW] at hpre2
      have : 0 ≤ 2 * S.sigma k * (H.bk k c).len := by positivity
      linarith
    refine ⟨hr.2.1, ?_⟩
    rw [hlen0, hnu1, hbank0, htS]
    -- the bound of (Λ10)
    have hl := G.ok.lam_pos k
    have hlamt : S.lam (k + S.nq k) ≤ S.cDPrime * S.lam k := G.ok.lam_add_nq_le k
    have hlt0 := (G.ok.lam_pos (k + S.nq k)).le
    have h10 := G.lc.l10 (S.lam k) (G.lam_ge k)
    have hτ : S.tau (k + S.nq k) ≤ 2 * S.A2 * (S.cDPrime * S.lam k) ^ S.p2 := by
      unfold Setting.tau
      have := G.ok.A2_pos
      gcongr
    have hWb : S.W (k + 1) (k + S.nq k) ≤
        (S.lam k / (S.α * S.logL) + 1) * S.Cw * (S.cDPrime * S.lam k) ^ (2 * S.d + 1) := by
      have h1 := G.ok.W_le (k + 1) (k + S.nq k)
      have h2 : ((k + S.nq k + 1 - (k + 1) : ℕ) : ℝ) = S.nq k := by
        have : k + S.nq k + 1 - (k + 1) = S.nq k := by omega
        rw [this]
      rw [h2] at h1
      have h3 := G.ok.nq_le k
      have h4 : S.lam (k + S.nq k) ^ (2 * S.d + 1) ≤ (S.cDPrime * S.lam k) ^ (2 * S.d + 1) :=
        pow_le_pow_left₀ hlt0 hlamt _
      have h5 := G.ok.Cw_nonneg
      calc S.W (k + 1) (k + S.nq k) ≤ (S.nq k : ℝ) * (S.Cw * S.lam (k + S.nq k) ^ (2 * S.d + 1)) := h1
        _ ≤ (S.lam k / (S.α * S.logL) + 1) * (S.Cw * (S.cDPrime * S.lam k) ^ (2 * S.d + 1)) := by
          apply mul_le_mul h3 _ (by positivity) (by
            have := G.ok.αlogL_pos
            positivity)
          exact mul_le_mul_of_nonneg_left h4 h5
        _ = _ := by ring
    simp only [Nat.cast_one, mul_zero, add_zero]
    linarith
  · have hpb : H.pbk k c = H.bk k c := S.postBook_of_not_ripe hrip
    have hG : H.G k c = H.Gp k c := H.rg_nonripe k hk1 hk0 c hc hrip
    refine ⟨hr.2.1, ?_⟩
    rw [hpb, hG]
    exact hpre.2

end Setting.Good

end Balaban.LargeField
