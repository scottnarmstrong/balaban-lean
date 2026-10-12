module

public import Balaban.LargeField.Counter.Window
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Transfer at `k₀` and the frozen regime (Part I, §I.5.6)

`H6flat` is (H6♭).  `W_horizon` is (B.20), `transfer` the passage from (H6′) at `k₀` to (H6♭),
`frozen_step` the inequality (I.6).
-/

@[expose] public section

namespace Balaban.LargeField

theorem Setting.postBook_len (S : Setting) (k0 k : ℕ) (b : Book) :
    (S.postBook k0 k b).len = b.len := by
  unfold Setting.postBook
  split_ifs <;> rfl

namespace CounterHist

variable {S : Setting} {k0 K : ℕ} {Cp : ℕ → Type} [∀ k, Fintype (Cp k)] [∀ k, DecidableEq (Cp k)]
  (H : CounterHist S k0 K Cp)

/-- (H6♭) for a component of `Z_k`, `k ≥ k₀`. -/
def H6flat (khat k : ℕ) (c : Cp k) : Prop :=
  S.A2 * S.lam k0 ^ S.p2 + 2 * S.sigma k * (H.bk k c).len + S.W (k + 1) khat ≤ H.G k c

end CounterHist

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

theorem W_horizon_aux {k0 khat : ℕ} (hk : k0 ≤ khat) (hH1 : (khat : ℝ) - k0 < S.lam k0)
    (hH2 : S.lam khat ≤ S.d / 2 * S.lam k0 + S.cH) :
    S.W (k0 + 1) khat ≤ S.lam k0 * S.Cw * (S.d * S.lam k0) ^ (2 * S.d + 1) := by
  have hl := G.ok.lam_pos k0
  have hd : (1 : ℝ) ≤ S.d := by exact_mod_cast G.ok.one_le_d
  have h11a := G.lc.l11_a (S.lam k0) (G.lam_ge k0)
  have h11b := G.lc.l11_b (S.lam k0) (G.lam_ge k0)
  have hlam : S.lam khat ≤ S.d * S.lam k0 := by nlinarith
  have hW := G.ok.W_le (k0 + 1) khat
  have hcnt : ((khat + 1 - (k0 + 1) : ℕ) : ℝ) = (khat : ℝ) - k0 := by
    have : khat + 1 - (k0 + 1) = khat - k0 := by omega
    rw [this, Nat.cast_sub hk]
  rw [hcnt] at hW
  have h1 : S.lam khat ^ (2 * S.d + 1) ≤ (S.d * S.lam k0) ^ (2 * S.d + 1) :=
    pow_le_pow_left₀ (G.ok.lam_pos _).le hlam _
  have hCw := G.ok.Cw_nonneg
  have hcnt0 : (0 : ℝ) ≤ (khat : ℝ) - k0 := by
    have : (k0 : ℝ) ≤ khat := by exact_mod_cast hk
    linarith
  calc S.W (k0 + 1) khat ≤ ((khat : ℝ) - k0) * (S.Cw * S.lam khat ^ (2 * S.d + 1)) := hW
    _ ≤ S.lam k0 * (S.Cw * (S.d * S.lam k0) ^ (2 * S.d + 1)) := by
      apply mul_le_mul hH1.le _ (mul_nonneg hCw (pow_nonneg (G.ok.lam_pos _).le _)) hl.le
      exact mul_le_mul_of_nonneg_left h1 hCw
    _ = S.lam k0 * S.Cw * (S.d * S.lam k0) ^ (2 * S.d + 1) := by ring

/-- (B.20): the horizon sum `W_{k₀+1}(k̂_f) ≤ A₂ λ_{k₀}^{p₂}`. -/
theorem W_horizon {k0 khat : ℕ} (hk : k0 ≤ khat) (hH1 : (khat : ℝ) - k0 < S.lam k0)
    (hH2 : S.lam khat ≤ S.d / 2 * S.lam k0 + S.cH) :
    S.W (k0 + 1) khat ≤ S.A2 * S.lam k0 ^ S.p2 :=
  (G.W_horizon_aux hk hH1 hH2).trans (G.lc.l11_b (S.lam k0) (G.lam_ge k0))

theorem W_anti_left (t : ℕ) {a a' : ℕ} (h : a ≤ a') : S.W a' t ≤ S.W a t := by
  unfold Setting.W
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc h le_rfl
  · intro j _ _; exact G.ok.w_nonneg j

/-- Transfer at `k₀`: (H6′) implies (H6♭). -/
theorem transfer {k0 K : ℕ} {Cp : ℕ → Type} [∀ k, Fintype (Cp k)] [∀ k, DecidableEq (Cp k)]
    (H : CounterHist S k0 K Cp) {khat : ℕ} (hk0 : k0 ≤ khat)
    (hH1 : (khat : ℝ) - k0 < S.lam k0) (hH2 : S.lam khat ≤ S.d / 2 * S.lam k0 + S.cH)
    (c : Cp k0) (hc : H.PostH6 k0 c) : H.H6flat khat k0 c := by
  obtain ⟨ht, hG⟩ := hc
  have hWh := G.W_horizon hk0 hH1 hH2
  set b := H.pbk k0 c with hb
  have hlen : b.len = (H.bk k0 c).len := S.postBook_len k0 k0 _
  unfold CounterHist.H6flat
  rw [← hlen]
  have hν : (0 : ℝ) ≤ b.nu := Nat.cast_nonneg _
  have hU := G.bank_nonneg b
  have hA2 := G.ok.A2_pos
  have hl0 := G.ok.lam_pos k0
  have hp : 0 ≤ S.lam k0 ^ S.p2 := by positivity
  have hτk : S.tau k0 = 2 * S.A2 * S.lam k0 ^ S.p2 := rfl
  by_cases hcmp : khat ≤ S.tStar b
  · have h1 := G.ok.W_mono_right (k0 + 1) hcmp
    have h2 := G.ok.tau_mono (show k0 ≤ S.tStar b by omega)
    nlinarith
  · have hlt := not_le.mp hcmp
    have h2 := G.ok.tau_mono (show k0 + 1 ≤ S.tStar b by omega)
    have h3 : S.tau k0 ≤ S.tau (k0 + 1) := G.ok.tau_mono (Nat.le_succ k0)
    have h4 := G.ok.W_nonneg (k0 + 1) (S.tStar b)
    nlinarith

/-- The frozen step `k → k+1`, `k₀ ≤ k < K` (inequality (I.6)). -/
theorem frozen_step {k0 K : ℕ} {Cp : ℕ → Type} [∀ k, Fintype (Cp k)] [∀ k, DecidableEq (Cp k)]
    (H : CounterHist S k0 K Cp) {khat : ℕ} (hK : K ≤ khat)
    (hH1 : (khat : ℝ) - k0 < S.lam k0) (hH2 : S.lam khat ≤ S.d / 2 * S.lam k0 + S.cH)
    {k : ℕ} (hkk0 : k0 ≤ k) (hkK : k < K) (Z' : Cp (k + 1))
    (hlenP : ∀ i ∈ H.parts k Z', 0 ≤ (H.bk k i).len)
    (hP : ∀ i ∈ H.parts k Z', H.H6flat khat k i) : H.H6flat khat (k + 1) Z' := by
  have hrule := H.book_rule k hkK Z'
  have hseed := H.seed_pos k hkK Z'
  have hlen : (H.bk (k + 1) Z').len ≤ ∑ i ∈ H.parts k Z', (H.bk k i).len / S.L +
      (((H.parts k Z').card + H.newc (k + 1) Z' : ℕ) - 1 : ℝ) * S.D (k + 1) := by
    have := hrule.len_gen
    simpa [Setting.postBook_len, CounterHist.pbk] using this
  have hk0K : k0 ≤ khat := by omega
  have hμkhat : k + 1 ≤ khat := by omega
  set A := S.A2 * S.lam k0 ^ S.p2 with hA
  set Wμ := S.W (k + 1) khat with hWμ
  have hl0 := G.ok.lam_pos k0
  have hd : (1 : ℝ) ≤ S.d := by exact_mod_cast G.ok.one_le_d
  have hlam_khat : S.lam khat ≤ S.d * S.lam k0 := by
    have := G.lc.l11_a (S.lam k0) (G.lam_ge k0); nlinarith
  have hlamμ : S.lam (k + 1) ≤ S.d * S.lam k0 :=
    (G.ok.lam_mono hμkhat).trans hlam_khat
  -- `A ≥ E_μ` and `g_k ≥ A + W_μ + E_μ`
  have hEμ : S.E (k + 1) ≤ S.CE * (S.d * S.lam k0) ^ (2 * S.d + 1) := by
    refine (G.ok.E_le (k + 1)).trans ?_
    have : S.lam (k + 1) ^ (2 * S.d + 1) ≤ (S.d * S.lam k0) ^ (2 * S.d + 1) :=
      pow_le_pow_left₀ (G.ok.lam_pos _).le hlamμ _
    have hCE : 0 ≤ S.CE := G.ok.CE_nonneg
    exact mul_le_mul_of_nonneg_left this hCE
  have hAE : S.E (k + 1) ≤ A := hEμ.trans (G.lc.l11_c (S.lam k0) (G.lam_ge k0))
  have hWμ_le : Wμ ≤ S.lam k0 * S.Cw * (S.d * S.lam k0) ^ (2 * S.d + 1) :=
    (G.W_anti_left khat (show k0 + 1 ≤ k + 1 by omega)).trans
      (G.W_horizon_aux hk0K hH1 hH2)
  have hg : A + Wμ + S.E (k + 1) ≤ S.g k := by
    have h11d := G.lc.l11_d (S.lam k0) (G.lam_ge k0)
    have hlk : S.lam k0 ≤ S.lam k := G.ok.lam_mono hkk0
    have hpow : S.lam k0 ^ (2 * S.p0) ≤ S.lam k ^ (2 * S.p0) := pow_le_pow_left₀ hl0.le hlk _
    have hA3 := G.ok.A3_pos
    have : 1 / 2 * S.A3 * S.lam k0 ^ (2 * S.p0) ≤ S.g k := by
      unfold Setting.g
      have : 1 / 2 * S.A3 * S.lam k0 ^ (2 * S.p0) ≤ 1 / 2 * S.A3 * S.lam k ^ (2 * S.p0) := by
        gcongr
      exact this
    linarith
  have hW0 : 0 ≤ Wμ := G.ok.W_nonneg _ _
  have hE0 := G.ok.E_nonneg (k + 1)
  have hA0 : 0 ≤ A := hE0.trans hAE
  -- (I.6)
  have hB : (A + Wμ) + ((((H.parts k Z').card + H.newc (k + 1) Z' : ℕ) : ℝ) - 1) * S.E (k + 1) ≤
      ∑ i ∈ H.parts k Z', (A + Wμ) + S.g k * (H.newc (k + 1) Z' : ℝ) +
        S.v (k + 1) / S.L * ∑ i ∈ H.parts k Z', (H.bk k i).len := by
    have hv : 0 ≤ S.v (k + 1) / S.L * ∑ i ∈ H.parts k Z', (H.bk k i).len := by
      have := G.ok.v_nonneg (k + 1)
      have : 0 ≤ ∑ i ∈ H.parts k Z', (H.bk k i).len := Finset.sum_nonneg hlenP
      have := G.ok.cast_L_ge
      positivity
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hm0 : (0 : ℝ) ≤ (H.parts k Z').card := Nat.cast_nonneg _
    have hr0 : (0 : ℝ) ≤ H.newc (k + 1) Z' := Nat.cast_nonneg _
    have hmr : (1 : ℝ) ≤ (H.parts k Z').card + H.newc (k + 1) Z' := by exact_mod_cast hseed
    push_cast
    by_cases hm1 : (1 : ℝ) ≤ (H.parts k Z').card
    · nlinarith [mul_nonneg (show 0 ≤ ((H.parts k Z').card : ℝ) - 1 by linarith)
          (show 0 ≤ A + Wμ - S.E (k + 1) by linarith),
        mul_nonneg hr0 (show 0 ≤ S.g k - S.E (k + 1) by linarith)]
    · have hm00 : ((H.parts k Z').card : ℝ) = 0 := by
        have : (H.parts k Z').card = 0 := by
          by_contra h
          have h1 : 1 ≤ (H.parts k Z').card := by omega
          exact hm1 (by exact_mod_cast h1)
        rw [this]; simp
      rw [hm00] at hmr ⊢
      have hr1 : 1 ≤ (H.newc (k + 1) Z' : ℝ) := by linarith
      nlinarith [mul_nonneg (show 0 ≤ (H.newc (k + 1) Z' : ℝ) - 1 by linarith)
        (show 0 ≤ S.g k - S.E (k + 1) by linarith)]
  have hcore := G.budget_core (P := H.parts k Z') (len := fun i => (H.bk k i).len)
    (c := fun _ => A + Wμ) (Gi := H.G k) (r := H.newc (k + 1) Z')
    (len' := (H.bk (k + 1) Z').len) (C' := A + Wμ) (Gpre := H.Gp (k + 1) Z')
    (vol := H.vol (k + 1) Z') (fun i hi => by
      have := hP i hi
      unfold CounterHist.H6flat at this
      linarith)
    (H.budget k hkK Z') (H.vol_bound k hkK Z') (by simpa using hlen) hseed (by simpa using hB)
  have hGG : H.G (k + 1) Z' = H.Gp (k + 1) Z' := H.rg_frozen (k + 1) (by omega) Z'
  have hsplit : Wμ = S.w (k + 1) + S.W (k + 1 + 1) khat := S.W_split hμkhat
  unfold CounterHist.H6flat
  rw [hGG]
  linarith

end Setting.Good

end Balaban.LargeField
