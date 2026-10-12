module

public import Balaban.LargeField.Counter.Frozen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The step counter on the numerical history (Part I, Theorem I.5.4)

`counter_main` proves (i) and (ii) of LF-2 and the numerical content of (iii), (iv) for a
`CounterHist`.  The geometric statement `LF2` (with the abstract region history) is
`Counter/LF2`; it reduces to this theorem.
-/

@[expose] public section

namespace Balaban.LargeField

/-- The conclusions of LF-2 (Theorem I.5.4) on a numerical history. -/
structure CounterConclusion {S : Setting} {k0 K : ℕ} {Cp : ℕ → Type} [∀ k, Fintype (Cp k)]
    [∀ k, DecidableEq (Cp k)] (H : CounterHist S k0 K Cp) (khat : ℕ) : Prop where
  /-- (i): (H6′)^pre -/
  pre : 1 ≤ k0 → ∀ k, 1 ≤ k → k ≤ k0 → k ≤ K → ∀ c : Cp k, H.PreH6 k c
  /-- (i): (H6′) -/
  post : 1 ≤ k0 → ∀ k, 1 ≤ k → k ≤ k0 → k ≤ K → ∀ c : Cp k, c ∉ H.rem k → H.PostH6 k c
  /-- (ii): (H6♭) -/
  flat : ∀ k, k0 ≤ k → 1 ≤ k → k ≤ K → ∀ c : Cp k, c ∉ H.rem k → H.H6flat khat k c
  /-- (iii): the shape statements of Lemmas I.4.10, I.4.13, before `R` -/
  shape_pre : ∀ k, 1 ≤ k → k ≤ k0 → k ≤ K → ∀ c : Cp k, BookInv S k (H.bk k c)
  /-- (iii): the shape statements after `R` -/
  shape_post : ∀ k, 1 ≤ k → k ≤ k0 → k ≤ K → ∀ c : Cp k,
    BookInv S k (H.pbk k c) ∧ k < S.tStar (H.pbk k c)
  /-- (iii): a ripe component is `Active` with core `k₁(k)` -/
  ripe_core : ∀ k, 1 ≤ k → k ≤ k0 → k ≤ K → ∀ c : Cp k, S.Ripe k (H.bk k c) →
    (H.bk k c).IsActive ∧ (H.bk k c).q = S.k1 k
  /-- (iv): `G_k ≥ 2 A₂ λ_k^{p₂}` -/
  G_ge : ∀ k, 1 ≤ k → k ≤ k0 → k ≤ K → ∀ c : Cp k, c ∉ H.rem k →
    2 * S.A2 * S.lam k ^ S.p2 ≤ H.G k c
  /-- (iv): `G^pre_k ≥ 2 A₂ λ_k^{p₂} + 1` for ripe components -/
  Gp_ripe : ∀ k, 1 ≤ k → k ≤ k0 → k ≤ K → ∀ c : Cp k, S.Ripe k (H.bk k c) →
    2 * S.A2 * S.lam k ^ S.p2 + 1 ≤ H.Gp k c
  /-- (iv): `G_k ≥ A₂ λ_{k₀}^{p₂}` for `k₀ ≤ k ≤ K` -/
  G_frozen : ∀ k, k0 ≤ k → 1 ≤ k → k ≤ K → ∀ c : Cp k, c ∉ H.rem k →
    S.A2 * S.lam k0 ^ S.p2 ≤ H.G k c

theorem CounterHist.len_nonneg_succ {S : Setting} {k0 K : ℕ} {Cp : ℕ → Type}
    [∀ k, Fintype (Cp k)] [∀ k, DecidableEq (Cp k)] (H : CounterHist S k0 K Cp) {j : ℕ}
    (hj : j < K) (Z' : Cp (j + 1)) : 0 ≤ (H.bk (j + 1) Z').len :=
  (H.book_rule j hj Z').len_nonneg

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

/-- (i) of LF-2: (H6′)^pre and (H6′) for `1 ≤ k ≤ min {k₀, K}`. -/
theorem window_budget {k0 K : ℕ} {Cp : ℕ → Type} [∀ k, Fintype (Cp k)] [∀ k, DecidableEq (Cp k)]
    (H : CounterHist S k0 K Cp) :
    ∀ k, 1 ≤ k → k ≤ k0 → k ≤ K →
      (∀ c : Cp k, H.PreH6 k c) ∧ (∀ c : Cp k, c ∉ H.rem k → H.PostH6 k c) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro hk0 hkK
    have hpre : ∀ c : Cp 1, H.PreH6 1 c := fun c =>
      G.pre_step H (k := 0) (by omega) (by omega) c (fun i _ => (H.isEmpty0.false i).elim)
        (fun i _ => (H.isEmpty0.false i).elim)
    refine ⟨hpre, fun c hc => ?_⟩
    exact G.post_of_pre H (le_refl 1) hk0 c hc ((G.window_inv H 1 (le_refl 1) hk0 hkK c).1)
      (hpre c)
  | succ k hk ih =>
    intro hk0 hkK
    obtain ⟨-, hpost⟩ := ih (by omega) (by omega)
    have hpre : ∀ c : Cp (k + 1), H.PreH6 (k + 1) c := fun c =>
      G.pre_step H (k := k) (by omega) hk0 c (fun i hi => by
        have := G.window_inv H k hk (by omega) (by omega) i
        exact ⟨this.2.1, this.2.2⟩)
        (fun i hi => hpost i ((H.mem_parts k i c).mp hi).1)
    refine ⟨hpre, fun c hc => ?_⟩
    exact G.post_of_pre H (by omega) hk0 c hc
      ((G.window_inv H (k + 1) (by omega) hk0 hkK c).1) (hpre c)

/-- (ii) of LF-2: (H6♭) for `k₀ ≤ k ≤ K`, `k ≥ 1`. -/
theorem frozen_budget {k0 K : ℕ} {Cp : ℕ → Type} [∀ k, Fintype (Cp k)] [∀ k, DecidableEq (Cp k)]
    (H : CounterHist S k0 K Cp) {khat : ℕ} (hk0K : k0 ≤ K) (hKk : K ≤ khat)
    (hH1 : (khat : ℝ) - k0 < S.lam k0) (hH2 : S.lam khat ≤ S.d / 2 * S.lam k0 + S.cH) :
    ∀ k, k0 ≤ k → 1 ≤ k → k ≤ K → ∀ c : Cp k, c ∉ H.rem k → H.H6flat khat k c := by
  have hk0khat : k0 ≤ khat := by omega
  -- the step `k → k + 1` for `k ≥ 1`, `k ≥ k₀`
  have step : ∀ k, k0 ≤ k → 1 ≤ k → k < K →
      (∀ c : Cp k, c ∉ H.rem k → H.H6flat khat k c) →
      (∀ c : Cp (k + 1), c ∉ H.rem (k + 1) → H.H6flat khat (k + 1) c) := by
    intro k hkk0 hk1 hkK ih Z' _
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact G.frozen_step H hKk hH1 hH2 hkk0 hkK Z'
      (fun i _ => H.len_nonneg_succ (by omega) i)
      (fun i hi => ih i ((H.mem_parts _ i Z').mp hi).1)
  by_cases hk0 : 1 ≤ k0
  · intro k hkk0
    induction k, hkk0 using Nat.le_induction with
    | base =>
      intro _ hkK c hc
      exact G.transfer H hk0khat hH1 hH2 c
        ((G.window_budget H k0 hk0 le_rfl hkK).2 c hc)
    | succ k hk ih =>
      intro _ hkK
      exact step k hk (by omega) (by omega) (ih (by omega) (by omega))
  · have hk00 : k0 = 0 := by omega
    intro k hkk0 hk1
    induction k, hk1 using Nat.le_induction with
    | base =>
      intro hkK Z' _
      exact G.frozen_step H hKk hH1 hH2 (k := 0) (by omega) (by omega) Z'
        (fun i _ => (H.isEmpty0.false i).elim) (fun i _ => (H.isEmpty0.false i).elim)
    | succ k hk ih =>
      intro hkK
      exact step k (by omega) hk (by omega) (ih (by omega) (by omega))

theorem ripe_core {k : ℕ} {b : Book} (hb : BookInv S k b) (hr : S.Ripe k b) :
    b.IsActive ∧ b.q = S.k1 k := by
  refine ⟨hr.1, ?_⟩
  have hf4 := hb.f4 (Or.inl hr.1)
  have hT : S.tStar b = k := hr.2
  have hl := S.tStar_ge_left b
  have hnq0 : S.nq 0 ≤ k := by
    have := G.ok.nq_mono (Nat.zero_le b.q)
    omega
  symm
  exact (G.ok.k1_eq_iff hnq0).mpr ⟨by omega, by omega⟩

/-- Theorem I.5.4 (LF-2) on a numerical history. -/
theorem counter_main {k0 K : ℕ} {Cp : ℕ → Type} [∀ k, Fintype (Cp k)] [∀ k, DecidableEq (Cp k)]
    (H : CounterHist S k0 K Cp) {khat : ℕ} (hk0K : k0 ≤ K) (hKk : K ≤ khat)
    (hH1 : (khat : ℝ) - k0 < S.lam k0) (hH2 : S.lam khat ≤ S.d / 2 * S.lam k0 + S.cH) :
    CounterConclusion H khat := by
  have hflat := G.frozen_budget H hk0K hKk hH1 hH2
  refine ⟨fun h k a b c => (G.window_budget H k a b c).1,
    fun h k a b c => (G.window_budget H k a b c).2, hflat,
    fun k a b c d => (G.window_inv H k a b c d).1,
    fun k a b c d => ⟨(G.window_inv H k a b c d).2.1, (G.window_inv H k a b c d).2.2⟩,
    fun k a b c d hr => G.ripe_core ((G.window_inv H k a b c d).1) hr, ?_, ?_, ?_⟩
  · intro k hk1 hkk0 hkK c hc
    have hp := (G.window_budget H k hk1 hkk0 hkK).2 c hc
    obtain ⟨ht, hG⟩ := hp
    have h1 := G.ok.tau_mono (show k ≤ S.tStar (H.pbk k c) by omega)
    have h2 := G.ok.W_nonneg (k + 1) (S.tStar (H.pbk k c))
    have h3 := G.ok.sigma_nonneg k
    have h4 := ((G.window_inv H k hk1 hkk0 hkK c).2.1).len_nonneg
    have h5 : (0 : ℝ) ≤ (H.pbk k c).nu := Nat.cast_nonneg _
    have h6 := G.bank_nonneg (H.pbk k c)
    have : 0 ≤ 2 * S.sigma k * (H.pbk k c).len := by positivity
    have hτ : S.tau k = 2 * S.A2 * S.lam k ^ S.p2 := rfl
    linarith
  · intro k hk1 hkk0 hkK c hr
    have hp := (G.window_budget H k hk1 hkk0 hkK).1 c
    obtain ⟨ht, hG⟩ := hp
    have hT : S.tStar (H.bk k c) = k := hr.2
    have hinv := (G.window_inv H k hk1 hkk0 hkK c).1
    have h2 := G.ok.W_nonneg (k + 1) k
    have h3 := G.ok.sigma_nonneg k
    have h4 := hinv.len_nonneg
    have h5 : (1 : ℝ) ≤ (H.bk k c).nu := by exact_mod_cast hinv.one_le_nu
    have h6 := G.bank_nonneg (H.bk k c)
    have : 0 ≤ 2 * S.sigma k * (H.bk k c).len := by positivity
    have hτ : S.tau k = 2 * S.A2 * S.lam k ^ S.p2 := rfl
    rw [hT] at hG
    linarith
  · intro k hkk0 hk1 hkK c hc
    have := hflat k hkk0 hk1 hkK c hc
    unfold CounterHist.H6flat at this
    have h2 := G.ok.W_nonneg (k + 1) khat
    have h3 := G.ok.sigma_nonneg k
    have h4 : 0 ≤ (H.bk k c).len := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact H.len_nonneg_succ (by omega) c
    have : 0 ≤ 2 * S.sigma k * (H.bk k c).len := by positivity
    linarith

end Setting.Good

end Balaban.LargeField
