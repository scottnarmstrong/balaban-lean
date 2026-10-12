module

public import Balaban.LargeField.Counter.Budget
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Auxiliary facts for the budget cases (Part I, §I.5.4)
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

theorem bank_nonneg (b : Book) : 0 ≤ S.bank b := by
  unfold Setting.bank
  have : 0 ≤ ∑ ξ ∈ b.M, S.tau ξ := Finset.sum_nonneg (fun ξ _ => G.ok.tau_nonneg ξ)
  linarith

theorem E_Phi_le_g (k : ℕ) : S.E (k + 1) + S.Phi (S.lam (k + 1)) + 1 ≤ S.g k := by
  have h1 := G.ok.E_le (k + 1)
  have h2 := G.lc.l2 (S.lam (k + 1)) (G.lam_ge (k + 1))
  have h3 := G.ok.lam_succ_le_two k
  have h4 : S.lam (k + 1) / 2 ≤ S.lam k := by linarith
  have h5 : (S.lam (k + 1) / 2) ^ (2 * S.p0) ≤ S.lam k ^ (2 * S.p0) :=
    pow_le_pow_left₀ (by have := G.ok.lam_pos (k + 1); positivity) h4 _
  have hA := G.ok.A3_pos
  unfold Setting.g
  nlinarith

theorem E_nonneg (j : ℕ) : 0 ≤ S.E j := G.ok.E_nonneg j

/-- `Σ_i (τ(t*_i) + W_μ(t*_i) + ν_i + U_i) ≥ m τ_μ` when all `t*_i ≥ μ`. -/
theorem sum_lower {ι : Type*} {μ : ℕ} {P : Finset ι} {f : ι → Book}
    (h : ∀ i ∈ P, μ ≤ S.tStar (f i)) :
    (P.card : ℝ) * S.tau μ ≤
      ∑ i ∈ P, (S.tau (S.tStar (f i)) + S.W μ (S.tStar (f i)) + (f i).nu + S.bank (f i)) := by
  have : ∑ i ∈ P, S.tau μ ≤
      ∑ i ∈ P, (S.tau (S.tStar (f i)) + S.W μ (S.tStar (f i)) + (f i).nu + S.bank (f i)) := by
    apply Finset.sum_le_sum
    intro i hi
    have h1 := G.ok.tau_mono (h i hi)
    have h2 := G.ok.W_nonneg μ (S.tStar (f i))
    have h3 : (0 : ℝ) ≤ (f i).nu := Nat.cast_nonneg _
    have h4 := G.bank_nonneg (f i)
    linarith
  simpa using this

/-- The restart bounds of Lemma I.5.3 for a restart output. -/
theorem restart_Phi {k : ℕ} {b' : Book} (hf : RestartFacts S k b') :
    S.lam (S.tStar b') ≤ S.cPrime * max (S.lam (k + 1)) (Real.logb S.L (max b'.len 1)) ∧
    ((S.tStar b' : ℕ) : ℝ) - (k + 1 : ℕ) + 1 ≤
      S.Ct * max (S.lam (k + 1)) (Real.logb S.L (max b'.len 1)) ∧
    S.tau (S.tStar b') + S.W (k + 1) (S.tStar b') ≤
      S.Phi (max (S.lam (k + 1)) (Real.logb S.L (max b'.len 1))) := by
  obtain ⟨ht, hs1, hs2, -, -⟩ := hf
  rw [ht]
  exact G.ok.restart_bounds hs1 hs2

end Setting.Good

end Balaban.LargeField
