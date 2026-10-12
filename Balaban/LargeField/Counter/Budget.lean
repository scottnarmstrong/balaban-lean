module

public import Balaban.LargeField.Counter.Hist
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The sufficient inequality (Part I, Lemma I.5.5)

`B7` is the inequality (B.7); `sufficient_B7` shows that it implies (H6′)^pre for the component.
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting

variable (S : Setting)

/-- The inequality (B.7) for a component with parts `P` (books `f`), `r` new cubes and
bookkeeping `b'`, at the step `k → k+1`. -/
def B7 (k : ℕ) {ι : Type*} (P : Finset ι) (f : ι → Book) (r : ℕ) (b' : Book) : Prop :=
  S.tau (S.tStar b') + S.W (k + 1) (S.tStar b') +
      (((P.card + r : ℕ) : ℝ) - 1) * S.E (k + 1) + b'.nu + S.bank b' ≤
    ∑ i ∈ P, (S.tau (S.tStar (f i)) + S.W (k + 1) (S.tStar (f i)) + (f i).nu + S.bank (f i)) +
      S.g k * r + S.v (k + 1) / S.L * ∑ i ∈ P, (f i).len

end Setting

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

/-- Lemma I.5.5: (B.7) implies (H6′)^pre. -/
theorem sufficient_B7 {k : ℕ} {ι : Type*} {P : Finset ι} {f : ι → Book} {r : ℕ} {b' : Book}
    {Gi : ι → ℝ} {Gpre vol : ℝ}
    (hGi : ∀ i ∈ P, S.tau (S.tStar (f i)) + 2 * S.sigma k * (f i).len +
      S.W (k + 1) (S.tStar (f i)) + (f i).nu + S.bank (f i) ≤ Gi i)
    (hbud : ∑ i ∈ P, Gi i + S.g k * r - S.cv * S.lam (k + 1) * vol ≤ Gpre)
    (hvol : vol ≤ S.CV * (S.rho (k + 1) : ℝ) ^ (S.d - 1) * (b'.len + S.rho (k + 1)))
    (hlen : b'.len ≤ ∑ i ∈ P, (f i).len / S.L + (((P.card + r : ℕ) : ℝ) - 1) * S.D (k + 1))
    (hn : 1 ≤ P.card + r) (hts : k + 1 ≤ S.tStar b') (hB7 : S.B7 k P f r b') :
    S.tau (S.tStar b') + 2 * S.sigma (k + 1) * b'.len + S.W (k + 2) (S.tStar b') + b'.nu +
      S.bank b' ≤ Gpre := by
  have hL : (2 : ℝ) ≤ S.L := G.ok.cast_L_ge
  have hL0 : (S.L : ℝ) ≠ 0 := by positivity
  set μ := k + 1 with hμ
  -- the cost of the volume
  have hcost : S.cv * S.lam μ * vol ≤ S.v μ * b'.len + S.w μ := by
    have h1 : 0 ≤ S.cv * S.lam μ := by
      have := G.ok.one_le_cv; have := G.ok.lam_pos μ; positivity
    calc S.cv * S.lam μ * vol ≤ S.cv * S.lam μ *
          (S.CV * (S.rho μ : ℝ) ^ (S.d - 1) * (b'.len + S.rho μ)) := by gcongr
      _ = S.v μ * b'.len + S.w μ := by
        simp only [Setting.w, Setting.v]; ring
  -- the reserve coefficient
  have hσ : 2 * S.sigma k = 2 * (S.L : ℝ)⁻¹ * (S.v μ + S.sigma μ) := by
    rw [G.ok.sigma_rec k]; ring
  have hsplit : S.W μ (S.tStar b') = S.w μ + S.W (μ + 1) (S.tStar b') :=
    S.W_split hts
  have hv0 := G.ok.v_nonneg μ
  have hσ0 := G.ok.sigma_nonneg μ
  have hn0 : (0 : ℝ) ≤ (((P.card + r : ℕ) : ℝ) - 1) := by
    have : (1 : ℝ) ≤ ((P.card + r : ℕ) : ℝ) := by exact_mod_cast hn
    linarith
  have hF2 := G.ok.v_add_two_sigma_D_le μ
  set A := ∑ i ∈ P, (f i).len with hA
  set n := (((P.card + r : ℕ) : ℝ) - 1) with hn_def
  set iL := (S.L : ℝ)⁻¹ with hiL
  have hsumdiv : ∑ i ∈ P, (f i).len / S.L = A * iL := by
    rw [← Finset.sum_div, div_eq_mul_inv]
  rw [hsumdiv] at hlen
  have hGsum : ∑ i ∈ P, (S.tau (S.tStar (f i)) + S.W μ (S.tStar (f i)) + (f i).nu +
      S.bank (f i)) + 2 * S.sigma k * A ≤ ∑ i ∈ P, Gi i := by
    have : ∑ i ∈ P, (S.tau (S.tStar (f i)) + 2 * S.sigma k * (f i).len +
        S.W μ (S.tStar (f i)) + (f i).nu + S.bank (f i)) ≤ ∑ i ∈ P, Gi i :=
      Finset.sum_le_sum hGi
    have e : ∑ i ∈ P, (S.tau (S.tStar (f i)) + 2 * S.sigma k * (f i).len +
        S.W μ (S.tStar (f i)) + (f i).nu + S.bank (f i)) =
        ∑ i ∈ P, (S.tau (S.tStar (f i)) + S.W μ (S.tStar (f i)) + (f i).nu +
          S.bank (f i)) + 2 * S.sigma k * A := by
      rw [hA, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    linarith
  have hD0 := S.D_nonneg μ
  have hkey : (S.v μ + 2 * S.sigma μ) * b'.len ≤
      (S.v μ + 2 * S.sigma μ) * (A * iL) + n * S.E μ := by
    have h1 : (S.v μ + 2 * S.sigma μ) * b'.len ≤
        (S.v μ + 2 * S.sigma μ) * (A * iL + n * S.D μ) := by
      gcongr
    have h2 : (S.v μ + 2 * S.sigma μ) * (n * S.D μ) ≤ n * S.E μ := by
      calc (S.v μ + 2 * S.sigma μ) * (n * S.D μ) = n * ((S.v μ + 2 * S.sigma μ) * S.D μ) := by
            ring
        _ ≤ n * S.E μ := by gcongr
    nlinarith
  unfold Setting.B7 at hB7
  rw [← hμ] at hB7
  rw [hsplit] at hB7
  have e1 : 2 * S.sigma k * A = 2 * iL * (S.v μ + S.sigma μ) * A := by rw [hσ]
  have hv : S.v μ / S.L = S.v μ * iL := by rw [div_eq_mul_inv]
  rw [hv] at hB7
  have hW2 : S.W (k + 2) (S.tStar b') = S.W (μ + 1) (S.tStar b') := rfl
  rw [hW2]
  nlinarith [hcost, hbud, hGsum, hkey, e1, hB7]

end Setting.Good

end Balaban.LargeField
