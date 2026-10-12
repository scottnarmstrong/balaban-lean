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

/-- The algebra behind Lemma I.5.5 and (I.6): if every part `i` guarantees `G_i ≥ c_i + 2σ_k ℓ_i`
and `C' + n E_μ ≤ ∑ c_i + g_k r + (v_μ/L) ∑ ℓ_i`, then `Gpre ≥ C' - w_μ + 2σ_μ ℓ'`. -/
theorem budget_core {k : ℕ} {ι : Type*} {P : Finset ι} {len : ι → ℝ} {c Gi : ι → ℝ}
    {r : ℕ} {len' C' Gpre vol : ℝ}
    (hGi : ∀ i ∈ P, c i + 2 * S.sigma k * len i ≤ Gi i)
    (hbud : ∑ i ∈ P, Gi i + S.g k * r - S.cv * S.lam (k + 1) * vol ≤ Gpre)
    (hvol : vol ≤ S.CV * (S.rho (k + 1) : ℝ) ^ (S.d - 1) * (len' + S.rho (k + 1)))
    (hlen : len' ≤ ∑ i ∈ P, len i / S.L + (((P.card + r : ℕ) : ℝ) - 1) * S.D (k + 1))
    (hn : 1 ≤ P.card + r)
    (hB : C' + (((P.card + r : ℕ) : ℝ) - 1) * S.E (k + 1) ≤
      ∑ i ∈ P, c i + S.g k * r + S.v (k + 1) / S.L * ∑ i ∈ P, len i) :
    C' - S.w (k + 1) + 2 * S.sigma (k + 1) * len' ≤ Gpre := by
  have hL : (2 : ℝ) ≤ S.L := G.ok.cast_L_ge
  have hL0 : (S.L : ℝ) ≠ 0 := by positivity
  set μ := k + 1 with hμ
  have hcost : S.cv * S.lam μ * vol ≤ S.v μ * len' + S.w μ := by
    have h1 : 0 ≤ S.cv * S.lam μ := by
      have := G.ok.one_le_cv; have := G.ok.lam_pos μ; positivity
    calc S.cv * S.lam μ * vol ≤ S.cv * S.lam μ *
          (S.CV * (S.rho μ : ℝ) ^ (S.d - 1) * (len' + S.rho μ)) := by gcongr
      _ = S.v μ * len' + S.w μ := by
        simp only [Setting.w, Setting.v]; ring
  have hσ : 2 * S.sigma k = 2 * (S.L : ℝ)⁻¹ * (S.v μ + S.sigma μ) := by
    rw [G.ok.sigma_rec k]; ring
  have hv0 := G.ok.v_nonneg μ
  have hσ0 := G.ok.sigma_nonneg μ
  have hn0 : (0 : ℝ) ≤ (((P.card + r : ℕ) : ℝ) - 1) := by
    have : (1 : ℝ) ≤ ((P.card + r : ℕ) : ℝ) := by exact_mod_cast hn
    linarith
  have hF2 := G.ok.v_add_two_sigma_D_le μ
  set A := ∑ i ∈ P, len i with hA
  set n := (((P.card + r : ℕ) : ℝ) - 1) with hn_def
  set iL := (S.L : ℝ)⁻¹ with hiL
  have hsumdiv : ∑ i ∈ P, len i / S.L = A * iL := by
    rw [← Finset.sum_div, div_eq_mul_inv]
  rw [hsumdiv] at hlen
  have hGsum : ∑ i ∈ P, c i + 2 * S.sigma k * A ≤ ∑ i ∈ P, Gi i := by
    have : ∑ i ∈ P, (c i + 2 * S.sigma k * len i) ≤ ∑ i ∈ P, Gi i := Finset.sum_le_sum hGi
    have e : ∑ i ∈ P, (c i + 2 * S.sigma k * len i) = ∑ i ∈ P, c i + 2 * S.sigma k * A := by
      rw [hA, Finset.mul_sum, Finset.sum_add_distrib]
    linarith
  have hD0 := S.D_nonneg μ
  have hkey : (S.v μ + 2 * S.sigma μ) * len' ≤
      (S.v μ + 2 * S.sigma μ) * (A * iL) + n * S.E μ := by
    have h1 : (S.v μ + 2 * S.sigma μ) * len' ≤
        (S.v μ + 2 * S.sigma μ) * (A * iL + n * S.D μ) := by
      gcongr
    have h2 : (S.v μ + 2 * S.sigma μ) * (n * S.D μ) ≤ n * S.E μ := by
      calc (S.v μ + 2 * S.sigma μ) * (n * S.D μ) = n * ((S.v μ + 2 * S.sigma μ) * S.D μ) := by
            ring
        _ ≤ n * S.E μ := by gcongr
    nlinarith
  have e1 : 2 * S.sigma k * A = 2 * iL * (S.v μ + S.sigma μ) * A := by rw [hσ]
  have hv : S.v μ / S.L = S.v μ * iL := by rw [div_eq_mul_inv]
  rw [hv] at hB
  nlinarith [hcost, hbud, hGsum, hkey, e1, hB]

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
  have hsplit : S.W (k + 1) (S.tStar b') = S.w (k + 1) + S.W (k + 1 + 1) (S.tStar b') :=
    S.W_split hts
  have := G.budget_core (P := P) (len := fun i => (f i).len)
    (c := fun i => S.tau (S.tStar (f i)) + S.W (k + 1) (S.tStar (f i)) + (f i).nu + S.bank (f i))
    (Gi := Gi) (r := r) (len' := b'.len)
    (C' := S.tau (S.tStar b') + S.W (k + 1) (S.tStar b') + b'.nu + S.bank b')
    (Gpre := Gpre) (vol := vol) (fun i hi => by have := hGi i hi; linarith) hbud hvol
    hlen hn (by unfold Setting.B7 at hB7; linarith)
  rw [hsplit] at this
  show S.tau (S.tStar b') + 2 * S.sigma (k + 1) * b'.len + S.W (k + 1 + 1) (S.tStar b') +
    b'.nu + S.bank b' ≤ Gpre
  linarith

end Setting.Good

end Balaban.LargeField
