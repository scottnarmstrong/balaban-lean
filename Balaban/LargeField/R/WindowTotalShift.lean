module

public import Balaban.LargeField.R.WindowShift
public import Balaban.LargeField.R.ZeroDomainScales
public import Balaban.LargeField.History.Scale
public import Balaban.LargeField.Counter.Growth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The total shift (Part III, Lemma III.1.7′): window numerics

Numerical consequences of the window data `k₁ + n_q(k₁) ≤ k < (k₁+1) + n_q(k₁+1)` and `s + n_2(s) ≤ k`
used in the bound of the total shift: `λ̂_k ≤ 2 c_* λ̂_{k₁}` (Lemma III.1.2 (a), (RQ4)) and
`L M R_base λ̂_s² ≤ L^{k-s}` (`k - s ≥ n_2(s)`, Lemma III.1.2 (d)).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

namespace Setting.Good

variable {S : Setting} (G : S.Good)
include G

/-- (RQ4): for a window with core `q`, `λ̂_k ≤ 2 c_* λ̂_q`. -/
theorem lam_le_two_cStar {k q : ℕ} (hq2 : k < (q + 1) + S.nq (q + 1)) : S.lam k ≤ 2 * S.cStar * S.lam q := by
  have ok := G.ok
  have h1 := ok.lam_mono hq2.le
  have h2 := ok.lam_add_nq (q + 1)
  have h3 := (ok.lam_step q).2
  have h4 := G.lc.l0_a (S.lam q) (G.lam_ge q)
  have hc := ok.cStar_ge_one
  have hθ : 0 < S.θp := ok.θp_pos
  have h5 : S.lam (q + 1) ≤ S.lam q + S.θp := by linarith
  have h6 : S.cStar * S.lam (q + 1) ≤ S.cStar * (S.lam q + S.θp) :=
    mul_le_mul_of_nonneg_left h5 (by linarith)
  have h7 : S.θp ≤ S.cStar * S.θp := by nlinarith
  have h8 : S.lam q ≤ S.cStar * S.lam q := by nlinarith [ok.lam_pos q]
  nlinarith

/-- `L M R_base λ̂_s² ≤ L M crit_s ≤ L^{k - s}` for `s + n_2(s) ≤ k`. -/
theorem pow_sub_ge {k s : ℕ} (hs : s + S.n2 s ≤ k) :
    (S.L : ℝ) * S.M * (S.Rb * S.lam s ^ 2) ≤ (S.L : ℝ) ^ (k - s) := by
  have ok := G.ok
  have h1 := ok.lt_pow_n2 s
  have h2 : (S.L : ℝ) ^ S.n2 s ≤ (S.L : ℝ) ^ (k - s) :=
    pow_le_pow_right₀ (by have := ok.two_le_L; exact_mod_cast (by omega : 1 ≤ S.L)) (by omega)
  have h3 : S.Rb * S.lam s ^ 2 ≤ (S.crit s : ℝ) := by
    have hr : S.Rb * S.lam s ^ 2 ≤ (S.r s : ℝ) := by unfold Setting.r; exact Nat.le_ceil _
    have : (S.r s : ℝ) ≤ S.crit s := by
      have h4 : S.r s ≤ S.rho s := by
        unfold Setting.rho; exact Nat.le_mul_of_pos_left _ ok.one_le_c0
      have h5 : S.rho s ≤ S.crit s := by unfold Setting.crit; omega
      exact_mod_cast h4.trans h5
    linarith
  have h1' : (S.L : ℝ) * S.M * S.crit s < (S.L : ℝ) ^ S.n2 s := by exact_mod_cast h1
  have hLM : (0 : ℝ) < S.L * S.M := by
    have := ok.cast_L_ge
    have : (1 : ℝ) ≤ S.M := by exact_mod_cast ok.one_le_M
    positivity
  calc (S.L : ℝ) * S.M * (S.Rb * S.lam s ^ 2) ≤ S.L * S.M * S.crit s :=
        mul_le_mul_of_nonneg_left h3 hLM.le
    _ ≤ (S.L : ℝ) ^ S.n2 s := h1'.le
    _ ≤ _ := h2

end Setting.Good

open Finset


/-- Geometric partial sums: `∑_{t<n} r^t ≤ 2 r^{n-1}` for `r ≥ 2`. -/
theorem geom_up_le {r : ℝ} (hr : 2 ≤ r) (n : ℕ) (hn : 1 ≤ n) :
    ∑ t ∈ range n, r ^ t ≤ 2 * r ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have ih' := ih (by omega)
    have h1 : (0 : ℝ) < r ^ m := by positivity
    have h2 : r ^ (m + 1) = r * r ^ m := by ring
    nlinarith

/-- Geometric tails: `∑_{j<n} q^j ≤ 2` for `0 ≤ q ≤ 1/2`. -/
theorem geom_down_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (n : ℕ) :
    ∑ j ∈ range n, q ^ j ≤ 2 := by
  have hgeom : (∑ t ∈ range n, q ^ t) * (1 - q) = 1 - q ^ n := geom_sum_mul_neg q n
  have hpow : 0 ≤ q ^ n := by positivity
  have h0 : 0 ≤ ∑ t ∈ range n, q ^ t := sum_nonneg fun t _ => by positivity
  nlinarith

/-- **The crossover estimate**: if `min (A r^t, B q^t) ≤ v` for all `t`, with `r ≥ 2`, `0 < q ≤ 1/2`, `A, B > 0`,
then `∑_{t<n} min (A r^t, B q^t) ≤ 4 v`. -/
theorem crossover_sum {A B r q v : ℝ} (hA : 0 < A) (hB : 0 < B) (hr : 2 ≤ r) (hq0 : 0 < q)
    (hq : q ≤ 1 / 2) (hv0 : 0 ≤ v) (n : ℕ)
    (hv : ∀ t : ℕ, t < n → min (A * r ^ t) (B * q ^ t) ≤ v) :
    ∑ t ∈ range n, min (A * r ^ t) (B * q ^ t) ≤ 4 * v := by
  have hr1 : 1 ≤ r := by linarith
  classical
  by_cases hex : ∃ t, B * q ^ t < A * r ^ t
  · set ts := Nat.find hex with hts
    have hts_spec : B * q ^ ts < A * r ^ ts := Nat.find_spec hex
    have hbefore : ∀ t < ts, A * r ^ t ≤ B * q ^ t := fun t ht => not_lt.mp (Nat.find_min hex ht)
    have hafter : ∀ t, ts ≤ t → B * q ^ t < A * r ^ t := by
      intro t ht
      have h1 : A * r ^ ts ≤ A * r ^ t := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr1 ht) hA.le
      have h2 : B * q ^ t ≤ B * q ^ ts :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0.le (by linarith) ht) hB.le
      linarith
    -- split the sum at `m' = min n ts`
    set m' := min n ts with hm'
    have hsplit : ∑ t ∈ range n, min (A * r ^ t) (B * q ^ t) =
        ∑ t ∈ range m', A * r ^ t + ∑ t ∈ Ico m' n, B * q ^ t := by
      rw [← sum_range_add_sum_Ico _ (min_le_left n ts)]
      congr 1
      · exact sum_congr rfl fun t ht => min_eq_left (hbefore t (lt_of_lt_of_le (mem_range.mp ht) (min_le_right _ _)))
      · refine sum_congr rfl fun t ht => ?_
        have : ts ≤ t := by
          have ht' := mem_Ico.mp ht
          simp only [hm'] at ht'
          omega
        exact min_eq_right (hafter t this).le
    rw [hsplit]
    have hfirst : ∑ t ∈ range m', A * r ^ t ≤ 2 * v := by
      by_cases h0 : m' = 0
      · rw [h0]; simp; linarith
      · rw [← mul_sum]
        have h1 := geom_up_le hr m' (Nat.pos_of_ne_zero h0)
        have h2 : A * r ^ (m' - 1) ≤ v := by
          have hlt : m' - 1 < ts := by have := min_le_right n ts; omega
          have := hv (m' - 1) (by have := min_le_left n ts; omega)
          rwa [min_eq_left (hbefore _ hlt)] at this
        calc A * ∑ t ∈ range m', r ^ t ≤ A * (2 * r ^ (m' - 1)) := mul_le_mul_of_nonneg_left h1 hA.le
          _ = 2 * (A * r ^ (m' - 1)) := by ring
          _ ≤ 2 * v := by linarith
    have hsecond : ∑ t ∈ Ico m' n, B * q ^ t ≤ 2 * v := by
      by_cases hmn : m' < n
      · have hm'ts : m' = ts := by
          have := min_le_right n ts
          have : m' = min n ts := rfl
          omega
        rw [sum_Ico_eq_sum_range]
        have : ∀ j ∈ range (n - m'), B * q ^ (m' + j) = (B * q ^ m') * q ^ j := fun j _ => by
          rw [pow_add]; ring
        rw [sum_congr rfl this, ← mul_sum]
        have hbound : B * q ^ m' ≤ v := by
          have := hv ts (by have := min_le_right n ts; omega)
          rw [min_eq_right (hafter ts le_rfl).le] at this
          rwa [hm'ts]
        calc (B * q ^ m') * ∑ j ∈ range (n - m'), q ^ j ≤ (B * q ^ m') * 2 :=
              mul_le_mul_of_nonneg_left (geom_down_le hq0.le hq _) (by positivity)
          _ ≤ 2 * v := by linarith
      · rw [Ico_eq_empty (by omega)]; simp; linarith
    linarith
  · push Not at hex
    -- all terms are `A r^t`
    have : ∀ t, min (A * r ^ t) (B * q ^ t) = A * r ^ t := fun t => min_eq_left (hex t)
    simp_rw [this]
    by_cases h0 : n = 0
    · subst h0; simp; linarith
    · rw [← mul_sum]
      have h1 := geom_up_le hr n (Nat.pos_of_ne_zero h0)
      have h2 : A * r ^ (n - 1) ≤ v := by
        have := hv (n - 1) (by omega)
        rwa [min_eq_left (hex _)] at this
      calc A * ∑ t ∈ range n, r ^ t ≤ A * (2 * r ^ (n - 1)) := mul_le_mul_of_nonneg_left h1 hA.le
        _ = 2 * (A * r ^ (n - 1)) := by ring
        _ ≤ 4 * v := by linarith

/-- **The layer sum of (III.1.8)** (pure arithmetic): with `t = k - 1 - n`, `K r^t V_n` is bounded by
`K M_c (r w)^t` for `n + 1 ≥ s` and by `K min (A r^t, B (r w)^t)` for `n + 1 < s`. -/
theorem layer_total_le {k1 k s : ℕ} (hsk : s ≤ k) {V : ℕ → ℝ} {K r w Mcd ν v : ℝ} (hr : 2 ≤ r) (hw : 0 < w)
    (hq : r * w ≤ 1 / 2) (hK : 0 ≤ K) (hMcd : 0 < Mcd) (hν : 0 < ν) (hv0 : 0 ≤ v)
    (hV1 : ∀ n, k1 ≤ n → n < k → s ≤ n + 1 → V n ≤ Mcd * w ^ (k - n - 1))
    (hV2 : ∀ n, k1 ≤ n → n < k → n + 1 < s →
      V n ≤ min (Mcd * w ^ (k - s)) (ν * Mcd * w ^ (k - n - 1)))
    (hv : ∀ t : ℕ, k - s < t → t < k - k1 →
      min (Mcd * w ^ (k - s) * r ^ t) (ν * Mcd * (r * w) ^ t) ≤ v) :
    ∑ n ∈ Ico k1 k, K * r ^ (k - n - 1) * V n ≤ 2 * K * Mcd + 4 * K * v := by
  have hr0 : 0 < r := by linarith
  have hq0 : 0 < r * w := mul_pos hr0 hw
  have hreflect : ∑ n ∈ Ico k1 k, K * r ^ (k - n - 1) * V n =
      ∑ t ∈ range (k - k1), K * r ^ t * V (k - 1 - t) := by
    refine Finset.sum_nbij' (fun n => k - 1 - n) (fun t => k - 1 - t) ?_ ?_ ?_ ?_ ?_
    · intro n hn; simp only [mem_Ico, mem_range] at hn ⊢; omega
    · intro t ht; simp only [mem_Ico, mem_range] at ht ⊢; omega
    · intro n hn; simp only [mem_Ico] at hn; omega
    · intro t ht; simp only [mem_range] at ht; omega
    · intro n hn
      simp only [mem_Ico] at hn
      have h1 : k - 1 - (k - 1 - n) = n := by omega
      have h2 : k - n - 1 = k - 1 - n := by omega
      rw [h1, h2]
  rw [hreflect]
  -- termwise
  have hterm : ∀ t ∈ range (k - k1), K * r ^ t * V (k - 1 - t) ≤
      K * Mcd * (r * w) ^ t +
        (if k - s < t then K * min (Mcd * w ^ (k - s) * r ^ t) (ν * Mcd * (r * w) ^ t) else 0) := by
    intro t ht
    have ht' := mem_range.mp ht
    have hn1 : k1 ≤ k - 1 - t := by omega
    have hn2 : k - 1 - t < k := by omega
    have hkn : k - (k - 1 - t) - 1 = t := by omega
    have hI : 0 ≤ K * Mcd * (r * w) ^ t := by positivity
    by_cases hc : s ≤ k - 1 - t + 1
    · have := hV1 _ hn1 hn2 hc
      rw [hkn] at this
      have hnot : ¬ (k - s < t) := by omega
      simp only [hnot, ↓reduceIte, add_zero]
      calc K * r ^ t * V (k - 1 - t) ≤ K * r ^ t * (Mcd * w ^ t) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = K * Mcd * (r * w) ^ t := by rw [mul_pow]; ring
    · push Not at hc
      have := hV2 _ hn1 hn2 hc
      rw [hkn] at this
      have hyes : k - s < t := by omega
      simp only [hyes, ↓reduceIte]
      calc K * r ^ t * V (k - 1 - t) ≤ K * r ^ t * min (Mcd * w ^ (k - s)) (ν * Mcd * w ^ t) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = K * min (Mcd * w ^ (k - s) * r ^ t) (ν * Mcd * (r * w) ^ t) := by
            rw [mul_pow]
            have e : K * r ^ t * min (Mcd * w ^ (k - s)) (ν * Mcd * w ^ t) =
                K * (r ^ t * min (Mcd * w ^ (k - s)) (ν * Mcd * w ^ t)) := by ring
            rw [e, mul_min_of_nonneg _ _ (by positivity : 0 ≤ r ^ t)]
            congr 2 <;> ring
        _ ≤ _ := le_add_of_nonneg_left hI
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, ← mul_sum]
  have h1 : ∑ t ∈ range (k - k1), (r * w) ^ t ≤ 2 := geom_down_le hq0.le hq _
  -- the second sum
  have h2 : ∑ t ∈ range (k - k1),
      (if k - s < t then K * min (Mcd * w ^ (k - s) * r ^ t) (ν * Mcd * (r * w) ^ t) else 0) ≤ 4 * K * v := by
    rw [← sum_filter]
    have hfil : (range (k - k1)).filter (fun t => k - s < t) = Ico (k - s + 1) (k - k1) := by
      ext t; simp only [mem_filter, mem_range, mem_Ico]; omega
    rw [hfil, ← mul_sum, sum_Ico_eq_sum_range]
    have hA : 0 < Mcd * w ^ (k - s) * r ^ (k - s + 1) := by positivity
    have hB : 0 < ν * Mcd * (r * w) ^ (k - s + 1) := by positivity
    have h3 := crossover_sum hA hB hr hq0 hq hv0 (k - k1 - (k - s + 1)) (fun j hj => by
      have := hv (k - s + 1 + j) (by omega) (by omega)
      have e1 : Mcd * w ^ (k - s) * r ^ (k - s + 1 + j) =
          Mcd * w ^ (k - s) * r ^ (k - s + 1) * r ^ j := by rw [pow_add]; ring
      have e2 : ν * Mcd * (r * w) ^ (k - s + 1 + j) =
          ν * Mcd * (r * w) ^ (k - s + 1) * (r * w) ^ j := by rw [pow_add]; ring
      rw [e1, e2] at this
      exact this)
    have e3 : ∑ j ∈ range (k - k1 - (k - s + 1)),
        min (Mcd * w ^ (k - s) * r ^ (k - s + 1 + j)) (ν * Mcd * (r * w) ^ (k - s + 1 + j)) =
        ∑ j ∈ range (k - k1 - (k - s + 1)),
          min (Mcd * w ^ (k - s) * r ^ (k - s + 1) * r ^ j)
            (ν * Mcd * (r * w) ^ (k - s + 1) * (r * w) ^ j) := by
      refine sum_congr rfl fun j _ => ?_
      rw [pow_add, pow_add]; congr 1 <;> ring
    rw [e3]
    nlinarith [mul_le_mul_of_nonneg_left h3 hK]
  nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hK hMcd.le)]

namespace BlockTree

variable {m k1 k : ℕ}

theorem sum_shiftBar_le {ι : Type*} (Zs : Finset ι) (B : ι → BlockTree m k1 k) (zf : ℕ → ℝ)
    (ς : ℕ → ℝ) (hς : ∀ n, k1 ≤ n → n < k → |varpi k zf n - 1| ≤ ς n) :
    ∑ z ∈ Zs, (B z).shiftBar zf ≤
      ∑ n ∈ Finset.Ico k1 k, ς n * ∑ z ∈ Zs, (B z).layerFrac n := by
  calc ∑ z ∈ Zs, (B z).shiftBar zf ≤ ∑ z ∈ Zs, ∑ n ∈ Finset.Ico k1 k, (B z).layerFrac n * ς n :=
        Finset.sum_le_sum fun z _ => (B z).shiftBar_le_layers zf ς hς
    _ = ∑ n ∈ Finset.Ico k1 k, ς n * ∑ z ∈ Zs, (B z).layerFrac n := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => mul_comm _ _

end BlockTree


section Real

open Real

/-- The coefficient bound of (III.1.8): `β_k ε_k ς_n ≤ 18 e^ε α₀² c_ξ L^{(k-n-1)(α+2γ)}`. -/
theorem coeff_layer_le {ℓ d α γ ε α0 cξ β βk εk : ℝ} {k n : ℕ} (hℓ : 0 < ℓ)
    (hα : α + γ = (d - 2) / 2) (hα0 : 0 ≤ α0) (hcξ : 0 ≤ cξ) (hβ : 0 < β) (hεk0 : 0 ≤ εk)
    (hβk : βk ≤ Real.exp ε * β * ℓ ^ ((k : ℝ) * (d - 2))) (hεk : εk ≤ 3 * α0 * ℓ ^ (-((k : ℝ) * α)))
    (hnk : n < k) :
    βk * εk * (6 * α0 * cξ / β * ℓ ^ (-(((n : ℝ) + 1) * (α + 2 * γ)))) ≤
      18 * Real.exp ε * α0 ^ 2 * cξ * (ℓ ^ (α + 2 * γ)) ^ (k - n - 1) := by
  have hexp : ((k : ℝ) * (d - 2)) + (-((k : ℝ) * α)) + (-(((n : ℝ) + 1) * (α + 2 * γ))) =
      ((k - n - 1 : ℕ) : ℝ) * (α + 2 * γ) := by
    have hk : ((k - n - 1 : ℕ) : ℝ) = (k : ℝ) - n - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [hk]
    have : d - 2 = 2 * (α + γ) := by linarith
    rw [this]; ring
  have h1 : βk * εk ≤ (Real.exp ε * β * ℓ ^ ((k : ℝ) * (d - 2))) * (3 * α0 * ℓ ^ (-((k : ℝ) * α))) :=
    mul_le_mul hβk hεk hεk0 (by positivity)
  have h2 : (ℓ ^ (α + 2 * γ)) ^ (k - n - 1) = ℓ ^ (((k - n - 1 : ℕ) : ℝ) * (α + 2 * γ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ.le, mul_comm]
  have hnn : 0 ≤ 6 * α0 * cξ / β * ℓ ^ (-(((n : ℝ) + 1) * (α + 2 * γ))) := by positivity
  calc βk * εk * (6 * α0 * cξ / β * ℓ ^ (-(((n : ℝ) + 1) * (α + 2 * γ))))
      ≤ ((Real.exp ε * β * ℓ ^ ((k : ℝ) * (d - 2))) * (3 * α0 * ℓ ^ (-((k : ℝ) * α)))) *
        (6 * α0 * cξ / β * ℓ ^ (-(((n : ℝ) + 1) * (α + 2 * γ)))) := mul_le_mul_of_nonneg_right h1 hnn
    _ = 18 * Real.exp ε * α0 ^ 2 * cξ *
        (ℓ ^ ((k : ℝ) * (d - 2)) * ℓ ^ (-((k : ℝ) * α)) * ℓ ^ (-(((n : ℝ) + 1) * (α + 2 * γ)))) := by
        field_simp
        ring
    _ = _ := by rw [← Real.rpow_add hℓ, ← Real.rpow_add hℓ, hexp, h2]

theorem min_le_rpow_mul {X Y θ : ℝ} (hX : 0 < X) (hY : 0 < Y) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    min X Y ≤ X ^ θ * Y ^ (1 - θ) := by
  have hm : 0 < min X Y := lt_min hX hY
  calc min X Y = min X Y ^ θ * min X Y ^ (1 - θ) := by
        rw [← Real.rpow_add hm]; simp
    _ ≤ X ^ θ * Y ^ (1 - θ) :=
        mul_le_mul (Real.rpow_le_rpow hm.le (min_le_left _ _) hθ0)
          (Real.rpow_le_rpow hm.le (min_le_right _ _) (by linarith)) (by positivity) (by positivity)

/-- The crossover value: `min (A r^t, B (r w)^t) ≤ M_c ℓ^{-N (d - a)} ν^{a/d}` for `A = M_c w^N`, `B = ν M_c`,
`r = ℓ^a`, `w = ℓ^{-d}`. -/
theorem min_term_le {ℓ d a Mcd ν : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (ha0 : 0 ≤ a) (had : a ≤ d)
    (hMcd : 0 < Mcd) (hν : 0 < ν) (N t : ℕ) :
    min (Mcd * (ℓ ^ (-d)) ^ N * (ℓ ^ a) ^ t) (ν * Mcd * (ℓ ^ a * ℓ ^ (-d)) ^ t) ≤
      Mcd * ℓ ^ (-((N : ℝ) * (d - a))) * ν ^ (a / d) := by
  set θ : ℝ := (d - a) / d with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hd.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hd]; linarith
  have h1θ : 1 - θ = a / d := by rw [hθ]; field_simp; ring
  set X := Mcd * (ℓ ^ (-d)) ^ N * (ℓ ^ a) ^ t with hX
  set Y := ν * Mcd * (ℓ ^ a * ℓ ^ (-d)) ^ t with hY
  have hX0 : 0 < X := by positivity
  have hY0 : 0 < Y := by positivity
  refine (min_le_rpow_mul hX0 hY0 hθ0 hθ1).trans (le_of_eq ?_)
  -- evaluate `X^θ Y^(1-θ)`
  have e1 : (ℓ ^ a) ^ t = ℓ ^ ((t : ℝ) * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ.le]; congr 1; ring
  have e2 : (ℓ ^ a * ℓ ^ (-d)) ^ t = ℓ ^ ((t : ℝ) * (a - d)) := by
    rw [← Real.rpow_add hℓ, ← Real.rpow_natCast, ← Real.rpow_mul hℓ.le]; congr 1; ring
  have e3 : (ℓ ^ (-d)) ^ N = ℓ ^ (-((N : ℝ) * d)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ.le]; congr 1; ring
  have hXe : X = Mcd * ℓ ^ (-((N : ℝ) * d) + (t : ℝ) * a) := by
    rw [hX, e1, e3, Real.rpow_add hℓ]; ring
  have hYe : Y = (ν * Mcd) * ℓ ^ ((t : ℝ) * (a - d)) := by rw [hY, e2]
  rw [hXe, hYe, Real.mul_rpow hMcd.le (Real.rpow_nonneg hℓ.le _),
    Real.mul_rpow (mul_pos hν hMcd).le (Real.rpow_nonneg hℓ.le _),
    ← Real.rpow_mul hℓ.le, ← Real.rpow_mul hℓ.le, Real.mul_rpow hν.le hMcd.le]
  -- collect powers of `Mcd`, `ν`, `ℓ`
  have hexp : (-((N : ℝ) * d) + (t : ℝ) * a) * θ + (t : ℝ) * (a - d) * (1 - θ) =
      -((N : ℝ) * (d - a)) := by
    rw [h1θ, hθ]; field_simp; ring
  have hMc : Mcd ^ θ * Mcd ^ (1 - θ) = Mcd := by
    rw [← Real.rpow_add hMcd]; simp
  calc Mcd ^ θ * (ℓ ^ ((-((N : ℝ) * d) + (t : ℝ) * a) * θ)) *
        (ν ^ (1 - θ) * Mcd ^ (1 - θ) * ℓ ^ ((t : ℝ) * (a - d) * (1 - θ)))
      = (Mcd ^ θ * Mcd ^ (1 - θ)) * ν ^ (1 - θ) *
        (ℓ ^ ((-((N : ℝ) * d) + (t : ℝ) * a) * θ) * ℓ ^ ((t : ℝ) * (a - d) * (1 - θ))) := by ring
    _ = Mcd * ν ^ (a / d) * ℓ ^ (-((N : ℝ) * (d - a))) := by
        rw [hMc, ← Real.rpow_add hℓ, hexp, h1θ]
    _ = _ := by ring

/-- The crossover value is `≤ P X₀^{-(d+1)/2} (2C_ν)^{1/2} λ^{2d+1}`. -/
theorem v_bound {ℓ lam X0 P Cν2 Mcd ν a : ℝ} {d N : ℕ} (hℓ : 1 ≤ ℓ) (hlam : 1 ≤ lam) (hd : 1 ≤ d)
    (ha0 : 0 ≤ a) (ha : a ≤ ((d : ℝ) - 1) / 2) (hX0 : 0 < X0) (hCν : 0 < Cν2) (hP : 0 ≤ P)
    (hMcd : Mcd ≤ P * lam ^ (2 * d)) (hν1 : 1 ≤ ν)
    (hν : ν ≤ Cν2 * lam ^ (2 * d + 3)) (hX : X0 * lam ^ 2 ≤ ℓ ^ N) :
    Mcd * ℓ ^ (-((N : ℝ) * ((d : ℝ) - a))) * ν ^ (a / (d : ℝ)) ≤
      P * X0 ^ (-(((d : ℝ) + 1) / 2)) * Cν2 ^ ((1 : ℝ) / 2) * lam ^ (2 * d + 1) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hlam0 : 0 < lam := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set e : ℝ := ((d : ℝ) + 1) / 2 with he
  have he0 : 0 < e := by positivity
  -- the `ℓ` factor
  have h1 : ℓ ^ (-((N : ℝ) * ((d : ℝ) - a))) ≤ ℓ ^ (-((N : ℝ) * e)) := by
    refine Real.rpow_le_rpow_of_exponent_le hℓ ?_
    have : (e : ℝ) ≤ (d : ℝ) - a := by rw [he]; linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have h2 : ℓ ^ (-((N : ℝ) * e)) = (ℓ ^ N) ^ (-e) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ0.le]; congr 1; ring
  have hXpos : 0 < X0 * lam ^ 2 := by positivity
  have h3 : (ℓ ^ N) ^ (-e) ≤ (X0 * lam ^ 2) ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos hXpos hX (by linarith)
  have h4 : (X0 * lam ^ 2) ^ (-e) = X0 ^ (-e) * lam ^ (-(2 * e)) := by
    rw [Real.mul_rpow hX0.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hlam0.le]
    congr 2; push_cast; ring
  -- the `ν` factor
  have hexp12 : a / (d : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hd0]; linarith
  have h5 : ν ^ (a / (d : ℝ)) ≤ ν ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hν1 hexp12
  have h6 : ν ^ ((1 : ℝ) / 2) ≤ (Cν2 * lam ^ (2 * d + 3)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (by linarith) hν (by norm_num)
  have h7 : (Cν2 * lam ^ (2 * d + 3)) ^ ((1 : ℝ) / 2) =
      Cν2 ^ ((1 : ℝ) / 2) * lam ^ (((2 * d + 3 : ℕ) : ℝ) / 2) := by
    rw [Real.mul_rpow hCν.le (by positivity), ← Real.rpow_natCast lam (2 * d + 3),
      ← Real.rpow_mul hlam0.le]; congr 2; ring
  -- assemble
  have hnn1 : 0 ≤ ℓ ^ (-((N : ℝ) * ((d : ℝ) - a))) := by positivity
  have hnn2 : 0 ≤ ν ^ (a / (d : ℝ)) := by positivity
  calc Mcd * ℓ ^ (-((N : ℝ) * ((d : ℝ) - a))) * ν ^ (a / (d : ℝ))
      ≤ (P * lam ^ (2 * d)) * (X0 ^ (-e) * lam ^ (-(2 * e))) *
        (Cν2 ^ ((1 : ℝ) / 2) * lam ^ (((2 * d + 3 : ℕ) : ℝ) / 2)) := by
        refine mul_le_mul (mul_le_mul hMcd (h1.trans (h2 ▸ h3 |>.trans h4.le)) hnn1 (by positivity))
          (h5.trans (h6.trans h7.le)) hnn2 (by positivity)
    _ = P * X0 ^ (-e) * Cν2 ^ ((1 : ℝ) / 2) *
        (lam ^ (2 * d) * lam ^ (-(2 * e)) * lam ^ (((2 * d + 3 : ℕ) : ℝ) / 2)) := by ring
    _ ≤ P * X0 ^ (-e) * Cν2 ^ ((1 : ℝ) / 2) * lam ^ (2 * d + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Real.rpow_natCast lam (2 * d), ← Real.rpow_add hlam0, ← Real.rpow_add hlam0,
          ← Real.rpow_natCast lam (2 * d + 1)]
        refine Real.rpow_le_rpow_of_exponent_le hlam ?_
        rw [he]; push_cast; linarith

end Real


/-- The explicit constant `C_ϑ` of (III.1.8). -/
noncomputable def totalShiftConst (S : Setting) (ε α0 cξ : ℝ) : ℝ :=
  18 * Real.exp ε * α0 ^ 2 * cξ *
    (2 * (((S.M : ℝ) * (2 * S.c0 * (S.Rb + 1) + 10)) ^ S.d) +
      4 * (((S.M : ℝ) * (2 * S.c0 * (S.Rb + 1) + 10)) ^ S.d) *
        (((S.L : ℝ) * S.M * S.Rb / (4 * S.cStar ^ 2)) ^ (-(((S.d : ℝ) + 1) / 2)) *
          (2 * S.Cν) ^ ((1 : ℝ) / 2)))

section Reduction

open Real

/-- Reduction of the total shift to the layer sum `∑_n K r^{k-n-1} V_n`, `V_n = ∑_z f_n(z)`. -/
theorem totalShift_reduce {ι : Type*} {m k1 k : ℕ} (Zs : Finset ι) (B : ι → BlockTree m k1 k)
    (zf : ℕ → ℝ) {ℓ d α γ ε α0 cξ β βk εk : ℝ} (hℓ0 : 0 < ℓ) (hαγ : α + γ = (d - 2) / 2)
    (hα0 : 0 ≤ α0) (hcξ : 0 ≤ cξ) (hβ : 0 < β) (hβk0 : 0 ≤ βk) (hεk0 : 0 ≤ εk)
    (hβk : βk ≤ Real.exp ε * β * ℓ ^ ((k : ℝ) * (d - 2))) (hεk : εk ≤ 3 * α0 * ℓ ^ (-((k : ℝ) * α)))
    (hς : ∀ n, k1 ≤ n → n < k → |varpi k zf n - 1| ≤
      6 * α0 * cξ / β * ℓ ^ (-(((n : ℝ) + 1) * (α + 2 * γ)))) :
    βk * εk * ∑ z ∈ Zs, (B z).shiftBar zf ≤
      ∑ n ∈ Finset.Ico k1 k, (18 * Real.exp ε * α0 ^ 2 * cξ) * (ℓ ^ (α + 2 * γ)) ^ (k - n - 1) *
        ∑ z ∈ Zs, (B z).layerFrac n := by
  have h1 := BlockTree.sum_shiftBar_le Zs B zf
    (fun n => 6 * α0 * cξ / β * ℓ ^ (-(((n : ℝ) + 1) * (α + 2 * γ)))) hς
  calc βk * εk * ∑ z ∈ Zs, (B z).shiftBar zf ≤ βk * εk * ∑ n ∈ Finset.Ico k1 k,
        (6 * α0 * cξ / β * ℓ ^ (-(((n : ℝ) + 1) * (α + 2 * γ)))) * ∑ z ∈ Zs, (B z).layerFrac n :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hβk0 hεk0)
    _ = ∑ n ∈ Finset.Ico k1 k, (βk * εk * (6 * α0 * cξ / β * ℓ ^ (-(((n : ℝ) + 1) * (α + 2 * γ))))) *
        ∑ z ∈ Zs, (B z).layerFrac n := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn' := Finset.mem_Ico.mp hn
        exact mul_le_mul_of_nonneg_right
          (coeff_layer_le hℓ0 hαγ hα0 hcξ hβ hεk0 hβk hεk hn'.2)
          (Finset.sum_nonneg fun z _ => (B z).layerFrac_nonneg n)

/-- Final arithmetic, small `s`. -/
theorem total_final_small {K P Y Mcd lam : ℝ} {n : ℕ} (hK : 0 ≤ K) (hP : 0 ≤ P) (_hY : 0 ≤ Y)
    (hlam : 1 ≤ lam) (hM : Mcd ≤ P * lam ^ n) :
    2 * K * Mcd + 4 * K * 0 ≤ K * (2 * P + 4 * P * Y) * lam ^ (n + 1) := by
  have hl0 : 0 ≤ lam := by linarith
  have hpow : lam ^ n ≤ lam ^ (n + 1) := pow_le_pow_right₀ hlam (Nat.le_succ _)
  have e1 : 2 * K * Mcd ≤ 2 * K * (P * lam ^ n) :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  have e2 : 2 * K * (P * lam ^ n) ≤ 2 * K * (P * lam ^ (n + 1)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hP) (by positivity)
  have e3 : K * (2 * P + 4 * P * Y) * lam ^ (n + 1) =
      2 * K * (P * lam ^ (n + 1)) + 4 * K * P * Y * lam ^ (n + 1) := by ring
  have e4 : 0 ≤ 4 * K * P * Y * lam ^ (n + 1) := by positivity
  linarith

/-- Final arithmetic, large `s`. -/
theorem total_final_big {K P Y Mcd v lam : ℝ} {n : ℕ} (hK : 0 ≤ K) (hP : 0 ≤ P) (hY : 0 ≤ Y)
    (hlam : 1 ≤ lam) (hM : Mcd ≤ P * lam ^ n) (hv : v ≤ P * Y * lam ^ (n + 1)) :
    2 * K * Mcd + 4 * K * v ≤ K * (2 * P + 4 * P * Y) * lam ^ (n + 1) := by
  have hl0 : 0 ≤ lam := by linarith
  have hpow : lam ^ n ≤ lam ^ (n + 1) := pow_le_pow_right₀ hlam (Nat.le_succ _)
  have e1 : 2 * K * Mcd ≤ 2 * K * (P * lam ^ n) :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  have e2 : 2 * K * (P * lam ^ n) ≤ 2 * K * (P * lam ^ (n + 1)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hP) (by positivity)
  have e3 : 4 * K * v ≤ 4 * K * (P * Y * lam ^ (n + 1)) :=
    mul_le_mul_of_nonneg_left hv (by positivity)
  have e4 : K * (2 * P + 4 * P * Y) * lam ^ (n + 1) =
      2 * K * (P * lam ^ (n + 1)) + 4 * K * (P * Y * lam ^ (n + 1)) := by ring
  linarith

end Reduction

namespace Setting.Good

variable {S : Setting} (G : S.Good)
include G

open Real in
/-- `(M crit_k)^d ≤ ((M c') )^d λ̂_k^{2d}`. -/
theorem Mcd_le (k : ℕ) :
    ((S.M : ℝ) * S.crit k) ^ S.d ≤
      (((S.M : ℝ) * (2 * S.c0 * (S.Rb + 1) + 10)) ^ S.d) * S.lam k ^ (2 * S.d) := by
  have ok := G.ok
  have h1 : (S.crit k : ℝ) ≤ (2 * S.c0 * (S.Rb + 1) + 10) * S.lam k ^ 2 := ok.hatW_crit_le k
  have h2 : (S.M : ℝ) * S.crit k ≤ ((S.M : ℝ) * (2 * S.c0 * (S.Rb + 1) + 10)) * S.lam k ^ 2 := by
    calc (S.M : ℝ) * S.crit k ≤ S.M * ((2 * S.c0 * (S.Rb + 1) + 10) * S.lam k ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have hc' : 0 ≤ (2 * S.c0 * (S.Rb + 1) + 10 : ℝ) := by
    have := ok.two_le_Rb; positivity
  calc ((S.M : ℝ) * S.crit k) ^ S.d ≤ (((S.M : ℝ) * (2 * S.c0 * (S.Rb + 1) + 10)) * S.lam k ^ 2) ^ S.d :=
        pow_le_pow_left₀ (by positivity) h2 _
    _ = _ := by rw [mul_pow, ← pow_mul]

open Real in
/-- The bound on the crossover value `v` (Lemma III.1.7′, last step), for `s ≥ k₁ + 2`. -/
theorem crossover_value_le {k1 k s : ℕ} {γ : ℝ} (hγ2 : γ ≤ 1 / 2) (hγ : 0 < γ)
    (hα : S.α = ((S.d : ℝ) - 2) / 2 - γ) (hp2 : S.p2 = 2 * S.d + 3)
    (hcore : k < (k1 + 1) + S.nq (k1 + 1)) (hs : s + S.n2 s ≤ k) (hs2 : k1 + 2 ≤ s) :
    ((((S.M : ℝ) * S.crit k) ^ S.d) * (S.L : ℝ) ^ (-(((k - s : ℕ) : ℝ) * ((S.d : ℝ) - (S.α + 2 * γ)))) *
        (S.numax k : ℝ) ^ ((S.α + 2 * γ) / (S.d : ℝ))) ≤
      (((S.M : ℝ) * (2 * S.c0 * (S.Rb + 1) + 10)) ^ S.d) *
        ((S.L : ℝ) * S.M * S.Rb / (4 * S.cStar ^ 2)) ^ (-(((S.d : ℝ) + 1) / 2)) *
        (2 * S.Cν) ^ ((1 : ℝ) / 2) * S.lam k ^ (2 * S.d + 1) := by
  have ok := G.ok
  have hL2 := ok.two_le_L
  have hℓ1 : (1 : ℝ) < S.L := by exact_mod_cast (by omega : 1 < S.L)
  have hd3 := ok.three_le_d
  have hd3' : (3 : ℝ) ≤ S.d := by exact_mod_cast hd3
  have ha0 : 0 ≤ S.α + 2 * γ := by rw [hα]; linarith
  have ha_le : S.α + 2 * γ ≤ ((S.d : ℝ) - 1) / 2 := by rw [hα]; linarith
  have hlam1 : 1 ≤ S.lam k := ok.one_le_lam k
  have hRb : 0 < S.Rb := by have := ok.two_le_Rb; linarith
  have hcs : 1 ≤ S.cStar := ok.cStar_ge_one
  have hlam_pos : ∀ j, 0 < S.lam j := ok.lam_pos
  have hlam_win : S.lam k ≤ 2 * S.cStar * S.lam k1 := G.lam_le_two_cStar hcore
  have hlam_s : S.lam k1 ≤ S.lam s := ok.lam_mono (by omega)
  have hpowN := G.pow_sub_ge hs
  set X0 : ℝ := (S.L : ℝ) * S.M * S.Rb / (4 * S.cStar ^ 2) with hX0def
  have hX0 : 0 < X0 := by
    have : (1 : ℝ) ≤ S.M := by exact_mod_cast ok.one_le_M
    positivity
  have hX : X0 * S.lam k ^ 2 ≤ (S.L : ℝ) ^ (k - s) := by
    have h1 : S.lam k / (2 * S.cStar) ≤ S.lam s := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h2 : (S.lam k / (2 * S.cStar)) ^ 2 ≤ S.lam s ^ 2 :=
      pow_le_pow_left₀ (by have := hlam_pos k; positivity) h1 2
    have hLM : (0 : ℝ) ≤ (S.L : ℝ) * S.M := by positivity
    calc X0 * S.lam k ^ 2 = (S.L : ℝ) * S.M * (S.Rb * (S.lam k / (2 * S.cStar)) ^ 2) := by
          rw [hX0def]; field_simp; ring
      _ ≤ (S.L : ℝ) * S.M * (S.Rb * S.lam s ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hRb.le) hLM
      _ ≤ _ := hpowN
  have hνle : (S.numax k : ℝ) ≤ 2 * S.Cν * S.lam k ^ (2 * S.d + 3) := by
    have := ok.hatW_numax_le k
    rw [hp2] at this
    exact this
  have hν1 : (1 : ℝ) ≤ S.numax k := by exact_mod_cast ok.hatW_numax_ge_one k
  have hCν : 0 < 2 * S.Cν := by have := ok.Cν_pos; linarith
  have hP0 : 0 ≤ ((S.M : ℝ) * (2 * S.c0 * (S.Rb + 1) + 10)) ^ S.d := by positivity
  exact v_bound (ℓ := (S.L : ℝ)) (lam := S.lam k) (X0 := X0) (Cν2 := 2 * S.Cν) hℓ1.le hlam1
    (by omega) ha0 ha_le hX0 hCν hP0 (G.Mcd_le k) hν1 hνle hX

end Setting.Good

open Real in
/-- **Lemma III.1.7′ (total shift), (III.1.8)**: for a finite family of blocks `z` with block trees `B z`, the
total shift `Θ^♮ = β_k ε_k ∑_z \bar ς_z` is at most `C_ϑ λ̂_k^{2d+1}`.  Premises: the flow bounds (the
bound `ς_n` on `|ϖ_n - 1|`, `β_k ≤ e^ε β L^{k(d-2)}`, `ε_k ≤ 3 α₀ L^{-kα}`, `p₂ = 2d + 3`, `L` large:
`L^{α+2γ} ≥ 2`, `L^{α+2γ-d} ≤ 1/2`), the window numerics (`k < (k₁+1) + n_q(k₁+1)`, `s + n_2(s) ≤ k`) and
the volume bounds on `V_n = ∑_z f_n(z)` of Lemma III.1.7′ (lineage boxes of Lemma III.1.2 (c), (d)). -/
theorem totalShift_le {S : Setting} (G : S.Good) {m k1 k s : ℕ} {ι : Type*} (Zs : Finset ι)
    (B : ι → BlockTree m k1 k) (zf : ℕ → ℝ) {γ ε α0 cξ β βk εk : ℝ}
    (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hα : S.α = ((S.d : ℝ) - 2) / 2 - γ)
    (hα0 : 0 ≤ α0) (hcξ : 0 ≤ cξ) (hβ : 0 < β) (hβk0 : 0 ≤ βk) (hεk0 : 0 ≤ εk)
    (hβk : βk ≤ Real.exp ε * β * (S.L : ℝ) ^ ((k : ℝ) * ((S.d : ℝ) - 2)))
    (hεk : εk ≤ 3 * α0 * (S.L : ℝ) ^ (-((k : ℝ) * S.α)))
    (hς : ∀ n, k1 ≤ n → n < k → |varpi k zf n - 1| ≤
      6 * α0 * cξ / β * (S.L : ℝ) ^ (-(((n : ℝ) + 1) * (S.α + 2 * γ))))
    (hr2 : 2 ≤ (S.L : ℝ) ^ (S.α + 2 * γ))
    (hq2 : (S.L : ℝ) ^ (S.α + 2 * γ) * ((S.L : ℝ) ^ S.d)⁻¹ ≤ 1 / 2)
    (hp2 : S.p2 = 2 * S.d + 3) (hcore : k < (k1 + 1) + S.nq (k1 + 1)) (hs : s + S.n2 s ≤ k)
    (hV1 : ∀ n, k1 ≤ n → n < k → s ≤ n + 1 → ∑ z ∈ Zs, (B z).layerFrac n ≤
      ((S.M : ℝ) * S.crit k) ^ S.d * (((S.L : ℝ) ^ S.d)⁻¹) ^ (k - n - 1))
    (hV2a : ∀ n, k1 ≤ n → n < k → n + 1 < s → ∑ z ∈ Zs, (B z).layerFrac n ≤
      ((S.M : ℝ) * S.crit k) ^ S.d * (((S.L : ℝ) ^ S.d)⁻¹) ^ (k - s))
    (hV2b : ∀ n, k1 ≤ n → n < k → n + 1 < s → ∑ z ∈ Zs, (B z).layerFrac n ≤
      S.numax k * ((S.M : ℝ) * S.crit k) ^ S.d * (((S.L : ℝ) ^ S.d)⁻¹) ^ (k - n - 1)) :
    βk * εk * ∑ z ∈ Zs, (B z).shiftBar zf ≤ totalShiftConst S ε α0 cξ * S.lam k ^ (2 * S.d + 1) := by
  have ok := G.ok
  have hL2 := ok.two_le_L
  have hℓ0 : (0 : ℝ) < S.L := by exact_mod_cast (by omega : 0 < S.L)
  have hsk : s ≤ k := by omega
  have hαγ : S.α + γ = ((S.d : ℝ) - 2) / 2 := by rw [hα]; ring
  have hred := totalShift_reduce Zs B zf hℓ0 hαγ hα0 hcξ hβ hβk0 hεk0 hβk hεk hς
  refine hred.trans ?_
  -- parameters of the layer sum
  have hK0 : 0 ≤ 18 * Real.exp ε * α0 ^ 2 * cξ := by positivity
  have hw0 : 0 < ((S.L : ℝ) ^ S.d)⁻¹ := by positivity
  have hM1 : (1 : ℝ) ≤ S.M := by exact_mod_cast ok.one_le_M
  have hcrit1 : (1 : ℝ) ≤ S.crit k := by
    have : 10 ≤ S.crit k := by unfold Setting.crit; omega
    exact_mod_cast (by omega : 1 ≤ S.crit k)
  have hMcd0 : 0 < ((S.M : ℝ) * S.crit k) ^ S.d := by positivity
  have hν1 : (1 : ℝ) ≤ S.numax k := by exact_mod_cast ok.hatW_numax_ge_one k
  have hν0 : (0 : ℝ) < S.numax k := by linarith
  have hV2 : ∀ n, k1 ≤ n → n < k → n + 1 < s →
      ∑ z ∈ Zs, (B z).layerFrac n ≤ min (((S.M : ℝ) * S.crit k) ^ S.d * (((S.L : ℝ) ^ S.d)⁻¹) ^ (k - s))
        (S.numax k * ((S.M : ℝ) * S.crit k) ^ S.d * (((S.L : ℝ) ^ S.d)⁻¹) ^ (k - n - 1)) :=
    fun n h1 h2 h3 => le_min (hV2a n h1 h2 h3) (hV2b n h1 h2 h3)
  have hRb : 0 < S.Rb := by have := ok.two_le_Rb; linarith
  have hCν : 0 < 2 * S.Cν := by have := ok.Cν_pos; linarith
  have hY0 : 0 ≤ ((S.L : ℝ) * S.M * S.Rb / (4 * S.cStar ^ 2)) ^ (-(((S.d : ℝ) + 1) / 2)) *
      (2 * S.Cν) ^ ((1 : ℝ) / 2) := by positivity
  have hP0 : 0 ≤ ((S.M : ℝ) * (2 * S.c0 * (S.Rb + 1) + 10)) ^ S.d := by positivity
  have hlam1 : 1 ≤ S.lam k := ok.one_le_lam k
  unfold totalShiftConst
  by_cases hs1 : s ≤ k1 + 1
  · have hv : ∀ t : ℕ, k - s < t → t < k - k1 →
        min (((S.M : ℝ) * S.crit k) ^ S.d * (((S.L : ℝ) ^ S.d)⁻¹) ^ (k - s) * ((S.L : ℝ) ^ (S.α + 2 * γ)) ^ t)
          ((S.numax k : ℝ) * ((S.M : ℝ) * S.crit k) ^ S.d *
            ((S.L : ℝ) ^ (S.α + 2 * γ) * ((S.L : ℝ) ^ S.d)⁻¹) ^ t) ≤ 0 := fun t h1 h2 => by omega
    have hmain := layer_total_le hsk hr2 hw0 hq2 hK0 hMcd0 hν0 le_rfl hV1 hV2 hv
    exact hmain.trans (total_final_small hK0 hP0 hY0 hlam1 (G.Mcd_le k))
  · have hs2 : k1 + 2 ≤ s := by omega
    have hd3 := ok.three_le_d
    have hd3' : (3 : ℝ) ≤ S.d := by exact_mod_cast hd3
    have hsw : (0 : ℝ) < S.d := by linarith
    have ha0 : 0 ≤ S.α + 2 * γ := by rw [hα]; linarith
    have had : S.α + 2 * γ ≤ (S.d : ℝ) := by rw [hα]; linarith
    have hw_eq : ((S.L : ℝ) ^ S.d)⁻¹ = (S.L : ℝ) ^ (-(S.d : ℝ)) := by
      rw [Real.rpow_neg hℓ0.le, Real.rpow_natCast]
    set v : ℝ := ((S.M : ℝ) * S.crit k) ^ S.d *
      (S.L : ℝ) ^ (-(((k - s : ℕ) : ℝ) * ((S.d : ℝ) - (S.α + 2 * γ)))) *
      (S.numax k : ℝ) ^ ((S.α + 2 * γ) / (S.d : ℝ)) with hvdef
    have hv0 : 0 ≤ v := by positivity
    have hv : ∀ t : ℕ, k - s < t → t < k - k1 →
        min (((S.M : ℝ) * S.crit k) ^ S.d * (((S.L : ℝ) ^ S.d)⁻¹) ^ (k - s) * ((S.L : ℝ) ^ (S.α + 2 * γ)) ^ t)
          ((S.numax k : ℝ) * ((S.M : ℝ) * S.crit k) ^ S.d *
            ((S.L : ℝ) ^ (S.α + 2 * γ) * ((S.L : ℝ) ^ S.d)⁻¹) ^ t) ≤ v := by
      intro t _ _
      have := min_term_le hℓ0 hsw ha0 had hMcd0 hν0 (k - s) t
      rw [hw_eq]
      exact this
    have hmain := layer_total_le hsk hr2 hw0 hq2 hK0 hMcd0 hν0 hv0 hV1 hV2 hv
    refine hmain.trans (total_final_big hK0 hP0 hY0 hlam1 (G.Mcd_le k) ?_)
    have := G.crossover_value_le hγ2 hγ hα hp2 hcore hs hs2
    linarith

end Balaban.LargeField
