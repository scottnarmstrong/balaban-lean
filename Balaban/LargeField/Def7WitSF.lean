module

public import Balaban.LargeField.Def7WitLF
public import Balaban.SmallField.Def6Inhabited
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Def-7 witness, part 3: the small-field data

At `d = L = 3`, `N = 2`, scale `k = 1`: the zero effective action of Def-6's witness
(`zeroFam`, `rhoZero`, `isSF_zero_density`) with the running coefficients of the large-field
witness, `β_n = β 3^n`, `ν_n = ν 9^n` (`ν ≤ 1/(27β)`), `a ≡ 5/4`, the constants
`witnessConsts 1` (`m₀ = 0`, `E₀ = 0`, `B = 0`, `ν̄ = 7/72`); `ℛ ≡ 0`, `corr ≡ 0`.

* `wcoeff`, `wIsSFFamily`: the Def-6 class (`IsSFFamily`) for these data;
* `wSF`: the small-field data `𝔰`; `wSF_D2`, `wSF_D8`, `wSF_D9`: the clauses (D2), (D8), (D9);
* `one_le_kZero`, `kZero_le_one`: the a priori regime index of `(β, ν)`.
-/

@[expose] public section

namespace Balaban.LargeField.Def7.Wit

open Balaban.SmallField Balaban.SmallField.Def6 Balaban.Background Filter Topology

/-- `β_n = β 3^n`. -/
noncomputable def wβs : ℕ → ℝ := fun n => wβ * 3 ^ n

/-- `ν_n = ν 9^n`. -/
noncomputable def wνs (ν : ℝ) : ℕ → ℝ := fun n => ν * 9 ^ n

theorem wcoeff (ν : ℝ) (hν0 : 0 < ν) (hν : ν * 9 ≤ 7 / 72) :
    CoeffBounds 3 3 1 (witnessConsts 1) wβs (wνs ν) witnessa where
  flow := by
    refine ⟨fun _ => 0, wβ, ν, fun n => ?_, ?_, fun n _ => ?_⟩
    · have := rate3_pos; have := rate3_lt
      simp only [witnessConsts, norm_zero]
      positivity
    · have := rate3_pos; have := rate3_lt
      simp only [witnessConsts]
      nlinarith
    · refine ⟨?_, ?_⟩
      · rw [betaSeq_zero]; simp [wβs]
      · rw [nuSeq_zero]
        simp only [wνs]
        push_cast
        rw [pow_mul]
        norm_num
  beta_gt := by
    have := wβ_pos
    simp [witnessConsts, wβs]
    positivity
  nu_pos := by simp only [wνs]; positivity
  nu_le := by simp only [wνs, witnessConsts]; linarith
  a_ge := by norm_num [witnessa]
  a_lt := by norm_num [witnessa]

theorem wIsSFFamily (ν : ℝ) (hν0 : 0 < ν) (hν : ν * 9 ≤ 7 / 72) (m₁ : ℕ) :
    IsSFFamily (d := 3) (L := 3) (m₁ := m₁) (k := 1) (N := 2) (ϱ := bgR0 3 3)
      (witnessConsts 1) wβs (wνs ν) witnessa (zeroFam 3 3 m₁ 1 2 (bgR0 3 3))
      (fun N₁ _ => rhoZero (N₁ := N₁) (m₁ := m₁) (N := 2) (ϱ := bgR0 3 3) (witnessConsts 1) wβs
        (wνs ν) witnessa) (fun _ => 0) where
  admissible := witnessConsts_admissible one_pos
  coeff := wcoeff ν hν0 hν
  torus := fun _ _ => isSF_zero_density _ _ _ _ rfl one_pos
    (bgHyp_of_class (witnessConsts_admissible one_pos) (wcoeff ν hν0 hν) le_rfl le_rfl le_rfl)
  torusIndep := torusIndep_zero _
  renorm := fun _ _ _ => renormCond_zero _ _ _ _

/-- **The small-field data of the witness.** -/
noncomputable def wSF (ν : ℝ) (m₁ : ℕ) : SFData 3 3 m₁ 1 2 (bgR0 3 3) where
  β := wβs
  ν := wνs ν
  z := fun _ => 1
  a := witnessa
  E := fun _ => 0
  Tm := zeroFam 3 3 m₁ 1 2 (bgR0 3 3)
  Rt := fun _ _ _ _ _ _ _ => 0
  corr := fun _ _ _ _ _ _ _ => 0

theorem wSF_rTerms (ν : ℝ) (m₁ : ℕ) (fac : ℕ → ℝ) (hfac : ∀ nn, 0 ≤ fac nn) (N₁ : ℕ)
    [NeZero N₁] :
    RTermsH4 (ϱ := bgR0 3 3) (witnessConsts 1) wβs (wνs ν) witnessa N₁ ((wSF ν m₁).Rt N₁) fac where
  analytic := fun _ _ _ _ _ => analyticOnNhd_const
  loc := fun _ _ _ _ _ _ _ _ _ => rfl
  rot := fun _ _ _ _ _ _ _ => rfl
  euc := fun _ _ _ _ _ _ _ => rfl
  bound := fun nn _ _ X _ ψ h g _ _ _ => by
    have := wβ_pos
    have h1 := hfac nn
    have h2 : (0 : ℝ) < wβs 1 := by simp only [wβs]; positivity
    simp only [wSF, norm_zero]
    positivity

/-- (D2) for the witness, with any nonnegative bound factors of the `ℛ`-terms. -/
theorem wSF_D2 (ν : ℝ) (hν0 : 0 < ν) (hν : ν * 9 ≤ 7 / 72) (m₁ : ℕ) (fac : ℕ → ℝ)
    (hfac : ∀ nn, 0 ≤ fac nn) : D2SF (witnessConsts 1) (wSF ν m₁) fac where
  sfClass := ⟨_, wIsSFFamily ν hν0 hν m₁⟩
  rTerms := fun N₁ _ => wSF_rTerms ν m₁ fac hfac N₁

/-- (D8), small-field part, for the witness (all terms vanish). -/
theorem wSF_D8 (ν : ℝ) (m₁ : ℕ) : D8SF (witnessConsts 1).m₀ (wSF ν m₁) where
  M_eq := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  R_eq := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl

/-- (D9) for the witness. -/
theorem wSF_D9 (ν : ℝ) (hν0 : 0 < ν) (hν : ν * 9 ≤ 7 / 72) (m₁ k0 : ℕ) (hk0 : 1 ≤ k0) :
    D9Coeff (witnessConsts 1) k0 (wSF ν m₁) where
  beta_gt := by
    have := wβ_pos
    simp [witnessConsts, wSF, wβs]
    positivity
  nu_pos := by simp only [wSF, wνs]; positivity
  nu_le := by simp only [wSF, wνs, witnessConsts]; linarith
  k_le := hk0

/-- `k₀(β, ν) ≥ 1` when `β ν L^d ≤ 1`. -/
theorem one_le_kZero {ν : ℝ} (hν0 : 0 < ν) (hν : wβ * ν * 27 ≤ 1) : 1 ≤ kZero 3 3 wβ ν := by
  have hβν : 0 < wβ * ν := mul_pos wβ_pos hν0
  refine le_csSup (kZero_bddAbove (by norm_num) (by norm_num) hβν) ?_
  show wβ * ν * ((3 : ℕ) : ℝ) ^ (1 * 3) ≤ 1
  norm_num
  linarith

/-- `k₀(β, ν) ≤ 1` when `β ν L^{2d} > 1`. -/
theorem kZero_le_one {ν : ℝ} (hν0 : 0 < ν) (hν : 1 < wβ * ν * 729) : kZero 3 3 wβ ν ≤ 1 := by
  have hβν : 0 < wβ * ν := mul_pos wβ_pos hν0
  by_cases hg : KZeroGenuine wβ ν
  · have hk := kZero_spec (d := 3) (L := 3) (by norm_num) (by norm_num) hβν hg
    by_contra hc
    push Not at hc
    have h2 : ((3 : ℕ) : ℝ) ^ (2 * 3) ≤ ((3 : ℕ) : ℝ) ^ (kZero 3 3 wβ ν * 3) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : (((3 : ℕ) : ℝ) ^ (2 * 3)) = 729 := by norm_num
    rw [h3] at h2
    nlinarith
  · rw [kZero_of_not_genuine (by norm_num) hg]; omega

/-- `ν₀ = 1/(27 β)`: `β ν₀ L^d = 1`, `k₀ = 1`. -/
noncomputable def wν₀ : ℝ := 1 / (27 * wβ)

theorem wν₀_pos : 0 < wν₀ := by unfold wν₀; have := wβ_pos; positivity

theorem wν₀_mul : wβ * wν₀ * 27 = 1 := by
  unfold wν₀; have := wβ_pos; field_simp

theorem wν₀_nine : wν₀ * 9 ≤ 7 / 72 := by
  have h := wβ_gt
  unfold wν₀
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem kZero_wν₀ : kZero 3 3 wβ wν₀ = 1 :=
  le_antisymm (kZero_le_one wν₀_pos (by nlinarith [wν₀_mul])) (one_le_kZero wν₀_pos wν₀_mul.le)

end Balaban.LargeField.Def7.Wit
