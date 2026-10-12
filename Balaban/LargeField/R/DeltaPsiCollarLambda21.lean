module

public import Balaban.LargeField.R.HatW
public import Balaban.LargeField.Counter.Basic
public import Balaban.LargeField.Region.Step
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# (Λ21′) is a consequence of the landed constants (LF-RECONSTRUCTION §I.1.3; COLLAR-FIX (2.2))

The condition `(m_W + 1) C_reg ≤ Ŵ_k` with `m_W = d (2⌊R_{k₁-1}⌋ + 3) M` and
`C_reg = 3 d L e^ε L^((d-2)/2)` holds for every `Setting.Ok` and every radius sequence with
`R_j ≤ R_base λ_j²` (`RadiusHyp`), because `Ŵ_k ≥ 8 d L e^ε (L M crit_k)^d`
and `crit_k = 2 c₀ ⌈R_base λ_k²⌉ + 10 ≥ 2 R_{k₁-1} + 10`.
-/

@[expose] public section

namespace Balaban.LargeField

open Region

theorem lambda21_key (L M c m : ℝ) (d : ℕ) (hd : 3 ≤ d) (hL : 2 ≤ L) (hM : 1 ≤ M) (hc : 10 ≤ c)
    (hm : m + 1 ≤ d * M * c) : (m + 1) * (3 * L ^ (d - 2)) ≤ 8 * (L * M * c) ^ d := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hM0 : 0 < M := by linarith
  have hcpos : 0 < c := by linarith
  have hL0 : 0 < L := by linarith
  have hbern : (d : ℝ) ≤ c ^ (d - 1) := by
    have hb := one_add_mul_le_pow (a := c - 1) (by linarith) (d - 1)
    have : (1 + (c - 1)) = c := by ring
    rw [this] at hb
    have hn : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [hn] at hb
    nlinarith
  have hcd : c ^ d = c * c ^ (d - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hLd : L ^ d = L ^ (d - 2) * L ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hMd : M ≤ M ^ d := by
    calc M = M ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hM (by omega)
  have hL2 : (4 : ℝ) ≤ L ^ 2 := by nlinarith
  have hcp := pow_pos hcpos (d - 1)
  have h4 : (3 : ℝ) * d ≤ 8 * L ^ 2 * c ^ (d - 1) := by
    calc (3 : ℝ) * d ≤ 3 * c ^ (d - 1) := by linarith
      _ ≤ 8 * 4 * c ^ (d - 1) := by linarith
      _ ≤ 8 * L ^ 2 * c ^ (d - 1) := by gcongr
  calc (m + 1) * (3 * L ^ (d - 2)) ≤ (d * M * c) * (3 * L ^ (d - 2)) :=
        mul_le_mul_of_nonneg_right hm (by positivity)
    _ = (M * c) * L ^ (d - 2) * (3 * d) := by ring
    _ ≤ (M * c) * L ^ (d - 2) * (8 * L ^ 2 * c ^ (d - 1)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 8 * (L ^ (d - 2) * L ^ 2) * (M * (c * c ^ (d - 1))) := by ring
    _ ≤ 8 * (L ^ (d - 2) * L ^ 2) * (M ^ d * (c * c ^ (d - 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMd (by positivity)) (by positivity)
    _ = 8 * (L * M * c) ^ d := by rw [mul_pow, mul_pow, hcd, hLd]; ring

theorem Setting.Ok.hatW_ge {S : Setting} (hS : S.Ok) (ε : ℝ) (k : ℕ) :
    8 * S.d * S.L * Real.exp ε * ((S.L : ℝ) * S.M * (S.crit k : ℝ)) ^ S.d ≤ S.hatW ε k := by
  have hL1 := hS.hatW_one_le_L
  have hν : (1 : ℝ) ≤ S.numax k := by exact_mod_cast hS.hatW_numax_ge_one k
  have hd3 := hS.three_le_d
  have hdR : (3 : ℝ) ≤ S.d := by exact_mod_cast hd3
  have hexp := Real.exp_pos ε
  have hP : (1 : ℝ) ≤ (S.L : ℝ) ^ (((S.d : ℝ) - 2) / 2 * ((S.h k : ℝ) - 2)) := by
    apply Real.one_le_rpow hL1
    apply mul_nonneg (by linarith)
    have : (2 : ℝ) ≤ S.h k := by unfold Setting.h; exact_mod_cast Nat.le_add_left 2 _
    linarith
  set X : ℝ := ((S.L : ℝ) * S.M * (S.crit k : ℝ)) ^ S.d with hXdef
  have hX : 0 ≤ X := by positivity
  set P : ℝ := (S.L : ℝ) ^ (((S.d : ℝ) - 2) / 2 * ((S.h k : ℝ) - 2)) with hPdef
  have hdL : 0 ≤ (S.d : ℝ) * S.L := by positivity
  have e : S.hatW ε k = 4 * Real.exp ε * (1 + 2 * (S.d * S.L)) * (S.numax k : ℝ) * X * P := by
    unfold Setting.hatW; ring
  rw [e]
  have h1 : 8 * (S.d * S.L) * Real.exp ε * X ≤
      4 * Real.exp ε * (1 + 2 * (S.d * S.L)) * 1 * X * 1 := by
    have := mul_nonneg hexp.le hX
    nlinarith
  calc 8 * (S.d : ℝ) * S.L * Real.exp ε * X = 8 * (S.d * S.L) * Real.exp ε * X := by ring
    _ ≤ _ := h1
    _ ≤ _ := by gcongr

theorem Setting.Ok.lambda21'_of_radiusHyp {S : Setting} (hS : S.Ok) {R : ℕ → ℝ}
    (RH : RadiusHyp S.L S.Rb S.lam R) (ε : ℝ) (k : ℕ) :
    (((S.d * ((2 * ⌊R (S.k1 k - 1)⌋₊ + 3) * S.M) : ℕ) : ℝ) + 1) *
        (3 * S.d * S.L * Real.exp ε * (S.L : ℝ) ^ (((S.d : ℝ) - 2) / 2)) ≤ S.hatW ε k := by
  have hL1 := hS.hatW_one_le_L
  have hd3 := hS.three_le_d
  have hdR : (3 : ℝ) ≤ S.d := by exact_mod_cast hd3
  have hM : (1 : ℝ) ≤ S.M := by exact_mod_cast hS.one_le_M
  have hR2 := hS.two_le_Rb
  have hk1 : S.k1 k - 1 ≤ k := le_trans (Nat.sub_le _ _) (Nat.findGreatest_le k)
  have hlm : S.lam (S.k1 k - 1) ≤ S.lam k := hS.lam_mono hk1
  have hlm0 : 0 ≤ S.lam (S.k1 k - 1) := by linarith [hS.one_le_lam (S.k1 k - 1)]
  have h1 : R (S.k1 k - 1) ≤ S.Rb * S.lam k ^ 2 :=
    (RH.le _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlm0 hlm 2) (by linarith))
  have hfl : (⌊R (S.k1 k - 1)⌋₊ : ℝ) ≤ R (S.k1 k - 1) := Nat.floor_le (RH.nonneg _)
  have hce : S.Rb * S.lam k ^ 2 ≤ (⌈S.Rb * S.lam k ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have hc0 : (1 : ℝ) ≤ S.c0 := by exact_mod_cast hS.one_le_c0
  have hcr : (0 : ℝ) ≤ (⌈S.Rb * S.lam k ^ 2⌉₊ : ℝ) := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ ⌊R (S.k1 k - 1)⌋₊ := Nat.cast_nonneg _
  have hcrit : 2 * (⌊R (S.k1 k - 1)⌋₊ : ℝ) + 10 ≤ S.crit k := by
    unfold Setting.crit Setting.rho Setting.r
    push_cast
    nlinarith
  have hz : (S.L : ℝ) ^ (((S.d : ℝ) - 2) / 2) ≤ (S.L : ℝ) ^ (S.d - 2) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    rw [Nat.cast_sub (by omega)]; push_cast; linarith
  have hexp := Real.exp_pos ε
  have hcast : (((S.d * ((2 * ⌊R (S.k1 k - 1)⌋₊ + 3) * S.M) : ℕ) : ℝ) + 1) ≤
      S.d * S.M * (S.crit k : ℝ) := by
    push_cast
    have : (1 : ℝ) ≤ S.d * S.M := by nlinarith
    nlinarith
  have key := lambda21_key (S.L : ℝ) S.M (S.crit k : ℝ) _ S.d hd3 (by exact_mod_cast hS.two_le_L) hM
    (by linarith) hcast
  have hge := hS.hatW_ge ε k
  have hq : 0 ≤ 3 * (S.d : ℝ) * S.L * Real.exp ε := by positivity
  have hm0 : (0 : ℝ) ≤ (((S.d * ((2 * ⌊R (S.k1 k - 1)⌋₊ + 3) * S.M) : ℕ) : ℝ) + 1) := by positivity
  calc _ ≤ (((S.d * ((2 * ⌊R (S.k1 k - 1)⌋₊ + 3) * S.M) : ℕ) : ℝ) + 1) *
          (3 * S.d * S.L * Real.exp ε * (S.L : ℝ) ^ (S.d - 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz hq) hm0
    _ = (S.d * S.L * Real.exp ε) * ((((S.d * ((2 * ⌊R (S.k1 k - 1)⌋₊ + 3) * S.M) : ℕ) : ℝ) + 1) *
          (3 * (S.L : ℝ) ^ (S.d - 2))) := by ring
    _ ≤ (S.d * S.L * Real.exp ε) * (8 * ((S.L : ℝ) * S.M * (S.crit k : ℝ)) ^ S.d) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring
    _ ≤ _ := hge

end Balaban.LargeField
