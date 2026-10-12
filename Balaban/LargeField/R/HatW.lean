module

public import Balaban.LargeField.Counter.Params
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The chain constant `Ŵ_k` (Part III, Lemma III.4.4, (2.26′))

`hatW S ε k := 4 e^ε (1 + 2dL) ν_max(k) (L M crit_k)^d L^{(d-2)(h_k-2)/2}` and the explicit bound
`hatW_le : Ŵ_k ≤ C_Ŵ λ̂_k^{w₀ - 2}` with `w₀ - 2 = p₂ d/2 + 3d - 2`, here `λ̂_k = S.lam k` (the
abstract a priori sequence of the step counter).
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting

variable (S : Setting)

/-- `Ŵ_k := 4 e^ε (1 + 2dL) ν_max(k) (L M crit_k)^d L^{(d-2)(h_k - 2)/2}` (Lemma III.4.4). -/
noncomputable def hatW (ε : ℝ) (k : ℕ) : ℝ :=
  4 * Real.exp ε * (1 + 2 * S.d * S.L) * (S.numax k : ℝ) * ((S.L : ℝ) * S.M * S.crit k) ^ S.d *
    (S.L : ℝ) ^ (((S.d : ℝ) - 2) / 2 * ((S.h k : ℝ) - 2))

/-- The exponent `w₀ - 2 = p₂ d/2 + 3d - 2` of Lemma III.4.4. -/
noncomputable def wExp : ℝ := (S.p2 : ℝ) * S.d / 2 + 3 * S.d - 2

/-- `C_Ŵ` of Lemma III.4.4. -/
noncomputable def CHatW (ε : ℝ) : ℝ :=
  4 * Real.exp ε * (1 + 2 * S.d * S.L) * (S.L : ℝ) ^ (S.d - 2) * (2 * S.Cν) ^ ((S.d : ℝ) / 2) *
    ((S.L : ℝ) * S.M) ^ S.d * (2 * Real.sqrt S.d * S.M) ^ (((S.d : ℝ) - 2) / 2) *
    (2 * S.c0 * (S.Rb + 1) + 10) ^ S.d *
    (2 * S.c0 * (S.Rb + 1) + 2 * S.Rb + S.L + 21) ^ (((S.d : ℝ) - 2) / 2)

end Setting

namespace Setting.Ok

variable {S : Setting} (hS : S.Ok)
include hS

theorem lam_mono {j k : ℕ} (hjk : j ≤ k) : S.lam j ≤ S.lam k := by
  induction hjk with
  | refl => exact le_rfl
  | @step m _ ih => have := (hS.lam_step m).1; linarith [hS.θm_pos]

theorem one_le_lam (k : ℕ) : 1 ≤ S.lam k := (hS.one_le_lam0).trans (hS.lam_mono (Nat.zero_le k))

theorem pos_L : (0 : ℝ) < S.L := by
  have := hS.two_le_L; exact_mod_cast (by omega : 0 < S.L)

theorem one_le_L : (1 : ℝ) ≤ S.L := by
  have := hS.two_le_L; exact_mod_cast (by omega : 1 ≤ S.L)

theorem one_le_Cν : 1 ≤ S.Cν := by
  have hlog : 0 < S.logL := by
    unfold Typing.logL
    apply Real.log_pos
    have := hS.two_le_L; exact_mod_cast (by omega : 1 < S.L)
  have hcs : 0 ≤ S.cStar := by
    unfold Typing.cStar
    have := hS.θm_pos; have := hS.θm_le_θp
    have := hS.α_pos
    have : 0 ≤ S.θp / (S.α * S.logL) := by apply div_nonneg <;> [linarith; positivity]
    linarith
  have hcp : 0 ≤ S.cPrime := by
    unfold Typing.cPrime
    have := hS.θm_pos; have := hS.θm_le_θp
    exact mul_nonneg hcs (by linarith)
  have hCr : 1 ≤ S.Cr := by
    unfold Typing.Cr
    have := hS.A2_pos
    have : 0 ≤ 2 * S.A2 * S.cPrime ^ S.p2 := by positivity
    linarith
  exact hCr.trans hS.Cr_le

theorem numax_ge_one (k : ℕ) : 1 ≤ S.numax k := by
  unfold Setting.numax
  apply Nat.one_le_iff_ne_zero.2
  have h1 := hS.one_le_lam k
  have h2 : 0 < S.Cν * S.lam k ^ S.p2 := by
    have := hS.Cν_pos; positivity
  exact (Nat.ceil_pos.2 h2).ne'

theorem numax_le (k : ℕ) : (S.numax k : ℝ) ≤ 2 * S.Cν * S.lam k ^ S.p2 := by
  unfold Setting.numax
  have h1 := hS.one_le_lam k
  have hC := hS.one_le_Cν
  have h2 : 1 ≤ S.lam k ^ S.p2 := one_le_pow₀ h1
  have h3 : 1 ≤ S.Cν * S.lam k ^ S.p2 := by nlinarith
  have h4 := Nat.ceil_lt_add_one (show 0 ≤ S.Cν * S.lam k ^ S.p2 by linarith)
  nlinarith

theorem crit_le (k : ℕ) :
    (S.crit k : ℝ) ≤ (2 * S.c0 * (S.Rb + 1) + 10) * S.lam k ^ 2 := by
  unfold Setting.crit Setting.rho Setting.r
  have h1 := hS.one_le_lam k
  have h2 : 1 ≤ S.lam k ^ 2 := one_le_pow₀ h1
  have hR := hS.two_le_Rb
  have h3 : (⌈S.Rb * S.lam k ^ 2⌉₊ : ℝ) ≤ S.Rb * S.lam k ^ 2 + 1 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ S.Rb * S.lam k ^ 2 by positivity)
    linarith
  have hc0 : (0 : ℝ) ≤ S.c0 := Nat.cast_nonneg _
  push_cast
  have h4 : (S.c0 : ℝ) * ⌈S.Rb * S.lam k ^ 2⌉₊ ≤ S.c0 * (S.Rb * S.lam k ^ 2 + 1) :=
    mul_le_mul_of_nonneg_left h3 hc0
  nlinarith [mul_le_mul_of_nonneg_left h2 hc0]

theorem omega_le (k : ℕ) :
    (S.omega k : ℝ) ≤ (2 * S.Rb + S.L + 11) * S.lam k ^ 2 := by
  unfold Setting.omega
  have h1 := hS.one_le_lam k
  have h2 : 1 ≤ S.lam k ^ 2 := one_le_pow₀ h1
  have hR := hS.two_le_Rb
  have hL : (0 : ℝ) ≤ S.L := hS.pos_L.le
  split_ifs with hk
  · push_cast; nlinarith
  · have hm : S.lam (k - 1) ≤ S.lam k := hS.lam_mono (Nat.sub_le k 1)
    have h0 : 0 ≤ S.lam (k - 1) := by linarith [hS.one_le_lam (k - 1)]
    have h3 : S.lam (k - 1) ^ 2 ≤ S.lam k ^ 2 := pow_le_pow_left₀ h0 hm 2
    have h4 : (⌊S.Rb * S.lam (k - 1) ^ 2⌋₊ : ℝ) ≤ S.Rb * S.lam (k - 1) ^ 2 :=
      Nat.floor_le (by positivity)
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ S.Rb)]

/-- `L^{h_k - 2} ≤ L · 2 √d ν_max M (crit_k + ω_k)` (definition of `h_k`). -/
theorem pow_h_le (k : ℕ) :
    (S.L : ℝ) ^ ((S.h k : ℝ) - 2) ≤
      S.L * (2 * Real.sqrt S.d * S.numax k * S.M * (S.crit k + S.omega k)) := by
  have hL1 : (1 : ℝ) < S.L := by
    have := hS.two_le_L; exact_mod_cast (by omega : 1 < S.L)
  have hL0 := hS.pos_L
  have hν : (1 : ℝ) ≤ S.numax k := by exact_mod_cast hS.numax_ge_one k
  have hM : (1 : ℝ) ≤ S.M := by exact_mod_cast hS.one_le_M
  have hd : (0 : ℝ) < Real.sqrt S.d := by
    apply Real.sqrt_pos.2
    have := hS.three_le_d; exact_mod_cast (by omega : 0 < S.d)
  have hcw : (0 : ℝ) < S.crit k + S.omega k := by
    have : 0 < S.crit k := by unfold Setting.crit; omega
    positivity
  set A : ℝ := 2 * Real.sqrt S.d * S.numax k * S.M * (S.crit k + S.omega k) with hA
  have hApos : 0 < A := by positivity
  have hh : (S.h k : ℝ) - 2 = (⌈Real.logb S.L A⌉₊ : ℝ) := by
    unfold Setting.h; push_cast; ring
  rw [hh]
  calc (S.L : ℝ) ^ ((⌈Real.logb S.L A⌉₊ : ℕ) : ℝ)
      ≤ (S.L : ℝ) ^ (Real.logb S.L A + 1) :=
        Real.rpow_le_rpow_of_exponent_le hL1.le (Nat.ceil_lt_add_one
          (Real.logb_nonneg hL1 (by
            have : (1 : ℝ) ≤ 2 * Real.sqrt S.d := by
              have : (1 : ℝ) ≤ Real.sqrt S.d := by
                rw [show (1 : ℝ) = Real.sqrt 1 by simp]
                exact Real.sqrt_le_sqrt (by have := hS.three_le_d; exact_mod_cast (by omega : 1 ≤ S.d))
              linarith
            have hc : (1 : ℝ) ≤ S.crit k + S.omega k := by
              have : 1 ≤ S.crit k := by unfold Setting.crit; omega
              have : (1 : ℝ) ≤ S.crit k := by exact_mod_cast this
              have : (0 : ℝ) ≤ S.omega k := Nat.cast_nonneg _
              linarith
            rw [hA]
            have h1 : (1 : ℝ) ≤ 2 * Real.sqrt S.d * S.numax k := by nlinarith
            have h2 : (1 : ℝ) ≤ 2 * Real.sqrt S.d * S.numax k * S.M := by nlinarith
            nlinarith))).le
    _ = S.L * A := by
        rw [Real.rpow_add hL0, Real.rpow_logb hL0 hL1.ne' hApos, Real.rpow_one]; ring

/-- **`Ŵ_k ≤ C_Ŵ λ̂_k^{w₀-2}`** (Lemma III.4.4, (2.26′)). -/
theorem hatW_le (ε : ℝ) (k : ℕ) : S.hatW ε k ≤ S.CHatW ε * S.lam k ^ S.wExp := by
  have hL0 := hS.pos_L
  have hL1 := hS.one_le_L
  have hlam := hS.one_le_lam k
  have hlam0 : 0 < S.lam k := by linarith
  have hd3 := hS.three_le_d
  have hdR : (3 : ℝ) ≤ S.d := by exact_mod_cast hd3
  have hM : (1 : ℝ) ≤ S.M := by exact_mod_cast hS.one_le_M
  have hCν := hS.one_le_Cν
  set l := S.lam k with hl
  set z : ℝ := ((S.d : ℝ) - 2) / 2 with hz
  have hz0 : 0 ≤ z := by rw [hz]; linarith
  set ν : ℝ := (S.numax k : ℝ) with hν
  have hν1 : 1 ≤ ν := by rw [hν]; exact_mod_cast hS.numax_ge_one k
  set c : ℝ := (S.crit k : ℝ) with hc
  set w : ℝ := (S.omega k : ℝ) with hw
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hw0 : 0 ≤ w := Nat.cast_nonneg _
  set c1 : ℝ := 2 * S.c0 * (S.Rb + 1) + 10 with hc1
  set c2 : ℝ := 2 * S.c0 * (S.Rb + 1) + 2 * S.Rb + S.L + 21 with hc2
  have hc1pos : 0 < c1 := by
    have : (0 : ℝ) ≤ S.c0 := Nat.cast_nonneg _
    have := hS.two_le_Rb
    rw [hc1]; positivity
  have hcc : c ≤ c1 * l ^ 2 := hS.crit_le k
  have hcw : c + w ≤ c2 * l ^ 2 := by
    have h1 := hS.crit_le k
    have h2 := hS.omega_le k
    rw [hc2]; nlinarith
  have hνle : ν ≤ 2 * S.Cν * l ^ S.p2 := hS.numax_le k
  have hpow := hS.pow_h_le k
  have hsqrt : (0 : ℝ) < Real.sqrt S.d := Real.sqrt_pos.2 (by linarith)
  -- the factor L^{z (h-2)}
  have hLz : (S.L : ℝ) ^ (z * ((S.h k : ℝ) - 2)) ≤
      (S.L : ℝ) ^ z * ((2 * Real.sqrt S.d * S.M) ^ z * (ν ^ z * (c + w) ^ z)) := by
    rw [mul_comm z, Real.rpow_mul hL0.le]
    calc ((S.L : ℝ) ^ ((S.h k : ℝ) - 2)) ^ z
        ≤ (S.L * (2 * Real.sqrt S.d * ν * S.M * (c + w))) ^ z :=
          Real.rpow_le_rpow (by positivity) hpow hz0
      _ = _ := by
        have e : (S.L : ℝ) * (2 * Real.sqrt S.d * ν * S.M * (c + w)) =
            (S.L : ℝ) * ((2 * Real.sqrt S.d * S.M) * (ν * (c + w))) := by ring
        rw [e, Real.mul_rpow hL0.le (by positivity),
          Real.mul_rpow (x := 2 * Real.sqrt S.d * S.M) (y := ν * (c + w)) (by positivity) (by positivity),
          Real.mul_rpow (x := ν) (y := c + w) (by positivity) (by positivity)]
  have hνpos : 0 < ν := by linarith
  have hlz : l ^ ((S.d : ℝ) - 2) = (l ^ 2) ^ z := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam0.le, hz]; congr 1; push_cast; ring
  -- factor ν
  have hν_d : ν * ν ^ z ≤ (2 * S.Cν) ^ ((S.d : ℝ) / 2) * l ^ ((S.p2 : ℝ) * S.d / 2) := by
    have e1 : ν * ν ^ z = ν ^ ((S.d : ℝ) / 2) := by
      rw [← Real.rpow_one_add' hνpos.le (by rw [hz]; linarith)]; congr 1; rw [hz]; ring
    rw [e1]
    have e2 : (2 * S.Cν * l ^ S.p2) ^ ((S.d : ℝ) / 2) =
        (2 * S.Cν) ^ ((S.d : ℝ) / 2) * l ^ ((S.p2 : ℝ) * S.d / 2) := by
      rw [Real.mul_rpow (by linarith) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hlam0.le]
      congr 2; ring
    calc ν ^ ((S.d : ℝ) / 2) ≤ (2 * S.Cν * l ^ S.p2) ^ ((S.d : ℝ) / 2) :=
          Real.rpow_le_rpow hνpos.le hνle (by linarith)
      _ = _ := e2
  -- factor c
  have hc_d : c ^ S.d ≤ c1 ^ S.d * l ^ (2 * S.d) := by
    calc c ^ S.d ≤ (c1 * l ^ 2) ^ S.d := pow_le_pow_left₀ hc0 hcc _
      _ = _ := by rw [mul_pow, ← pow_mul]
  -- factor c + w
  have hcw_z : (c + w) ^ z ≤ c2 ^ z * l ^ ((S.d : ℝ) - 2) := by
    calc (c + w) ^ z ≤ (c2 * l ^ 2) ^ z := Real.rpow_le_rpow (by positivity) hcw hz0
      _ = _ := by
        rw [Real.mul_rpow (by rw [hc2]; have := hS.two_le_Rb; have : (0 : ℝ) ≤ S.c0 := Nat.cast_nonneg _; positivity)
          (by positivity), hlz]
  -- factor L^z
  have hLz' : (S.L : ℝ) ^ z ≤ (S.L : ℝ) ^ (S.d - 2) := by
    have : (S.L : ℝ) ^ (S.d - 2) = (S.L : ℝ) ^ (((S.d - 2 : ℕ) : ℝ)) := (Real.rpow_natCast _ _).symm
    rw [this]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    rw [Nat.cast_sub (by omega), hz]; push_cast; linarith
  have hlexp : l ^ S.wExp = l ^ ((S.p2 : ℝ) * S.d / 2) * (l ^ (2 * S.d) * l ^ ((S.d : ℝ) - 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hlam0, ← Real.rpow_add hlam0]
    unfold Setting.wExp; congr 1; push_cast; ring
  unfold Setting.hatW Setting.CHatW
  have hP : 0 ≤ 4 * Real.exp ε * (1 + 2 * (S.d : ℝ) * S.L) := by positivity
  have hcd : 0 ≤ c ^ S.d := by positivity
  calc 4 * Real.exp ε * (1 + 2 * (S.d : ℝ) * S.L) * ν * ((S.L : ℝ) * S.M * c) ^ S.d *
        (S.L : ℝ) ^ (z * ((S.h k : ℝ) - 2))
      ≤ 4 * Real.exp ε * (1 + 2 * (S.d : ℝ) * S.L) * ν * ((S.L : ℝ) * S.M * c) ^ S.d *
        ((S.L : ℝ) ^ z * ((2 * Real.sqrt S.d * S.M) ^ z * (ν ^ z * (c + w) ^ z))) :=
          mul_le_mul_of_nonneg_left hLz (by positivity)
    _ = (4 * Real.exp ε * (1 + 2 * (S.d : ℝ) * S.L)) * (ν * ν ^ z) * (((S.L : ℝ) * S.M) ^ S.d * c ^ S.d) *
        ((S.L : ℝ) ^ z * ((2 * Real.sqrt S.d * S.M) ^ z * (c + w) ^ z)) := by
          rw [mul_pow]; ring
    _ ≤ (4 * Real.exp ε * (1 + 2 * (S.d : ℝ) * S.L)) *
          ((2 * S.Cν) ^ ((S.d : ℝ) / 2) * l ^ ((S.p2 : ℝ) * S.d / 2)) *
          (((S.L : ℝ) * S.M) ^ S.d * (c1 ^ S.d * l ^ (2 * S.d))) *
          ((S.L : ℝ) ^ (S.d - 2) * ((2 * Real.sqrt S.d * S.M) ^ z * (c2 ^ z * l ^ ((S.d : ℝ) - 2)))) := by
          have h2 : 0 ≤ ν * ν ^ z := by positivity
          have h3 : 0 ≤ ((S.L : ℝ) * S.M) ^ S.d * c ^ S.d := by positivity
          have h4 : 0 ≤ (2 * Real.sqrt S.d * S.M) ^ z * (c + w) ^ z := by positivity
          gcongr
    _ = _ := by rw [hlexp]; ring

end Setting.Ok

end Balaban.LargeField
