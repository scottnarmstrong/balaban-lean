/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.PsiGeomSlice
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# P1 Lemma 3.3: the invariant coordinates `(U, V, W²)` on the constant tube

P1 pp. 126-129, (3.28), (3.37)-(3.44).  The effective potential is a function of the three
`O(N)` invariants `(u, v, w²) = (|ψ|, ν_j (ψ₀ · h), ν_j² (|h|² - (ψ₀ · h)²))` (3.28).  Its analytic
extension to the constant complex tube `Ψ^c_{const}(σ, ε)` of (3.13)-(3.14) (derivative conditions
dropped) is obtained by inserting
`U = √((ψ + ψ')²)`, `V = (ψ + ψ')₀ · (h + h')`, `W² = (h + h')² - V²` (3.37),
where `(ψ + ψ')₀ = (ψ + ψ') / U` is the analytic extension of `ψ₀ = ψ / |ψ|`
(`tubeU`, `tubeV`, `tubeW2`).  `lemma33_tube` proves (3.44): `U, V, W²` map the tube into the
polydisc (3.31),
`|U - 1| < (7σ)² ε / 6`, `|V - 1| < (7σ)² ε² / (2 ν)`, `|W²| < (7σ)⁴ ε² / (4 ν²)`
(P1 p. 129; the polydisc in the variables `(u, ν_j v, ν_j² w²)` is (3.31), with `ν = ν_j`).

The smallness assumptions of P1 ("`ε` sufficiently small", "`ν_j ≤ σ²`", `σ ≤ 1`) are explicit:
`0 < ν ≤ σ² ≤ 1`, `ε ≤ 1/100`.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Multiscale Balaban.Background Finset

variable {N : ℕ}

/-- The complex bilinear form `a · b = ∑ aᵢ bᵢ` on `ℂ^N` (not the Hermitian product). -/
def dotc (a b : Fin N → ℂ) : ℂ := ∑ i, a i * b i

theorem dotc_comm (a b : Fin N → ℂ) : dotc a b = dotc b a := by
  unfold dotc; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem dotc_add_left (a a' b : Fin N → ℂ) : dotc (a + a') b = dotc a b + dotc a' b := by
  unfold dotc; simp [add_mul, Finset.sum_add_distrib]

theorem dotc_add_right (a b b' : Fin N → ℂ) : dotc a (b + b') = dotc a b + dotc a b' := by
  unfold dotc; simp [mul_add, Finset.sum_add_distrib]

theorem dotc_sub_left (a a' b : Fin N → ℂ) : dotc (a - a') b = dotc a b - dotc a' b := by
  unfold dotc; simp [sub_mul, Finset.sum_sub_distrib]

theorem dotc_sub_right (a b b' : Fin N → ℂ) : dotc a (b - b') = dotc a b - dotc a b' := by
  unfold dotc; simp [mul_sub, Finset.sum_sub_distrib]

theorem dotc_smul_left (c : ℂ) (a b : Fin N → ℂ) : dotc (c • a) b = c * dotc a b := by
  unfold dotc; simp [Finset.mul_sum, mul_assoc]

theorem dotc_smul_right (c : ℂ) (a b : Fin N → ℂ) : dotc a (c • b) = c * dotc a b := by
  unfold dotc; simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

theorem norm_dotc_le (a b : Fin N → ℂ) : ‖dotc a b‖ ≤ vn a * vn b := norm_sum_mul_le_vn a b

/-- The principal square root `z^{1/2}` (the analytic extension of `|ψ| = √(ψ·ψ)` to `ψ·ψ` near
`1`). -/
noncomputable def uExt (z : ℂ) : ℂ := z ^ (1 / 2 : ℂ)

theorem uExt_sq (z : ℂ) : uExt z * uExt z = z := by
  unfold uExt
  have h := Complex.cpow_nat_inv_pow z (n := 2) (by norm_num)
  rw [sq] at h
  simpa using h

theorem uExt_re_nonneg (z : ℂ) : 0 ≤ (uExt z).re := by
  by_cases hz : z = 0
  · subst hz; simp [uExt]
  · unfold uExt
    rw [Complex.cpow_def_of_ne_zero hz, Complex.exp_re]
    refine mul_nonneg (Real.exp_pos _).le ?_
    have h1 : (Complex.log z * (1 / 2 : ℂ)).im = Complex.arg z / 2 := by
      simp [Complex.log_im]; ring
    rw [h1]
    refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
    · have := Complex.neg_pi_lt_arg z; linarith [Real.pi_pos]
    · have := Complex.arg_le_pi z; linarith [Real.pi_pos]

theorem vn_smul_pi (c : ℂ) (v : Fin N → ℂ) : vn (c • v) = ‖c‖ * vn v := by
  unfold vn
  have : (WithLp.toLp 2 (c • v) : EuclideanSpace ℂ (Fin N)) = c • WithLp.toLp 2 v := rfl
  rw [this, norm_smul]

theorem vn_add_pi (v w : Fin N → ℂ) : vn (v + w) ≤ vn v + vn w := vn_add v w

theorem vn_sub_pi (v w : Fin N → ℂ) : vn (v - w) ≤ vn v + vn w := by
  have h := vn_add_pi v (-w)
  have e : -w = (-1 : ℂ) • w := by simp
  rw [e, vn_smul_pi] at h
  simpa [sub_eq_add_neg] using h

/-- **The `V`-estimate** of P1 (3.40)-(3.41), in vector form: if `s₀·s₀ = 1 = p·p` then
`s₀·(h + h') - 1 = d·(h - p) - ½ d·d + d·h' + (p·h - 1) + p·h'`, `d = s₀ - p`. -/
theorem tube_V_bound (s0 p hv h' : Fin N → ℂ) (hs : dotc s0 s0 = 1) (hp : dotc p p = 1) :
    ‖dotc s0 (hv + h') - 1‖ ≤ ‖dotc p hv - 1‖ + ‖dotc p h'‖ + vn (s0 - p) * vn (hv - p) +
      1 / 2 * vn (s0 - p) ^ 2 + vn (s0 - p) * vn h' := by
  set d := s0 - p with hd
  have hs0 : s0 = d + p := by rw [hd]; abel
  have hdd : dotc d p = -(1 / 2) * dotc d d := by
    have : dotc d d = dotc s0 s0 - 2 * dotc s0 p + dotc p p := by
      rw [hd, dotc_sub_left, dotc_sub_right, dotc_sub_right, dotc_comm p s0]; ring
    have h2 : dotc d p = dotc s0 p - 1 := by
      rw [hd, dotc_sub_left, hp]
    rw [this, hs, hp, h2]; ring
  have key : dotc s0 (hv + h') - 1 = dotc d (hv - p) + (-(1 / 2) * dotc d d) + dotc d h' +
      (dotc p hv - 1) + dotc p h' := by
    have e : hv + h' = (hv - p) + p + h' := by abel
    conv_lhs => rw [hs0, e]
    simp only [dotc_add_left, dotc_add_right, dotc_sub_right]
    rw [← hdd, hp]; ring
  rw [key]
  have t1 := norm_dotc_le d (hv - p)
  have t2 : ‖-(1 / 2 : ℂ) * dotc d d‖ ≤ 1 / 2 * vn d ^ 2 := by
    rw [norm_mul]; norm_num
    exact (norm_dotc_le d d).trans (le_of_eq (by ring))
  have t3 := norm_dotc_le d h'
  calc _ ≤ ‖dotc d (hv - p)‖ + ‖-(1 / 2 : ℂ) * dotc d d‖ + ‖dotc d h'‖ + ‖dotc p hv - 1‖ +
        ‖dotc p h'‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

/-- **The `W²`-estimate** (P1 (3.42)-(3.43)): `W² = (h + h')² - V²` is the square `e·e` of
`e = k - V s₀`. -/
theorem tube_W_bound (s0 p hv h' : Fin N → ℂ) (hs : dotc s0 s0 = 1) :
    ‖dotc (hv + h') (hv + h') - (dotc s0 (hv + h')) ^ 2‖ ≤
      (vn (hv - p) + vn h' + vn (s0 - p) + ‖1 - dotc s0 (hv + h')‖ * vn s0) ^ 2 := by
  set k := hv + h' with hk
  set V := dotc s0 k with hV
  set e : Fin N → ℂ := (hv - p) + h' + (p - s0) + (1 - V) • s0 with he
  have hek : e = k - V • s0 := by
    rw [he, hk, sub_smul, one_smul]; abel
  have hee : dotc e e = dotc k k - V ^ 2 := by
    rw [hek, dotc_sub_left, dotc_sub_right, dotc_sub_right, dotc_smul_left, dotc_smul_right,
      dotc_smul_left, dotc_smul_right, hs, dotc_comm k s0, ← hV]
    ring
  rw [← hee]
  refine (norm_dotc_le e e).trans ?_
  have hve : vn e ≤ vn (hv - p) + vn h' + vn (s0 - p) + ‖1 - V‖ * vn s0 := by
    have h1 := vn_add_pi ((hv - p) + h' + (p - s0)) ((1 - V) • s0)
    have h2 := vn_add_pi ((hv - p) + h') (p - s0)
    have h3 := vn_add_pi (hv - p) h'
    have h4 : vn (p - s0) = vn (s0 - p) := by
      have := vn_sub_comm p s0; exact this
    rw [vn_smul_pi] at h1
    simp only [he]
    linarith
  have := vn_nonneg e
  nlinarith

/-- The principal square root of `z` near `1`: `Re √z ≥ 0.98`, `|√z - 1| ≤ |z - 1| / 1.98`. -/
theorem uExt_bounds {z : ℂ} (hz : ‖z - 1‖ ≤ 1 / 50) :
    98 / 100 ≤ (uExt z).re ∧ ‖uExt z - 1‖ * (198 / 100) ≤ ‖z - 1‖ ∧ 98 / 100 ≤ ‖uExt z‖ := by
  have hU := uExt_sq z
  have h0 := uExt_re_nonneg z
  set U := uExt z with hUdef
  have hzre : 49 / 50 ≤ z.re := by
    have := Complex.abs_re_le_norm (z - 1)
    have h2 := (abs_le.1 this).1
    simp only [Complex.sub_re, Complex.one_re] at h2
    linarith
  have hre : z.re = U.re * U.re - U.im * U.im := by rw [← hU]; simp [Complex.mul_re]
  have hsq : 49 / 50 ≤ U.re * U.re := by nlinarith [mul_self_nonneg U.im]
  have h98 : 98 / 100 ≤ U.re := by
    by_contra h
    push Not at h
    nlinarith
  refine ⟨h98, ?_, ?_⟩
  · have e : (U - 1) * (U + 1) = z - 1 := by rw [← hU]; ring
    have h1 : 198 / 100 ≤ ‖U + 1‖ := by
      have := Complex.abs_re_le_norm (U + 1)
      have h2 : (U + 1).re = U.re + 1 := by simp
      rw [h2, abs_of_nonneg (by linarith)] at this
      linarith
    calc ‖U - 1‖ * (198 / 100) ≤ ‖U - 1‖ * ‖U + 1‖ :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖z - 1‖ := by rw [← norm_mul, e]
  · have := Complex.abs_re_le_norm U
    rw [abs_of_nonneg h0] at this
    linarith

/-- `U = √((ψ + ψ')²)` (P1 (3.37)). -/
noncomputable def tubeU (ψ : Fin N → ℝ) (ψ' : Fin N → ℂ) : ℂ :=
  uExt (dotc (fun i => (ψ i : ℂ) + ψ' i) (fun i => (ψ i : ℂ) + ψ' i))

/-- `V = (ψ + ψ')₀ · (h + h')`, `(ψ + ψ')₀ = (ψ + ψ') / U` (P1 (3.37)). -/
noncomputable def tubeV (ψ : Fin N → ℝ) (ψ' : Fin N → ℂ) (h : Fin N → ℝ) (h' : Fin N → ℂ) : ℂ :=
  dotc (fun i => (ψ i : ℂ) + ψ' i) (fun i => (h i : ℂ) + h' i) / tubeU ψ ψ'

/-- `W² = (h + h')² - V²` (P1 (3.37)). -/
noncomputable def tubeW2 (ψ : Fin N → ℝ) (ψ' : Fin N → ℂ) (h : Fin N → ℝ) (h' : Fin N → ℂ) : ℂ :=
  dotc (fun i => (h i : ℂ) + h' i) (fun i => (h i : ℂ) + h' i) - tubeV ψ ψ' h h' ^ 2


theorem dotc_ofReal (a b : Fin N → ℝ) :
    dotc (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) = ((∑ i, a i * b i : ℝ) : ℂ) := by
  unfold dotc; push_cast; rfl

/-- The normalized vector `s₀ = (ψ + ψ') / U` is a complex unit vector close to `ψ₀`: the
estimates (3.38)-(3.39) and the bound of `s₀ - ψ₀` used in (3.40)-(3.43). -/
theorem tube_aux {σ ε : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1 / 100)
    {ψ : Fin N → ℝ} {ψ' : Fin N → ℂ} (hψ : |∑ i, ψ i ^ 2 - 1| < σ ^ 2 * ε)
    (hψ' : vn ψ' < ε + σ ^ 2 * ε)
    (hb : ‖∑ i, ((ψ i : ℂ) + ψ' i) * ((ψ i : ℂ) + ψ' i) - ∑ i, (ψ i : ℂ) * (ψ i : ℂ)‖ <
      σ ^ 2 * ε) :
    tubeU ψ ψ' ≠ 0 ∧ ‖tubeU ψ ψ' - 1‖ ≤ 2 * (σ ^ 2 * ε) / (198 / 100) ∧
      dotc ((tubeU ψ ψ')⁻¹ • fun i => (ψ i : ℂ) + ψ' i)
        ((tubeU ψ ψ')⁻¹ • fun i => (ψ i : ℂ) + ψ' i) = 1 ∧
      dotc (fun i => ((ψ i / rn ψ : ℝ) : ℂ)) (fun i => ((ψ i / rn ψ : ℝ) : ℂ)) = 1 ∧
      vn (fun i => ((ψ i / rn ψ : ℝ) : ℂ)) = 1 ∧
      vn ((tubeU ψ ψ')⁻¹ • (fun i => (ψ i : ℂ) + ψ' i) - fun i => ((ψ i / rn ψ : ℝ) : ℂ)) ≤
        21 / 5 * ε := by
  have hσ2 : σ ^ 2 ≤ 1 := by nlinarith
  set t : ℝ := σ ^ 2 * ε with ht
  have ht0 : 0 < t := by positivity
  have htε : t ≤ ε := by rw [ht]; nlinarith
  set ρ : ℝ := rn ψ with hρ
  have hρ0 : 0 ≤ ρ := rn_nonneg ψ
  have hρsq : ρ ^ 2 = ∑ i, ψ i ^ 2 := rn_sq_sum ψ
  have hρ2 : |ρ ^ 2 - 1| < t := by rw [hρsq]; exact hψ
  have hρ1 : |ρ - 1| < t := by
    have e : ρ ^ 2 - 1 = (ρ - 1) * (ρ + 1) := by ring
    have : |ρ - 1| ≤ |ρ ^ 2 - 1| := by
      rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ ρ + 1)]
      nlinarith [abs_nonneg (ρ - 1)]
    linarith
  have hρpos : 0 < ρ := by have := (abs_lt.1 hρ1).1; linarith
  set ψ0 : Fin N → ℝ := fun i => ψ i / ρ with hψ0
  set p : Fin N → ℂ := fun i => (ψ0 i : ℂ) with hp
  set s : Fin N → ℂ := fun i => (ψ i : ℂ) + ψ' i with hs
  have hψ0sq : ∑ i, ψ0 i * ψ0 i = 1 := by
    have : ∑ i, ψ0 i * ψ0 i = (∑ i, ψ i ^ 2) / ρ ^ 2 := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by simp only [hψ0]; field_simp
    rw [this, ← hρsq]; field_simp
  have hpp : dotc p p = 1 := by
    rw [hp, dotc_ofReal, hψ0sq]; simp
  have hpn : vn p = 1 := by
    have h1 : rn ψ0 ^ 2 = 1 := by rw [rn_sq_sum]; simpa [sq] using hψ0sq
    have h2 : rn ψ0 = 1 := by nlinarith [rn_nonneg ψ0]
    rw [hp, vn_ofReal, h2]
  set zc : ℂ := dotc s s with hzc
  have hzsum : zc - (ρ ^ 2 : ℝ) = ∑ i, ((ψ i : ℂ) + ψ' i) * ((ψ i : ℂ) + ψ' i) -
      ∑ i, (ψ i : ℂ) * (ψ i : ℂ) := by
    have : ∑ i, (ψ i : ℂ) * (ψ i : ℂ) = ((ρ ^ 2 : ℝ) : ℂ) := by
      rw [hρsq]; push_cast; simp [sq]
    rw [this]; rfl
  have hz1 : ‖zc - 1‖ ≤ 2 * t := by
    have e : zc - 1 = (zc - (ρ ^ 2 : ℝ)) + (((ρ ^ 2 - 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, hzsum]
    have := hb
    linarith
  have hz50 : ‖zc - 1‖ ≤ 1 / 50 := by linarith
  obtain ⟨hUre, hU1, hUn⟩ := uExt_bounds hz50
  have hUdef : tubeU ψ ψ' = uExt zc := rfl
  rw [hUdef]
  set U : ℂ := uExt zc with hU
  have hUU : U * U = zc := uExt_sq zc
  have hU0 : U ≠ 0 := by
    intro h0; rw [h0] at hUn; simp at hUn; linarith
  have hUnear : ‖U - 1‖ ≤ 2 * t / (198 / 100) := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  set s0 : Fin N → ℂ := U⁻¹ • s with hs0
  have hss : dotc s0 s0 = 1 := by
    rw [hs0, dotc_smul_left, dotc_smul_right]
    have : dotc s s = U * U := by rw [hUU]
    rw [this]; field_simp
  have hd0 : s0 - p = (((ρ : ℂ) / U - 1)) • p + U⁻¹ • ψ' := by
    funext i
    simp only [hs0, hs, hp, hψ0, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρpos.ne'
    push_cast
    field_simp
    ring
  have hq : ‖(ρ : ℂ) / U - 1‖ * (98 / 100) ≤ t + 2 * t / (198 / 100) := by
    have e : ((ρ : ℂ) / U - 1) * U = (ρ : ℂ) - U := by field_simp
    have h1 : ‖(ρ : ℂ) / U - 1‖ * ‖U‖ = ‖(ρ : ℂ) - U‖ := by rw [← norm_mul, e]
    have h2 : ‖(ρ : ℂ) - U‖ ≤ |ρ - 1| + ‖U - 1‖ := by
      have e2 : (ρ : ℂ) - U = ((ρ - 1 : ℝ) : ℂ) - (U - 1) := by push_cast; ring
      rw [e2]
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
    calc ‖(ρ : ℂ) / U - 1‖ * (98 / 100) ≤ ‖(ρ : ℂ) / U - 1‖ * ‖U‖ :=
          mul_le_mul_of_nonneg_left hUn (norm_nonneg _)
      _ ≤ _ := by rw [h1]; linarith
  have hUinv : ‖U⁻¹‖ * (98 / 100) ≤ 1 := by
    rw [norm_inv]
    have : 0 < ‖U‖ := norm_pos_iff.2 hU0
    rw [inv_mul_le_iff₀ this]; linarith
  have hvd0 : vn (s0 - p) ≤ 21 / 5 * ε := by
    rw [hd0]
    refine (vn_add_pi _ _).trans ?_
    rw [vn_smul_pi, vn_smul_pi, hpn]
    have hn1 : ‖(ρ : ℂ) / U - 1‖ ≤ (t + 2 * t / (198 / 100)) / (98 / 100) := by
      rw [le_div_iff₀ (by norm_num)]; exact hq
    have hn2 : ‖U⁻¹‖ ≤ 1 / (98 / 100) := by
      rw [le_div_iff₀ (by norm_num)]; exact hUinv
    have hn3 : ‖U⁻¹‖ * vn ψ' ≤ 1 / (98 / 100) * (ε + t) :=
      mul_le_mul hn2 (le_of_lt (by rw [ht]; exact hψ')) (vn_nonneg _) (by norm_num)
    linarith
  exact ⟨hU0, hUnear, hss, hpp, hpn, hvd0⟩

theorem rn_pos_of_close {σ ε : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1 / 100)
    {ψ : Fin N → ℝ} (hψ : |∑ i, ψ i ^ 2 - 1| < σ ^ 2 * ε) : 0 < rn ψ := by
  rcases (rn_nonneg ψ).lt_or_eq with h0 | h0
  · exact h0
  · exfalso
    have : ∑ i, ψ i ^ 2 = 0 := by rw [← rn_sq_sum, ← h0]; simp
    rw [this] at hψ
    simp at hψ
    have : σ ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_pos (pow_pos hσ 2) hε]

/-- The sizes of the real inputs of (3.40)-(3.43): in terms of `R = σ² ε / ν`,
`|ψ₀·h - 1|, |ψ₀·h'| < ε R`, `|h - ψ₀| ≤ (7/4) R`, `|h'| < R`, `ε ≤ R`. -/
theorem tube_sizes {ν σ ε : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hνσ : ν ≤ σ ^ 2)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 100) {ψ h : Fin N → ℝ} {h' : Fin N → ℂ}
    (hψ : |∑ i, ψ i ^ 2 - 1| < σ ^ 2 * ε)
    (hh1 : ν * |1 - (∑ i, ψ i * h i) / rn ψ| < σ ^ 2 * ε ^ 2)
    (hh2 : ν * |∑ i, h i ^ 2 - 1| < σ ^ 2 * ε ^ 2)
    (hhp : ν * vn h' < σ ^ 2 * ε)
    (hψh : ν * ‖∑ i, ((ψ i / rn ψ : ℝ) : ℂ) * h' i‖ < σ ^ 2 * ε ^ 2) :
    ε ≤ σ ^ 2 * ε / ν ∧
    ‖dotc (fun i => ((ψ i / rn ψ : ℝ) : ℂ)) (fun i => (h i : ℂ)) - 1‖ <
      ε * (σ ^ 2 * ε / ν) ∧
    ‖dotc (fun i => ((ψ i / rn ψ : ℝ) : ℂ)) h'‖ < ε * (σ ^ 2 * ε / ν) ∧
    vn ((fun i => (h i : ℂ)) - fun i => ((ψ i / rn ψ : ℝ) : ℂ)) ≤ 7 / 4 * (σ ^ 2 * ε / ν) ∧
    vn h' < σ ^ 2 * ε / ν := by
  set R : ℝ := σ ^ 2 * ε / ν with hR
  have hR0 : 0 < R := by positivity
  have hεR : ε ≤ R := by
    rw [hR, le_div_iff₀ hν]; nlinarith
  have hεRt : σ ^ 2 * ε ^ 2 / ν = ε * R := by rw [hR]; ring
  have hρpos : 0 < rn ψ := rn_pos_of_close hσ hσ1 hε hε1 hψ
  have hρ := rn_sq_sum ψ
  refine ⟨hεR, ?_, ?_, ?_, ?_⟩
  · have e : dotc (fun i => ((ψ i / rn ψ : ℝ) : ℂ)) (fun i => (h i : ℂ)) - 1 =
        (((∑ i, ψ i * h i) / rn ψ - 1 : ℝ) : ℂ) := by
      rw [dotc_ofReal]
      have : ∑ i, ψ i / rn ψ * h i = (∑ i, ψ i * h i) / rn ψ := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [this]; push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, ← hεRt, lt_div_iff₀ hν]
    linarith
  · have : dotc (fun i => ((ψ i / rn ψ : ℝ) : ℂ)) h' =
        ∑ i, ((ψ i / rn ψ : ℝ) : ℂ) * h' i := rfl
    rw [this, ← hεRt, lt_div_iff₀ hν]
    linarith
  · have e : ((fun i => (h i : ℂ)) - fun i => ((ψ i / rn ψ : ℝ) : ℂ)) =
        fun i => ((h i - ψ i / rn ψ : ℝ) : ℂ) := by
      funext i; simp
    rw [e, vn_ofReal]
    have hsq := rn_sq_sum (fun i => h i - ψ i / rn ψ)
    have h1 : ∑ i, (h i - ψ i / rn ψ) ^ 2 =
        (∑ i, h i ^ 2 - 1) + 2 * (1 - (∑ i, ψ i * h i) / rn ψ) := by
      have e2 : ∀ i, (h i - ψ i / rn ψ) ^ 2 =
          h i ^ 2 - 2 * (ψ i * h i / rn ψ) + ψ i ^ 2 / rn ψ ^ 2 := by
        intro i; field_simp; ring
      simp only [e2]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div,
        ← Finset.sum_div, ← hρ]
      field_simp
      ring
    have h2 : |∑ i, h i ^ 2 - 1| < ε * R := by
      rw [← hεRt, lt_div_iff₀ hν]; linarith
    have h3 : |1 - (∑ i, ψ i * h i) / rn ψ| < ε * R := by
      rw [← hεRt, lt_div_iff₀ hν]; linarith
    have h4 : rn (fun i => h i - ψ i / rn ψ) ^ 2 < 3 * R ^ 2 := by
      rw [hsq, h1]
      have := le_abs_self (∑ i, h i ^ 2 - 1)
      have := le_abs_self (1 - (∑ i, ψ i * h i) / rn ψ)
      nlinarith [mul_le_mul_of_nonneg_right hεR hR0.le]
    nlinarith [rn_nonneg (fun i => h i - ψ i / rn ψ)]
  · rw [hR, lt_div_iff₀ hν]; linarith

/-- Arithmetic of the `V`-estimate (3.41): the sum of the five terms is below `22.4 ε R`. -/
theorem tube_numV {ε R Ta Tb vd X hn : ℝ} (hε : 0 < ε) (hR : 0 < R) (hεR : ε ≤ R)
    (hTa : Ta < ε * R) (hTb : Tb < ε * R) (hvd0 : 0 ≤ vd) (hvd : vd ≤ 21 / 5 * ε)
    (hX0 : 0 ≤ X) (hX : X ≤ 7 / 4 * R) (hn0 : 0 ≤ hn) (hhn : hn ≤ R) :
    Ta + Tb + vd * X + 1 / 2 * vd ^ 2 + vd * hn < 22.4 * (ε * R) := by
  have h1 : vd * X ≤ 21 / 5 * ε * (7 / 4 * R) :=
    mul_le_mul hvd hX hX0 (by have := hR; positivity)
  have h2 : vd * hn ≤ 21 / 5 * ε * R := mul_le_mul hvd hhn hn0 (by positivity)
  have h3 : vd ^ 2 ≤ (21 / 5 * ε) ^ 2 := pow_le_pow_left₀ hvd0 hvd 2
  have h4 : ε * ε ≤ ε * R := mul_le_mul_of_nonneg_left hεR hε.le
  nlinarith [mul_pos hε hR]

/-- Arithmetic of the `W²`-estimate (3.43). -/
theorem tube_numW {ε R X hn vd V1 sn : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 100) (hR : 0 < R)
    (hεR : ε ≤ R) (hX0 : 0 ≤ X) (hX : X ≤ 7 / 4 * R) (hn0 : 0 ≤ hn) (hhn : hn ≤ R)
    (hvd0 : 0 ≤ vd) (hvd : vd ≤ 21 / 5 * ε) (hV0 : 0 ≤ V1) (hV : V1 < 22.4 * (ε * R))
    (hsn0 : 0 ≤ sn) (hsn : sn ≤ 1 + 21 / 5 * ε) :
    (X + hn + vd + V1 * sn) ^ 2 < 600.25 * R ^ 2 := by
  have h1 : V1 * sn ≤ 22.4 * (ε * R) * (1 + 21 / 5 * ε) :=
    mul_le_mul hV.le hsn hsn0 (by positivity)
  have h2 : ε * R ≤ 1 / 100 * R := mul_le_mul_of_nonneg_right hε1 hR.le
  have hS : X + hn + vd + V1 * sn ≤ 8 * R := by nlinarith [mul_pos hε hR]
  have hS0 : 0 ≤ X + hn + vd + V1 * sn := by positivity
  have h3 := pow_le_pow_left₀ hS0 hS 2
  nlinarith [pow_pos hR 2]

/-- **P1 Lemma 3.3 (3.44)**: `U, V, W²` map the constant tube `Ψ^c_{const}(σ, ε)` of (3.13)-(3.14)
into the polydisc (3.31): `|U - 1| < (7σ)² ε / 6`, `|V - 1| < (7σ)² ε² / (2ν)`,
`|W²| < (7σ)⁴ ε² / (4ν²)`.

The hypotheses are the conditions (3.13) and (3.14) of `Ψ^c_{const}(σ, ε; ν)` with the derivative
conditions dropped (`ψ ∈ ℝ^N`, `h ∈ ℝ^N` real, `ψ', h' ∈ ℂ^N`): `||ψ|² - 1| < σ² ε`,
`ν |1 - ψ₀·h| < σ² ε²`, `ν ||h|² - 1| < σ² ε²`, `|ψ'| < ε + σ² ε`, `|(ψ + ψ')² - ψ²| < σ² ε`,
`ν |h'| < σ² ε`, `ν |ψ₀·h'| < σ² ε²`, together with the standing assumptions of P1:
`σ ≤ 1`, `ν ≤ σ²` (p. 128) and `ε ≤ 1/100` ("`ε` sufficiently small"). -/
theorem lemma33_tube {ν σ ε : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hνσ : ν ≤ σ ^ 2)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 100) {ψ h : Fin N → ℝ} {ψ' h' : Fin N → ℂ}
    (hψ : |∑ i, ψ i ^ 2 - 1| < σ ^ 2 * ε)
    (hh1 : ν * |1 - (∑ i, ψ i * h i) / rn ψ| < σ ^ 2 * ε ^ 2)
    (hh2 : ν * |∑ i, h i ^ 2 - 1| < σ ^ 2 * ε ^ 2)
    (hψ' : vn ψ' < ε + σ ^ 2 * ε)
    (hb : ‖∑ i, ((ψ i : ℂ) + ψ' i) * ((ψ i : ℂ) + ψ' i) - ∑ i, (ψ i : ℂ) * (ψ i : ℂ)‖ <
      σ ^ 2 * ε)
    (hhp : ν * vn h' < σ ^ 2 * ε)
    (hψh : ν * ‖∑ i, ((ψ i / rn ψ : ℝ) : ℂ) * h' i‖ < σ ^ 2 * ε ^ 2) :
    ‖tubeU ψ ψ' - 1‖ < 1 / 6 * (7 * σ) ^ 2 * ε ∧
    ‖tubeV ψ ψ' h h' - 1‖ < 1 / 2 * (7 * σ) ^ 2 * ε ^ 2 / ν ∧
    ‖tubeW2 ψ ψ' h h'‖ < 1 / 4 * (7 * σ) ^ 4 * ε ^ 2 / ν ^ 2 := by
  obtain ⟨hU0, hUnear, hss, hpp, hpn, hvd0⟩ := tube_aux hσ hσ1 hε hε1 hψ hψ' hb
  obtain ⟨hεR, hTa, hTb, hX, hhn⟩ := tube_sizes hν hσ hσ1 hνσ hε hε1 hψ hh1 hh2 hhp hψh
  set R : ℝ := σ ^ 2 * ε / ν with hR
  have hR0 : 0 < R := by positivity
  have hσ2 : σ ^ 2 ≤ 1 := by nlinarith
  have hεRt : σ ^ 2 * ε ^ 2 / ν = ε * R := by rw [hR]; ring
  set U : ℂ := tubeU ψ ψ' with hU
  set s0 : Fin N → ℂ := U⁻¹ • (fun i => (ψ i : ℂ) + ψ' i) with hs0
  set p : Fin N → ℂ := fun i => ((ψ i / rn ψ : ℝ) : ℂ) with hp
  set hc : Fin N → ℂ := fun i => (h i : ℂ) with hhc
  have hVeq : tubeV ψ ψ' h h' = dotc s0 (hc + h') := by
    rw [hs0, dotc_smul_left]
    unfold tubeV
    rw [div_eq_inv_mul]; rfl
  have c1 : ‖U - 1‖ < 1 / 6 * (7 * σ) ^ 2 * ε := by
    refine hUnear.trans_lt ?_
    rw [div_lt_iff₀ (by norm_num)]
    nlinarith [mul_pos (pow_pos hσ 2) hε]
  have hvd := vn_nonneg (s0 - p)
  have hV := tube_V_bound s0 p hc h' hss hpp
  have hV' : ‖dotc s0 (hc + h') - 1‖ < 22.4 * (ε * R) := by
    have := tube_numV hε hR0 hεR hTa hTb hvd hvd0 (vn_nonneg _) hX (vn_nonneg _) hhn.le
    linarith
  refine ⟨c1, ?_, ?_⟩
  · rw [hVeq]
    have : 22.4 * (ε * R) ≤ 1 / 2 * (7 * σ) ^ 2 * ε ^ 2 / ν := by
      have e : 1 / 2 * (7 * σ) ^ 2 * ε ^ 2 / ν = 24.5 * (ε * R) := by
        rw [← hεRt]; ring
      rw [e]; nlinarith [mul_pos hε hR0]
    exact hV'.trans_le this
  · unfold tubeW2
    rw [hVeq]
    have hW := tube_W_bound s0 p hc h' hss
    have hs0n : vn s0 ≤ 1 + 21 / 5 * ε := by
      have e : s0 = (s0 - p) + p := by abel
      have := vn_add_pi (s0 - p) p
      rw [← e, hpn] at this
      linarith
    refine hW.trans_lt ?_
    have e : 1 / 4 * (7 * σ) ^ 4 * ε ^ 2 / ν ^ 2 = 600.25 * R ^ 2 := by
      rw [hR]; field_simp; ring
    rw [e, norm_sub_rev]
    exact tube_numW hε hε1 hR0 hεR (vn_nonneg _) hX (vn_nonneg _) hhn.le hvd hvd0 (norm_nonneg _)
      (by simpa using hV') (vn_nonneg _) hs0n

section Landed

open Balaban.Multiscale Balaban.Localization

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {ν : ℝ}

/-- **Lemma 3.3 on the landed data domain**: the landed `Ψ̃^c(𝔹; δ, δ)` at a site `x ∈ Ω₁` is the
constant tube `Ψ^c_{const}(1, δ; ν_x)` of (3.13)-(3.14) with `σ = 1`, `ε = δ`, `ν_x = ν ℓ(x)²`
(the weight of the layer of `x`).  So `U, V, W²` of the configuration `(Ψ₀(x), Ψ''(x); h₀, h')` lie in the
polydisc (3.31): `|U - 1| < 49 δ / 6`, `|V - 1| < 49 δ² / (2 ν_x)`, `|W²| < 2401 δ² / (4 ν_x²)`,
for `0 < ν_x ≤ 1` and `δ ≤ 1/100`. -/
theorem tube_of_inPsiTildeC (hν : 0 ≤ ν) (hνk : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ}
    {h₀ : Fin N → ℝ} {Ψ'' : CTorus d L N₁ m₁ k → Fin N → ℂ} {h'' : CTorus d L N₁ m₁ k → Fin N → ℂ}
    (hP : InPsiTildeC G ν δ δ Ψ₀ h₀ Ψ'' h'') {x : CTorus d L N₁ m₁ k} (hx : x ∈ G.Ω 1)
    (hνx : 0 < ν * ((L : ℝ) ^ G.layerIndex x) ^ 2) :
    ‖tubeU (Ψ₀ x) (Ψ'' x) - 1‖ < 1 / 6 * (7 * 1) ^ 2 * δ ∧
    ‖tubeV (Ψ₀ x) (Ψ'' x) h₀ (h'' x) - 1‖ <
      1 / 2 * (7 * 1) ^ 2 * δ ^ 2 / (ν * ((L : ℝ) ^ G.layerIndex x) ^ 2) ∧
    ‖tubeW2 (Ψ₀ x) (Ψ'' x) h₀ (h'' x)‖ <
      1 / 4 * (7 * 1) ^ 4 * δ ^ 2 / (ν * ((L : ℝ) ^ G.layerIndex x) ^ 2) ^ 2 := by
  have hxD : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
  obtain ⟨-, hlk, -⟩ := G.layerIndex_spec hx
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hw : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ ν * ((L : ℝ) ^ k) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (pow_le_pow_right₀ hL1 hlk) 2) hν
  have hw1 : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ 1 ^ 2 := by simpa using hw.trans hνk
  have h1 := hP.r2 x hxD
  have h2 := hP.r3 x hxD
  have h3 := hP.r4
  have h4 := hP.c2a x hxD
  have h5 := hP.c2b x hxD
  have h6 := hP.c3a x hx
  have h7 := hP.c3b x hx
  have hδ2 : δ ^ 2 / δ = δ := by field_simp
  rw [hδ2] at h6
  refine lemma33_tube hνx one_pos le_rfl hw1 hδ hδ1 (by simpa using h1) (by simpa using h2) ?_
    (by simpa using h4) (by simpa using h5) (by simpa using h6) (by simpa using h7)
  have : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * |∑ i, h₀ i ^ 2 - 1| ≤
      ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, h₀ i ^ 2 - 1| :=
    mul_le_mul_of_nonneg_right hw (abs_nonneg _)
  simpa using this.trans_lt h3

end Landed

end Balaban.SmallField
