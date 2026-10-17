/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassBirthChart
public import Balaban.SmallField.XiLevel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Re-realization of a chart datum at a unit real witness (decision D2(b), blocker 6)

A member `(Ψ₀ + Ψ'', h₀ + h'')` of `Ξ^c_j(𝔹; 1, e)` satisfies only the level-`j` norm clause
`ν L^{2j} | |h₀|² - 1 | < e²`.  The external field enters the background problem through the source
`ν h̃` (and through the weights of the clauses), so replacing the real witness `h₀` by the nearest
unit vector `h₀'` and the displacement `h''` by `h'' + h₀ - h₀'` (which leaves the complex datum
unchanged) moves the real source by `ν |h₀ - h₀'| ≤ ν |(|h₀|² - 1)|`, of size `e² / L^{2j}`.

* `exists_unit_near`: the unit vector `h₀'` with `|h₀ - h₀'| = ||h₀| - 1|`;
* `inPsiTilde_of_unit`: the real datum `(Ψ₀, h₀')` lies in `Ψ̃(2 δ)` if `(Ψ₀, h₀)` lies in the level-`j`
  domain `Ψ̃_{j|k}(δ)`;
* `unitWitness_real`: the response of the real background to `h₀ → h₀'` (Proposition 5.1 with the source
  `ν (h₀' - h₀)`), increments `‖δφ‖_*, |δα|₂ ≤ K₂ e²`;
* `xiC_unitWitness`: the re-realization satisfies `XiC` at level `j` with radius
  `2 e + 2 (N + 1) K₂ e²`.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- `| |h| - 1 | ≤ | |h|² - 1 |`. -/
theorem abs_rn_sub_one_le (h : Fin N → ℝ) : |rn h - 1| ≤ |∑ i, h i ^ 2 - 1| := by
  have hr := rn_nonneg h
  have e : ∑ i, h i ^ 2 - 1 = (rn h - 1) * (rn h + 1) := by
    rw [← rn_sq_sum]; ring
  rw [e, abs_mul, abs_of_pos (by linarith : 0 < rn h + 1)]
  nlinarith [abs_nonneg (rn h - 1)]

/-- **The nearest unit vector.**  For `N ≥ 1` every `h₀ ∈ ℝ^N` has a unit vector `h₀'` with
`|h₀ - h₀'| = ||h₀| - 1|` (the radial projection; any unit vector if `h₀ = 0`). -/
theorem exists_unit_near [NeZero N] (h₀ : Fin N → ℝ) :
    ∃ h₀' : Fin N → ℝ, ∑ i, h₀' i ^ 2 = 1 ∧ rn (fun i => h₀ i - h₀' i) = |rn h₀ - 1| := by
  by_cases hr : rn h₀ = 0
  · have hS : ∑ i, h₀ i ^ 2 = 0 := by rw [← rn_sq_sum, hr]; ring
    have hz : ∀ i, h₀ i = 0 := fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (h₀ i))).1 hS i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    refine ⟨Pi.single (0 : Fin N) 1, ?_, ?_⟩
    · simp [Pi.single_apply]
    · rw [hr]
      unfold rn
      have : ∀ i, (h₀ i - (Pi.single (0 : Fin N) (1 : ℝ) : Fin N → ℝ) i) ^ 2 =
          (Pi.single (0 : Fin N) (1 : ℝ) : Fin N → ℝ) i ^ 2 := fun i => by rw [hz i]; ring
      simp only [this]
      simp [Pi.single_apply]
  · have hpos : 0 < rn h₀ := lt_of_le_of_ne (rn_nonneg h₀) (Ne.symm hr)
    have hsq := rn_sq_sum h₀
    refine ⟨fun i => h₀ i / rn h₀, ?_, ?_⟩
    · have : ∑ i, (h₀ i / rn h₀) ^ 2 = (∑ i, h₀ i ^ 2) / rn h₀ ^ 2 := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by rw [div_pow]
      rw [this, ← hsq]; field_simp
    · have hsum : ∑ i, (h₀ i - h₀ i / rn h₀) ^ 2 = (rn h₀ - 1) ^ 2 := by
        have e : ∀ i, (h₀ i - h₀ i / rn h₀) ^ 2 = (1 - 1 / rn h₀) ^ 2 * h₀ i ^ 2 := fun i => by
          field_simp
        rw [Finset.sum_congr rfl (fun i _ => e i), ← Finset.mul_sum, ← hsq]
        field_simp
      show Real.sqrt (∑ i, (h₀ i - h₀ i / rn h₀) ^ 2) = _
      rw [hsum, Real.sqrt_sq_eq_abs]

/-- `|(Ψ · u) / |Ψ|| ≤ |u|` (Cauchy–Schwarz; the quotient is `0` for `Ψ = 0`). -/
theorem abs_dot_div_rn_le (Ψ u : Fin N → ℝ) : |(∑ i, Ψ i * u i) / rn Ψ| ≤ rn u := by
  by_cases h0 : rn Ψ = 0
  · simp [h0, rn_nonneg]
  · have hpos : 0 < rn Ψ := lt_of_le_of_ne (rn_nonneg Ψ) (Ne.symm h0)
    have h := norm_dot_le (fun i => (Ψ i : ℂ)) (fun i => (u i : ℂ))
    rw [vn_ofReal, vn_ofReal] at h
    have e : (∑ i, (Ψ i : ℂ) * (u i : ℂ)) = ((∑ i, Ψ i * u i : ℝ) : ℂ) := by push_cast; rfl
    rw [e, Complex.norm_real, Real.norm_eq_abs] at h
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    linarith

/-- **The unit witness stays in the real data domain.**  If `(Ψ, h)` lies in the level-`j` domain
`Ψ̃_{j|k}(δ)` (no layers above `j`) and `h'` is a unit vector with `|h - h'| = ||h| - 1|`, then
`(Ψ, h')` lies in `Ψ̃(2 δ)`. -/
theorem inPsiTilde_of_unit {G : GeneratingSet d L N₀ k ϱ} {ν δ : ℝ} {j : ℕ}
    {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h h' : Fin N → ℝ}
    (hΩ : G.Ω (j + 1) = ∅) (hν : 0 ≤ ν) (hδ : 0 < δ) (H : InPsiTildeLevel G ν j δ Ψ h)
    (hu : ∑ i, h' i ^ 2 = 1) (hd : rn (fun i => h i - h' i) = |rn h - 1|) :
    InPsiTilde G ν (2 * δ) Ψ h' where
  layerConst := H.layerConst
  r1 x x' hxx' := (H.r1 x x' hxx').trans_le (by linarith)
  r2 x hx := (H.r2 x hx).trans_le (by linarith)
  r3 x hx := by
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    have hw : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ ν * ((L : ℝ) ^ j) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
        (pow_le_pow_right₀ hL1 (layerIndex_le_of_Ω_empty G hΩ x)) 2) hν
    have hdot : |(∑ i, Ψ x i * h i) / rn (Ψ x) - (∑ i, Ψ x i * h' i) / rn (Ψ x)| ≤
        |rn h - 1| := by
      have e : (∑ i, Ψ x i * h i) / rn (Ψ x) - (∑ i, Ψ x i * h' i) / rn (Ψ x) =
          (∑ i, Ψ x i * (h i - h' i)) / rn (Ψ x) := by
        rw [← sub_div, ← Finset.sum_sub_distrib]
        simp only [mul_sub]
      rw [e]
      exact (abs_dot_div_rn_le (Ψ x) (fun i => h i - h' i)).trans hd.le
    have h3 := H.r3 x hx
    have h4 := H.r4
    have hA : 0 ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 := by positivity
    have hb : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * |rn h - 1| < δ ^ 2 := by
      calc ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * |rn h - 1|
          ≤ ν * ((L : ℝ) ^ j) ^ 2 * |∑ i, h i ^ 2 - 1| :=
            mul_le_mul hw (abs_rn_sub_one_le h) (abs_nonneg _) (by positivity)
        _ < δ ^ 2 := h4
    have htri : |1 - (∑ i, Ψ x i * h' i) / rn (Ψ x)| ≤
        |1 - (∑ i, Ψ x i * h i) / rn (Ψ x)| + |rn h - 1| := by
      have e : 1 - (∑ i, Ψ x i * h' i) / rn (Ψ x) =
          (1 - (∑ i, Ψ x i * h i) / rn (Ψ x)) +
            ((∑ i, Ψ x i * h i) / rn (Ψ x) - (∑ i, Ψ x i * h' i) / rn (Ψ x)) := by ring
      rw [e]
      exact (abs_add_le _ _).trans (add_le_add le_rfl hdot)
    calc ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * |1 - (∑ i, Ψ x i * h' i) / rn (Ψ x)|
        ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
            (|1 - (∑ i, Ψ x i * h i) / rn (Ψ x)| + |rn h - 1|) :=
          mul_le_mul_of_nonneg_left htri hA
      _ = ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * |1 - (∑ i, Ψ x i * h i) / rn (Ψ x)| +
          ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * |rn h - 1| := by ring
      _ < (2 * δ) ^ 2 := by nlinarith
  r4 := by
    rw [hu]
    simp only [sub_self, abs_zero, mul_zero]
    positivity

/-! ### The response of the real background to a change of `h₀` -/

section Response

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem vn_eq_one_of_unit {v : Fin N → ℂ} (him : ∀ i, (v i).im = 0) (hs : ∑ i, v i * v i = 1) :
    vn v = 1 := by
  have h1 : vn v ^ 2 = 1 := by
    rw [vn_sq]
    have := congrArg Complex.re hs
    simp only [Complex.re_sum, Complex.mul_re, him, mul_zero, sub_zero, Complex.one_re] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply, him i]; ring
  nlinarith [vn_nonneg v]

theorem pertSource_zero (f₁ : G.Ω 1 × Fin N → ℂ) :
    pertSource G a (0 : Torus d (N₀ * L ^ k) → Fin N → ℂ) f₁ = f₁ := by
  funext p
  simp [pertSource, qStar, boundaryTerm]

/-- A solution of the perturbed system of Proposition 5.1 with the source `ν (h' - h)` is a
solution of (EL) for the datum with `h` replaced by `h'`. -/
theorem isEL_add_of_isPerturbed {D D' : BgData G N} {φ δφ : G.Ω 1 × Fin N → ℂ}
    {α δα : G.Ω 1 → ℂ} (hΨ : D'.Ψ = D.Ψ) (hφ : IsEL G a ν D φ α)
    {f₁ : G.Ω 1 × Fin N → ℂ} (hf : ∀ p, f₁ p = (ν : ℂ) * (D'.h p.1 p.2 - D.h p.1 p.2))
    (hP : IsPerturbed G a ν α (barField G D.Ψ φ) (pertSource G a 0 f₁) δφ δα) :
    IsEL G a ν D' (φ + δφ) (α + δα) := by
  rw [pertSource_zero] at hP
  refine ⟨funext fun p => ?_, fun x => ?_⟩
  · have e1 := congrFun hφ.1 p
    have e2 := congrFun hP.1 p
    have hφ₀ : barField G D.Ψ φ p.1 p.2 = φ p := by
      obtain ⟨x, i⟩ := p
      simp [barField, x.2]
    rw [hφ₀] at e2
    have hS : source G a ν D' p = source G a ν D p + f₁ p := by
      simp only [source, hΨ, hf]; ring
    rw [liftOp_dirichlet_add, Matrix.mulVec_add, Pi.add_apply, hS]
    simp only [Pi.add_apply] at e2 ⊢
    linear_combination e1 + e2
  · have := hP.2 x
    have hφ₀ : ∀ i, barField G D.Ψ φ x i = φ (x, i) := fun i => by simp [barField, x.2]
    simpa only [hφ₀, Pi.add_apply] using this

theorem supBounds_zero {V : ℝ} (hV : 0 ≤ V) : SupBounds G (0 : G.Ω 1 × Fin N → ℂ) V := by
  refine ⟨fun y i => ?_, fun x hx m i => ?_, fun x hx m i => ?_, fun x hx i => ?_⟩
  · simpa [svec, zeroExt] using hV
  · simpa [svec, zeroExt] using by positivity
  · simpa [svec, zeroExt] using by positivity
  · simpa [svec, zeroExt] using by positivity

theorem small_zero {V : ℝ} (hV : 0 ≤ V) : Small G (0 : G.Ω 1 → ℂ) V := fun x => by
  simpa using hV

/-- The source `ν (h₀' - h₀)` of the change of the real witness is of size `e²`:
`ℓ(x)² ν |h₀' - h₀| ≤ ν L^{2j} ||h₀|² - 1| < e²` when there are no layers above `j`. -/
theorem source_bound {G : GeneratingSet d L N₀ k ϱ} {ν e : ℝ} {j : ℕ} (hΩ : G.Ω (j + 1) = ∅)
    (hν : 0 ≤ ν) {h₀ h₀' : Fin N → ℝ} (hd : rn (fun i => h₀ i - h₀' i) = |rn h₀ - 1|)
    (hnorm : ν * ((L : ℝ) ^ j) ^ 2 * |∑ i, h₀ i ^ 2 - 1| < (1 * e) ^ 2) (x : Torus d (N₀ * L ^ k))
    (i : Fin N) :
    ν * G.spacing x ^ 2 * |h₀' i - h₀ i| < e ^ 2 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hsp : G.spacing x ≤ (L : ℝ) ^ j := by
    unfold GeneratingSet.spacing
    exact pow_le_pow_right₀ hL1 (layerIndex_le_of_Ω_empty G hΩ x)
  have hsp0 : 0 ≤ G.spacing x := by unfold GeneratingSet.spacing; positivity
  have h1 : |h₀' i - h₀ i| ≤ |rn h₀ - 1| := by
    rw [← hd, abs_sub_comm]
    have := norm_le_vn (fun i => ((h₀ i - h₀' i : ℝ) : ℂ)) i
    rw [vn_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  calc ν * G.spacing x ^ 2 * |h₀' i - h₀ i| ≤ ν * ((L : ℝ) ^ j) ^ 2 * |∑ i, h₀ i ^ 2 - 1| :=
        mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsp0 hsp 2) hν)
          (h1.trans (abs_rn_sub_one_le h₀)) (abs_nonneg _) (by positivity)
    _ < e ^ 2 := by simpa using hnorm

/-- **The response of the real background to `h₀ ↦ h₀'`** (decision D2(b); Proposition 5.1 with the
source `f₁ = ν (h₀' - h₀)`).  Let `(Ψ₀, h₀)` be a real datum of `Ξ_j(𝔹; 1, e)` at the mass `ν`
(`Ω_{j+1} = ∅`), and `D'` the datum with the same `Ψ` and `h = h₀'`, where `h₀'` is a unit vector with
`|h₀ - h₀'| = ||h₀| - 1|`.  Then `D'` lies in the real union domain at the mass `ν`, and its
background is that of `D` plus an increment `(δφ, δα)` with `‖δφ‖_*, |δα|₂ ≤ K₂ e²`.
The hypotheses are the smallness conditions of `(D1-j)` (`hsm`), of the domain (`hc1`) and of
Proposition 5.1 (`he1`, `hK2`). -/
theorem unitWitness_real {j : ℕ} {e : ℝ} {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ}
    {h₀ h₀' : Fin N → ℝ} {Dr Dr' : BgData G N} (H : BgHyp d L k ϱ a ν)
    (hΩ : G.Ω (j + 1) = ∅) (he : 0 < e) (hsm : (4 * d + 6) * ((2 * d + 1) * e) ≤ 1)
    (hc1 : 2 * (xiC1 d * e) ≤ bgC1 d L N) (he1 : e ≤ deltaStar d L N)
    (hK2 : e + cK2 d L N * e ^ 2 ≤ bgC0 d L N)
    (hX : XiAt G a ν j 1 e Dr Ψ₀ h₀) (hΨ : Dr'.Ψ = Dr.Ψ)
    (hh' : ∀ x ∈ G.Ω 1, ∀ i, Dr'.h x i = (h₀' i : ℂ))
    (hu : ∑ i, h₀' i ^ 2 = 1) (hd : rn (fun i => h₀ i - h₀' i) = |rn h₀ - 1|) :
    InUnionDomainR G (bgC1 d L N) ν Dr' ∧
      ∃ (δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ),
        bgField G a ν Dr' = bgField G a ν Dr + δφ ∧ bgMult G a ν Dr' = bgMult G a ν Dr + δα ∧
        SupBounds G δφ (cK2 d L N * e ^ 2) ∧ Small G δα (cK2 d L N * e ^ 2) := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hC1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * e := by positivity
  have hX' := hX
  obtain ⟨hR, hDom, hb⟩ := hX
  -- the datum `D'` lies in the real domain
  have hL : InPsiTildeLevel G ν j (compC4 d * xiEta d 1 e) Ψ₀ h₀ :=
    xi_inPsiTildeLevel H hΩ one_pos he le_rfl (by simpa [xiEta] using hsm) hX'
  have e1 : compC4 d * xiEta d 1 e = xiC1 d * e := by
    rw [compC4_mul_xiEta, one_mul]
  rw [e1] at hL
  have hP2 := inPsiTilde_of_unit hΩ H.mass hδ0 hL hu hd
  have hDR' : InUnionDomainR G (bgC1 d L N) ν Dr' :=
    ⟨2 * (xiC1 d * e), by positivity, hc1,
      ⟨Ψ₀, h₀', hP2, fun x hx i => by rw [hΨ]; exact hR.1 x hx i, hh'⟩⟩
  refine ⟨hDR', ?_⟩
  -- the base solution
  obtain ⟨-, hunit, hs, -⟩ := theorem71 H hDom
  set φ := bgField G a ν Dr with hφ
  set α := bgMult G a ν Dr with hα
  have hv1 : ∀ z : G.Ω 1, vn (fun i => φ (z, i)) = 1 := fun z =>
    vn_eq_one_of_unit (fun i => (hunit z).1 i) (hs.1.2 z)
  have hbar : ∀ (x : Torus d (N₀ * L ^ k)) (hx : x ∈ G.Ω 1),
      barField G Dr.Ψ φ x = fun i => φ (⟨x, hx⟩, i) := fun x hx => by
    funext i; simp [barField, hx]
  set f₁ : G.Ω 1 × Fin N → ℂ := fun p => (ν : ℂ) * ((h₀' p.2 : ℂ) - (h₀ p.2 : ℂ)) with hf₁
  have hgd : gdef G (barField G Dr.Ψ φ) = 0 := by
    funext x
    have h1 := hs.1.2 x
    simp only [gdef, hbar x x.2, Pi.zero_apply]
    rw [h1]; ring
  have he1' : e ≤ 1 := he1.trans (deltaStar_le_one (d := d) (L := L) (N := N))
  have he2 : e ^ 2 ≤ e := by nlinarith
  have hP : Prop51Hyp G a ν α (barField G Dr.Ψ φ)
      (0 : Torus d (N₀ * L ^ k) → Fin N → ℂ) f₁ e (e ^ 2) := by
    refine ⟨H.green, he.le, sq_nonneg _, he1, he2.trans he1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := xi_smooth (G := G) one_pos he le_rfl hb
      rw [one_mul] at this
      exact this
    · intro x hx
      have := hv1 ⟨x, hx⟩
      rw [hbar x hx]; simp only [this]; norm_num
    · intro x
      simpa using (hb.mult x).le
    · intro x i
      have h := source_bound hΩ H.mass hd hb.hnorm (x : Torus d (N₀ * L ^ k)) i
      have e2 : ‖f₁ (x, i)‖ = ν * |h₀' i - h₀ i| := by
        simp only [hf₁, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg H.mass]
      rw [e2]; nlinarith
    · intro x hx
      show vn (0 : Fin N → ℂ) ≤ e ^ 2
      rw [vn_zero]; positivity
    · intro x
      rw [hgd]; simp; positivity
    · intro x
      rw [hgd]
      have : zeroExt (G.Ω 1) (0 : G.Ω 1 → ℂ) = 0 := by
        funext y; simp [zeroExt]
      rw [this]; simp [negLap]; positivity
  obtain ⟨δφ, δα, hPert, hsmall, hsup, -⟩ := prop51_exists_unique hd0 hP
  have hEL' := isEL_add_of_isPerturbed hΨ hs.1 (f₁ := f₁)
    (fun p => by simp only [hf₁]; rw [hh' p.1 p.1.2 p.2, hR.2 p.1 p.1.2 p.2]) hPert
  have hsol : IsSmallSolution G a ν (bgC0 d L N) Dr' (φ + δφ) (α + δα) := by
    refine ⟨hEL', fun x => ?_⟩
    have h1 := hb.mult x
    have h2 := hsmall x
    simp only [Pi.add_apply]
    calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x + δα x‖
        ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * (‖α x‖ + ‖δα x‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ = G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x‖ +
          G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖δα x‖ := by ring
      _ < bgC0 d L N := by nlinarith
  have hDC := inUnionDomainC_of_R hd0 H.massLe hDR'
  obtain ⟨⟨s', -, hsu⟩, hsC, -⟩ := theorem72 H hDC
  obtain ⟨hfR, hmR⟩ := theorem72_real H hDR'
  have e1' := hsu (bgFieldC G a ν (bgC0 d L N) Dr', bgMultC G a ν (bgC0 d L N) Dr') hsC
  have e2' := hsu (φ + δφ, α + δα) hsol
  have e3 := e1'.trans e2'.symm
  refine ⟨δφ, δα, ?_, ?_, hsup, hsmall⟩
  · rw [← hfR]; exact congrArg Prod.fst e3
  · rw [← hmR]; exact congrArg Prod.snd e3

/-- The weighted size of the change of the witness: `ℓ(x)² ν ||h₀| - 1| < e²`. -/
theorem weight_bound {G : GeneratingSet d L N₀ k ϱ} {ν e : ℝ} {j : ℕ} (hΩ : G.Ω (j + 1) = ∅)
    (hν : 0 ≤ ν) {h₀ : Fin N → ℝ}
    (hnorm : ν * ((L : ℝ) ^ j) ^ 2 * |∑ i, h₀ i ^ 2 - 1| < (1 * e) ^ 2) (x : Torus d (N₀ * L ^ k)) :
    ν * G.spacing x ^ 2 * |rn h₀ - 1| < e ^ 2 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hsp : G.spacing x ≤ (L : ℝ) ^ j := by
    unfold GeneratingSet.spacing
    exact pow_le_pow_right₀ hL1 (layerIndex_le_of_Ω_empty G hΩ x)
  have hsp0 : 0 ≤ G.spacing x := by unfold GeneratingSet.spacing; positivity
  calc ν * G.spacing x ^ 2 * |rn h₀ - 1| ≤ ν * ((L : ℝ) ^ j) ^ 2 * |∑ i, h₀ i ^ 2 - 1| :=
        mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsp0 hsp 2) hν)
          (abs_rn_sub_one_le h₀) (abs_nonneg _) (by positivity)
    _ < e ^ 2 := by simpa using hnorm

/-- A unit vector `v` is at distance at least `||h₀| - 1|` from `h₀`. -/
theorem abs_rn_sub_one_le_vn {v : Fin N → ℂ} (hv : vn v = 1) (h₀ : Fin N → ℝ) :
    |rn h₀ - 1| ≤ vn (fun i => v i - (h₀ i : ℂ)) := by
  have h1 := vn_le_sub_add (fun i => (h₀ i : ℂ)) v
  have h2 := vn_le_sub_add v (fun i => (h₀ i : ℂ))
  have e : vn (fun i => (h₀ i : ℂ) - v i) = vn (fun i => v i - (h₀ i : ℂ)) := by
    rw [← vn_neg]; congr 1; funext i; ring
  rw [vn_ofReal] at h1 h2
  rw [e, hv] at h1
  rw [hv] at h2
  rw [abs_le]
  constructor <;> linarith

/-- The mass clause for the unit witness: `|v - h₀'| ≤ 2 |v - h₀|` for a unit vector `v`. -/
theorem vn_sub_unit_le {v : Fin N → ℂ} (hv : vn v = 1) {h₀ h₀' : Fin N → ℝ}
    (hd : rn (fun i => h₀ i - h₀' i) = |rn h₀ - 1|) :
    vn (fun i => v i - (h₀' i : ℂ)) ≤ 2 * vn (fun i => v i - (h₀ i : ℂ)) := by
  have h1 := vn_add (fun i => v i - (h₀ i : ℂ)) (fun i => ((h₀ i - h₀' i : ℝ) : ℂ))
  have e : ((fun i => v i - (h₀ i : ℂ)) + fun i => ((h₀ i - h₀' i : ℝ) : ℂ)) =
      fun i => v i - (h₀' i : ℂ) := by
    funext i; simp only [Pi.add_apply]; push_cast; ring
  rw [e, vn_ofReal, hd] at h1
  have := abs_rn_sub_one_le_vn hv h₀
  linarith

end Response

section Mono

variable {G : GeneratingSet d L N₀ k ϱ}

/-- The inequalities of `Ξ^c` are monotone in the radius (`σ = 1`). -/
theorem xiCBounds_mono {ν e e₂ : ℝ} {Dr Dc : BgData G N} {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {φr φc : G.Ω 1 × Fin N → ℂ} {αr αc : G.Ω 1 → ℂ} (he : 0 < e) (hee : e ≤ e₂)
    (hb : XiCBounds G ν 1 e Dr Dc Ψ'' h'' φr φc αr αc) :
    XiCBounds G ν 1 e₂ Dr Dc Ψ'' h'' φr φc αr αc := by
  have hp : ∀ x : Torus d (N₀ * L ^ k), 0 < G.spacing x := fun x => spacing_pos G
  have he2 : 0 < e₂ := he.trans_le hee
  refine ⟨fun x hx m => ?_, fun x hx => ?_, fun x => ?_, fun x => ?_, fun x hx => ?_,
    fun z hz z' hz' hadj => ?_, fun x hx => ?_, fun x => ?_⟩
  · obtain ⟨o1, o2⟩ := hb.grad x hx m
    exact ⟨o1.trans_le (div_le_div_of_nonneg_right (by linarith) (hp x).le),
      o2.trans_le (div_le_div_of_nonneg_right (by linarith) (hp x).le)⟩
  · exact (hb.lap x hx).trans_le (div_le_div_of_nonneg_right (by linarith)
      (by have := hp x; positivity))
  · exact (hb.mult x).trans_le (by linarith)
  · exact (hb.val x).trans_le hee
  · exact (hb.close x hx).trans_le (by linarith)
  · exact (hb.collarBond z hz z' hz' hadj).trans_le (by linarith)
  · have o := hb.hAbs x hx
    have e1 : (1 * e) ^ 2 / e = e := by field_simp
    have e2 : (1 * e₂) ^ 2 / e₂ = e₂ := by field_simp
    rw [e1] at o; rw [e2]; linarith
  · exact (hb.hDot x).trans_le (pow_le_pow_left₀ (by linarith) (by linarith) 2)

end Mono


section Main

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **Re-realization at the unit real witness** (decision D2(b), blocker 6).  A member
`(Ψ₀ + Ψ'', h₀ + h'')` of `Ξ^c_j(𝔹; 1, e)` at the mass `ν` (`Ω_{j+1} = ∅`, `N ≥ 1`) is re-realized
as `(Ψ₀ + Ψ'', h₀' + h''')` with the unit real witness `h₀' = h₀ / |h₀|` and
`h''' = h'' + (h₀ - h₀')`, which realizes the same complex datum `D`, and it lies in
`Ξ^c_j(𝔹; 1, e')` with `e' = 2 e + 2 (N + 1) K₂ e²`, `K₂ = cK2 d L N`.  The factor `2` in `e'` is
the mass clause `√ν ℓ |φ - h₀'| ≤ 2 √ν ℓ |φ - h₀| + …` and cannot be avoided in general (a field
spread over the unit sphere and `h₀ = 0`); everything else changes by `O(K₂ e²)`. -/
theorem xiC_unitWitness [NeZero N] {j : ℕ} {e : ℝ} {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ}
    {h₀ : Fin N → ℝ} {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (H : BgHyp d L k ϱ a ν)
    (hΩ : G.Ω (j + 1) = ∅) (he : 0 < e) (hsm : (4 * d + 6) * ((2 * d + 1) * e) ≤ 1)
    (hc1 : 2 * (xiC1 d * e) ≤ bgC1 d L N) (he1 : e ≤ deltaStar d L N)
    (hK2 : e + cK2 d L N * e ^ 2 ≤ bgC0 d L N) (hX : XiC G a ν j 1 e Ψ₀ h₀ Ψ'' h'') :
    ∃ (h₀' : Fin N → ℝ) (h''' : Torus d (N₀ * L ^ k) → Fin N → ℂ),
      ∑ i, h₀' i ^ 2 = 1 ∧
      XiC G a ν j 1 (2 * e + 2 * ((N : ℝ) + 1) * (cK2 d L N * e ^ 2)) Ψ₀ h₀' Ψ'' h''' ∧
      ∀ D : BgData G N, RealizesC D Ψ₀ h₀ Ψ'' h'' → RealizesC D Ψ₀ h₀' Ψ'' h''' := by
  obtain ⟨-, -, Dr, Dc, hXr, hC, hDcU, hb⟩ := hX
  obtain ⟨h₀', hu, hd⟩ := exists_unit_near h₀
  refine ⟨h₀', fun x i => h'' x i + ((h₀ i : ℂ) - (h₀' i : ℂ)), hu, ?_, ?_⟩
  swap
  · intro D hD
    exact ⟨hD.1, fun x hx i => by rw [hD.2 x hx i]; ring⟩
  have hd0 : 0 < d := by have := H.hd; omega
  -- the new real datum
  let Dc' := BgData.clip G Dr.Ψ (fun _ i => ((h₀' i : ℝ) : ℂ)) Dr.Ψ_layerConst
    (fun _ _ _ _ _ _ _ => rfl)
  let Dr' : BgData G N :=
    { Dr with h := Dc'.h, h_layerConst := Dc'.h_layerConst, h_zero := Dc'.h_zero }
  have hh' : ∀ x ∈ G.Ω 1, ∀ i, Dr'.h x i = (h₀' i : ℂ) := fun x hx i => by
    simp [Dr', Dc', BgData.clip, hx]
  obtain ⟨hDR', δφ, δα, hfe, hme, hsup, hsmall⟩ :=
    unitWitness_real (Dr' := Dr') H hΩ he hsm hc1 he1 hK2 hXr rfl hh' hu hd
  set V : ℝ := cK2 d L N * e ^ 2 with hVdef
  have hV : 0 ≤ V := by have := cK2_pos d L N; positivity
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNV : 0 ≤ (N : ℝ) * V := mul_nonneg hN hV
  have he1' : e ≤ 1 := he1.trans (deltaStar_le_one (d := d) (L := L) (N := N))
  set ef : ℝ := 2 * e + 2 * ((N : ℝ) + 1) * V with hef
  have hef0 : 0 < ef := by rw [hef]; positivity
  have hnormj := hXr.2.2.hnorm
  obtain ⟨him, hunit⟩ := xi_unit H hXr
  have hv1 : ∀ z : G.Ω 1, vn (fun i => bgField G a ν Dr (z, i)) = 1 := fun z =>
    vn_eq_one_of_unit (fun i => him z i) (hunit z)
  -- the real inequalities
  have hR1 : XiBounds G ν j 1 ef Dr h₀ (bgField G a ν Dr + δφ) (bgMult G a ν Dr + δα) :=
    xiBounds_massResponse (s := 0) le_rfl he hV H.mass (by simp) H.massLe
      (by rw [hef]; nlinarith) (by rw [hef]; nlinarith) hXr.2.2 hsup hsmall
  have hXB : XiBounds G ν j 1 ef Dr' h₀' (bgField G a ν Dr + δφ) (bgMult G a ν Dr + δα) := by
    refine ⟨hR1.grad, hR1.lap, hR1.mult, hR1.close, hR1.collarBond, fun z => ?_, ?_⟩
    · have o := hXr.2.2.mass z
      have hz1 : Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ k)) ≤ 1 :=
        sqrt_mul_spacing_le_one H.mass H.massLe G _
      have hA : 0 ≤ Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ k)) := by
        have := spacing_pos G (x := (z : Torus d (N₀ * L ^ k))); positivity
      have e1 : (fun i => (bgField G a ν Dr + δφ) (z, i) - (h₀' i : ℂ)) =
          (fun i => bgField G a ν Dr (z, i) - (h₀' i : ℂ)) + fun i => δφ (z, i) := by
        funext i; simp only [Pi.add_apply]; ring
      rw [e1]
      have t1 := vn_add (fun i => bgField G a ν Dr (z, i) - (h₀' i : ℂ)) (fun i => δφ (z, i))
      have t2 := vn_sub_unit_le (hv1 z) hd
      have t3 : vn (fun i => δφ (z, i)) ≤ N * V := by
        have := incr_val hV hsup (z : Torus d (N₀ * L ^ k))
        simpa [svec_of_mem G δφ z] using this
      calc Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ k)) *
            vn ((fun i => bgField G a ν Dr (z, i) - (h₀' i : ℂ)) + fun i => δφ (z, i))
          ≤ Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ k)) *
            (2 * vn (fun i => bgField G a ν Dr (z, i) - (h₀ i : ℂ)) + N * V) :=
            mul_le_mul_of_nonneg_left (by linarith) hA
        _ = 2 * (Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ k)) *
              vn (fun i => bgField G a ν Dr (z, i) - (h₀ i : ℂ))) +
            Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ k)) * (N * V) := by ring
        _ < 1 * ef := by
            have : Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ k)) * (N * V) ≤ N * V := by
              nlinarith
            rw [hef]; nlinarith
    · rw [hu]
      simp only [sub_self, abs_zero, mul_zero]
      positivity
  have hRe' : Realizes Dr' Ψ₀ h₀' := ⟨fun x hx i => hXr.1.1 x hx i, hh'⟩
  have hXAt : XiAt G a ν j 1 ef Dr' Ψ₀ h₀' := by
    refine ⟨hRe', hDR', ?_⟩
    rw [hfe, hme]; exact hXB
  -- the complex inequalities
  have hm := xiCBounds_mono he (by linarith : e ≤ 2 * e) hb
  have hrw : ∀ x : Torus d (N₀ * L ^ k), ν * G.spacing x ^ 2 * |rn h₀ - 1| < e ^ 2 :=
    fun x => weight_bound hΩ H.mass hnormj x
  have hcv : vn (fun i => (h₀ i : ℂ) - (h₀' i : ℂ)) = |rn h₀ - 1| := by
    rw [← hd, ← vn_ofReal]; congr 1; funext i; push_cast; ring
  have hb₁ : XiCBounds G ν 1 (2 * e) Dr Dc Ψ'' (fun x i => h'' x i + ((h₀ i : ℂ) - (h₀' i : ℂ)))
      (bgField G a ν Dr) (bgFieldC G a ν (bgC0 d L N) Dc) (bgMult G a ν Dr)
      (bgMultC G a ν (bgC0 d L N) Dc) := by
    refine ⟨hm.grad, hm.lap, hm.mult, hm.val, hm.close, hm.collarBond, fun x hx => ?_,
      fun x => ?_⟩
    · have o := hb.hAbs x hx
      have e1 : (1 * e) ^ 2 / e = e := by field_simp
      have e2 : (1 * (2 * e)) ^ 2 / (2 * e) = 2 * e := by field_simp
      rw [e1] at o; rw [e2]
      have t := vn_add (h'' x) (fun i => (h₀ i : ℂ) - (h₀' i : ℂ))
      have hA : 0 ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 := by have := H.mass; positivity
      have hs : G.spacing x = (L : ℝ) ^ G.layerIndex x := rfl
      have w := hrw x
      rw [hs] at w
      calc ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h'' x + fun i => (h₀ i : ℂ) - (h₀' i : ℂ))
          ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
            (vn (h'' x) + vn (fun i => (h₀ i : ℂ) - (h₀' i : ℂ))) :=
            mul_le_mul_of_nonneg_left t hA
        _ = ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h'' x) +
            ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * |rn h₀ - 1| := by rw [hcv]; ring
        _ < 2 * e := by nlinarith
    · have o := hb.hDot x
      have hA : 0 ≤ ν * ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 := by
        have := H.mass; positivity
      have hs : G.spacing (x : Torus d (N₀ * L ^ k)) =
          (L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k)) := rfl
      have w := hrw (x : Torus d (N₀ * L ^ k))
      rw [hs] at w
      have esum : (∑ i, bgField G a ν Dr (x, i) * (h'' x i + ((h₀ i : ℂ) - (h₀' i : ℂ)))) =
          (∑ i, bgField G a ν Dr (x, i) * h'' x i) +
            ∑ i, bgField G a ν Dr (x, i) * ((h₀ i : ℂ) - (h₀' i : ℂ)) := by
        simp only [mul_add, Finset.sum_add_distrib]
      rw [esum]
      have t1 := norm_add_le (∑ i, bgField G a ν Dr (x, i) * h'' x i)
        (∑ i, bgField G a ν Dr (x, i) * ((h₀ i : ℂ) - (h₀' i : ℂ)))
      have t2 := norm_dot_le (fun i => bgField G a ν Dr (x, i))
        (fun i => (h₀ i : ℂ) - (h₀' i : ℂ))
      rw [hv1 x, hcv, one_mul] at t2
      calc ν * ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 *
            ‖(∑ i, bgField G a ν Dr (x, i) * h'' x i) +
              ∑ i, bgField G a ν Dr (x, i) * ((h₀ i : ℂ) - (h₀' i : ℂ))‖
          ≤ ν * ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 *
            (‖∑ i, bgField G a ν Dr (x, i) * h'' x i‖ + |rn h₀ - 1|) :=
            mul_le_mul_of_nonneg_left (t1.trans (add_le_add le_rfl t2)) hA
        _ = ν * ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 *
              ‖∑ i, bgField G a ν Dr (x, i) * h'' x i‖ +
            ν * ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 * |rn h₀ - 1| := by ring
        _ < (1 * (2 * e)) ^ 2 := by nlinarith
  have hCB := xiCBounds_massResponse (s := 0) (μ := ν) (e := 2 * e) (e' := ef) (V := V)
    (δc := 0) (δαc := 0) le_rfl (by linarith) hV H.mass (by simp)
    (by rw [hef]; nlinarith) (by rw [hef]; nlinarith) (by rw [hef]; nlinarith)
    (by rw [hef]; nlinarith [mul_nonneg he.le hV, mul_nonneg (mul_nonneg he.le hV) hN,
      sq_nonneg (((N : ℝ) + 1) * V)])
    hb₁ hsup (supBounds_zero hV) hsmall (small_zero hV)
  simp only [add_zero] at hCB
  refine ⟨one_pos, hef0, Dr', Dc, hXAt, ⟨hC.1, fun x hx i => by rw [hC.2 x hx i]; ring⟩,
    hDcU, ?_⟩
  rw [hfe, hme]
  exact ⟨hCB.grad, hCB.lap, hCB.mult, hCB.val, hCB.close, hCB.collarBond, hCB.hAbs, hCB.hDot⟩

end Main

end Balaban.SmallField

namespace Balaban.Fluctuation

open Finset Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6v2 Balaban.Flow

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The smallness conditions of `xiC_unitWitness` for the radius `e` follow from those at the larger
radius `E = 2 e + 2 (N + 1) K₂ e²` of the birth inclusion. -/
theorem unitWitness_numerics {e E r : ℝ} (hd : 0 < d) (he : 0 < e)
    (hE : E = 2 * e + 2 * ((N : ℝ) + 1) * (cK2 d L N * e ^ 2)) (hr0 : 0 ≤ r)
    (hsm : (4 * d + 6) * ((2 * d + 1) * E) ≤ 1) (hc1 : 4 * (xiC1 d * E) ≤ bgC1 d L N)
    (hK : bgK1 d L N * (xiC1 d * E) + 3 * r ≤ deltaStar d L N) :
    (4 * d + 6) * ((2 * d + 1) * e) ≤ 1 ∧ 2 * (xiC1 d * e) ≤ bgC1 d L N ∧
      e ≤ deltaStar d L N ∧ e + cK2 d L N * e ^ 2 ≤ bgC0 d L N := by
  have hK2 := cK2_pos d L N
  have hC1 := one_le_xiC1 d
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hq : 0 ≤ cK2 d L N * e ^ 2 := by positivity
  have hq' : 0 ≤ ((N : ℝ) + 1) * (cK2 d L N * e ^ 2) := by positivity
  have heE : e ≤ E := by rw [hE]; nlinarith
  have hKE : e + cK2 d L N * e ^ 2 ≤ E := by rw [hE]; nlinarith
  have hE0 : 0 < E := he.trans_le heE
  have hCE : E ≤ xiC1 d * E := le_mul_of_one_le_left hE0.le hC1
  have hB1 := bgK1_ge_one (d := d) (L := L) (N := N)
  have hCK : xiC1 d * E ≤ bgK1 d L N * (xiC1 d * E) :=
    le_mul_of_one_le_left (by positivity) hB1
  have hc0 := bgC1_le_bgC0 d L N hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine le_trans ?_ hsm; gcongr
  · nlinarith
  · linarith
  · linarith

/-- **The birth inclusion without the unit-witness hypothesis** (decision D2(b), blocker 6).  The
chart point `D` realizes a member of `Ξ^c_j(𝔹; C₀, e)` at the step mass `ν`, with a possibly
non-unit real witness; the layers above `j` are empty.  It is re-realized at the unit witness
`h₀ / |h₀|` (`xiC_unitWitness`), in `Ξ^c_j(𝔹; 1, E)` with `E = 2 e₁ + 2 (N + 1) K₂ e₁²`,
`e₁ ≥ C₀² e`, and then lies in the birth-mass domain `Ξ^c_j(𝔹; 1, ε_j)` at `μ = ν (1 + t)` as
soon as `E (1 + K_m |t|) ≤ ε_j`. -/
theorem xiDom_birth_of_realization [NeZero N] {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ}
    {A : ℕ → ℝ} {ν μ C₀ e e₁ E εj t r : ℝ} {j : ℕ} (H : BgHyp d L k ϱ A ν)
    (H' : BgHyp d L k ϱ A μ) (hΩ : G.Ω (j + 1) = ∅) (hσ : 1 ≤ C₀) (hrad : C₀ ^ 2 * e ≤ e₁)
    (hε : 0 < e₁) (hE : E = 2 * e₁ + 2 * ((N : ℝ) + 1) * (cK2 d L N * e₁ ^ 2))
    (hsm : (4 * d + 6) * ((2 * d + 1) * E) ≤ 1) (hc1 : 4 * (xiC1 d * E) ≤ bgC1 d L N)
    (hμ : μ = ν * (1 + t)) (ht1 : |t| ≤ 1) (htr : |t| < r) (hr : r ≤ 1 / 16)
    (hK : bgK1 d L N * (xiC1 d * E) + 3 * r ≤ deltaStar d L N)
    (hζ : 8 * E * r ≤ deltaStar d L N)
    (hee : E * (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * |t|) ≤ εj)
    {D : BgData G N}
    (hD : ∃ (Ψ₀ : Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ)
        (Ψ'' h'' : Localization.CTorus d L N₁ m₁ k → Fin N → ℂ),
      XiC G A ν j C₀ e Ψ₀ h₀ Ψ'' h'' ∧ RealizesC D Ψ₀ h₀ Ψ'' h'') :
    Def6.XiDom G A μ j εj D.Ψ D.h := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hxc, hR⟩ := hD
  have hd0 : 0 < d := by have := H.hd; omega
  have hr0 : 0 ≤ r := (abs_nonneg t).trans htr.le
  obtain ⟨n1, n2, n3, n4⟩ := unitWitness_numerics (N := N) hd0 hε hE hr0 hsm hc1 hK
  have hR' : RealizesC D Ψ₀ h₀ (fun x i => D.Ψ x i - Ψ₀ x i) (fun x i => D.h x i - h₀ i) :=
    ⟨fun x hx i => by simp [hR.1 x hx i], fun x hx i => by simp [hR.2 x hx i]⟩
  have hx1 : XiC G A ν j 1 e₁ Ψ₀ h₀ (fun x i => D.Ψ x i - Ψ₀ x i) (fun x i => D.h x i - h₀ i) :=
    xiC_rescale_of_agree hσ hrad (fun x hx i => by rw [hR.1 x hx i]; ring)
      (fun x hx i => by rw [hR.2 x hx i]; ring) hxc
  have hEpos : 0 < E := by rw [hE]; have := cK2_pos d L N; positivity
  obtain ⟨h₀', h''', hu, hxE, hRe⟩ := xiC_unitWitness H hΩ hε n1 n2 n3 n4 hx1
  rw [← hE] at hxE
  exact xiDom_birth_of_unit_realization (C₀ := 1) (e := E) (e₁ := E) H H' le_rfl (by simp)
    hEpos
    hsm hc1 hμ ht1 htr hr hK hζ hee ⟨Ψ₀, h₀', _, h''', hxE, hRe D hR', hu⟩

/-- **The chart point lies in the birth-mass domain, without the unit-witness hypothesis**
(decision D2(b)).  The chart data of `ClassOldCover.hchart`: `D` realizes a member of
`Ξ^c_j(𝔹; C₀, e)` at the step mass `ν`, `C₀ = scaledC0 d`, `e = C₀² ε′ + K₂ δ₃ + K₂ δfl`, with
no condition on the real witness; the layers above `j` are empty.  With `E₁ = C₀² e` the (DL-gap) is
`(2 E₁ + 2 (N + 1) K₂ E₁²) (1 + K_m τ) ≤ ε_j`, `K_m = 1 + 16 (N + 1) K₂`, and the other hypotheses
are those of `xiDom_birth_chart`. -/
theorem xiDom_birth_chart_unitfree [NeZero N] {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ}
    {A : ℕ → ℝ} {ν μ eps δ₃ δfl εj τ r t : ℝ} {j : ℕ} (H : BgHyp d L k ϱ A ν)
    (H' : BgHyp d L k ϱ A μ) (hΩ : G.Ω (j + 1) = ∅)
    (heps : 0 < eps) (hδ₃ : 0 ≤ δ₃) (hδfl : 0 ≤ δfl)
    (hμ : μ = ν * (1 + t)) (ht : |t| ≤ τ) (hτr : τ < r) (hr : r ≤ 1 / 16)
    (hDL : (2 * (scaledC0 d ^ 2 *
          (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)) +
        2 * ((N : ℝ) + 1) * (cK2 d L N * (scaledC0 d ^ 2 *
          (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)) ^ 2)) *
      (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τ) ≤ εj)
    (hsmε : (4 * d + 6) * ((2 * d + 1) * εj) ≤ 1) (hc1ε : 4 * (xiC1 d * εj) ≤ bgC1 d L N)
    (hKε : bgK1 d L N * (xiC1 d * εj) + 3 * r ≤ deltaStar d L N)
    (hζε : 8 * εj * r ≤ deltaStar d L N)
    {D : BgData G N}
    (hD : Localization.XiCData G A ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) D) :
    Def6.XiDom G A μ j εj D.Ψ D.h := by
  have hd : 0 < d := by have := H.hd; omega
  have hC : 0 < scaledC0 d := by unfold scaledC0; positivity
  have hQ := cK2_pos d L N
  have hK2 : 0 < xiK2 d L N := by unfold xiK2; positivity
  have hE₁ : 0 < scaledC0 d ^ 2 *
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) := by positivity
  set E₁ := scaledC0 d ^ 2 * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
    with hE₁def
  set E := 2 * E₁ + 2 * ((N : ℝ) + 1) * (cK2 d L N * E₁ ^ 2) with hEdef
  have hE0 : 0 < E := by rw [hEdef]; positivity
  have hEq : scaledC0 d ^ 2 * (scaledC0 d ^ 2 * (E / scaledC0 d ^ 4) + xiK2 d L N * 0 +
      xiK2 d L N * 0) = E := by
    have : scaledC0 d ≠ 0 := hC.ne'
    field_simp
    ring
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7⟩ := chart_numerics (L := L) (N := N) hd
    (eps := E / scaledC0 d ^ 4) (δ₃ := 0) (δfl := 0) (by positivity) le_rfl le_rfl ht hτr hr
    (by rw [hEq]; exact hDL) hsmε hc1ε hKε hζε
  rw [hEq] at n1 n2 n5 n6 n7
  exact xiDom_birth_of_realization (C₀ := scaledC0 d) (e₁ := E₁) (E := E) H H' hΩ
    (one_le_scaledC0 d) le_rfl hE₁ rfl n1 n2 hμ n3 n4 hr n5 n6 n7 hD

/-- **`hchart` at the birth mass, without the unit-witness hypothesis.**  The raw data of the chart
`Ξ^c_j(𝔹; C₀, e)` at the step mass `ν` lie in `xiFieldDom A μ ε`, under the (DL-gap) of
`xiDom_birth_chart_unitfree`; the layers above `j` are empty.  This replaces `hunit` of
`xiCRaw_dom_birth`. -/
theorem xiCRaw_dom_birth_unitfree [NeZero N] {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ}
    {A : ℕ → ℝ} {ν μ eps δ₃ δfl τ r t : ℝ} {εs : ℕ → ℝ} {j : ℕ} (H : BgHyp d L k ϱ A ν)
    (H' : BgHyp d L k ϱ A μ) (hΩ : G.Ω (j + 1) = ∅)
    (heps : 0 < eps) (hδ₃ : 0 ≤ δ₃) (hδfl : 0 ≤ δfl)
    (hμ : μ = ν * (1 + t)) (ht : |t| ≤ τ) (hτr : τ < r) (hr : r ≤ 1 / 16)
    (hDL : (2 * (scaledC0 d ^ 2 *
          (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)) +
        2 * ((N : ℝ) + 1) * (cK2 d L N * (scaledC0 d ^ 2 *
          (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)) ^ 2)) *
      (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τ) ≤ εs j)
    (hsmε : (4 * d + 6) * ((2 * d + 1) * εs j) ≤ 1) (hc1ε : 4 * (xiC1 d * εs j) ≤ bgC1 d L N)
    (hKε : bgK1 d L N * (xiC1 d * εs j) + 3 * r ≤ deltaStar d L N)
    (hζε : 8 * εs j * r ≤ deltaStar d L N) :
    ∀ p ∈ Localization.XiCRaw G A ν j (scaledC0 d)
        (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      (xiFieldDom A μ εs : FieldDom d L N₁ m₁ k N ϱ).dom j G p.1 p.2 := by
  rintro p ⟨D, hD, rfl⟩
  exact xiDom_birth_chart_unitfree H H' hΩ heps hδ₃ hδfl hμ ht hτr hr hDL hsmε hc1ε hKε hζε hD

/-- If `μ = ν P` with `P` complex and `μ`, `ν` real, then `μ = ν (1 + t)` with `t` real and
`|t| ≤ ‖P - 1‖`. -/
theorem exists_real_defect {ν μ : ℝ} {P : ℂ} (hμ : (μ : ℂ) = ν * P) :
    ∃ t : ℝ, μ = ν * (1 + t) ∧ |t| ≤ ‖P - 1‖ := by
  by_cases hν : ν = 0
  · have : μ = 0 := by
      have h0 : (μ : ℂ) = 0 := by rw [hμ, hν]; simp
      exact_mod_cast h0
    exact ⟨0, by simp [this, hν], by simp⟩
  · refine ⟨μ / ν - 1, by field_simp; ring, ?_⟩
    have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
    have e : (((μ / ν - 1 : ℝ)) : ℂ) = P - 1 := by
      push_cast
      rw [hμ]; field_simp
    rw [← e, Complex.norm_real, Real.norm_eq_abs]

/-- **`xiCRaw_dom_birth_unitfree` with the birth mass given by the flow**: `μ = ν ∏_{n ∈ [j, K)}
(1 + ξ₃^{(n)})/(1 + ξ₂^{(n)})` and `‖ξ_n‖ ≤ (c₈/4) q^{n+1}`; the mass defect is
`τ = exp (3 (c₈/4) q^{j+1}/(1-q)) - 1`. -/
theorem xiCRaw_dom_birth_flow_unitfree [NeZero N] {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ}
    {A : ℕ → ℝ} {ν μ eps δ₃ δfl r : ℝ} {εs : ℕ → ℝ} {j K : ℕ} {ξ : ℕ → Fin 3 → ℂ} {q c₈ : ℝ}
    (H : BgHyp d L k ϱ A ν) (H' : BgHyp d L k ϱ A μ) (hΩ : G.Ω (j + 1) = ∅)
    (heps : 0 < eps) (hδ₃ : 0 ≤ δ₃) (hδfl : 0 ≤ δfl)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c₈) (hs : c₈ * q ≤ 1 - q)
    (hξ : ∀ n, ‖ξ n‖ ≤ c₈ / 4 * q ^ (n + 1))
    (hμ : (μ : ℂ) = ν * ∏ n ∈ Ico j K, ((1 + ξ n 2) / (1 + ξ n 1)))
    (hτr : Real.exp (3 * (c₈ / 4 * (q ^ (j + 1) / (1 - q)))) - 1 < r) (hr : r ≤ 1 / 16)
    (hDL : (2 * (scaledC0 d ^ 2 *
          (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)) +
        2 * ((N : ℝ) + 1) * (cK2 d L N * (scaledC0 d ^ 2 *
          (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)) ^ 2)) *
      (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) *
        (Real.exp (3 * (c₈ / 4 * (q ^ (j + 1) / (1 - q)))) - 1)) ≤ εs j)
    (hsmε : (4 * d + 6) * ((2 * d + 1) * εs j) ≤ 1) (hc1ε : 4 * (xiC1 d * εs j) ≤ bgC1 d L N)
    (hKε : bgK1 d L N * (xiC1 d * εs j) + 3 * r ≤ deltaStar d L N)
    (hζε : 8 * εs j * r ≤ deltaStar d L N) :
    ∀ p ∈ Localization.XiCRaw G A ν j (scaledC0 d)
        (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      (xiFieldDom A μ εs : FieldDom d L N₁ m₁ k N ϱ).dom j G p.1 p.2 := by
  have hbd := norm_ratio_prod_sub_one_le_geom hq0 hq1 hc hs hξ j K
  obtain ⟨t, ht, htb⟩ := exists_real_defect hμ
  exact xiCRaw_dom_birth_unitfree H H' hΩ heps hδ₃ hδfl ht (htb.trans hbd) hτr hr hDL hsmε hc1ε
    hKε hζε

end Balaban.Fluctuation
