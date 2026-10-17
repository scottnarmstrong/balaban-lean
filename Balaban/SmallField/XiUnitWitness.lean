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

end Response

end Balaban.SmallField
