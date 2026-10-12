/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CubeActionShift
public import Balaban.Fluctuation.FarDecayUncond
public import Balaban.LargeField.Characteristic.Reg
import Balaban.Multiscale.ConstraintKernel
import Balaban.Multiscale.Locality
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 4.2, Step 3 (undecoupled): the bound `|F_□| ≤ C_F' β r² e^{-γ_w D}`
(FLUCTUATION.md §4.2, Step 3)

* `cubeDiff_bound_of_far`: given the far-decay bounds (4.1) for the change `τ = δφ` of the
  background (`FarBounds`) and the regularity inequalities `RegIneq` of the data on the
  neighbourhood `R` of the cube (these are the inequalities of `Δ^c_j(□; 1, r)`, Definition II.3.5
  (a): `DeltaC` is `RegC` for the lifted data), the cube action difference is at most
  `½ |Q| (d + 3) N (2 r T + T²)`, `T = B e^{-γ Dist}`;
* `cubeDiff_step3`: the same with `FarBounds` supplied by the unconditional weighted response
  `lemma41_domain_uncond` (`B = K_w C_F δ₁`, `γ = γ_w`);
* `cubeDiff_step3_quadratic`: with `δ₁ ≤ C_δ r` (Step 1), `|β F_□| ≤ C_F' β |Q| r² e^{-γ_w Dist}`.

The decoupled version (the decoupling polydisc `|s_P| ≤ e^{κ₁}`) would additionally need the
decoupled weighted response, which is the open mixed-pair input (OPEN-NC-MIXED); here the data
are undecoupled.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField

section Far

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

theorem decay_le_exp_dist {γ Dist : ℝ} (hγ : 0 ≤ γ) {D : ENNReal}
    (h : ENNReal.ofReal Dist ≤ D) : decay γ D ≤ Real.exp (-(γ * Dist)) := by
  by_cases hD' : D = ⊤
  · rw [hD', decay_top]; exact (Real.exp_pos _).le
  · rw [decay_of_ne_top hD']
    refine Real.exp_le_exp.2 ?_
    have : Dist ≤ D.toReal := (ENNReal.ofReal_le_iff_le_toReal hD').1 h
    nlinarith


variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- The weights `a_n L^{-2n}` of the block term are at most `2` on `Ω₁`. -/
theorem blockWeight_le (hw : IsAdmissibleWeights K a) (x : G.Ω 1) :
    ‖((a (G.layerIndex (x : CTorus d L N₁ m₁ K)) /
      ((L : ℝ) ^ G.layerIndex (x : CTorus d L N₁ m₁ K)) ^ 2 : ℝ) : ℂ)‖ ≤ 2 := by
  obtain ⟨h1, h2, -⟩ := G.layerIndex_spec x.2
  have ha := hw _ h1 h2
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hp : (1 : ℝ) ≤ ((L : ℝ) ^ G.layerIndex (x : CTorus d L N₁ m₁ K)) ^ 2 :=
    one_le_pow₀ (one_le_pow₀ hL)
  rw [Complex.norm_real, Real.norm_of_nonneg (div_nonneg (by linarith [ha.1]) (by linarith))]
  rw [div_le_iff₀ (by linarith)]
  nlinarith [ha.2]


theorem blockAvg_norm_le (τ : G.Ω 1 × Fin N → ℂ) {T : ℝ}
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.Ω 1)
    (hbd : ∀ y ∈ G.blk (G.layerIndex x) x, ∀ (hy : y ∈ G.Ω 1) (i : Fin N), ‖τ (⟨y, hy⟩, i)‖ ≤ T)
    (i : Fin N) : ‖blockAvg G τ x i‖ ≤ T := by
  obtain ⟨h1, h2, hxl⟩ := G.layerIndex_spec hx
  have hsub := blk_subset_Ω G h1 h2 hxl
  unfold blockAvg
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hsum : ‖∑ y ∈ G.blk (G.layerIndex x) x, svec G τ y i‖ ≤
      ((G.blk (G.layerIndex x) x).card : ℝ) * T := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ y ∈ G.blk (G.layerIndex x) x, ‖svec G τ y i‖
        ≤ ∑ _y ∈ G.blk (G.layerIndex x) x, T := by
          refine Finset.sum_le_sum fun y hy => ?_
          rw [svec_of_mem G τ ⟨y, hsub hy⟩ i]
          exact hbd y hy (hsub hy) i
      _ = _ := by simp
  rw [card_blk G _ h2] at hsum
  have hpos : (0 : ℝ) < (((L : ℝ) ^ G.layerIndex x) ^ d) := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  calc (((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ * ‖∑ y ∈ G.blk (G.layerIndex x) x, svec G τ y i‖
      ≤ (((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ * ((((L ^ G.layerIndex x) ^ d : ℕ) : ℝ) * T) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = T := by push_cast; field_simp


open Classical in
/-- **Step 3, the bound on `F_□` from the far-decay of the data change.**  Let `D` be the data of
the background `φ = bgFieldC D`, `τ = δφ` its change, bounded as in (4.1) (`FarBounds`, here with
distance `Dist` from the neighbourhood `R` of the cube to the support of the data change), and let
`D` satisfy the regularity inequalities `RegIneq` with radius `r` on `R` (the content of the
membership of the complex data in `Δ^c`, Definition II.3.5 (a)).  Then
`|A_Q(φ + τ) - A_Q(φ)| ≤ ½ |Q| (W + d + 1) N (2 r T + T²)`, `T = B e^{-γ Dist}`, `W = 2`. -/
theorem cubeDiff_bound_of_far (hw : IsAdmissibleWeights K a) (hν0 : 0 ≤ ν)
    (hν1 : ν * ((L : ℝ) ^ K) ^ 2 ≤ 1) (D : BgData G N) {r : ℝ} (hr : 0 ≤ r)
    (Q R : Finset (CTorus d L N₁ m₁ K)) (hQR : Q ⊆ R)
    (hQR1 : ∀ x ∈ Q, ∀ μ : Fin d, x + Pi.single μ 1 ∈ R)
    (hQblk : ∀ x ∈ Q, x ∈ G.Ω 1 → ∀ y ∈ G.blk (G.layerIndex x) x, y ∈ R)
    (hreg : RegIneq G a ν D r R R)
    {Ws : Finset (CTorus d L N₁ m₁ K)} {γ Bnd Dist : ℝ} (hγ : 0 ≤ γ) (hB : 0 ≤ Bnd)
    (hdist : ∀ y ∈ R, y ∈ G.Ω 1 → ENNReal.ofReal Dist ≤ siteSetDist G Ws y)
    {τ : G.Ω 1 × Fin N → ℂ} {δα : G.Ω 1 → ℂ} (hfar : FarBounds G Ws γ Bnd τ δα) :
    ‖cubeActionR G a ν Q D.Ψ D.h (bgFieldC G a ν (bgC0 d L N) D + τ) -
        cubeActionR G a ν Q D.Ψ D.h (bgFieldC G a ν (bgC0 d L N) D)‖ ≤
      (1 / 2) * (Q.card * ((2 + d + 1) * (N * (2 * r * (Bnd * Real.exp (-(γ * Dist))) +
        (Bnd * Real.exp (-(γ * Dist))) ^ 2)))) := by
  set φ := bgFieldC G a ν (bgC0 d L N) D with hφ
  set T := Bnd * Real.exp (-(γ * Dist)) with hT
  have hT0 : 0 ≤ T := by positivity
  have hℓ : (1 : ℝ) ≤ (L : ℝ) ^ K := by
    exact one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have hdec : ∀ y ∈ R, y ∈ G.Ω 1 → decay γ (siteSetDist G Ws y) ≤ Real.exp (-(γ * Dist)) :=
    fun y hy hyΩ => decay_le_exp_dist hγ (hdist y hy hyΩ)
  have hBd : ∀ y ∈ R, y ∈ G.Ω 1 → Bnd * decay γ (siteSetDist G Ws y) ≤ T :=
    fun y hy hyΩ => mul_le_mul_of_nonneg_left (hdec y hy hyΩ) hB
  have TF : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Q → ∀ i, ‖τ (x, i)‖ ≤ T :=
    fun x hx i => (hfar.val x i).trans (hBd x (hQR hx) x.2)
  refine cubeAction_shift_bound Q D.Ψ D.h φ τ (blockWeight_le hw) hν0
    ((le_mul_of_one_le_right hν0 (one_le_pow₀ hℓ)).trans hν1) (by norm_num) hr hT0 ?_ ?_ ?_ ?_ ?_ TF
  · -- HB
    intro x hx i
    have h1 := hreg.1 x (hQR hx)
    exact (norm_le_vn (fun i => D.Ψ x i - blockAvg G φ x i) i).trans h1.le
  · -- HG
    intro x hx μ hact i
    obtain ⟨-, hgrad, -⟩ := hreg
    rcases hact with hxΩ | hyΩ
    · have h1 := ((hgrad ⟨x, hxΩ⟩ (hQR hx)).1 μ).1
      have h2 := norm_le_vn (barVec G D φ (x + Pi.single μ 1) - barVec G D φ x) i
      have h3 : ‖barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i‖ ≤
          vn (barVec G D φ (x + Pi.single μ 1) - barVec G D φ x) := h2
      nlinarith [vn_nonneg (barVec G D φ (x + Pi.single μ 1) - barVec G D φ x)]
    · have h1 := ((hgrad ⟨x + Pi.single μ 1, hyΩ⟩ (hQR1 x hx μ)).1 μ).2
      have h2 := norm_le_vn (barVec G D φ (x + Pi.single μ 1 - Pi.single μ 1) -
        barVec G D φ (x + Pi.single μ 1)) i
      rw [add_sub_cancel_right] at h2 h1
      have h3 : ‖barField G D.Ψ φ x i - barField G D.Ψ φ (x + Pi.single μ 1) i‖ ≤
          vn (barVec G D φ x - barVec G D φ (x + Pi.single μ 1)) := h2
      rw [norm_sub_rev] at h3
      simp only at h1
      nlinarith [vn_nonneg (barVec G D φ x - barVec G D φ (x + Pi.single μ 1))]
  · -- HF
    intro x hx i
    rcases hν0.eq_or_lt with h0 | hpos
    · rw [← h0]; simpa using hr
    · set νd := ν * ((L : ℝ) ^ K) ^ 2 with hνd
      have hνd0 : 0 < νd := by positivity
      have hνdle : ν ≤ νd := le_mul_of_one_le_right hν0 (one_le_pow₀ hℓ)
      have hsq : νd ≤ Real.sqrt νd := by
        rw [Real.le_sqrt' hνd0]
        nlinarith
      have hfc := (hreg.2.2 hνd0 x (hQR hx)).1
      have h1 := norm_le_vn (fun i => φ (x, i) - D.h x i) i
      have hs0 : 0 < Real.sqrt νd := Real.sqrt_pos.2 hνd0
      calc ν * ‖φ (x, i) - D.h x i‖ ≤ ν * (r / Real.sqrt νd) :=
            mul_le_mul_of_nonneg_left (h1.trans hfc.le) hν0
        _ ≤ Real.sqrt νd * (r / Real.sqrt νd) :=
            mul_le_mul_of_nonneg_right (hνdle.trans hsq) (by positivity)
        _ = r := by field_simp
  · -- TB
    intro x hx i
    exact blockAvg_norm_le τ x.2 (fun y hy hyΩ j => by
      refine (hfar.val ⟨y, hyΩ⟩ j).trans (hBd y (hQblk x hx x.2 y hy) hyΩ)) i
  · -- TG
    intro x hx μ hact i
    rcases hact with hxΩ | hyΩ
    · have h1 := hfar.fwd x hxΩ μ i
      have hsp := G.spacing_ge_one x
      have hn := norm_nonneg (svec G τ (x + Pi.single μ 1) i - svec G τ x i)
      nlinarith [hBd x (hQR hx) hxΩ]
    · have h1 := hfar.bwd (x + Pi.single μ 1) hyΩ μ i
      rw [add_sub_cancel_right] at h1
      have hsp := G.spacing_ge_one (x + Pi.single μ 1)
      have hn := norm_nonneg (svec G τ x i - svec G τ (x + Pi.single μ 1) i)
      rw [norm_sub_rev] at h1 hn
      nlinarith [hBd _ (hQR1 x hx μ) hyΩ]


open Classical in
/-- **Theorem 4.2, Step 3 (undecoupled): the bound on the cube action difference.**
There are `K_w, δ_w > 0` (depending on `(d, L, N)`) such that the following holds.  Let `D`, `Du`
be data in the complex domain, with `Du = D + δΨ` (same `h`), `δΨ` supported in `W` and bounded by
`δ₁` on the data sites, as in `lemma41_domain_uncond`.  Let `Q ⊆ R` be a cube and its
neighbourhood (the bonds based at `Q` and the blocks of the sites of `Q` lie in `R`), let the data
`D` satisfy the regularity inequalities on `R` with radius `r` (the membership of the data in
`Δ^c`, Definition II.3.5 (a)), and let `R ∩ Ω₁` be at distance at least `Dist` from the shadow
of `W`.  Then with `φ = bgFieldC D`, `φ' = bgFieldC Du` and `T = K_w C_F δ₁ e^{-γ_w Dist}`,
`|A_Q(D; φ') - A_Q(D; φ)| ≤ ½ |Q| (d + 3) N (2 r T + T²)`. -/
theorem cubeDiff_step3 (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
        {a : ℕ → ℝ} {ν : ℝ}, BgHyp d L K ϱ a ν → Dec2.OpSetting G a ν →
        ∀ {D Du : BgData G N} {δ ε δ' ε' : ℝ},
        0 < δ → δ ≤ ε → ε ≤ bgC0 d L N → δ ≤ bgC1 d L N →
        ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2 → InDomainC G ν δ ε D →
        0 < δ' → δ' ≤ ε' → ε' ≤ bgC0 d L N → δ' ≤ bgC1 d L N →
        ν * ((L : ℝ) ^ K) ^ 2 * ε' ^ 2 ≤ δ' ^ 2 → InDomainC G ν δ' ε' Du →
        bgK1 d L N * δ ≤ deltaStar d L N → bgK1 d L N * δ ≤ δw →
        ∀ {δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} (W : Finset (CTorus d L N₁ m₁ K)),
        (∀ y ∉ W, δΨ y = 0) →
        (∀ x i, Du.Ψ x i = D.Ψ x i + δΨ x i) → (∀ x i, Du.h x i = D.h x i) →
        ∀ {δ₁ : ℝ}, 0 ≤ δ₁ → δ₁ ≤ deltaStar d L N → δ₁ ≤ δw →
        (∀ x ∈ dataSites G, vn (δΨ x) ≤ δ₁) →
        ∀ (Q R : Finset (CTorus d L N₁ m₁ K)) {r Dist : ℝ}, 0 ≤ r → 0 ≤ Dist → Q ⊆ R →
        (∀ x ∈ Q, ∀ μ : Fin d, x + Pi.single μ 1 ∈ R) →
        (∀ x ∈ Q, x ∈ G.Ω 1 → ∀ y ∈ G.blk (G.layerIndex x) x, y ∈ R) →
        RegIneq G a ν D r R R →
        (∀ y ∈ R, y ∈ G.Ω 1 → ENNReal.ofReal Dist ≤ siteSetDist G (shadow G W) y) →
        ‖cubeActionC G a ν Q D (bgFieldC G a ν (bgC0 d L N) Du) -
            cubeActionC G a ν Q D (bgFieldC G a ν (bgC0 d L N) D)‖ ≤
          (1 / 2) * (Q.card * ((2 + d + 1) * (N * (2 * r *
            (Kw * (cF d L * δ₁) * Real.exp (-(gammaW d * Dist))) +
            (Kw * (cF d L * δ₁) * Real.exp (-(gammaW d * Dist))) ^ 2)))) := by
  obtain ⟨Kw, δw, hK, hδ, hfar⟩ := lemma41_domain_uncond (d := d) (L := L) (N := N) hd hL
  refine ⟨Kw, δw, hK, hδ, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν H hOp D Du δ ε δ' ε' hδ0 hδε hε hδ1 hνε hD hδ0' hδε' hε' hδ1' hνε' hDu
    hK1 hKw δΨ W hsupp hΨ hh δ₁ hδ₁0 hδ₁s hδ₁w hdΨ Q R r Dist hr hDist hQR hQR1 hQblk hreg hdist
  have hF := hfar H hOp hδ0 hδε hε hδ1 hνε hD hδ0' hδε' hε' hδ1' hνε' hDu hK1 hKw W hsupp hΨ hh
    hδ₁0 hδ₁s hδ₁w hdΨ
  have hB : 0 ≤ Kw * (cF d L * δ₁) := mul_nonneg hK.le (mul_nonneg (cF_pos d L).le hδ₁0)
  have hγ : 0 ≤ gammaW d := by
    unfold gammaW
    have := agmonRate_pos (d := d) (by omega)
    positivity
  have h1 := cubeDiff_bound_of_far hOp.weights hOp.mass hOp.massLe D hr Q R hQR hQR1 hQblk hreg
    (Ws := shadow G W) (γ := gammaW d) (Bnd := Kw * (cF d L * δ₁)) (Dist := Dist) hγ hB hdist hF
  have e : bgFieldC G a ν (bgC0 d L N) Du = bgFieldC G a ν (bgC0 d L N) D +
      (bgFieldC G a ν (bgC0 d L N) Du - bgFieldC G a ν (bgC0 d L N) D) := by abel
  unfold cubeActionC
  rw [e]
  exact h1


/-- The arithmetic of the last step of Step 3: with `T ≤ c r e`, `e ≤ 1`. -/
theorem step3_arith {r T c e : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) (he0 : 0 ≤ e)
    (he : e ≤ 1) (hTb : T ≤ c * r * e) : 2 * r * T + T ^ 2 ≤ (2 * c + c ^ 2) * r ^ 2 * e := by
  have h1 : 2 * r * T ≤ 2 * c * r ^ 2 * e := by nlinarith [mul_le_mul_of_nonneg_left hTb hr]
  have h2 : T ^ 2 ≤ c ^ 2 * r ^ 2 * e := by
    have : T ^ 2 ≤ (c * r * e) ^ 2 := pow_le_pow_left₀ hT hTb 2
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg c) (sq_nonneg r)) he0,
      mul_le_mul_of_nonneg_left he (mul_nonneg (mul_nonneg (sq_nonneg c) (sq_nonneg r)) he0)]
  nlinarith

open Classical in
/-- **Theorem 4.2, Step 3, in the form of the statement:** if moreover `δ₁ ≤ C_δ r` (Step 1: the
data change is bounded by a constant multiple of the H7 radius `r`), then
`|β F_□| ≤ C_F' β |Q| r² e^{-γ_w Dist}` with `C_F'` depending only on `(d, L, N, C_δ)`. -/
theorem cubeDiff_step3_quadratic (hd : 3 ≤ d) (hL : 3 ≤ L) {Cδ : ℝ} (hCδ : 0 ≤ Cδ) :
    ∃ CF δw : ℝ, 0 < CF ∧ 0 < δw ∧
      ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
        {a : ℕ → ℝ} {ν : ℝ}, BgHyp d L K ϱ a ν → Dec2.OpSetting G a ν →
        ∀ {D Du : BgData G N} {δ ε δ' ε' : ℝ},
        0 < δ → δ ≤ ε → ε ≤ bgC0 d L N → δ ≤ bgC1 d L N →
        ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2 → InDomainC G ν δ ε D →
        0 < δ' → δ' ≤ ε' → ε' ≤ bgC0 d L N → δ' ≤ bgC1 d L N →
        ν * ((L : ℝ) ^ K) ^ 2 * ε' ^ 2 ≤ δ' ^ 2 → InDomainC G ν δ' ε' Du →
        bgK1 d L N * δ ≤ deltaStar d L N → bgK1 d L N * δ ≤ δw →
        ∀ {δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} (W : Finset (CTorus d L N₁ m₁ K)),
        (∀ y ∉ W, δΨ y = 0) →
        (∀ x i, Du.Ψ x i = D.Ψ x i + δΨ x i) → (∀ x i, Du.h x i = D.h x i) →
        ∀ {δ₁ : ℝ}, 0 ≤ δ₁ → δ₁ ≤ deltaStar d L N → δ₁ ≤ δw →
        (∀ x ∈ dataSites G, vn (δΨ x) ≤ δ₁) →
        ∀ (Q R : Finset (CTorus d L N₁ m₁ K)) {r Dist : ℝ}, 0 ≤ r → 0 ≤ Dist → δ₁ ≤ Cδ * r →
        Q ⊆ R → (∀ x ∈ Q, ∀ μ : Fin d, x + Pi.single μ 1 ∈ R) →
        (∀ x ∈ Q, x ∈ G.Ω 1 → ∀ y ∈ G.blk (G.layerIndex x) x, y ∈ R) →
        RegIneq G a ν D r R R →
        (∀ y ∈ R, y ∈ G.Ω 1 → ENNReal.ofReal Dist ≤ siteSetDist G (shadow G W) y) →
        ∀ β : ℝ, 0 ≤ β →
        ‖(β : ℂ) * (cubeActionC G a ν Q D (bgFieldC G a ν (bgC0 d L N) Du) -
            cubeActionC G a ν Q D (bgFieldC G a ν (bgC0 d L N) D))‖ ≤
          CF * β * Q.card * r ^ 2 * Real.exp (-(gammaW d * Dist)) := by
  obtain ⟨Kw, δw, hK, hδ, hstep⟩ := cubeDiff_step3 (N := N) hd hL
  set c : ℝ := Kw * (cF d L * Cδ) with hc
  have hc0 : 0 ≤ c := mul_nonneg hK.le (mul_nonneg (cF_pos d L).le hCδ)
  refine ⟨(1 / 2) * ((2 + d + 1) * (N * (2 * c + c ^ 2))) + 1, δw, by positivity, hδ, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν H hOp D Du δ ε δ' ε' hδ0 hδε hε hδ1 hνε hD hδ0' hδε' hε' hδ1' hνε' hDu
    hK1 hKw δΨ W hsupp hΨ hh δ₁ hδ₁0 hδ₁s hδ₁w hdΨ Q R r Dist hr hDist hδr hQR hQR1 hQblk hreg
    hdist β hβ
  have h1 := hstep H hOp hδ0 hδε hε hδ1 hνε hD hδ0' hδε' hε' hδ1' hνε' hDu hK1 hKw W hsupp hΨ hh
    hδ₁0 hδ₁s hδ₁w hdΨ Q R hr hDist hQR hQR1 hQblk hreg hdist
  have hγ : 0 ≤ gammaW d := by
    unfold gammaW
    have := agmonRate_pos (d := d) (by omega)
    positivity
  set e := Real.exp (-(gammaW d * Dist)) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  set T := Kw * (cF d L * δ₁) * e with hT
  have hT0 : 0 ≤ T := mul_nonneg (mul_nonneg hK.le (mul_nonneg (cF_pos d L).le hδ₁0)) he0
  have hTb : T ≤ c * r * e := by
    rw [hT, hc]
    have : Kw * (cF d L * δ₁) ≤ Kw * (cF d L * Cδ) * r := by
      calc Kw * (cF d L * δ₁) ≤ Kw * (cF d L * (Cδ * r)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδr (cF_pos d L).le) hK.le
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_right this he0
  have h2 := step3_arith hr hT0 he0 he1 hTb
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ]
  have hQ0 : (0 : ℝ) ≤ Q.card := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  calc β * ‖cubeActionC G a ν Q D (bgFieldC G a ν (bgC0 d L N) Du) -
            cubeActionC G a ν Q D (bgFieldC G a ν (bgC0 d L N) D)‖
      ≤ β * ((1 / 2) * (Q.card * ((2 + d + 1) * (N * (2 * r * T + T ^ 2))))) :=
        mul_le_mul_of_nonneg_left h1 hβ
    _ ≤ β * ((1 / 2) * (Q.card * ((2 + d + 1) * (N * ((2 * c + c ^ 2) * r ^ 2 * e))))) := by
        refine mul_le_mul_of_nonneg_left ?_ hβ
        gcongr
    _ ≤ _ := by
        have hpos : 0 ≤ β * Q.card * r ^ 2 * e := by positivity
        nlinarith [mul_nonneg hpos (by positivity : (0 : ℝ) ≤ (1 / 2) * ((2 + d + 1) * (N * (2 * c + c ^ 2))))]

end Far

end Balaban.Fluctuation
