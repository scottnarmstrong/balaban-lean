/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.CutCoercivity
public import Balaban.Multiscale.CutAgmon
public import Balaban.Multiscale.XVariantAgmon
public import Balaban.Multiscale.XVariantSharp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The cut x-variant operator: NC1 and the weighted energy inequality (LOCALIZATION.md §3.1, DG7)

The x-variant operator `H_{k,x}(α₀)` of GREEN.md (1.7) (`xDirichletOperator`) with the bonds of a
set `cut` removed from `-Δ`:

* `cutXFullMatrix`, `cutXOperator`: `-Δ_cut + ν + (x-variant averaging form)` restricted to `Ω₁`,
  plus the diagonal `α`; for `cut = ∅` it is `xDirichletOperator` (`cutXOperator_empty`);
* `xCore_real_cut_sharp`, `x_multiscale_coercive_cut_sharp`, `cutXOperator_isUnit` (**NC1** for
  the x-variant): `½ ‖∂φ‖²_cut + ¼ ‖ℓ⁻¹φ‖² ≤ φᵀ A φ` uniformly in `x ≥ 0`, when `cut` avoids the
  blocks of all layers (`CutAligned`);
* `agmon_energy_gen_cut`: the Agmon energy inequality for a general real operator and a cut;
* `x_weighted_core_cut`, `x_agmon_energy_cut` (**NC2 in the weighted `L²` form**): for a weight
  `w = e^{ε r}`, `r` an Agmon weight and `0 ≤ ε ≤ ε_x = c_x/(16 d L)`,
  `½ ‖∂(w u)‖²_cut + (1/32) ‖ℓ⁻¹ w u‖² ≤ 8 ‖ℓ w f‖²` for `H u = f`, uniformly in `x ≥ 0`
  and for potentials with `|α| ≤ ℓ⁻²/8`.
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix Balaban

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Operator

variable (G : GeneratingSet d L N₀ (k + 1) ϱ)

/-- The real matrix `-Δ_cut + ν + (x-variant averaging form)` on the whole fine torus. -/
noncomputable def cutXFullMatrix (a : ℕ → ℝ) (aT x ν : ℝ)
    (cut : Finset (Torus d (N₀ * L ^ (k + 1)) × Fin d)) :
    Matrix (Torus d (N₀ * L ^ (k + 1))) (Torus d (N₀ * L ^ (k + 1))) ℝ :=
  cutLaplacian ν cut + xAvgMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x)

/-- **The cut x-variant operator** `H_{k,x}(α)` with the bonds of `cut` removed, as a complex matrix
on `Ω₁`. -/
noncomputable def cutXOperator (a : ℕ → ℝ) (aT x ν : ℝ)
    (cut : Finset (Torus d (N₀ * L ^ (k + 1)) × Fin d)) (α : G.Ω 1 → ℂ) :
    Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  Green.restrictOp ((cutXFullMatrix G a aT x ν cut).map (algebraMap ℝ ℂ)) (G.Ω 1) +
    Matrix.diagonal α

@[simp] theorem cutXFullMatrix_empty (a : ℕ → ℝ) (aT x ν : ℝ) :
    cutXFullMatrix G a aT x ν ∅ =
      xFullMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) ν := by
  simp [cutXFullMatrix, xFullMatrix]

/-- Without removed bonds one has the landed x-variant operator. -/
@[simp] theorem cutXOperator_empty (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) :
    cutXOperator G a aT x ν ∅ α = xDirichletOperator G a aT x ν α := by
  simp [cutXOperator, xDirichletOperator]

theorem reQuad_cutXOperator (a : ℕ → ℝ) (aT x ν : ℝ)
    (cut : Finset (Torus d (N₀ * L ^ (k + 1)) × Fin d)) (α : G.Ω 1 → ℂ) (u : G.Ω 1 → ℂ) :
    Green.reQuad (cutXOperator G a aT x ν cut α) u =
      Green.reQuad ((cutXFullMatrix G a aT x ν cut).map (algebraMap ℝ ℂ))
        (zeroExt (G.Ω 1) u) + ∑ i, (α i).re * ‖u i‖ ^ 2 := by
  unfold cutXOperator
  rw [Green.reQuad_add, reQuad_restrictOp, reQuad_diagonal]

/-- The equation `H_{cut,x} u = f` at a point of `Ω₁`, in terms of the zero extension. -/
theorem cutXOperator_eq {a : ℕ → ℝ} {aT x ν : ℝ}
    {cut : Finset (Torus d (N₀ * L ^ (k + 1)) × Fin d)} {α : G.Ω 1 → ℂ} {u f : G.Ω 1 → ℂ}
    (hu : cutXOperator G a aT x ν cut α *ᵥ u = f) (y : G.Ω 1) :
    ((cutXFullMatrix G a aT x ν cut).map (algebraMap ℝ ℂ) *ᵥ zeroExt (G.Ω 1) u)
        (y : Torus d (N₀ * L ^ (k + 1))) + α y * u y = f y := by
  have h := congrFun hu y
  unfold cutXOperator at h
  rw [Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal, restrictOp_mulVec] at h
  exact h

end Operator

/-! ### NC1 -/

section Core

variable (G : GeneratingSet d L N₀ (k + 1) ϱ) {cut : Finset (Torus d (N₀ * L ^ (k + 1)) × Fin d)}

/-- **NC1, real core of the cut x-variant** (`d`-free): for `ν ≥ 0`, `a_j ∈ [1/2, 2]`, `a ∈ [1/2, 2]`,
`x ≥ 0` and a cut avoiding the layer blocks,
`½ ‖∂φ‖²_cut + ¼ ‖ℓ⁻¹ φ‖² ≤ φᵀ (-Δ_cut + ν + Q* a Q|_x) φ`. -/
theorem xCore_real_cut_sharp (hcut : CutAligned G cut) (hL : 3 ≤ L) (hk : 1 ≤ k) {a : ℕ → ℝ}
    {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT)
    (haT2 : aT ≤ 2) (hx : 0 ≤ x) (φ : Torus d (N₀ * L ^ (k + 1)) → ℝ) :
    (1 / 2) * cutLatticeEnergy cut φ + xPoincareConstSharp * ∑ y, invSqSpacing G y * φ y ^ 2 ≤
      φ ⬝ᵥ cutXFullMatrix G a aT x ν cut *ᵥ φ := by
  obtain ⟨hs₁, hs, hcase⟩ := xSymbols_cases (L := L) hL (ha k hk le_rfl).1 haT1 haT2 hx
  unfold cutXFullMatrix
  rw [Matrix.add_mulVec, dotProduct_add, cutLaplacian_quadratic, xAvgMatrix_quadratic]
  have hE := sum_innerEnergy_le_cut G hcut φ
  rw [Finset.sum_Icc_succ_top (by omega)] at hE
  have hlay : ∑ y, invSqSpacing G y * φ y ^ 2 =
      ∑ j ∈ Icc 1 (k + 1), (((L : ℝ) ^ j) ^ 2)⁻¹ * ∑ y, (layerPart G j φ y) ^ 2 :=
    wsq_eq_sum_layers G φ
  rw [Finset.sum_Icc_succ_top (by omega)] at hlay
  have hper : ∑ j ∈ Icc 1 k, xPoincareConstSharp / ((L : ℝ) ^ j) ^ 2 *
        ∑ y, (layerPart G j φ y) ^ 2 ≤
      ∑ j ∈ Icc 1 k, ((1 / 2) * innerEnergy (L ^ j) (layerPart G j φ) +
        (a j / ((L : ℝ) ^ j) ^ 2) *
          ∑ y, (blockProjection (L ^ j) (N₀ * L ^ (k + 1 - j)) (layerPart G j φ) y) ^ 2) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hjk := (Finset.mem_Icc.1 hj).2
    have h1 := layer_ineq_sharp G (j := j) (by omega) (ha j (Finset.mem_Icc.1 hj).1 hjk).1 φ
    refine le_trans ?_ h1
    have hs0 : 0 ≤ ∑ y, (layerPart G j φ y) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hq : (0 : ℝ) < ((L : ℝ) ^ j) ^ 2 := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    refine mul_le_mul_of_nonneg_right ?_ hs0
    refine div_le_div_of_nonneg_right ?_ hq.le
    unfold xPoincareConstSharp; norm_num
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hper
  have htop := top_ineq_sharp (N₀ := N₀) hL hs₁ hs hcase (layerPart G (k + 1) φ)
  have hlay' : xPoincareConstSharp * ∑ y, invSqSpacing G y * φ y ^ 2 =
      ∑ j ∈ Icc 1 k, xPoincareConstSharp / ((L : ℝ) ^ j) ^ 2 * ∑ y, (layerPart G j φ y) ^ 2 +
        xPoincareConstSharp / ((L : ℝ) ^ (k + 1)) ^ 2 * ∑ y, (layerPart G (k + 1) φ y) ^ 2 := by
    rw [hlay, mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, div_eq_mul_inv]
    · rw [← mul_assoc, div_eq_mul_inv]
  have hν' : 0 ≤ ν * ∑ y, φ y ^ 2 := mul_nonneg hν (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [hlay']
  linarith

theorem x_multiscale_coercive_cut_sharp (hcut : CutAligned G cut) (hL : 3 ≤ L) (hk : 1 ≤ k)
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) {aT x : ℝ}
    (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2) (hx : 0 ≤ x) {θ : ℝ} (hθ0 : 0 ≤ θ) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ θ / (G.spacing y) ^ 2) (u : G.Ω 1 → ℂ) :
    (1 / 4 - θ) * (cutEnergy cut (zeroExt (G.Ω 1) u) + weightedSqNorm G u) ≤
      Green.reQuad (cutXOperator G a aT x ν cut α) u := by
  rw [reQuad_cutXOperator, reQuad_map_ofReal]
  have h1 := xCore_real_cut_sharp G hcut hL hk hν ha haT1 haT2 hx
    (fun y => (zeroExt (G.Ω 1) u y).re)
  have h2 := xCore_real_cut_sharp G hcut hL hk hν ha haT1 haT2 hx
    (fun y => (zeroExt (G.Ω 1) u y).im)
  have hw := sum_invSqSpacing_eq G u
  have hsplit : ∑ y, invSqSpacing G y * ‖zeroExt (G.Ω 1) u y‖ ^ 2 =
      ∑ y, invSqSpacing G y * (zeroExt (G.Ω 1) u y).re ^ 2 +
        ∑ y, invSqSpacing G y * (zeroExt (G.Ω 1) u y).im ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hαs : -(θ * weightedSqNorm G u) ≤ ∑ i, (α i).re * ‖u i‖ ^ 2 := by
    unfold weightedSqNorm
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hre : -(θ / (G.spacing i) ^ 2) ≤ (α i).re := by
      have := Complex.abs_re_le_norm (α i)
      have := hα i
      linarith [neg_abs_le (α i).re]
    have : -(θ * (‖u i‖ ^ 2 / (G.spacing i) ^ 2)) = -(θ / (G.spacing i) ^ 2) * ‖u i‖ ^ 2 := by
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hre (sq_nonneg _)
  have hE := cutEnergy_eq cut (zeroExt (G.Ω 1) u)
  have hDE := cutEnergy_nonneg cut (zeroExt (G.Ω 1) u)
  have hW := weightedSqNorm_nonneg G u
  have hq : xPoincareConstSharp = 1 / 4 := rfl
  rw [hq] at h1 h2
  nlinarith

theorem cutXOperator_isCoercive_sharp (hcut : CutAligned G cut) (hL : 3 ≤ L) (hk : 1 ≤ k)
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) {aT x : ℝ}
    (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2) (hx : 0 ≤ x) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 4)
    (α : G.Ω 1 → ℂ) (hα : ∀ y, ‖α y‖ ≤ θ / (G.spacing y) ^ 2) {γ : ℝ}
    (hγ : ∀ y : G.Ω 1, γ ≤ ((G.spacing y) ^ 2)⁻¹) :
    Green.IsCoercive (cutXOperator G a aT x ν cut α) ((1 / 4 - θ) * γ) := by
  intro u
  have h := x_multiscale_coercive_cut_sharp G hcut hL hk hν ha haT1 haT2 hx hθ0 α hα u
  have hc : 0 < 1 / 4 - θ := by linarith
  have hsq : γ * Green.sqNorm u ≤ weightedSqNorm G u := by
    unfold Green.sqNorm weightedSqNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [div_eq_mul_inv, mul_comm (‖u y‖ ^ 2)]
    exact mul_le_mul_of_nonneg_right (hγ y) (sq_nonneg _)
  have hDE := cutEnergy_nonneg cut (zeroExt (G.Ω 1) u)
  nlinarith

/-- **NC1 for the cut x-variant: invertibility**, for `|α(y)| ≤ ℓ(y)⁻² / 8`. -/
theorem cutXOperator_isUnit (hcut : CutAligned G cut) (hL : 3 ≤ L) (hk : 1 ≤ k) {a : ℕ → ℝ}
    {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT)
    (haT2 : aT ≤ 2) (hx : 0 ≤ x) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ (1 / 8) / (G.spacing y) ^ 2) :
    IsUnit (cutXOperator G a aT x ν cut α) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine Green.isUnit_of_isCoercive
    (γ := (1 / 4 - 1 / 8) * (((L : ℝ) ^ (k + 1)) ^ 2)⁻¹)
    (mul_pos (by norm_num) (inv_pos.2 (by positivity)))
    (cutXOperator_isCoercive_sharp G hcut hL hk hν ha haT1 haT2 hx (θ := 1 / 8)
      (by norm_num) (by norm_num) α hα
      (γ := (((L : ℝ) ^ (k + 1)) ^ 2)⁻¹) fun y => ?_)
  have hp : 0 < G.spacing y := spacing_pos G
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hp.le (spacing_le G y.2) 2)

theorem cutXOperator_mulVec_inv (hcut : CutAligned G cut) (hL : 3 ≤ L) (hk : 1 ≤ k) {a : ℕ → ℝ}
    {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT)
    (haT2 : aT ≤ 2) (hx : 0 ≤ x) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ (1 / 8) / (G.spacing y) ^ 2) (f : G.Ω 1 → ℂ) :
    cutXOperator G a aT x ν cut α *ᵥ ((cutXOperator G a aT x ν cut α)⁻¹ *ᵥ f) = f := by
  have hU := cutXOperator_isUnit G hcut hL hk hν ha haT1 haT2 hx α hα
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU),
    Matrix.one_mulVec]

end Core

/-! ### The Agmon energy inequality -/

section Energy

variable {K : ℕ}

/-- **The Agmon energy inequality for a general real operator and a cut.** If the conjugated real
form satisfies `hcore` (with the retained energy of the cut) then for `H u = f`, `v = w ũ`:
`½ ‖∂v‖²_cut + (c₂/2) ‖ℓ⁻¹ v‖² ≤ (2 c₂)⁻¹ ‖ℓ w f‖²`, `c₂ = c₁ - θ`. -/
theorem agmon_energy_gen_cut (G : GeneratingSet d L N₀ K ϱ)
    {cut : Finset (Torus d (N₀ * L ^ K) × Fin d)}
    {M : Matrix (Torus d (N₀ * L ^ K)) (Torus d (N₀ * L ^ K)) ℝ} {c₁ θ c₂ : ℝ} (hc₂ : 0 < c₂)
    (hθ0 : 0 ≤ θ) (hc : c₂ = c₁ - θ) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ θ / (G.spacing x) ^ 2)
    {r : Torus d (N₀ * L ^ K) → ℝ} {ε : ℝ}
    (hcore : ∀ φ : Torus d (N₀ * L ^ K) → ℝ, (∀ x, x ∉ G.Ω 1 → φ x = 0) →
      (1 / 2) * cutLatticeEnergy cut (fun x => Real.exp (ε * r x) * φ x) +
          c₁ * wsq G (fun x => Real.exp (ε * r x) * φ x) ≤
        (fun x => Real.exp (ε * r x) ^ 2 * φ x) ⬝ᵥ M *ᵥ φ)
    {u f : G.Ω 1 → ℂ}
    (hu : (Green.restrictOp (M.map (algebraMap ℝ ℂ)) (G.Ω 1) + Matrix.diagonal α) *ᵥ u = f) :
    (1 / 2) * cutEnergy cut (agmonField G ε r u) + (c₂ / 2) * cwsq G (agmonField G ε r u) ≤
      (1 / (2 * c₂)) * agmonSource G ε r f := by
  set w : Torus d (N₀ * L ^ K) → ℝ := fun x => Real.exp (ε * r x) with hw
  set ut := zeroExt (G.Ω 1) u with hut
  set ft := zeroExt (G.Ω 1) f with hft
  set αt := zeroExt (G.Ω 1) α with hαt
  set p : Torus d (N₀ * L ^ K) → ℝ := fun x => (ut x).re with hp
  set q : Torus d (N₀ * L ^ K) → ℝ := fun x => (ut x).im with hq
  have hpz : ∀ x, x ∉ G.Ω 1 → p x = 0 := fun x hx => by simp [hp, hut, zeroExt_not_mem _ _ hx]
  have hqz : ∀ x, x ∉ G.Ω 1 → q x = 0 := fun x hx => by simp [hq, hut, zeroExt_not_mem _ _ hx]
  have core_p := hcore p hpz
  have core_q := hcore q hqz
  set v := agmonField G ε r u with hv
  have hvre : (fun x => (v x).re) = fun x => w x * p x := by
    funext x; exact Complex.re_ofReal_mul _ _
  have hvim : (fun x => (v x).im) = fun x => w x * q x := by
    funext x; exact Complex.im_ofReal_mul _ _
  have hE : cutEnergy cut v = cutLatticeEnergy cut (fun x => w x * p x) +
      cutLatticeEnergy cut (fun x => w x * q x) := by
    rw [cutEnergy_eq, hvre, hvim]
  have hS : cwsq G v = wsq G (fun x => w x * p x) + wsq G (fun x => w x * q x) := by
    rw [cwsq_eq, hvre, hvim]
  set Ap := M *ᵥ p with hAp
  set Aq := M *ᵥ q with hAq
  have hpt : ∀ x : Torus d (N₀ * L ^ K), w x ^ 2 * (star (ut x) * ft x).re =
      w x ^ 2 * p x * Ap x + w x ^ 2 * q x * Aq x + w x ^ 2 * (αt x).re * ‖ut x‖ ^ 2 := by
    intro x
    by_cases hx : x ∈ G.Ω 1
    · have heq := congrFun hu ⟨x, hx⟩
      rw [Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal, restrictOp_mulVec] at heq
      have h1 : ft x = (M.map (algebraMap ℝ ℂ) *ᵥ ut) x + αt x * ut x := by
        have e1 : ft x = f ⟨x, hx⟩ := zeroExt_mem (G.Ω 1) f ⟨x, hx⟩
        have e2 : αt x = α ⟨x, hx⟩ := zeroExt_mem (G.Ω 1) α ⟨x, hx⟩
        have e3 : ut x = u ⟨x, hx⟩ := zeroExt_mem (G.Ω 1) u ⟨x, hx⟩
        rw [e1, e2, e3]
        exact heq.symm
      rw [h1, mul_add, Complex.add_re, re_star_mul, re_star_mul_mul, re_mulVec_map, im_mulVec_map]
      simp only [hp, hq, hAp, hAq]
      ring
    · have : ut x = 0 := zeroExt_not_mem _ _ hx
      simp [this, hp, hq]
  set T : ℝ := ∑ x, w x ^ 2 * (star (ut x) * ft x).re with hT
  have hTsum : T = (∑ x, w x ^ 2 * p x * Ap x) + (∑ x, w x ^ 2 * q x * Aq x) +
      ∑ x, w x ^ 2 * (αt x).re * ‖ut x‖ ^ 2 := by
    rw [hT, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => hpt x
  have hRp : (∑ x, w x ^ 2 * p x * Ap x) =
      (fun x => Real.exp (ε * r x) ^ 2 * p x) ⬝ᵥ M *ᵥ p := rfl
  have hRq : (∑ x, w x ^ 2 * q x * Aq x) =
      (fun x => Real.exp (ε * r x) ^ 2 * q x) ⬝ᵥ M *ᵥ q := rfl
  have hpot : -(θ * cwsq G v) ≤ ∑ x, w x ^ 2 * (αt x).re * ‖ut x‖ ^ 2 := by
    unfold cwsq
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases hx : x ∈ G.Ω 1
    · have hαx : ‖αt x‖ ≤ θ / (G.spacing x) ^ 2 := by
        have e : αt x = α ⟨x, hx⟩ := zeroExt_mem (G.Ω 1) α ⟨x, hx⟩
        rw [e]
        exact hα ⟨x, hx⟩
      have hre : -(θ / (G.spacing x) ^ 2) ≤ (αt x).re := by
        have := Complex.abs_re_le_norm (αt x)
        linarith [neg_abs_le (αt x).re]
      have hnv : ‖v x‖ ^ 2 = w x ^ 2 * ‖ut x‖ ^ 2 := by
        rw [hv, norm_agmonField]; ring
      rw [invSqSpacing_eq G hx, hnv]
      have hsp : 0 < (G.spacing x) ^ 2 := by have := spacing_pos G (x := x); positivity
      have e2 : -(θ * ((G.spacing x ^ 2)⁻¹ * (w x ^ 2 * ‖ut x‖ ^ 2))) =
          -(θ / (G.spacing x) ^ 2) * (w x ^ 2 * ‖ut x‖ ^ 2) := by
        field_simp
      rw [e2]
      calc -(θ / (G.spacing x) ^ 2) * (w x ^ 2 * ‖ut x‖ ^ 2)
          ≤ (αt x).re * (w x ^ 2 * ‖ut x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hre (by positivity)
        _ = _ := by ring
    · have h0 : ut x = 0 := zeroExt_not_mem _ _ hx
      have h1 : 0 ≤ θ * (invSqSpacing G x * ‖v x‖ ^ 2) := by
        have := invSqSpacing_nonneg G x
        positivity
      have h2 : w x ^ 2 * (αt x).re * ‖ut x‖ ^ 2 = 0 := by rw [h0]; simp
      linarith
  have hsrc : T ≤ c₂ / 2 * cwsq G v + (1 / (2 * c₂)) * agmonSource G ε r f := by
    unfold cwsq agmonSource
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases hx : x ∈ G.Ω 1
    · have hsp : 0 < G.spacing x := spacing_pos G
      have hnv : ‖v x‖ = w x * ‖ut x‖ := by rw [hv, norm_agmonField]
      have hnh : ‖((Real.exp (ε * r x) : ℝ) : ℂ) * ft x‖ = w x * ‖ft x‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      have hre : (star (ut x) * ft x).re ≤ ‖ut x‖ * ‖ft x‖ := by
        calc _ ≤ ‖star (ut x) * ft x‖ := Complex.re_le_norm _
          _ = _ := by rw [norm_mul, norm_star]
      have h1 : w x ^ 2 * (star (ut x) * ft x).re ≤ ‖v x‖ * (w x * ‖ft x‖) := by
        rw [hnv]
        have := mul_le_mul_of_nonneg_left hre (sq_nonneg (w x))
        nlinarith [this]
      rw [invSqSpacing_eq G hx, hnh]
      set A := ‖v x‖
      set B := w x * ‖ft x‖
      set s := G.spacing x
      have hs2 : 0 < s ^ 2 := by positivity
      have key : A * B ≤ c₂ / 2 * ((s ^ 2)⁻¹ * A ^ 2) + 1 / (2 * c₂) * (s ^ 2 * B ^ 2) := by
        have h0 : 0 ≤ 1 / (2 * c₂) * (s * B - c₂ * (A / s)) ^ 2 := by positivity
        have e : c₂ / 2 * ((s ^ 2)⁻¹ * A ^ 2) + 1 / (2 * c₂) * (s ^ 2 * B ^ 2) - A * B =
            1 / (2 * c₂) * (s * B - c₂ * (A / s)) ^ 2 := by
          field_simp; ring
        linarith
      linarith
    · have : ut x = 0 := zeroExt_not_mem _ _ hx
      have h0 : 0 ≤ c₂ / 2 * (invSqSpacing G x * ‖v x‖ ^ 2) := by
        have := invSqSpacing_nonneg G x
        positivity
      have h1 : 0 ≤ 1 / (2 * c₂) * (G.spacing x ^ 2 * ‖((Real.exp (ε * r x) : ℝ) : ℂ) *
          zeroExt (G.Ω 1) f x‖ ^ 2) := by positivity
      simp only [this, star_zero, zero_mul, Complex.zero_re, mul_zero]
      linarith
  have hcomb : (1 / 2) * cutEnergy cut v + c₁ * cwsq G v ≤
      (∑ x, w x ^ 2 * p x * Ap x) + (∑ x, w x ^ 2 * q x * Aq x) := by
    rw [hE, hS, hRp, hRq]
    nlinarith [core_p, core_q]
  have hS0 := cwsq_nonneg G v
  have hE0 := cutEnergy_nonneg cut v
  have hcθ : c₁ = c₂ + θ := by linarith
  rw [hcθ] at hcomb
  nlinarith [hcomb, hTsum, hpot, hsrc]

end Energy

/-! ### The weighted core of the cut x-variant and NC2 in the weighted `L²` form -/

section XEnergy

variable (G : GeneratingSet d L N₀ (k + 1) ϱ) {cut : Finset (Torus d (N₀ * L ^ (k + 1)) × Fin d)}

/-- **The conjugated real form of the cut x-variant.** For `w = exp (ε r)`, `v = w φ`,
`½ ‖∂v‖²_cut + (¼ - 4 d ε² - L² (e^{2εd} - 1)²) ‖ℓ⁻¹ v‖² ≤ ∑ w² φ (A φ)`, uniformly in `x ≥ 0`. -/
theorem x_weighted_core_cut (hcut : CutAligned G cut) (hL : 3 ≤ L) (hk : 1 ≤ k) {a : ℕ → ℝ}
    {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT)
    (haT2 : aT ≤ 2) (hx : 0 ≤ x) {r : Torus d (N₀ * L ^ (k + 1)) → ℝ} (hr : IsAgmonWeight G r)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) {φ : Torus d (N₀ * L ^ (k + 1)) → ℝ}
    (hφ : ∀ y, y ∉ G.Ω 1 → φ y = 0) :
    (1 / 2) * cutLatticeEnergy cut (fun y => Real.exp (ε * r y) * φ y) +
        (xPoincareConstSharp - (4 * d * ε ^ 2 + (L : ℝ) ^ 2 * (Real.exp (ε * (2 * d)) - 1) ^ 2)) *
          wsq G (fun y => Real.exp (ε * r y) * φ y) ≤
      (fun y => Real.exp (ε * r y) ^ 2 * φ y) ⬝ᵥ cutXFullMatrix G a aT x ν cut *ᵥ φ := by
  set v : Torus d (N₀ * L ^ (k + 1)) → ℝ := fun y => Real.exp (ε * r y) * φ y with hv
  have hcore := xCore_real_cut_sharp G hcut hL hk hν ha haT1 haT2 hx v
  have hlap := lap_diff_cut r ε ν cut φ
  have hlapE := lap_error_le_cut G (cut := cut) hr hε0 hε1 hφ
  have havg := xAvg_diff_ge G hk ha haT1 hx hL hr hε0 φ
  have hwsq : ∑ y, invSqSpacing G y * v y ^ 2 = wsq G v := rfl
  rw [hwsq] at hcore
  have hsplit : ∀ ψ : Torus d (N₀ * L ^ (k + 1)) → ℝ, ∀ g : Torus d (N₀ * L ^ (k + 1)) → ℝ,
      g ⬝ᵥ cutXFullMatrix G a aT x ν cut *ᵥ ψ =
        g ⬝ᵥ cutLaplacian ν cut *ᵥ ψ +
          g ⬝ᵥ xAvgMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) *ᵥ ψ := by
    intro ψ g
    unfold cutXFullMatrix
    rw [Matrix.add_mulVec, dotProduct_add]
  rw [hsplit] at hcore ⊢
  rw [hlap]
  nlinarith [hcore, hlapE, havg]

/-- **NC2, weighted `L²` form, for the cut x-variant** (uniform in `x ≥ 0`): for
`0 ≤ ε ≤ ε_x = c_x/(16 d L)`, an Agmon weight `r`, `|α| ≤ ℓ⁻²/8`, `H_{cut,x}(α) u = f`, `v = w ũ`:
`½ ‖∂v‖²_cut + (1/32) ‖ℓ⁻¹ v‖² ≤ 8 ‖ℓ w f‖²`. -/
theorem x_agmon_energy_cut (hcut : CutAligned G cut) (hd : 0 < d) (hL : 3 ≤ L) (hk : 1 ≤ k)
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) {aT x : ℝ}
    (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2) (hx : 0 ≤ x) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ (1 / 8) / (G.spacing y) ^ 2)
    {r : Torus d (N₀ * L ^ (k + 1)) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) {u f : G.Ω 1 → ℂ}
    (hu : cutXOperator G a aT x ν cut α *ᵥ u = f) :
    (1 / 2) * cutEnergy cut (agmonField G ε r u) + (1 / 32) * cwsq G (agmonField G ε r u) ≤
      8 * agmonSource G ε r f := by
  have hc0 := xPoincareConst_pos hd
  have hεhalf : ε ≤ 1 / 2 := by
    have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
    have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have h1 : xAgmonRate d L ≤ xPoincareConst d / 16 := by
      unfold xAgmonRate
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_le_mul hdd hLr (by norm_num) (by linarith)]
    linarith [xPoincareConst_le_quarter d]
  have hκ := kappa_x_le hd hL hε0 hε1
  have hq4 := xPoincareConst_le_quarter d
  have h := agmon_energy_gen_cut G (cut := cut) (M := cutXFullMatrix G a aT x ν cut)
    (c₁ := 3 / 16) (θ := 1 / 8) (c₂ := 1 / 16) (by norm_num) (by norm_num) (by norm_num) α hα
    (r := r) (ε := ε) (fun φ hφ => by
      have h0 := x_weighted_core_cut G hcut hL hk hν ha haT1 haT2 hx hr hε0 hεhalf hφ
      have hW := wsq_nonneg G (fun y => Real.exp (ε * r y) * φ y)
      have e : xPoincareConstSharp = 1 / 4 := rfl
      rw [e] at h0
      nlinarith [mul_nonneg hW (by linarith : (0 : ℝ) ≤ 1 / 16 - (4 * d * ε ^ 2 +
        (L : ℝ) ^ 2 * (Real.exp (ε * (2 * d)) - 1) ^ 2))]) (u := u) (f := f) hu
  norm_num at h ⊢
  linarith

end XEnergy

end Balaban.Multiscale
