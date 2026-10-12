/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledFieldX0
public import Balaban.Localization.Decoupled2FieldClose
public import Balaban.Localization.Decoupled2Geometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# OPEN-LOCAL-X0-DIST: the top-layer replacement of `i4a_close_X0` (VMOD-12 §3)

The global premise of `DecoupledFieldX0.i4a_close_X0` (`r₀* M₁ ≤ ϱ - 1`) fails at the P6 constants.
This file proves the local replacement for a common cover `C` (which supplies the cube and
parameter incidence) and an operator `H` with empty top layer (which supplies the path metric):

* `torusDist_hatBox_le_cover`: the estimate of `DecoupledFieldX0.torusDist_hatBox_le` without the
  `DGSetting` wrapper (only `L ≥ 3`, `M₁ ≥ 4 L²`);
* `Wcover` (3.2) and `hW_of_par_cover`: the mixed-cover form of `Wpar` and of `hW_of_par`;
* `p6_local_X0_dist` (3.4): `siteSetDist_H(x, W_C(X₁)) ≥ M₁` from the selected-set collar (3.3);
* `p6_i4a_close_X0`: `Dec2.i4a_close` with the factor `e^{-γ_w M₁}`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

section Dist

/-- The sites of the thickened interaction cube are within `4 d M₁ ℓ_j` of the centre (VMOD-12 §3;
`DecoupledFieldX0.torusDist_hatBox_le` without the `DGSetting` wrapper). -/
theorem torusDist_hatBox_le_cover (hL : 3 ≤ L) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {z : ℕ × CTorus d L N₁ m₁ K} {y : CTorus d L N₁ m₁ K} (hy : y ∈ hatBox z) :
    Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) y z.2 ≤ 4 * d * (L : ℝ) ^ (z.1 + m₁) := by
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hM' : (4 : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ m₁ := by exact_mod_cast hM
  have hd1 : (0 : ℝ) ≤ d := by positivity
  have hLj : (1 : ℝ) ≤ (L : ℝ) ^ z.1 := one_le_pow₀ (by linarith)
  have hlam : (L : ℝ) ^ (z.1 + m₁) = (L : ℝ) ^ z.1 * (L : ℝ) ^ m₁ := pow_add _ _ _
  have hl0 : (0 : ℝ) ≤ (L : ℝ) ^ (z.1 + m₁) := by positivity
  have key : hatRad L m₁ z.1 + (L : ℝ) ^ (z.1 + m₁) / 2 ≤ 4 * (L : ℝ) ^ (z.1 + m₁) := by
    unfold hatRad
    have := mul_le_mul_of_nonneg_right hM' (by linarith : (0 : ℝ) ≤ (L : ℝ) ^ z.1)
    rw [hlam] at *
    nlinarith
  have hbox : InBox m₁ z.1 z.2 (hatRad L m₁ z.1) y := by
    unfold hatBox at hy
    exact mem_boxSet.1 hy
  have hdist := torusDist_le_of_inBox hbox
  refine hdist.trans ?_
  nlinarith [mul_le_mul_of_nonneg_left key hd1]

open Classical in
/-- **(3.2)** `W_C(X₁)`: the interaction cubes of the centres of `C` whose parameter set `𝒬(z)`
contains a cube not contained in `X₁`. -/
noncomputable def Wcover (C : DecCover d L N₁ m₁ K) (X₁ : Finset (CTorus d L N₁ m₁ K)) :
    Finset (CTorus d L N₁ m₁ K) :=
  (C.cubeIdx.filter fun z => ∃ P ∈ C.Qset z, ¬ cubeP P ⊆ X₁).biUnion intBox

theorem mem_Wcover {C : DecCover d L N₁ m₁ K} {X₁ : Finset (CTorus d L N₁ m₁ K)}
    {w : CTorus d L N₁ m₁ K} :
    w ∈ Wcover C X₁ ↔ ∃ z ∈ C.cubeIdx, (∃ P ∈ C.Qset z, ¬ cubeP P ⊆ X₁) ∧ w ∈ intBox z := by
  classical
  unfold Wcover
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨z, ⟨hz, hP⟩, hw⟩; exact ⟨z, hz, hP, hw⟩
  · rintro ⟨z, hz, hP, hw⟩; exact ⟨z, ⟨hz, hP⟩, hw⟩

/-- **The mixed-cover `hW_of_par`**: if `s_P = 1` off `C.parCubes X₁`, the centres with
`s_z ≠ 1` have their interaction cube in `W_C(X₁)`. -/
theorem hW_of_par_cover {C : DecCover d L N₁ m₁ K} {X₁ : Finset (CTorus d L N₁ m₁ K)}
    {s : Dec2.DecParams C}
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ C.cubeIdx), P ∉ C.parCubes X₁ →
      s ⟨P, hP⟩ = 1) :
    ∀ z ∈ C.cubeIdx, C.sProd (Dec2.extS C s) z ≠ 1 → intBox z ⊆ Wcover C X₁ := by
  classical
  intro z hz hne w hw
  rw [mem_Wcover]
  refine ⟨z, hz, ?_, hw⟩
  by_contra hcon
  push Not at hcon
  apply hne
  unfold DecCover.sProd
  refine Finset.prod_eq_one fun P hP => ?_
  have hPi : P ∈ C.cubeIdx := (C.mem_Qset.1 hP).1
  unfold Dec2.extS
  simp only [hPi, ↓reduceDIte]
  refine hs1 P hPi ?_
  intro hpar
  exact (Finset.mem_filter.1 hpar).2 (hcon P hP)

/-- **OPEN-LOCAL-X0-DIST, (3.4).**  Let `C` be a cover whose centres have scale at most `K = k + 1`,
`H` an operator with empty layer `k + 1`, `x ∈ Ω_k(H)`, and assume `L ≥ 3`, `M₁ = L^{m₁} ≥ 4 L²`,
`ϱ L^{k+1} - 1 ≥ M₁ L^{k+1}` and the selected-set collar (3.3): the open torus ball of radius
`r₀* M₁ L^k`, `r₀* = 4 d L³ + L`, around `x ∈ X₀` lies in `X₁`.  Then the path distance of
`H` from `x` to `W_C(X₁)` is at least `M₁`. -/
theorem p6_local_X0_dist {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {k : ℕ} (hK : K = k + 1) (hk : 1 ≤ k) (hL : 3 ≤ L) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hC : ∀ z ∈ C.cubeIdx, z.1 ≤ K) (hΩtop : H.Ω (k + 1) = ∅)
    (hϱ : (L : ℝ) ^ m₁ * (L : ℝ) ^ (k + 1) ≤ ϱ * (L : ℝ) ^ (k + 1) - 1)
    {X₀ X₁ : Finset (CTorus d L N₁ m₁ K)}
    (hcollar : ∀ x ∈ X₀, ∀ y : CTorus d L N₁ m₁ K,
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y <
        (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ * (L : ℝ) ^ k → y ∈ X₁)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ X₀) (hxΩ : x ∈ H.Ω k) :
    ENNReal.ofReal ((L : ℝ) ^ m₁) ≤ siteSetDist H (Wcover C X₁) x := by
  classical
  unfold siteSetDist
  refine le_iInf₂ fun w hw => ?_
  by_cases hwΩ : w ∉ H.Ω 1
  · have : H.pathDist x w = ⊤ := by
      refine eq_top_iff.2 (le_iInf₂ fun c hc => ?_)
      exact absurd hc.right_mem hwΩ
    rw [this]; exact le_top
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hM' : (4 : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ m₁ := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ (L : ℝ) ^ m₁ := one_le_pow₀ hL1
  have hc1 : (1 : ℝ) ≤ (L : ℝ) ^ (k + 1) := one_le_pow₀ hL1
  have hρ : 1 ≤ ϱ := by nlinarith
  obtain ⟨z, hz, ⟨P, hPQ, hPsub⟩, hwz⟩ := mem_Wcover.1 hw
  obtain ⟨y', hy'P, hy'X⟩ := Finset.not_subset.1 hPsub
  obtain ⟨hPi, y, hy, hbox⟩ := C.mem_Qset.1 hPQ
  have hyhat : y ∈ hatBox z := by unfold hatBox; exact mem_boxSet.2 hbox
  have d1 := torusDist_hatBox_le_cover (K := K) (N₁ := N₁) hL hM (box_subset_hatBox z hwz)
  have d2 := torusDist_hatBox_le_cover (K := K) (N₁ := N₁) hL hM hyhat
  have hyy : SameCell (L ^ (P.1 + m₁)) y' y := (mem_cubeP.1 hy'P).trans hy.symm
  have d3 := torusDist_sameCell_le (L := L) (N₁ := N₁) (m₁ := m₁) (K := K)
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _) hyy
  have e3 : Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) y' y ≤ d * (L : ℝ) ^ (P.1 + m₁) := by
    have : ((L ^ (P.1 + m₁) : ℕ) : ℝ) = (L : ℝ) ^ (P.1 + m₁) := by push_cast; rfl
    rw [← this]; exact d3
  have t1 := Green.torusDist_triangle_gen (d := d) (m := (N₁ * L ^ m₁) * L ^ K) w z.2 y'
  have t2 := Green.torusDist_triangle_gen (d := d) (m := (N₁ * L ^ m₁) * L ^ K) z.2 y y'
  have c1 : Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) z.2 y =
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) y z.2 := Green.torusDist_comm_gen _ _
  have c2 : Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) y y' =
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) y' y := Green.torusDist_comm_gen _ _
  have hz1 : (L : ℝ) ^ (z.1 + m₁) ≤ (L : ℝ) ^ (k + 1) * (L : ℝ) ^ m₁ := by
    rw [← pow_add]; exact pow_le_pow_right₀ hL1 (by have := hC z hz; omega)
  have hP1 : (L : ℝ) ^ (P.1 + m₁) ≤ (L : ℝ) ^ (k + 1) * (L : ℝ) ^ m₁ := by
    rw [← pow_add]; exact pow_le_pow_right₀ hL1 (by have := hC P hPi; omega)
  -- (3.5)
  have h35 : Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) w y' ≤
      9 * d * ((L : ℝ) ^ (k + 1) * (L : ℝ) ^ m₁) := by
    nlinarith [mul_le_mul_of_nonneg_left hz1 hd0, mul_le_mul_of_nonneg_left hP1 hd0]
  have htm := hcollar x hx
  have hxy : (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ * (L : ℝ) ^ k ≤
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y' := by
    by_contra h
    push Not at h
    exact hy'X (htm y' h)
  have tri := Green.torusDist_triangle_gen (d := d) (m := (N₁ * L ^ m₁) * L ^ K) x w y'
  set tw := Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x w with htw
  have hpk : (L : ℝ) ^ (k + 1) = (L : ℝ) ^ k * L := pow_succ _ _
  -- (3.6)
  have h36 : (L : ℝ) ^ m₁ * (L : ℝ) ^ (k + 1) ≤ tw := by
    have hk0 : (0 : ℝ) ≤ (L : ℝ) ^ k := by positivity
    have hpos : 0 ≤ (d : ℝ) * (L : ℝ) ^ m₁ * (L : ℝ) ^ k * L * (4 * (L : ℝ) ^ 2 - 9) := by
      have : 0 ≤ 4 * (L : ℝ) ^ 2 - 9 := by nlinarith
      positivity
    rw [hpk] at h35 ⊢
    nlinarith
  -- (3.7)
  have hxl : x ∈ H.layer k := H.mem_layer.2 ⟨hxΩ, by rw [hΩtop]; simp⟩
  have hA := pathDist_ge_torusDist H hρ hk hxl w
  have hmin : (L : ℝ) ^ m₁ * (L : ℝ) ^ (k + 1) ≤ min tw (ϱ * (L : ℝ) ^ (k + 1) - 1) :=
    le_min h36 hϱ
  have hdiv : (L : ℝ) ^ m₁ ≤ min tw (ϱ * (L : ℝ) ^ (k + 1) - 1) / (L : ℝ) ^ (k + 1) := by
    rw [le_div_iff₀ (by positivity)]; exact hmin
  exact (ENNReal.ofReal_le_ofReal hdiv).trans hA

omit [NeZero N₁] [NeZero L] in
/-- The P6 value `ϱ = 5 L M₁` satisfies the radius hypothesis `ϱ L^{k+1} - 1 ≥ M₁ L^{k+1}`. -/
theorem rho_hyp_of_five (hL : 3 ≤ L) (k : ℕ) :
    (L : ℝ) ^ m₁ * (L : ℝ) ^ (k + 1) ≤ (5 * L * (L : ℝ) ^ m₁) * (L : ℝ) ^ (k + 1) - 1 := by
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have h1 : (1 : ℝ) ≤ (L : ℝ) ^ m₁ := one_le_pow₀ (by linarith)
  have h2 : (1 : ℝ) ≤ (L : ℝ) ^ (k + 1) := one_le_pow₀ (by linarith)
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (L : ℝ) ^ m₁ - 1) (by linarith : (0 : ℝ) ≤ (L : ℝ) ^ (k + 1) - 1),
    mul_nonneg (by linarith : (0 : ℝ) ≤ (L : ℝ) ^ m₁) (by linarith : (0 : ℝ) ≤ (L : ℝ) ^ (k + 1) - 1)]

end Dist

section Close

variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {N : ℕ}

/-- **The top-layer replacement of `i4a_close_X0` (OPEN-LOCAL-X0-DIST)**: `Dec2.i4a_close` with
`W = W_C(X₁)` and the distance (3.4); the closeness of the solutions at `s` and at `s ≡ 1` on
`X₀ ∩ Ω₁` is `closeConst · e^{-γ_w M₁}` (twice that for the value, gradient and Laplacian of the
fluctuation).  The hypotheses of `Dec2.i4a_close` are unchanged; those of `p6_local_X0_dist` replace
`r₀* M₁ ≤ ϱ - 1`. -/
theorem p6_i4a_close_X0 {c BG : ℝ} (hF : Dec2.FamSpec d L Kc Cx c BG)
    (hD : Dec2.Dg2Spec d L Kc Cx c BG) (hCl : Dec2.CloseSpec d L Kc Cx c BG)
    (h1 : Dec2.OneSpec d L Kc Cx c) (S : Dec2.CoverBase C H a ν Kc Cx) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : Dec2.DecParams C}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {X₀ X₁ : Finset (CTorus d L N₁ m₁ K)}
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ C.cubeIdx), P ∉ C.parCubes X₁ →
      s ⟨P, hP⟩ = 1)
    {k : ℕ} (hK : K = k + 1) (hk : 1 ≤ k) (hL : 3 ≤ L) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hC : ∀ z ∈ C.cubeIdx, z.1 ≤ K) (hΩtop : H.Ω (k + 1) = ∅)
    (hϱ : (L : ℝ) ^ m₁ * (L : ℝ) ^ (k + 1) ≤ ϱ * (L : ℝ) ^ (k + 1) - 1)
    (hcollar : ∀ x ∈ X₀, ∀ y : CTorus d L N₁ m₁ K,
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y <
        (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ * (L : ℝ) ^ k → y ∈ X₁)
    (hX₀ : ∀ x ∈ X₀, x ∈ H.Ω k)
    {ιU : Bool} {α₀ : H.Ω 1 → ℂ} {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ : H.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ} (Hh : DecHyp H a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaClose d L N BG κ) (hδ₁ : δ₁ ≤ deltaClose d L N BG κ)
    {δα δα' : H.Ω 1 → ℂ}
    (hfix : Dec2.DecFixed C H a ν s ιU α₀ φ₀ (pertSource H a δΨ f₁) δα)
    (hsm : Small H δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (hfix' : Dec2.DecFixed C H a ν (fun _ => 1) ιU α₀ φ₀ (pertSource H a δΨ f₁) δα')
    (hsm' : Small H δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) :
    (∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ X₀ →
      H.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x - δα' x‖ ≤ closeConst d L N BG κ δ₁ *
        Real.exp (-(gammaW d * (L : ℝ) ^ m₁))) ∧
    (∀ y ∈ X₀, ∀ i : Fin N,
      ‖svec H (dphi H (Dec2.decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα -
        dphi H (Dec2.decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα') y i‖ ≤
        2 * closeConst d L N BG κ δ₁ * Real.exp (-(gammaW d * (L : ℝ) ^ m₁))) ∧
    (∀ x ∈ X₀, x ∈ H.Ω 1 → ∀ (μ : Fin d) (i : Fin N), H.spacing x *
      ‖svec H (dphi H (Dec2.decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα -
        dphi H (Dec2.decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα')
          (x + Pi.single μ 1) i -
        svec H (dphi H (Dec2.decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα -
        dphi H (Dec2.decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα') x i‖ ≤
        2 * closeConst d L N BG κ δ₁ * Real.exp (-(gammaW d * (L : ℝ) ^ m₁))) ∧
    (∀ x ∈ X₀, x ∈ H.Ω 1 → ∀ i : Fin N, H.spacing x ^ 2 * ‖∑ μ : Fin d,
      (2 * svec H (dphi H (Dec2.decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα -
        dphi H (Dec2.decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα') x i -
      svec H (dphi H (Dec2.decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα -
        dphi H (Dec2.decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα')
          (x + Pi.single μ 1) i -
      svec H (dphi H (Dec2.decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα -
        dphi H (Dec2.decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα')
          (x - Pi.single μ 1) i)‖ ≤
        2 * closeConst d L N BG κ δ₁ * Real.exp (-(gammaW d * (L : ℝ) ^ m₁))) := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hBG : 0 ≤ BG := hF.2.1
  have hcc := closeConst_nonneg (d := d) (L := L) (κ := κ) (N := N) hBG Hh.δ₁_nn hd0
  have hγ0 : 0 ≤ gammaW d := gammaW_nonneg hd0
  have hM0 : (0 : ℝ) ≤ (L : ℝ) ^ m₁ := by positivity
  have hclose := Dec2.i4a_close hF hD hCl h1 S hκ hM hs (W := Wcover C X₁)
    (hW_of_par_cover hs1) Hh hδ₀ hδ₁ hfix hsm hfix' hsm'
  have hdec : ∀ x ∈ X₀, decay (gammaW d) (siteSetDist H (Wcover C X₁) x) ≤
      Real.exp (-(gammaW d * (L : ℝ) ^ m₁)) := by
    intro x hx
    have h := decay_anti_dist hγ0
      (p6_local_X0_dist hK hk hL hMM hC hΩtop hϱ hcollar hx (hX₀ x hx))
    rw [decay_of_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hM0] at h
    exact h
  obtain ⟨c1, c2, c3, c4⟩ := hclose
  refine ⟨fun x hx => ?_, fun y hy i => ?_, fun x hx hxΩ μ i => ?_, fun x hx hxΩ i => ?_⟩
  · exact (c1 x).trans (mul_le_mul_of_nonneg_left (hdec x hx) hcc)
  · exact (c2 y i).trans (mul_le_mul_of_nonneg_left (hdec y hy) (by positivity))
  · exact (c3 x hxΩ μ i).trans (mul_le_mul_of_nonneg_left (hdec x hx) (by positivity))
  · exact (c4 x hxΩ i).trans (mul_le_mul_of_nonneg_left (hdec x hx) (by positivity))

end Close

end Balaban.Localization
