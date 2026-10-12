/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCube
public import Balaban.Localization.DecoupledChiPair
public import Balaban.Localization.NC3Small
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Hölder bound of the cube Green's function, summed over the blocks of the source

The two-point (Hölder) form of (NC3) for the interaction cubes of the cover
(LOCALIZATION.md §3.1, (DG2)):

* `chart_z`: for two points of a coordinate cube whose integer displacement is small, the
  displacement is the chart difference of the reflection argument;
* `CubeBlockHolder`, `cubeBlockHolder_exists`: the two-center Hölder bound of the cube operator
  for a source in one block (`holder_pair_cut_cube` for scale `≥ 2`, `small_holder_pair_cut` for
  scale `1`);
* `cube_holder`: the Hölder bound for a source supported in the cube with `ℓ² |f| ≤ C` (no
  weight), by the weighted summation over the blocks of the source;
* `cube_lip`: the increments of the cube solution along a displacement inside the lifted ball.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

section Chart

variable {d : ℕ}

/-- **The displacement of two points of a cube is the chart difference.** -/
theorem chart_z {N S B : ℕ} [NeZero N] (c : Fin d → ℕ) {x x' : Torus d N}
    (hx : ∀ i, InCube1 N S (c i) (x i)) (hx' : ∀ i, InCube1 N S (c i) (x' i))
    {z : Fin d → ℤ} (hxz : x' = x + intTorus z) (hz : ‖z‖ < B) (hSB : S + B ≤ N) :
    ∀ i, z i = (((x' i - (c i : ZMod N)).val : ℕ) : ℤ) - (((x i - (c i : ZMod N)).val : ℕ) : ℤ) := by
  intro i
  obtain ⟨t, ht, hxt⟩ := hx i
  obtain ⟨t', ht', hxt'⟩ := hx' i
  have e1 : x i - (c i : ZMod N) = (t : ZMod N) := by rw [hxt]; push_cast; ring
  have e2 : x' i - (c i : ZMod N) = (t' : ZMod N) := by rw [hxt']; push_cast; ring
  have hv1 : (x i - (c i : ZMod N)).val = t := by
    rw [e1]; exact ZMod.val_natCast_of_lt (by omega)
  have hv2 : (x' i - (c i : ZMod N)).val = t' := by
    rw [e2]; exact ZMod.val_natCast_of_lt (by omega)
  rw [hv1, hv2]
  have hzi : (x' i) = x i + ((z i : ℤ) : ZMod N) := by
    have := congrFun hxz i
    simpa [intTorus_apply] using this
  have hcast : ((((t' : ℤ) - t - z i : ℤ)) : ZMod N) = 0 := by
    push_cast
    have a1 : (t : ZMod N) = x i - c i := e1.symm
    have a2 : (t' : ZMod N) = x' i - c i := e2.symm
    rw [a1, a2, hzi]; ring
  have hdvd : (N : ℤ) ∣ (t' : ℤ) - t - z i := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hcast
  have hzabs : |z i| < B := by
    have h1 := norm_le_pi_norm z i
    rw [Int.norm_eq_abs] at h1
    have : ((|z i| : ℤ) : ℝ) < B := by
      rw [Int.cast_abs]; exact lt_of_le_of_lt h1 hz
    exact_mod_cast this
  have hlt : |(t' : ℤ) - t - z i| < (N : ℤ) := by
    rw [abs_lt] at hzabs ⊢
    constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  omega

end Chart

section Block

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) in
/-- **The two-center Hölder bound for the cube operator of the centre `q`**: for a source in one
`j'`-block of the cube, the second difference `(∂u)(x') - (∂u)(x)` of the cube solution at two
points of the cube whose displacement is `z`, `1 ≤ ‖z‖ < M₁ ℓ_q`. -/
structure CubeBlockHolder (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ K)
    (Kh : ℝ) : Prop where
  pair : ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ {j' : ℕ} {y' : CTorus d L N₁ m₁ K}, 1 ≤ j' → j' ≤ K →
    y' ∈ G.layer j' → y' ∈ intBox q → ∀ (f : G.Ω 1 → ℂ),
    (∀ z : G.Ω 1, f z ≠ 0 → jBlock d L (N₁ * L ^ m₁) K j' z = jBlock d L (N₁ * L ^ m₁) K j' y') →
    ∀ {Mf : ℝ}, 0 ≤ Mf → (∀ z, ‖f z‖ ≤ Mf) →
    ∀ {x x' : CTorus d L N₁ m₁ K}, x ∈ G.Ω 1 → x' ∈ G.Ω 1 → x ∈ intBox q → x' ∈ intBox q →
    ∀ {μ : Fin d}, x + Pi.single μ 1 ∈ intBox q → x' + Pi.single μ 1 ∈ intBox q →
    G.layerIndex x ≤ G.layerIndex x' + 1 → ∀ {z : Fin d → ℤ}, x' = x + intTorus z → 1 ≤ ‖z‖ →
    ‖z‖ < (L : ℝ) ^ (q.1 + m₁) →
    (G.spacing x) ^ 2 *
        ‖(solExt G (cubeH G a ν α q)⁻¹ f (x' + Pi.single μ 1) -
            solExt G (cubeH G a ν α q)⁻¹ f x') -
          (solExt G (cubeH G a ν α q)⁻¹ f (x + Pi.single μ 1) -
            solExt G (cubeH G a ν α q)⁻¹ f x)‖ ≤
      (Kh / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) *
        ((decay (agmonRate d / 2) (G.pathDist x y') +
          decay (agmonRate d / 2) (G.pathDist x' y')) * ((L : ℝ) ^ (2 * j') * Mf))

theorem cubeBlockHolder_exists (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kh : ℝ, 0 ≤ Kh ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {q : ℕ × CTorus d L N₁ m₁ K}, q ∈ cubeIdx G →
      CubeBlockHolder G a ν α q Kh := by
  obtain ⟨B, hB, hH⟩ := holder_pair_cut_cube (d := d) (L := L) hd hL
  have hsc := smallConst_nonneg d L
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  refine ⟨B + (L : ℝ) ^ 3 * smallConst d L, by positivity, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα q hq
  have hd0 : 0 < d := by omega
  have hρ1 : 1 ≤ ϱ := S.one_lt_rho.le
  have hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) := S.sep_pow (le_of_eq rfl)
  have hsep1 : (L : ℝ) ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) := by
    simpa using S.sep_pow (n := 1) (by exact_mod_cast (by omega : 1 ≤ d))
  obtain ⟨⟨hm1, hmK⟩, hl, hbase⟩ := (mem_cubeIdx G).1 hq
  refine ⟨fun {θ} hθ0 hθ1 {j'} {y'} hj'1 hj'k hy' hy'b f hsupp {Mf} hMf0 hMf {x} {x'} hxΩ hx'Ω hxb
    hx'b {μ} hxe hx'e hlay {z} hxz hz1 hzB => ?_⟩
  have hF0 : 0 ≤ (decay (agmonRate d / 2) (G.pathDist x y') +
      decay (agmonRate d / 2) (G.pathDist x' y')) * ((L : ℝ) ^ (2 * j') * Mf) := by
    have := decay_nonneg (agmonRate d / 2) (G.pathDist x y')
    have := decay_nonneg (agmonRate d / 2) (G.pathDist x' y')
    positivity
  have hX0 : 0 ≤ (G.spacing x) ^ θ * ‖z‖ ^ (1 - θ) := by
    have := spacing_pos G (x := x)
    positivity
  have hBθ : B / θ ≤ (B + (L : ℝ) ^ 3 * smallConst d L) / θ :=
    div_le_div_of_nonneg_right (by nlinarith [mul_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ L) 3) hsc])
      hθ0.le
  have hBθ' : (L : ℝ) ^ 3 * smallConst d L / θ ≤ (B + (L : ℝ) ^ 3 * smallConst d L) / θ :=
    div_le_div_of_nonneg_right (by linarith) hθ0.le
  by_cases hm : 2 ≤ q.1
  · have hc := alignedCube_box S hq
    have : NeZero (5 * L ^ (q.1 + m₁ - min K (q.1 + 1))) :=
      ⟨Nat.mul_ne_zero (by norm_num) (pow_ne_zero _ (NeZero.ne L))⟩
    have hF := hc.foldSetting hm
    have hcb : cubeOf (N₁ * L ^ m₁) L K (min K (q.1 + 1)) (5 * L ^ (q.1 + m₁ - min K (q.1 + 1)))
        (boxCorner q) = intBox q := by
      rw [hc.cubeOf_eq, ← box_eq_cubeSet S.big hq]
    have hyc : y' ∈ cubeOf (N₁ * L ^ m₁) L K (min K (q.1 + 1))
        (5 * L ^ (q.1 + m₁ - min K (q.1 + 1))) (boxCorner q) := by rw [hcb]; exact hy'b
    have hbs := box_eq_cubeSet S.big hq
    have hxc : ∀ i, InCube1 ((N₁ * L ^ m₁) * L ^ K) (5 * L ^ (q.1 + m₁)) (boxCorner q i) (x i) :=
      mem_cubeSet.1 (hbs ▸ hxb)
    have hx'c : ∀ i, InCube1 ((N₁ * L ^ m₁) * L ^ K) (5 * L ^ (q.1 + m₁)) (boxCorner q i) (x' i) :=
      mem_cubeSet.1 (hbs ▸ hx'b)
    have hzchart := chart_z (B := L ^ (q.1 + m₁)) (boxCorner q) hxc hx'c hxz
      (by rw [show ((L ^ (q.1 + m₁) : ℕ) : ℝ) = (L : ℝ) ^ (q.1 + m₁) by push_cast; rfl]; exact hzB)
      (by have := torusSide_ge (L := L) (m₁ := m₁) S.big hmK; omega)
    have key := hH hθ0 hθ1 G hF S.mass S.massLe S.weights α hα hρ1 hsep hj'1 hj'k hy' hyc f hsupp
      hMf0 hMf (x := x) (x' := x') (by rw [hcb]; exact hxb) (by rw [hcb]; exact hx'b) hlay
      (z := z) (by simpa [hc.hS] using hzchart) hz1 μ (by rw [hcb]; exact hxe)
      (by rw [hcb]; exact hx'e)
    rw [hcb] at key
    refine key.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBθ hX0) hF0
  · have hq1 : q.1 = 1 := by omega
    have hcut := cubeCut_aligned G (box_blockAligned S.aligned S.cover_sep (by omega) hq)
    have hj'2 : j' ≤ 2 := by
      have := layer_le_of_mem_box S.cover_sep (by omega) hq hj'1 hj'k hy' hy'b
      omega
    have hx2 : G.layerIndex x ≤ 2 := by
      obtain ⟨h1, h2, h3⟩ := G.layerIndex_spec hxΩ
      have := layer_le_of_mem_box S.cover_sep (by omega) hq h1 h2 h3 hxb
      omega
    have hν : (x, μ) ∉ cubeCut G (intBox q) := by
      intro hc
      rcases (mem_cubeCut G).1 hc with ⟨_, _, h3⟩ | ⟨h1, _, _⟩
      · exact h3 hxe
      · exact h1 hxb
    have hν' : (x', μ) ∉ cubeCut G (intBox q) := by
      intro hc
      rcases (mem_cubeCut G).1 hc with ⟨_, _, h3⟩ | ⟨h1, _, _⟩
      · exact h3 hx'e
      · exact h1 hx'b
    have key := small_holder_pair_cut G hcut hd0 S.mass S.weights α hα hj'1 hj'2 hj'k hy' f hsupp
      hMf0 hMf hρ1 hsep1 hθ0 hθ1 hxΩ hx'Ω hx2 hlay hz1 hν hν'
    refine key.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBθ' hX0) hF0

/-- The pair functional `(u(x'+e) - u(x')) - (u(x+e) - u(x))`. -/
noncomputable def pairLM {n : ℕ} (x x' : Torus d n) (μ : Fin d) : (Torus d n → ℂ) →ₗ[ℂ] ℂ :=
  evalLM (x' + Pi.single μ 1) - evalLM x' - evalLM (x + Pi.single μ 1) + evalLM x

theorem pairLM_apply {n : ℕ} (x x' : Torus d n) (μ : Fin d) (u : Torus d n → ℂ) :
    pairLM x x' μ u = (u (x' + Pi.single μ 1) - u x') - (u (x + Pi.single μ 1) - u x) := by
  simp only [pairLM, LinearMap.add_apply, LinearMap.sub_apply, evalLM_apply]
  ring

/-- **The Hölder bound of the cube Green's function** (no weight): for a source supported in the
cube with `ℓ² |f| ≤ C`, and two points of the cube at path distance `≤ 1` with displacement `z`,
`1 ≤ ‖z‖ < M₁ ℓ_q`: `ℓ(x)² |(∂u)(x') - (∂u)(x)| ≤ (K/θ) ℓ(x)^θ ‖z‖^{1-θ} C`. -/
theorem cube_holder (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kh : ℝ, 0 ≤ Kh ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {q : ℕ × CTorus d L N₁ m₁ K}, q ∈ cubeIdx G →
      ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ (f : G.Ω 1 → ℂ),
      (∀ z : G.Ω 1, f z ≠ 0 → (z : CTorus d L N₁ m₁ K) ∈ intBox q) → ∀ {C : ℝ}, 0 ≤ C →
      (∀ x : G.Ω 1, (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ C) →
      ∀ {x x' : CTorus d L N₁ m₁ K}, x ∈ G.Ω 1 → x' ∈ G.Ω 1 → x ∈ intBox q → x' ∈ intBox q →
      ∀ {μ : Fin d}, x + Pi.single μ 1 ∈ intBox q → x' + Pi.single μ 1 ∈ intBox q →
      G.layerIndex x ≤ G.layerIndex x' + 1 → G.pathDist x x' ≤ ENNReal.ofReal 1 →
      ∀ {z : Fin d → ℤ}, x' = x + intTorus z → 1 ≤ ‖z‖ → ‖z‖ < (L : ℝ) ^ (q.1 + m₁) →
      (G.spacing x) ^ 2 *
          ‖(solExt G (cubeH G a ν α q)⁻¹ f (x' + Pi.single μ 1) -
              solExt G (cubeH G a ν α q)⁻¹ f x') -
            (solExt G (cubeH G a ν α q)⁻¹ f (x + Pi.single μ 1) -
              solExt G (cubeH G a ν α q)⁻¹ f x)‖ ≤
        (Kh / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) * C := by
  obtain ⟨Kb, hKb, hB⟩ := cubeBlockHolder_exists (d := d) (L := L) hd hL
  have hε := agmonRate_pos (d := d) (by omega)
  have hγ0 : 0 < agmonRate d / 2 := by positivity
  have hcc : 0 ≤ countConst d L (agmonRate d / 2) := tsum_nonneg fun m => by positivity
  have hE1 : 1 ≤ Real.exp (agmonRate d / 2 * 1) := Real.one_le_exp (by positivity)
  refine ⟨Kb * (1 + Real.exp (agmonRate d / 2 * 1)) * countConst d L (agmonRate d / 2), by positivity, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα q hq θ hθ0 hθ1 f hf C hC hfC x x' hxΩ hx'Ω hxb hx'b μ hxe hx'e hlay
    hdist z hxz hz1 hzB
  have hBq := hB G S hα hq
  have hρ := S.one_lt_rho
  have hsp0 := spacing_pos G (x := x)
  have hz0 : (0 : ℝ) < ‖z‖ := by linarith
  set X : ℝ := (G.spacing x) ^ θ * ‖z‖ ^ (1 - θ) with hX
  have hX0 : 0 < X := by positivity
  have hΛ := box_blockAligned S.aligned S.cover_sep (by omega) hq
  have hx'x : G.pathDist x' x ≤ ENNReal.ofReal 1 := by rw [GeneratingSet.pathDist_comm]; exact hdist
  have hw1 : IsWeight G 0 (fun _ => (1 : ℝ)) := IsWeight.one G le_rfl
  have hcond : 2 * d * Real.log L ≤ (agmonRate d / 2 - 0) / 2 * (ϱ - 1) := by
    have h := S.sep
    have : agmonRate d / 16 * (ϱ - 1) ≤ (agmonRate d / 2 - 0) / 2 * (ϱ - 1) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      linarith
    linarith
  have key := weighted_sum_bound (G := G) (γ := 0) (γ0 := agmonRate d / 2)
    (Kc := Kb * (1 + Real.exp (agmonRate d / 2 * 1)) / θ) (s := (G.spacing x) ^ 2 / X)
    le_rfl hγ0 (by positivity) (by positivity) hw1 (cubeH G a ν α q)⁻¹ (pairLM x x' μ) hxΩ hΛ hρ
    hcond
    (fun {j'} {y'} hj'1 hj'k hy' hy'b g hsupp {Mf} hMf0 hMf => by
      have h := (hBq.pair hθ0 hθ1 hj'1 hj'k hy' hy'b g hsupp hMf0 hMf hxΩ hx'Ω hxb hx'b hxe hx'e
        hlay hxz hz1 hzB)
      rw [pairLM_apply]
      have hdec : decay (agmonRate d / 2) (G.pathDist x' y') ≤
          Real.exp (agmonRate d / 2 * 1) * decay (agmonRate d / 2) (G.pathDist x y') := by
        refine decay_le_exp_mul hγ0.le zero_le_one ?_
        exact (G.pathDist_triangle x x' y').trans (add_le_add hdist le_rfl)
      have hF0 : 0 ≤ (L : ℝ) ^ (2 * j') * Mf := by positivity
      have hd0 := decay_nonneg (agmonRate d / 2) (G.pathDist x y')
      rw [div_mul_eq_mul_div, div_le_iff₀ hX0]
      refine h.trans ?_
      have hsum : decay (agmonRate d / 2) (G.pathDist x y') +
          decay (agmonRate d / 2) (G.pathDist x' y') ≤
          (1 + Real.exp (agmonRate d / 2 * 1)) * decay (agmonRate d / 2) (G.pathDist x y') := by
        nlinarith
      have hK0 : 0 ≤ Kb / θ := by positivity
      calc Kb / θ * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) *
            ((decay (agmonRate d / 2) (G.pathDist x y') +
              decay (agmonRate d / 2) (G.pathDist x' y')) * ((L : ℝ) ^ (2 * j') * Mf))
          ≤ Kb / θ * X * (((1 + Real.exp (agmonRate d / 2 * 1)) *
              decay (agmonRate d / 2) (G.pathDist x y')) * ((L : ℝ) ^ (2 * j') * Mf)) := by
            rw [← hX]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsum hF0)
              (by positivity)
        _ = Kb * (1 + Real.exp (agmonRate d / 2 * 1)) / θ *
              decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf) * X := by
            ring)
    f hf hC (fun y => by simpa using hfC y)
  rw [pairLM_apply] at key
  simp only [mul_zero, zero_mul, Real.exp_zero, mul_one, sub_zero, one_mul] at key
  have e : (G.spacing x) ^ 2 * ‖(solExt G (cubeH G a ν α q)⁻¹ f (x' + Pi.single μ 1) -
        solExt G (cubeH G a ν α q)⁻¹ f x') - (solExt G (cubeH G a ν α q)⁻¹ f (x + Pi.single μ 1) -
        solExt G (cubeH G a ν α q)⁻¹ f x)‖ =
      X * ((G.spacing x) ^ 2 / X * ‖(solExt G (cubeH G a ν α q)⁻¹ f (x' + Pi.single μ 1) -
        solExt G (cubeH G a ν α q)⁻¹ f x') - (solExt G (cubeH G a ν α q)⁻¹ f (x + Pi.single μ 1) -
        solExt G (cubeH G a ν α q)⁻¹ f x)‖) := by
    field_simp
  rw [e]
  have hexp : Real.exp (agmonRate d / 2 * 1) = Real.exp (agmonRate d / 2) := by rw [mul_one]
  rw [hexp]
  calc _ ≤ X * (Kb * (1 + Real.exp (agmonRate d / 2)) / θ * countConst d L (agmonRate d / 2) * C) :=
        mul_le_mul_of_nonneg_left key hX0.le
    _ = _ := by ring

/-- **Increments of the cube solution inside the lifted ball.**  For `x` of layer `n ≥ 2` and
`d ‖z‖ ≤ L^(n-1)`, if the lifted points `x + w`, `‖w‖ ≤ ‖z‖`, lie in the cube together with their
forward neighbours, then `|u(x + z) - u(x)| ≤ (∑|z_i|) B_w C / L^(n-1)`. -/
theorem cube_lip (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Bw : ℝ, 0 ≤ Bw ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {q : ℕ × CTorus d L N₁ m₁ K}, q ∈ cubeIdx G →
      ∀ (f : G.Ω 1 → ℂ), (∀ z : G.Ω 1, f z ≠ 0 → (z : CTorus d L N₁ m₁ K) ∈ intBox q) →
      ∀ {C : ℝ}, 0 ≤ C → (∀ x : G.Ω 1, (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ C) →
      ∀ {n : ℕ}, 2 ≤ n → n ≤ K → ∀ {x : CTorus d L N₁ m₁ K}, x ∈ G.layer n →
      ∀ {z : Fin d → ℤ}, (d : ℝ) * ‖z‖ ≤ (L : ℝ) ^ (n - 1) →
      (∀ w : Fin d → ℤ, ‖w‖ ≤ ‖z‖ → x + intTorus w ∈ intBox q ∧
        ∀ ν' : Fin d, x + intTorus w + Pi.single ν' 1 ∈ intBox q) →
      ‖solExt G (cubeH G a ν α q)⁻¹ f (x + intTorus z) - solExt G (cubeH G a ν α q)⁻¹ f x‖ ≤
        ((∑ i, (z i).natAbs : ℕ) : ℝ) * (Bw * C / (L : ℝ) ^ (n - 1)) := by
  obtain ⟨Bw, hBw, hW⟩ := cube_weighted (d := d) (L := L) hd hL
  refine ⟨Bw, hBw, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα q hq f hf C hC hfC n hn2 hnK x hx z hzd hmarg
  have hd0 : 0 < d := by omega
  have hρ1 := S.one_lt_rho
  have hw1 : IsWeight G (gammaW d) (fun _ => (1 : ℝ)) := IsWeight.one G (gammaW_nonneg hd0)
  obtain ⟨-, hgrad, -⟩ := hW G S hα hq hw1 f hf hC (fun y => by simpa using hfC y)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hLp : (0 : ℝ) < (L : ℝ) ^ (n - 1) := by positivity
  refine lipschitz_ball (solExt G (cubeH G a ν α q)⁻¹ f) x (c := Bw * C / (L : ℝ) ^ (n - 1))
    (R := ‖z‖) ?_ _ z rfl le_rfl
  intro w' hw' μ
  have hdw : (d : ℝ) * ‖w'‖ ≤ (L : ℝ) ^ (n - 1) :=
    (mul_le_mul_of_nonneg_left hw' (Nat.cast_nonneg d)).trans hzd
  obtain ⟨hΩ, hlo, -⟩ := lift_mem_layers G hρ1.le hn2 hnK hx hdw
  obtain ⟨hb, hbe⟩ := hmarg w' hw'
  have hΩ' : x + intTorus w' ∈ G.Ω 1 := hΩ
  have h := hgrad (x := x + intTorus w') hΩ' hb hbe μ
  simp only [one_mul] at h
  rw [le_div_iff₀ hLp]
  have hn := norm_nonneg (solExt G (cubeH G a ν α q)⁻¹ f (x + intTorus w' + Pi.single μ 1) -
    solExt G (cubeH G a ν α q)⁻¹ f (x + intTorus w'))
  have hlo' : (L : ℝ) ^ (n - 1) ≤ G.spacing (x + intTorus w') := hlo
  nlinarith [mul_le_mul_of_nonneg_right hlo' hn]

end Block

end Balaban.Localization
