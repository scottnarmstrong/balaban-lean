/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.BoxCube
public import Balaban.Localization.DecoupledWeighted
public import Balaban.Localization.NC3

/-!
# NC3 for the interaction cubes of the cover, and its weighted form (LOCALIZATION.md §3.1)

`cubeBlockBounds`: for every centre `z` of the cover, the cube Green's function `H_z(A)⁻¹` of a
source supported in one block of the cube satisfies the block bounds of (NC3) — value, forward
gradient on retained bonds and Laplacian, each with the decay `e^{-(ε₀/2) d(x, y')}` — with a
constant `K_c(d, L)` independent of the centre, `M₁`, `K` and the torus.  Scale `j ≥ 2` is the
reflection regime (`pointwise_cut_cube`, `value_cut_cube`, `laplacian_cut_cube`), scale `j = 1` the
bounded regime (`small_*_cut`).

`cube_weighted_*`: the weighted form of (NC3) (`weighted_sum_bound`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ}

/-! ### Consequences of the separation hypothesis -/

theorem DGSetting.one_lt_rho (S : DGSetting G a ν) : 1 < ϱ := by
  have hd : (3 : ℝ) ≤ d := by exact_mod_cast S.hd
  have hL : (3 : ℝ) ≤ L := by exact_mod_cast S.hL
  have hlog : 0 < Real.log L := Real.log_pos (by linarith)
  have hε : 0 < agmonRate d := agmonRate_pos (by have := S.hd; omega)
  have h := S.sep
  by_contra hcon
  push Not at hcon
  have : agmonRate d / 16 * (ϱ - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have : 0 < 2 * (d : ℝ) * Real.log L := by positivity
  linarith

theorem DGSetting.sep_pow (S : DGSetting G a ν) {n : ℕ} (hn : (n : ℝ) ≤ d) :
    (L : ℝ) ^ n ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) := by
  have hL : (3 : ℝ) ≤ L := by exact_mod_cast S.hL
  have hlog : 0 < Real.log L := Real.log_pos (by linarith)
  have hε : 0 < agmonRate d := agmonRate_pos (by have := S.hd; omega)
  have hρ := S.one_lt_rho
  rw [← Real.exp_log (by positivity : (0 : ℝ) < (L : ℝ) ^ n), Real.log_pow]
  apply Real.exp_le_exp.2
  have h := S.sep
  have h1 : 0 < ϱ - 1 := by linarith
  have h2 : (n : ℝ) * Real.log L ≤ d * Real.log L := mul_le_mul_of_nonneg_right hn hlog.le
  have h3 : 0 ≤ agmonRate d * (ϱ - 1) := by positivity
  nlinarith

/-- The rate of the weights: `γ_w = ε₀ / 8` (one quarter of the decay rate `ε₀ / 2` of (NC2)). -/
noncomputable def gammaW (d : ℕ) : ℝ := agmonRate d / 8

theorem gammaW_nonneg (hd : 0 < d) : 0 ≤ gammaW d := by
  unfold gammaW; have := agmonRate_pos hd; positivity

theorem gammaW_lt (hd : 0 < d) : gammaW d < agmonRate d / 2 := by
  unfold gammaW; have := agmonRate_pos hd; linarith

theorem DGSetting.sep_weight (S : DGSetting G a ν) :
    2 * d * Real.log L ≤ (agmonRate d / 2 - gammaW d) / 2 * (ϱ - 1) := by
  have h := S.sep
  have hρ := S.one_lt_rho
  have hε : 0 < agmonRate d := agmonRate_pos (by have := S.hd; omega)
  unfold gammaW
  have : agmonRate d / 16 * (ϱ - 1) ≤ (agmonRate d / 2 - agmonRate d / 8) / 2 * (ϱ - 1) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    linarith
  linarith

/-! ### The block bounds of the cube operator -/

variable (G) in
/-- **The block bounds (NC3) for the cube operator of the centre `q`**: for a source `f` supported
in one `j'`-block of a point `y'` of the cube, `|f| ≤ M_f`, the solution `u = H_z(A)⁻¹ f` satisfies
at the points of the cube that are interior for the observable (value: all; forward gradient: the
forward neighbours in the cube; Laplacian: all neighbours in the cube) the bounds with the factor
`K_c e^{-(ε₀/2) d(x, y')} ℓ_{j'}² M_f`. -/
structure CubeBlockBounds (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ K)
    (Kc : ℝ) : Prop where
  bounds : ∀ {j' : ℕ} {y' : CTorus d L N₁ m₁ K}, 1 ≤ j' → j' ≤ K → y' ∈ G.layer j' →
    y' ∈ box q → ∀ (f : G.Ω 1 → ℂ),
    (∀ z : G.Ω 1, f z ≠ 0 → jBlock d L (N₁ * L ^ m₁) K j' z = jBlock d L (N₁ * L ^ m₁) K j' y') →
    ∀ {Mf : ℝ}, 0 ≤ Mf → (∀ z, ‖f z‖ ≤ Mf) →
    (∀ {x : CTorus d L N₁ m₁ K}, x ∈ G.Ω 1 → x ∈ box q →
      ‖solExt G (cubeH G a ν α q)⁻¹ f x‖ ≤
        Kc * decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf)) ∧
    (∀ {x : CTorus d L N₁ m₁ K}, x ∈ G.Ω 1 → x ∈ box q → (∀ ν' : Fin d, x + Pi.single ν' 1 ∈ box q) →
      ∀ μ : Fin d, G.spacing x * ‖solExt G (cubeH G a ν α q)⁻¹ f (x + Pi.single μ 1) -
          solExt G (cubeH G a ν α q)⁻¹ f x‖ ≤
        Kc * decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf)) ∧
    (∀ {x : CTorus d L N₁ m₁ K}, x ∈ G.Ω 1 → x ∈ box q →
      (∀ μ : Fin d, x + Pi.single μ 1 ∈ box q ∧ x - Pi.single μ 1 ∈ box q) →
      (G.spacing x) ^ 2 * ‖∑ μ : Fin d, (2 * solExt G (cubeH G a ν α q)⁻¹ f x -
          solExt G (cubeH G a ν α q)⁻¹ f (x + Pi.single μ 1) -
          solExt G (cubeH G a ν α q)⁻¹ f (x - Pi.single μ 1))‖ ≤
        Kc * decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf))

/-- A single forward difference is bounded by the sum of all of them. -/
theorem grad_le_of_sum {n : ℕ} [NeZero n] (u : Torus d n → ℂ) {s : ℝ} (hs : 0 ≤ s)
    (x : Torus d n) (μ : Fin d) :
    s * ‖u (x + Pi.single μ 1) - u x‖ ≤
      ‖u x‖ + s * ∑ ν : Fin d, ‖u (x + Pi.single ν 1) - u x‖ := by
  have h2 : ‖u (x + Pi.single μ 1) - u x‖ ≤ ∑ ν : Fin d, ‖u (x + Pi.single ν 1) - u x‖ :=
    Finset.single_le_sum (f := fun ν : Fin d => ‖u (x + Pi.single ν 1) - u x‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ μ)
  have := mul_le_mul_of_nonneg_left h2 hs
  have := norm_nonneg (u x)
  linarith

theorem cubeBlockBounds_exists (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {q : ℕ × CTorus d L N₁ m₁ K}, q ∈ cubeIdx G →
      CubeBlockBounds G a ν α q Kc := by
  obtain ⟨K1, hK1, hP⟩ := pointwise_cut_cube (d := d) (L := L) hd hL
  obtain ⟨K2, hK2, hLp⟩ := laplacian_cut_cube (d := d) (L := L) hd hL
  obtain ⟨K3, hK3, hV⟩ := value_cut_cube (d := d) (L := L) hd hL
  have hsc := smallConst_nonneg d L
  have hE : 0 ≤ Real.exp (agmonRate d * d) * (1 + 4 * smallConst d L) := by positivity
  refine ⟨K1 + K2 + K3 + smallConst d L + Real.exp (agmonRate d * d) * (1 + 4 * smallConst d L),
    by positivity, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα q hq
  have hd0 : 0 < d := by omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hρ1 : 1 ≤ ϱ := S.one_lt_rho.le
  have hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) := S.sep_pow (le_of_eq rfl)
  have hsep1 : (L : ℝ) ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) := by
    simpa using S.sep_pow (n := 1) (by exact_mod_cast (by omega : 1 ≤ d))
  obtain ⟨⟨hm1, hmK⟩, hl, hbase⟩ := (mem_cubeIdx G).1 hq
  refine ⟨fun {j'} {y'} hj'1 hj'k hy' hy'b f hsupp {Mf} hMf0 hMf => ?_⟩
  have hF0 : 0 ≤ (L : ℝ) ^ (2 * j') * Mf := by positivity
  have mono : ∀ (K0 : ℝ) (D : ℝ), K0 ≤ K1 + K2 + K3 + smallConst d L +
      Real.exp (agmonRate d * d) * (1 + 4 * smallConst d L) → 0 ≤ D → ∀ (X : ℝ), 0 ≤ X →
      K0 * D * X ≤ (K1 + K2 + K3 + smallConst d L +
      Real.exp (agmonRate d * d) * (1 + 4 * smallConst d L)) * D * X := by
    intro K0 D h hD X hX
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hD) hX
  by_cases hm : 2 ≤ q.1
  · -- reflection regime
    have hc := alignedCube_box S hq
    have : NeZero (5 * L ^ (q.1 + m₁ - min K (q.1 + 1))) :=
      ⟨Nat.mul_ne_zero (by norm_num) (pow_ne_zero _ (NeZero.ne L))⟩
    have hF := hc.foldSetting hm
    have hcb : cubeOf (N₁ * L ^ m₁) L K (min K (q.1 + 1)) (5 * L ^ (q.1 + m₁ - min K (q.1 + 1)))
        (boxCorner q) = box q := by
      rw [hc.cubeOf_eq, ← box_eq_cubeSet S.big hq]
    have hyc : y' ∈ cubeOf (N₁ * L ^ m₁) L K (min K (q.1 + 1))
        (5 * L ^ (q.1 + m₁ - min K (q.1 + 1))) (boxCorner q) := by rw [hcb]; exact hy'b
    refine ⟨fun {x} hxΩ hxb => ?_, fun {x} hxΩ hxb hxe μ => ?_, fun {x} hxΩ hxb hxe => ?_⟩
    · have key := hV G hF S.mass S.massLe S.weights α hα hρ1 hsep hj'1 hj'k hy' hyc f hsupp hMf0 hMf
        (x := x) (by rw [hcb]; exact hxb)
      rw [hcb] at key
      exact key.trans (mono K3 _ (by linarith) (decay_nonneg _ _) _ hF0)
    · have key := hP G hF S.mass S.massLe S.weights α hα hρ1 hsep hj'1 hj'k hy' hyc f hsupp hMf0 hMf
        (x := x) (by rw [hcb]; exact hxb) (fun ν' => by rw [hcb]; exact hxe ν')
      rw [hcb] at key
      have h1 := grad_le_of_sum (cubeSol G a ν (box q) α f) (spacing_pos G (x := x)).le x μ
      exact (h1.trans key).trans (mono K1 _ (by linarith) (decay_nonneg _ _) _ hF0)
    · have key := hLp G hF S.mass S.massLe S.weights α hα hρ1 hsep hj'1 hj'k hy' hyc f hsupp hMf0 hMf
        (x := x) (by rw [hcb]; exact hxb) (fun μ => by rw [hcb]; exact hxe μ)
      rw [hcb] at key
      exact key.trans (mono K2 _ (by linarith) (decay_nonneg _ _) _ hF0)
  · -- the bounded regime `j = 1`
    have hq1 : q.1 = 1 := by omega
    have hcut := cubeCut_aligned G (box_blockAligned S.aligned S.cover_sep (by omega) hq)
    have hj'2 : j' ≤ 2 := by
      have := layer_le_of_mem_box S.cover_sep (by omega) hq hj'1 hj'k hy' hy'b
      omega
    refine ⟨fun {x} hxΩ hxb => ?_, fun {x} hxΩ hxb hxe μ => ?_, fun {x} hxΩ hxb hxe => ?_⟩
    · have key := small_value_cut G hcut hd0 S.mass S.weights α hα hj'1 hj'2 hj'k hxΩ hy' f hsupp
        hMf0 hMf hρ1 hsep1
      exact key.trans (mono (smallConst d L) _ (by linarith [hK1, hK2, hK3, hE]) (decay_nonneg _ _) _ hF0)
    · have hμ : (x, μ) ∉ cubeCut G (box q) := by
        intro hc
        rcases (mem_cubeCut G).1 hc with ⟨_, _, h3⟩ | ⟨h1, _, _⟩
        · exact h3 (hxe μ)
        · exact h1 hxb
      have key := small_pointwise_cut G hcut hd0 S.mass S.weights α hα hj'1 hj'2 hj'k hxΩ hy' f hsupp
        hMf0 hMf hρ1 hsep1 hμ
      have h1 := norm_nonneg (cutSol G a ν (cubeCut G (box q)) α f x)
      change G.spacing x * ‖cutSol G a ν (cubeCut G (box q)) α f (x + Pi.single μ 1) -
        cutSol G a ν (cubeCut G (box q)) α f x‖ ≤ _
      refine (by linarith : _ ≤ _ + _).trans (key.trans ?_)
      exact mono (smallConst d L) _ (by linarith [hK1, hK2, hK3, hE]) (decay_nonneg _ _) _ hF0
    · have hnc : NoCutAt (cubeCut G (box q)) x :=
        noCutAt_cubeCut (box q) hxb hxe
      have key := small_laplacian_cut G hcut hd0 S.mass S.massLe S.weights α hα hj'1 hj'2 hj'k hxΩ hnc
        hy' f hsupp hMf0 hMf hρ1 hsep1
      exact key.trans (mono _ _ (by linarith [hK1, hK2, hK3, hsc]) (decay_nonneg _ _) _ hF0)

end Balaban.Localization
