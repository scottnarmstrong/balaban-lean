/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCubeHolder
public import Balaban.Localization.DecoupledMain
public import Balaban.Multiscale.HolderGlobal
public import Balaban.Multiscale.PointwiseHolder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Hölder part of (DG2) (LOCALIZATION.md §3.1)

For the decoupled Green's operator `G_s(A) f = ∑_z s_z χ_z ũ_z`, `ũ_z = H_z(A)⁻¹ c_z g`,
`g = (1 - 𝒦_s)⁻¹ f`, the Hölder seminorm of `∂(G_s f)` in the P2 (3.17) convention
(`HolderSeminormLE`) is bounded by `B e^{N₀ κ₁} θ⁻¹ |f|₂`.

* `perq_holder`: the pair bound for one centre.  Far pairs (`ℓ(x) ≤ d L ‖z‖`) are treated by the
  pointwise bounds of the product; for near pairs the Leibniz rule for the second difference
  `Δ²(χ u) = χ Δ²u + u Δ²χ + Δχ (u' - u) + (χ' - χ) Δu` is used, with the Hölder bound of the cube
  Green's function (`cube_holder`), the Lipschitz bound of `u` inside the lifted ball (`cube_lip`)
  and the pair regularity of `χ` at arbitrary displacements (`chi_pair`);
* `dg2_holder`: the sum over the at most `18 · 3^d` centres active at the four points.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

section Helpers

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ}

theorem chi_zero_of_not_inner (S : DGSetting G a ν) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) {P : CTorus d L N₁ m₁ K} (hP : P ∈ G.Ω 1) (hI : ¬ Inner q P)
    (μ : Fin d) : chi G q P = 0 ∧ chi G q (P + Pi.single μ 1) = 0 := by
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hP
  constructor
  · by_contra h
    exact hI (inner_of_chi_ne_zero S hq hP h)
  · by_contra h
    exact hI (inner_of_near S.cover_sep S.hM (by have := S.hL; omega) hq hn1 hnK hxl
      (inBox_of_chi_ne_zero h) (Or.inl ⟨μ, Or.inl rfl⟩))

/-- **The gradient of `χ_z ũ_z` at a site**, for every centre. -/
theorem T_grad (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Bg : ℝ, 0 ≤ Bg ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {q : ℕ × CTorus d L N₁ m₁ K}, q ∈ cubeIdx G →
      ∀ (g : G.Ω 1 → ℂ) {Cg : ℝ}, 0 ≤ Cg →
      (∀ x : G.Ω 1, (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖g x‖ ≤ Cg) →
      ∀ {P : CTorus d L N₁ m₁ K}, P ∈ G.Ω 1 → ∀ μ : Fin d,
      G.spacing P * ‖((chi G q (P + Pi.single μ 1) : ℝ) : ℂ) *
          cubeSolE G a ν α q g (P + Pi.single μ 1) -
        ((chi G q P : ℝ) : ℂ) * cubeSolE G a ν α q g P‖ ≤ Bg * Cg := by
  obtain ⟨Bs, hBs, hS⟩ := cube_star (d := d) (L := L) hd hL
  refine ⟨(1 + Cchi d L) * (Bs * Real.exp (2 * gammaW d * d)), by
    have := Cchi_nonneg d L; positivity, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα q hq g Cg hCg hg P hP μ
  classical
  by_cases hI : Inner q P
  · have hd0 : 0 < d := by omega
    have hw1 : IsWeight G (gammaW d) (fun _ => (1 : ℝ)) := IsWeight.one G (gammaW_nonneg hd0)
    obtain ⟨hsupp, hgq⟩ := cD_source (w := fun _ => (1 : ℝ)) q g hCg (fun z => by simpa using hg z)
    have hst := hS G S hα hq hw1 (cD G q *ᵥ g) hsupp hCg hgq (x := ⟨P, hP⟩) hI
    have hux : ∀ y, y ∉ G.Ω 1 → cubeSolE G a ν α q g y = 0 := fun y hy => cubeSolE_of_not_mem q g hy
    have hV0 : 0 ≤ Bs * Cg * Real.exp (2 * gammaW d * d) / (fun _ => (1 : ℝ)) P := by
      simp only; positivity
    have hper := perq_bounds S hq hux hV0 (x := ⟨P, hP⟩) hst
    have h := hper.2.1 μ
    simp only [div_one] at h
    refine h.trans (le_of_eq ?_)
    ring
  · obtain ⟨h1, h2⟩ := chi_zero_of_not_inner S hq hP hI μ
    rw [h1, h2]
    simp only [Complex.ofReal_zero, zero_mul, sub_self, norm_zero, mul_zero]
    have := Cchi_nonneg d L
    positivity

/-- The margin of the cube around a point of the support of `χ_z`. -/
theorem box_margin (S : DGSetting G a ν) {q : ℕ × CTorus d L N₁ m₁ K}
    {P0 x : CTorus d L N₁ m₁ K} (hP0 : chi G q P0 ≠ 0) {c0 w : Fin d → ℤ}
    (hx : P0 = x + intTorus c0)
    (hw : ∀ μ, |(((w - c0) μ : ℤ) : ℝ)| ≤ 2 * (L : ℝ) ^ 2 * (L : ℝ) ^ q.1 + 1) :
    x + intTorus w ∈ intBox q := by
  have h := inBox_cov4 S.hM (inBox_of_chi_ne_zero hP0) (w - c0) hw
  rw [mem_intBox]
  have e : P0 + (intTorus (w - c0) : CTorus d L N₁ m₁ K) = x + intTorus w := by
    rw [hx, add_assoc, intTorus_add_aux]
    congr 2; abel
  rwa [e] at h

theorem norm_single_le_one (μ : Fin d) : ‖(Pi.single μ (1 : ℤ) : Fin d → ℤ)‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  by_cases h : i = μ
  · subst h; simp
  · simp [h]

/-- If `χ_q` does not vanish at all four corners, one of them is `x + c₀` with `c₀` small, and the
scale of `x` is bounded by that of the centre. -/
theorem exists_corner (S : DGSetting G a ν) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G)
    {n n' : ℕ} (hn1 : 1 ≤ n) (hnK : n ≤ K) (hn1' : 1 ≤ n') (hnK' : n' ≤ K) (hnn : n ≤ n' + 1)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) {z : Fin d → ℤ}
    (hx' : x + intTorus z ∈ G.layer n') (μ : Fin d)
    (hrel : ¬ (chi G q x = 0 ∧ chi G q (x + Pi.single μ 1) = 0 ∧ chi G q (x + intTorus z) = 0 ∧
      chi G q (x + intTorus z + Pi.single μ 1) = 0)) :
    ∃ c0 : Fin d → ℤ, ‖c0‖ ≤ ‖z‖ + 1 ∧ chi G q (x + intTorus c0) ≠ 0 ∧ n ≤ q.1 + 2 := by
  have hd : 1 ≤ d := by have := S.hd; omega
  have hLL : 1 ≤ L := by have := S.hL; omega
  have hact : ∀ P : CTorus d L N₁ m₁ K, chi G q P ≠ 0 → q ∈ cubeActive G P := by
    intro P hP
    rw [mem_cubeActive]
    refine ⟨hq, fun h0 => hP ?_⟩
    unfold chi; rw [h0, zero_div]
  have he : ‖(Pi.single μ (1 : ℤ) : Fin d → ℤ)‖ ≤ 1 := norm_single_le_one μ
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
  by_cases h1 : chi G q x = 0
  · by_cases h2 : chi G q (x + Pi.single μ 1) = 0
    · by_cases h3 : chi G q (x + intTorus z) = 0
      · have h4 : chi G q (x + intTorus z + Pi.single μ 1) ≠ 0 := fun h4 => hrel ⟨h1, h2, h3, h4⟩
        refine ⟨z + Pi.single μ 1, ?_, ?_, ?_⟩
        · exact (norm_add_le _ _).trans (by linarith)
        · rw [intTorus_add_single']; rwa [← add_assoc]
        · have := cubeActive_layer_bounds S.aligned S.cover_sep hd hLL hn1' hnK' hx'
            (adj_add (x + intTorus z) μ).torusDist_le (hact _ h4)
          omega
      · refine ⟨z, by linarith, h3, ?_⟩
        have := cubeActive_layer_bounds S.aligned S.cover_sep hd hLL hn1' hnK' hx'
          (torusDist_self_le _) (hact _ h3)
        omega
    · refine ⟨Pi.single μ 1, by linarith [norm_nonneg (Pi.single μ (1 : ℤ) : Fin d → ℤ)], ?_, ?_⟩
      · rw [intTorus_single_aux]; simpa using h2
      · have := cubeActive_layer_bounds S.aligned S.cover_sep hd hLL hn1 hnK hx
          (adj_add x μ).torusDist_le (hact _ h2)
        omega
  · refine ⟨0, by simp; linarith, ?_, ?_⟩
    · rwa [intTorus_zero_aux, add_zero]
    · have := cubeActive_layer_bounds S.aligned S.cover_sep hd hLL hn1 hnK hx
        (torusDist_self_le _) (hact _ h1)
      omega

end Helpers

section Near

/-- **Leibniz rule for the second difference of a product.** -/
theorem leibniz_bound (u1 u2 u3 u4 : ℂ) (c1 c2 c3 c4 : ℝ) (h4 : |c4| ≤ 1) :
    ‖((c4 : ℂ) * u4 - (c3 : ℂ) * u3) - ((c2 : ℂ) * u2 - (c1 : ℂ) * u1)‖ ≤
      ‖(u4 - u3) - (u2 - u1)‖ + ‖u1‖ * |(c4 - c3) - (c2 - c1)| + |c4 - c3| * ‖u3 - u1‖ +
        |c4 - c2| * ‖u2 - u1‖ := by
  have hid : ((c4 : ℂ) * u4 - (c3 : ℂ) * u3) - ((c2 : ℂ) * u2 - (c1 : ℂ) * u1) =
      (c4 : ℂ) * ((u4 - u3) - (u2 - u1)) + u1 * (((c4 - c3) - (c2 - c1) : ℝ) : ℂ) +
        (((c4 - c3 : ℝ)) : ℂ) * (u3 - u1) + (((c4 - c2 : ℝ)) : ℂ) * (u2 - u1) := by
    push_cast; ring
  rw [hid]
  have n1 : ‖(c4 : ℂ) * ((u4 - u3) - (u2 - u1))‖ ≤ ‖(u4 - u3) - (u2 - u1)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right h4 (norm_nonneg _)).trans (one_mul _).le
  have n2 : ‖u1 * (((c4 - c3) - (c2 - c1) : ℝ) : ℂ)‖ = ‖u1‖ * |(c4 - c3) - (c2 - c1)| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have n3 : ‖(((c4 - c3 : ℝ)) : ℂ) * (u3 - u1)‖ = |c4 - c3| * ‖u3 - u1‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have n4 : ‖(((c4 - c2 : ℝ)) : ℂ) * (u2 - u1)‖ = |c4 - c2| * ‖u2 - u1‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc _ ≤ ‖(c4 : ℂ) * ((u4 - u3) - (u2 - u1))‖ + ‖u1 * (((c4 - c3) - (c2 - c1) : ℝ) : ℂ)‖ +
        ‖(((c4 - c3 : ℝ)) : ℂ) * (u3 - u1)‖ + ‖(((c4 - c2 : ℝ)) : ℂ) * (u2 - u1)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by rw [n2, n3, n4]; linarith

section Scales

theorem scaleB' {ℓ M c : ℝ} (hℓ : 0 < ℓ) (hM : 1 ≤ M) (hc : 0 ≤ c) :
    ℓ ^ 2 * (c / (ℓ * M) ^ 2) ≤ c := by
  have hM0 : 0 < M := by linarith
  have e : ℓ ^ 2 * (c / (ℓ * M) ^ 2) = c / M ^ 2 := by field_simp
  rw [e]
  exact div_le_self hc (one_le_pow₀ hM)

theorem scaleC' {ℓ a b cH N V Lr : ℝ} (ha : 0 < a) (hab : a ≤ b) (hℓ : ℓ = Lr * a)
    (hcH : 0 ≤ cH) (hN : 0 ≤ N) (hV : 0 ≤ V) :
    ℓ ^ 2 * ((cH / b) * (N * (V / a))) ≤ cH * Lr ^ 2 * (N * V) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  subst hℓ
  have e : (Lr * a) ^ 2 * ((cH / b) * (N * (V / a))) = (cH * Lr ^ 2 * (N * V)) * (a / b) := by
    field_simp
  rw [e]
  have h1 : a / b ≤ 1 := (div_le_one hb).2 hab
  have h0 : 0 ≤ cH * Lr ^ 2 * (N * V) := by positivity
  nlinarith

theorem scaleD' {ℓ M c V : ℝ} (hℓ : 0 < ℓ) (hM : 1 ≤ M) (hc : 0 ≤ c) (hV : 0 ≤ V) :
    ℓ ^ 2 * ((c / (ℓ * M)) * (V / ℓ)) ≤ c * V := by
  have hM0 : 0 < M := by linarith
  have e : ℓ ^ 2 * ((c / (ℓ * M)) * (V / ℓ)) = (c * V) / M := by field_simp
  rw [e]
  exact div_le_self (mul_nonneg hc hV) hM

end Scales

section Geom

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **The geometry of a near pair for a centre at which `χ_q` does not vanish.** -/
theorem near_geom (S : DGSetting G a ν) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G)
    {x : CTorus d L N₁ m₁ K} {z : Fin d → ℤ} (hxΩ : x ∈ G.Ω 1) (hx'Ω : x + intTorus z ∈ G.Ω 1)
    (hlay : G.layerIndex x ≤ G.layerIndex (x + intTorus z) + 1) (hz1 : 1 ≤ ‖z‖) (μ : Fin d)
    (hrel : ¬ (chi G q x = 0 ∧ chi G q (x + Pi.single μ 1) = 0 ∧ chi G q (x + intTorus z) = 0 ∧
      chi G q (x + intTorus z + Pi.single μ 1) = 0))
    (hfar : (d : ℝ) * L * ‖z‖ < G.spacing x) :
    2 ≤ G.layerIndex x ∧ (d : ℝ) * ‖z‖ ≤ (L : ℝ) ^ (G.layerIndex x - 1) ∧
      G.pathDist x (x + intTorus z) ≤ ENNReal.ofReal 1 ∧ ‖z‖ < (L : ℝ) ^ (q.1 + m₁) ∧
      (∀ w : Fin d → ℤ, ‖w‖ ≤ ‖z‖ + 3 → x + intTorus w ∈ intBox q) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by have := S.hd; omega : 1 ≤ d)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := S.hL; omega : 1 ≤ L)
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast S.hL
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hxΩ
  obtain ⟨hn1', hnK', hxl'⟩ := G.layerIndex_spec hx'Ω
  set n := G.layerIndex x with hn
  have hsp : G.spacing x = (L : ℝ) ^ n := rfl
  have hLn : (L : ℝ) ^ n = L * (L : ℝ) ^ (n - 1) := by
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨k', hk'⟩
    rw [hk']; simp [pow_succ']
  have hz0 : (0 : ℝ) < ‖z‖ := by linarith
  have hdz : 1 ≤ (d : ℝ) * ‖z‖ := by nlinarith
  have hn2 : 2 ≤ n := by
    by_contra h
    have h1 : n = 1 := by omega
    have h2 : G.spacing x = L := by rw [hsp, h1, pow_one]
    rw [h2] at hfar
    nlinarith [mul_le_mul_of_nonneg_left hdz (by linarith : (0 : ℝ) ≤ L)]
  have hzd : (d : ℝ) * ‖z‖ ≤ (L : ℝ) ^ (n - 1) := by
    rw [hsp, hLn] at hfar
    by_contra h
    push Not at h
    nlinarith [mul_lt_mul_of_pos_left h (by linarith : (0 : ℝ) < L)]
  have hfacts := holder_pair_facts G S.one_lt_rho.le (x := x) hxΩ (z := z) hx'Ω
    (Or.inr ⟨hn2, hzd⟩)
  have hdist : G.pathDist x (x + intTorus z) ≤ ENNReal.ofReal 1 := by
    rw [GeneratingSet.pathDist_comm]; exact hfacts.1
  obtain ⟨c0, hc0, hchi0, hnq⟩ := exists_corner S hq hn1 hnK hn1' hnK' hlay hxl hxl' μ hrel
  have hnorm_le : ∀ (w : Fin d → ℤ) (i : Fin d), |((w i : ℤ) : ℝ)| ≤ ‖w‖ := by
    intro w i
    have := norm_le_pi_norm w i
    rwa [Int.norm_eq_abs] at this
  have hzq : ‖z‖ ≤ (L : ℝ) ^ (q.1 + 1) := by
    have h1 : (L : ℝ) ^ (n - 1) ≤ (L : ℝ) ^ (q.1 + 1) := pow_le_pow_right₀ hL1 (by omega)
    have h2 : ‖z‖ ≤ (d : ℝ) * ‖z‖ := le_mul_of_one_le_left (norm_nonneg _) hd1
    linarith
  have hLq : (1 : ℝ) ≤ (L : ℝ) ^ q.1 := one_le_pow₀ hL1
  refine ⟨hn2, hzd, hdist, ?_, ?_⟩
  · have h2 := S.aligned.two_le
    calc ‖z‖ ≤ (L : ℝ) ^ (q.1 + 1) := hzq
      _ < (L : ℝ) ^ (q.1 + m₁) := pow_lt_pow_right₀ (by linarith) (by omega)
  · intro w hw
    refine box_margin S hchi0 (c0 := c0) (w := w) rfl (fun i => ?_)
    have e1 : (((w - c0) i : ℤ) : ℝ) = (w i : ℝ) - (c0 i : ℝ) := by simp
    rw [e1]
    refine (abs_sub _ _).trans ?_
    have a1 := hnorm_le w i
    have a2 := hnorm_le c0 i
    have hp : (L : ℝ) ^ (q.1 + 1) = L * (L : ℝ) ^ q.1 := by ring
    have hY : 3 ≤ (L : ℝ) * (L : ℝ) ^ q.1 := by
      have := mul_le_mul hL3 hLq zero_le_one (by linarith)
      linarith
    have e : 2 * (L : ℝ) ^ 2 * (L : ℝ) ^ q.1 = 2 * L * ((L : ℝ) * (L : ℝ) ^ q.1) := by ring
    have h6 : 6 * ((L : ℝ) * (L : ℝ) ^ q.1) ≤ 2 * L * ((L : ℝ) * (L : ℝ) ^ q.1) := by
      nlinarith
    rw [e]
    linarith

end Geom

end Near

section Arith

theorem near_arith {Kh Q θ X Cg N D P S2 S3 S4 : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hQ : 0 ≤ Q) (hCg : 0 ≤ Cg) (hX0 : 0 < X) (hNX : N ≤ D * X)
    (hmain : P ≤ Kh / θ * X * Cg + S2 + S3 + S4) (hsum : S2 + S3 + S4 = Q * (N * Cg))
    (hD0 : 0 ≤ D) : P ≤ (Kh + D * Q) / θ * X * Cg := by
  have hθ' : 1 ≤ 1 / θ := by rw [le_div_iff₀ hθ0]; linarith
  have h1 : Q * (N * Cg) ≤ Q * ((D * X) * Cg) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNX hCg) hQ
  have hDQ : 0 ≤ D * Q := mul_nonneg hD0 hQ
  have h2 : D * Q ≤ D * Q / θ := by
    calc D * Q = D * Q * 1 := (mul_one _).symm
      _ ≤ D * Q * (1 / θ) := mul_le_mul_of_nonneg_left hθ' hDQ
      _ = D * Q / θ := by ring
  have h3 : D * Q * X * Cg ≤ D * Q / θ * X * Cg :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hX0.le) hCg
  have e : (Kh + D * Q) / θ * X * Cg = Kh / θ * X * Cg + D * Q / θ * X * Cg := by ring
  rw [e]
  have e2 : Q * ((D * X) * Cg) = D * Q * X * Cg := by ring
  linarith

end Arith

section PerQ

variable {d L : ℕ} [NeZero L]

/-- The product `χ_q ũ_q`. -/
noncomputable def Tq {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) (g : G.Ω 1 → ℂ)
    (P : CTorus d L N₁ m₁ K) : ℂ :=
  ((chi G q P : ℝ) : ℂ) * cubeSolE G a ν α q g P

/-- **The pair bound for one centre, near pairs.** -/
theorem perq_near (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Bn : ℝ, 0 ≤ Bn ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {q : ℕ × CTorus d L N₁ m₁ K}, q ∈ cubeIdx G →
      ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ (g : G.Ω 1 → ℂ) {Cg : ℝ}, 0 ≤ Cg →
      (∀ x : G.Ω 1, (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖g x‖ ≤ Cg) →
      ∀ {x : CTorus d L N₁ m₁ K} {z : Fin d → ℤ}, x ∈ G.Ω 1 → x + intTorus z ∈ G.Ω 1 →
      G.layerIndex x ≤ G.layerIndex (x + intTorus z) + 1 → 1 ≤ ‖z‖ → ∀ (μ : Fin d),
      2 ≤ G.layerIndex x → (d : ℝ) * ‖z‖ ≤ (L : ℝ) ^ (G.layerIndex x - 1) →
      G.pathDist x (x + intTorus z) ≤ ENNReal.ofReal 1 → ‖z‖ < (L : ℝ) ^ (q.1 + m₁) →
      (∀ w : Fin d → ℤ, ‖w‖ ≤ ‖z‖ + 3 → x + intTorus w ∈ intBox q) →
      (G.spacing x) ^ 2 *
        ‖(Tq G a ν α q g (x + intTorus z + Pi.single μ 1) - Tq G a ν α q g (x + intTorus z)) -
          (Tq G a ν α q g (x + Pi.single μ 1) - Tq G a ν α q g x)‖ ≤
        (Bn / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) * Cg := by
  obtain ⟨Kh, hKh, hCH⟩ := cube_holder hd hL
  obtain ⟨Bl, hBl, hLip⟩ := cube_lip hd hL
  obtain ⟨Bw, hBw, hW⟩ := cube_weighted hd hL
  have hc1 := cChi1_nonneg d L
  have hc2 := cChi2_nonneg d L
  have hH1 := cH1_nonneg d L
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  refine ⟨Kh + d * (Bw * cChi2 d L + cH1 d L * (L : ℝ) ^ 2 * Bl + cChi1 d L * Bw),
    by positivity, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα q hq θ hθ0 hθ1 g Cg hCg hg x z hxΩ hx'Ω hlay hz1 μ hn2 hzd
    hdist hzB hmarg
  classical
  set x' : CTorus d L N₁ m₁ K := x + intTorus z with hx'def
  set e : CTorus d L N₁ m₁ K := Pi.single μ 1 with he
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hxΩ
  obtain ⟨hn1', hnK', hxl'⟩ := G.layerIndex_spec hx'Ω
  set n := G.layerIndex x with hn
  set n' := G.layerIndex x' with hn'
  have hsp : G.spacing x = (L : ℝ) ^ n := rfl
  have hℓ1 : (1 : ℝ) ≤ G.spacing x := one_le_pow₀ hL1
  have hℓ0 : 0 < G.spacing x := by linarith
  have hz0 : (0 : ℝ) < ‖z‖ := by linarith
  set X : ℝ := (G.spacing x) ^ θ * ‖z‖ ^ (1 - θ) with hX
  have hX0 : 0 < X := by positivity
  have hθ' : 1 ≤ 1 / θ := by rw [le_div_iff₀ hθ0]; linarith
  have hLn : (L : ℝ) ^ n = L * (L : ℝ) ^ (n - 1) := by
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨k', hk'⟩
    rw [hk']; simp [pow_succ']
  -- `‖z‖ ≤ X`
  have hzℓ : ‖z‖ ≤ G.spacing x := by
    have h1 : ‖z‖ ≤ (d : ℝ) * ‖z‖ := le_mul_of_one_le_left (norm_nonneg _) hd1
    have h2 : (L : ℝ) ^ (n - 1) ≤ (L : ℝ) ^ n := pow_le_pow_right₀ hL1 (by omega)
    rw [hsp]; linarith
  have hzX : ‖z‖ ≤ X := by
    have e1 : ‖z‖ = ‖z‖ ^ θ * ‖z‖ ^ (1 - θ) := by
      rw [← Real.rpow_add hz0]; simp
    have e2 : ‖z‖ ^ θ ≤ (G.spacing x) ^ θ := Real.rpow_le_rpow hz0.le hzℓ hθ0.le
    calc ‖z‖ = ‖z‖ ^ θ * ‖z‖ ^ (1 - θ) := e1
      _ ≤ (G.spacing x) ^ θ * ‖z‖ ^ (1 - θ) :=
          mul_le_mul_of_nonneg_right e2 (by positivity)
  have hNle : ((∑ i, (z i).natAbs : ℕ) : ℝ) ≤ d * ‖z‖ := natAbs_sum_le_card_mul z
  set N : ℝ := ((∑ i, (z i).natAbs : ℕ) : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  -- box memberships
  have hsingle : ∀ ν' : Fin d, ‖(Pi.single ν' (1 : ℤ) : Fin d → ℤ)‖ ≤ 1 := norm_single_le_one
  have hint_single : ∀ ν' : Fin d, (intTorus (Pi.single ν' (1 : ℤ)) : CTorus d L N₁ m₁ K) =
      Pi.single ν' 1 := by
    intro ν'; rw [intTorus_single_aux]; simp
  have hxb : x ∈ intBox q := by
    have := hmarg 0 (by simp; linarith)
    rwa [intTorus_zero_aux, add_zero] at this
  have hxeb : x + e ∈ intBox q := by
    have := hmarg (Pi.single μ 1) (by linarith [hsingle μ])
    rwa [hint_single] at this
  have hx'b : x' ∈ intBox q := hmarg z (by linarith)
  have hx'eb : x' + e ∈ intBox q := by
    have := hmarg (z + Pi.single μ 1) ((norm_add_le _ _).trans (by linarith [hsingle μ]))
    rwa [intTorus_add_single', ← add_assoc] at this
  have hnb : ∀ w : Fin d → ℤ, ‖w‖ ≤ ‖z‖ → x + intTorus w ∈ intBox q ∧
      ∀ ν' : Fin d, x + intTorus w + Pi.single ν' 1 ∈ intBox q := by
    intro w hw
    refine ⟨hmarg w (by linarith), fun ν' => ?_⟩
    have := hmarg (w + Pi.single ν' 1) ((norm_add_le _ _).trans (by linarith [hsingle ν']))
    rwa [intTorus_add_single', ← add_assoc] at this
  -- the data of the cube problem
  have hd0 : 0 < d := by omega
  have hw1 : IsWeight G (gammaW d) (fun _ => (1 : ℝ)) := IsWeight.one G (gammaW_nonneg hd0)
  obtain ⟨hsupp, hgq⟩ := cD_source (w := fun _ => (1 : ℝ)) q g hCg (fun z => by simpa using hg z)
  have hgq1 : ∀ y : G.Ω 1, (G.spacing (y : CTorus d L N₁ m₁ K)) ^ 2 * ‖(cD G q *ᵥ g) y‖ ≤ Cg :=
    fun y => by simpa using hgq y
  obtain ⟨hval, hgrad, -⟩ := hW G S hα hq hw1 (cD G q *ᵥ g) hsupp hCg hgq
  -- (A): the Hölder bound of the cube solution
  have hA := hCH G S hα hq hθ0 hθ1 (cD G q *ᵥ g) hsupp hCg hgq1 hxΩ hx'Ω hxb hx'b hxeb hx'eb
    hlay hdist (z := z) rfl hz1 hzB
  -- the Lipschitz bound of the cube solution
  have hlip := hLip G S hα hq (cD G q *ᵥ g) hsupp hCg hgq1 hn2 hnK hxl hzd hnb
  -- the pair regularity of `χ`
  have hchip := chi_pair S.aligned S.cover_sep (by omega : 1 ≤ d) (by omega : 2 ≤ L) hn1 hnK hn1'
    hnK' hlay hxl z hxl' μ hq
  have hchid := (chi_diff S.aligned S.cover_sep (by omega : 1 ≤ d) (by omega : 2 ≤ L) hn1' hnK'
    hxl' μ hq).1
  have hc4 := chi_nbr_mem_unit S.aligned (by omega : 2 ≤ L) hn1' hnK' hxl' μ
    (Or.inr (Or.inl rfl)) hq
  have hux : ‖cubeSolE G a ν α q g x‖ ≤ Bw * Cg := by
    have := hval hxΩ hxb
    simpa [cubeSolE] using this
  have hgx : G.spacing x * ‖cubeSolE G a ν α q g (x + e) - cubeSolE G a ν α q g x‖ ≤
      Bw * Cg := by
    have := hgrad hxΩ hxb (fun ν' => by
      have := (hnb 0 (by simp)).2 ν'
      rwa [intTorus_zero_aux, add_zero] at this) μ
    simpa [cubeSolE] using this
  -- the Leibniz rule
  have hLb := leibniz_bound (cubeSolE G a ν α q g x) (cubeSolE G a ν α q g (x + e))
    (cubeSolE G a ν α q g x') (cubeSolE G a ν α q g (x' + e)) (chi G q x) (chi G q (x + e))
    (chi G q x') (chi G q (x' + e)) (by rw [abs_of_nonneg hc4.1]; exact hc4.2)
  have eBn : (L : ℝ) ^ (n + m₁) = G.spacing x * (L : ℝ) ^ m₁ := by rw [hsp, pow_add]
  have hM1 : (1 : ℝ) ≤ (L : ℝ) ^ m₁ := one_le_pow₀ hL1
  have hB : G.spacing x ^ 2 * |(chi G q (x' + e) - chi G q x') - (chi G q (x + e) - chi G q x)| ≤
      cChi2 d L * N := by
    have h := hchip.2
    rw [eBn] at h
    calc _ ≤ G.spacing x ^ 2 * (cChi2 d L * N / (G.spacing x * (L : ℝ) ^ m₁) ^ 2) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ ≤ cChi2 d L * N := scaleB' hℓ0 hM1 (mul_nonneg hc2 hN0)
  have hC : G.spacing x ^ 2 * (|chi G q (x' + e) - chi G q x'| *
      ‖cubeSolE G a ν α q g x' - cubeSolE G a ν α q g x‖) ≤
      cH1 d L * (L : ℝ) ^ 2 * (N * (Bl * Cg)) := by
    have h2 : ‖cubeSolE G a ν α q g x' - cubeSolE G a ν α q g x‖ ≤
        N * (Bl * Cg / (L : ℝ) ^ (n - 1)) := hlip
    have ha : 0 < (L : ℝ) ^ (n - 1) := by positivity
    have hab : (L : ℝ) ^ (n - 1) ≤ (L : ℝ) ^ (n' + m₁) := pow_le_pow_right₀ hL1 (by omega)
    calc _ ≤ G.spacing x ^ 2 * ((cH1 d L / (L : ℝ) ^ (n' + m₁)) *
          (N * (Bl * Cg / (L : ℝ) ^ (n - 1)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hchid h2 (norm_nonneg _) (by positivity))
            (by positivity)
      _ ≤ _ := scaleC' ha hab (by rw [hsp]; exact hLn) hH1 hN0 (mul_nonneg hBl hCg)
  have hD : G.spacing x ^ 2 * (|chi G q (x' + e) - chi G q (x + e)| *
      ‖cubeSolE G a ν α q g (x + e) - cubeSolE G a ν α q g x‖) ≤
      cChi1 d L * N * (Bw * Cg) := by
    have h1 := hchip.1
    rw [eBn] at h1
    have h2 : ‖cubeSolE G a ν α q g (x + e) - cubeSolE G a ν α q g x‖ ≤
        Bw * Cg / G.spacing x := by
      rw [le_div_iff₀ hℓ0]; linarith [hgx]
    calc _ ≤ G.spacing x ^ 2 * ((cChi1 d L * N / (G.spacing x * (L : ℝ) ^ m₁)) *
          (Bw * Cg / G.spacing x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
            (by positivity)
      _ ≤ _ := scaleD' hℓ0 hM1 (mul_nonneg hc1 hN0) (mul_nonneg hBw hCg)
  have hu1 : ‖cubeSolE G a ν α q g x‖ * (G.spacing x ^ 2 * |(chi G q (x' + e) - chi G q x') -
      (chi G q (x + e) - chi G q x)|) ≤ (Bw * Cg) * (cChi2 d L * N) :=
    mul_le_mul hux hB (by positivity) (by positivity)
  have hA' : G.spacing x ^ 2 * ‖(cubeSolE G a ν α q g (x' + e) - cubeSolE G a ν α q g x') -
      (cubeSolE G a ν α q g (x + e) - cubeSolE G a ν α q g x)‖ ≤ Kh / θ * X * Cg := hA
  have hmain : G.spacing x ^ 2 * ‖(Tq G a ν α q g (x' + e) - Tq G a ν α q g x') -
      (Tq G a ν α q g (x + e) - Tq G a ν α q g x)‖ ≤
      Kh / θ * X * Cg + (Bw * Cg) * (cChi2 d L * N) + cH1 d L * (L : ℝ) ^ 2 * (N * (Bl * Cg)) +
        cChi1 d L * N * (Bw * Cg) := by
    have h0 := mul_le_mul_of_nonneg_left hLb (by positivity : 0 ≤ G.spacing x ^ 2)
    have e : G.spacing x ^ 2 * (‖(cubeSolE G a ν α q g (x' + e) - cubeSolE G a ν α q g x') -
        (cubeSolE G a ν α q g (x + e) - cubeSolE G a ν α q g x)‖ +
        ‖cubeSolE G a ν α q g x‖ * |(chi G q (x' + e) - chi G q x') -
          (chi G q (x + e) - chi G q x)| +
        |chi G q (x' + e) - chi G q x'| *
          ‖cubeSolE G a ν α q g x' - cubeSolE G a ν α q g x‖ +
        |chi G q (x' + e) - chi G q (x + e)| *
          ‖cubeSolE G a ν α q g (x + e) - cubeSolE G a ν α q g x‖) =
        G.spacing x ^ 2 * ‖(cubeSolE G a ν α q g (x' + e) - cubeSolE G a ν α q g x') -
          (cubeSolE G a ν α q g (x + e) - cubeSolE G a ν α q g x)‖ +
        ‖cubeSolE G a ν α q g x‖ * (G.spacing x ^ 2 * |(chi G q (x' + e) - chi G q x') -
          (chi G q (x + e) - chi G q x)|) +
        G.spacing x ^ 2 * (|chi G q (x' + e) - chi G q x'| *
          ‖cubeSolE G a ν α q g x' - cubeSolE G a ν α q g x‖) +
        G.spacing x ^ 2 * (|chi G q (x' + e) - chi G q (x + e)| *
          ‖cubeSolE G a ν α q g (x + e) - cubeSolE G a ν α q g x‖) := by ring
    rw [e] at h0
    unfold Tq
    linarith
  -- the conclusion
  have hQ : 0 ≤ Bw * cChi2 d L + cH1 d L * (L : ℝ) ^ 2 * Bl + cChi1 d L * Bw := by positivity
  have hsumN : (Bw * Cg) * (cChi2 d L * N) + cH1 d L * (L : ℝ) ^ 2 * (N * (Bl * Cg)) +
      cChi1 d L * N * (Bw * Cg) =
      (Bw * cChi2 d L + cH1 d L * (L : ℝ) ^ 2 * Bl + cChi1 d L * Bw) * (N * Cg) := by ring
  have hNX : N ≤ d * X := hNle.trans (mul_le_mul_of_nonneg_left hzX (by positivity))
  exact near_arith hθ0 hθ1 hQ hCg hX0 hNX hmain hsumN (Nat.cast_nonneg d)

/-- **The pair bound for one centre, far pairs.** -/
theorem perq_far (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Bf : ℝ, 0 ≤ Bf ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {q : ℕ × CTorus d L N₁ m₁ K}, q ∈ cubeIdx G →
      ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ (g : G.Ω 1 → ℂ) {Cg : ℝ}, 0 ≤ Cg →
      (∀ x : G.Ω 1, (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖g x‖ ≤ Cg) →
      ∀ {x : CTorus d L N₁ m₁ K} {z : Fin d → ℤ}, x ∈ G.Ω 1 → x + intTorus z ∈ G.Ω 1 →
      G.layerIndex x ≤ G.layerIndex (x + intTorus z) + 1 → 1 ≤ ‖z‖ → ∀ (μ : Fin d),
      G.spacing x ≤ d * L * ‖z‖ →
      (G.spacing x) ^ 2 *
        ‖(Tq G a ν α q g (x + intTorus z + Pi.single μ 1) - Tq G a ν α q g (x + intTorus z)) -
          (Tq G a ν α q g (x + Pi.single μ 1) - Tq G a ν α q g x)‖ ≤
        (Bf / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) * Cg := by
  obtain ⟨Bg, hBg, hTg⟩ := T_grad hd hL
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  refine ⟨Bg * (d * L) * (1 + L), by positivity, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα q hq θ hθ0 hθ1 g Cg hCg hg x z hxΩ hx'Ω hlay hz1 μ hfar
  classical
  set x' : CTorus d L N₁ m₁ K := x + intTorus z with hx'def
  set e : CTorus d L N₁ m₁ K := Pi.single μ 1 with he
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hxΩ
  have hsp : G.spacing x = (L : ℝ) ^ G.layerIndex x := rfl
  have hsp' : G.spacing x' = (L : ℝ) ^ G.layerIndex x' := rfl
  have hℓ1 : (1 : ℝ) ≤ G.spacing x := one_le_pow₀ hL1
  have hℓ0 : 0 < G.spacing x := by linarith
  have hsx : G.spacing x ≤ L * G.spacing x' := by
    rw [hsp, hsp', ← pow_succ']; exact pow_le_pow_right₀ hL1 hlay
  have hz0 : (0 : ℝ) < ‖z‖ := by linarith
  set X : ℝ := (G.spacing x) ^ θ * ‖z‖ ^ (1 - θ) with hX
  have hX0 : 0 < X := by positivity
  have hθ' : 1 ≤ 1 / θ := by rw [le_div_iff₀ hθ0]; linarith
  have hg1 := hTg G S hα hq g hCg hg hxΩ μ
  have hg2 := hTg G S hα hq g hCg hg hx'Ω μ
  have hℓX : G.spacing x ≤ (d * L) * X :=
    le_const_rpow_mul hℓ1 hz1 (by nlinarith) hθ0 hθ1 (Or.inr hfar)
  have hBC : 0 ≤ Bg * Cg := mul_nonneg hBg hCg
  set D1 := Tq G a ν α q g (x' + e) - Tq G a ν α q g x' with hD1
  set D2 := Tq G a ν α q g (x + e) - Tq G a ν α q g x with hD2
  have hn := norm_sub_le D1 D2
  have hn1' : 0 ≤ ‖D1‖ := norm_nonneg _
  have hn2' : 0 ≤ ‖D2‖ := norm_nonneg _
  have e1 : G.spacing x * ‖D1‖ ≤ L * (Bg * Cg) := by
    calc G.spacing x * ‖D1‖ ≤ (L * G.spacing x') * ‖D1‖ := mul_le_mul_of_nonneg_right hsx hn1'
      _ = L * (G.spacing x' * ‖D1‖) := by ring
      _ ≤ L * (Bg * Cg) := mul_le_mul_of_nonneg_left hg2 (by linarith)
  have e2 : G.spacing x * ‖D2‖ ≤ Bg * Cg := hg1
  calc (G.spacing x) ^ 2 * ‖D1 - D2‖ ≤ (G.spacing x) ^ 2 * (‖D1‖ + ‖D2‖) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
    _ = G.spacing x * (G.spacing x * ‖D1‖) + G.spacing x * (G.spacing x * ‖D2‖) := by ring
    _ ≤ G.spacing x * (L * (Bg * Cg)) + G.spacing x * (Bg * Cg) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hℓ0.le) (mul_le_mul_of_nonneg_left e2 hℓ0.le)
    _ = G.spacing x * ((1 + L) * (Bg * Cg)) := by ring
    _ ≤ ((d * L) * X) * ((1 + L) * (Bg * Cg)) :=
        mul_le_mul_of_nonneg_right hℓX (by positivity)
    _ = (Bg * (d * L) * (1 + L)) * X * Cg := by ring
    _ ≤ Bg * (d * L) * (1 + L) / θ * X * Cg := by
        have h0 : 0 ≤ Bg * (d * L) * (1 + L) := by positivity
        have h2 : Bg * (d * L) * (1 + L) ≤ Bg * (d * L) * (1 + L) / θ := by
          calc _ = _ * 1 := (mul_one _).symm
            _ ≤ _ * (1 / θ) := mul_le_mul_of_nonneg_left hθ' h0
            _ = _ / θ := by ring
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hX0.le) hCg

/-- **The pair bound for one centre.** -/
theorem perq_holder (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Bq : ℝ, 0 ≤ Bq ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {q : ℕ × CTorus d L N₁ m₁ K}, q ∈ cubeIdx G →
      ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ (g : G.Ω 1 → ℂ) {Cg : ℝ}, 0 ≤ Cg →
      (∀ x : G.Ω 1, (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖g x‖ ≤ Cg) →
      ∀ {x : CTorus d L N₁ m₁ K} {z : Fin d → ℤ}, x ∈ G.Ω 1 → x + intTorus z ∈ G.Ω 1 →
      G.layerIndex x ≤ G.layerIndex (x + intTorus z) + 1 → 1 ≤ ‖z‖ → ∀ (μ : Fin d),
      (G.spacing x) ^ 2 *
        ‖(Tq G a ν α q g (x + intTorus z + Pi.single μ 1) - Tq G a ν α q g (x + intTorus z)) -
          (Tq G a ν α q g (x + Pi.single μ 1) - Tq G a ν α q g x)‖ ≤
        (Bq / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) * Cg := by
  obtain ⟨Bf, hBf, hF⟩ := perq_far hd hL
  obtain ⟨Bn, hBn, hN⟩ := perq_near hd hL
  refine ⟨Bf + Bn, by positivity, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα q hq θ hθ0 hθ1 g Cg hCg hg x z hxΩ hx'Ω hlay hz1 μ
  classical
  have hℓ1 : (1 : ℝ) ≤ G.spacing x := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ L))
  have hz0 : (0 : ℝ) < ‖z‖ := by linarith
  have hX0 : 0 < (G.spacing x) ^ θ * ‖z‖ ^ (1 - θ) := by positivity
  have hmono : ∀ B : ℝ, 0 ≤ B → B ≤ Bf + Bn → ∀ T : ℝ,
      T ≤ B / θ * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) * Cg →
      T ≤ (Bf + Bn) / θ * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) * Cg := by
    intro B hB0 hB T hT
    refine hT.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hB hθ0.le) hX0.le) hCg
  by_cases hrel : chi G q x = 0 ∧ chi G q (x + Pi.single μ 1) = 0 ∧
      chi G q (x + intTorus z) = 0 ∧ chi G q (x + intTorus z + Pi.single μ 1) = 0
  · obtain ⟨h1, h2, h3, h4⟩ := hrel
    have : (G.spacing x) ^ 2 *
        ‖(Tq G a ν α q g (x + intTorus z + Pi.single μ 1) - Tq G a ν α q g (x + intTorus z)) -
          (Tq G a ν α q g (x + Pi.single μ 1) - Tq G a ν α q g x)‖ = 0 := by
      unfold Tq
      rw [h1, h2, h3, h4]
      simp
    rw [this]
    positivity
  by_cases hfar : G.spacing x ≤ d * L * ‖z‖
  · exact hmono Bf hBf (by linarith) _ (hF G S hα hq hθ0 hθ1 g hCg hg hxΩ hx'Ω hlay hz1 μ hfar)
  · push Not at hfar
    obtain ⟨hn2, hzd, hdist, hzB, hmarg⟩ := near_geom S hq hxΩ hx'Ω hlay hz1 μ hrel hfar
    exact hmono Bn hBn (by linarith) _ (hN G S hα hq hθ0 hθ1 g hCg hg hxΩ hx'Ω hlay hz1 μ hn2 hzd
      hdist hzB hmarg)

end PerQ

section Assembly

variable {d L : ℕ} [NeZero L]

/-- The coefficient bound `‖s_z‖ ≤ e^{N₀ κ₁}` and the Neumann solution `g = (1 - 𝒦_s)⁻¹ f`. -/
theorem dg2_g_bound (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ cstar : ℝ, 0 ≤ cstar ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {κ : ℝ}, 0 ≤ κ →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : ℕ × CTorus d L N₁ m₁ K → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ (f : G.Ω 1 → ℂ) {C : ℝ}, 0 ≤ C →
      (∀ x : G.Ω 1, (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ C) →
      Gs G a ν α s *ᵥ f = Gstar G a ν α s *ᵥ ((1 - Kcal G a ν α s)⁻¹ *ᵥ f) ∧
      ∀ x : G.Ω 1, (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
        ‖((1 - Kcal G a ν α s)⁻¹ *ᵥ f) x‖ ≤ 4 * C / 3 := by
  obtain ⟨cstar, BG, hcs, hBG, H⟩ := dg2_all (d := d) (L := L) hd hL
  refine ⟨cstar, hcs, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα κ hκ hMκ s hs f C hC hfC
  have hd0 : 0 < d := by omega
  have hw1 : IsWeight G (gammaW d) (fun _ => (1 : ℝ)) := IsWeight.one G (gammaW_nonneg hd0)
  obtain ⟨⟨hU, -⟩, hKc⟩ := H G S hα hκ hMκ hs hw1 f hC (fun x => by simpa using hfC x)
  have hspos : ∀ x : G.Ω 1, 0 < (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 := fun x => by
    have := spacing_pos G (x := (x : CTorus d L N₁ m₁ K)); positivity
  set g : G.Ω 1 → ℂ := (1 - Kcal G a ν α s)⁻¹ *ᵥ f with hgdef
  have hg : g - Kcal G a ν α s *ᵥ g = f := by
    have h1 : (1 - Kcal G a ν α s) *ᵥ g = f := by
      rw [hgdef, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU), Matrix.one_mulVec]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h1
    exact h1
  have hKw : ∀ (h : G.Ω 1 → ℂ) (C : ℝ), 0 ≤ C →
      WBd (fun x : G.Ω 1 => (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2) h C →
      WBd (fun x : G.Ω 1 => (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2) (Kcal G a ν α s *ᵥ h)
        (C / 4) := by
    intro h C0 hC0 hh x
    have := hKc h hC0 (fun y => by simpa using hh y) x
    simpa using this
  have hgW := neumann_bound hspos hKw hg (fun x => hfC x)
  refine ⟨?_, fun x => hgW x⟩
  rw [hgdef, Gs, ← Matrix.mulVec_mulVec]

/-- **The Hölder part of (DG2).**  For `M₁ ≥ c_* e^{N₀ κ₁}`, `|s_P| ≤ e^{κ₁}`, `|A|₂ ≤ γ₁` and
`|f|₂ ≤ C`: `|∂ G_s(A) f|_{(θ),2-θ} ≤ (B_H e^{N₀κ₁}/θ) C`, in the convention of P2 (3.17)
(`HolderSeminormLE`); `B_H = B_H(d, L)`. -/
theorem dg2_holder (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ cstar BH : ℝ, 0 ≤ cstar ∧ 0 ≤ BH ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {κ : ℝ}, 0 ≤ κ →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : ℕ × CTorus d L N₁ m₁ K → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ (f : G.Ω 1 → ℂ) {C : ℝ}, 0 ≤ C →
      (∀ x : G.Ω 1, (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ C) →
      HolderSeminormLE G (zeroExt (G.Ω 1) (Gs G a ν α s *ᵥ f)) θ (2 - θ)
        (BH * Real.exp (N0 d L * κ) / θ * C) := by
  obtain ⟨cstar, hcs, hgb⟩ := dg2_g_bound hd hL
  obtain ⟨Bq, hBq, hP⟩ := perq_holder hd hL
  refine ⟨cstar, 18 * 3 ^ d * Bq * (4 / 3), hcs, by positivity, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα κ hκ hMκ s hs θ hθ0 hθ1 f C hC hfC
  classical
  obtain ⟨hGs, hgC⟩ := hgb G S hα hκ hMκ hs f hC hfC
  set g : G.Ω 1 → ℂ := (1 - Kcal G a ν α s)⁻¹ *ᵥ f with hgdef
  have hC' : 0 ≤ 4 * C / 3 := by positivity
  have hv : ∀ y : CTorus d L N₁ m₁ K, zeroExt (G.Ω 1) (Gs G a ν α s *ᵥ f) y =
      ∑ q ∈ cubeIdx G, sProd G s q * Tq G a ν α q g y := by
    intro y; rw [hGs]; exact Gstar_apply s g y
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hρ : (d : ℝ) < ϱ := by
    have h1 := S.cover_sep
    have h2 : (1 : ℝ) ≤ (L : ℝ) ^ m₁ := one_le_pow₀ hL1
    have h3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith [mul_le_mul h3 h2 zero_le_one (by linarith), mul_pos hd0 hd0]
  have hcoef : ∀ q ∈ cubeIdx G, ‖sProd G s q‖ ≤ Real.exp (N0 d L * κ) := fun q hq =>
    norm_sProd_le S.aligned S.cover_sep S.hM (by omega : 1 ≤ L) hq hκ hs
  intro x hx x' hx'T hne z hz ν'
  have hx'Ω : x' ∈ G.Ω 1 := hx'T.1
  have hlay := layer_le_of_tildeDelta G hρ hx hx'T
  have hz1 : 1 ≤ ‖z‖ := by
    refine one_le_norm_of_ne_zero ?_
    rintro rfl
    rw [liftPt_zero] at hz
    exact hne hz
  have hx'eq : x' = x + intTorus z := hz.symm
  subst hx'eq
  have hz0 : (0 : ℝ) < ‖z‖ := by linarith
  have hsp0 := spacing_pos G (x := x)
  set X : ℝ := (G.spacing x) ^ θ * ‖z‖ ^ (1 - θ) with hX
  have hX0 : 0 < X := by positivity
  -- the sum over the active centres
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hx
  obtain ⟨hn1', hnK', hxl'⟩ := G.layerIndex_spec hx'Ω
  set A : Finset (ℕ × CTorus d L N₁ m₁ K) := cubeSupp G x ν' ∪ cubeSupp G (x + intTorus z) ν' with hA
  have hAsub : A ⊆ cubeIdx G :=
    Finset.union_subset (cubeSupp_subset x ν') (cubeSupp_subset (x + intTorus z) ν')
  have hAcard : (A.card : ℝ) ≤ 18 * 3 ^ d := by
    have h1 := card_cubeSupp_le S.aligned S.cover_sep (by omega : 1 ≤ d) (by omega : 1 ≤ L) hn1 hnK
      hxl ν'
    have h2 := card_cubeSupp_le S.aligned S.cover_sep (by omega : 1 ≤ d) (by omega : 1 ≤ L) hn1'
      hnK' hxl' ν'
    have := card_union_le (cubeSupp G x ν') (cubeSupp G (x + intTorus z) ν')
    have h3 : A.card ≤ 18 * 3 ^ d := by rw [hA]; omega
    exact_mod_cast h3
  set Pq : ℕ × CTorus d L N₁ m₁ K → ℂ := fun q =>
    (Tq G a ν α q g (x + intTorus z + Pi.single ν' 1) - Tq G a ν α q g (x + intTorus z)) -
      (Tq G a ν α q g (x + Pi.single ν' 1) - Tq G a ν α q g x) with hPq
  have hdiff : (zeroExt (G.Ω 1) (Gs G a ν α s *ᵥ f) (x + intTorus z + Pi.single ν' 1) -
        zeroExt (G.Ω 1) (Gs G a ν α s *ᵥ f) (x + intTorus z)) -
      (zeroExt (G.Ω 1) (Gs G a ν α s *ᵥ f) (x + Pi.single ν' 1) -
        zeroExt (G.Ω 1) (Gs G a ν α s *ᵥ f) x) = ∑ q ∈ cubeIdx G, sProd G s q * Pq q := by
    simp only [hv, hPq]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hzero : ∀ q ∈ cubeIdx G, q ∉ A → Pq q = 0 := by
    intro q hq hqA
    have h1 : q ∉ cubeSupp G x ν' := fun h => hqA (Finset.mem_union_left _ h)
    have h2 : q ∉ cubeSupp G (x + intTorus z) ν' := fun h => hqA (Finset.mem_union_right _ h)
    obtain ⟨a1, a2, -⟩ := not_mem_cubeSupp hq h1
    obtain ⟨a3, a4, -⟩ := not_mem_cubeSupp hq h2
    have c1 : chi G q x = 0 := by unfold chi; rw [a1, zero_div]
    have c2 : chi G q (x + Pi.single ν' 1) = 0 := by unfold chi; rw [a2, zero_div]
    have c3 : chi G q (x + intTorus z) = 0 := by unfold chi; rw [a3, zero_div]
    have c4 : chi G q (x + intTorus z + Pi.single ν' 1) = 0 := by unfold chi; rw [a4, zero_div]
    simp only [hPq, Tq, c1, c2, c3, c4, Complex.ofReal_zero, zero_mul, sub_self]
  set Dn : ℂ := (zeroExt (G.Ω 1) (Gs G a ν α s *ᵥ f) (x + intTorus z + Pi.single ν' 1) -
        zeroExt (G.Ω 1) (Gs G a ν α s *ᵥ f) (x + intTorus z)) -
      (zeroExt (G.Ω 1) (Gs G a ν α s *ᵥ f) (x + Pi.single ν' 1) -
        zeroExt (G.Ω 1) (Gs G a ν α s *ᵥ f) x) with hDn
  have hterm : ∀ q ∈ A, (G.spacing x) ^ 2 * ‖sProd G s q * Pq q‖ ≤
      Real.exp (N0 d L * κ) * (Bq / θ * X * (4 * C / 3)) := by
    intro q hqA
    have hq := hAsub hqA
    have := hP G S hα hq hθ0 hθ1 g hC' hgC hx hx'Ω hlay hz1 ν'
    rw [norm_mul]
    calc (G.spacing x) ^ 2 * (‖sProd G s q‖ * ‖Pq q‖)
        = ‖sProd G s q‖ * ((G.spacing x) ^ 2 * ‖Pq q‖) := by ring
      _ ≤ Real.exp (N0 d L * κ) * (Bq / θ * X * (4 * C / 3)) :=
          mul_le_mul (hcoef q hq) this (by positivity) (Real.exp_pos _).le
  have hsumb : (G.spacing x) ^ 2 * ‖Dn‖ ≤
      18 * 3 ^ d * (Real.exp (N0 d L * κ) * (Bq / θ * X * (4 * C / 3))) := by
    rw [hdiff, ← Finset.sum_subset hAsub (fun q hq hnA => by rw [hzero q hq hnA, mul_zero])]
    calc (G.spacing x) ^ 2 * ‖∑ q ∈ A, sProd G s q * Pq q‖
        ≤ (G.spacing x) ^ 2 * ∑ q ∈ A, ‖sProd G s q * Pq q‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ = ∑ q ∈ A, (G.spacing x) ^ 2 * ‖sProd G s q * Pq q‖ := by rw [Finset.mul_sum]
      _ ≤ ∑ _q ∈ A, Real.exp (N0 d L * κ) * (Bq / θ * X * (4 * C / 3)) :=
          Finset.sum_le_sum hterm
      _ = A.card * (Real.exp (N0 d L * κ) * (Bq / θ * X * (4 * C / 3))) := by simp
      _ ≤ 18 * 3 ^ d * (Real.exp (N0 d L * κ) * (Bq / θ * X * (4 * C / 3))) :=
          mul_le_mul_of_nonneg_right hAcard (by positivity)
  have hsig : (G.spacing x) ^ (2 - θ) * (‖z‖ ^ (1 - θ))⁻¹ = (G.spacing x) ^ 2 / X := by
    rw [hX, Real.rpow_sub hsp0, Real.rpow_two]
    have : 0 < ‖z‖ ^ (1 - θ) := by positivity
    have : 0 < (G.spacing x) ^ θ := by positivity
    field_simp
  rw [hsig, div_mul_eq_mul_div, div_le_iff₀ hX0]
  refine hsumb.trans (le_of_eq ?_)
  ring

end Assembly

end Balaban.Localization
