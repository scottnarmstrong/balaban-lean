/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledBounds

/-!
# The decoupled Green's operator: inverse and bounds (DG1)--(DG3)

* `neumann_bound`, `neumann_isUnit`: an operator of weighted norm `≤ 1/4` has `1 - K` invertible
  with inverse of norm `≤ 4/3`;
* `Kcal_isUnit`: `1 - 𝒦_s(A)` is invertible (DG1), `Gs_eq`: `G_s f = G*_s g`, `g = (1 - 𝒦_s)⁻¹ f`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Neumann

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weighted sup-norm bound `ω(x) ‖f(x)‖ ≤ C`. -/
def WBd (ω : ι → ℝ) (f : ι → ℂ) (C : ℝ) : Prop := ∀ x, ω x * ‖f x‖ ≤ C

theorem neumann_bound {ω : ι → ℝ} (hω : ∀ x, 0 < ω x) {K : Matrix ι ι ℂ}
    (hK : ∀ (h : ι → ℂ) (C : ℝ), 0 ≤ C → WBd ω h C → WBd ω (K *ᵥ h) (C / 4))
    {f g : ι → ℂ} (hg : g - K *ᵥ g = f) {C : ℝ} (hC : 0 ≤ C) (hf : WBd ω f C) :
    WBd ω g (4 * C / 3) := by
  intro x
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact hι.elim x
  obtain ⟨x0, -, hx0⟩ := Finset.exists_max_image Finset.univ (fun y => ω y * ‖g y‖)
    Finset.univ_nonempty
  set m : ℝ := ω x0 * ‖g x0‖ with hm
  have hm0 : 0 ≤ m := by have := hω x0; positivity
  have hWg : WBd ω g m := fun y => hx0 y (Finset.mem_univ y)
  have hKg := hK g m hm0 hWg
  have key : ∀ y, ω y * ‖g y‖ ≤ C + m / 4 := by
    intro y
    have e : g y = f y + (K *ᵥ g) y := by
      have := congrFun hg y
      simp only [Pi.sub_apply] at this
      rw [← this]; ring
    calc ω y * ‖g y‖ ≤ ω y * (‖f y‖ + ‖(K *ᵥ g) y‖) := by
          rw [e]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (hω y).le
      _ = ω y * ‖f y‖ + ω y * ‖(K *ᵥ g) y‖ := by ring
      _ ≤ C + m / 4 := add_le_add (hf y) (hKg y)
  have h0 := key x0
  have hmC : m ≤ 4 * C / 3 := by linarith
  exact (hx0 x (Finset.mem_univ x)).trans hmC

theorem neumann_isUnit {ω : ι → ℝ} (hω : ∀ x, 0 < ω x) {K : Matrix ι ι ℂ}
    (hK : ∀ (h : ι → ℂ) (C : ℝ), 0 ≤ C → WBd ω h C → WBd ω (K *ᵥ h) (C / 4)) :
    IsUnit (1 - K) := by
  refine Matrix.mulVec_injective_iff_isUnit.1 ?_
  intro g g' hgg
  have hlin : (1 - K) *ᵥ (g - g') = 0 := by
    rw [Matrix.mulVec_sub, hgg, sub_self]
  have h1 : (g - g') - K *ᵥ (g - g') = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hlin; exact hlin
  have := neumann_bound hω hK h1 (C := 0) le_rfl (fun x => by simp)
  have h0 : g - g' = 0 := by
    funext x
    have := this x
    have hx := hω x
    simp only [mul_zero, div_zero] at this
    have : ‖(g - g') x‖ ≤ 0 := by
      by_contra hpos
      have : 0 < ‖(g - g') x‖ := lt_of_not_ge hpos
      nlinarith
    exact norm_le_zero_iff.1 this
  exact sub_eq_zero.1 h0

end Neumann

section Sup

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ}

/-- The four pointwise (weighted) bounds of `G_s f`: value, forward gradient (spacing at either
end of the bond) and Laplacian. -/
structure SupBdW (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (w : CTorus d L N₁ m₁ K → ℝ)
    (v : CTorus d L N₁ m₁ K → ℂ) (V : ℝ) : Prop where
  val : ∀ x ∈ G.Ω 1, w x * ‖v x‖ ≤ V
  fwd : ∀ x ∈ G.Ω 1, ∀ μ : Fin d, w x * (G.spacing x * ‖v (x + Pi.single μ 1) - v x‖) ≤ V
  fwd' : ∀ x ∈ G.Ω 1, ∀ μ : Fin d, x + Pi.single μ 1 ∈ G.Ω 1 →
    w x * (G.spacing (x + Pi.single μ 1) * ‖v (x + Pi.single μ 1) - v x‖) ≤ V
  lap : ∀ x ∈ G.Ω 1, w x * ((G.spacing x) ^ 2 * ‖∑ μ : Fin d, (2 * v x - v (x + Pi.single μ 1) -
    v (x - Pi.single μ 1))‖) ≤ V

/-- The cube solution `ũ_z` for the source `c_z g`. -/
noncomputable def cubeSolE (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (α : G.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) (g : G.Ω 1 → ℂ) :
    CTorus d L N₁ m₁ K → ℂ :=
  solExt G (cubeH G a ν α q)⁻¹ (cD G q *ᵥ g)

theorem zeroExt_of_mem' {ι : Type*} [DecidableEq ι] {Λ : Finset ι} {u : Λ → ℂ} {y : ι}
    (hy : y ∈ Λ) : zeroExt Λ u y = u ⟨y, hy⟩ := by
  simp [zeroExt, hy]

theorem cubeSolE_of_not_mem (q : ℕ × CTorus d L N₁ m₁ K) (g : G.Ω 1 → ℂ)
    {y : CTorus d L N₁ m₁ K} (hy : y ∉ G.Ω 1) : cubeSolE G a ν α q g y = 0 :=
  zeroExt_not_mem _ _ hy

/-- `G*_s g = ∑_z s_z χ_z ũ_z` pointwise on the whole torus (zero extension). -/
theorem Gstar_apply (s : ℕ × CTorus d L N₁ m₁ K → ℂ) (g : G.Ω 1 → ℂ)
    (y : CTorus d L N₁ m₁ K) :
    zeroExt (G.Ω 1) (Gstar G a ν α s *ᵥ g) y =
      ∑ q ∈ cubeIdx G, sProd G s q * (((chi G q y : ℝ) : ℂ) * cubeSolE G a ν α q g y) := by
  by_cases hy : y ∈ G.Ω 1
  · rw [zeroExt_of_mem' hy]
    unfold Gstar
    rw [Matrix.sum_mulVec, Finset.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, ← Matrix.mulVec_mulVec, chiD_mulVec,
      cubeG_mulVec]
    congr 2
    unfold cubeSolE solExt
    rw [zeroExt_of_mem' hy]
  · rw [zeroExt_not_mem _ _ hy]
    refine (Finset.sum_eq_zero fun q _ => ?_).symm
    rw [cubeSolE_of_not_mem q g hy]; simp

/-! ### The cut-off functions at the neighbours of a site -/

theorem chi_nbr_mem_unit (hG : CubeAligned G m₁) (hL : 2 ≤ L) {n : ℕ} (hn1 : 1 ≤ n) (hnK : n ≤ K)
    {x z : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (μ : Fin d)
    (hz : z = x ∨ z = x + Pi.single μ 1 ∨ z = x - Pi.single μ 1) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) : 0 ≤ chi G q z ∧ chi G q z ≤ 1 := by
  have hD := coverDenom_ge hG hL hn1 hnK hx μ hz
  have hq0 : (0 : ℝ) < (1 / 4 : ℝ) ^ d := by positivity
  have hDpos : 0 < coverDenom G z := lt_of_lt_of_le hq0 hD
  have hb0 := cubeBump_nonneg_of_mem G hq z
  have hbD : cubeBump m₁ q.1 q.2 z ≤ coverDenom G z := by
    have := Finset.single_le_sum
      (f := fun q : ℕ × CTorus d L N₁ m₁ K => cubeBump m₁ q.1 q.2 z)
      (fun q hq => cubeBump_nonneg_of_mem G hq z) hq
    exact this
  unfold chi
  exact ⟨div_nonneg hb0 hDpos.le, (div_le_one hDpos).2 hbD⟩

theorem chi_grad_real {δ : ℝ} {q : ℕ × CTorus d L N₁ m₁ K}
    (hsm : IsSmoothField G δ (chiField G q)) {y : CTorus d L N₁ m₁ K} (hy : y ∈ G.Ω 1)
    (μ : Fin d) :
    G.spacing y * |chi G q (y + Pi.single μ 1) - chi G q y| ≤ δ ∧
    G.spacing y * |chi G q (y - Pi.single μ 1) - chi G q y| ≤ δ := by
  obtain ⟨h1, h2⟩ := hsm.grad y hy μ
  have hsp := spacing_pos G (x := y)
  have e : ∀ z : CTorus d L N₁ m₁ K,
      chiField G q z - chiField G q y = fun _ => ((chi G q z - chi G q y : ℝ) : ℂ) := by
    intro z; funext i; simp [chiField]
  rw [e, vn_const_one, le_div_iff₀ hsp] at h1 h2
  exact ⟨by linarith, by linarith⟩

theorem chi_lap_real {δ : ℝ} {q : ℕ × CTorus d L N₁ m₁ K}
    (hsm : IsSmoothField G δ (chiField G q)) {y : CTorus d L N₁ m₁ K} (hy : y ∈ G.Ω 1) :
    (G.spacing y) ^ 2 * |∑ μ : Fin d, (chi G q (y + Pi.single μ 1) +
      chi G q (y - Pi.single μ 1) - 2 * chi G q y)| ≤ δ := by
  have h := hsm.lap y hy
  have hsp := spacing_pos G (x := y)
  have e : (fun i : Fin 1 => ∑ μ : Fin d, (chiField G q (y + Pi.single μ 1) i +
      chiField G q (y - Pi.single μ 1) i - 2 * chiField G q y i)) =
      fun _ => ((∑ μ : Fin d, (chi G q (y + Pi.single μ 1) + chi G q (y - Pi.single μ 1) -
        2 * chi G q y) : ℝ) : ℂ) := by
    funext i; simp [chiField]
  rw [e, vn_const_one, le_div_iff₀ (by positivity)] at h
  linarith

/-- The Leibniz rule for the Laplacian of a product. -/
theorem lap_prod_aux (c0 cp cm u0 up um : ℂ) :
    2 * (c0 * u0) - cp * up - cm * um = c0 * (2 * u0 - up - um) + u0 * (2 * c0 - cp - cm) -
      (cp - c0) * (up - u0) - (cm - c0) * (um - u0) := by ring

theorem lap_sum_aux {d : ℕ} (c0 u0 : ℂ) (cp cm up um : Fin d → ℂ) :
    ∑ μ : Fin d, (2 * (c0 * u0) - cp μ * up μ - cm μ * um μ) =
      c0 * ∑ μ : Fin d, (2 * u0 - up μ - um μ) + u0 * ∑ μ : Fin d, (2 * c0 - cp μ - cm μ) -
        ∑ μ : Fin d, ((cp μ - c0) * (up μ - u0) + (cm μ - c0) * (um μ - u0)) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun μ _ => by ring

/-- **The three bounds for one centre**: value, forward difference and Laplacian of the product
`χ_z ũ_z` at an interior point. -/
theorem perq_bounds (S : DGSetting G a ν) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G)
    {u : CTorus d L N₁ m₁ K → ℂ} (hux : ∀ y, y ∉ G.Ω 1 → u y = 0) {x : G.Ω 1} {V : ℝ}
    (hV : 0 ≤ V) (hst : StarBd G u x V) :
    ‖((chi G q x : ℝ) : ℂ) * u x‖ ≤ V ∧
    (∀ μ : Fin d, G.spacing (x : CTorus d L N₁ m₁ K) *
      ‖((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
        u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - ((chi G q x : ℝ) : ℂ) * u x‖ ≤
      (1 + Cchi d L) * V) ∧
    (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖∑ μ : Fin d, (2 * (((chi G q x : ℝ) : ℂ) * u x) -
      ((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
        u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
      ((chi G q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) : ℝ) : ℂ) *
        u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1))‖ ≤
      (1 + Cchi d L + d * Cchi d L * (1 + L)) * V := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hL2 : 2 ≤ L := by have := S.hL; omega
  have hM1 : (1 : ℝ) ≤ (L : ℝ) ^ m₁ := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ L))
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec x.2
  have hxΩ : (x : CTorus d L N₁ m₁ K) ∈ G.Ω 1 := x.2
  have hCc := Cchi_nonneg d L
  set δ : ℝ := Cchi d L / (L : ℝ) ^ m₁ with hδ
  have hδ0 : 0 ≤ δ := div_nonneg hCc (by positivity)
  have hδC : δ ≤ Cchi d L := div_le_self hCc hM1
  have hsm := chiField_isSmooth S.aligned S.cover_sep (by omega : 1 ≤ d) hL2 hq
  set ℓ : ℝ := G.spacing (x : CTorus d L N₁ m₁ K) with hℓ
  have hℓ0 : 0 < ℓ := spacing_pos G
  -- the data at `x`
  have hc0 := chi_nbr_mem_unit S.aligned hL2 hn1 hnK hxl (⟨0, hd0⟩ : Fin d) (Or.inl rfl) hq
  have hcp : ∀ μ : Fin d, 0 ≤ chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) ∧
      chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) ≤ 1 := fun μ =>
    chi_nbr_mem_unit S.aligned hL2 hn1 hnK hxl μ (Or.inr (Or.inl rfl)) hq
  have hcm : ∀ μ : Fin d, 0 ≤ chi G q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) ∧
      chi G q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) ≤ 1 := fun μ =>
    chi_nbr_mem_unit S.aligned hL2 hn1 hnK hxl μ (Or.inr (Or.inr rfl)) hq
  have hu0 : ‖u x‖ ≤ V := hst.val x hxΩ (by simp [G.pathDist_self hxΩ])
  -- values at the neighbours
  have hnbr : ∀ y : CTorus d L N₁ m₁ K, Adj (x : CTorus d L N₁ m₁ K) y → ‖u y‖ ≤ V := by
    intro y hadj
    by_cases hyΩ : y ∈ G.Ω 1
    · refine hst.val y hyΩ ?_
      refine (G.pathDist_le_bondCost hxΩ hyΩ hadj).trans ?_
      refine (ENNReal.ofReal_le_ofReal (G.bondCost_le_one hxΩ y)).trans ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd0
      linarith
    · rw [hux y hyΩ, norm_zero]; exact hV
  have hup : ∀ μ : Fin d, ‖u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1)‖ ≤ V := fun μ =>
    hnbr _ ⟨μ, Or.inl rfl⟩
  have hum : ∀ μ : Fin d, ‖u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1)‖ ≤ V := fun μ =>
    hnbr _ ⟨μ, Or.inr (by simp)⟩
  have hgr := fun μ => chi_grad_real hsm hxΩ μ
  have hlapχ := chi_lap_real hsm hxΩ
  have hnorm : ∀ (c : ℝ) (z : ℂ), ‖(c : ℂ) * z‖ = |c| * ‖z‖ := fun c z => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine ⟨?_, fun μ => ?_, ?_⟩
  · rw [hnorm, abs_of_nonneg hc0.1]
    calc chi G q x * ‖u x‖ ≤ 1 * V := mul_le_mul hc0.2 hu0 (norm_nonneg _) zero_le_one
      _ = V := one_mul V
  · have e : ((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
        u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - ((chi G q x : ℝ) : ℂ) * u x =
        ((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
          (u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - u x) +
        ((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - chi G q x : ℝ) : ℂ) * u x := by
      push_cast; ring
    rw [e]
    have h1 := hst.fwd μ
    have h2 := (hgr μ).1
    have hc := hcp μ
    calc ℓ * ‖((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
          (u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - u x) +
          ((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - chi G q x : ℝ) : ℂ) * u x‖
        ≤ ℓ * (‖((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
          (u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - u x)‖ +
          ‖((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - chi G q x : ℝ) : ℂ) * u x‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hℓ0.le
      _ = |chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1)| *
            (ℓ * ‖u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - u x‖) +
          (ℓ * |chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - chi G q x|) * ‖u x‖ := by
          rw [hnorm, hnorm]; ring
      _ ≤ 1 * V + δ * V := by
          rw [abs_of_nonneg hc.1]
          have a1 : chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) *
              (ℓ * ‖u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - u x‖) ≤ 1 * V :=
            mul_le_mul hc.2 h1 (by positivity) zero_le_one
          have a2 : (ℓ * |chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - chi G q x|) *
              ‖u x‖ ≤ δ * V := mul_le_mul h2 hu0 (norm_nonneg _) hδ0
          linarith
      _ ≤ (1 + Cchi d L) * V := by nlinarith
  · -- Laplacian
    set c0 : ℂ := ((chi G q x : ℝ) : ℂ) with hc0def
    set cp : Fin d → ℂ := fun μ => ((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ)
      with hcpdef
    set cm : Fin d → ℂ := fun μ => ((chi G q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) : ℝ) : ℂ)
      with hcmdef
    set up : Fin d → ℂ := fun μ => u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) with hupdef
    set um : Fin d → ℂ := fun μ => u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) with humdef
    have e := lap_sum_aux c0 (u x) cp cm up um
    show ℓ ^ 2 * ‖∑ μ : Fin d, (2 * (c0 * u x) - cp μ * up μ - cm μ * um μ)‖ ≤ _
    rw [e]
    have hΔu := hst.lap
    have hr : ∑ μ : Fin d, (2 * c0 - cp μ - cm μ) =
        -(((∑ μ : Fin d, (chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) +
          chi G q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) - 2 * chi G q x) : ℝ)) : ℂ) := by
      push_cast
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun μ _ => by simp only [hc0def, hcpdef, hcmdef]; ring
    set r : ℝ := ∑ μ : Fin d, (chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) +
          chi G q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) - 2 * chi G q x) with hrdef
    rw [hr]
    have hdiff : ‖∑ μ : Fin d, ((cp μ - c0) * (up μ - u x) + (cm μ - c0) * (um μ - u x))‖ * ℓ ^ 2 ≤
        d * (δ * V + δ * (L * V)) := by
      calc ‖∑ μ : Fin d, ((cp μ - c0) * (up μ - u x) + (cm μ - c0) * (um μ - u x))‖ * ℓ ^ 2
          ≤ (∑ μ : Fin d, ‖(cp μ - c0) * (up μ - u x) + (cm μ - c0) * (um μ - u x)‖) * ℓ ^ 2 :=
            mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
        _ = ∑ μ : Fin d, ‖(cp μ - c0) * (up μ - u x) + (cm μ - c0) * (um μ - u x)‖ * ℓ ^ 2 := by
            rw [Finset.sum_mul]
        _ ≤ ∑ _μ : Fin d, (δ * V + δ * (L * V)) := by
            refine Finset.sum_le_sum fun μ _ => ?_
            have h1 : ‖(cp μ - c0) * (up μ - u x)‖ * ℓ ^ 2 ≤ δ * V := by
              have : (cp μ - c0) = (((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
                chi G q x : ℝ)) : ℂ) := by simp [hcpdef, hc0def]
              rw [norm_mul, this, Complex.norm_real, Real.norm_eq_abs]
              have := (hgr μ).1
              have h3 := hst.fwd μ
              calc |chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - chi G q x| *
                    ‖up μ - u x‖ * ℓ ^ 2
                  = (ℓ * |chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - chi G q x|) *
                    (ℓ * ‖up μ - u x‖) := by ring
                _ ≤ δ * V := mul_le_mul this h3 (by positivity) hδ0
            have h2 : ‖(cm μ - c0) * (um μ - u x)‖ * ℓ ^ 2 ≤ δ * (L * V) := by
              have : (cm μ - c0) = (((chi G q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) -
                chi G q x : ℝ)) : ℂ) := by simp [hcmdef, hc0def]
              rw [norm_mul, this, Complex.norm_real, Real.norm_eq_abs]
              have := (hgr μ).2
              have h3 := hst.bwd μ
              calc |chi G q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) - chi G q x| *
                    ‖um μ - u x‖ * ℓ ^ 2
                  = (ℓ * |chi G q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) - chi G q x|) *
                    (ℓ * ‖um μ - u x‖) := by ring
                _ ≤ δ * (L * V) := mul_le_mul this h3 (by positivity) hδ0
            calc ‖(cp μ - c0) * (up μ - u x) + (cm μ - c0) * (um μ - u x)‖ * ℓ ^ 2
                ≤ (‖(cp μ - c0) * (up μ - u x)‖ + ‖(cm μ - c0) * (um μ - u x)‖) * ℓ ^ 2 :=
                  mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
              _ = ‖(cp μ - c0) * (up μ - u x)‖ * ℓ ^ 2 + ‖(cm μ - c0) * (um μ - u x)‖ * ℓ ^ 2 := by
                  ring
              _ ≤ δ * V + δ * (L * V) := add_le_add h1 h2
        _ = d * (δ * V + δ * (L * V)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hA : ℓ ^ 2 * ‖c0 * ∑ μ : Fin d, (2 * u x - up μ - um μ)‖ ≤ V := by
      rw [norm_mul, hc0def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0.1]
      calc ℓ ^ 2 * (chi G q x * ‖∑ μ : Fin d, (2 * u x - up μ - um μ)‖)
          = chi G q x * (ℓ ^ 2 * ‖∑ μ : Fin d, (2 * u x - up μ - um μ)‖) := by ring
        _ ≤ 1 * V := mul_le_mul hc0.2 hΔu (by positivity) zero_le_one
        _ = V := one_mul V
    have hB : ℓ ^ 2 * ‖u x * (-((r : ℝ) : ℂ))‖ ≤ δ * V := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      have hr' : ℓ ^ 2 * |r| ≤ δ := by
        have := hlapχ
        rw [hrdef]
        exact this
      calc ℓ ^ 2 * (‖u x‖ * |r|) = ‖u x‖ * (ℓ ^ 2 * |r|) := by ring
        _ ≤ V * δ := mul_le_mul hu0 hr' (by positivity) hV
        _ = δ * V := by ring
    calc ℓ ^ 2 * ‖c0 * ∑ μ : Fin d, (2 * u x - up μ - um μ) + u x * (-((r : ℝ) : ℂ)) -
          ∑ μ : Fin d, ((cp μ - c0) * (up μ - u x) + (cm μ - c0) * (um μ - u x))‖
        ≤ ℓ ^ 2 * (‖c0 * ∑ μ : Fin d, (2 * u x - up μ - um μ)‖ + ‖u x * (-((r : ℝ) : ℂ))‖ +
          ‖∑ μ : Fin d, ((cp μ - c0) * (up μ - u x) + (cm μ - c0) * (um μ - u x))‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc _ ≤ ‖c0 * ∑ μ : Fin d, (2 * u x - up μ - um μ) + u x * (-((r : ℝ) : ℂ))‖ +
                ‖∑ μ : Fin d, ((cp μ - c0) * (up μ - u x) + (cm μ - c0) * (um μ - u x))‖ :=
                norm_sub_le _ _
            _ ≤ _ := by
                have := norm_add_le (c0 * ∑ μ : Fin d, (2 * u x - up μ - um μ))
                  (u x * (-((r : ℝ) : ℂ)))
                linarith
      _ = ℓ ^ 2 * ‖c0 * ∑ μ : Fin d, (2 * u x - up μ - um μ)‖ +
          ℓ ^ 2 * ‖u x * (-((r : ℝ) : ℂ))‖ +
          ‖∑ μ : Fin d, ((cp μ - c0) * (up μ - u x) + (cm μ - c0) * (um μ - u x))‖ * ℓ ^ 2 := by
          ring
      _ ≤ V + δ * V + d * (δ * V + δ * (L * V)) := add_le_add (add_le_add hA hB) hdiff
      _ ≤ (1 + Cchi d L + d * Cchi d L * (1 + L)) * V := by
          have hd1 : (0 : ℝ) ≤ d := by positivity
          have h1 : δ * V ≤ Cchi d L * V := mul_le_mul_of_nonneg_right hδC hV
          have h2 : d * (δ * V + δ * (L * V)) ≤ d * (Cchi d L * V + Cchi d L * (L * V)) := by
            apply mul_le_mul_of_nonneg_left _ hd1
            have h3 : δ * (L * V) ≤ Cchi d L * (L * V) :=
              mul_le_mul_of_nonneg_right hδC (by positivity)
            linarith
          nlinarith

end Sup

end Balaban.Localization
