/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledLocal
public import Balaban.Localization.NC3

/-!
# (DG6): closeness of `G_s(A)` to `G_1(A) = G_D(A)` away from the parameters

* `dirichlet_block_bounds`: block bounds of the global Dirichlet Green's function (landed `prop48`,
  `laplacian_cut_bound` with the empty cut), in the form of `CubeBlockBounds`;
* `dirichlet_weighted`: their weighted form (`weighted_sum_bound`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

section Dirichlet

variable {d L : ℕ} [NeZero L]

theorem dirichlet_block_bounds (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧ ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)
      {a : ℕ → ℝ} {ν : ℝ}, 0 ≤ ν → ν * ((L : ℝ) ^ k) ^ 2 ≤ 1 → IsAdmissibleWeights k a →
      ∀ {α : G.Ω 1 → ℂ}, (∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) →
      1 ≤ ϱ → (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) →
      ∀ {j' : ℕ} {y' : Torus d (N₀ * L ^ k)}, 1 ≤ j' → j' ≤ k → y' ∈ G.layer j' →
      ∀ (f : G.Ω 1 → ℂ),
      (∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y') →
      ∀ {Mf : ℝ}, 0 ≤ Mf → (∀ z, ‖f z‖ ≤ Mf) →
      (∀ {x : Torus d (N₀ * L ^ k)}, x ∈ G.Ω 1 →
        ‖solExt G (dirichletOperator G a ν α)⁻¹ f x‖ ≤
          Kd * decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf)) ∧
      (∀ {x : Torus d (N₀ * L ^ k)}, x ∈ G.Ω 1 → ∀ μ : Fin d,
        G.spacing x * ‖solExt G (dirichletOperator G a ν α)⁻¹ f (x + Pi.single μ 1) -
          solExt G (dirichletOperator G a ν α)⁻¹ f x‖ ≤
          Kd * decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf)) ∧
      (∀ {x : Torus d (N₀ * L ^ k)}, x ∈ G.Ω 1 →
        (G.spacing x) ^ 2 * ‖∑ μ : Fin d, (2 * solExt G (dirichletOperator G a ν α)⁻¹ f x -
          solExt G (dirichletOperator G a ν α)⁻¹ f (x + Pi.single μ 1) -
          solExt G (dirichletOperator G a ν α)⁻¹ f (x - Pi.single μ 1))‖ ≤
          Kd * decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf)) := by
  obtain ⟨K2, hK2, hP⟩ := prop48 (d := d) (L := L) hd hL 1 zero_le_one
  have hε := agmonRate_pos (d := d) (by omega)
  have hE : 0 ≤ Real.exp (agmonRate d * d) * (1 + 4 * K2) := by positivity
  refine ⟨K2 + Real.exp (agmonRate d * d) * (1 + 4 * K2), by positivity, ?_⟩
  intro k N₀ _ ϱ G a ν hν0 hν1 ha α hα hϱ hsep j' y' hj'1 hj'k hy' f hsupp Mf hMf0 hMf
  have hd0 : 0 < d := by omega
  have hF0 : 0 ≤ (L : ℝ) ^ (2 * j') * Mf := by positivity
  let S : PtSetting G 1 :=
    { a := a, ν := ν, α := α, f := f, j' := j', y' := y', hd := hd, hL := hL, hν0 := hν0,
      hν1 := hν1, ha := ha, hα := hα, hϱ := hϱ, hsep := hsep, hj'1 := hj'1, hj'k := hj'k,
      hy' := hy', hsupp := hsupp }
  have hU : ∀ {x : Torus d (N₀ * L ^ k)}, x ∈ G.Ω 1 →
      S.U x ≤ K2 * decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hP G S hMf0 hMf hx
    by_cases ht : G.pathDist x y' = ⊤
    · have h3 : S.U x = 0 := h2 ht
      rw [h3]
      exact mul_nonneg (mul_nonneg hK2 (decay_nonneg _ _)) hF0
    · have h3 := h1 ht
      simpa [decay, ht] using h3
  have hval : ∀ {x : Torus d (N₀ * L ^ k)}, x ∈ G.Ω 1 →
      ‖solExt G (dirichletOperator G a ν α)⁻¹ f x‖ ≤
        K2 * decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf) := by
    intro x hx
    exact (S.norm_ut_le_U x).trans (hU hx)
  have hK2le : K2 ≤ K2 + Real.exp (agmonRate d * d) * (1 + 4 * K2) := by linarith
  have hDec := fun x => decay_nonneg (agmonRate d / 2) (G.pathDist x y')
  refine ⟨fun {x} hx => (hval hx).trans ?_, fun {x} hx μ => ?_, fun {x} hx => ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK2le (hDec x)) hF0
  · have h1 := PtSetting.spacing_mul_diff_le_U S x μ
    refine (h1.trans (hU hx)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK2le (hDec x)) hF0
  · have hlap := laplacian_cut_bound (cutAligned_empty G) hd0 hν0 hν1 ha α hα hj'1 hj'k hy' f hsupp
      hMf0 hMf hx (fun μ => ⟨Finset.notMem_empty _, Finset.notMem_empty _⟩) (V := K2 * ((L : ℝ) ^ (2 * j') * Mf)) (by positivity)
      (by
        intro q' hq'
        obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hx
        have hq'l : q' ∈ G.layer (G.layerIndex x) := (G.mem_layer_iff hj1 hjk hq').2 hxl
        have hq'Ω : q' ∈ G.Ω 1 := G.layer_subset hj1 hjk hq'l
        have := hval hq'Ω
        simp only [cutOperator_empty]
        exact this.trans (le_of_eq (by ring)))
    simp only [cutOperator_empty] at hlap
    refine hlap.trans ?_
    have h0 := mul_nonneg (mul_nonneg hK2 (hDec x)) hF0
    nlinarith [h0]

end Dirichlet

section Weighted

variable {d L : ℕ} [NeZero L]

/-- The weighted form of the block bounds of the global Dirichlet Green's function. -/
theorem dirichlet_weighted (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α →
      ∀ {w : CTorus d L N₁ m₁ K → ℝ}, IsWeight G (gammaW d) w →
      ∀ (g : G.Ω 1 → ℂ) {C : ℝ}, 0 ≤ C →
      (∀ x : G.Ω 1, w x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖g x‖ ≤ C) →
      (∀ {x : CTorus d L N₁ m₁ K}, x ∈ G.Ω 1 →
        w x * ‖solExt G (dirichletOperator G a ν α)⁻¹ g x‖ ≤ Bd * C) ∧
      (∀ {x : CTorus d L N₁ m₁ K}, x ∈ G.Ω 1 → ∀ μ : Fin d,
        w x * (G.spacing x * ‖solExt G (dirichletOperator G a ν α)⁻¹ g (x + Pi.single μ 1) -
          solExt G (dirichletOperator G a ν α)⁻¹ g x‖) ≤ Bd * C) ∧
      (∀ {x : CTorus d L N₁ m₁ K}, x ∈ G.Ω 1 →
        w x * ((G.spacing x) ^ 2 * ‖∑ μ : Fin d, (2 * solExt G (dirichletOperator G a ν α)⁻¹ g x -
          solExt G (dirichletOperator G a ν α)⁻¹ g (x + Pi.single μ 1) -
          solExt G (dirichletOperator G a ν α)⁻¹ g (x - Pi.single μ 1))‖) ≤ Bd * C) := by
  obtain ⟨Kd, hKd, hB⟩ := dirichlet_block_bounds (d := d) (L := L) hd hL
  refine ⟨Kd * Real.exp (2 * gammaW d * d) * countConst d L (agmonRate d / 2 - gammaW d), ?_, ?_⟩
  · have : 0 ≤ countConst d L (agmonRate d / 2 - gammaW d) := tsum_nonneg fun m => by positivity
    positivity
  intro N₁ m₁ K _ ϱ G a ν S α hα w hw g C hC hgC
  have hd0 : 0 < d := by omega
  have hγ0 := gammaW_nonneg hd0
  have hγlt := gammaW_lt hd0
  have hρ := S.one_lt_rho
  have hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) := S.sep_pow (le_of_eq rfl)
  have hΛ : BlockAligned G (Finset.univ : Finset (CTorus d L N₁ m₁ K)) :=
    fun j hj1 hjk x x' _ _ => by simp
  have hpieces := fun {j'} {y'} (hj'1 : 1 ≤ j') (hj'k : j' ≤ K) (hy' : y' ∈ G.layer j')
      (f : G.Ω 1 → ℂ) (hs : ∀ z : G.Ω 1, f z ≠ 0 →
        jBlock d L (N₁ * L ^ m₁) K j' z = jBlock d L (N₁ * L ^ m₁) K j' y') {Mf : ℝ} (hMf0 : 0 ≤ Mf)
      (hMf : ∀ z, ‖f z‖ ≤ Mf) =>
    hB G S.mass S.massLe S.weights hα hρ.le hsep hj'1 hj'k hy' f hs hMf0 hMf
  refine ⟨fun {x} hx => ?_, fun {x} hx μ => ?_, fun {x} hx => ?_⟩
  · have := weighted_sum_bound (G := G) (γ := gammaW d) (γ0 := agmonRate d / 2) (Kc := Kd) (s := 1)
      hγ0 hγlt hKd zero_le_one hw (dirichletOperator G a ν α)⁻¹
      (evalLM (n := (N₁ * L ^ m₁) * L ^ K) x) hx hΛ hρ S.sep_weight
      (fun {j'} {y'} hj'1 hj'k hy' _ g' hs {Mf} hMf0 hMf => by
        have := (hpieces hj'1 hj'k hy' g' hs hMf0 hMf).1 hx
        simpa [evalLM_apply] using this)
      g (fun _ _ => Finset.mem_univ _) hC hgC
    simpa [evalLM_apply] using this
  · have := weighted_sum_bound (G := G) (γ := gammaW d) (γ0 := agmonRate d / 2) (Kc := Kd)
      (s := G.spacing x) hγ0 hγlt hKd (spacing_pos G).le hw (dirichletOperator G a ν α)⁻¹
      (gradLM (n := (N₁ * L ^ m₁) * L ^ K) x μ) hx hΛ hρ S.sep_weight
      (fun {j'} {y'} hj'1 hj'k hy' _ g' hs {Mf} hMf0 hMf => by
        have := (hpieces hj'1 hj'k hy' g' hs hMf0 hMf).2.1 hx μ
        simpa [gradLM_apply] using this)
      g (fun _ _ => Finset.mem_univ _) hC hgC
    simpa [gradLM_apply] using this
  · have := weighted_sum_bound (G := G) (γ := gammaW d) (γ0 := agmonRate d / 2) (Kc := Kd)
      (s := G.spacing x ^ 2) hγ0 hγlt hKd (by have := spacing_pos G (x := x); positivity) hw
      (dirichletOperator G a ν α)⁻¹ (lapLM (n := (N₁ * L ^ m₁) * L ^ K) x) hx hΛ hρ S.sep_weight
      (fun {j'} {y'} hj'1 hj'k hy' _ g' hs {Mf} hMf0 hMf => by
        have := (hpieces hj'1 hj'k hy' g' hs hMf0 hMf).2.2 hx
        simpa [lapLM_apply] using this)
      g (fun _ _ => Finset.mem_univ _) hC hgC
    simpa [lapLM_apply] using this

end Weighted

section Close

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ}

/-- The distance from a site to a set of sites in the path metric. -/
noncomputable def siteSetDist (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (W : Finset (CTorus d L N₁ m₁ K))
    (x : CTorus d L N₁ m₁ K) : ENNReal := ⨅ w ∈ W, G.pathDist x w

theorem setDist_triangle (W : Finset (CTorus d L N₁ m₁ K)) (x y : CTorus d L N₁ m₁ K) :
    siteSetDist G W x ≤ G.pathDist x y + siteSetDist G W y := by
  unfold siteSetDist
  rw [ENNReal.add_iInf]
  refine le_iInf fun w => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun hw => ?_
  exact (iInf₂_le w hw).trans (G.pathDist_triangle x y w)

theorem setDist_of_mem (W : Finset (CTorus d L N₁ m₁ K)) {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ W) (hxΩ : x ∈ G.Ω 1) : siteSetDist G W x = 0 :=
  le_antisymm ((iInf₂_le x hx).trans (by rw [G.pathDist_self hxΩ])) bot_le

theorem setDist_adj_le (W : Finset (CTorus d L N₁ m₁ K)) {x y : CTorus d L N₁ m₁ K}
    (hx : x ∈ G.Ω 1) (hy : y ∈ G.Ω 1) (hyW : y ∈ W) (hadj : Adj x y) :
    siteSetDist G W x ≤ ENNReal.ofReal 1 :=
  (iInf₂_le y hyW).trans ((G.pathDist_le_bondCost hx hy hadj).trans
    (ENNReal.ofReal_le_ofReal (G.bondCost_le_one hx y)))

/-- A function of a "distance" `D` with the triangle inequality is a weight. -/
theorem isWeight_of_dist (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {γ T : ℝ} (hγ : 0 ≤ γ)
    (hT : 1 ≤ T) (D : CTorus d L N₁ m₁ K → ENNReal)
    (htri : ∀ x y, D x ≤ G.pathDist x y + D y) :
    IsWeight G γ (fun x => if D x = ⊤ then T else Real.exp (γ * (D x).toReal)) := by
  have hT0 : 0 ≤ T := by linarith
  have hnn : ∀ y, 0 ≤ (if D y = ⊤ then T else Real.exp (γ * (D y).toReal)) := fun y => by
    split_ifs
    · exact hT0
    · exact (Real.exp_pos _).le
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · show 1 ≤ if D x = ⊤ then T else Real.exp (γ * (D x).toReal)
    split_ifs
    · exact hT
    · exact Real.one_le_exp (by positivity)
  · by_cases hxy : G.pathDist x y = ⊤
    · simp only [hxy, decay_top, mul_zero]
      exact hnn y
    · have h1 := htri x y
      have h2 := htri y x
      rw [G.pathDist_comm y x] at h2
      by_cases hy : D y = ⊤
      · have hx : D x = ⊤ := by
          by_contra hx
          have : D y ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hxy, hx⟩) h2
          exact this hy
        simp only [hx, hy, ↓reduceIte]
        calc T * decay γ (G.pathDist x y) ≤ T * 1 :=
              mul_le_mul_of_nonneg_left (decay_le_one hγ _) hT0
          _ = T := mul_one T
      · have hx : D x ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hxy, hy⟩) h1
        simp only [hx, hy, ↓reduceIte]
        rw [decay_of_ne_top hxy, ← Real.exp_add]
        apply Real.exp_le_exp.2
        have h3 : (D x).toReal ≤ (G.pathDist x y).toReal + (D y).toReal := by
          rw [← ENNReal.toReal_add hxy hy]
          exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hxy, hy⟩) h1
        nlinarith

theorem sProd_one (q : ℕ × CTorus d L N₁ m₁ K) : sProd G (fun _ => (1 : ℂ)) q = 1 := by
  simp [sProd]

/-- **The algebraic identity behind (DG6)**:
`(G_s - G_D) f = (G*_s - G*_1) g + G_D (𝒦_s - 𝒦_1) g`, `g = (1 - 𝒦_s)⁻¹ f`. -/
theorem Gs_sub_Gd (S : DGSetting G a ν) (hα : AdmPot G α) {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hU : IsUnit (1 - Kcal G a ν α s)) (f : G.Ω 1 → ℂ) :
    Gs G a ν α s *ᵥ f - (dirichletOperator G a ν α)⁻¹ *ᵥ f =
      (Gstar G a ν α s - Gstar G a ν α (fun _ => 1)) *ᵥ ((1 - Kcal G a ν α s)⁻¹ *ᵥ f) +
      (dirichletOperator G a ν α)⁻¹ *ᵥ
        ((Kcal G a ν α s - Kcal G a ν α (fun _ => 1)) *ᵥ ((1 - Kcal G a ν α s)⁻¹ *ᵥ f)) := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hHU := dirichletOperator_isUnit G hd0 S.mass S.weights α hα
  have hdetH := (Matrix.isUnit_iff_isUnit_det _).1 hHU
  have hdetK := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hpar := parametrix S hα
  set Gd := (dirichletOperator G a ν α)⁻¹ with hGd
  have h1 : Gstar G a ν α (fun _ => 1) = Gd * (1 - Kcal G a ν α (fun _ => 1)) := by
    rw [← hpar, ← Matrix.mul_assoc, hGd, Matrix.nonsing_inv_mul _ hdetH, Matrix.one_mul]
  set g := (1 - Kcal G a ν α s)⁻¹ *ᵥ f with hg
  have hg1 : (1 - Kcal G a ν α s) *ᵥ g = f := by
    rw [hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetK, Matrix.one_mulVec]
  have e : Gs G a ν α s *ᵥ f = Gstar G a ν α s *ᵥ g := by
    rw [hg, Gs, ← Matrix.mulVec_mulVec]
  have hA1g : Gstar G a ν α (fun _ => 1) *ᵥ g =
      Gd *ᵥ (g - Kcal G a ν α (fun _ => 1) *ᵥ g) := by
    rw [h1, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hf : f = g - Kcal G a ν α s *ᵥ g := by
    rw [← hg1, Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [e, Matrix.sub_mulVec, Matrix.sub_mulVec, hA1g, Matrix.mulVec_sub, Matrix.mulVec_sub]
  conv_lhs => rw [hf, Matrix.mulVec_sub]
  abel

theorem cubeSolE_eq_zero_of_not_mem_box (S : DGSetting G a ν) (hα : AdmPot G α)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) (g : G.Ω 1 → ℂ)
    {y : CTorus d L N₁ m₁ K} (hy : y ∉ intBox q) : cubeSolE G a ν α q g y = 0 := by
  by_cases hyΩ : y ∈ G.Ω 1
  · have h := cubeG_supp S hα hq g ⟨y, hyΩ⟩ hy
    rw [cubeG_mulVec] at h
    unfold cubeSolE solExt
    rw [zeroExt_of_mem' hyΩ]
    exact h
  · exact cubeSolE_of_not_mem q g hyΩ

/-- `(G*_s - G*_1) g` vanishes off `W`. -/
theorem Gstar_diff_zero (S : DGSetting G a ν) (hα : AdmPot G α)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {W : Finset (CTorus d L N₁ m₁ K)}
    (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) (g : G.Ω 1 → ℂ)
    {y : CTorus d L N₁ m₁ K} (hy : y ∉ W) :
    zeroExt (G.Ω 1) (Gstar G a ν α s *ᵥ g) y -
      zeroExt (G.Ω 1) (Gstar G a ν α (fun _ => 1) *ᵥ g) y = 0 := by
  rw [Gstar_apply, Gstar_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun z hz => ?_
  by_cases hc : sProd G s z = 1
  · rw [hc, sProd_one]; ring
  · have hb : y ∉ intBox z := fun h => hy (hW z hz hc h)
    rw [cubeSolE_eq_zero_of_not_mem_box S hα hz g hb]; simp

/-- `(𝒦_s - 𝒦_1) g` vanishes off `W`. -/
theorem Kcal_diff_zero (S : DGSetting G a ν)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {W : Finset (CTorus d L N₁ m₁ K)}
    (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) (g : G.Ω 1 → ℂ) {x : G.Ω 1}
    (hx : (x : CTorus d L N₁ m₁ K) ∉ W) :
    ((Kcal G a ν α s - Kcal G a ν α (fun _ => 1)) *ᵥ g) x = 0 := by
  rw [Matrix.sub_mulVec, Pi.sub_apply]
  unfold Kcal
  rw [Matrix.sum_mulVec, Matrix.sum_mulVec, Finset.sum_apply, Finset.sum_apply,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun z hz => ?_
  by_cases hc : sProd G s z = 1
  · rw [hc, sProd_one]; ring
  · have hb : (x : CTorus d L N₁ m₁ K) ∉ intBox z := fun h => hx (hW z hz hc h)
    have := rowSupp_Kz_cubeG (α := α) S hz g x hb
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, this]
    simp

theorem zeroExt_sub' {ι : Type*} [DecidableEq ι] (Λ : Finset ι) (u v : Λ → ℂ) (y : ι) :
    zeroExt Λ (u - v) y = zeroExt Λ u y - zeroExt Λ v y := by
  by_cases hy : y ∈ Λ <;> simp [zeroExt, hy]

theorem zeroExt_add' {ι : Type*} [DecidableEq ι] (Λ : Finset ι) (u v : Λ → ℂ) (y : ι) :
    zeroExt Λ (u + v) y = zeroExt Λ u y + zeroExt Λ v y := by
  by_cases hy : y ∈ Λ <;> simp [zeroExt, hy]

/-- At `s ≡ 1` with `1 - 𝒦_1` invertible, `G_1 = G_D`. -/
theorem Gs_one_of_unit (S : DGSetting G a ν) (hα : AdmPot G α)
    (hU : IsUnit (1 - Kcal G a ν α (fun _ => 1))) :
    Gs G a ν α (fun _ => 1) = (dirichletOperator G a ν α)⁻¹ := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hdetK := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hpar := parametrix S hα
  have h1 : dirichletOperator G a ν α * Gs G a ν α (fun _ => 1) = 1 := by
    unfold Gs
    rw [← Matrix.mul_assoc, hpar, Matrix.mul_nonsing_inv _ hdetK]
  exact (Matrix.inv_eq_right_inv h1).symm

/-- The estimate of one observable of `G_s f - G_D f = A + B` (see `dg6`): `A` is supported in
`W ∩ Ω₁` (so it only matters at distance `≤ 1` from `W`), `B` obeys the weighted bound. -/
theorem dg6_core {γ T1 Mb c : ℝ} (hγ : 0 ≤ γ) (hc : 0 ≤ c) (hT1 : 0 ≤ T1)
    (W : Finset (CTorus d L N₁ m₁ K)) (o : (CTorus d L N₁ m₁ K → ℂ) →ₗ[ℂ] ℂ)
    (A B Δ : CTorus d L N₁ m₁ K → ℂ) (hΔ : ∀ y, Δ y = A y + B y)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.Ω 1) (pts : Finset (CTorus d L N₁ m₁ K))
    (hpts : ∀ p ∈ pts, p = x ∨ Adj x p)
    (hvan : (∀ p ∈ pts, A p = 0) → o A = 0)
    (hAW : ∀ p ∈ pts, A p ≠ 0 → p ∈ W ∧ p ∈ G.Ω 1)
    (hA : c * ‖o A‖ ≤ T1)
    (hB : ∀ T : ℝ, 1 ≤ T → (if siteSetDist G W x = ⊤ then T else
      Real.exp (γ * (siteSetDist G W x).toReal)) * (c * ‖o B‖) ≤ Mb) :
    c * ‖o Δ‖ ≤ (Real.exp γ * T1 + Mb) * decay γ (siteSetDist G W x) := by
  have hΔ' : Δ = A + B := funext hΔ
  have hoΔ : o Δ = o A + o B := by rw [hΔ', map_add]
  have hdec := decay_nonneg γ (siteSetDist G W x)
  have hBd : c * ‖o B‖ ≤ Mb * decay γ (siteSetDist G W x) :=
    decay_of_dist_weights (mul_nonneg hc (norm_nonneg _)) _ hB
  have hAd : c * ‖o A‖ ≤ Real.exp γ * T1 * decay γ (siteSetDist G W x) := by
    by_cases hA0 : o A = 0
    · rw [hA0, norm_zero, mul_zero]; positivity
    · have hex : ∃ p ∈ pts, A p ≠ 0 := by
        by_contra hne
        push Not at hne
        exact hA0 (hvan hne)
      obtain ⟨p, hp, hAp⟩ := hex
      obtain ⟨hpW, hpΩ⟩ := hAW p hp hAp
      have hD : siteSetDist G W x ≤ ENNReal.ofReal 1 := by
        rcases hpts p hp with rfl | hadj
        · rw [setDist_of_mem W hpW hpΩ]; exact bot_le
        · exact setDist_adj_le W hx hpΩ hpW hadj
      have h1 := decay_ofReal_ge hγ zero_le_one hD
      have h2 : T1 ≤ Real.exp γ * T1 * decay γ (siteSetDist G W x) := by
        have hE : Real.exp γ * Real.exp (-(γ * 1)) = 1 := by rw [← Real.exp_add]; simp
        calc T1 = T1 * (Real.exp γ * Real.exp (-(γ * 1))) := by rw [hE, mul_one]
          _ ≤ T1 * (Real.exp γ * decay γ (siteSetDist G W x)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le) hT1
          _ = Real.exp γ * T1 * decay γ (siteSetDist G W x) := by ring
      exact hA.trans h2
  rw [hoΔ]
  calc c * ‖o A + o B‖ ≤ c * (‖o A‖ + ‖o B‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hc
    _ = c * ‖o A‖ + c * ‖o B‖ := by ring
    _ ≤ Real.exp γ * T1 * decay γ (siteSetDist G W x) + Mb * decay γ (siteSetDist G W x) :=
        add_le_add hAd hBd
    _ = _ := by ring

/-- `G_s(A) f - G_D(A) f` on the whole torus (zero extensions). -/
noncomputable def Gdiff (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (α : G.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ K → ℂ) (f : G.Ω 1 → ℂ)
    (y : CTorus d L N₁ m₁ K) : ℂ :=
  zeroExt (G.Ω 1) (Gs G a ν α s *ᵥ f) y - zeroExt (G.Ω 1) ((dirichletOperator G a ν α)⁻¹ *ᵥ f) y

/-- **(DG6), closeness.**  If every centre with `s_z ≠ 1` has its interaction cube in `W`, then
`G_s(A) f - G_D(A) f` and its differences decay like `e^{-γ_w d(x, W)}`. -/
theorem dg6 (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ cstar BG : ℝ, 0 ≤ cstar ∧ 0 ≤ BG ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {κ : ℝ}, 0 ≤ κ →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : ℕ × CTorus d L N₁ m₁ K → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ {W : Finset (CTorus d L N₁ m₁ K)},
      (∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) →
      ∀ (f : G.Ω 1 → ℂ) {C : ℝ}, 0 ≤ C →
      (∀ x : G.Ω 1, (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ C) →
      ∀ x ∈ G.Ω 1,
      ‖Gdiff G a ν α s f x‖ ≤ BG * Real.exp (N0 d L * κ) * decay (gammaW d) (siteSetDist G W x) * C ∧
      (∀ μ : Fin d, G.spacing x * ‖Gdiff G a ν α s f (x + Pi.single μ 1) -
        Gdiff G a ν α s f x‖ ≤
        BG * Real.exp (N0 d L * κ) * decay (gammaW d) (siteSetDist G W x) * C) ∧
      (G.spacing x) ^ 2 * ‖∑ μ : Fin d, (2 * Gdiff G a ν α s f x -
        Gdiff G a ν α s f (x + Pi.single μ 1) - Gdiff G a ν α s f (x - Pi.single μ 1))‖ ≤
        BG * Real.exp (N0 d L * κ) * decay (gammaW d) (siteSetDist G W x) * C := by
  obtain ⟨cstar, BG0, hc, hB, H2⟩ := dg2_all (d := d) (L := L) hd hL
  obtain ⟨Bd, hBd, hDw⟩ := dirichlet_weighted (d := d) (L := L) hd hL
  refine ⟨cstar, Real.exp (gammaW d) * (2 * BG0 + 2 * Bd / 3) + 2 * Bd / 3, hc, by positivity, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα κ hκ hMκ s hs W hW f C hC hfC
  have hd0 : 0 < d := by omega
  have hγ0 := gammaW_nonneg hd0
  have hE1 : 1 ≤ Real.exp (N0 d L * κ) := Real.one_le_exp (by positivity)
  have hMκ0 : cstar * Real.exp (N0 d L * 0) ≤ (L : ℝ) ^ m₁ := by
    simp only [mul_zero, Real.exp_zero, mul_one]
    nlinarith
  have hw1 : IsWeight G (gammaW d) (fun _ => (1 : ℝ)) := IsWeight.one G hγ0
  have hfC1 : ∀ x : G.Ω 1, (fun _ => (1 : ℝ)) x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ C :=
    fun x => by simpa using hfC x
  -- the two operators: `s` and `s ≡ 1`
  obtain ⟨⟨hUs, hSs⟩, hCs⟩ := H2 G S hα hκ hMκ hs hw1 f hC hfC1
  obtain ⟨⟨hU1, hS1⟩, hC1⟩ := H2 G S hα (κ := 0) le_rfl hMκ0 (s := fun _ => 1) (by simp) hw1 f hC hfC1
  have hspos : ∀ x : G.Ω 1, 0 < (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 := fun x => by
    have := spacing_pos G (x := (x : CTorus d L N₁ m₁ K)); positivity
  have hGs1 : Gs G a ν α (fun _ => 1) = (dirichletOperator G a ν α)⁻¹ := Gs_one_of_unit S hα hU1
  have hdetK := (Matrix.isUnit_iff_isUnit_det _).1 hUs
  set g : G.Ω 1 → ℂ := (1 - Kcal G a ν α s)⁻¹ *ᵥ f with hgdef
  have hg1 : (1 - Kcal G a ν α s) *ᵥ g = f := by
    rw [hgdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetK, Matrix.one_mulVec]
  have hg2 : g - Kcal G a ν α s *ᵥ g = f := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hg1; exact hg1
  have hKs1 : ∀ (h : G.Ω 1 → ℂ) (C0 : ℝ), 0 ≤ C0 →
      WBd (fun x : G.Ω 1 => (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2) h C0 →
      WBd (fun x : G.Ω 1 => (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2) (Kcal G a ν α s *ᵥ h) (C0 / 4) := by
    intro h C0 hC0 hh x
    have := hCs h hC0 (fun y => by simpa using hh y) x
    simpa using this
  have hgW : WBd (fun x : G.Ω 1 => (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2) g (4 * C / 3) :=
    neumann_bound hspos hKs1 hg2 (fun x => hfC x)
  have hgW' : ∀ x : G.Ω 1, (fun _ => (1 : ℝ)) x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖g x‖ ≤
      4 * C / 3 := fun x => by simpa using hgW x
  set h : G.Ω 1 → ℂ := (Kcal G a ν α s - Kcal G a ν α (fun _ => 1)) *ᵥ g with hhdef
  have hhW : ∀ x : G.Ω 1, (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖h x‖ ≤ 2 * C / 3 := by
    intro x
    have h1 := hCs g (by positivity) hgW' x
    have h2 := hC1 g (by positivity) hgW' x
    simp only [one_mul] at h1 h2
    rw [hhdef, Matrix.sub_mulVec, Pi.sub_apply]
    calc (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
          ‖(Kcal G a ν α s *ᵥ g) x - (Kcal G a ν α (fun _ => 1) *ᵥ g) x‖
        ≤ (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
          (‖(Kcal G a ν α s *ᵥ g) x‖ + ‖(Kcal G a ν α (fun _ => 1) *ᵥ g) x‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (hspos x).le
      _ = (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖(Kcal G a ν α s *ᵥ g) x‖ +
          (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖(Kcal G a ν α (fun _ => 1) *ᵥ g) x‖ := by ring
      _ ≤ 2 * C / 3 := by linarith
  -- the decomposition `G_s f - G_D f = A + B`
  have hid := Gs_sub_Gd S hα hUs f
  have hdec : ∀ y, Gdiff G a ν α s f y =
      (zeroExt (G.Ω 1) (Gstar G a ν α s *ᵥ g) y -
        zeroExt (G.Ω 1) (Gstar G a ν α (fun _ => 1) *ᵥ g) y) +
      solExt G (dirichletOperator G a ν α)⁻¹ h y := by
    intro y
    unfold Gdiff
    rw [← zeroExt_sub', hid, zeroExt_add', Matrix.sub_mulVec, zeroExt_sub']
    rfl
  -- the weights
  have hwT : ∀ T : ℝ, 1 ≤ T → IsWeight G (gammaW d) (fun y => if siteSetDist G W y = ⊤ then T else
      Real.exp (gammaW d * (siteSetDist G W y).toReal)) := fun T hT =>
    isWeight_of_dist G hγ0 hT (siteSetDist G W) (setDist_triangle W)
  have hhWT : ∀ T : ℝ, 1 ≤ T → ∀ y : G.Ω 1, (fun y => if siteSetDist G W y = ⊤ then T else
      Real.exp (gammaW d * (siteSetDist G W y).toReal)) (y : CTorus d L N₁ m₁ K) *
      (G.spacing (y : CTorus d L N₁ m₁ K)) ^ 2 * ‖h y‖ ≤ 2 * C / 3 := by
    intro T hT y
    by_cases hyW : (y : CTorus d L N₁ m₁ K) ∈ W
    · simp only [setDist_of_mem W hyW y.2, ENNReal.zero_ne_top, ↓reduceIte, ENNReal.toReal_zero,
        mul_zero, Real.exp_zero, one_mul]
      exact hhW y
    · have : h y = 0 := Kcal_diff_zero (α := α) S hW g hyW
      rw [this, norm_zero, mul_zero]; positivity
  have hDT := fun T (hT : 1 ≤ T) => hDw G S hα (hwT T hT) h (C := 2 * C / 3) (by positivity)
    (hhWT T hT)
  have hD1 := hDw G S hα hw1 h (C := 2 * C / 3) (by positivity) (fun y => by simpa using hhW y)
  -- bounds for `G_1 f = G_D f`
  rw [hGs1] at hS1
  intro x hx
  set vs : CTorus d L N₁ m₁ K → ℂ := zeroExt (G.Ω 1) (Gs G a ν α s *ᵥ f) with hvs
  set vD : CTorus d L N₁ m₁ K → ℂ := zeroExt (G.Ω 1) ((dirichletOperator G a ν α)⁻¹ *ᵥ f) with hvD
  set Bf : CTorus d L N₁ m₁ K → ℂ := solExt G (dirichletOperator G a ν α)⁻¹ h with hBf
  set Af : CTorus d L N₁ m₁ K → ℂ := fun y => zeroExt (G.Ω 1) (Gstar G a ν α s *ᵥ g) y -
    zeroExt (G.Ω 1) (Gstar G a ν α (fun _ => 1) *ᵥ g) y with hAf
  have hΔ : ∀ y, Gdiff G a ν α s f y = Af y + Bf y := hdec
  have hAeq : ∀ y, Af y = vs y - vD y - Bf y := by
    intro y; have := hΔ y; unfold Gdiff at this; rw [hvs, hvD]; linear_combination -this
  set T1 : ℝ := BG0 * Real.exp (N0 d L * κ) * C + BG0 * Real.exp (N0 d L * 0) * C +
    Bd * (2 * C / 3) with hT1
  have hT1pos : 0 ≤ T1 := by positivity
  have hT1le : T1 ≤ (2 * BG0 + 2 * Bd / 3) * Real.exp (N0 d L * κ) * C := by
    rw [hT1]; simp only [mul_zero, Real.exp_zero, mul_one]
    have h1 : BG0 * C ≤ BG0 * Real.exp (N0 d L * κ) * C := by
      calc BG0 * C = BG0 * 1 * C := by ring
        _ ≤ BG0 * Real.exp (N0 d L * κ) * C := by gcongr
    have h2 : Bd * (2 * C / 3) ≤ (2 * Bd / 3) * Real.exp (N0 d L * κ) * C := by
      calc Bd * (2 * C / 3) = (2 * Bd / 3) * 1 * C := by ring
        _ ≤ (2 * Bd / 3) * Real.exp (N0 d L * κ) * C := by gcongr
    nlinarith
  have hMb : 0 ≤ Bd * (2 * C / 3) := by positivity
  -- the generic observable estimate
  have obs : ∀ (o : (CTorus d L N₁ m₁ K → ℂ) →ₗ[ℂ] ℂ) (c : ℝ), 0 ≤ c →
      ∀ (pts : Finset (CTorus d L N₁ m₁ K)), (∀ p ∈ pts, p = x ∨ Adj x p) →
      (∀ u : CTorus d L N₁ m₁ K → ℂ, (∀ p ∈ pts, u p = 0) → o u = 0) →
      c * ‖o vs‖ ≤ BG0 * Real.exp (N0 d L * κ) * C →
      c * ‖o vD‖ ≤ BG0 * Real.exp (N0 d L * 0) * C →
      c * ‖o Bf‖ ≤ Bd * (2 * C / 3) →
      (∀ T : ℝ, 1 ≤ T → (if siteSetDist G W x = ⊤ then T else
        Real.exp (gammaW d * (siteSetDist G W x).toReal)) * (c * ‖o Bf‖) ≤ Bd * (2 * C / 3)) →
      c * ‖o (Gdiff G a ν α s f)‖ ≤ (Real.exp (gammaW d) * T1 + Bd * (2 * C / 3)) *
        decay (gammaW d) (siteSetDist G W x) := by
    intro o c hc pts hpts hvan h1 h2 h3 h4
    refine dg6_core hγ0 hc hT1pos W o Af Bf (Gdiff G a ν α s f) hΔ hx pts hpts
      (fun hz => hvan Af hz) ?_ ?_ h4
    · intro p hp hAp
      by_contra hne
      apply hAp
      by_cases hpW : p ∈ W
      · have hpΩ : p ∉ G.Ω 1 := fun h' => hne ⟨hpW, h'⟩
        simp [hAf, zeroExt_not_mem _ _ hpΩ]
      · exact Gstar_diff_zero S hα hW g hpW
    · have hoA : o Af = o vs - o vD - o Bf := by
        have : Af = vs - vD - Bf := funext hAeq
        rw [this, map_sub, map_sub]
      rw [hoA]
      calc c * ‖o vs - o vD - o Bf‖ ≤ c * (‖o vs‖ + ‖o vD‖ + ‖o Bf‖) := by
            refine mul_le_mul_of_nonneg_left ?_ hc
            calc ‖o vs - o vD - o Bf‖ ≤ ‖o vs - o vD‖ + ‖o Bf‖ := norm_sub_le _ _
              _ ≤ ‖o vs‖ + ‖o vD‖ + ‖o Bf‖ := by linarith [norm_sub_le (o vs) (o vD)]
        _ = c * ‖o vs‖ + c * ‖o vD‖ + c * ‖o Bf‖ := by ring
        _ ≤ T1 := by rw [hT1]; linarith
  have hdecay := decay_nonneg (gammaW d) (siteSetDist G W x)
  have hfin : (Real.exp (gammaW d) * T1 + Bd * (2 * C / 3)) *
      decay (gammaW d) (siteSetDist G W x) ≤
      (Real.exp (gammaW d) * (2 * BG0 + 2 * Bd / 3) + 2 * Bd / 3) * Real.exp (N0 d L * κ) *
        decay (gammaW d) (siteSetDist G W x) * C := by
    have h1 : Real.exp (gammaW d) * T1 ≤
        Real.exp (gammaW d) * ((2 * BG0 + 2 * Bd / 3) * Real.exp (N0 d L * κ) * C) :=
      mul_le_mul_of_nonneg_left hT1le (Real.exp_pos _).le
    have h2 : Bd * (2 * C / 3) ≤ (2 * Bd / 3) * Real.exp (N0 d L * κ) * C := by
      calc Bd * (2 * C / 3) = (2 * Bd / 3) * 1 * C := by ring
        _ ≤ (2 * Bd / 3) * Real.exp (N0 d L * κ) * C := by gcongr
    have h3 : Real.exp (gammaW d) * T1 + Bd * (2 * C / 3) ≤
        (Real.exp (gammaW d) * (2 * BG0 + 2 * Bd / 3) + 2 * Bd / 3) * Real.exp (N0 d L * κ) * C := by
      nlinarith
    calc (Real.exp (gammaW d) * T1 + Bd * (2 * C / 3)) * decay (gammaW d) (siteSetDist G W x)
        ≤ ((Real.exp (gammaW d) * (2 * BG0 + 2 * Bd / 3) + 2 * Bd / 3) * Real.exp (N0 d L * κ) * C) *
          decay (gammaW d) (siteSetDist G W x) := mul_le_mul_of_nonneg_right h3 hdecay
      _ = _ := by ring
  have hsp := (spacing_pos G (x := x)).le
  refine ⟨?_, fun μ => ?_, ?_⟩
  · have := obs (evalLM (n := (N₁ * L ^ m₁) * L ^ K) x) 1 zero_le_one {x}
      (fun p hp => Or.inl (Finset.mem_singleton.1 hp))
      (fun u hu => by simpa [evalLM_apply] using hu x (Finset.mem_singleton_self x))
      (by simpa [evalLM_apply, hvs] using hSs.val x hx)
      (by simpa [evalLM_apply, hvD] using hS1.val x hx)
      (by simpa [evalLM_apply, hBf] using hD1.1 hx)
      (fun T hT => by simpa [evalLM_apply, hBf] using (hDT T hT).1 hx)
    have h := this.trans hfin
    simpa [evalLM_apply, Gdiff] using h
  · have := obs (gradLM (n := (N₁ * L ^ m₁) * L ^ K) x μ) (G.spacing x) hsp {x, x + Pi.single μ 1}
      (by
        intro p hp
        rcases Finset.mem_insert.1 hp with rfl | hp'
        · exact Or.inl rfl
        · rw [Finset.mem_singleton.1 hp']; exact Or.inr ⟨μ, Or.inl rfl⟩)
      (fun u hu => by
        rw [gradLM_apply, hu x (by simp), hu (x + Pi.single μ 1) (by simp), sub_zero])
      (by simpa [gradLM_apply, hvs] using hSs.fwd x hx μ)
      (by simpa [gradLM_apply, hvD] using hS1.fwd x hx μ)
      (by simpa [gradLM_apply, hBf] using (hD1.2.1 hx μ))
      (fun T hT => by simpa [gradLM_apply, hBf] using ((hDT T hT).2.1 hx μ))
    have h := this.trans hfin
    simpa [gradLM_apply, Gdiff] using h
  · classical
    have := obs (lapLM (n := (N₁ * L ^ m₁) * L ^ K) x) ((G.spacing x) ^ 2) (by positivity)
      (Finset.univ.image (fun μ : Fin d => x + Pi.single μ 1) ∪
        Finset.univ.image (fun μ : Fin d => x - Pi.single μ 1) ∪ {x})
      (by
        intro p hp
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_singleton] at hp
        rcases hp with (⟨μ, rfl⟩ | ⟨μ, rfl⟩) | rfl
        · exact Or.inr ⟨μ, Or.inl rfl⟩
        · exact Or.inr ⟨μ, Or.inr (by simp)⟩
        · exact Or.inl rfl)
      (fun u hu => by
        rw [lapLM_apply]
        refine Finset.sum_eq_zero fun μ _ => ?_
        rw [hu x (by simp), hu (x + Pi.single μ 1) (by simp), hu (x - Pi.single μ 1) (by simp)]
        ring)
      (by simpa [lapLM_apply, hvs] using hSs.lap x hx)
      (by simpa [lapLM_apply, hvD] using hS1.lap x hx)
      (by simpa [lapLM_apply, hBf] using (hD1.2.2 hx))
      (fun T hT => by simpa [lapLM_apply, hBf] using ((hDT T hT).2.2 hx))
    have h := this.trans hfin
    simpa [lapLM_apply, Gdiff] using h

end Close

end Balaban.Localization
