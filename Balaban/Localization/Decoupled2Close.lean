/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2Gs
public import Balaban.Localization.Decoupled2Local
public import Balaban.Localization.DecoupledClose

/-!
# (DG6): closeness of `G_s(A)` to `G_1(A) = G_D(A)` away from the parameters

For a cover `C` and an operator `H`.  The weighted block bounds of the global Dirichlet Green's
function (`dirichlet_weighted`) only involve `H`; the identity `Gs_sub_Gd` and the support of
`(G*_s - G*_1) g` involve the cover.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {α : H.Ω 1 → ℂ}


/-- The weighted form of the block bounds of the global Dirichlet Green's function. -/
theorem dirichlet_weighted (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, OpSetting H a ν →
      ∀ {α : H.Ω 1 → ℂ}, AdmPot H α →
      ∀ {w : CTorus d L N₁ m₁ K → ℝ}, IsWeight H (gammaW d) w →
      ∀ (g : H.Ω 1 → ℂ) {Cb : ℝ}, 0 ≤ Cb →
      (∀ x : H.Ω 1, w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖g x‖ ≤ Cb) →
      (∀ {x : CTorus d L N₁ m₁ K}, x ∈ H.Ω 1 →
        w x * ‖solExt H (dirichletOperator H a ν α)⁻¹ g x‖ ≤ Bd * Cb) ∧
      (∀ {x : CTorus d L N₁ m₁ K}, x ∈ H.Ω 1 → ∀ μ : Fin d,
        w x * (H.spacing x * ‖solExt H (dirichletOperator H a ν α)⁻¹ g (x + Pi.single μ 1) -
          solExt H (dirichletOperator H a ν α)⁻¹ g x‖) ≤ Bd * Cb) ∧
      (∀ {x : CTorus d L N₁ m₁ K}, x ∈ H.Ω 1 →
        w x * ((H.spacing x) ^ 2 * ‖∑ μ : Fin d, (2 * solExt H (dirichletOperator H a ν α)⁻¹ g x -
          solExt H (dirichletOperator H a ν α)⁻¹ g (x + Pi.single μ 1) -
          solExt H (dirichletOperator H a ν α)⁻¹ g (x - Pi.single μ 1))‖) ≤ Bd * Cb) := by
  obtain ⟨Kd, hKd, hB⟩ := dirichlet_block_bounds (d := d) (L := L) hd hL
  refine ⟨Kd * Real.exp (2 * gammaW d * d) * countConst d L (agmonRate d / 2 - gammaW d), ?_, ?_⟩
  · have : 0 ≤ countConst d L (agmonRate d / 2 - gammaW d) := tsum_nonneg fun m => by positivity
    positivity
  intro N₁ m₁ K _ ϱ H a ν S α hα w hw g Cb hC hgC
  have hd0 : 0 < d := by omega
  have hγ0 := gammaW_nonneg hd0
  have hγlt := gammaW_lt hd0
  have hρ := S.one_lt_rho
  have hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) := S.sep_pow (le_of_eq rfl)
  have hΛ : BlockAligned H (Finset.univ : Finset (CTorus d L N₁ m₁ K)) :=
    fun j hj1 hjk x x' _ _ => by simp
  have hpieces := fun {j'} {y'} (hj'1 : 1 ≤ j') (hj'k : j' ≤ K) (hy' : y' ∈ H.layer j')
      (f : H.Ω 1 → ℂ) (hs : ∀ z : H.Ω 1, f z ≠ 0 →
        jBlock d L (N₁ * L ^ m₁) K j' z = jBlock d L (N₁ * L ^ m₁) K j' y') {Mf : ℝ} (hMf0 : 0 ≤ Mf)
      (hMf : ∀ z, ‖f z‖ ≤ Mf) =>
    hB H S.mass S.massLe S.weights hα hρ.le hsep hj'1 hj'k hy' f hs hMf0 hMf
  refine ⟨fun {x} hx => ?_, fun {x} hx μ => ?_, fun {x} hx => ?_⟩
  · have := weighted_sum_bound (G := H) (γ := gammaW d) (γ0 := agmonRate d / 2) (Kc := Kd) (s := 1)
      hγ0 hγlt hKd zero_le_one hw (dirichletOperator H a ν α)⁻¹
      (evalLM (n := (N₁ * L ^ m₁) * L ^ K) x) hx hΛ hρ S.sep_weight
      (fun {j'} {y'} hj'1 hj'k hy' _ g' hs {Mf} hMf0 hMf => by
        have := (hpieces hj'1 hj'k hy' g' hs hMf0 hMf).1 hx
        simpa [evalLM_apply] using this)
      g (fun _ _ => Finset.mem_univ _) hC hgC
    simpa [evalLM_apply] using this
  · have := weighted_sum_bound (G := H) (γ := gammaW d) (γ0 := agmonRate d / 2) (Kc := Kd)
      (s := H.spacing x) hγ0 hγlt hKd (spacing_pos H).le hw (dirichletOperator H a ν α)⁻¹
      (gradLM (n := (N₁ * L ^ m₁) * L ^ K) x μ) hx hΛ hρ S.sep_weight
      (fun {j'} {y'} hj'1 hj'k hy' _ g' hs {Mf} hMf0 hMf => by
        have := (hpieces hj'1 hj'k hy' g' hs hMf0 hMf).2.1 hx μ
        simpa [gradLM_apply] using this)
      g (fun _ _ => Finset.mem_univ _) hC hgC
    simpa [gradLM_apply] using this
  · have := weighted_sum_bound (G := H) (γ := gammaW d) (γ0 := agmonRate d / 2) (Kc := Kd)
      (s := H.spacing x ^ 2) hγ0 hγlt hKd (by have := spacing_pos H (x := x); positivity) hw
      (dirichletOperator H a ν α)⁻¹ (lapLM (n := (N₁ * L ^ m₁) * L ^ K) x) hx hΛ hρ S.sep_weight
      (fun {j'} {y'} hj'1 hj'k hy' _ g' hs {Mf} hMf0 hMf => by
        have := (hpieces hj'1 hj'k hy' g' hs hMf0 hMf).2.2 hx
        simpa [lapLM_apply] using this)
      g (fun _ _ => Finset.mem_univ _) hC hgC
    simpa [lapLM_apply] using this

/-- **The algebraic identity behind (DG6)**:
`(G_s - G_D) f = (H*_s - H*_1) g + G_D (𝒦_s - 𝒦_1) g`, `g = (1 - 𝒦_s)⁻¹ f`. -/
theorem Gs_sub_Gd (S : CoverBase C H a ν Kc Cx) (hα : AdmPot H α) {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hU : IsUnit (1 - Kcal C H a ν α s)) (f : H.Ω 1 → ℂ) :
    Gs C H a ν α s *ᵥ f - (dirichletOperator H a ν α)⁻¹ *ᵥ f =
      (Gstar C H a ν α s - Gstar C H a ν α (fun _ => 1)) *ᵥ ((1 - Kcal C H a ν α s)⁻¹ *ᵥ f) +
      (dirichletOperator H a ν α)⁻¹ *ᵥ
        ((Kcal C H a ν α s - Kcal C H a ν α (fun _ => 1)) *ᵥ ((1 - Kcal C H a ν α s)⁻¹ *ᵥ f)) := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hHU := dirichletOperator_isUnit H hd0 S.mass S.weights α hα
  have hdetH := (Matrix.isUnit_iff_isUnit_det _).1 hHU
  have hdetK := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hpar := parametrix S hα
  set Gd := (dirichletOperator H a ν α)⁻¹ with hGd
  have h1 : Gstar C H a ν α (fun _ => 1) = Gd * (1 - Kcal C H a ν α (fun _ => 1)) := by
    rw [← hpar, ← Matrix.mul_assoc, hGd, Matrix.nonsing_inv_mul _ hdetH, Matrix.one_mul]
  set g := (1 - Kcal C H a ν α s)⁻¹ *ᵥ f with hg
  have hg1 : (1 - Kcal C H a ν α s) *ᵥ g = f := by
    rw [hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetK, Matrix.one_mulVec]
  have e : Gs C H a ν α s *ᵥ f = Gstar C H a ν α s *ᵥ g := by
    rw [hg, Gs, ← Matrix.mulVec_mulVec]
  have hA1g : Gstar C H a ν α (fun _ => 1) *ᵥ g =
      Gd *ᵥ (g - Kcal C H a ν α (fun _ => 1) *ᵥ g) := by
    rw [h1, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hf : f = g - Kcal C H a ν α s *ᵥ g := by
    rw [← hg1, Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [e, Matrix.sub_mulVec, Matrix.sub_mulVec, hA1g, Matrix.mulVec_sub, Matrix.mulVec_sub]
  conv_lhs => rw [hf, Matrix.mulVec_sub]
  abel

theorem cubeSolE_eq_zero_of_not_mem_box (S : CoverBase C H a ν Kc Cx) (hα : AdmPot H α)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ C.cubeIdx) (g : H.Ω 1 → ℂ)
    {y : CTorus d L N₁ m₁ K} (hy : y ∉ intBox q) : cubeSolE H a ν α q g y = 0 := by
  by_cases hyΩ : y ∈ H.Ω 1
  · have h := cubeG_supp S hα hq g ⟨y, hyΩ⟩ hy
    rw [cubeG_mulVec] at h
    unfold cubeSolE solExt
    rw [zeroExt_of_mem' hyΩ]
    exact h
  · exact cubeSolE_of_not_mem q g hyΩ

/-- `(H*_s - H*_1) g` vanishes off `W`. -/
theorem Gstar_diff_zero (S : CoverBase C H a ν Kc Cx) (hα : AdmPot H α)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {W : Finset (CTorus d L N₁ m₁ K)}
    (hW : ∀ z ∈ C.cubeIdx, C.sProd s z ≠ 1 → intBox z ⊆ W) (g : H.Ω 1 → ℂ)
    {y : CTorus d L N₁ m₁ K} (hy : y ∉ W) :
    zeroExt (H.Ω 1) (Gstar C H a ν α s *ᵥ g) y -
      zeroExt (H.Ω 1) (Gstar C H a ν α (fun _ => 1) *ᵥ g) y = 0 := by
  rw [Gstar_apply, Gstar_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun z hz => ?_
  by_cases hc : C.sProd s z = 1
  · rw [hc, C.sProd_one _]; ring
  · have hb : y ∉ intBox z := fun h => hy (hW z hz hc h)
    rw [cubeSolE_eq_zero_of_not_mem_box S hα hz g hb]; simp

/-- `(𝒦_s - 𝒦_1) g` vanishes off `W`. -/
theorem Kcal_diff_zero (S : CoverBase C H a ν Kc Cx)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {W : Finset (CTorus d L N₁ m₁ K)}
    (hW : ∀ z ∈ C.cubeIdx, C.sProd s z ≠ 1 → intBox z ⊆ W) (g : H.Ω 1 → ℂ) {x : H.Ω 1}
    (hx : (x : CTorus d L N₁ m₁ K) ∉ W) :
    ((Kcal C H a ν α s - Kcal C H a ν α (fun _ => 1)) *ᵥ g) x = 0 := by
  rw [Matrix.sub_mulVec, Pi.sub_apply]
  unfold Kcal
  rw [Matrix.sum_mulVec, Matrix.sum_mulVec, Finset.sum_apply, Finset.sum_apply,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun z hz => ?_
  by_cases hc : C.sProd s z = 1
  · rw [hc, C.sProd_one _]; ring
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
theorem Gs_one_of_unit (S : CoverBase C H a ν Kc Cx) (hα : AdmPot H α)
    (hU : IsUnit (1 - Kcal C H a ν α (fun _ => 1))) :
    Gs C H a ν α (fun _ => 1) = (dirichletOperator H a ν α)⁻¹ := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hdetK := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hpar := parametrix S hα
  have h1 : dirichletOperator H a ν α * Gs C H a ν α (fun _ => 1) = 1 := by
    unfold Gs
    rw [← Matrix.mul_assoc, hpar, Matrix.mul_nonsing_inv _ hdetK]
  exact (Matrix.inv_eq_right_inv h1).symm

/-- The estimate of one observable of `G_s f - G_D f = A + B` (see `dg6`): `A` is supported in
`W ∩ Ω₁` (so it only matters at distance `≤ 1` from `W`), `B` obeys the weighted bound. -/
theorem dg6_core {γ T1 Mb c : ℝ} (hγ : 0 ≤ γ) (hc : 0 ≤ c) (hT1 : 0 ≤ T1)
    (W : Finset (CTorus d L N₁ m₁ K)) (o : (CTorus d L N₁ m₁ K → ℂ) →ₗ[ℂ] ℂ)
    (A B Δ : CTorus d L N₁ m₁ K → ℂ) (hΔ : ∀ y, Δ y = A y + B y)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1) (pts : Finset (CTorus d L N₁ m₁ K))
    (hpts : ∀ p ∈ pts, p = x ∨ Adj x p)
    (hvan : (∀ p ∈ pts, A p = 0) → o A = 0)
    (hAW : ∀ p ∈ pts, A p ≠ 0 → p ∈ W ∧ p ∈ H.Ω 1)
    (hA : c * ‖o A‖ ≤ T1)
    (hB : ∀ T : ℝ, 1 ≤ T → (if siteSetDist H W x = ⊤ then T else
      Real.exp (γ * (siteSetDist H W x).toReal)) * (c * ‖o B‖) ≤ Mb) :
    c * ‖o Δ‖ ≤ (Real.exp γ * T1 + Mb) * decay γ (siteSetDist H W x) := by
  have hΔ' : Δ = A + B := funext hΔ
  have hoΔ : o Δ = o A + o B := by rw [hΔ', map_add]
  have hdec := decay_nonneg γ (siteSetDist H W x)
  have hBd : c * ‖o B‖ ≤ Mb * decay γ (siteSetDist H W x) :=
    decay_of_dist_weights (mul_nonneg hc (norm_nonneg _)) _ hB
  have hAd : c * ‖o A‖ ≤ Real.exp γ * T1 * decay γ (siteSetDist H W x) := by
    by_cases hA0 : o A = 0
    · rw [hA0, norm_zero, mul_zero]; positivity
    · have hex : ∃ p ∈ pts, A p ≠ 0 := by
        by_contra hne
        push Not at hne
        exact hA0 (hvan hne)
      obtain ⟨p, hp, hAp⟩ := hex
      obtain ⟨hpW, hpΩ⟩ := hAW p hp hAp
      have hD : siteSetDist H W x ≤ ENNReal.ofReal 1 := by
        rcases hpts p hp with rfl | hadj
        · rw [setDist_of_mem W hpW hpΩ]; exact bot_le
        · exact setDist_adj_le W hx hpΩ hpW hadj
      have h1 := decay_ofReal_ge hγ zero_le_one hD
      have h2 : T1 ≤ Real.exp γ * T1 * decay γ (siteSetDist H W x) := by
        have hE : Real.exp γ * Real.exp (-(γ * 1)) = 1 := by rw [← Real.exp_add]; simp
        calc T1 = T1 * (Real.exp γ * Real.exp (-(γ * 1))) := by rw [hE, mul_one]
          _ ≤ T1 * (Real.exp γ * decay γ (siteSetDist H W x)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le) hT1
          _ = Real.exp γ * T1 * decay γ (siteSetDist H W x) := by ring
      exact hA.trans h2
  rw [hoΔ]
  calc c * ‖o A + o B‖ ≤ c * (‖o A‖ + ‖o B‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hc
    _ = c * ‖o A‖ + c * ‖o B‖ := by ring
    _ ≤ Real.exp γ * T1 * decay γ (siteSetDist H W x) + Mb * decay γ (siteSetDist H W x) :=
        add_le_add hAd hBd
    _ = _ := by ring

/-- `G_s(A) f - G_D(A) f` on the whole torus (zero extensions). -/
noncomputable def Gdiff (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (α : H.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ K → ℂ) (f : H.Ω 1 → ℂ)
    (y : CTorus d L N₁ m₁ K) : ℂ :=
  zeroExt (H.Ω 1) (Gs C H a ν α s *ᵥ f) y - zeroExt (H.Ω 1) ((dirichletOperator H a ν α)⁻¹ *ᵥ f) y

/-- **(DG6), closeness.**  If every centre with `s_z ≠ 1` has its interaction cube in `W`, then
`G_s(A) f - G_D(A) f` and its differences decay like `e^{-γ_w d(x, W)}`. -/
theorem dg6 (hd : 3 ≤ d) (hL : 3 ≤ L) (hKc : 0 ≤ Kc) (hCx : 0 ≤ Cx) :
    ∃ cstar BG : ℝ, 0 ≤ cstar ∧ 0 ≤ BG ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, CoverBase C H a ν Kc Cx →
      ∀ {α : H.Ω 1 → ℂ}, AdmPot H α → ∀ {κ : ℝ}, 0 ≤ κ →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : ℕ × CTorus d L N₁ m₁ K → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ {W : Finset (CTorus d L N₁ m₁ K)},
      (∀ z ∈ C.cubeIdx, C.sProd s z ≠ 1 → intBox z ⊆ W) →
      ∀ (f : H.Ω 1 → ℂ) {Cb : ℝ}, 0 ≤ Cb →
      (∀ x : H.Ω 1, (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ Cb) →
      ∀ x ∈ H.Ω 1,
      ‖Gdiff C H a ν α s f x‖ ≤ BG * Real.exp (N0 d L * κ) * decay (gammaW d) (siteSetDist H W x) * Cb ∧
      (∀ μ : Fin d, H.spacing x * ‖Gdiff C H a ν α s f (x + Pi.single μ 1) -
        Gdiff C H a ν α s f x‖ ≤
        BG * Real.exp (N0 d L * κ) * decay (gammaW d) (siteSetDist H W x) * Cb) ∧
      (H.spacing x) ^ 2 * ‖∑ μ : Fin d, (2 * Gdiff C H a ν α s f x -
        Gdiff C H a ν α s f (x + Pi.single μ 1) - Gdiff C H a ν α s f (x - Pi.single μ 1))‖ ≤
        BG * Real.exp (N0 d L * κ) * decay (gammaW d) (siteSetDist H W x) * Cb := by
  obtain ⟨cstar, BG0, hc, hB, Hh2⟩ := dg2_all (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  obtain ⟨Bd, hBd, hDw⟩ := dirichlet_weighted (d := d) (L := L) hd hL
  refine ⟨cstar, Real.exp (gammaW d) * (2 * BG0 + 2 * Bd / 3) + 2 * Bd / 3, hc, by positivity, ?_⟩
  intro N₁ m₁ K _ ϱ C H a ν S α hα κ hκ hMκ s hs W hW f Cb hC hfC
  have hd0 : 0 < d := by omega
  have hγ0 := gammaW_nonneg hd0
  have hE1 : 1 ≤ Real.exp (N0 d L * κ) := Real.one_le_exp (by positivity)
  have hMκ0 : cstar * Real.exp (N0 d L * 0) ≤ (L : ℝ) ^ m₁ := by
    simp only [mul_zero, Real.exp_zero, mul_one]
    nlinarith
  have hw1 : IsWeight H (gammaW d) (fun _ => (1 : ℝ)) := IsWeight.one H hγ0
  have hfC1 : ∀ x : H.Ω 1, (fun _ => (1 : ℝ)) x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ Cb :=
    fun x => by simpa using hfC x
  -- the two operators: `s` and `s ≡ 1`
  obtain ⟨⟨hUs, hSs⟩, hCs⟩ := Hh2 C H S hα hκ hMκ hs hw1 f hC hfC1
  obtain ⟨⟨hU1, hS1⟩, hC1⟩ := Hh2 C H S hα (κ := 0) le_rfl hMκ0 (s := fun _ => 1) (by simp) hw1 f hC hfC1
  have hspos : ∀ x : H.Ω 1, 0 < (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 := fun x => by
    have := spacing_pos H (x := (x : CTorus d L N₁ m₁ K)); positivity
  have hGs1 : Gs C H a ν α (fun _ => 1) = (dirichletOperator H a ν α)⁻¹ := Gs_one_of_unit S hα hU1
  have hdetK := (Matrix.isUnit_iff_isUnit_det _).1 hUs
  set g : H.Ω 1 → ℂ := (1 - Kcal C H a ν α s)⁻¹ *ᵥ f with hgdef
  have hg1 : (1 - Kcal C H a ν α s) *ᵥ g = f := by
    rw [hgdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetK, Matrix.one_mulVec]
  have hg2 : g - Kcal C H a ν α s *ᵥ g = f := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hg1; exact hg1
  have hKs1 : ∀ (h : H.Ω 1 → ℂ) (Cb0 : ℝ), 0 ≤ Cb0 →
      WBd (fun x : H.Ω 1 => (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2) h Cb0 →
      WBd (fun x : H.Ω 1 => (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2) (Kcal C H a ν α s *ᵥ h) (Cb0 / 4) := by
    intro h Cb0 hC0 hh x
    have := hCs h hC0 (fun y => by simpa using hh y) x
    simpa using this
  have hgW : WBd (fun x : H.Ω 1 => (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2) g (4 * Cb / 3) :=
    neumann_bound hspos hKs1 hg2 (fun x => hfC x)
  have hgW' : ∀ x : H.Ω 1, (fun _ => (1 : ℝ)) x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖g x‖ ≤
      4 * Cb / 3 := fun x => by simpa using hgW x
  set h : H.Ω 1 → ℂ := (Kcal C H a ν α s - Kcal C H a ν α (fun _ => 1)) *ᵥ g with hhdef
  have hhW : ∀ x : H.Ω 1, (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖h x‖ ≤ 2 * Cb / 3 := by
    intro x
    have h1 := hCs g (by positivity) hgW' x
    have h2 := hC1 g (by positivity) hgW' x
    simp only [one_mul] at h1 h2
    rw [hhdef, Matrix.sub_mulVec, Pi.sub_apply]
    calc (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
          ‖(Kcal C H a ν α s *ᵥ g) x - (Kcal C H a ν α (fun _ => 1) *ᵥ g) x‖
        ≤ (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
          (‖(Kcal C H a ν α s *ᵥ g) x‖ + ‖(Kcal C H a ν α (fun _ => 1) *ᵥ g) x‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (hspos x).le
      _ = (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖(Kcal C H a ν α s *ᵥ g) x‖ +
          (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖(Kcal C H a ν α (fun _ => 1) *ᵥ g) x‖ := by ring
      _ ≤ 2 * Cb / 3 := by linarith
  -- the decomposition `G_s f - G_D f = A + B`
  have hid := Gs_sub_Gd S hα hUs f
  have hdec : ∀ y, Gdiff C H a ν α s f y =
      (zeroExt (H.Ω 1) (Gstar C H a ν α s *ᵥ g) y -
        zeroExt (H.Ω 1) (Gstar C H a ν α (fun _ => 1) *ᵥ g) y) +
      solExt H (dirichletOperator H a ν α)⁻¹ h y := by
    intro y
    unfold Gdiff
    rw [← zeroExt_sub', hid, zeroExt_add', Matrix.sub_mulVec, zeroExt_sub']
    rfl
  -- the weights
  have hwT : ∀ T : ℝ, 1 ≤ T → IsWeight H (gammaW d) (fun y => if siteSetDist H W y = ⊤ then T else
      Real.exp (gammaW d * (siteSetDist H W y).toReal)) := fun T hT =>
    isWeight_of_dist H hγ0 hT (siteSetDist H W) (setDist_triangle W)
  have hhWT : ∀ T : ℝ, 1 ≤ T → ∀ y : H.Ω 1, (fun y => if siteSetDist H W y = ⊤ then T else
      Real.exp (gammaW d * (siteSetDist H W y).toReal)) (y : CTorus d L N₁ m₁ K) *
      (H.spacing (y : CTorus d L N₁ m₁ K)) ^ 2 * ‖h y‖ ≤ 2 * Cb / 3 := by
    intro T hT y
    by_cases hyW : (y : CTorus d L N₁ m₁ K) ∈ W
    · simp only [setDist_of_mem W hyW y.2, ENNReal.zero_ne_top, ↓reduceIte, ENNReal.toReal_zero,
        mul_zero, Real.exp_zero, one_mul]
      exact hhW y
    · have : h y = 0 := Kcal_diff_zero (α := α) S hW g hyW
      rw [this, norm_zero, mul_zero]; positivity
  have hDT := fun T (hT : 1 ≤ T) => hDw H S.toOpSetting hα (hwT T hT) h (Cb := 2 * Cb / 3) (by positivity)
    (hhWT T hT)
  have hD1 := hDw H S.toOpSetting hα hw1 h (Cb := 2 * Cb / 3) (by positivity) (fun y => by simpa using hhW y)
  -- bounds for `G_1 f = G_D f`
  rw [hGs1] at hS1
  intro x hx
  set vs : CTorus d L N₁ m₁ K → ℂ := zeroExt (H.Ω 1) (Gs C H a ν α s *ᵥ f) with hvs
  set vD : CTorus d L N₁ m₁ K → ℂ := zeroExt (H.Ω 1) ((dirichletOperator H a ν α)⁻¹ *ᵥ f) with hvD
  set Bf : CTorus d L N₁ m₁ K → ℂ := solExt H (dirichletOperator H a ν α)⁻¹ h with hBf
  set Af : CTorus d L N₁ m₁ K → ℂ := fun y => zeroExt (H.Ω 1) (Gstar C H a ν α s *ᵥ g) y -
    zeroExt (H.Ω 1) (Gstar C H a ν α (fun _ => 1) *ᵥ g) y with hAf
  have hΔ : ∀ y, Gdiff C H a ν α s f y = Af y + Bf y := hdec
  have hAeq : ∀ y, Af y = vs y - vD y - Bf y := by
    intro y; have := hΔ y; unfold Gdiff at this; rw [hvs, hvD]; linear_combination -this
  set T1 : ℝ := BG0 * Real.exp (N0 d L * κ) * Cb + BG0 * Real.exp (N0 d L * 0) * Cb +
    Bd * (2 * Cb / 3) with hT1
  have hT1pos : 0 ≤ T1 := by positivity
  have hT1le : T1 ≤ (2 * BG0 + 2 * Bd / 3) * Real.exp (N0 d L * κ) * Cb := by
    rw [hT1]; simp only [mul_zero, Real.exp_zero, mul_one]
    have h1 : BG0 * Cb ≤ BG0 * Real.exp (N0 d L * κ) * Cb := by
      calc BG0 * Cb = BG0 * 1 * Cb := by ring
        _ ≤ BG0 * Real.exp (N0 d L * κ) * Cb := by gcongr
    have h2 : Bd * (2 * Cb / 3) ≤ (2 * Bd / 3) * Real.exp (N0 d L * κ) * Cb := by
      calc Bd * (2 * Cb / 3) = (2 * Bd / 3) * 1 * Cb := by ring
        _ ≤ (2 * Bd / 3) * Real.exp (N0 d L * κ) * Cb := by gcongr
    nlinarith
  have hMb : 0 ≤ Bd * (2 * Cb / 3) := by positivity
  -- the generic observable estimate
  have obs : ∀ (o : (CTorus d L N₁ m₁ K → ℂ) →ₗ[ℂ] ℂ) (c : ℝ), 0 ≤ c →
      ∀ (pts : Finset (CTorus d L N₁ m₁ K)), (∀ p ∈ pts, p = x ∨ Adj x p) →
      (∀ u : CTorus d L N₁ m₁ K → ℂ, (∀ p ∈ pts, u p = 0) → o u = 0) →
      c * ‖o vs‖ ≤ BG0 * Real.exp (N0 d L * κ) * Cb →
      c * ‖o vD‖ ≤ BG0 * Real.exp (N0 d L * 0) * Cb →
      c * ‖o Bf‖ ≤ Bd * (2 * Cb / 3) →
      (∀ T : ℝ, 1 ≤ T → (if siteSetDist H W x = ⊤ then T else
        Real.exp (gammaW d * (siteSetDist H W x).toReal)) * (c * ‖o Bf‖) ≤ Bd * (2 * Cb / 3)) →
      c * ‖o (Gdiff C H a ν α s f)‖ ≤ (Real.exp (gammaW d) * T1 + Bd * (2 * Cb / 3)) *
        decay (gammaW d) (siteSetDist H W x) := by
    intro o c hc pts hpts hvan h1 h2 h3 h4
    refine dg6_core hγ0 hc hT1pos W o Af Bf (Gdiff C H a ν α s f) hΔ hx pts hpts
      (fun hz => hvan Af hz) ?_ ?_ h4
    · intro p hp hAp
      by_contra hne
      apply hAp
      by_cases hpW : p ∈ W
      · have hpΩ : p ∉ H.Ω 1 := fun h' => hne ⟨hpW, h'⟩
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
  have hdecay := decay_nonneg (gammaW d) (siteSetDist H W x)
  have hfin : (Real.exp (gammaW d) * T1 + Bd * (2 * Cb / 3)) *
      decay (gammaW d) (siteSetDist H W x) ≤
      (Real.exp (gammaW d) * (2 * BG0 + 2 * Bd / 3) + 2 * Bd / 3) * Real.exp (N0 d L * κ) *
        decay (gammaW d) (siteSetDist H W x) * Cb := by
    have h1 : Real.exp (gammaW d) * T1 ≤
        Real.exp (gammaW d) * ((2 * BG0 + 2 * Bd / 3) * Real.exp (N0 d L * κ) * Cb) :=
      mul_le_mul_of_nonneg_left hT1le (Real.exp_pos _).le
    have h2 : Bd * (2 * Cb / 3) ≤ (2 * Bd / 3) * Real.exp (N0 d L * κ) * Cb := by
      calc Bd * (2 * Cb / 3) = (2 * Bd / 3) * 1 * Cb := by ring
        _ ≤ (2 * Bd / 3) * Real.exp (N0 d L * κ) * Cb := by gcongr
    have h3 : Real.exp (gammaW d) * T1 + Bd * (2 * Cb / 3) ≤
        (Real.exp (gammaW d) * (2 * BG0 + 2 * Bd / 3) + 2 * Bd / 3) * Real.exp (N0 d L * κ) * Cb := by
      nlinarith
    calc (Real.exp (gammaW d) * T1 + Bd * (2 * Cb / 3)) * decay (gammaW d) (siteSetDist H W x)
        ≤ ((Real.exp (gammaW d) * (2 * BG0 + 2 * Bd / 3) + 2 * Bd / 3) * Real.exp (N0 d L * κ) * Cb) *
          decay (gammaW d) (siteSetDist H W x) := mul_le_mul_of_nonneg_right h3 hdecay
      _ = _ := by ring
  have hsp := (spacing_pos H (x := x)).le
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
  · have := obs (gradLM (n := (N₁ * L ^ m₁) * L ^ K) x μ) (H.spacing x) hsp {x, x + Pi.single μ 1}
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
    have := obs (lapLM (n := (N₁ * L ^ m₁) * L ^ K) x) ((H.spacing x) ^ 2) (by positivity)
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

end Balaban.Localization.Dec2
