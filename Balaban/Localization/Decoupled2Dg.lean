/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2

/-!
# (DG1), (DG2) for a cover `C` and an operator `H`

The cube bounds `cube_weighted`, `cube_star`, `Kz_cube_weighted`, the weighted contraction
`dg1` (`‖𝒦_s(A)‖ ≤ 1/4`), and the pointwise bounds `dg2_all`, `dg2_sup`, `Gs_one`.  The proofs are
those of `DecoupledCube.lean`, `DecoupledBounds.lean`, `DecoupledGs.lean`, `DecoupledMain.lean`;
only the hypotheses change: the cut-operator estimate (NC3) and the cover facts are read from
`CoverBase C H a ν Kc Cx`.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {α : H.Ω 1 → ℂ}

theorem OpSetting.one_lt_rho (S : OpSetting H a ν) : 1 < ϱ := by
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


theorem OpSetting.sep_pow (S : OpSetting H a ν) {n : ℕ} (hn : (n : ℝ) ≤ d) :
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

theorem OpSetting.sep_weight (S : OpSetting H a ν) :
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


/-- **The weighted form of (NC3)** for the cube operator of the centre `q` (LOCALIZATION.md §3.1):
for `f` supported in `□_z` with `w ℓ² |f| ≤ Cb`, `w` a weight of rate `γ_w`, the value, the forward
gradient (at points with all forward neighbours in the cube) and the Laplacian (at points with all
neighbours in the cube) of `u = H_z(A)⁻¹ f` satisfy `w · (…) ≤ B_w Cb`. -/
theorem cube_weighted (hd : 3 ≤ d) (hL : 3 ≤ L) (hKc : 0 ≤ Kc) :
    ∃ Bw : ℝ, 0 ≤ Bw ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, CoverBase C H a ν Kc Cx →
      ∀ {α : H.Ω 1 → ℂ}, AdmPot H α → ∀ {q : ℕ × CTorus d L N₁ m₁ K}, q ∈ C.cubeIdx →
      ∀ {w : CTorus d L N₁ m₁ K → ℝ}, IsWeight H (gammaW d) w →
      ∀ (f : H.Ω 1 → ℂ), (∀ z : H.Ω 1, f z ≠ 0 → (z : CTorus d L N₁ m₁ K) ∈ intBox q) →
      ∀ {Cb : ℝ}, 0 ≤ Cb → (∀ x : H.Ω 1, w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ Cb) →
      (∀ {x : CTorus d L N₁ m₁ K}, x ∈ H.Ω 1 → x ∈ intBox q →
        w x * ‖solExt H (cubeH H a ν α q)⁻¹ f x‖ ≤ Bw * Cb) ∧
      (∀ {x : CTorus d L N₁ m₁ K}, x ∈ H.Ω 1 → x ∈ intBox q →
        (∀ ν' : Fin d, x + Pi.single ν' 1 ∈ intBox q) → ∀ μ : Fin d,
        w x * (H.spacing x * ‖solExt H (cubeH H a ν α q)⁻¹ f (x + Pi.single μ 1) -
          solExt H (cubeH H a ν α q)⁻¹ f x‖) ≤ Bw * Cb) ∧
      (∀ {x : CTorus d L N₁ m₁ K}, x ∈ H.Ω 1 → x ∈ intBox q →
        (∀ μ : Fin d, x + Pi.single μ 1 ∈ intBox q ∧ x - Pi.single μ 1 ∈ intBox q) →
        w x * ((H.spacing x) ^ 2 * ‖∑ μ : Fin d, (2 * solExt H (cubeH H a ν α q)⁻¹ f x -
          solExt H (cubeH H a ν α q)⁻¹ f (x + Pi.single μ 1) -
          solExt H (cubeH H a ν α q)⁻¹ f (x - Pi.single μ 1))‖) ≤ Bw * Cb) := by
  refine ⟨Kc * Real.exp (2 * gammaW d * d) * countConst d L (agmonRate d / 2 - gammaW d),
    ?_, ?_⟩
  · have : 0 ≤ countConst d L (agmonRate d / 2 - gammaW d) :=
      tsum_nonneg fun m => by positivity
    positivity
  intro N₁ m₁ K _ ϱ C H a ν S α hα q hq w hw f hf Cb hC hfC
  have hd0 : 0 < d := by omega
  have hBq := S.nc hα q hq
  have hγ0 := gammaW_nonneg hd0
  have hγlt := gammaW_lt hd0
  have hρ := S.one_lt_rho
  have hΛ := S.blockAligned q hq
  refine ⟨fun {x} hxΩ hxb => ?_, fun {x} hxΩ hxb hxe μ => ?_, fun {x} hxΩ hxb hxe => ?_⟩
  · have := weighted_sum_bound (G := H) (γ := gammaW d) (γ0 := agmonRate d / 2) (Kc := Kc) (s := 1)
      hγ0 hγlt hKc zero_le_one hw (cubeH H a ν α q)⁻¹ (evalLM (n := (N₁ * L ^ m₁) * L ^ K) x) hxΩ hΛ hρ
      S.sep_weight
      (fun {j'} {y'} hj'1 hj'k hy' hy'b g hsupp {Mf} hMf0 hMf => by
        have := ((hBq.bounds hj'1 hj'k hy' hy'b g hsupp hMf0 hMf).1 hxΩ hxb)
        simpa [evalLM_apply] using this)
      f hf hC hfC
    simpa [evalLM_apply] using this
  · have := weighted_sum_bound (G := H) (γ := gammaW d) (γ0 := agmonRate d / 2) (Kc := Kc)
      (s := H.spacing x) hγ0 hγlt hKc (spacing_pos H).le hw (cubeH H a ν α q)⁻¹
      (gradLM (n := (N₁ * L ^ m₁) * L ^ K) x μ) hxΩ hΛ hρ S.sep_weight
      (fun {j'} {y'} hj'1 hj'k hy' hy'b g hsupp {Mf} hMf0 hMf => by
        have := ((hBq.bounds hj'1 hj'k hy' hy'b g hsupp hMf0 hMf).2.1 hxΩ hxb hxe μ)
        simpa [gradLM_apply] using this)
      f hf hC hfC
    simpa [gradLM_apply] using this
  · have := weighted_sum_bound (G := H) (γ := gammaW d) (γ0 := agmonRate d / 2) (Kc := Kc)
      (s := H.spacing x ^ 2) hγ0 hγlt hKc (by have := spacing_pos H (x := x); positivity) hw
      (cubeH H a ν α q)⁻¹ (lapLM (n := (N₁ * L ^ m₁) * L ^ K) x) hxΩ hΛ hρ S.sep_weight
      (fun {j'} {y'} hj'1 hj'k hy' hy'b g hsupp {Mf} hMf0 hMf => by
        have := ((hBq.bounds hj'1 hj'k hy' hy'b g hsupp hMf0 hMf).2.2 hxΩ hxb hxe)
        simpa [lapLM_apply] using this)
      f hf hC hfC
    simpa [lapLM_apply] using this


theorem Kz_apply (α : H.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) (x y : H.Ω 1) :
    Kz C H a ν q x y = dirichletOperator H a ν α x y *
      (((C.chi q x : ℝ) : ℂ) - ((C.chi q y : ℝ) : ℂ)) := by
  rw [Kz_eq a ν α q]
  unfold chiD
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

theorem Kz_mulVec_eq_commK (α : H.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) (u : H.Ω 1 → ℂ)
    (x : H.Ω 1) :
    (Kz C H a ν q *ᵥ u) x =
      (commK (dirichletOperator H a ν α) (restrictField H (C.chiField q)) *ᵥ
        (fun p : H.Ω 1 × Fin 1 => u p.1)) x := by
  rw [commK_mulVec]
  simp only [Matrix.mulVec, dotProduct, Kz_apply α q, Finset.univ_unique, Finset.sum_singleton]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [restrictField, DecCover.chiField]

/-- **Support of the commutator.** If `K_z u (x) ≠ 0` then `x` is an interior point of `□_z`. -/
theorem inner_of_Kz_ne_zero (S : CoverBase C H a ν Kc Cx) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ C.cubeIdx) (u : H.Ω 1 → ℂ) (x : H.Ω 1) (h : (Kz C H a ν q *ᵥ u) x ≠ 0) :
    Inner q x := by
  by_contra hI
  obtain ⟨-, hnK, -⟩ := H.layerIndex_spec x.2
  set n := H.layerIndex (x : CTorus d L N₁ m₁ K) with hn
  have hz : ∀ z : CTorus d L N₁ m₁ K,
      ((∃ μ : Fin d, z = (x : CTorus d L N₁ m₁ K) + Pi.single μ 1 ∨
        z = (x : CTorus d L N₁ m₁ K) - Pi.single μ 1) ∨ SameCell (L ^ n) (x : CTorus d L N₁ m₁ K) z) →
      C.chi q z = 0 := by
    intro z hnear
    by_contra hne
    exact hI (S.inner_near q hq x.2 hne hnear)
  have hx0 : C.chi q (x : CTorus d L N₁ m₁ K) = 0 := hz _ (Or.inr (SameCell.refl _ _))
  have e : ∀ z : CTorus d L N₁ m₁ K, C.chi q z = 0 → C.chiField q z = fun _ => 0 := by
    intro z hz0; funext i; unfold DecCover.chiField; rw [hz0]; simp
  apply h
  rw [Kz_mulVec_eq_commK (α := 0) q u x]
  refine commK_apply_eq_zero ν 0 _ x (fun μ => ?_) (fun y hy => ?_)
  · have h1 := hz _ (Or.inl ⟨μ, Or.inl rfl⟩)
    have h2 := hz _ (Or.inl ⟨μ, Or.inr rfl⟩)
    rw [e _ h1, e _ h2, e _ hx0]; exact ⟨rfl, rfl⟩
  · have hy' := H.mem_blk.1 hy
    have h1 := hz y (Or.inr (sameCell_of_jBlock_eq hnK hy'.symm))
    rw [e _ h1, e _ hx0]


/-- **Local bounds of the cube Green's function at an interior point** (the weighted (NC3) of
LOCALIZATION.md §3.1). -/
theorem cube_star (hd : 3 ≤ d) (hL : 3 ≤ L) (hKc : 0 ≤ Kc) :
    ∃ Bw : ℝ, 0 ≤ Bw ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, CoverBase C H a ν Kc Cx →
      ∀ {α : H.Ω 1 → ℂ}, AdmPot H α → ∀ {q : ℕ × CTorus d L N₁ m₁ K}, q ∈ C.cubeIdx →
      ∀ {w : CTorus d L N₁ m₁ K → ℝ}, IsWeight H (gammaW d) w →
      ∀ (g : H.Ω 1 → ℂ), (∀ z : H.Ω 1, g z ≠ 0 → (z : CTorus d L N₁ m₁ K) ∈ intBox q) →
      ∀ {Cb : ℝ}, 0 ≤ Cb →
      (∀ z : H.Ω 1, w z * (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖g z‖ ≤ Cb) →
      ∀ {x : H.Ω 1}, Inner q x →
      StarBd H (solExt H (cubeH H a ν α q)⁻¹ g) x
        (Bw * Cb * Real.exp (2 * gammaW d * d) / w x) := by
  obtain ⟨Bw, hBw, hW⟩ := cube_weighted (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc
  refine ⟨Bw, hBw, ?_⟩
  intro N₁ m₁ K _ ϱ C H a ν S α hα q hq w hw g hgsupp Cb hC hgC x hI
  have hd0 : 0 < d := by omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hρ := S.one_lt_rho
  have hγ0 := gammaW_nonneg hd0
  obtain ⟨hW1, hW2, hW3⟩ := hW C H S hα hq hw g hgsupp hC hgC
  have hwx := hw.pos x
  have hBC := mul_nonneg hBw hC
  set u : CTorus d L N₁ m₁ K → ℂ := solExt H (cubeH H a ν α q)⁻¹ g with hudef
  have hzero : ∀ y : CTorus d L N₁ m₁ K, y ∉ intBox q → u y = 0 := by
    intro y hy
    by_cases hyΩ : y ∈ H.Ω 1
    · have e : u y = ((cubeH H a ν α q)⁻¹ *ᵥ g) ⟨y, hyΩ⟩ := by
        simp [hudef, solExt, zeroExt, hyΩ]
      rw [e]
      have := cubeG_supp S hα hq g ⟨y, hyΩ⟩ hy
      have hcg : cD H q *ᵥ g = g := by
        funext z; rw [cD_mulVec]; by_cases hz : (z : CTorus d L N₁ m₁ K) ∈ intBox q
        · simp [hz]
        · have : g z = 0 := by_contra fun h => hz (hgsupp z h)
          simp [this]
      have hc : cubeG H a ν α q *ᵥ g = (cubeH H a ν α q)⁻¹ *ᵥ (cD H q *ᵥ g) := cubeG_mulVec q g
      rw [hcg] at hc
      rw [← hc]; exact this
    · exact zeroExt_not_mem _ _ hyΩ
  have hval : ∀ (y : CTorus d L N₁ m₁ K), y ∈ H.Ω 1 → ∀ {ρ : ℝ}, 0 ≤ ρ →
      H.pathDist x y ≤ ENNReal.ofReal ρ → ‖u y‖ ≤ Bw * Cb * Real.exp (gammaW d * ρ) / w x := by
    intro y hyΩ ρ hρ0 hdist
    have hwxy := hw.le_mul hγ0 hρ0 hdist
    rw [le_div_iff₀ hwx]
    by_cases hyb : y ∈ intBox q
    · have h1 := hW1 hyΩ hyb
      calc ‖u y‖ * w x ≤ ‖u y‖ * (w y * Real.exp (gammaW d * ρ)) :=
            mul_le_mul_of_nonneg_left hwxy (norm_nonneg _)
        _ = (w y * ‖u y‖) * Real.exp (gammaW d * ρ) := by ring
        _ ≤ Bw * Cb * Real.exp (gammaW d * ρ) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    · rw [hzero y hyb, norm_zero, zero_mul]
      exact mul_nonneg hBC (Real.exp_pos _).le
  have hVx : ∀ {ρ : ℝ}, 0 ≤ ρ → ρ ≤ 2 * d → Bw * Cb * Real.exp (gammaW d * ρ) / w x ≤
      Bw * Cb * Real.exp (2 * gammaW d * d) / w x := by
    intro ρ hρ0 hρ2
    apply div_le_div_of_nonneg_right _ hwx.le
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 _) hBC
    nlinarith
  set V : ℝ := Bw * Cb * Real.exp (2 * gammaW d * d) / w x with hV
  have hV0 : 0 ≤ V := by positivity
  have hVw : V * w x = Bw * Cb * Real.exp (2 * gammaW d * d) := by
    rw [hV]; field_simp
  have hxΩ : (x : CTorus d L N₁ m₁ K) ∈ H.Ω 1 := x.2
  have hxV : ‖u x‖ ≤ V := by
    refine (hval x hxΩ (le_refl 0) (by simp [H.pathDist_self hxΩ])).trans ?_
    simpa using hVx (le_refl 0) (by positivity)
  have hE1 : 1 ≤ Real.exp (2 * gammaW d * d) := Real.one_le_exp (by positivity)
  refine ⟨fun y hyΩ hdist => (hval y hyΩ (by positivity) hdist).trans
      (hVx (by positivity) le_rfl), fun μ => ?_, fun μ => ?_, ?_⟩
  · have h := hW2 hxΩ hI.self hI.add_single μ
    rw [← mul_le_mul_iff_of_pos_right hwx, hVw]
    nlinarith [mul_nonneg hBC (sub_nonneg.2 hE1)]
  · by_cases hyΩ : ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) ∈ H.Ω 1
    · set y : CTorus d L N₁ m₁ K := (x : CTorus d L N₁ m₁ K) - Pi.single μ 1 with hy
      have hadj : Adj y (x : CTorus d L N₁ m₁ K) := ⟨μ, Or.inl (by rw [hy]; simp)⟩
      have hyb : y ∈ intBox q := hI.sub_single μ
      have hye : ∀ ν' : Fin d, y + Pi.single ν' 1 ∈ intBox q := fun ν' => hI.sub_add_single μ ν'
      have h := hW2 hyΩ hyb hye μ
      have hyx : y + Pi.single μ 1 = (x : CTorus d L N₁ m₁ K) := by rw [hy]; simp
      rw [hyx] at h
      have hsp := spacing_adj_le H hρ.le hyΩ hxΩ hadj
      have hd1 := (H.pathDist_comm (x : CTorus d L N₁ m₁ K) y) ▸
        (H.pathDist_le_bondCost hyΩ hxΩ hadj |>.trans
          (ENNReal.ofReal_le_ofReal (H.bondCost_le_one hyΩ _)))
      have hwxy := hw.le_mul hγ0 zero_le_one hd1
      have hwy := hw.pos y
      change w y * (H.spacing y * ‖u (x : CTorus d L N₁ m₁ K) - u y‖) ≤ Bw * Cb at h
      have hnn := norm_nonneg (u y - u (x : CTorus d L N₁ m₁ K))
      rw [norm_sub_rev] at h
      rw [← mul_le_mul_iff_of_pos_right hwx]
      set Dn := ‖u y - u (x : CTorus d L N₁ m₁ K)‖ with hDn
      have hsp0 := (spacing_pos H (x := y)).le
      have hE : Real.exp (gammaW d * 1) ≤ Real.exp (2 * gammaW d * d) :=
        Real.exp_le_exp.2 (by
          have : (1 : ℝ) ≤ d := by exact_mod_cast hd0
          nlinarith)
      calc H.spacing (x : CTorus d L N₁ m₁ K) * Dn * w x
          ≤ (L * H.spacing y) * Dn * (w y * Real.exp (gammaW d * 1)) := by
            gcongr
        _ = L * Real.exp (gammaW d * 1) * (w y * (H.spacing y * Dn)) := by ring
        _ ≤ L * Real.exp (gammaW d * 1) * (Bw * Cb) := by
            gcongr
        _ ≤ L * Real.exp (2 * gammaW d * d) * (Bw * Cb) := by gcongr
        _ = L * V * w x := by rw [mul_assoc (L : ℝ) V, hVw]; ring
    · have hz : u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) = 0 := zeroExt_not_mem _ _ hyΩ
      rw [hz, zero_sub, norm_neg]
      have hadj : Adj (x : CTorus d L N₁ m₁ K) ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) :=
        ⟨μ, Or.inr (by simp)⟩
      have hsp := spacing_le_of_adj_not_mem H hρ (by omega : 1 ≤ L) hxΩ hyΩ hadj
      calc _ ≤ (L : ℝ) * ‖u x‖ := mul_le_mul_of_nonneg_right hsp (norm_nonneg _)
        _ ≤ L * V := mul_le_mul_of_nonneg_left hxV (by positivity)
  · have h := hW3 hxΩ hI.self (fun μ => ⟨hI.add_single μ, hI.sub_single μ⟩)
    rw [← mul_le_mul_iff_of_pos_right hwx, hVw]
    nlinarith [mul_nonneg hBC (sub_nonneg.2 hE1)]

/-- **The cut commutator on a cube solution, weighted.** For `f` with `w ℓ² |f| ≤ Cb`,
`w ℓ² |K_z H^{(z)} c_z f| ≤ B_K Cb / M₁`. -/
theorem Kz_cube_weighted (hd : 3 ≤ d) (hL : 3 ≤ L) (hKc : 0 ≤ Kc) (hCx : 0 ≤ Cx) :
    ∃ Bk : ℝ, 0 ≤ Bk ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, CoverBase C H a ν Kc Cx →
      ∀ {α : H.Ω 1 → ℂ}, AdmPot H α → ∀ {q : ℕ × CTorus d L N₁ m₁ K}, q ∈ C.cubeIdx →
      ∀ {w : CTorus d L N₁ m₁ K → ℝ}, IsWeight H (gammaW d) w →
      ∀ (f : H.Ω 1 → ℂ) {Cb : ℝ}, 0 ≤ Cb →
      (∀ x : H.Ω 1, w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ Cb) →
      ∀ x : H.Ω 1, w x * ((H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
        ‖((Kz C H a ν q * cubeG H a ν α q) *ᵥ f) x‖) ≤ Bk * Cb / (L : ℝ) ^ m₁ := by
  obtain ⟨Bw, hBw, hS⟩ := cube_star (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc
  refine ⟨commKConst d L 1 * Cx * Bw * Real.exp (2 * gammaW d * d), ?_, ?_⟩
  · have := hCx
    have : 0 ≤ commKConst d L 1 := by unfold commKConst; positivity
    positivity
  intro N₁ m₁ K _ ϱ C H a ν S α hα q hq w hw f Cb hC hfC x
  have hd0 : 0 < d := by omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hM0 : (0 : ℝ) < (L : ℝ) ^ m₁ := by positivity
  have hρ := S.one_lt_rho
  -- the source restricted to the cube
  set g : H.Ω 1 → ℂ := cD H q *ᵥ f with hgdef
  have hgsupp : ∀ z : H.Ω 1, g z ≠ 0 → (z : CTorus d L N₁ m₁ K) ∈ intBox q := by
    intro z hz
    by_contra hnb
    exact hz (by rw [hgdef, cD_mulVec]; simp [hnb])
  have hgC : ∀ z : H.Ω 1, w z * (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖g z‖ ≤ Cb := by
    intro z
    rw [hgdef, cD_mulVec]
    split_ifs
    · exact hfC z
    · simpa using hC
  have hu : cubeG H a ν α q *ᵥ f = (cubeH H a ν α q)⁻¹ *ᵥ g := cubeG_mulVec q f
  have hrw : ((Kz C H a ν q * cubeG H a ν α q) *ᵥ f) = Kz C H a ν q *ᵥ ((cubeH H a ν α q)⁻¹ *ᵥ g) := by
    rw [← Matrix.mulVec_mulVec, hu]
  rw [hrw]
  set u : H.Ω 1 → ℂ := (cubeH H a ν α q)⁻¹ *ᵥ g with hudef
  have hwx := hw.pos x
  have hBk0 : 0 ≤ commKConst d L 1 * Cx * Bw * Real.exp (2 * gammaW d * d) := by
    have := hCx
    have : 0 ≤ commKConst d L 1 := by unfold commKConst; positivity
    positivity
  by_cases hK0 : (Kz C H a ν q *ᵥ u) x = 0
  · rw [hK0]; simp only [norm_zero, mul_zero]
    positivity
  have hI := inner_of_Kz_ne_zero S hq u x hK0
  have hstar := hS C H S hα hq hw g hgsupp hC hgC hI
  obtain ⟨hn1, hnK, hxl⟩ := H.layerIndex_spec x.2
  set n := H.layerIndex (x : CTorus d L N₁ m₁ K) with hn
  set V : ℝ := Bw * Cb * Real.exp (2 * gammaW d * d) / w x with hV
  have hV0 : 0 ≤ V := by
    have := mul_nonneg hBw hC
    positivity
  have hVw : V * w x = Bw * Cb * Real.exp (2 * gammaW d * d) := by
    rw [hV]; field_simp
  have hsmooth := S.chi_smooth q hq
  have hδ : 0 ≤ Cx / (L : ℝ) ^ m₁ := div_nonneg (hCx) hM0.le
  have hloc := commK_local_bound H hd0 (by omega : 1 ≤ L) S.weights ν (0 : H.Ω 1 → ℂ) hsmooth hδ
    (fun p : H.Ω 1 × Fin 1 => u p.1) hV0 x
    (fun y hy i => by
      rw [svec_scalar]
      have hy' := H.mem_blk.1 hy
      have hyl : y ∈ H.layer n := (H.mem_layer_iff hn1 hnK hy').2 hxl
      have hyΩ : y ∈ H.Ω 1 := H.layer_subset hn1 hnK hyl
      exact hstar.val y hyΩ (H.pathDist_block_le hn1 hnK hxl hy'))
    (fun μ i => by simp only [svec_scalar]; exact hstar.fwd μ)
    (fun μ i => by simp only [svec_scalar]; exact hstar.bwd μ)
  rw [Kz_mulVec_eq_commK (α := 0) q u x]
  calc w x * (H.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖(commK (dirichletOperator H a ν 0)
        (restrictField H (C.chiField q)) *ᵥ fun p : H.Ω 1 × Fin 1 => u p.1) x‖)
      ≤ w x * (commKConst d L 1 * (Cx / (L : ℝ) ^ m₁) * V) :=
        mul_le_mul_of_nonneg_left hloc hwx.le
    _ = commKConst d L 1 * Cx * Bw * Real.exp (2 * gammaW d * d) * Cb / (L : ℝ) ^ m₁ := by
        rw [hV]; field_simp

/-- **(DG1)** `‖𝒦_s(A)‖ ≤ 1/4` in the weighted norm `|·|_{2,w}`, for `M₁ ≥ c_* e^{N₀ κ₁}`. -/
theorem dg1 (hd : 3 ≤ d) (hL : 3 ≤ L) (hKc : 0 ≤ Kc) (hCx : 0 ≤ Cx) :
    ∃ cstar : ℝ, 0 ≤ cstar ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, CoverBase C H a ν Kc Cx →
      ∀ {α : H.Ω 1 → ℂ}, AdmPot H α → ∀ {κ : ℝ}, 0 ≤ κ →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : ℕ × CTorus d L N₁ m₁ K → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ {w : CTorus d L N₁ m₁ K → ℝ}, IsWeight H (gammaW d) w →
      ∀ (f : H.Ω 1 → ℂ) {Cb : ℝ}, 0 ≤ Cb →
      (∀ x : H.Ω 1, w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ Cb) →
      ∀ x : H.Ω 1, w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
        ‖(Kcal C H a ν α s *ᵥ f) x‖ ≤ Cb / 4 := by
  obtain ⟨Bk, hBk, hK⟩ := Kz_cube_weighted (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  refine ⟨12 * 5 ^ d * Bk, by positivity, ?_⟩
  intro N₁ m₁ K _ ϱ C H a ν S α hα κ hκ hMκ s hs w hw f Cb hC hfC x
  classical
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hM0 : (0 : ℝ) < (L : ℝ) ^ m₁ := by positivity
  have hwx := hw.pos x
  have hsp := (spacing_pos H (x := (x : CTorus d L N₁ m₁ K))).le
  have hexp : 0 < Real.exp (N0 d L * κ) := Real.exp_pos _
  -- the sum over centres
  set T : (ℕ × CTorus d L N₁ m₁ K) → ℂ := fun q =>
    C.sProd s q * (((Kz C H a ν q * cubeG H a ν α q) *ᵥ f) x) with hT
  have hsum : (Kcal C H a ν α s *ᵥ f) x = ∑ q ∈ C.cubeIdx, T q := by
    unfold Kcal
    rw [Matrix.sum_mulVec, Finset.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  have hfilter : ∑ q ∈ (C.cubeIdx).filter (fun q => (x : CTorus d L N₁ m₁ K) ∈ intBox q), T q =
      ∑ q ∈ C.cubeIdx, T q := by
    refine Finset.sum_filter_of_ne fun q hq hne => ?_
    have h1 : (((Kz C H a ν q * cubeG H a ν α q) *ᵥ f) x) ≠ 0 := right_ne_zero_of_mul hne
    rw [← Matrix.mulVec_mulVec] at h1
    exact (inner_of_Kz_ne_zero S hq _ x h1).self
  have hcard := S.card_box _ x.2
  have hterm : ∀ q ∈ (C.cubeIdx).filter (fun q => (x : CTorus d L N₁ m₁ K) ∈ intBox q),
      w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖T q‖ ≤
        Real.exp (N0 d L * κ) * (Bk * Cb / (L : ℝ) ^ m₁) := by
    intro q hq
    have hqi := (Finset.mem_filter.1 hq).1
    have h1 := hK C H S hα hqi hw f hC hfC x
    have h2 := C.norm_sProd_le (S.card_qset q hqi) hκ hs
    calc w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖T q‖
        = ‖C.sProd s q‖ * (w x * ((H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
            ‖((Kz C H a ν q * cubeG H a ν α q) *ᵥ f) x‖)) := by
          rw [hT]; simp only [norm_mul]; ring
      _ ≤ Real.exp (N0 d L * κ) * (Bk * Cb / (L : ℝ) ^ m₁) :=
          mul_le_mul h2 h1 (by positivity) hexp.le
  rw [hsum, ← hfilter]
  calc w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
        ‖∑ q ∈ (C.cubeIdx).filter (fun q => (x : CTorus d L N₁ m₁ K) ∈ intBox q), T q‖
      ≤ w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
        ∑ q ∈ (C.cubeIdx).filter (fun q => (x : CTorus d L N₁ m₁ K) ∈ intBox q), ‖T q‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ q ∈ (C.cubeIdx).filter (fun q => (x : CTorus d L N₁ m₁ K) ∈ intBox q),
          w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖T q‖ := by rw [Finset.mul_sum]
    _ ≤ ∑ q ∈ (C.cubeIdx).filter (fun q => (x : CTorus d L N₁ m₁ K) ∈ intBox q),
          Real.exp (N0 d L * κ) * (Bk * Cb / (L : ℝ) ^ m₁) := Finset.sum_le_sum hterm
    _ = ((C.cubeIdx).filter (fun q => (x : CTorus d L N₁ m₁ K) ∈ intBox q)).card *
          (Real.exp (N0 d L * κ) * (Bk * Cb / (L : ℝ) ^ m₁)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * 5 ^ d) * (Real.exp (N0 d L * κ) * (Bk * Cb / (L : ℝ) ^ m₁)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
    _ ≤ Cb / 4 := by
        have h4 : 12 * 5 ^ d * Bk * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ := hMκ
        rw [show (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) * (Bk * Cb / (L : ℝ) ^ m₁)) =
          (3 * 5 ^ d * Bk * Real.exp (N0 d L * κ)) * Cb / (L : ℝ) ^ m₁ by ring]
        rw [div_le_iff₀ hM0]
        nlinarith [mul_le_mul_of_nonneg_right h4 hC]


end Balaban.Localization.Dec2
