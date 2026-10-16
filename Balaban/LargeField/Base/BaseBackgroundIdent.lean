/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseBackgroundLocal
public import Balaban.LargeField.Base.BaseSectorSupport
public import Balaban.LargeField.Base.BaseChartHessian

/-!
# The first step's background and operator are the level-one decoupled ones

The first step's background is the real minimizer `bgField`, with multiplier `bgMult`, of the
datum `baseSectorDatum ϱ θ h = liftSingle G θ h` of the single-scale generating set: the sector
variables `θ` are the block data `Ψ` (block-constant lift of `θ`) and `h` is the external field.
This file identifies it with the decoupled background `Dec2.IsDecBg` of the cover `coverOf G` at
`s ≡ 1` (Theorem I-4b with `Dec2.i4b_one` and `theorem72_real`), and the operator `H(1)` of the
first step with the Dirichlet operator of the `Dec2.Gs` fixed point at `s ≡ 1`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization

section Real

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}

/-- Real data of `Ψ̃(δ)` are complex data of `Ψ̃^c(δ, δ)` (with zero perturbations). -/
theorem inDomainC_of_inDomainR {ν δ : ℝ} (hδ : 0 < δ) {D : BgData G N}
    (hD : InDomainR G ν δ D) : InDomainC G ν δ δ D := by
  obtain ⟨Ψ, h, hP, hΨ, hh⟩ := hD
  have hL0 : ∀ {β : Type} (c : β), IsLayerConstant (G := G) (fun _ : Torus d (N₀ * L ^ k) => c) :=
    fun c _ _ _ _ _ _ _ => rfl
  have hz : vn (fun _ : Fin N => (0 : ℂ)) = 0 := by
    unfold vn
    exact norm_eq_zero.2 rfl
  refine ⟨Ψ, h, fun _ _ => 0, fun _ _ => 0, ?_, ?_, ?_⟩
  · refine
      { toInPsiTilde := hP
        eps_pos := hδ
        layerConst' := hL0 (fun _ : Fin N => (0 : ℂ))
        hLayerConst' := hL0 (fun _ : Fin N => (0 : ℂ))
        c1 := ?_, c2a := ?_, c2b := ?_, c3a := ?_, c3b := ?_ }
    · intro x x' _
      rw [sub_self]
      exact lt_of_eq_of_lt hz hδ
    · intro x _
      rw [hz]
      linarith
    · intro x _
      simpa using hδ
    · intro x _
      rw [hz, mul_zero]
      positivity
    · intro x _
      simp
      positivity
  · intro x hx i
    simpa using hΨ x hx i
  · intro x hx i
    simpa using hh x hx i

end Real

section Dec

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a₁ ν : ℝ} {Kc Cx : ℝ}

/-- **The first step's background is the decoupled background at `s ≡ 1`.**  For real data
`D ∈ Ψ̃(δ)` with `δ ≤ c₇` (the smallness of Theorem I-4b) the real minimizer `bgField` with
multiplier `bgMult` (the first step's `(e, α)`) satisfies `Dec2.IsDecBg` of the cover
`coverOf Gp` at `s ≡ 1`, and it is the only solution of that system. -/
theorem decBg_one_eq_bgField_of_inDomainR {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L K ϱ (compWeight L a₁) ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ0 : 0 < δ)
    (hδc : δ ≤ c7 d L N BG κ) {D : BgData Gp N} (hD : InDomainR Gp ν δ D) :
    Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) (fun _ => 1) D
      (bgField Gp (compWeight L a₁) ν D) (bgMult Gp (compWeight L a₁) ν D) ∧
    ∀ φ α, Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) (fun _ => 1) D φ α →
      φ = bgField Gp (compWeight L a₁) ν D ∧ α = bgMult Gp (compWeight L a₁) ν D := by
  have hd0 : 0 < d := by have := HBp.hd; omega
  have hDC := inDomainC_of_inDomainR hδ0 hD
  have hδ1 : δ ≤ bgC1 d L N := hδc.trans (c7_le_bgC1 d L N BG κ)
  have hδ0' : δ ≤ bgC0 d L N := hδ1.trans (bgC1_le_bgC0 d L N hd0)
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * δ ^ 2 ≤ δ ^ 2 := by
    have := HBp.massLe; nlinarith [sq_nonneg δ]
  have hone : ∀ P : ↥(coverOf Gp).cubeIdx,
      ‖(fun _ : ↥(coverOf Gp).cubeIdx => (1 : ℂ)) P‖ ≤ Real.exp κ :=
    fun P => by simpa using Real.one_le_exp hκ
  obtain ⟨φ, α, hI, hu, -⟩ := Dec2.i4b_exists_unique hS S HBp hκ hM hone hδ0 le_rfl hδ0' hδc hνε hDC
  obtain ⟨-, hφ1, hα1⟩ := Dec2.i4b_one hS S HBp hκ hM hδ0 le_rfl hδ0' hδc hνε hDC hI
  have hR := theorem72_real HBp (D := D) ⟨δ, hδ0, hδ1, hD⟩
  have hφ : φ = bgField Gp (compWeight L a₁) ν D := by rw [← hR.1, hφ1]
  have hα : α = bgMult Gp (compWeight L a₁) ν D := by rw [← hR.2, hα1]
  subst hφ hα
  exact ⟨hI, hu⟩

end Dec

section Single

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L]

/-- The single-scale generating set `Ω₁ = 𝕋` of the first step, on the step torus
`N₁ L^{m₁} L`, carries the parametrix setting `DGSetting` with the weights `compWeight L 1`. -/
theorem baseSingle_dgSetting (hd : 3 ≤ d) (hL : 3 ≤ L) (hM : 4 * L ^ 2 ≤ L ^ m₁) (hN₁ : 5 < N₁)
    {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ 2 ≤ 1) :
    DGSetting (GeneratingSet.single (d := d) (L := L) (N₀ := N₁ * L ^ m₁) (k := 1)
      (Inhabited.LevelStep.rhoSepG d L m₁)) (compWeight L 1) ν := by
  have hm2 : 2 ≤ m₁ := by
    by_contra h
    push Not at h
    have : L ^ m₁ ≤ L ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  exact
  { hd := hd
    hL := hL
    aligned :=
      { two_le := hm2
        dvd := dvd_mul_left _ _
        union := fun j _ hj x x' _ => by simp [GeneratingSet.single, singleΩ, hj] }
    hM := hM
    cover_sep := Inhabited.LevelStep.cover_le_rhoSepG m₁ hd hL
    sep := Inhabited.LevelStep.sep_le_rhoSepG m₁ hd hL
    weights := isAdmissibleWeights_compWeight hL (by norm_num) (by norm_num) _
    mass := hν0
    massLe := by simpa using hν
    big := hN₁ }

/-- **The first step's `(e, α)` at the single-scale generating set is the decoupled background of
the cover at `s ≡ 1`.**  The torus is the step torus `N₁ L^{m₁} L`; `D` is any real datum of
`Ψ̃(δ)`, in particular `D = liftSingle G θ h = baseSectorDatum` (block data `Ψ` the lift of the
sector variables `θ`, external field `h`), with `δ ≤ c₇`. -/
theorem baseSingle_decBg_one (hd : 3 ≤ d) (hL : 3 ≤ L) (hM : 4 * L ^ 2 ≤ L ^ m₁) (hN₁ : 5 < N₁)
    {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ 2 ≤ 1) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c BG) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMκ : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ0 : 0 < δ)
    (hδc : δ ≤ c7 d L N BG κ)
    {D : BgData (GeneratingSet.single (d := d) (L := L) (N₀ := N₁ * L ^ m₁) (k := 1)
      (Inhabited.LevelStep.rhoSepG d L m₁)) N}
    (hD : InDomainR (GeneratingSet.single (d := d) (L := L) (N₀ := N₁ * L ^ m₁) (k := 1)
      (Inhabited.LevelStep.rhoSepG d L m₁)) ν δ D) :
    Dec2.IsDecBg (coverOf (GeneratingSet.single (d := d) (L := L) (N₀ := N₁ * L ^ m₁) (k := 1)
      (Inhabited.LevelStep.rhoSepG d L m₁))) (GeneratingSet.single (d := d) (L := L)
      (N₀ := N₁ * L ^ m₁) (k := 1) (Inhabited.LevelStep.rhoSepG d L m₁)) (compWeight L 1) ν
      (rho4 d L N BG κ) (fun _ => 1) D
      (bgField _ (compWeight L 1) ν D) (bgMult _ (compWeight L 1) ν D) := by
  have S := baseSingle_dgSetting (N₁ := N₁) (m₁ := m₁) hd hL hM hN₁ hν0 hν
  have HB : BgHyp d L 1 (Inhabited.LevelStep.rhoSepG d L m₁) (compWeight L 1) ν :=
    Inhabited.LevelStep.bgHyp_lvG (k := 0) hd hL
      (Inhabited.LevelStep.bgR0_le_rhoSepG m₁ hd hL) hν0 (by simpa using hν)
  exact (decBg_one_eq_bgField_of_inDomainR hS (Dec2.coverBase_self S) HB hκ hMκ hδ0 hδc hD).1

end Single

section Operator

variable {d L N₀ N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The first step's operator `A_e = Q_e (H(1) ⊗ I) Q_e + P_e` with `H(1) = H_cut + ∑ T_b` is the
operator `A_e` built from the Dirichlet operator of the level-one step machinery. -/
theorem baseOp_baseHamiltonian_one (G : GeneratingSet d L N₀ 1 ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (α : G.Ω 1 → ℂ) (e : G.Ω 1 → Fin N → ℂ) :
    baseOp N e (baseHamiltonian G a ν α (fun _ => 1)) = baseOp N e (dirichletOperator G a ν α) := by
  rw [baseHamiltonian_one]

/-- The Dirichlet operator at one layer does not read the weight `a₀`: it depends on `a` only
through `a₁`. -/
theorem dirichletOperator_congr_weight (G : GeneratingSet d L N₀ 1 ϱ) {a a' : ℕ → ℝ}
    (h : a 1 = a' 1) (ν : ℝ) (α : G.Ω 1 → ℂ) :
    dirichletOperator G a ν α = dirichletOperator G a' ν α := by
  simp [dirichletOperator, fullMatrix, avgMatrix, h]

end Operator

section Fixed

variable {d L : ℕ} [NeZero L]

/-- **The `Dec2.Gs` fixed point at `s ≡ 1`, at the first step's multiplier, inverts the first
step's Dirichlet operator.**  For real data `D ∈ Ψ̃(δ)`, `δ ≤ c₇`, the multiplier `bgMult` of the
first step is admissible, `1 - 𝒦` is invertible, and `Gs(bgMult, s ≡ 1)` is the inverse of
`dirichletOperator G (compWeight L 1) ν (bgMult D)`. -/
theorem decGs_one_bgMult (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ cstar : ℝ, 0 ≤ cstar ∧ ∀ {N₁ m₁ N : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) {ν : ℝ},
      DGSetting G (compWeight L 1) ν →
      ∀ {c BG : ℝ}, Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c BG →
      BgHyp d L 1 ϱ (compWeight L 1) ν → ∀ {κ : ℝ}, 0 ≤ κ →
      c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ → cstar ≤ (L : ℝ) ^ m₁ →
      ∀ {δ : ℝ}, 0 < δ → δ ≤ c7 d L N BG κ → ∀ {D : BgData G N}, InDomainR G ν δ D →
      IsUnit (1 - Dec2.Kcal (coverOf G) G (compWeight L 1) ν
        (bgMult G (compWeight L 1) ν D) (fun _ => 1)) ∧
      Dec2.Gs (coverOf G) G (compWeight L 1) ν (bgMult G (compWeight L 1) ν D) (fun _ => 1) =
        (dirichletOperator G (compWeight L 1) ν (bgMult G (compWeight L 1) ν D))⁻¹ := by
  obtain ⟨cstar, hc, H⟩ := baseParametrix_one (d := d) (L := L) hd hL
  refine ⟨cstar, hc, ?_⟩
  intro N₁ m₁ N _ ϱ G ν S c BG hS HB κ hκ hMκ hcs δ hδ0 hδc D hD
  have hd0 : 0 < d := by omega
  have hB := (decBg_one_eq_bgField_of_inDomainR hS (Dec2.coverBase_self S) HB hκ hMκ hδ0 hδc hD).1
  have hg := gamma1_pos hd0
  have hle : rho4 d L N BG κ ≤ gamma1 d / 8 := by
    unfold rho4 c6'
    exact (min_le_left _ _).trans (by linarith)
  have hα : AdmPot G (bgMult G (compWeight L 1) ν D) :=
    admPot_of_small hd0 (fun x => (hB.small x).trans hle)
  obtain ⟨hU, h⟩ := H G S hα hcs
  rw [baseHamiltonian_one] at h
  exact ⟨hU, h⟩

end Fixed

end Balaban.LargeField.Base
