/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseParametrix
public import Balaban.Inhabited.LevelPairGeneral
public import Balaban.Localization.DecoupledCovAnalyticFull
public import Balaban.Localization.Decoupled2Field

/-!
# The first step through the decoupled parametrix: inhabitation and the constrained covariance

* `baseDGSetting_exists`: the setting `DGSetting G a ν` of the parametrix theorems of
  `BaseParametrix.lean` is inhabited at one layer (`K = 1`) by the whole level, for every
  `d ≥ 3`, `L ≥ 3`, `4 L² ≤ L ^ m₁`, `5 < N₁`, `0 ≤ ν`, `ν L² ≤ 1`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Matrix

/-- **The parametrix setting at one layer is inhabited.**  The whole level `Ω₁ = Ω_j = torus`
(`j ≤ 1`) is cube aligned, and carries the weights `Background.compWeight L 1`. -/
theorem baseDGSetting_exists {d L N₁ m₁ : ℕ} [NeZero L] [NeZero N₁] (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hN₁ : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ 2 ≤ 1) :
    ∃ G : GeneratingSet d L (N₁ * L ^ m₁) 1 (Inhabited.LevelStep.rhoSepG d L m₁),
      G.Ω 1 = Finset.univ ∧ DGSetting G (Background.compWeight L 1) ν := by
  have hm2 : 2 ≤ m₁ := by
    by_contra h
    push Not at h
    have : L ^ m₁ ≤ L ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  refine ⟨Inhabited.LevelStep.lvTopG d L N₁ m₁ 0 _, by simp [Inhabited.LevelStep.lvTopG_Ω], ?_⟩
  exact
  { hd := hd
    hL := hL
    aligned :=
      { two_le := hm2
        dvd := dvd_mul_left _ _
        union := fun j _ hj x x' _ => by simp [Inhabited.LevelStep.lvTopG_Ω, hj] }
    hM := hM
    cover_sep := Inhabited.LevelStep.cover_le_rhoSepG m₁ hd hL
    sep := Inhabited.LevelStep.sep_le_rhoSepG m₁ hd hL
    weights := Background.isAdmissibleWeights_compWeight hL (by norm_num) (by norm_num) _
    mass := hν0
    massLe := by simpa using hν
    big := hN₁ }


/-! ### Sup bounds of the parametrix on vector fields -/

section Sup

variable {d L : ℕ} [NeZero L]

/-- In the parametrix setting the separation exceeds one. -/
theorem one_lt_rho_of_dgSetting {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}
    {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {ν : ℝ} (S : DGSetting G a ν) :
    1 < ϱ := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by have := S.hL; omega : 1 < L)
  have h1 := agmonRate_pos hd0
  have h2 := Real.log_pos hL1
  have h3 := S.sep
  by_contra h
  push Not at h
  have h4 : agmonRate d / 16 * (ϱ - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have h5 : 0 < 2 * (d : ℝ) * Real.log L := by positivity
  linarith

/-- **Sup bounds of `Ĝ_s g` on the whole admissible potential disc.**  Value, forward and
backward gradients and Laplacian of `liftOp N (Gs_s α) g` are at most `B e^{N₀ κ} C` when
`|g|₂ ≤ C`, for every admissible `α` and `|s_P| ≤ e^κ`. -/
theorem baseParametrix_supBounds (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ cstar B : ℝ, 0 ≤ cstar ∧ 0 ≤ B ∧ ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {κ : ℝ}, 0 ≤ κ →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ {N : ℕ} (g : G.Ω 1 × Fin N → ℂ) {Cb : ℝ}, 0 ≤ Cb → Balaban.Background.SrcBound G g Cb →
      SupBounds G (liftOp N (Dec2.Gs (coverOf G) G a ν α s) *ᵥ g)
        (B * Real.exp (N0 d L * κ) * Cb) := by
  obtain ⟨cstar, BG, hc, hB, H⟩ := Dec2.dg2_sup (d := d) (L := L) (Kc := Dec2.selfKc d L)
    (Cx := Cchi d L) hd hL (Dec2.selfKc_nonneg hd hL) (Cchi_nonneg d L)
  refine ⟨cstar, L * BG, hc, by positivity, ?_⟩
  intro N₁ m₁ _ ϱ G a ν S α hα κ hκ hM s hs N g Cb hC hg
  have hd0 : 0 < d := by omega
  have hb : 0 ≤ BG * Real.exp (N0 d L * κ) := by positivity
  have h := supBounds_liftOp (N := N) (G := G) (M := Dec2.Gs (coverOf G) G a ν α s)
    (one_lt_rho_of_dgSetting S) (by omega) hb
    (fun f C' hC' hf => (H (coverOf G) G (Dec2.coverBase_self S) hα hκ hM hs
      (w := fun _ => 1) (IsWeight.one G (gammaW_nonneg hd0)) f hC'
      (fun x => by simpa using hf x)).2) g hC hg
  refine h.mono (le_of_eq ?_)
  ring

end Sup


/-! ### Invertibility of the constraint matrix `M` -/

section Unit

variable {d L : ℕ} [NeZero L]

/-- **The constraint matrix `M = φ₀² - K(φ₀) Ĝ_s φ₀` is invertible** on the whole disc `|s_P| ≤ e^κ`
and for every admissible potential, when the constraint field is `δ`-close to the constraint
(`IsConstraintField`) with `δ ≤ δ_*(d, L, N, κ)`.  Here `Ĝ_s` is the parametrix and `K(φ₀)` the
commutator with the first-step Dirichlet operator.  (The step's `decM_isUnit` is the same
statement for the x-variant; the proof here uses the sup bounds of the parametrix.) -/
theorem baseConstraint_isUnit (hd : 3 ≤ d) (hL : 3 ≤ L) (N : ℕ) :
    ∃ cstar : ℝ, 0 ≤ cstar ∧ ∀ {κ : ℝ}, 0 ≤ κ → ∃ δs : ℝ, 0 < δs ∧
      ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ {δ : ℝ}, 0 ≤ δ → δ ≤ δs →
      ∀ {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}, IsConstraintField G δ φ →
      IsUnit (constraintM (dirichletOperator G a ν α) (Dec2.Gs (coverOf G) G a ν α s)
        (restrictField G φ)) := by
  obtain ⟨cstar, B, hc, hB, H⟩ := baseParametrix_supBounds (d := d) (L := L) hd hL
  refine ⟨cstar, hc, fun {κ} hκ => ?_⟩
  have hcK : 0 ≤ commKConst d L N := by unfold commKConst; positivity
  set c0 : ℝ := 1 + commKConst d L N * (B * Real.exp (N0 d L * κ) * (3 / 2)) with hc0
  have hc01 : 1 ≤ c0 := by
    have : 0 ≤ commKConst d L N * (B * Real.exp (N0 d L * κ) * (3 / 2)) := by positivity
    rw [hc0]; linarith
  have hc0p : 0 < c0 := by linarith
  refine ⟨1 / (2 * c0), by positivity, ?_⟩
  intro N₁ m₁ _ ϱ G a ν S α hα hM s hs δ hδ hδs φ hφ
  have hd0 : 0 < d := by omega
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro f f' hff
  have hz : constraintM (dirichletOperator G a ν α) (Dec2.Gs (coverOf G) G a ν α s)
      (restrictField G φ) *ᵥ (f - f') = 0 := by
    rw [Matrix.mulVec_sub, hff, sub_self]
  refine sub_eq_zero.1 ?_
  generalize f - f' = z at hz
  by_cases hne : (Finset.univ : Finset (G.Ω 1)).Nonempty
  · obtain ⟨x0, -, hx0⟩ := Finset.exists_max_image Finset.univ
      (fun x : G.Ω 1 => (G.spacing (x : Balaban.Localization.CTorus d L N₁ m₁ 1)) ^ 2 * ‖z x‖) hne
    set C : ℝ := (G.spacing (x0 : Balaban.Localization.CTorus d L N₁ m₁ 1)) ^ 2 * ‖z x0‖ with hC
    have hsp : ∀ x : G.Ω 1, 0 < (G.spacing (x : Balaban.Localization.CTorus d L N₁ m₁ 1)) ^ 2 := by
      intro x
      have := spacing_pos G (x := (x : Balaban.Localization.CTorus d L N₁ m₁ 1))
      positivity
    have hC0 : 0 ≤ C := by have := hsp x0; positivity
    have hsrc : Balaban.Background.SrcBound G (fieldMul (restrictField G φ) *ᵥ z) (3 / 2 * C) := by
      intro x i
      rw [fieldMul_mulVec, norm_mul]
      have h1 : ‖restrictField G φ x i‖ ≤ 3 / 2 :=
        (norm_le_vn (φ x) i).trans (hφ.bound x x.2)
      have h2 := hx0 x (Finset.mem_univ _)
      calc _ = ‖φ x i‖ * ((G.spacing (x : Balaban.Localization.CTorus d L N₁ m₁ 1)) ^ 2 * ‖z x‖) := by
            simp only [restrictField]; ring
        _ ≤ 3 / 2 * C := mul_le_mul h1 h2 (by have := hsp x; positivity) (by norm_num)
    have hstar := Balaban.Background.SupBounds.star
      (H G S hα hκ hM hs (fieldMul (restrictField G φ) *ᵥ z) (by positivity) hsrc)
    have hK := Balaban.Background.commK_bound (G := G) hd0 (by omega) S.weights ν α hφ.toIsSmoothField hδ
      (by positivity) hstar x0
    have hid := congrFun (constraintM_mulVec_gen (G := G) (φ := φ)
      (dirichletOperator G a ν α) (Dec2.Gs (coverOf G) G a ν α s) z) x0
    rw [hz] at hid
    simp only [Pi.sub_apply, Pi.zero_apply, Pi.add_apply] at hid
    have hz0 : z x0 = (1 - ∑ i, φ x0 i * φ x0 i) * z x0 +
        (commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ
          (liftOp N (Dec2.Gs (coverOf G) G a ν α s) *ᵥ (fieldMul (restrictField G φ) *ᵥ z))) x0 := by
      have := hid
      linear_combination this
    have hsq : ‖1 - ∑ i, φ x0 i * φ x0 i‖ ≤ δ := by
      rw [norm_sub_rev]; exact hφ.sq x0 x0.2
    have hp0 := hsp x0
    have hbound : C ≤ δ * C + commKConst d L N * δ * (B * Real.exp (N0 d L * κ) * (3 / 2 * C)) := by
      have e1 : C = (G.spacing (x0 : Balaban.Localization.CTorus d L N₁ m₁ 1)) ^ 2 * ‖z x0‖ := hC
      calc C = (G.spacing (x0 : Balaban.Localization.CTorus d L N₁ m₁ 1)) ^ 2 *
            ‖(1 - ∑ i, φ x0 i * φ x0 i) * z x0 +
              (commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ
                (liftOp N (Dec2.Gs (coverOf G) G a ν α s) *ᵥ
                  (fieldMul (restrictField G φ) *ᵥ z))) x0‖ := by rw [e1, ← hz0]
        _ ≤ (G.spacing (x0 : Balaban.Localization.CTorus d L N₁ m₁ 1)) ^ 2 *
            (‖1 - ∑ i, φ x0 i * φ x0 i‖ * ‖z x0‖ +
            ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ
                (liftOp N (Dec2.Gs (coverOf G) G a ν α s) *ᵥ
                  (fieldMul (restrictField G φ) *ᵥ z))) x0‖) := by
            refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) hp0.le
            rw [norm_mul]
        _ = ‖1 - ∑ i, φ x0 i * φ x0 i‖ * C +
            (G.spacing (x0 : Balaban.Localization.CTorus d L N₁ m₁ 1)) ^ 2 *
            ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ
                (liftOp N (Dec2.Gs (coverOf G) G a ν α s) *ᵥ
                  (fieldMul (restrictField G φ) *ᵥ z))) x0‖ := by rw [e1]; ring
        _ ≤ δ * C + commKConst d L N * δ * (B * Real.exp (N0 d L * κ) * (3 / 2 * C)) :=
            add_le_add (mul_le_mul_of_nonneg_right hsq hC0) hK
    have hsmall : δ * c0 ≤ 1 / 2 := by
      calc δ * c0 ≤ 1 / (2 * c0) * c0 := mul_le_mul_of_nonneg_right hδs hc0p.le
        _ = 1 / 2 := by field_simp
    have hCle : C ≤ 1 / 2 * C := by
      calc C ≤ _ := hbound
        _ = δ * c0 * C := by rw [hc0]; ring
        _ ≤ 1 / 2 * C := mul_le_mul_of_nonneg_right hsmall hC0
    have hCz : C = 0 := by linarith
    funext x
    have h1 := hx0 x (Finset.mem_univ _)
    have h2 : (G.spacing (x : Balaban.Localization.CTorus d L N₁ m₁ 1)) ^ 2 * ‖z x‖ = 0 := by
      have := mul_nonneg (hsp x).le (norm_nonneg (z x))
      linarith
    have h3 := (mul_eq_zero.1 h2).resolve_left (hsp x).ne'
    simpa using h3
  · funext x
    exact absurd ⟨x, Finset.mem_univ _⟩ hne

end Unit


/-! ### Holomorphy of the constrained covariance on the full discs -/

section Analytic

variable {d L : ℕ} [NeZero L]

/-- **The first-step constrained covariance through the parametrix is holomorphic on the full
H7 discs.**  The covariance is `P_e + Ĝ_s - Ĝ_s φ₀ M⁻¹ N` (the step's `P + Ĝ - Π`), with `Ĝ_s` the
parametrix, `M = φ₀² - K(φ₀) Ĝ_s φ₀`, `N = φ₀ - K(φ₀) Ĝ_s` and `P_e = φ₀ φ₀ᵀ`.  Every entry is
analytic in `(s, φ₀, α)` on `DecDom G N κ δ`: the polydisc `|s_P| < e^κ` (any `κ ≥ 0` with
`c_* e^{N₀ κ} ≤ L^{m₁}`), the strict constraint field conditions and the strict potential bound,
for `δ ≤ δ_*(d, L, N, κ)`. -/
theorem baseConstrainedCov_analytic (hd : 3 ≤ d) (hL : 3 ≤ L) (N : ℕ) :
    ∃ cstar : ℝ, 0 ≤ cstar ∧ ∀ {κ : ℝ}, 0 ≤ κ → ∃ δs : ℝ, 0 < δs ∧
      ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {δ : ℝ}, 0 ≤ δ → δ ≤ δs → ∀ (x y : G.Ω 1 × Fin N),
      AnalyticOnNhd ℂ
        (fun p : DecData G N =>
          (basePart (restrictField G p.2.1) +
            liftOp N (Dec2.Gs (coverOf G) G a ν p.2.2 (Dec2.extS (coverOf G) p.1)) -
            liftOp N (Dec2.Gs (coverOf G) G a ν p.2.2 (Dec2.extS (coverOf G) p.1)) *
              fieldMul (restrictField G p.2.1) *
              (constraintM (dirichletOperator G a ν p.2.2)
                (Dec2.Gs (coverOf G) G a ν p.2.2 (Dec2.extS (coverOf G) p.1))
                (restrictField G p.2.1))⁻¹ *
              constraintN (dirichletOperator G a ν p.2.2)
                (Dec2.Gs (coverOf G) G a ν p.2.2 (Dec2.extS (coverOf G) p.1))
                (restrictField G p.2.1)) x y)
        (DecDom G N κ δ) := by
  obtain ⟨c1, hc1, H1⟩ := baseParametrix_analytic (d := d) (L := L) hd hL
  obtain ⟨c2, hc2, H2⟩ := baseConstraint_isUnit (d := d) (L := L) hd hL N
  refine ⟨max c1 c2, le_max_of_le_left hc1, fun {κ} hκ => ?_⟩
  obtain ⟨δs, hδs, H3⟩ := H2 hκ
  refine ⟨δs, hδs, ?_⟩
  intro N₁ m₁ _ ϱ G a ν S hM δ hδ hδδs x y e he
  have hE : 0 < Real.exp (N0 d L * κ) := Real.exp_pos _
  have hM1 : c1 * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hE.le) hM
  have hM2 : c2 * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hE.le) hM
  have hα : AdmPot G e.2.2 := fun w => (he.2.2 w).le
  have hs : ∀ P, ‖Dec2.extS (coverOf G) e.1 P‖ ≤ Real.exp κ := by
    intro P
    unfold Dec2.extS
    split_ifs with h
    · exact (he.1 ⟨P, h⟩).le
    · simpa using Real.one_le_exp hκ
  have hpr : AnalyticAt ℂ (fun p : DecData G N => ((p.1, p.2.2) : DecParams G × (G.Ω 1 → ℂ))) e :=
    AnalyticAt.prod analyticAt_fst (analyticAt_snd.comp analyticAt_snd)
  have hGs : RectAt (fun p : DecData G N =>
      Dec2.Gs (coverOf G) G a ν p.2.2 (Dec2.extS (coverOf G) p.1)) e := by
    intro i j
    have h0 := H1 G S hκ hM1 i j ((e.1, e.2.2) : Dec2.DecParams (coverOf G) × (G.Ω 1 → ℂ))
      ⟨he.1, he.2.2⟩
    have hpr' : AnalyticAt ℂ (fun p : DecData G N =>
        ((p.1, p.2.2) : Dec2.DecParams (coverOf G) × (G.Ω 1 → ℂ))) e :=
      AnalyticAt.prod analyticAt_fst (analyticAt_snd.comp analyticAt_snd)
    exact h0.comp (f := fun p : DecData G N =>
      ((p.1, p.2.2) : Dec2.DecParams (coverOf G) × (G.Ω 1 → ℂ))) (x := e) hpr'
  have hdiag : RectAt (fun p : DecData G N => Matrix.diagonal p.2.2) e :=
    RectAt.comp' (f := fun p : DecData G N => ((p.1, p.2.2) : DecParams G × (G.Ω 1 → ℂ)))
      (rectAt_diagonal ((e.1, e.2.2) : DecParams G × (G.Ω 1 → ℂ))) hpr
  have hHd : RectAt (fun p : DecData G N => dirichletOperator G a ν p.2.2) e := by
    have : (fun p : DecData G N => dirichletOperator G a ν p.2.2) =
        fun p => dirichletOperator G a ν 0 + Matrix.diagonal p.2.2 := by
      funext p; exact dirichletOperator_eq_add a ν p.2.2
    rw [this]
    exact (RectAt.const _ e).add hdiag
  have hGl := hGs.liftOp (N := N)
  have hHl := hHd.liftOp (N := N)
  have hF := rectAt_fieldMul (G := G) (N := N) e
  have hK : RectAt (fun p : DecData G N =>
      commK (dirichletOperator G a ν p.2.2) (restrictField G p.2.1)) e := by
    unfold commK
    exact (hF.transpose'.mul hHl).sub (hHd.mul hF.transpose')
  have hMa : RectAt (fun p : DecData G N =>
      constraintM (dirichletOperator G a ν p.2.2)
        (Dec2.Gs (coverOf G) G a ν p.2.2 (Dec2.extS (coverOf G) p.1))
        (restrictField G p.2.1)) e := by
    unfold constraintM
    exact (hF.transpose'.mul hF).sub ((hK.mul hGl).mul hF)
  have hNa : RectAt (fun p : DecData G N =>
      constraintN (dirichletOperator G a ν p.2.2)
        (Dec2.Gs (coverOf G) G a ν p.2.2 (Dec2.extS (coverOf G) p.1))
        (restrictField G p.2.1)) e := by
    unfold constraintN
    exact hF.transpose'.sub (hK.mul hGl)
  have hdet : (constraintM (dirichletOperator G a ν e.2.2)
      (Dec2.Gs (coverOf G) G a ν e.2.2 (Dec2.extS (coverOf G) e.1))
      (restrictField G e.2.1)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1
      (H3 G S hα hM2 hs hδ hδδs he.2.1.toIsConstraintField)).ne_zero
  have hMi := hMa.inv hdet
  have hP : RectAt (fun p : DecData G N => basePart (restrictField G p.2.1)) e := by
    unfold basePart
    exact hF.mul hF.transpose'
  exact ((hP.add hGl).sub (((hGl.mul hF).mul hMi).mul hNa)) x y

end Analytic


/-! ### The constrained covariance inverts `A_e` -/

section Inverse

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

theorem fieldMul_transpose_mul_self {e : ι → Fin N → ℂ} (he : ∀ z, ∑ i, e z i * e z i = 1) :
    (fieldMul e)ᵀ * fieldMul e = 1 := by
  ext z z'
  simp only [Matrix.mul_apply, transpose_apply, fieldMul, Fintype.sum_prod_type, one_apply]
  by_cases h : z = z'
  · subst h
    simp [he z]
  · simp [h, Ne.symm h]

theorem ring_aux {R : Type*} [Ring R] (P Hl Gl T : R) (hHG : Hl * Gl = 1) (hPP : P * P = P)
    (hPGT : P * Gl * T = P) (hPT : P * T = T) :
    ((1 - P) * Hl * (1 - P) + P) * (P + Gl - Gl * T * Gl) = 1 := by
  have hQT : (1 - P) * T = 0 := by rw [sub_mul, one_mul, hPT, sub_self]
  have hPG : P * (Gl * T * Gl) = P * Gl := by
    rw [← mul_assoc, ← mul_assoc, mul_assoc P Gl T, ← mul_assoc, hPGT]
  have hHG' : Hl * (Gl * T * Gl) = T * Gl := by
    rw [← mul_assoc, ← mul_assoc, hHG, one_mul]
  have h1 : (1 - P) * (P + Gl - Gl * T * Gl) = Gl - Gl * T * Gl := by
    have : (1 - P) * (P + Gl - Gl * T * Gl) =
        P + Gl - Gl * T * Gl - (P * P + P * Gl - P * (Gl * T * Gl)) := by noncomm_ring
    rw [this, hPP, hPG]; abel
  have h2 : Hl * (Gl - Gl * T * Gl) = 1 - T * Gl := by rw [mul_sub, hHG, hHG']
  have h3 : (1 - P) * (1 - T * Gl) = 1 - P := by
    rw [mul_sub, mul_one, ← mul_assoc, hQT, zero_mul, sub_zero]
  have h4 : P * (P + Gl - Gl * T * Gl) = P := by
    rw [mul_sub, mul_add, hPP, hPG]; abel
  have h5 : ((1 - P) * Hl * (1 - P) + P) * (P + Gl - Gl * T * Gl) =
      (1 - P) * (Hl * ((1 - P) * (P + Gl - Gl * T * Gl))) + P * (P + Gl - Gl * T * Gl) := by
    noncomm_ring
  rw [h5, h1, h2, h3, h4]
  abel

/-- **The constrained covariance is the inverse of `A_e`.**  For an exact constraint field
(`∑ᵢ e_z,i² = 1`), `H G = G H = 1` and `M = e² - K(e) Ĝ e` invertible, the matrix
`P_e + Ĝ - Ĝ e M⁻¹ N` is the two-sided inverse of `A_e = Q_e Ĥ Q_e + P_e`. -/
theorem baseOp_mul_constrainedCov {H G : Matrix ι ι ℂ} (hHG : H * G = 1) (hGH : G * H = 1)
    {e : ι → Fin N → ℂ} (he : ∀ z, ∑ i, e z i * e z i = 1) (hM : IsUnit (constraintM H G e)) :
    baseOp N e H * (basePart e + liftOp N G -
        liftOp N G * fieldMul e * (constraintM H G e)⁻¹ * constraintN H G e) = 1 ∧
      (basePart e + liftOp N G -
        liftOp N G * fieldMul e * (constraintM H G e)⁻¹ * constraintN H G e) * baseOp N e H = 1 := by
  have hE := fieldMul_transpose_mul_self he
  have hW : IsUnit (constraintForm G e) := by
    rw [constraintForm_eq_mul hHG hGH e]
    exact IsUnit.mul (show IsUnit G from ⟨⟨G, H, hGH, hHG⟩, rfl⟩) hM
  have hWi : constraintForm G e * (constraintForm G e)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hW)
  have hCov : liftOp N G * fieldMul e * (constraintM H G e)⁻¹ * constraintN H G e =
      liftOp N G * (fieldMul e * (constraintForm G e)⁻¹ * (fieldMul e)ᵀ) * liftOp N G := by
    rw [← constrainedOp_eq hHG hGH e]
    unfold constrainedOp
    simp only [Matrix.mul_assoc]
  have hHl : liftOp N H * liftOp N G = 1 := by rw [← liftOp_mul, hHG, liftOp_one]
  have key : baseOp N e H * (basePart e + liftOp N G -
        liftOp N G * fieldMul e * (constraintM H G e)⁻¹ * constraintN H G e) = 1 := by
    rw [hCov]
    unfold baseOp basePart
    refine ring_aux _ _ _ _ hHl ?_ ?_ ?_
    · calc fieldMul e * (fieldMul e)ᵀ * (fieldMul e * (fieldMul e)ᵀ)
          = fieldMul e * ((fieldMul e)ᵀ * fieldMul e) * (fieldMul e)ᵀ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hE, Matrix.mul_one]
    · calc fieldMul e * (fieldMul e)ᵀ * liftOp N G *
            (fieldMul e * (constraintForm G e)⁻¹ * (fieldMul e)ᵀ)
          = fieldMul e * (constraintForm G e * (constraintForm G e)⁻¹) * (fieldMul e)ᵀ := by
            unfold constraintForm
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hWi, Matrix.mul_one]
    · calc fieldMul e * (fieldMul e)ᵀ * (fieldMul e * (constraintForm G e)⁻¹ * (fieldMul e)ᵀ)
          = fieldMul e * ((fieldMul e)ᵀ * fieldMul e) * (constraintForm G e)⁻¹ * (fieldMul e)ᵀ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hE, Matrix.mul_one]
  exact ⟨key, mul_eq_one_comm.1 key⟩

end Inverse


/-! ### The physical point `s ≡ 1` -/

section Physical

variable {d L : ℕ} [NeZero L]

/-- The constant family `s ≡ 1` extended by `1` is `fun _ => 1`. -/
theorem extS_const_one {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ} (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) :
    Dec2.extS (coverOf G) (fun _ => (1 : ℂ)) = fun _ => 1 := by
  funext q
  unfold Dec2.extS
  split_ifs <;> rfl

/-- **At the physical point the constrained covariance is `A_e⁻¹`.**  For an exact constraint
field `e = φ₀|_{Ω₁}` (`∑ᵢ e_z,i² = 1`, `δ`-smooth with `δ ≤ δ_*`), an admissible potential and
`c_* ≤ L^{m₁}`, the parametrix covariance `P_e + Ĝ_1 - Ĝ_1 e M⁻¹ N` at `s ≡ 1` is the two-sided
inverse of the first-step operator `A_e = Q_e (H(1) ⊗ I) Q_e + P_e` of `baseOp`, with
`H(1) = baseHamiltonian G a ν α 1`. -/
theorem baseConstrainedCov_one (hd : 3 ≤ d) (hL : 3 ≤ L) (N : ℕ) :
    ∃ cstar δs : ℝ, 0 ≤ cstar ∧ 0 < δs ∧ ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → cstar ≤ (L : ℝ) ^ m₁ →
      ∀ {δ : ℝ}, 0 ≤ δ → δ ≤ δs →
      ∀ {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}, IsConstraintField G δ φ →
      (∀ x : G.Ω 1, ∑ i, φ x i * φ x i = 1) →
      baseOp N (restrictField G φ) (baseHamiltonian G a ν α (fun _ => 1)) *
        (basePart (restrictField G φ) +
          liftOp N (Dec2.Gs (coverOf G) G a ν α (fun _ => 1)) -
          liftOp N (Dec2.Gs (coverOf G) G a ν α (fun _ => 1)) * fieldMul (restrictField G φ) *
          (constraintM (dirichletOperator G a ν α) (Dec2.Gs (coverOf G) G a ν α (fun _ => 1))
            (restrictField G φ))⁻¹ *
          constraintN (dirichletOperator G a ν α) (Dec2.Gs (coverOf G) G a ν α (fun _ => 1))
            (restrictField G φ)) = 1 ∧
      (basePart (restrictField G φ) +
          liftOp N (Dec2.Gs (coverOf G) G a ν α (fun _ => 1)) -
          liftOp N (Dec2.Gs (coverOf G) G a ν α (fun _ => 1)) * fieldMul (restrictField G φ) *
          (constraintM (dirichletOperator G a ν α) (Dec2.Gs (coverOf G) G a ν α (fun _ => 1))
            (restrictField G φ))⁻¹ *
          constraintN (dirichletOperator G a ν α) (Dec2.Gs (coverOf G) G a ν α (fun _ => 1))
            (restrictField G φ)) *
        baseOp N (restrictField G φ) (baseHamiltonian G a ν α (fun _ => 1)) = 1 := by
  obtain ⟨c1, hc1, H1⟩ := baseParametrix_one (d := d) (L := L) hd hL
  obtain ⟨c2, hc2, H2⟩ := baseConstraint_isUnit (d := d) (L := L) hd hL N
  obtain ⟨δs, hδs, H3⟩ := H2 (κ := 0) le_rfl
  refine ⟨max c1 c2, δs, le_max_of_le_left hc1, hδs, ?_⟩
  intro N₁ m₁ _ ϱ G a ν S α hα hM δ hδ hδδs φ hφ hsq
  have hd0 : 0 < d := by omega
  have hM1 : c1 ≤ (L : ℝ) ^ m₁ := le_trans (le_max_left _ _) hM
  have hM2 : c2 * Real.exp (N0 d L * 0) ≤ (L : ℝ) ^ m₁ := by
    simpa using le_trans (le_max_right _ _) hM
  obtain ⟨-, hG1⟩ := H1 G S hα hM1
  rw [baseHamiltonian_one] at hG1
  have hHu : IsUnit (dirichletOperator G a ν α) :=
    dirichletOperator_isUnit G hd0 S.mass S.weights α hα
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hHu
  have hHG : dirichletOperator G a ν α * (dirichletOperator G a ν α)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdet
  have hGH : (dirichletOperator G a ν α)⁻¹ * dirichletOperator G a ν α = 1 :=
    Matrix.nonsing_inv_mul _ hdet
  have hMu := H3 G S hα hM2 (s := fun _ => 1) (fun P => by simp) hδ hδδs hφ
  rw [hG1] at hMu ⊢
  rw [baseHamiltonian_one]
  exact baseOp_mul_constrainedCov hHG hGH (fun z => hsq z) hMu

end Physical

end Balaban.LargeField.Base
