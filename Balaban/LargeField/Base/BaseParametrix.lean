/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseCubeDiscs
public import Balaban.Localization.Decoupled2Self
public import Balaban.Localization.Decoupled2Analytic
public import Balaban.Localization.Decoupled2Close
public import Balaban.Localization.Decoupled2Local

/-!
# The first step through the decoupled parametrix

The first-step operator `H(s)` of `BaseResolvent.lean` lives on `G.Ω 1` for a generating set with
one layer (`K = 1`).  The decoupled parametrix `Gs` of the cover `coverOf G` (the family used by
the renormalization-group step, `Localization/Decoupled2*.lean`) is stated for every number of
layers `K`, so it applies verbatim with `K = 1`, with the torus side `N₁ * L ^ m₁` in place of `N₀`.
Its hypotheses are `DGSetting G a ν`: `d, L ≥ 3`, cube alignment of `Ω₁` (cells of side
`L ^ (1 + m₁)`, `L ^ m₁ ∣ N₀`), `4 L² ≤ L ^ m₁`, `ϱ ≥ 4 d L L ^ m₁`, the Green's function
separation, admissible weights, `0 ≤ ν`, `ν L² ≤ 1`, `5 < N₁`.

The decoupling parameters are one `s_P` per cover cube `P` (cubes of side `L ^ (1 + m₁)`), and the
discs are `‖s_P‖ < e^{κ}` with `κ ≥ 0` and `c_* e^{N₀ κ} ≤ L ^ m₁`.  The cover cubes are not the
first blocks and `Gs` at `s = 0` is `0`, so this family is not the cube family `t_Q` of
`BaseCubeDiscs.lean`.  The theorems below concern the scalar operator
`baseHamiltonian G a ν α 1 = dirichletOperator G a ν α`; the constrained operator `baseOp N e H`
is not treated here.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Matrix

variable {d L : ℕ} [NeZero L]

/-- **The parametrix for the first step: holomorphy in the cube parameters and the potential.**
Every entry of `Gs` of the cover of `G` is analytic on the polydisc `‖s_P‖ < e^κ`, with the
potential admissible. -/
theorem baseParametrix_analytic (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ cstar : ℝ, 0 ≤ cstar ∧ ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {κ : ℝ}, 0 ≤ κ → cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ x y : G.Ω 1, AnalyticOnNhd ℂ
        (fun p : Dec2.DecParams (coverOf G) × (G.Ω 1 → ℂ) =>
          Dec2.Gs (coverOf G) G a ν p.2 (Dec2.extS (coverOf G) p.1) x y)
        {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
          ∀ z, ‖p.2 z‖ < coerciveConst d / (2 * (G.spacing (z : Balaban.Localization.CTorus d L N₁ m₁ 1)) ^ 2)} := by
  obtain ⟨cstar, hc, H⟩ := Dec2.dg4_analytic (d := d) (L := L) (Kc := Dec2.selfKc d L)
    (Cx := Cchi d L) hd hL (Dec2.selfKc_nonneg hd hL) (Cchi_nonneg d L)
  refine ⟨cstar, hc, ?_⟩
  intro N₁ m₁ _ ϱ G a ν S κ hκ hM x y
  exact H (coverOf G) G (Dec2.coverBase_self S) hκ hM x y

/-- Holomorphy in the cube parameters alone, for a fixed admissible potential. -/
theorem baseParametrix_analytic_s (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ cstar : ℝ, 0 ≤ cstar ∧ ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → (∀ z, ‖α z‖ < coerciveConst d /
          (2 * (G.spacing (z : Balaban.Localization.CTorus d L N₁ m₁ 1)) ^ 2)) →
      ∀ {κ : ℝ}, 0 ≤ κ → cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ x y : G.Ω 1, AnalyticOnNhd ℂ
        (fun s : Dec2.DecParams (coverOf G) =>
          Dec2.Gs (coverOf G) G a ν α (Dec2.extS (coverOf G) s) x y)
        {s | ∀ P, ‖s P‖ < Real.exp κ} := by
  obtain ⟨cstar, hc, H⟩ := baseParametrix_analytic (d := d) (L := L) hd hL
  refine ⟨cstar, hc, ?_⟩
  intro N₁ m₁ _ ϱ G a ν S α _ hαs κ hκ hM x y
  have h := H G S hκ hM x y
  intro s hs
  have h1 : AnalyticAt ℂ (fun s' : Dec2.DecParams (coverOf G) => (s', α)) s :=
    analyticAt_id.prod analyticAt_const
  exact (h (s, α) ⟨hs, hαs⟩).comp (f := fun s' : Dec2.DecParams (coverOf G) => (s', α)) (x := s) h1

/-- **The parametrix at the physical point**: for `s ≡ 1` the family is the inverse of the
first-step operator at `t ≡ 1`, `H(1) = dirichletOperator`. -/
theorem baseParametrix_one (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ cstar : ℝ, 0 ≤ cstar ∧ ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → cstar ≤ (L : ℝ) ^ m₁ →
      IsUnit (1 - Dec2.Kcal (coverOf G) G a ν α (fun _ => 1)) ∧
      Dec2.Gs (coverOf G) G a ν α (fun _ => 1) =
        (baseHamiltonian G a ν α (fun _ => 1))⁻¹ := by
  obtain ⟨cstar, hc, H⟩ := Dec2.Gs_one (d := d) (L := L) (Kc := Dec2.selfKc d L) (Cx := Cchi d L)
    hd hL (Dec2.selfKc_nonneg hd hL) (Cchi_nonneg d L)
  refine ⟨cstar, hc, ?_⟩
  intro N₁ m₁ _ ϱ G a ν S α hα hM
  obtain ⟨hU, h⟩ := H (coverOf G) G (Dec2.coverBase_self S) hα hM
  exact ⟨hU, by rw [h, baseHamiltonian_one]⟩

/-- **The parametrix on the disc is well defined**: `1 - 𝒦_s` is invertible for `‖s_P‖ ≤ e^κ`. -/
theorem baseParametrix_isUnit (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ cstar : ℝ, 0 ≤ cstar ∧ ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {κ : ℝ}, 0 ≤ κ →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      IsUnit (1 - Dec2.Kcal (coverOf G) G a ν α s) := by
  obtain ⟨cstar, BG, hc, hB, H⟩ := Dec2.dg2_sup (d := d) (L := L) (Kc := Dec2.selfKc d L)
    (Cx := Cchi d L) hd hL (Dec2.selfKc_nonneg hd hL) (Cchi_nonneg d L)
  refine ⟨cstar, hc, ?_⟩
  intro N₁ m₁ _ ϱ G a ν S α hα κ hκ hM s hs
  have hd0 : 0 < d := by omega
  exact (H (coverOf G) G (Dec2.coverBase_self S) hα hκ hM hs (w := fun _ => 1)
    (IsWeight.one G (gammaW_nonneg hd0)) 0 (Cb := 0) le_rfl (by simp)).1

/-- **Weighted comparison with the physical inverse**: if every cover cube with `s_z ≠ 1` has its
interaction cube in `W`, then `Gs_s f - H(1)⁻¹ f` decays like `e^{-γ_w d(x, W)}`. -/
theorem baseParametrix_close (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ cstar BG : ℝ, 0 ≤ cstar ∧ 0 ≤ BG ∧ ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {κ : ℝ}, 0 ≤ κ →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ {W : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)},
      (∀ z ∈ (coverOf G).cubeIdx, (coverOf G).sProd s z ≠ 1 → intBox z ⊆ W) →
      ∀ (f : G.Ω 1 → ℂ) {Cb : ℝ}, 0 ≤ Cb →
      (∀ x : G.Ω 1, (G.spacing (x : Balaban.Localization.CTorus d L N₁ m₁ 1)) ^ 2 * ‖f x‖ ≤ Cb) →
      ∀ x ∈ G.Ω 1,
      ‖Dec2.Gdiff (coverOf G) G a ν α s f x‖ ≤
        BG * Real.exp (N0 d L * κ) * decay (gammaW d) (siteSetDist G W x) * Cb := by
  obtain ⟨cstar, BG, hc, hB, H⟩ := Dec2.dg6 (d := d) (L := L) (Kc := Dec2.selfKc d L)
    (Cx := Cchi d L) hd hL (Dec2.selfKc_nonneg hd hL) (Cchi_nonneg d L)
  refine ⟨cstar, BG, hc, hB, ?_⟩
  intro N₁ m₁ _ ϱ G a ν S α hα κ hκ hM s hs W hW f Cb hC hfC x hx
  exact (H (coverOf G) G (Dec2.coverBase_self S) hα hκ hM hs hW f hC hfC x hx).1

/-- **Exact agreement at a cut**: if every cover cube with a non-zero factor `s_z` or `s'_z` lies
inside `Y` or outside `Y` (as sets of `G`-sites), the factors agree on the cubes inside `Y`, and
the potentials and sources agree on `Y`, then `Gs_s α f` and `Gs_{s'} α' f'` agree on `Y`. -/
theorem baseParametrix_local (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ cstar : ℝ, 0 ≤ cstar ∧ ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {κ : ℝ}, 0 ≤ κ → cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {Y : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)} {α α' : G.Ω 1 → ℂ}, AdmPot G α → AdmPot G α' →
      ∀ {s s' : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      (∀ P, ‖s' P‖ ≤ Real.exp κ) →
      (∀ q ∈ (coverOf G).cubeIdx, ((coverOf G).sProd s q ≠ 0 ∨ (coverOf G).sProd s' q ≠ 0) →
        SubI G (intBox q) Y ∨ DisjI G (intBox q) Y) →
      (∀ q ∈ (coverOf G).cubeIdx, SubI G (intBox q) Y →
        (coverOf G).sProd s q = (coverOf G).sProd s' q) →
      (∀ x : G.Ω 1, (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y → α x = α' x) →
      ∀ {f f' : G.Ω 1 → ℂ}, (∀ x : G.Ω 1, (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y → f x = f' x) →
      ∀ x : G.Ω 1, (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y →
        (Dec2.Gs (coverOf G) G a ν α s *ᵥ f) x = (Dec2.Gs (coverOf G) G a ν α' s' *ᵥ f') x := by
  obtain ⟨cstar, hc, H⟩ := baseParametrix_isUnit (d := d) (L := L) hd hL
  refine ⟨cstar, hc, ?_⟩
  intro N₁ m₁ _ ϱ G a ν S κ hκ hM Y α α' hα hα' s s' hs hs' hdich hagree hA f f' hf x hx
  exact Dec2.Gs_local (Dec2.coverBase_self S) hα hα' (H G S hα hκ hM hs) (H G S hα' hκ hM hs')
    hdich hagree hA hf x hx

end Balaban.LargeField.Base
