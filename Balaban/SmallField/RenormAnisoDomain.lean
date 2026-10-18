/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6BridgeLift
public import Balaban.SmallField.RenormAnisoDefs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The domain inclusion of the anisotropic bridge

`inPsiTildeC_of_aniso`, `xiDom_of_aniso` strengthen the landed `inPsiTildeC_of_close`,
`xiDom_of_close` (moved from `RenormAnisoBridge` so that the complex invariance on the anisotropic
polydisc, `RenormAnisoRot`, can use them), and `mass_mul_norm_div_le` (moved from `Def6v2Bridge`).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.SmallField Balaban.Multiscale Balaban.Background Balaban.Localization Metric Set

variable {d L N₁ m₁ k N : ℕ} {ϱ : ℝ}

/-! ### The domain inclusion -/

section Close

variable [NeZero L] [NeZero N₁] {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {j : ℕ}

/-- **I6-ANISO (1.3)**: a field `Ψ` constant on the `j`-blocks with `|Ψ_i - δ_{i i₀}| ≤ ρ_s` and a
constant `c` with `ν L^{2j} |c_i - δ_{i i₀}| ≤ ρ_h`, `ν L^{2j} |c_{i₀} - 1| ≤ ρ_l` are in the
complex data domain `Ψ̃^c(𝔹; δ, δ)` over the real datum `(e, e)`, as soon as `4 N ρ_s ≤ δ`,
`2 N ρ_h ≤ δ`, `ρ_l < δ²`, `δ ≤ 1/16`. -/
theorem inPsiTildeC_of_aniso (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k) {ν δ ρs ρh ρl : ℝ}
    (hν : 0 ≤ ν) (i₀ : Fin N) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 16) (hρs0 : 0 ≤ ρs) (hρh0 : 0 ≤ ρh)
    (hρs : 4 * N * ρs ≤ δ) (hρh : 2 * N * ρh ≤ δ) (hρl : ρl < δ ^ 2)
    (Ψ : CTorus d L N₁ m₁ k → Fin N → ℂ) (c : Fin N → ℂ)
    (hΨ : ∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρs)
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    (hc : ∀ i, ν * ((L : ℝ) ^ j) ^ 2 * ‖c i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρh)
    (hcl : ν * ((L : ℝ) ^ j) ^ 2 * ‖c i₀ - 1‖ ≤ ρl) :
    InPsiTildeC G ν δ δ (fun _ => Pi.single i₀ 1) (Pi.single i₀ 1)
      (fun x i => Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i)
      (fun _ i => c i - (Pi.single i₀ 1 : Fin N → ℂ) i) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hvn : ∀ x, vn (fun i => Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i) ≤ N * ρs :=
    fun x => vn_le_card_mul hρs0 (hΨ x)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hlayer : ∀ x ∈ G.Ω 1, G.layerIndex x ≤ j := by
    intro x hx
    obtain ⟨-, -, hxl⟩ := G.layerIndex_spec hx
    by_contra h
    have := hΩ (G.layerIndex x) (by omega)
    have h2 := (G.mem_layer.1 hxl).1
    rw [this] at h2; simp at h2
  have hw : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ ν * ((L : ℝ) ^ j) ^ 2 := by
    intro x hx
    refine mul_le_mul_of_nonneg_left ?_ hν
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 (hlayer x hx)) 2
  have hhs : vn (fun i => ((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) *
      (c i - (Pi.single i₀ 1 : Fin N → ℂ) i)) ≤ N * ρh := by
    refine vn_le_card_mul hρh0 fun i => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hc i
  have hhx : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
      vn (fun i => c i - (Pi.single i₀ 1 : Fin N → ℂ) i) ≤ N * ρh := by
    intro x hx
    have e := vn_smul_real (ν * ((L : ℝ) ^ j) ^ 2) (fun i => c i - (Pi.single i₀ 1 : Fin N → ℂ) i)
    rw [abs_of_nonneg (by positivity)] at e
    calc _ ≤ ν * ((L : ℝ) ^ j) ^ 2 * vn (fun i => c i - (Pi.single i₀ 1 : Fin N → ℂ) i) :=
          mul_le_mul_of_nonneg_right (hw x hx) (vn_nonneg _)
      _ ≤ _ := e ▸ hhs
  refine
    { layerConst := isLayerConstant_of_jBlock hjk hΩ (fun _ _ _ => rfl)
      r1 := fun x x' _ => ?_
      r2 := fun x _ => ?_
      r3 := fun x _ => ?_
      r4 := ?_
      eps_pos := hδ0
      layerConst' := isLayerConstant_of_jBlock hjk hΩ (fun x x' hb => by
        funext i; simp only [hΨb x x' hb])
      hLayerConst' := isLayerConstant_of_jBlock hjk hΩ (fun _ _ _ => rfl)
      c1 := fun x x' _ => ?_
      c2a := fun x _ => ?_
      c2b := fun x _ => ?_
      c3a := fun x hx => ?_
      c3b := fun x hx => ?_ }
  · simp [rn]; exact hδ0
  · simp [Pi.single_apply]; exact hδ0
  · rw [rn_single]
    have : ∑ i, (Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i * (Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i = 1 := by
      simp [Pi.single_apply]
    simp only [this, div_one, sub_self, abs_zero, mul_zero]
    positivity
  · have : ∑ i, (Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i ^ 2 = 1 := by simp [Pi.single_apply]
    rw [this]; simp; positivity
  · have h1 : vn ((fun i => Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i) -
        fun i => Ψ x' i - (Pi.single i₀ 1 : Fin N → ℂ) i) ≤ N * (2 * ρs) := by
      refine vn_le_card_mul (by positivity) fun i => ?_
      have a1 := hΨ x i
      have a2 := hΨ x' i
      have : ((fun i => Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i) -
          fun i => Ψ x' i - (Pi.single i₀ 1 : Fin N → ℂ) i) i =
          (Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i) - (Ψ x' i - (Pi.single i₀ 1 : Fin N → ℂ) i) :=
        rfl
      rw [this]
      exact (norm_sub_le _ _).trans (by linarith)
    nlinarith
  · have := hvn x
    nlinarith
  · have hu : ∀ i, (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℝ) : ℂ) =
        (Pi.single i₀ 1 : Fin N → ℂ) i := by
      intro i; by_cases h : i = i₀ <;> simp [h]
    simp only [hu]
    set u : Fin N → ℂ := fun i => Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i with hu'
    have e1 : ∑ i, ((Pi.single i₀ 1 : Fin N → ℂ) i + u i) * ((Pi.single i₀ 1 : Fin N → ℂ) i + u i) -
        ∑ i, (Pi.single i₀ 1 : Fin N → ℂ) i * (Pi.single i₀ 1 : Fin N → ℂ) i =
        2 * u i₀ + ∑ i, u i * u i := by
      rw [← Finset.sum_sub_distrib]
      have : ∀ i, ((Pi.single i₀ 1 : Fin N → ℂ) i + u i) * ((Pi.single i₀ 1 : Fin N → ℂ) i + u i) -
          (Pi.single i₀ 1 : Fin N → ℂ) i * (Pi.single i₀ 1 : Fin N → ℂ) i =
          2 * ((Pi.single i₀ 1 : Fin N → ℂ) i * u i) + u i * u i := fun i => by ring
      simp_rw [this]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 2
      simp [Pi.single_apply]
    rw [e1]
    have b1 : ‖u i₀‖ ≤ ρs := hΨ x i₀
    have b2 : ‖∑ i, u i * u i‖ ≤ (N * ρs) * (N * ρs) :=
      (norm_dot_le u u).trans (mul_le_mul (hvn x) (hvn x) (vn_nonneg _) (by positivity))
    calc _ ≤ ‖2 * u i₀‖ + ‖∑ i, u i * u i‖ := norm_add_le _ _
      _ ≤ 2 * ρs + (N * ρs) * (N * ρs) := by
          rw [norm_mul]; norm_num; linarith
      _ < δ := by
          have h1 : ρs ≤ N * ρs := by nlinarith
          have h2 : (N : ℝ) * ρs ≤ δ / 4 := by linarith
          have h3 : (N : ℝ) * ρs * (N * ρs) ≤ δ / 4 * (δ / 4) :=
            mul_le_mul h2 h2 (by positivity) (by positivity)
          nlinarith
  · have e : δ ^ 2 / δ = δ := by field_simp
    rw [e]
    nlinarith [hhx x hx]
  · have hu : ∀ i, ((((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i) /
        rn (Pi.single i₀ (1 : ℝ) : Fin N → ℝ) : ℝ) : ℂ) = (Pi.single i₀ 1 : Fin N → ℂ) i := by
      intro i; rw [rn_single]; by_cases h : i = i₀ <;> simp [h]
    simp only [hu]
    have e : ∑ i, (Pi.single i₀ 1 : Fin N → ℂ) i * (c i - (Pi.single i₀ 1 : Fin N → ℂ) i) =
        c i₀ - 1 := by
      simp [Pi.single_apply]
    rw [e]
    calc _ ≤ ν * ((L : ℝ) ^ j) ^ 2 * ‖c i₀ - 1‖ :=
          mul_le_mul_of_nonneg_right (hw x hx) (norm_nonneg _)
      _ ≤ ρl := hcl
      _ < δ ^ 2 := hρl

/-- **The anisotropic box around the constant `e_{i₀}` lies in `Ξ^c_j(𝔹; 1, ε)`** (the domain
inclusion of the anisotropic bridge, torus side): the radii are `ρ_s, ρ_h ≍ δ` for the spins and
the field, `ρ_l < δ²` for the longitudinal field component. -/
theorem xiDom_of_aniso {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν)
    (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k) {δ ρs ρh ρl ε : ℝ} (i₀ : Fin N) (hδ0 : 0 < δ)
    (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N) (hρs0 : 0 ≤ ρs) (hρh0 : 0 ≤ ρh)
    (hρs : 4 * N * ρs ≤ δ) (hρh : 2 * N * ρh ≤ δ) (hρl : ρl < δ ^ 2)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ ε)
    (Ψ : CTorus d L N₁ m₁ k → Fin N → ℂ) (c : Fin N → ℂ)
    (hΨ : ∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρs)
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    (hc : ∀ i, ν * ((L : ℝ) ^ j) ^ 2 * ‖c i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρh)
    (hcl : ν * ((L : ℝ) ^ j) ^ 2 * ‖c i₀ - 1‖ ≤ ρl) :
    XiDom G a ν j ε Ψ (fun _ => c) := by
  have hP := inPsiTildeC_of_aniso (G := G) hΩ hjk H.mass i₀ hδ0 (hδc0.trans (bgC0_le d L N))
    hρs0 hρh0 hρs hρh hρl Ψ c hΨ hΨb hc hcl
  have hK := bgK1_pos d L N
  have hX := psiTildeC_subset_xiC (G := G) (a := a) H hδ0 le_rfl hδc0 hδc1
    (by
      have := H.massLe
      nlinarith [sq_nonneg δ]) hP (εb := ε) (by nlinarith)
  have hX' := xiC_level_irrel (n' := j) (by simp [Pi.single_apply]) hX
  refine ⟨fun _ => Pi.single i₀ 1, Pi.single i₀ 1, fun x i => Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i,
    fun _ i => c i - (Pi.single i₀ 1 : Fin N → ℂ) i, fun x i => ?_, fun x i => ?_, hX'⟩
  · have hu : (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℝ) : ℂ) = (Pi.single i₀ 1 : Fin N → ℂ) i := by
      by_cases h : i = i₀ <;> simp [h]
    rw [hu]; ring
  · have hu : (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℝ) : ℂ) = (Pi.single i₀ 1 : Fin N → ℂ) i := by
      by_cases h : i = i₀ <;> simp [h]
    rw [hu]; ring

end Close


/-! ### Coordinates of the anisotropic polydisc -/

section Poly

variable {i₀ : Fin N} {νj r : ℝ} {X' : Finset (Site d)}

theorem polyAniso_inl {c : Cfg d N X'} (hc : c ∈ polyAniso i₀ νj r X') (p : ↥X' × Fin N) :
    ‖c (Sum.inl p) - (Pi.single i₀ 1 : Fin N → ℂ) p.2‖ < r := by
  have := hc (Sum.inl p)
  rwa [refPt_inl, anisoWt_inl] at this

theorem polyAniso_inr {c : Cfg d N X'} (hc : c ∈ polyAniso i₀ νj r X') (hr0 : 0 < r) (hr1 : r ≤ 1)
    (i : Fin N) : ‖c (Sum.inr i) - (νj : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i‖ < r := by
  have h := hc (Sum.inr i)
  rw [refPt_inr] at h
  refine lt_of_lt_of_le h ?_
  simp only [anisoWt, Sum.elim_inr]
  split_ifs
  · nlinarith
  · exact le_rfl

theorem polyAniso_inr_self {c : Cfg d N X'} (hc : c ∈ polyAniso i₀ νj r X') :
    ‖c (Sum.inr i₀) - (νj : ℂ)‖ < r ^ 2 := by
  have h := hc (Sum.inr i₀)
  rw [refPt_inr, anisoWt_inr_self] at h
  simpa using h

theorem fieldOf_sub_le_poly [NeZero L] [NeZero N₁] {j : ℕ} {c : Cfg d N X'}
    (hc : c ∈ polyAniso i₀ νj r X') (hr0 : 0 ≤ r) (x : CTorus d L N₁ m₁ k) (i : Fin N) :
    ‖fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' c x i -
      (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ r := by
  unfold fieldOf
  split_ifs with h
  · exact (polyAniso_inl hc (⟨_, h⟩, i)).le
  · simpa using hr0

/-- The reflection of a coordinate `p ≠ i₀` preserves the anisotropic polydisc. -/
theorem rotCfgL_reflP_mem_polyAniso {p : Fin N} (hp : p ≠ i₀) {c : Cfg d N X'}
    (hc : c ∈ polyAniso i₀ νj r X') : rotCfgL (reflP N p) X' c ∈ polyAniso i₀ νj r X' := by
  have e : rotCfgL (reflP N p) X' c - refPt i₀ νj X' =
      rotCfgL (reflP N p) X' (c - refPt i₀ νj X') := by
    rw [map_sub, reflP_refPt hp]
  intro q
  have h := hc q
  have h2 : ‖(rotCfgL (reflP N p) X' c - refPt i₀ νj X') q‖ = ‖(c - refPt i₀ νj X') q‖ := by
    rw [e]
    rcases q with ⟨z, i⟩ | i
    · rw [rotCfgL_apply_inl]
      simp only [reflP, Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
      split_ifs <;> simp
      exact norm_sub_rev _ _
    · rw [rotCfgL_apply_inr]
      simp only [reflP, Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
      split_ifs <;> simp
      exact norm_sub_rev _ _
  have h3 : ‖rotCfgL (reflP N p) X' c q - refPt i₀ νj X' q‖ = ‖c q - refPt i₀ νj X' q‖ := h2
  rw [h3]; exact h

end Poly


end Balaban.SmallField.Def6

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Finset

variable {d L N₁ m₁ k N : ℕ} {ϱ : ℝ}

/-- **The mass-weighted field deviation is at most the deviation of the source `b = ν_j h`**, for
an arbitrary mass `0 ≤ μ` with `μ L^{2j} ≤ ν_j` (the landed `Def6.bgMass_mul_norm_div_le`, in which
the mass is `bgMass`). -/
theorem mass_mul_norm_div_le {μ νj : ℝ} {j : ℕ} (hνj : 0 < νj)
    (hm : μ * ((L : ℝ) ^ j) ^ 2 ≤ νj) (w t : ℂ) :
    μ * ((L : ℝ) ^ j) ^ 2 * ‖w / (νj : ℂ) - t‖ ≤ ‖w - (νj : ℂ) * t‖ := by
  have e : w / (νj : ℂ) - t = (w - (νj : ℂ) * t) / (νj : ℂ) := by
    have hνc : (νj : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
    field_simp
  rw [e, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hνj]
  calc μ * ((L : ℝ) ^ j) ^ 2 * (‖w - (νj : ℂ) * t‖ / νj)
      = (μ * ((L : ℝ) ^ j) ^ 2 / νj) * ‖w - (νj : ℂ) * t‖ := by field_simp
    _ ≤ 1 * ‖w - (νj : ℂ) * t‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [div_le_one hνj]; exact hm
    _ = _ := one_mul _


section Mass

variable [NeZero L] [NeZero N₁] {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a' : ℕ → ℝ}
  {μ νj : ℝ} {j : ℕ}

/-- **The domain inclusion, anisotropic field form, for an arbitrary mass** (the landed
`Def6.xiDom_of_fieldA` with `bgMass` replaced by a mass `μ` with `μ L^{2j} ≤ ν_j`): a torus field
`Ψ`, constant on the `j`-blocks, within `ρ_s` of `e_{i₀}`, and `h = b / ν_j` with
`|b - ν_j e_{i₀}| ≤ ρ_h` (componentwise) and `|b_{i₀} - ν_j| ≤ ρ_l` lie in `Ξ^c_j(𝔹; 1, ε)` at the
mass `μ`.  The radii `ρ_s, ρ_h, ρ_l` are those of `xiDom_of_aniso`; they do not involve `μ`. -/
theorem xiDom_of_fieldM (H : BgHyp d L k ϱ a' μ) (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k)
    (hνj : 0 < νj) (hm : μ * ((L : ℝ) ^ j) ^ 2 ≤ νj) (i₀ : Fin N) {δ ρs ρh ρl ε : ℝ}
    (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N) (hρs0 : 0 ≤ ρs)
    (hρh0 : 0 ≤ ρh) (hρs : 4 * N * ρs ≤ δ) (hρh : 2 * N * ρh ≤ δ) (hρl : ρl < δ ^ 2)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ ε) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ)
    (hΨ : ∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρs)
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    (hb : ∀ i, ‖b i - (νj : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρh)
    (hbl : ‖b i₀ - (νj : ℂ)‖ ≤ ρl) :
    XiDom G a' μ j ε Ψ (fun _ i => b i / (νj : ℂ)) := by
  refine xiDom_of_aniso H hΩ hjk i₀ hδ0 hδc0 hδc1 hρs0 hρh0 hρs hρh hρl hε Ψ
    (fun i => b i / (νj : ℂ)) hΨ hΨb (fun i => ?_) ?_
  · exact (mass_mul_norm_div_le hνj hm _ _).trans (hb i)
  · have := mass_mul_norm_div_le (L := L) hνj hm (b i₀) 1
    rw [mul_one] at this
    exact this.trans hbl


end Mass

end Balaban.SmallField.Def6v2
