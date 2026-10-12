/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6BridgeLift
public import Balaban.SmallField.RenormAnisoCtx
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The bridge Def-6 to the anisotropic I-6: the domain and the lifted term (torus side)

**The domain inclusion** (I6-ANISO (1.3)): `inPsiTildeC_of_aniso`, `xiDom_of_aniso` strengthen
the landed `inPsiTildeC_of_close`, `xiDom_of_close`.  A field `Ψ`, constant on the `j`-blocks,
within `ρ_s` of `e_{i₀}`, and a constant field `h = c` whose mass-weighted deviation
`ν L^{2j} |c - e|` is at most `ρ_h` in every component and at most `ρ_l` in the longitudinal
component `c_{i₀} - 1`, lie in `Ξ^c_j(𝔹; 1, ε)` when `4 N ρ_s ≤ δ`, `2 N ρ_h ≤ δ`, `ρ_l < δ²`,
`0 < δ ≤ min (c₀, c₁)` and `(2 K₁ + 2) δ ≤ ε`.  The common condition `N ρ < δ²` of the landed
lemma is replaced by these separate bounds: the longitudinal bound is quadratic in `δ`, the
others are linear.

**The lifted term on the anisotropic tube**: for the polydisc `polyAniso i₀ ν_j r X'` with
`4 N r (1 + N B) ≤ δ` the class term is analytic and rotation invariant (`Eaux_rotA`,
`Eaux_orthA`); `termLA` is the term at a rotation carrying the configuration into the polydisc
(well defined, `termLA_eq`), and `termLA_analytic`, `termLA_bdd_tube`, `termLA_bdd_dom`,
`termLA_rot_inv` are the analytic premises of `PremisesTermAniso` on `TubeAniso`.  The radius is
`anisoRadius = ε_j / ((2 K₁ + 2) · 4 N (1 + N · rotB N))`, of order `ε_j`.
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

/-! ### The class term on the anisotropic polydisc -/

section Core

variable [NeZero L] [NeZero N₁]

variable {P : Consts} {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ}

/-- The mass-weighted field deviation is at most the deviation of `b = ν_j h`. -/
theorem bgMass_mul_norm_div_le (hν : 0 < ν k) (hjk : j ≤ k) (w t : ℂ) :
    bgMass L k (β k) (ν k) * ((L : ℝ) ^ j) ^ 2 * ‖w / (nuIdeal L k (ν k) j : ℂ) - t‖ ≤
      ‖w - (nuIdeal L k (ν k) j : ℂ) * t‖ := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hνj : 0 < nuIdeal L k (ν k) j := by unfold nuIdeal; positivity
  have hm := bgMass_mul_le_nuIdeal (L := L) (k := k) (βk := β k) hν.le hjk
  have hm0 : 0 ≤ bgMass L k (β k) (ν k) := bgMass_nonneg hν L k
  have e : w / (nuIdeal L k (ν k) j : ℂ) - t =
      (w - (nuIdeal L k (ν k) j : ℂ) * t) / (nuIdeal L k (ν k) j : ℂ) := by
    have hνc : (nuIdeal L k (ν k) j : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
    field_simp
  rw [e, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hνj]
  calc _ = (bgMass L k (β k) (ν k) * ((L : ℝ) ^ j) ^ 2 / nuIdeal L k (ν k) j) *
        ‖w - (nuIdeal L k (ν k) j : ℂ) * t‖ := by
        field_simp
    _ ≤ 1 * ‖w - (nuIdeal L k (ν k) j : ℂ) * t‖ := by
        gcongr
        rw [div_le_one hνj]; exact hm
    _ = _ := one_mul _

/-- **The domain inclusion, anisotropic field form**: a torus field `Ψ`, constant on the
`j`-blocks, within `ρ_s` of `e_{i₀}`, and `h = b / ν_j` with `|b - ν_j e_{i₀}| ≤ ρ_h`
(componentwise) and `|b_{i₀} - ν_j| ≤ ρ_l` lie in `Ξ^c_j(𝔹_j(Z); 1, ε_j)`. -/
theorem xiDom_of_fieldA (hsf : IsSF P β ν a Tm ρd Ek)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {Z : Set (CTorus d L N₁ m₁ k)}
    (hZ : IsPolyDom P.m₀ j Z) (i₀ : Fin N) {δ ρs ρh ρl : ℝ} (hδ0 : 0 < δ)
    (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N) (hρs0 : 0 ≤ ρs) (hρh0 : 0 ≤ ρh)
    (hρs : 4 * N * ρs ≤ δ) (hρh : 2 * N * ρh ≤ δ) (hρl : ρl < δ ^ 2)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ)
    (hΨ : ∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρs)
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    (hb : ∀ i, ‖b i - (nuIdeal L k (ν k) j : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρh)
    (hbl : ‖b i₀ - (nuIdeal L k (ν k) j : ℂ)‖ ≤ ρl) :
    XiDom (Tm.gs j Z) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ
      (fun _ i => b i / (nuIdeal L k (ν k) j : ℂ)) := by
  have hspec := (hsf.gs_spec j hj1 hjk _ hZ).2
  refine xiDom_of_aniso hBg hspec hjk i₀ hδ0 hδc0 hδc1 hρs0 hρh0 hρs hρh hρl hε Ψ
    (fun i => b i / (nuIdeal L k (ν k) j : ℂ)) hΨ hΨb (fun i => ?_) ?_
  · exact (bgMass_mul_norm_div_le (β := β) hν hjk _ _).trans (hb i)
  · have := bgMass_mul_norm_div_le (L := L) (β := β) hν hjk (b i₀) 1
    rw [mul_one] at this
    exact this.trans hbl

/-- **The domain inclusion for a configuration**: a field `Ψ` within `ρ_s ≥ r` of `e_{i₀}`,
constant on the blocks, together with the field `b` of a configuration of the anisotropic
polydisc of radius `r`, lies in `Ξ^c_j(𝔹_j(Ypoly X'); 1, ε_j)` when `4 N ρ_s ≤ δ`. -/
theorem xiDom_of_polyA (hsf : IsSF P β ν a Tm ρd Ek)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) (i₀ : Fin N)
    {δ r ρs : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N) (hr0 : 0 < r)
    (hr1 : r ≤ 1) (hrs : r ≤ ρs) (hρs : 4 * N * ρs ≤ δ)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    (Ψ : Fld d L N₁ m₁ k N)
    (hΨ : ∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρs)
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    {u : Cfg d N X'} (hu : u ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X') :
    XiDom (Tm.gs j (Ypoly j X')) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
      Ψ (hOf (nuIdeal L k (ν k) j) X' u) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hrδ : r < δ := by nlinarith
  exact xiDom_of_fieldA hsf hBg hν hj1 hjk hX i₀ hδ0 hδc0 hδc1 (hr0.le.trans hrs) hr0.le hρs
    (by nlinarith) (by nlinarith) hε Ψ (fun i => u (Sum.inr i)) hΨ hΨb
    (fun i => (polyAniso_inr hu hr0 hr1 i).le) (polyAniso_inr_self hu).le

theorem fp_mem_xiDomA (hsf : IsSF P β ν a Tm ρd Ek)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) (i₀ : Fin N)
    {δ r : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N) (hr0 : 0 < r)
    (hr1 : r ≤ 1) (hrδ : 4 * N * r ≤ δ) (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    {c : Cfg d N X'} (hc : c ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X') :
    XiDom (Tm.gs j (Ypoly j X')) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
      (fieldOf j i₀ X' c) (hOf (nuIdeal L k (ν k) j) X' c) :=
  xiDom_of_polyA hsf hBg hν hj1 hjk hX i₀ hδ0 hδc0 hδc1 hr0 hr1 le_rfl hrδ hε _
    (fun x i => fieldOf_sub_le_poly hc hr0.le x i) (fun _ _ h => fieldOf_block c h) hc

/-- **Rotation invariance of the centred term on the anisotropic polydisc** (from (H.3) `rotE`):
two configurations of the polydisc related by an `IsRot` matrix with entries bounded by `B` have
the same term. -/
theorem Eaux_rotA (hsf : IsSF P β ν a Tm ρd Ek)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') (i₀ : Fin N)
    {δ r B : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hB : 0 ≤ B) (hrδ : 4 * N * (r * (1 + N * B)) ≤ δ)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsRot M) (hMb : ∀ i k, ‖M i k‖ ≤ B)
    {u u' : Cfg d N X'} (hu : u ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X')
    (hu' : u' ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X') (hrot : rotCfgL M X' u = u') :
    Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' u' = Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' u := by
  have hNB : 0 ≤ (N : ℝ) * B := by positivity
  set ρs : ℝ := r * (1 + N * B) with hρs
  have hrs : r ≤ ρs := by rw [hρs]; nlinarith
  have hXi := xiDom_of_polyA hsf hBg hν hj1 hjk hX i₀ hδ0 hδc0 hδc1 hr0 hr1 hrs hrδ hε _
    (fun x i => (fieldOf_sub_le_poly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (j := j) hu hr0.le
      x i).trans hrs) (fun x x' h => fieldOf_block u h) hu
  have h0u : fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u' 0 =
      M.mulVec (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u 0) := by
    have := fieldOf_rot (j := j) (i₀ := i₀) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) M u
      (x := 0) (by rw [unlift_zero]; exact h0)
    rw [← hrot, this]; rfl
  have hMe : ∀ i, ‖(M.mulVec (Pi.single i₀ 1 : Fin N → ℂ)) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤
      ρs := by
    intro i
    have h1 := fieldOf_sub_le_poly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (j := j) hu' hr0.le 0 i
    have h2 := fun k' =>
      fieldOf_sub_le_poly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (j := j) hu hr0.le 0 k'
    have e1 : (M.mulVec (Pi.single i₀ 1 : Fin N → ℂ)) i - (Pi.single i₀ 1 : Fin N → ℂ) i =
        (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u' 0 i -
            (Pi.single i₀ 1 : Fin N → ℂ) i) -
          ∑ k', M i k' * (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u
            (0 : CTorus d L N₁ m₁ k) k' - (Pi.single i₀ 1 : Fin N → ℂ) k') := by
      rw [h0u]
      simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [e1]
    calc _ ≤ ‖fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u' 0 i -
            (Pi.single i₀ 1 : Fin N → ℂ) i‖ +
          ‖∑ k', M i k' * (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u
            (0 : CTorus d L N₁ m₁ k) k' - (Pi.single i₀ 1 : Fin N → ℂ) k')‖ :=
          norm_sub_le _ _
      _ ≤ r + ∑ _k' : Fin N, B * r := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k' _ => ?_)
          rw [norm_mul]
          exact mul_le_mul (hMb i k') (h2 k') (norm_nonneg _) hB
      _ = ρs := by rw [hρs]; simp; ring
  have hXirot : XiDom (Tm.gs j (Ypoly j X')) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j
      (P.eps d L j)
      (rotField M (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u))
      (rotField M (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k (ν k) j) X' u)) := by
    rw [← hOf_rot, hrot]
    refine xiDom_of_polyA hsf hBg hν hj1 hjk hX i₀ hδ0 hδc0 hδc1 hr0 hr1 hrs hrδ hε _
      (fun x i => ?_) (fun x x' h => ?_) hu'
    · by_cases hx : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x ∈ X'
      · rw [← fieldOf_rot M u hx, hrot]
        exact (fieldOf_sub_le_poly hu' hr0.le x i).trans hrs
      · have : fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u x =
            (Pi.single i₀ 1 : Fin N → ℂ) := by
          funext i; simp [fieldOf, hx]
        have e : rotField M (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u) x =
            M.mulVec (Pi.single i₀ 1 : Fin N → ℂ) := by
          simp [rotField, this]
        rw [e]; exact hMe i
    · simp only [rotField]
      rw [fieldOf_block u h]
  have hr := hsf.rotE j hj1 hjk 0 (Ypoly j X') hX (zero_mem_Ypoly h0) M hM _ _ hXi hXirot
  unfold Eaux
  rw [← hr]
  refine hsf.localE j 0 (Ypoly j X') _ _ _ _ (fun x hx => ⟨?_, ?_⟩)
  · rw [← hrot, fieldOf_rot M u hx]
  · rw [← hrot, hOf_rot]

/-- **Rotation invariance for `O(N, ℂ)` on the anisotropic polydisc**: as `Eaux_rotA` for any
complex orthogonal `M`, through one real reflection of a coordinate `p ≠ i₀`. -/
theorem Eaux_orthA (hsf : IsSF P β ν a Tm ρd Ek)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') {i₀ p : Fin N} (hp : p ≠ i₀)
    {δ r B : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hB : 1 ≤ B) (hrδ : 4 * N * (r * (1 + N * B)) ≤ δ)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsOrth M) (hMb : ∀ i k, ‖M i k‖ ≤ B)
    {u u' : Cfg d N X'} (hu : u ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X')
    (hu' : u' ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X') (hrot : rotCfgL M X' u = u') :
    Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' u' = Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' u := by
  have hB0 : 0 ≤ B := by linarith
  rcases det_isOrth hM with hd | hd
  · exact Eaux_rotA hsf hBg hν hj1 hjk hX h0 i₀ hδ0 hδc0 hδc1 hr0 hr1 hB0 hrδ hε
      ⟨hM, Or.inr hd⟩ hMb hu hu' hrot
  · set Pm := reflP N p with hPm
    have hPpoly : rotCfgL Pm X' u ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X' :=
      rotCfgL_reflP_mem_polyAniso hp hu
    have h1 := Eaux_rotA hsf hBg hν hj1 hjk hX h0 i₀ hδ0 hδc0 hδc1 hr0 hr1 hB0 hrδ hε
      (isRot_reflP p) (fun i k => (reflP_norm_le p i k).trans hB) hu hPpoly rfl
    have hMP : IsRot (M * Pm) := by
      refine ⟨?_, Or.inr ?_⟩
      · rw [Matrix.transpose_mul, hPm, reflP_transpose, Matrix.mul_assoc,
          ← Matrix.mul_assoc M.transpose, hM, Matrix.one_mul, reflP_mul_self]
      · rw [Matrix.det_mul, hd, hPm, reflP_det]; norm_num
    have hMPb : ∀ i k, ‖(M * Pm) i k‖ ≤ B := by
      intro i k
      rw [hPm]
      unfold reflP
      rw [Matrix.mul_diagonal]
      by_cases h : k = p
      · simp [h]; exact hMb i p
      · simp [h]; exact hMb i k
    have h2 := Eaux_rotA hsf hBg hν hj1 hjk hX h0 i₀ hδ0 hδc0 hδc1 hr0 hr1 hB0 hrδ hε hMP hMPb
      hPpoly hu' (by
        have hPP : Pm * Pm = 1 := by rw [hPm]; exact reflP_mul_self p
        rw [← rotCfgL_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]; exact hrot)
    rw [h2, h1]

/-- The radius condition of the anisotropic bridge: `0 < r ≤ 1` and some `δ` with
`0 < δ ≤ min (c₀, c₁)`, `(2 K₁ + 2) δ ≤ ε_j` and `4 N r (1 + N · rotB N) ≤ δ`. -/
def AnisoRadiusOK (d L N : ℕ) [NeZero L] (P : Consts) (j : ℕ) (r : ℝ) : Prop :=
  0 < r ∧ r ≤ 1 ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ bgC0 d L N ∧ δ ≤ bgC1 d L N ∧
    (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j ∧ 4 * N * (r * (1 + N * rotB N)) ≤ δ

/-- **The radius of the anisotropic tube**:
`r_j = ε_j / ((2 K₁ + 2) · 4 N (1 + N · rotB N))`, of order `ε_j`. -/
noncomputable def anisoRadius (d L N : ℕ) [NeZero L] (P : Consts) (j : ℕ) : ℝ :=
  P.eps d L j / ((2 * bgK1 d L N + 2) * (4 * N * (1 + N * rotB N)))

omit [NeZero N₁] in
/-- The radius condition holds for `anisoRadius` as soon as `ε_j ≤ (2 K₁ + 2) min (c₀, c₁)`
(P1's "`ε` sufficiently small"). -/
theorem anisoRadius_spec {P : Consts} {j : ℕ} (hε : 0 < P.eps d L j) (i₀ : Fin N)
    (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N)) :
    AnisoRadiusOK d L N P j (anisoRadius d L N P j) := by
  have hK := bgK1_pos d L N
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hK2 : 0 < 2 * bgK1 d L N + 2 := by positivity
  have hB : 0 < 1 + N * rotB N := by unfold rotB; positivity
  have hQ : 1 ≤ 4 * N * (1 + N * rotB N) := by
    have : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
    nlinarith
  set δ := P.eps d L j / (2 * bgK1 d L N + 2) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδc0 : δ ≤ bgC0 d L N := by
    rw [hδ, div_le_iff₀ hK2]
    exact hsmall.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hK2.le) |>.trans_eq (by ring)
  have hδc1 : δ ≤ bgC1 d L N := by
    rw [hδ, div_le_iff₀ hK2]
    exact hsmall.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hK2.le) |>.trans_eq (by ring)
  have hδ1 : δ ≤ 1 / 16 := hδc0.trans (bgC0_le d L N)
  have hr : anisoRadius d L N P j = δ / (4 * N * (1 + N * rotB N)) := by
    unfold anisoRadius; rw [hδ, div_div]
  refine ⟨by rw [hr]; positivity, ?_, δ, hδ0, hδc0, hδc1, by rw [hδ, mul_div_cancel₀ _ hK2.ne'],
    ?_⟩
  · rw [hr, div_le_iff₀ (by positivity)]
    nlinarith
  · rw [hr]
    have : 4 * (N : ℝ) * (δ / (4 * N * (1 + N * rotB N)) * (1 + N * rotB N)) = δ := by
      field_simp
    rw [this]

omit [NeZero N₁] in
/-- **The radius condition is satisfiable** (inhabitation of `AnisoRadiusOK`): for every `j` with
`ε_j > 0` (every admissible `P`, `eps_pos`) some radius `r > 0` satisfies it. -/
theorem exists_anisoRadiusOK (hd : 0 < d) {P : Consts} {j : ℕ} (hε : 0 < P.eps d L j)
    (i₀ : Fin N) : ∃ r : ℝ, AnisoRadiusOK d L N P j r := by
  have hK := bgK1_pos d L N
  have hK2 : 0 < 2 * bgK1 d L N + 2 := by positivity
  have hc0 := bgC0_pos d L N hd
  have hc1 : 0 < bgC1 d L N := by
    have h1 := approxDelta_pos d L
    have h2 := deltaStar_pos (d := d) (L := L) (N := N) hd
    have h3 := lemma53Const_pos d L
    unfold bgC1
    refine lt_min (lt_min h1 ?_) (lt_min ?_ ?_) <;> positivity
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hB : 0 < 1 + N * rotB N := by unfold rotB; positivity
  set δ : ℝ := min (min (bgC0 d L N) (bgC1 d L N)) (P.eps d L j / (2 * bgK1 d L N + 2)) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hc0 hc1) (by positivity)
  have hQ : 0 < 4 * N * (1 + N * rotB N) := by positivity
  refine ⟨min 1 (δ / (4 * N * (1 + N * rotB N))), lt_min one_pos (by positivity), min_le_left _ _,
    δ, hδ0, (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
    ?_, ?_⟩
  · have := min_le_right (min (bgC0 d L N) (bgC1 d L N)) (P.eps d L j / (2 * bgK1 d L N + 2))
    rw [← hδ] at this
    rw [le_div_iff₀ hK2] at this
    linarith
  · have h1 : min 1 (δ / (4 * N * (1 + N * rotB N))) ≤ δ / (4 * N * (1 + N * rotB N)) :=
      min_le_right _ _
    calc 4 * (N : ℝ) * (min 1 (δ / (4 * N * (1 + N * rotB N))) * (1 + N * rotB N))
        ≤ 4 * N * (δ / (4 * N * (1 + N * rotB N)) * (1 + N * rotB N)) := by gcongr
      _ = δ := by field_simp

open Classical in
/-- **The term of the lifted family on the anisotropic tube**: the term at a rotation carrying the
configuration into the anisotropic polydisc (well defined by `termLA_eq`); elsewhere the term
itself. -/
noncomputable def termLA (Tm : Terms d L N₁ m₁ k N ϱ) (j : ℕ) (i₀ : Fin N) (νj r : ℝ)
    (X' : Finset (Site d)) (c : Cfg d N X') : ℂ :=
  if h : ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
      rotCfgL R X' c ∈ polyAniso i₀ νj r X' then
    Eaux Tm j i₀ νj X' (rotCfgL (Classical.choose h) X' c)
  else Eaux Tm j i₀ νj X' c

section Lift

variable (hsf : IsSF P β ν a Tm ρd Ek)
  (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
  (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
include hsf hBg hν hj1 hjk hrad

theorem witnessA {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') {i₀ p : Fin N} (hp : p ≠ i₀) {c : Cfg d N X'}
    {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsOrth A) (hB : IsOrth B) {ma mb : ℝ}
    (hAb : ∀ i k, ‖A i k‖ ≤ ma) (hBb : ∀ i k, ‖B i k‖ ≤ mb) (ha : 0 ≤ ma)
    (hab : (N : ℝ) * (ma * mb) ≤ rotB N)
    (hcA : rotCfgL A X' c ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X')
    (hcB : rotCfgL B X' c ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X') :
    Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' (rotCfgL A X' c) =
      Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' (rotCfgL B X' c) := by
  obtain ⟨hr0, hr1, δ, hδ0, hδc0, hδc1, hε, hrδ⟩ := hrad
  have hBBt : B * B.transpose = 1 := isOrth_mul_transpose hB
  have hM : IsOrth (A * B.transpose) := by
    unfold IsOrth
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc A.transpose, hA, Matrix.one_mul, hBBt]
  refine Eaux_orthA hsf hBg hν hj1 hjk hX h0 hp hδ0 hδc0 hδc1 hr0 hr1 (one_le_rotB i₀) hrδ hε hM
    (fun i k => (mul_entry_le hAb (transpose_entry_le hBb) ha i k).trans hab) hcB hcA ?_
  rw [← rotCfgL_mul, Matrix.mul_assoc, show B.transpose * B = 1 from hB, Matrix.mul_one]

/-- On the anisotropic tube the term is the term at any admissible witness rotation. -/
theorem termLA_eq {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') {i₀ p : Fin N} (hp : p ≠ i₀) {c : Cfg d N X'}
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsOrth R) (hRb : EntryBd N R)
    (hRc : rotCfgL R X' c ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X') :
    termLA Tm j i₀ (nuIdeal L k (ν k) j) r X' c =
      Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' (rotCfgL R X' c) := by
  have hex : ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
      rotCfgL R X' c ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X' := ⟨R, hR, hRb, hRc⟩
  unfold termLA
  simp only [hex, dite_true]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec hex
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  refine witnessA hsf hBg hν hj1 hjk hrad hX h0 hp h1 hR (entryBd_bound h2) (entryBd_bound hRb)
    (by norm_num) ?_ h3 hRc
  unfold rotB; nlinarith

theorem analyticAt_EauxA (i₀ : Fin N) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') {u₀ : Cfg d N X'}
    (hu : u₀ ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X') :
    AnalyticAt ℂ (Eaux Tm j i₀ (nuIdeal L k (ν k) j) X') u₀ := by
  obtain ⟨hr0, hr1, δ, hδ0, hδc0, hδc1, hε, hrδ⟩ := hrad
  have hN : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
  have hXi := fp_mem_xiDomA hsf hBg hν hj1 hjk hX i₀ hδ0 hδc0 hδc1 hr0 hr1
    (by nlinarith) hε hu
  have hE := hsf.analyticE j hj1 hjk 0 (Ypoly j X') hX (zero_mem_Ypoly h0)
    (fieldOf j i₀ X' u₀, hOf (nuIdeal L k (ν k) j) X' u₀) hXi
  exact AnalyticAt.comp (g := fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
    Tm.E j 0 (Ypoly j X') p.1 p.2)
    (f := fun c : Cfg d N X' => ((fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' c,
      hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k (ν k) j) X' c) :
        Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N)) (x := u₀) hE
    (analyticAt_fp j i₀ (nuIdeal L k (ν k) j) X' u₀)

/-- **Analyticity on the anisotropic tube** (premise (H.2)/(H.4) of the anisotropic I-6). -/
theorem termLA_analytic {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') :
    AnalyticOnNhd ℂ (termLA Tm j i₀ (nuIdeal L k (ν k) j) r X')
      (TubeAniso i₀ (nuIdeal L k (ν k) j) r X') := by
  intro c₀ hc₀
  obtain ⟨R₀, h1, h2, h3⟩ := hc₀
  have hcont : Continuous (rotCfgL R₀ X') := LinearMap.continuous_of_finiteDimensional _
  have hopen : IsOpen {c : Cfg d N X' |
      rotCfgL R₀ X' c ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X'} :=
    isOpen_polyAniso.preimage hcont
  have hAn : AnalyticAt ℂ (fun c => Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' (rotCfgL R₀ X' c)) c₀ :=
    AnalyticAt.comp (g := Eaux Tm j i₀ (nuIdeal L k (ν k) j) X')
      (analyticAt_EauxA hsf hBg hν hj1 hjk hrad i₀ hX h0 h3)
      ((LinearMap.toContinuousLinearMap (rotCfgL R₀ X')).analyticAt c₀)
  refine hAn.congr ?_
  filter_upwards [hopen.mem_nhds h3] with c hc
  exact (termLA_eq hsf hBg hν hj1 hjk hrad hX h0 hne h1 h2 hc).symm

/-- **The bound (H.4) on the anisotropic tube.** -/
theorem termLA_bdd_tube {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') {c : Cfg d N X'} (hc : c ∈ TubeAniso i₀ (nuIdeal L k (ν k) j) r X') :
    ‖termLA Tm j i₀ (nuIdeal L k (ν k) j) r X' c‖ ≤
      P.E₀ * Real.exp (-P.κ *
        sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X')) := by
  obtain ⟨R, h1, h2, h3⟩ := hc
  rw [termLA_eq hsf hBg hν hj1 hjk hrad hX h0 hne h1 h2 h3]
  obtain ⟨hr0, hr1, δ, hδ0, hδc0, hδc1, hε, hrδ⟩ := hrad
  have hN : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
  exact hsf.boundE j hj1 hjk 0 (Ypoly j X') hX (zero_mem_Ypoly h0) _ _
    (fp_mem_xiDomA hsf hBg hν hj1 hjk hX i₀ hδ0 hδc0 hδc1 hr0 hr1 (by nlinarith) hε h3)

/-- **Rotation invariance on the anisotropic tube** (premise (H.3)). -/
theorem termLA_rot_inv {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') {c : Cfg d N X'} (hc : c ∈ TubeAniso i₀ (nuIdeal L k (ν k) j) r X')
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsOrth R) (hRb : EntryBd N R)
    (hRc : rotCfgL R X' c ∈ TubeAniso i₀ (nuIdeal L k (ν k) j) r X') :
    termLA Tm j i₀ (nuIdeal L k (ν k) j) r X' (rotCfgL R X' c) =
      termLA Tm j i₀ (nuIdeal L k (ν k) j) r X' c := by
  obtain ⟨W, hW1, hW2, hW3⟩ := hc
  obtain ⟨W', hW1', hW2', hW3'⟩ := hRc
  rw [termLA_eq hsf hBg hν hj1 hjk hrad hX h0 hne hW1' hW2' hW3',
    termLA_eq hsf hBg hν hj1 hjk hrad hX h0 hne hW1 hW2 hW3]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hWR : IsOrth (W' * R) := by
    unfold IsOrth
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc W'.transpose, hW1',
      Matrix.one_mul, hR]
  have := witnessA hsf hBg hν hj1 hjk hrad hX h0 hne hWR hW1 (ma := (N : ℝ) * (40 * 40))
    (mb := 40) (mul_entry_le (entryBd_bound hW2') (entryBd_bound hRb) (by norm_num))
    (entryBd_bound hW2) (by positivity) (by unfold rotB; nlinarith)
    (by rw [rotCfgL_mul]; exact hW3') hW3
  rw [rotCfgL_mul] at this
  exact this

/-- **The bound (H.4) on the data domain**, with the witness of the data domain only for the
polymer itself. -/
theorem termLA_bdd_dom_at {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') {p : (Site d → Spin N) × Spin N}
    (hwit : ∃ (Ψ h : Fld d L N₁ m₁ k N),
      (∀ x ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X',
        Ψ x = fieldOf j i₀ X' (pack X' p.1 p.2) x ∧
          h x = hOf (nuIdeal L k (ν k) j) X' (pack X' p.1 p.2) x) ∧
      XiDom (Tm.gs j (Ypoly j X')) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        Ψ h) :
    ‖termLA Tm j i₀ (nuIdeal L k (ν k) j) r X' (pack X' p.1 p.2)‖ ≤
      P.E₀ * Real.exp (-P.κ *
        sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X')) := by
  by_cases hex : ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
      rotCfgL R X' (pack X' p.1 p.2) ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X'
  · exact termLA_bdd_tube hsf hBg hν hj1 hjk hrad hne hX h0 hex
  · unfold termLA
    simp only [hex, dite_false]
    obtain ⟨Ψ, h, hag, hXi⟩ := hwit
    have hloc : Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' (pack X' p.1 p.2) =
        Tm.E j 0 (Ypoly j X') Ψ h := by
      unfold Eaux
      exact (hsf.localE j 0 (Ypoly j X') _ _ _ _
        (fun x hx => ⟨(hag x hx).1.symm, (hag x hx).2.symm⟩))
    rw [hloc]
    exact hsf.boundE j hj1 hjk 0 (Ypoly j X') hX (zero_mem_Ypoly h0) Ψ h hXi

end Lift

end Core

end Balaban.SmallField.Def6
