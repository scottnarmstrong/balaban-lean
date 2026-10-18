/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2BirthMass

/-!
# The radius inclusion on the birth domains with an allowance `Λ`

The level-`j` birth mass `μ_j = ν_j L⁻²ʲ` exceeds the ideal mass of the current scale by at most
the factor `e²` (`physMass_mul_sq_le_exp_nuIdeal`).  The anisotropic polydisc of radius `r / Λ`
(`Λ = e²`) in the variables `(ψ, b = ν_j h)` then lies in the level-`j` birth chart, whenever the
radius `r` satisfies `AnisoRadiusOK`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

omit [NeZero L] [NeZero N₁] in
/-- The mass-weighted field deviation is at most `Λ` times the deviation of the source
`b = ν_j h`, when `μ L^{2j} ≤ Λ ν_j`. -/
theorem mass_mul_norm_div_le_allow {μ νj Λ : ℝ} {j : ℕ} (hνj : 0 < νj) (hΛp : 0 < Λ)
    (hm : μ * ((L : ℝ) ^ j) ^ 2 ≤ Λ * νj) (w t : ℂ) :
    μ * ((L : ℝ) ^ j) ^ 2 * ‖w / (νj : ℂ) - t‖ ≤ Λ * ‖w - (νj : ℂ) * t‖ := by
  have h := mass_mul_norm_div_le (L := L) (μ := μ / Λ) (νj := νj) (j := j) hνj
  have hm' : (μ / Λ) * ((L : ℝ) ^ j) ^ 2 ≤ νj := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hΛp]; linarith
  have := h hm' w t
  calc μ * ((L : ℝ) ^ j) ^ 2 * ‖w / (νj : ℂ) - t‖
      = Λ * (μ / Λ * ((L : ℝ) ^ j) ^ 2 * ‖w / (νj : ℂ) - t‖) := by field_simp
    _ ≤ Λ * ‖w - (νj : ℂ) * t‖ := mul_le_mul_of_nonneg_left this hΛp.le

/-- The allowance form of `polyAniso_subset_xiDom_of_radius`: for `μ L^{2j} ≤ Λ ν_j` with
`1 ≤ Λ`, the polydisc of radius `r / Λ` lies in the level-`j` chart at the mass `μ`, where `r`
satisfies `AnisoRadiusOK`.  The `h`-variable radii `ρ_h = r`, `ρ_l = r²` of `xiDom_of_aniso` are
divided by `Λ` in the `b`-variable. -/
theorem polyAniso_subset_xiDom_of_radius_allow
    {P : Consts} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a' : ℕ → ℝ} {μ νj Λ : ℝ} {j : ℕ}
    (hBg : BgHyp d L k ϱ a' μ) (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k)
    (hνj : 0 < νj) (hΛ : 1 ≤ Λ) (hm : μ * ((L : ℝ) ^ j) ^ 2 ≤ Λ * νj) (i₀ : Fin N)
    {r : ℝ} (hr : AnisoRadiusOK d L N P j r) {X' : Finset (Site d)}
    {c : Cfg d N X'} (hc : c ∈ polyAniso i₀ νj (r / Λ) X') :
    XiDom G a' μ j (P.eps d L j) (fieldOf j i₀ X' c) (hOf νj X' c) := by
  obtain ⟨hr0, hr1, δ, hδ0, hδc0, hδc1, hε, hrδ⟩ := hr
  have hΛ0 : 0 < Λ := by linarith
  have hNB : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hrδ' : 4 * (N : ℝ) * r ≤ δ := (aniK_old (P := P) i₀ hr0 hrδ).2
  have hrδ2 : r < δ := by nlinarith
  have hr' : 0 < r / Λ := div_pos hr0 hΛ0
  have hr'r : r / Λ ≤ r := div_le_self hr0.le hΛ
  have hr'1 : r / Λ ≤ 1 := hr'r.trans hr1
  have hΛr : Λ * (r / Λ) = r := by field_simp
  have hΛr2 : Λ * (r / Λ) ^ 2 ≤ r ^ 2 := by
    have : Λ * (r / Λ) ^ 2 = r * (r / Λ) := by field_simp
    rw [this]; nlinarith
  have hb := fun i => (polyAniso_inr hc hr' hr'1 i).le
  have hbl := (polyAniso_inr_self hc).le
  refine xiDom_of_aniso hBg hΩ hjk i₀ hδ0 hδc0 hδc1 (ρs := r) (ρh := r) (ρl := r ^ 2) hr0.le
    hr0.le (by linarith) (by nlinarith) (by nlinarith) hε _ (fun i => c (Sum.inr i ) / (νj : ℂ))
    (fun x i => (fieldOf_sub_le_poly hc hr'.le x i).trans hr'r)
    (fun _ _ h => fieldOf_block c h) (fun i => ?_) ?_
  · have := mass_mul_norm_div_le_allow (L := L) hνj hΛ0 hm (c (Sum.inr i))
      ((Pi.single i₀ 1 : Fin N → ℂ) i)
    refine this.trans ?_
    calc Λ * ‖c (Sum.inr i) - (νj : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ Λ * (r / Λ) :=
          mul_le_mul_of_nonneg_left (hb i) hΛ0.le
      _ = r := hΛr
  · have := mass_mul_norm_div_le_allow (L := L) hνj hΛ0 hm (c (Sum.inr i₀)) 1
    rw [mul_one] at this
    refine this.trans ?_
    exact (mul_le_mul_of_nonneg_left hbl hΛ0.le).trans hΛr2

section Birth

variable {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρ : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}

/-- **The anisotropic polydisc of radius `r / e²` lies in the level-`j` birth chart.**  The sharp
mass comparison of `polyAniso_subset_birthXiDom_of_mass` is replaced by the uniform allowance
`e²` of `physMass_mul_sq_le_exp_nuIdeal`, and the radius of the polydisc is divided by `e²`. -/
theorem polyAniso_subset_birthXiDom
    (hF : IsSFFamily2 P Rg β a (birthXiDom P Rg a) Tm ρ Ek) {j : ℕ}
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (physMass L j (Rg.ν j)))
    (hL : 2 ≤ L) (hj1 : 1 ≤ j) (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (i₀ : Fin N) {r : ℝ} (hr : AnisoRadiusOK d L N P j r) {c : Cfg d N X'}
    (hc : c ∈ polyAniso i₀ (nuIdeal L k (Rg.ν k) j) (r / Real.exp 2) X') :
    (birthXiDom P Rg a N₁).dom j ((Tm N₁).gs j (Ypoly j X'))
      (fieldOf j i₀ X' c) (hOf (nuIdeal L k (Rg.ν k) j) X' c) := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hνj : 0 < nuIdeal L k (Rg.ν k) j := by
    unfold nuIdeal; have := hF.coeff.nu_pos; positivity
  rw [birthXiDom_dom_iff]
  exact polyAniso_subset_xiDom_of_radius_allow hBg
    ((hF.torus N₁).terms.gs_spec j hj1 hjk _ hX).2 hjk hνj
    (by rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by norm_num))
    (physMass_mul_sq_le_exp_nuIdeal hF.admissible hL hF.coeff hjk) i₀ hr hc

end Birth

end Balaban.SmallField.Def6v2
