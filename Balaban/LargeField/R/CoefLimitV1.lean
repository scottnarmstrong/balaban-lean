/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoefCtxV1
public import Balaban.SmallField.CoefShapeLimit
public import Balaban.LargeField.R.RadialCoefficientLimit

/-!
# The thermodynamic limit of the radial coefficient `v₁`, from the coefficient context

For a family of coefficient contexts along the tori `torusSeq L m₀ n` (`CoefFam`) and torus
independence of the terms, the whole-torus coefficient `v1T` at the block corners of two lattice
sites converges along the tori (P1 p. 147 (3.110)).  The proof is the one of
`tendsto_v1T_aInfC`: the sum over the polymers of the torus is a sum over shapes, the torus values
are Cauchy coefficients bounded by `E₀ ρ⁻¹ e^{-κ d_j}`, agree on any two good tori, and the sum
converges by the entropy bound (`exists_tendsto_shapeSum`).  The limit function is built by choice,
so neither the cut-off term `GE` nor the infinite-volume terms of the landed class are used.
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation Filter Matrix Metric

section Fam

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **The coefficient family**: coefficient contexts of one radius `ρ` on every torus `torusSeq L m₀ n`
of the sequence, torus independence of the terms, and the numerical premises `E₀ ≥ 0`,
`κ > a_ent + 1` of the entropy bound. -/
structure CoefFam (P : Consts) (νk : ℝ)
    (Dom : ∀ (N₁ : ℕ) [NeZero N₁], FieldDom d L N₁ m₁ k N ϱ)
    (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (j : ℕ) (ρ : ℝ) : Prop where
  ctx : ∀ n : ℕ, haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
    CoefCtx P νk (Dom (torusSeq L P.m₀ n)) (Tm (torusSeq L P.m₀ n)) j ρ
  indep : TorusIndep P.m₀ Tm
  E0_nonneg : 0 ≤ P.E₀
  kappa : aEnt d L + 1 < P.κ

variable {P : Consts} {νk : ℝ} {Dom : ∀ (N₁ : ℕ) [NeZero N₁], FieldDom d L N₁ m₁ k N ϱ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ} {j : ℕ} {ρ : ℝ}

/-- **The centred term does not depend on the good torus**: for a shape `X' ∋ y` that is good on two
tori of the sequence, the two class terms are the same function of the configuration. -/
theorem EauxC_eq_of_good (hT : TorusIndep P.m₀ Tm) (hj1 : 1 ≤ j) (hjk : j ≤ k) (i₀ : Fin N)
    (νj : ℝ) {y : SmallField.Site d} {X' : Finset (SmallField.Site d)} (hy : y ∈ X') {n n' : ℕ}
    (hg : GoodAt L m₁ k P.m₀ j X' n) (hg' : GoodAt L m₁ k P.m₀ j X' n') :
    EauxC (Tm (torusSeq L P.m₀ n)) j i₀ νj y X' = EauxC (Tm (torusSeq L P.m₀ n')) j i₀ νj y X' := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have : NeZero (torusSeq L P.m₀ n') := ⟨torusSeq_ne_zero P.m₀ n'⟩
  funext c
  unfold EauxC
  rw [← pullFld_fieldInfOf (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j i₀ X' c,
    ← pullFld_hInfOf (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j νj X' c,
    ← pullFld_fieldInfOf (L := L) (N₁ := torusSeq L P.m₀ n') (m₁ := m₁) (k := k) j i₀ X' c,
    ← pullFld_hInfOf (L := L) (N₁ := torusSeq L P.m₀ n') (m₁ := m₁) (k := k) j νj X' c]
  exact hT.E_eq j hj1 hjk y X' hy _ _ _ _ hg.1 hg'.1 hg.2 hg'.2

/-! ### The radial coefficient -/

variable (fam : CoefFam P νk Dom Tm j ρ)
include fam

/-- The coefficient of the shape on the `n`-th torus does not depend on the good torus. -/
theorem CoefFam.GEderN_eq (i₀ : Fin N) {y z : SmallField.Site d} {X' : Finset (SmallField.Site d)}
    (hy : y ∈ X') {n n' : ℕ} (hg : GoodAt L m₁ k P.m₀ j X' n) (hg' : GoodAt L m₁ k P.m₀ j X' n') :
    GEderN P (fun _ => νk) Tm j i₀ y z n X' = GEderN P (fun _ => νk) Tm j i₀ y z n' X' := by
  have hj1 := (fam.ctx 0).j1
  have hjk := (fam.ctx 0).jk
  have e := EauxC_eq_of_good fam.indep hj1 hjk i₀ (nuIdeal L k νk j) hy hg hg'
  unfold GEderN
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have : NeZero (torusSeq L P.m₀ n') := ⟨torusSeq_ne_zero P.m₀ n'⟩
  by_cases hz : z ∈ X'
  · simp only [hz, dite_true]
    exact congrArg (fun F => tensA i₀ (nuIdeal L k νk j) X' F ⟨z, hz⟩) e
  · simp [hz]

/-- The Cauchy bound of the coefficient on a good torus. -/
theorem CoefFam.norm_GEderN_le (i₀ : Fin N) {y z : SmallField.Site d} {n : ℕ}
    {X' : Finset (SmallField.Site d)} (hy : y ∈ X') (hgood : GoodAt L m₁ k P.m₀ j X' n) :
    ‖GEderN P (fun _ => νk) Tm j i₀ y z n X'‖ ≤
      P.E₀ / ρ * Real.exp (-P.κ * sizeSeq L m₁ k P.m₀ j X' n) := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have ctx := fam.ctx n
  unfold GEderN
  by_cases hz : z ∈ X'
  · simp only [hz, dite_true]
    refine (ctx.norm_tensA_EauxC_le i₀ hgood.1 hgood.2 hy ⟨z, hz⟩).trans (le_of_eq ?_)
    unfold sizeSeq
    ring
  · simp only [hz, dite_false, norm_zero]
    have := fam.E0_nonneg
    have := (fam.ctx 0).rho_pos
    positivity

/-- **On one torus the whole-torus coefficient is a sum over the shapes** through `y`: for `n` so
large that the block corners of `y` and `z` are centred, `v1T` at them is the sum of the
coefficients `GEderN` over the good shapes. -/
theorem CoefFam.v1T_eq_sum (i₀ : Fin N)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N)
    (hsrc : ∀ (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • b)))
    (y z : SmallField.Site d) (n : ℕ)
    (hyu : unlift (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j (blockPt j y) = y)
    (hzu : unlift (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j (blockPt j z) = z) :
    (haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩;
      v1T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k νk j) (Pi.single i₀ 1)
        (blockPt j y) (blockPt j z)) =
      ∑ᶠ X' ∈ ShAt (d := d) L m₁ k P.m₀ j y n, GEderN P (fun _ => νk) Tm j i₀ y z n X' := by
  classical
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have ctx := fam.ctx n
  have hjk := ctx.jk
  unfold v1T
  rw [finsum_polysAt_eq_shAt (m₁ := m₁) hjk y n hyu
    (fun Y => v1Loc ((St (torusSeq L P.m₀ n)).E j (blockPt j y) Y) j (nuIdeal L k νk j)
      (Pi.single i₀ 1) (blockPt j z))]
  refine finsum_mem_congr rfl fun X' hX' => ?_
  obtain ⟨hy, hnw, hpd⟩ := hX'
  have hEt : ∀ (Ψ : Fld d L (torusSeq L P.m₀ n) m₁ k N) (b : Fin N → ℂ),
      (St (torusSeq L P.m₀ n)).E j (blockPt j y) (Ypoly j X') Ψ (constFld b) =
        (Tm (torusSeq L P.m₀ n)).E j (blockPt j y) (Ypoly j X') Ψ
          (constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • b)) :=
    fun Ψ b => hsrc (torusSeq L P.m₀ n) (blockPt j y) (Ypoly j X') Ψ b
  have hbp : blockPt (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z = ibase j z := by
    funext μ; simp only [blockPt, ibase]; congr 1; ring
  have hal : Aligned (L ^ j) (blockPt (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z) := by
    rw [hbp]; exact ibase_aligned hjk z
  unfold GEderN
  by_cases hz : z ∈ X'
  · simp only [hz, dite_true]
    have hzX : unlift (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j (blockPt j z) ∈ X' := by
      rw [hzu]; exact hz
    have key := ctx.tensA_EauxC_eq_v1Loc (i₀ := i₀) hnw hpd hy hal hzX _ hEt
    rw [← key]
    have : (⟨unlift (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j (blockPt j z), hzX⟩ :
        ↥X') = ⟨z, hz⟩ := Subtype.ext hzu
    rw [this]
  · simp only [hz, dite_false]
    exact ctx.v1Loc_eq_zero_of_not_mem hpd (blockPt_mem_Ypoly hjk hnw hy) hal
      (by rw [hzu]; exact hz) _ hEt

/-- **The thermodynamic limit of the radial coefficient exists**: for all lattice sites `y z`, the
whole-torus coefficient `v1T` at the block corners of `y` and `z` converges along the tori of the
sequence. -/
theorem CoefFam.exists_tendsto_v1T (i₀ : Fin N)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N)
    (hsrc : ∀ (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • b)))
    (y z : SmallField.Site d) :
    ∃ ℓ : ℂ, Tendsto (fun n : ℕ =>
      haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩;
      v1T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k νk j) (Pi.single i₀ 1)
        (blockPt j y) (blockPt j z)) atTop (nhds ℓ) := by
  have hjk := (fam.ctx 0).jk
  have hC : 0 ≤ P.E₀ / ρ := by
    have := fam.E0_nonneg
    have := (fam.ctx 0).rho_pos
    positivity
  obtain ⟨ℓ, hℓ⟩ := exists_tendsto_shapeSum (m₀ := P.m₀) (m₁ := m₁) (j := j) hjk fam.kappa y
    (fun n X' => GEderN P (fun _ => νk) Tm j i₀ y z n X') hC
    (fun n n' X' hy hg hg' => fam.GEderN_eq i₀ hy hg hg')
    (fun n X' hy hg => fam.norm_GEderN_le i₀ hy hg)
  refine ⟨ℓ, hℓ.congr' ?_⟩
  filter_upwards [eventually_unlift_blockPt (L := L) (m₁ := m₁) (k := k) hjk P.m₀ y,
    eventually_unlift_blockPt (L := L) (m₁ := m₁) (k := k) hjk P.m₀ z] with n h1 h2
  exact (fam.v1T_eq_sum i₀ St hsrc y z n h1 h2).symm

end Fam

end Balaban.LargeField.Def7v2
