/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoefLimitV2
public import Balaban.LargeField.R.CoefRotPair
public import Balaban.LargeField.Def7v2Form

/-!
# The coefficient data of a small-field family: existence of `D1CorrLim`

For small-field data `sf` whose terms form a coefficient family (`CoefFam`) at every level
`1 ≤ j ≤ k`, and a physical field `h` of norm one, the source form `St = sourceOf sf.ν sf.Tm` and the
thermodynamic limits `v^{(j)}_1`, `v^{(j)}_2` of the whole-torus coefficients (P1 p. 147 (3.110))
exist: `D1CorrLim`.  The limits at the physical field `h` and at an orthonormal transverse
direction `e₂` are the limits at the coordinate axes (the coefficients are rotation invariant,
`CoefCtx.v1Loc_axis_eq`, `CoefCtx.v2Loc_axis_eq`), which exist by `CoefFam.exists_tendsto_v1T`,
`CoefFam.exists_tendsto_v2T`.
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.LargeField.Def7 Filter Topology Matrix

section D1

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}
  {P : Consts} {νk : ℝ} {Dom : ∀ (N₁ : ℕ) [NeZero N₁], FieldDom d L N₁ m₁ k N ϱ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ} {j : ℕ} {ρ : ℝ}

/-- On each torus of the sequence the whole-torus coefficient `v1T` at the physical field `Q e_{i₀}`
is the one at the axis `e_{i₀}`. -/
theorem CoefFam.v1T_axis_eq (fam : CoefFam P νk Dom Tm j ρ) {i₀ : Fin N}
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N)
    (hsrc : ∀ (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • b)))
    {w : Fin N → ℂ} (hw : w = cmat Q *ᵥ (Pi.single i₀ 1 : Fin N → ℂ)) (n : ℕ)
    (y x : Localization.CTorus d L (torusSeq L P.m₀ n) m₁ k) :
    (haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩;
      v1T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k νk j) w y x) =
    (haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩;
      v1T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k νk j) (Pi.single i₀ 1) y x) := by
  classical
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  unfold v1T
  refine finsum_mem_congr rfl fun X hX => ?_
  exact (fam.ctx n).v1Loc_axis_eq hQ hX.1 hX.2 _
    (fun Ψ b => hsrc (torusSeq L P.m₀ n) y X Ψ b) hw x

/-- The same for the transverse coefficient `v2T` at the pair `(Q e_{i₀}, Q e_{i₁})`. -/
theorem CoefFam.v2T_axis_eq (fam : CoefFam P νk Dom Tm j ρ) {i₀ i₁ : Fin N}
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N)
    (hsrc : ∀ (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • b)))
    {w0 w1 : Fin N → ℂ} (hw0 : w0 = cmat Q *ᵥ (Pi.single i₀ 1 : Fin N → ℂ))
    (hw1 : w1 = cmat Q *ᵥ (Pi.single i₁ 1 : Fin N → ℂ)) (n : ℕ)
    (y x : Localization.CTorus d L (torusSeq L P.m₀ n) m₁ k) :
    (haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩;
      v2T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k νk j) w0 w1 y x) =
    (haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩;
      v2T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k νk j) (Pi.single i₀ 1) (Pi.single i₁ 1)
        y x) := by
  classical
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  unfold v2T
  refine finsum_mem_congr rfl fun X hX => ?_
  exact (fam.ctx n).v2Loc_axis_eq hQ hX.1 hX.2 _
    (fun Ψ b => hsrc (torusSeq L P.m₀ n) y X Ψ b) hw0 hw1 x

end D1

section Exists

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **The coefficient data of a small-field family exist.**  Let `sf` be small-field data whose
terms form a coefficient family at every level `1 ≤ j ≤ k` (for the constants `P` and the mass
`ν_k`), and `h` a physical field of norm one.  Then the source form of the terms and the
thermodynamic limits of the whole-torus coefficients exist: `D1CorrLim`. -/
theorem exists_d1CorrLim {P : Consts} (sf : SFData d L m₁ k N ϱ)
    (Dom : ∀ (N₁ : ℕ) [NeZero N₁], FieldDom d L N₁ m₁ k N ϱ)
    (hv : EuclideanSpace ℝ (Fin N)) (hhv : ‖hv‖ = 1)
    (fams : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ, CoefFam P (sf.ν k) Dom sf.Tm j ρ) :
    ∃ (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N) (vc : CorrCoef d),
      D1CorrLim P.m₀ sf St hv vc := by
  classical
  have hN : 0 < N := by
    by_contra h
    have : N = 0 := by omega
    subst this
    have : hv = 0 := Subsingleton.elim _ _
    rw [this] at hhv; simp at hhv
  set i₀ : Fin N := ⟨0, hN⟩ with hi₀
  obtain ⟨Q1, hQ1, hw1⟩ := exists_rot_axis i₀ hv hhv
  let St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N :=
    fun N₁ _ => sourceOf sf.ν (sf.Tm N₁)
  have hsrc : ∀ j (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (sf.Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k (sf.ν k) j : ℝ) : ℂ)⁻¹ • b)) :=
    fun j N₁ _ y Y Ψ b => rfl
  -- the radial sequences
  let v1r : ℕ → ℕ → (Fin d → ℤ) → ℂ := fun j n z =>
    haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
    v1T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k (sf.ν k) j) (Pi.single i₀ 1) 0 (blockPt j z)
  let v2r : ℕ → ℕ → (Fin d → ℤ) → ℂ := fun j n z =>
    if h : ∃ i₁ : Fin N, i₁ ≠ i₀ then
      haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
      v2T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k (sf.ν k) j) (Pi.single i₀ 1)
        (Pi.single h.choose 1) 0 (blockPt j z)
    else 0
  refine ⟨St, ⟨fun j z => limUnder atTop (fun n => v1r j n z),
    fun j z => limUnder atTop (fun n => v2r j n z)⟩, ?_, ?_, ?_⟩
  · intro N₁ _ j _ _ _ y X Ψ b
    exact hsrc j N₁ y X Ψ b
  · intro j hj1 hjk z
    obtain ⟨ρ, fam⟩ := fams j hj1 hjk
    have hex : ∃ ℓ, Tendsto (fun n => v1r j n z) atTop (nhds ℓ) := by
      have := fam.exists_tendsto_v1T i₀ St (hsrc j) 0 z
      simpa [v1r, blockPt_zero] using this
    have h := tendsto_nhds_limUnder hex
    refine h.congr fun n => ?_
    simp only [v1r]
    have := fam.v1T_axis_eq hQ1 St (hsrc j) hw1 n 0 (blockPt j z)
    exact this.symm
  · intro j hj1 hjk e₂ he hort z
    obtain ⟨ρ, fam⟩ := fams j hj1 hjk
    have hex2 : ∃ i₁ : Fin N, i₁ ≠ i₀ := by
      by_contra hno
      push Not at hno
      have h1 : ∀ i, i = i₀ := fun i => hno i
      have hv0 : hv i₀ ^ 2 = 1 := by
        have h2 : ∑ i, ‖hv i‖ ^ 2 = 1 := by
          have := hhv
          rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at this
          exact this
        rw [Finset.sum_eq_single i₀ (fun b _ hb => absurd (h1 b) hb) (by simp)] at h2
        simpa using h2
      have he0 : e₂ i₀ ^ 2 = 1 := by
        rw [Finset.sum_eq_single i₀ (fun b _ hb => absurd (h1 b) hb) (by simp)] at he
        exact he
      rw [Finset.sum_eq_single i₀ (fun b _ hb => absurd (h1 b) hb) (by simp)] at hort
      have : hv i₀ ≠ 0 := fun h => by rw [h] at hv0; norm_num at hv0
      have : e₂ i₀ = 0 := by
        rcases mul_eq_zero.1 hort with h | h
        · exact absurd h this
        · exact h
      rw [this] at he0; norm_num at he0
    set i₁ := hex2.choose with hi₁
    have hne : i₁ ≠ i₀ := hex2.choose_spec
    set b : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 e₂ with hb
    have hb1 : ‖b‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp only [hb, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
      rw [he, Real.sqrt_one]
    have hab : inner ℝ hv b = 0 := by
      simp only [hb, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      rw [← hort]
      exact Finset.sum_congr rfl fun i _ => by ring
    obtain ⟨Q2, hQ2, hwa, hwb⟩ := exists_rot_pair i₀ i₁ hne.symm hv b hhv hb1 hab
    have hex : ∃ ℓ, Tendsto (fun n => v2r j n z) atTop (nhds ℓ) := by
      have := fam.exists_tendsto_v2T i₀ i₁ St (hsrc j) 0 z
      simpa [v2r, blockPt_zero, hex2, hi₁] using this
    have h := tendsto_nhds_limUnder hex
    refine h.congr fun n => ?_
    simp only [v2r, hex2, dite_true]
    have := fam.v2T_axis_eq hQ2 St (hsrc j) hwa hwb n 0 (blockPt j z)
    exact this.symm

end Exists

end Balaban.LargeField.Def7v2
