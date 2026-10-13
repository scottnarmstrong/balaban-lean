/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RadialCoefficientLimit
public import Balaban.SmallField.Def6Inhabited
public import Balaban.LargeField.Def7v2

/-!
# The hypotheses of `aCoef_avgFamilyA_eq_v1` are jointly satisfiable

On the landed class witness of `Def6Inhabited` (zero terms, `d = L = 3`, `N = 2`) there is a `D1Corr`
datum (coefficients `v₁ = v₂ = 0`).  `nonempty_final_hypotheses` says that the class member, the
numeric premises `MomNum`, the datum `D1Corr` for the same small-field data, the unit field and a
pair of distinct components exist together; `aCoef_avgFamilyA_eq_v1_witness` is the final theorem
`aCoef_avgFamilyA_eq_v1` at that instance.  The witness class is the zero class, so both sides of the
identity are `0`: this shows that the hypotheses are consistent, not that the kernel is nonzero.
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.LargeField.Def7 Filter Topology

/-- The small-field data of the zero class witness at the scale `k`. -/
noncomputable def zSF (m₁ k : ℕ) (ϱ : ℝ) : SFData 3 3 m₁ k 2 ϱ where
  β := witnessβ
  ν := witnessν k
  z := fun _ => 1
  a := witnessa
  E := fun _ => 0
  Tm := zeroFam 3 3 m₁ k 2 ϱ
  Rt := fun _ _ _ _ _ _ _ => 0
  corr := fun _ _ _ _ _ _ _ => 0

/-- `(D1-corr)` for the zero class witness, with the coefficients `v₁ = v₂ = 0`. -/
theorem zD1Corr (m₁ k : ℕ) (ϱ : ℝ) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin 2)) :
    D1Corr m₀ (zSF m₁ k ϱ) (fun N₁ _ => sourceOf (zSF m₁ k ϱ).ν ((zSF m₁ k ϱ).Tm N₁)) hv
      ⟨fun _ _ => 0, fun _ _ => 0⟩ where
  src_pos := fun _ _ _ _ _ _ _ _ _ _ => rfl
  v1_lim := by
    intro j _ _ z
    have h : ∀ n : ℕ, (haveI : NeZero (torusSeq 3 m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
        v1T m₀ (sourceOf (zSF m₁ k ϱ).ν ((zSF m₁ k ϱ).Tm (torusSeq 3 m₀ n))) j
          (nuIdeal 3 k ((zSF m₁ k ϱ).ν k) j) (hC hv) 0 (blockPt j z)) = 0 := by
      intro n
      have : NeZero (torusSeq 3 m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
      unfold v1T
      refine finsum_mem_eq_zero_of_forall_eq_zero fun X _ => ?_
      exact v1Loc_zero _ _ _ _
    simp only [h]
    exact tendsto_const_nhds
  v2_lim := by
    intro j _ _ e₂ _ _ z
    have h : ∀ n : ℕ, (haveI : NeZero (torusSeq 3 m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
        v2T m₀ (sourceOf (zSF m₁ k ϱ).ν ((zSF m₁ k ϱ).Tm (torusSeq 3 m₀ n))) j
          (nuIdeal 3 k ((zSF m₁ k ϱ).ν k) j) (hC hv) (fun i => (e₂ i : ℂ)) 0 (blockPt j z)) = 0 := by
      intro n
      have : NeZero (torusSeq 3 m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
      unfold v2T
      refine finsum_mem_eq_zero_of_forall_eq_zero fun X _ => ?_
      exact v2Loc_zero _ _ _ _ _
    simp only [h]
    exact tendsto_const_nhds
  corr_eq := by
    intro N₁ _ j _ _ y x ψ _ _
    show (0 : ℂ) = _
    simp [corrPair]

/-- The unit field `e₀` of `ℝ²`. -/
noncomputable def zhv : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

theorem norm_zhv : ‖zhv‖ = 1 := by simp [zhv]

/-- **The hypotheses of `aCoef_avgFamilyA_eq_v1` are jointly satisfiable** (non-vacuity, T5): the
class member, `MomNum`, `D1Corr` for the same small-field data, the unit field and distinct
components exist at every scale `1 ≤ j ≤ k`. -/
theorem nonempty_final_hypotheses (m₁ k j : ℕ) (ϱ : ℝ) (hϱ : bgR0 3 3 ≤ ϱ) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) :
    ∃ (P : Consts) (ρd : ∀ (N₁ : ℕ) [NeZero N₁], (Localization.CTorus 3 3 N₁ m₁ k → Fin 2 → ℝ) → (Fin 2 → ℝ) →
        (Localization.CTorus 3 3 N₁ m₁ k → Fin 2 → ℝ) → ℝ) (Ek : ℕ → ℝ),
      IsSFFamily P (zSF m₁ k ϱ).β (zSF m₁ k ϱ).ν (zSF m₁ k ϱ).a (zSF m₁ k ϱ).Tm ρd Ek ∧
      MomNum 3 3 2 k j ϱ P ∧
      D1Corr P.m₀ (zSF m₁ k ϱ) (fun N₁ _ => sourceOf (zSF m₁ k ϱ).ν ((zSF m₁ k ϱ).Tm N₁)) zhv
        ⟨fun _ _ => 0, fun _ _ => 0⟩ ∧ ‖zhv‖ = 1 ∧ (1 : Fin 2) ≠ 0 :=
  ⟨witnessConsts (witnessα₀ j), _, _, isSFFamily_witness m₁ k j ϱ hϱ,
    momNum_witness k j ϱ hϱ hj1 hjk, zD1Corr m₁ k ϱ _ zhv, norm_zhv, by decide⟩

/-- **`aCoef_avgFamilyA_eq_v1` at the witness**: both sides are `0` (the witness is the zero class). -/
theorem aCoef_avgFamilyA_eq_v1_witness (m₁ k j : ℕ) (ϱ : ℝ) (hϱ : bgR0 3 3 ≤ ϱ) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (x : SmallField.Site 3) :
    aCoef (avgFamilyA (witnessConsts (witnessα₀ j)) witnessβ (witnessν k) witnessa
        (zeroFam 3 3 m₁ k 2 ϱ) j 0 (nuIdeal 3 k (witnessν k k) j)
        (anisoRadius 3 3 2 (witnessConsts (witnessα₀ j)) j)) 0 (nuIdeal 3 k (witnessν k k) j) x =
      0 :=
  aCoef_avgFamilyA_eq_v1 (sf := zSF m₁ k ϱ) (zD1Corr m₁ k ϱ _ zhv)
    (isSFFamily_witness m₁ k j ϱ hϱ) (momNum_witness k j ϱ hϱ hj1 hjk) (i₁ := 1)
    (by decide) norm_zhv x

end Balaban.LargeField.Def7v2
