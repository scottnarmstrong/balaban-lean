/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.LocalGeneratorPoly
public import Balaban.SmallField.LocalGeneratorCovariance
public import Balaban.SmallField.GsSpecClass
public import Balaban.SmallField.Def6v2Inhabited

/-!
# A class member at the low index with the local generating sets `𝔹_j(X)`

The class structures `Terms`, `SFTermClausesStrong`, `IsSF2` instantiated at the separation index
`R₀(d, L)` (SF3TYPE option (a)), with the generating set of a polymer `X ∈ 𝒟_j` the minimal set
`𝔹_j(X) = localB j hj X hsep` of P3 (4.4)-(4.6) (cubes of side `M₁ L^n`, `M₁ = L^{m₁}`) and no
terms: `ℰ = ℳ = 0`, the class at the scale where no term has been produced.

* `localBZeroTerms`: the terms, `gs j X = 𝔹_j(X)` for `j ≤ k`;
* `sfTermClausesStrong_localBZeroTerms`: all clauses of `SFTermClausesStrong` on every field domain,
  for `L^{m₀} ∣ N₁` (polymers are unions of `M₁ L^j`-cubes, `isPolyDom_cubeUnion`), with
  `pavingGS` from `pavingGS_localB` and `gsStrong` from `gsSpecStrong_localB_of_isPolyDom`;
* `isSF2_localBZeroTerms`: membership in `IsSF2` at the index `R₀(d, L)` with the density `rho2`;
* `sfTermClausesStrong_localBZeroTerms_nonempty`: an inhabitant at `witnessConsts`.

The successor terms of a step are not of this form; their analyticity on `Ξ^c(𝔹_{k+1}(Y))` needs
the recomputation of P3 (4.46)-(4.47) (`Fluctuation.LocalSuccessorEngine`).
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.LargeField Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

/-- **The terms of the class at the low index with the local generating sets**: `ℰ = ℳ = 0` and
`gs j X = 𝔹_j(X) = localB j hj X hsep` (P3 (4.4)-(4.6)) for `j ≤ k`, the top set otherwise. -/
noncomputable def localBZeroTerms (d L N₁ m₁ k N : ℕ) [NeZero L] [NeZero N₁]
    (hsep : bgR0 d L ≤ minSep L (L ^ m₁)) : Terms d L N₁ m₁ k N (bgR0 d L) where
  E := fun _ _ _ _ _ => 0
  M := fun _ _ _ _ _ _ => 0
  gs := fun j X => if h : j ≤ k then localB j h X hsep else topGS d L N₁ m₁ k (bgR0 d L)

variable {hsep : bgR0 d L ≤ minSep L (L ^ m₁)}

theorem localBZeroTerms_gs {j : ℕ} (hjk : j ≤ k) (X : Set (CTorus d L N₁ m₁ k)) :
    (localBZeroTerms d L N₁ m₁ k N hsep).gs j X = localB j hjk X hsep := by
  simp [localBZeroTerms, hjk]

theorem Eloc_localBZeroTerms (m₀ j : ℕ) (y : CTorus d L N₁ m₁ k) (ψ h : Fld d L N₁ m₁ k N) :
    Eloc m₀ (localBZeroTerms d L N₁ m₁ k N hsep) j y ψ h = 0 := by
  simp [Eloc, localBZeroTerms]

theorem Mloc_localBZeroTerms (m₀ j : ℕ) (x : CTorus d L N₁ m₁ k) (ψ h g : Fld d L N₁ m₁ k N) :
    Mloc m₀ (localBZeroTerms d L N₁ m₁ k N hsep) j x ψ h g = 0 := by
  simp [Mloc, localBZeroTerms]

/-- **All clauses of `SFTermClausesStrong` for the zero terms with the sets `𝔹_j(X)`**, on every
field domain at the index `R₀(d, L)`, when `L^{m₀} ∣ N₁`. -/
theorem sfTermClausesStrong_localBZeroTerms {P : Consts} (hE₀ : 0 ≤ P.E₀)
    (hc9 : ∀ j, 0 < P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hN : L ^ P.m₀ ∣ N₁) (Dom : FieldDom d L N₁ m₁ k N (bgR0 d L)) :
    SFTermClausesStrong P Dom (localBZeroTerms d L N₁ m₁ k N hsep) where
  gs_spec := fun j hj1 hjk X hX => by
    rw [localBZeroTerms_gs hjk]
    have := gsSpecCore_localB (hj := hjk) (hsep := hsep) hj1 (isPolyDom_cubeUnion hjk hN hX)
    exact ⟨this.subset, this.noAbove⟩
  analyticE := fun j _ _ y X _ _ => analyticOnNhd_const
  analyticM := fun j _ _ x X _ _ => analyticOnNhd_const
  rotE := by intros; rfl
  pavingGS := fun j hj1 hjk X _ r hr i => by
    rw [localBZeroTerms_gs hjk, localBZeroTerms_gs hjk]
    exact pavingGS_localB hr i
  eucE := by intros; rfl
  eucEloc := by
    intro j _ hjk y r _ Ψ h _ _
    rw [Eloc_localBZeroTerms, Eloc_localBZeroTerms]
  rotM := by
    intro j _ _ x X _ _ R hR Ψ h g _ _
    show (0 : Fin N → ℂ) = R.mulVec 0
    simp
  eucM := by intros; rfl
  eucMloc := by
    intro j _ hjk x r _ Ψ h g _ _
    rw [Mloc_localBZeroTerms, Mloc_localBZeroTerms]
  localE := by intros; rfl
  localM := by intros; rfl
  boundE := by
    intro j _ _ y X _ _ Ψ h _
    show ‖(0 : ℂ)‖ ≤ _
    rw [norm_zero]
    exact mul_nonneg hE₀ (Real.exp_pos _).le
  boundM := by
    intro j _ _ x X _ _ Ψ h g _ _
    show vn (0 : Fin N → ℂ) < _
    rw [vn_zero]
    exact mul_pos (hc9 j) (Real.exp_pos _)
  gsStrong := fun j hj1 hjk X hX => by
    rw [localBZeroTerms_gs hjk]
    exact gsSpecStrong_localB_of_isPolyDom hN hj1 hX

/-- The strong term clauses with the local generating sets `𝔹_j(X)` at the low index are inhabited
(hard rule 10): the zero terms, every field domain, the constants `witnessConsts` (`m₀ = 0`). -/
theorem sfTermClausesStrong_localBZeroTerms_nonempty
    (Dom : FieldDom d L N₁ m₁ k N (bgR0 d L)) :
    Nonempty (SFTermClausesStrong witnessConsts Dom (localBZeroTerms d L N₁ m₁ k N hsep)) := by
  refine ⟨sfTermClausesStrong_localBZeroTerms (by simp [witnessConsts]) (fun j => ?_)
    (by simp [witnessConsts]) Dom⟩
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  simp only [witnessConsts, one_mul]
  positivity

/-- The observable composite `ℱ_k` of the local zero terms is the one of the whole-level zero
terms (both have `ℳ = 0`). -/
theorem Fcomp_localBZeroTerms (m₀ : ℕ) (a : ℕ → ℝ) (ν : ℝ)
    (D : BgData (topGS d L N₁ m₁ k (bgR0 d L)) N) (g : Fld d L N₁ m₁ k N) :
    Fcomp m₀ (localBZeroTerms d L N₁ m₁ k N hsep) a ν D g =
      Fcomp m₀ (zeroTerms d L N₁ m₁ k N (bgR0 d L)) a ν D g := by
  simp [Fcomp, Floc, Mloc_localBZeroTerms, Mloc_zero]

/-- **The class member at the low index with the local generating sets**: the zero terms with
`gs j X = 𝔹_j(X)` belong to `IsSF2` at the separation index `R₀(d, L)`, on every field domain, with
the density `rho2` and `E_k = 0`, when `L^{m₀} ∣ N₁` and the background hypotheses hold at that
index for the regime. -/
theorem isSF2_localBZeroTerms {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ}
    {Dom : FieldDom d L N₁ m₁ k N (bgR0 d L)} (hE₀ : 0 ≤ P.E₀)
    (hc9 : ∀ j, 0 < P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hN : L ^ P.m₀ ∣ N₁)
    (H : BgHyp d L k (bgR0 d L) (aIdeal L k (a k)) (Rg.sfBgMass k)) :
    IsSF2 P Rg β a Dom (localBZeroTerms d L N₁ m₁ k N hsep)
      (rho2 P Rg β a (localBZeroTerms d L N₁ m₁ k N hsep) 0) 0 := by
  have hT := sfTermClausesStrong_localBZeroTerms (hsep := hsep) (N := N) hE₀ hc9 hN Dom
  refine isSF2_rho2 hT.toSFTermClauses hT.gsStrong ?_
  intro Ψ₀ h₀ g D hD
  have h1 := im_Fcomp_zero H hD.2.1 P.m₀ g
  rw [← Fcomp_localBZeroTerms (hsep := hsep)] at h1
  have hE : Ecomp P.m₀ (localBZeroTerms d L N₁ m₁ k N hsep) (aIdeal L k (a k))
      (Rg.sfBgMass k) D = 0 := by
    simp [Ecomp, Edens, Eloc_localBZeroTerms]
  unfold expo2
  rw [hE]
  simp [Complex.add_im, Complex.mul_im, h1]

end Balaban.SmallField.GsSpec
