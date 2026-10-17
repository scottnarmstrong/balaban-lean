/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RhoZeroPhysical
public import Balaban.LargeField.R.RRemovedExponent
import Mathlib
import Balaban.LargeField.R.PsiZeroAnalytic
import Balaban.LargeField.R.PsiZeroSmooth

/-!
# The reference density with the action restricted to `Z` (Definition III.8.1, P7 (1.5); Lemma III.8.2)

P7 (1.5) and LF-RECONSTRUCTION Definition III.8.1 define
`ρ_{k,0}(Z) = χ_{Z₀} exp(-β_k A*_k(Z; ψ_k, φ_k(𝔹_k(U_k); ψ̃_k)))`: the action is the action **restricted to the
component `Z`** (half-bond convention on `∂Z`, with its `ν`-term), evaluated at the massless background of the
generating set `𝔹_k(U_k)`, `U_k = Z^≈`.  The landed `rhoZero` (`RhoZero.lean`) uses the action `effAction` on all of
`Ω₁(𝔹_k(U_k))` (LF4R-PLAN §4.3 item 2, §5).

Units.  `β₀` is the coupling in fine units, `β_k = betaK d L k β₀ = β₀ L^{k(d-2)}`; the restricted action is written in
fine units, `A_D = actionRegionR D a ν` (the action of (2.58′), `ActionConvDef.lean`), so `β₀ A_D = β_k A*_k(Z)`.  The
cutoff `χ_{Z₀}` has radius `C₆ β_k^{-1/2} p₀(β_k)` about the massless centre `ψ⁰_k` (`psiZero`), as in `rhoZero`.

* `dataRH G ψ h`: the data `lift_k ψ_k` with the constant external field `h` (`dataR` has `h = 0`);
  `psiZeroData_eq_dataRH`: it is the datum `psiZeroData` of (2.58′) at `ψ⁰_k`.
* `actionZ G a Zr ν h ψ = A_{Zr}(ψ̃, φ_k(𝔹; ψ̃))`: the restricted action (fine units) at the massless background of the
  lifted block field; `re_actionRegionC_eq_actionZ`: it is the real part of the complex action of (2.58′).
* `rhoZeroRestrictedWith` (any centre), `rhoZeroRestricted` (the source object: centre `ψ⁰_k`, `C₆ = 3dD₀(K₆+1)`).
* Characterization: `rhoZeroRestrictedWith_of_cutoff`, `rhoZeroRestrictedWith_eq_zero` (the value), and
  `rhoZeroRestricted_eq_mul`: `ρ^Z = ρ_{landed} · e^{β₀ (A_{Ω₁} - A_Z)}` (`ρ_{landed} = rhoZero` at `β_k`).
* Lemma III.8.2 for the restricted density: `denominatorRestricted_eq` (the identity with
  `Ẽ₀^Z = tildeE0Restricted`, and positivity of the integral: unconditional), and
  `denominatorRestricted_bounds_of_osc` (`|Ẽ₀^Z - Ẽ₀| ≤ E`, `|Ẽ₀^Z| ≤ C_Ẽ D₀^d + E`) under the oscillation bound
  `|β₀ (A_{Ω₁} - A_Z)(ψ) - β₀ (A_{Ω₁} - A_Z)(ψ⁰_k)| ≤ E` on the cutoff.  This bound is the ingredient of P7 (3.3)-(3.4)
  that is not landed: the first variation of `A*_k(Z)` at `ψ⁰_k` in the directions of `Z₀` is not `0` (only that of
  the action on `Ω₁` is, P7 (2.52)); it is the surface term on `st(Z)` and the `ν`-term, bounded in P7 by the decay of
  `δφ_k` from `Z₀` (the core-to-action response, Q13-SHARED (2.4), open).
* `removedFactor_le_of_den_eq_AZ`, `removedFactor_le_restricted`: (2.58′) for the removed outcome with the restricted
  denominator, without the term `A_den - A_Z` of `removedFactor_le`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background MeasureTheory ActionConv

section Data

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)

/-- The data `lift_k ψ_k` of a real block field `ψ_k` with the constant external field `h ∈ ℝ^N` on `Ω₁`. -/
noncomputable def dataRH (ψ : BlockField d L N₀ k N) (h : Fin N → ℝ) : BgData G N :=
  liftSingle G (fun z i => ((ψ z i : ℝ) : ℂ)) (fun i => ((h i : ℝ) : ℂ))

variable {G}

theorem dataRH_isReal (ψ : BlockField d L N₀ k N) (h : Fin N → ℝ) : (dataRH G ψ h).IsReal := by
  intro x i
  constructor
  · by_cases hx : x ∈ dataSites G
    · simp [dataRH, liftSingle_Ψ G _ _ hx]
    · simp [(dataRH G ψ h).Ψ_zero x hx]
  · by_cases hx : x ∈ G.Ω 1
    · simp [dataRH, liftSingle_h G _ _ hx]
    · simp [(dataRH G ψ h).h_zero x hx]

theorem dataR_isReal_of_block (ψ : BlockField d L N₀ k N) : (dataR G ψ).IsReal := by
  intro x i
  constructor
  · by_cases hx : x ∈ dataSites G
    · rw [dataR_Ψ G ψ hx i]; simp
    · simp [(dataR G ψ).Ψ_zero x hx]
  · by_cases hx : x ∈ G.Ω 1
    · rw [dataR_h G ψ hx i]; simp
    · simp [(dataR G ψ).h_zero x hx]

theorem dataRH_Ψ (ψ : BlockField d L N₀ k N) (h : Fin N → ℝ) : (dataRH G ψ h).Ψ = (dataR G ψ).Ψ := by
  funext x
  by_cases hx : x ∈ dataSites G
  · funext i
    rw [dataR_Ψ G ψ hx i]
    simp [dataRH, liftSingle_Ψ G _ _ hx, liftR]
  · rw [(dataRH G ψ h).Ψ_zero x hx, (dataR G ψ).Ψ_zero x hx]

/-- At mass `0` the background of `dataRH` is that of `dataR` (it does not read `h`). -/
theorem bgField_dataRH (a : ℕ → ℝ) (ψ : BlockField d L N₀ k N) (h : Fin N → ℝ) :
    bgField G a 0 (dataRH G ψ h) = bgField G a 0 (dataR G ψ) :=
  bgField_congr_Ψ (dataRH_isReal ψ h) (dataR_isReal_of_block ψ) (dataRH_Ψ ψ h)

/-- The datum `psiZeroData` of (2.58′) is `dataRH` of the block field `ψ` read off the layer `k` of `ψ⁰`. -/
theorem psiZeroData_eq_dataRH (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    (ψ : BlockField d L N₀ k N) (hψ : ∀ z i, ψ0 ⟨k, z⟩ i = ψ z i) :
    psiZeroData G ψ0 h = dataRH G ψ h := by
  unfold psiZeroData dataRH
  congr 1
  funext z i
  rw [hψ]

end Data

section ActionZ

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)

/-- **The restricted action `A*_k(Z; ψ_k, φ_k(𝔹_k(U_k); ψ̃_k))` of P7 (1.5)** in fine units: the action `A_D` of the
region `Zr` (the cubes of the component `Z` in `𝔹_k(U_k)`; half-bond weights on `∂Z`; the `ν`-term with the
external field `h`) at the massless Def-5 background of the lift of the block field `ψ`. -/
noncomputable def actionZ (Zr : Region G) (ν : ℝ) (h : Fin N → ℝ) (ψ : BlockField d L N₀ k N) : ℝ :=
  actionRegionR Zr a ν (dataRH G ψ h) (bgField G a 0 (dataRH G ψ h))

variable {G a}

theorem actionZ_eq (Zr : Region G) (ν : ℝ) (h : Fin N → ℝ) (ψ : BlockField d L N₀ k N) :
    actionZ G a Zr ν h ψ = actionRegionR Zr a ν (dataRH G ψ h) (bgField G a 0 (dataR G ψ)) := by
  rw [actionZ, bgField_dataRH]

theorem actionRegionR_nonneg (D : Region G) {ν : ℝ} (ha : ∀ j, 0 ≤ a j) (hν : 0 ≤ ν) (Dat : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) : 0 ≤ actionRegionR D a ν Dat φ := by
  unfold actionRegionR
  have h1 : 0 ≤ ∑ x ∈ D.sites, (a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2) *
      ∑ i, ‖Dat.Ψ x i - blockAvg G φ x i‖ ^ 2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (div_nonneg (ha _) (by positivity))
      (Finset.sum_nonneg fun i _ => by positivity)
  have h2 : 0 ≤ ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d, D.starWeight x μ *
      ∑ i, ‖barField G Dat.Ψ φ (x + Pi.single μ 1) i - barField G Dat.Ψ φ x i‖ ^ 2 := by
    refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun μ _ => mul_nonneg ?_
      (Finset.sum_nonneg fun i _ => by positivity)
    unfold Region.starWeight
    split_ifs <;> norm_num
  have h3 : 0 ≤ ∑ x ∈ D.sites, ∑ i, ‖svec G φ x i - Dat.h x i‖ ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun i _ => by positivity
  have : 0 ≤ ν / 2 := by positivity
  positivity

theorem actionZ_nonneg (Zr : Region G) {ν : ℝ} (ha : ∀ j, 0 ≤ a j) (hν : 0 ≤ ν) (h : Fin N → ℝ)
    (ψ : BlockField d L N₀ k N) : 0 ≤ actionZ G a Zr ν h ψ :=
  actionRegionR_nonneg Zr ha hν _ _

/-- **The restricted action is the action of (2.58′)**: for a block field whose background is real (e.g. on the
tube, `theorem71`), `Re(β₀ A_D(lift ψ, φ(ψ)))` of the complex bilinear action is `β₀ · actionZ`. -/
theorem re_actionRegionC_eq_actionZ (Zr : Region G) (ν : ℝ) (h : Fin N → ℝ) (ψ : BlockField d L N₀ k N)
    (hφ : ∀ p, (bgField G a 0 (dataRH G ψ h) p).im = 0) (β0 : ℝ) :
    ((β0 : ℂ) * actionRegionC Zr a ν (dataRH G ψ h) (bgField G a 0 (dataRH G ψ h))).re =
      β0 * actionZ G a Zr ν h ψ := by
  rw [actionRegionC_eq_ofReal Zr a ν (dataRH_isReal ψ h) hφ, Complex.re_ofReal_mul]
  rfl

end ActionZ

section Density

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)

/-- **The reference density with the action restricted to `Z`, for an arbitrary centre `ψ⁰`**: the cutoff
`χ_{Z₀}` of radius `C₆ β_k^{-1/2} p₀` (`β_k = betaK d L k β₀`) about `ψ⁰` times `exp(-β₀ A_{Zr})` at the merged field
(`ψ_k↾Z₀ = u`, `ψ_k` fixed off `Z₀`). -/
noncomputable def rhoZeroRestrictedWith (Zr : Region G) (ν : ℝ) (h : Fin N → ℝ)
    (Zf : Finset (Torus d (N₀ * L ^ (k - k)))) (ψ0 ψk : BlockField d L N₀ k N) (C6 β0 p0 : ℝ)
    (u : SuppSpace Zf N) : ℝ :=
  chiZeroCut ψ0 (zeroRadius C6 (betaK d L k β0) p0) u *
    Real.exp (-β0 * actionZ G a Zr ν h (mergeField Zf ψk u))

variable {G a}

theorem rhoZeroRestrictedWith_nonneg (Zr : Region G) (ν : ℝ) (h : Fin N → ℝ)
    (Zf : Finset (Torus d (N₀ * L ^ (k - k)))) (ψ0 ψk : BlockField d L N₀ k N) (C6 β0 p0 : ℝ)
    (u : SuppSpace Zf N) : 0 ≤ rhoZeroRestrictedWith G a Zr ν h Zf ψ0 ψk C6 β0 p0 u := by
  unfold rhoZeroRestrictedWith chiZeroCut
  split_ifs <;> positivity

theorem rhoZeroRestrictedWith_eq_zero (Zr : Region G) (ν : ℝ) (h : Fin N → ℝ)
    (Zf : Finset (Torus d (N₀ * L ^ (k - k)))) (ψ0 ψk : BlockField d L N₀ k N) (C6 β0 p0 : ℝ)
    (u : SuppSpace Zf N) (hc : ¬ ZeroCutoff ψ0 (zeroRadius C6 (betaK d L k β0) p0) u) :
    rhoZeroRestrictedWith G a Zr ν h Zf ψ0 ψk C6 β0 p0 u = 0 := by
  simp [rhoZeroRestrictedWith, chiZeroCut, hc]

theorem rhoZeroRestrictedWith_of_cutoff (Zr : Region G) (ν : ℝ) (h : Fin N → ℝ)
    (Zf : Finset (Torus d (N₀ * L ^ (k - k)))) (ψ0 ψk : BlockField d L N₀ k N) (C6 β0 p0 : ℝ)
    (u : SuppSpace Zf N) (hc : ZeroCutoff ψ0 (zeroRadius C6 (betaK d L k β0) p0) u) :
    rhoZeroRestrictedWith G a Zr ν h Zf ψ0 ψk C6 β0 p0 u =
      Real.exp (-β0 * actionZ G a Zr ν h (mergeField Zf ψk u)) := by
  simp [rhoZeroRestrictedWith, chiZeroCut, hc]

/-- `β_k A*_k = β₀ A` for the normalized effective action: `betaK β₀ · effActionNorm = β₀ · effAction`. -/
theorem betaK_mul_effActionNorm (β0 : ℝ) (ψ : BlockField d L N₀ k N) :
    betaK d L k β0 * effActionNorm G a ψ = β0 * effAction G a ψ := by
  have hL : (0 : ℝ) < (L : ℝ) ^ (k * (d - 2)) := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  unfold betaK effActionNorm
  field_simp

/-- **The restricted density through the landed one**: `ρ^Z = ρ_{landed} · e^{β₀ (A_{Ω₁} - A_Z)}` at the merged field,
`ρ_{landed} = rhoZeroWith` (the action on all of `Ω₁(𝔹_k(U_k))`) at `β_k = betaK β₀`, same centre and cutoff. -/
theorem rhoZeroRestrictedWith_eq_mul (Zr : Region G) (ν : ℝ) (h : Fin N → ℝ)
    (Zf : Finset (Torus d (N₀ * L ^ (k - k)))) (ψ0 ψk : BlockField d L N₀ k N) (C6 β0 p0 : ℝ)
    (u : SuppSpace Zf N) :
    rhoZeroRestrictedWith G a Zr ν h Zf ψ0 ψk C6 β0 p0 u =
      rhoZeroWith G a Zf ψ0 ψk C6 (betaK d L k β0) p0 u *
        Real.exp (β0 * (effAction G a (mergeField Zf ψk u) - actionZ G a Zr ν h (mergeField Zf ψk u))) := by
  unfold rhoZeroRestrictedWith rhoZeroWith
  have e : -betaK d L k β0 * effActionNorm G a (mergeField Zf ψk u) = -(β0 * effAction G a (mergeField Zf ψk u)) := by
    rw [neg_mul, betaK_mul_effActionNorm]
  rw [e, mul_assoc, ← Real.exp_add]
  congr 2
  ring

end Density

section Cont

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {α : Type*} [TopologicalSpace α] {S : Set α}

theorem continuousOn_svec {φ : α → G.Ω 1 × Fin N → ℂ} (hφ : ContinuousOn φ S)
    (y : Torus d (N₀ * L ^ k)) (i : Fin N) : ContinuousOn (fun p => svec G (φ p) y i) S := by
  by_cases hy : y ∈ G.Ω 1
  · have : (fun p => svec G (φ p) y i) = fun p => φ p (⟨y, hy⟩, i) :=
      funext fun p => svec_of_mem G (φ p) ⟨y, hy⟩ i
    rw [this]
    exact (continuous_apply _).comp_continuousOn hφ
  · have : (fun p => svec G (φ p) y i) = fun _ => 0 := funext fun p => svec_of_not_mem G (φ p) hy i
    rw [this]
    exact continuousOn_const

theorem continuousOn_blockAvg {φ : α → G.Ω 1 × Fin N → ℂ} (hφ : ContinuousOn φ S)
    (x : Torus d (N₀ * L ^ k)) (i : Fin N) : ContinuousOn (fun p => blockAvg G (φ p) x i) S := by
  unfold blockAvg
  exact continuousOn_const.mul (continuousOn_finsetSum _ fun y _ => continuousOn_svec hφ y i)

theorem continuousOn_barField {Ψ : α → Torus d (N₀ * L ^ k) → Fin N → ℂ} {φ : α → G.Ω 1 × Fin N → ℂ}
    (hΨ : ContinuousOn Ψ S) (hφ : ContinuousOn φ S) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    ContinuousOn (fun p => barField G (Ψ p) (φ p) x i) S := by
  unfold barField
  by_cases hx : x ∈ G.Ω 1
  · simp only [hx, dite_true]
    exact (continuous_apply _).comp_continuousOn hφ
  · simp only [hx, dite_false]
    exact (continuous_apply i).comp_continuousOn ((continuous_apply x).comp_continuousOn hΨ)

/-- The restricted action is continuous in the data and the field. -/
theorem continuousOn_actionRegionR (D : Region G) (a : ℕ → ℝ) (ν : ℝ) {Dat : α → BgData G N}
    {φ : α → G.Ω 1 × Fin N → ℂ} (hΨ : ContinuousOn (fun p => (Dat p).Ψ) S)
    (hh : ContinuousOn (fun p => (Dat p).h) S) (hφ : ContinuousOn φ S) :
    ContinuousOn (fun p => actionRegionR D a ν (Dat p) (φ p)) S := by
  have hΨc : ∀ x i, ContinuousOn (fun p => (Dat p).Ψ x i) S := fun x i =>
    (continuous_apply i).comp_continuousOn ((continuous_apply x).comp_continuousOn hΨ)
  have hhc : ∀ x i, ContinuousOn (fun p => (Dat p).h x i) S := fun x i =>
    (continuous_apply i).comp_continuousOn ((continuous_apply x).comp_continuousOn hh)
  unfold actionRegionR
  refine ((continuousOn_const.mul ?_).add (continuousOn_const.mul ?_)).add (continuousOn_const.mul ?_)
  · exact continuousOn_finsetSum _ fun x _ => continuousOn_const.mul (continuousOn_finsetSum _ fun i _ =>
      ((hΨc x i).sub (continuousOn_blockAvg hφ x i)).norm.pow 2)
  · exact continuousOn_finsetSum _ fun x _ => continuousOn_finsetSum _ fun μ _ => continuousOn_const.mul
      (continuousOn_finsetSum _ fun i _ =>
        ((continuousOn_barField hΨ hφ _ i).sub (continuousOn_barField hΨ hφ x i)).norm.pow 2)
  · exact continuousOn_finsetSum _ fun x _ => continuousOn_finsetSum _ fun i _ =>
      ((continuousOn_svec hφ x i).sub (hhc x i)).norm.pow 2

variable (G) in
theorem dataRH_h_eq (ψ ψ' : BlockField d L N₀ k N) (h : Fin N → ℝ) :
    (dataRH G ψ h).h = (dataRH G ψ' h).h := by
  funext x
  by_cases hx : x ∈ G.Ω 1
  · simp [dataRH, liftSingle_h G _ _ hx]
  · rw [(dataRH G ψ h).h_zero x hx, (dataRH G ψ' h).h_zero x hx]

/-- **The restricted action is continuous on the tube** `Ψ̃(𝔹; τ)`, `τ ≤ min (c₀, c₁)` (the massless background is
continuous there, `continuousOn_bgField`). -/
theorem continuousOn_actionZ {a : ℕ → ℝ} (H : BgHyp d L k ϱ a 0) {τ : ℝ} (hτ : 0 < τ)
    (hτ0 : τ ≤ bgC0 d L N) (hτ1 : τ ≤ bgC1 d L N) (Zr : Region G) (ν : ℝ) (h : Fin N → ℝ) :
    ContinuousOn (actionZ G a Zr ν h) {ψ : BlockField d L N₀ k N | TubeOn G Set.univ τ ψ} := by
  have e : actionZ G a Zr ν h =
      fun ψ => actionRegionR Zr a ν (dataRH G ψ h) (bgField G a 0 (dataR G ψ)) :=
    funext fun ψ => actionZ_eq Zr ν h ψ
  rw [e]
  refine continuousOn_actionRegionR Zr a ν ?_ ?_ (continuousOn_bgField H hτ hτ0 hτ1)
  · have e2 : (fun ψ : BlockField d L N₀ k N => (dataRH G ψ h).Ψ) = fun ψ => (rawMap G ψ).1 :=
      funext fun ψ => dataRH_Ψ ψ h
    rw [e2]
    exact ((contDiff_rawMap (n := 0) G).continuous.fst).continuousOn
  · have e2 : (fun ψ : BlockField d L N₀ k N => (dataRH G ψ h).h) = fun _ => (dataRH G 0 h).h :=
      funext fun ψ => dataRH_h_eq G ψ 0 h
    rw [e2]
    exact continuousOn_const

end Cont

section Ball

variable {Z : Type*} [Fintype Z] {N : ℕ}

theorem siteBall_subset_gaussCube {r : ℝ} (hr : 0 < r) :
    siteBall (Z := Z) (N := N) r ⊆ gaussCube (ι := Z × Fin N) r := by
  intro y hy j
  have h1 : y j ^ 2 ≤ ∑ i, y (j.1, i) ^ 2 :=
    Finset.single_le_sum (f := fun i => y (j.1, i) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j.2)
  exact abs_lt_of_sq_lt_sq (h1.trans_lt (hy j.1)) hr.le

/-- **A truncated exponential on a site ball is integrable with positive integral**: for `A` continuous on
`siteBall r` with `β A ≥ 0` there. -/
theorem siteBall_density_integrable_pos {A : EuclideanSpace ℝ (Z × Fin N) → ℝ} {β r : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn A (siteBall r)) (hA : ∀ y ∈ siteBall (Z := Z) (N := N) r, 0 ≤ β * A y) :
    Integrable ((siteBall (Z := Z) (N := N) r).indicator (fun y => Real.exp (-β * A y))) ∧
      0 < ∫ y, (siteBall (Z := Z) (N := N) r).indicator (fun y => Real.exp (-β * A y)) y := by
  have hmeas : MeasurableSet (siteBall (Z := Z) (N := N) r) := (isOpen_siteBall r).measurableSet
  have hasm : AEStronglyMeasurable ((siteBall (Z := Z) (N := N) r).indicator
      (fun y => Real.exp (-β * A y))) volume := by
    rw [aestronglyMeasurable_indicator_iff hmeas]
    exact (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hcont)).aestronglyMeasurable hmeas
  have hmc : MeasurableSet (gaussCube (ι := Z × Fin N) r) := measurableSet_gaussCube r
  have hvol : volume (gaussCube (ι := Z × Fin N) r) ≠ ⊤ := by
    intro h
    have h1 := volume_gaussCube (ι := Z × Fin N) hr
    rw [h, ENNReal.toReal_top] at h1
    have h2 : 0 < (2 * r) ^ Fintype.card (Z × Fin N) := by positivity
    linarith
  have hg : Integrable ((gaussCube (ι := Z × Fin N) r).indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff hmc).2 (integrableOn_const hvol)
  have hnn : ∀ y, 0 ≤ (siteBall (Z := Z) (N := N) r).indicator (fun y => Real.exp (-β * A y)) y := fun y =>
    Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) y
  have hint : Integrable ((siteBall (Z := Z) (N := N) r).indicator (fun y => Real.exp (-β * A y))) := by
    refine hg.mono' hasm (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn y)]
    by_cases hy : y ∈ siteBall (Z := Z) (N := N) r
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (siteBall_subset_gaussCube hr hy)]
      exact Real.exp_le_one_iff.2 (by linarith [hA y hy])
    · rw [Set.indicator_of_notMem hy]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) y
  refine ⟨hint, (integral_pos_iff_support_of_nonneg hnn hint).2 ?_⟩
  have h0 : (0 : EuclideanSpace ℝ (Z × Fin N)) ∈ siteBall (Z := Z) (N := N) r := fun z => by
    simp only [PiLp.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero]
    positivity
  have hpos := (isOpen_siteBall (Z := Z) (N := N) r).measure_pos volume ⟨0, h0⟩
  refine hpos.trans_le (measure_mono fun y hy => ?_)
  rw [Function.mem_support, Set.indicator_of_mem hy]
  exact (Real.exp_pos _).ne'

end Ball

section Cutoff

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L]

/-- The cutoff `χ_{Z₀}` about `ψ⁰` is the site ball about `ψ⁰↾Z₀`. -/
theorem zeroCutoff_iff_sub_mem {Zf : Finset (Torus d (N₀ * L ^ (k - k)))} (ψ0 : BlockField d L N₀ k N) {r : ℝ}
    (hr : 0 < r) (u : SuppSpace Zf N) :
    ZeroCutoff ψ0 r u ↔ u - restrictSupp Zf ψ0 ∈ siteBall (Z := ↥Zf) (N := N) r := by
  unfold ZeroCutoff siteBall
  refine forall_congr' fun z => ?_
  have : (fun i => u (z, i) - ψ0 z i) = fun i => (u - restrictSupp Zf ψ0) (z, i) := by
    funext i; simp [restrictSupp]
  rw [this]
  unfold rn
  exact Real.sqrt_lt' hr

theorem zeroRadius_pos {C6 β p0 : ℝ} (hC6 : 0 < C6) (hβ : 0 < β) (hp0 : 1 ≤ C6 * p0) :
    0 < zeroRadius C6 β p0 := by
  have hp : 0 < p0 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hC6.le h]
  unfold zeroRadius
  positivity

theorem cSix_pos {d D : ℕ} {K6 : ℝ} (hd : 0 < d) (hD : 1 ≤ D) (hK : 0 ≤ K6) : 0 < cSix d D K6 := by
  unfold cSix
  have : (0 : ℝ) < d := by exact_mod_cast hd
  have : (0 : ℝ) < D := by exact_mod_cast hD
  positivity

end Cutoff

section Source

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)
  [NeZero N] {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
  (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
  {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
  (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
  (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0)

local notation "Kz" => psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H
local notation "Zb" => boxFinset (L := L) (N₀ := N₀) (k := k) b0 w

/-- **Definition III.8.1 (P7 (1.5)): `ρ_{k,0}(Z)` with the action restricted to `Z`**, for `Z₀ = box b₀ w`: the cutoff
`χ_{Z₀}` of radius `C₆ β_k^{-1/2} p₀(β_k)` (`β_k = betaK d L k β₀`, `C₆ = 3dD₀(K₆+1)`) about the massless centre
`ψ⁰_k = psiZero` times `exp(-β₀ A_{Zr}(ψ̃_k, φ_k(𝔹_k(U_k); ψ̃_k)))` (`β₀ A_{Zr} = β_k A*_k(Z)`), `Zr` the region of the
component `Z` in the generating set `G = 𝔹_k(U_k)`, `ν` the mass of the action (fine units) and `h` the external field
of its `ν`-term; a function of `u = ψ_k↾Z₀` for `ψ_k ∈ Ψ̃(X ∖ Z₀; δ)` fixed outside `Z₀`. -/
noncomputable def rhoZeroRestricted {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (Zr : Region G) (ν : ℝ) (h : Fin N → ℝ) (β0 p0 : ℝ)
    (u : SuppSpace (boxFinset b0 w) N) : ℝ :=
  rhoZeroRestrictedWith G a Zr ν h (boxFinset b0 w)
    (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk) ψk
    (cSix d D (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)) β0 p0 u

/-- **Characterization through the landed density**: `ρ^Z_{k,0}(Z) = ρ_{k,0} · e^{β₀ (A_{Ω₁} - A_Z)}` at the merged
field, `ρ_{k,0} = rhoZero` at `β_k = betaK d L k β₀` (the action on all of `Ω₁(𝔹_k(U_k))`). -/
theorem rhoZeroRestricted_eq_mul {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (Zr : Region G) (ν : ℝ) (h : Fin N → ℝ) (β0 p0 : ℝ)
    (u : SuppSpace (boxFinset b0 w) N) :
    rhoZeroRestricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0 u =
      rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk (betaK d L k β0) p0 u *
        Real.exp (β0 * (effAction G a (mergeField Zb ψk u) - actionZ G a Zr ν h (mergeField Zb ψk u))) :=
  rhoZeroRestrictedWith_eq_mul Zr ν h _ _ _ _ β0 p0 u

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **The restricted density in the translated variable** `y = u - ψ⁰_k↾Z₀`: the indicator of the site ball of radius
`C₆ β_k^{-1/2} p₀` of `exp(-β₀ A_Z)` at the merged field. -/
theorem rhoZeroRestricted_eq_translate {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (Zr : Region G) (ν : ℝ) (h : Fin N → ℝ) {β0 p0 : ℝ}
    (hρ : 0 < zeroRadius (cSix d D Kz) (betaK d L k β0) p0) (u : SuppSpace (boxFinset b0 w) N) :
    rhoZeroRestricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0 u =
      (siteBall (Z := ↥Zb) (N := N) (zeroRadius (cSix d D Kz) (betaK d L k β0) p0)).indicator
        (fun y => Real.exp (-β0 * actionZ G a Zr ν h (mergeField Zb ψk
          (restrictSupp Zb (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk) + y))))
        (u - restrictSupp Zb (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk)) := by
  set ψ0 := psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk with hψ0
  have hu : restrictSupp Zb ψ0 + (u - restrictSupp Zb ψ0) = u := by abel
  by_cases hc : ZeroCutoff ψ0 (zeroRadius (cSix d D Kz) (betaK d L k β0) p0) u
  · rw [Set.indicator_of_mem ((zeroCutoff_iff_sub_mem ψ0 hρ u).1 hc), hu]
    exact rhoZeroRestrictedWith_of_cutoff Zr ν h _ _ _ _ β0 p0 u hc
  · rw [Set.indicator_of_notMem (fun hh => hc ((zeroCutoff_iff_sub_mem ψ0 hρ u).2 hh))]
    exact rhoZeroRestrictedWith_eq_zero Zr ν h _ _ _ _ β0 p0 u hc

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **Integrability and positivity of `∫ ρ^Z_{k,0}(Z)`** (Lemma III.8.2, first part): under the parameter conditions of
`denominator_eq` at `β_k = betaK d L k β₀`, non-negative weights `a` and mass `ν`. -/
theorem integrable_rhoZeroRestricted {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (Zr : Region G) {ν : ℝ} (h : Fin N → ℝ) {β0 p0 : ℝ}
    (ha : ∀ j, 0 ≤ a j) (hν : 0 ≤ ν) (hβ0 : 0 < β0)
    (hp0 : 1 ≤ cSix d D Kz * p0)
    (hrad : Kz * δ + 5 * zeroRadius (cSix d D Kz) (betaK d L k β0) p0 ≤ etaDen d L N D) :
    Integrable (rhoZeroRestricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0) volume ∧
    0 < ∫ u, rhoZeroRestricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0 u := by
  have hβk : 0 < betaK d L k β0 := by
    unfold betaK
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hd0 : 0 < d := by omega
  have hD1 : 1 ≤ D := (hw1 ⟨0, hd0⟩).trans (hwD _)
  have hC6 : 0 < cSix d D Kz :=
    cSix_pos hd0 hD1 (psiZeroK_pos N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H).le
  have hρ := zeroRadius_pos hC6 hβk hp0
  set ρ := zeroRadius (cSix d D Kz) (betaK d L k β0) p0 with hρdef
  set ψ0 := psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk with hψ0
  set u0 := restrictSupp Zb ψ0 with hu0
  obtain ⟨hηpos, hη0, hη1, hcut⟩ :=
    tube_of_cutoff G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk hβk hp0 hrad
  set A : SuppSpace Zb N → ℝ := fun y => actionZ G a Zr ν h (mergeField Zb ψk (u0 + y)) with hA
  have hcont : ContinuousOn A (siteBall (Z := ↥Zb) (N := N) ρ) := by
    have hmerge : Continuous fun y : SuppSpace Zb N => mergeField Zb ψk (u0 + y) :=
      (continuous_mergeField (N := N) Zb).comp ((continuous_const.add continuous_id).prodMk continuous_const)
    refine (continuousOn_actionZ H hηpos hη0 hη1 Zr ν h).comp hmerge.continuousOn fun y hy => ?_
    have hc : ZeroCutoff ψ0 ρ (u0 + y) := by
      rw [zeroCutoff_iff_sub_mem ψ0 hρ]
      simpa [hu0] using hy
    exact hcut _ hc
  have hAnn : ∀ y ∈ siteBall (Z := ↥Zb) (N := N) ρ, 0 ≤ β0 * A y := fun y _ =>
    mul_nonneg hβ0.le (actionZ_nonneg Zr ha hν h _)
  obtain ⟨hgi, hgpos⟩ := siteBall_density_integrable_pos hρ hcont hAnn
  have heq : rhoZeroRestricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0 =
      fun u => (siteBall (Z := ↥Zb) (N := N) ρ).indicator (fun y => Real.exp (-β0 * A y)) (u - u0) :=
    funext fun u => rhoZeroRestricted_eq_translate G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h
      hρ u
  rw [heq]
  refine ⟨hgi.comp_sub_right u0, ?_⟩
  rw [integral_sub_right_eq_self (fun y => (siteBall (Z := ↥Zb) (N := N) ρ).indicator
    (fun y => Real.exp (-β0 * A y)) y) u0]
  exact hgpos

/-- **`Ẽ₀^{Z}`** of Lemma III.8.2 for the restricted density, defined by the identity of the lemma:
`log ∫ρ^Z_{k,0}(Z) + β₀ A_Z(ψ⁰_k) + (N/2) log β_k |Z₀|` (`β₀ A_Z(ψ⁰_k) = β_k A*_k(Z; ψ⁰_k, φ⁰_k)`). -/
noncomputable def tildeE0Restricted {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (Zr : Region G) (ν : ℝ) (h : Fin N → ℝ) (β0 p0 : ℝ) : ℝ :=
  Real.log (∫ u, rhoZeroRestricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0 u) +
    β0 * actionZ G a Zr ν h (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk) +
    (N : ℝ) / 2 * Real.log (betaK d L k β0) * ((boxFinset (L := L) (N₀ := N₀) (k := k) b0 w).card : ℝ)

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **Lemma III.8.2 for the restricted density (the identity)**:
`∫ dψ_k↾Z₀ ρ^Z_{k,0}(Z) = exp(-β₀ A_Z(ψ⁰_k) - (N/2) log β_k |Z₀| + Ẽ₀^Z)` with `β₀ A_Z(ψ⁰_k) = β_k A*_k(Z; ψ⁰_k, φ⁰_k)`
the action of (2.58′), and the integral is positive.  The bound on `Ẽ₀^Z` is
`denominatorRestricted_bounds_of_osc`. -/
theorem denominatorRestricted_eq {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (Zr : Region G) {ν : ℝ} (h : Fin N → ℝ) {β0 p0 : ℝ}
    (ha : ∀ j, 0 ≤ a j) (hν : 0 ≤ ν) (hβ0 : 0 < β0)
    (hp0 : 1 ≤ cSix d D Kz * p0)
    (hrad : Kz * δ + 5 * zeroRadius (cSix d D Kz) (betaK d L k β0) p0 ≤ etaDen d L N D) :
    ∫ u, rhoZeroRestricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0 u =
      Real.exp (-(β0 * actionZ G a Zr ν h (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk))
        - (N : ℝ) / 2 * Real.log (betaK d L k β0) * ((Zb).card : ℝ) +
        tildeE0Restricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0) ∧
    0 < ∫ u, rhoZeroRestricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0 u := by
  obtain ⟨-, hpos⟩ := integrable_rhoZeroRestricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr h
    ha hν hβ0 hp0 hrad
  refine ⟨?_, hpos⟩
  unfold tildeE0Restricted
  rw [show ∀ x y z : ℝ, -x - y + (z + x + y) = z from fun x y z => by ring, Real.exp_log hpos]

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **Lemma III.8.2 for the restricted density (the bound), conditional on the oscillation bound.**  If on the cutoff
`χ_{Z₀}` the difference `β₀ (A_{Ω₁} - A_Z)` of the action on all of `Ω₁(𝔹_k(U_k))` (`effAction`, massless) and the
restricted action (`actionZ`) oscillates by at most `E` about its value at `ψ⁰_k`, then
`|Ẽ₀^Z - Ẽ₀| ≤ E` (`Ẽ₀ = tildeE0` of the landed `denominator_eq` at `β_k`) and `|Ẽ₀^Z| ≤ C_Ẽ D₀^d + E`.

The oscillation bound is the ingredient of P7 (3.3)-(3.4) that is not landed: P7 bounds the first variation of
`A*_k(Z)` at `ψ⁰_k` in the directions of `Z₀` (the surface term on `st(Z)` and the `ν`-term; the bulk term vanishes by
P7 (2.52), `resZero_psiZero_eq_zero`) through the decay of `δφ_k` away from `Z₀`. -/
theorem denominatorRestricted_bounds_of_osc {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (Zr : Region G) {ν : ℝ} (h : Fin N → ℝ) {β0 p0 E : ℝ}
    (ha : ∀ j, 0 ≤ a j) (hν : 0 ≤ ν) (hβ0 : 0 < β0)
    (hp0 : 1 ≤ cSix d D Kz * p0)
    (hrad : Kz * δ + 5 * zeroRadius (cSix d D Kz) (betaK d L k β0) p0 ≤ etaDen d L N D)
    (hosc : ∀ u : SuppSpace Zb N,
      ZeroCutoff (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk)
        (zeroRadius (cSix d D Kz) (betaK d L k β0) p0) u →
      |β0 * (effAction G a (mergeField Zb ψk u) - actionZ G a Zr ν h (mergeField Zb ψk u)) -
        β0 * (effAction G a (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk) -
          actionZ G a Zr ν h (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk))| ≤ E) :
    |tildeE0Restricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0 -
        tildeE0 G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk (betaK d L k β0) p0| ≤ E ∧
    |tildeE0Restricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0| ≤
      cTildeE N d D * (D : ℝ) ^ d + E := by
  have hβk : 0 < betaK d L k β0 := by
    unfold betaK
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  obtain ⟨-, hpos0, hE0⟩ := denominator_eq G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk hβk hp0 hrad
  obtain ⟨hint, hpos⟩ := integrable_rhoZeroRestricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr h
    ha hν hβ0 hp0 hrad
  set ψ0 := psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk with hψ0
  set ρf := rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk (betaK d L k β0) p0 with hρf
  set ρZ := rhoZeroRestricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0 with hρZ
  have hint0 : Integrable ρf volume := by
    by_contra hni
    have := integral_undef hni
    linarith
  set c := β0 * (effAction G a ψ0 - actionZ G a Zr ν h ψ0) with hc
  have hpt : ∀ u, Real.exp (c - E) * ρf u ≤ ρZ u ∧ ρZ u ≤ Real.exp (c + E) * ρf u := by
    intro u
    have e := rhoZeroRestricted_eq_mul G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0 u
    rw [← hρZ, ← hρf] at e
    rw [e]
    have hr0 : 0 ≤ ρf u := rhoZeroWith_nonneg _ _ _ _ _ _ _ _ _
    by_cases hcut : ZeroCutoff ψ0 (zeroRadius (cSix d D Kz) (betaK d L k β0) p0) u
    · have hb := abs_le.1 (hosc u hcut)
      constructor
      · rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [hb.1])) hr0
      · rw [mul_comm (Real.exp (c + E))]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [hb.2])) hr0
    · have : ρf u = 0 := rhoZeroWith_eq_zero G a _ _ _ _ _ p0 u hcut
      rw [this]; simp
  have hlow : Real.exp (c - E) * ∫ u, ρf u ≤ ∫ u, ρZ u := by
    rw [← integral_const_mul]
    exact integral_mono (hint0.const_mul _) hint fun u => (hpt u).1
  have hup : ∫ u, ρZ u ≤ Real.exp (c + E) * ∫ u, ρf u := by
    rw [← integral_const_mul]
    exact integral_mono hint (hint0.const_mul _) fun u => (hpt u).2
  set I := ∫ u, ρZ u with hI
  set I0 := ∫ u, ρf u with hI0
  have hl1 : c - E + Real.log I0 ≤ Real.log I := by
    have := Real.log_le_log (mul_pos (Real.exp_pos _) hpos0) hlow
    rwa [Real.log_mul (Real.exp_pos _).ne' hpos0.ne', Real.log_exp] at this
  have hl2 : Real.log I ≤ c + E + Real.log I0 := by
    have := Real.log_le_log hpos hup
    rwa [Real.log_mul (Real.exp_pos _).ne' hpos0.ne', Real.log_exp] at this
  have hdiff : tildeE0Restricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0 -
      tildeE0 G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk (betaK d L k β0) p0 =
      Real.log I - Real.log I0 - c := by
    unfold tildeE0Restricted tildeE0
    rw [← hI, ← hI0, betaK_mul_effActionNorm, hc]
    ring
  have h1 : |tildeE0Restricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0 -
      tildeE0 G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk (betaK d L k β0) p0| ≤ E := by
    rw [hdiff, abs_le]
    constructor <;> linarith
  refine ⟨h1, ?_⟩
  have := abs_sub_abs_le_abs_sub
    (tildeE0Restricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0)
    (tildeE0 G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk (betaK d L k β0) p0)
  linarith

end Source

end Balaban.LargeField
