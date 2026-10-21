/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalDomPsiJ
public import Balaban.LargeField.Operators.QuietStepDataMeas
public import Balaban.LargeField.Characteristic.MeasurableChi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Continuity of the building blocks of the small-field factor on the `χ`-support

A6-3 (a), item 1: the background `φ_k`, the real background `φ̄_k` and the inherited fields
`ψ^{(j)}_k` of the whole torus are continuous in the block field `ψ_k` on the set where the datum
lies in the real domain `𝒟_ℝ` (Theorem 7.2, `contOn_bg`). These are the inputs of the measurability
of `sfFactor2` (`Spine/FinalSfMeas.lean`).
-/

@[expose] public section

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.LargeField.Def7
  Balaban.SmallField.Def6v2 Balaban.Localization

namespace Balaban.RootFSpine

section Generic

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-- The zero extension `svec` of a field on `Ω₁` is continuous in the field, coordinatewise. -/
theorem continuousOn_svec_coord {Z : Type*} [TopologicalSpace Z] {E : Set Z}
    (G : GeneratingSet d L N₀ q ϱ) (φ : Z → G.Ω 1 × Fin N → ℂ) (hφ : ContinuousOn φ E)
    (y : Torus d (N₀ * L ^ q)) (i : Fin N) :
    ContinuousOn (fun z => svec G (φ z) y i) E := by
  by_cases hy : y ∈ G.Ω 1
  · have : (fun z => svec G (φ z) y i) = fun z => φ z (⟨y, hy⟩, i) := by
      funext z; exact svec_of_mem' (φ z) hy i
    rw [this]
    exact (continuous_apply _).comp_continuousOn hφ
  · have : (fun z => svec G (φ z) y i) = fun _ => 0 := by
      funext z; exact svec_of_not_mem G (φ z) hy i
    rw [this]
    exact continuousOn_const

/-- The block mean of the zero extension is continuous. -/
theorem continuousOn_blockMean_svec {Z : Type*} [TopologicalSpace Z] {E : Set Z}
    (G : GeneratingSet d L N₀ q ϱ) (G' : GeneratingSet d L N₀ q ϱ') (n : ℕ) (φ : Z → G'.Ω 1 × Fin N → ℂ)
    (hφ : ContinuousOn φ E) (x : Torus d (N₀ * L ^ q)) (i : Fin N) :
    ContinuousOn (fun z => blockMean G n (fun y => svec G' (φ z) y i) x) E := by
  unfold blockMean
  exact continuousOn_const.mul (continuousOn_finsetSum _ fun y _ => continuousOn_svec_coord G' φ hφ y i)

/-- **The composed field is continuous in the data**: for `x ∈ Ω₁(𝔹)`, the coordinate
`composeField 𝔹 𝔹' a φ' Ψ' (x, i)` is continuous in `(φ', Ψ')`. -/
theorem continuousOn_composeField_coord {Z : Type*} [TopologicalSpace Z] {E : Set Z}
    (G : GeneratingSet d L N₀ q ϱ) (G' : GeneratingSet d L N₀ q ϱ') (a : ℕ → ℝ)
    (φ : Z → G'.Ω 1 × Fin N → ℂ) (Ψ : Z → Torus d (N₀ * L ^ q) → Fin N → ℂ)
    (hφ : ContinuousOn φ E) (hΨ : ∀ x i, Continuous fun z => Ψ z x i)
    {x : Torus d (N₀ * L ^ q)} (hx : x ∈ G.Ω 1) (i : Fin N) :
    ContinuousOn (fun z => composeField G G' a (φ z) (Ψ z) x i) E := by
  have : (fun z => composeField G G' a (φ z) (Ψ z) x i) = fun z =>
      blockMean G (G.layerIndex x) (fun y => svec G' (φ z) y i) x +
        ((a (G'.layerIndex x) / a (G.layerIndex x) *
          (((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2) : ℝ) : ℂ) *
          (Ψ z x i - blockMean G' (G'.layerIndex x) (fun y => svec G' (φ z) y i) x) := by
    funext z; exact composeField_of_mem a (φ z) (Ψ z) hx i
  rw [this]
  exact (continuousOn_blockMean_svec G G' _ φ hφ x i).add
    (continuousOn_const.mul ((hΨ x i).continuousOn.sub
      (continuousOn_blockMean_svec G' G' _ φ hφ x i)))

/-- **The composed field is continuous in the data at every site** (on `Ω₁(𝔹)` by
`continuousOn_composeField_coord`, on the collar it is the extension `φ̄'`, elsewhere `0`). -/
theorem continuousOn_composeField_coord_all {Z : Type*} [TopologicalSpace Z] {E : Set Z}
    (G : GeneratingSet d L N₀ q ϱ) (G' : GeneratingSet d L N₀ q ϱ') (a : ℕ → ℝ)
    (φ : Z → G'.Ω 1 × Fin N → ℂ) (Ψ : Z → Torus d (N₀ * L ^ q) → Fin N → ℂ)
    (hφ : ContinuousOn φ E) (hΨ : ∀ x i, Continuous fun z => Ψ z x i)
    (x : Torus d (N₀ * L ^ q)) (i : Fin N) :
    ContinuousOn (fun z => composeField G G' a (φ z) (Ψ z) x i) E := by
  classical
  by_cases hx : x ∈ G.Ω 1
  · exact continuousOn_composeField_coord G G' a φ Ψ hφ hΨ hx i
  by_cases hc : x ∈ collar G
  · have e : (fun z => composeField G G' a (φ z) (Ψ z) x i) =
        fun z => barField G' (Ψ z) (φ z) x i := by
      funext z
      exact composeField_of_collar a (φ z) (Ψ z) hc i
    rw [e]
    by_cases hx' : x ∈ G'.Ω 1
    · have e2 : (fun z => barField G' (Ψ z) (φ z) x i) = fun z => φ z (⟨x, hx'⟩, i) := by
        funext z
        simp [barField, hx']
      rw [e2]
      exact (continuous_apply _).comp_continuousOn hφ
    · have e2 : (fun z => barField G' (Ψ z) (φ z) x i) = fun z => Ψ z x i := by
        funext z
        simp [barField, hx']
      rw [e2]
      exact (hΨ x i).continuousOn
  · have e : (fun z => composeField G G' a (φ z) (Ψ z) x i) = fun _ => 0 := by
      funext z
      exact composeField_of_not_mem a (φ z) (Ψ z)
        (fun h => ((mem_dataSites G).1 h).elim hx hc) i
    rw [e]
    exact continuousOn_const

end Generic

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N (j + 1) m₁ ϱ)
  (hv : EuclideanSpace ℝ (Fin N))

/-- The datum `D_k = lift_k ψ_k` of the cut `Y` (the background on `𝔹_k(W₂(Y))`) as a function of
the block field. -/
noncomputable def DfamY (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) : BgData (C.genW Y) N :=
  liftSingle (C.genW Y) (C.liftData ψk) (hC hv)

/-- The datum `D_k = lift_k ψ_k` of the whole torus as a function of the block field. -/
noncomputable def Dfam (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) :
    BgData (C.genW (Set.univ : Set (Torus S.d (n (j + 1))))) N :=
  DfamY C hv Set.univ ψk

/-- The block fields whose datum of the cut `Y` lies in the real domain `𝒟_ℝ` (mass `μ`). -/
def DomSetY (Y : Set (Torus S.d (n (j + 1)))) (μ : ℝ) :
    Set (BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) :=
  {ψk | InUnionDomainR (C.genW Y) (bgC1 S.d S.L N) μ (DfamY C hv Y ψk)}

/-- The block fields whose datum lies in the real domain `𝒟_ℝ` (mass `μ`). -/
def DomSet (μ : ℝ) : Set (BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) :=
  DomSetY C hv Set.univ μ

theorem continuous_DfamY_Ψ (Y : Set (Torus S.d (n (j + 1))))
    (x : Torus S.d (C.geo.M1 * (C.geo.c * n (j + 1)) * S.L ^ (j + 1)))
    (i : Fin N) : Continuous fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      (DfamY C hv Y ψk).Ψ x i := by
  classical
  unfold DfamY liftSingle BgData.clip
  by_cases hx : x ∈ dataSites (C.genW Y)
  · simp only [hx, ↓reduceIte, blockLift, SFCtx.liftData, BlockCfg.toC, blockCfgOf]
    exact Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj i).continuous.comp
        (continuous_apply (blkToBlock C.geo C.hnn C.hkK (jBlock S.d S.L _ (j + 1) (j + 1) x))))
  · simp [hx]
    exact continuous_const

theorem continuous_DfamY_h (Y : Set (Torus S.d (n (j + 1))))
    (x : Torus S.d (C.geo.M1 * (C.geo.c * n (j + 1)) * S.L ^ (j + 1)))
    (i : Fin N) : Continuous fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      (DfamY C hv Y ψk).h x i := by
  classical
  unfold DfamY liftSingle BgData.clip
  by_cases hx : x ∈ (C.genW Y).Ω 1
  · simp only [hx, ↓reduceIte]
    exact continuous_const
  · simp [hx]
    exact continuous_const

theorem continuous_Dfam_Ψ (x : Torus S.d (C.geo.M1 * (C.geo.c * n (j + 1)) * S.L ^ (j + 1)))
    (i : Fin N) : Continuous fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      (Dfam C hv ψk).Ψ x i :=
  continuous_DfamY_Ψ C hv Set.univ x i

theorem continuous_Dfam_h (x : Torus S.d (C.geo.M1 * (C.geo.c * n (j + 1)) * S.L ^ (j + 1)))
    (i : Fin N) : Continuous fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      (Dfam C hv ψk).h x i :=
  continuous_DfamY_h C hv Set.univ x i

/-- **`φ_k` of the cut `Y` is continuous in the block field on the domain** (Theorem 7.2). -/
theorem continuousOn_bgFieldC_DfamY (Y : Set (Torus S.d (n (j + 1))))
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1))) :
    ContinuousOn (fun ψk => bgFieldC (C.genW Y)
        C.weights (C.cs.muBg (j + 1)) (bgC0 S.d S.L N) (DfamY C hv Y ψk))
      (DomSetY C hv Y (C.cs.muBg (j + 1))) :=
  (contOn_bg (fun ψk => DfamY C hv Y ψk) HB (continuous_DfamY_Ψ C hv Y)
    (continuous_DfamY_h C hv Y)).1

/-- **`φ_k` is continuous in the block field on the domain** (Theorem 7.2). -/
theorem continuousOn_bgFieldC_Dfam
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1))) :
    ContinuousOn (fun ψk => bgFieldC (C.genW (Set.univ : Set (Torus S.d (n (j + 1)))))
        C.weights (C.cs.muBg (j + 1)) (bgC0 S.d S.L N) (Dfam C hv ψk))
      (DomSet C hv (C.cs.muBg (j + 1))) :=
  continuousOn_bgFieldC_DfamY C hv Set.univ HB

/-- **`φ̄_k` of the cut `Y` is continuous in the block field on the domain.** -/
theorem continuousOn_phiBarY (Y : Set (Torus S.d (n (j + 1))))
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1))) :
    ContinuousOn (fun ψk => C.phiBar Y ψk hv) (DomSetY C hv Y (C.cs.muBg (j + 1))) :=
  continuousOn_barPhi (C.genW Y)
    (fun ψk => DfamY C hv Y ψk) C.weights (C.cs.muBg (j + 1)) (bgC0 S.d S.L N)
    (continuous_DfamY_Ψ C hv Y) (continuousOn_bgFieldC_DfamY C hv Y HB)

/-- **`φ̄_k` is continuous in the block field on the domain.** -/
theorem continuousOn_phiBar
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1))) :
    ContinuousOn (fun ψk => C.phiBar (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv)
      (DomSet C hv (C.cs.muBg (j + 1))) :=
  continuousOn_phiBarY C hv Set.univ HB

/-- **The inherited fields `ψ^{(j')}_k` of the cut `Y` are continuous in the block field on the
domain** (coordinatewise, at every site, `j' ≤ k`). -/
theorem continuousOn_psiSF_coordY (Y : Set (Torus S.d (n (j + 1))))
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    {jj : ℕ} (hj : jj ≤ j + 1) (x : BgT C.geo (j + 1)) (i : Fin N) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      psiSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L) (c := C.geo.c)
        (n := n (j + 1)) C.weights (C.cs.muBg (j + 1)) (bgC0 S.d S.L N) hj
        (W2 R Y) (C.liftData ψk) (hC hv) x i)
      (DomSetY C hv Y (C.cs.muBg (j + 1))) :=
  continuousOn_composeField_coord_all _ (C.genW Y) C.weights
    (fun ψk => bgFieldC (C.genW Y) C.weights (C.cs.muBg (j + 1)) (bgC0 S.d S.L N)
      (DfamY C hv Y ψk))
    (fun ψk => (DfamY C hv Y ψk).Ψ) (continuousOn_bgFieldC_DfamY C hv Y HB)
    (continuous_DfamY_Ψ C hv Y) x i

/-- **The inherited field `ψ^{(j')}_k` of the cut `Y` on the Def-6 torus is continuous in the block
field on the domain** (coordinatewise). -/
theorem continuousOn_psiJ_coordY (Y : Set (Torus S.d (n (j + 1))))
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    {jj : ℕ} (hj : jj ≤ j + 1) (x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) (i : Fin N) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      C.psiJ Y ψk hv jj x i) (DomSetY C hv Y (C.cs.muBg (j + 1))) := by
  have : (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      C.psiJ Y ψk hv jj x i) = fun ψk =>
      psiSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L) (c := C.geo.c)
        (n := n (j + 1)) C.weights (C.cs.muBg (j + 1)) (bgC0 S.d S.L N) hj
        (W2 R Y) (C.liftData ψk) (hC hv) (sfToBg C.geo C.hT x) i := by
    funext ψk
    unfold SFCtx.psiJ sfPull
    simp only [hj, ↓reduceDIte]
  rw [this]
  exact continuousOn_psiSF_coordY C hv Y HB hj _ i

/-- **The inherited field of the cut `Y` as a point of the field space is continuous in the block
field on the domain.** -/
theorem continuousOn_psiJY (Y : Set (Torus S.d (n (j + 1))))
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    {jj : ℕ} (hj : jj ≤ j + 1) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      C.psiJ Y ψk hv jj) (DomSetY C hv Y (C.cs.muBg (j + 1))) :=
  continuousOn_pi.2 fun x => continuousOn_pi.2 fun i => continuousOn_psiJ_coordY C hv Y HB hj x i

/-- **The inherited fields `ψ^{(j')}_k` are continuous in the block field on the domain**
(coordinatewise, `j' ≤ k`). -/
theorem continuousOn_psiSF_coord
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1) (x : BgT C.geo (j + 1)) (i : Fin N) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      psiSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L) (c := C.geo.c)
        (n := n (j + 1)) C.weights (C.cs.muBg (j + 1)) (bgC0 S.d S.L N) hj
        (W2 R (Set.univ : Set (Torus S.d (n (j + 1))))) (C.liftData ψk) (hC hv) x i)
      (DomSet C hv (C.cs.muBg (j + 1))) := by
  have hx : x ∈ (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L)
      (c := C.geo.c) (n := n (j + 1)) hj
      (W2 R (Set.univ : Set (Torus S.d (n (j + 1)))))).Ω 1 := by
    rw [genSF_Ω_univ_of_le C hj hj1]; exact Finset.mem_univ _
  exact continuousOn_composeField_coord _ (C.genW (Set.univ : Set (Torus S.d (n (j + 1)))))
    C.weights (fun ψk => bgFieldC (C.genW (Set.univ : Set (Torus S.d (n (j + 1)))))
        C.weights (C.cs.muBg (j + 1)) (bgC0 S.d S.L N) (Dfam C hv ψk))
    (fun ψk => (Dfam C hv ψk).Ψ) (continuousOn_bgFieldC_Dfam C hv HB)
    (continuous_Dfam_Ψ C hv) hx i

/-- **The inherited field `ψ^{(j')}_k` of the Def-6 torus is continuous in the block field on the
domain** (coordinatewise). -/
theorem continuousOn_psiJ_coord
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1) (x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1))
    (i : Fin N) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj x i)
      (DomSet C hv (C.cs.muBg (j + 1))) := by
  have : (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj x i) = fun ψk =>
      psiSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L) (c := C.geo.c)
        (n := n (j + 1)) C.weights (C.cs.muBg (j + 1)) (bgC0 S.d S.L N) hj
        (W2 R (Set.univ : Set (Torus S.d (n (j + 1))))) (C.liftData ψk) (hC hv)
        (sfToBg C.geo C.hT x) i := by
    funext ψk
    unfold SFCtx.psiJ sfPull
    simp only [hj, ↓reduceDIte]
  rw [this]
  exact continuousOn_psiSF_coord C hv HB hj1 hj _ i

/-- **The inherited field as a point of the field space is continuous in the block field on the
domain.** -/
theorem continuousOn_psiJ
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj)
      (DomSet C hv (C.cs.muBg (j + 1))) :=
  continuousOn_pi.2 fun x => continuousOn_pi.2 fun i => continuousOn_psiJ_coord C hv HB hj1 hj x i

/-- The lift `sfLiftK` of the block field is continuous. -/
theorem continuous_sfLiftK :
    Continuous fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      sfLiftK C.geo C.hnn C.hkK C.hT ψk :=
  continuous_pi fun _ => continuous_pi fun i =>
    Complex.continuous_ofReal.comp ((EuclideanSpace.proj i).continuous.comp
      (continuous_apply _))

end Ctx

end Balaban.RootFSpine
