/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepIdentityQuad
public import Balaban.Fluctuation.HatEngineLift
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The step objects at a complex block datum (FLUCTUATION.md §2.2-§2.6; ACTIVITY.md §2)

The objects of `StepObjects` are those of Proposition 2.6 for a *real* block datum `θ`: the
background of `θ` is Def-5(a) (`bgField`, `bgMult`: the minimizer, which exists for real data only),
`S.K` and `S.psi0` take the real parts of `S.covSqrt` and of `ψ^{(k)}(θ)`, the old spin `ψ` is a
real field (`dataU`), and the class composites `EcompAt`, `FcompAt` are built on `bgField`.  The
continuation of the step to a complex `θ` (FLUCTUATION Lemma 2.2 (c), Lemma 2.3 (d), Lemma 2.4;
P4 (2.4)-(2.14), (2.36)-(2.63) at `λ = ∞`) replaces every one of these by the object built on the
complex small solution Def-5(b) (`bgFieldC`, `bgMultC`), without real parts; the integration
variable `ψ̂` stays real.  This file defines that continuation (`…C`), in parallel with the landed
definitions, which are not changed.

* `bgField_eq_zero_of_not_isReal`, `StepSetting.covSqrt_of_not_isReal`,
  `StepSetting.psiKd_of_not_isReal`, `bgFieldC_ne_bgField_of_not_isReal`: at a nonreal datum the
  landed `S.covSqrt` and `S.psiKd` are the objects of the zero background (`bgField = 0`), whereas
  the small solution `bgFieldC` is a unit field; hence the landed objects are not the continuation;
* Part A (`composedDataAtC`, `EcompAtC`, `McompAtC`, `FcompAtC`): the composites `ℰ_k`, `ℳ_k`,
  `ℱ_k` of (H.2), (H.7) with the complex backgrounds;
* `psiKdC` (`ψ^{(k)}(θ)`, (2.1) with the complex small solution), `covSqrtC` (`C^{(k)1/2}`), `KC`,
  `psi0C`, `shiftUC` (`ψ' = β_k^{-1/2} C^{(k)1/2} ψ̂`, (2.7)), `psiAtC`, `dataUC`;
* `VkC` (`V^{(k)}`, (2.4)), `dEC`, `dFC` (`δℰ_k`, `δℱ_k`), `WoneC`, `WtwoC` (the exponents of
  `μ_{s,t}`, (2.6)), `ZstC` (`Z_{s,t}`);
* the identities that hold for every datum: `dataUC_yhat`, `VkC_yhat`, `shiftUC_eq_hatField`,
  `dataUC_psi0C`, `WtwoC_zero`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset Matrix

/-! ### The landed backgrounds at a nonreal datum -/

section NonReal

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}

/-- **The real background field Def-5(a) vanishes at every nonreal datum**: a minimizer
(`IsMinimizer`) exists for real data only, and `bgField` is `0` when there is none. -/
theorem bgField_eq_zero_of_not_isReal (a : ℕ → ℝ) (ν : ℝ) {D : BgData G N} (h : ¬ D.IsReal) :
    bgField G a ν D = 0 := by
  classical
  have hn : ¬ ∃! φ : G.Ω 1 × Fin N → ℂ, IsMinimizer G a ν D φ := fun ⟨_, hφ, _⟩ => h hφ.1
  unfold bgField
  simp only [hn, ↓reduceDIte]

/-- The multiplier Def-5(a) vanishes at every nonreal datum. -/
theorem bgMult_eq_zero_of_not_isReal (a : ℕ → ℝ) (ν : ℝ) {D : BgData G N} (h : ¬ D.IsReal) :
    bgMult G a ν D = 0 := by
  funext x
  unfold bgMult
  rw [bgField_eq_zero_of_not_isReal a ν h]
  simp

/-- **At a nonreal datum of the complex domain `𝒟` the two backgrounds differ**: the small solution
`bgFieldC` of Theorem 7.2 satisfies the constraint `φ · φ = 1`, the landed `bgField` is `0`. -/
theorem bgFieldC_ne_bgField_of_not_isReal {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν)
    {D : BgData G N} (hD : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D)
    (hΩ : (G.Ω 1).Nonempty) (h : ¬ D.IsReal) :
    bgFieldC G a ν (bgC0 d L N) D ≠ bgField G a ν D := by
  intro e
  obtain ⟨x, hx⟩ := hΩ
  have h1 := (theorem72 H hD).2.1.1.2 ⟨x, hx⟩
  rw [e, bgField_eq_zero_of_not_isReal a ν h] at h1
  simp at h1

end NonReal

/-! ### Part A: the class composites with the complex backgrounds -/

section ClassAtC

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The datum `ψ_k^{(j)}(ψ_k, h)`** (H.2) of a complex top datum `D` of level `k` on the torus
of index `K ≥ k`: `composeData` of the level-`j` set over the level-`k` set at the complex small
solution `φ_k = bgFieldC` (Def-5(b); Theorem 7.3 for complex data).  It is `composedDataAt` with
`bgField` replaced by `bgFieldC`. -/
noncomputable def composedDataAtC (a : ℕ → ℝ) (ν : ℝ) {j k : ℕ} (hj : j ≤ k) (hk : k ≤ K)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N) :
    BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j (hj.trans hk))
      N :=
  composeData (levelGS_precedes_at hj hk) a
    (bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) a ν
      (bgC0 d L N) D) D

open Classical in
/-- The pair `(ψ_k^{(j)}, h)` of (H.2) at a complex datum, `0` for `j > k`. -/
noncomputable def composedPairAtC (a : ℕ → ℝ) (ν : ℝ) {k : ℕ} (hk : k ≤ K) (j : ℕ)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N) :
    Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N :=
  if hj : j ≤ k then ((composedDataAtC a ν hj hk D).Ψ, (composedDataAtC a ν hj hk D).h) else (0, 0)

/-- **`ℰ_k(ψ_k, h) = ∑_{j=1}^k ℰ^{(j)}(ψ_k^{(j)}(ψ_k, h), h)`** (H.2) at a complex datum of the top
level `k ≤ K`. -/
noncomputable def EcompAtC (m₀ : ℕ) (Tm : Terms d L N₁ m₁ K N ϱ) (a : ℕ → ℝ) (ν : ℝ) {k : ℕ}
    (hk : k ≤ K)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N) : ℂ :=
  ∑ j ∈ Finset.Icc 1 k,
    Edens m₀ Tm j (composedPairAtC a ν hk j D).1 (composedPairAtC a ν hk j D).2

/-- **The vector `ℳ_k(x; ψ_k, h, g)`** of (H.7) at a complex datum of the top level `k ≤ K`:
`φ_k(x) + ∑_{j=1}^k ℳ^{(j)}(x; ψ_k^{(j)}, h, g)`, `φ_k = bgFieldC`. -/
noncomputable def McompAtC (m₀ : ℕ) (Tm : Terms d L N₁ m₁ K N ϱ) (a : ℕ → ℝ) (ν : ℝ) {k : ℕ}
    (hk : k ≤ K)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N)
    (g : Fld d L N₁ m₁ K N) (x : CTorus d L N₁ m₁ K) : Fin N → ℂ := fun i =>
  svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
      (bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) a ν
        (bgC0 d L N) D) x i +
    ∑ j ∈ Finset.Icc 1 k, Mloc m₀ Tm j x (composedPairAtC a ν hk j D).1
      (composedPairAtC a ν hk j D).2 g i

/-- **`ℱ_k(ψ_k, h, g) = ⟨g, φ_k⟩₁ + ∑_{j=1}^k ℱ^{(j)}(ψ_k^{(j)}, h, g)`** (H.7) at a complex datum
of the top level `k ≤ K`, `φ_k = bgFieldC`. -/
noncomputable def FcompAtC (m₀ : ℕ) (Tm : Terms d L N₁ m₁ K N ϱ) (a : ℕ → ℝ) (ν : ℝ) {k : ℕ}
    (hk : k ≤ K)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N)
    (g : Fld d L N₁ m₁ K N) : ℂ :=
  (∑ x : CTorus d L N₁ m₁ K, ∑ i, g x i *
      svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
        (bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) a ν
          (bgC0 d L N) D) x i) +
    ∑ j ∈ Finset.Icc 1 k, Floc m₀ Tm j (composedPairAtC a ν hk j D).1
      (composedPairAtC a ν hk j D).2 g

/-- `ℱ_k = ⟨g, ℳ_k⟩₁` at a complex datum. -/
theorem FcompAtC_eq_pair (m₀ : ℕ) (Tm : Terms d L N₁ m₁ K N ϱ) (a : ℕ → ℝ) (ν : ℝ) {k : ℕ}
    (hk : k ≤ K)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N)
    (g : Fld d L N₁ m₁ K N) :
    FcompAtC m₀ Tm a ν hk D g =
      ∑ x : CTorus d L N₁ m₁ K, ∑ i, g x i * McompAtC m₀ Tm a ν hk D g x i := by
  unfold FcompAtC McompAtC Floc
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

section Agree

variable {a : ℕ → ℝ} {ν : ℝ} {k : ℕ} {hk : k ≤ K}
  {D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N}

/-- If the two backgrounds of the datum agree, the composed pairs agree. -/
theorem composedPairAtC_eq_of_bg
    (hbg : bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) a ν
        (bgC0 d L N) D =
      bgField (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) a ν D)
    (j : ℕ) : composedPairAtC a ν hk j D = composedPairAt a ν hk j D := by
  unfold composedPairAtC composedPairAt composedDataAtC composedDataAt
  rw [hbg]

/-- If the two backgrounds of the datum agree, `ℰ_k` is the landed composite. -/
theorem EcompAtC_eq_of_bg (m₀ : ℕ) (Tm : Terms d L N₁ m₁ K N ϱ)
    (hbg : bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) a ν
        (bgC0 d L N) D =
      bgField (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) a ν D) :
    EcompAtC m₀ Tm a ν hk D = EcompAt m₀ Tm a ν hk D := by
  unfold EcompAtC EcompAt
  simp only [composedPairAtC_eq_of_bg hbg]

/-- If the two backgrounds of the datum agree, `ℳ_k` is the landed composite. -/
theorem McompAtC_eq_of_bg (m₀ : ℕ) (Tm : Terms d L N₁ m₁ K N ϱ)
    (hbg : bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) a ν
        (bgC0 d L N) D =
      bgField (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) a ν D)
    (g : Fld d L N₁ m₁ K N) (x : CTorus d L N₁ m₁ K) :
    McompAtC m₀ Tm a ν hk D g x = McompAt m₀ Tm a ν hk D g x := by
  unfold McompAtC McompAt
  simp only [composedPairAtC_eq_of_bg hbg, hbg]

/-- If the two backgrounds of the datum agree, `ℱ_k` is the landed composite. -/
theorem FcompAtC_eq_of_bg (m₀ : ℕ) (Tm : Terms d L N₁ m₁ K N ϱ)
    (hbg : bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) a ν
        (bgC0 d L N) D =
      bgField (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) a ν D)
    (g : Fld d L N₁ m₁ K N) : FcompAtC m₀ Tm a ν hk D g = FcompAt m₀ Tm a ν hk D g := by
  unfold FcompAtC FcompAt
  simp only [composedPairAtC_eq_of_bg hbg, hbg]

/-- **On the real domain `𝒟_ℝ` the complex composite `ℰ_k` is the landed one** (Theorem 7.2,
agreement with the real field). -/
theorem EcompAtC_eq (H : BgHyp d L K ϱ a ν) (m₀ : ℕ) (Tm : Terms d L N₁ m₁ K N ϱ)
    (hD : InUnionDomainR (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
      (bgC1 d L N) ν D) :
    EcompAtC m₀ Tm a ν hk D = EcompAt m₀ Tm a ν hk D :=
  EcompAtC_eq_of_bg m₀ Tm (theorem72_real H hD).1

/-- On the real domain `𝒟_ℝ` the complex composite `ℳ_k` is the landed one. -/
theorem McompAtC_eq (H : BgHyp d L K ϱ a ν) (m₀ : ℕ) (Tm : Terms d L N₁ m₁ K N ϱ)
    (hD : InUnionDomainR (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
      (bgC1 d L N) ν D) (g : Fld d L N₁ m₁ K N) (x : CTorus d L N₁ m₁ K) :
    McompAtC m₀ Tm a ν hk D g x = McompAt m₀ Tm a ν hk D g x :=
  McompAtC_eq_of_bg m₀ Tm (theorem72_real H hD).1 g x

/-- On the real domain `𝒟_ℝ` the complex composite `ℱ_k` is the landed one. -/
theorem FcompAtC_eq (H : BgHyp d L K ϱ a ν) (m₀ : ℕ) (Tm : Terms d L N₁ m₁ K N ϱ)
    (hD : InUnionDomainR (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
      (bgC1 d L N) ν D) (g : Fld d L N₁ m₁ K N) :
    FcompAtC m₀ Tm a ν hk D g = FcompAt m₀ Tm a ν hk D g :=
  FcompAtC_eq_of_bg m₀ Tm (theorem72_real H hD).1 g

end Agree

end ClassAtC

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-! ### The landed step objects at a nonreal datum -/

/-- **At a nonreal datum the landed `S.covSqrt` is the square root of the zero background**: it
does not depend on the datum. -/
theorem covSqrt_of_not_isReal (h : ¬ S.D'.IsReal) :
    S.covSqrt = decCovSqrt S.G' S.a S.a₁ S.ν 0 (fun _ => 1) 0 (unitQ S.G') (unitP S.G') := by
  have hs : svec S.G' (0 : S.G'.Ω 1 × Fin N → ℂ) = 0 := by
    funext y i
    by_cases hy : y ∈ S.G'.Ω 1
    · rw [svec_of_mem S.G' _ ⟨y, hy⟩ i]; rfl
    · rw [svec_of_not_mem S.G' _ hy]; rfl
  unfold covSqrt
  rw [bgMult_eq_zero_of_not_isReal S.a S.ν h, bgField_eq_zero_of_not_isReal S.a S.ν h, hs]

/-- At a nonreal datum the landed `S.psiKd` is the composition with the zero field. -/
theorem psiKd_of_not_isReal (h : ¬ S.D'.IsReal) :
    S.psiKd = composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a 0 S.D' := by
  unfold psiKd psiK
  rw [bgField_eq_zero_of_not_isReal S.a S.ν h]

/-- **At a nonreal datum of the complex domain `𝒟` the background of the landed step is not the
small solution**: `S.covSqrt`, `S.psiKd` are built on `bgField = 0 ≠ bgFieldC`. -/
theorem bgFieldC_ne_bgField (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD : InUnionDomainC S.G' (bgC0 d L N) (bgC1 d L N) S.ν S.D') (h : ¬ S.D'.IsReal) :
    bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D' ≠ bgField S.G' S.a S.ν S.D' :=
  bgFieldC_ne_bgField_of_not_isReal H hD ⟨0, (S.hG' 0).1⟩ h

/-! ### The critical point, the covariance and the substitution at a complex datum -/

/-- The complex fluctuation fields `ψ' ∈ (ℂ^N)^{T^{(k)}_1}`, as vectors on `T^{(k)}_1 × [N]` (the
variables of `decCovSqrt` and of `liftC`); also the space of the complex old spin `ψ`. -/
abbrev EC : Type := S.U × Fin N → ℂ

/-- **`ψ^{(k)}(θ)` at a complex datum**, the critical point (2.1) with the complex small solution
`φ_{k+1}(θ) = bgFieldC` (FLUCTUATION Lemma 2.2 (c); landed `criticalPoint_complex`).  It is `psiKd`
with `bgField` replaced by `bgFieldC`. -/
noncomputable def psiKdC : BgData (stepG d L N₁ m₁ k ϱ) N :=
  composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D'

/-- **`C^{(k)1/2}` at a complex datum** (FLUCTUATION Lemma 2.4 (c), (d); P4 (2.24)-(2.25)): the
decoupled square root `decCovSqrt` at `s = 1` and at the complex background
`(φ_{k+1}, α_{k+1}) = (bgFieldC, bgMultC)` of `θ`.  It is `covSqrt` with `bgField`, `bgMult`
replaced by `bgFieldC`, `bgMultC`. -/
noncomputable def covSqrtC : Matrix (S.U × Fin N) (S.U × Fin N) ℂ :=
  decCovSqrt S.G' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (fun _ => 1)
    (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')) (unitQ S.G') (unitP S.G')

/-- `C^{(k)1/2}` at a complex datum as a complex-linear map of the complex fluctuation fields
(FLUCTUATION Lemma 2.4 (c); the operator of the substitution (2.7)): the matrix `covSqrtC` itself,
no real parts.  It is `K` without `Complex.re`. -/
noncomputable def KC : S.EC →ₗ[ℂ] S.EC := Matrix.mulVecLin S.covSqrtC

/-- The background `ψ^{(k)}(θ)` of (2.1) at a complex datum as a complex field on the unit lattice
`T^{(k)}_1`: the restriction of `psiKdC.Ψ` (its value at a site of each unit block), no real
parts.  It is `psi0` without `Complex.re`. -/
noncomputable def psi0C : S.EC := fun q => S.psiKdC.Ψ (unitRep (G' := S.G') q.1) q.2

/-- **The substitution (2.7) at a complex datum**: `ψ' = β_k^{-1/2} C^{(k)1/2} ψ̂` for the real
integration variable `ψ̂`, complexified (`yhat`); a complex field on the unit lattice. -/
noncomputable def shiftUC (x : S.E) : S.EC :=
  ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • S.KC (yhat x)

/-- The complex old spin `ψ = ψ^{(k)}(θ) + s ψ'(ψ̂)`, `ψ' = β_k^{-1/2} C^{(k)1/2} ψ̂`, on the path
of the interpolation: the argument of `V^{(k)}`, `δℰ_k`, `δℱ_k` in the measures `μ_{s,t}` of
(2.6).  It is `psiAt` for the complex objects. -/
noncomputable def psiAtC (s : ℝ) (x : S.E) : S.EC := S.psi0C + (s : ℂ) • S.shiftUC x

/-- The datum `(ψ, h)` of the complex old spin `ψ` (a field on the unit lattice `T^{(k)}_1`, lifted
to the fine torus by `liftC`: constant on the `L^k`-blocks) with the field `h` of the step, as
`BgData` of `𝔹_k` (the argument `(ψ_k, h)` of `φ_k`, `ℰ_k`, `ℱ_k` in (H.1)).  For a real `ψ` it is
`dataU` (`dataUC_yhat`). -/
noncomputable def dataUC (ψ : S.EC) : BgData (stepG d L N₁ m₁ k ϱ) N :=
  BgData.clip (stepG d L N₁ m₁ k ϱ) (liftC S.hG' ψ) (fun _ i => (S.h₀ i : ℂ))
    (isLayerConstant_liftC S.hG S.hG' ψ) (fun _ _ _ _ _ _ _ => rfl)

theorem dataUC_Ψ (ψ : S.EC) (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    (S.dataUC ψ).Ψ x i = ψ (unitPt S.hG' x, i) := by
  have hx : x ∈ dataSites (stepG d L N₁ m₁ k ϱ) := (mem_dataSites _).2 (Or.inl (S.hG x).1)
  simp [dataUC, BgData.clip, hx, liftC_apply]

theorem dataUC_h (ψ : S.EC) (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    (S.dataUC ψ).h x i = (S.h₀ i : ℂ) := by
  simp [dataUC, BgData.clip, (S.hG x).1]

/-- **The datum of a real old spin**: on the complexification of a real field, `dataUC` is the
landed `dataU`. -/
theorem dataUC_yhat (ψ : S.E) : S.dataUC (yhat ψ) = S.dataU ψ := rfl

end StepSetting

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

/-! ### The interaction and the interpolating exponents at a complex datum -/

/-- **The interaction `V^{(k)}(ψ')`** of (2.4), `ψ' = ψ - ψ^{(k)}(θ)`, at the complex old spin `ψ`
of the unit lattice: `½⟨α^{(1)}, φ'·φ'⟩ + ½⟨φ₂, H_k φ₂⟩` (landed `interactionV`; analytic in
`(ψ', φ_{k+1}, α_{k+1})`, FLUCTUATION Lemma 2.3 (d)).  It is `Vk` with `dataU ψ` replaced by
`dataUC ψ`. -/
noncomputable def VkC (ψ : S.EC) : ℂ :=
  interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
    (compTangent S.hG S.hG' (le_refl (k + 1)) S.a (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D'
      (S.dataUC ψ))
    (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC ψ) -
      (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D'))

/-- `δℰ_k(ψ') = ℰ_k(ψ^{(k)} + ψ') - ℰ_k(ψ^{(k)})` as a function of the complex old spin `ψ`
((2.6); the composite `ℰ_k` with the complex backgrounds, `EcompAtC`). -/
noncomputable def dEC (ψ : S.EC) : ℂ :=
  EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC ψ) -
    EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC S.psi0C)

/-- `δℱ_k(ψ', g) = ℱ_k(ψ^{(k)} + ψ', g) - ℱ_k(ψ^{(k)}, g)` as a function of the complex old spin
`ψ` ((2.6); `FcompAtC`). -/
noncomputable def dFC (g : Fld d L N₁ m₁ (k + 1) N) (ψ : S.EC) : ℂ :=
  FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC ψ) g -
    FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC S.psi0C) g

/-- **The exponent of `μ_{s,·}` at a complex datum** ((2.6)):
`W₁(s, ψ̂) = -β_k V^{(k)}(s ψ') + δℰ_k(s ψ')`, `ψ' = β_k^{-1/2} C^{(k)1/2} ψ̂` with the complex
square root; a function of the real integration variable `ψ̂`. -/
noncomputable def WoneC (s : ℝ) (x : S.E) : ℂ :=
  -(S.β : ℂ) * S.VkC (S.psiAtC s x) + S.dEC C (S.psiAtC s x)

/-- **The exponent of `μ_{·,t}` at a complex datum** ((2.6)): `W₂(t, ψ̂) = δℱ_k(t ψ', g)`. -/
noncomputable def WtwoC (g : Fld d L N₁ m₁ (k + 1) N) (t : ℝ) (x : S.E) : ℂ :=
  S.dFC C g (S.psiAtC t x)

/-- **The partition functions `Z_{s,t}` of (2.6) at a complex datum**: the integral of
`exp (W₁(s,·) + W₂(t,·))` over the same fluctuation measure `ν_{p₁}` (2.5). -/
noncomputable def ZstC (g : Fld d L N₁ m₁ (k + 1) N) (s t : ℝ) : ℂ :=
  partFun₂ S.nuFl (S.WoneC C) (S.WtwoC C g) s t

/-! ### Identities for every datum -/

/-- The substitution (2.7) at a complex datum is the hat field of `HatEngineLift` for the matrix
`covSqrtC`. -/
theorem shiftUC_eq_hatField (x : S.E) : S.shiftUC x = S.hatField S.covSqrtC (yhat x) := rfl

theorem shiftUC_apply (x : S.E) (q : S.U × Fin N) :
    S.shiftUC x q = ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      ∑ r : S.U × Fin N, S.covSqrtC q r * ((x r.1 r.2 : ℝ) : ℂ) := rfl

/-- **`V^{(k)}` at a real old spin**: on the complexification of a real field, `VkC` is the landed
`Vk` (for every datum). -/
theorem VkC_yhat (ψ : S.E) : S.VkC (yhat ψ) = S.Vk ψ := rfl

theorem psiAtC_zero (x : S.E) : S.psiAtC 0 x = S.psi0C := by
  unfold psiAtC
  rw [Complex.ofReal_zero, zero_smul, add_zero]

/-- **The datum of the background is the critical point**: `dataUC psi0C = psiKdC` (for every
datum; the complex form of `dataU_psi0`). -/
theorem dataUC_psi0C : S.dataUC S.psi0C = S.psiKdC := by
  refine BgData.eq_of_raw (Prod.ext ?_ ?_)
  · funext x i
    show (S.dataUC S.psi0C).Ψ x i = S.psiKdC.Ψ x i
    rw [S.dataUC_Ψ]
    show S.psiKdC.Ψ (unitRep (unitPt S.hG' x)) i = S.psiKdC.Ψ x i
    have hb : unitBlock (unitRep (unitPt S.hG' x)) = unitBlock x := by
      rw [unitBlock_unitRep]; rfl
    have hx' : x ∈ (stepG d L N₁ m₁ k ϱ).blk k (unitRep (unitPt S.hG' x)) :=
      GeneratingSet.mem_blk.2 hb.symm
    have hl := S.hG.mem_layer (unitRep (unitPt S.hG' x))
    have hk := S.hG.bounds
    exact (congrFun (S.psiKdC.Ψ_layerConst k hk.1 hk.2 (unitRep (unitPt S.hG' x)) hl x hx') i).symm
  · funext x i
    show (S.dataUC S.psi0C).h x i = S.psiKdC.h x i
    rw [S.dataUC_h]
    show (S.h₀ i : ℂ) = (if x ∈ (stepG d L N₁ m₁ k ϱ).Ω 1 then S.D'.h x i else 0 : ℂ)
    simp [(S.hG x).1, S.hh₀]

theorem WtwoC_zero (g : Fld d L N₁ m₁ (k + 1) N) (x : S.E) : S.WtwoC C g 0 x = 0 := by
  unfold WtwoC dFC
  rw [S.psiAtC_zero]
  exact sub_self _

/-- `δℰ_k` at a complex datum, with the critical point written as `psiKdC`. -/
theorem dEC_eq (ψ : S.EC) :
    S.dEC C ψ = EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC ψ) -
      EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC := by
  unfold dEC
  rw [S.dataUC_psi0C]

/-- `δℱ_k` at a complex datum, with the critical point written as `psiKdC`. -/
theorem dFC_eq (g : Fld d L N₁ m₁ (k + 1) N) (ψ : S.EC) :
    S.dFC C g ψ = FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC ψ) g -
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC g := by
  unfold dFC
  rw [S.dataUC_psi0C]

end StepSetting

end Balaban.Fluctuation
