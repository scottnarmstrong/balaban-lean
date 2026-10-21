/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7SmallField
public import Balaban.LargeField.Operators.MainAction
public import Balaban.SmallField.RenormDefs

/-!
# The holomorphic extension of the restricted small-field functions

The restricted small-field functions of P5 (1.6)–(1.17) (`Def7.SFCtx.Ares`, `Fres`, `Rres`) are
defined at real fields `ψ_k`.  In the fluctuation integral of the large-field step (P5 (2.16),
(2.39), (2.48)) they are evaluated at the composed field `ψ_k(ψ̂)`, which is complex for complex
variables; the integrand is their holomorphic extension, with the squares `|v|²` of the action replaced
by the bilinear products `v · v = ∑_i v_i²` (as `actionC` for `action`, BACKGROUND.md (5.3)).

* `bondTermWith`, `bondEdirWith`, `bondEWith`, `starBondEWith`, `actionGWith`: the bond energies and
  the multiscale action `A_G(X; ψ, φ)` of §II.4 with a general square `sq`; the landed ones are the
  instances `sq v = ‖v‖²` (`bondE_eq_with`, `starBondE_eq_with`, `actionG_eq_with`), the holomorphic
  ones `bondEC`, `starBondEC`, `actionGC` the instances `sq v = v · v`; at real fields these are the
  landed ones (`bondEC_hC`, `starBondEC_hC`, `actionGC_hC`);
* `singleScaleOf`, `SFCtx.psiLevelKOf`: the single-scale fields with values in any type with `0`
  (the landed `singleScale`, `psiLevelK` are the instances `ℝ^N`);
* `SFCtx.liftDataC`, `phiKC`, `phiBarC`, `psiJC`, `EresJC`, `EresKC`, `MresJC`, `sfLiftKC`: the
  functions of a complex field `ψ_k` on the `k`-blocks; at the complexification `blockToC ψ_k` of a
  real field they are the landed ones (`liftData_eq`, `phiK_eq`, `psiJ_eq`, `EresJ_eq`, `EresK_eq`,
  `MresJ_eq`, `sfLiftK_eq`; `phiBar_apply`: `φ̄_k` is the real part of `phiBarC`);
* `actStarC`, `AresC`, `FresC`, `RresC`, `sfExpC`: the holomorphic `A*_k`, `𝒜_k`, `ℱ_k`, `ℛ^{(k)}`
  and the exponent `𝒜_k + ℱ_k + ℛ^{(k)}` of (D1) on `Y`;
* `phiBarAt`, `psiJAt`, `EresMainAt`, `MresJAt`, `actStarAt`, `FresAt`: the same functions at a
  general background field `φ` of `𝔹_k(W_k)` (and, for `actStarAt`, a general action mass); the
  functions above are their instances `φ = φ_k`.  The decoupled background fields of the localization
  of the residual of `R` (P3 §4) are inserted through them;
* `sfExpC_blockToC`: at a real field whose complex background `φ_k` is real (the case of real data on
  the domain of BG Theorem 7.1), the exponent is the landed `𝒜_k + ℱ_k + ℛ^{(k)}`, and
  `sfFactor_eq_mul_exp`: the small-field factor of (D1) is `χ_k(Y) exp(sfExpC)`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale

/-! ### The bond energies and the action with a general square -/

section With

variable {E R : Type*} [NormedAddCommGroup E] [CommRing R] {d ℓ : ℕ} [NeZero ℓ]

/-- The bond term `sq(φ(x + e_μ) - φ(x))` for a general square `sq`. -/
def bondTermWith (sq : E → R) (φ : Torus d ℓ → E) (μ : Fin d) (x : Torus d ℓ) : R :=
  sq (φ (x + Pi.single μ 1) - φ x)

/-- The bonds `{x, x + e_μ}` with both end points in `S`, for a general square `sq`. -/
def bondEdirWith (sq : E → R) (μ : Fin d) (S : Finset (Torus d ℓ)) (φ : Torus d ℓ → E) : R :=
  ∑ x, if x ∈ S ∧ x + Pi.single μ 1 ∈ S then bondTermWith sq φ μ x else 0

/-- All bonds with both end points in `S`, for a general square `sq`. -/
def bondEWith (sq : E → R) (S : Finset (Torus d ℓ)) (φ : Torus d ℓ → E) : R :=
  ∑ μ : Fin d, bondEdirWith sq μ S φ

/-- The bonds with exactly one end point in `X`, for a general square `sq`. -/
def starBondEWith (sq : E → R) (X : Finset (Torus d ℓ)) (φ : Torus d ℓ → E) : R := by
  classical
  exact ∑ μ : Fin d, ∑ x, if (x ∈ X) ≠ (x + Pi.single μ 1 ∈ X) then bondTermWith sq φ μ x else 0

/-- The landed bond energy is the instance `sq v = ‖v‖²`. -/
theorem bondE_eq_with (S : Finset (Torus d ℓ)) (φ : Torus d ℓ → E) :
    bondE S φ = bondEWith (fun v : E => ‖v‖ ^ 2) S φ := rfl

/-- The landed star bond energy is the instance `sq v = ‖v‖²`. -/
theorem starBondE_eq_with (X : Finset (Torus d ℓ)) (φ : Torus d ℓ → E) :
    starBondE X φ = starBondEWith (fun v : E => ‖v‖ ^ 2) X φ := rfl

end With

section ActionWith

variable {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The multiscale action `A_G(X; ψ, φ)` of §II.4 with a general square `sq`** (values in an
`ℝ`-algebra `R`). -/
noncomputable def actionGWith {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CommRing R]
    [Algebra ℝ R] (sq : E → R) (G : GeneratingSet d L N₀ q ϱ) (a : ℕ → ℝ) (μ : ℝ) (h : E)
    (X : Finset (Site d L N₀ q)) (ψ : (m : ℕ) → Blk d L N₀ q m → E) (φ : Site d L N₀ q → E) : R :=
  algebraMap ℝ R (1 / 2) * ∑ n ∈ Finset.Icc 1 q, ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X),
      algebraMap ℝ R (a n * (L : ℝ) ^ (n * (d - 2))) * sq (ψ n y - bavgL d L N₀ q n φ y) +
    algebraMap ℝ R (1 / 2) * bondEWith sq X φ + algebraMap ℝ R (μ / 2) * ∑ x ∈ X, sq (φ x - h)

/-- The landed action is the instance `sq v = ‖v‖²`. -/
theorem actionG_eq_with {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : GeneratingSet d L N₀ q ϱ) (a : ℕ → ℝ) (μ : ℝ) (h : E) (X : Finset (Site d L N₀ q))
    (ψ : (m : ℕ) → Blk d L N₀ q m → E) (φ : Site d L N₀ q → E) :
    actionG G a μ h X ψ φ = actionGWith (fun v : E => ‖v‖ ^ 2) G a μ h X ψ φ := rfl

end ActionWith

/-! ### The holomorphic bond energies and action -/

section Holo

open Balaban.SmallField

variable {N : ℕ}

/-- The bond energy with the bilinear square `v · v` (holomorphic in the field). -/
noncomputable def bondEC {d ℓ : ℕ} [NeZero ℓ] (S : Finset (Torus d ℓ)) (φ : Torus d ℓ → Fin N → ℂ) :
    ℂ :=
  bondEWith (fun v => dot v v) S φ

/-- The star bond energy with the bilinear square `v · v` (holomorphic in the field). -/
noncomputable def starBondEC {d ℓ : ℕ} [NeZero ℓ] (X : Finset (Torus d ℓ))
    (φ : Torus d ℓ → Fin N → ℂ) : ℂ :=
  starBondEWith (fun v => dot v v) X φ

/-- **The holomorphic multiscale action**: `A_G(X; ψ, φ)` with the bilinear square `v · v`. -/
noncomputable def actionGC {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    (G : GeneratingSet d L N₀ q ϱ) (a : ℕ → ℝ) (μ : ℝ) (h : Fin N → ℂ)
    (X : Finset (Site d L N₀ q)) (ψ : (m : ℕ) → Blk d L N₀ q m → Fin N → ℂ)
    (φ : Site d L N₀ q → Fin N → ℂ) : ℂ :=
  actionGWith (fun v => dot v v) G a μ h X ψ φ

open Def7

/-- At a real vector the bilinear square is the square of the norm. -/
theorem dot_hC (v : EuclideanSpace ℝ (Fin N)) : dot (hC v) (hC v) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [dot, hC]
  push_cast
  simp [sq]

theorem hC_sub (v w : EuclideanSpace ℝ (Fin N)) : hC (v - w) = hC v - hC w := by
  funext i; simp [hC]

theorem hC_zero : hC (0 : EuclideanSpace ℝ (Fin N)) = 0 := by
  funext i; simp [hC]

theorem hC_smul_sum {ι : Type*} (s : Finset ι) (c : ℝ) (v : ι → EuclideanSpace ℝ (Fin N)) :
    hC (c • ∑ x ∈ s, v x) = c • ∑ x ∈ s, hC (v x) := by
  funext i
  simp [hC, Finset.sum_apply, Complex.ofReal_sum]

/-- The block average commutes with the complexification. -/
theorem bavgL_hC {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] (m : ℕ)
    (φ : Site d L N₀ q → EuclideanSpace ℝ (Fin N)) (y : Blk d L N₀ q m) :
    bavgL d L N₀ q m (fun x => hC (φ x)) y = hC (bavgL d L N₀ q m φ y) := by
  unfold bavgL bavg
  rw [hC_smul_sum]

theorem bondEC_hC {d ℓ : ℕ} [NeZero ℓ] (S : Finset (Torus d ℓ))
    (φ : Torus d ℓ → EuclideanSpace ℝ (Fin N)) :
    bondEC S (fun x => hC (φ x)) = ((bondE S φ : ℝ) : ℂ) := by
  unfold bondEC bondEWith bondEdirWith bondTermWith bondE bondEdir bondTerm
  push_cast
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · rw [← hC_sub, dot_hC]
  · simp

theorem starBondEC_hC {d ℓ : ℕ} [NeZero ℓ] (X : Finset (Torus d ℓ))
    (φ : Torus d ℓ → EuclideanSpace ℝ (Fin N)) :
    starBondEC X (fun x => hC (φ x)) = ((starBondE X φ : ℝ) : ℂ) := by
  classical
  unfold starBondEC starBondEWith bondTermWith starBondE bondTerm
  push_cast
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · rw [← hC_sub, dot_hC]
  · simp

/-- **At real fields the holomorphic action is the action.** -/
theorem actionGC_hC {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    (G : GeneratingSet d L N₀ q ϱ) (a : ℕ → ℝ) (μ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (X : Finset (Site d L N₀ q)) (ψ : (m : ℕ) → Blk d L N₀ q m → EuclideanSpace ℝ (Fin N))
    (φ : Site d L N₀ q → EuclideanSpace ℝ (Fin N)) :
    actionGC G a μ (hC h) X (fun m y => hC (ψ m y)) (fun x => hC (φ x)) =
      ((actionG G a μ h X ψ φ : ℝ) : ℂ) := by
  have hb := bondEC_hC X φ
  unfold bondEC at hb
  unfold actionGC actionGWith actionG
  rw [hb]
  simp only [Complex.coe_algebraMap, bavgL_hC, ← hC_sub, dot_hC]
  push_cast
  ring

end Holo

/-! ### The holomorphic restricted small-field functions -/

namespace Def7

open MeasureTheory Balaban.Background RegionHistory Balaban.SmallField

section SingleScale

variable {S : Setting} {n : ℕ → ℕ} {M K : ℕ}

/-- The multiscale family equal to `ψ_k` at the scale `k` and to `0` at the other scales, with
values in any type with `0` (`singleScale` is the instance `ℝ^N`). -/
def singleScaleOf {E : Type*} [Zero E] (k : ℕ) (ψk : BlockAt S n M K k → E) :
    (m : ℕ) → BlockAt S n M K m → E :=
  fun m y => if hm : m = k then ψk (hm ▸ y) else 0

theorem singleScale_eq_of {N : ℕ} (k : ℕ) (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    singleScale k ψk = singleScaleOf k ψk := rfl

end SingleScale

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (Y : Set (Torus S.d (n k))) (ψC : BlockAt S n M K k → Fin N → ℂ)
  (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)

/-- The complexification of a real field on the `k`-blocks. -/
def blockToC (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) : BlockAt S n M K k → Fin N → ℂ :=
  fun b => hC (ψk b)

namespace SFCtx

/-- The level-`k` multiscale field of the single-scale action, with values in any type with `0`
(`psiLevelK` is the instance `ℝ^N`). -/
def psiLevelKOf {E : Type*} [Zero E] (ψk : BlockAt S n M K k → E) :
    (m : ℕ) → LargeField.Blk S.d S.L (C.geo.M1 * (C.geo.c * n k)) k m → E :=
  fun m y => if hm : m ≤ k then
    singleScaleOf k ψk m (torusCast (histScale_eq C.geo.hM C.hnn hm C.hkK) y) else 0

theorem psiLevelK_eq_of (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    C.psiLevelK ψk = C.psiLevelKOf ψk := rfl

theorem psiLevelKOf_blockToC (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    C.psiLevelKOf (blockToC ψk) = fun m y => hC (C.psiLevelK ψk m y) := by
  funext m y
  unfold psiLevelKOf psiLevelK singleScaleOf singleScale blockToC
  split_ifs <;> simp [hC_zero]

/-- The lifted data `lift_k ψ_k` of a complex field on the `k`-blocks. -/
def liftDataC : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) → Fin N → ℂ :=
  fun z => ψC (torusCast (histScale_eq C.geo.hM C.hnn le_rfl C.hkK) z)

theorem liftData_eq (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    C.liftData ψk = C.liftDataC (blockToC ψk) := rfl

/-- `φ_k = bg(𝔹_k(W_k); lift_k ψ_k)` at a complex field. -/
noncomputable def phiKC : (C.genW Y).Ω 1 × Fin N → ℂ :=
  bgSF C.weights (C.cs.muBg k) (bgC0 S.d S.L N) (W2 R Y) (C.liftDataC ψC) (hC hv)

theorem phiK_eq (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    C.phiK Y ψk hv = C.phiKC Y (blockToC ψk) hv := rfl

/-- **The extension `φ̄` of a background field `φ` of `𝔹_k(W_k)`** to all sites of the level-`k`
torus (by the data off `Ω_1`); `phiBarC` is the instance `φ = φ_k`.  The field `φ` is a parameter
so that the decoupled background fields of the localization expansion (P3 §4) can be inserted. -/
noncomputable def phiBarAt (φ : (C.genW Y).Ω 1 × Fin N → ℂ) : BgT C.geo k → Fin N → ℂ :=
  fun z i => barField (C.genW Y) (liftSingle (C.genW Y) (C.liftDataC ψC) (hC hv)).Ψ φ z i

/-- **The complex background `φ̄_k`** on all sites of the level-`k` torus (extended by the data off
`Ω_1`); the landed `φ̄_k` is its real part at real fields (`phiBar_apply`). -/
noncomputable def phiBarC : BgT C.geo k → Fin N → ℂ :=
  C.phiBarAt Y ψC hv (C.phiKC Y ψC hv)

theorem phiBar_apply (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (z : BgT C.geo k)
    (i : Fin N) : C.phiBar Y ψk hv z i = (C.phiBarC Y (blockToC ψk) hv z i).re := rfl

/-- If the complex background is real, it is the complexification of `φ̄_k`. -/
theorem hC_phiBar_of_real (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (hre : ∀ z i, (C.phiBarC Y (blockToC ψk) hv z i).im = 0) (z : BgT C.geo k) :
    hC (C.phiBar Y ψk hv z) = C.phiBarC Y (blockToC ψk) hv z := by
  funext i
  refine Complex.ext ?_ ?_
  · simp [hC, phiBar_apply]
  · simp [hC, hre z i]

/-- **The composed field `ψ^{(j)}` of a background field `φ` of `𝔹_k(W_k)`**
(`composeField(𝔹_j(W_k), 𝔹_k(W_k), a; φ, lift_k ψ_k)`, P5 (1.4)), read on the Def-6 torus; `psiJC`
is the instance `φ = φ_k`. -/
noncomputable def psiJAt (φ : (C.genW Y).Ω 1 × Fin N → ℂ) (j : ℕ) : Def6.Fld S.d S.L C.N₁ m₁ k N :=
  if hj : j ≤ k then
    sfPull C.geo C.hT (composeField
      (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n k) (L := S.L) (c := C.geo.c) (n := n k) hj
        (W2 R Y))
      (C.genW Y) C.weights φ (liftSingle (C.genW Y) (C.liftDataC ψC) (hC hv)).Ψ)
  else 0

/-- `ψ^{(j)}_k` at a complex field. -/
noncomputable def psiJC (j : ℕ) : Def6.Fld S.d S.L C.N₁ m₁ k N :=
  C.psiJAt Y ψC hv (C.phiKC Y ψC hv) j

theorem psiJ_eq (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (j : ℕ) :
    C.psiJ Y ψk hv j = C.psiJC Y (blockToC ψk) hv j := rfl

open Classical in
/-- **The localized terms of `ℰ^{(j)}(Y)`** (P5 (1.8), without the correction) at the composed field
of a background field `φ`. -/
noncomputable def EresMainAt (φ : (C.genW Y).Ω 1 × Fin N → ℂ) (j : ℕ) : ℂ :=
  ∑ y ∈ C.alignedIn j Y,
    ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) | Def6.IsPolyDom C.m₀ j X ∧
        y ∈ X ∧ X ⊆ C.sset (thickY R Y)},
      (C.sf.Tm C.N₁).E j y X (C.psiJAt Y ψC hv φ j) (Def6.constFld (hC hv))

/-- `ℰ^{(j)}(Y; ψ_j, h)` (P5 (1.8)) at a complex field. -/
noncomputable def EresJC (j : ℕ) : ℂ :=
  C.EresMainAt Y ψC hv (C.phiKC Y ψC hv) j -
    ∑ y ∈ C.alignedIn j Y, ∑ x ∈ C.alignedIn j (thickY R Y),
      C.sf.corr C.N₁ j y x (C.psiJC Y ψC hv j) (Def6.constFld (hC hv))

theorem EresJ_eq (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (j : ℕ) :
    C.EresJ Y ψk hv j = C.EresJC Y (blockToC ψk) hv j := rfl

/-- `ℰ_k = ∑_{j=1}^k ℰ^{(j)}` (P5 (1.7)) at a complex field. -/
noncomputable def EresKC : ℂ := ∑ j ∈ Finset.Icc 1 k, C.EresJC Y ψC hv j

theorem EresK_eq (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    C.EresK Y ψk hv = C.EresKC Y (blockToC ψk) hv := rfl

open Classical in
/-- **`ℳ^{(j)}(x, Y)` (P5 (1.13)) at the composed field of a background field `φ`** of
`𝔹_k(W_k)`; `MresJC` is the instance `φ = φ_k`. -/
noncomputable def MresJAt (φ : (C.genW Y).Ω 1 × Fin N → ℂ) (j : ℕ)
    (x : Localization.CTorus S.d S.L C.N₁ m₁ k) : Fin N → ℂ :=
  ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) | Def6.IsPolyDom C.m₀ j X ∧ x ∈ X ∧
      X ⊆ C.sset (thickY R Y)},
    (C.sf.Tm C.N₁).M j x X (C.psiJAt Y ψC hv φ j) (Def6.constFld (hC hv))
      (sfG C.geo C.hnn C.hkK C.hT g)

/-- `ℳ^{(j)}(x, Y)` (P5 (1.13)) at a complex field. -/
noncomputable def MresJC (j : ℕ) (x : Localization.CTorus S.d S.L C.N₁ m₁ k) : Fin N → ℂ :=
  C.MresJAt Y ψC hv g (C.phiKC Y ψC hv) j x

theorem MresJ_eq (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (j : ℕ)
    (x : Localization.CTorus S.d S.L C.N₁ m₁ k) :
    C.MresJ Y ψk hv g j x = C.MresJC Y (blockToC ψk) hv g j x := rfl

/-- The lift of a complex field on the `k`-blocks to the sites of the Def-6 torus. -/
def sfLiftKC : Def6.Fld S.d S.L C.N₁ m₁ k N :=
  fun x => ψC (jBlock S.d S.L (M * n K) K k (bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT x)))

theorem sfLiftK_eq (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    sfLiftK C.geo C.hnn C.hkK C.hT ψk = C.sfLiftKC (blockToC ψk) := rfl

/-- **The holomorphic single-scale action with half star bonds at a background field `φ` and an
action mass `μ`**: `A*_k(Y; ψ_k, φ) = A_{T^{(k)}_1}(Y; ψ_k, φ̄) + ¼ ∑_{st(Y)} (∂φ̄)·(∂φ̄)` (P5 (1.5));
`actStarC` is the instance `μ = sfActMass`, `φ = φ_k`. -/
noncomputable def actStarAt (μ : ℝ) (φ : (C.genW Y).Ω 1 × Fin N → ℂ) : ℂ :=
  actionGC (levelGen (ϱ := (1 : ℝ)) k) C.weights μ (hC hv) (C.bgSet Y)
      (C.psiLevelKOf ψC) (C.phiBarAt Y ψC hv φ) +
    1 / 4 * starBondEC (C.bgSet Y) (C.phiBarAt Y ψC hv φ)

/-- **The holomorphic single-scale action with half star bonds** `A*_k(Y; ψ_k, φ_k)` (P5 (1.5)). -/
noncomputable def actStarC : ℂ := C.actStarAt Y ψC hv (sfActMass C.cs k) (C.phiKC Y ψC hv)

/-- **The holomorphic `𝒜_k = -β_k A*_k + ℰ_k - E_k |Y|_k`** (P5 (1.6)). -/
noncomputable def AresC : ℂ :=
  -((betaCanon S.d S.L (C.sf.β k) k 0 : ℝ) : ℂ) * C.actStarC Y ψC hv + C.EresKC Y ψC hv -
    ((C.sf.E C.N₁ * volK M Y : ℝ) : ℂ)

open Classical in
/-- **`ℱ_k(Y; ψ_k, h, g)` (P5 (1.10)–(1.13)) at a background field `φ`** of `𝔹_k(W_k)`
(`⟨χ_Y g, φ̄⟩₁` and the composed fields of `φ`); `FresC` is the instance `φ = φ_k`. -/
noncomputable def FresAt (φ : (C.genW Y).Ω 1 × Fin N → ℂ) : ℂ :=
  (∑ x ∈ C.bgSet Y, ∑ i : Fin N,
      g (bgToFine C.geo C.hnn C.hkK x, i) * C.phiBarAt Y ψC hv φ x i) +
    ∑ j ∈ Finset.Icc 1 k, ∑ x : Localization.CTorus S.d S.L C.N₁ m₁ k,
      if x ∈ C.sset Y then
        ∑ i : Fin N, sfG C.geo C.hnn C.hkK C.hT g x i * C.MresJAt Y ψC hv g φ j x i
      else 0

/-- **The holomorphic `ℱ_k(Y; ψ_k, h, g)`** (P5 (1.10)–(1.13)). -/
noncomputable def FresC : ℂ := C.FresAt Y ψC hv g (C.phiKC Y ψC hv)

open Classical in
/-- **`ℛ^{(k)}(Y; ψ_k, h, g)`** (P5 (1.16)–(1.17)) at a complex field. -/
noncomputable def RresC : ℂ :=
  ∑ nn ∈ Finset.Icc 1 (C.m₀ + m₁), ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) |
      Def6.IsPolyDom C.m₀ k X ∧ X ⊆ C.sset Y},
    C.sf.Rt C.N₁ nn X (C.sfLiftKC ψC) (Def6.constFld (hC hv)) (sfG C.geo C.hnn C.hkK C.hT g)

theorem Rres_eq (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    C.Rres Y ψk hv g = C.RresC Y (blockToC ψk) hv g := rfl

/-- **The exponent `𝒜_k + ℱ_k + ℛ^{(k)}` of (D1) on `Y`**, holomorphic in the field `ψ_k`. -/
noncomputable def sfExpC : ℂ := C.AresC Y ψC hv + C.FresC Y ψC hv g + C.RresC Y ψC hv g

section Real

variable (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
  (hre : ∀ z i, (C.phiBarC Y (blockToC ψk) hv z i).im = 0)
include hre

/-- **At a real field with real background, the holomorphic action at the background `φ_k` and any
action mass `μ` is the landed action** `A_{T^{(k)}_1}(Y; ψ_k, φ̄_k) + ¼ ∑_{st(Y)} |∂φ̄_k|²` of mass
`μ` (the core of `actStarC_blockToC`). -/
theorem actStarAt_blockToC (μ : ℝ) :
    C.actStarAt Y (blockToC ψk) hv μ (C.phiKC Y (blockToC ψk) hv) =
      ((actionG (levelGen (ϱ := (1 : ℝ)) k) C.weights μ hv (C.bgSet Y) (C.psiLevelK ψk)
          (C.phiBar Y ψk hv) + 1 / 4 * starBondE (C.bgSet Y) (C.phiBar Y ψk hv) : ℝ) : ℂ) := by
  have hφ : C.phiBarAt Y (blockToC ψk) hv (C.phiKC Y (blockToC ψk) hv) =
      fun z => hC (C.phiBar Y ψk hv z) :=
    funext fun z => (C.hC_phiBar_of_real Y hv ψk hre z).symm
  unfold actStarAt
  rw [hφ, psiLevelKOf_blockToC, actionGC_hC, starBondEC_hC]
  push_cast
  ring

theorem actStarC_blockToC :
    C.actStarC Y (blockToC ψk) hv = ((C.actStar Y ψk hv : ℝ) : ℂ) :=
  C.actStarAt_blockToC Y hv ψk hre (sfActMass C.cs k)

theorem AresC_blockToC : C.AresC Y (blockToC ψk) hv = C.Ares Y ψk hv := by
  unfold AresC Ares
  rw [C.actStarC_blockToC Y hv ψk hre, ← EresK_eq]

theorem FresC_blockToC : C.FresC Y (blockToC ψk) hv g = C.Fres Y ψk hv g := by
  unfold FresC FresAt Fres
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  show _ * C.phiBarC Y (blockToC ψk) hv x i = _
  rw [← C.hC_phiBar_of_real Y hv ψk hre x]
  rfl

/-- **At a real field with real background, the holomorphic exponent is the exponent of (D1).** -/
theorem sfExpC_blockToC :
    C.sfExpC Y (blockToC ψk) hv g = C.Ares Y ψk hv + C.Fres Y ψk hv g + C.Rres Y ψk hv g := by
  unfold sfExpC
  rw [C.AresC_blockToC Y hv ψk hre, C.FresC_blockToC Y hv g ψk hre, ← Rres_eq]

/-- **The small-field factor of (D1)** at a real field with real background:
`χ_k(Y) exp(𝒜_k + ℱ_k + ℛ^{(k)})(Y) = χ_k(Y) exp(sfExpC)`. -/
theorem sfFactor_eq_mul_exp :
    C.sfFactor Y ψk hv g =
      ((C.chiY Y ψk hv : ℝ) : ℂ) * Complex.exp (C.sfExpC Y (blockToC ψk) hv g) := by
  unfold sfFactor
  rw [C.sfExpC_blockToC Y hv g ψk hre]

end Real

end SFCtx

end Def7

end Balaban.LargeField
