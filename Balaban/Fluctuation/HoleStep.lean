/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepObjects
public import Balaban.Localization.Dec2Covariance
public import Balaban.Localization.Decoupled2Background
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The step on a region: the composed field (P5 (2.17)–(2.20), (2.33)–(2.39))

The step `k → k + 1` of a representation with large-field regions integrates the variable `ψ_k`
only on the new small-field region `Ω_{k+1}` (P5 (2.16)).  P5 expands the integrand around the
approximate minimum of (2.17),
```
ψ^{(k)}(θ̃) = ψ(𝔹_k(W_k), (𝔹_k(W_k) ∩ Ω^c_{k+1}) ∪ Λ_{k+1}; θ̃),
```
the composed datum (BG (6.2)) of the generating set `𝔹_k(W_k)` over the generating set obtained by
adding the top layer `Λ_{k+1} = Ω_{k+1}`, with the mixed datum `θ̃` (`θ` on `Ω_{k+1}`, `ψ_k` on the
blocks of the lower layers); and it changes variables by
```
ψ_k = ψ^{(k)}_loc(θ) + β_k^{-1/2} C^{(k)1/2}_loc ψ̂   on the blocks of Ω_{k+1}       (P5 (2.39)),
```
with `C^{(k)} = ((a L⁻² Q*Q + Δ^{(k)})|_{B(Λ_{k+1})})⁻¹` the covariance of the quadratic form of
(2.33) and the subscript `loc` the localization extensions at `s = 0` of P5 (2.18), (2.35) (one for
each cube `□' ⊂ Ω_{k+1}`, with the pair `(□', R_{k+1}(□'))`).

This file defines these objects for an arbitrary pair of generating sets `G ≺ G'` (the *core*,
`HoleStep`), so that the whole-lattice step of `StepObjects.lean` (`StepSetting`, `G = 𝔹_k`,
`G'` of level `k + 1`) is the instance `StepSetting.toHole`:

* `HoleStep`: the old operator set `G` (`𝔹_k(W_k)` at depth `k + 1`, empty top layer), the set `G'`
  of (2.17) (`G` with the top layer `Ω_{k+1}`), the datum `D'` (`θ̃`), and the constants;
* `U`, `E`: the unit points of the top layer of `G'` (the blocks of side `L^k` of `Ω_{k+1}`, the
  sites `B(Λ_{k+1})` of the fluctuation variables) and the fields on them;
* `psiKd`: `ψ^{(k)}(θ̃)` (P5 (2.17)); `covSqrt`: `C^{(k)1/2}` at `s = 1` (P5 (2.33)–(2.34), the
  formula of `StepSetting.covSqrt` with `G'`); `psi0`, `shiftU`, `psiAt`: the critical field on the
  unit points, the shift `β_k^{-1/2} C^{(k)1/2} ψ̂`, the field on the interpolation path;
* `liftIn`, `oldData`: the datum of `G` with the values of a field on the unit points of the top
  layer and the values of `ψ^{(k)}(θ̃)` elsewhere (P5 (2.20): the decomposition of `ψ_k` on
  `Ω_{k+1}`, the other values of the datum unchanged);
* the localized objects (P5 (2.18), (2.35)): for a decoupling cover `C` and a localization map
  `sloc` (the decoupling vector attached to each unit point; P5's choice is `slocOf`, the vector
  vanishing on the cover cubes outside the localization domain of the point), `psiKdAt`,
  `covSqrtAt` (the decoupled
  background and covariance of the pair `(C, G')` at a decoupling vector), `psiLoc`, `shiftLoc`
  (`ψ^{(k)}_loc(θ)` and `β_k^{-1/2} C^{(k)1/2}_loc ψ̂` of (2.39), read row by row at the vector of the
  row), `composed` (the field of (2.39)) and `composedData` (the datum of `G` it determines).

Characterizations: `toHole_psiKd`, `toHole_covSqrt`, `toHole_psi0`, `toHole_shiftU`,
`toHole_psiAt` (the whole-lattice objects are the instances), `toHole_oldData` (the whole-lattice
datum `dataU` is `oldData`); `isEL_psiKdC` (the background of the composed datum is the background
of `θ̃` restricted, BG Theorem 6.1, P5 (2.22)); `oldData_out`, `oldData_in` (the values of the old
datum); `composed_zero` (at `ψ̂ = 0` the composed field is the localized background), and
`composed_affine` (it is affine in `ψ̂`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization Finset Matrix

section Core

variable (d L N₁ m₁ k N : ℕ) [NeZero L] [NeZero N₁] (ϱ ϱ' : ℝ)

/-- **The data of one step on a region** (P5 (2.16)–(2.20); FLUCTUATION §2.7): the old operator
set `G` (`𝔹_k(W_k)` at depth `k + 1`, `W_k = (Z_k^c)^{≈2}`, with an empty top layer), the set `G'`
of P5 (2.17) (`(𝔹_k(W_k) ∩ Ω^c_{k+1}) ∪ Λ_{k+1}`: the layers of `G` and the top layer `Ω_{k+1}`),
the datum `D'` of `G'` (the mixed lift `θ̃`: the block variable `θ` on `Ω_{k+1}`, the old field
`ψ_k` on the blocks of the lower layers) with its constant field `h`, and the numbers `a = a₁`,
mass `ν` of the backgrounds, `β = β_k` (in fine units), the radius `p₁` of `χ_fl` and the threshold
`δ = δ_k`.  Only typing data. -/
structure HoleStep where
  /-- the old operator set `𝔹_k(W_k)` -/
  G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ
  /-- the set of P5 (2.17): `G` with the top layer `Ω_{k+1}` -/
  G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'
  /-- `G ≺ G'` -/
  hpre : Precedes G G'
  /-- the old set has no top layer -/
  topG : G.Ω (k + 1) = ∅
  /-- the new region lies in the layer `k` of the old set -/
  topIn : G'.Ω (k + 1) ⊆ G.Ω k
  hk1 : 1 ≤ k
  /-- the mixed datum `θ̃` -/
  D' : BgData G' N
  h₀ : Fin N → ℝ
  hh₀ : ∀ x ∈ G'.Ω 1, ∀ i, D'.h x i = (h₀ i : ℂ)
  a₁ : ℝ
  ν : ℝ
  β : ℝ
  p₁ : ℝ
  δ : ℝ

end Core

namespace HoleStep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  (S : HoleStep d L N₁ m₁ k N ϱ ϱ')

/-- The unit points of the new region (the blocks of side `L^k` of `Ω_{k+1}`, `B(Λ_{k+1})`). -/
abbrev U : Type := ↥(unitPts S.G')

/-- The fluctuation variables `ψ̂ ∈ (ℝ^N)^{B(Λ_{k+1})}`; also the space of the old field on the new
region. -/
abbrev E : Type := S.U → Rn N

/-- The weights `a_n = a₁ (1 - L⁻²)/(1 - L⁻²ⁿ)` (P2 (4.4)). -/
noncomputable abbrev a : ℕ → ℝ := compWeight L S.a₁

/-- `β_k` in the units of the paper: `β_k^{paper} = β L^{k(d-2)}`. -/
noncomputable def betaU : ℝ := S.β * ((L : ℝ) ^ k) ^ d / ((L : ℝ) ^ k) ^ 2

/-- **`ψ^{(k)}(θ̃)`, the approximate minimum (P5 (2.17))**: the composed datum of `G` over `G'` with
the background of `θ̃`. -/
noncomputable def psiKd : BgData S.G N :=
  composeData S.hpre S.a (bgField S.G' S.a S.ν S.D') S.D'

/-- **`C^{(k)1/2}` at `s = 1`** (P5 (2.33)–(2.34); Lemma 2.4 (c) of the whole-lattice step), a
complex matrix on `B(Λ_{k+1}) × [N]`. -/
noncomputable def covSqrt : Matrix (S.U × Fin N) (S.U × Fin N) ℂ :=
  decCovSqrt S.G' S.a S.a₁ S.ν (bgMult S.G' S.a S.ν S.D') (fun _ => 1)
    (svec S.G' (bgField S.G' S.a S.ν S.D')) (unitQ S.G') (unitP S.G')

/-- `C^{(k)1/2}` as a linear map of the fluctuation variables (its real entries). -/
noncomputable def K : S.E →ₗ[ℝ] S.E :=
  matMap S.U N (S.covSqrt.map Complex.re)

/-- `C^{(k)-1/2}` as a linear map. -/
noncomputable def Kinv : S.E →ₗ[ℝ] S.E :=
  matMap S.U N (S.covSqrt.map Complex.re)⁻¹

/-- The approximate minimum `ψ^{(k)}(θ̃)` as a field on the unit points of the new region. -/
noncomputable def psi0 : S.E := unitRestrict (G' := S.G') (fun x i => ((S.psiKd.Ψ x i).re))

/-- The substitution `ψ' = β_k^{-1/2} C^{(k)1/2} ψ̂` on the unit points of the new region. -/
noncomputable def shiftU (x : S.E) : S.E := (S.betaU ^ (-(1 / 2 : ℝ))) • S.K x

/-- The old field `ψ = ψ^{(k)}(θ̃) + s ψ'(ψ̂)` on the path of the interpolation. -/
noncomputable def psiAt (s : ℝ) (x : S.E) : S.E := S.psi0 + s • S.shiftU x

/-! ### The datum of the old field -/

/-- **The fine field of a field on the unit points of the new region**, with the values `Ψout` off
the new region: on a site whose block of side `L^k` is a unit point of `Ω_{k+1}` the value of the
field at that point, elsewhere `Ψout`. -/
noncomputable def liftIn {T : Type*} (ψ : S.U → T) (Ψout : CTorus d L N₁ m₁ (k + 1) → T)
    (x : CTorus d L N₁ m₁ (k + 1)) : T := by
  classical
  exact if h : unitBlock x ∈ unitPts S.G' then ψ ⟨unitBlock x, h⟩ else Ψout x

variable {S}

theorem liftIn_of_mem {T : Type*} (ψ : S.U → T) (Ψout : CTorus d L N₁ m₁ (k + 1) → T)
    {x : CTorus d L N₁ m₁ (k + 1)} (h : unitBlock x ∈ unitPts S.G') :
    S.liftIn ψ Ψout x = ψ ⟨unitBlock x, h⟩ := by
  classical
  simp [liftIn, h]

theorem liftIn_of_not_mem {T : Type*} (ψ : S.U → T) (Ψout : CTorus d L N₁ m₁ (k + 1) → T)
    {x : CTorus d L N₁ m₁ (k + 1)} (h : unitBlock x ∉ unitPts S.G') :
    S.liftIn ψ Ψout x = Ψout x := by
  classical
  simp [liftIn, h]

/-- A site whose unit block is a unit point of the new region lies in the top layer of `G'`. -/
theorem mem_top_of_unitBlock {x : CTorus d L N₁ m₁ (k + 1)} (h : unitBlock x ∈ unitPts S.G') :
    x ∈ S.G'.Ω (k + 1) := by
  obtain ⟨y, hy, hyx⟩ := (mem_unitPts S.G').1 h
  exact (S.G'.mem_layer.1 (layer_of_unitBlock S.G' hyx hy)).1

/-- **The lifted field is constant on the blocks of every layer of `G`**, if `Ψout` is: the blocks
of the layer `k` are the unit blocks, and the lower layers of `G` miss the new region. -/
theorem isLayerConstant_liftIn {T : Type*} (ψ : S.U → T) {Ψout : CTorus d L N₁ m₁ (k + 1) → T}
    (hout : IsLayerConstant S.G Ψout) : IsLayerConstant S.G (S.liftIn ψ Ψout) := by
  intro n hn1 hnk x hx x' hx'
  have hb : jBlock d L (N₁ * L ^ m₁) (k + 1) n x' = jBlock d L (N₁ * L ^ m₁) (k + 1) n x :=
    GeneratingSet.mem_blk.1 hx'
  have hxΩ : x ∈ S.G.Ω n := (S.G.mem_layer.1 hx).1
  -- the layer `n` of `G` is at most `k`
  have hnk' : n ≤ k := by
    by_contra hcon
    have : n = k + 1 := by omega
    subst this
    rw [S.topG] at hxΩ
    exact absurd hxΩ (Finset.notMem_empty _)
  by_cases hn : n = k
  · subst hn
    have hu : unitBlock x' = unitBlock x := by
      unfold unitBlock
      unfold jBlock at hb
      exact hb
    by_cases hm : unitBlock x ∈ unitPts S.G'
    · have hm' : unitBlock x' ∈ unitPts S.G' := hu ▸ hm
      rw [liftIn_of_mem ψ Ψout hm, liftIn_of_mem ψ Ψout hm']
      congr 1
      exact Subtype.ext hu
    · have hm' : unitBlock x' ∉ unitPts S.G' := fun h => hm (hu ▸ h)
      rw [liftIn_of_not_mem ψ Ψout hm, liftIn_of_not_mem ψ Ψout hm']
      exact hout _ hn1 hnk x hx x' hx'
  · -- below the layer `k` the new region is not met
    have hnot : ∀ z : CTorus d L N₁ m₁ (k + 1), z ∈ S.G.layer n → unitBlock z ∉ unitPts S.G' := by
      intro z hz hm
      have hzk : z ∈ S.G.Ω k := S.topIn (mem_top_of_unitBlock hm)
      have hlt : n < k := lt_of_le_of_ne hnk' hn
      exact (S.G.mem_layer.1 hz).2 (S.G.Ω_antitone (by omega) (by omega) (by omega) hzk)
    have hx'l : x' ∈ S.G.layer n := by
      have hb' := hb
      rw [S.G.mem_layer]
      have hiff := S.G.blockUnion n hn1 (by omega) x' x hb'
      have hiff1 := S.G.blockUnion (n + 1) (by omega) (by omega) x' x
        (jBlock_eq_of_le (Nat.le_succ n) (by omega) hb')
      exact ⟨hiff.2 hxΩ, fun h => (S.G.mem_layer.1 hx).2 (hiff1.1 h)⟩
    rw [liftIn_of_not_mem ψ Ψout (hnot x hx), liftIn_of_not_mem ψ Ψout (hnot x' hx'l)]
    exact hout _ hn1 hnk x hx x' hx'

variable (S)

/-- The real part of `ψ^{(k)}(θ̃)` as a fine field (the values of the old datum off the new region). -/
noncomputable def psiKdRe : CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ :=
  fun x i => (S.psiKd.Ψ x i).re

theorem isLayerConstant_psiKdRe : IsLayerConstant S.G S.psiKdRe := by
  intro n hn1 hnk x hx x' hx'
  funext i
  unfold psiKdRe
  rw [S.psiKd.Ψ_layerConst n hn1 hnk x hx x' hx']

/-- **The datum of the old field** (P5 (2.16), (2.20)): the real datum of `G` with the values of the
field `ψ` on the unit points of the new region and the values of `ψ^{(k)}(θ̃)` elsewhere, with the
field `h₀`. -/
noncomputable def oldData (ψ : S.E) : BgData S.G N :=
  realData S.G (S.liftIn (fun b i => ψ b i) S.psiKdRe) S.h₀
    (isLayerConstant_liftIn _ S.isLayerConstant_psiKdRe)

variable {S}

theorem oldData_in (ψ : S.E) {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ dataSites S.G)
    (h : unitBlock x ∈ unitPts S.G') (i : Fin N) :
    (S.oldData ψ).Ψ x i = ((ψ ⟨unitBlock x, h⟩ i : ℝ) : ℂ) := by
  classical
  simp [oldData, realData, BgData.clip, hx, liftIn_of_mem _ _ h]

theorem oldData_out (ψ : S.E) {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ dataSites S.G)
    (h : unitBlock x ∉ unitPts S.G') (i : Fin N) :
    (S.oldData ψ).Ψ x i = ((S.psiKd.Ψ x i).re : ℂ) := by
  classical
  simp [oldData, realData, BgData.clip, hx, liftIn_of_not_mem _ _ h, psiKdRe]

/-! ### The background of the composed datum -/

variable (S) in
/-- **`ψ^{(k)}(θ̃)` with the complex background** (P5 (2.17) for complex data): the composed datum
with the small solution `bgFieldC` of `G'` (radius `c₀`). -/
noncomputable def psiKdC (c₀ : ℝ) : BgData S.G N :=
  composeData S.hpre S.a (bgFieldC S.G' S.a S.ν c₀ S.D') S.D'

/-- **The background of the composed datum is the background of `θ̃`** (BG Theorem 6.1 (ii), (iv);
P5 (2.22): `φ_k(ψ^{(k)}(θ̃)) = φ_{k+1}(θ̃)`): if `(φ', α')` solves (EL) for `G'` with the datum `θ̃`,
its restriction solves (EL) for `G` with the composed datum. -/
theorem isEL_psiKdC (ha : ∀ j, 1 ≤ j → j ≤ k + 1 → S.a j ≠ 0) (c₀ : ℝ)
    {α' : S.G'.Ω 1 → ℂ} (hEL : IsEL S.G' S.a S.ν S.D' (bgFieldC S.G' S.a S.ν c₀ S.D') α') :
    IsEL S.G S.a S.ν (S.psiKdC c₀) (S.hpre.restrictφ (bgFieldC S.G' S.a S.ν c₀ S.D'))
      (S.hpre.restrictα α') :=
  isEL_compose S.hpre S.a ha S.ν S.D' hEL

/-! ### The localized background and covariance (P5 (2.18), (2.35)) -/

variable (S) in
/-- **The decoupled approximate minimum `ψ^{(k)}(θ̃, s)`** (P5 (2.18), P3 Proposition 2.3): the
composed datum of `G` over `G'` with the decoupled background of the pair `(C, G')` at the
decoupling vector `s` (Theorem I-4b; radius `ρ`). -/
noncomputable def psiKdAt (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ) (s : Dec2.DecParams C) :
    BgData S.G N :=
  composeData S.hpre S.a (Dec2.decBgField C S.G' S.a S.ν ρ s S.D') S.D'

variable (S) in
/-- **The decoupled covariance `C^{(k)1/2}(s)`** (P5 (2.33)–(2.35), P3 §3): the square root of the
covariance of the pair `(C, G')` at the decoupling vector `s`, with the decoupled background and
multiplier of `θ̃` (the vector extended by `1` off the cover cubes, `Dec2.extS`). -/
noncomputable def covSqrtAt (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ) (s : Dec2.DecParams C) :
    Matrix (S.U × Fin N) (S.U × Fin N) ℂ :=
  Dec2.decCovSqrt C S.G' S.a S.a₁ S.ν (Dec2.decBgMult C S.G' S.a S.ν ρ s S.D')
    (Dec2.extS C s)
    (svec S.G' (Dec2.decBgField C S.G' S.a S.ν ρ s S.D')) (unitQ S.G') (unitP S.G')

variable (S) in
open Classical in
/-- **The localization vector of P5 (2.18), (2.35)** at a unit point `b` with the localization
domain `X₁ b` (P5: `X₁ = R_{k+1}(□')` for the cube `□' ∋ b`), times a decoupling vector `s`: the
parameters of the cover cubes not contained in `X₁ b` are set to `0` (the localization extension
at `s = 0` outside `X₁`, P3 Proposition 2.3; P6 p. 33 "the same extensions but with `s = 0`
outside the domain `R_{k+1}(□')`"). -/
noncomputable def slocOf (C : DecCover d L N₁ m₁ (k + 1))
    (X₁ : S.U → Finset (CTorus d L N₁ m₁ (k + 1))) (s : Dec2.DecParams C) (b : S.U) :
    Dec2.DecParams C :=
  fun P => s P * if cubeP (P : ℕ × CTorus d L N₁ m₁ (k + 1)) ⊆ X₁ b then 1 else 0

theorem slocOf_of_subset (C : DecCover d L N₁ m₁ (k + 1))
    (X₁ : S.U → Finset (CTorus d L N₁ m₁ (k + 1))) (s : Dec2.DecParams C) (b : S.U)
    (P : C.cubeIdx) (h : cubeP (P : ℕ × CTorus d L N₁ m₁ (k + 1)) ⊆ X₁ b) :
    S.slocOf C X₁ s b P = s P := by
  classical
  simp [slocOf, h]

theorem slocOf_of_not_subset (C : DecCover d L N₁ m₁ (k + 1))
    (X₁ : S.U → Finset (CTorus d L N₁ m₁ (k + 1))) (s : Dec2.DecParams C) (b : S.U)
    (P : C.cubeIdx) (h : ¬ cubeP (P : ℕ × CTorus d L N₁ m₁ (k + 1)) ⊆ X₁ b) :
    S.slocOf C X₁ s b P = 0 := by
  classical
  simp [slocOf, h]

variable (S) in
/-- **`ψ^{(k)}_loc(θ)` of P5 (2.39)** on the unit points of the new region: at the unit point `b`,
the value of the decoupled approximate minimum at the localization vector `sloc b` of `b` (P5
(2.18): `ψ^{(k)}(□', θ) = ψ^{(k)}(θ̃, 0)` on `□'`, the pair `(□', R_{k+1}(□'))`). -/
noncomputable def psiLoc (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    (sloc : S.U → Dec2.DecParams C) (b : S.U) : Fin N → ℂ :=
  (S.psiKdAt C ρ (sloc b)).Ψ (unitRep b)

variable (S) in
/-- **`β_k^{-1/2} C^{(k)1/2}_loc ψ̂` of P5 (2.39)**: the row of `b` is the row of `b` of the
decoupled covariance at the localization vector `sloc b` (P5 (2.35)). -/
noncomputable def shiftLoc (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    (sloc : S.U → Dec2.DecParams C) (ψhat : S.U → Fin N → ℂ) (b : S.U) (i : Fin N) : ℂ :=
  ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    ∑ q : S.U × Fin N, S.covSqrtAt C ρ (sloc b) (b, i) q * ψhat q.1 q.2

variable (S) in
/-- **The composed field of P5 (2.39)**: `ψ_k = ψ^{(k)}_loc(θ) + β_k^{-1/2} C^{(k)1/2}_loc ψ̂` on the
unit points of the new region. -/
noncomputable def composed (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    (sloc : S.U → Dec2.DecParams C) (ψhat : S.U → Fin N → ℂ) (b : S.U) (i : Fin N) : ℂ :=
  S.psiLoc C ρ sloc b i + S.shiftLoc C ρ sloc ψhat b i

/-- At `ψ̂ = 0` the composed field is the localized approximate minimum. -/
theorem composed_zero (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    (sloc : S.U → Dec2.DecParams C) :
    S.composed C ρ sloc 0 = S.psiLoc C ρ sloc := by
  funext b i
  simp [composed, shiftLoc]

/-- **The composed field is affine in `ψ̂`**: its value at `ψ̂ + t η` is its value at `ψ̂` plus `t`
times the shift of `η`. -/
theorem composed_affine (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    (sloc : S.U → Dec2.DecParams C) (ψhat η : S.U → Fin N → ℂ) (t : ℂ) :
    S.composed C ρ sloc (ψhat + t • η) =
      S.composed C ρ sloc ψhat + t • S.shiftLoc C ρ sloc η := by
  funext b i
  simp only [composed, shiftLoc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ q : S.U × Fin N, S.covSqrtAt C ρ (sloc b) (b, i) q * (ψhat q.1 q.2 + t * η q.1 q.2)) =
      (∑ q : S.U × Fin N, S.covSqrtAt C ρ (sloc b) (b, i) q * ψhat q.1 q.2) +
        t * ∑ q : S.U × Fin N, S.covSqrtAt C ρ (sloc b) (b, i) q * η q.1 q.2 by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => by ring]
  ring

end HoleStep

/-! ### The whole-lattice step is an instance -/

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- **The whole-lattice step as a step on a region** (the region is the whole torus): `G = 𝔹_k`
(`stepG`), `G'` the generating set of level `k + 1` of the step. -/
noncomputable def toHole : HoleStep d L N₁ m₁ k N ϱ ϱ where
  G := stepG d L N₁ m₁ k ϱ
  G' := S.G'
  hpre := S.hG.precedes S.hG' (le_refl (k + 1))
  topG := by
    simp [stepG, Def6.levelGS]
  topIn := by
    intro x _
    simp [stepG, Def6.levelGS]
  hk1 := S.hk1
  D' := S.D'
  h₀ := S.h₀
  hh₀ := fun x _ i => S.hh₀ x i
  a₁ := S.a₁
  ν := S.ν
  β := S.β
  p₁ := S.p₁
  δ := S.δ

theorem toHole_psiKd : S.toHole.psiKd = S.psiKd := rfl

theorem toHole_covSqrt : S.toHole.covSqrt = S.covSqrt := rfl

theorem toHole_K : S.toHole.K = S.K := rfl

theorem toHole_psi0 : S.toHole.psi0 = S.psi0 := rfl

theorem toHole_shiftU : S.toHole.shiftU = S.shiftU := rfl

theorem toHole_psiAt : S.toHole.psiAt = S.psiAt := rfl

theorem realData_congr {N₀ K' : ℕ} [NeZero N₀] {ϱ₀ : ℝ} (G : GeneratingSet d L N₀ K' ϱ₀)
    {Ψ₁ Ψ₂ : Torus d (N₀ * L ^ K') → Fin N → ℝ} (h₀ : Fin N → ℝ) (h : Ψ₁ = Ψ₂)
    (h₁ : IsLayerConstant G Ψ₁) (h₂ : IsLayerConstant G Ψ₂) :
    realData G Ψ₁ h₀ h₁ = realData G Ψ₂ h₀ h₂ := by
  subst h; rfl

/-- **The whole-lattice datum of the old field is the datum `oldData` of the step on a region**:
every site is in the region, so the lifted field is `liftU`. -/
theorem toHole_oldData (ψ : S.E) : S.toHole.oldData ψ = S.dataU ψ := by
  have hlift : S.toHole.liftIn (fun b i => ψ b i) S.toHole.psiKdRe = liftU S.hG' ψ := by
    funext x i
    have hm : unitBlock x ∈ unitPts S.toHole.G' := (unitPt S.hG' x).2
    rw [HoleStep.liftIn_of_mem _ _ hm]
    rfl
  exact realData_congr (stepG d L N₁ m₁ k ϱ) S.h₀ hlift _ _

end StepSetting

end Balaban.Fluctuation
