/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCovX0Sup
public import Balaban.Localization.DecoupledCovAnalyticFull
public import Balaban.Fluctuation.CovSqrtSupComplexDec
public import Balaban.Fluctuation.LocalFluctGen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The local hat square root: sup bound and the local hat lift

The cover-form twins of the analyticity and bounds of `decCovSqrt` (for the data
`Dec2.XCover (coverOf G) G …`, no `DGSetting`) live next to their originals:
`rectAt_decCov_full_cover`, `analyticOnNhd_decCovSqrt_entry_cover` (`DecoupledCovAnalyticFull`),
`decCovSqrt_bound_cover` (`DecoupledSqrt`), `covC_sqrt_supNorm_cover` (`CovSqrtSupComplex`); the
landed statements are their applications through `Dec2.xCover_self` / `XData.toCover`.  Here:

* `decCovSqrt_supNorm_cover`: the sup bound `K c`, `K = covSupConstC d L N (a k) κ`, on `DecDom`;
* `localLift_mem_flBallLC_of_top_empty`, `localHatLift_mem_flBallLC_cover`: the local hat lift
  (the hat variable on the unit lattice of `G`, `ψ' = cc C^{1/2}(s) ψ̂` extended by zero off the
  unit blocks of `G`) is a block fluctuation of every generating set without layer `k + 1`;
* `localB_analyticOnNhd_decCovSqrt_entry`, `localB_localHatLift_mem_flBallLC`: the instances at the
  literal local generator, at the unit lattice `(unitQ, unitP)`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.LargeField Finset Matrix

section LocalHat

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱl : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
variable {a : ℕ → ℝ} {aT ν Cx κ δ δ₁ : ℝ}

/-- **The sup bound of `C^{1/2}(s)` on `DecDom`, cover form**: for `e = (s, φ₀, α₀) ∈ DecDom`,
`|(C^{1/2}(s) v)(p)| ≤ K c` for `|v| ≤ c` on the unit lattice, `K = covSupConstC d L N (a k) κ`. -/
theorem decCovSqrt_supNorm_cover (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hCx : 0 ≤ Cx)
    (hκ : 0 ≤ κ) (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) {e : DecData G N}
    (he : e ∈ DecDom G N κ δ) (v : unitPts G × Fin N → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hv : ∀ p, ‖v p‖ ≤ c) (p : unitPts G × Fin N) :
    ‖(decCovSqrt G a aT ν e.2.2 (extS G e.1) e.2.1 (unitQ G) (unitP G) *ᵥ v) p‖ ≤
      covSupConstC d L N (a k) κ * c :=
  covC_sqrt_supNorm_cover (fun (x : ℝ) (hx : 0 ≤ x) => xData_cover_of_mem (N := N) S hCx hx hκ hM he)
    he.2.1.toIsConstraintField hδ hsm v hc hv p

/-- **A field on the unit lattice of a generating set, extended by zero to the fine lattice and
lifted, is a block fluctuation of every generating set without layer `k + 1`**: the lift is
`ψ'(x) = v(unitBlock x)` on the unit blocks of `G` and `0` elsewhere; it is constant on the blocks
of the layers `n ≤ k`, and lies in `FlBallLC Hl δ₁` when `|v| < δ₁` at the unit points of `G`.
(This is `liftC_mem_flBallLC_of_top_empty` without `IsLevel G (k + 1)`: the local generator has
unit points only over its top layer.) -/
theorem localLift_mem_flBallLC_of_top_empty (hHl : Hl.Ω (k + 1) = ∅) (hδ₁ : 0 < δ₁)
    {v : unitPts G × Fin N → ℂ} (hv : ∀ b : unitPts G, vn (fun i => v (b, i)) < δ₁) :
    (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts G then v (⟨unitBlock x, h⟩, i) else 0) ∈ FlBallLC Hl δ₁ := by
  classical
  refine ⟨fun x _ => ?_, ?_⟩
  · by_cases h : unitBlock x ∈ unitPts G
    · simpa only [h, dite_true] using hv ⟨unitBlock x, h⟩
    · have : (fun i : Fin N => if h : unitBlock x ∈ unitPts G then v (⟨unitBlock x, h⟩, i)
          else 0) = fun _ => 0 := by
        funext i; simp [h]
      show vn (fun i : Fin N => if h : unitBlock x ∈ unitPts G then v (⟨unitBlock x, h⟩, i)
          else 0) < δ₁
      rw [this, vn_eq_sqrt]
      simpa using hδ₁
  · intro n hn1 hnk x hx x' hx'
    have hn : n ≤ k := by
      by_contra h
      obtain rfl : n = k + 1 := by omega
      rw [GeneratingSet.mem_layer, hHl] at hx
      exact Finset.notMem_empty _ hx.1
    have hb : jBlock d L (N₁ * L ^ m₁) (k + 1) k x' = jBlock d L (N₁ * L ^ m₁) (k + 1) k x :=
      jBlock_eq_of_le hn (by omega) (GeneratingSet.mem_blk.1 hx')
    have hu : unitBlock x' = unitBlock x := hb
    funext i
    simp only [hu]

/-- **The local hat lift lands in the local fluctuation ball** (cover form, any `G` with the
standing data `Dec2.XCover (coverOf G) G …`).  For a datum `e = (s, φ₀, α₀) ∈ DecDom`, a hat
variable `ψ̂` on the unit lattice of `G` with `|ψ̂| ≤ c_ψ`, and the bound
`√N ‖cc‖ K c_ψ < δ₁`, the fluctuation `ψ' = cc C^{1/2}(s) ψ̂` (extended by zero outside the unit
blocks of `G` and lifted to the fine lattice) is a block fluctuation of every generating set
without layer `k + 1`, in particular of `𝔹_k(Y)`. -/
theorem localHatLift_mem_flBallLC_cover (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hCx : 0 ≤ Cx)
    (hκ : 0 ≤ κ) (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) {e : DecData G N}
    (he : e ∈ DecDom G N κ δ) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ) (hδ₁0 : 0 < δ₁)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (a k) κ * cψ)) < δ₁)
    {ψh : unitPts G × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hHl : Hl.Ω (k + 1) = ∅) :
    (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts G then
        (cc • (decCovSqrt G a aT ν e.2.2 (extS G e.1) e.2.1 (unitQ G) (unitP G) *ᵥ ψh))
          (⟨unitBlock x, h⟩, i)
      else 0) ∈ FlBallLC Hl δ₁ := by
  refine localLift_mem_flBallLC_of_top_empty hHl hδ₁0 fun b => ?_
  have hsup := decCovSqrt_supNorm_cover (N := N) S hCx hκ hM hδ hsm he ψh hcψ hψh
  have hcoord : ∀ i, ‖(cc • (decCovSqrt G a aT ν e.2.2 (extS G e.1) e.2.1 (unitQ G) (unitP G) *ᵥ
      ψh)) (b, i)‖ ≤ ‖cc‖ * (covSupConstC d L N (a k) κ * cψ) := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hsup (b, i)) (norm_nonneg _)
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : vn (fun i : Fin 0 => (cc • (decCovSqrt G a aT ν e.2.2 (extS G e.1) e.2.1 (unitQ G)
        (unitP G) *ᵥ ψh)) (b, i)) = 0 := by
      rw [vn_eq_sqrt]; simp
    rw [this]; exact hδ₁0
  · have hV : 0 ≤ ‖cc‖ * (covSupConstC d L N (a k) κ * cψ) :=
      (norm_nonneg _).trans (hcoord ⟨0, hN⟩)
    exact lt_of_le_of_lt (vn_le_sqrt_mul hV hcoord) hδ₁

end LocalHat

section LocalB

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱl : ℝ}
variable {a : ℕ → ℝ} {aT ν κ δ δ₁ : ℝ}

/-- **The local hat square root is analytic on the polydisc** (instance at the literal local
generator `𝔹(Y) = localB j hj Y`, with `Dec2.XCover (coverOf 𝔹) 𝔹` from `localB_xCover`, `k ≥ 1`):
every entry of `C^{1/2}(s)` at the unit lattice of `𝔹(Y)` is analytic in `(s, φ₀, α₀)` on
`DecDom`. -/
theorem localB_analyticOnNhd_decCovSqrt_entry {j : ℕ} (hj : j ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱ ≤ minSep L (L ^ m₁)) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1)) (hk : 1 ≤ k) (haT1 : 1 / 2 ≤ aT)
    (haT2 : aT ≤ 2) (hκ : 0 ≤ κ)
    (hbig : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (p q : unitPts (SmallField.GsSpec.localB j hj Y hsep) × Fin N) :
    AnalyticOnNhd ℂ (fun e : DecData (SmallField.GsSpec.localB j hj Y hsep) N =>
      decCovSqrt (SmallField.GsSpec.localB j hj Y hsep) a aT ν e.2.2
        (extS (SmallField.GsSpec.localB j hj Y hsep) e.1) e.2.1
        (unitQ (SmallField.GsSpec.localB j hj Y hsep))
        (unitP (SmallField.GsSpec.localB j hj Y hsep)) p q)
      (DecDom (SmallField.GsSpec.localB j hj Y hsep) N κ δ) :=
  analyticOnNhd_decCovSqrt_entry_cover
    (localB_xCover hj Y hsep hm₁ hM hd hL hν hνL ha hag hk haT1 haT2) (Cchi_nonneg d L) hκ hbig
    hδ hsm (isUnitLatticeB_unit (G := SmallField.GsSpec.localB j hj Y hsep)).toIsUnitLattice p q

/-- **The local hat lift lands in the local fluctuation ball** (instance at `𝔹(Y) = localB j hj Y`
of `localHatLift_mem_flBallLC_cover`; `H⁻` is any generating set without layer `k + 1`, e.g.
`𝔹_k(Y)` of `GsSpec.localB_drop_top`). -/
theorem localB_localHatLift_mem_flBallLC {j : ℕ} (hj : j ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱ ≤ minSep L (L ^ m₁)) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1)) (hk : 1 ≤ k) (haT1 : 1 / 2 ≤ aT)
    (haT2 : aT ≤ 2) (hκ : 0 ≤ κ)
    (hbig : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {e : DecData (SmallField.GsSpec.localB j hj Y hsep) N}
    (he : e ∈ DecDom (SmallField.GsSpec.localB j hj Y hsep) N κ δ) (cc : ℂ) {cψ : ℝ}
    (hcψ : 0 ≤ cψ) (hδ₁0 : 0 < δ₁)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (a k) κ * cψ)) < δ₁)
    {ψh : unitPts (SmallField.GsSpec.localB j hj Y hsep) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) {Hl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
    (hHl : Hl.Ω (k + 1) = ∅) :
    (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts (SmallField.GsSpec.localB j hj Y hsep) then
        (cc • (decCovSqrt (SmallField.GsSpec.localB j hj Y hsep) a aT ν e.2.2
          (extS (SmallField.GsSpec.localB j hj Y hsep) e.1) e.2.1
          (unitQ (SmallField.GsSpec.localB j hj Y hsep))
          (unitP (SmallField.GsSpec.localB j hj Y hsep)) *ᵥ ψh)) (⟨unitBlock x, h⟩, i)
      else 0) ∈ FlBallLC Hl δ₁ :=
  localHatLift_mem_flBallLC_cover
    (localB_xCover hj Y hsep hm₁ hM hd hL hν hνL ha hag hk haT1 haT2) (Cchi_nonneg d L) hκ hbig
    hδ hsm he cc hcψ hδ₁0 hδ₁ hψh hHl

end LocalB

end Balaban.Localization
