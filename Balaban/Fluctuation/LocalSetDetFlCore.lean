/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalSetDetConn
public import Balaban.Fluctuation.LocalFluctGen
public import Balaban.Fluctuation.LocalClassDensityFamilySetCast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The fluctuation core of the local generating sets of the new level

The support, bound, locality and cross theorems of the determinant without `HatConn`
(`LocalSetDetConn`, `LocalSetDetCross*`) hold for every generating set with the fluctuation core
`FlCore`.  The local generating set of a label polymer of the new level is
`𝔹 = castG hc (localB (k + 1) … X hsep)`, the set `𝔹_{k+1}(X)` read on a torus `(N₁', m₁')` with
`N₁' L^{m₁'} = N₁ L^{m₁}`, `m₁ ≤ m₁'` and `ϱ ≤ minSep L L^{m₁'}` (the class index `ϱ`), transported
to the step torus; its fluctuation set is `𝔹⁻ = castG hc (localB k … Ω_k(𝔹_{k+1}(X)))` (the top
layer dropped).  Here the pair `(𝔹, 𝔹⁻)` is shown to have `FlCore`, with the step's numbers:

* `supSep_of_le`: the sup-separation of the layers passes to a finer cube size;
* `precedes_castG_localB_drop`: `𝔹⁻ ≺ 𝔹`, and `Ω_{k+1}(𝔹⁻) = ∅` (`castG_localB_drop_top`);
* `footLocal_castG_localB`: `FootLocal` of `(coverOf 𝔹, H⁻)` for every `H⁻ ≺ 𝔹`, with the
  constants `mixedKc d L`, `Cchi d L` (the P6 pair geometry `p6_coverGeom_of_pair` at the cube size
  `m₁` of the step torus: the layers of `𝔹` are unions of cubes of side `L^{m₁'} L^j`, hence of side
  `L^{m₁} L^j`, and are separated by more than `4 L^{j+1+m₁'} ≥ 4 L^{j+1+m₁}`);
* `flCore_castG_localB`: `FlCore` of `(𝔹, 𝔹⁻)` from `DGSetting` of any generating set of the step
  torus with the same index (`dgSetting_castG_localB`), the background hypotheses and the numerical
  fields of the core (those of the step's core with the constants `mixedKc`, `Cchi`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.GsSpec Balaban.LargeField Finset

section SupSep

variable {d L : ℕ} [NeZero L]

/-- **The sup-separation of the layers passes to a finer cube size**: `SupSep G m'` and `m ≤ m'`
give `SupSep G m` (`4 L^{j+1+m} ≤ 4 L^{j+1+m'}`). -/
theorem supSep_of_le {N₀ K : ℕ} [NeZero N₀] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ} {m m' : ℕ}
    (h : SupSep G m') (hmm : m ≤ m') : SupSep G m := by
  intro j hj1 hjK x hx y hy
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hpow : (L : ℝ) ^ (j + 1 + m) ≤ (L : ℝ) ^ (j + 1 + m') := pow_le_pow_right₀ hL1 (by omega)
  have := h j hj1 hjK x hx y hy
  linarith

end SupSep

section Pair

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {N₁' m₁' : ℕ} [NeZero N₁'] {ϱ ϱ' ϱm : ℝ}

/-- **The fluctuation set of the local generating set precedes it**: for
`𝔹 = castG hc (localB (j + 1) … X hsep)` and `𝔹⁻ = castG hc (localB j … Ω_j(𝔹_{j+1}(X)) hsep')`,
`𝔹⁻ ≺ 𝔹`. -/
theorem precedes_castG_localB_drop (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) {j : ℕ} (hA : j + 1 ≤ K)
    (hB : j ≤ K) (X : Set (CTorus d L N₁' m₁' K)) (hsep : ϱ ≤ minSep L (L ^ m₁'))
    (hsep' : ϱ' ≤ minSep L (L ^ m₁')) :
    Precedes (castG hc (localB j hB (↑((localB (j + 1) hA X hsep).Ω j) :
        Set (CTorus d L N₁' m₁' K)) hsep'))
      (castG hc (localB (j + 1) hA X hsep)) :=
  precedes_castG hc (localB_drop_precedes hA hB X hsep hsep')

/-- **The fluctuation set of the local generating set has no layer above `j`.** -/
theorem castG_localB_drop_top (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) {j : ℕ} (hA : j + 1 ≤ K)
    (hB : j ≤ K) (X : Set (CTorus d L N₁' m₁' K)) (hsep : ϱ ≤ minSep L (L ^ m₁'))
    (hsep' : ϱ' ≤ minSep L (L ^ m₁')) :
    (castG hc (localB j hB (↑((localB (j + 1) hA X hsep).Ω j) :
        Set (CTorus d L N₁' m₁' K)) hsep')).Ω (j + 1) = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  rw [mem_castG_Ω, localB_Ω_of_gt (Nat.lt_succ_self j)]
  exact Finset.notMem_empty _

/-- **`FootLocal` of the pair `(coverOf 𝔹, H⁻)` for a local generating set read on a coarser cube
torus.**  For `𝔹 = castG hc (localB t … X hsep)` (`m₁ ≤ m₁'`) and every `H⁻ ≺ 𝔹`, the pair has the
cover base and the footprint geometry with the constants `mixedKc d L`, `Cchi d L`: the P6 pair
geometry at the cube size `m₁` of the step torus (cube alignment `cubeAligned_of_le`,
sup-separation `supSep_of_le`) and the mixed-wall cut estimate `Dec2.coverBase_mixed`. -/
theorem footLocal_castG_localB (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hm : m₁ ≤ m₁') {t : ℕ}
    (ht : t ≤ K) (X : Set (CTorus d L N₁' m₁' K)) (hsep : ϱ ≤ minSep L (L ^ m₁'))
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm} (hP : Precedes Hm (castG hc (localB t ht X hsep)))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁) {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d)
    (hL : 3 ≤ L) (hν : 0 ≤ ν) (hνL : ν * ((L : ℝ) ^ K) ^ 2 ≤ 1) (ha : IsAdmissibleWeights K a)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1)) :
    Dec2.FootLocal (coverOf (castG hc (localB t ht X hsep))) Hm a ν (Dec2.mixedKc d L)
      (Cchi d L) :=
  { toCoverBase := Dec2.coverBase_mixed hN (castG hc (localB t ht X hsep))
      (p6_coverGeom_of_pair
        (cubeAligned_of_le (cubeAligned_castG hc (localB_cubeAligned ht X hsep (by omega))) hm₁
          hm (dvd_mul_left _ _))
        (supSep_of_le (supSep_castG hc (localB_supSep ht X hsep)) hm) hP hM hd hL hν hνL ha hag)
      hνL (fun _ hq => hq)
    chi_core := (Dec2.footLocalGeom_coverOf _).chi_core }

end Pair

section Core

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {N₁' m₁' : ℕ} [NeZero N₁'] {ϱ : ℝ}

/-- **The fluctuation core of the local generating sets of the new level.**  Let `Gs` be a
generating set of the step torus of index `ϱ` with `DGSetting` (e.g. the level set of the step),
`𝔹 = castG hc (localB (k + 1) … X hsep)` the local generating set read on the torus `(N₁', m₁')`
(`N₁' L^{m₁'} = N₁ L^{m₁}`, `m₁ ≤ m₁'`, `ϱ ≤ minSep L L^{m₁'}`) and
`𝔹⁻ = castG hc (localB k … Ω_k(𝔹_{k+1}(X)) hsep)` its fluctuation set.  With the numerical fields of
the core (constants `mixedKc d L`, `Cchi d L`), the pair `(𝔹, 𝔹⁻)` has `FlCore`. -/
theorem flCore_castG_localB {Gs : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a₁ ν : ℝ}
    (S : DGSetting Gs (compWeight L a₁) ν) (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hm : m₁ ≤ m₁')
    (X : Set (CTorus d L N₁' m₁' (k + 1))) (hsep : ϱ ≤ minSep L (L ^ m₁'))
    {c BG κ eps c₂ BG₂ δ₁ : ℝ} (hS : DecSpecs d L c BG)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (hκ : 0 < κ)
    (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    (hS2 : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM2 : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ₁ : 0 < δ₁)
    (hδ₁le : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hBle : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤
      deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hBone : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤ 1)
    (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2) :
    FlCore N (castG hc (localB (k + 1) (le_refl (k + 1)) X hsep))
      (castG hc (localB k (Nat.le_succ k)
        (↑((localB (k + 1) (le_refl (k + 1)) X hsep).Ω k) : Set (CTorus d L N₁' m₁' (k + 1)))
          hsep))
      a₁ ν c BG κ eps (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂ δ₁ where
  hS := hS
  Sp := dgSetting_castG_localB S hc hm (le_refl (k + 1)) X hsep
  HBp := HBp
  hκ := hκ
  hM := hMc
  eps_pos := heps
  small1 := hsmall
  c7le := hc7
  hS2 := hS2
  SM := footLocal_castG_localB hc hm (le_refl (k + 1)) X hsep
    (precedes_castG_localB_drop hc (le_refl (k + 1)) (Nat.le_succ k) X hsep hsep) S.big
    S.aligned.two_le S.hM S.hd S.hL S.mass S.massLe S.weights S.sep
  hM2 := hM2
  hPmp := precedes_castG_localB_drop hc (le_refl (k + 1)) (Nat.le_succ k) X hsep hsep
  δ₁_pos := hδ₁
  δ₁_le := hδ₁le
  B_le := hBle
  B_one := hBone
  phi_lt := hphi

end Core

end Balaban.Fluctuation
