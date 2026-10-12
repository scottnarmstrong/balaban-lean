/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RLaneWitness
public import Balaban.Inhabited.PsiZeroWitness
public import Balaban.LargeField.R.Denominator
public import Balaban.LargeField.R.CancelStationary
public import Balaban.LargeField.R.RopPhysical
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The R step at the actual ripe window of `ripeRemHistory`: denominator and normalization

LF-RECONSTRUCTION Lemma III.8.2 (`denominator_eq`) and Lemma III.8.4 (`R_normalization_ripe`),
instantiated at the boundary piece `𝔹_T(U_T)` of the window of the removed component of
`ripeRemHistory`, with the constant unit datum (which lies in the tube).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.Inhabited.RLane

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.Localization
  Balaban.LargeField.RegionHistory MeasureTheory

section Generic

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M] {k : ℕ} (Z : H.Comp k)
  (g : Geo S n R S.M) (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) (hkK : k ≤ K) (hk : 1 ≤ k)
  (hd : 2 ≤ S.d) {D : ℕ} (b0 : Torus S.d (S.M * n k * S.L ^ (k - k))) (w : Fin S.d → ℕ)
  (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ S.M * n k * S.L ^ (k - k))
  (hbx : ∀ x : Torus S.d (S.M * n k * S.L ^ k), (jBlock S.d S.L (S.M * n k) k k x ∈ box b0 w ↔
        blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k Z))
  (a : ℕ → ℝ) (hBg : BgHyp S.d S.L k (winSep g) a 0) (N : ℕ) [NeZero N]

local notation "Gb" => windowBdry H Z g
local notation "hX" => H.ripeX_hXreg hR hkK hk Z hbx
local notation "hO" => windowBdry_overTop H Z g hR hkK hk hbx
local notation "hDa" => windowBdry_hdata H Z g hkK

/-- **Lemma III.8.2 at the window** (T4): for the constant unit datum (in the tube), the massless
reference integral over the box `Z₀` of the window is positive and has the form of the lemma. -/
def RipeDenominator : Prop :=
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδc : δ ≤ psiZeroC11 N Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg)
      (β p0 : ℝ), 0 < β ∧
      ∫ u, rhoZero Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg hδ hδc
          (tube_constBlock Gb (NeZero.pos N) hδ _) β p0 u =
        Real.exp (-β * effActionNorm Gb a (psiZero N Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg hδ hδc
            (tube_constBlock Gb (NeZero.pos N) hδ _))
          - (N : ℝ) / 2 * Real.log β * ((boxFinset (L := S.L) (N₀ := S.M * n k) (k := k) b0 w).card : ℝ) +
          tildeE0 Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg hδ hδc
            (tube_constBlock Gb (NeZero.pos N) hδ _) β p0) ∧
      0 < ∫ u, rhoZero Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg hδ hδc
          (tube_constBlock Gb (NeZero.pos N) hδ _) β p0 u

include hBg hbx in
theorem ripe_denominator : RipeDenominator H Z g hR hkK hk hd b0 w hw1 hwD hm hbx a hBg N := by
  obtain ⟨δ, hδ, hδc, hKδ⟩ := ActionConv.smallness_satisfiable (N := N) (D := D) Gb a hd hk b0 w hw1
    hwD hm hX hO hDa hBg
  have hK := psiZeroK_pos N Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg
  have hC : 0 < cSix S.d D (psiZeroK N Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg) := by
    unfold cSix
    have hd0 : (0 : ℝ) < S.d := by exact_mod_cast (by omega : 0 < S.d)
    have hD1 : (0 : ℝ) < D := by
      have d0 : 0 < S.d := by omega
      exact_mod_cast (lt_of_lt_of_le (hw1 ⟨0, d0⟩) (hwD _))
    positivity
  obtain ⟨β, p0, hβ, hp0, hrad⟩ := denominator_params_exist (d := S.d) (L := S.L) (N := N) (D := D)
    hC hKδ
  have hden := denominator_eq (N := N) Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg hδ hδc
    (tube_constBlock Gb (NeZero.pos N) hδ _) hβ hp0 hrad
  exact ⟨δ, hδ, hδc, β, p0, hβ, hden.1, hden.2.1⟩

/-- **`psiZero_spec` at the window** (T3): for the constant unit datum (in the tube) at some admissible
`δ`, `ψ⁰_k` solves (2.34) in `Ψ̃(X; K₆ δ)` and every solution equals it. -/
def RipePsiZeroSpec : Prop :=
  ∃ (δ : ℝ) (hδ : 0 < δ) (hδc : δ ≤ psiZeroC11 N Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg),
    PsiZeroSol Gb a b0 w (H.ripeX Z) (psiZeroK N Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg * δ)
        (constBlock (NeZero.pos N)) (psiZero N Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg hδ hδc
          (tube_constBlock Gb (NeZero.pos N) hδ _)) ∧
      ∀ ψ, PsiZeroSol Gb a b0 w (H.ripeX Z)
          (psiZeroK N Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg * δ) (constBlock (NeZero.pos N)) ψ →
        ψ = psiZero N Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg hδ hδc
          (tube_constBlock Gb (NeZero.pos N) hδ _)

include hBg hbx in
theorem ripe_psiZero_spec : RipePsiZeroSpec H Z g hR hkK hk hd b0 w hw1 hwD hm hbx a hBg N := by
  obtain ⟨δ, hδ, hδc, -⟩ := ActionConv.smallness_satisfiable (N := N) (D := D) Gb a hd hk b0 w hw1
    hwD hm hX hO hDa hBg
  exact ⟨δ, hδ, hδc, psiZero_spec N Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg hδ hδc
    (tube_constBlock Gb (NeZero.pos N) hδ _)⟩

local notation "Zc1" => (fun _ : Unit => Z)
local notation "hZc1" => (fun _ _ _ => rfl : Function.Injective (fun _ : Unit => Z))
local notation "hsep1" => H.zeroDomain_hsep hkK hk (fun _ : Unit => Z) (fun _ _ _ => rfl)
  (fun _ : Unit => b0) (fun _ : Unit => w) (fun _ : Unit => hbx)

/-- **Lemma III.8.4 (normalization) at the window of the removed component** (T4): the family
consisting of the one removed component `Z` of `ripeRemHistory`.  There are parameters
`δ, β, p₀` in the range of the lemma (constructed from `denominator_params_exist` and the smallness
of `psiZero_exists_unique`) for which `∫ R[ρ] = ∫ ρ` over the tube for every integrable `ρ`. -/
def RipeNormalization : Prop :=
    ∃ (δ : Unit → ℝ) (hδ : ∀ c, 0 < δ c)
      (hδc : ∀ c, δ c ≤ psiZeroC11 N Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg) (β p0 : ℝ),
      0 < β ∧
      (∀ c ∈ (Finset.univ : Finset Unit),
        1 ≤ cSix S.d D (psiZeroK N Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg) * p0) ∧
      (∀ c ∈ (Finset.univ : Finset Unit),
        psiZeroK N Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg * δ c +
          5 * zeroRadius (cSix S.d D (psiZeroK N Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg)) β p0 ≤
          etaDen S.d S.L N D) ∧
      ∀ {ρ : BlockField S.d S.L (S.M * n k) k N → ℝ},
        Integrable ρ (volume.restrict (famTubeSet N (fun _ : Unit => Gb) (fun _ : Unit => b0)
          (fun _ : Unit => w) (fun _ : Unit => H.ripeX Z) δ)) →
        Integrable (Rop (famDecomp N (fun _ : Unit => Gb) a hd hk (fun _ : Unit => b0)
            (fun _ : Unit => w) (fun _ _ => hw1 _) (fun _ _ => hwD _) hm (fun _ : Unit => H.ripeX Z)
            (fun _ => hX) hsep1 (fun _ => hO) (fun _ => hDa) hBg δ hδ hδc Finset.univ β p0) ρ)
          (volume.restrict (famTubeSet N (fun _ : Unit => Gb) (fun _ : Unit => b0)
            (fun _ : Unit => w) (fun _ : Unit => H.ripeX Z) δ)) ∧
        ∫ ψ, Rop (famDecomp N (fun _ : Unit => Gb) a hd hk (fun _ : Unit => b0)
            (fun _ : Unit => w) (fun _ _ => hw1 _) (fun _ _ => hwD _) hm (fun _ : Unit => H.ripeX Z)
            (fun _ => hX) hsep1 (fun _ => hO) (fun _ => hDa) hBg δ hδ hδc Finset.univ β p0) ρ ψ
            ∂(volume.restrict (famTubeSet N (fun _ : Unit => Gb) (fun _ : Unit => b0)
              (fun _ : Unit => w) (fun _ : Unit => H.ripeX Z) δ)) =
          ∫ ψ, ρ ψ ∂(volume.restrict (famTubeSet N (fun _ : Unit => Gb) (fun _ : Unit => b0)
            (fun _ : Unit => w) (fun _ : Unit => H.ripeX Z) δ))

include hBg hbx in
theorem ripe_normalization : RipeNormalization H Z g hR hkK hk hd b0 w hw1 hwD hm hbx a hBg N := by
  obtain ⟨δ, hδ, hδc, hKδ⟩ := ActionConv.smallness_satisfiable (N := N) (D := D) Gb a hd hk b0 w hw1
    hwD hm hX hO hDa hBg
  have hK := psiZeroK_pos N Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg
  have hC : 0 < cSix S.d D (psiZeroK N Gb a hd hk b0 w hw1 hwD hm hX hO hDa hBg) := by
    unfold cSix
    have hd0 : (0 : ℝ) < S.d := by exact_mod_cast (by omega : 0 < S.d)
    have hD1 : (0 : ℝ) < D := by
      have d0 : 0 < S.d := by omega
      exact_mod_cast (lt_of_lt_of_le (hw1 ⟨0, d0⟩) (hwD _))
    positivity
  obtain ⟨β, p0, hβ, hp0, hrad⟩ := denominator_params_exist (d := S.d) (L := S.L) (N := N) (D := D)
    hC hKδ
  refine ⟨fun _ => δ, fun _ => hδ, fun _ => hδc, β, p0, hβ, fun _ _ => hp0, fun _ _ => hrad, ?_⟩
  intro ρ hρ
  exact H.R_normalization_ripe hR hkK N (fun _ : Unit => Z) (fun _ _ _ => rfl)
    (fun _ : Unit => Gb) a hd hk (fun _ : Unit => b0) (fun _ : Unit => w) (fun _ _ => hw1 _)
    (fun _ _ => hwD _) hm (fun _ => hbx) (fun _ => hO)
    (fun _ _ hx => windowBdry_dataSites_cube H Z g
      (fun i hi => H.F.hnn i (lt_of_lt_of_le hi hkK)) hx) hBg (fun _ => δ) (fun _ => hδ)
    (fun _ => hδc) Finset.univ hβ (fun _ _ => hp0) (fun _ _ => hrad) hρ

end Generic

section Concrete

open Balaban.Inhabited.RipeRemoval Balaban.Inhabited.RadiiSet Balaban.Inhabited RadiiHist

/-- The box `Z₀` of the window of the removed component exists with the properties used below
(`exists_window_box` at the witness). -/
theorem ripeRem_window_box (Z : ripeRemHistory.Comp (Tstar wS))
    (hW : ripeRemHistory.RipeWindow (Tstar wS) Z) :
    ∃ (b0 : Torus wS.d (wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS) *
        wS.L ^ (Tstar wS - Tstar wS))) (w : Fin wS.d → ℕ),
      (∀ i, 1 ≤ w i ∧ w i ≤ 3 * wS.c0 + 4) ∧
      ∀ x : Torus wS.d (wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS) * wS.L ^ Tstar wS),
        (jBlock wS.d wS.L (wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS)) (Tstar wS)
          (Tstar wS) x ∈ box b0 w ↔
          blockMap (wS.L ^ Tstar wS) (wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS)) x ∈
            ripeRemHistory.Zzero (Tstar wS) Z) :=
  ripeRemHistory.exists_window_box wS_good wS_h18 wS_hR0 (Nat.le_succ _) hW le_rfl ripeRem_hT

/-- **Lemma III.8.2 at the actual removal step** (T4): the denominator of the R operation at the
window of the component removed by `ripeRemHistory`. -/
theorem ripeRem_denominator (Z : ripeRemHistory.Comp (Tstar wS))
    (b0 : Torus wS.d (wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS) *
        wS.L ^ (Tstar wS - Tstar wS))) (w : Fin wS.d → ℕ)
    (hw : ∀ i, 1 ≤ w i ∧ w i ≤ 3 * wS.c0 + 4)
    (hbx : ∀ x : Torus wS.d (wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS) *
        wS.L ^ Tstar wS),
      (jBlock wS.d wS.L (wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS)) (Tstar wS)
        (Tstar wS) x ∈ box b0 w ↔
        blockMap (wS.L ^ Tstar wS) (wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS)) x ∈
          ripeRemHistory.Zzero (Tstar wS) Z)) (N : ℕ) [NeZero N] :
    RipeDenominator ripeRemHistory Z (wGeo _) (fun j => wR_eq j) (Nat.le_succ _) (one_le_Tstar _)
      (by show 2 ≤ 3; norm_num) b0 w (fun i => (hw i).1) (fun i => (hw i).2)
      (by simpa using (by have := ripeRem_hn; omega : 3 * wS.c0 + 4 + 2 ≤
        wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS))) hbx (compWeight wS.L 1)
      (wS_bgHyp _ _) N :=
  ripe_denominator ripeRemHistory Z (wGeo _) (fun j => wR_eq j) (Nat.le_succ _) (one_le_Tstar _)
    (by show 2 ≤ 3; norm_num) b0 w (fun i => (hw i).1) (fun i => (hw i).2)
    (by simpa using (by have := ripeRem_hn; omega : 3 * wS.c0 + 4 + 2 ≤
      wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS))) hbx (compWeight wS.L 1)
    (wS_bgHyp _ _) N

/-- **The R step at the removal step of an actual admissible history** (T3/T4): for the component
`Z` removed by `ripeRemHistory` (the ripe component of `Z^pre_T`) and the box `Z₀` of its window, the
reference minimizer `ψ⁰_k` at `G′ = 𝔹_T(U_T)` exists and is unique, the reference integral is positive
(`denominator_eq`) and `R` preserves the integral (`R_normalization_ripe`). -/
theorem ripeRem_R_step (N : ℕ) [NeZero N] :
    ∃ Z : ripeRemHistory.Comp (Tstar wS), Z.1 ∈ ripeRemHistory.rem (Tstar wS) ∧
      wS.Ripe (Tstar wS) (ripeRemHistory.bk (Tstar wS) Z) ∧
      ripeRemHistory.RipeWindow (Tstar wS) Z ∧
        ∃ (b0 : Torus wS.d (wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS) *
            wS.L ^ (Tstar wS - Tstar wS))) (w : Fin wS.d → ℕ)
          (hw : ∀ i, 1 ≤ w i ∧ w i ≤ 3 * wS.c0 + 4)
          (hbx : ∀ x : Torus wS.d (wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS) *
              wS.L ^ Tstar wS),
            (jBlock wS.d wS.L (wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS)) (Tstar wS)
              (Tstar wS) x ∈ box b0 w ↔
              blockMap (wS.L ^ Tstar wS) (wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS)) x ∈
                ripeRemHistory.Zzero (Tstar wS) Z)),
          RipePsiZeroSpec ripeRemHistory Z (wGeo _) (fun j => wR_eq j) (Nat.le_succ _)
              (one_le_Tstar _) (by show 2 ≤ 3; norm_num) b0 w (fun i => (hw i).1)
              (fun i => (hw i).2)
              (by simpa using (by have := ripeRem_hn; omega : 3 * wS.c0 + 4 + 2 ≤
                wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS))) hbx (compWeight wS.L 1)
              (wS_bgHyp _ _) N ∧
          RipeDenominator ripeRemHistory Z (wGeo _) (fun j => wR_eq j) (Nat.le_succ _)
              (one_le_Tstar _) (by show 2 ≤ 3; norm_num) b0 w (fun i => (hw i).1)
              (fun i => (hw i).2)
              (by simpa using (by have := ripeRem_hn; omega : 3 * wS.c0 + 4 + 2 ≤
                wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS))) hbx (compWeight wS.L 1)
              (wS_bgHyp _ _) N ∧
          RipeNormalization ripeRemHistory Z (wGeo _) (fun j => wR_eq j) (Nat.le_succ _)
              (one_le_Tstar _) (by show 2 ≤ 3; norm_num) b0 w (fun i => (hw i).1)
              (fun i => (hw i).2)
              (by simpa using (by have := ripeRem_hn; omega : 3 * wS.c0 + 4 + 2 ≤
                wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS))) hbx (compWeight wS.L 1)
              (wS_bgHyp _ _) N := by
  obtain ⟨Z, hrem, hrip, hW, -⟩ := ripeRemHistory_windowOfHistory_hyp
  obtain ⟨b0, w, hw, hbx⟩ := ripeRem_window_box Z hW
  have hm : 3 * wS.c0 + 4 + 2 ≤ wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS) := by
    have := ripeRem_hn; omega
  refine ⟨Z, hrem, hrip, hW, b0, w, hw, hbx, ?_, ?_, ?_⟩
  · exact ripe_psiZero_spec ripeRemHistory Z (wGeo _) (fun j => wR_eq j) (Nat.le_succ _)
      (one_le_Tstar _) (by show 2 ≤ 3; norm_num) b0 w (fun i => (hw i).1) (fun i => (hw i).2)
      (by simpa using hm) hbx (compWeight wS.L 1) (wS_bgHyp _ _) N
  · exact ripe_denominator ripeRemHistory Z (wGeo _) (fun j => wR_eq j) (Nat.le_succ _)
      (one_le_Tstar _) (by show 2 ≤ 3; norm_num) b0 w (fun i => (hw i).1) (fun i => (hw i).2)
      (by simpa using hm) hbx (compWeight wS.L 1) (wS_bgHyp _ _) N
  · exact ripe_normalization ripeRemHistory Z (wGeo _) (fun j => wR_eq j) (Nat.le_succ _)
      (one_le_Tstar _) (by show 2 ≤ 3; norm_num) b0 w (fun i => (hw i).1) (fun i => (hw i).2)
      (by simpa using hm) hbx (compWeight wS.L 1) (wS_bgHyp _ _) N

end Concrete

end Balaban.Inhabited.RLane
