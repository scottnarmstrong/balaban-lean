/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepRegBg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The composed data `ψ_k^{(j)}(ψ^{(k)} + s ψ')` are smooth along the ray

The composed field of (6.2), `composeField`, is a finite linear combination of the coordinates of the
pair `(φ', Ψ')` (block averages, the extension `φ̄'`), hence `C^∞` in it
(`contDiff_composeField`).  With the smoothness of `bgField` along the ray (`StepRegBg`) the pair
`(ψ_k^{(j)}, h)` of (H.2) is `C^∞` along the ray (`RayData.contDiffAt_pairRay`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory Set Matrix

section Compose

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

theorem contDiff_svec_phi {n : WithTop ℕ∞} (y : Torus d (N₀ * L ^ k)) (i : Fin N) :
    ContDiff ℝ n (fun φ : G'.Ω 1 × Fin N → ℂ => svec G' φ y i) := by
  classical
  by_cases hy : y ∈ G'.Ω 1
  · simp only [svec_of_mem G' _ ⟨y, hy⟩ i]
    exact contDiff_apply ℝ ℂ ((⟨y, hy⟩ : G'.Ω 1), i)
  · simp only [svec_of_not_mem G' _ hy i]
    exact contDiff_const

/-- **The composed field is `C^∞` in the pair `(φ', Ψ')`** (it is linear). -/
theorem contDiff_composeField (a : ℕ → ℝ) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    ContDiff ℝ ⊤ (fun p : (G'.Ω 1 × Fin N → ℂ) × (Torus d (N₀ * L ^ k) → Fin N → ℂ) =>
      composeField G G' a p.1 p.2 x i) := by
  classical
  have hbm : ∀ (H : GeneratingSet d L N₀ k ϱ) (n : ℕ),
      ContDiff ℝ ⊤ (fun p : (G'.Ω 1 × Fin N → ℂ) × (Torus d (N₀ * L ^ k) → Fin N → ℂ) =>
        blockMean H n (fun y => svec G' p.1 y i) x) := by
    intro H n
    unfold blockMean
    exact contDiff_const.mul (ContDiff.sum fun y _ =>
      (contDiff_svec_phi (G' := G') y i).comp contDiff_fst)
  have hbm' : ∀ (H : GeneratingSet d L N₀ k ϱ') (n : ℕ),
      ContDiff ℝ ⊤ (fun p : (G'.Ω 1 × Fin N → ℂ) × (Torus d (N₀ * L ^ k) → Fin N → ℂ) =>
        blockMean H n (fun y => svec G' p.1 y i) x) := by
    intro H n
    unfold blockMean
    exact contDiff_const.mul (ContDiff.sum fun y _ =>
      (contDiff_svec_phi (G' := G') y i).comp contDiff_fst)
  have hΨ : ContDiff ℝ ⊤ (fun p : (G'.Ω 1 × Fin N → ℂ) × (Torus d (N₀ * L ^ k) → Fin N → ℂ) =>
      p.2 x i) :=
    (contDiff_apply ℝ ℂ i).comp ((contDiff_apply ℝ (Fin N → ℂ) x).comp contDiff_snd)
  by_cases hx : x ∈ G.Ω 1
  · have : (fun p : (G'.Ω 1 × Fin N → ℂ) × (Torus d (N₀ * L ^ k) → Fin N → ℂ) =>
        composeField G G' a p.1 p.2 x i) = fun p =>
        blockMean G (G.layerIndex x) (fun y => svec G' p.1 y i) x +
          ((a (G'.layerIndex x) / a (G.layerIndex x) *
            (((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2) : ℝ) : ℂ) *
            (p.2 x i - blockMean G' (G'.layerIndex x) (fun y => svec G' p.1 y i) x) :=
      funext fun p => composeField_of_mem a p.1 p.2 hx i
    rw [this]
    exact (hbm G _).add (contDiff_const.mul (hΨ.sub (hbm' G' _)))
  · by_cases hc : x ∈ collar G
    · have : (fun p : (G'.Ω 1 × Fin N → ℂ) × (Torus d (N₀ * L ^ k) → Fin N → ℂ) =>
          composeField G G' a p.1 p.2 x i) = fun p => barField G' p.2 p.1 x i :=
        funext fun p => composeField_of_collar a p.1 p.2 hc i
      rw [this]
      unfold barField
      by_cases h' : x ∈ G'.Ω 1
      · simp only [h', dite_true]
        exact (contDiff_apply ℝ ℂ ((⟨x, h'⟩ : G'.Ω 1), i)).comp contDiff_fst
      · simp only [h', dite_false]
        exact hΨ
    · have : (fun p : (G'.Ω 1 × Fin N → ℂ) × (Torus d (N₀ * L ^ k) → Fin N → ℂ) =>
          composeField G G' a p.1 p.2 x i) = fun _ => 0 :=
        funext fun p => composeField_of_not_mem a p.1 p.2
          (fun h => by
            rcases (mem_dataSites G).1 h with h | h
            · exact hx h
            · exact hc h) i
      rw [this]
      exact contDiff_const

end Compose

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {pp : ℝ}

/-- The pair `(ψ_k^{(j)}, h)` of (H.2) of the datum of `ψ^{(k)} + s ψ'`. -/
noncomputable def pairRay (j : ℕ) (q : ℝ × S.E) :
    Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N :=
  composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU (S.psiAt q.1 q.2))

/-- **The composed data are smooth along the ray**: for `1 ≤ j ≤ k`, the pair `(ψ_k^{(j)}, h)` of
the datum of `ψ^{(k)} + s ψ'` is `C^∞` near every `(s, ψ̂)` with `|s| ‖ψ̂‖ < p⁺`. -/
theorem RayData.contDiffAt_pairRay (R : S.RayData pp) {j : ℕ} (hj : j ≤ k) {q : ℝ × S.E}
    (hq : |q.1| * ‖q.2‖ < pp) : ContDiffAt ℝ ⊤ (S.pairRay (N := N) j) q := by
  classical
  have hjk : j ≤ k + 1 := hj.trans (Nat.le_succ k)
  have hraw : ContDiff ℝ ⊤ (fun q : ℝ × S.E => S.rawU (S.psiAt q.1 q.2)) :=
    S.contDiff_rawU.comp S.contDiff_psiAt
  have hbg := R.contDiffAt_bgFieldRay hq
  have hpair : ContDiffAt ℝ ⊤ (fun q : ℝ × S.E =>
      (bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataU (S.psiAt q.1 q.2)),
        (S.dataU (S.psiAt q.1 q.2)).Ψ)) q := by
    refine hbg.prodMk ?_
    have : (fun q : ℝ × S.E => (S.dataU (S.psiAt q.1 q.2)).Ψ) =
        fun q => (S.rawU (S.psiAt q.1 q.2)).1 := by
      funext q
      exact congrArg Prod.fst (S.dataU_raw _)
    rw [this]
    exact (contDiff_fst.comp hraw).contDiffAt
  unfold pairRay composedPairAt
  simp only [hj, dite_true]
  refine ContDiffAt.prodMk ?_ ?_
  · refine contDiffAt_pi.2 fun x => contDiffAt_pi.2 fun i => ?_
    exact (contDiff_composeField (G := levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) j hjk) (G' := stepG d L N₁ m₁ k ϱ) S.a x i).contDiffAt.comp q hpair
  · refine contDiffAt_pi.2 fun x => contDiffAt_pi.2 fun i => ?_
    have : (fun q : ℝ × S.E => (composedDataAt S.a S.ν hj (Nat.le_succ k)
        (S.dataU (S.psiAt q.1 q.2))).h x i) = fun _ => if x ∈ (levelGS (d := d) (L := L)
          (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j hjk).Ω 1 then (S.h₀ i : ℂ) else 0 := by
      funext q
      show (if x ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j hjk).Ω 1
        then (S.dataU (S.psiAt q.1 q.2)).h x i else 0) = _
      by_cases h : x ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
        j hjk).Ω 1
      · simp only [h, ite_true, S.dataU_h]
      · simp only [h, ite_false]
    rw [this]
    exact contDiffAt_const

end StepSetting

end Balaban.Fluctuation
