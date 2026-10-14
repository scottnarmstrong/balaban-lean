/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCovWeighted
public import Balaban.Localization.SharpX0Distance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# I-4c (vi) on `X₀` for a sup-separated generating set and for the literal local generator

`I4c_close_sqrt_X0` bounds the matrix elements of `C^{1/2}(s) - C^{1/2}(1)` at the unit points of
`X₀` for the standing data `XData G …` (built on `DGSetting`) under `r₀ M₁ ≤ ϱ - 1`.  The chain
behind it (`decM_isUnit`, `vecM_decZ_sub_le`, `sum_w_sqrt_sub_le`, `I4c_close_sqrt_entry`, …) is
proved for the data `Dec2.XData (coverOf G) G …` of the cover form (the landed statements are its
instances through `XData.toCover`); here it is combined with the sharp `X₀` distance.

* `I4c_close_sqrt_X0_sup`: I-4c (vi) on `X₀` for the data `Dec2.XData (coverOf G) G …` of a
  sup-separated, cube-aligned `G`, under the target bound `T = ((r₀ - 4 d L³)/L) M₁ ≤ ϱ - 1` only;
* `localB_xCover`: the literal local generator `𝔹 = localB …` satisfies `Dec2.XCover (coverOf 𝔹) 𝔹`;
* `localB_I4c_close_sqrt_X0`: **the instance `𝔹 = localB …`** at the separation `ϱ = 5 L M₁` and
  the collar `r₀ = 4 d L³ + L`: the bound `B e^{-γ_x M₁}` (P3's `r₁ = 1`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Finset Matrix

section Sup

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}
  {α : G.Ω 1 → ℂ} {κ δ : ℝ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {Cx : ℝ}

/-- **Theorem I-4c (vi) on `X₀` for a sup-separated generating set** (cover form of
`I4c_close_sqrt_X0`).  For the data `Dec2.XData (coverOf G) G …` of a sup-separated, cube-aligned
`G` (`M₁ ≥ 4 L²`), the parameters equal to `1` off the parameter cubes of `X₁`, the physical
`r₀ M₁ ℓ(x)`-collar of `X₀ ∩ Ω₁` inside `X₁`, `4 d L³ ≤ r₀` and the target bound
`T = ((r₀ - 4 d L³)/L) M₁ ≤ ϱ - 1`, the matrix elements of `C^{1/2}(s) - C^{1/2}(1)` at the unit
points of `X₀` are at most `B e^{-γ_x T}`.  No `ℓ¹` cover separation and no `r₀ M₁ ≤ ϱ - 1`. -/
theorem I4c_close_sqrt_X0_sup (hG : CubeAligned G m₁) (hSS : SupSep G m₁)
    (hMM : 4 * L ^ 2 ≤ L ^ m₁) {s' : DecParams G}
    (hfam : ∀ x, 0 ≤ x → Dec2.XData (coverOf G) G a aT ν x α κ (extS G s') Cx)
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {X₀ X₁ : Finset (CTorus d L N₁ m₁ (k + 1))} {r₀ : ℝ}
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ cubeIdx G), P ∉ parCubes G X₁ →
      s' ⟨P, hP⟩ = 1)
    (hN : ∀ x ∈ X₀, x ∈ G.Ω 1 → ∀ y : CTorus d L N₁ m₁ (k + 1),
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y < r₀ * (L : ℝ) ^ m₁ * G.spacing x →
        y ∈ X₁)
    (hT : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤ ϱ - 1)
    (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀)
    {b b' : unitPts G} (hX : ∀ y, unitBlock y = b.1 → y ∈ X₀) (i i' : Fin N) :
    ‖(decCovSqrt G a aT ν α (extS G s') φ (unitQ G) (unitP G) -
        decCovSqrt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G)) (b, i) (b', i')‖ ≤
      covWSqrt d L (a k) κ (xAgmonRate d L) (2 * d) *
        Real.exp (-(xAgmonRate d L * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L))) := by
  have D0 := hfam 0 le_rfl
  exact I4c_close_sqrt_X0_of_dist hfam hφ hδ hsm hs1 hr₀
    (fun _ hy hyΩ => siteSetDist_X0_sup hG hSS D0.st.hL hMM D0.st.one_lt_rho.le hN hT hy hyΩ) hX
    i i'

end Sup

section LocalB

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L]

/-- **The standing data `XCover` of the cover of the literal local generator** `𝔹 = localB …`
(`localB_coverGeom`), for `k ≥ 1` and `1/2 ≤ a_T ≤ 2`. -/
theorem localB_xCover {ϱ : ℝ} {j : ℕ} (hj : j ≤ k + 1) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hsep : ϱ ≤ minSep L (L ^ m₁)) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁) {a : ℕ → ℝ}
    {aT ν : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν) (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights (k + 1) a)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1)) (hk : 1 ≤ k) (haT1 : 1 / 2 ≤ aT)
    (haT2 : aT ≤ 2) :
    Dec2.XCover (coverOf (SmallField.GsSpec.localB j hj Y hsep))
      (SmallField.GsSpec.localB j hj Y hsep) a aT ν (Cchi d L) where
  toCoverGeom := localB_coverGeom hj Y hsep hm₁ hM hd hL hν hνL ha hag
  hak1 := (ha k hk (by omega)).1
  hak2 := (ha k hk (by omega)).2
  haT1 := haT1
  haT2 := haT2

/-- **I-4c (vi) on `X₀` for the literal local generator** (P3 pp. 44, 57, 69).  For
`𝔹 = localB j hj Y …` at the separation `ϱ = 5 L M₁`, `L ≥ 3`, `M₁ = L^{m₁} ≥ 4 L²`, the collar
`r₀ = 4 d L³ + L` (the `(4 d L³ + L) M₁ ℓ(x)`-neighbourhood of `X₀ ∩ Ω₁` inside `X₁`), the
parameters equal to `1` off the parameter cubes of `X₁`, and the standing data of (DG7) of the
pair `(coverOf 𝔹, 𝔹)` (an admissible potential `α`, `M₁ ≥ c_* e^{N₀ κ}`, `|s_P| ≤ e^κ`), the
matrix elements of `C^{1/2}(s) - C^{1/2}(1)` at the unit points of `X₀` are at most
`B e^{-γ_x M₁}` (`r₁ = 1`). -/
theorem localB_I4c_close_sqrt_X0 {j : ℕ} (hj : j ≤ k + 1) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hM : 4 * L ^ 2 ≤ L ^ m₁) {a : ℕ → ℝ} {aT ν : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) (hk : 1 ≤ k)
    (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    {α : (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ}
    (hα : AdmPot (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁)))) α)
    {κ δ : ℝ} (hκ : 0 ≤ κ)
    (hbig : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s' : DecParams (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁))))}
    (hsb : ∀ P, ‖extS (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁)))) s' P‖ ≤
      Real.exp κ)
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    (hφ : IsConstraintField (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁)))) δ φ)
    (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {X₀ X₁ : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1))
      (hP : P ∈ cubeIdx (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁))))),
      P ∉ parCubes (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁)))) X₁ →
        s' ⟨P, hP⟩ = 1)
    (hN : ∀ x ∈ X₀, x ∈ (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁)))).Ω 1 →
      ∀ y : CTorus d L N₁ m₁ (k + 1), Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ *
          (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁)))).spacing x → y ∈ X₁)
    {b b' : unitPts (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁))))}
    (hX : ∀ y, unitBlock y = b.1 → y ∈ X₀) (i i' : Fin N) :
    ‖(decCovSqrt (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁)))) a aT ν α
          (extS (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁)))) s') φ
          (unitQ (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁)))))
          (unitP (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁))))) -
        decCovSqrt (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁)))) a aT ν α
          (fun _ => 1) φ (unitQ (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁)))))
          (unitP (SmallField.GsSpec.localB j hj Y (le_refl (minSep L (L ^ m₁))))))
        (b, i) (b', i')‖ ≤
      covWSqrt d L (a k) κ (xAgmonRate d L) (2 * d) *
        Real.exp (-(xAgmonRate d L * (L : ℝ) ^ m₁)) := by
  have hm₁ : 2 ≤ m₁ := by
    by_contra h
    push Not at h
    have hL2 : L ^ m₁ ≤ L ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  obtain ⟨hT1, hT2⟩ := target_le_minSep (d := d) (m₁ := m₁) (by omega : 1 ≤ L)
  have hS := localB_xCover hj Y le_rfl hm₁ hM hd hL hν hνL ha hag hk haT1 haT2
  have h := I4c_close_sqrt_X0_sup (localB_cubeAligned hj Y le_rfl hm₁) (localB_supSep hj Y le_rfl)
    hM (s' := s') (r₀ := 4 * d * (L : ℝ) ^ 3 + L) (b := b) (b' := b')
    (fun x hx => ⟨hS, Cchi_nonneg d L, hα, hx, hκ, hbig, hsb⟩) hφ hδ hsm hs1 hN
    (by rw [hT1]; exact hT2) (by linarith [show (0 : ℝ) ≤ L from by positivity]) hX i i'
  rwa [hT1] at h

end LocalB

end Balaban.Localization
