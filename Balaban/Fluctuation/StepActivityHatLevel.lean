/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepActivityHatGeneral
public import Balaban.Fluctuation.StepRegDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The old-term functionals on the whole-lattice sets are the old terms of the step

`StepActivityHatGeneral` identifies the step exponent of a general class with the hat expansion
under two named hypotheses, `OldEnergyHatMatch` and `OldObsHatMatch`: the old-term functionals of
the expansion, `flComp hB hF E`, must be the old terms of the class at the composed data of the
step.  The two sides are built differently.  The functional evaluates `E` at

`ψ(𝔹_j(X), 𝔹_k(X); ψ(𝔹_k(X), 𝔹_{k+1}; Θ) + δψ(𝔹_k(X), 𝔹_k; ψ'))`

with the complex solver of the generating set `𝔹_k(X)` of the functional (`flDatumOne`,
`composeData`), and the step evaluates the term at the pair `composedPairAt` of the whole-lattice
sets `levelGS j`, `𝔹_k = stepG`, with the solver of `𝔹_k` at the datum `dataU (ψ^{(k)} + ψ')`.

This file proves the two hypotheses when the generating sets of the functionals are the
whole-lattice sets, `𝔹_k(X) = 𝔹_k` and `𝔹_j(X) = levelGS j`, for an arbitrary class:

* `flDatumOne_stepG`: the datum of the functional is the datum of the step,
  `flDatumOne 𝔹_k … Θ (hatLift ψ̂) = dataUC (ψ^{(k)} + ψ'(ψ̂))` (the composition of `𝔹_k` with itself
  is the identity; same square root of the covariance, same shift);
* `hatFun_flComp_level`, `hatFun_flComp_level_real`: the functional at the physical point is `E` at
  the composed pair of the step (complex datum; real chart);
* `oldEnergyHatMatch_level`: `OldEnergyHatMatch` for the functionals
  `EE_j = β⁻¹ ℰ^{(j)}(·, ·)`, `1 ≤ j ≤ k` (one functional per scale, the whole density);
* `oldObsHatMatch_level`: `OldObsHatMatch` for the functionals
  `EM_{(j, x, i)} = ℳ^{(j)}(x; ·, ·, g)_i`;
* `Wone_eq_hat_level`: the first segment of the step exponent of an arbitrary class as the value
  of the hat expansion, with no named hypothesis.

So the step exponent identity holds for the landed objects, with the same datum, solver,
covariance and normalization (`β⁻¹` on the old energy functionals, none on the observable ones),
when the old-term functionals live on the whole-lattice sets.  No class hypothesis is used: the
identities are algebraic, on the real chart of `RayData`.

What is not proved: the two hypotheses for functionals on localized generating sets
`𝔹_k(X) ≠ 𝔹_k`.  There the solver of the functional is that of `𝔹_k(X)` and the comparison needs
the composition identity of the backgrounds on localized sets and the locality of the class terms;
it also depends on which generating sets the class terms use, on which nothing is assumed here
(`C.Tm.gs` does not appear).  The functionals of this file carry the whole density of a scale, so
their bounds are not uniform in the volume: this is a check of the value identity, not of the
smallness hypotheses of the activity bound.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Finset Matrix Set
  Filter Topology

section Level

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

namespace StepSetting

variable (S : StepSetting d L N₁ m₁ k N ϱ)

/-- **The datum of an old-term functional on the whole-lattice set `𝔹_k` is the datum of the
step**: `ψ(𝔹_k, 𝔹_{k+1}; Θ) + δψ(𝔹_k, 𝔹_k; ψ') = ψ^{(k)}(θ) + ψ'` with
`ψ' = hatLift (β_k^{-1/2}) θ ψ̂`, the lift of the substitution (2.7).  For every block datum. -/
theorem flDatumOne_stepG (ha : S.a k ≠ 0) (BG₂ κ : ℝ)
    (hP : Precedes (stepG d L N₁ m₁ k ϱ) S.G')
    (hPm : Precedes (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ)) (y : S.E)
    (hz : IsLayerConstant (stepG d L N₁ m₁ k ϱ)
      (hatLift S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.D' (yhat y))) :
    flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hP hPm S.a₁ S.ν S.D'
        (hatLift S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.D' (yhat y)) hz =
      S.dataUC (S.psiAtC 1 y) := by
  refine BgData.eq_of_raw (Prod.ext ?_ ?_)
  · funext x i
    have ht := congrFun (congrFun (S.compTangent_psiAtC 1 y) x) i
    simp only [compTangent] at ht
    rw [Complex.ofReal_one, one_smul] at ht
    have e : (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D').Ψ x i =
        composeField (stepG d L N₁ m₁ k ϱ) S.G' S.a (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
          S.D'.Ψ x i := rfl
    rw [e] at ht
    show (flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hP hPm S.a₁ S.ν S.D' _ hz).Ψ x i =
      (S.dataUC (S.psiAtC 1 y)).Ψ x i
    unfold flDatumOne
    rw [flDatum_Ψ, composeField_self S.hG S.a ha]
    linear_combination -ht
  · funext x i
    show (flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hP hPm S.a₁ S.ν S.D' _ hz).h x i =
      (S.dataUC (S.psiAtC 1 y)).h x i
    rw [S.dataUC_h]
    unfold flDatumOne
    rw [flDatum_h]
    show (if x ∈ (stepG d L N₁ m₁ k ϱ).Ω 1 then S.D'.h x i else 0) = _
    rw [ite_eq_left (S.hG x).1, S.hh₀]

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **An old-term functional on the whole-lattice sets, at the physical point, is the old term at
the composed pair of the complex step**: for `𝔹_k(X) = 𝔹_k`, `𝔹_j(X) = levelGS j`, `j ≤ k`,
`hatFun … (flComp hB hF E) (Θ, ψ̂) = E (ψ_k^{(j)}, h)` at the datum `dataUC (ψ^{(k)} + ψ'(ψ̂))`, with
the complex solver of `𝔹_k`.  For every block datum of `Ξ^c(𝔹_{k+1}; 1, ε)`. -/
theorem hatFun_flComp_level {j : ℕ} (hjk : j ≤ k) {r₀ δ₃ δfl : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N S.G' (stepG d L N₁ m₁ k ϱ)
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j
        (hjk.trans (Nat.le_succ k))) S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hF : FlSetting N S.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx
      c₂ BG₂ δ₁ δfl X₁f)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (y : S.E) :
    hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (flComp hB hF E)
        (rawOf S.D', S.hatC y) =
      E (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC 1 y))) := by
  have ha : S.a k ≠ 0 :=
    (compWeight_pos (by have := hB.HBp.hL; omega) hB.ha₁ S.hk1).ne'
  have hz : IsLayerConstant (stepG d L N₁ m₁ k ϱ)
      (hatLift S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.D' (yhat y)) :=
    isLayerConstant_hatLift S.hG S.hG' _ S.D' _
  show hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (flComp hB hF E)
    (rawOf S.D', yhat y) = _
  rw [hatFun_rawOf S.hG' _ _ hD, flComp_rawOf hB hF E hD hz,
    S.flDatumOne_stepG ha BG₂ κ hB.hP hF.hPm y hz]
  unfold composedPairAtC
  simp only [hjk, ↓reduceDIte]
  rfl

/-- **The same on the real chart**: under `RayData`, for `‖ψ̂‖ < p⁺`, the functional at the
physical point is `E` at the pair `(ψ_k^{(j)}, h)` of the landed real step,
`composedPairAt … (dataU (ψ^{(k)} + ψ'))`: same datum, same solver. -/
theorem hatFun_flComp_level_real {pp : ℝ} (R0 : S.RayData pp) {j : ℕ} (hjk : j ≤ k)
    {r₀ δ₃ δfl : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N S.G' (stepG d L N₁ m₁ k ϱ)
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j
        (hjk.trans (Nat.le_succ k))) S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hF : FlSetting N S.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx
      c₂ BG₂ δ₁ δfl X₁f)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) {y : S.E} (hy : ‖y‖ < pp) :
    hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (flComp hB hF E)
        (rawOf S.D', S.hatC y) =
      E (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU (S.psiAt 1 y))) := by
  have hχ := (chiU_eq_one_iff _ _ _ _).1 R0.hχu
  have hdom : InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L N) S.ν (S.dataU (S.psiAt 1 y)) :=
    R0.dom (q := (1, y)) (by simpa using hy)
  rw [S.hatFun_flComp_level hjk hB hF hD E y,
    S.psiAtC_eq R0.ha₁ R0.H R0.hδ'0 R0.hδ' R0.hD'R R0.hδ0 hχ R0.hfam R0.hsm, S.dataUC_yhat,
    composedPairAtC_eq_of_bg (theorem72_real R0.H hdom).1 j]

/-- The path at the fluctuation variable `0` is the background. -/
theorem psiAt_zero_right (s : ℝ) : S.psiAt s (0 : S.E) = S.psi0 := by
  unfold psiAt shiftU
  simp

/-- The hat variable of the fluctuation variable `0`. -/
theorem hatC_zero : S.hatC (0 : S.E) = 0 := by
  funext q
  simp [StepSetting.hatC]

variable {pp : ℝ} (C : StepClass d L N₁ m₁ k N ϱ) (R0 : S.RayData pp) (hlt : S.p₁ < pp)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (hp₁ : 0 < S.p₁)

include R0 hlt hD hp₁ in
/-- **`OldEnergyHatMatch` for the whole-lattice functionals of an arbitrary class.**  One
functional per scale `1 ≤ j ≤ k`, on the generating sets `𝔹_k(X) = 𝔹_k`, `𝔹_j(X) = levelGS j`, with
`EE_j(Ψ, h) = β⁻¹ ℰ^{(j)}(Ψ, h)` (the density of the scale `j`, divided by the outer factor `β` of
the expansion): on the support of `ν_{p₁}`,
`β ∑_j (F_j(ψ̂) - F_j(0)) = δℰ_k(ψ')`.  No class hypothesis is used. -/
theorem oldEnergyHatMatch_level {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : {j // j ∈ Finset.Icc 1 k} → Finset (CTorus d L N₁ m₁ (k + 1))}
    {jE : {j // j ∈ Finset.Icc 1 k} → ℕ}
    (hBE : ∀ τ ∈ (Finset.Icc 1 k).attach, BgSetting N S.G' (stepG d L N₁ m₁ k ϱ)
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) τ.1
        ((Finset.mem_Icc.1 τ.2).2.trans (Nat.le_succ k))) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ)
      (jE τ))
    (hFE : ∀ τ ∈ (Finset.Icc 1 k).attach, FlSetting N S.G' (stepG d L N₁ m₁ k ϱ)
      (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ)) :
    OldEnergyHatMatch S C (Finset.Icc 1 k).attach hBE hFE
      (fun τ raw => (S.β : ℂ)⁻¹ * Edens C.m₀ C.Tm τ.1 raw.1 raw.2) := by
  intro x hx
  have hβ : (S.β : ℂ) ≠ 0 := by exact_mod_cast R0.hβ.ne'
  have hxn : ‖x‖ < pp := ((chiFl_eq_one_iff hp₁ x).1 hx).trans hlt
  have h0n : ‖(0 : S.E)‖ < pp := by simpa using R0.hpp
  have hterm : ∀ (τ : {j // j ∈ Finset.Icc 1 k}) (hτ : τ ∈ (Finset.Icc 1 k).attach),
      (if h : τ ∈ (Finset.Icc 1 k).attach then
        hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (flComp (hBE τ h) (hFE τ h)
              (fun raw => (S.β : ℂ)⁻¹ * Edens C.m₀ C.Tm τ.1 raw.1 raw.2)) (rawOf S.D', S.hatC x) -
          hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (flComp (hBE τ h) (hFE τ h)
              (fun raw => (S.β : ℂ)⁻¹ * Edens C.m₀ C.Tm τ.1 raw.1 raw.2)) (rawOf S.D', 0)
        else 0) =
      (S.β : ℂ)⁻¹ * (Edens C.m₀ C.Tm τ.1
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1 (S.dataU (S.psiAt 1 x))).1
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1 (S.dataU (S.psiAt 1 x))).2 -
        Edens C.m₀ C.Tm τ.1
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1 (S.dataU S.psi0)).1
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1 (S.dataU S.psi0)).2) := by
    intro τ hτ
    rw [dite_eq_left hτ, ← S.hatC_zero,
      S.hatFun_flComp_level_real R0 (Finset.mem_Icc.1 τ.2).2 (hBE τ hτ) (hFE τ hτ) hD _ hxn,
      S.hatFun_flComp_level_real R0 (Finset.mem_Icc.1 τ.2).2 (hBE τ hτ) (hFE τ hτ) hD _ h0n,
      S.psiAt_zero_right]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← mul_assoc, mul_inv_cancel₀ hβ, one_mul,
    Finset.sum_attach (Finset.Icc 1 k) (fun j => Edens C.m₀ C.Tm j
      (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU (S.psiAt 1 x))).1
      (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU (S.psiAt 1 x))).2 -
      Edens C.m₀ C.Tm j
        (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU S.psi0)).1
        (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU S.psi0)).2),
    Finset.sum_sub_distrib]
  rfl

include R0 hlt hD hp₁ in
/-- **`OldObsHatMatch` for the whole-lattice functionals of an arbitrary class**, for a source
`g`.  One functional per scale `1 ≤ j ≤ k`, site `x` and component `i`, on the generating sets
`𝔹_k(X) = 𝔹_k`, `𝔹_j(X) = levelGS j`, with `EM_{(j,x,i)}(Ψ, h) = ℳ^{(j)}(x; Ψ, h, g)_i` (no factor
`β`: the source factor `g/β` and the outer factor `β` of the expansion cancel): on the support of
`ν_{p₁}`, the sum of the functionals is the old observable increment.  No class hypothesis is
used. -/
theorem oldObsHatMatch_level (g : Fld d L N₁ m₁ (k + 1) N) {r₀ δ₃ δfl : ℝ}
    {X₀M X₁M : {j // j ∈ Finset.Icc 1 k} × CTorus d L N₁ m₁ (k + 1) × Fin N →
      Finset (CTorus d L N₁ m₁ (k + 1))}
    {jM : {j // j ∈ Finset.Icc 1 k} × CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    (hBM : ∀ τ ∈ (Finset.Icc 1 k).attach ×ˢ
        ((Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))) ×ˢ (Finset.univ : Finset (Fin N))),
      BgSetting N S.G' (stepG d L N₁ m₁ k ϱ)
        (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) τ.1.1
          ((Finset.mem_Icc.1 τ.1.2).2.trans (Nat.le_succ k))) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀M τ)
        (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ (Finset.Icc 1 k).attach ×ˢ
        ((Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))) ×ˢ (Finset.univ : Finset (Fin N))),
      FlSetting N S.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂
        BG₂ δ₁ δfl (X₁M τ)) :
    OldObsHatMatch S C g ((Finset.Icc 1 k).attach ×ˢ
        ((Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))) ×ˢ (Finset.univ : Finset (Fin N))))
      (fun τ => τ.2.1) (fun τ => τ.2.2) hBM hFM
      (fun τ raw => Mloc C.m₀ C.Tm τ.1.1 τ.2.1 raw.1 raw.2 g τ.2.2) := by
  intro x hx
  have hβ : (S.β : ℂ) ≠ 0 := by exact_mod_cast R0.hβ.ne'
  have hxn : ‖x‖ < pp := ((chiFl_eq_one_iff hp₁ x).1 hx).trans hlt
  have h0n : ‖(0 : S.E)‖ < pp := by simpa using R0.hpp
  have hterm : ∀ (τ : {j // j ∈ Finset.Icc 1 k} × CTorus d L N₁ m₁ (k + 1) × Fin N)
      (hτ : τ ∈ (Finset.Icc 1 k).attach ×ˢ
        ((Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))) ×ˢ (Finset.univ : Finset (Fin N)))),
      (if h : τ ∈ (Finset.Icc 1 k).attach ×ˢ
          ((Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))) ×ˢ (Finset.univ : Finset (Fin N)))
        then (g τ.2.1 τ.2.2 / (S.β : ℂ)) *
          (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (flComp (hBM τ h) (hFM τ h)
                (fun raw => Mloc C.m₀ C.Tm τ.1.1 τ.2.1 raw.1 raw.2 g τ.2.2))
              (rawOf S.D', S.hatC x) -
            hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (flComp (hBM τ h) (hFM τ h)
                (fun raw => Mloc C.m₀ C.Tm τ.1.1 τ.2.1 raw.1 raw.2 g τ.2.2)) (rawOf S.D', 0))
        else 0) =
      (S.β : ℂ)⁻¹ * (g τ.2.1 τ.2.2 * Mloc C.m₀ C.Tm τ.1.1 τ.2.1
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1.1 (S.dataU (S.psiAt 1 x))).1
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1.1 (S.dataU (S.psiAt 1 x))).2 g τ.2.2 -
        g τ.2.1 τ.2.2 * Mloc C.m₀ C.Tm τ.1.1 τ.2.1
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1.1 (S.dataU S.psi0)).1
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1.1 (S.dataU S.psi0)).2 g τ.2.2) := by
    intro τ hτ
    rw [dite_eq_left hτ, ← S.hatC_zero,
      S.hatFun_flComp_level_real R0 (Finset.mem_Icc.1 τ.1.2).2 (hBM τ hτ) (hFM τ hτ) hD _ hxn,
      S.hatFun_flComp_level_real R0 (Finset.mem_Icc.1 τ.1.2).2 (hBM τ hτ) (hFM τ hτ) hD _ h0n,
      S.psiAt_zero_right]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← mul_assoc, mul_inv_cancel₀ hβ, one_mul,
    S.dF_sub_dF_zeroClass C g (S.psiAt 1 x), ← Finset.sum_sub_distrib, Finset.sum_product,
    Finset.sum_attach (Finset.Icc 1 k) (fun j => ∑ p ∈ (Finset.univ : Finset
        (CTorus d L N₁ m₁ (k + 1))) ×ˢ (Finset.univ : Finset (Fin N)),
      (g p.1 p.2 * Mloc C.m₀ C.Tm j p.1
          (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU (S.psiAt 1 x))).1
          (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU (S.psiAt 1 x))).2 g p.2 -
        g p.1 p.2 * Mloc C.m₀ C.Tm j p.1
          (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU S.psi0)).1
          (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU S.psi0)).2 g p.2))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_product]
  unfold Floc
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_sub_distrib]

variable {δc : ℝ}
  (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
  (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
  (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
    c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
  (hpc : S.p₁ < cψ)
  (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)

include R0 hlt hD hp₁ hC hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hcψ hpc hδ₁ in
/-- **The first segment of the step exponent of an arbitrary class, with the whole-lattice
old-energy functionals.**  With one functional `β⁻¹ ℰ^{(j)}` per scale `1 ≤ j ≤ k` on the sets
`𝔹_k`, `levelGS j`, analytic on its chart, for `s ∈ [0,1]` on the support of `ν_{p₁}`,

`s² · ((-β) · raySrc3 (hatFun … (interactionOne …)) (1-t)²/2 ψ̂ ψ̂ s Θ)
  + β ∑_j dirTermSrc (hatFun … (flComp … (β⁻¹ ℰ^{(j)}))) 1 ψ̂ ψ̂ s Θ = W₁(s, ψ̂)`.

No named hypothesis remains (`Wone_eq_hat_of_oldEnergyHatMatch` with `oldEnergyHatMatch_level`). -/
theorem Wone_eq_hat_level {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : {j // j ∈ Finset.Icc 1 k} → Finset (CTorus d L N₁ m₁ (k + 1))}
    {jE : {j // j ∈ Finset.Icc 1 k} → ℕ}
    (hBE : ∀ τ ∈ (Finset.Icc 1 k).attach, BgSetting N S.G' (stepG d L N₁ m₁ k ϱ)
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) τ.1
        ((Finset.mem_Icc.1 τ.2).2.trans (Nat.le_succ k))) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ)
      (jE τ))
    (hFE : ∀ τ ∈ (Finset.Icc 1 k).attach, FlSetting N S.G' (stepG d L N₁ m₁ k ϱ)
      (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hEanE : ∀ τ ∈ (Finset.Icc 1 k).attach, AnalyticOnNhd ℂ
      (fun raw : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
        (S.β : ℂ)⁻¹ * Edens C.m₀ C.Tm τ.1 raw.1 raw.2)
      (XiCRaw (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) τ.1
        ((Finset.mem_Icc.1 τ.2).2.trans (Nat.le_succ k))) (compWeight L S.a₁) S.ν (jE τ)
        (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x : S.E} (hx : chiFl S.U N S.p₁ x = 1) :
    (s : ℂ) ^ 2 * ((-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)) taylorWeight (S.hatC x)
        (S.hatC x) (s : ℂ) (rawOf S.D')) +
      (S.β : ℂ) * ∑ τ ∈ (Finset.Icc 1 k).attach, (if h : τ ∈ (Finset.Icc 1 k).attach then
        dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (flComp (hBE τ h) (hFE τ h)
            (fun raw => (S.β : ℂ)⁻¹ * Edens C.m₀ C.Tm τ.1 raw.1 raw.2)))
          (fun _ => (1 : ℂ)) (S.hatC x) (S.hatC x) (s : ℂ) (rawOf S.D') else 0) =
      S.Wone C s x :=
  S.Wone_eq_hat_of_oldEnergyHatMatch (C := C) (hC := hC) (R0 := R0) (hlt := hlt) (hD := hD)
    (hc7 := hc7) (hR := hR) (hsmR := hsmR) (hRs := hRs) (hsmall := hsmall) (hnum := hnum)
    (hnum' := hnum') (hMX := hMX) (hdm := hdm) (hα := hα) (hsm := hsm) (hp₁ := hp₁) (hcψ := hcψ)
    (hpc := hpc) (hδ₁ := hδ₁) (𝒯E := (Finset.Icc 1 k).attach) (hBE := hBE) (hFE := hFE)
    (hEanE := hEanE) (hmatchE := S.oldEnergyHatMatch_level C R0 hlt hD hp₁ hBE hFE) hs hx

end StepSetting

end Level

end Balaban.Fluctuation
