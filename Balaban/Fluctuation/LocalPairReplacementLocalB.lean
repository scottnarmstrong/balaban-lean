/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairDepth

/-!
# The replacement identity at the local generating set

P3 pp. 78-79 replaces `𝔹_{k+1}` by `𝔹_{k+1}(Y)` in every term of (4.45).  Here this is the
coefficient equality of Lemma AE between the ambient term (decoupled background field of
`(coverOf 𝔹_{k+1}, 𝔹_{k+1})`, decoupled fluctuation field of `(coverOf 𝔹_{k+1}, 𝔹_k)`, parameters
`σ w = extParams 𝔹_{k+1} X₁ w`) and the term recomputed on the local pairs `(𝔹_{k+1}(Y), 𝔹_k(Y))`,
`𝔹_{k+1}(Y) = localB (k + 1) … Y`, `𝔹_k(Y) = localB k … Ω_k(𝔹_{k+1}(Y))`, with the transported
parameters `τ w` (`σ w` at the cubes of `𝔹_{k+1}(Y)` with base in the top layer, `0` at the others)
and the same fluctuation `ψ'(w)` (the hat variable stays ambient).

* `coef_eTermFun_replacement_localB`: the coefficient equality, from
  `coef_eTermFun_replacement_cross`, with the component hypotheses discharged by the depth lemmas of
  `LocalPairDepth.lean` (margin `2 M₁ L^{k+1}` between the read region `R` and the complement of the
  top layer) and the four cover bases by `localB_replacement_coverBases`.  The remaining hypotheses
  are the constants, the specifications of the solution maps `F₁, F₁', Sol, Sol'`, the data domains
  of `D`, `D'`, the agreement of `D'` with `D` on the top layer, and the strict data inequalities of
  the two fluctuation problems.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset
  Balaban.LargeField Balaban.SmallField.GsSpec Balaban.Fluctuation

section Assembly

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm ϱ₁ ϱ₂ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {a : ℕ → ℝ} {ν : ℝ}

/-- **The replacement identity at the local generating set (P3 pp. 78-79).**  Let `𝔹_{k+1}`, `𝔹_k`
be level sets (`k ≥ 1`), `𝔹_{k+1}(Y) = localB (k + 1) … Y` and `𝔹_k(Y) = localB k … Ω_k(𝔹_{k+1}(Y))`
(index `5 L M₁`), and let `𝒞` be a family of cubes of the cover of `𝔹_{k+1}` disjoint from `X₁`.
Let `R` be a set of sites containing the cubes of `𝒞`, the cubes meeting `X₁` and the data sites of
the term generator `𝔹_k(X)`, with the margin: every site within sup-distance `2 M₁ L^{k+1}` of `R`
lies in `Ω_{k+1}(𝔹_{k+1}(Y))` (its `𝒞_{k+1}`-cube lies in `Y`).  With one pair of constants
`(mixedKc d L, Cchi d L)`, the maps `F₁, F₁'` (decoupled background fields) and `Sol, Sol'`
(decoupled fluctuation fields) of the ambient and the local pairs, a datum `D` and a datum `D'` of
`𝔹_{k+1}(Y)` in the union domains that agrees with `D` on the top layer, and a fluctuation `ψ'(w)` with
the strict data inequalities on both sides for `w` in the polydisc of radius `1 < R' ≤ e^κ`
supported on `𝒞`: the coefficient `coef (·) 𝒞` of Lemma AE of the old term with parameters
`σ w = extParams 𝔹_{k+1} X₁ w` equals that of the term recomputed on `(𝔹_{k+1}(Y), 𝔹_k(Y))` with the
transported parameters `τ w`. -/
theorem coef_eTermFun_replacement_localB (hG' : IsLevel Gp (k + 1)) (hG : IsLevel Hm k)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ k + 1) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {c BG : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ a ν) (HB' : BgHyp d L (k + 1) (minSep L (L ^ m₁)) a ν)
    {κ : ℝ} (hκ : 0 ≤ κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gp) Gp a ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
          (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) a ν (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N →
      ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm a ν p.1) p.2.2.1 p.2.1
          (pertSource Hm a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm a ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm a ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm a p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (Dec2.decG (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) a ν p.1)
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) a p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) a ν p.1 false
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) a p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ,
          Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) a ν p.1 false
            p.2.2.1 p.2.1
            (pertSource (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) a p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (C : Finset (ParIdx Gp X₁)) {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
    {D : BgData Gp N} {D' : BgData (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) N}
    (hDd : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D)
    (hDd' : InUnionDomainC (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
      (c7 d L N BG κ) ν D')
    (hD' : ∀ x ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1),
      D'.Ψ x = D.Ψ x ∧ D'.h x = D.h x)
    (ψ' : (ParIdx Gp X₁ → ℂ) → CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (he : ∀ w ∈ supN C R', StrictDataM Hm N false δ₀ δ₁
      (flEdat Gp Hm (F₁ (extParams Gp X₁ w, rawOf D)) D.Ψ (ψ' w)))
    (he' : ∀ w ∈ supN C R', StrictDataM (localB k (Nat.le_succ k)
        (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
          Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁
      (flEdat (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))
        (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D'))
        D'.Ψ (ψ' w)))
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    (hRk : ∀ x ∈ dataSites Gk, x ∈ R)
    (hmar : ∀ x ∈ R, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) →
      y ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)) :
    coef (fun w => eTermFun Gp Gk Gj Hm ac Fk E (F₁ (extParams Gp X₁ w, rawOf D))
        (Sol (extParams Gp X₁ w,
          flEdat Gp Hm (F₁ (extParams Gp X₁ w, rawOf D)) D.Ψ (ψ' w))).1 (rawOf D, ψ' w)) C =
      coef (fun w => eTermFun (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) Gk Gj
        (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
        ac Fk E
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D'))
        (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0),
          flEdat (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
            (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω
                (k + 1) then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D'))
            D'.Ψ (ψ' w))).1 (rawOf D', ψ' w)) C := by
  classical
  -- the cover bases with one pair of constants
  obtain ⟨Sb, Sb', Sf, Sf'⟩ := localB_replacement_coverBases hG' Hm hk Y hN hm₁ hM HB hag hagm hagl
  -- the sets `T = R` and `Y₀ = {y : d(R, y) ≤ M₁ L^{k+1}}`
  set Y₀ : Finset (CTorus d L N₁ m₁ (k + 1)) :=
    Finset.univ.filter (fun y => ∃ x ∈ R, supDist x y ≤ L ^ (k + 1 + m₁)) with hY₀
  have hRY : ∀ x ∈ R, ∀ y, supDist x y ≤ L ^ (k + 1 + m₁) → y ∈ Y₀ := fun x hx y h =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, x, hx, h⟩
  have hYR : ∀ y ∈ Y₀, ∃ x ∈ R, supDist x y ≤ L ^ (k + 1 + m₁) := fun y hy =>
    (Finset.mem_filter.1 hy).2
  have hRY₀ : ∀ x ∈ R, x ∈ Y₀ := fun x hx => hRY x hx x (by rw [supDist_self]; exact Nat.zero_le _)
  have hM2 : 2 ≤ L ^ m₁ := by
    have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    nlinarith [Nat.one_le_pow 2 L hL1]
  have htop : ∀ y ∈ Y₀, y ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) :=
    fun y hy => localB_top_of_mem hk Y _ hmar hYR hy
  -- layers on the top layer
  have hstb := fun y (hy : y ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)) =>
    level_localB_layer_iff_of_top hG' hk Y (le_refl (minSep L (L ^ m₁))) hy
  have hstf := fun y (hy : y ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)) =>
    localB_drop_layer_iff_of_top (Hm := Hm) hG hk1 hk (Nat.le_succ k) Y
      (le_refl (minSep L (L ^ m₁))) (le_refl (minSep L (L ^ m₁))) hy
  have hHb : ∀ x, x ∈ Gp.Ω 1 := fun x => (hG' x).1
  have hHf : ∀ x, x ∈ Hm.Ω 1 := fun x => (hG x).1
  have hH'b : ∀ x ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k,
      x ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 := fun x hx =>
    (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω_antitone le_rfl hk1 (by omega) hx
  have hH'f := fun x (hx : x ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) =>
    localB_drop_Ω_one_of_mem hk1 hk (Nat.le_succ k) Y (le_refl (minSep L (L ^ m₁)))
      (le_refl (minSep L (L ^ m₁))) hx
  -- the transported parameters
  have hs'0 := fun w : ParIdx Gp X₁ → ℂ =>
    localB_tau_off_top hk Y (le_refl (minSep L (L ^ m₁))) (extParams Gp X₁ w)
  have hsτ := fun w : ParIdx Gp X₁ → ℂ =>
    localB_tau_top hG' hk Y (le_refl (minSep L (L ^ m₁))) (extParams Gp X₁ w)
  have hhat := fun w : ParIdx Gp X₁ → ℂ =>
    localB_hat_of_active (Gp := Gp) hk1 hk Y (le_refl (minSep L (L ^ m₁))) hm₁ hM (hs'0 w)
  have hsσ : ∀ w ∈ supN C R', ∀ P, ‖extParams Gp X₁ w P‖ < Real.exp κ := fun w hw P =>
    (norm_extParams_lt hR' hw.2 P).trans_le hRκ
  -- the background and fluctuation components
  have hdichb := fun w (hw : w ∈ supN C R') => localB_depth_dich hG' hm₁ hRC hRX Gp hw.1
  have hdichf := fun w (hw : w ∈ supN C R') => localB_depth_dich hG' hm₁ hRC hRX Hm hw.1
  have hrow := fun w (hw : w ∈ supN C R') => localB_depth_row hG' hm₁ hRC hRX Y₀ hw.1
  refine coef_eTermFun_replacement_cross hS Sb Sb' HB HB' hκ hMc hF₁ hF₁' hF₂ Sf Sf' hM₂ h0 h1
    hδ₀ hδ₁ hSol hSol' ac Fk E C hR' (extParams Gp X₁)
    (fun w P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
      then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0)
    hsσ (fun w hw => localB_tau_norm_lt hk Y _ (hsσ w hw) (hR'.trans_le hRκ))
    hDd hDd' ψ' he he' hRY₀ (fun y hy => hstb y (htop y hy)) hdichb
    (fun w hw => level_localB_dich_cross hG' hk1 hk Y _ hHb hH'b (hs'0 w) (hhat w) (hsτ w)
      (hdichb w hw))
    hrow
    (fun w hw => level_localB_row_cross hG' hk1 hk Y _ (hs'0 w) (hhat w) (hsτ w) (hrow w hw))
    (fun w hw => level_localB_inner_cross hG' hk Y _ hHb
      (localB_depth_deep hG' hm₁ hk Y _ hRC hRX hmar hstb hw.1) (hsτ w))
    (fun w _ => level_localB_inner_cross' hG' hk1 hk Y _ hH'b (hs'0 w) (hhat w) (hsτ w))
    (localB_depth_res_bg hG' hRY) (localB_depth_act hG' hM2 hk Y _ hmar hYR)
    (fun y hy _ z hz => by
      have ht := localB_depth_approxDep (Gp := Gp) hM2 hk Y _ hmar hYR y hy z hz
      exact ⟨(hD' z ht).1.symm, (hD' z ht).2.symm⟩)
    (fun y hy => (hD' y (htop y hy)).1.symm)
    hRY₀ (fun _ hx => hx)
    (fun x hx => iff_of_true (hHf x) (hH'f x
      ((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω_antitone hk1 (Nat.le_succ k)
        (by omega) (htop x hx))))
    hdichf
    (fun w hw => level_localB_dich_cross hG' hk1 hk Y _ hHf hH'f (hs'0 w) (hhat w) (hsτ w)
      (hdichf w hw))
    hrow
    (fun w hw => level_localB_row_cross hG' hk1 hk Y _ (hs'0 w) (hhat w) (hsτ w) (hrow w hw))
    (fun w hw => level_localB_inner_cross hG' hk Y _ hHf
      (localB_depth_deep hG' hm₁ hk Y _ hRC hRX hmar hstf hw.1) (hsτ w))
    (fun w _ => level_localB_inner_cross' hG' hk1 hk Y _ hH'f (hs'0 w) (hhat w) (hsτ w))
    (localB_depth_res_fl hk Y _ hmar hRY hYR hstf)
    (localB_depth_compose hk Y _ hmar hRY hstb hRk)
    (localB_depth_compose hk Y _ hmar hRY hstf hRk)
    (fun x hx => by
      have ht := hmar x (hRk x hx) x (by rw [supDist_self]; exact Nat.zero_le _)
      exact ⟨(hD' x ht).1.symm, fun _ => (hD' x ht).2.symm⟩)

end Assembly

end Balaban.Localization
