/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairReplacementHat
public import Balaban.Fluctuation.LocalClassChart

/-!
# The replacement identity at the local generating set as an identity of functions of the datum

P3 pp. 78-79 recomputes every term of (4.45) on `𝔹_{k+1}(Y)` and uses that the recomputed term
equals the term of the whole-level expansion.  `coef_eTermFun_replacement_localB_hat` gives this
equality of the Lemma AE coefficients for one datum `D` of the chart, with the local term evaluated
at the restricted datum `localBRestrict D`.  Here it is restated as an identity of functions of the
raw datum on the whole chart and on the class domain:

* `rawOf_localBRestrict`: the raw datum of the restricted datum is the cut-off `clipRaw 𝔹_j(X)` of
  the raw datum;
* `clipRaw_levelGS`, `clipRaw_localB_clipRaw_levelGS`: the cut-off of a whole-level set is the
  identity on pairs of fields, and the cut-off of `𝔹_j(X)` absorbs it;
* `coef_eTermFun_replacement_localB_hat_raw`: for every raw datum `Θ` of the chart
  `Ξ^c(𝔹_{k+1}; 1, ε)` and every hat variable `ψ̂` of the box `|ψ̂| ≤ c_ψ`, the coefficient of the
  term of the whole level at `(Θ, ψ̂)` equals the coefficient of the term recomputed on
  `(𝔹_{k+1}(Y⁺), 𝔹_k(Y⁺))` at the cut-off `clipRaw 𝔹_{k+1}(Y⁺) Θ` and the restriction of `ψ̂`;
* `evTerm_eTermFun_replacement_localB_hat`: the same for the term `𝓔(X, Y)` of the polymer `Y`, the
  sum of the coefficients over the connected families `𝒞` with `Y[𝒞] = Y`, as functions of
  `(Θ, ψ̂)` on the chart times the box (the read region of every such `𝒞` lies in `Y`);
* `evTerm_eTermFun_replacement_localB_hat_xiDom`: on the class domain `Ξ^c_{k+1}(𝔹_{k+1}; 1, ε)`
  the term of the whole level read at a pair of fields `q` equals the term recomputed on
  `𝔹_{k+1}(Y⁺)` read at the cut-off `clipRaw 𝔹_{k+1}(Y⁺) q`, the reading of the local terms of
  `localB_eTermHat_evTerm_xiFieldDom`.

The old term enters only through the functional `E` (and its generating sets `𝔹_k(X)`, `𝔹_j(X)`,
the set `X₁` of the expansion); every statement holds for each label `(j, y, X)` of the class.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset
  Balaban.LargeField Balaban.SmallField.GsSpec Balaban.SmallField.Def6 Balaban.Fluctuation Matrix

section Restrict

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  {j : ℕ} {hj : j ≤ K} {X : Set (CTorus d L N₁ m₁ K)} {hsep : ϱ ≤ minSep L (L ^ m₁)}

/-- **The raw datum of the restricted datum is the cut-off of the raw datum** to the data sites of
`𝔹_j(X) = localB j … X` (resp. to `Ω₁(𝔹_j(X))` for the external field). -/
theorem rawOf_localBRestrict (hj1 : 1 ≤ j)
    (D : BgData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ') j hj) N) :
    rawOf (localBRestrict (X := X) (hsep := hsep) hj1 D) =
      clipRaw (localB j hj X hsep) (rawOf D) := by
  classical
  refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_)
  · by_cases hx : x ∈ dataSites (localB j hj X hsep) <;>
      simp [clipRaw, rawOf, localBRestrict, BgData.clip, hx]
  · by_cases hx : x ∈ (localB j hj X hsep).Ω 1 <;>
      simp [clipRaw, rawOf, localBRestrict, BgData.clip, hx]

/-- **The cut-off of a whole-level set is the identity**: every site lies in `Ω₁(𝔹_j)`, `j ≥ 1`. -/
theorem clipRaw_levelGS (hj1 : 1 ≤ j) (q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) :
    clipRaw (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ') j hj) q =
      q := by
  classical
  have hΩ : ∀ x, x ∈ (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ')
      j hj).Ω 1 := fun x => by simp [Def6.levelGS, hj1]
  refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_)
  · have hx : x ∈ dataSites (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
        (ϱ := ϱ') j hj) := (mem_dataSites _).2 (Or.inl (hΩ x))
    simp [clipRaw, hx]
  · simp [clipRaw, hΩ x]

/-- **The cut-off of `𝔹_j(X)` absorbs the cut-off of the whole level `𝔹_j`.** -/
theorem clipRaw_localB_clipRaw_levelGS (hj1 : 1 ≤ j)
    (q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) :
    clipRaw (localB j hj X hsep)
        (clipRaw (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ') j hj)
          q) =
      clipRaw (localB j hj X hsep) q := by
  rw [clipRaw_levelGS hj1]

end Restrict

section Assembly

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm ϱ₁ ϱ₂ : ℝ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {ν : ℝ}

/-- **The replacement identity as an identity of functions of the raw datum** (P3 pp. 78-79,
(4.46)).  The hypotheses of `coef_eTermFun_replacement_localB_hat` with the datum `D` replaced by a
raw datum `Θ` of the chart `Ξ^c(𝔹_{k+1}; 1, ε)`: the coefficient `coef (·) 𝒞` of Lemma AE of the
term of the whole level at `(Θ, ψ̂)` equals that of the term recomputed on
`(𝔹_{k+1}(Y⁺), 𝔹_k(Y⁺))` at the cut-off `clipRaw 𝔹_{k+1}(Y⁺) Θ` (the raw datum of the restricted
datum, `rawOf_localBRestrict`) and the restriction of `ψ̂` to the unit lattice of `𝔹_{k+1}(Y⁺)`. -/
theorem coef_eTermFun_replacement_localB_hat_raw (hG : IsLevel Hm k) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ k + 1) (Y Yp : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (HB' : BgHyp d L (k + 1) (minSep L (L ^ m₁))
      (compWeight L a₁) ν)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 ×
        Fin N → ℂ) × ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk))) (D : BgData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ :
        (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1
        × Fin N → ℂ)
        (α : (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ), Dec2.IsDecBg (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
          (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N →
      ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (Dec2.decG (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1)
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν p.1
                false
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ,
          Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1 false
            p.2.2.1 p.2.1
            (pertSource (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                  p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (C : Finset (ParIdx
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁))
      {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
    {eps eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hεb : xiC1 d * eps + (2 * bgK1 d L N + 1) * (xiC1 d * eps) ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (hΘ : Θ ∈ XiCRaw
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
      (compWeight L a₁) ν (k + 1) 1 eps)
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁c : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (ψh : unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) hk) × Fin N → ℂ) (hψh : ∀ p, ‖ψh p‖ ≤ cψ)
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk), ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    (hRk : ∀ x ∈ dataSites Gk, x ∈ R)
    (hRY : ∀ x ∈ R, x ∈ Y) :
    coef (fun w => eTermFun (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) Gk Gj Hm ac Fk E (F₁ (extParams
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
      Θ))
        (Sol (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
          flEdat (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk) Hm (F₁ (extParams
            (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
            X₁ w, Θ)) Θ.1
            (hatPsiF (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc
              F₁
              (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) (Θ) ψh))).1
        (Θ, (hatPsiF (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                (k := k + 1) (ϱ := ϱ) (k + 1) hk) a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc
              F₁
                (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) (Θ) ψh))) C =
      coef (fun w => eTermFun (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj
        (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
        ac Fk E
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ))
        (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0),
          flEdat (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
            (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                (k + 1) then Dec2.extS (coverOf
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ))
            (clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ).1
            (fun x i => if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ)).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ).1
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ)).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then ψh (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0))).1
        (clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ,
            (fun x i => if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ)).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ).1
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ)).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then ψh (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0))) C := by
  obtain ⟨D, hD, rfl⟩ := hΘ
  rw [← rawOf_localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
    (Nat.le_add_left 1 k) D]
  exact coef_eTermFun_replacement_localB_hat hG hk1 hk Y Yp hYp hN hm₁ hM hag hagm hagl hS HB
    HB' ha₁ ha₂ hκ hMc hMX hF₁ hF₁' hF₂ hM₂ h0 h1 hδ₀ hδ₁ hSol hSol' ac Fk E C hR' hRκ heps hsmall
    hc7 hphi hεb hsmall' hc7' hphi' hδ₀e hD hmarD' hαD' hsm cc hcψ hδ₁c ψh hψh hRC hRX hRk hRY

/-- **The term `𝓔(X, Y)` of the polymer `Y`, recomputed on `𝔹_{k+1}(Y⁺)`, as a function of the
datum** (P3 pp. 78-79).  For the connected families `𝒞` of the expansion of the whole level with
`Y[𝒞] = Y` the read region of `coef_eTermFun_replacement_localB_hat` may be taken to be `Y` itself
(the cubes of `𝒞` lie in `Y[𝒞]`, `Pset_subset_Dsites`; the cubes meeting `X₁` and the data sites of
`𝔹_k(X)` lie in `Y` by hypothesis).  Hence the term of the whole level, `∑_{Y[𝒞] = Y} coef (·) 𝒞`
at `(Θ, ψ̂)`, equals the term recomputed on `(𝔹_{k+1}(Y⁺), 𝔹_k(Y⁺))` at the cut-off
`clipRaw 𝔹_{k+1}(Y⁺) Θ` and `ψ̂`, at every point of the chart times the box. -/
theorem evTerm_eTermFun_replacement_localB_hat (hG : IsLevel Hm k) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ k + 1) (Y Yp : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (HB' : BgHyp d L (k + 1) (minSep L (L ^ m₁))
      (compWeight L a₁) ν)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 ×
        Fin N → ℂ) × ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk))) (D : BgData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ :
        (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1
        × Fin N → ℂ)
        (α : (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ), Dec2.IsDecBg (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
          (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N →
      ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (Dec2.decG (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1)
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν p.1
                false
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ,
          Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1 false
            p.2.2.1 p.2.1
            (pertSource (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                  p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
    {eps eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hεb : xiC1 d * eps + (2 * bgK1 d L N + 1) * (xiC1 d * eps) ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀)
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁c : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {m₀ : ℕ} (hU : LayerUnion (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
      (ϱ := ϱ) (k + 1) hk) m₀) (hNm : L ^ m₀ ∣ N₁)
    (hXY : ∀ P ∈ cubeIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk), ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ Y)
    (hkY : ∀ x ∈ dataSites Gk, x ∈ Y) :
    ∀ u ∈ XiCRaw (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
      (compWeight L a₁) ν (k + 1) 1 eps ×ˢ {ψh : unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) × Fin N → ℂ |
        ∀ p, ‖ψh p‖ ≤ cψ},
    evTerm (fun i : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ => i.1.1)
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) m₀ X₁
      (fun (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) × Fin N → ℂ))
        (w : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ → ℂ) =>
      eTermFun (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) Gk Gj Hm ac Fk E (F₁ (extParams
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
      u.1))
        (Sol (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
          flEdat (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk) Hm (F₁ (extParams
            (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
            X₁ w, u.1)) u.1.1
            (hatPsiF (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc
              F₁
              (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) u.1 u.2))).1
        (u.1, (hatPsiF (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                (k := k + 1) (ϱ := ϱ) (k + 1) hk) a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc
              F₁
                (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) u.1 u.2))) Y u =
    evTerm (fun i : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ => i.1.1)
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) m₀ X₁
      (fun (v : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) × Fin N → ℂ))
        (w : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ → ℂ) =>
      eTermFun (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj
        (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
        ac Fk E
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1))
        (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0),
          flEdat (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
            (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                (k + 1) then Dec2.extS (coverOf
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1))
            (v.1).1
            (fun x i => if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1)).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (v.1).1
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1)).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then v.2 (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0))).1
        (v.1,
            (fun x i => if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1)).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (v.1).1
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1)).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then v.2 (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0)))
      Y (clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) u.1, u.2) := by
  classical
  rintro ⟨Θ, ψh⟩ ⟨hΘ, hψh⟩
  unfold evTerm
  refine Finset.sum_congr rfl fun C hC => ?_
  have hY := ((mem_connFams _).1 hC).2
  exact coef_eTermFun_replacement_localB_hat_raw hG hk1 hk Y Yp hYp hN hm₁ hM hag hagm hagl hS HB
    HB' ha₁ ha₂ hκ hMc hMX hF₁ hF₁' hF₂ hM₂ h0 h1 hδ₀ hδ₁ hSol hSol' ac Fk E C hR' hRκ heps hsmall
    hc7 hphi hεb hsmall' hc7' hphi' hδ₀e Θ hΘ hmarD' hαD' hsm cc hcψ hδ₁c ψh hψh
    (R := Finset.univ.filter (· ∈ Y))
    (fun i hi y hy => by
      rw [Finset.mem_filter, ← hY]
      exact ⟨Finset.mem_univ _,
        Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, Pset_subset_Dsites hU hNm i.1.2 hy⟩)⟩)
    (fun P hP hdis y hy => Finset.mem_filter.2 ⟨Finset.mem_univ _, hXY P hP hdis y hy⟩)
    (fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, hkY x hx⟩)
    (fun x hx => (Finset.mem_filter.1 hx).2)

/-- **The replacement identity on the class domain** (the per-label input of `hrepl`).  At a pair
of fields `q` of the class domain `Ξ^c_{k+1}(𝔹_{k+1}; 1, ε)`, `ε ≤ eps`, the term of the polymer `Y`
of the whole level read at `q` (the cut-off of the whole level is the identity, `clipRaw_levelGS`)
equals the term recomputed on `(𝔹_{k+1}(Y⁺), 𝔹_k(Y⁺))` read at the cut-off
`clipRaw 𝔹_{k+1}(Y⁺) q`, for every hat variable of the box. -/
theorem evTerm_eTermFun_replacement_localB_hat_xiDom (hG : IsLevel Hm k) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ k + 1) (Y Yp : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (HB' : BgHyp d L (k + 1) (minSep L (L ^ m₁))
      (compWeight L a₁) ν)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 ×
        Fin N → ℂ) × ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk))) (D : BgData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ :
        (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1
        × Fin N → ℂ)
        (α : (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ), Dec2.IsDecBg (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
          (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N →
      ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (Dec2.decG (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1)
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν p.1
                false
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ,
          Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1 false
            p.2.2.1 p.2.1
            (pertSource (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                  p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
    {eps eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hεb : xiC1 d * eps + (2 * bgK1 d L N + 1) * (xiC1 d * eps) ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀)
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁c : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {m₀ : ℕ} (hU : LayerUnion (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
      (ϱ := ϱ) (k + 1) hk) m₀) (hNm : L ^ m₀ ∣ N₁)
    (hXY : ∀ P ∈ cubeIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk), ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ Y)
    (hkY : ∀ x ∈ dataSites Gk, x ∈ Y)
    {ε : ℝ} (hε : ε ≤ eps) (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hq : XiDom (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
      (compWeight L a₁) ν (k + 1) ε q.1 q.2)
    (ψh : unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) × Fin N → ℂ) (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    evTerm (fun i : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ => i.1.1)
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) m₀ X₁
      (fun (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) × Fin N → ℂ))
        (w : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ → ℂ) =>
      eTermFun (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) Gk Gj Hm ac Fk E (F₁ (extParams
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
      u.1))
        (Sol (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
          flEdat (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk) Hm (F₁ (extParams
            (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
            X₁ w, u.1)) u.1.1
            (hatPsiF (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc
              F₁
              (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) u.1 u.2))).1
        (u.1, (hatPsiF (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                (k := k + 1) (ϱ := ϱ) (k + 1) hk) a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc
              F₁
                (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) u.1 u.2))) Y (q, ψh) =
    evTerm (fun i : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ => i.1.1)
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) m₀ X₁
      (fun (v : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) × Fin N → ℂ))
        (w : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ → ℂ) =>
      eTermFun (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj
        (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
        ac Fk E
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1))
        (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0),
          flEdat (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
            (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                (k + 1) then Dec2.extS (coverOf
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1))
            (v.1).1
            (fun x i => if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1)).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (v.1).1
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1)).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then v.2 (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0))).1
        (v.1,
            (fun x i => if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1)).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (v.1).1
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1)).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then v.2 (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0)))
      Y (clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) q, ψh) := by
  have hq' := clipRaw_mem_xiCRaw_of_xiDom
    (G := Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
    hε hq
  rw [clipRaw_levelGS (Nat.le_add_left 1 k)] at hq'
  exact evTerm_eTermFun_replacement_localB_hat hG hk1 hk Y Yp hYp hN hm₁ hM hag hagm hagl hS HB
    HB' ha₁ ha₂ hκ hMc hMX hF₁ hF₁' hF₂ hM₂ h0 h1 hδ₀ hδ₁ hSol hSol' ac Fk E hR' hRκ heps hsmall
    hc7 hphi hεb hsmall' hc7' hphi' hδ₀e hmarD' hαD' hsm cc hcψ hδ₁c hU hNm hXY hkY (q, ψh)
    ⟨hq', hψh⟩

end Assembly

end Balaban.Localization
