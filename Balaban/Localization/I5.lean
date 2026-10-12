/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5Local
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem I-5, background part (LOCALIZATION.md §4.4; P3 Prop. 4.3 at `λ = ∞`, `ψ' = 0`)

For `X ⊂ X₁ ⊂ Ω_{k+1}` and `𝓔(X; ·)` analytic on `Ξ^c_j(𝔹_j(X); C₀, ε₂)` with
`|𝓔| ≤ E e^{-(κ-1) d^{cov}_j(X)}`, the composite
`𝒯(Θ) = 𝓔(X; ψ(𝔹_j(X), 𝔹_k(X); ψ(𝔹_k(X), 𝔹_{k+1}; Θ)))` expands, for
`Θ ∈ Ξ^c_{k+1}(𝔹_{k+1}; 1, ε')`, as `∑_{Y ⊃ X₁} 𝓔(X, Y; Θ)` with terms analytic in `Θ`, depending
on `Θ` only through its restriction to the thickening `thickSet Y` of `Y`, and bounded by
`E e^{-κ₀ d^{cov}_j(X) - 2κ d̃^{cov}_{k+1}(Y)}` (`i5_background`).

The fluctuation variable `ψ'` (mode P of Theorem I-4a for `𝔹_k` with the cover of `𝔹_{k+1}`) is
not included: the landed Theorem I-4a is for a single generating set, see the handoff note.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix

section I5

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

/-- **Theorem I-5 (background part).**  See the module docstring. -/
theorem i5_background (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {E : RawData d L (N₁ * L ^ m₁) K N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃),
      ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X)) :
    ∃ Ev : Set (CTorus d L N₁ m₁ K) → RawData d L (N₁ * L ^ m₁) K N → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
        E (rawOf (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (composeData hB.hP (compWeight L a₁) (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D) D))
          (composeData hB.hP (compWeight L a₁) (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D)
            D))) =
        ∑ Y ∈ domains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps, ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps,
        agreeOn (thickSet Gp Y) u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps,
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν K 1 eps)) := by
  classical
  have hd : 3 ≤ d := hB.HBp.hd
  have hL : 3 ≤ L := hB.HBp.hL
  -- the analytic functions of Theorems I-4b and 7.2
  obtain ⟨F₁, hF₁an, hF₁⟩ := i4b_analytic hB.hS hB.Sp hB.HBp hB.hκ.le hB.hM
  obtain ⟨Fk, hFkan, hFk⟩ := theorem72_analytic (G := Gk) (a := compWeight L a₁) (ν := ν) hB.HBk
  set ι := ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) with hι
  set cc : ι → ℕ × CTorus d L N₁ m₁ K := fun i => i.1.1 with hcc
  have hc : ∀ i, cc i ∈ cubeIdx Gp := fun i => i.1.2
  have hcinj : Function.Injective cc := fun i i' h =>
    Subtype.ext (Subtype.ext h)
  have hdisj : ∀ i, Disjoint (Pset m₁ (cc i)) (X1 Gp m₀ j 𝒦X) := fun i => hX₁ ▸ i.2
  set F : RawData d L (N₁ * L ^ m₁) K N → (ι → ℂ) → ℂ := fun u s =>
    E (D2raw Gk Gj (compWeight L a₁) Fk (D1raw Gp Gk (compWeight L a₁) F₁
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, u))) with hF
  have hana := fan_analytic hB hF₁an hF₁ hFkan hFk hEan
  have hbd : ∀ u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν K 1 eps,
      ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ),
      ‖F u s‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X) := fun u hu s hs =>
    fan_bound hB hF₁ hFk hEbd hu hs
  have hloc := fan_local hB hcov hX₁ hconn hF₁ hFk E
  have hloc' : LocalityAEOn (Real.exp κ) (XiCRaw (N := N) Gp (compWeight L a₁) ν K 1 eps)
      (fun i : ι => Pset m₁ (cc i)) (compY cc (X1 Gp m₀ j 𝒦X))
      (fun C u u' => agreeOn (N := N) (thickSet Gp (compY cc (↑X₁f : Set (CTorus d L N₁ m₁ K)) C)) u u')
      F := by
    rw [← hX₁]; exact hloc
  have hrefl : ∀ C u, u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν K 1 eps →
      (fun C u u' => agreeOn (N := N) (thickSet Gp (compY cc (↑X₁f : Set (CTorus d L N₁ m₁ K)) C)) u u')
        C u u := fun C u _ => agreeOn_refl _ u
  have hlink : ∀ C u u', agreeOn (N := N) (thickSet Gp (Ysites Gp m₀ cc (X1 Gp m₀ j 𝒦X) C)) u u' →
      agreeOn (N := N) (thickSet Gp (compY cc (↑X₁f : Set (CTorus d L N₁ m₁ K)) C)) u u' := by
    intro C u u' h
    refine agreeOn_mono (thickSet_mono ?_) h
    rw [hX₁]
    exact compY_subset_Ysites hcov.hU hcov.hN hc _ C
  obtain ⟨hsum, hlocY, hbound, hanY⟩ := localization_expansion (c := cc) hcov hd hL hc hcinj hdisj
    hopt hκ₀ hκdec hκ h1 hlog hEb (AgY := fun Y u u' => agreeOn (N := N) (thickSet Gp Y) u u') hrefl hlink
    hana hbd hloc'
  refine ⟨evTerm cc Gp m₀ (X1 Gp m₀ j 𝒦X) F, fun D hD => ?_, hlocY, hbound, hanY⟩
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hB.hκ
  have hsum' := hsum (rawOf D) ⟨D, hD, rfl⟩
  rw [← hsum']
  symm
  show E (D2raw Gk Gj (compWeight L a₁) Fk (D1raw Gp Gk (compWeight L a₁) F₁
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) 1, rawOf D))) = _
  rw [extParams_one]
  obtain ⟨φ, α, hI, -, -, hD1, hD2, -⟩ := point_facts hB hF₁ hFk (s := fun _ => (1 : ℂ))
    (fun P => by simpa using hE1) (fun P hP hPn => rfl) hD
  have hφ := decBg_one_eq hB hD hI
  rw [hD1, hD2, hφ]

end I5

end Balaban.Localization
