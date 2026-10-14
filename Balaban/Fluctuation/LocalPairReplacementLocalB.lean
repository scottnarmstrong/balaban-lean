/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairDepth
public import Balaban.Fluctuation.FlCoreCover
public import Balaban.SmallField.LocalGeneratorRestriction

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
  the two fluctuation problems;
* `localB_inUnionDomainC_restrict_const`, `localBRestrict_eq_of_mem_top`, `strictDataM_mono_left`,
  `strictDataM_flEdat_cover`: the data of the local side (the restricted datum, the strict data
  inequalities of both fluctuation problems);
* `coef_eTermFun_replacement_localB_restrict`: the case `𝔹_{k+1} = levelGS (k + 1)`,
  `D' = localBRestrict D`, with the data hypotheses discharged from the chart of `D`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset
  Balaban.LargeField Balaban.SmallField.GsSpec Balaban.Fluctuation

section Data

/-! ### The data of the local side (deliverable (3)) -/

section Restrict

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  {j : ℕ} {hj : j ≤ K} {X : Set (CTorus d L N₁ m₁ K)} {hsep : ϱ ≤ minSep L (L ^ m₁)}

/-- **The restricted datum lies in the local union domain** (any constants `c₀, c₁`): the clip
`localBRestrict` of a datum of the union domain of the whole-level set `𝔹_j` lies in the union domain
of `𝔹_j(X) = localB j … X` with the same constants (`localB_inDomainC_restrict`).  The landed
`localB_inUnionDomainC_restrict` is the case `(bgC0, bgC1)`; the replacement uses `c₁ = c₇`. -/
theorem localB_inUnionDomainC_restrict_const (hj1 : 1 ≤ j) {c₀ c₁ μ : ℝ} (hμ : 0 ≤ μ)
    (D : BgData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ') j hj) N)
    (hD : InUnionDomainC _ c₀ c₁ μ D) :
    InUnionDomainC (localB j hj X hsep) c₀ c₁ μ (localBRestrict (X := X) (hsep := hsep) hj1 D) := by
  obtain ⟨δ, ε, hδ, hδε, hε, hδc, hμε, hDC⟩ := hD
  exact ⟨δ, ε, hδ, hδε, hε, hδc, hμε, localB_inDomainC_restrict hj1 hμ D hDC⟩

/-- **The restricted datum agrees with the datum on the top layer** `Ω_j(𝔹_j(X))` (both fields). -/
theorem localBRestrict_eq_of_mem_top (hj1 : 1 ≤ j)
    (D : BgData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ') j hj) N)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ (localB j hj X hsep).Ω j) :
    (localBRestrict (X := X) (hsep := hsep) hj1 D).Ψ x = D.Ψ x ∧
      (localBRestrict (X := X) (hsep := hsep) hj1 D).h x = D.h x := by
  have hx1 : x ∈ (localB j hj X hsep).Ω 1 :=
    (localB j hj X hsep).Ω_antitone le_rfl hj1 (by omega) hx
  exact ⟨localBRestrict_Ψ hj1 D ((mem_dataSites _).2 (Or.inl hx1)), localBRestrict_h hj1 D hx1⟩

end Restrict

section Strict

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν Kc Cx : ℝ}

/-- The strict data inequalities (mode P) are monotone in `δ₀`. -/
theorem strictDataM_mono_left {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {δ₀ δ₀' δ₁ : ℝ}
    (h : δ₀ ≤ δ₀') {p : Edat G N} (hp : StrictDataM G N false δ₀ δ₁ p) :
    StrictDataM G N false δ₀' δ₁ p := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, -⟩ := hp
  refine ⟨⟨fun x μ => ?_, fun x => ?_, h3, fun x => (h4 x).trans_le h, h5, h6⟩,
    fun h => absurd h (by simp)⟩
  · have hs := spacing_pos' G (x : CTorus d L N₁ m₁ K)
    exact ⟨(h1 x μ).1.trans_le (div_le_div_of_nonneg_right h hs.le),
      (h1 x μ).2.trans_le (div_le_div_of_nonneg_right h hs.le)⟩
  · have hs := spacing_pos' G (x : CTorus d L N₁ m₁ K)
    exact (h2 x).trans_le (div_le_div_of_nonneg_right h (by positivity))

/-- **The strict data inequalities of the fluctuation problem, for a cover pair** (from
`point_facts_core_cover`): for the cover base of `(coverOf 𝔹, 𝔹)`, a datum of the chart
`Ξ^c_K(𝔹; 1, ε')`, parameters `|s_P| < e^κ` and a fluctuation `ψ'` of the ball `|ψ'| < δ₁` on the
data sites of `H⁻ ≺ 𝔹`, the fluctuation data `flEdat 𝔹 H⁻ (F₁(s, Θ)) Ψ ψ'` satisfy `StrictDataM` at
every `δ₀ ≥ 2 K₄ C₁ ε'`.  Applied to the ambient pair and to the local pair
`(𝔹_{k+1}(Y), 𝔹_k(Y))` this gives the hypotheses `he`, `he'` of the replacement. -/
theorem strictDataM_flEdat_cover {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L K ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2) {δ₀ δ₁ BG₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hδ₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤ δ₀) (hPmp : Precedes Hm Gp)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {s : Dec2.DecParams (coverOf Gp)} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D)
    {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ} (hψ : ψ' ∈ FlBall Hm δ₁) :
    StrictDataM Hm N false δ₀ δ₁ (flEdat Gp Hm (F₁ (s, rawOf D)) D.Ψ ψ') := by
  classical
  obtain ⟨φ, α, δφ, δα, -, hF, hstr, -, -⟩ := point_facts_core_cover hS S HBp hκ hM heps hsmall
    hc7 hphi (BG₂ := BG₂) hδ₁ hPmp hF₁ (Sol := Sol)
    (fun p hp hp2 => hSol p hp (strictDataM_mono_left hδ₀ hp2))
    (X₁f := ∅) hs (fun P hP hnot => absurd (Finset.mem_filter.2 ⟨hP, fun h =>
      Finset.notMem_empty _ (h (mem_cubeP.2 (SameCell.refl _ _)))⟩) hnot) hD hψ
  rw [hF]
  exact strictDataM_mono_left hδ₀ hstr

end Strict

end Data

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

/-- **The replacement identity at the local generating set, with the restricted datum.**  The case
`𝔹_{k+1} = levelGS (k + 1)` (the whole-level set of the class) and `D' = localBRestrict D` (the clip of
the datum to the data sites of `𝔹_{k+1}(Y)`, P3 (4.44)) of `coef_eTermFun_replacement_localB`: the
data hypotheses are discharged from the chart `Ξ^c_{k+1}(𝔹_{k+1}; 1, ε')` of `D`
(`localB_inUnionDomainC_restrict_const`, `localBRestrict_eq_of_mem_top`, `localB_xiCData_restrict`
at the radius `ε'' ≥ C₁ε' + (2K₁ + 1) C₁ε'`, and `strictDataM_flEdat_cover` on both sides for a
fluctuation `ψ'(w)` in the ball `|ψ'| < δ₁` of the ambient level set `𝔹_k`).  The hypotheses left are
the constants (numerical conditions at `ε'` and `ε''`, `δ₀ ≥ 2 K₄ C₁ ε''`), the specifications of
the solution maps, and the margin of the read region in `Y`. -/
theorem coef_eTermFun_replacement_localB_restrict (hG : IsLevel Hm k) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ k + 1) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (HB' : BgHyp d L (k + 1) (minSep L (L ^ m₁))
      (compWeight L a₁) ν)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 ×
        Fin N → ℂ) × ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
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
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
          (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (rho4 d L N BG κ)
            s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
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
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1)
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν p.1
                false
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
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
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1 false
            p.2.2.1 p.2.1
            (pertSource (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
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
    {D : BgData (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) N} (hD : XiCData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
      (compWeight L a₁) ν (k + 1) 1 eps D)
    (ψ' : (ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ → ℂ) → CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (hψ : ∀ w ∈ supN C R', ψ' w ∈ FlBall Hm δ₁)
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk), ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    (hRk : ∀ x ∈ dataSites Gk, x ∈ R)
    (hmar : ∀ x ∈ R, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) →
      y ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)) :
    coef (fun w => eTermFun (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) Gk Gj Hm ac Fk E (F₁ (extParams
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
      rawOf D))
        (Sol (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
          flEdat (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk) Hm (F₁ (extParams
            (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
            X₁ w, rawOf D)) D.Ψ (ψ' w))).1 (rawOf D, ψ' w)) C =
      coef (fun w => eTermFun (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) Gk Gj
        (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
        ac Fk E
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), rawOf
              (localBRestrict (X := Y) (hsep := le_refl (minSep L (L ^ m₁)))
              (Nat.le_add_left 1 k) D)))
        (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0),
          flEdat (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
            (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω
                (k + 1) then Dec2.extS (coverOf
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), rawOf
                  (localBRestrict (X := Y) (hsep := le_refl (minSep L (L ^ m₁)))
                  (Nat.le_add_left 1 k) D)))
            (localBRestrict (X := Y) (hsep := le_refl (minSep L (L ^ m₁)))
              (Nat.le_add_left 1 k) D).Ψ (ψ' w))).1 (rawOf
              (localBRestrict (X := Y) (hsep := le_refl (minSep L (L ^ m₁)))
              (Nat.le_add_left 1 k) D), ψ' w)) C := by
  classical
  have hG' : IsLevel (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) hk) (k + 1) := isLevel_levelGS (Nat.le_add_left 1 k) hk
  obtain ⟨Sb, Sb', -, -⟩ := localB_replacement_coverBases hG' Hm hk Y hN hm₁ hM HB hag hagm hagl
  have hd0 : 0 < d := by have := HB.hd; omega
  have hxi := one_le_xiC1 d
  have hK1 : 0 < bgK1 d L N := bgK1_pos d L N
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have heps' : 0 < eps' := by nlinarith
  have hle : eps ≤ eps' := by nlinarith
  have hK4 : 0 ≤ K4 d L N BG κ := (K4_pos hS.fam.2.1 hd0).le
  have hδ₀a : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤ δ₀ := by
    have : K4 d L N BG κ * (xiC1 d * eps) ≤ K4 d L N BG κ * (xiC1 d * eps') :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (by linarith)) hK4
    linarith
  have hDom := xiCData_inDomainC HB hsmall hD
  have hc1 : xiC1 d * eps ≤ bgC1 d L N := hc7.trans (c7_le_bgC1 d L N BG κ)
  have hc0 : xiC1 d * eps ≤ bgC0 d L N := hc1.trans (bgC1_le_bgC0 d L N hd0)
  have hDd := inUnionDomainC_of_inDomainC HB hδ0 hc0 hc7 hDom
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := HB.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hD'x := localB_xiCData_restrict (X := Y) (hsep := le_refl (minSep L (L ^ m₁)))
    (Nat.le_add_left 1 k) HB' HB.mass hδ0 le_rfl hc0 hc1 hνε hεb D hDom
  have hsσ : ∀ w ∈ supN C R', ∀ P, ‖extParams _ X₁ w P‖ < Real.exp κ := fun w hw P =>
    (norm_extParams_lt hR' hw.2 P).trans_le hRκ
  exact coef_eTermFun_replacement_localB hG' hG hk1 hk Y hN hm₁ hM hag hagm hagl hS HB HB' hκ.le
    hMc hF₁ hF₁' hF₂ hM₂ h0 h1.le hδ₀ hδ₁ hSol hSol' ac Fk E C hR' hRκ hDd
    (localB_inUnionDomainC_restrict_const (Nat.le_add_left 1 k) HB.mass D hDd)
    (fun x hx => localBRestrict_eq_of_mem_top (Nat.le_add_left 1 k) D hx) ψ'
    (fun w hw => strictDataM_flEdat_cover hS Sb HB hκ hMc heps hsmall hc7 hphi h1 hδ₀a
      (isLevel_top_precedes hG' Hm) hF₁ hSol (hsσ w hw) hD (hψ w hw))
    (fun w hw => strictDataM_flEdat_cover hS Sb' HB' hκ hMc heps' hsmall' hc7' hphi' h1 hδ₀e
      (localB_drop_precedes hk (Nat.le_succ k) Y le_rfl le_rfl) hF₁' hSol'
      (localB_tau_norm_lt hk Y _ (hsσ w hw) (hR'.trans_le hRκ)) hD'x
      (fun x _ => hψ w hw x ((mem_dataSites Hm).2 (Or.inl (hG x).1))))
    hRC hRX hRk hmar

end Assembly

end Balaban.Localization
