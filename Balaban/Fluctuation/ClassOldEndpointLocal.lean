/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldMarksY
public import Balaban.Fluctuation.StepActivityHatFlRay
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The endpoint identity of an inherited label with a localized ambient generator

For an inherited label `(j, y, X)` the functional `flComp` of the decoupled expansion evaluates the
term at `ψ(𝔹_j(X), 𝔹_k(X); ψ(𝔹_k(X), 𝔹_{k+1}; θ) + δψ(𝔹_k(X), 𝔹_k; ψ'))`, with the background of
the ambient set `Gk = 𝔹_k(X)` recomputed on `Gk`.  For a localized `Gk` this is the term at the
composed pair of the step, with the background of the whole set `𝔹_k`: P3 (4.16) (printed p. 71),
an exact identity, which rests on

* the fluctuation identity `φ_k(ψ^{(k)} + ψ') = φ_{k+1}| + δφ(ψ')`
  (`exact_fluct_eq_flFieldOne`; here `fluct_of_tangent` at an arbitrary tangent of the ball), by
  which the datum of `Gk` is `ψ(𝔹_k(X), 𝔹_k; ψ^{(k)} + ψ')` (`flDatum_eq_composeData_of_fluct`);
* Theorem 7.3, the composition formula P3 (4.9): the background of `Gk` at the datum composed from
  the background of `𝔹_k` is the restriction of that background (`bgFieldC_compose`);
* the composition identity for `𝔹_j(X) ≺ 𝔹_k(X) ≺ 𝔹_k` (`composeData_composeData`), and the
  agreement on `X` of the compositions from `𝔹_j(X)` and from the whole level `j`
  (`composeData_agree_on_X`).

Results:

* `flCompLocal_agree_on_X`: on `X` the composed datum of `flComp` is the composed pair of the step;
* `classOldEndpointLocal_liftC`, `classOldEndpointLocalM_liftC`: the endpoint identities at the
  lifted tangent `liftC v` of a complex field `v` of the unit lattice with `liftC v` in the ball of
  fluctuations;
* `classOldEndpointLocal_complex`: the same at the physical point `hatC z` of the hat expansion;
* `classOldEndpointLocal_marked`: the identity along the masked decoupled tangent, the hypothesis
  `hend` of `deriv_eq_sum_of_expansion` (for the marks of W748's `classOldMarksY_expansion`).

The ambient set `Gk` is arbitrary (at its own separation index) subject to the settings `hB`, `hF`,
with the fluctuation set the whole level `𝔹_k = stepG`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Finset

section Fluct

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The fluctuation identity at an arbitrary tangent of the ball** (Lemma 2.3 (d) and
Theorem I-4a at `s = 1`; `bgFieldC_sub_eq_flFieldOne_hatLift` for a general tangent).  For a datum
`D'` of `Ξ^c(𝔹_{k+1}; 1, ε)` and a datum `D` of level `k` with the same `h̃` whose tangent
`D.Ψ - ψ^{(k)}(D')` is a block field `ψ'` of the ball `FlBallLC Hm δ₁`: `D` lies in the domain `𝒟`
of the small solution and `φ_k(D) - φ_{k+1}(D')| = δφ(ψ')`. -/
theorem fluct_of_tangent (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (ha₁ : 0 < a₁)
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {D' : BgData Gp N} (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    {D : BgData Hm N} (hh : ∀ x i, D.h x i = D'.h x i)
    {ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hψ : ψ' ∈ FlBallLC Hm δ₁)
    (ht : compTangent hG hG' (le_refl (k + 1)) (compWeight L a₁)
      (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = ψ') :
    InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν D ∧
      bgFieldC Hm (compWeight L a₁) ν (bgC0 d L N) D -
          (hG.precedes hG' (le_refl (k + 1))).restrictφ
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') =
        flFieldOne Gp Hm BG₂ κ a₁ ν D' ψ' := by
  obtain ⟨D₀, hDh, hDt, hDdisc⟩ := hreal_level hC hG hG' (le_refl (k + 1)) ha₁ H hc7
    (R := R) (by linarith) hsmR D' hD' ψ' hψ.1 hψ.2
  have hDeq : D₀ = D := by
    refine BgData.eq_of_raw (Prod.ext ?_ ?_)
    · funext z i
      have h1 := congrFun (congrFun hDt z) i
      have h2 := congrFun (congrFun ht z) i
      simp only [compTangent] at h1 h2
      show D₀.Ψ z i = D.Ψ z i
      linear_combination h1 - h2
    · funext z i
      show D₀.h z i = D.h z i
      rw [hDh z i, hh z i]
  subst hDeq
  have hhB : D₀.h = (composeData (hG.precedes hG' (le_refl (k + 1))) (compWeight L a₁)
      (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').h := by
    funext z i
    rw [hDh z i]
    show D'.h z i = (if z ∈ Hm.Ω 1 then D'.h z i else 0 : ℂ)
    simp [(hG z).1]
  have h1 := hDdisc 1 (by rw [norm_one]; linarith)
  rw [lineAt_tangent D₀ _ hhB] at h1
  refine ⟨h1, ?_⟩
  have := exact_fluct_eq_flFieldOne hC hG hG' (le_refl (k + 1)) ha₁ H D' hD' hc7 D₀ hDh
    (by rw [hDt]; exact hψ.1) hR hDdisc hRs hsmall hnum hnum'
  rw [this, hDt]

end Fluct

section Algebra

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}

/-- **The datum of the ambient set is a composition from the level `k`** (P3 (4.16), second
equality, with (4.17)).  If the datum `Dk` of `Hm` is `ψ(Hm, Gp; φ, D) + ψ'` on all sites with
the field of `D` on `Ω₁(Gk)`, then the datum `flDatum` of `Gk`,
`ψ(Gk, Gp; φ, D) + δψ(Gk, Hm; δφ, ψ')`, is the composition `ψ(Gk, Hm; φ| + δφ, Dk)`. -/
theorem flDatum_eq_composeData_of_fluct (hP : Precedes Gk Gp) (hPm : Precedes Gk Hm)
    (hHp : Precedes Hm Gp) {a : ℕ → ℝ} (ha : ∀ j, 1 ≤ j → j ≤ K → a j ≠ 0)
    (φ : Gp.Ω 1 × Fin N → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ) (D : BgData Gp N)
    (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ) (hψ' : IsLayerConstant Hm ψ') (Dk : BgData Hm N)
    (hΨ : ∀ x i, Dk.Ψ x i = composeField Hm Gp a φ D.Ψ x i + ψ' x i)
    (hh : ∀ x ∈ Gk.Ω 1, ∀ i, Dk.h x i = D.h x i) :
    flDatum Gk hP hPm a φ δφ D ψ' hψ' = composeData hPm a (hHp.restrictφ φ + δφ) Dk := by
  classical
  refine BgData.eq_of_raw (Prod.ext ?_ ?_)
  · funext x i
    show (flDatum Gk hP hPm a φ δφ D ψ' hψ').Ψ x i = composeField Gk Hm a (hHp.restrictφ φ + δφ)
      Dk.Ψ x i
    have eDk : Dk.Ψ = fun y j => composeField Hm Gp a φ D.Ψ y j + ψ' y j :=
      funext fun y => funext fun j => hΨ y j
    rw [flDatum_Ψ, eDk, composeField_add a (fun y j => composeField Hm Gp a φ D.Ψ y j) ψ'
      (hHp.restrictφ φ) δφ x i, composeField_trans hPm hHp ha φ D.Ψ x i]
  · funext x i
    show (flDatum Gk hP hPm a φ δφ D ψ' hψ').h x i =
      (composeData hPm a (hHp.restrictφ φ + δφ) Dk).h x i
    rw [flDatum_h]
    show (if x ∈ Gk.Ω 1 then D.h x i else 0) = (if x ∈ Gk.Ω 1 then Dk.h x i else 0)
    by_cases hx : x ∈ Gk.Ω 1
    · simp only [hx, ↓reduceIte, hh x hx i]
    · simp only [hx, ↓reduceIte]

/-- **Composing twice is composing once**, for `Gj ≺ Gk ≺ Hm` (`composeField_trans` on the spin
datum; the field datum is restricted twice). -/
theorem composeData_composeData (hq : Precedes Gj Gk) (hPm : Precedes Gk Hm)
    (hjm : Precedes Gj Hm) {a : ℕ → ℝ} (ha : ∀ j, 1 ≤ j → j ≤ K → a j ≠ 0)
    (Φ : Hm.Ω 1 × Fin N → ℂ) (Dk : BgData Hm N) :
    composeData hq a (hPm.restrictφ Φ) (composeData hPm a Φ Dk) = composeData hjm a Φ Dk := by
  classical
  refine BgData.eq_of_raw (Prod.ext ?_ ?_)
  · funext x i
    exact composeField_trans hq hPm ha Φ Dk.Ψ x i
  · funext x i
    show (if x ∈ Gj.Ω 1 then (if x ∈ Gk.Ω 1 then Dk.h x i else 0) else 0) =
      (if x ∈ Gj.Ω 1 then Dk.h x i else 0)
    by_cases hx : x ∈ Gj.Ω 1
    · simp only [hx, hq.mem_Ω1 hx, ↓reduceIte]
    · simp only [hx, ↓reduceIte]

end Algebra

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ : ℝ}

namespace StepSetting

variable (S : StepSetting d L N₁ m₁ k N ϱ)

/-- **On `X` the composed datum of `flComp` is the composed pair of the step** (P3 (4.16)).  For a
term generator `Gj` with the strong specification for `X`, a localized ambient set `Gk` (any
separation index) with the settings `hB`, `hF` (fluctuation set `𝔹_k = stepG`) and a complex field
`v` of the unit lattice with `liftC v` in the ball of fluctuations: at every site of `X`, the datum
`ψ(Gj, Gk; ψ(Gk, 𝔹_{k+1}; θ) + δψ(Gk, 𝔹_k; liftC v))` evaluated by `flComp` (background recomputed
on `Gk`) has the spin and field of `composedPairAtC … j (dataUC (ψ^{(k)} + v))` (background of
`𝔹_k`). -/
theorem flCompLocal_agree_on_X {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ (k + 1))} {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hS : GsSpecStrong j (hjk.trans (Nat.le_succ k)) X Gj)
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N S.G' Gk Gj S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hF : FlSetting N S.G' Gk (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl
      X₁f)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (v : S.EC) (hv : liftC S.hG' v ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁)
    (hz : IsLayerConstant (stepG d L N₁ m₁ k ϱ) (liftC S.hG' v))
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ X) :
    (composeData hB.hq S.a
        (bgFieldC Gk S.a S.ν (bgC0 d L N)
          (flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hB.hP hF.hPm S.a₁ S.ν S.D' (liftC S.hG' v) hz))
        (flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hB.hP hF.hPm S.a₁ S.ν S.D' (liftC S.hG' v)
          hz)).Ψ x =
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + v))).1 x ∧
      (composeData hB.hq S.a
        (bgFieldC Gk S.a S.ν (bgC0 d L N)
          (flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hB.hP hF.hPm S.a₁ S.ν S.D' (liftC S.hG' v) hz))
        (flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hB.hP hF.hPm S.a₁ S.ν S.D' (liftC S.hG' v)
          hz)).h x =
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + v))).2 x := by
  classical
  have hC := flCore_of hB hF
  have hL2 : 2 ≤ L := by have := hB.HBp.hL; omega
  have ha : ∀ i, 1 ≤ i → i ≤ k + 1 → S.a i ≠ 0 := fun i hi _ =>
    (compWeight_pos hL2 hB.ha₁ hi).ne'
  have hψ : liftC S.hG' v ∈ FlBallLC (stepG d L N₁ m₁ k ϱ) δ₁ := ⟨hv, hz⟩
  set Dk := S.dataUC (S.psi0C + v) with hDk
  set φ := bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D' with hφ
  set Φ := bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) Dk with hΦ
  have hhD : ∀ z i, Dk.h z i = S.D'.h z i := fun z i => by rw [hDk, S.dataUC_h, S.hh₀]
  have ht : compTangent S.hG S.hG' (le_refl (k + 1)) S.a φ S.D' Dk = liftC S.hG' v := by
    rw [hDk, hφ, S.compTangent_dataUC, add_sub_cancel_left]
  -- the fluctuation identity at the step datum
  obtain ⟨hDkdom, hfl⟩ := fluct_of_tangent hC S.hG S.hG' hB.ha₁ hB.HBp hc7 hR hsmR hRs hsmall
    hnum hnum' hD hhD hψ ht
  have hΦeq : Φ = (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ φ +
      flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν S.D' (liftC S.hG' v) := by
    rw [← hfl]; abel
  -- the datum of `Gk` is the composition from the step datum
  have hFd : flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hB.hP hF.hPm S.a₁ S.ν S.D' (liftC S.hG' v)
      hz = composeData hF.hPm S.a Φ Dk := by
    rw [hΦeq]
    refine flDatum_eq_composeData_of_fluct hB.hP hF.hPm (S.hG.precedes S.hG' (le_refl (k + 1)))
      ha φ _ S.D' (liftC S.hG' v) hz Dk (fun z i => ?_) (fun z _ i => hhD z i)
    have h1 := congrFun (congrFun ht z) i
    simp only [compTangent] at h1
    have e : (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a φ S.D').Ψ z i =
        composeField (stepG d L N₁ m₁ k ϱ) S.G' S.a φ S.D'.Ψ z i := rfl
    rw [e] at h1
    linear_combination h1
  -- the chart of `Gk` at the datum (uniqueness of its small solution)
  obtain ⟨Fk, -, hFk⟩ := theorem72_analytic (G := Gk) (a := compWeight L S.a₁) (ν := S.ν)
    hB.HBk
  have hmem := triple_one_mem (X₁f := X₁f) hC hD hψ
  obtain ⟨D₁, ψ₁, hlc, ht22, hX3, -, -, -⟩ := eTerm_chain hB hF hFk hmem
  obtain ⟨hr, hψe⟩ := Prod.mk.inj ht22
  have hDD : S.D' = D₁ := BgData.eq_of_raw hr
  subst hDD
  subst hψe
  have hDj0 : InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) S.ν
      (flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hB.hP hF.hPm S.a₁ S.ν S.D' (liftC S.hG' v) hz) :=
    xiCData_unionC hX3
  have hDj : InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) S.ν (composeData hF.hPm S.a Φ Dk) := by
    rw [← hFd]; exact hDj0
  -- Theorem 7.3: the background of `Gk` at the composed datum is the restriction
  have hbg : bgFieldC Gk S.a S.ν (bgC0 d L N) (composeData hF.hPm S.a Φ Dk) =
      hF.hPm.restrictφ Φ :=
    (bgFieldC_compose hF.hPm ha Dk (theorem72 hB.HBp hDkdom).2.1
      (theorem72 hB.HBk hDj).1).1
  rw [hFd, hbg, composeData_composeData hB.hq hF.hPm
    (precedes_levelGS hS hjk (Nat.le_succ k)) ha Φ Dk]
  unfold composedPairAtC
  simp only [hjk, ↓reduceDIte]
  exact composeData_agree_on_X (N := N) (a := S.a) hj1 hjk hS Φ Dk hx

/-- **The endpoint identity of an inherited energy label with a localized ambient set**, at the
lifted tangent `liftC v` of a complex field `v` of the unit lattice in the ball of fluctuations:
`flComp Eτ (rawOf D', liftC v) = β⁻¹ ℰ^{(j)}(y, X; composedPairAtC … j (dataUC (ψ^{(k)} + v)))`,
the label term at the composed pair of the step with the background of the whole set `𝔹_k`
(P3 (4.16)).  The ambient set `Gk` of `hB`, `hF` is arbitrary, at its own separation index; the
term generator `Gj` has the strong specification for `X`. -/
theorem classOldEndpointLocal_liftC
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
    (hcl : SFTermClauses P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} {X : Set (CTorus d L N₁ m₁ (k + 1))}
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hS : GsSpecStrong j (hjk.trans (Nat.le_succ k)) X Gj)
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N S.G' Gk Gj S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hF : FlSetting N S.G' Gk (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl
      X₁f)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (v : S.EC) (hv : liftC S.hG' v ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁) :
    flComp hB hF (fun raw => (S.β : ℂ)⁻¹ * Tm.E j y X raw.1 raw.2) (rawOf S.D', liftC S.hG' v) =
      (S.β : ℂ)⁻¹ * Tm.E j y X
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + v))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + v))).2 := by
  have hz : IsLayerConstant (stepG d L N₁ m₁ k ϱ) (liftC S.hG' v) :=
    isLayerConstant_liftC S.hG S.hG' v
  rw [flComp_rawOf hB hF _ hD hz]
  congr 1
  exact hcl.localE j y X _ _ _ _ fun x hx =>
    S.flCompLocal_agree_on_X hj1 hjk hS hB hF hD hc7 hR hsmR hRs hsmall hnum hnum' v hv hz hx

/-- **The endpoint identity of an inherited observable label with a localized ambient set**
(`classOldEndpointLocal_liftC` for `ℳ^{(j)}(x, X; ·, ·, g)_i`, clause `localM` with the same
source `g`). -/
theorem classOldEndpointLocalM_liftC
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
    (hcl : SFTermClauses P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} (i : Fin N) (g : Fld d L N₁ m₁ (k + 1) N)
    {X : Set (CTorus d L N₁ m₁ (k + 1))} {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hS : GsSpecStrong j (hjk.trans (Nat.le_succ k)) X Gj)
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N S.G' Gk Gj S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hF : FlSetting N S.G' Gk (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl
      X₁f)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (v : S.EC) (hv : liftC S.hG' v ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁) :
    flComp hB hF (fun raw => Tm.M j y X raw.1 raw.2 g i) (rawOf S.D', liftC S.hG' v) =
      Tm.M j y X
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + v))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + v))).2 g i := by
  have hz : IsLayerConstant (stepG d L N₁ m₁ k ϱ) (liftC S.hG' v) :=
    isLayerConstant_liftC S.hG S.hG' v
  rw [flComp_rawOf hB hF _ hD hz]
  refine congrFun ?_ i
  refine hcl.localM j y X _ _ _ _ g g fun x hx => ?_
  have h := S.flCompLocal_agree_on_X hj1 hjk hS hB hF hD hc7 hR hsmR hRs hsmall hnum hnum' v hv
    hz hx
  exact ⟨h.1, h.2, rfl⟩

/-- **The endpoint identity at the physical point of the hat expansion, localized ambient set**
(`classOldEndpoint_complex` with `Gk` arbitrary): for a hat variable `ψ̂ = hatC z` with
`‖ψ̂‖ ≤ c_ψ` in the radius of the ball,
`hatFun (flComp Eτ) (rawOf D', hatC z) = β⁻¹ ℰ^{(j)}(y, X; composedPairAtC … j (dataUC (psiAtC 1 z)))`.
This is the per-label identity `hid` of `oldEnergyHatMatch_of_label_identity` at the complex
datum. -/
theorem classOldEndpointLocal_complex
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
    (hcl : SFTermClauses P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} {X : Set (CTorus d L N₁ m₁ (k + 1))}
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hS : GsSpecStrong j (hjk.trans (Nat.le_succ k)) X Gj)
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N S.G' Gk Gj S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hF : FlSetting N S.G' Gk (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl
      X₁f)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)
    (z : S.E) (hψh : ∀ p, ‖yhat z p‖ ≤ cψ) :
    hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (flComp hB hF (fun raw => (S.β : ℂ)⁻¹ * Tm.E j y X raw.1 raw.2))
        (rawOf S.D', S.hatC z) =
      (S.β : ℂ)⁻¹ * Tm.E j y X
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC 1 z))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC 1 z))).2 := by
  have hC := flCore_of hB hF
  have hball := hatLift_mem_flBallLC hC S.hk1 S.hG S.hG' _ hcψ hMX hdm hα hsm hδ₁ hD hψh
  rw [← S.liftC_shiftUC] at hball
  have hpsi : S.psiAtC 1 z = S.psi0C + S.shiftUC z := by
    unfold psiAtC
    rw [Complex.ofReal_one, one_smul]
  show hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    (flComp hB hF (fun raw => (S.β : ℂ)⁻¹ * Tm.E j y X raw.1 raw.2)) (rawOf S.D', yhat z) = _
  rw [hatFun_rawOf S.hG' _ _ hD, ← S.liftC_shiftUC, hpsi]
  exact S.classOldEndpointLocal_liftC hcl hj1 hjk hS hB hF hD hc7 hR hsmR hRs hsmall hnum hnum'
    (S.shiftUC z) hball.1

/-- **The endpoint identity along the masked decoupled tangent, localized ambient set** (the
hypothesis `hend` of `deriv_eq_sum_of_expansion` for the marks of `classOldMarksY_expansion`): for
the marks `(u, t)` of the radius set,
`flComp Eτ (rawOf D', markedTangDec … (blockU z) u t D' (yhat x)) =
β⁻¹ ℰ^{(j)}(y, X; composedPairAtC … j (dataUC (ψ^{(k)} + markedTangentC z u t x)))`. -/
theorem classOldEndpointLocal_marked
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
    (hcl : SFTermClauses P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} {X : Set (CTorus d L N₁ m₁ (k + 1))}
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hS : GsSpecStrong j (hjk.trans (Nat.le_succ k)) X Gj)
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N S.G' Gk Gj S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hF : FlSetting N S.G' Gk (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl
      X₁f)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (x : S.E)
    (hψh : ∀ p, ‖yhat x p‖ ≤ cψ) {u t : ℂ}
    (hut : (‖u‖ + ‖t‖) * (Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ))) < δ₁) :
    flComp hB hF (fun raw => (S.β : ℂ)⁻¹ * Tm.E j y X raw.1 raw.2)
        (rawOf S.D', markedTangDec S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν
          (S.blockU z) u t S.D' (yhat x)) =
      (S.β : ℂ)⁻¹ * Tm.E j y X
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          (S.dataUC (S.psi0C + S.markedTangentC z u t x))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          (S.dataUC (S.psi0C + S.markedTangentC z u t x))).2 := by
  have hC := flCore_of hB hF
  have hball := markedTangDec_mem_flBallLC hC S.hk1 S.hG S.hG' _ hcψ (S.blockU z) hMX hdm hα hsm
    hut hD hψh
  rw [S.markedTangDec_eq_liftC_markedTangentC z u t x] at hball ⊢
  exact S.classOldEndpointLocal_liftC hcl hj1 hjk hS hB hF hD hc7 hR hsmR hRs hsmall hnum hnum'
    (S.markedTangentC z u t x) hball.1

end StepSetting

end Balaban.Fluctuation
