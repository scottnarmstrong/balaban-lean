/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldD7Analytic
public import Balaban.Spine.LFOldD7Hist

@[expose] public section

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.Localization Matrix Balaban.LargeField

namespace Balaban.RootFSpine

open Balaban.Fluctuation Balaban.LargeField.Def7 Balaban.LargeField.RegionHistory

set_option linter.unusedSectionVars false

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- Any datum `glob`. -/
theorem holeStepLocAt_eq_withD (glob : Bool) (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ ψ₁ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ V =
      (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).withD
        (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ V).D'
        (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ V).hh₀ := by
  rfl
section Fam

theorem holeStepLoc_eq_withD (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ ψ₁ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    holeStepLoc g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ V =
      (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).withD
        (holeStepLoc g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ V).D'
        (holeStepLoc g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ V).hh₀ :=
  holeStepLocAt_eq_withD (glob := false) g hnn hM1 H hk hk1 hρ ψ ψ₁ z h₀ a₁ ν β p₁ δ V

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ψE : E → MultiFieldC S n M K N}

/-- Any datum `glob`. -/
theorem holeStepLocAt_D'_Ψ_analytic (glob : Bool) (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {Pset : Set E} (hψ : ∀ j y i, AnalyticOnNhd ℂ (fun e => ψE e j y i) Pset) {e₀ : E}
    (he₀ : e₀ ∈ Pset) (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) (i : Fin N) :
    AnalyticAt ℂ (fun e => (holeStepLocAt g hnn hM1 glob H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ V).D'.Ψ x i)
      e₀ := by
  classical
  have hc : ∀ e, x ∈ dataSites ((holeStepLF g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ).G'.inter
      (locB g hM1 V)) ↔ x ∈ dataSites ((holeStepLF g hnn hM1 H hk hk1 hρ (ψE e₀) z h₀ a₁ ν β p₁ δ).G'.inter
      (locB g hM1 V)) := fun e => Iff.rfl
  simp only [holeStepLocAt_D'_eq, liftMixed, BgData.clip, hc]
  by_cases hx : x ∈ dataSites ((holeStepLF g hnn hM1 H hk hk1 hρ (ψE e₀) z h₀ a₁ ν β p₁ δ).G'.inter
      (locB g hM1 V))
  · simp only [hx, ↓reduceIte]
    have hc2 : ∀ e, x ∈ locTop g hM1 glob (holeStepLF g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ).G'
        V ↔ x ∈ locTop g hM1 glob (holeStepLF g hnn hM1 H hk hk1 hρ (ψE e₀) z h₀ a₁ ν β p₁ δ).G' V :=
      fun e => Iff.rfl
    unfold mixedLift
    simp only [hc2]
    split_ifs
    · unfold blockLift coverField scaleMulti
      exact analyticAt_const.mul (hψ _ _ _ e₀ he₀)
    · unfold blockLift coverField
      exact hψ _ _ _ e₀ he₀
  · simp only [hx, ↓reduceIte]
    exact analyticAt_const

theorem holeStepLoc_D'_Ψ_analytic (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {Pset : Set E} (hψ : ∀ j y i, AnalyticOnNhd ℂ (fun e => ψE e j y i) Pset) {e₀ : E}
    (he₀ : e₀ ∈ Pset) (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) (i : Fin N) :
    AnalyticAt ℂ (fun e => (holeStepLoc g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ V).D'.Ψ x i)
      e₀ :=
  holeStepLocAt_D'_Ψ_analytic (glob := false) g hnn hM1 H hk hk1 hρ z h₀ a₁ ν β p₁ δ V hψ he₀ x i

/-- Any datum `glob`. -/
theorem holeStepLocAt_D'_h_const (glob : Bool) (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψ₀ : MultiFieldC S n M K N) (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) (i : Fin N)
    {Pset : Set E} :
    AnalyticOnNhd ℂ (fun e =>
      (holeStepLocAt g hnn hM1 glob H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ V).D'.h x i) Pset := by
  intro e₀ _
  have : (fun e => (holeStepLocAt g hnn hM1 glob H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ V).D'.h x i) =
      fun _ => (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ V).D'.h x i := by
    funext e; rfl
  rw [this]
  exact analyticAt_const

theorem holeStepLoc_D'_h_const (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψ₀ : MultiFieldC S n M K N) (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) (i : Fin N)
    {Pset : Set E} :
    AnalyticOnNhd ℂ (fun e =>
      (holeStepLoc g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ V).D'.h x i) Pset :=
  holeStepLocAt_D'_h_const (glob := false) g hnn hM1 H hk hk1 hρ z h₀ a₁ ν β p₁ δ V ψ₀ x i

end Fam

/-- The local step of the coefficient `T(X, J)`: `holeStepLoc` at the local set `V(X, J)`. Core for
the readings of the local pair (`holeStepLocAt glob` at `V(σ X, J)`). -/
noncomputable abbrev locStepXJAt (glob : Bool) (H : RegionHistory S n R k0 K) {k : ℕ} (σ : Finset (Torus S.d (n k)) → Finset (Torus S.d (n k))) (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (r r' : ℕ) (X : Finset (Torus S.d (n k)))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N (minSep S.L g.M1) (minSep S.L g.M1) :=
  holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 H r r' (σ X) J)

/-- The local step of the coefficient `T(X, J)`: `holeStepLoc` at the local set `V(X, J)`. -/
noncomputable abbrev locStepXJ (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (r r' : ℕ) (X : Finset (Torus S.d (n k)))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N (minSep S.L g.M1) (minSep S.L g.M1) :=
  locStepXJAt (glob := false) (σ := fun X => X) g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ r r' X J

section Fam2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ψE : E → MultiFieldC S n M K N}

/-- **The coefficient `T(X, J)` on the local pair is analytic in the fields** (the clause
`analytic` of (D7) for the re-expanded old term, at the level of one coefficient): for a family of
multiscale fields `ψE e`, `ψ'E e`, sources `gxE e` depending analytically on a parameter `e ∈ Pset`
(open), the coefficient is analytic on `Pset`.  Inputs: the standing conditions of Theorems I-4b,
I-4c for the local step (`hS … hsm`, as in `HoleStep.analyticAt_composed`), `hD` (the datum of the
local step of `ψE e` lies in `Ψ̃^c(δ, δ)`), and the analyticity of the old term `oldTermLF … (ψE e)
(ψ'E e) hv (gxE e)` at the composed field jointly in `(e, field)` (`hB`; from the clause `analytic`
of the record at `X` and the H7 conditions of the local pair). Core for the readings of the local
pair (the datum `glob`, the label `σ` of the local set). -/
theorem oldCoefLocAt_analytic_family (glob : Bool) (H : RegionHistory S n R k0 K) {k : ℕ} (σ : Finset (Torus S.d (n k)) → Finset (Torus S.d (n k))) (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ₀ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M}
    {cs : OpConsts} {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k)
    (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψout : (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).U → Fin N → ℂ)
    {Kc Cx Cx₂ c BG δ' δc : ℝ} {κ κ₁ : ℝ}
    (hS : Dec2.DecSpecs S.d S.L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G')
      (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G' (compWeight S.L a₁) ν Kc Cx)
    (SX : Dec2.XCover (coverOf (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G')
      (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G' (compWeight S.L a₁) a₁ ν Cx₂)
    (hCx₂ : 0 ≤ Cx₂)
    (HB : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν) (hκ : 0 < κ)
    (hM : c * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX S.d S.L Cx₂ * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    (hδ0 : 0 < δ') (hε : δ' ≤ bgC0 S.d S.L N) (hδ : δ' ≤ c7 S.d S.L N BG κ)
    (hνε : ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * δ' ^ 2 ≤ δ' ^ 2)
    (hphi : 3 * δ' + K4 S.d S.L N BG κ * δ' < 1 / 2)
    (hmarD : K4 S.d S.L N BG κ * δ' + 2 * δ' + K4 S.d S.L N BG κ * δ' *
      (K4 S.d S.L N BG κ * δ' + 2 * (1 + 3 * δ')) < δc)
    (hαD : K4 S.d S.L N BG κ * δ' < coerciveConst S.d / 2)
    (hsm : δc ^ 2 * smallConstX S.d S.L κ ≤ 1 / 4) (hκ₁0 : 0 < κ₁) (hκ₁ : κ₁ ≤ κ)
    {Pset : Set E} (hP : IsOpen Pset)
    (hψ : ∀ j y i, AnalyticOnNhd ℂ (fun e => ψE e j y i) Pset)
    (ψ'E : E → MultiFieldC S n M K N) (gxE : E → GIdx S n M K N → ℂ)
    (hD : ∀ e ∈ Pset, InDomainC (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G'
      ν δ' δ' (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).D')
    (hB : ∀ e ∈ Pset, ∀ s ∈ Analysis.polydisc
      (0 : Dec2.DecParams (coverOf (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G'))
      (fun _ => Real.exp κ₁),
      AnalyticAt ℂ (fun q : E × ((locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).U →
          Fin N → ℂ) =>
        oldTermLF g hnn hM1 rep A X hk
          (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G'
          (ψE q.1) (ψ'E q.1) hv (gxE q.1) q.2)
        (e, ((locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).withD
            (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).D'
            (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).hh₀).composed
          (coverOf (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G')
          (rho4 S.d S.L N BG κ)
          ((locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).slocOf
            (coverOf (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G')
            (locDomsLF g hM1 (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J) ρ)
            (HoleStep.coreExt (coverOf (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G')
              (collarCoreC (c := g.c) (H.step k) hM1 r X) s))
          ((locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).fill ∅
            (fun b => absurd b.2 (Finset.notMem_empty _)) ψout))) :
    AnalyticOnNhd ℂ (fun e =>
      ((locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).withD
        (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).D'
        (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).hh₀).oldCoef
        (coverOf (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G') (rho4 S.d S.L N BG κ)
        (locDomsLF g hM1 (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J) ρ)
        (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅ ψout
        (oldTermLF g hnn hM1 rep A X hk
          (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G' (ψE e) (ψ'E e) hv
          (gxE e))
        (locCubes g (coverOf (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G') J)
        (fun b => absurd b.2 (Finset.notMem_empty _))) Pset := by
  have key := (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).analyticOnNhd_oldCoef_family
    hS Sb SX hCx₂ HB hκ hM hMX hδ0 hε hδ hνε hphi hmarD hαD hsm hκ₁0 hκ₁ hP
    (D := fun e => (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).D')
    (fun e => (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).hh₀) hD
    (fun x i e he => holeStepLocAt_D'_Ψ_analytic g hnn hM1 glob H hk hk1 hρ z h₀ a₁ ν β p₁ δ _ hψ he x i)
    (fun x i => holeStepLocAt_D'_h_const g hnn hM1 glob H hk hk1 hρ z h₀ a₁ ν β p₁ δ _ ψ₀ x i)
    (locDomsLF g hM1 (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J) ρ)
    (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅ ψout
    (fun b => absurd b.2 (Finset.notMem_empty _))
    (fun e c => oldTermLF g hnn hM1 rep A X hk
      (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G' (ψE e) (ψ'E e) hv
      (gxE e) c) hB
    (locCubes g (coverOf (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G') J)
  exact key

/-- **The coefficient `T(X, J)` on the local pair is analytic in the fields** (the clause `analytic`
of (D7) for the re-expanded old term, at the level of one coefficient): for a family of multiscale
fields `ψE e`, `ψ'E e`, sources `gxE e` depending analytically on a parameter `e ∈ Pset` (open), the
coefficient is analytic on `Pset`.  Inputs: the standing conditions of Theorems I-4b, I-4c for the
local step (`hS … hsm`, as in `HoleStep.analyticAt_composed`), `hD` (the datum of the local step of
`ψE e` lies in `Ψ̃^c(δ, δ)`), and the analyticity of the old term `oldTermLF … (ψE e) (ψ'E e) hv
(gxE e)` at the composed field jointly in `(e, field)` (`hB`; from the clause `analytic` of the
record at `X` and the H7 conditions of the local pair). -/
theorem oldCoefLoc_analytic_family (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ₀ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M}
    {cs : OpConsts} {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k)
    (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψout : (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).U → Fin N → ℂ)
    {Kc Cx Cx₂ c BG δ' δc : ℝ} {κ κ₁ : ℝ}
    (hS : Dec2.DecSpecs S.d S.L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G')
      (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G' (compWeight S.L a₁) ν Kc Cx)
    (SX : Dec2.XCover (coverOf (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G')
      (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G' (compWeight S.L a₁) a₁ ν Cx₂)
    (hCx₂ : 0 ≤ Cx₂)
    (HB : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν) (hκ : 0 < κ)
    (hM : c * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX S.d S.L Cx₂ * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    (hδ0 : 0 < δ') (hε : δ' ≤ bgC0 S.d S.L N) (hδ : δ' ≤ c7 S.d S.L N BG κ)
    (hνε : ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * δ' ^ 2 ≤ δ' ^ 2)
    (hphi : 3 * δ' + K4 S.d S.L N BG κ * δ' < 1 / 2)
    (hmarD : K4 S.d S.L N BG κ * δ' + 2 * δ' + K4 S.d S.L N BG κ * δ' *
      (K4 S.d S.L N BG κ * δ' + 2 * (1 + 3 * δ')) < δc)
    (hαD : K4 S.d S.L N BG κ * δ' < coerciveConst S.d / 2)
    (hsm : δc ^ 2 * smallConstX S.d S.L κ ≤ 1 / 4) (hκ₁0 : 0 < κ₁) (hκ₁ : κ₁ ≤ κ)
    {Pset : Set E} (hP : IsOpen Pset)
    (hψ : ∀ j y i, AnalyticOnNhd ℂ (fun e => ψE e j y i) Pset)
    (ψ'E : E → MultiFieldC S n M K N) (gxE : E → GIdx S n M K N → ℂ)
    (hD : ∀ e ∈ Pset, InDomainC (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G'
      ν δ' δ' (locStepXJ g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).D')
    (hB : ∀ e ∈ Pset, ∀ s ∈ Analysis.polydisc
      (0 : Dec2.DecParams (coverOf (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G'))
      (fun _ => Real.exp κ₁),
      AnalyticAt ℂ (fun q : E × ((locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).U →
          Fin N → ℂ) =>
        oldTermLF g hnn hM1 rep A X hk
          (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G'
          (ψE q.1) (ψ'E q.1) hv (gxE q.1) q.2)
        (e, ((locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).withD
            (locStepXJ g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).D'
            (locStepXJ g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).hh₀).composed
          (coverOf (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G')
          (rho4 S.d S.L N BG κ)
          ((locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).slocOf
            (coverOf (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G')
            (locDomsLF g hM1 (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J) ρ)
            (HoleStep.coreExt (coverOf (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G')
              (collarCoreC (c := g.c) (H.step k) hM1 r X) s))
          ((locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).fill ∅
            (fun b => absurd b.2 (Finset.notMem_empty _)) ψout))) :
    AnalyticOnNhd ℂ (fun e =>
      ((locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).withD
        (locStepXJ g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).D'
        (locStepXJ g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).hh₀).oldCoef
        (coverOf (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G') (rho4 S.d S.L N BG κ)
        (locDomsLF g hM1 (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J) ρ)
        (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅ ψout
        (oldTermLF g hnn hM1 rep A X hk
          (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G' (ψE e) (ψ'E e) hv
          (gxE e))
        (locCubes g (coverOf (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G') J)
        (fun b => absurd b.2 (Finset.notMem_empty _))) Pset :=
  oldCoefLocAt_analytic_family (glob := false) (σ := fun X => X) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν
    β p₁ δ ρ r r' rep A X hv J ψout hS Sb SX hCx₂ HB hκ hM hMX hδ0 hε hδ hνε hphi hmarD hαD hsm
    hκ₁0 hκ₁ hP hψ ψ'E gxE hD hB

/-- Core for the readings of the local pair (the datum `glob`, the label `σ` of the local set). -/
theorem oldCoefLFAt_eq_withD (glob : Bool) (H : RegionHistory S n R k0 K) {k : ℕ} (σ : Finset (Torus S.d (n k)) → Finset (Torus S.d (n k))) (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ₀ ψ₁ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M}
    {cs : OpConsts} {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k)
    (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k))) (ψ' : MultiFieldC S n M K N)
    (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψout : (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).U → Fin N → ℂ) :
    oldCoefLF g hnn hM1 (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ r r' X J) H hk
      (coverOf (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ r r' X J).G') ρc ρ r ∅
      ψout rep A X ψ₁ ψ' hv gx
      (locCubes g (coverOf (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ r r' X J).G') J)
      (fun b => absurd b.2 (Finset.notMem_empty _)) =
    ((locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).withD
        (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ r r' X J).D'
        (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ r r' X J).hh₀).oldCoef
      (coverOf (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G') ρc
      (locDomsLF g hM1 (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J) ρ)
      (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅ ψout
      (oldTermLF g hnn hM1 rep A X hk
        (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G' ψ₁ ψ' hv gx)
      (locCubes g (coverOf (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G') J)
      (fun b => absurd b.2 (Finset.notMem_empty _)) := by
  have e := holeStepLocAt_eq_withD g hnn hM1 glob H hk hk1 hρ ψ₀ ψ₁ z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 H r r' (σ X) J)
  unfold oldCoefLF
  rfl

theorem oldCoefLF_eq_withD (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ₀ ψ₁ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M}
    {cs : OpConsts} {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k)
    (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k))) (ψ' : MultiFieldC S n M K N)
    (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψout : (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).U → Fin N → ℂ) :
    oldCoefLF g hnn hM1 (locStepXJ g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ r r' X J) H hk
      (coverOf (locStepXJ g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ r r' X J).G') ρc ρ r ∅
      ψout rep A X ψ₁ ψ' hv gx
      (locCubes g (coverOf (locStepXJ g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ r r' X J).G') J)
      (fun b => absurd b.2 (Finset.notMem_empty _)) =
    ((locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).withD
        (locStepXJ g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ r r' X J).D'
        (locStepXJ g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ r r' X J).hh₀).oldCoef
      (coverOf (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G') ρc
      (locDomsLF g hM1 (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J) ρ)
      (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅ ψout
      (oldTermLF g hnn hM1 rep A X hk
        (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G' ψ₁ ψ' hv gx)
      (locCubes g (coverOf (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G') J)
      (fun b => absurd b.2 (Finset.notMem_empty _)) :=
  oldCoefLFAt_eq_withD (glob := false) (σ := fun X => X) g hnn hM1 H hk hk1 hρ ψ₀ ψ₁ z h₀ a₁ ν β p₁
    δ ρc ρ r r' rep A X ψ' hv gx J ψout

/-- Core for the readings of the local pair (the datum `glob`, the label `σ` of the local set). -/
theorem oldCoefLocAt_analytic_family_LF (glob : Bool) (H : RegionHistory S n R k0 K) {k : ℕ} (σ : Finset (Torus S.d (n k)) → Finset (Torus S.d (n k))) (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ₀ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M}
    {cs : OpConsts} {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k)
    (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψout : (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).U → Fin N → ℂ)
    {ρc₀ : ℝ} {Pset : Set E} (hP : IsOpen Pset) (ψ'E : E → MultiFieldC S n M K N)
    (gxE : E → GIdx S n M K N → ℂ)
    (key : AnalyticOnNhd ℂ (fun e =>
      ((locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).withD
        (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).D'
        (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).hh₀).oldCoef
        (coverOf (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G') ρc₀
        (locDomsLF g hM1 (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J) ρ)
        (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅ ψout
        (oldTermLF g hnn hM1 rep A X hk
          (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G' (ψE e) (ψ'E e) hv
          (gxE e))
        (locCubes g (coverOf (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G') J)
        (fun b => absurd b.2 (Finset.notMem_empty _))) Pset) :
    AnalyticOnNhd ℂ (fun e => oldCoefLF g hnn hM1
      (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J) H hk
      (coverOf (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).G') ρc₀ ρ r ∅
      ψout rep A X (ψE e) (ψ'E e) hv (gxE e)
      (locCubes g (coverOf (locStepXJAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).G') J)
      (fun b => absurd b.2 (Finset.notMem_empty _))) Pset :=
  key.congr hP (fun e _ => (oldCoefLFAt_eq_withD (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₀ (ψE e) z h₀ a₁ ν β p₁ δ
    ρc₀ ρ r r' rep A X (ψ'E e) hv (gxE e) J ψout).symm)

theorem oldCoefLoc_analytic_family_LF (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ₀ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M}
    {cs : OpConsts} {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k)
    (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψout : (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).U → Fin N → ℂ)
    {ρc₀ : ℝ} {Pset : Set E} (hP : IsOpen Pset) (ψ'E : E → MultiFieldC S n M K N)
    (gxE : E → GIdx S n M K N → ℂ)
    (key : AnalyticOnNhd ℂ (fun e =>
      ((locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).withD
        (locStepXJ g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).D'
        (locStepXJ g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).hh₀).oldCoef
        (coverOf (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G') ρc₀
        (locDomsLF g hM1 (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J) ρ)
        (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅ ψout
        (oldTermLF g hnn hM1 rep A X hk
          (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G' (ψE e) (ψ'E e) hv
          (gxE e))
        (locCubes g (coverOf (locStepXJ g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G') J)
        (fun b => absurd b.2 (Finset.notMem_empty _))) Pset) :
    AnalyticOnNhd ℂ (fun e => oldCoefLF g hnn hM1
      (locStepXJ g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J) H hk
      (coverOf (locStepXJ g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).G') ρc₀ ρ r ∅
      ψout rep A X (ψE e) (ψ'E e) hv (gxE e)
      (locCubes g (coverOf (locStepXJ g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).G') J)
      (fun b => absurd b.2 (Finset.notMem_empty _))) Pset :=
  oldCoefLocAt_analytic_family_LF (glob := false) (σ := fun X => X) g hnn hM1 H hk hk1 hρ ψ₀ z h₀
    a₁ ν β p₁ δ ρ r r' rep A X hv J ψout hP ψ'E gxE key

end Fam2

end Balaban.RootFSpine
