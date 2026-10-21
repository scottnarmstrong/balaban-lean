/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFHoleStepLoc

/-!
# The coefficient of an old boundary term on its local pair (reading HS-1′)

Reading HS-1′ (`notes/phase1/PLAN-B.md`): the coefficient `T(X, J)` of the re-expansion of an old
boundary term `ℬ^{(k)}(X, 𝔸)` at a family `J` of cover cubes is computed on the local pair, the
restriction of the step on a region to `𝔹_{k+1}(V(X, J))`, `V(X, J)` the sites within `r'` of the
core `X₁` (the `r`-collar of `A_X = X ∩ Ω_{k+1}`) or of a cube of `J`.

* `locSetXJ`: the local set `V(X, J)`;
* `locCubes`: the cubes of a cover with the labels of `J`;
* `restrictU`: the fluctuation field on the unit points of the restricted step;
* `oldCoefLoc`: **the coefficient `T(X, J)` on the local pair**, as a function of the fluctuation
  field `ψ̂` on the unit points of `Ω_{k+1}` (`oldCoefLF` at the restricted step, its cover, no
  integration variable);
* `norm_oldCoefLoc_le`: the Cauchy bound `|T(X, J)| ≤ B e^{-(κ₁ - 1)|J|}` (Lemma AE) when the
  interpolated old term of the local pair is analytic and bounded by `B` on the polydisc of radius
  `e^{κ₁}`.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background

namespace Balaban.RootFSpine

section LocCoef

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- **The local set `V(X, J)`** of the coefficient `T(X, J)` (reading HS-1′): the sites of the cover
torus within `r'` of the core `X₁` (the `r`-collar of `A_X`, `collarCoreC`) or of a cube of `J`. -/
def locSetXJ (H : RegionHistory S n R k0 K) {k : ℕ} (r r' : ℕ) (X : Finset (Torus S.d (n k)))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :=
  {x | ∃ y, (y ∈ collarCoreC (c := g.c) (k := k) (H.step k) hM1 r X ∨ ∃ P ∈ J, y ∈ cubeP P) ∧
    supDist x y ≤ r'}

omit [NeZero M] in
/-- The core lies in the local set. -/
theorem collarCoreC_subset_locSetXJ (H : RegionHistory S n R k0 K) {k : ℕ} (r r' : ℕ)
    (X : Finset (Torus S.d (n k))) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    (↑(collarCoreC (c := g.c) (k := k) (H.step k) hM1 r X) :
      Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) ⊆ locSetXJ g hM1 H r r' X J :=
  fun x hx => ⟨x, Or.inl hx, by simp [supDist_self]⟩

omit [NeZero M] in
/-- The cubes of `J` lie in the local set. -/
theorem cubeP_subset_locSetXJ (H : RegionHistory S n R k0 K) {k : ℕ} (r r' : ℕ)
    (X : Finset (Torus S.d (n k))) {J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))}
    {P : ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)} (hP : P ∈ J) :
    (↑(cubeP P) : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) ⊆ locSetXJ g hM1 H r r' X J :=
  fun x hx => ⟨x, Or.inr ⟨P, hP, hx⟩, by simp [supDist_self]⟩

open Classical in
/-- **The cubes of a cover with the labels of `J`.** -/
noncomputable def locCubes {k : ℕ} (C : DecCover S.d S.L (g.c * n (k + 1)) m₁ (k + 1))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) : Finset C.cubeIdx :=
  Finset.univ.filter fun Q => (Q : ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) ∈ J

/-- **The fluctuation field on the unit points of the restricted step**: the restriction of a field on
the unit points of the step. -/
def restrictU {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
    (St : HoleStep d L N₁ m₁ k N ϱ ϱ') (B : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (B' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ') (hBB : Precedes B B')
    (hBtop : B'.Ω (k + 1) ⊆ B.Ω k) (D'' : BgData (St.G'.inter B') N)
    (hh : ∀ x ∈ (St.G'.inter B').Ω 1, ∀ i, D''.h x i = (St.h₀ i : ℂ))
    (ψhat : St.U → Fin N → ℂ) : (St.restrict B B' hBB hBtop D'' hh).U → Fin N → ℂ :=
  fun b => ψhat ⟨b.1, HoleStep.unitPts_restrict_subset St B B' hBB hBtop D'' hh b.2⟩

/-- **The coefficient `T(X, J)` of an old boundary term on its local pair** (reading HS-1′; P6
(4.32)–(4.33), P3 (4.43)): the coefficient of Lemma AE of the interpolated old term of the
step restricted to `𝔹_{k+1}(V(X, J))` (`holeStepLoc`), at the cubes of its cover with the labels of
`J`, as a function of the fluctuation field `ψ̂` on the unit points of `Ω_{k+1}`. Core of
`oldCoefLoc` for the readings of the local pair: the datum `holeStepLocAt glob` and the local set
`V(σ X, J)` (reading HS-1′: `glob = false`, `σ = id`; reading HS-2: `glob = true`, `σ = stencilX`).
-/
noncomputable def oldCoefLocAt (glob : Bool) (H : RegionHistory S n R k0 K) {k : ℕ} (σ : Finset (Torus S.d (n k)) → Finset (Torus S.d (n k))) (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts}
    {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (X : Finset (Torus S.d (n k))) (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N))
    (gx : GIdx S n M K N → ℂ) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψhat : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) : ℂ :=
  oldCoefLF g hnn hM1 (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 H r r' (σ X) J))
    H hk (coverOf (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
      (locSetXJ g hM1 H r r' (σ X) J)).G') ρc ρ r ∅
    (restrictU _ _ _ _ _ _ _ ψhat) rep A X ψ ψ' hv gx
    (locCubes g (coverOf (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
      (locSetXJ g hM1 H r r' (σ X) J)).G') J)
    (fun b => absurd b.2 (Finset.notMem_empty _))

/-- **The coefficient `T(X, J)` of an old boundary term on its local pair** (reading HS-1′;
P6 (4.32)–(4.33), P3 (4.43)): the coefficient of Lemma AE of the interpolated old term of the step
restricted to `𝔹_{k+1}(V(X, J))` (`holeStepLoc`), at the cubes of its cover with the labels of `J`,
as a function of the fluctuation field `ψ̂` on the unit points of `Ω_{k+1}`. -/
noncomputable def oldCoefLoc (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts}
    {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (X : Finset (Torus S.d (n k))) (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N))
    (gx : GIdx S n M K N → ℂ) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψhat : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) : ℂ :=
  oldCoefLocAt (glob := false) (σ := fun X => X) g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ ρc ρ r r'
    rep A X ψ' hv gx J ψhat

/-- **The Cauchy bound of the coefficient on the local pair** (Lemma AE; P6 (4.33)–(4.34) at
the level of one coefficient): if the interpolated old term of the local pair is analytic and
bounded by `B` on the polydisc of radius `e^{κ₁}`, `κ₁ ≥ 1`, then `|T(X, J)| ≤ B e^{-(κ₁ -
1)|J_V|}`, `J_V` the cubes of the local cover with the labels of `J`. Core for the readings of the
local pair (`oldCoefLocAt`). -/
theorem norm_oldCoefLocAt_le (glob : Bool) (H : RegionHistory S n R k0 K) {k : ℕ} (σ : Finset (Torus S.d (n k)) → Finset (Torus S.d (n k))) (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts}
    {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (X : Finset (Torus S.d (n k))) (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N))
    (gx : GIdx S n M K N → ℂ) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψhat : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) {κ₁ Bd : ℝ}
    (hκ₁ : 1 ≤ κ₁)
    (hana : AnalyticOnNhd ℂ
      ((holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 H r r' (σ X) J)).oldInterp
        (coverOf (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' (σ X) J)).G') ρc
        (locDomsLF g hM1 (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' (σ X) J)) ρ)
        (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅ (restrictU _ _ _ _ _ _ _ ψhat)
        (oldTermLF g hnn hM1 rep A X hk (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' (σ X) J)).G' ψ ψ' hv gx)
        (fun b => absurd b.2 (Finset.notMem_empty _)))
      (Analysis.polydisc 0 fun _ => Real.exp κ₁))
    (hB : ∀ s ∈ Analysis.polydisc (0 : Dec2.DecParams (coverOf (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ
        z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 H r r' (σ X) J)).G')) (fun _ => Real.exp κ₁),
      ‖(holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 H r r' (σ X) J)).oldInterp
        (coverOf (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' (σ X) J)).G') ρc
        (locDomsLF g hM1 (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' (σ X) J)) ρ)
        (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅ (restrictU _ _ _ _ _ _ _ ψhat)
        (oldTermLF g hnn hM1 rep A X hk (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' (σ X) J)).G' ψ ψ' hv gx)
        (fun b => absurd b.2 (Finset.notMem_empty _)) s‖ ≤ Bd) :
    ‖oldCoefLocAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X ψ' hv gx J ψhat‖ ≤
      Bd * Real.exp (-(κ₁ - 1) * (locCubes g (coverOf (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁
        ν β p₁ δ (locSetXJ g hM1 H r r' (σ X) J)).G') J).card) :=
  norm_coef_le_exp hκ₁ hana hB _

/-- **The Cauchy bound of the coefficient on the local pair** (Lemma AE; P6 (4.33)–(4.34) at the
level of one coefficient): if the interpolated old term of the local pair is analytic and bounded by
`B` on the polydisc of radius `e^{κ₁}`, `κ₁ ≥ 1`, then `|T(X, J)| ≤ B e^{-(κ₁ - 1)|J_V|}`, `J_V` the
cubes of the local cover with the labels of `J`. -/
theorem norm_oldCoefLoc_le (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts}
    {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (X : Finset (Torus S.d (n k))) (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N))
    (gx : GIdx S n M K N → ℂ) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψhat : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) {κ₁ Bd : ℝ}
    (hκ₁ : 1 ≤ κ₁)
    (hana : AnalyticOnNhd ℂ
      ((holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 H r r' X J)).oldInterp
        (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' X J)).G') ρc
        (locDomsLF g hM1 (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' X J)) ρ)
        (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅ (restrictU _ _ _ _ _ _ _ ψhat)
        (oldTermLF g hnn hM1 rep A X hk (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' X J)).G' ψ ψ' hv gx)
        (fun b => absurd b.2 (Finset.notMem_empty _)))
      (Analysis.polydisc 0 fun _ => Real.exp κ₁))
    (hB : ∀ s ∈ Analysis.polydisc (0 : Dec2.DecParams (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ
        z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 H r r' X J)).G')) (fun _ => Real.exp κ₁),
      ‖(holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 H r r' X J)).oldInterp
        (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' X J)).G') ρc
        (locDomsLF g hM1 (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' X J)) ρ)
        (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅ (restrictU _ _ _ _ _ _ _ ψhat)
        (oldTermLF g hnn hM1 rep A X hk (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' X J)).G' ψ ψ' hv gx)
        (fun b => absurd b.2 (Finset.notMem_empty _)) s‖ ≤ Bd) :
    ‖oldCoefLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X ψ' hv gx J ψhat‖ ≤
      Bd * Real.exp (-(κ₁ - 1) * (locCubes g (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁
        ν β p₁ δ (locSetXJ g hM1 H r r' X J)).G') J).card) :=
  norm_oldCoefLocAt_le (glob := false) (σ := fun X => X) g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
    ρc ρ r r' rep A X ψ' hv gx J ψhat hκ₁ hana hB

end LocCoef

end Balaban.RootFSpine
