/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldCoef
public import Balaban.Fluctuation.HoleStepGeom
public import Balaban.LargeField.Background.HoleStepCover

/-!
# The locality of the re-expansion of an old boundary term of a history (OPEN-P6-ACTIVE-COMPOSITE-LOC)

The history instance of `HoleStep.oldCoef_eq_zero_of_not_reached` (reading R12 of
`notes/phase1/PLAN-B.md`): for the step on a region of a history (`holeStepLF`, the set `G′` of
P5 (2.17) on the cover torus), the cover `coverOf G′`, the localization domains of (2.18)
(`locDomsLF`) and the uncut core, the `r`-collar of `A_X = X ∩ Ω_{k+1}` (`collarCoreC`), the
coefficient `T(X, J)` vanishes unless every cube of `J` lies in the region reached from the read unit
points.  Every geometric hypothesis is proved here; the remaining inputs are the datum of the step in
the domain `Ψ̃^c(δ, δ)` of Theorem I-4b (implied by the chart `Ξ^c(G′; 1, ε)`; the background part of
OPEN-H7-MIXED), the numerical conditions of Theorems I-4b, I-4c, and the locality of the record's
term in the field (its (D7) clause, `hB`).

* `readPts`: the read unit points of an old term (the unit points of `A_X`);
* `locDomsLF_deep`, `locDomsLF_ball`, `collarCoreC_ball`: the domains lie in the deep part of
  `Ω₁(G′)` and contain the balls of radius `6 L^{k+1+m₁}` around the read points, and so does the core
  for `r ≥ 6 L^{k+1+m₁}`;
* `oldCoefLF_eq_zero_of_not_reached`: **the coefficients of an old term of a history are rooted at its
  read points**.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.Background Balaban.SmallField

namespace Balaban.RootFSpine

section History

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

open Classical in
/-- **The read unit points of an old term** `ℬ^{(k)}(X)`: the unit points of `Ω_{k+1}` whose
representative lies in `A_X = X ∩ Ω_{k+1}`. -/
noncomputable def readPts (H : RegionHistory S n R k0 K) {k : ℕ} {ϱ ϱ' : ℝ}
    (St : HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N ϱ ϱ') (X : Finset (Torus S.d (n k))) :
    Finset St.U :=
  Finset.univ.filter fun b => (unitRep b : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) ∈
    activeCoreC (c := g.c) (H.step k) hM1 X

omit [NeZero M] in
/-- The localization domains lie in the deep part of `Ω₁(G′)`. -/
theorem locDomsLF_deep {k : ℕ} {ϱ ϱ' : ℝ} (St : HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N ϱ ϱ')
    (ρ : ℕ) (b : St.U) :
    ∀ y ∈ locDomsLF g hM1 St ρ b, ∀ z : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1),
      supDist y z ≤ 4 * S.L ^ (k + 1 + m₁) → z ∈ St.G'.Ω 1 := by
  classical
  intro y hy
  exact (Finset.mem_filter.1 hy).2

omit [NeZero M] in
/-- **The localization domains of the step of a history contain the balls around the points of
`Ω_{k+1}`**: for a unit point whose representative lies in `Ω_{k+1}`, every site within
`6 L^{k+1+m₁}` of it lies in its domain (its cube of `𝕋_{k+1}` is a neighbour of that of the point,
and its `4 L^{k+1+m₁}`-ball lies in `Ω₁(G′)`, `p6TopC_ball`). -/
theorem locDomsLF_ball (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z₀ : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (ρ : ℕ) (b : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).U)
    (hb : cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 (unitRep b) ∈ (H.step k).Omega)
    (y : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))
    (hy : supDist (unitRep b : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) y ≤
      6 * S.L ^ (k + 1 + m₁)) :
    y ∈ locDomsLF g hM1 (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ) ρ b := by
  classical
  have hc := g.hc
  refine Finset.mem_filter.2 ⟨?_, fun z hz => ?_⟩
  · -- the cube of `y` is a neighbour of the cube of `b`
    rw [mem_locDomC]
    refine (mem_nbhd).2 ⟨_, Set.mem_singleton _, ?_⟩
    set e := (congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm
    have hP : g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1) =
        (S.L ^ (k + 1) * (g.c * g.M1)) * n (k + 1) := by ring
    have hD : 6 * (g.M1 * S.L ^ (k + 1)) ≤ S.L ^ (k + 1) * (g.c * g.M1) := by
      have : 6 * (g.M1 * S.L ^ (k + 1)) = (S.L ^ (k + 1) * g.M1) * 6 := by ring
      rw [this, show S.L ^ (k + 1) * (g.c * g.M1) = (S.L ^ (k + 1) * g.M1) * g.c by ring]
      exact Nat.mul_le_mul_left _ (by omega)
    have hd : supDist (e ▸ y : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)))
        (e ▸ (unitRep b : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) ≤
        6 * (g.M1 * S.L ^ (k + 1)) := by
      have e : g.M1 * S.L ^ (k + 1) = S.L ^ (k + 1 + m₁) := by
        rw [hM1, ← pow_add, add_comm m₁]
      rw [supDist_cast, supDist_comm, e]
      exact hy
    have h1 := supDist_blockMap_le_one (M1 := g.M1) (N₁ := g.c * n (k + 1)) (L := S.L)
      (q := k + 1) hP hD _ _ hd
    exact h1.trans (by omega)
  · -- the `4 L^{k+1+m₁}`-ball of `y` lies in `Ω₁(G′)`
    have h2 := supDist_triangle (unitRep b : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) y z
    exact p6TopC_ball (H.step k) hM1 (hnn k (by omega)) hρ (by omega) hc hk1 hb (by omega)

omit [NeZero M] in
/-- **The core contains the balls around the read points** when its collar radius is at least
`6 L^{k+1+m₁}`. -/
theorem collarCoreC_ball (H : RegionHistory S n R k0 K) {k : ℕ} {ϱ ϱ' : ℝ}
    (St : HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N ϱ ϱ') (X : Finset (Torus S.d (n k))) {r : ℕ}
    (hr : 6 * S.L ^ (k + 1 + m₁) ≤ r) :
    ∀ b ∈ readPts g hM1 H St X, ∀ y : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1),
      supDist (unitRep b : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) y ≤
        6 * S.L ^ (k + 1 + m₁) → y ∈ collarCoreC (c := g.c) (H.step k) hM1 r X := by
  classical
  intro b hb y hy
  rw [mem_collarCoreC]
  refine ⟨_, (Finset.mem_filter.1 hb).2, ?_⟩
  rw [supDist_comm]
  omega

/-- **The coefficients of the re-expansion of an old term of a history are rooted at its read points**
(OPEN-P6-ACTIVE-COMPOSITE-LOC under R12, history instance): `T(X, J) = 0` unless every cube of `J`
lies in the region `Y(J)` reached from the read unit points of `X` through chains of active centres.
The inputs: the datum of the step in the domain `Ψ̃^c(δ, δ)` of Theorem I-4b (the background part of
OPEN-H7-MIXED), the numerical conditions of Theorems I-4b and I-4c, the cover constants of the cube-aligned set `G′`, a collar radius
`r ≥ 6 L^{k+1+m₁}`, and the locality of the old term in the field (`hB`, the (D7) clause). -/
theorem oldCoefLF_eq_zero_of_not_reached (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z₀ : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) {c BG δb δc κ : ℝ}
    (hS : Dec2.DecSpecs S.d S.L (Dec2.mixedKc S.d S.L) (Cchi S.d S.L) c BG)
    (HB : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν)
    (hm₁ : 2 ≤ m₁) (hN : 5 < g.c * n (k + 1)) (hM : 4 * S.L ^ 2 ≤ S.L ^ m₁)
    (hag : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1))
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2) (hκ : 0 ≤ κ)
    (hMc : c * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX S.d S.L (Cchi S.d S.L) * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    (hδ0 : 0 < δb) (hε : δb ≤ bgC0 S.d S.L N) (hδ : δb ≤ c7 S.d S.L N BG κ)
    (hphi : 3 * δb + K4 S.d S.L N BG κ * δb < 1 / 2)
    (hmarD : K4 S.d S.L N BG κ * δb + 2 * δb +
      K4 S.d S.L N BG κ * δb * (K4 S.d S.L N BG κ * δb + 2 * (1 + 3 * δb)) < δc)
    (hαD : K4 S.d S.L N BG κ * δb < coerciveConst S.d / 2)
    (hsm : δc ^ 2 * smallConstX S.d S.L κ ≤ 1 / 4)
    (hD : InDomainC (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).G' ν δb δb
      (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).D')
    {D : ℕ} (hDD : S.L ^ (k + 1) + 2 * S.L ^ (k + 1) ≤ D) (ρ : ℕ) {r : ℕ}
    (hr : 6 * S.L ^ (k + 1 + m₁) ≤ r)
    (inner : Finset (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).U)
    (ψout : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).U → Fin N → ℂ)
    {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k)
    (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k))) (ψ' : MultiFieldC S n M K N)
    (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (hB : ∀ c c' : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).U → Fin N → ℂ,
      (∀ b ∈ readPts g hM1 H (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ) X,
        c b = c' b) →
      oldTermLF g hnn hM1 rep A X hk (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).G' ψ ψ'
          hv gx c =
        oldTermLF g hnn hM1 rep A X hk (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).G' ψ
          ψ' hv gx c')
    {Rp : ℝ} (hR1 : 1 < Rp) (hRk : Rp < Real.exp κ)
    {J : Finset (coverOf (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).G').cubeIdx}
    (hJ : ¬ IsConnectedFamily
      (fun Q : (coverOf (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).G').cubeIdx =>
        (cubeP (Q : ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
          Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))))
      ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).reachSet
        (coverOf (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).G')
        (locDomsLF g hM1 (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ) ρ)
        (collarCoreC (c := g.c) (H.step k) hM1 r X) D
        (readPts g hM1 H (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ) X)) J)
    (ψin : inner → Rn N) :
    oldCoefLF g hnn hM1 (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ) H hk
      (coverOf (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).G') (rho4 S.d S.L N BG κ) ρ r
      inner ψout rep A X ψ ψ' hv gx J ψin = 0 := by
  classical
  have hc := g.hc
  have hn : n k = S.L * n (k + 1) := hnn k (by omega)
  have Sb := p6TopC_coverBase (H.step k) hM1 hn hρ (by omega) hm₁ hN hM HB.hd HB.hL HB.mass
    HB.massLe HB.weights hag
  have SX := p6TopC_xCover (H.step k) hM1 hn hρ (by omega) hm₁ hN hM HB.hd HB.hL HB.mass HB.massLe
    HB.weights hag hk1 ha₁ ha₂
  have hG : CubeAligned (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).G' m₁ :=
    p6TopC_cubeAligned hM1 hn hρ (by omega) hm₁
  have hcov := (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).hcov_of_balls hG hM
    (Rd := readPts g hM1 H (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ) X)
    (X₁ := collarCoreC (c := g.c) (H.step k) hM1 r X)
    (X₁loc := locDomsLF g hM1 (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ) ρ)
    (collarCoreC_ball g hM1 H (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ) X hr)
    (fun b hb y hy => locDomsLF_ball g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ ρ b
      ((mem_activeCoreC (H.step k)).1 (Finset.mem_filter.1 hb).2).2 y hy)
  have hdeep := (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).hlocdeep_of_deep hM
    (Rd := readPts g hM1 H (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ) X)
    (X₁loc := locDomsLF g hM1 (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ) ρ)
    (fun b _ => locDomsLF_deep g hM1 (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ) ρ b)
  have hloc :=
    (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).oldInterp_localityAEOn_of_inDomainC
    hS Sb SX (Cchi_nonneg S.d S.L) HB hκ hMc hMX hδ0 hε hδ hphi hmarD hαD hsm HB.massLe hD hDD
    (locDomsLF g hM1 (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ) ρ)
    (collarCoreC (c := g.c) (H.step k) hM1 r X) inner ψout hB hR1.le hRk hcov hdeep
  exact coef_eq_zero_of_not_connected_on hR1 hloc (fun _ _ _ _ _ => rfl) (Set.mem_univ ψin) hJ

end History

end Balaban.RootFSpine
