/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ActionConvChain
public import Balaban.LargeField.R.RRemovedHidBridgeStep
public import Balaban.LargeField.Characteristic.RealDomain
import Balaban.SmallField.XiMassResponse

/-!
# The chain of conversions of a piece of the window (W958, S4)

`notes/phase1/LF4R-PLAN.md` §9.3, item S4 (route A′); P7 (2.10)-(2.16), P6 (2.31), LFR Lemma III.2.2
("we do not renormalize the spin variables").  A piece of the window is a component `Z'` (`Zc`) of
the step `j → j + 1`; its main action `𝒜_{j+1}(Z'; ψ)` (`mainActionLoc`) is converted to the
coefficients of the scales `n = j + 2, …, k` on the local family `G^{Z'}_{j+1}` (`locGen`) and the
region `X` with sites `X_{Z'}` (`Xfine`), keeping the datum `lift_{j,j+1}(ψ_j, ψ_{j+1})`
(`locData`) of the step at every scale.  The coefficients at the scale `n`, in the units of the
fine sites of `G^{Z'}_{j+1}`:

* `β_n = β^{(n)}_0 = β_n L^{-n(d-2)}` (`betaCanon (cs.beta n) n 0`, the coupling of the main action
  of the step `n - 1 → n`);
* `a_n = (β_{j+1}/β_n) a`: the block coefficient `β_n a_n = β_{j+1} a` is kept (the coefficient
  identity `β_u a_u = β a` of P6 (2.31), field `coeff`; under the free flow `a_n = a`, P7 (2.10));
* `ν_n = ν_n L^{-2n}` (`cs.muAct n`, the mass of the main action at scale `n`), and
  `e_n = (β_{n-1} ν_{n-1} - β_n ν_n)/ν_n` (the mass identity of P6 (2.31), field `mass`).

The backgrounds: `φ_{j+1} = φ^loc_{j+1}` (`locBg`, background mass `cs.muBg (j + 1)`), and for `n ≥ j + 2` the
background of the same datum with the coefficients `(a_n, ν_n)` in the mass convention `br` of the
Euler-Lagrange system (`bgFieldC`, `bgMultC`; P631 §1).  The parameter domain `Sdom` is a set of
configurations `u` (read by `ou`, `xu`, `hvu`) whose datum lies in the real domains `𝒟_ℝ` of
Theorem 7.1 for the masses used.

* `pieceChain`: the chain (`ConvChain`), with the fields `β_ne`, `coeff`, `mass`, `same_h`, `el`
  (Theorem 7.2: the small solution satisfies (EL)), `unit` (hard-spin constraint of the small
  solution);
* `pieceChain_T`: `Re T_{j,j+1} = 𝒜_{j+1}(Z'; ψ)` (`mainActionLoc_eq_re_actionRegionC`);
* `bgHyp_massless`, `inUnionDomainR_massless`: the premises `hBn`, `hS` in the massless branch.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory Balaban.LargeField.ActionConv

section Piece

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (j : ℕ)
  (Zc : Finset (Torus S.d (n (j + 1)))) (hZc : Zc ∈ comps (S.omega (j + 1)) (Hl.F.Zp (j + 1)))
  (hk : j + 1 ≤ K) (cs : OpConsts)

/-- **The chain of conversions of the piece `Z'` of the step `j → j + 1`** (route A′ of
`LF4R-PLAN.md` §9.3, S4; P7 (2.10)-(2.16), P6 (2.31)): on `G^{Z'}_{j+1}` and the region `X`, the
coupling `β_n = β_n L^{-n(d-2)}`, the block weights `a_n = (β_{j+1}/β_n) a`, the mass
`ν_n = ν_n L^{-2n}` and `e_n = (β_{n-1}ν_{n-1} - β_nν_n)/ν_n`; the datum `lift_{j,j+1}(ψ_j, ψ_{j+1})`
at every scale; the background `φ^loc_{j+1}` at `n = j + 1` and the background of the same datum
with the coefficients `(a_n, ν_n)` (mass convention `br`) at `n ≥ j + 2`, with its multiplier. -/
noncomputable def pieceChain {U : Type*} (Sdom : Set U) (k : ℕ) (br : MassBranch)
    (X : Region (locGen g Hl j Zc hZc hk))
    (ou : U → OutT N R (locHist Hl M K (j + 1) Zc) (j + 1))
    (xu : U → NewCfg N (locHist Hl M K (j + 1) Zc) j) (hvu : U → EuclideanSpace ℝ (Fin N))
    (hβ : ∀ m, j + 1 ≤ m → m ≤ k → cs.beta m ≠ 0)
    (hμ : ∀ m, j + 2 ≤ m → m ≤ k → cs.muAct m ≠ 0)
    (hB0 : BgHyp S.d S.L (j + 1) (minSep S.L g.M1) cs.aw (cs.muBg (j + 1)))
    (hBn : ∀ m, j + 2 ≤ m → m ≤ k → BgHyp S.d S.L (j + 1) (minSep S.L g.M1)
      (fun l => cs.aw l * (betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0 /
        betaCanon S.d S.L (cs.beta m) m 0)) (br.elMass (cs.muAct m)))
    (hS : ∀ u ∈ Sdom,
      InUnionDomainR (locGen g Hl j Zc hZc hk) (bgC1 S.d S.L N) (cs.muBg (j + 1))
        (locData g Hl j Zc hZc hk (ou u) (xu u) (hvu u)) ∧
      ∀ m, j + 2 ≤ m → m ≤ k →
        InUnionDomainR (locGen g Hl j Zc hZc hk) (bgC1 S.d S.L N) (br.elMass (cs.muAct m))
          (locData g Hl j Zc hZc hk (ou u) (xu u) (hvu u))) :
    ConvChain Sdom j k (locGen g Hl j Zc hZc hk) X br N where
  β := fun m => betaCanon S.d S.L (cs.beta m) m 0
  a := fun m l => cs.aw l * (betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0 /
    betaCanon S.d S.L (cs.beta m) m 0)
  ν := fun m => cs.muAct m
  e := fun m => (betaCanon S.d S.L (cs.beta (m - 1)) (m - 1) 0 * cs.muAct (m - 1) -
    betaCanon S.d S.L (cs.beta m) m 0 * cs.muAct m) / cs.muAct m
  Dat := fun u _ => locData g Hl j Zc hZc hk (ou u) (xu u) (hvu u)
  φ := fun u m => if m = j + 1 then locBg g Hl j Zc hZc hk cs (ou u) (xu u) (hvu u) else
    bgFieldC (locGen g Hl j Zc hZc hk)
      (fun l => cs.aw l * (betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0 /
        betaCanon S.d S.L (cs.beta m) m 0)) (br.elMass (cs.muAct m)) (bgC0 S.d S.L N)
      (locData g Hl j Zc hZc hk (ou u) (xu u) (hvu u))
  α := fun u m => bgMultC (locGen g Hl j Zc hZc hk)
      (fun l => cs.aw l * (betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0 /
        betaCanon S.d S.L (cs.beta m) m 0)) (br.elMass (cs.muAct m)) (bgC0 S.d S.L N)
      (locData g Hl j Zc hZc hk (ou u) (xu u) (hvu u))
  β_ne := fun m h1 h2 => by
    unfold betaCanon
    exact div_ne_zero (hβ m h1 h2) (pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne S.L)))
  coeff := fun m h1 h2 l => by
    have hb : ∀ q, j + 1 ≤ q → q ≤ k → betaCanon S.d S.L (cs.beta q) q 0 ≠ 0 := fun q hq1 hq2 => by
      unfold betaCanon
      exact div_ne_zero (hβ q hq1 hq2) (pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne S.L)))
    have e1 := hb (m - 1) (by omega) (by omega)
    have e2 := hb m (by omega) h2
    field_simp
  mass := fun m h1 h2 => by
    have := hμ m h1 h2
    field_simp
    ring
  same_h := fun _ _ _ _ _ _ _ => rfl
  el := fun m h1 h2 u hu => by
    have hm : m ≠ j + 1 := by omega
    simp only [hm, ↓reduceIte]
    exact (theorem72 (hBn m h1 h2) (inUnionDomainC_of_R (hBn m h1 h2) ((hS u hu).2 m h1 h2))).2.1.1
  unit := fun m h1 h2 u hu x => by
    by_cases hm : m - 1 = j + 1
    · simp only [hm, ↓reduceIte]
      exact (theorem72 hB0 (inUnionDomainC_of_R hB0 (hS u hu).1)).2.1.1.2 x
    · simp only [hm, ↓reduceIte]
      exact (theorem72 (hBn (m - 1) (by omega) (by omega))
        (inUnionDomainC_of_R (hBn (m - 1) (by omega) (by omega))
          ((hS u hu).2 (m - 1) (by omega) (by omega)))).2.1.1.2 x

/-- **`Re T_{j,j+1} = 𝒜_{j+1}(Z'; ψ)`** (S4): the unconverted action of the chain of the piece is
the main action of the quiet step on the piece, at every configuration of the domain. -/
theorem pieceChain_T (hrem : ∀ i, Hl.rem i = ∅) (hj1 : 1 ≤ j) {U : Type*} (Sdom : Set U) (k : ℕ)
    (br : MassBranch) (X : Region (locGen g Hl j Zc hZc hk)) (hXs : X.sites = Xfine g Hl j Zc)
    (ou : U → OutT N R (locHist Hl M K (j + 1) Zc) (j + 1))
    (xu : U → NewCfg N (locHist Hl M K (j + 1) Zc) j) (hvu : U → EuclideanSpace ℝ (Fin N))
    (hβ : ∀ m, j + 1 ≤ m → m ≤ k → cs.beta m ≠ 0)
    (hμ : ∀ m, j + 2 ≤ m → m ≤ k → cs.muAct m ≠ 0)
    (hB0 : BgHyp S.d S.L (j + 1) (minSep S.L g.M1) cs.aw (cs.muBg (j + 1)))
    (hBn : ∀ m, j + 2 ≤ m → m ≤ k → BgHyp S.d S.L (j + 1) (minSep S.L g.M1)
      (fun l => cs.aw l * (betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0 /
        betaCanon S.d S.L (cs.beta m) m 0)) (br.elMass (cs.muAct m)))
    (hS : ∀ u ∈ Sdom,
      InUnionDomainR (locGen g Hl j Zc hZc hk) (bgC1 S.d S.L N) (cs.muBg (j + 1))
        (locData g Hl j Zc hZc hk (ou u) (xu u) (hvu u)) ∧
      ∀ m, j + 2 ≤ m → m ≤ k →
        InUnionDomainR (locGen g Hl j Zc hZc hk) (bgC1 S.d S.L N) (br.elMass (cs.muAct m))
          (locData g Hl j Zc hZc hk (ou u) (xu u) (hvu u)))
    (hjk : j + 1 ≤ k) {u : U} (hu : u ∈ Sdom) :
    ((pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).T u (j + 1)).re =
      mainActionLoc g Hl j Zc hZc hk cs hrem (ou u) (xu u) (hvu u) := by
  rw [Fluctuation.mainActionLoc_eq_re_actionRegionC g Hl j Zc hZc hk hrem cs hj1 hB0 (ou u) (xu u)
    (hvu u) (inUnionDomainC_of_R hB0 (hS u hu).1) X hXs]
  have hb : betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0 ≠ 0 := by
    unfold betaCanon
    exact div_ne_zero (hβ (j + 1) le_rfl hjk) (pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne S.L)))
  have ha : (fun l => cs.aw l * (betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0 /
      betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0)) = cs.aw :=
    funext fun l => by rw [div_self hb, mul_one]
  simp only [ConvChain.T, pieceChain, ↓reduceIte, ha]

end Piece

section Massless

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The standing hypotheses of Theorem 5.2 for the converted weights in the massless branch: those of
the step and the admissibility of the weights. -/
theorem bgHyp_massless {a a' : ℕ → ℝ} {μ ν : ℝ} (H : BgHyp d L q ϱ a μ)
    (hw : IsAdmissibleWeights q a') : BgHyp d L q ϱ a' (MassBranch.massless.elMass ν) where
  hd := H.hd
  hL := H.hL
  hϱ := H.hϱ
  weights := hw
  mass := le_rfl
  massLe := by simp [MassBranch.elMass]

/-- The real domain at the mass `μ ≥ 0` is contained in the real domain at the mass `0` of the
massless branch. -/
theorem inUnionDomainR_massless {G : GeneratingSet d L N₀ q ϱ} {c₁ μ ν : ℝ} (hμ : 0 ≤ μ)
    {D : BgData G N} (hD : InUnionDomainR G c₁ μ D) :
    InUnionDomainR G c₁ (MassBranch.massless.elMass ν) D := by
  obtain ⟨δ, hδ0, hδc, hDδ⟩ := hD
  refine ⟨δ, hδ0, hδc, ?_⟩
  have h := SmallField.inDomainR_massScale (s := 0) le_rfl hδ0.le
    (μ := MassBranch.massless.elMass ν) (by simp [MassBranch.elMass, hμ]) hDδ
  simpa using h

end Massless

end Balaban.LargeField
