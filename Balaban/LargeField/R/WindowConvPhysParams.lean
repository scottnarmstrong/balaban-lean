/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PieceChain
public import Balaban.LargeField.R.WindowConvCoeff

/-!
# Terminal parameters of an actual window piece

The chain of a physical piece retains its local datum. Its terminal coupling and mass
are the fine-unit versions of the scale parameters. The block coefficient retains
the originating coupling times the originating weight.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField.ActionConv

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ}
  {k0 M K N : ℕ} [NeZero M] [NeZero S.L]
  {g : Geo S n R M} {Hl : RegionHistory S n R k0 K}
  {j : ℕ} {Zc : Finset (Torus S.d (n (j + 1)))}
  {hZc : Zc ∈ comps (S.omega (j + 1)) (Hl.F.Zp (j + 1))}
  {hk : j + 1 ≤ K} {cs : OpConsts}
  {U : Type*} {Sdom : Set U} {k : ℕ} {br : MassBranch}
  {X : Region (locGen g Hl j Zc hZc hk)}
  {ou : U → OutT N R (locHist Hl M K (j + 1) Zc) (j + 1)}
  {xu : U → NewCfg N (locHist Hl M K (j + 1) Zc) j}
  {hvu : U → EuclideanSpace ℝ (Fin N)}
  {hβ : ∀ m, j + 1 ≤ m → m ≤ k → cs.beta m ≠ 0}
  {hμ : ∀ m, j + 2 ≤ m → m ≤ k → cs.muAct m ≠ 0}
  {hB0 : BgHyp S.d S.L (j + 1) (minSep S.L g.M1) cs.aw (cs.mu (j + 1))}
  {hBn : ∀ m, j + 2 ≤ m → m ≤ k → BgHyp S.d S.L (j + 1) (minSep S.L g.M1)
    (fun l => cs.aw l * (betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0 /
      betaCanon S.d S.L (cs.beta m) m 0)) (br.elMass (cs.muAct m))}
  {hS : ∀ u ∈ Sdom,
    InUnionDomainR (locGen g Hl j Zc hZc hk) (bgC1 S.d S.L N) (cs.mu (j + 1))
      (locData g Hl j Zc hZc hk (ou u) (xu u) (hvu u)) ∧
    ∀ m, j + 2 ≤ m → m ≤ k →
      InUnionDomainR (locGen g Hl j Zc hZc hk) (bgC1 S.d S.L N)
        (br.elMass (cs.muAct m))
        (locData g Hl j Zc hZc hk (ou u) (xu u) (hvu u))}

/-- The terminal fine-unit normalization and originating block coefficient of the
actual chain. This supplies the coefficient part of the window read comparison. -/
theorem pieceChain_terminal_parameters
    (C : ConvChain Sdom j k (locGen g Hl j Zc hZc hk) X br N)
    (hC : C = pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu
      hβ hμ hB0 hBn hS) (hjk : j + 1 ≤ k) :
    C.β k = betaCanon S.d S.L (cs.beta k) k 0 ∧
    C.ν k = cs.muAct k ∧
    (∀ u : U, C.Dat u k = locData g Hl j Zc hZc hk (ou u) (xu u) (hvu u)) ∧
    (∀ ℓ, C.β k * C.a k ℓ =
      betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0 * cs.aw ℓ) := by
  subst C
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro u
    rfl
  · intro ℓ
    have hstart : betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0 ≠ 0 := by
      unfold betaCanon
      exact div_ne_zero (hβ (j + 1) le_rfl hjk)
        (pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne S.L)))
    have hcoeff := (pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu
      hβ hμ hB0 hBn hS).coeff_from_start hjk le_rfl ℓ
    simpa only [pieceChain, div_self hstart, mul_one] using hcoeff.symm

/-- The initial and later backgrounds of a physical piece use different declared
mass conventions. At the terminal scale the later branch is fixed by `br`. -/
theorem pieceChain_backgrounds
    (C : ConvChain Sdom j k (locGen g Hl j Zc hZc hk) X br N)
    (hC : C = pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu
      hβ hμ hB0 hBn hS) (hjk : j + 2 ≤ k) (u : U) :
    C.φ u (j + 1) = locBg g Hl j Zc hZc hk cs (ou u) (xu u) (hvu u) ∧
    C.φ u k =
      bgFieldC (locGen g Hl j Zc hZc hk)
        (fun ℓ => cs.aw ℓ *
          (betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0 /
            betaCanon S.d S.L (cs.beta k) k 0))
        (br.elMass (cs.muAct k)) (bgC0 S.d S.L N)
        (locData g Hl j Zc hZc hk (ou u) (xu u) (hvu u)) := by
  subst C
  constructor
  · simp only [pieceChain, ↓reduceIte]
  · have hne : k ≠ j + 1 := by omega
    simp only [pieceChain, hne, ↓reduceIte]

end Balaban.LargeField
