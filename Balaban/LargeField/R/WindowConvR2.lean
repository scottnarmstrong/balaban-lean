/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysParams
public import Balaban.LargeField.R.WindowConvUniform
public import Balaban.LargeField.Def7

/-!
# The conversion chain of a window piece without a mass switch (ruling R2)

`notes/phase1/astra/P7CONV.md` §3.2 (41) and §3.5.  Before ruling R2 the chain `pieceChain` of a
piece started with the local background `locBg` at the mass `cs.mu (j + 1)` (zero below `k₀`)
and continued with backgrounds of the mass convention `br` at the action masses `cs.muAct n`;
the first step was exceptional (the coherence (41) failed below `k₀`) and a window crossing `k₀`
carried a mass switch (`hswitch` of `PieceWindowSetup.window_uniform_of_parts`).  Under R2 the
local background is solved with the background mass `cs.muBg`, and route R-YM′ takes
`muBg = muAct` (`Def7.FieldClauses.muBg_eq`).  Then:

* `pieceChain_a_first`: the first coefficient sequence is `cs.aw`;
* `pieceChain_φ_first`: under the coherence (41) `cs.muBg (j+1) = br.elMass (cs.muAct (j+1))`,
  the first background of the chain is the background of the branch `br` at the first scale;
* `pieceChain_φ`: then every background of the chain is the background of the branch at its own
  coefficients, mass and datum (the typing premise of `PieceWindowSetup.exists_hsource_of_flow`);
* `pieceChain_el_first`, `pieceChain_el`: the first background solves the Euler-Lagrange system of
  the branch too, so every background of the chain, `j + 1 ≤ n ≤ k`, solves the system of one
  branch (no switch);
* `Def7.FieldClauses.muBg_coherent_complete`: (41) for the complete branch from the field clauses
  of Def-7.

With the complete branch the mass-convention residual of the window conversion is therefore
absent: the intermediate actions `Q` and `R` of `window_uniform_of_parts` can be taken equal,
`Kswitch = 0` (`PieceWindowSetup.window_uniform_of_parts_noSwitch`), and the massless-to-complete
comparison of `P7CONV.md` §3.5 (55)-(56) is not used.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory Balaban.LargeField.ActionConv

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
  {hB0 : BgHyp S.d S.L (j + 1) (minSep S.L g.M1) cs.aw (cs.muBg (j + 1))}
  {hBn : ∀ m, j + 2 ≤ m → m ≤ k → BgHyp S.d S.L (j + 1) (minSep S.L g.M1)
    (fun l => cs.aw l * (betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0 /
      betaCanon S.d S.L (cs.beta m) m 0)) (br.elMass (cs.muAct m))}
  {hS : ∀ u ∈ Sdom,
    InUnionDomainR (locGen g Hl j Zc hZc hk) (bgC1 S.d S.L N) (cs.muBg (j + 1))
      (locData g Hl j Zc hZc hk (ou u) (xu u) (hvu u)) ∧
    ∀ m, j + 2 ≤ m → m ≤ k →
      InUnionDomainR (locGen g Hl j Zc hZc hk) (bgC1 S.d S.L N)
        (br.elMass (cs.muAct m))
        (locData g Hl j Zc hZc hk (ou u) (xu u) (hvu u))}

/-- **(41) for the complete branch in the class** (ruling R2): under the field clauses of Def-7
(`muBg_eq`, `muAct_eq`) the background mass is the complete-branch mass of the action mass at
every scale `q ≤ k`. -/
theorem _root_.Balaban.LargeField.Def7.FieldClauses.muBg_coherent_complete {k0 k' : ℕ}
    {m₁ N' : ℕ} {ϱ : ℝ} {sf : Def7.SFData S.d S.L m₁ k' N' ϱ} {hv : EuclideanSpace ℝ (Fin N')}
    (h : Def7.FieldClauses S k0 k' cs sf hv) {q : ℕ} (hq : q ≤ k') :
    cs.muBg q = MassBranch.complete.elMass (cs.muAct q) := by
  rw [h.muBg_eq q hq, h.muAct_eq q hq]
  rfl

/-- The first coefficient sequence of the chain is `cs.aw`. -/
theorem pieceChain_a_first (hjk : j + 1 ≤ k) :
    (pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).a (j + 1) =
      cs.aw := by
  have hb : betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0 ≠ 0 := by
    unfold betaCanon
    exact div_ne_zero (hβ (j + 1) le_rfl hjk) (pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne S.L)))
  funext l
  simp only [pieceChain, div_self hb, mul_one]

/-- **The first background under the coherence (41)**: it is the background of the branch `br`
with the chain's first coefficients and mass. -/
theorem pieceChain_φ_first (hjk : j + 1 ≤ k)
    (hcoh : cs.muBg (j + 1) = br.elMass (cs.muAct (j + 1))) (u : U) :
    (pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).φ u (j + 1) =
      bgFieldC (locGen g Hl j Zc hZc hk)
        ((pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).a (j + 1))
        (br.elMass
          ((pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).ν (j + 1)))
        (bgC0 S.d S.L N)
        ((pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).Dat u
          (j + 1)) := by
  rw [pieceChain_a_first hjk]
  simp only [pieceChain, ↓reduceIte]
  rw [← hcoh]
  rfl

/-- **Every background of the chain is the background of the branch** at its own coefficients,
mass and datum, under the coherence (41) at the first scale (ruling R2).  For the complete branch
this is the typing premise on the backgrounds of `PieceWindowSetup.exists_hsource_of_flow` at
every scale, including the first. -/
theorem pieceChain_φ (hcoh : cs.muBg (j + 1) = br.elMass (cs.muAct (j + 1)))
    {nn : ℕ} (h1 : j + 1 ≤ nn) (h2 : nn ≤ k) (u : U) :
    (pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).φ u nn =
      bgFieldC (locGen g Hl j Zc hZc hk)
        ((pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).a nn)
        (br.elMass
          ((pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).ν nn))
        (bgC0 S.d S.L N)
        ((pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).Dat u nn) := by
  rcases Nat.eq_or_lt_of_le h1 with e | hlt
  · subst e
    exact pieceChain_φ_first h2 hcoh u
  · have hne : nn ≠ j + 1 := by omega
    simp only [pieceChain, hne, ↓reduceIte]

/-- **The first background solves the Euler-Lagrange system of the branch** under the coherence
(41), with the chain's multiplier. -/
theorem pieceChain_el_first (hjk : j + 1 ≤ k)
    (hcoh : cs.muBg (j + 1) = br.elMass (cs.muAct (j + 1))) {u : U} (hu : u ∈ Sdom) :
    IsEL (locGen g Hl j Zc hZc hk)
      ((pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).a (j + 1))
      (br.elMass
        ((pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).ν (j + 1)))
      ((pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).Dat u (j + 1))
      ((pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).φ u (j + 1))
      ((pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).α u (j + 1)) := by
  have hel := (theorem72 hB0 (inUnionDomainC_of_R hB0 (hS u hu).1)).2.1.1
  simp only [pieceChain, ↓reduceIte]
  have hb : betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0 ≠ 0 := by
    unfold betaCanon
    exact div_ne_zero (hβ (j + 1) le_rfl hjk) (pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne S.L)))
  have ha : (fun l => cs.aw l * (betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0 /
      betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0)) = cs.aw := by
    funext l; rw [div_self hb, mul_one]
  rw [ha, ← hcoh]
  exact hel

/-- **No mass switch along the chain** (ruling R2): under the coherence (41) every background of
the chain, `j + 1 ≤ n ≤ k`, solves the Euler-Lagrange system of the one branch `br` with the
chain's coefficients and mass. -/
theorem pieceChain_el (hcoh : cs.muBg (j + 1) = br.elMass (cs.muAct (j + 1)))
    {nn : ℕ} (h1 : j + 1 ≤ nn) (h2 : nn ≤ k) {u : U} (hu : u ∈ Sdom) :
    IsEL (locGen g Hl j Zc hZc hk)
      ((pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).a nn)
      (br.elMass
        ((pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).ν nn))
      ((pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).Dat u nn)
      ((pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).φ u nn)
      ((pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).α u nn) := by
  rcases Nat.eq_or_lt_of_le h1 with e | hlt
  · subst e
    exact pieceChain_el_first h2 hcoh hu
  · exact (pieceChain g Hl j Zc hZc hk cs Sdom k br X ou xu hvu hβ hμ hB0 hBn hS).el nn hlt h2 u hu

namespace ActionConv

variable {d L N₀ K' N' : ℕ} [NeZero N₀] [NeZero L] {U' : Type*} {S' : Set U'} {ι : Type*}
  [Fintype ι] {sc : ι → ℕ} {k1 k' : ℕ}

/-- **The window comparison without a mass switch** (ruling R2): when every background of a piece
solves the system of one branch (`pieceChain_el`), the intermediate action of the mass switch is
the coefficient-adjusted action itself, and the switch premise `hswitch` of
`window_uniform_of_parts` holds with `R = Q` and `Kswitch = 0`. -/
theorem PieceWindowSetup.window_uniform_of_parts_noSwitch
    (W : PieceWindowSetup d L N₀ K' N' S' ι sc k1 k')
    (P Q : ι → U' → ℂ) (Kpair Kcoef Kread : ℝ)
    (hpair : ∀ i, ∀ u ∈ S',
      ‖(W.chain i).T u k' - P i u‖ ≤ Kpair * W.mcount i)
    (hcoef : ∀ i, ∀ u ∈ S',
      ‖P i u - Q i u‖ ≤ Kcoef * W.mcount i)
    (hread : ∀ i, ∀ u ∈ S',
      ‖Q i u - (W.βk : ℂ) *
        actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)‖ ≤
        Kread * W.mcount i) :
    ∀ i, ∀ u ∈ S',
      ‖(W.chain i).T u k' - (W.βk : ℂ) *
        actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)‖ ≤
          (Kpair + Kcoef + Kread) * W.mcount i := by
  have h := W.window_uniform_of_parts P Q Q Kpair Kcoef 0 Kread hpair hcoef
    (fun i u _ => by simp) hread
  intro i u hu
  simpa using h i u hu

end ActionConv

end Balaban.LargeField
