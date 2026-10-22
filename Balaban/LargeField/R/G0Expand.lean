/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.HoleOperator
public import Balaban.Polymer.Local

/-!
# G0: the cluster expansion of the decorated operator gas with a hole

P7 (3.27)–(3.28), printed p. 528; LFR Lemma III.10.5 (`notes/phase1/LF-RECONSTRUCTION.md`
§III.10.3).  The bracket of P7 (3.26) is the partition function of a gas whose heavy objects `m`
(support `czF m`, weight `τ m`) are the removed clusters and whose light objects are the boundary
couplings `(X, S)` *decorated* by the nonempty set `S` of heavy objects they meet (`near`): the
coupling of the domain `X` depends on the removed members it meets, `b_X(S)`, and its Mayer weight
is `e^{b_X(S)} - 1` (P7 p. 528: "we sum over all clusters and all sets `{Z_{i₁}, …, Z_{i_q}}`
determining the polymer"; `gasDecor_eq`).  The weights are functions of one internal
configuration `Φ ∈ Ξ`, integrated against one reference measure `μ` ((H-op); the integral of the
product, `gasR4DecorOp_eq`).

The hole `S₀` (`Ω^c_k ∩ Y_k`, no internal variable) is treated as in `HoleOperator.lean`: two
objects are in contact when their *charged* supports (full support minus `S₀`) meet; the polymer of
a connected admissible family is the union of the *full* supports, a hole polymer.  The
admissibility of a family is that of `gasDecor_eq`: the heavy objects are pairwise compatible
(disjoint compatibility supports `czA`, the supports `S(𝒞)` of Definition III.10.3), and every
light `(X, S)` of the family has `S` equal to the set of heavy objects of the family that it
meets.

* `decHoleAct`, `decHoleK`: the activity integrand and the activity (expectation over `μ`) of a hole
  polymer: the sum over the connected admissible families whose charged union is its charged
  support and whose full union is the polymer;
* `decP`: **the local term `P(X)` of the cluster expansion** (P7 (3.28)): the sum over the clusters
  of hole polymers (Ursell function) whose union of *full* supports is `X`; `logSeries = Σ_X P(X)`
  (`logSeries_eq_sum_PY`, with the full support as localization).

Only definitions; the identity `E Ξ = exp Σ_X P(X)` and the bounds are the convergence items
(G1, G3, G4 of `/home/scott/Balaban-scratch/orch/CLOSING-A.md`).
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset MeasureTheory Balaban.Polymer

namespace Balaban.LargeField.G0

section Dec

variable {B Zt Xt : Type*} [Fintype B] [Fintype Zt] [Fintype Xt]

/-- **The decorated light objects** `(X, S)`: a domain `X` and a nonempty set `S` of heavy objects
that it meets (P7 p. 528). -/
def DecObj (near : Xt → Zt → Prop) : Type _ :=
  {p : Xt × Finset Zt // p.2.Nonempty ∧ ∀ m ∈ p.2, near p.1 m}

noncomputable instance (near : Xt → Zt → Prop) : Fintype (DecObj near) := by
  unfold DecObj; infer_instance

/-- **The full supports** of the elementary objects: `czF m` for a heavy object, the domain support
`cxF X` together with the supports of its decoration for a light object `(X, S)`. -/
def decSuppF (czF : Zt → Finset B) (cxF : Xt → Finset B) (near : Xt → Zt → Prop) :
    Zt ⊕ DecObj near → Finset B :=
  Sum.elim czF (fun y => cxF y.1.1 ∪ y.1.2.biUnion czF)

/-- **The charged supports**: the full supports minus the hole `S₀`. -/
def decSupp (S₀ : Finset B) (czF : Zt → Finset B) (cxF : Xt → Finset B) (near : Xt → Zt → Prop) :
    Zt ⊕ DecObj near → Finset B :=
  fun t => decSuppF czF cxF near t \ S₀

/-- **Admissibility of a family** (`gasDecor_eq`): the heavy objects have pairwise disjoint
compatibility supports `czA`, and each light object `(X, S)` of the family is decorated by exactly
the heavy objects of the family that `X` meets. -/
def decAdm (czA : Zt → Finset B) (near : Xt → Zt → Prop) (D : Finset (Zt ⊕ DecObj near)) : Prop :=
  (∀ m ∈ D.toLeft, ∀ m' ∈ D.toLeft, m ≠ m' → Disjoint (czA m) (czA m')) ∧
    ∀ y ∈ D.toRight, y.1.2 = D.toLeft.filter (near y.1.1)

variable {Ξ : Type*} [MeasurableSpace Ξ]

/-- **The weights at the internal configuration `Φ`**: `τ_m(Φ)` for a heavy object,
`e^{b_X(S)(Φ)} - 1` for a light object `(X, S)` (the Mayer expansion of `exp ℬ''`). -/
def decW (near : Xt → Zt → Prop) (τ : Zt → Ξ → ℂ) (b : Xt → Finset Zt → Ξ → ℂ) (Φ : Ξ) :
    Zt ⊕ DecObj near → ℂ :=
  Sum.elim (fun m => τ m Φ) (fun y => Complex.exp (b y.1.1 y.1.2 Φ) - 1)

/-- **The activity integrand of a hole polymer `X`**: the sum, over the connected (through charged
contacts) admissible families whose charged union is the charged support of `X` and whose full
union is `X`, of the product of the weights at `Φ`. -/
def decHoleAct (H : SimpleGraph B) (S₀ : Finset B) (czA czF : Zt → Finset B)
    (cxF : Xt → Finset B) (near : Xt → Zt → Prop) (τ : Zt → Ξ → ℂ) (b : Xt → Finset Zt → Ξ → ℂ)
    (X : HolePolymer H S₀) (Φ : Ξ) : ℂ :=
  ∑ C ∈ Cfam (decSupp S₀ czF cxF near) (decAdm czA near) (holeSupp H S₀ X),
    if unionCs (decSuppF czF cxF near) C = X.1 then ∏ t ∈ C, decW near τ b Φ t else 0

/-- **The activity of a hole polymer** (P7 (3.27)): the expectation of the activity integrand under
the reference measure `μ` of the internal variables ((H-op)). -/
def decHoleK (H : SimpleGraph B) (S₀ : Finset B) (czA czF : Zt → Finset B)
    (cxF : Xt → Finset B) (near : Xt → Zt → Prop) (τ : Zt → Ξ → ℂ) (b : Xt → Finset Zt → Ξ → ℂ)
    (μ : Measure Ξ) (X : HolePolymer H S₀) : ℂ :=
  ∫ Φ, decHoleAct H S₀ czA czF cxF near τ b X Φ ∂μ

/-- **The local term `P(X)` of the cluster expansion** (P7 (3.28); LFR Lemma III.10.5): the sum over
the clusters of hole polymers (with their Ursell function, `PY`) whose union of full supports is
`X`.  Incompatibility of hole polymers is the meeting of their charged supports. -/
def decP (H : SimpleGraph B) (S₀ : Finset B) (czA czF : Zt → Finset B) (cxF : Xt → Finset B)
    (near : Xt → Zt → Prop) (τ : Zt → Ξ → ℂ) (b : Xt → Finset Zt → Ξ → ℂ) (μ : Measure Ξ)
    (X : Finset B) : ℂ :=
  PY (shareBlock (holeSupp H S₀)) (fun Y : HolePolymer H S₀ => Y.1)
    (decHoleK H S₀ czA czF cxF near τ b μ) X

end Dec

end Balaban.LargeField.G0
