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
(full support `czF m`, weight `τ m`) are the removed clusters and whose light objects are the
boundary couplings `(X, S)` *decorated* by the nonempty set `S` of heavy objects they meet (`near`):
the coupling of the domain `X` depends on the removed members it meets, `b_X(S)`, and its Mayer
weight is `e^{b_X(S)} - 1` (P7 p. 528: "we sum over all clusters and all sets
`{Z_{i₁}, …, Z_{i_q}}` determining the polymer"; `gasDecor_eq`).  The weights are functions of one
internal configuration `Φ ∈ ∏_b Ω_b` (cubes `b`), integrated against the product reference measure
`⨂_b μ_b` of (H-op).

This is the gas with an activation rule of `Gas.lean` (`actGasA`): the light object `(X, S)` is
*active* for a family `Γ` of heavy objects when `S` is exactly the set of members of `Γ` that `X`
meets (`decAct`).  The hole `S₀` (`Ω^c_k ∩ Y_k`, no internal variable) is treated as in
`HoleOperator.lean`: contact and compatibility are through the *charged* supports (full support
minus `S₀`); the polymer of a connected admissible family is the union of the *full* supports, a
hole polymer.

* `decHoleK`: the activity of a hole polymer (`actGasHoleKOp` of the decorated gas);
* `decP`: **the local term `P(X)` of the cluster expansion** (P7 (3.28)): the sum over the clusters
  of hole polymers (Ursell function) whose union of *full* supports is `X` (`PY` localized on the
  full support; `logSeries = Σ_X P(X)` by `logSeries_eq_sum_PY`).
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

/-- **The activation rule of the decorated couplings**: `(X, S)` is active for the family `Γ` of
heavy objects iff `S` is the set of members of `Γ` that `X` meets (`gasDecor_eq`). -/
def decAct (near : Xt → Zt → Prop) (y : DecObj near) (Γ : Finset Zt) : Prop :=
  y.1.2 = Γ.filter (near y.1.1)

/-- **The full support of a decorated light object** `(X, S)`: the domain support `cxF X` together
with the full supports of its decoration. -/
def decCyF (czF : Zt → Finset B) (cxF : Xt → Finset B) (near : Xt → Zt → Prop) (y : DecObj near) :
    Finset B :=
  cxF y.1.1 ∪ y.1.2.biUnion czF

variable {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]

/-- **The activity of a hole polymer** (P7 (3.27); LFR Lemma III.10.5): the expectation, under the
product reference measure `⨂_b μ_b`, of the sum over the connected (through charged contacts)
admissible families of the decorated gas whose union of full supports is `X`, of the product of the
weights `τ_m(Φ)`, `e^{b_X(S)(Φ)} - 1`. -/
def decHoleK (H : SimpleGraph B) (S₀ : Finset B) (czF : Zt → Finset B) (cxF : Xt → Finset B)
    (near : Xt → Zt → Prop) (τ : Zt → (∀ b, Ω b) → ℂ) (b : Xt → Finset Zt → (∀ b, Ω b) → ℂ)
    (μ : ∀ b, Measure (Ω b)) (X : HolePolymer H S₀) : ℂ :=
  actGasHoleKOp H S₀ (decCyF czF cxF near) czF (decAct near)
    (fun y => decCyF czF cxF near y \ S₀) (fun m => czF m \ S₀) (fun y Φ => b y.1.1 y.1.2 Φ) τ μ X

/-- **The local term `P(X)` of the cluster expansion** (P7 (3.28); LFR Lemma III.10.5): the sum over
the clusters of hole polymers (with their Ursell function, `PY`) whose union of full supports is
`X`.  Incompatibility of hole polymers is the meeting of their charged supports. -/
def decP (H : SimpleGraph B) (S₀ : Finset B) (czF : Zt → Finset B) (cxF : Xt → Finset B)
    (near : Xt → Zt → Prop) (τ : Zt → (∀ b, Ω b) → ℂ) (b : Xt → Finset Zt → (∀ b, Ω b) → ℂ)
    (μ : ∀ b, Measure (Ω b)) (X : Finset B) : ℂ :=
  PY (shareBlock (holeSupp H S₀)) (fun Y : HolePolymer H S₀ => Y.1)
    (decHoleK H S₀ czF cxF near τ b μ) X

end Dec

end Balaban.LargeField.G0
