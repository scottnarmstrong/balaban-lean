/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RGasRepR4Decor

/-!
# Decorated gas before the common internal integration

P7 (3.26)–(3.28), printed pp. 527–528, expands the removed-cluster sum
with its boundary terms before integrating the common internal variables.
The identity below integrates `gasR4Decor_eq` over the single product
reference measure of (H-op).  In particular it does not replace an integral
of a product by a product of integrals; that later step requires disjoint
dependence supports and the hypotheses of `Polymer.integral_prod_depOn`.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset MeasureTheory Balaban.Polymer

namespace Balaban.LargeField

variable {B Zt Xt : Type*} [Fintype B] [Fintype Zt] [Fintype Xt]
  {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]

set_option hygiene false in
local notation "Dec" => {p : Xt × Finset Zt // p.2.Nonempty ∧ ∀ m ∈ p.2, near p.1 m}

/-- The shared-internal-variable form of the decorated P7 (3.26) gas identity.
Every heavy and light weight on the right is evaluated at the same `Φ`.
The measure is the (H-op) product reference probability measure when each
`μ b` is a probability measure. -/
theorem gasR4DecorOp_eq
    (cz : Zt → Finset B) (cx : Xt → Finset B) (near : Xt → Zt → Prop)
    (τ : Zt → (∀ b, Ω b) → ℂ)
    (old fresh : Xt → Finset Zt → (∀ b, Ω b) → ℂ)
    (kept : Xt → (∀ b, Ω b) → ℂ)
    (μ : ∀ b, Measure (Ω b))
    (hz : ∀ m, (cz m).Nonempty)
    (hnear : ∀ x m, near x m → ¬ Disjoint (cx x) (cz m))
    (hbase : ∀ x Φ, old x ∅ Φ = kept x Φ)
    (hfresh : ∀ x Φ, fresh x ∅ Φ = 0) :
    (∫ Φ, ∑ Γ ∈ univ.filter (fun Γ : Finset Zt =>
        ∀ m ∈ Γ, ∀ m' ∈ Γ, m ≠ m' → Disjoint (cz m) (cz m')),
      (∏ m ∈ Γ, τ m Φ) *
        Complex.exp (∑ x, r4Coupling
          (fun x S => old x S Φ) (fun x S => fresh x S Φ)
          (fun x => kept x Φ) x (Γ.filter (near x))) ∂(hOpMeasure μ)) =
      ∫ Φ, Xi (shareBlock (Subtype.val : NePoly B → Finset B))
        (polyAct (Sum.elim cz (fun y : Dec => cx y.1.1 ∪ y.1.2.biUnion cz))
          (fun D => (∀ m ∈ D.toLeft, ∀ m' ∈ D.toLeft,
              m ≠ m' → Disjoint (cz m) (cz m')) ∧
            ∀ y ∈ D.toRight, y.1.2 = D.toLeft.filter (near y.1.1))
          (Sum.elim (fun m => τ m Φ) (fun y : Dec =>
            Complex.exp (r4Coupling
              (fun x S => old x S Φ) (fun x S => fresh x S Φ)
              (fun x => kept x Φ) y.1.1 y.1.2) - 1))) ∂(hOpMeasure μ) := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
  exact gasR4Decor_eq cz cx near (fun m => τ m Φ)
    (fun x S => old x S Φ) (fun x S => fresh x S Φ)
    (fun x => kept x Φ) hz hnear (fun x => hbase x Φ) (fun x => hfresh x Φ)

end Balaban.LargeField
