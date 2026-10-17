/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RGasRepDecor
public import Balaban.LargeField.R.RGasRepR4Measure

/-!
# Decorated boundary couplings of R

P7 (3.26), printed p. 527, groups the old boundary terms that meet removed
components with the new boundary terms from the re-expansion (3.22)–(3.25),
printed pp. 526–527.  For a domain `X` and the set `S` of removed objects it
meets, the resulting coupling is
`ℬ(X, 𝔸′ ∪ S) − ℬ̂(X; 𝔸′) + ℬ′_X(S)`.

`r4Coupling` records this algebraic formula.  Its `fresh` argument is the
localized term `ℬ′_X(S)`; the source describes its construction by localization
and resummation rather than giving a unique coefficient formula.  The theorem
below applies `gasDecor_eq` to the literal coupling.  It is pointwise in the
output field and the internal variables; it does not integrate separate heavy
weights before the gas expansion.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset Balaban.Polymer

namespace Balaban.LargeField

variable {Xt Zt : Type*}

/-- The decorated coupling of P7 (3.26), with `fresh = ℬ′` from
(3.22)–(3.25). -/
def r4Coupling (old fresh : Xt → Finset Zt → ℂ) (kept : Xt → ℂ)
    (x : Xt) (S : Finset Zt) : ℂ :=
  old x S - kept x + fresh x S

/-- Unfolding the approved formula for `b_X(S)`. -/
theorem r4Coupling_apply (old fresh : Xt → Finset Zt → ℂ) (kept : Xt → ℂ)
    (x : Xt) (S : Finset Zt) :
    r4Coupling old fresh kept x S = old x S - kept x + fresh x S := rfl

/-- The coupling vanishes for no removed members, as required by the
decorated Mayer expansion. -/
theorem r4Coupling_empty (old fresh : Xt → Finset Zt → ℂ) (kept : Xt → ℂ)
    (hbase : ∀ x, old x ∅ = kept x) (hfresh : ∀ x, fresh x ∅ = 0) (x : Xt) :
    r4Coupling old fresh kept x ∅ = 0 := by
  simp only [r4Coupling_apply, hbase x, hfresh x, sub_self, zero_add]

section Gas

variable {B : Type*} [Fintype B] [Fintype Zt] [Fintype Xt]
  (cz : Zt → Finset B) (cx : Xt → Finset B) (near : Xt → Zt → Prop)
  (τ : Zt → ℂ) (old fresh : Xt → Finset Zt → ℂ) (kept : Xt → ℂ)

set_option hygiene false in
local notation "Dec" => {p : Xt × Finset Zt // p.2.Nonempty ∧ ∀ m ∈ p.2, near p.1 m}

/-- P7 (3.26)–(3.27), printed pp. 527–528: the pointwise gas identity
for the approved decorated boundary coupling.  The heavy objects and
their supports may be chosen to be the removed clusters of Definition
III.10.3; `gas_identity` identifies their compatible families with the
removed parts of admissible histories. -/
theorem gasR4Decor_eq (hz : ∀ m, (cz m).Nonempty)
    (hnear : ∀ x m, near x m → ¬ Disjoint (cx x) (cz m))
    (hbase : ∀ x, old x ∅ = kept x) (hfresh : ∀ x, fresh x ∅ = 0) :
    ∑ Γ ∈ univ.filter (fun Γ : Finset Zt =>
        ∀ m ∈ Γ, ∀ m' ∈ Γ, m ≠ m' → Disjoint (cz m) (cz m')),
      (∏ m ∈ Γ, τ m) *
        Complex.exp (∑ x, r4Coupling old fresh kept x (Γ.filter (near x))) =
      Xi (shareBlock (Subtype.val : NePoly B → Finset B))
        (polyAct (Sum.elim cz (fun y : Dec => cx y.1.1 ∪ y.1.2.biUnion cz))
          (fun D => (∀ m ∈ D.toLeft, ∀ m' ∈ D.toLeft,
              m ≠ m' → Disjoint (cz m) (cz m')) ∧
            ∀ y ∈ D.toRight, y.1.2 = D.toLeft.filter (near y.1.1))
          (Sum.elim τ (fun y : Dec =>
            Complex.exp (r4Coupling old fresh kept y.1.1 y.1.2) - 1))) :=
  gasDecor_eq cz cx near τ (r4Coupling old fresh kept) hz hnear
    (r4Coupling_empty old fresh kept hbase hfresh)

end Gas

end Balaban.LargeField
