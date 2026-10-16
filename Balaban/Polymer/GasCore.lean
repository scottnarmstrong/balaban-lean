module

public import Balaban.Polymer.GasBound

/-!
# GAS with compatibility on cores (blocker 4, `notes/phase1/VMOD-43.md` §3)

For a fixed core map `core : Finset B → Finset B` (for the removed-component gas,
`core X = X \ retained`), the landed abstract gas of `Gas.lean` and `GasBound.lean` is applied to the
couplings with charged support `core (cy y)` and the heavy objects with support `core (zs z)`.
Heavy objects are then compatible when their *cores* are disjoint, a coupling is attached to a heavy
object whose core it meets, and two elementary objects are in contact when their cores meet.  Both
landed theorems hold verbatim in this setting; the statements below are their instances.

The size step: the hypothesis `hG3` of `gas_activity_bound_core` is the subadditivity of the size
over core-connected admissible families.  For the covering size of `Fluctuation/SizeMod*.lean`
this is `G3_dcov` (one core contact: the intersection contains a `π_k`-cell of `Ω`, that is, a cell
of the core) folded along the contact tree by `dcovMod_union_range_le` and
`dcovMod_biUnion_le_of_activeTree` (`SizeModUnionTree.lean`).  Its transfer to `Finset B` is not
done here.  Core incidence with an expectation over the charged variables is `Polymer/HoleOperator.lean`
(hole `S₀`, charged supports `Z \ S₀`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer

section Core

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {cy : Yt → Finset B} {zs cr : Zt → Finset B} {β : Yt → ℂ} {τ : Zt → ℂ}

/-- **GAS with compatibility on cores (identity).**  Heavy objects are compatible when the cores
`core (zs z)` are disjoint, and the polymers are the connected clusters for contact of cores. -/
theorem gas_eq_core (core : Finset B → Finset B) (hz : ∀ z, (core (zs z)).Nonempty)
    (hcr : ∀ z, cr z ⊆ core (zs z)) :
    gasXi (fun y => core (cy y)) (fun z => core (zs z)) cr β τ =
      Xi (shareBlock (Subtype.val : NePoly B → Finset B))
        (gasK (fun y => core (cy y)) (fun z => core (zs z)) cr β τ) :=
  gas_eq β τ hz hcr

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- The admissibility of a family for the gas on cores: the heavy objects have pairwise disjoint
cores and every coupling has a core meeting the core `cr z` of a heavy object of the family. -/
theorem gasA_core_iff (core : Finset B → Finset B) (D : Finset (Yt ⊕ Zt)) :
    gasA (fun y => core (cy y)) (fun z => core (zs z)) cr D ↔
      (∀ z ∈ D.toRight, ∀ z' ∈ D.toRight, z ≠ z' → Disjoint (core (zs z)) (core (zs z'))) ∧
        ∀ y ∈ D.toLeft, ∃ z ∈ D.toRight, ¬ Disjoint (core (cy y)) (cr z) :=
  Iff.rfl

/-- **GAS (activity bound) with compatibility on cores.**  `gas_activity_bound` for the supports
`core (cy y)`, `core (zs z)`; all hypotheses are about cores. -/
theorem gas_activity_bound_core (core : Finset B → Finset B)
    {d : Finset B → ℝ} {B0 κ' κ'' c c1 c2 p h : ℝ}
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c)
    (hc1 : 0 ≤ c1) (hp : 0 ≤ p) (hd : ∀ Y, 0 ≤ d Y) (hz : ∀ z, (core (zs z)).Nonempty)
    (hcr : ∀ z, cr z ⊆ core (zs z))
    (hB : ∀ y, ‖β y‖ ≤ B0 * Real.exp (-κ'' * d (core (cy y))))
    (hτ : ∀ z, ‖τ z‖ ≤ Real.exp (-p - h * (core (zs z)).card))
    (hzd : ∀ z, d (core (zs z)) ≤ c2 * (core (zs z)).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt),
      ConnSet (gasCs (fun y => core (cy y)) (fun z => core (zs z))) C →
      gasA (fun y => core (cy y)) (fun z => core (zs z)) cr C →
      d (unionCs (gasCs (fun y => core (cy y)) (fun z => core (zs z))) C) ≤
        ∑ t ∈ C, d (gasCs (fun y => core (cy y)) (fun z => core (zs z)) t) +
          c * ((C.card : ℝ) - 1))
    {K0' K0'' : ℝ} (hK0' : 0 ≤ K0')
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ core (cy y)),
      Real.exp (-(κ'' - κ') * d (core (cy y))) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ((Finset.univ.filter (fun z => b ∈ core (zs z) ∧ (core (zs z)).card = v)).card : ℝ) ≤
        K0'' ^ v)
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' + κ' * (c2 + c) + c1 + 3 +
      Real.log K0'' ≤ h)
    (X : NePoly B) (hG1 : (X.1.card : ℝ) ≤ c1 * (1 + d X.1)) :
    ‖gasK (fun y => core (cy y)) (fun z => core (zs z)) cr β τ X‖ ≤
      3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d X.1) :=
  gas_activity_bound hB0 hκ' hκ'' hc hc1 hp hd hz hcr hB hτ hzd hG3 hK0' hent hK1 hcount hh X hG1

end Core

end Balaban.Polymer
