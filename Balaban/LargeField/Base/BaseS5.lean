module

public import Balaban.LargeField.Base.BaseSmallField
import Mathlib.Tactic.Linarith

/-!
# The rotation form (S5) of the base kernel (BASE-KERNEL §5, Definition II.5.7 (S5), Lemma II.7.7 (e))

`BaseS5 ε a T` is the *target* statement of §5 for a base kernel `T` at the localized history `a`
in regime (A): `K_0 = ∑_w 1_{A_w} exp(-a_w)` with finitely many Borel sets `A_w` of the real
output and internal variables invariant under a common real rotation `R ∈ O(N)` (with `h` fixed),
real exponents `a_w(x; h)` that are jointly covariant, `a_w(Rx; Rh) = a_w(x; h)`, and extend
holomorphically in all variables and `h` to the neighbourhood of `A_w × S^{N-1}` formed by the
displacements of modulus `< ε_j` for each scale-`j` variable (the outputs `ψ_1` have scale `1`, the
spins and fluctuation variables scale `0`) and `< 1` for `h`; on that entire neighbourhood
`|a_w(x; h') - a_w(x; h)| ≤ 3 |X|_1 |h' - h|` (5.1), `C_{S5} = 3`.

This is a statement only: BASE-KERNEL §5 derives it from separate analytic obligations (holomorphic
base covariance, the cutoff-transfer identity leaving `A_w` independent of `h`), which are part of
the open Proposition II.7.9; it is not proved here and is not used as a hypothesis.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

section S5

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- The embedding `ℝ^N → ℂ^N`. -/
noncomputable def toCplx (v : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 fun i => (v i : ℂ)

noncomputable instance fintypeVblkSub (R : ℕ → ℝ) (a : LocalHistory S n M K) (k : ℕ) :
    Fintype {y : BlockAt S n M K k // y ∈ Vblk R a k} := Fintype.ofFinite _

noncomputable instance fintypeNewVarsSub (a : LocalHistory S n M K) (k : ℕ) :
    Fintype {p : InternalVars a (k + 1) // p ∈ newVars a k} := Fintype.ofFinite _

/-- Complex output configurations `ψ_1 ∈ ℂ^N` on the blocks of `V`. -/
abbrev OutTC (N : ℕ) (R : ℕ → ℝ) (a : LocalHistory S n M K) (k : ℕ) : Type :=
  {y : BlockAt S n M K k // y ∈ Vblk R a k} → EuclideanSpace ℂ (Fin N)

/-- Complex configurations of the new internal variables. -/
abbrev NewCfgC (N : ℕ) (a : LocalHistory S n M K) (k : ℕ) : Type :=
  {p : InternalVars a (k + 1) // p ∈ newVars a k} → EuclideanSpace ℂ (Fin N)

/-- The displacement neighbourhood of `A × S^{N-1}`: complex configurations within `ε 1` (outputs),
`ε 0` (internal variables) of a point of `A`, and `h` within `1` of a unit vector. -/
def S5Nbhd (ε : ℕ → ℝ) (a : LocalHistory S n M K)
    (A : Set (OutT N R a (0 + 1) × NewCfg N a 0)) :
    Set (OutTC N R a (0 + 1) × NewCfgC N a 0 × EuclideanSpace ℂ (Fin N)) :=
  {q | ∃ p ∈ A, ∃ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 ∧
    (∀ y, ‖q.1 y - toCplx (p.1 y)‖ < ε 1) ∧
    (∀ v, ‖q.2.1 v - toCplx (VarVal.toEuc (p.2 v))‖ < ε 0) ∧ ‖q.2.2 - toCplx h‖ < 1}

/-- **The rotation form (S5) of the base kernel** (BASE-KERNEL §5, regime (A)); see the module
docstring.  `vol` is `|X|_1`. -/
def BaseS5 (ε : ℕ → ℝ) (vol : ℝ) (a : LocalHistory S n M K)
    (T : LFKernel (OutT N R a (0 + 1)) (NewCfg N a 0) (EuclideanSpace ℝ (Fin N))
      (GIdx S n M K N)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (A : ι → Set (OutT N R a (0 + 1) × NewCfg N a 0))
    (aR : ι → OutT N R a (0 + 1) → NewCfg N a 0 → EuclideanSpace ℝ (Fin N) → ℝ)
    (aC : ι → OutTC N R a (0 + 1) × NewCfgC N a 0 × EuclideanSpace ℂ (Fin N) → ℂ),
    (∀ i, MeasurableSet (A i)) ∧
    (∀ i (ρ : OrthN N) p, p ∈ A i → (rotOut ρ p.1, rotSub ρ p.2) ∈ A i) ∧
    (∀ o x (hv : EuclideanSpace ℝ (Fin N)), ‖hv‖ = 1 →
      T.K o x hv = ∑ i, (A i).indicator (fun p => Real.exp (-(aR i p.1 p.2 hv))) (o, x)) ∧
    (∀ i (ρ : OrthN N) o x hv, aR i (rotOut ρ o) (rotSub ρ x) (ρ hv) = aR i o x hv) ∧
    (∀ i, AnalyticOnNhd ℂ (aC i) (S5Nbhd ε a (A i))) ∧
    (∀ i o x hv, aC i (fun y => toCplx (o y), fun v => toCplx (VarVal.toEuc (x v)), toCplx hv) =
      (aR i o x hv : ℂ)) ∧
    (∀ i (q : OutTC N R a (0 + 1) × NewCfgC N a 0) (h h' : EuclideanSpace ℂ (Fin N)),
      (q.1, q.2, h) ∈ S5Nbhd ε a (A i) → (q.1, q.2, h') ∈ S5Nbhd ε a (A i) →
      ‖aC i (q.1, q.2, h') - aC i (q.1, q.2, h)‖ ≤ 3 * vol * ‖h' - h‖)

end S5

end Balaban.LargeField
