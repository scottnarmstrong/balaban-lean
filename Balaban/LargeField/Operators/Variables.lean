module

public import Balaban.LargeField.History.LocalHistory
public import Balaban.Frozen.Model.AprioriMeasure

/-!
# Variables of a localized history and the reference measure (Part II, Definition II.5.1)

For a localized history `a` (fine sets, `LocalHistory`) and a level `k`:

* `InternalVars a k`: the index set `I(Z, 𝔞)` of the internal variables — for `0 ≤ j < k` the
  large-field variables `ψ_j(y)`, `y ∈ T^{(j)} ∩ Ω^c_{j+1} ∩ Z`, and the fluctuation variables
  `ψ'_j(y)`, `y ∈ T^{(j)} ∩ (Ω_{j+1} ∖ Ω''_{j+1}) ∩ Z`.  As all sets of a `LocalHistory` are
  already intersected with `Z`, `Ω^c_{j+1} ∩ Z` is `Z_{j+1} ∩ Z ∖ Ω_{j+1}` (Lemma I.3.5 (e):
  `Ω^c_{j+1} ⊂ Z_{j+1}`).  A cube of scale `j` belongs to a fine set if all its fine sites do.
* `refMeasure`: the product of the surface measures `volume.toSphere` (total mass `N v_N`, not
  normalized; D-IV.4) on the scale-`0` large-field variables (the spins) and Lebesgue measure on
  the others.
* `multiscaleField`: the multiscale field `ψ` as a function of the internal and output variables.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

/-- The unit sphere `S^{N-1} ⊂ ℝ^N`. -/
abbrev SpinSphere (N : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1

/-- Values of a variable: spins (`true`) live on the sphere, all others in `ℝ^N`. -/
def VarVal (N : ℕ) : Bool → Type
  | true => SpinSphere N
  | false => EuclideanSpace ℝ (Fin N)

noncomputable instance (N : ℕ) : (b : Bool) → MeasurableSpace (VarVal N b)
  | true => inferInstanceAs (MeasurableSpace (SpinSphere N))
  | false => inferInstanceAs (MeasurableSpace (EuclideanSpace ℝ (Fin N)))

/-- The reference measure of one variable: `volume.toSphere` on the sphere (total mass `N v_N`),
Lebesgue measure on `ℝ^N`. -/
noncomputable def varMeasure (N : ℕ) : (b : Bool) → Measure (VarVal N b)
  | true => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere
  | false => (volume : Measure (EuclideanSpace ℝ (Fin N)))

instance (N : ℕ) : (b : Bool) → SigmaFinite (varMeasure N b)
  | true => by
      show SigmaFinite (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere
      infer_instance
  | false => by
      show SigmaFinite (volume : Measure (EuclideanSpace ℝ (Fin N)))
      infer_instance

/-- The value of a variable as a vector of `ℝ^N`. -/
def VarVal.toEuc {N : ℕ} : {b : Bool} → VarVal N b → EuclideanSpace ℝ (Fin N)
  | true, v => (show SpinSphere N from v).1
  | false, v => v

theorem VarVal.measurable_toEuc (N : ℕ) : ∀ b : Bool, Measurable (@VarVal.toEuc N b)
  | true => (measurable_subtype_coe (α := EuclideanSpace ℝ (Fin N)) (p := fun x => x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1))
  | false => measurable_id

/-- The two kinds of internal variables. -/
inductive VarKind
  | large
  | fluct
  deriving DecidableEq

instance : Finite VarKind :=
  Finite.of_injective (fun k : VarKind => (k = VarKind.large : Prop)) (by
    intro a b h
    cases a <;> cases b <;> simp_all)

section Vars

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ}

/-- A cube of scale `j` lies in a fine set if all of its fine sites do. -/
def cubeIn (M K j : ℕ) (y : Torus S.d (n j)) (B : Set (Torus S.d (M * n K * S.L ^ K))) : Prop :=
  ∀ x, cubeMap n S.L M K j x = y → x ∈ B

/-- Membership of a site `y` of scale `j` in the variable set of the given kind. -/
def varSet (a : LocalHistory S n M K) (j : ℕ) :
    VarKind → Set (Torus S.d (M * n K * S.L ^ K))
  | .large => a.Z (j + 1) \ a.Omega j
  | .fluct => a.Omega j \ a.OmegaDD j

/-- The index set `I(Z, 𝔞)` of the internal variables of a localized history at level `k`. -/
def InternalVars (a : LocalHistory S n M K) (k : ℕ) : Type :=
  {p : (j : Fin k) × VarKind × Torus S.d (n j) //
    cubeIn (S := S) (n := n) M K p.1 p.2.2 (varSet a p.1 p.2.1)}

noncomputable instance (a : LocalHistory S n M K) (k : ℕ) : Fintype (InternalVars a k) :=
  haveI : Finite (InternalVars a k) := by unfold InternalVars; infer_instance
  Fintype.ofFinite (InternalVars a k)

/-- Is the variable a spin (large-field variable of scale `0`)? -/
def InternalVars.isSpin {a : LocalHistory S n M K} {k : ℕ} (p : InternalVars a k) : Bool :=
  decide (p.1.1.val = 0 ∧ p.1.2.1 = VarKind.large)

/-- Configurations of the internal variables. -/
abbrev IntConfig (N : ℕ) (a : LocalHistory S n M K) (k : ℕ) : Type :=
  (p : InternalVars a k) → VarVal N p.isSpin

/-- The reference measure `μ_{Z,𝔞}` on the internal variables (Definition II.5.1, D-IV.4). -/
noncomputable def refMeasure (N : ℕ) (a : LocalHistory S n M K) (k : ℕ) :
    Measure (IntConfig N a k) :=
  Measure.pi fun p => varMeasure N p.isSpin

instance (N : ℕ) (a : LocalHistory S n M K) (k : ℕ) : SigmaFinite (refMeasure N a k) := by
  unfold refMeasure; infer_instance

/-- Output variables `ψ_k(y)`, `y ∈ T^{(k)} ∩ V`. -/
abbrev OutConfig (N : ℕ) {k : ℕ} (V : Set (Torus S.d (n k))) : Type :=
  V → EuclideanSpace ℝ (Fin N)

/-- Lebesgue measure on the output variables. -/
noncomputable def outMeasure (N : ℕ) {k : ℕ} (V : Set (Torus S.d (n k))) :
    Measure (OutConfig (S := S) N V) :=
  haveI : Finite V := inferInstance
  haveI := Fintype.ofFinite V
  Measure.pi fun _ => volume

open Classical in
/-- The multiscale field `ψ` of the history (II.3): `ψ_j` on `Λ_j = Ω_j ∖ Ω_{j+1}` for `j < k`
(`Ω_0` is everything), and `ψ_k` on `Ω_k ∩ V`; zero elsewhere. -/
noncomputable def multiscaleField (N : ℕ) (a : LocalHistory S n M K) (k : ℕ)
    (V : Set (Torus S.d (n k))) (x : IntConfig N a k) (o : OutConfig (S := S) N V)
    (j : ℕ) (y : Torus S.d (n j)) : EuclideanSpace ℝ (Fin N) :=
  if hj : j < k then
    if h : cubeIn (S := S) (n := n) M K j y (varSet a j .large) ∧
        (j = 0 ∨ cubeIn (S := S) (n := n) M K j y (a.Omega (j - 1))) then
      VarVal.toEuc (x ⟨⟨⟨j, hj⟩, .large, y⟩, h.1⟩)
    else 0
  else if hjk : j = k then
    (by
      subst hjk
      exact if h : y ∈ V ∧ cubeIn (S := S) (n := n) M K j y (a.Omega (j - 1)) then
        o ⟨y, h.1⟩ else 0)
  else 0

end Vars

end Balaban.LargeField
