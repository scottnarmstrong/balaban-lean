module

public import Balaban.LargeField.Operators.Setup
public import Balaban.LargeField.Operators.Kernel
public import Balaban.LargeField.Operators.Variables

/-!
# The bound (1.26) (Part II, Definition II.5.2)

`KerBound a k T κ` is the bound (1.26) for a large-field kernel `T` of a localized history `a` at
scale `k`: the integral of `K e^{Re b}` over the output variables `ψ_k` on `T^{(k)} ∩ Z`
(`ZBlk`) and the internal variables is at most `e^{-κ}`, for **every value of the parameters**
(the outputs on `V ∖ Z`, `OutPar`), every `h` and every `‖g‖_{ℓ¹} < 1`.  This is the single bound
predicate of the project; it is the case `F ≡ 1` of (1.26), equivalent to the general case by the
support property (the kernel vanishes off `χ^dom`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

section KerBound

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- Output variables on the blocks of `V` satisfying `P`. -/
abbrev OutPart (N : ℕ) {α : Type} (V : Set α) (P : α → Prop) : Type :=
  {y : α // y ∈ V ∧ P y} → EuclideanSpace ℝ (Fin N)

/-- Restriction of an output configuration. -/
def restrictOutPart {α : Type} {V : Set α} (o : OutConfig N V) (P : α → Prop) : OutPart N V P :=
  fun y => o ⟨y.1, y.2.1⟩

/-- Lebesgue measure on `OutPart`. -/
noncomputable def outPartMeasure (N : ℕ) {α : Type} [Finite α] (V : Set α) (P : α → Prop) :
    Measure (OutPart N V P) :=
  haveI := Fintype.ofFinite {y : α // y ∈ V ∧ P y}
  Measure.pi fun _ => volume

/-- The finite type of output blocks (the instance used by `outPartMeasure`). -/
noncomputable instance (priority := 2000) fintypeOutBlocks {j : ℕ} (V : Set (BlockAt S n M K j))
    (P : BlockAt S n M K j → Prop) : Fintype {y : BlockAt S n M K j // y ∈ V ∧ P y} :=
  Fintype.ofFinite _

instance (N : ℕ) {j : ℕ} (V : Set (BlockAt S n M K j)) (P : BlockAt S n M K j → Prop) :
    SigmaFinite (outPartMeasure N V P) := by
  unfold outPartMeasure
  infer_instance

/-- The `k`-blocks of `T^{(k)} ∩ Z`: the blocks lying in the `Z_k` of the localized history. -/
def ZBlk (a : LocalHistory S n M K) (k : ℕ) (y : BlockAt S n M K k) : Prop :=
  BlockSub (S := S) (n := n) (M := M) (K := K) k y (a.Z k)

/-- The output variables `ψ_k` on `T^{(k)} ∩ Z` (those integrated in (1.26)). -/
abbrev OutZ (N : ℕ) (R : ℕ → ℝ) (a : LocalHistory S n M K) (k : ℕ) : Type :=
  OutPart N (Vblk R a k) (ZBlk a k)

/-- The output variables on `V ∖ Z` (parameters of (1.26)). -/
abbrev OutPar (N : ℕ) (R : ℕ → ℝ) (a : LocalHistory S n M K) (k : ℕ) : Type :=
  OutPart N (Vblk R a k) (fun y => ¬ ZBlk a k y)

open Classical in
/-- The output configuration with the given values on `Z` and the given parameters. -/
noncomputable def mergeOut (a : LocalHistory S n M K) (k : ℕ) (oz : OutZ N R a k)
    (par : OutPar N R a k) : OutT N R a k :=
  fun y => if h : ZBlk a k y.1 then oz ⟨y.1, y.2, h⟩ else par ⟨y.1, y.2, h⟩

theorem measurable_mergeOut (a : LocalHistory S n M K) (k : ℕ) (par : OutPar N R a k) :
    Measurable fun oz : OutZ N R a k => mergeOut a k oz par := by
  classical
  refine measurable_pi_iff.mpr fun y => ?_
  unfold mergeOut
  by_cases h : ZBlk a k y.1
  · simp only [h, ↓reduceDIte]
    exact measurable_pi_apply _
  · simp only [h, ↓reduceDIte]
    exact measurable_const

/-- **The bound (1.26)** with exponent `κ` (see the module docstring). -/
def KerBound (a : LocalHistory S n M K) (k : ℕ) {A : Set (InternalVars a k)}
    (T : LFKernel (OutT N R a k) (SubCfg N a k A) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N))
    (κ : ℝ) : Prop :=
  ∀ (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) →
    ∀ par : OutPar N R a k,
      ∫⁻ oz, ∫⁻ x, T.absW (mergeOut a k oz par) x hv g ∂(subMeasure N a k A)
        ∂(outPartMeasure N (Vblk R a k) (ZBlk a k)) ≤ ENNReal.ofReal (Real.exp (-κ))



end KerBound

end Balaban.LargeField
