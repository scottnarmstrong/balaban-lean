module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The outcomes of `R` on a ripe component (Part III, Definition III.5.2)

Inserting the binary decompositions `1 = χ + (1 - χ)` for `χ̃_k, χ_S, χ^0, χ''` (in this order) into
the kernel `K^pre`, and then `1 = χ_{Z''} + (1 - χ_{Z''})` into the last term, gives six pieces:
the kept outcomes of the first kind `ϰ₁, …, ϰ₄` (`Outcome.kept 0, …, Outcome.kept 3`), the kept
outcome of the second kind `ϰ₅` (`Outcome.kept 4`) and the removed outcome `Outcome.rem`.
The label set is `Fin 5` (the label type of `LocOp`/`Labelled`), with `C_dec ≡ 5`.

* `Outcome`, `Outcome.weight`: the product of the indicators of the outcome;
* `Outcome.weight_sum` (the decomposition of unity), `Outcome.weight_nonneg`;
* `outcomeKernel`, `outcomeKernel_sum`: the algebraic content of `K^pre = ∑ K^{(ϰ)} + K^{rem}`;
* `cDec`, `sum_inv_cDec`: `C_dec(ϰ) = 5` and `∑_ϰ C_dec(ϰ)^{-1} = 1`.
-/

@[expose] public section

namespace Balaban.LargeField

/-- The outcomes of `R` on a ripe component: the five kept labels `ϰ₁, …, ϰ₅` (as `Fin 5`,
`kept i` is `ϰ_{i+1}`) and the removed outcome. -/
inductive Outcome
  | kept (i : Fin 5)
  | rem
  deriving DecidableEq

namespace Outcome

instance : Fintype Outcome :=
  Fintype.ofEquiv (Option (Fin 5))
    { toFun := fun o => o.elim rem kept
      invFun := fun o => match o with
        | kept i => some i
        | rem => none
      left_inv := fun o => by cases o <;> rfl
      right_inv := fun o => by cases o <;> rfl }

/-- `ϰ₁`. -/
abbrev kappa1 : Outcome := kept 0
/-- `ϰ₂`. -/
abbrev kappa2 : Outcome := kept 1
/-- `ϰ₃`. -/
abbrev kappa3 : Outcome := kept 2
/-- `ϰ₄`. -/
abbrev kappa4 : Outcome := kept 3
/-- `ϰ₅`. -/
abbrev kappa5 : Outcome := kept 4

/-- The outcome is a kept one (K1 or K2). -/
def IsKept : Outcome → Prop
  | kept _ => True
  | rem => False

/-- The indicator weight of an outcome, given the values `t = χ̃_k`, `s = χ_S`, `z = χ^0`,
`w = χ''`, `u = χ_{Z''}` of the five small-field functions:
`ϰ₁: 1-t`, `ϰ₂: t(1-s)`, `ϰ₃: t s (1-z)`, `ϰ₄: t s z (1-w)`, `ϰ₅: t s z w (1-u)`,
`rem: t s z w u`. -/
def weight (t s z w u : ℝ) : Outcome → ℝ
  | kept 0 => 1 - t
  | kept 1 => t * (1 - s)
  | kept 2 => t * s * (1 - z)
  | kept 3 => t * s * z * (1 - w)
  | kept 4 => t * s * z * w * (1 - u)
  | rem => t * s * z * w * u

/-- The decomposition of unity: the six weights sum to `1` (for arbitrary real values). -/
theorem weight_sum (t s z w u : ℝ) : ∑ o : Outcome, weight t s z w u o = 1 := by
  have h : ∑ o : Outcome, weight t s z w u o =
      ∑ o : Option (Fin 5), weight t s z w u (o.elim rem kept) := by
    refine (Fintype.sum_equiv
      { toFun := fun o => match o with
          | kept i => some i
          | rem => none
        invFun := fun o => o.elim rem kept
        left_inv := fun o => by cases o <;> rfl
        right_inv := fun o => by cases o <;> rfl } _ _ fun o => ?_)
    cases o <;> rfl
  rw [h, Fintype.sum_option]
  simp only [Option.elim_none, Option.elim_some, Fin.sum_univ_five]
  simp only [weight]
  ring

/-- The weights are non-negative when the five values lie in `[0, 1]`. -/
theorem weight_nonneg {t s z w u : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (hw : w ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (o : Outcome) : 0 ≤ weight t s z w u o := by
  obtain ⟨t0, t1⟩ := ht
  obtain ⟨s0, s1⟩ := hs
  obtain ⟨z0, z1⟩ := hz
  obtain ⟨w0, w1⟩ := hw
  obtain ⟨u0, u1⟩ := hu
  have h1 : 0 ≤ 1 - t := by linarith
  have h2 : 0 ≤ 1 - s := by linarith
  have h3 : 0 ≤ 1 - z := by linarith
  have h4 : 0 ≤ 1 - w := by linarith
  have h5 : 0 ≤ 1 - u := by linarith
  cases o with
  | rem => unfold weight; positivity
  | kept i =>
    fin_cases i <;> simp only [weight] <;> positivity

end Outcome

section Kernel

variable {X : Type*}

/-- The kernel of an outcome: `K^{pre}` times the weight of the outcome, with the five functions
`χ̃_k, χ_S, χ^0, χ'', χ_{Z''}` of Definition III.5.1 given as functions on the integration
variables. -/
def outcomeKernel (K t s z w u : X → ℝ) (o : Outcome) : X → ℝ := fun x =>
  K x * Outcome.weight (t x) (s x) (z x) (w x) (u x) o

/-- **The kernel decomposition** of Definition III.5.2 (algebraic content):
`K^{pre} = K^{(ϰ₁)} + … + K^{(ϰ₅)} + K^{rem}` pointwise. -/
theorem outcomeKernel_sum (K t s z w u : X → ℝ) (x : X) :
    ∑ o : Outcome, outcomeKernel K t s z w u o x = K x := by
  unfold outcomeKernel
  rw [← Finset.mul_sum, Outcome.weight_sum, mul_one]

/-- Each outcome kernel is non-negative when `K ≥ 0` and the functions take values in `[0, 1]`. -/
theorem outcomeKernel_nonneg {K t s z w u : X → ℝ} (hK : ∀ x, 0 ≤ K x)
    (ht : ∀ x, t x ∈ Set.Icc (0 : ℝ) 1) (hs : ∀ x, s x ∈ Set.Icc (0 : ℝ) 1)
    (hz : ∀ x, z x ∈ Set.Icc (0 : ℝ) 1) (hw : ∀ x, w x ∈ Set.Icc (0 : ℝ) 1)
    (hu : ∀ x, u x ∈ Set.Icc (0 : ℝ) 1) (o : Outcome) (x : X) :
    0 ≤ outcomeKernel K t s z w u o x :=
  mul_nonneg (hK x) (Outcome.weight_nonneg (ht x) (hs x) (hz x) (hw x) (hu x) o)

end Kernel

/-- The combinatoric label factor `C_dec(ϰ) = 5` of the kept outcomes (Definition III.5.2). -/
def cDec (_ : Fin 5) : ℝ := 5

theorem cDec_pos (i : Fin 5) : 0 < cDec i := by unfold cDec; norm_num

/-- `∑_ϰ C_dec(ϰ)^{-1} = 1` (the condition (S3) on the labels). -/
theorem sum_inv_cDec : ∑ i : Fin 5, (cDec i)⁻¹ = 1 := by
  simp [cDec]

/-- `log C_dec(ϰ) = log 5`; the exponentials of the negatives sum to `1`. -/
theorem sum_exp_neg_log_cDec : ∑ i : Fin 5, Real.exp (-Real.log (cDec i)) = 1 := by
  have : ∀ i : Fin 5, Real.exp (-Real.log (cDec i)) = (cDec i)⁻¹ := fun i => by
    rw [Real.exp_neg, Real.exp_log (cDec_pos i)]
  simp only [this]
  exact sum_inv_cDec

end Balaban.LargeField
