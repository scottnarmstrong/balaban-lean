/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.KerBound
public import Balaban.LargeField.Operators.AncVars
public import Balaban.LargeField.Operators.PiTools
public import Balaban.LargeField.R.Rop
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The removed kernel of `R` (P7 (3.7) on `χ_{Z''}`; LFR Definition III.8.5, Lemma III.8.7)

`notes/phase1/LF4R-PLAN.md` §4, leaf 5.  For a ripe component `Z` with localized history `𝔞`
sent to `R`, P7 (3.7) is obtained from the term `ρ(𝔸, σ)` by integrating `ψ_k` over `Z₀` (and
the Gaussian-only variables) and dividing by the denominator `∫ dψ_k↾Z₀ ρ_{k,0}(Z)` (3.5); the
composition (III.1.4), Lemma III.7.1, the translation `ψ'' = ψ̃ - ψ⁰_{k₁,k}` and (2.58′) are
identities of the integrand or measure-preserving changes of variables.  The removed outcome is
this operator times `χ_{Z''}`, applied **after** `R` (`χ_{Z''}` reads `ψ_k` on `Z₀ ⊆ Z''₀`).

On the variables of the pre-operator `𝕋^pre_k(Z, 𝔞)` (an `OpPkg`: outputs `ψ_k` on `V_Z`, internal
variables `P.A`), with `t, s, z, w` the values of `χ̃_k, χ_S, χ⁰, χ''`, `u = χ_{Z''}`,
`c₀ = χ_{Z₀}`, `r` the reference density as a function of `(ψ_k↾Z₀, ψ_k↾(V_Z ∖ Z₀))` and
`EZ = E_k |Z|_k`, the removed kernel is
`K^rem(o, x) = e^{EZ} u(o) c₀(o) ∫ dψ_k↾Z₀ K^pre t s z w / ∫ dψ_k↾Z₀ r`, with exponent `b^pre`.

* `remZeroSplit`: the measure-preserving identification `ψ_k↾V_Z ↔ (ψ_k↾Z₀, ψ_k↾(V_Z ∖ Z₀))`
  (`measurePreserving_remZeroSplit`); `remZeroMerge` its inverse;
* `remDecomp r`: the `RDecomp` of one component with reference density `r`;
* `remDen`, `remNum`, `removedK`: the denominator, the integrated kernel, the removed kernel as a
  function; `removedKernel`: the `LFKernel` on the carrier of `KerBound a k`;
* basic properties: `removedKernel_K`, `removedKernel_b` (`g` enters only through `b = b^pre`),
  `remNum_congr`, `remDen_congr` (`ψ_k↾Z₀` enters only through `u` and `c₀`),
  `removedK_ne_zero`, `removedKernel_support` (support in the domain of the pre-operator);
* characterization: `Rop_remDecomp_removed` (`χ_{Z''} · R[ρ] = ρ_{k,0} e^{-EZ} 𝕋^rem`, the
  removed part of `R` applied to the pre-operator) and `removedK_eq_outcomeKernel` (the kernel is
  `outcomeKernel` with the removed weight of the `R`-normalized pre-kernel).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

section Split

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (a : LocalHistory S n M K) (k : ℕ) (Z0 : Set (BlockAt S n M K k))

/-- The output variables `ψ_k↾Z₀` (the `k`-blocks of `V_Z` in `Z₀`). -/
abbrev OutZero (N : ℕ) (R : ℕ → ℝ) (a : LocalHistory S n M K) (k : ℕ)
    (Z0 : Set (BlockAt S n M K k)) : Type :=
  OutPart N (Vblk R a k) (· ∈ Z0)

/-- The output variables `ψ_k↾(V_Z ∖ Z₀)`. -/
abbrev OutRest (N : ℕ) (R : ℕ → ℝ) (a : LocalHistory S n M K) (k : ℕ)
    (Z0 : Set (BlockAt S n M K k)) : Type :=
  OutPart N (Vblk R a k) (· ∉ Z0)

open Classical in
/-- The output configuration with the given values on `Z₀` and on `V_Z ∖ Z₀`. -/
noncomputable def remZeroMerge (p : OutZero N R a k Z0 × OutRest N R a k Z0) : OutT N R a k :=
  fun y => if h : y.1 ∈ Z0 then p.1 ⟨y.1, y.2, h⟩ else p.2 ⟨y.1, y.2, h⟩

theorem measurable_remZeroMerge :
    Measurable (remZeroMerge (N := N) (R := R) a k Z0) := by
  classical
  refine measurable_pi_iff.mpr fun y => ?_
  by_cases h : y.1 ∈ Z0
  · simp only [remZeroMerge, h, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [remZeroMerge, h, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_snd

/-- **The identification `ψ_k↾V_Z ↔ (ψ_k↾Z₀, ψ_k↾(V_Z ∖ Z₀))`** of the output configurations. -/
noncomputable def remZeroSplit : OutT N R a k ≃ᵐ OutZero N R a k Z0 × OutRest N R a k Z0 where
  toFun o := (restrictOutPart o (· ∈ Z0), restrictOutPart o (· ∉ Z0))
  invFun := remZeroMerge a k Z0
  left_inv o := by
    classical
    funext y
    by_cases h : y.1 ∈ Z0 <;> simp [remZeroMerge, restrictOutPart, h]
  right_inv p := by
    classical
    refine Prod.ext (funext fun y => ?_) (funext fun y => ?_)
    · simp [remZeroMerge, restrictOutPart, y.2.2]
    · simp [remZeroMerge, restrictOutPart, y.2.2]
  measurable_toFun :=
    (measurable_pi_iff.mpr fun _ => measurable_pi_apply _).prodMk
      (measurable_pi_iff.mpr fun _ => measurable_pi_apply _)
  measurable_invFun := measurable_remZeroMerge a k Z0

theorem remZeroSplit_apply (o : OutT N R a k) :
    remZeroSplit a k Z0 o = (restrictOutPart o (· ∈ Z0), restrictOutPart o (· ∉ Z0)) := rfl

theorem remZeroSplit_symm_apply (p : OutZero N R a k Z0 × OutRest N R a k Z0) :
    (remZeroSplit a k Z0).symm p = remZeroMerge a k Z0 p := rfl

theorem remZeroSplit_merge (p : OutZero N R a k Z0 × OutRest N R a k Z0) :
    remZeroSplit a k Z0 (remZeroMerge a k Z0 p) = p :=
  (remZeroSplit a k Z0).apply_symm_apply p

theorem remZeroMerge_split (o : OutT N R a k) :
    remZeroMerge a k Z0 (remZeroSplit a k Z0 o) = o :=
  (remZeroSplit a k Z0).symm_apply_apply o

/-- `remZeroSplit` maps the Lebesgue measure of `ψ_k↾V_Z` to the product of the Lebesgue measures
of `ψ_k↾Z₀` and `ψ_k↾(V_Z ∖ Z₀)`. -/
theorem measurePreserving_remZeroSplit :
    MeasurePreserving (remZeroSplit (N := N) (R := R) a k Z0) (outMeasure N (Vblk R a k))
      ((outPartMeasure N (Vblk R a k) (· ∈ Z0)).prod
        (outPartMeasure N (Vblk R a k) (· ∉ Z0))) := by
  classical
  let _inst : Fintype (Vblk R a k) := Fintype.ofFinite _
  let p : Vblk R a k → Prop := fun y => y.1 ∈ Z0
  have h1 := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Vblk R a k => (volume : Measure (EuclideanSpace ℝ (Fin N)))) p
  let e1 : {y : BlockAt S n M K k // y ∈ Vblk R a k ∧ y ∈ Z0} ≃ {i : Vblk R a k // p i} :=
    { toFun := fun b => ⟨⟨b.1, b.2.1⟩, b.2.2⟩
      invFun := fun i => ⟨i.1.1, i.1.2, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : {y : BlockAt S n M K k // y ∈ Vblk R a k ∧ y ∉ Z0} ≃ {i : Vblk R a k // ¬ p i} :=
    { toFun := fun b => ⟨⟨b.1, b.2.1⟩, b.2.2⟩
      invFun := fun i => ⟨i.1.1, i.1.2, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h2 := PiTools.measurePreserving_reindex e1
    (fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N))))
    (fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) (fun _ v => v)
    (fun _ => MeasurePreserving.id _)
  have h3 := PiTools.measurePreserving_reindex e2
    (fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N))))
    (fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) (fun _ v => v)
    (fun _ => MeasurePreserving.id _)
  have h4 := (h2.prod h3).comp h1
  unfold outMeasure outPartMeasure
  convert h4 using 1
  funext o
  rfl

/-- `(Unit → W) ≃ᵐ W`, `f ↦ f ()` (the variables of the single component of `𝒵_σ`). -/
noncomputable def remUnitEquiv (W : Type) [MeasurableSpace W] : (Unit → W) ≃ᵐ W where
  toFun f := f ()
  invFun w := fun _ => w
  left_inv f := funext fun c => by cases c; rfl
  right_inv _ := rfl
  measurable_toFun := measurable_pi_apply ()
  measurable_invFun := measurable_pi_iff.mpr fun _ => measurable_id

theorem measurePreserving_remUnitEquiv {W : Type} [MeasurableSpace W] (μ : Measure W)
    [SigmaFinite μ] :
    MeasurePreserving (remUnitEquiv W) (Measure.pi fun _ : Unit => μ) μ :=
  measurePreserving_funUnique μ Unit

/-- **The `R` decomposition of one ripe component on its output variables** (Definition III.8.3):
`𝒵_σ = {Z}` (`ι = Unit`), `W = ψ_k↾Z₀`, `Y = ψ_k↾(V_Z ∖ Z₀)`, the Lebesgue measures, and the
reference density `r = ρ_{k,0}(Z)` as a function of `(ψ_k↾Z₀, ψ_k↾(V_Z ∖ Z₀))`. -/
noncomputable def remDecomp (r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ) :
    RDecomp (outMeasure N (Vblk R a k)) where
  ι := Unit
  W := fun _ => OutZero N R a k Z0
  μ := fun _ => outPartMeasure N (Vblk R a k) (· ∈ Z0)
  Y := OutRest N R a k Z0
  νY := outPartMeasure N (Vblk R a k) (· ∉ Z0)
  e := (remZeroSplit a k Z0).trans
    (MeasurableEquiv.prodCongr (remUnitEquiv (OutZero N R a k Z0)).symm (MeasurableEquiv.refl _))
  mp := by
    have h := ((measurePreserving_remUnitEquiv (outPartMeasure N (Vblk R a k) (· ∈ Z0))).symm
      (remUnitEquiv (OutZero N R a k Z0))).prod
        (MeasurePreserving.id (outPartMeasure N (Vblk R a k) (· ∉ Z0)))
    exact h.comp (measurePreserving_remZeroSplit a k Z0)
  r := fun _ w y => r w y

end Split

section Kernel

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (a : LocalHistory S n M K) (k : ℕ) (Z0 : Set (BlockAt S n M K k))
  {X H : Type*} [MeasurableSpace X]

/-- **The denominator** `∫ dψ_k↾Z₀ ρ_{k,0}(Z)` (P7 (3.5)) at the output configuration `o`: a
function of `ψ_k↾(V_Z ∖ Z₀)` only. -/
noncomputable def remDen (r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ) (o : OutT N R a k) :
    ℝ :=
  ∫ w, r w (remZeroSplit a k Z0 o).2 ∂(outPartMeasure N (Vblk R a k) (· ∈ Z0))

/-- **The kernel integrated over `ψ_k↾Z₀`**: `∫ dψ_k↾Z₀ Kf(ψ_k, x)` at the output configuration
`o`, with `ψ_k↾(V_Z ∖ Z₀)` read from `o`. -/
noncomputable def remNum (Kf : OutT N R a k → X → H → ℝ) (o : OutT N R a k) (x : X) (h : H) : ℝ :=
  ∫ w, Kf (remZeroMerge a k Z0 (w, (remZeroSplit a k Z0 o).2)) x h
    ∂(outPartMeasure N (Vblk R a k) (· ∈ Z0))

/-- **The removed kernel as a function** (P7 (3.7) times `χ_{Z''} e^{E_k|Z|}`):
`e^{EZ} u(o) c₀(o) ∫ dψ_k↾Z₀ Kf / ∫ dψ_k↾Z₀ r`, with `Kf` the "to `R`" kernel
`K^pre χ̃_k χ_S χ⁰ χ''`, `u = χ_{Z''}`, `c₀ = χ_{Z₀}`, `r = ρ_{k,0}(Z)`, `EZ = E_k |Z|_k`. -/
noncomputable def removedK (Kf : OutT N R a k → X → H → ℝ) (u c0 : OutT N R a k → ℝ)
    (r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ) (EZ : ℝ) (o : OutT N R a k) (x : X)
    (h : H) : ℝ :=
  Real.exp EZ * u o * c0 o * remNum a k Z0 Kf o x h / remDen a k Z0 r o

theorem remDen_congr (r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ) {o o' : OutT N R a k}
    (h : (remZeroSplit a k Z0 o).2 = (remZeroSplit a k Z0 o').2) :
    remDen a k Z0 r o = remDen a k Z0 r o' := by
  unfold remDen; rw [h]

theorem remNum_congr (Kf : OutT N R a k → X → H → ℝ) {o o' : OutT N R a k}
    (h : (remZeroSplit a k Z0 o).2 = (remZeroSplit a k Z0 o').2) (x : X) (hv : H) :
    remNum a k Z0 Kf o x hv = remNum a k Z0 Kf o' x hv := by
  unfold remNum; rw [h]

theorem remDen_nonneg {r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ} (hr : ∀ w y, 0 ≤ r w y)
    (o : OutT N R a k) : 0 ≤ remDen a k Z0 r o :=
  integral_nonneg fun _ => hr _ _

theorem remNum_nonneg {Kf : OutT N R a k → X → H → ℝ} (hK : ∀ o x h, 0 ≤ Kf o x h)
    (o : OutT N R a k) (x : X) (hv : H) : 0 ≤ remNum a k Z0 Kf o x hv :=
  integral_nonneg fun _ => hK _ _ _

theorem removedK_nonneg {Kf : OutT N R a k → X → H → ℝ} (hK : ∀ o x h, 0 ≤ Kf o x h)
    {u c0 : OutT N R a k → ℝ} (hu : ∀ o, 0 ≤ u o) (hc0 : ∀ o, 0 ≤ c0 o)
    {r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ} (hr : ∀ w y, 0 ≤ r w y) (EZ : ℝ)
    (o : OutT N R a k) (x : X) (hv : H) : 0 ≤ removedK a k Z0 Kf u c0 r EZ o x hv := by
  unfold removedK
  have := remNum_nonneg a k Z0 hK o x hv
  have := remDen_nonneg a k Z0 hr o
  have := hu o
  have := hc0 o
  positivity

theorem measurable_remDen {r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ}
    (hr : Measurable fun q : OutZero N R a k Z0 × OutRest N R a k Z0 => r q.1 q.2) :
    Measurable (remDen a k Z0 r) := by
  have hm : Measurable fun q : OutT N R a k × OutZero N R a k Z0 =>
      r q.2 (remZeroSplit a k Z0 q.1).2 :=
    hr.comp (measurable_snd.prodMk
      (measurable_snd.comp ((remZeroSplit a k Z0).measurable.comp measurable_fst)))
  exact (hm.stronglyMeasurable.integral_prod_right'
    (ν := outPartMeasure N (Vblk R a k) (· ∈ Z0))).measurable

theorem measurable_remNum {Kf : OutT N R a k → X → H → ℝ} (hv : H)
    (hK : Measurable fun p : OutT N R a k × X => Kf p.1 p.2 hv) :
    Measurable fun p : OutT N R a k × X => remNum a k Z0 Kf p.1 p.2 hv := by
  have hmap : Measurable fun q : (OutT N R a k × X) × OutZero N R a k Z0 =>
      (remZeroMerge a k Z0 (q.2, (remZeroSplit a k Z0 q.1.1).2), q.1.2) :=
    ((measurable_remZeroMerge a k Z0).comp (measurable_snd.prodMk
      (measurable_snd.comp ((remZeroSplit a k Z0).measurable.comp
        (measurable_fst.comp measurable_fst))))).prodMk (measurable_snd.comp measurable_fst)
  have hm := hK.comp hmap
  exact (hm.stronglyMeasurable.integral_prod_right'
    (ν := outPartMeasure N (Vblk R a k) (· ∈ Z0))).measurable

theorem measurable_removedK {Kf : OutT N R a k → X → H → ℝ} (hv : H)
    (hK : Measurable fun p : OutT N R a k × X => Kf p.1 p.2 hv) {u c0 : OutT N R a k → ℝ}
    (hu : Measurable u) (hc0 : Measurable c0)
    {r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ}
    (hr : Measurable fun q : OutZero N R a k Z0 × OutRest N R a k Z0 => r q.1 q.2) (EZ : ℝ) :
    Measurable fun p : OutT N R a k × X => removedK a k Z0 Kf u c0 r EZ p.1 p.2 hv := by
  unfold removedK
  exact ((((measurable_const.mul (hu.comp measurable_fst)).mul (hc0.comp measurable_fst)).mul
    (measurable_remNum a k Z0 hv hK)).div ((measurable_remDen a k Z0 hr).comp measurable_fst))

end Kernel

section Kernel2

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (a : LocalHistory S n M K) (k : ℕ) (Z0 : Set (BlockAt S n M K k))
  {X H : Type*} [MeasurableSpace X]

/-- **The "to `R`" kernel** `K^pre χ̃_k χ_S χ⁰ χ''` (the last term of Definition III.5.2), for the
values `t, s, z, w` of the four small-field functions: `K^pre` times the weight of `→R`. -/
noncomputable def toRKernel (Kf : OutT N R a k → X → H → ℝ) (t s z w : OutT N R a k → X → ℝ)
    (o : OutT N R a k) (x : X) (h : H) : ℝ :=
  Kf o x h * ROutcome.weight (t o x) (s o x) (z o x) (w o x) ROutcome.toR

theorem toRKernel_nonneg {Kf : OutT N R a k → X → H → ℝ} (hK : ∀ o x h, 0 ≤ Kf o x h)
    {t s z w : OutT N R a k → X → ℝ} (ht : ∀ o x, 0 ≤ t o x) (hs : ∀ o x, 0 ≤ s o x)
    (hz : ∀ o x, 0 ≤ z o x) (hw : ∀ o x, 0 ≤ w o x) (o : OutT N R a k) (x : X) (hv : H) :
    0 ≤ toRKernel a k Kf t s z w o x hv := by
  unfold toRKernel ROutcome.weight
  have := hK o x hv; have := ht o x; have := hs o x; have := hz o x; have := hw o x
  positivity

theorem measurable_toRKernel {Kf : OutT N R a k → X → H → ℝ} (hv : H)
    (hK : Measurable fun p : OutT N R a k × X => Kf p.1 p.2 hv)
    {t s z w : OutT N R a k → X → ℝ} (ht : Measurable fun p : OutT N R a k × X => t p.1 p.2)
    (hs : Measurable fun p : OutT N R a k × X => s p.1 p.2)
    (hz : Measurable fun p : OutT N R a k × X => z p.1 p.2)
    (hw : Measurable fun p : OutT N R a k × X => w p.1 p.2) :
    Measurable fun p : OutT N R a k × X => toRKernel a k Kf t s z w p.1 p.2 hv := by
  unfold toRKernel ROutcome.weight
  exact hK.mul (((ht.mul hs).mul hz).mul hw)

/-- **The support of the removed kernel**: it vanishes unless `u(o) ≠ 0`, `c₀(o) ≠ 0` and the
integrated kernel is non-zero at some configuration agreeing with `o` off `Z₀`. -/
theorem removedK_ne_zero {Kf : OutT N R a k → X → H → ℝ} {u c0 : OutT N R a k → ℝ}
    {r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ} {EZ : ℝ} {o : OutT N R a k} {x : X}
    {hv : H} (h : removedK a k Z0 Kf u c0 r EZ o x hv ≠ 0) :
    u o ≠ 0 ∧ c0 o ≠ 0 ∧
      ∃ w, Kf (remZeroMerge a k Z0 (w, (remZeroSplit a k Z0 o).2)) x hv ≠ 0 := by
  unfold removedK at h
  refine ⟨fun hu => h (by simp [hu]), fun hc => h (by simp [hc]), ?_⟩
  by_contra hne
  push Not at hne
  apply h
  have : remNum a k Z0 Kf o x hv = 0 := by
    unfold remNum
    simp [hne]
  simp [this]

/-- **The decomposition (3.20)**: `χ_{Z''}` and `1 - χ_{Z''}` split the `R`-normalized kernel into
the removed kernel and the kernel of the kept outcome `ϰ₅` (before the factor `ρ_{k,0}(Z)`). -/
theorem removedK_add_one_sub (Kf : OutT N R a k → X → H → ℝ) (u c0 : OutT N R a k → ℝ)
    (r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ) (EZ : ℝ) (o : OutT N R a k) (x : X)
    (hv : H) :
    removedK a k Z0 Kf u c0 r EZ o x hv + removedK a k Z0 Kf (fun o => 1 - u o) c0 r EZ o x hv =
      removedK a k Z0 Kf (fun _ => 1) c0 r EZ o x hv := by
  unfold removedK
  ring

/-- **The removed kernel is `outcomeKernel` with the removed weight** (Definition III.5.2 and
(3.20)): if `χ̃_k, χ_S, χ⁰, χ''` do not read `ψ_k↾Z₀` (P7 p. 517, Lemma III.8.4 (i)), the removed
kernel of the "to `R`" kernel `K^pre t s z w` is `outcomeKernel` of the `R`-normalized pre-kernel
`e^{EZ} χ_{Z₀} ∫_{Z₀} K^pre / ∫_{Z₀} ρ_{k,0}` with the weights `t, s, z, w, u = χ_{Z''}` of the
removed outcome. -/
theorem removedK_eq_outcomeKernel (Kf : OutT N R a k → X → H → ℝ) (t s z w : OutT N R a k → X → ℝ)
    (u c0 : OutT N R a k → ℝ) (r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ) (EZ : ℝ)
    (hv : H)
    (hind : ∀ o o' x, (remZeroSplit a k Z0 o).2 = (remZeroSplit a k Z0 o').2 →
      t o x = t o' x ∧ s o x = s o' x ∧ z o x = z o' x ∧ w o x = w o' x)
    (o : OutT N R a k) (x : X) :
    removedK a k Z0 (toRKernel a k Kf t s z w) u c0 r EZ o x hv =
      outcomeKernel (fun p : OutT N R a k × X => removedK a k Z0 Kf (fun _ => 1) c0 r EZ p.1 p.2 hv)
        (fun p => t p.1 p.2) (fun p => s p.1 p.2) (fun p => z p.1 p.2) (fun p => w p.1 p.2)
        (fun p => u p.1) Outcome.rem (o, x) := by
  have hn : remNum a k Z0 (toRKernel a k Kf t s z w) o x hv =
      remNum a k Z0 Kf o x hv * (t o x * s o x * z o x * w o x) := by
    unfold remNum toRKernel
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w' => ?_)
    have hy : (remZeroSplit a k Z0 (remZeroMerge a k Z0 (w', (remZeroSplit a k Z0 o).2))).2 =
        (remZeroSplit a k Z0 o).2 := by rw [remZeroSplit_merge]
    obtain ⟨e1, e2, e3, e4⟩ := hind _ _ x hy
    simp only [ROutcome.weight, e1, e2, e3, e4]
  unfold outcomeKernel
  simp only [removedK, Outcome.weight]
  rw [hn]
  ring

end Kernel2

section Identity

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (a : LocalHistory S n M K) (k : ℕ) (Z0 : Set (BlockAt S n M K k))
  {X H : Type*} [MeasurableSpace X]

/-- `R` of the one-component decomposition, explicitly (P7 (1.6)):
`R[ρ](o) = r(ψ_k↾Z₀, ψ_k↾Z₀ᶜ) · ∫ dψ_k↾Z₀ ρ / ∫ dψ_k↾Z₀ r`. -/
theorem Rop_remDecomp_apply (r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ)
    (ρ : OutT N R a k → ℝ) (o : OutT N R a k) :
    Rop (remDecomp a k Z0 r) ρ o =
      r (remZeroSplit a k Z0 o).1 (remZeroSplit a k Z0 o).2 *
        ((∫ w, ρ (remZeroMerge a k Z0 (w, (remZeroSplit a k Z0 o).2))
            ∂(outPartMeasure N (Vblk R a k) (· ∈ Z0))) / remDen a k Z0 r o) := by
  have hint : ∫ x, ρ ((remDecomp a k Z0 r).e.symm (x, ((remDecomp a k Z0 r).e o).2))
        ∂(Measure.pi (remDecomp a k Z0 r).μ) =
      ∫ w, ρ (remZeroMerge a k Z0 (w, (remZeroSplit a k Z0 o).2))
        ∂(outPartMeasure N (Vblk R a k) (· ∈ Z0)) := by
    exact (measurePreserving_remUnitEquiv (outPartMeasure N (Vblk R a k) (· ∈ Z0))).integral_comp'
      (fun w => ρ (remZeroMerge a k Z0 (w, (remZeroSplit a k Z0 o).2)))
  unfold Rop RopProd
  rw [hint]
  have hp : ∀ g : (remDecomp a k Z0 r).ι → ℝ,
      ∏ c, g c = g (show (remDecomp a k Z0 r).ι from ()) := fun g => by
    show ∏ c : Unit, g c = g ()
    exact Fintype.prod_unique (ι := Unit) (fun c : Unit => g c)
  rw [hp, hp]
  rfl

/-- **The removed part of `R` applied to the pre-operator** (Definition III.8.5, (3.20),
P7 (3.10)): for the term `ρ(o) = ∫ dx Kf(o, x) f(o, x)` of the "to `R`" kernel `Kf` against a
function `f` that does not read `ψ_k↾Z₀` (the boundary terms, the exponent `b^pre` and the other
factors of `ρ(𝔸, σ)`; P7 p. 517), with absolute integrability on each fibre (Fubini) and a
reference density `r` vanishing where `χ_{Z₀} = 0` (`r = c₀ r`):
`χ_{Z''}(o) · R[ρ](o) = ρ_{k,0}(Z)(o) · e^{-EZ} · ∫ dx K^rem(o, x) f(o, x)`. -/
theorem Rop_remDecomp_removed (μX : Measure X) [SFinite μX] (Kf : OutT N R a k → X → H → ℝ)
    (u c0 : OutT N R a k → ℝ) (r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ) (EZ : ℝ) (hv : H)
    (f : OutT N R a k → X → ℝ)
    (hf : ∀ o o' x, (remZeroSplit a k Z0 o).2 = (remZeroSplit a k Z0 o').2 → f o x = f o' x)
    (hint : ∀ y : OutRest N R a k Z0, Integrable
      (fun q : OutZero N R a k Z0 × X => Kf (remZeroMerge a k Z0 (q.1, y)) q.2 hv *
        f (remZeroMerge a k Z0 (q.1, y)) q.2)
      ((outPartMeasure N (Vblk R a k) (· ∈ Z0)).prod μX))
    (hrc : ∀ q : OutZero N R a k Z0 × OutRest N R a k Z0,
      r q.1 q.2 = c0 (remZeroMerge a k Z0 q) * r q.1 q.2)
    (o : OutT N R a k) :
    u o * Rop (remDecomp a k Z0 r) (fun o' => ∫ x, Kf o' x hv * f o' x ∂μX) o =
      r (remZeroSplit a k Z0 o).1 (remZeroSplit a k Z0 o).2 * Real.exp (-EZ) *
        ∫ x, removedK a k Z0 Kf u c0 r EZ o x hv * f o x ∂μX := by
  set y := (remZeroSplit a k Z0 o).2 with hy
  set R0 := r (remZeroSplit a k Z0 o).1 y with hR0
  set D := remDen a k Z0 r o with hD
  have hI : ∫ w, (∫ x, Kf (remZeroMerge a k Z0 (w, y)) x hv * f (remZeroMerge a k Z0 (w, y)) x ∂μX)
        ∂(outPartMeasure N (Vblk R a k) (· ∈ Z0)) =
      ∫ x, remNum a k Z0 Kf o x hv * f o x ∂μX := by
    rw [integral_integral_swap (hint y)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hfx : ∀ w, f (remZeroMerge a k Z0 (w, y)) x = f o x := fun w =>
      hf _ _ x (by rw [remZeroSplit_merge])
    simp only [hfx]
    rw [integral_mul_const]
    rfl
  have hrhs : ∫ x, removedK a k Z0 Kf u c0 r EZ o x hv * f o x ∂μX =
      Real.exp EZ * u o * c0 o / D * ∫ x, remNum a k Z0 Kf o x hv * f o x ∂μX := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [removedK, hD]
    ring
  have hrc' : R0 = c0 o * R0 := by
    have := hrc (remZeroSplit a k Z0 o)
    rwa [remZeroMerge_split] at this
  have hexp : Real.exp (-EZ) * Real.exp EZ = 1 := by
    rw [← Real.exp_add]; simp
  rw [Rop_remDecomp_apply, hI, hrhs]
  set I := ∫ x, remNum a k Z0 Kf o x hv * f o x ∂μX
  linear_combination (u o * I / D) * hrc' - (u o * I / D * R0 * c0 o) * hexp

end Identity

section LF

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (a : LocalHistory S n M K) (k : ℕ) (Z0 : Set (BlockAt S n M K k))

/-- **The removed kernel of `R`** (P7 (3.7) on `χ_{Z''}`, times `e^{E_k|Z|}`; Lemma III.8.7 for the
removed outcome) as a large-field kernel on the carrier of `KerBound a k`: for the pre-operator
package `P` of the ripe component (`P.T = (K^pre, b^pre)`, internal variables `P.A`), the values
`t, s, z, w` of `χ̃_k, χ_S, χ⁰, χ''`, `u = χ_{Z''}`, `c₀ = χ_{Z₀}`, the reference density `r` and
`EZ = E_k |Z|_k`: kernel `removedK a k Z0 (toRKernel a k P.T.K t s z w) u c0 r EZ`, exponent
`b^pre`.  `EZ = 0` gives P7's `T''_k(Z) χ_{Z''}`. -/
noncomputable def removedKernel (P : OpPkg N R a k) (t s z w : OutT N R a k → SubCfg N a k P.A → ℝ)
    (u c0 : OutT N R a k → ℝ) (r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ) (EZ : ℝ)
    (ht : ∀ o x, 0 ≤ t o x) (hs : ∀ o x, 0 ≤ s o x) (hz : ∀ o x, 0 ≤ z o x)
    (hw : ∀ o x, 0 ≤ w o x) (hu : ∀ o, 0 ≤ u o) (hc0 : ∀ o, 0 ≤ c0 o) (hr : ∀ w y, 0 ≤ r w y)
    (htm : Measurable fun p : OutT N R a k × SubCfg N a k P.A => t p.1 p.2)
    (hsm : Measurable fun p : OutT N R a k × SubCfg N a k P.A => s p.1 p.2)
    (hzm : Measurable fun p : OutT N R a k × SubCfg N a k P.A => z p.1 p.2)
    (hwm : Measurable fun p : OutT N R a k × SubCfg N a k P.A => w p.1 p.2)
    (hum : Measurable u) (hc0m : Measurable c0)
    (hrm : Measurable fun q : OutZero N R a k Z0 × OutRest N R a k Z0 => r q.1 q.2) :
    LFKernel (OutT N R a k) (SubCfg N a k P.A) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N) where
  K := removedK a k Z0 (toRKernel a k P.T.K t s z w) u c0 r EZ
  b := P.T.b
  K_nonneg o x hv :=
    removedK_nonneg a k Z0 (toRKernel_nonneg a k P.T.K_nonneg ht hs hz hw) hu hc0 hr EZ o x hv
  measurable_K hv := measurable_removedK a k Z0 hv
    (measurable_toRKernel a k hv (P.T.measurable_K hv) htm hsm hzm hwm) hum hc0m hrm EZ
  measurable_b := P.T.measurable_b
  analytic_b := P.T.analytic_b
  real_b := P.T.real_b

end LF

section LFProps

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (a : LocalHistory S n M K) (k : ℕ) (Z0 : Set (BlockAt S n M K k))
  (P : OpPkg N R a k) {t s z w : OutT N R a k → SubCfg N a k P.A → ℝ} {u c0 : OutT N R a k → ℝ}
  {r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ} (EZ : ℝ)
  (ht : ∀ o x, 0 ≤ t o x) (hs : ∀ o x, 0 ≤ s o x) (hz : ∀ o x, 0 ≤ z o x)
  (hw : ∀ o x, 0 ≤ w o x) (hu : ∀ o, 0 ≤ u o) (hc0 : ∀ o, 0 ≤ c0 o) (hr : ∀ w y, 0 ≤ r w y)
  (htm : Measurable fun p : OutT N R a k × SubCfg N a k P.A => t p.1 p.2)
  (hsm : Measurable fun p : OutT N R a k × SubCfg N a k P.A => s p.1 p.2)
  (hzm : Measurable fun p : OutT N R a k × SubCfg N a k P.A => z p.1 p.2)
  (hwm : Measurable fun p : OutT N R a k × SubCfg N a k P.A => w p.1 p.2)
  (hum : Measurable u) (hc0m : Measurable c0)
  (hrm : Measurable fun q : OutZero N R a k Z0 × OutRest N R a k Z0 => r q.1 q.2)

/-- The kernel of `removedKernel`: a function of the outputs, the internal variables and `h` only
(it does not depend on `g`). -/
theorem removedKernel_K (o : OutT N R a k) (x : SubCfg N a k P.A) (hv : EuclideanSpace ℝ (Fin N)) :
    (removedKernel a k Z0 P t s z w u c0 r EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm hum hc0m hrm).K
        o x hv =
      Real.exp EZ * u o * c0 o *
        (∫ w', P.T.K (remZeroMerge a k Z0 (w', (remZeroSplit a k Z0 o).2)) x hv *
            ROutcome.weight (t (remZeroMerge a k Z0 (w', (remZeroSplit a k Z0 o).2)) x)
              (s (remZeroMerge a k Z0 (w', (remZeroSplit a k Z0 o).2)) x)
              (z (remZeroMerge a k Z0 (w', (remZeroSplit a k Z0 o).2)) x)
              (w (remZeroMerge a k Z0 (w', (remZeroSplit a k Z0 o).2)) x) ROutcome.toR
          ∂(outPartMeasure N (Vblk R a k) (· ∈ Z0))) /
        ∫ w', r w' (remZeroSplit a k Z0 o).2 ∂(outPartMeasure N (Vblk R a k) (· ∈ Z0)) := rfl

/-- The exponent of `removedKernel` is the exponent `b^pre` of the pre-operator: the external field
`g` enters the removed operator only through `e^{b^pre}`. -/
theorem removedKernel_b :
    (removedKernel a k Z0 P t s z w u c0 r EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm hum hc0m hrm).b =
      P.T.b := rfl

/-- **Support in the domain** (Lemma II.5.9 (d) for the removed kernel): where the removed kernel is
non-zero, `χ_{Z''} ≠ 0`, `χ_{Z₀} ≠ 0`, and there is an output configuration agreeing with `o` off
`Z₀` at which the pre-operator is in its domain (`P.dom`, which is `χ^dom_k(Z, 𝔞)` for the
pre-operator, `preOp_dom_iff_chiDom`) and the "to `R`" weight `χ̃_k χ_S χ⁰ χ''` is non-zero. -/
theorem removedKernel_support {o : OutT N R a k} {x : SubCfg N a k P.A}
    {hv : EuclideanSpace ℝ (Fin N)}
    (h : (removedKernel a k Z0 P t s z w u c0 r EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm hum hc0m
      hrm).K o x hv ≠ 0) :
    u o ≠ 0 ∧ c0 o ≠ 0 ∧ ∃ o' : OutT N R a k,
      (remZeroSplit a k Z0 o').2 = (remZeroSplit a k Z0 o).2 ∧ P.dom o' x ∧
        ROutcome.weight (t o' x) (s o' x) (z o' x) (w o' x) ROutcome.toR ≠ 0 := by
  obtain ⟨h1, h2, w', hK⟩ := removedK_ne_zero a k Z0 h
  refine ⟨h1, h2, remZeroMerge a k Z0 (w', (remZeroSplit a k Z0 o).2),
    by rw [remZeroSplit_merge], ?_, ?_⟩
  · by_contra hd
    exact hK (by simp [toRKernel, P.vanish _ _ hv hd])
  · intro hw0
    exact hK (by simp [toRKernel, hw0])

/-- **Vanishing off the domain**: if the domain of the pre-operator does not read `ψ_k↾Z₀`
(Lemma III.1.5, P7 p. 517), the removed kernel vanishes off it. -/
theorem removedKernel_vanish (hdom : ∀ o o' x, (remZeroSplit a k Z0 o).2 = (remZeroSplit a k Z0 o').2 →
      (P.dom o x ↔ P.dom o' x))
    (o : OutT N R a k) (x : SubCfg N a k P.A) (hv : EuclideanSpace ℝ (Fin N)) (hd : ¬ P.dom o x) :
    (removedKernel a k Z0 P t s z w u c0 r EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm hum hc0m
      hrm).K o x hv = 0 := by
  by_contra h
  obtain ⟨-, -, o', ho', hd', -⟩ :=
    removedKernel_support a k Z0 P EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm hum hc0m hrm h
  exact hd ((hdom o' o x ho').1 hd')

/-- **The removed operator is the removed part of `R` applied to the pre-operator**
(`Rop_remDecomp_removed` for `removedKernel`): for the term
`ρ(o) = ∫ dx K^pre(o, x) χ̃_k χ_S χ⁰ χ''(o, x) f(o, x)` of the pre-operator against a function `f`
that does not read `ψ_k↾Z₀`, `χ_{Z''}(o) R[ρ](o) = ρ_{k,0}(Z)(o) e^{-EZ} ∫ dx K^rem(o, x) f(o, x)`. -/
theorem Rop_remDecomp_removedKernel (hv : EuclideanSpace ℝ (Fin N))
    (f : OutT N R a k → SubCfg N a k P.A → ℝ)
    (hf : ∀ o o' x, (remZeroSplit a k Z0 o).2 = (remZeroSplit a k Z0 o').2 → f o x = f o' x)
    (hint : ∀ y : OutRest N R a k Z0, Integrable
      (fun q : OutZero N R a k Z0 × SubCfg N a k P.A =>
        toRKernel a k P.T.K t s z w (remZeroMerge a k Z0 (q.1, y)) q.2 hv *
          f (remZeroMerge a k Z0 (q.1, y)) q.2)
      ((outPartMeasure N (Vblk R a k) (· ∈ Z0)).prod (subMeasure N a k P.A)))
    (hrc : ∀ q : OutZero N R a k Z0 × OutRest N R a k Z0,
      r q.1 q.2 = c0 (remZeroMerge a k Z0 q) * r q.1 q.2)
    (o : OutT N R a k) :
    u o * Rop (remDecomp a k Z0 r)
        (fun o' => ∫ x, toRKernel a k P.T.K t s z w o' x hv * f o' x ∂(subMeasure N a k P.A)) o =
      r (remZeroSplit a k Z0 o).1 (remZeroSplit a k Z0 o).2 * Real.exp (-EZ) *
        ∫ x, (removedKernel a k Z0 P t s z w u c0 r EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm hum
          hc0m hrm).K o x hv * f o x ∂(subMeasure N a k P.A) :=
  Rop_remDecomp_removed a k Z0 (subMeasure N a k P.A) (toRKernel a k P.T.K t s z w) u c0 r EZ hv f
    hf hint hrc o

end LFProps

end Balaban.LargeField
