module

public import Balaban.LargeField.Base.BaseRecord
public import Balaban.LargeField.Operators.StepData
public import Balaban.LargeField.Operators.QuietSymm
public import Balaban.LargeField.Operators.QuietInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The witness functions of the base kernel (LF-RECONSTRUCTION (II.7.4), Lemma II.7.7 (a))

The base kernel has the Gaussian structure (S1) of version 1.2:
`K_0(Z') = ∏_y z^N t_0(z ψ_1(y), (Qφ)(y)) · ∑_w F^w_0(u) K̃^w_0(Z')`, where `w` runs over the maps
`P_1 ∩ Z' → {blk, bd}` (the witness type of each cube), and
```
F^w_0(u) = ∏_{□' ∈ P_1, w = blk} (1 - A(□')) · ∏_{□' ∈ P_1, w = bd} A(□') · ∏_{□' ⊂ Ω^c ∖ P_1} A(□'),
```
with `A(□')` the block condition `|u_y| < 2 δ₀` for the Gaussian blocks `y` of the cube.

* `BaseW`, `baseF`: the index type `{blk, bd}^{P_1 ∩ Z'}` (`true` = `blk`) and `F^w_0`, as a `GaussWit`
  function of `u = (u_y)`;
* `baseF_mem_unit`, `measurable_baseF`, `baseF_rot`: `F^w_0 ∈ [0, 1]`, Borel, `O(N)`-invariant;
* `baseF_decomposition`: `∑_w F^w_0(u) ∏_{□' ∈ P_1, w = bd} (1 - B(□')) · ∏_{Ω^c ∖ P_1} B(□')
  = ∏_{□' ∈ P_1} (1 - A B)(□') · ∏_{Ω^c ∖ P_1} (A B)(□')`, i.e. the witness decomposition
  `χ'^{(0)c}(□') = (1 - A) + A (1 - B)` reproduces `χ'^{(0)c}(P_1) χ'^{(0)}(P_1^c ∩ Ω^c)` of
  Definition II.7.1;
* `baseBlockProp_iff`: `A(□')` of `F^w_0` is the block factor `chiBlockA` of Definition II.7.1.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory

section Witness

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  (a : LocalHistory S n M K) (k : ℕ)

open Classical in
/-- The cubes of `P_{k+1} ∩ Z'` (all sites of the cube lie in the record `P` of the localized
history). -/
noncomputable def basePCubes : Finset (Torus S.d (n (k + 1))) :=
  cubeFin {c | CubeSub (S := S) (n := n) M K (k + 1) c (a.P k)}

open Classical in
/-- The cubes of `(Ω^c_{k+1} ∖ P_{k+1}) ∩ Z'`. -/
noncomputable def baseOCubes : Finset (Torus S.d (n (k + 1))) :=
  cubeFin {c | CubeSub (S := S) (n := n) M K (k + 1) c (a.Z (k + 1) \ a.Omega k)} \ basePCubes a k

/-- The witness types: a map `P_{k+1} ∩ Z' → {blk, bd}` (`true` = `blk`, `false` = `bd`). -/
abbrev BaseW : Type := ↥(basePCubes a k) → Bool

/-- The block condition `A(□')` in terms of the Gaussian differences `u_y = z ψ_{k+1}(y) - (Qψ_k)(y)`:
`|u_y| < 2 δ₀` for every Gaussian block `y` of the cube. -/
def BaseBlockProp (δ₀ : ℝ) (u : gaussBlocks a k → EuclideanSpace ℝ (Fin N))
    (c : Torus S.d (n (k + 1))) : Prop :=
  ∀ y : gaussBlocks a k, blockCube S n M K (k + 1) y.1 = c → ‖u y‖ < 2 * δ₀

open Classical in
/-- The indicator of `A(□')`. -/
noncomputable def baseA (δ₀ : ℝ) (c : Torus S.d (n (k + 1)))
    (u : gaussBlocks a k → EuclideanSpace ℝ (Fin N)) : ℝ :=
  charFn (fun u => BaseBlockProp a k δ₀ u c) u

open Classical in
/-- **The witness functions `F^w_0` of (II.7.4)** (Lemma II.7.7 (a)). -/
noncomputable def baseF (δ₀ : ℝ) (w : BaseW a k)
    (u : gaussBlocks a k → EuclideanSpace ℝ (Fin N)) : ℝ :=
  (∏ c : ↥(basePCubes a k), if w c then 1 - baseA a k δ₀ c.1 u else baseA a k δ₀ c.1 u) *
    ∏ c ∈ baseOCubes a k, baseA a k δ₀ c u

theorem baseA_mem_unit (δ₀ : ℝ) (c : Torus S.d (n (k + 1)))
    (u : gaussBlocks a k → EuclideanSpace ℝ (Fin N)) :
    0 ≤ baseA a k δ₀ c u ∧ baseA a k δ₀ c u ≤ 1 :=
  ⟨charFn_nonneg' _ _, charFn_le_one' _ _⟩

theorem baseF_mem_unit (δ₀ : ℝ) (w : BaseW a k) (u : gaussBlocks a k → EuclideanSpace ℝ (Fin N)) :
    0 ≤ baseF a k δ₀ w u ∧ baseF a k δ₀ w u ≤ 1 := by
  classical
  unfold baseF
  refine unit_mul ⟨Finset.prod_nonneg fun c _ => ?_, Finset.prod_le_one₀ (fun c _ => ?_) fun c _ => ?_⟩
    ⟨Finset.prod_nonneg fun c _ => (baseA_mem_unit a k δ₀ c u).1,
      Finset.prod_le_one₀ (fun c _ => (baseA_mem_unit a k δ₀ c u).1)
        fun c _ => (baseA_mem_unit a k δ₀ c u).2⟩
  · have := baseA_mem_unit a k δ₀ c.1 u
    split_ifs <;> linarith
  · have := baseA_mem_unit a k δ₀ c.1 u
    split_ifs <;> linarith
  · have := baseA_mem_unit a k δ₀ c.1 u
    split_ifs <;> linarith

theorem measurableSet_baseBlockProp (δ₀ : ℝ) (c : Torus S.d (n (k + 1))) :
    MeasurableSet {u : gaussBlocks a k → EuclideanSpace ℝ (Fin N) | BaseBlockProp a k δ₀ u c} := by
  classical
  have : {u : gaussBlocks a k → EuclideanSpace ℝ (Fin N) | BaseBlockProp a k δ₀ u c} =
      ⋂ y : gaussBlocks a k, {u | blockCube S n M K (k + 1) y.1 = c → ‖u y‖ < 2 * δ₀} := by
    ext u; simp [BaseBlockProp]
  rw [this]
  refine MeasurableSet.iInter fun y => ?_
  by_cases hy : blockCube S n M K (k + 1) y.1 = c
  · simp only [hy, forall_true_left]
    exact measurableSet_lt ((measurable_norm.comp (measurable_pi_apply y))) measurable_const
  · simp [hy]

theorem measurable_baseA (δ₀ : ℝ) (c : Torus S.d (n (k + 1))) :
    Measurable (baseA (N := N) a k δ₀ c) := by
  classical
  unfold baseA charFn
  exact (measurable_const.indicator (measurableSet_baseBlockProp a k δ₀ c))

theorem measurable_baseF (δ₀ : ℝ) (w : BaseW a k) : Measurable (baseF (N := N) a k δ₀ w) := by
  classical
  unfold baseF
  refine Measurable.mul (Finset.measurable_prod _ fun c _ => ?_)
    (Finset.measurable_prod _ fun c _ => measurable_baseA a k δ₀ c)
  split_ifs
  · exact measurable_const.sub (measurable_baseA a k δ₀ c.1)
  · exact measurable_baseA a k δ₀ c.1

/-- `O(N)`-invariance of `F^w_0`: rotating all the `u_y`. -/
theorem baseF_rot (δ₀ : ℝ) (w : BaseW a k) (ρ : OrthN N)
    (u : gaussBlocks a k → EuclideanSpace ℝ (Fin N)) :
    baseF a k δ₀ w (fun y => ρ (u y)) = baseF a k δ₀ w u := by
  classical
  have hA : ∀ c, baseA a k δ₀ c (fun y => ρ (u y)) = baseA a k δ₀ c u := by
    intro c
    unfold baseA charFn
    simp only [Set.indicator, Set.mem_ofPred_eq, BaseBlockProp, LinearIsometryEquiv.norm_map]
    congr 1
  unfold baseF
  simp only [hA]

/-- **The witness decomposition** `χ'^{(0)c}(□') = (1 - A) + A (1 - B)` for the cubes of `P_1`
(and `A B` on the cubes of `Ω^c ∖ P_1`): for every function `B` of the cubes,
`∑_w F^w_0(u) ∏_{w = bd} (1 - B) ∏_{Ω^c ∖ P_1} B = ∏_{P_1} (1 - A B) ∏_{Ω^c ∖ P_1} (A B)`. -/
theorem baseF_decomposition (δ₀ : ℝ) (B : Torus S.d (n (k + 1)) → ℝ)
    (u : gaussBlocks a k → EuclideanSpace ℝ (Fin N)) :
    ∑ w : BaseW a k, baseF a k δ₀ w u *
        ((∏ c : ↥(basePCubes a k), if w c then 1 else 1 - B c.1) * ∏ c ∈ baseOCubes a k, B c) =
      (∏ c : ↥(basePCubes a k), (1 - baseA a k δ₀ c.1 u * B c.1)) *
        ∏ c ∈ baseOCubes a k, (baseA a k δ₀ c u * B c) := by
  classical
  set Ac : Torus S.d (n (k + 1)) → ℝ := fun c => baseA a k δ₀ c u with hAc
  have h1 : ∀ w : BaseW a k, baseF a k δ₀ w u *
      ((∏ c : ↥(basePCubes a k), if w c then 1 else 1 - B c.1) * ∏ c ∈ baseOCubes a k, B c) =
      (∏ c : ↥(basePCubes a k), (if w c then 1 - Ac c.1 else Ac c.1 * (1 - B c.1))) *
        ∏ c ∈ baseOCubes a k, (Ac c * B c) := by
    intro w
    unfold baseF
    rw [Finset.prod_mul_distrib (s := baseOCubes a k) (f := Ac) (g := B)]
    have e : (∏ c : ↥(basePCubes a k), (if w c then 1 - Ac c.1 else Ac c.1 * (1 - B c.1))) =
        (∏ c : ↥(basePCubes a k), if w c then 1 - Ac c.1 else Ac c.1) *
          ∏ c : ↥(basePCubes a k), (if w c then 1 else 1 - B c.1) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun c _ => ?_
      split_ifs <;> ring
    rw [e]
    ring
  simp_rw [h1]
  rw [← Finset.sum_mul]
  have h2 : ∑ w : BaseW a k, ∏ c : ↥(basePCubes a k),
      (if w c then 1 - Ac c.1 else Ac c.1 * (1 - B c.1)) =
      ∏ c : ↥(basePCubes a k), (1 - Ac c.1 * B c.1) := by
    have := Finset.prod_univ_sum (fun _ : ↥(basePCubes a k) => (Finset.univ : Finset Bool))
      (fun (c : ↥(basePCubes a k)) (b : Bool) =>
        if b then 1 - Ac c.1 else Ac c.1 * (1 - B c.1))
    rw [Fintype.piFinset_univ] at this
    rw [← this]
    refine Finset.prod_congr rfl fun c _ => ?_
    simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
    ring
  rw [h2]

/-! ### The block condition of `F^w_0` is the factor `A(□')` of Definition II.7.1 -/

theorem rn_eq_norm (v : EuclideanSpace ℝ (Fin N)) : rn (fun i => v i) = ‖v‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold rn
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

open Classical in
/-- **`A(□')` of Definition II.7.1 is the block condition of `F^w_0`.**  For a cube `c` lying in
`Ω^c_1 ∩ Z'`, the condition `|u_y| < 2 δ₀` on the Gaussian differences
`u_y = z_1 ψ_1(y) - (Q φ)(y)` (the spins `φ = ψ_0` being the large-field variables of scale `0`) is
`ChiBlockProp` for the block field `θ = z_1 ψ_1`. -/
theorem baseBlockProp_iff {R : ℕ → ℝ} (δ₀ z : ℝ) (hK : 1 ≤ K)
    (o : OutT N R a 1) (x : NewCfg N a 0) (c : Torus S.d (n 1))
    (hc : CubeSub (S := S) (n := n) M K 1 c (a.Z 1 \ a.Omega 0))
    (hnn : ∀ i, n i = S.L * n (i + 1)) :
    BaseBlockProp a 0 δ₀ (fun y => gaussArg N z o x y.1) c ↔
      ChiBlockProp n S.L M K δ₀ (fun s i => subVarField N x 0 s i)
        (fun y i => (z • outField N o y) i) c := by
  have hgb : ∀ y : BlockAt S n M K 1, blockCube S n M K 1 y = c → y ∈ gaussBlocks a 0 := by
    intro y hy x0 hx0
    have h1 := blockCube_eq_cubeMap hnn hK hx0
    exact hc x0 (h1.symm.trans hy)
  unfold BaseBlockProp ChiBlockProp
  constructor
  · intro h y hy
    have := h ⟨y, hgb y hy⟩ hy
    have e : (fun i => (z • outField N o y) i - spinAverage n S.L M K (fun s i => subVarField N x 0 s i) y i)
        = fun i => (gaussArg N z o x y) i := by
      funext i
      simp only [gaussArg, qCoarseK, spinAverage, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
        WithLp.ofLp_sum, Finset.sum_apply]
      rfl
    rw [e, rn_eq_norm]
    exact this
  · intro h y hy
    have := h y.1 hy
    have e : (fun i => (z • outField N o y.1) i - spinAverage n S.L M K (fun s i => subVarField N x 0 s i) y.1 i)
        = fun i => (gaussArg N z o x y.1) i := by
      funext i
      simp only [gaussArg, qCoarseK, spinAverage, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
        WithLp.ofLp_sum, Finset.sum_apply]
      rfl
    rw [e, rn_eq_norm] at this
    exact this

end Witness

end Balaban.LargeField
