module

public import Balaban.LargeField.Operators.QuietInt
public import Balaban.LargeField.R.SmallFactorChi

/-!
# Volumes of the window variables of the removed outcome (Lemma III.8.7, step (3))

Every window variable lies in a shell `{u : |u·u - 1| < t}` ((1.24) in `χ^new`) or in a ball
(`χ''`), and the Lebesgue measure of the set of configurations of all the variables of an
`outPartMeasure` or a `subMeasure` with each variable in its set is the product of the volumes of
the sets, hence at most `1` when each volume is at most `1`.  The radii may depend on the
variable (they are `3dLδ_j` or `δ_{j,1}` with `j` the layer of the variable).

* `outPartMeasure_pi_le_one`, `subMeasure_pi_le_one`: the product-set bound.
* `outPartMeasure_shell_le_one`, `subMeasure_shell_le_one`: shells, under `c_N t ≤ 1`.
* `outPartMeasure_ball_le_one`, `subMeasure_ball_le_one`: balls about a centre, under `v_N r^N ≤ 1`.
* `chiDD_norm_lt`: the ball condition `‖δψ(y)‖ < δ_{j,1}` from `χ'' = 1`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory ENNReal

section Generic

variable {N : ℕ}

theorem volume_ball_eq (hN : 0 < N) (c : EuclideanSpace ℝ (Fin N)) (r : ℝ) :
    volume (Metric.ball c r) =
      ENNReal.ofReal r ^ N * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
  simp

theorem volume_ball_le_one (hN : 0 < N) (c : EuclideanSpace ℝ (Fin N)) {r : ℝ}
    (h : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal * r ^ N ≤ 1) :
    volume (Metric.ball c r) ≤ 1 := by
  rw [volume_ball_eq hN]
  have hfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1) ≠ ∞ := measure_ball_lt_top.ne
  rcases le_or_gt r 0 with hr | hr
  · rw [ENNReal.ofReal_of_nonpos hr, zero_pow hN.ne']; simp
  · rw [← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_one.mpr (by rw [mul_comm]; exact h)

end Generic

section Vars

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}

/-- **Product-set bound for output variables**: if each output variable `o y` lies in a measurable
set `s y` of volume at most `1`, the `outPartMeasure` of the set of such configurations is at
most `1`. -/
theorem outPartMeasure_pi_le_one {α : Type} [Finite α] (V : Set α) (P : α → Prop)
    (s : {y : α // y ∈ V ∧ P y} → Set (EuclideanSpace ℝ (Fin N))) (h : ∀ y, volume (s y) ≤ 1) :
    outPartMeasure N V P {o | ∀ y, o y ∈ s y} ≤ 1 := by
  unfold outPartMeasure
  let _ : Fintype {y : α // y ∈ V ∧ P y} := Fintype.ofFinite _
  have : {o : OutPart N V P | ∀ y, o y ∈ s y} = Set.pi Set.univ s := by
    ext o; simp
  rw [this]
  exact pi_pi_le_one (fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) s h

/-- **Product-set bound for internal variables** (non-spin variables, Lebesgue measure). -/
theorem subMeasure_pi_le_one (a : LocalHistory S n M K) {k : ℕ} (A : Set (InternalVars a k))
    (hA : ∀ p ∈ A, p.isSpin = false) (s : A → Set (EuclideanSpace ℝ (Fin N)))
    (hs : ∀ p, MeasurableSet (s p)) (h : ∀ p, volume (s p) ≤ 1) :
    subMeasure N a k A {x | ∀ p : A, VarVal.toEuc (x p) ∈ s p} ≤ 1 := by
  have hset : {x : SubCfg N a k A | ∀ p : A, VarVal.toEuc (x p) ∈ s p} =
      Set.pi Set.univ (fun p : A => (VarVal.toEuc : VarVal N p.1.isSpin → _) ⁻¹' s p) := by
    ext x; simp
  rw [hset]
  unfold subMeasure
  refine pi_pi_le_one (fun p : A => varMeasure N p.1.isSpin) _ fun p => ?_
  rw [(measurePreserving_toEuc_false (N := N) _ (hA p.1 p.2)).measure_preimage
    (hs p).nullMeasurableSet]
  exact h p

/-- **Shells, output variables**: each output variable in its shell `{|u·u - 1| < t y}` with
`0 < t y ≤ 1/2`, `c_N t y ≤ 1`: the configurations have measure at most `1`. -/
theorem outPartMeasure_shell_le_one (hN : 2 ≤ N) {α : Type} [Finite α] (V : Set α) (P : α → Prop)
    (t : {y : α // y ∈ V ∧ P y} → ℝ) (ht : ∀ y, 0 < t y) (ht1 : ∀ y, t y ≤ 1 / 2)
    (hct : ∀ y, cShell N * t y ≤ 1) :
    outPartMeasure N V P {o | ∀ y, |‖o y‖ ^ 2 - 1| < t y} ≤ 1 := by
  have := outPartMeasure_pi_le_one (N := N) V P (fun y => shellSet N (t y))
    (fun y => (volume_shellSet_le N hN (ht y) (ht1 y)).trans (ENNReal.ofReal_le_one.mpr (hct y)))
  exact this

/-- **The shells of a finite family of non-spin variables have measure at most `1`.** -/
theorem pi_shell_le_one (hN : 2 ≤ N) {ι : Type} [Fintype ι] (b : ι → Bool) (hb : ∀ i, b i = false)
    (t : ι → ℝ) (ht : ∀ i, 0 < t i) (ht1 : ∀ i, t i ≤ 1 / 2) (hct : ∀ i, cShell N * t i ≤ 1) :
    (Measure.pi fun i => varMeasure N (b i))
      {x | ∀ i, |‖VarVal.toEuc (x i)‖ ^ 2 - 1| < t i} ≤ 1 := by
  have hset : {x : ∀ i, VarVal N (b i) | ∀ i, |‖VarVal.toEuc (x i)‖ ^ 2 - 1| < t i} =
      Set.pi Set.univ (fun i => (VarVal.toEuc : VarVal N (b i) → EuclideanSpace ℝ (Fin N)) ⁻¹'
        shellSet N (t i)) := by
    ext x; simp [shellSet]
  rw [hset]
  refine pi_pi_le_one (fun i => varMeasure N (b i)) _ fun i => ?_
  rw [(measurePreserving_toEuc_false (N := N) _ (hb i)).measure_preimage
    (measurableSet_shellSet N (t i)).nullMeasurableSet]
  exact (volume_shellSet_le N hN (ht i) (ht1 i)).trans (ENNReal.ofReal_le_one.mpr (hct i))

/-- **Shells, internal variables** (non-spin). -/
theorem subMeasure_shell_le_one (hN : 2 ≤ N) (a : LocalHistory S n M K) {k : ℕ}
    (A : Set (InternalVars a k)) (hA : ∀ p ∈ A, p.isSpin = false) (t : A → ℝ)
    (ht : ∀ p, 0 < t p) (ht1 : ∀ p, t p ≤ 1 / 2) (hct : ∀ p, cShell N * t p ≤ 1) :
    subMeasure N a k A {x | ∀ p : A, |‖VarVal.toEuc (x p)‖ ^ 2 - 1| < t p} ≤ 1 := by
  unfold subMeasure
  exact pi_shell_le_one hN (fun p : A => p.1.isSpin) (fun p => hA p.1 p.2) t ht ht1 hct

/-- **Balls, output variables**: `‖o y - c y‖ < r y` with `v_N (r y)^N ≤ 1`. -/
theorem outPartMeasure_ball_le_one (hN : 0 < N) {α : Type} [Finite α] (V : Set α) (P : α → Prop)
    (c : {y : α // y ∈ V ∧ P y} → EuclideanSpace ℝ (Fin N)) (r : {y : α // y ∈ V ∧ P y} → ℝ)
    (h : ∀ y, (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal * r y ^ N ≤ 1) :
    outPartMeasure N V P {o | ∀ y, ‖o y - c y‖ < r y} ≤ 1 := by
  have := outPartMeasure_pi_le_one (N := N) V P (fun y => Metric.ball (c y) (r y))
    (fun y => volume_ball_le_one hN (c y) (h y))
  simpa [Metric.mem_ball, dist_eq_norm] using this

/-- **Balls, internal variables** (non-spin): `‖x p - c p‖ < r p` with `v_N (r p)^N ≤ 1`. -/
theorem subMeasure_ball_le_one (hN : 0 < N) (a : LocalHistory S n M K) {k : ℕ}
    (A : Set (InternalVars a k)) (hA : ∀ p ∈ A, p.isSpin = false)
    (c : A → EuclideanSpace ℝ (Fin N)) (r : A → ℝ)
    (h : ∀ p, (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal * r p ^ N ≤ 1) :
    subMeasure N a k A {x | ∀ p : A, ‖VarVal.toEuc (x p) - c p‖ < r p} ≤ 1 := by
  have := subMeasure_pi_le_one a A hA (fun p => Metric.ball (c p) (r p))
    (fun p => Metric.isOpen_ball.measurableSet) (fun p => volume_ball_le_one hN (c p) (h p))
  simpa [Metric.mem_ball, dist_eq_norm] using this

end Vars

section ChiDDBall

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {ϱ : ℝ}

/-- **The ball of `χ''`** (Definition III.5.1 item 4): on `χ'' = 1` the field `δψ` at a block `y`
of `D''` of layer `j` has norm `< δ_{j,1}`. -/
theorem chiDD_norm_lt (a : LocalHistory S n M K) (k : ℕ)
    (B : GeneratingSet S.d S.L (M * n K) K ϱ) (Zk1 Lam U3 : Set (Torus S.d (M * n K * S.L ^ K)))
    (δ1 : ℕ → ℝ) (dpsi : MultiField S n M K N) (h : chiDD a k B Zk1 Lam U3 δ1 dpsi = 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hjK : j ≤ K) (y : BlockAt S n M K j)
    (hy : BlockSub (S := S) (n := n) (M := M) (K := K) j y
      (ddRegion a k B Zk1 Lam U3 ∩ {x | x ∈ B.layer j})) : ‖dpsi j y‖ < δ1 j := by
  classical
  have hP : ChiDDProp a k B Zk1 Lam U3 δ1 dpsi := by
    by_contra hn
    unfold chiDD at h
    rw [charFn_apply] at h
    simp [hn] at h
  exact hP j hj1 hjK y hy

end ChiDDBall

end Balaban.LargeField
