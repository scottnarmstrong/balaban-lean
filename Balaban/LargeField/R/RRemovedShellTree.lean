module

public import Balaban.LargeField.R.RRemovedShell
public import Balaban.LargeField.R.SmallFactorChi
public import Mathlib.MeasureTheory.Constructions.Pi
public import Balaban.LargeField.Operators.PiTools

/-!
# Spanning-tree balls (Lemma III.8.7, step (3), `ψ_k` on `Z^c_0 ∩ Z`)
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory ENNReal

section Tree

variable {N : ℕ}

theorem measurableSet_treeSet {ι ρ : Type} [Finite ι] (e : ρ → EuclideanSpace ℝ (Fin N))
    (par : ι → ι ⊕ ρ) (r : ι → ℝ) :
    MeasurableSet {ψ : ι → EuclideanSpace ℝ (Fin N) |
      ∀ i, ‖ψ i - Sum.elim ψ e (par i)‖ < r i} := by
  have hm : ∀ i, Measurable fun ψ : ι → EuclideanSpace ℝ (Fin N) => Sum.elim ψ e (par i) := by
    intro i
    cases h : par i with
    | inl j => simp only [Sum.elim_inl]; exact measurable_pi_apply j
    | inr c => simp only [Sum.elim_inr]; exact measurable_const
  simp_rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i =>
    measurableSet_lt ((measurable_pi_apply i).sub (hm i)).norm measurable_const

theorem pi_treeSet_le (hN : 0 < N) : ∀ (m : ℕ) {ι : Type} [Fintype ι], Fintype.card ι = m →
    ∀ {ρ : Type} (e : ρ → EuclideanSpace ℝ (Fin N)) (par : ι → ι ⊕ ρ) (rk : ι → ℕ)
      (_ : ∀ i j, par i = Sum.inl j → rk j < rk i) (r : ι → ℝ),
      Measure.pi (fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N))))
        {ψ | ∀ i, ‖ψ i - Sum.elim ψ e (par i)‖ < r i} ≤
        ∏ i, volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) (r i)) := by
  classical
  intro m
  induction m with
  | zero =>
    intro ι _ hcard ρ e par rk hrk r
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    rw [Measure.pi_of_empty]
    simp
  | succ m ih =>
    intro ι _ hcard ρ e par rk hrk r
    have hne : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨a, -, hamax⟩ := Finset.exists_max_image Finset.univ rk ⟨hne.some, Finset.mem_univ _⟩
    have hpar : ∀ i : {i // i ≠ a}, ∀ j, par i.1 = Sum.inl j → j ≠ a := by
      intro i j h hj
      have h1 := hrk i.1 j h
      have h2 := hamax i.1 (Finset.mem_univ _)
      subst hj
      omega
    let par' : {i // i ≠ a} → {i // i ≠ a} ⊕ ρ := fun i =>
      match h : par i.1 with
      | Sum.inl j => Sum.inl ⟨j, hpar i j h⟩
      | Sum.inr c => Sum.inr c
    have hpara : ∀ j, par a = Sum.inl j → j ≠ a := by
      intro j h hj
      have := hrk a j h
      subst hj
      omega
    have hcard' : Fintype.card {i // i ≠ a} = m := by
      have := Fintype.card_subtype_compl (fun i : ι => i = a)
      simp only [Fintype.card_subtype_eq] at this
      simp only [ne_eq]
      omega
    have hp'l : ∀ (i : {i // i ≠ a}) (j' : ι) (h : par i.1 = Sum.inl j'),
        par' i = Sum.inl ⟨j', hpar i j' h⟩ := by
      intro i j' h
      simp only [par']
      split
      · rename_i j'' hj''
        have := Sum.inl.inj (h.symm.trans hj'')
        subst this
        rfl
      · rename_i c hc
        rw [h] at hc
        exact absurd hc (by simp)
    have hp'r : ∀ (i : {i // i ≠ a}) (c : ρ) (h : par i.1 = Sum.inr c), par' i = Sum.inr c := by
      intro i c h
      simp only [par']
      split
      · rename_i j'' hj''
        rw [h] at hj''
        exact absurd hj'' (by simp)
      · rename_i c' hc'
        have := Sum.inr.inj (h.symm.trans hc')
        rw [this]
    have hT'le := ih hcard' e par' (fun i => rk i.1) (by
      intro i j h
      obtain ⟨j', hj'⟩ : ∃ j', par i.1 = Sum.inl j' := by
        cases hc : par i.1 with
        | inl j' => exact ⟨j', rfl⟩
        | inr c => rw [hp'r i c hc] at h; exact absurd h (by simp)
      rw [hp'l i j' hj'] at h
      have := Sum.inl.inj h
      subst this
      exact hrk i.1 j' hj') (fun i => r i.1)
    let E := EuclideanSpace ℝ (Fin N)
    let T : Set (ι → E) := {ψ | ∀ i, ‖ψ i - Sum.elim ψ e (par i)‖ < r i}
    let T' : Set ({i // i ≠ a} → E) :=
      {z | ∀ i, ‖z i - Sum.elim z e (par' i)‖ < r i.1}
    have hTm : MeasurableSet T := measurableSet_treeSet e par r
    have hT'm : MeasurableSet T' := measurableSet_treeSet e par' (fun i => r i.1)
    let mg : ({i // i ≠ a} → E) → ({i // ¬ i ≠ a} → E) → ι → E := fun z w =>
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => E) (fun i => i ≠ a)).symm (z, w)
    have hmg1 : ∀ z w (i : {i // i ≠ a}), mg z w i.1 = z i := by
      intro z w i
      simp [mg, MeasurableEquiv.piEquivPiSubtypeProd, i.2]
    have hmg2 : ∀ z w, mg z w a = w ⟨a, not_not.2 rfl⟩ := by
      intro z w
      simp [mg, MeasurableEquiv.piEquivPiSubtypeProd]
    have hval : ∀ z w (i : {i // i ≠ a}),
        Sum.elim (mg z w) e (par i.1) = Sum.elim z e (par' i) := by
      intro z w i
      cases hc : par i.1 with
      | inl j' => rw [hp'l i j' hc]; simp [hmg1 z w ⟨j', hpar i j' hc⟩]
      | inr c => rw [hp'r i c hc]; simp
    have hvala : ∀ z w w', Sum.elim (mg z w) e (par a) = Sum.elim (mg z w') e (par a) := by
      intro z w w'
      cases hc : par a with
      | inl j' => simp [hmg1 z w ⟨j', hpara j' hc⟩, hmg1 z w' ⟨j', hpara j' hc⟩]
      | inr c => simp
    let g : ({i // i ≠ a} → E) → E := fun z => Sum.elim (mg z 0) e (par a)
    have : Unique {i // ¬ i ≠ a} :=
      ⟨⟨⟨a, not_not.2 rfl⟩⟩, fun b => Subtype.ext (not_not.1 b.2)⟩
    let B : ({i // i ≠ a} → E) → Set ({i // ¬ i ≠ a} → E) := fun z =>
      Set.pi Set.univ (fun _ => Metric.ball (g z) (r a))
    have hpt : ∀ z w, T.indicator (1 : (ι → E) → ℝ≥0∞) (mg z w) ≤
        T'.indicator 1 z * (B z).indicator 1 w := by
      intro z w
      by_cases hm : mg z w ∈ T
      · rw [Set.indicator_of_mem hm]
        have hz : z ∈ T' := by
          intro i
          have := hm i.1
          rwa [hmg1, hval] at this
        have hw : w ∈ B z := by
          intro b _
          have hb : b = ⟨a, not_not.2 rfl⟩ := Subtype.ext (not_not.1 b.2)
          have := hm a
          rw [hmg2, hvala z w 0] at this
          rw [hb, Metric.mem_ball, dist_eq_norm]
          exact this
        rw [Set.indicator_of_mem hz, Set.indicator_of_mem hw]
        simp
      · rw [Set.indicator_of_notMem hm]
        exact zero_le
    have hVa : ∀ z, Measure.pi (fun _ : {i // ¬ i ≠ a} => (volume : Measure E)) (B z) =
        volume (Metric.ball (0 : E) (r a)) := by
      intro z
      simp only [B]
      rw [Measure.pi_pi, Fintype.prod_unique, volume_ball_eq hN (g z) (r a), volume_ball_eq hN 0 (r a)]
    have hfirst : Measure.pi (fun _ : ι => (volume : Measure E)) T =
        ∫⁻ z, ∫⁻ w, T.indicator 1 (mg z w) ∂(Measure.pi fun _ : {i // ¬ i ≠ a} => (volume : Measure E))
          ∂(Measure.pi fun _ : {i // i ≠ a} => (volume : Measure E)) := by
      rw [← lintegral_indicator_one hTm]
      exact PiTools.lintegral_split (fun _ => (volume : Measure E)) (fun i => i ≠ a)
        (T.indicator 1) (measurable_one.indicator hTm)
    calc Measure.pi (fun _ : ι => (volume : Measure E)) T
        = _ := hfirst
      _ ≤ ∫⁻ z, T'.indicator 1 z * volume (Metric.ball (0 : E) (r a))
          ∂(Measure.pi fun _ : {i // i ≠ a} => (volume : Measure E)) := by
          refine lintegral_mono fun z => ?_
          calc ∫⁻ w, T.indicator 1 (mg z w) ∂_
              ≤ ∫⁻ w, T'.indicator 1 z * (B z).indicator 1 w ∂_ := lintegral_mono (hpt z)
            _ = T'.indicator 1 z * volume (Metric.ball (0 : E) (r a)) := by
                rw [lintegral_const_mul _ (measurable_one.indicator
                  (MeasurableSet.univ_pi fun _ => Metric.isOpen_ball.measurableSet)),
                  lintegral_indicator_one (MeasurableSet.univ_pi fun _ =>
                    Metric.isOpen_ball.measurableSet), hVa]
      _ = (∫⁻ z, T'.indicator 1 z ∂(Measure.pi fun _ : {i // i ≠ a} => (volume : Measure E))) *
            volume (Metric.ball (0 : E) (r a)) := by
          rw [lintegral_mul_const _ (measurable_one.indicator hT'm)]
      _ ≤ (∏ i : {i // i ≠ a}, volume (Metric.ball (0 : E) (r i.1))) *
            volume (Metric.ball (0 : E) (r a)) := by
          gcongr
          rw [lintegral_indicator_one hT'm]
          exact hT'le
      _ = ∏ i, volume (Metric.ball (0 : E) (r i)) := by
          rw [Fintype.prod_eq_mul_prod_subtype_ne (fun i => volume (Metric.ball (0 : E) (r i))) a,
            mul_comm]

/-- **Tree sets of output variables**: along a forest (each variable has a parent, a variable or a
fixed anchor value `e c`, with `rk` decreasing towards the roots), the configurations with
`‖o i - o(parent i)‖ < r i` have `outPartMeasure` at most `∏ vol B(0, r i)` (Fubini from the
leaves to the roots). -/
theorem outPartMeasure_tree_le (hN : 0 < N) {α : Type} [Finite α] (V : Set α) (P : α → Prop)
    {ρ : Type} (e : ρ → EuclideanSpace ℝ (Fin N))
    (par : {y : α // y ∈ V ∧ P y} → {y : α // y ∈ V ∧ P y} ⊕ ρ) (rk : {y : α // y ∈ V ∧ P y} → ℕ)
    (hrk : ∀ i j, par i = Sum.inl j → rk j < rk i) (r : {y : α // y ∈ V ∧ P y} → ℝ) :
    haveI := Fintype.ofFinite {y : α // y ∈ V ∧ P y}
    outPartMeasure N V P {o | ∀ i, ‖o i - Sum.elim o e (par i)‖ < r i} ≤
      ∏ i, volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) (r i)) := by
  let _ : Fintype {y : α // y ∈ V ∧ P y} := Fintype.ofFinite _
  unfold outPartMeasure
  exact pi_treeSet_le hN _ rfl e par rk hrk r

end Tree

section ChiTildeTree

open Balaban Balaban.Multiscale RegionHistory

variable {N : ℕ} {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]

/-- **Spanning-tree balls of `χ̃_k`** (Lemma III.8.7 step (3), `ψ_k` on `Z^c_0 ∩ Z`): let the
output blocks `i` of `V` satisfying `P` lie in `Z^c_0 ∩ (Ω^c_k)^{∼3}` (`tildeRegion`), each with a
parent (a block of the same kind or an anchor block `cb c` of `tildeRegion` carrying the value
`e c`) adjacent to it in `T^{(k)}_1`, ranks decreasing towards the roots.  Then the
configurations that extend (by the anchor values) to a field with `χ̃_k = 1` have
`outPartMeasure` at most `vol B(0, 3δ_k)^{#blocks}`. -/
theorem outPartMeasure_chiTilde_le (hN : 0 < N) (a : LocalHistory S n M K) (k : ℕ)
    (Z0 : Set (Torus S.d (M * n K * S.L ^ K))) (δk : ℝ) (V : Set (BlockAt S n M K k))
    (P : BlockAt S n M K k → Prop) {ρ : Type} (e : ρ → EuclideanSpace ℝ (Fin N))
    (cb : ρ → BlockAt S n M K k)
    (par : {y : BlockAt S n M K k // y ∈ V ∧ P y} → {y : BlockAt S n M K k // y ∈ V ∧ P y} ⊕ ρ)
    (rk : {y : BlockAt S n M K k // y ∈ V ∧ P y} → ℕ)
    (hrk : ∀ i j, par i = Sum.inl j → rk j < rk i)
    (hreg : ∀ i : {y : BlockAt S n M K k // y ∈ V ∧ P y},
      BlockSub (S := S) (n := n) (M := M) (K := K) k i.1 (tildeRegion a k Z0))
    (hregc : ∀ c, BlockSub (S := S) (n := n) (M := M) (K := K) k (cb c) (tildeRegion a k Z0))
    (hadj : ∀ i j, par i = Sum.inl j → AdjT i.1 j.1)
    (hadjc : ∀ i c, par i = Sum.inr c → AdjT i.1 (cb c)) :
    outPartMeasure N V P {o | ∃ ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N),
        (∀ i, ψ i.1 = o i) ∧ (∀ c, ψ (cb c) = e c) ∧ ChiTildeProp a k Z0 δk ψ} ≤
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) (3 * δk)) ^
        Nat.card {y : BlockAt S n M K k // y ∈ V ∧ P y} := by
  classical
  let _ : Fintype {y : BlockAt S n M K k // y ∈ V ∧ P y} := Fintype.ofFinite _
  have hsub : {o : OutPart N V P | ∃ ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N),
        (∀ i, ψ i.1 = o i) ∧ (∀ c, ψ (cb c) = e c) ∧ ChiTildeProp a k Z0 δk ψ} ⊆
      {o | ∀ i, ‖o i - Sum.elim o e (par i)‖ < 3 * δk} := by
    rintro o ⟨ψ, hψo, hψe, hχ⟩ i
    have hval : Sum.elim o e (par i) = ψ (match par i with | Sum.inl j => j.1 | Sum.inr c => cb c) := by
      cases hc : par i with
      | inl j => simp [hψo j]
      | inr c => simp [hψe c]
    rw [hval, ← hψo i]
    have hadj' : AdjT i.1 (match par i with | Sum.inl j => j.1 | Sum.inr c => cb c) := by
      cases hc : par i with
      | inl j => simpa using hadj i j hc
      | inr c => simpa using hadjc i c hc
    have hreg' : BlockSub (S := S) (n := n) (M := M) (K := K) k
        (match par i with | Sum.inl j => j.1 | Sum.inr c => cb c) (tildeRegion a k Z0) := by
      cases hc : par i with
      | inl j => simpa using hreg j
      | inr c => simpa using hregc c
    exact hχ.1 i.1 (hreg i) _ hreg' hadj'
  refine (measure_mono hsub).trans ?_
  refine (outPartMeasure_tree_le hN V P e par rk hrk (fun _ => 3 * δk)).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]

end ChiTildeTree

end Balaban.LargeField
