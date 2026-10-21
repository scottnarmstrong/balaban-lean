/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalBoxLocal
public import Balaban.Spine.FinalBoxCells
public import Balaban.Spine.FinalBoxMeasure
public import Balaban.Polymer.LocalGas
public import Balaban.LargeField.Base.KF0AllGoodGas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The gas of the box integral on the macro cells

A6-3, gas layer, the box instance of `Polymer/LocalGas.lean` (P4 (6.6); P7 (4.9)–(4.14)), with
the dilation `t` of the Gaussian variable as a parameter. On one torus, with the local form
`BoxLocalForm C vc hv A p₁ G₀ R_t M_c a ε ε_U W U` of the fluctuation integrand at the whitening `A`:

* the sites of the gas are the macro cells `z` of side `M_c` of the `k`-block torus (`cellOf`, the
  cells `Green.macZ` of the cut family), with the graph `macCellGraph` (degree `≤ 16^d`);
* a cell configuration `Φ` carries the Gaussian variable on the blocks of the cell (`cellField`); the
  measure is the product over the blocks of the one-block Gaussian conditioned on the box
  (`boxSiteMeasure`), grouped by cells (`Polymer.qRef`);
* the terms of the gas at the parameter `q = (t, g)` (`BoxParam`) are the grouped terms
  `W_c(𝒳; t, g) = Σ_{cells(Y) = 𝒳} (W_Y(t w, g) + U_Y(w))` at the field `w` clamped onto the box
  (`boxCellTerm`, `dilField`; the part `U` is not dilated); the clamp `clampBox` is the identity on
  the box, which carries the measure, and makes the terms bounded and continuous for every
  configuration;
* `boxLocalForm_toLocalGasFormE`: the grouped terms have the local form of the generic core on the
  cells over the parameters `|t| < R_t`, `‖g‖₁ < G₀` (`boxParamSet`), with the bound
  `(2M_c)^d (ε + ε_U)` (a cell has at most `(2M_c)^d` blocks);
* `ctxFluctBoxIntegral_eq_boxGas`: the box average of the fluctuation integrand is
  `|det A| (2π)^{n/2} e^{E₀ + ℛ^{(k)}(T; h, h, g)} γ₁(box₁)^{|Λ|} exp(Σ_𝒳 P(𝒳; 1, g))` at the
  whitening `A` (`ctxFluctBoxIntegralL_eq_boxGas`), with the explicit local
  terms `boxCellP` (`boxCellAct` at `t = 1`); the local terms vanish off connected cell sets, depend
  on the source only at the fine sites of their cells, are analytic on `boxParamSet` and obey the
  Kotecký–Preiss bound (`boxCellP_kp_bound`, `boxCellP_eq_zero_of_not_isAnimal`, `boxCellP_congr_g`,
  `analyticOnNhd_boxCellP`);
* the parity: the box measure is symmetric under `w ↦ -w` and `U` is even, so
  `P(𝒳; -t, g) = P(𝒳; t, g)` (`boxCellP_neg`), and by the normalization (W0) `P(𝒳; 0, g)` is the
  local term of the gas of `U` alone, independent of the source (`boxCellP_zero_dil`).

The numerical conditions: `a ≥ κ' + 12d + 21/2` and `(2M_c)^d (ε + ε_U) ≤ 1/2` (`κ₀ = 4 + 6d`,
`κ₁ = κ' + κ₀ + 5/2` in `Polymer.integral_exp_eq_gasP`, with `Δ = 16^d`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Balaban Balaban.LargeField Balaban.LargeField.Def7
  Balaban.LargeField.Def7v2 Balaban.Green Balaban.Polymer Finset

namespace Balaban.RootFSpine

section Clamp

variable {ι : Type*}

/-- The clamp of a real field onto the box `|w_p| ≤ p₁`. -/
def clampBox (p1 : ℝ) (w : ι → ℝ) : ι → ℝ := fun p => max (-p1) (min p1 (w p))

theorem clampBox_mem {p1 : ℝ} (hp1 : 0 ≤ p1) (w : ι → ℝ) : clampBox p1 w ∈ gaussBox ι p1 := by
  intro p
  simp only [clampBox, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem clampBox_of_mem {p1 : ℝ} {w : ι → ℝ} (hw : w ∈ gaussBox ι p1) : clampBox p1 w = w := by
  funext p
  have h := abs_le.1 (hw p)
  simp only [clampBox]
  rw [min_eq_right h.2, max_eq_right h.1]

theorem continuous_clampBox (p1 : ℝ) : Continuous (clampBox (ι := ι) p1) :=
  continuous_pi fun p => continuous_const.max (continuous_const.min (continuous_apply p))

end Clamp

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ}

/-- The cell of a `k`-block. -/
def cellOf (k Mc : ℕ) (x : BlockAt S n M K k) : MacIdx S.d (M * n K * S.L ^ (K - k)) Mc :=
  macZ Mc (x : L1Torus S.d (M * n K * S.L ^ (K - k)))

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
theorem cellCount_eq (k Mc : ℕ) (Y : Finset (BlockAt S n M K k)) :
    cellCount k Mc Y = (Y.image (cellOf k Mc)).card := rfl

/-- The cell of an index of the source (the cell of the `k`-block of its fine site). -/
def cellOfSrc (k Mc : ℕ) (i : GIdx S n M K N) : MacIdx S.d (M * n K * S.L ^ (K - k)) Mc :=
  cellOf k Mc (fineBlock k i.1)

/-- The configurations of a cell: the Gaussian variables of the blocks of the cell. -/
abbrev CellSpace (k Mc N : ℕ) (z : MacIdx S.d (M * n K * S.L ^ (K - k)) Mc) : Type :=
  QSpace (cellOf (S := S) (n := n) (M := M) (K := K) k Mc) (Fin N → ℝ) z

/-- The Gaussian variable of a cell configuration. -/
def cellField {k Mc : ℕ} (Φ : ∀ z, CellSpace (S := S) (n := n) (M := M) (K := K) k Mc N z) :
    BlockAt S n M K k × Fin N → ℝ :=
  fieldCurry (BlockAt S n M K k) N (qSites (cellOf k Mc) Φ)

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
theorem cellField_apply {k Mc : ℕ} (Φ : ∀ z, CellSpace (S := S) (n := n) (M := M) (K := K) k Mc N z)
    (x : BlockAt S n M K k) (i : Fin N) : cellField Φ (x, i) = Φ (cellOf k Mc x) ⟨x, rfl⟩ i := rfl

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
theorem continuous_cellField (k Mc : ℕ) :
    Continuous (cellField (S := S) (n := n) (M := M) (K := K) (N := N) (k := k) (Mc := Mc)) :=
  continuous_pi fun p => (continuous_apply p.2).comp
    ((continuous_apply (⟨p.1, rfl⟩ : QFibre (cellOf k Mc) (cellOf k Mc p.1))).comp
      (continuous_apply (cellOf k Mc p.1)))

/-- **The one-block measure of the box**: the standard Gaussian of `Fin N → ℝ` conditioned on the
box `|v_i| ≤ p₁`. -/
noncomputable def boxSiteMeasure (N : ℕ) (p1 : ℝ) : Measure (Fin N → ℝ) :=
  cond (pdGaussian (Fin N) ℝ) (gaussBox (Fin N) p1)

/-- The dilated complex field `t · w` of a real field `w`. -/
abbrev dilField {ι : Type*} (t : ℂ) (w : ι → ℝ) : ι → ℂ := fun p => t * (w p : ℂ)

/-- The parameters of the box gas: a dilation `t` and a source `g`. -/
abbrev BoxParam (S : Setting) (n : ℕ → ℕ) (M K N : ℕ) : Type := ℂ × (GIdx S n M K N → ℂ)

/-- **The terms of the gas of the cells**: the grouped terms
`W_c(𝒳)(t, g) = Σ_{cells(Y) = 𝒳} (W_Y(t w, g) + U_Y(w))` at the field `w` of the cell configuration
clamped onto the box, the part `W` dilated and the part `U` not. -/
def boxCellTerm (W : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℂ) →
      (GIdx S n M K N → ℂ) → ℂ)
    (U : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℝ) → ℂ) (Mc : ℕ) (p1 : ℝ)
    (𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc))
    (Φ : ∀ z, CellSpace (S := S) (n := n) (M := M) (K := K) k Mc N z)
    (q : BoxParam S n M K N) : ℂ :=
  ∑ Y ∈ (Finset.univ : Finset (Finset (BlockAt S n M K k))).filter
    (fun Y => Y.image (cellOf k Mc) = 𝒳),
      (W Y (dilField q.1 (clampBox p1 (cellField Φ))) q.2 + U Y (clampBox p1 (cellField Φ)))

/-- **The local terms of the box gas** on the sets of cells, at the parameter `(t, g)`: the local
terms `localGasP` of the generic core for the grouped terms `boxCellTerm` and the product of the box
measures. -/
noncomputable def boxCellP (W : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℂ) →
      (GIdx S n M K N → ℂ) → ℂ)
    (U : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℝ) → ℂ) (Mc : ℕ) (p1 : ℝ) (q : BoxParam S n M K N)
    (𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc)) : ℂ :=
  localGasP (qRef (cellOf k Mc) (boxSiteMeasure N p1)) (boxCellTerm W U Mc p1) q 𝒳

/-- **The activity of a set of cells** at the source `g`: the local term of the box gas at the
dilation `t = 1`. -/
noncomputable def boxCellAct (W : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℂ) →
      (GIdx S n M K N → ℂ) → ℂ)
    (U : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℝ) → ℂ) (Mc : ℕ) (p1 : ℝ) (g : GIdx S n M K N → ℂ)
    (𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc)) : ℂ :=
  boxCellP W U Mc p1 (1, g) 𝒳

section Form

variable {C : SFCtx S n R M K N k m₁ ϱ} {vc : CorrCoef S.d} {hv : EuclideanSpace ℝ (Fin N)}
  {A : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ}
  {p1 G₀ Rt : ℝ} {Mc : ℕ} {a ε εU : ℝ}
  {W : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℂ) → (GIdx S n M K N → ℂ) → ℂ}
  {U : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℝ) → ℂ}

/-- The sum over the cell sets containing a cell of the grouped weights is at most the sum over the
blocks of the cell of the weights of the block sets containing the block. -/
theorem sum_cellSets_le (f : Finset (BlockAt S n M K k) → ℝ) (hf : ∀ Y, 0 ≤ f Y)
    (z : MacIdx S.d (M * n K * S.L ^ (K - k)) Mc) :
    ∑ 𝒳 ∈ (Finset.univ : Finset (Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc))).filter
        (fun 𝒳 => z ∈ 𝒳),
      ∑ Y ∈ (Finset.univ : Finset (Finset (BlockAt S n M K k))).filter
        (fun Y => Y.image (cellOf k Mc) = 𝒳), f Y ≤
      ∑ x ∈ (Finset.univ : Finset (BlockAt S n M K k)).filter (fun x => cellOf k Mc x = z),
        ∑ Y ∈ (Finset.univ : Finset (Finset (BlockAt S n M K k))).filter (fun Y => x ∈ Y), f Y := by
  classical
  set s := (Finset.univ : Finset (Finset (BlockAt S n M K k))).filter
    (fun Y => z ∈ Y.image (cellOf k Mc)) with hs
  have h1 : ∑ 𝒳 ∈ (Finset.univ : Finset (Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc))).filter
        (fun 𝒳 => z ∈ 𝒳),
      ∑ Y ∈ (Finset.univ : Finset (Finset (BlockAt S n M K k))).filter
        (fun Y => Y.image (cellOf k Mc) = 𝒳), f Y = ∑ Y ∈ s, f Y := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun Y : Finset (BlockAt S n M K k) =>
      Y.image (cellOf k Mc)) (t := (Finset.univ : Finset (Finset (MacIdx S.d
        (M * n K * S.L ^ (K - k)) Mc))).filter (fun 𝒳 => z ∈ 𝒳)) (s := s)
      (fun Y hY => by simpa [hs] using hY)]
    refine Finset.sum_congr rfl fun 𝒳 h𝒳 => Finset.sum_congr ?_ fun _ _ => rfl
    ext Y
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hY; exact ⟨by rw [hY]; exact (Finset.mem_filter.1 h𝒳).2, hY⟩
    · exact fun h => h.2
  rw [h1, Finset.sum_filter]
  have h2 : ∑ x ∈ (Finset.univ : Finset (BlockAt S n M K k)).filter (fun x => cellOf k Mc x = z),
      ∑ Y ∈ (Finset.univ : Finset (Finset (BlockAt S n M K k))).filter (fun Y => x ∈ Y), f Y =
      ∑ Y : Finset (BlockAt S n M K k), ∑ x ∈ (Finset.univ : Finset (BlockAt S n M K k)).filter
        (fun x => cellOf k Mc x = z), (if x ∈ Y then f Y else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_filter]
  rw [h2]
  refine Finset.sum_le_sum fun Y _ => ?_
  split_ifs with hz
  · obtain ⟨x, hx, hxz⟩ := Finset.mem_image.1 hz
    have hmem : x ∈ (Finset.univ : Finset (BlockAt S n M K k)).filter
        (fun x => cellOf k Mc x = z) := Finset.mem_filter.2 ⟨Finset.mem_univ _, hxz⟩
    calc f Y = (if x ∈ Y then f Y else 0) := by simp [hx]
      _ ≤ _ := Finset.single_le_sum (f := fun x => if x ∈ Y then f Y else 0)
          (fun x _ => by split_ifs <;> simp [hf Y]) hmem
  · exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp [hf Y]

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
theorem clampBox_cellField_apply {p1 : ℝ}
    (Φ : ∀ z, CellSpace (S := S) (n := n) (M := M) (K := K) k Mc N z) (x : BlockAt S n M K k)
    (i : Fin N) : clampBox p1 (cellField Φ) (x, i) =
      max (-p1) (min p1 (Φ (cellOf k Mc x) ⟨x, rfl⟩ i)) := rfl

/-- The open set of parameters of the box gas: `|t| < R_t`, `‖g‖₁ < G₀`. -/
abbrev boxParamSet (Rt G₀ : ℝ) : Set (BoxParam S n M K N) :=
  Metric.ball (0 : ℂ) Rt ×ˢ l1BallR (GIdx S n M K N) G₀

theorem isOpen_boxParamSet (Rt G₀ : ℝ) :
    IsOpen (boxParamSet (S := S) (n := n) (M := M) (K := K) (N := N) Rt G₀) :=
  Metric.isOpen_ball.prod (isOpen_l1BallR _ _)

/-- The map `(t, g) ↦ (0, g)` of the parameters. -/
theorem zero_param_mem {Rt G₀ : ℝ} (hRt : 0 < Rt) {q : BoxParam S n M K N}
    (hq : q ∈ boxParamSet (S := S) (n := n) (M := M) (K := K) (N := N) Rt G₀) : ((0 : ℂ), q.2) ∈ boxParamSet (S := S) (n := n) (M := M) (K := K) (N := N) Rt G₀ :=
  ⟨by simpa using hRt, hq.2⟩

theorem dilField_zero {ι : Type*} (w : ι → ℝ) : dilField (0 : ℂ) w = 0 := by
  funext p; simp [dilField]

/-- **The grouped fluctuation parts have the local form of the generic core on the cells**, with
the parameters `(t, g)` on the polydisc `|t| < R_t`, `‖g‖₁ < G₀` and the bound `(2M_c)^d (ε + ε_U)`. -/
theorem boxLocalForm_toLocalGasFormE (hW : BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU W U)
    (hMc : 0 < Mc) (hp1 : 0 ≤ p1) :
    LocalGasFormE (Ω := CellSpace (S := S) (n := n) (M := M) (K := K) k Mc N) (macCellGraph Mc)
      (boxParamSet (S := S) (n := n) (M := M) (K := K) (N := N) Rt G₀) a
      (((2 * Mc : ℕ) : ℝ) ^ S.d * (ε + εU)) (boxCellTerm W U Mc p1) where
  local_w 𝒳 q Φ Φ' hΦ := by
    unfold boxCellTerm
    refine Finset.sum_congr rfl fun Y hY => ?_
    have hc : ∀ x ∈ Y, cellOf k Mc x ∈ 𝒳 := fun x hx => by
      rw [← (Finset.mem_filter.1 hY).2]; exact Finset.mem_image_of_mem _ hx
    congr 1
    · refine hW.local_w Y _ _ q.2 fun x hx i => ?_
      simp only [dilField]
      rw [clampBox_cellField_apply, clampBox_cellField_apply, hΦ _ (hc x hx)]
    · refine hW.local_u Y _ _ fun x hx i => ?_
      rw [clampBox_cellField_apply, clampBox_cellField_apply, hΦ _ (hc x hx)]
  support 𝒳 h𝒳 Φ q := by
    unfold boxCellTerm
    refine Finset.sum_eq_zero fun Y hY => ?_
    have hY' : ¬ Polymer.IsAnimal (Polymer.blockGraph S.d (M * n K * S.L ^ (K - k))) Y :=
      fun hYa => h𝒳 (by rw [← (Finset.mem_filter.1 hY).2]; exact isAnimal_image_macZ hYa)
    rw [hW.support Y hY', hW.support_u Y hY', add_zero]
  analytic 𝒳 Φ := by
    unfold boxCellTerm
    refine Finset.analyticOnNhd_fun_sum _ fun Y _ => ?_
    exact (hW.analytic Y _ (clampBox_mem hp1 (cellField Φ))).add analyticOnNhd_const
  cont 𝒳 := by
    unfold boxCellTerm
    refine continuousOn_finsetSum _ fun Y _ => ?_
    have hmap : Continuous fun q : BoxParam S n M K N ×
        (∀ z, CellSpace (S := S) (n := n) (M := M) (K := K) k Mc N z) =>
        (q.1, clampBox p1 (cellField q.2)) :=
      continuous_fst.prodMk ((continuous_clampBox p1).comp ((continuous_cellField k Mc).comp
        continuous_snd))
    have hmap2 : Continuous fun q : BoxParam S n M K N ×
        (∀ z, CellSpace (S := S) (n := n) (M := M) (K := K) k Mc N z) =>
        clampBox p1 (cellField q.2) :=
      (continuous_clampBox p1).comp ((continuous_cellField k Mc).comp continuous_snd)
    exact ((hW.cont Y).comp hmap.continuousOn
      fun q (hq : q ∈ boxParamSet (S := S) (n := n) (M := M) (K := K) (N := N) Rt G₀ ×ˢ
        Set.univ) => ⟨hq.1, clampBox_mem hp1 _⟩).add ((hW.cont_u Y).comp hmap2.continuousOn
      fun q _ => clampBox_mem hp1 _)
  bound Φ q hq z := by
    set w := clampBox p1 (cellField Φ) with hw
    have hwb : w ∈ gaussBox (BlockAt S n M K k × Fin N) p1 := clampBox_mem hp1 _
    have hq1 : ‖q.1‖ < Rt := by simpa using hq.1
    have hε : 0 ≤ ε + εU := add_nonneg
      (le_trans (Finset.sum_nonneg fun Y _ => by positivity) (hW.bound w hwb q.1 hq1 q.2 hq.2 0))
      (le_trans (Finset.sum_nonneg fun Y _ => by positivity) (hW.bound_u w hwb 0))
    have h1 : ∀ 𝒳 ∈ (Finset.univ : Finset (Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc))).filter
        (fun 𝒳 => z ∈ 𝒳), ‖boxCellTerm W U Mc p1 𝒳 Φ q‖ * Real.exp (a * (𝒳.card : ℝ)) ≤
        ∑ Y ∈ (Finset.univ : Finset (Finset (BlockAt S n M K k))).filter
          (fun Y => Y.image (cellOf k Mc) = 𝒳),
          (‖W Y (fun p => q.1 * (w p : ℂ)) q.2‖ + ‖U Y w‖) *
            Real.exp (a * (cellCount k Mc Y : ℝ)) := by
      intro 𝒳 _
      unfold boxCellTerm
      calc _ ≤ (∑ Y ∈ (Finset.univ : Finset (Finset (BlockAt S n M K k))).filter
              (fun Y => Y.image (cellOf k Mc) = 𝒳),
                (‖W Y (dilField q.1 w) q.2‖ + ‖U Y w‖)) * Real.exp (a * (𝒳.card : ℝ)) :=
            mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans
              (Finset.sum_le_sum fun Y _ => norm_add_le _ _)) (Real.exp_pos _).le
        _ = _ := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun Y hY => ?_
            rw [cellCount_eq, (Finset.mem_filter.1 hY).2]
    refine (Finset.sum_le_sum h1).trans ((sum_cellSets_le (fun Y =>
      (‖W Y (fun p => q.1 * (w p : ℂ)) q.2‖ + ‖U Y w‖) * Real.exp (a * (cellCount k Mc Y : ℝ)))
      (fun Y => by positivity) z).trans ?_)
    have hx : ∀ x : BlockAt S n M K k,
        ∑ Y ∈ (Finset.univ : Finset (Finset (BlockAt S n M K k))).filter (fun Y => x ∈ Y),
          (‖W Y (fun p => q.1 * (w p : ℂ)) q.2‖ + ‖U Y w‖) *
            Real.exp (a * (cellCount k Mc Y : ℝ)) ≤ ε + εU := fun x => by
      simp only [add_mul, Finset.sum_add_distrib]
      exact add_le_add (hW.bound w hwb q.1 hq1 q.2 hq.2 x) (hW.bound_u w hwb x)
    calc _ ≤ ∑ x ∈ (Finset.univ : Finset (BlockAt S n M K k)).filter (fun x => cellOf k Mc x = z),
            (ε + εU) := Finset.sum_le_sum fun x _ => hx x
      _ = (((Finset.univ : Finset (BlockAt S n M K k)).filter
            (fun x => cellOf k Mc x = z)).card : ℝ) * (ε + εU) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (((2 * Mc : ℕ) : ℝ) ^ S.d) * (ε + εU) := by
          refine mul_le_mul_of_nonneg_right ?_ hε
          have := card_macZ_fibre_le (d := S.d) (m := M * n K * S.L ^ (K - k)) hMc z
          have h2 : ((Finset.univ : Finset (BlockAt S n M K k)).filter
              (fun x => cellOf k Mc x = z)).card ≤ (2 * Mc) ^ S.d := by
            refine le_trans (Finset.card_le_card fun x hx => ?_) this
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
            exact hx
          exact_mod_cast h2

end Form

/-! ### Numerics -/

/-- The entropy rate of the cell gas: `κ₀ = 4 + 6d`. -/
noncomputable def cellKappa0 (d : ℕ) : ℝ := 4 + 6 * d

/-- **The numerical conditions of the cell gas** (`Δ = 16^d`, `κ₀ = 4 + 6d`,
`κ₁ = κ' + κ₀ + 5/2`): from `a ≥ κ' + 12d + 21/2` and `ε_c ≤ 1/2`. -/
theorem cellGas_numerics (d : ℕ) {κ' a εc : ℝ} (ha : κ' + 12 * d + 21 / 2 ≤ a) (hεc : εc ≤ 1 / 2) :
    (((16 ^ d : ℕ) : ℝ)) ^ 2 * 2 * Real.exp (-cellKappa0 d) ≤ 1 / 2 ∧
      Real.log 4 + 1 ≤ cellKappa0 d ∧
      κ' + cellKappa0 d + 1 ≤ (κ' + cellKappa0 d + 5 / 2) - 3 / 2 ∧
      cellKappa0 d + (κ' + cellKappa0 d + 5 / 2) ≤ a ∧ εc ≤ Real.log 2 ∧
      εc * (4 * Real.exp (-cellKappa0 d)) ≤ 1 / 4 := by
  have he1 : (2.7 : ℝ) < Real.exp 1 := lt_of_lt_of_le (by norm_num) Real.exp_one_gt_d9.le
  have h4 : 4 * Real.exp (-4) ≤ 1 / 2 := by
    have : (8 : ℝ) ≤ Real.exp 4 := by
      have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]; nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7) he1.le 4]
    rw [Real.exp_neg]
    rw [mul_inv_le_iff₀ (Real.exp_pos 4)]; linarith
  have hκ0 : 4 ≤ cellKappa0 d := by unfold cellKappa0; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have h4' : 4 * Real.exp (-cellKappa0 d) ≤ 1 / 2 :=
    le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by norm_num)) h4
  refine ⟨?_, ?_, by linarith, ?_, ?_, ?_⟩
  · have h256 : (256 : ℝ) ≤ Real.exp 6 := by
      have : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]; nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7) he1.le 6]
    have e1 : (((16 ^ d : ℕ) : ℝ)) ^ 2 * 2 * Real.exp (-cellKappa0 d) =
        2 * Real.exp (-4) * ((256 : ℝ) * Real.exp (-6)) ^ d := by
      unfold cellKappa0
      rw [mul_pow, ← Real.exp_nat_mul, show -(4 + 6 * (d : ℝ)) = -4 + (d : ℝ) * (-6) by ring,
        Real.exp_add]
      push_cast
      rw [← pow_mul, show (16 : ℝ) ^ (d * 2) = 256 ^ d by rw [pow_mul']; norm_num]
      ring
    rw [e1]
    have h1 : (256 : ℝ) * Real.exp (-6) ≤ 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos 6)]; exact h256
    have h2 : ((256 : ℝ) * Real.exp (-6)) ^ d ≤ 1 := pow_le_one₀ (by positivity) h1
    nlinarith [Real.exp_pos (-4), pow_nonneg (by positivity : (0:ℝ) ≤ 256 * Real.exp (-6)) d]
  · have := Balaban.LargeField.log_four_bounds; linarith
  · unfold cellKappa0; linarith
  · have := Real.log_two_gt_d9; linarith
  · by_cases h0 : εc ≤ 0
    · nlinarith [Real.exp_pos (-cellKappa0 d)]
    · push Not at h0
      nlinarith [Real.exp_pos (-cellKappa0 d)]

/-! ### The gas of the box -/

section Gas

variable {C : SFCtx S n R M K N k m₁ ϱ} {vc : CorrCoef S.d} {hv : EuclideanSpace ℝ (Fin N)}
  {A : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ}
  {p1 G₀ Rt : ℝ} {Mc : ℕ} {a ε εU : ℝ}
  {W : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℂ) → (GIdx S n M K N → ℂ) → ℂ}
  {U : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℝ) → ℂ}

theorem isProbabilityMeasure_boxSiteMeasure {p1 : ℝ} (hp1 : 0 < p1) :
    IsProbabilityMeasure (boxSiteMeasure N p1) := by
  have : IsProbabilityMeasure (pdGaussian (Fin N) ℝ) := ⟨pdGaussian_univ⟩
  exact cond_isProbabilityMeasure (pdGaussian_gaussBox_pos hp1).ne'

/-- The compact carrier of the cell measure: every block value in the box. -/
def cellBoxSet (k Mc N : ℕ) (p1 : ℝ) :
    Set (∀ z, CellSpace (S := S) (n := n) (M := M) (K := K) k Mc N z) :=
  Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => gaussBox (Fin N) p1

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
theorem isCompact_cellBoxSet (k Mc N : ℕ) (p1 : ℝ) :
    IsCompact (cellBoxSet (S := S) (n := n) (M := M) (K := K) k Mc N p1) := by
  have hb : IsCompact (gaussBox (Fin N) p1) := by
    have : gaussBox (Fin N) p1 = Set.pi Set.univ fun _ : Fin N => Set.Icc (-p1) p1 := by
      ext v
      simp only [gaussBox, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
        abs_le]
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hb

theorem measurableSet_cellBoxSet (k Mc N : ℕ) (p1 : ℝ) :
    MeasurableSet (cellBoxSet (S := S) (n := n) (M := M) (K := K) k Mc N p1) :=
  MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_gaussBox _ p1

theorem ae_cellBoxSet {p1 : ℝ} (hp1 : 0 < p1) :
    ∀ᵐ Φ ∂(Measure.pi (qRef (cellOf (S := S) (n := n) (M := M) (K := K) k Mc)
      (boxSiteMeasure N p1))), Φ ∈ cellBoxSet (S := S) (n := n) (M := M) (K := K) k Mc N p1 := by
  have : IsProbabilityMeasure (boxSiteMeasure N p1) := isProbabilityMeasure_boxSiteMeasure hp1
  have hone : boxSiteMeasure N p1 (gaussBox (Fin N) p1) = 1 := by
    have : IsProbabilityMeasure (pdGaussian (Fin N) ℝ) := ⟨pdGaussian_univ⟩
    exact cond_apply_self (pdGaussian_gaussBox_pos hp1).ne' (measure_ne_top _ _)
  have h1 : Measure.pi (qRef (cellOf (S := S) (n := n) (M := M) (K := K) k Mc)
      (boxSiteMeasure N p1)) (cellBoxSet (S := S) (n := n) (M := M) (K := K) k Mc N p1) = 1 := by
    rw [cellBoxSet, Measure.pi_pi]
    refine Finset.prod_eq_one fun z _ => ?_
    simp only [qRef, Measure.pi_pi, hone, Finset.prod_const_one]
  have hc : Measure.pi (qRef (cellOf (S := S) (n := n) (M := M) (K := K) k Mc)
      (boxSiteMeasure N p1)) (cellBoxSet (S := S) (n := n) (M := M) (K := K) k Mc N p1)ᶜ = 0 := by
    rw [measure_compl (measurableSet_cellBoxSet _ _ _ _) (measure_ne_top _ _), h1, measure_univ,
      tsub_self]
  filter_upwards [mem_ae_iff.2 hc] with Φ hΦ using hΦ

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
theorem cellField_mem_of_mem_cellBoxSet {p1 : ℝ}
    {Φ : ∀ z, CellSpace (S := S) (n := n) (M := M) (K := K) k Mc N z}
    (hΦ : Φ ∈ cellBoxSet (S := S) (n := n) (M := M) (K := K) k Mc N p1) :
    cellField Φ ∈ gaussBox (BlockAt S n M K k × Fin N) p1 := fun p =>
  hΦ (cellOf k Mc p.1) (Set.mem_univ _) ⟨p.1, rfl⟩ (Set.mem_univ _) p.2

/-- The sum of the terms over the block sets at the clamped field is the sum over the cell sets of
the grouped terms at `t = 1`. -/
theorem sum_W_eq_sum_boxCellTerm (Φ : ∀ z, CellSpace (S := S) (n := n) (M := M) (K := K) k Mc N z)
    (g : GIdx S n M K N → ℂ) :
    ∑ Y : Finset (BlockAt S n M K k), W Y (fun p => ((clampBox p1 (cellField Φ) p : ℝ) : ℂ)) g +
        ∑ Y : Finset (BlockAt S n M K k), U Y (clampBox p1 (cellField Φ)) =
      ∑ 𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc), boxCellTerm W U Mc p1 𝒳 Φ (1, g) := by
  unfold boxCellTerm
  have h1 : dilField (1 : ℂ) (clampBox p1 (cellField Φ)) =
      fun p => ((clampBox p1 (cellField Φ) p : ℝ) : ℂ) := by
    funext p; simp [dilField]
  simp only [h1]
  rw [← Finset.sum_add_distrib]
  exact (Finset.sum_fiberwise _ _ _).symm

/-- **The box average of the fluctuation integrand is a cell gas** (A6-3, gas layer): under the local
form at the whitening `A`, for every source of the unit ball,
`ctxFluctBoxIntegralL = |det A| (2π)^{n/2} e^{E₀ + ℛ^{(k)}} γ₁(box₁)^{|Λ|} exp(Σ_𝒳 A(𝒳))` with the
activities `boxCellAct` (the parts at the constant configuration and the local terms of the gas at
`t = 1`). -/
theorem ctxFluctBoxIntegralL_eq_boxGas (hW : BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU W U)
    (hMc : 0 < Mc) (hp1 : 0 < p1) {κ' : ℝ} (hκ' : 0 ≤ κ') (ha : κ' + 12 * S.d + 21 / 2 ≤ a)
    (hε : ((2 * Mc : ℕ) : ℝ) ^ S.d * (ε + εU) ≤ 1 / 2) :
    ∃ E₀ : ℂ, ∀ g ∈ l1Ball (GIdx S n M K N),
      ctxFluctBoxIntegralL C vc hv A p1 g =
        (whitenNorm A : ℂ) *
          Complex.exp (E₀ + C.Rres Set.univ (fun _ => hv) hv g) *
          (((pdGaussian (Fin N) ℝ (gaussBox (Fin N) p1)).toReal ^
            Fintype.card (BlockAt S n M K k) : ℝ) : ℂ) *
          Complex.exp (∑ 𝒳, boxCellAct W U Mc p1 g 𝒳) := by
  have : IsProbabilityMeasure (boxSiteMeasure N p1) := isProbabilityMeasure_boxSiteMeasure hp1
  obtain ⟨E₀, hE⟩ := ctxFluctBoxIntegralL_eq_of_boxLocalForm hW
  refine ⟨E₀, fun g hg => ?_⟩
  have hgU : ((1 : ℂ), g) ∈ boxParamSet (S := S) (n := n) (M := M) (K := K) (N := N) Rt G₀ :=
    ⟨by simp; linarith [hW.two_le_Rt], l1Ball_subset_l1BallR _ hW.one_le_G₀ hg⟩
  have hF := boxLocalForm_toLocalGasFormE hW hMc hp1.le
  obtain ⟨hq, hκ0, hκ, ha', hεlog, hεK⟩ := cellGas_numerics S.d (κ' := κ') ha hε
  have hgas := integral_exp_eq_gasP (μ := qRef (cellOf (S := S) (n := n) (M := M) (K := K) k Mc)
      (boxSiteMeasure N p1)) (macCellGraph_connected (KF0Gas.blockGraph_connected S.d _))
    (macCellGraph_degree_le hMc) hq hκ0 hκ' hκ ha' hεlog hεK hF hgU
  rw [hE g hg, setIntegral_gaussBox_eq hp1,
    integral_pi_eq_qRef (cellOf (S := S) (n := n) (M := M) (K := K) k Mc)]
  have hint : ∫ Φ, Complex.exp (∑ Y, W Y (fun p => ((fieldCurry (BlockAt S n M K k) N
        (qSites (cellOf k Mc) Φ) p : ℝ) : ℂ)) g +
          ∑ Y, U Y (fieldCurry (BlockAt S n M K k) N (qSites (cellOf k Mc) Φ)))
        ∂(Measure.pi (qRef (cellOf (S := S) (n := n) (M := M) (K := K) k Mc)
          (boxSiteMeasure N p1))) =
      ∫ Φ, Complex.exp (∑ 𝒳, boxCellTerm W U Mc p1 𝒳 Φ ((1 : ℂ), g))
          ∂(Measure.pi (qRef (cellOf (S := S) (n := n) (M := M) (K := K) k Mc)
            (boxSiteMeasure N p1))) := by
    refine integral_congr_ae ((ae_cellBoxSet hp1).mono fun Φ hΦ => ?_)
    beta_reduce
    have h1 := sum_W_eq_sum_boxCellTerm (W := W) (U := U) (p1 := p1) Φ g
    rw [clampBox_of_mem (cellField_mem_of_mem_cellBoxSet hΦ)] at h1
    rw [← h1]
    rfl
  rw [show cond (pdGaussian (Fin N) ℝ) (gaussBox (Fin N) p1) = boxSiteMeasure N p1 from rfl,
    hint, hgas.1]
  unfold boxCellAct boxCellP
  ring

/-- **The Kotecký–Preiss bound of the box gas**: for parameters of the polydisc,
`Σ_{𝒳 ∋ z} ‖P_{(t,g)}(𝒳)‖ e^{κ' |𝒳|_St} ≤ 64 e (2M_c)^d (ε + ε_U) e^{-2κ₀}`. -/
theorem boxCellP_kp_bound (hW : BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU W U) (hMc : 0 < Mc)
    (hp1 : 0 < p1) {κ' : ℝ} (hκ' : 0 ≤ κ') (ha : κ' + 12 * S.d + 21 / 2 ≤ a)
    (hε : ((2 * Mc : ℕ) : ℝ) ^ S.d * (ε + εU) ≤ 1 / 2) {q : BoxParam S n M K N}
    (hq : q ∈ boxParamSet (S := S) (n := n) (M := M) (K := K) (N := N) Rt G₀) (z : MacIdx S.d (M * n K * S.L ^ (K - k)) Mc) :
    ∑ 𝒳 ∈ (Finset.univ : Finset (Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc))).filter
        (fun 𝒳 => z ∈ 𝒳), ‖boxCellP W U Mc p1 q 𝒳‖ * Real.exp (κ' * stSizeG (macCellGraph Mc) 𝒳) ≤
      64 * Real.exp 1 * (((2 * Mc : ℕ) : ℝ) ^ S.d * (ε + εU)) * Real.exp (-(2 * cellKappa0 S.d)) := by
  have : IsProbabilityMeasure (boxSiteMeasure N p1) := isProbabilityMeasure_boxSiteMeasure hp1
  obtain ⟨hq', hκ0, hκ, ha', hεlog, hεK⟩ := cellGas_numerics S.d (κ' := κ') ha hε
  exact (integral_exp_eq_gasP (μ := qRef (cellOf (S := S) (n := n) (M := M) (K := K) k Mc)
      (boxSiteMeasure N p1)) (macCellGraph_connected (KF0Gas.blockGraph_connected S.d _))
    (macCellGraph_degree_le hMc) hq' hκ0 hκ' hκ ha' hεlog hεK
    (boxLocalForm_toLocalGasFormE hW hMc hp1.le) hq).2 z

/-- **The local terms of the box gas vanish off connected cell sets.** -/
theorem boxCellP_eq_zero_of_not_isAnimal (hW : BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU W U)
    (hMc : 0 < Mc) (hp1 : 0 ≤ p1) (q : BoxParam S n M K N)
    (𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc))
    (h𝒳 : ¬ IsAnimal (macCellGraph Mc) 𝒳) : boxCellP W U Mc p1 q 𝒳 = 0 :=
  gasP_eq_zero_of_not_isAnimal (boxLocalForm_toLocalGasFormE hW hMc hp1) q 𝒳 h𝒳

/-- **The local terms of the box gas depend on the source only at the fine sites of their
cells.** -/
theorem boxCellP_congr_g (hW : BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU W U) (t : ℂ)
    (𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc))
    {g g' : GIdx S n M K N → ℂ} (hgg : ∀ i, cellOfSrc k Mc i ∈ 𝒳 → g i = g' i) :
    boxCellP W U Mc p1 (t, g) 𝒳 = boxCellP W U Mc p1 (t, g') 𝒳 := by
  refine gasP_congr_param 𝒳 fun 𝒴 h𝒴 Φ => ?_
  unfold boxCellTerm
  refine Finset.sum_congr rfl fun Y hY => ?_
  have hloc : ∀ ζ, W Y ζ g = W Y ζ g' := fun ζ => hW.local_g Y ζ g g' fun x hx i => hgg (x, i) (by
    show cellOf k Mc (fineBlock k x) ∈ 𝒳
    refine h𝒴 ?_
    rw [← (Finset.mem_filter.1 hY).2]; exact Finset.mem_image_of_mem _ hx)
  rw [hloc]

/-- **The local terms of the box gas are analytic in the parameters** on the polydisc. -/
theorem analyticOnNhd_boxCellP (hW : BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU W U) (hMc : 0 < Mc)
    (hp1 : 0 < p1) {κ' : ℝ} (hκ' : 0 ≤ κ') (ha : κ' + 12 * S.d + 21 / 2 ≤ a)
    (hε : ((2 * Mc : ℕ) : ℝ) ^ S.d * (ε + εU) ≤ 1 / 2)
    (𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc)) :
    AnalyticOnNhd ℂ (fun q => boxCellP W U Mc p1 q 𝒳) (boxParamSet (S := S) (n := n) (M := M) (K := K) (N := N) Rt G₀) := by
  have : IsProbabilityMeasure (boxSiteMeasure N p1) := isProbabilityMeasure_boxSiteMeasure hp1
  obtain ⟨hq, hκ0, hκ, ha', hεlog, hεK⟩ := cellGas_numerics S.d (κ' := κ') ha hε
  exact analyticOnNhd_gasP (μ := qRef (cellOf (S := S) (n := n) (M := M) (K := K) k Mc)
      (boxSiteMeasure N p1)) (macCellGraph_connected (KF0Gas.blockGraph_connected S.d _))
    (macCellGraph_degree_le hMc) hq hκ0 hκ' hκ ha' hεlog hεK (isOpen_boxParamSet Rt G₀)
    (isCompact_cellBoxSet k Mc N p1) (measurableSet_cellBoxSet k Mc N p1) (ae_cellBoxSet hp1)
    (boxLocalForm_toLocalGasFormE hW hMc hp1.le) 𝒳

/-! ### Symmetry under `w ↦ -w` and the dilation `t = 0` -/

theorem clampBox_neg {ι : Type*} {p1 : ℝ} (hp1 : 0 ≤ p1) (w : ι → ℝ) :
    clampBox p1 (-w) = -clampBox p1 w := by
  funext p
  simp only [clampBox, Pi.neg_apply]
  rcases le_total (w p) (-p1) with h1 | h1
  · rw [min_eq_left (by linarith : p1 ≤ -w p), max_eq_right (by linarith : -p1 ≤ p1),
      min_eq_right (by linarith : w p ≤ p1), max_eq_left h1, neg_neg]
  · rcases le_total (w p) p1 with h2 | h2
    · rw [min_eq_right (by linarith : -w p ≤ p1), max_eq_right (by linarith : -p1 ≤ -w p),
        min_eq_right h2, max_eq_right h1]
    · rw [min_eq_right (by linarith : -w p ≤ p1), max_eq_left (by linarith : -w p ≤ -p1),
        min_eq_left h2, max_eq_right (by linarith : -p1 ≤ p1)]

instance isProbabilityMeasure_pdGaussian_fin : IsProbabilityMeasure (pdGaussian (Fin N) ℝ) :=
  ⟨pdGaussian_univ⟩

instance isFiniteMeasure_boxSiteMeasure (p1 : ℝ) : IsFiniteMeasure (boxSiteMeasure N p1) := by
  unfold boxSiteMeasure; infer_instance

/-- The standard Gaussian of `Fin N → ℝ` is symmetric. -/
theorem map_neg_pdGaussian_fin : (pdGaussian (Fin N) ℝ).map Neg.neg = pdGaussian (Fin N) ℝ := by
  rw [pdGaussian_fin_eq]
  have h := withDensity_map_equiv (Measure.pi fun _ : Fin N => (volume : Measure ℝ))
    (MeasurableEquiv.neg (Fin N → ℝ)) (fun v => ENNReal.ofReal ((2 * Real.pi) ^ (-(N : ℝ) / 2) *
      Real.exp (-(1 / 2) * ∑ i, ‖v i‖ ^ 2)))
  rw [show ((MeasurableEquiv.neg (Fin N → ℝ) : (Fin N → ℝ) → (Fin N → ℝ))) = Neg.neg from rfl] at h
  rw [h, Measure.map_neg_eq_self]
  congr 1
  funext v
  simp [Function.comp, MeasurableEquiv.neg]

theorem neg_preimage_gaussBox (p1 : ℝ) :
    (Neg.neg : (Fin N → ℝ) → (Fin N → ℝ)) ⁻¹' gaussBox (Fin N) p1 = gaussBox (Fin N) p1 := by
  ext v
  simp [gaussBox, abs_neg]

/-- The box measure of a block is symmetric. -/
theorem map_neg_boxSiteMeasure (p1 : ℝ) :
    (boxSiteMeasure N p1).map Neg.neg = boxSiteMeasure N p1 := by
  have hA := measurableSet_gaussBox (Fin N) p1
  ext s hs
  rw [Measure.map_apply measurable_neg hs]
  unfold boxSiteMeasure
  rw [cond_apply hA, cond_apply hA]
  congr 1
  have e : gaussBox (Fin N) p1 ∩ (Neg.neg ⁻¹' s) =
      (Neg.neg : (Fin N → ℝ) → (Fin N → ℝ)) ⁻¹' (gaussBox (Fin N) p1 ∩ s) := by
    rw [Set.preimage_inter, neg_preimage_gaussBox]
  rw [e, ← Measure.map_apply measurable_neg (hA.inter hs), map_neg_pdGaussian_fin]

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
theorem cellField_neg (Φ : ∀ z, CellSpace (S := S) (n := n) (M := M) (K := K) k Mc N z) :
    cellField (-Φ) = -cellField Φ := rfl

/-- The negation of the cell configurations preserves the product of the box measures. -/
theorem measurePreserving_neg_cell (p1 : ℝ) :
    MeasurePreserving (MeasurableEquiv.neg (∀ z, CellSpace (S := S) (n := n) (M := M) (K := K)
      k Mc N z)) (Measure.pi (qRef (cellOf (S := S) (n := n) (M := M) (K := K) k Mc)
        (boxSiteMeasure N p1)))
      (Measure.pi (qRef (cellOf (S := S) (n := n) (M := M) (K := K) k Mc)
        (boxSiteMeasure N p1))) := by
  have h1 : ∀ z, MeasurePreserving
      (fun a : CellSpace (S := S) (n := n) (M := M) (K := K) k Mc N z => fun x => -a x)
      (qRef (cellOf (S := S) (n := n) (M := M) (K := K) k Mc) (boxSiteMeasure N p1) z)
      (qRef (cellOf (S := S) (n := n) (M := M) (K := K) k Mc) (boxSiteMeasure N p1) z) :=
    fun z => measurePreserving_pi _ _ fun _ => ⟨measurable_neg, map_neg_boxSiteMeasure p1⟩
  have hσ : ∀ z, SigmaFinite
      (qRef (cellOf (S := S) (n := n) (M := M) (K := K) k Mc) (boxSiteMeasure N p1) z) :=
    fun z => qRef_sigmaFinite (boxSiteMeasure N p1) z
  exact measurePreserving_pi _ _ h1

/-- The terms at the dilation `-t` are the terms at `t` of the negated configuration (the
undilated part is even). -/
theorem boxCellTerm_neg {W : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℂ) →
      (GIdx S n M K N → ℂ) → ℂ}
    {U : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℝ) → ℂ}
    (hU : ∀ Y w, U Y (-w) = U Y w) {p1 : ℝ} (hp1 : 0 ≤ p1)
    (𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc))
    (Φ : ∀ z, CellSpace (S := S) (n := n) (M := M) (K := K) k Mc N z) (t : ℂ)
    (g : GIdx S n M K N → ℂ) :
    boxCellTerm W U Mc p1 𝒳 Φ (-t, g) = boxCellTerm W U Mc p1 𝒳 (-Φ) (t, g) := by
  unfold boxCellTerm
  refine Finset.sum_congr rfl fun Y _ => ?_
  have e : dilField (-t) (clampBox p1 (cellField Φ)) =
      dilField t (clampBox p1 (cellField (-Φ))) := by
    rw [cellField_neg, clampBox_neg hp1]
    funext p
    simp only [dilField, Pi.neg_apply]
    push_cast; ring
  have eU : U Y (clampBox p1 (cellField (-Φ))) = U Y (clampBox p1 (cellField Φ)) := by
    rw [cellField_neg, clampBox_neg hp1, hU]
  simp only
  rw [e, eU]

/-- **The local terms of the box gas are even in the dilation** (the box measure is symmetric and the
undilated part is even). -/
theorem boxCellP_neg {W : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℂ) →
      (GIdx S n M K N → ℂ) → ℂ}
    {U : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℝ) → ℂ}
    (hU : ∀ Y w, U Y (-w) = U Y w) {p1 : ℝ} (hp1 : 0 ≤ p1) (t : ℂ) (g : GIdx S n M K N → ℂ)
    (𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc)) :
    boxCellP W U Mc p1 (-t, g) 𝒳 = boxCellP W U Mc p1 (t, g) 𝒳 := by
  unfold boxCellP localGasP
  congr 1
  funext Z
  unfold localGasK mayerK
  rw [← (measurePreserving_neg_cell p1).integral_comp']
  congr 1
  funext Φ
  unfold mayerAct polyAct
  refine Finset.sum_congr rfl fun C _ => Finset.prod_congr rfl fun X _ => ?_
  show Complex.exp (boxCellTerm W U Mc p1 X.1 (-Φ) (-t, g)) - 1 =
    Complex.exp (boxCellTerm W U Mc p1 X.1 Φ (t, g)) - 1
  rw [boxCellTerm_neg hU hp1, neg_neg]

/-- **At the dilation `t = 0` the local terms of the box gas do not depend on the source** (they are
those of the gas of the undilated part, by (W0)). -/
theorem boxCellP_zero_dil (hW : BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU W U)
    (g : GIdx S n M K N → ℂ) (𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc)) :
    boxCellP W U Mc p1 (0, g) 𝒳 = boxCellP W U Mc p1 (0, 0) 𝒳 := by
  refine gasP_congr_param 𝒳 fun X _ Φ => ?_
  unfold boxCellTerm
  refine Finset.sum_congr rfl fun Y _ => ?_
  simp only [dilField_zero, hW.normalized]

end Gas


end Balaban.RootFSpine
