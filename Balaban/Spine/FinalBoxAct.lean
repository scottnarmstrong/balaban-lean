/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalBoxHull
public import Balaban.Spine.FinalBoxEven
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The scale-`(k+1)` activities of the box gas on one torus

A6-3, gas layer, the regrouping of the activities of the cell gas (`boxCellAct`) into Root-F's
scale-`(k+1)` polymers: the activity of a set `X` of fine sites is the sum of the activities of the
sets of cells whose hull in the cubes of side `M L^{k+1}` is `X` (`boxAct`). On one torus:

* `sum_boxAct`: `Σ_X A(X) = Σ_𝒳 A(𝒳)`;
* `boxAct_support`: `A(X) = 0` unless `X` is a polymer of side `M L^{k+1}`;
* `boxAct_analytic`, `boxAct_local`: analytic on the unit `ℓ¹` ball, local in `g|_X`;
* `boxAct_bound`: the increments `A(X; g) - A(X; 0)` are of second order in the dilation:
  `≤ (2 (M L)^d C_KP / R_t²) e^{-(κ'/3^d - 1)|X|/(M L^{k+1})^d}` with `C_KP` the Kotecký–Preiss bound
  of the cell gas (`boxCellP_kp_bound`, with `ε + ε_U`). The proof: `F(t, g) = A_t(X; g) - A_t(X; 0)`
  is even in the dilation `t` (`boxCellP_neg`; the undilated part is even) and vanishes at `t = 0`
  (`boxCellP_zero_dil`: at `t = 0` only the undilated part remains, which does not depend on the
  source), so `|F(1, g)| ≤ sup|F| / R_t²` (`norm_le_div_sq_of_even_param`).
-/

@[expose] public section

open Finset Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2 Balaban.Green
  Balaban.Polymer Balaban.Multiscale

namespace Balaban.RootFSpine

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ}

/-- The source on the fine torus as a function on the indices `GIdx`. -/
def srcIdx (g : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ) : GIdx S n M K N → ℂ :=
  fun i => g i.1 i.2

theorem sum_norm_srcIdx (g : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ) :
    ∑ i, ‖srcIdx (S := S) (n := n) (M := M) (K := K) g i‖ = ∑ y, ∑ i, ‖g y i‖ := by
  unfold srcIdx
  rw [Fintype.sum_prod_type]

/-- **The scale-`(k+1)` activity of the box gas** at the dilation `t` and the source `g`: the sum of
the local terms of the cell gas over the sets of cells with hull `X`. -/
noncomputable def boxActDil (W : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℂ) →
      (GIdx S n M K N → ℂ) → ℂ) (U : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℝ) → ℂ) (Mc : ℕ) (p1 : ℝ) (X : Finset (Torus S.d (M * n K * S.L ^ K)))
    (q : ℂ × (Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ)) : ℂ :=
  ∑ 𝒳 ∈ (Finset.univ : Finset (Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc))).filter
    (fun 𝒳 => cellHull (S := S) (n := n) (M := M) (K := K) k Mc 𝒳 = X),
      boxCellP W U Mc p1 (q.1, srcIdx q.2) 𝒳

/-- **The scale-`(k+1)` activity of the box gas** on a set `X` of fine sites (the dilation `t = 1`):
`A(X; g) = Σ_{𝒳 : hull(𝒳) = X} A(𝒳; g)`. -/
noncomputable def boxAct (W : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℂ) →
      (GIdx S n M K N → ℂ) → ℂ) (U : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℝ) → ℂ) (Mc : ℕ) (p1 : ℝ) (X : Finset (Torus S.d (M * n K * S.L ^ K)))
    (g : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ) : ℂ :=
  boxActDil W U Mc p1 X (1, g)

variable {W : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℂ) →
  (GIdx S n M K N → ℂ) → ℂ} {U : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℝ) → ℂ}
  {Mc : ℕ} {p1 : ℝ}

/-- **The regrouping is a partition**: `Σ_X A(X; g) = Σ_𝒳 A(𝒳; g)`. -/
theorem sum_boxAct (g : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ) :
    ∑ X, boxAct W U Mc p1 X g = ∑ 𝒳, boxCellAct W U Mc p1 (srcIdx g) 𝒳 := by
  unfold boxAct boxActDil boxCellAct
  exact Finset.sum_fiberwise _ _ _

section Clauses

variable {C : SFCtx S n R M K N k m₁ ϱ} {vc : CorrCoef S.d} {hv : EuclideanSpace ℝ (Fin N)}
  {A : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ} {G₀ Rt a ε εU : ℝ}

/-- **Support**: the activity vanishes unless `X` is a polymer of side `M L^{k+1}`. -/
theorem boxAct_support (hW : BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU W U) (hMc : 0 < Mc)
    (hp1 : 0 ≤ p1) (hk : k ≤ K) (X : Finset (Torus S.d (M * n K * S.L ^ K)))
    (hX : ¬ IsPolymer S.d (M * n K * S.L ^ K) (M * S.L ^ (k + 1)) X)
    (q : ℂ × (Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ)) : boxActDil W U Mc p1 X q = 0 := by
  unfold boxActDil
  refine Finset.sum_eq_zero fun 𝒳 h𝒳 => ?_
  refine boxCellP_eq_zero_of_not_isAnimal hW hMc hp1 _ 𝒳 fun ha => hX ?_
  rw [← (Finset.mem_filter.1 h𝒳).2]
  exact isPolymer_cellHull hk ha

/-- **Locality**: the activity of `X` depends on the source at the sites of `X` only. -/
theorem boxAct_local (hW : BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU W U)
    (X : Finset (Torus S.d (M * n K * S.L ^ K))) (t : ℂ)
    {g g' : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ} (hgg : ∀ y ∈ X, g y = g' y) :
    boxActDil W U Mc p1 X (t, g) = boxActDil W U Mc p1 X (t, g') := by
  unfold boxActDil
  refine Finset.sum_congr rfl fun 𝒳 h𝒳 => boxCellP_congr_g hW t 𝒳 fun i hi => ?_
  have hmem : i.1 ∈ X := by
    rw [← (Finset.mem_filter.1 h𝒳).2]
    refine subset_hullT _ _ ?_
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
  show g i.1 i.2 = g' i.1 i.2
  rw [hgg _ hmem]

/-- The source map `(t, g) ↦ (t, srcIdx g)` is a continuous linear map. -/
theorem analyticOnNhd_srcParam (s : Set (ℂ × (Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ))) :
    AnalyticOnNhd ℂ (fun q : ℂ × (Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ) =>
      ((q.1, srcIdx q.2) : BoxParam S n M K N)) s := by
  have hl : AnalyticOnNhd ℂ (fun g : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ =>
      srcIdx (S := S) (n := n) (M := M) (K := K) g) Set.univ := by
    let U : (Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ) →L[ℂ] (GIdx S n M K N → ℂ) :=
      ContinuousLinearMap.pi fun p =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) p.2).comp
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Torus S.d (M * n K * S.L ^ K) =>
            Fin N → ℂ) p.1)
    exact (U.analyticOnNhd Set.univ).congr isOpen_univ fun g _ => rfl
  exact analyticOnNhd_fst.prod ((hl.comp analyticOnNhd_snd fun _ _ => Set.mem_univ _).mono
    (Set.subset_univ _))

/-- **Analyticity** of the dilated activity on `|t| < R_t` × the unit `ℓ¹` ball. -/
theorem boxActDil_analytic (hW : BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU W U) (hMc : 0 < Mc)
    (hp1 : 0 < p1) {κ' : ℝ} (hκ' : 0 ≤ κ') (ha : κ' + 12 * S.d + 21 / 2 ≤ a)
    (hε : ((2 * Mc : ℕ) : ℝ) ^ S.d * (ε + εU) ≤ 1 / 2) (X : Finset (Torus S.d (M * n K * S.L ^ K))) :
    AnalyticOnNhd ℂ (boxActDil W U Mc p1 X)
      (Metric.ball (0 : ℂ) Rt ×ˢ {g | ∑ y, ∑ i, ‖g y i‖ < 1}) := by
  unfold boxActDil
  refine Finset.analyticOnNhd_fun_sum _ fun 𝒳 _ => ?_
  refine (analyticOnNhd_boxCellP hW hMc hp1 hκ' ha hε 𝒳).comp (analyticOnNhd_srcParam _)
    fun q hq => ⟨hq.1, ?_⟩
  show ∑ i, ‖srcIdx q.2 i‖ < G₀
  rw [sum_norm_srcIdx]
  exact lt_of_lt_of_le hq.2 hW.one_le_G₀

/-- **Analyticity** of the activity on the unit `ℓ¹` ball. -/
theorem boxAct_analytic (hW : BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU W U) (hMc : 0 < Mc)
    (hp1 : 0 < p1) {κ' : ℝ} (hκ' : 0 ≤ κ') (ha : κ' + 12 * S.d + 21 / 2 ≤ a)
    (hε : ((2 * Mc : ℕ) : ℝ) ^ S.d * (ε + εU) ≤ 1 / 2) (X : Finset (Torus S.d (M * n K * S.L ^ K))) :
    AnalyticOnNhd ℂ (boxAct W U Mc p1 X) {g | ∑ y, ∑ i, ‖g y i‖ < 1} := by
  have h1 := boxActDil_analytic hW hMc hp1 hκ' ha hε X
  have hRt : (1 : ℝ) < Rt := by linarith [hW.two_le_Rt]
  have h2 : AnalyticOnNhd ℂ (fun g : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ => ((1 : ℂ), g))
      {g | ∑ y, ∑ i, ‖g y i‖ < 1} := analyticOnNhd_const.prod analyticOnNhd_id
  exact h1.comp h2 fun g hg => ⟨by simpa using hRt, hg⟩

/-- The hull of a set of cells is a union of cubes of side `M L^{k+1}`. -/
theorem cellHull_closed (𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc)) :
    ∀ x ∈ cellHull (S := S) (n := n) (M := M) (K := K) k Mc 𝒳, ∀ z : Torus S.d (M * n K * S.L ^ K),
      (∀ μ, (x μ).val / (M * S.L ^ (k + 1)) = (z μ).val / (M * S.L ^ (k + 1))) →
        z ∈ cellHull (S := S) (n := n) (M := M) (K := K) k Mc 𝒳 := by
  intro x hx z hxz
  obtain ⟨y, hy, hxy⟩ := mem_hullT.1 hx
  exact mem_hullT.2 ⟨y, hy, fun μ => (hxz μ).symm.trans (hxy μ)⟩

/-- The Kotecký–Preiss constant of the box gas. -/
noncomputable def boxKP (d Mc : ℕ) (ε : ℝ) : ℝ :=
  64 * Real.exp 1 * (((2 * Mc : ℕ) : ℝ) ^ d * ε) * Real.exp (-(2 * cellKappa0 d))

/-- The Kotecký–Preiss constant of the box gas is nonnegative. -/
theorem boxKP_nonneg (hW : BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU W U) (hMc : 0 < Mc)
    (hp1 : 0 < p1) {κ' : ℝ} (hκ' : 0 ≤ κ') (ha : κ' + 12 * S.d + 21 / 2 ≤ a)
    (hε : ((2 * Mc : ℕ) : ℝ) ^ S.d * (ε + εU) ≤ 1 / 2) : 0 ≤ boxKP S.d Mc (ε + εU) := by
  have hq : ((0 : ℂ), (0 : GIdx S n M K N → ℂ)) ∈
      boxParamSet (S := S) (n := n) (M := M) (K := K) (N := N) Rt G₀ :=
    ⟨by simpa using (by linarith [hW.two_le_Rt] : (0 : ℝ) < Rt), by
      show ∑ i, ‖(0 : GIdx S n M K N → ℂ) i‖ < G₀
      simp only [Pi.zero_apply, norm_zero, Finset.sum_const_zero]
      linarith [hW.one_le_G₀]⟩
  exact (Finset.sum_nonneg fun 𝒳 _ => by positivity).trans
    (boxCellP_kp_bound hW hMc hp1 hκ' ha hε hq (cellOf (S := S) (n := n) (M := M) (K := K) k Mc 0))

/-- The activity of a set that is not the hull of a set of cells vanishes. -/
theorem boxActDil_eq_zero_of_not_hull {X : Finset (Torus S.d (M * n K * S.L ^ K))}
    (hX : ¬ ∃ 𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc),
      cellHull (S := S) (n := n) (M := M) (K := K) k Mc 𝒳 = X)
    (q : ℂ × (Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ)) : boxActDil W U Mc p1 X q = 0 := by
  unfold boxActDil
  exact Finset.sum_eq_zero fun 𝒳 h𝒳 => absurd ⟨𝒳, (Finset.mem_filter.1 h𝒳).2⟩ hX

/-- **The sup bound of the dilated activity**: on the polydisc, `|A_t(X; g)| ≤ (M L)^d C_KP r
e^{-κ' r/3^d}`, `r` the number of cubes of side `M L^{k+1}` of `X`. -/
theorem norm_boxActDil_le (hW : BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU W U) (hMc : 0 < Mc)
    (hp1 : 0 < p1) (hk1 : k + 1 ≤ K) (hMcL : Mc ≤ M * S.L) {κ' : ℝ} (hκ' : 0 ≤ κ')
    (ha : κ' + 12 * S.d + 21 / 2 ≤ a) (hε : ((2 * Mc : ℕ) : ℝ) ^ S.d * (ε + εU) ≤ 1 / 2)
    (X : Finset (Torus S.d (M * n K * S.L ^ K))) {t : ℂ} (ht : ‖t‖ < Rt)
    {g : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ} (hg : ∑ y, ∑ i, ‖g y i‖ < 1) :
    ‖boxActDil W U Mc p1 X (t, g)‖ ≤
      ((M * S.L : ℕ) : ℝ) ^ S.d * boxKP S.d Mc (ε + εU) *
        ((X.image (cubeOf (S := S) (n := n) (M := M) (K := K) k)).card : ℝ) *
        Real.exp (-κ' * ((X.image (cubeOf (S := S) (n := n) (M := M) (K := K) k)).card : ℝ) /
          3 ^ S.d) := by
  have hk : k ≤ K := by omega
  have hKP := boxKP_nonneg hW hMc hp1 hκ' ha hε
  by_cases hX : ∃ 𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc),
      cellHull (S := S) (n := n) (M := M) (K := K) k Mc 𝒳 = X
  swap
  · rw [boxActDil_eq_zero_of_not_hull hX, norm_zero]; positivity
  obtain ⟨𝒳₀, rfl⟩ := hX
  set X := cellHull (S := S) (n := n) (M := M) (K := K) k Mc 𝒳₀ with hXdef
  set r : ℕ := (X.image (cubeOf (S := S) (n := n) (M := M) (K := K) k)).card with hr
  set Z := X.image (fineCellOf (S := S) (n := n) (M := M) (K := K) k Mc) with hZ
  have hq : ((t, srcIdx g) : BoxParam S n M K N) ∈
      boxParamSet (S := S) (n := n) (M := M) (K := K) (N := N) Rt G₀ :=
    ⟨by simpa using ht, by
      show ∑ i, ‖srcIdx g i‖ < G₀
      rw [sum_norm_srcIdx]; exact lt_of_lt_of_le hg hW.one_le_G₀⟩
  set f : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc) → ℝ := fun 𝒳 =>
    ‖boxCellP W U Mc p1 (t, srcIdx g) 𝒳‖ * Real.exp (κ' * stSizeG (macCellGraph Mc) 𝒳) *
      Real.exp (-κ' * (r : ℝ) / 3 ^ S.d) with hf
  have hf0 : ∀ 𝒳, 0 ≤ f 𝒳 := fun 𝒳 => by positivity
  have hterm : ∀ 𝒳 ∈ (Finset.univ : Finset (Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc))).filter
      (fun 𝒳 => cellHull (S := S) (n := n) (M := M) (K := K) k Mc 𝒳 = X),
      ‖boxCellP W U Mc p1 (t, srcIdx g) 𝒳‖ ≤ f 𝒳 := by
    intro 𝒳 h𝒳
    have hX𝒳 := (Finset.mem_filter.1 h𝒳).2
    by_cases ha𝒳 : IsAnimal (macCellGraph Mc) 𝒳
    · have hst := stSizeG_eq_card ha𝒳
      have hcount := card_image_cubeOf_cellHull_le hk1 hMc hMcL 𝒳
      rw [hX𝒳] at hcount
      have h1 : (r : ℝ) / 3 ^ S.d ≤ 𝒳.card := by
        rw [div_le_iff₀ (by positivity)]
        have : (r : ℝ) ≤ (3 ^ S.d * 𝒳.card : ℕ) := by exact_mod_cast hcount
        push_cast at this; linarith
      have h2 : 1 ≤ Real.exp (κ' * stSizeG (macCellGraph Mc) 𝒳) *
          Real.exp (-κ' * (r : ℝ) / 3 ^ S.d) := by
        rw [← Real.exp_add, hst]
        refine Real.one_le_exp ?_
        have : κ' * ((r : ℝ) / 3 ^ S.d) ≤ κ' * 𝒳.card := mul_le_mul_of_nonneg_left h1 hκ'
        have e : -κ' * (r : ℝ) / 3 ^ S.d = -(κ' * ((r : ℝ) / 3 ^ S.d)) := by ring
        linarith
      calc ‖boxCellP W U Mc p1 (t, srcIdx g) 𝒳‖ = ‖boxCellP W U Mc p1 (t, srcIdx g) 𝒳‖ * 1 :=
            (mul_one _).symm
        _ ≤ _ := by
            have e : f 𝒳 = ‖boxCellP W U Mc p1 (t, srcIdx g) 𝒳‖ *
                (Real.exp (κ' * stSizeG (macCellGraph Mc) 𝒳) *
                  Real.exp (-κ' * (r : ℝ) / 3 ^ S.d)) := by simp only [hf]; ring
            rw [e]; exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    · rw [boxCellP_eq_zero_of_not_isAnimal hW hMc hp1.le _ 𝒳 ha𝒳, norm_zero]; exact hf0 𝒳
  have hcover : ∀ 𝒳 ∈ (Finset.univ : Finset (Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc))).filter
      (fun 𝒳 => cellHull (S := S) (n := n) (M := M) (K := K) k Mc 𝒳 = X), f 𝒳 ≠ 0 →
        ∃ z ∈ Z, z ∈ 𝒳 := by
    intro 𝒳 h𝒳 hne
    have hX𝒳 := (Finset.mem_filter.1 h𝒳).2
    have hP : boxCellP W U Mc p1 (t, srcIdx g) 𝒳 ≠ 0 := fun h0 => hne (by rw [hf]; simp [h0])
    have ha𝒳 : IsAnimal (macCellGraph Mc) 𝒳 := by
      by_contra hna; exact hP (boxCellP_eq_zero_of_not_isAnimal hW hMc hp1.le _ 𝒳 hna)
    obtain ⟨y, hy⟩ := (isPolymer_fineCells hk ha𝒳).1
    have hyX : y ∈ X := by rw [← hX𝒳]; exact subset_hullT _ _ hy
    exact ⟨_, Finset.mem_image_of_mem _ hyX, (Finset.mem_filter.1 hy).2⟩
  have hsum : ∑ z ∈ Z, ∑ 𝒳 ∈ (Finset.univ : Finset (Finset (MacIdx S.d (M * n K * S.L ^ (K - k))
      Mc))).filter (fun 𝒳 => z ∈ 𝒳), f 𝒳 ≤ (Z.card : ℝ) * (boxKP S.d Mc (ε + εU) *
        Real.exp (-κ' * (r : ℝ) / 3 ^ S.d)) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun z _ => ?_
    rw [hf]
    simp only
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (boxCellP_kp_bound hW hMc hp1 hκ' ha hε hq z)
      (Real.exp_pos _).le
  have hZcard : (Z.card : ℝ) ≤ ((M * S.L : ℕ) : ℝ) ^ S.d * r := by
    have h1 : Z.card ≤ (X.image (fineBlock (S := S) (n := n) (M := M) (K := K) k)).card := by
      rw [hZ]
      have : X.image (fineCellOf (S := S) (n := n) (M := M) (K := K) k Mc) =
          (X.image (fineBlock (S := S) (n := n) (M := M) (K := K) k)).image (cellOf k Mc) := by
        rw [Finset.image_image]; rfl
      rw [this]; exact Finset.card_image_le
    have h2 := card_image_fineBlock_eq hk1 X (cellHull_closed 𝒳₀)
    rw [h2] at h1
    exact_mod_cast h1
  unfold boxActDil
  calc _ ≤ ∑ 𝒳 ∈ (Finset.univ : Finset (Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc))).filter
        (fun 𝒳 => cellHull (S := S) (n := n) (M := M) (K := K) k Mc 𝒳 = X),
          ‖boxCellP W U Mc p1 (t, srcIdx g) 𝒳‖ := norm_sum_le _ _
    _ ≤ ∑ 𝒳 ∈ (Finset.univ : Finset (Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc))).filter
        (fun 𝒳 => cellHull (S := S) (n := n) (M := M) (K := K) k Mc 𝒳 = X), f 𝒳 :=
        Finset.sum_le_sum hterm
    _ ≤ _ := by
        rw [← Finset.sum_filter_ne_zero]
        convert Polymer.sum_le_sum_cover _ (fun 𝒳 => 𝒳) Z f hf0 fun 𝒳 h𝒳 =>
          hcover 𝒳 (Finset.mem_filter.1 h𝒳).1 (Finset.mem_filter.1 h𝒳).2 using 4
    _ ≤ _ := hsum
    _ ≤ ((M * S.L : ℕ) : ℝ) ^ S.d * r * (boxKP S.d Mc (ε + εU) * Real.exp (-κ' * (r : ℝ) / 3 ^ S.d)) :=
        mul_le_mul_of_nonneg_right hZcard (by positivity)
    _ = _ := by ring

/-- The dilated activity is even in the dilation (the undilated part is even). -/
theorem boxActDil_neg (hU : ∀ Y w, U Y (-w) = U Y w) (hp1 : 0 ≤ p1)
    (X : Finset (Torus S.d (M * n K * S.L ^ K))) (t : ℂ)
    (g : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ) :
    boxActDil W U Mc p1 X (-t, g) = boxActDil W U Mc p1 X (t, g) := by
  unfold boxActDil
  exact Finset.sum_congr rfl fun 𝒳 _ => boxCellP_neg hU hp1 t (srcIdx g) 𝒳

/-- At the dilation `0` the dilated activity does not depend on the source. -/
theorem boxActDil_zero (hW : BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU W U)
    (X : Finset (Torus S.d (M * n K * S.L ^ K))) (g : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ) :
    boxActDil W U Mc p1 X (0, g) = boxActDil W U Mc p1 X (0, 0) := by
  unfold boxActDil
  refine Finset.sum_congr rfl fun 𝒳 _ => ?_
  rw [boxCellP_zero_dil hW (srcIdx g) 𝒳, boxCellP_zero_dil hW (srcIdx 0) 𝒳]

/-- The amplitude of the increments of the box activities:
`B = 2 (M L)^d C_KP / R_t²`. -/
noncomputable def boxAmp (d M L Mc : ℕ) (ε Rt : ℝ) : ℝ :=
  2 * (((M * L : ℕ) : ℝ) ^ d * boxKP d Mc ε) / Rt ^ 2

/-- A union of cubes of side `M L^{k+1}` has `(M L^{k+1})^d` sites per cube. -/
theorem card_div_cube_eq (hk1 : k + 1 ≤ K) (𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc)) :
    ((cellHull (S := S) (n := n) (M := M) (K := K) k Mc 𝒳).card : ℝ) /
        ((M * S.L ^ (k + 1) : ℕ) : ℝ) ^ S.d =
      ((cellHull (S := S) (n := n) (M := M) (K := K) k Mc 𝒳).image
        (cubeOf (S := S) (n := n) (M := M) (K := K) k)).card := by
  have h := card_blockClosed (fine_eq_cubeSide hk1) _ (cellHull_closed (S := S) (n := n) (M := M)
    (K := K) (k := k) 𝒳)
  have hpos : (0 : ℝ) < ((M * S.L ^ (k + 1) : ℕ) : ℝ) ^ S.d := by
    have : 0 < M * S.L ^ (k + 1) := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne M))
      (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _)
    positivity
  rw [div_eq_iff hpos.ne', h]
  unfold cubeOf
  push_cast; ring

/-- **The increment bound of the box activities**: on the unit `ℓ¹` ball,
`|A(X; g) - A(X; 0)| ≤ B e^{-(κ'/3^d - 1)|X|/(M L^{k+1})^d}` with `B = boxAmp`. Second order in the
dilation: the increment `F(t, g) = A_t(X; g) - A_t(X; 0)` is even in `t` and vanishes at `t = 0`
(at `t = 0` the activity does not depend on the source), so `|F(1, g)| ≤ sup_{|t|<R_t} |F| / R_t²`
(`norm_le_div_sq_of_even_param`). -/
theorem boxAct_bound (hW : BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU W U) (hMc : 0 < Mc)
    (hp1 : 0 < p1) (hk1 : k + 1 ≤ K) (hMcL : Mc ≤ M * S.L) {κ' : ℝ} (hκ' : 0 ≤ κ')
    (ha : κ' + 12 * S.d + 21 / 2 ≤ a) (hε : ((2 * Mc : ℕ) : ℝ) ^ S.d * (ε + εU) ≤ 1 / 2)
    (X : Finset (Torus S.d (M * n K * S.L ^ K))) {g : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ}
    (hg : ∑ y, ∑ i, ‖g y i‖ < 1) :
    ‖boxAct W U Mc p1 X g - boxAct W U Mc p1 X 0‖ ≤ boxAmp S.d M S.L Mc (ε + εU) Rt *
      Real.exp (-(κ' / 3 ^ S.d - 1) * (X.card : ℝ) / ((M * S.L ^ (k + 1) : ℕ) : ℝ) ^ S.d) := by
  have hk : k ≤ K := by omega
  have hRt : (1 : ℝ) < Rt := by linarith [hW.two_le_Rt]
  have hKP := boxKP_nonneg hW hMc hp1 hκ' ha hε
  by_cases hX : ∃ 𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc),
      cellHull (S := S) (n := n) (M := M) (K := K) k Mc 𝒳 = X
  swap
  · unfold boxAct
    rw [boxActDil_eq_zero_of_not_hull hX, boxActDil_eq_zero_of_not_hull hX, sub_zero, norm_zero]
    unfold boxAmp; positivity
  obtain ⟨𝒳₀, rfl⟩ := hX
  set X := cellHull (S := S) (n := n) (M := M) (K := K) k Mc 𝒳₀ with hXdef
  set r : ℕ := (X.image (cubeOf (S := S) (n := n) (M := M) (K := K) k)).card with hr
  set Sup : ℝ := ((M * S.L : ℕ) : ℝ) ^ S.d * boxKP S.d Mc (ε + εU) * r *
    Real.exp (-κ' * (r : ℝ) / 3 ^ S.d) with hSup
  set Bl : Set (Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ) := {g | ∑ y, ∑ i, ‖g y i‖ < 1}
    with hBl
  have h0B : (0 : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ) ∈ Bl := by
    simp only [hBl, Set.mem_ofPred_eq, Pi.zero_apply, norm_zero, Finset.sum_const_zero]
    norm_num
  set F : ℂ × (Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ) → ℂ := fun q =>
    boxActDil W U Mc p1 X q - boxActDil W U Mc p1 X (q.1, 0) with hF
  have hA := boxActDil_analytic hW hMc hp1 hκ' ha hε X
  have hFa : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) Rt ×ˢ Bl) := by
    have h2 : AnalyticOnNhd ℂ (fun q : ℂ × (Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ) =>
        (q.1, (0 : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ))) (Metric.ball (0 : ℂ) Rt ×ˢ Bl) :=
      analyticOnNhd_fst.prod analyticOnNhd_const
    exact hA.sub (hA.comp h2 fun q hq => ⟨hq.1, h0B⟩)
  have hF0 : ∀ u ∈ Bl, F (0, u) = 0 := fun u _ => by
    simp only [hF]
    rw [boxActDil_zero hW X u, sub_self]
  have hFe : ∀ t ∈ Metric.ball (0 : ℂ) Rt, ∀ u ∈ Bl, F (-t, u) = F (t, u) := fun t _ u _ => by
    simp only [hF]
    rw [boxActDil_neg hW.even_u hp1.le X t u, boxActDil_neg hW.even_u hp1.le X t 0]
  have hFS : ∀ t ∈ Metric.ball (0 : ℂ) Rt, ∀ u ∈ Bl, ‖F (t, u)‖ ≤ 2 * Sup := fun t ht u hu => by
    have ht' : ‖t‖ < Rt := by simpa using ht
    simp only [hF]
    calc _ ≤ ‖boxActDil W U Mc p1 X (t, u)‖ + ‖boxActDil W U Mc p1 X (t, 0)‖ := norm_sub_le _ _
      _ ≤ Sup + Sup := add_le_add
          (norm_boxActDil_le hW hMc hp1 hk1 hMcL hκ' ha hε X ht' hu)
          (norm_boxActDil_le hW hMc hp1 hk1 hMcL hκ' ha hε X ht' h0B)
      _ = 2 * Sup := by ring
  have hmain := norm_le_div_sq_of_even_param hRt hFa hF0 hFe hFS (u := g) hg
  have hr_exp : (r : ℝ) * Real.exp (-κ' * (r : ℝ) / 3 ^ S.d) ≤
      Real.exp (-(κ' / 3 ^ S.d - 1) * (r : ℝ)) := by
    have h1 : (r : ℝ) ≤ Real.exp r := by linarith [Real.add_one_le_exp (r : ℝ)]
    calc (r : ℝ) * Real.exp (-κ' * (r : ℝ) / 3 ^ S.d)
        ≤ Real.exp r * Real.exp (-κ' * (r : ℝ) / 3 ^ S.d) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hcard := card_div_cube_eq (S := S) (n := n) (M := M) (K := K) hk1 𝒳₀
  have hrate : -(κ' / 3 ^ S.d - 1) * (X.card : ℝ) / ((M * S.L ^ (k + 1) : ℕ) : ℝ) ^ S.d =
      -(κ' / 3 ^ S.d - 1) * (r : ℝ) := by
    rw [mul_div_assoc, hcard]
  rw [hrate]
  calc ‖boxAct W U Mc p1 X g - boxAct W U Mc p1 X 0‖ = ‖F (1, g)‖ := rfl
    _ ≤ 2 * Sup / Rt ^ 2 := hmain
    _ = 2 * (((M * S.L : ℕ) : ℝ) ^ S.d * boxKP S.d Mc (ε + εU)) / Rt ^ 2 *
          ((r : ℝ) * Real.exp (-κ' * (r : ℝ) / 3 ^ S.d)) := by rw [hSup]; ring
    _ ≤ _ := by
        unfold boxAmp
        exact mul_le_mul_of_nonneg_left hr_exp (by positivity)

end Clauses

end Balaban.RootFSpine
