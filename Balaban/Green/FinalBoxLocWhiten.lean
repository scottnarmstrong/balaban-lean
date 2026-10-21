/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocTies
public import Balaban.Green.FinalBoxLocK
public import Balaban.Green.FinalBoxLocConj
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NoncommRing

/-!
# The localized square root of the final Hessian (A6-3, Amendment B-1′; P5 (2.39))

The last integral changes variables by `ψ = h + β_k^{-1/2} L ψ̂`, where `L` is the **localized
square root**: row `p` of `L` is row `p` of the cut family `boxCut(s_p)` of the final Hessian `D`,
with `s_p = 1` on the macro cells of the localization domain of `p` and `0` elsewhere.  At `s = 1`
the cut family is `D^{-1/2}` (`boxCut_one`), so `L` differs from `D^{-1/2}` by the truncation of
the parameters, which the rooted expansion of the entries `s ↦ boxCut(s)(p, q)` controls.

**Abstract core** (any cut family with the decoupling property, `CutDecoupling`):
* `sub_cutTo_eq_sum_coef`: `f(1) - f(1_B) = ∑_{C ⊄ B} coef_C f` (Lemma AE and its truncation);
* `locDom P D x`: the cells within distance `D` in the cell graph of a cell whose patch contains
  `x`;
* `norm_cutTo_sub_le`: `‖T(1_B) x y - T(1) x y‖ ≤ b ∑_{C ⊄ B rooted at x} e^{-(κ-1)|C|}`, `b` a
  bound of the entry on the polydisc of radius `e^κ`;
* `sum_rooted_not_subset_locDom_le`: a family rooted at `x` and not inside `locDom P D x` is an
  animal of at least `D + 2` cells, so the sum is at most `#roots · whitenTail Δ (κ - 1) D`,
  `whitenTail Δ c D = e^{-c} q^{D+1} / (1 - q)`, `q = Δ² e^{-c}`.

**The localized square root** (`finalWhiten`) and the **mismatch** `Q = Lᵀ D L - 1`
(`finalWhitenMismatch`):
* `finalWhiten_eq_zero_of_not_mem` (finite range): `L(p, q) = 0` unless `q` lies in the region
  of the localization domain of `p`;
* `finalWhiten_row_bound`: the row sums of `L` are at most `boxCutConst`;
* `whitenCut`: the cut family of `L` (row `p` of `boxCut(s|_{locDom p})`, `whitenCut_one`), with
  the decoupling property (`cutDecoupling_whitenCut`, core `CutDecoupling.rowCut`), analytic
  entries and the row bound `boxCutConst` on the polydisc: the rooted expansion
  (`rootedExpansion_of_row_bound`) localizes the terms at the field `h + c L w`;
* `norm_finalWhiten_sub_le` (row error, entrywise): `‖L(p, q) - D^{-1/2}(p, q)‖ ≤
  boxCutConst(N = 1) e^{-r |p - q|} 7^d whitenTail (16^d) (κ - 1) D`; weighted row and column sums
  `sum_finalWhiten_sub_row_le`, `sum_finalWhiten_sub_col_le` (`whitenErr`);
* `finalWhiten_real`, `finalWhitenR_map`: for a real `h` the entries of `L` are real;
* `finalWhitenMismatch_eq`: `Q = D^{-1/2} D E + Eᵀ D D^{-1/2} + Eᵀ D E`, `E = L - D^{-1/2}`, for a
  real unit `h` (`D^{-1/2} D D^{-1/2} = 1` by the K-link);
* `finalWhitenMismatch_transpose` (evenness): `Qᵀ = Q`, so `⟨ψ̂, Q ψ̂⟩` is a symmetric even form
  (`finalWhitenMismatch_quad_neg`);
* `sum_finalWhitenMismatch_le` (smallness): the weighted row sums of `Q` (weight
  `e^{r' |p - q|}`, `0 ≤ r' < r ≤ ε/8`) are at most `whitenMismatchBound`;
* the choice of the radius: `whitenTail_le_of_ties` (`whitenTail ≤ 2^{-D}` under `BoxCutTies`),
  `whitenErr_le_of_ties` (`whitenErr ≤ whitenErrConst 2^{-D}`), `whitenMismatchBound_le_of_ties`
  (`whitenMismatchBound ≤ whitenQConst 2^{-D}`), `exists_whitenRadius` (every `ε > 0` is reached
  beyond some `D₀`);
* `det_finalWhiten_sq`: `det(L)² det(D) = det(1 + Q)`; `isUnit_finalWhiten_of_lt_one`: `L` is
  invertible when `whitenMismatchBound < 1`; `exists_isUnit_finalWhiten`: `L` is invertible for
  all radii beyond some `D₀`.
-/

@[expose] public section

namespace Balaban.Green

open Finset Matrix Balaban.Localization Balaban.Analysis ComplexConjugate

section Truncation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cut to `B` is analytic. -/
theorem analyticAt_cutTo (B : Finset ι) (s : ι → ℂ) : AnalyticAt ℂ (cutTo B) s := by
  refine analyticAt_pi_iff.2 fun i => ?_
  by_cases hi : i ∈ B
  · simp only [cutTo, hi, ↓reduceIte]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt s
  · simp only [cutTo, hi, ↓reduceIte]
    exact analyticAt_const

/-- **The truncation identity**: for `f` analytic on the polydisc of radius `R > 1`,
`f(1) - f(1_B) = ∑_{C ⊄ B} coef_C f`. -/
theorem sub_cutTo_eq_sum_coef {R : ℝ} (hR : 1 < R) {f : (ι → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f (polydisc (0 : ι → ℂ) (fun _ => R))) (B : Finset ι) :
    f (fun _ => 1) - f (cutTo B (fun _ => 1)) =
      ∑ C ∈ Finset.univ.filter (fun C : Finset ι => ¬ C ⊆ B), coef f C := by
  have hR0 : 0 < R := by linarith
  have hg : AnalyticOnNhd ℂ (fun s => f (cutTo B s)) (polydisc (0 : ι → ℂ) (fun _ => R)) :=
    fun s hs => (hf _ (cutTo_mem_polydisc hR0 B hs)).comp (analyticAt_cutTo B s)
  have h1 := sum_coef_eq hR hf
  have h2 := sum_coef_eq hR hg
  have hin : ∀ C : Finset ι, C ⊆ B → coef (fun s => f (cutTo B s)) C = coef f C := by
    intro C hCB
    refine coef_congr_supported hR fun s _ hsC => ?_
    rw [cutTo_eq_self (fun i hi => hsC i (fun h => hi (hCB h)))]
  have hout : ∀ C : Finset ι, ¬ C ⊆ B → coef (fun s => f (cutTo B s)) C = 0 := by
    intro C hCB
    obtain ⟨i₀, hi₀C, hi₀B⟩ := Finset.not_subset.1 hCB
    refine coef_eq_zero_of_eq_cutTo hR hi₀C hi₀B fun s _ _ => ?_
    simp only [cutTo_cutTo_of_subset (subset_refl B)]
  have e1 : ∑ C : Finset ι, coef f C =
      ∑ C ∈ Finset.univ.filter (fun C : Finset ι => C ⊆ B), coef f C +
        ∑ C ∈ Finset.univ.filter (fun C : Finset ι => ¬ C ⊆ B), coef f C :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have e2 : ∑ C : Finset ι, coef (fun s => f (cutTo B s)) C =
      ∑ C ∈ Finset.univ.filter (fun C : Finset ι => C ⊆ B), coef f C := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun C : Finset ι => C ⊆ B)]
    rw [Finset.sum_eq_zero (fun C hC => hout C (Finset.mem_filter.1 hC).2), add_zero]
    exact Finset.sum_congr rfl fun C hC => hin C (Finset.mem_filter.1 hC).2
  change f 1 - f (cutTo B 1) = _
  have h2' : f (cutTo B 1) = ∑ C : Finset ι, coef (fun s => f (cutTo B s)) C := h2
  rw [h1, h2', e1, e2]
  ring

end Truncation

section Dom

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] {P : ι → Set Ω}

open Classical in
/-- **The localization domain of radius `D` of a point `x`**: the cells within distance `D` in
the cell graph of a cell whose patch contains `x`. -/
noncomputable def locDom (P : ι → Set Ω) (D : ℕ) (x : Ω) : Finset ι :=
  Finset.univ.filter fun z => ∃ j, x ∈ P j ∧ (cellGraph P).edist j z ≤ D

omit [DecidableEq ι] in
theorem mem_locDom {D : ℕ} {x : Ω} {z : ι} :
    z ∈ locDom P D x ↔ ∃ j, x ∈ P j ∧ (cellGraph P).edist j z ≤ D := by
  classical
  unfold locDom
  simp

omit [DecidableEq ι] in
/-- The cells whose patch contains `x` lie in its localization domain. -/
theorem mem_locDom_of_mem {D : ℕ} {x : Ω} {j : ι} (hj : x ∈ P j) : j ∈ locDom P D x :=
  mem_locDom.2 ⟨j, hj, by simp⟩

omit [Fintype ι] [DecidableEq ι] in
/-- In an animal, the graph distance of two cells is less than the number of cells. -/
theorem exists_edist_le_card {G : SimpleGraph ι} {K : Finset ι} (hK : Polymer.IsAnimal G K)
    {i j : ι} (hi : i ∈ K) (hj : j ∈ K) : ∃ n : ℕ, G.edist i j ≤ n ∧ n + 1 ≤ K.card := by
  classical
  obtain ⟨w⟩ := hK.2.preconnected ⟨i, hi⟩ ⟨j, hj⟩
  refine ⟨w.toPath.1.length, ?_, ?_⟩
  · have := SimpleGraph.edist_le
      (w.toPath.1.map (SimpleGraph.Embedding.induce (K : Set ι)).toHom)
    rwa [SimpleGraph.Walk.length_map] at this
  · have := w.toPath.2.length_lt
    have hc : Fintype.card (K : Set ι) = K.card := by simp
    omega

omit [Fintype ι] [DecidableEq ι] in
/-- **A family rooted at a point is the component of any root cell.** -/
theorem compOf_eq_of_isRootedFamily_singleton {x : Ω} {C : Finset ι}
    (hC : IsRootedFamily P {x} C) {j : ι} (hj : j ∈ C) (hxj : x ∈ P j) : compOf P C j = C := by
  refine Finset.Subset.antisymm (compOf_subset C j) fun i hi => ?_
  obtain ⟨l, hl, ⟨y, hyl, hy⟩, hli⟩ := hC i hi
  have hyx : y = x := hy
  rw [hyx] at hyl
  exact mem_compOf.2 ⟨hi, Relation.ReflTransGen.head ⟨hj, hl, x, hxj, hyl⟩ hli⟩

/-- The tail of the count: `whitenTail Δ c D = e^{-c} q^{D+1} / (1 - q)`, `q = Δ² e^{-c}`. -/
noncomputable def whitenTail (Δ : ℕ) (c : ℝ) (D : ℕ) : ℝ :=
  Real.exp (-c) * ((Δ : ℝ) ^ 2 * Real.exp (-c)) ^ (D + 1) / (1 - (Δ : ℝ) ^ 2 * Real.exp (-c))

theorem whitenTail_nonneg {Δ : ℕ} {c : ℝ} (hq : (Δ : ℝ) ^ 2 * Real.exp (-c) < 1) (D : ℕ) :
    0 ≤ whitenTail Δ c D := by
  unfold whitenTail
  have : 0 < 1 - (Δ : ℝ) ^ 2 * Real.exp (-c) := by linarith
  positivity

open Classical in
/-- **The count of the rooted families leaving the localization domain**: with a degree bound `Δ`
of the cell graph and `q = Δ² e^{-c} < 1`,
`∑_{C rooted at x, C ⊄ locDom P D x} e^{-c|C|} ≤ #roots(x) · whitenTail Δ c D`. -/
theorem sum_rooted_not_subset_locDom_le {Δ : ℕ} (hΔ : ∀ v, (cellGraph P).degree v ≤ Δ) {c : ℝ}
    (hq : (Δ : ℝ) ^ 2 * Real.exp (-c) < 1) (D : ℕ) (x : Ω) :
    ∑ C ∈ Finset.univ.filter
        (fun C : Finset ι => ¬ C ⊆ locDom P D x ∧ IsRootedFamily P {x} C),
        Real.exp (-c * C.card) ≤ (rootCells P {x}).card * whitenTail Δ c D := by
  set F := Finset.univ.filter
    (fun C : Finset ι => ¬ C ⊆ locDom P D x ∧ IsRootedFamily P {x} C)
  have hsub : F ⊆ (rootCells P {x}).biUnion
      (fun j => (animalsAt P j).filter (fun K => D + 2 ≤ K.card)) := by
    intro C hC
    obtain ⟨hCB, hCr⟩ := (Finset.mem_filter.1 hC).2
    obtain ⟨z, hzC, hzB⟩ := Finset.not_subset.1 hCB
    obtain ⟨l, hl, ⟨y, hyl, hy⟩, -⟩ := hCr z hzC
    have hyx : y = x := hy
    rw [hyx] at hyl
    have hA : Polymer.IsAnimal (cellGraph P) C := by
      have := isAnimal_compOf (P := P) hl
      rwa [compOf_eq_of_isRootedFamily_singleton hCr hl hyl] at this
    obtain ⟨n, hn, hnc⟩ := exists_edist_le_card hA hl hzC
    have hnD : D < n := by
      by_contra hle
      push Not at hle
      exact hzB (mem_locDom.2 ⟨l, hyl, hn.trans (by exact_mod_cast hle)⟩)
    exact Finset.mem_biUnion.2 ⟨l, mem_rootCells.2 ⟨x, hyl, Set.mem_singleton x⟩,
      Finset.mem_filter.2 ⟨mem_animalsAt.2 ⟨hA, hl⟩, by omega⟩⟩
  have hq0 : 0 ≤ (Δ : ℝ) ^ 2 * Real.exp (-c) := by positivity
  have hinner : ∀ j, ∑ K ∈ (animalsAt P j).filter (fun K => D + 2 ≤ K.card),
      Real.exp (-c * K.card) ≤ whitenTail Δ c D := by
    intro j
    rw [Finset.sum_filter]
    have hw := sum_animalsAt_weight_le hΔ
      (fun n => if D + 2 ≤ n then Real.exp (-c * n) else 0)
      (fun n => by split_ifs <;> positivity) j
    refine hw.trans ?_
    set q := (Δ : ℝ) ^ 2 * Real.exp (-c) with hqdef
    have e0 : ∀ n : ℕ, (Δ : ℝ) ^ (2 * n) * Real.exp (-c * ((n : ℝ) + 1)) =
        Real.exp (-c) * q ^ n := by
      intro n
      rw [hqdef, mul_pow, ← pow_mul, ← Real.exp_nat_mul,
        show -c * ((n : ℝ) + 1) = (n : ℝ) * (-c) + (-c) by ring, Real.exp_add]
      ring
    have e : ∀ n : ℕ, (Δ : ℝ) ^ (2 * n) *
        (if D + 2 ≤ n + 1 then Real.exp (-c * ((n + 1 : ℕ) : ℝ)) else 0) =
          if D + 1 ≤ n then Real.exp (-c) * q ^ n else 0 := by
      intro n
      by_cases hn : D + 1 ≤ n
      · have hn' : D + 2 ≤ n + 1 := by omega
        simp only [hn, hn', ↓reduceIte]
        push_cast
        exact e0 n
      · have hn' : ¬ D + 2 ≤ n + 1 := by omega
        simp [hn, hn']
    have hIco : ∀ m : ℕ, (Finset.range m).filter (fun n => D + 1 ≤ n) = Finset.Ico (D + 1) m := by
      intro m
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    calc ∑ n ∈ Finset.range (Fintype.card ι), (Δ : ℝ) ^ (2 * n) *
          (if D + 2 ≤ n + 1 then Real.exp (-c * ((n + 1 : ℕ) : ℝ)) else 0)
        = ∑ n ∈ Finset.range (Fintype.card ι),
            (if D + 1 ≤ n then Real.exp (-c) * q ^ n else 0) :=
          Finset.sum_congr rfl fun n _ => e n
      _ = ∑ n ∈ Finset.Ico (D + 1) (Fintype.card ι), Real.exp (-c) * q ^ n := by
          rw [← Finset.sum_filter, hIco]
      _ = Real.exp (-c) * ∑ n ∈ Finset.Ico (D + 1) (Fintype.card ι), q ^ n :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ Real.exp (-c) * (q ^ (D + 1) / (1 - q)) :=
          mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq0 hq) (Real.exp_pos _).le
      _ = whitenTail Δ c D := by unfold whitenTail; rw [hqdef]; ring
  calc ∑ C ∈ F, Real.exp (-c * C.card)
      ≤ ∑ C ∈ (rootCells P {x}).biUnion
          (fun j => (animalsAt P j).filter (fun K => D + 2 ≤ K.card)),
          Real.exp (-c * C.card) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => (Real.exp_pos _).le
    _ ≤ ∑ j ∈ rootCells P {x}, ∑ K ∈ (animalsAt P j).filter (fun K => D + 2 ≤ K.card),
          Real.exp (-c * K.card) :=
        sum_biUnion_le_of_nonneg fun _ => (Real.exp_pos _).le
    _ ≤ ∑ _j ∈ rootCells P {x}, whitenTail Δ c D := Finset.sum_le_sum fun j _ => hinner j
    _ = (rootCells P {x}).card * whitenTail Δ c D := by rw [Finset.sum_const, nsmul_eq_mul]

end Dom

section Entry

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] {P : ι → Set Ω}
  {T : (ι → ℂ) → Ω → Ω → ℂ}

open Classical in
/-- **The entry error of a truncated cut family** (core): for a cut family with the decoupling
property on the polydisc of radius `e^κ`, `κ ≥ 1`, analytic entries, and a bound `b` of the entry
`(x, y)` on the polydisc, `‖T(1_B) x y - T(1) x y‖ ≤ b ∑_{C ⊄ B rooted at x} e^{-(κ-1)|C|}`. -/
theorem norm_cutTo_sub_le {κ : ℝ} (hκ : 1 ≤ κ) (hT : CutDecoupling P (Real.exp κ) T)
    (hTan : ∀ x y, AnalyticOnNhd ℂ (fun s => T s x y)
      (polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)))
    {x y : Ω} {b : ℝ}
    (hb : ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ‖T s x y‖ ≤ b) (B : Finset ι) :
    ‖T (cutTo B (fun _ => 1)) x y - T (fun _ => 1) x y‖ ≤
      b * ∑ C ∈ Finset.univ.filter (fun C : Finset ι => ¬ C ⊆ B ∧ IsRootedFamily P {x} C),
        Real.exp (-(κ - 1) * C.card) := by
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 (by linarith)
  have hR0 : 0 < Real.exp κ := Real.exp_pos κ
  have hfan := hTan x y
  have hid := sub_cutTo_eq_sum_coef hR hfan B
  have hzero : ∀ C, ¬ IsRootedFamily P {x} C → coef (fun s => T s x y) C = 0 := by
    intro C hC
    refine coef_eq_zero_of_not_rooted hR (fun s hs hsC => ?_) hC
    have hsplit := hT.split C (rootComp P {x} C) s hs hsC (rootComp_subset P {x} C)
      (disjoint_patchReg_rootComp P {x} C) x y
    have hB0 : T (cutTo (C \ rootComp P {x} C) s) x y = 0 := by
      by_contra hne
      exact Set.disjoint_left.1 (disjoint_root_patchReg_sdiff P {x} C) (Set.mem_singleton x)
        (hT.supp _ _ (cutTo_mem_polydisc hR0 _ hs) (cutTo_mem_supportedOn _ _) x y hne).1
    change T s x y = T (cutTo (rootComp P {x} C) s) x y
    rw [hsplit, hB0, add_zero]
  calc ‖T (cutTo B (fun _ => 1)) x y - T (fun _ => 1) x y‖
      = ‖∑ C ∈ Finset.univ.filter (fun C : Finset ι => ¬ C ⊆ B),
          coef (fun s => T s x y) C‖ := by
        rw [norm_sub_rev]; exact congrArg norm hid
    _ ≤ ∑ C ∈ Finset.univ.filter (fun C : Finset ι => ¬ C ⊆ B),
          ‖coef (fun s => T s x y) C‖ := norm_sum_le _ _
    _ ≤ ∑ C ∈ Finset.univ.filter (fun C : Finset ι => ¬ C ⊆ B ∧ IsRootedFamily P {x} C),
          b * Real.exp (-(κ - 1) * C.card) := by
        rw [Finset.sum_filter, Finset.sum_filter]
        refine Finset.sum_le_sum fun C _ => ?_
        by_cases h1 : C ⊆ B
        · simp [h1]
        · by_cases h2 : IsRootedFamily P {x} C
          · simp only [h1, h2, not_false_eq_true, and_self, ↓reduceIte]
            exact norm_coef_le_exp hκ hfan hb C
          · simp only [h1, h2, not_false_eq_true, and_false, ↓reduceIte, hzero C h2, norm_zero,
              le_refl]
    _ = b * ∑ C ∈ Finset.univ.filter (fun C : Finset ι => ¬ C ⊆ B ∧ IsRootedFamily P {x} C),
          Real.exp (-(κ - 1) * C.card) := (Finset.mul_sum _ _ _).symm

open Classical in
/-- **The entry error of the localized cut family** (core): with a degree bound `Δ` of the cell
graph and `Δ² e^{-(κ-1)} < 1`,
`‖T(1_{locDom P D x}) x y - T(1) x y‖ ≤ b · #roots(x) · whitenTail Δ (κ - 1) D`. -/
theorem norm_cutTo_locDom_sub_le {Δ : ℕ} (hΔ : ∀ v, (cellGraph P).degree v ≤ Δ) {κ : ℝ}
    (hκ : 1 ≤ κ) (hq : (Δ : ℝ) ^ 2 * Real.exp (-(κ - 1)) < 1)
    (hT : CutDecoupling P (Real.exp κ) T)
    (hTan : ∀ x y, AnalyticOnNhd ℂ (fun s => T s x y)
      (polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)))
    {x y : Ω} {b : ℝ}
    (hb : ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ‖T s x y‖ ≤ b) (D : ℕ) :
    ‖T (cutTo (locDom P D x) (fun _ => 1)) x y - T (fun _ => 1) x y‖ ≤
      b * ((rootCells P {x}).card * whitenTail Δ (κ - 1) D) := by
  have hR0 : 0 < Real.exp κ := Real.exp_pos κ
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 fun i => by simpa using hR0)
  exact (norm_cutTo_sub_le hκ hT hTan hb _).trans
    (mul_le_mul_of_nonneg_left (sum_rooted_not_subset_locDom_le hΔ hq D x) hb0)

end Entry

section RowCut

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] {P : ι → Set Ω}
  {T : (ι → ℂ) → Ω → Ω → ℂ}

omit [Fintype ι] in
theorem cutTo_mem_supportedOn_inter {C B : Finset ι} {s : ι → ℂ} (hsC : s ∈ supportedOn C) :
    cutTo B s ∈ supportedOn (C ∩ B) := by
  intro i hi
  by_cases hiB : i ∈ B
  · have hiC : i ∉ C := fun h => hi (Finset.mem_inter.2 ⟨h, hiB⟩)
    simp [cutTo, hiB, hsC i hiC]
  · simp [cutTo, hiB]

omit [Fintype ι] in
theorem cutTo_cutTo_comm (A B : Finset ι) (s : ι → ℂ) :
    cutTo (A ∩ B) (cutTo B s) = cutTo B (cutTo A s) := by
  funext i
  by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B <;> simp [cutTo, hiA, hiB]

omit [Fintype ι] in
theorem cutTo_sdiff_inter (C A B : Finset ι) (s : ι → ℂ) :
    cutTo ((C ∩ B) \ (A ∩ B)) (cutTo B s) = cutTo B (cutTo (C \ A) s) := by
  funext i
  by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B <;> by_cases hiC : i ∈ C <;>
    simp [cutTo, hiA, hiB, hiC]

omit [Fintype ι] in
/-- **The row cut of a decoupled family is decoupled** (core): restricting the parameters of row
`p` to a set `B p` of cells preserves the decoupling property. -/
theorem CutDecoupling.rowCut {R : ℝ} (hR : 0 < R) (hT : CutDecoupling P R T)
    (B : Ω → Finset ι) : CutDecoupling P R (fun s p q => T (cutTo (B p) s) p q) where
  supp C s hs hsC p q hne := by
    have h := hT.supp (C ∩ B p) (cutTo (B p) s) (cutTo_mem_polydisc hR _ hs)
      (cutTo_mem_supportedOn_inter hsC) p q hne
    exact ⟨patchReg_mono Finset.inter_subset_left h.1, patchReg_mono Finset.inter_subset_left h.2⟩
  split C A s hs hsC hAC hd p q := by
    have hA' : A ∩ B p ⊆ C ∩ B p := Finset.inter_subset_inter_right hAC
    have hd' : Disjoint (patchReg P (A ∩ B p)) (patchReg P ((C ∩ B p) \ (A ∩ B p))) := by
      refine Set.disjoint_of_subset (patchReg_mono Finset.inter_subset_left)
        (patchReg_mono fun i hi => ?_) hd
      obtain ⟨hiCB, hiAB⟩ := Finset.mem_sdiff.1 hi
      exact Finset.mem_sdiff.2 ⟨(Finset.mem_inter.1 hiCB).1,
        fun hiA => hiAB (Finset.mem_inter.2 ⟨hiA, (Finset.mem_inter.1 hiCB).2⟩)⟩
    have h := hT.split (C ∩ B p) (A ∩ B p) (cutTo (B p) s) (cutTo_mem_polydisc hR _ hs)
      (cutTo_mem_supportedOn_inter hsC) hA' hd' p q
    rw [cutTo_cutTo_comm, cutTo_sdiff_inter] at h
    exact h

omit [DecidableEq ι] in
theorem analyticOnNhd_rowCut [DecidableEq ι] {R : ℝ} (hR : 0 < R)
    (hTan : ∀ p q, AnalyticOnNhd ℂ (fun s => T s p q) (polydisc (0 : ι → ℂ) (fun _ => R)))
    (B : Ω → Finset ι) (p q : Ω) :
    AnalyticOnNhd ℂ (fun s => T (cutTo (B p) s) p q) (polydisc (0 : ι → ℂ) (fun _ => R)) :=
  fun s hs => (hTan p q _ (cutTo_mem_polydisc hR _ hs)).comp (analyticAt_cutTo (B p) s)

end RowCut

section Weighted

variable {d N₀ N : ℕ} [NeZero N₀]

/-- **Weighted row sums from an entry bound**: if `‖A p q‖ ≤ c e^{-r |p - q|}` and `r' < r`, then
`∑_q e^{r' |p - q|} ‖A p q‖ ≤ c N ballConst(r - r')`. -/
theorem sum_exp_mul_le_of_entry {A : Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ}
    {c r r' : ℝ} (hA : ∀ p q, ‖A p q‖ ≤ c * Real.exp (-r * dist p.1 q.1)) (hr' : r' < r)
    (p : L1Torus d N₀ × Fin N) :
    ∑ q, Real.exp (r' * dist p.1 q.1) * ‖A p q‖ ≤ c * (N * ballConst d (r - r')) := by
  have hc : 0 ≤ c := by
    have := (norm_nonneg _).trans (hA p p)
    simpa using this
  have e : ∀ t : ℝ, Real.exp (r' * t) * (c * Real.exp (-r * t)) =
      c * Real.exp (-(r - r') * t) := by
    intro t
    rw [mul_left_comm, ← Real.exp_add]
    congr 2; ring
  calc ∑ q, Real.exp (r' * dist p.1 q.1) * ‖A p q‖
      ≤ ∑ q : L1Torus d N₀ × Fin N, c * Real.exp (-(r - r') * dist p.1 q.1) :=
        Finset.sum_le_sum fun q _ => by
          rw [← e]
          exact mul_le_mul_of_nonneg_left (hA p q) (Real.exp_pos _).le
    _ = c * (N * ∑ y : L1Torus d N₀, Real.exp (-(r - r') * dist p.1 y)) := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
    _ ≤ c * (N * ballConst d (r - r')) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) hc
        exact ballSum_L1Torus d N₀ (by linarith) p.1

theorem transpose_entry_le {A : Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ}
    {c r : ℝ} (hA : ∀ p q, ‖A p q‖ ≤ c * Real.exp (-r * dist p.1 q.1)) (p q) :
    ‖Aᵀ p q‖ ≤ c * Real.exp (-r * dist p.1 q.1) := by
  rw [Matrix.transpose_apply, dist_comm]
  exact hA q p

theorem expWeight_sub (r' : ℝ) (hr' : 0 ≤ r') (p u q : L1Torus d N₀ × Fin N) :
    Real.exp (r' * dist p.1 q.1) ≤ Real.exp (r' * dist p.1 u.1) * Real.exp (r' * dist u.1 q.1) := by
  rw [← Real.exp_add, Real.exp_le_exp, ← mul_add]
  exact mul_le_mul_of_nonneg_left (dist_triangle _ _ _) hr'

end Weighted

section Whiten

variable {d L N₀ k M N : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

/-- **The localized square root of the final Hessian** (Amendment B-1′, P5 (2.39)): row `p` is
row `p` of the cut family `boxCut(s_p)` at the parameters `s_p = 1` on the cells of the
localization domain `locDom (spinBoxPatch) D p` of radius `D` and `0` elsewhere. -/
noncomputable def finalWhiten (d L N₀ k M : ℕ) [NeZero N₀] [NeZero L] {N : ℕ} (v a : ℝ)
    (h : Fin N → ℂ) (D : ℕ) : Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ :=
  Matrix.of fun p q =>
    boxCut d L N₀ k M v a h (cutTo (locDom (spinBoxPatch d N₀ M N) D p) (fun _ => 1)) p q

/-- **The Gaussian mismatch of the localized square root**: `Q = Lᵀ D L - 1`, `D` the final
Hessian. -/
noncomputable def finalWhitenMismatch (d L N₀ k M : ℕ) [NeZero N₀] [NeZero L] {N : ℕ} (v a : ℝ)
    (h : Fin N → ℂ) (D : ℕ) : Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ :=
  (finalWhiten d L N₀ k M v a h D)ᵀ * finalHessianC d L N₀ k v a h *
    finalWhiten d L N₀ k M v a h D - 1

/-- The real matrix of the localized square root (its entries are real for a real `h`,
`finalWhitenR_map`). -/
noncomputable def finalWhitenR (d L N₀ k M : ℕ) [NeZero N₀] [NeZero L] {N : ℕ} (v a : ℝ)
    (h : Fin N → ℂ) (D : ℕ) : Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℝ :=
  Matrix.of fun p q => (finalWhiten d L N₀ k M v a h D p q).re

/-- **The cut family of the localized square root**: row `p` of `boxCut(s|_{locDom p})`;
at `s = 1` it is `finalWhiten` (`whitenCut_one`). -/
noncomputable def whitenCut (d L N₀ k M : ℕ) [NeZero N₀] [NeZero L] {N : ℕ} (v a : ℝ)
    (h : Fin N → ℂ) (D : ℕ) (s : MacIdx d N₀ M → ℂ) :
    Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ :=
  Matrix.of fun p q =>
    boxCut d L N₀ k M v a h (cutTo (locDom (spinBoxPatch d N₀ M N) D p) s) p q

theorem whitenCut_one (h : Fin N → ℂ) (D : ℕ) :
    whitenCut d L N₀ k M v a h D (fun _ => 1) = finalWhiten d L N₀ k M v a h D := rfl

theorem finalWhiten_apply (h : Fin N → ℂ) (D : ℕ) (p q : L1Torus d N₀ × Fin N) :
    finalWhiten d L N₀ k M v a h D p q =
      boxCut d L N₀ k M v a h (cutTo (locDom (spinBoxPatch d N₀ M N) D p) (fun _ => 1)) p q :=
  rfl

omit [NeZero N₀] [NeZero L] in
theorem cutTo_one_mem_polydisc {κ : ℝ} (hκ : 0 < κ) (B : Finset (MacIdx d N₀ M)) :
    cutTo B (fun _ => 1) ∈ polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ) := by
  refine cutTo_mem_polydisc (Real.exp_pos κ) B fun _ => ?_
  simpa using Real.one_lt_exp_iff.2 hκ

omit [NeZero N₀] [NeZero L] in
theorem norm_cutTo_one_le {κ : ℝ} (hκ : 0 ≤ κ) (B : Finset (MacIdx d N₀ M)) (z : MacIdx d N₀ M) :
    ‖cutTo B (fun _ => (1 : ℂ)) z‖ ≤ Real.exp κ := by
  have := Real.one_le_exp_iff.2 hκ
  by_cases hz : z ∈ B <;> simp [cutTo, hz, this, (Real.exp_pos κ).le]

/-- **The entry bound of the cut family** on the polydisc of radius `e^κ`:
`‖boxCut(s)(p, q)‖ ≤ boxCutConst(N = 1) e^{-r |p - q|}` for `0 ≤ r ≤ ε/8`. -/
theorem norm_boxCut_apply_le (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {h : Fin N → ℂ} {p : ℝ} (hp : ∀ i j, ‖spinProj h i j‖ ≤ p)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ z, ‖s z‖ ≤ Real.exp κ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ pdEps d L / 8) (P Q : L1Torus d N₀ × Fin N) :
    ‖boxCut d L N₀ k M v a h s P Q‖ ≤ boxCutConst d L 1 a κ p * Real.exp (-r * dist P.1 Q.1) :=
  (norm_boxCutU_apply_le (cutOpHyp_finalOp hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ) hp hs hr0 hr
    P Q).trans (le_of_eq (by unfold boxCutConst; push_cast; ring))

/-- **Finite range of the localized square root**: `L(p, q) = 0` unless `q` lies in the region
of the localization domain of `p`. -/
theorem finalWhiten_eq_zero_of_not_mem (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 0 < κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    (h : Fin N → ℂ) (D : ℕ) {p q : L1Torus d N₀ × Fin N}
    (hq : q.1 ∉ macRegion d N₀ M (locDom (spinBoxPatch d N₀ M N) D p)) :
    finalWhiten d L N₀ k M v a h D p q = 0 := by
  by_contra hne
  have := ((cutDecoupling_boxCut (N₀ := N₀) (k := k) (L := L) (v := v) (a := a) (M := M) hd hk
    hv0 hv1 ha1 ha2 hmass hM hκ.le hMB hMκ h).supp (locDom (spinBoxPatch d N₀ M N) D p)
    (cutTo (locDom (spinBoxPatch d N₀ M N) D p) (fun _ => 1)) (cutTo_one_mem_polydisc hκ _)
    (cutTo_mem_supportedOn _ _) p q hne).2
  exact hq (mem_patchReg_spinBoxPatch.1 this)

/-- **Row sums of the localized square root**: `∑_q ‖L(p, q)‖ ≤ boxCutConst`. -/
theorem finalWhiten_row_bound (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {h : Fin N → ℂ} {p : ℝ} (hp : ∀ i j, ‖spinProj h i j‖ ≤ p) (D : ℕ)
    (P : L1Torus d N₀ × Fin N) :
    ∑ Q, ‖finalWhiten d L N₀ k M v a h D P Q‖ ≤ boxCutConst d L N a κ p :=
  boxCut_row_bound hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hp
    (norm_cutTo_one_le hκ (locDom (spinBoxPatch d N₀ M N) D P)) P

/-- **The cut family of the localized square root is decoupled** on the polydisc of radius
`e^κ` (`CutDecoupling.rowCut` of `cutDecoupling_boxCut`). -/
theorem cutDecoupling_whitenCut (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    (h : Fin N → ℂ) (D : ℕ) :
    CutDecoupling (spinBoxPatch d N₀ M N) (Real.exp κ)
      (fun s p q => whitenCut d L N₀ k M v a h D s p q) :=
  (cutDecoupling_boxCut hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ h).rowCut (Real.exp_pos κ)
    (fun p => locDom (spinBoxPatch d N₀ M N) D p)

theorem analyticOnNhd_whitenCut (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    (h : Fin N → ℂ) (D : ℕ) (p q : L1Torus d N₀ × Fin N) :
    AnalyticOnNhd ℂ (fun s => whitenCut d L N₀ k M v a h D s p q)
      (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) :=
  analyticOnNhd_rowCut (Real.exp_pos κ)
    (analyticOnNhd_boxCut hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ h)
    (fun p => locDom (spinBoxPatch d N₀ M N) D p) p q

/-- **Row sums of the cut family of the localized square root** on the polydisc of radius
`e^κ`: at most `boxCutConst`. -/
theorem whitenCut_row_bound (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {h : Fin N → ℂ} {p : ℝ} (hp : ∀ i j, ‖spinProj h i j‖ ≤ p) (D : ℕ)
    {s : MacIdx d N₀ M → ℂ} (hs : s ∈ polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ))
    (P : L1Torus d N₀ × Fin N) :
    ∑ Q, ‖whitenCut d L N₀ k M v a h D s P Q‖ ≤ boxCutConst d L N a κ p := by
  have hs' := cutTo_mem_polydisc (Real.exp_pos κ) (locDom (spinBoxPatch d N₀ M N) D P) hs
  exact boxCut_row_bound hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hp
    (fun z => by simpa using (hs' z).le) P

/-- The root cells of a site-spin index: at most `7^d` boxes contain a site. -/
theorem card_rootCells_spinBoxPatch_le (hM : 0 < M) (P : L1Torus d N₀ × Fin N) :
    (rootCells (spinBoxPatch d N₀ M N) {P}).card ≤ 7 ^ d := by
  classical
  refine (Finset.card_le_card fun z hz => ?_).trans (card_boxes_mem_le hM P.1)
  obtain ⟨u, hu, hu'⟩ := mem_rootCells.1 hz
  have hP : u = P := hu'
  rw [hP] at hu
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, mem_macBoxF.2 hu⟩

open Classical in
theorem cellGraph_spinBoxPatch_degree_le (hM : 0 < M) (z : MacIdx d N₀ M) :
    (cellGraph (spinBoxPatch d N₀ M N)).degree z ≤ 16 ^ d := by
  have := cellGraph_degree_le (N := N) hM z
  rwa [blockPatch_macBoxF] at this

omit [NeZero L] in
/-- The ratio of the count under `BoxCutTies`: `(16^d)² e^{-(κ-1)} ≤ 1/2`. -/
theorem ratio_le_of_ties {Mc : ℕ} {κ α : ℝ} (ht : BoxCutTies d L Mc κ α) :
    ((16 ^ d : ℕ) : ℝ) ^ 2 * Real.exp (-(κ - 1)) ≤ 1 / 2 := by
  obtain ⟨-, -, -, hα, hr⟩ := ht
  have h1 : 1 ≤ Real.exp (α * 16 ^ d) := Real.one_le_exp_iff.2 (mul_nonneg hα (by positivity))
  have h0 : 0 ≤ ((16 ^ d : ℕ) : ℝ) ^ 2 * Real.exp (-(κ - 1)) := by positivity
  nlinarith

omit [NeZero L] in
/-- **The tail is exponentially small in the radius** under `BoxCutTies`:
`whitenTail (16^d) (κ - 1) D ≤ 2^{-D}`. -/
theorem whitenTail_le_of_ties {Mc : ℕ} {κ α : ℝ} (ht : BoxCutTies d L Mc κ α) (D : ℕ) :
    whitenTail (16 ^ d) (κ - 1) D ≤ (1 / 2) ^ D := by
  have hq := ratio_le_of_ties ht
  have hκ : 1 ≤ κ := ht.1
  set q := ((16 ^ d : ℕ) : ℝ) ^ 2 * Real.exp (-(κ - 1)) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have he : Real.exp (-(κ - 1)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  unfold whitenTail
  rw [← hqdef]
  have h1q : 1 / 2 ≤ 1 - q := by linarith
  have hpow : q ^ (D + 1) ≤ (1 / 2) ^ (D + 1) := pow_le_pow_left₀ hq0 hq _
  rw [div_le_iff₀ (by linarith)]
  calc Real.exp (-(κ - 1)) * q ^ (D + 1) ≤ 1 * (1 / 2) ^ (D + 1) :=
        mul_le_mul he hpow (pow_nonneg hq0 _) zero_le_one
    _ = (1 / 2) ^ D * (1 / 2) := by rw [one_mul, pow_succ]
    _ ≤ (1 / 2) ^ D * (1 - q) := mul_le_mul_of_nonneg_left h1q (by positivity)

/-- **The row error of the localized square root, entrywise**: for `0 ≤ r ≤ ε/8`,
`‖L(p, q) - D^{-1/2}(p, q)‖ ≤ boxCutConst(N = 1) e^{-r |p - q|} · 7^d whitenTail (16^d) (κ - 1) D`
(`D^{-1/2} = boxCut(1)`, `boxCut_one`). -/
theorem norm_finalWhiten_sub_le {κ α : ℝ} (hC : BoxCutConsts d L k M v a κ α)
    {h : Fin N → ℂ} {p : ℝ} (hp : ∀ i j, ‖spinProj h i j‖ ≤ p) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ pdEps d L / 8) (D : ℕ) (P Q : L1Torus d N₀ × Fin N) :
    ‖finalWhiten d L N₀ k M v a h D P Q - boxCut d L N₀ k M v a h (fun _ => 1) P Q‖ ≤
      boxCutConst d L 1 a κ p * Real.exp (-r * dist P.1 Q.1) *
        (7 ^ d * whitenTail (16 ^ d) (κ - 1) D) := by
  obtain ⟨hd, hk, hv0, hv1, ha1, ha2, hmass, hM, ht⟩ := hC
  have hκ : 1 ≤ κ := ht.1
  have hκ0 : 0 ≤ κ := by linarith
  have hMB := ht.2.1
  have hMκ := ht.2.2.1
  have hq : ((16 ^ d : ℕ) : ℝ) ^ 2 * Real.exp (-(κ - 1)) < 1 := by
    linarith [ratio_le_of_ties ht]
  have hp0 : 0 ≤ p := (norm_nonneg _).trans (hp P.2 P.2)
  have hb : ∀ s ∈ polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ),
      ‖boxCut d L N₀ k M v a h s P Q‖ ≤ boxCutConst d L 1 a κ p * Real.exp (-r * dist P.1 Q.1) :=
    fun s hs => norm_boxCut_apply_le hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ hp
      (fun z => by simpa using (hs z).le) hr0 hr P Q
  have hmain := norm_cutTo_locDom_sub_le (Δ := 16 ^ d) (cellGraph_spinBoxPatch_degree_le hM) hκ hq
    (cutDecoupling_boxCut hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ h)
    (fun p q => analyticOnNhd_boxCut hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ h p q) hb D
  have hb0 : 0 ≤ boxCutConst d L 1 a κ p * Real.exp (-r * dist P.1 Q.1) :=
    mul_nonneg (boxCutConst_nonneg hd hp0) (Real.exp_pos _).le
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ hb0)
  refine mul_le_mul_of_nonneg_right ?_ (whitenTail_nonneg hq D)
  exact_mod_cast card_rootCells_spinBoxPatch_le hM P

/-- The weighted row constant of the row error:
`whitenErr = boxCutConst(N = 1) · 7^d whitenTail (16^d) (κ - 1) D · N ballConst(r - r')`. -/
noncomputable def whitenErr (d L N : ℕ) (a κ p r r' : ℝ) (D : ℕ) : ℝ :=
  boxCutConst d L 1 a κ p * (7 ^ d * whitenTail (16 ^ d) (κ - 1) D) * (N * ballConst d (r - r'))

/-- **Weighted row sums of the row error**: for `0 ≤ r' < r ≤ ε/8`,
`∑_q e^{r' |p - q|} ‖L(p, q) - D^{-1/2}(p, q)‖ ≤ whitenErr`. -/
theorem sum_finalWhiten_sub_row_le {κ α : ℝ} (hC : BoxCutConsts d L k M v a κ α)
    {h : Fin N → ℂ} {p : ℝ} (hp : ∀ i j, ‖spinProj h i j‖ ≤ p) {r r' : ℝ} (hr' : r' < r)
    (hr0 : 0 ≤ r) (hr : r ≤ pdEps d L / 8) (D : ℕ) (P : L1Torus d N₀ × Fin N) :
    ∑ Q, Real.exp (r' * dist P.1 Q.1) *
        ‖(finalWhiten d L N₀ k M v a h D - boxCut d L N₀ k M v a h (fun _ => 1)) P Q‖ ≤
      whitenErr d L N a κ p r r' D := by
  have hA : ∀ P Q, ‖(finalWhiten d L N₀ k M v a h D - boxCut d L N₀ k M v a h (fun _ => 1)) P Q‖ ≤
      (boxCutConst d L 1 a κ p * (7 ^ d * whitenTail (16 ^ d) (κ - 1) D)) *
        Real.exp (-r * dist P.1 Q.1) := fun P Q => by
    rw [Matrix.sub_apply]
    have := norm_finalWhiten_sub_le hC hp hr0 hr D P Q
    linarith
  exact sum_exp_mul_le_of_entry hA hr' P

/-- **Weighted column sums of the row error**: for `0 ≤ r' < r ≤ ε/8`,
`∑_q e^{r' |p - q|} ‖L(q, p) - D^{-1/2}(q, p)‖ ≤ whitenErr`. -/
theorem sum_finalWhiten_sub_col_le {κ α : ℝ} (hC : BoxCutConsts d L k M v a κ α)
    {h : Fin N → ℂ} {p : ℝ} (hp : ∀ i j, ‖spinProj h i j‖ ≤ p) {r r' : ℝ} (hr' : r' < r)
    (hr0 : 0 ≤ r) (hr : r ≤ pdEps d L / 8) (D : ℕ) (P : L1Torus d N₀ × Fin N) :
    ∑ Q, Real.exp (r' * dist P.1 Q.1) *
        ‖(finalWhiten d L N₀ k M v a h D - boxCut d L N₀ k M v a h (fun _ => 1))ᵀ P Q‖ ≤
      whitenErr d L N a κ p r r' D := by
  have hA : ∀ P Q, ‖(finalWhiten d L N₀ k M v a h D - boxCut d L N₀ k M v a h (fun _ => 1)) P Q‖ ≤
      (boxCutConst d L 1 a κ p * (7 ^ d * whitenTail (16 ^ d) (κ - 1) D)) *
        Real.exp (-r * dist P.1 Q.1) := fun P Q => by
    rw [Matrix.sub_apply]
    have := norm_finalWhiten_sub_le hC hp hr0 hr D P Q
    linarith
  exact sum_exp_mul_le_of_entry (transpose_entry_le hA) hr' P

/-- **The localized square root is real at a real `h`.** -/
theorem finalWhiten_real (h : Fin N → ℝ) (D : ℕ) (P Q : L1Torus d N₀ × Fin N) :
    conj (finalWhiten d L N₀ k M v a (fun i => (h i : ℂ)) D P Q) =
      finalWhiten d L N₀ k M v a (fun i => (h i : ℂ)) D P Q := by
  have e1 : (fun i => conj ((h i : ℝ) : ℂ)) = fun i => (h i : ℂ) :=
    funext fun i => Complex.conj_ofReal _
  have e2 : (fun z => conj (cutTo (locDom (spinBoxPatch d N₀ M N) D P) (fun _ => (1 : ℂ)) z)) =
      cutTo (locDom (spinBoxPatch d N₀ M N) D P) (fun _ => 1) := by
    funext z
    by_cases hz : z ∈ locDom (spinBoxPatch d N₀ M N) D P <;> simp [cutTo, hz]
  have hc := congrFun (congrFun (conjM_boxCut (d := d) (L := L) (N₀ := N₀) (k := k) (M := M)
    (v := v) (a := a) (fun i => (h i : ℂ))
    (cutTo (locDom (spinBoxPatch d N₀ M N) D P) (fun _ => 1))) P) Q
  rw [e1, e2] at hc
  exact hc

/-- **The real localized square root**: at a real `h`, `finalWhitenR` complexifies to
`finalWhiten`. -/
theorem finalWhitenR_map (h : Fin N → ℝ) (D : ℕ) :
    (finalWhitenR d L N₀ k M v a (fun i => (h i : ℂ)) D).map (algebraMap ℝ ℂ) =
      finalWhiten d L N₀ k M v a (fun i => (h i : ℂ)) D := by
  ext P Q
  simp only [Matrix.map_apply, finalWhitenR, Matrix.of_apply, Complex.coe_algebraMap]
  exact Complex.conj_eq_iff_re.1 (finalWhiten_real h D P Q)

end Whiten

section Mismatch

variable {d L N₀ k M N : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

/-- The entry constant of the final Hessian: `a p + C_U (1 + p)`. -/
noncomputable def hessEntryConst (d L : ℕ) (a p : ℝ) : ℝ := a * p + finalDecayC d L * (1 + p)

/-- **The entry bound of the final Hessian**:
`‖D(p, q)‖ ≤ hessEntryConst e^{-δ₀ |p - q|}`, `δ₀ = blockDecayRate d`. -/
theorem norm_finalHessianC_apply_le (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) {h : Fin N → ℂ} {p : ℝ}
    (hp : ∀ i j, ‖spinProj h i j‖ ≤ p) (P Q : L1Torus d N₀ × Fin N) :
    ‖finalHessianC d L N₀ k v a h P Q‖ ≤
      hessEntryConst d L a p * Real.exp (-blockDecayRate d * dist P.1 Q.1) := by
  obtain ⟨x, i⟩ := P
  obtain ⟨y, j⟩ := Q
  have hp0 : 0 ≤ p := (norm_nonneg _).trans (hp i i)
  have ha0 : 0 ≤ a := by linarith
  have hU := finalMass_entry_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 ha1 ha2 x y
  have hspin : ‖((if i = j then 1 else 0 : ℂ) - spinProj h i j)‖ ≤ 1 + p := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ (hp i j))
    by_cases hij : i = j <;> simp [hij]
  have happ : finalHessianC d L N₀ k v a h (x, i) (y, j) =
      (a : ℂ) * (if x = y then spinProj h i j else 0) +
        finalOp d L N₀ k v a x y * ((if i = j then 1 else 0) - spinProj h i j) := by
    unfold finalHessianC hessC
    rw [Matrix.add_apply, Matrix.smul_apply, one_sub_projHC_eq_idKron, liftOp_mul_idKron_apply,
      projHC_apply]
    simp only [smul_eq_mul, Matrix.sub_apply, Matrix.one_apply]
    rfl
  have h2 : ‖finalOp d L N₀ k v a x y * ((if i = j then 1 else 0 : ℂ) - spinProj h i j)‖ ≤
      finalDecayC d L * Real.exp (-blockDecayRate d * dist x y) * (1 + p) := by
    rw [norm_mul]
    exact mul_le_mul hU hspin (norm_nonneg _) ((norm_nonneg _).trans hU)
  rw [happ]
  unfold hessEntryConst
  refine (norm_add_le _ _).trans ?_
  by_cases hxy : x = y
  · subst hxy
    simp only [dist_self, mul_zero, Real.exp_zero, mul_one, ↓reduceIte] at h2 ⊢
    have h1 : ‖(a : ℂ) * spinProj h i j‖ ≤ a * p := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha0]
      exact mul_le_mul_of_nonneg_left (hp i j) ha0
    linarith
  · simp only [hxy, ↓reduceIte, mul_zero, norm_zero, zero_add]
    have : 0 ≤ a * p * Real.exp (-blockDecayRate d * dist x y) := by positivity
    nlinarith

/-- The bound of the mismatch: `whitenErr · g_D (2 g_G + whitenErr)`, with
`g_G = boxCutConst(N = 1) N ballConst(r - r')` and `g_D = hessEntryConst N ballConst(δ₀ - r')`
the weighted row constants of `D^{-1/2}` and `D`. -/
noncomputable def whitenMismatchBound (d L N : ℕ) (a κ p r r' : ℝ) (D : ℕ) : ℝ :=
  whitenErr d L N a κ p r r' D *
    (hessEntryConst d L a p * (N * ballConst d (blockDecayRate d - r')) *
      (2 * (boxCutConst d L 1 a κ p * (N * ballConst d (r - r'))) + whitenErr d L N a κ p r r' D))

/-- **Evenness**: the quadratic form of the mismatch is even. -/
theorem finalWhitenMismatch_quad_neg (h : Fin N → ℂ) (D : ℕ) (w : L1Torus d N₀ × Fin N → ℂ) :
    (-w) ⬝ᵥ (finalWhitenMismatch d L N₀ k M v a h D *ᵥ (-w)) =
      w ⬝ᵥ (finalWhitenMismatch d L N₀ k M v a h D *ᵥ w) := by
  rw [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

/-- **The determinant identity**: `det(L)² det(D) = det(1 + Q)`. -/
theorem det_finalWhiten_sq (h : Fin N → ℂ) (D : ℕ) :
    (finalWhiten d L N₀ k M v a h D).det ^ 2 * (finalHessianC d L N₀ k v a h).det =
      (1 + finalWhitenMismatch d L N₀ k M v a h D).det := by
  unfold finalWhitenMismatch
  rw [add_sub_cancel, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

variable [NeZero N]

/-- **`D^{-1/2} D D^{-1/2} = 1`** for a real unit `h` (`D^{-1/2} = boxCut(1)`, the K-link). -/
theorem boxCut_one_transpose_mul_mul (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 < v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) :
    (boxCut d L N₀ k M v a (fun i => (h i : ℂ)) (fun _ => 1))ᵀ *
        finalHessianC d L N₀ k v a (fun i => (h i : ℂ)) *
        boxCut d L N₀ k M v a (fun i => (h i : ℂ)) (fun _ => 1) = 1 := by
  have hN : 0 < L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) k
  have hpd := finalHessian_posDef (N := N) (ℓ := N₀ * L ^ k) (Nb := L ^ k) (m := N₀)
    (mul_comm N₀ (L ^ k)) hN hd hv0 hv1 ha1 hh
  have hG := pdSqrtInv_finalHessian_map (N₀ := N₀) (M := M) rfl hd hk hv0 hv1 ha1 ha2 hmass hM hκ
    hMB hMκ hh
  have hD := finalHessianC_ofReal (L := L) (N₀ := N₀) (k := k) (v := v) (a := a) hd hv0.le
    (by linarith) hh
  have key : ((pdSqrtInv (finalHessian d (N₀ * L ^ k) (L ^ k) N₀ v a h)).map (algebraMap ℝ ℂ))ᵀ *
      (finalHessian d (N₀ * L ^ k) (L ^ k) N₀ v a h).map (algebraMap ℝ ℂ) *
      (pdSqrtInv (finalHessian d (N₀ * L ^ k) (L ^ k) N₀ v a h)).map (algebraMap ℝ ℂ) = 1 := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, pdSqrtInv_transpose,
      pdSqrtInv_mul_mul hpd]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [hG, ← hD] at key
  exact key

/-- **The mismatch in terms of the row error**: for a real unit `h`, with `G = D^{-1/2}` and
`E = L - G`, `Q = Gᵀ D E + Eᵀ D G + Eᵀ D E`. -/
theorem finalWhitenMismatch_eq (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 < v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) (D : ℕ) :
    finalWhitenMismatch d L N₀ k M v a (fun i => (h i : ℂ)) D =
      (boxCut d L N₀ k M v a (fun i => (h i : ℂ)) (fun _ => 1))ᵀ *
          finalHessianC d L N₀ k v a (fun i => (h i : ℂ)) *
          (finalWhiten d L N₀ k M v a (fun i => (h i : ℂ)) D -
            boxCut d L N₀ k M v a (fun i => (h i : ℂ)) (fun _ => 1)) +
        (finalWhiten d L N₀ k M v a (fun i => (h i : ℂ)) D -
            boxCut d L N₀ k M v a (fun i => (h i : ℂ)) (fun _ => 1))ᵀ *
          finalHessianC d L N₀ k v a (fun i => (h i : ℂ)) *
          boxCut d L N₀ k M v a (fun i => (h i : ℂ)) (fun _ => 1) +
        (finalWhiten d L N₀ k M v a (fun i => (h i : ℂ)) D -
            boxCut d L N₀ k M v a (fun i => (h i : ℂ)) (fun _ => 1))ᵀ *
          finalHessianC d L N₀ k v a (fun i => (h i : ℂ)) *
          (finalWhiten d L N₀ k M v a (fun i => (h i : ℂ)) D -
            boxCut d L N₀ k M v a (fun i => (h i : ℂ)) (fun _ => 1)) := by
  have hGDG := boxCut_one_transpose_mul_mul (N₀ := N₀) (L := L) (k := k) (M := M) (v := v) (a := a)
    hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hh
  unfold finalWhitenMismatch
  set G := boxCut d L N₀ k M v a (fun i => (h i : ℂ)) (fun _ => 1)
  set W := finalWhiten d L N₀ k M v a (fun i => (h i : ℂ)) D
  set Dm := finalHessianC d L N₀ k v a (fun i => (h i : ℂ))
  rw [← hGDG, Matrix.transpose_sub]
  noncomm_ring

omit [NeZero N] in
/-- **The mismatch is symmetric** (`Qᵀ = Q`) for a real unit `h`. -/
theorem finalWhitenMismatch_transpose (hd : 0 < d) {v : ℝ} (hv0 : 0 ≤ v) (ha1 : 1 / 2 ≤ a)
    {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) (D : ℕ) :
    (finalWhitenMismatch d L N₀ k M v a (fun i => (h i : ℂ)) D)ᵀ =
      finalWhitenMismatch d L N₀ k M v a (fun i => (h i : ℂ)) D := by
  have hN : 0 < L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) k
  have hDt : (finalHessianC d L N₀ k v a (fun i => (h i : ℂ)))ᵀ =
      finalHessianC d L N₀ k v a (fun i => (h i : ℂ)) := by
    have key : ((finalHessian d (N₀ * L ^ k) (L ^ k) N₀ v a h).map (algebraMap ℝ ℂ))ᵀ =
        (finalHessian d (N₀ * L ^ k) (L ^ k) N₀ v a h).map (algebraMap ℝ ℂ) := by
      rw [← Matrix.transpose_map,
        finalHessian_transpose (mul_comm N₀ (L ^ k)) hN hd hv0 (by linarith) hh]
    rw [finalHessianC_ofReal (L := L) (N₀ := N₀) (k := k) (v := v) (a := a) hd hv0
      (by linarith) hh]
    exact key
  unfold finalWhitenMismatch
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, hDt, Matrix.mul_assoc]

/-- **Smallness of the mismatch**: for a real unit `h`, `p` a bound of the entries of the spin
projection and `0 ≤ r' < r ≤ ε/8`, the weighted row sums of `Q` are at most
`whitenMismatchBound`, which is `O(whitenTail (16^d) (κ - 1) D)`. -/
theorem sum_finalWhitenMismatch_le {κ α : ℝ} (hC : BoxCutConsts d L k M v a κ α) (hv : 0 < v)
    {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) {p : ℝ}
    (hp : ∀ i j, ‖spinProj (fun i => (h i : ℂ)) i j‖ ≤ p) {r r' : ℝ} (hr'0 : 0 ≤ r')
    (hr' : r' < r) (hr : r ≤ pdEps d L / 8) (D : ℕ) (P : L1Torus d N₀ × Fin N) :
    ∑ Q, Real.exp (r' * dist P.1 Q.1) *
        ‖finalWhitenMismatch d L N₀ k M v a (fun i => (h i : ℂ)) D P Q‖ ≤
      whitenMismatchBound d L N a κ p r r' D := by
  have hd := hC.hd
  have hk := hC.hk
  have hv0 := hC.hv0
  have hv1 := hC.hv1
  have ha1 := hC.ha1
  have ha2 := hC.ha2
  have hmass := hC.hmass
  have hM := hC.hM
  have ht := hC.ties
  have hκ : 1 ≤ κ := ht.1
  have hκ0 : 0 ≤ κ := by linarith
  have hMB := ht.2.1
  have hMκ := ht.2.2.1
  have hr0 : 0 ≤ r := by linarith
  have hεδ : pdEps d L ≤ blockDecayRate d := min_le_left _ _
  have hε0 : 0 < pdEps d L := pdEps_pos hd
  have hrδ : r' < blockDecayRate d := by linarith
  rw [finalWhitenMismatch_eq hd hk hv hv1 ha1 ha2 hmass hM hκ0 hMB hMκ hh D]
  set G := boxCut d L N₀ k M v a (fun i => (h i : ℂ)) (fun _ => 1)
  set E := finalWhiten d L N₀ k M v a (fun i => (h i : ℂ)) D - G
  set Dm := finalHessianC d L N₀ k v a (fun i => (h i : ℂ))
  set w : L1Torus d N₀ × Fin N → L1Torus d N₀ × Fin N → ℝ :=
    fun P Q => Real.exp (r' * dist P.1 Q.1)
  have hw0 : ∀ P Q, 0 ≤ w P Q := fun _ _ => (Real.exp_pos _).le
  have hsub : ∀ P U Q, w P Q ≤ w P U * w U Q := fun P U Q => expWeight_sub r' hr'0 P U Q
  set gG := boxCutConst d L 1 a κ p * (N * ballConst d (r - r')) with hgG
  set gD := hessEntryConst d L a p * (N * ballConst d (blockDecayRate d - r')) with hgD
  set eE := whitenErr d L N a κ p r r' D with heE
  have hG1 : ∀ z : MacIdx d N₀ M, ‖(fun _ => (1 : ℂ)) z‖ ≤ Real.exp κ := fun _ => by
    simpa using Real.one_le_exp_iff.2 hκ0
  have hGe : ∀ P Q, ‖G P Q‖ ≤ boxCutConst d L 1 a κ p * Real.exp (-r * dist P.1 Q.1) :=
    fun P Q => norm_boxCut_apply_le hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ hp hG1 hr0 hr P Q
  have hDe : ∀ P Q, ‖Dm P Q‖ ≤
      hessEntryConst d L a p * Real.exp (-blockDecayRate d * dist P.1 Q.1) :=
    fun P Q => norm_finalHessianC_apply_le hd hk hv0 ha1 ha2 hp P Q
  have hGT : ∀ P, ∑ Q, w P Q * ‖Gᵀ P Q‖ ≤ gG := fun P =>
    sum_exp_mul_le_of_entry (transpose_entry_le hGe) hr' P
  have hGr : ∀ P, ∑ Q, w P Q * ‖G P Q‖ ≤ gG := fun P => sum_exp_mul_le_of_entry hGe hr' P
  have hDr : ∀ P, ∑ Q, w P Q * ‖Dm P Q‖ ≤ gD := fun P => sum_exp_mul_le_of_entry hDe hrδ P
  have hEr : ∀ P, ∑ Q, w P Q * ‖E P Q‖ ≤ eE := fun P =>
    sum_finalWhiten_sub_row_le hC hp hr' hr0 hr D P
  have hET : ∀ P, ∑ Q, w P Q * ‖Eᵀ P Q‖ ≤ eE := fun P =>
    sum_finalWhiten_sub_col_le hC hp hr' hr0 hr D P
  have hgG0 : 0 ≤ gG := (Finset.sum_nonneg fun Q _ => mul_nonneg (hw0 P Q) (norm_nonneg _)).trans
    (hGr P)
  have hgD0 : 0 ≤ gD := (Finset.sum_nonneg fun Q _ => mul_nonneg (hw0 P Q) (norm_nonneg _)).trans
    (hDr P)
  have heE0 : 0 ≤ eE := (Finset.sum_nonneg fun Q _ => mul_nonneg (hw0 P Q) (norm_nonneg _)).trans
    (hEr P)
  have hGD : ∀ P, ∑ Q, w P Q * ‖(Gᵀ * Dm) P Q‖ ≤ gG * gD :=
    weightedRow_mul_le w hw0 hsub _ _ hgD0 hGT hDr
  have hED : ∀ P, ∑ Q, w P Q * ‖(Eᵀ * Dm) P Q‖ ≤ eE * gD :=
    weightedRow_mul_le w hw0 hsub _ _ hgD0 hET hDr
  have h1 := weightedRow_mul_le w hw0 hsub (Gᵀ * Dm) E heE0 hGD hEr P
  have h2 := weightedRow_mul_le w hw0 hsub (Eᵀ * Dm) G hgG0 hED hGr P
  have h3 := weightedRow_mul_le w hw0 hsub (Eᵀ * Dm) E heE0 hED hEr P
  calc ∑ Q, w P Q * ‖(Gᵀ * Dm * E + Eᵀ * Dm * G + Eᵀ * Dm * E) P Q‖
      ≤ ∑ Q, (w P Q * ‖(Gᵀ * Dm * E) P Q‖ + w P Q * ‖(Eᵀ * Dm * G) P Q‖ +
          w P Q * ‖(Eᵀ * Dm * E) P Q‖) := by
        refine Finset.sum_le_sum fun Q _ => ?_
        rw [Matrix.add_apply, Matrix.add_apply, ← mul_add, ← mul_add]
        refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (hw0 P Q)
        exact add_le_add (norm_add_le _ _) le_rfl
    _ = ∑ Q, w P Q * ‖(Gᵀ * Dm * E) P Q‖ + ∑ Q, w P Q * ‖(Eᵀ * Dm * G) P Q‖ +
          ∑ Q, w P Q * ‖(Eᵀ * Dm * E) P Q‖ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ gG * gD * eE + eE * gD * gG + eE * gD * eE := add_le_add (add_le_add h1 h2) h3
    _ = whitenMismatchBound d L N a κ p r r' D := by
        simp only [whitenMismatchBound, ← hgG, ← hgD, ← heE]
        ring

omit [NeZero N] in
/-- The entries of the spin projection of a real unit vector are at most `1`. -/
theorem norm_spinProj_ofReal_le_one {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) (i j : Fin N) :
    ‖spinProj (fun i => (h i : ℂ)) i j‖ ≤ 1 := by
  have hs : ∑ l, ((h l : ℝ) : ℂ) ^ 2 = 1 := by exact_mod_cast hh
  refine (spinProj_norm_le (by rw [hs]; exact one_ne_zero) i j).trans (le_of_eq ?_)
  rw [hs, norm_one, div_one]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact hh

/-- The constant of the row error: `whitenErr ≤ whitenErrConst · 2^{-D}` under `BoxCutTies`. -/
noncomputable def whitenErrConst (d L N : ℕ) (a κ p r r' : ℝ) : ℝ :=
  boxCutConst d L 1 a κ p * 7 ^ d * (N * ballConst d (r - r'))

/-- The constant of the mismatch: `whitenMismatchBound ≤ whitenQConst · 2^{-D}` under
`BoxCutTies`. -/
noncomputable def whitenQConst (d L N : ℕ) (a κ p r r' : ℝ) : ℝ :=
  whitenErrConst d L N a κ p r r' *
    (hessEntryConst d L a p * (N * ballConst d (blockDecayRate d - r')) *
      (2 * (boxCutConst d L 1 a κ p * (N * ballConst d (r - r'))) + whitenErrConst d L N a κ p r r'))

omit [NeZero N] in
/-- **The row error is exponentially small in the radius**:
`whitenErr ≤ whitenErrConst · 2^{-D}` under `BoxCutTies`. -/
theorem whitenErr_le_of_ties {Mc : ℕ} {κ α : ℝ} (ht : BoxCutTies d L Mc κ α) (hd : 0 < d)
    {p r r' : ℝ} (hp0 : 0 ≤ p) (hr' : r' < r) (D : ℕ) :
    whitenErr d L N a κ p r r' D ≤ whitenErrConst d L N a κ p r r' * (1 / 2) ^ D := by
  have h0 : 0 ≤ whitenErrConst d L N a κ p r r' := by
    unfold whitenErrConst
    have := boxCutConst_nonneg (L := L) (N := 1) (a := a) hd (κ := κ) hp0
    have := ballConst_decay_nonneg (d := d) (sub_pos.2 hr')
    positivity
  calc whitenErr d L N a κ p r r' D
      = whitenErrConst d L N a κ p r r' * whitenTail (16 ^ d) (κ - 1) D := by
        unfold whitenErr whitenErrConst; ring
    _ ≤ whitenErrConst d L N a κ p r r' * (1 / 2) ^ D :=
        mul_le_mul_of_nonneg_left (whitenTail_le_of_ties ht D) h0

omit [NeZero N] in
/-- **The mismatch is exponentially small in the radius**:
`whitenMismatchBound ≤ whitenQConst · 2^{-D}` under `BoxCutTies`. -/
theorem whitenMismatchBound_le_of_ties {Mc : ℕ} {κ α : ℝ} (ht : BoxCutTies d L Mc κ α)
    (hd : 0 < d) (ha : 0 ≤ a) {p r r' : ℝ} (hp0 : 0 ≤ p) (hr' : r' < r)
    (hrδ : r' < blockDecayRate d) (D : ℕ) :
    whitenMismatchBound d L N a κ p r r' D ≤ whitenQConst d L N a κ p r r' * (1 / 2) ^ D := by
  have hq : ((16 ^ d : ℕ) : ℝ) ^ 2 * Real.exp (-(κ - 1)) < 1 := by
    linarith [ratio_le_of_ties ht]
  have hB := boxCutConst_nonneg (L := L) (N := 1) (a := a) hd (κ := κ) hp0
  have hb1 := ballConst_decay_nonneg (d := d) (sub_pos.2 hr')
  have hb2 := ballConst_decay_nonneg (d := d) (sub_pos.2 hrδ)
  have hU := (finalDecayC_pos (L := L) hd).le
  have hE0 : 0 ≤ whitenErr d L N a κ p r r' D := by
    unfold whitenErr
    have := whitenTail_nonneg hq D
    positivity
  have hE := whitenErr_le_of_ties (N := N) (a := a) ht hd hp0 hr' D
  have hh : (1 / 2 : ℝ) ^ D ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hc0 : 0 ≤ whitenErrConst d L N a κ p r r' := by
    unfold whitenErrConst; positivity
  have hE' : whitenErr d L N a κ p r r' D ≤ whitenErrConst d L N a κ p r r' :=
    hE.trans (mul_le_of_le_one_right hc0 hh)
  have hgD : 0 ≤ hessEntryConst d L a p * (N * ballConst d (blockDecayRate d - r')) := by
    unfold hessEntryConst; positivity
  have hgG : 0 ≤ boxCutConst d L 1 a κ p * (N * ballConst d (r - r')) := by positivity
  unfold whitenMismatchBound whitenQConst
  calc whitenErr d L N a κ p r r' D *
        (hessEntryConst d L a p * (N * ballConst d (blockDecayRate d - r')) *
          (2 * (boxCutConst d L 1 a κ p * (N * ballConst d (r - r'))) +
            whitenErr d L N a κ p r r' D))
      ≤ (whitenErrConst d L N a κ p r r' * (1 / 2) ^ D) *
        (hessEntryConst d L a p * (N * ballConst d (blockDecayRate d - r')) *
          (2 * (boxCutConst d L 1 a κ p * (N * ballConst d (r - r'))) +
            whitenErrConst d L N a κ p r r')) := by
        refine mul_le_mul hE (mul_le_mul_of_nonneg_left (by linarith) hgD)
          (mul_nonneg hgD (by linarith)) (mul_nonneg hc0 (by positivity))
    _ = _ := by ring

omit [NeZero N] in
/-- **The choice of the radius**: for every `ε > 0` there is `D₀` with
`whitenMismatchBound ≤ ε` for all `D ≥ D₀` (under `BoxCutTies`). -/
theorem exists_whitenRadius {Mc : ℕ} {κ α : ℝ} (ht : BoxCutTies d L Mc κ α) (hd : 0 < d)
    (ha : 0 ≤ a) {p r r' : ℝ} (hp0 : 0 ≤ p) (hr' : r' < r) (hrδ : r' < blockDecayRate d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D₀ : ℕ, ∀ D, D₀ ≤ D → whitenMismatchBound d L N a κ p r r' D ≤ ε := by
  set C := whitenQConst d L N a κ p r r'
  have hC0 : 0 ≤ C := by
    have h := (whitenMismatchBound_le_of_ties (N := N) ht hd ha hp0 hr' hrδ 0)
    have hB := boxCutConst_nonneg (L := L) (N := 1) (a := a) hd (κ := κ) hp0
    have hb1 := ballConst_decay_nonneg (d := d) (sub_pos.2 hr')
    have hb2 := ballConst_decay_nonneg (d := d) (sub_pos.2 hrδ)
    have hU := (finalDecayC_pos (L := L) hd).le
    simp only [C, whitenQConst, whitenErrConst, hessEntryConst]
    positivity
  obtain ⟨D₀, hD₀⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith : (0 : ℝ) < C + 1))
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨D₀, fun D hD => (whitenMismatchBound_le_of_ties ht hd ha hp0 hr' hrδ D).trans ?_⟩
  have hmono : (1 / 2 : ℝ) ^ D ≤ (1 / 2) ^ D₀ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hD
  have h1 : C * (1 / 2) ^ D ≤ C * (ε / (C + 1)) :=
    mul_le_mul_of_nonneg_left (hmono.trans hD₀.le) hC0
  have h2 : C * (ε / (C + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  exact h1.trans h2

/-- **Invertibility of the localized square root** (conditional form): for a real unit `h`, if
`whitenMismatchBound < 1` (at some `0 ≤ r' < r ≤ ε/8`), then `L` is invertible. -/
theorem isUnit_finalWhiten_of_lt_one {κ α : ℝ} (hC : BoxCutConsts d L k M v a κ α) (hv : 0 < v)
    {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) {p : ℝ}
    (hp : ∀ i j, ‖spinProj (fun i => (h i : ℂ)) i j‖ ≤ p) {r r' : ℝ} (hr'0 : 0 ≤ r')
    (hr' : r' < r) (hr : r ≤ pdEps d L / 8) (D : ℕ)
    (hsmall : whitenMismatchBound d L N a κ p r r' D < 1) :
    IsUnit (finalWhiten d L N₀ k M v a (fun i => (h i : ℂ)) D) := by
  have hrow : ∀ P, ∑ P', (fun _ => (1 : ℝ)) P *
      ‖(-finalWhitenMismatch d L N₀ k M v a (fun i => (h i : ℂ)) D) P P'‖ /
        (fun _ => (1 : ℝ)) P' ≤ whitenMismatchBound d L N a κ p r r' D := by
    intro P
    refine le_trans (Finset.sum_le_sum fun P' _ => ?_)
      (sum_finalWhitenMismatch_le hC hv hh hp hr'0 hr' hr D P)
    simp only [one_mul, div_one, Matrix.neg_apply, norm_neg]
    exact le_mul_of_one_le_left (norm_nonneg _)
      (Real.one_le_exp_iff.2 (mul_nonneg hr'0 dist_nonneg))
  have hu : IsUnit (1 - -finalWhitenMismatch d L N₀ k M v a (fun i => (h i : ℂ)) D) :=
    isUnit_one_sub_of_weighted_row_sum (fun _ => one_pos) hsmall hrow
  rw [sub_neg_eq_add] at hu
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hu
  rw [← det_finalWhiten_sq] at hdet
  refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
  have h1 := isUnit_of_mul_isUnit_left hdet
  rw [pow_two] at h1
  exact isUnit_of_mul_isUnit_left h1

/-- **Invertibility of the localized square root**: for a real unit `h` and `0 ≤ r' < r ≤ ε/8`,
`L` is invertible for every radius `D` beyond some `D₀`. -/
theorem exists_isUnit_finalWhiten {κ α : ℝ} (hC : BoxCutConsts d L k M v a κ α) (hv : 0 < v)
    {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) {r r' : ℝ} (hr'0 : 0 ≤ r') (hr' : r' < r)
    (hr : r ≤ pdEps d L / 8) :
    ∃ D₀ : ℕ, ∀ D, D₀ ≤ D → IsUnit (finalWhiten d L N₀ k M v a (fun i => (h i : ℂ)) D) := by
  have hd := hC.hd
  have hεδ : pdEps d L ≤ blockDecayRate d := min_le_left _ _
  have hrδ : r' < blockDecayRate d := by linarith
  obtain ⟨D₀, hD₀⟩ := exists_whitenRadius (N := N) (a := a) hC.ties hd (by linarith [hC.ha1])
    zero_le_one hr' hrδ (by norm_num : (0 : ℝ) < 1 / 2)
  exact ⟨D₀, fun D hD => isUnit_finalWhiten_of_lt_one hC hv hh (norm_spinProj_ofReal_le_one hh)
    hr'0 hr' hr D (by linarith [hD₀ D hD])⟩

end Mismatch

end Balaban.Green
