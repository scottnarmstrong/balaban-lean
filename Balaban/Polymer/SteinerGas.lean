/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MayerPE
public import Balaban.Polymer.Hole
public import Balaban.Fluctuation.ClusterUnion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The gas of local terms on a connected graph with the Steiner size

`B` is a finite set of sites with a connected graph `H` of degree at most `Δ`. The Steiner size of a
set of sites (`stSizeG`) is the least number of sites of a connected set containing it. With it the
hypotheses (G1)–(G3) of `mayerGen_pe` hold with `c = cP = 0`, `c1 = 1`, `K0 = K0P = 4 e^{-κ0}`:

* (G1) `card_le_stSizeG`;
* (G2) `card_setsG_le`, `sum_exp_stSizeG_le` (the animal count `card_animals_le`, for
  `Δ² · 2 · e^{-κ0} ≤ 1/2`);
* (G3) `stSizeG_union_le`, `stSizeG_unionCs_le` (families) and `stSizeG_union_cluster` (clusters).

`steinerGen_gas` is the resulting gas theorem for general weights `f X` on the nonempty site sets,
`steinerGen_kp` its Kotecký–Preiss data, and `steiner_gas` the case `f X = e^{H X} - 1` of local
terms bounded by `H0 e^{-(κ0+κ1)|X|_St}`. The block torus with its nearest-neighbour graph
(`LargeField/Base/KF0AllGoodGas.lean`: `blockGen_gas`, `blockGen_kp`, `block_gas`) is the instance
`Δ = 2d`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory

namespace Balaban.Polymer

section Geometry

variable {B : Type*} [Fintype B] {H : SimpleGraph B}

variable (H) in
/-- The Steiner size of a set of sites: the least number of sites of an `H`-connected set
containing it. -/
def stSizeG (Y : Finset B) : ℝ := (steiner H Y : ℝ)

omit [Fintype B] in
theorem stSizeG_nonneg (Y : Finset B) : 0 ≤ stSizeG H Y := Nat.cast_nonneg _

theorem isAnimal_univ_of_connected (hconn : H.Connected) :
    IsAnimal H (Finset.univ : Finset B) := by
  have := hconn.nonempty
  refine ⟨Finset.univ_nonempty, ?_⟩
  rw [Finset.coe_univ]
  exact (SimpleGraph.induceUnivIso _).connected_iff.2 hconn

theorem exists_animal_supset_of_connected (hconn : H.Connected) (Y : Finset B) :
    ∃ W : Finset B, IsAnimal H W ∧ Y ⊆ W :=
  ⟨Finset.univ, isAnimal_univ_of_connected hconn, Finset.subset_univ _⟩

/-- (G1) with `c1 = 1`. -/
theorem card_le_stSizeG (hconn : H.Connected) (Y : Finset B) :
    (Y.card : ℝ) ≤ 1 * (1 + stSizeG H Y) := by
  have := card_le_steiner (exists_animal_supset_of_connected hconn Y)
  unfold stSizeG
  have h : (Y.card : ℝ) ≤ (steiner H Y : ℝ) := by exact_mod_cast this
  linarith

omit [Fintype B] in
/-- The Steiner size of a connected set is its number of sites. -/
theorem stSizeG_eq_card {Y : Finset B} (hY : IsAnimal H Y) : stSizeG H Y = Y.card := by
  unfold stSizeG
  have h1 := steiner_le hY (Finset.Subset.refl Y)
  have h2 := card_le_steiner ⟨Y, hY, Finset.Subset.refl Y⟩
  exact_mod_cast le_antisymm h1 h2

theorem stSizeG_union_le [DecidableEq B] (hconn : H.Connected) {X Y : Finset B}
    (_hX : X.Nonempty) (_hY : Y.Nonempty) (h : ¬ Disjoint X Y) :
    stSizeG H (X ∪ Y) ≤ stSizeG H X + stSizeG H Y + 0 := by
  have key := steiner_union_le (H := H) (n := 1) ![X, Y]
    (fun i => exists_animal_supset_of_connected hconn _) ⊤ (by
      refine ⟨fun i j => ?_⟩
      by_cases hij : i = j
      · rw [hij]
      · exact SimpleGraph.Adj.reachable (by simpa using hij))
    (fun i j hij => by
      have hne : i ≠ j := by simpa using hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hne
      · exact h
      · exact fun hd => h hd.symm
      · exact absurd rfl hne)
  have key' : steiner H (X ∪ Y) ≤ steiner H X + steiner H Y := by
    rw [Fin.sum_univ_two] at key
    convert key using 2 <;> first | rfl | (ext x; simp [Fin.exists_fin_two])
  unfold stSizeG
  have : ((steiner H (X ∪ Y) : ℕ) : ℝ) ≤ ((steiner H X + steiner H Y : ℕ) : ℝ) := by
    exact_mod_cast key'
  simpa using this

/-- (G3) for the Steiner size, clusters (`hG3P`), with `cP = 0`. -/
theorem stSizeG_union_cluster [DecidableEq B] (hconn : H.Connected) {n : ℕ}
    (X : Fin (n + 1) → NePoly B)
    (hc : (clusterGraph (shareBlock (Subtype.val : NePoly B → Finset B)) X).Connected) :
    stSizeG H (unionOf (Subtype.val : NePoly B → Finset B) X) ≤ ∑ i, stSizeG H (X i).1 + 0 * n := by
  have key := Balaban.Fluctuation.phi_union_le (stSizeG H) 0
    (fun X Y hX hY h => stSizeG_union_le hconn hX hY h)
    (clusterGraph (shareBlock (Subtype.val : NePoly B → Finset B)) X) (fun i => (X i).1)
    (fun i => (X i).2) (fun i j hij => by
      have := ((clusterGraph_adj _ X i j).1 hij).2
      exact (lnk_shareBlock _ _ _).1 this) n Finset.univ (by simp)
    (by
      rw [Finset.coe_univ]
      exact (SimpleGraph.induceUnivIso _).connected_iff.2 hc)
  convert key using 3
  ext x; simp [unionOf]

/-- (G3) for the Steiner size, connected families of terms (`hG3T`), with `c = 0`. -/
theorem stSizeG_unionCs_le [DecidableEq B] (hconn : H.Connected) (C : Finset (NePoly B))
    (hC : ConnSet (Subtype.val : NePoly B → Finset B) C) :
    stSizeG H (unionCs (Subtype.val : NePoly B → Finset B) C) ≤
      ∑ t ∈ C, stSizeG H t.1 + 0 * ((C.card : ℝ) - 1) := by
  obtain ⟨hne, hreach⟩ := hC
  let Gc : SimpleGraph (NePoly B) :=
    SimpleGraph.fromRel (Contact (Subtype.val : NePoly B → Finset B))
  have hconnC : (Gc.induce (C : Set (NePoly B))).Connected := by
    obtain ⟨x₀, hx₀⟩ := hne
    have : Nonempty (C : Set (NePoly B)) := ⟨⟨x₀, hx₀⟩⟩
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    have key : ∀ y, Relation.ReflTransGen
        (fun x y => x ∈ C ∧ y ∈ C ∧ Contact (Subtype.val : NePoly B → Finset B) x y) a y →
        ∀ hy : y ∈ C, (Gc.induce (C : Set (NePoly B))).Reachable ⟨a, ha⟩ ⟨y, hy⟩ := by
      intro y hy
      induction hy with
      | refl => intro _; exact SimpleGraph.Reachable.refl _
      | @tail u v _ huv ih =>
        intro hv
        have hu : u ∈ C := huv.1
        refine (ih hu).trans ?_
        by_cases heq : u = v
        · subst heq; exact SimpleGraph.Reachable.refl _
        · exact SimpleGraph.Adj.reachable (show Gc.Adj u v from by
            rw [SimpleGraph.fromRel_adj]; exact ⟨heq, Or.inl huv.2.2⟩)
    exact key b (hreach a ha b hb) hb
  have := Balaban.Fluctuation.phi_union_le (stSizeG H) 0
    (fun X Y hX hY h => stSizeG_union_le hconn hX hY h) Gc (fun t => t.1) (fun t => t.2)
    (fun i j hij => by
      rw [SimpleGraph.fromRel_adj] at hij
      rcases hij.2 with h | h
      · exact h
      · exact fun hd => h hd.symm) (C.card - 1) C
    (Nat.sub_add_cancel (Finset.card_pos.2 hne)).symm hconnC
  have hc : ((C.card - 1 : ℕ) : ℝ) = (C.card : ℝ) - 1 := by
    rw [Nat.cast_sub (Finset.card_pos.2 hne)]; simp
  rw [hc] at this
  convert this using 3
  ext x; simp [unionCs]

/-- The number of nonempty site sets through `b` of Steiner size `n + 1`. -/
theorem card_setsG_le [DecidableEq B] (hconn : H.Connected) {Δ : ℕ}
    (hdeg : ∀ v, H.degree v ≤ Δ) (b : B) (n : ℕ) :
    ((Finset.univ : Finset (NePoly B)).filter
      (fun Y => b ∈ Y.1 ∧ steiner H Y.1 = n + 1)).card ≤ Δ ^ (2 * n) * 2 ^ (n + 1) := by
  set 𝒴 : Finset (Finset B) := (animals H b (n + 1)).biUnion (fun W => W.powerset) with h𝒴
  have hmaps : ∀ Y ∈ (Finset.univ : Finset (NePoly B)).filter
      (fun Y => b ∈ Y.1 ∧ steiner H Y.1 = n + 1), Y.1 ∈ 𝒴 := by
    intro Y hY
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY
    obtain ⟨W, hW, hYW, hWc⟩ := steiner_spec (exists_animal_supset_of_connected hconn Y.1)
    rw [h𝒴, Finset.mem_biUnion]
    refine ⟨W, ?_, Finset.mem_powerset.mpr hYW⟩
    rw [mem_animals]
    exact ⟨hYW hY.1, by rw [hWc, hY.2], hW.2⟩
  have hcard : 𝒴.card ≤ Δ ^ (2 * n) * 2 ^ (n + 1) := by
    calc 𝒴.card ≤ ∑ W ∈ animals H b (n + 1), (W.powerset).card := Finset.card_biUnion_le
      _ = ∑ W ∈ animals H b (n + 1), 2 ^ (n + 1) :=
          Finset.sum_congr rfl (fun W hW => by
            rw [Finset.card_powerset, ((mem_animals _).mp hW).2.1])
      _ = (animals H b (n + 1)).card * 2 ^ (n + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ Δ ^ (2 * n) * 2 ^ (n + 1) := by
          refine Nat.mul_le_mul_right _ ?_
          have := card_animals_le H hdeg b (n + 1)
          simpa using this
  exact (Finset.card_le_card_of_injOn (fun Y => Y.1) (fun Y hY => hmaps Y hY)
    (fun Y _ Y' _ h => Subtype.ext h)).trans hcard

/-- (G2): the entropy sum over nonempty site sets through a site, in the Steiner size. -/
theorem sum_exp_stSizeG_le [DecidableEq B] (hconn : H.Connected) {Δ : ℕ}
    (hdeg : ∀ v, H.degree v ≤ Δ) {κ0 : ℝ}
    (hq : (Δ : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2) (b : B) :
    ∑ Y : NePoly B, (if b ∈ Y.1 then Real.exp (-κ0 * stSizeG H Y.1) else 0) ≤
      4 * Real.exp (-κ0) := by
  set f : ℕ → ℝ := fun n => Real.exp (-κ0 * (n : ℝ)) with hf
  have h1 : ∑ Y : NePoly B, (if b ∈ Y.1 then Real.exp (-κ0 * stSizeG H Y.1) else 0) =
      ∑ Y ∈ (Finset.univ : Finset (NePoly B)).filter (fun Y => b ∈ Y.1), f (steiner H Y.1) := by
    rw [Finset.sum_filter]; rfl
  rw [h1]
  have hpos : ∀ Y : NePoly B, b ∈ Y.1 → 1 ≤ steiner H Y.1 := by
    intro Y hb
    have := card_le_steiner (exists_animal_supset_of_connected hconn Y.1)
    have h2 : 0 < Y.1.card := Finset.card_pos.mpr ⟨b, hb⟩
    omega
  have hmaps : ∀ Y ∈ (Finset.univ : Finset (NePoly B)).filter (fun Y => b ∈ Y.1),
      steiner H Y.1 - 1 ∈ range (Fintype.card B) := by
    intro Y hY
    rw [Finset.mem_filter] at hY
    have h3 : steiner H Y.1 ≤ Fintype.card B :=
      (steiner_le (isAnimal_univ_of_connected hconn) (Finset.subset_univ _)).trans
        (Finset.card_le_univ _)
    have h4 := hpos Y hY.2
    have h5 : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ⟨b⟩
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  set q : ℝ := (Δ : ℝ) ^ 2 * 2 * Real.exp (-κ0) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hterm : ∀ n ∈ range (Fintype.card B),
      ∑ Y ∈ ((Finset.univ : Finset (NePoly B)).filter (fun Y => b ∈ Y.1)).filter
        (fun Y => steiner H Y.1 - 1 = n), f (steiner H Y.1) ≤ 2 * Real.exp (-κ0) * q ^ n := by
    intro n _
    have hval : ∀ Y ∈ ((Finset.univ : Finset (NePoly B)).filter (fun Y => b ∈ Y.1)).filter
        (fun Y => steiner H Y.1 - 1 = n), f (steiner H Y.1) = f (n + 1) := by
      intro Y hY
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY
      have h4 := hpos Y hY.1
      congr 2; omega
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    have hc : ((((Finset.univ : Finset (NePoly B)).filter (fun Y => b ∈ Y.1)).filter
        (fun Y => steiner H Y.1 - 1 = n)).card : ℝ) ≤ ((Δ ^ (2 * n) * 2 ^ (n + 1) : ℕ) : ℝ) := by
      refine Nat.cast_le.mpr (le_trans (le_of_eq ?_) (card_setsG_le hconn hdeg b n))
      congr 1
      ext Y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hb, h⟩; exact ⟨hb, by have := hpos Y hb; omega⟩
      · rintro ⟨hb, h⟩; exact ⟨hb, by omega⟩
    refine (mul_le_mul_of_nonneg_right hc (by positivity)).trans (le_of_eq ?_)
    have eexp : f (n + 1) = Real.exp (-κ0) * Real.exp (-κ0) ^ n := by
      rw [hf]; simp only; rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    rw [eexp, hqdef]
    push_cast
    rw [pow_mul]
    ring_nf
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have h3 : ∑ i ∈ range (Fintype.card B), q ^ i ≤ (1 - q)⁻¹ :=
    sum_le_hasSum _ (fun i _ => by positivity) (hasSum_geometric_of_lt_one hq0 (by linarith))
  have h4 : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h5 : ∑ i ∈ range (Fintype.card B), q ^ i ≤ 2 := h3.trans h4
  nlinarith [Real.exp_pos (-κ0)]

end Geometry

/-! ### The gas theorem with the Steiner size -/

section Consumer

variable {B : Type*} [Fintype B] [DecidableEq B] {H : SimpleGraph B} {Ω : B → Type*}
  [∀ b, MeasurableSpace (Ω b)]
  (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]

/-- The numerical conditions of `mayerGen_pe` for the Steiner gas (`c = cP = 0`, `c1 = 1`,
`K0 = K0P = 4 e^{-κ0}`). -/
theorem steinerGen_numerics {κ0 κ1 κ' H0 : ℝ} (hκ0 : Real.log 4 + 1 ≤ κ0)
    (hH0 : 0 ≤ H0) (hH0K : H0 * (4 * Real.exp (-κ0)) ≤ 1 / 4) :
    2 * H0 * (4 * Real.exp (-κ0)) * Real.exp (κ1 * 0) * 1 ≤ 1 / 2 ∧
    2 * (2 * H0 * (4 * Real.exp (-κ0)) * Real.exp (κ1 * 0)) * 1 * (4 * Real.exp (-κ0)) *
      Real.exp (1 + κ' * 0) ≤ 1 := by
  have hK0 : 0 ≤ 4 * Real.exp (-κ0) := by positivity
  have hKle : 4 * Real.exp (-κ0) ≤ Real.exp (-1) := by
    have h4 : (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
    rw [h4, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  refine ⟨?_, ?_⟩
  · simp only [mul_zero, Real.exp_zero, mul_one]; nlinarith
  · simp only [mul_zero, Real.exp_zero, mul_one, add_zero]
    have h1 : 4 * Real.exp (-κ0) * Real.exp 1 ≤ 1 := by
      calc 4 * Real.exp (-κ0) * Real.exp 1 ≤ Real.exp (-1) * Real.exp 1 :=
            mul_le_mul_of_nonneg_right hKle (Real.exp_pos 1).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have h2 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    nlinarith [mul_nonneg hH0 hK0]

/-- **The gas theorem with general weights on a connected graph.** On a finite set of sites with a
connected graph of degree at most `Δ` and the Steiner size, weights `f X`, one for each nonempty set
`X` of sites, measurable, depending only on the sites of `X`, with an integrable dominating
function `∏_X (1 + |f X|)` and the product bound
`|∫ ∏_{X ∈ C} f X| ≤ ∏_{X ∈ C} 2 H₀ e^{-(κ₀ + κ₁) |X|_St}`, satisfy
`∫ ∏_X (1 + f X) d⨂μ = exp (∑_Y P(Y))` with `∑_{Y ∋ b} ‖P(Y)‖ e^{κ' |Y|_St} ≤ 64 e H0 e^{-2 κ0}`. -/
theorem steinerGen_gas (hconn : H.Connected) {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ)
    {κ0 κ1 κ' H0 : ℝ} (hq : (Δ : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2)
    (hκ0 : Real.log 4 + 1 ≤ κ0) (hκ' : 0 ≤ κ') (hκ : κ' + κ0 + 1 ≤ κ1 - 3 / 2)
    (hH0 : 0 ≤ H0) (hH0K : H0 * (4 * Real.exp (-κ0)) ≤ 1 / 4)
    (f : NePoly B → (∀ b, Ω b) → ℂ)
    (hloc : ∀ X, DepOn X.1 (f X)) (hmeas : ∀ X, Measurable (f X))
    (hdom : Integrable (fun Φ => ∏ X, (1 + ‖f X Φ‖)) (Measure.pi μ))
    (hprod : ∀ C : Finset (NePoly B), ‖∫ Φ, ∏ X ∈ C, f X Φ ∂(Measure.pi μ)‖ ≤
      ∏ X ∈ C, (mayerRho (fun X : NePoly B => X.1) (stSizeG H) κ0 H0 X *
        Real.exp (-κ1 * stSizeG H X.1))) :
    ∫ Φ, ∏ X, (1 + f X Φ) ∂(Measure.pi μ) =
      Complex.exp (logSeries (shareBlock (Subtype.val : NePoly B → Finset B))
        (mayerGenK μ (fun X : NePoly B => X.1) f)) ∧
    (∀ b : B, ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
      ‖PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
          (mayerGenK μ (fun X : NePoly B => X.1) f) Y‖ *
        Real.exp (κ' * stSizeG H Y) ≤ 64 * Real.exp 1 * H0 * Real.exp (-(2 * κ0))) ∧
    logSeries (shareBlock (Subtype.val : NePoly B → Finset B))
        (mayerGenK μ (fun X : NePoly B => X.1) f) =
      ∑ Y : Finset B, PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
          (mayerGenK μ (fun X : NePoly B => X.1) f) Y := by
  have hκ0nn : 0 ≤ κ0 := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hκ1nn : 0 ≤ κ1 := by linarith
  have hK0 : 0 ≤ 4 * Real.exp (-κ0) := by positivity
  have hG2 : ∀ b : B, ∑ Y : NePoly B,
      (if b ∈ Y.1 then Real.exp (-κ0 * stSizeG H Y.1) else 0) ≤ 4 * Real.exp (-κ0) :=
    fun b => sum_exp_stSizeG_le hconn hdeg hq b
  obtain ⟨hq', hα⟩ := steinerGen_numerics (κ1 := κ1) (κ' := κ') hκ0 hH0 hH0K
  have hmain := mayerGen_pe (μ := μ) (sup := fun X : NePoly B => X.1) (f := f)
    (d := stSizeG H) (H0 := H0) (κ0 := κ0) (κ1 := κ1) (c := 0) (K0 := 4 * Real.exp (-κ0))
    (c1 := 1) (κ' := κ') (κ0P := κ0) (K0P := 4 * Real.exp (-κ0)) (cP := 0)
    (fun X => X.2) hloc hmeas hdom hH0 hκ1nn le_rfl (fun Y => stSizeG_nonneg Y) hprod hK0
    (fun b => by rw [Finset.sum_filter]; convert hG2 b)
    (fun C hC => by simpa using stSizeG_unionCs_le hconn C hC) zero_le_one hq'
    (fun Y => card_le_stSizeG hconn Y.1) hK0 hκ' le_rfl
    (fun b => by convert hG2 b) (fun n X hX => by simpa using stSizeG_union_cluster hconn X hX)
    hκ hα
  obtain ⟨h1, h2, -, h5⟩ := hmain
  refine ⟨h1, fun b => ?_, h5⟩
  have h4 : 2 * (2 * H0 * (4 * Real.exp (-κ0)) * Real.exp (κ1 * 0)) * 1 * (4 * Real.exp (-κ0)) *
      Real.exp (1 + κ' * 0) * Real.exp (-(κ' * 0)) ≤
      64 * Real.exp 1 * H0 * Real.exp (-(2 * κ0)) := by
    simp only [mul_zero, Real.exp_zero, mul_one, neg_zero, add_zero]
    have e : 2 * (2 * H0 * (4 * Real.exp (-κ0))) * (4 * Real.exp (-κ0)) * Real.exp 1 =
        64 * Real.exp 1 * H0 * Real.exp (-(2 * κ0)) := by
      rw [show -(2 * κ0) = -κ0 + -κ0 by ring, Real.exp_add]; ring
    exact le_of_eq e
  convert (h2 b).trans h4

omit [∀ b, IsProbabilityMeasure (μ b)] in
/-- **The Kotecký–Preiss data of the Steiner gas with general weights**: under the hypotheses of
`steinerGen_gas`, the activities are bounded by the weights `sizeW` of PE-L, which satisfy the
Kotecký–Preiss condition (the input of the analyticity of the local terms). -/
theorem steinerGen_kp (hconn : H.Connected) {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ)
    {κ0 κ1 κ' H0 : ℝ} (hq : (Δ : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2)
    (hκ0 : Real.log 4 + 1 ≤ κ0) (hκ' : 0 ≤ κ') (hκ : κ' + κ0 + 1 ≤ κ1 - 3 / 2)
    (hH0 : 0 ≤ H0) (hH0K : H0 * (4 * Real.exp (-κ0)) ≤ 1 / 4)
    (f : NePoly B → (∀ b, Ω b) → ℂ) (hmeas : ∀ X, Measurable (f X))
    (hdom : Integrable (fun Φ => ∏ X, (1 + ‖f X Φ‖)) (Measure.pi μ))
    (hprod : ∀ C : Finset (NePoly B), ‖∫ Φ, ∏ X ∈ C, f X Φ ∂(Measure.pi μ)‖ ≤
      ∏ X ∈ C, (mayerRho (fun X : NePoly B => X.1) (stSizeG H) κ0 H0 X *
        Real.exp (-κ1 * stSizeG H X.1))) :
    (∀ Y : NePoly B, ‖mayerGenK μ (fun X : NePoly B => X.1) f Y‖ ≤
        sizeW (Subtype.val : NePoly B → Finset B) (stSizeG H)
          (2 * (2 * H0 * (4 * Real.exp (-κ0)) * Real.exp (κ1 * 0)) * 1) (κ1 - 3 / 2) κ' 0 Y) ∧
    KPCond (shareBlock (Subtype.val : NePoly B → Finset B))
      (sizeW (Subtype.val : NePoly B → Finset B) (stSizeG H)
        (2 * (2 * H0 * (4 * Real.exp (-κ0)) * Real.exp (κ1 * 0)) * 1) (κ1 - 3 / 2) κ' 0)
      (fun Y => (2 * (2 * H0 * (4 * Real.exp (-κ0)) * Real.exp (κ1 * 0)) * 1 *
        (4 * Real.exp (-κ0)) * Real.exp (1 + κ' * 0)) * (Y.1.card : ℝ)) := by
  have hκ0nn : 0 ≤ κ0 := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hκ1nn : 0 ≤ κ1 := by linarith
  have hK0 : 0 ≤ 4 * Real.exp (-κ0) := by positivity
  have hG2 : ∀ b : B, ∑ Y : NePoly B,
      (if b ∈ Y.1 then Real.exp (-κ0 * stSizeG H Y.1) else 0) ≤ 4 * Real.exp (-κ0) :=
    fun b => sum_exp_stSizeG_le hconn hdeg hq b
  obtain ⟨hq', hα⟩ := steinerGen_numerics (κ1 := κ1) (κ' := κ') hκ0 hH0 hH0K
  set ε := 2 * (2 * H0 * (4 * Real.exp (-κ0)) * Real.exp (κ1 * 0)) * 1 with hε
  have hε0 : 0 ≤ ε := by positivity
  have hK : ∀ Y : NePoly B, ‖mayerGenK μ (fun X : NePoly B => X.1) f Y‖ ≤
        ε * Real.exp (-(κ1 - 3 / 2) * stSizeG H Y.1) := fun Y =>
    mayerGen_activity_bound μ (sup := fun X : NePoly B => X.1) (d := stSizeG H)
      (κ0 := κ0) (c := 0) hmeas hdom hH0 hκ1nn le_rfl (fun Y => stSizeG_nonneg Y) (fun X => X.2)
      hprod (fun b => by rw [Finset.sum_filter]; convert hG2 b)
      (fun C hC => by simpa using stSizeG_unionCs_le hconn C hC) zero_le_one hq' Y
      (card_le_stSizeG hconn Y.1)
  refine ⟨fun Y => (hK Y).trans ?_, ?_⟩
  · unfold sizeW
    calc ε * Real.exp (-(κ1 - 3 / 2) * stSizeG H Y.1) =
          ε * Real.exp (-(κ1 - 3 / 2) * stSizeG H Y.1) * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_le_exp (by
          have := stSizeG_nonneg (H := H) Y.1; positivity)) (by positivity)
  · exact kp_of_entropy _ _ (sizeW_nonneg _ (stSizeG H) hε0)
      (size_entropy (Subtype.val : NePoly B → Finset B) (stSizeG H) hε0
        (fun Y => stSizeG_nonneg Y) (fun Y => card_le_stSizeG hconn Y.1)
        (fun b => by convert hG2 b) hκ
        (by simpa [mul_assoc] using hα))

/-- **The gas theorem for local terms on a connected graph.** Local terms `H X`, one for each
nonempty set `X` of sites, measurable, depending only on the sites of `X` and bounded for all
configurations by `H0 e^{-(κ0 + κ1) |X|_St}`, satisfy `∫ exp (∑_X H X) d⨂μ = exp (∑_Y P(Y))` with
`∑_{Y ∋ b} ‖P(Y)‖ e^{κ' |Y|_St} ≤ 64 e H0 e^{-2 κ0}` and `L = ∑_Y P(Y)`: the case `f X = e^{H X} - 1`
of `steinerGen_gas`. -/
theorem steiner_gas (hconn : H.Connected) {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ)
    {κ0 κ1 κ' H0 : ℝ} (hq : (Δ : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2)
    (hκ0 : Real.log 4 + 1 ≤ κ0) (hκ' : 0 ≤ κ') (hκ : κ' + κ0 + 1 ≤ κ1 - 3 / 2)
    (hH0 : 0 ≤ H0) (hH0log : H0 ≤ Real.log 2) (hH0K : H0 * (4 * Real.exp (-κ0)) ≤ 1 / 4)
    (Ht : NePoly B → (∀ b, Ω b) → ℂ)
    (hloc : ∀ X, DepOn X.1 (Ht X)) (hmeas : ∀ X, Measurable (Ht X))
    (hbd : ∀ X Φ, ‖Ht X Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * stSizeG H X.1)) :
    ∫ Φ, Complex.exp (∑ X, Ht X Φ) ∂(Measure.pi μ) =
      Complex.exp (logSeries (shareBlock (Subtype.val : NePoly B → Finset B))
        (mayerK μ (fun X : NePoly B => X.1) Ht)) ∧
    (∀ b : B, ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
      ‖PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
          (mayerK μ (fun X : NePoly B => X.1) Ht) Y‖ *
        Real.exp (κ' * stSizeG H Y) ≤ 64 * Real.exp 1 * H0 * Real.exp (-(2 * κ0))) ∧
    logSeries (shareBlock (Subtype.val : NePoly B → Finset B))
        (mayerK μ (fun X : NePoly B => X.1) Ht) =
      ∑ Y : Finset B, PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
          (mayerK μ (fun X : NePoly B => X.1) Ht) Y := by
  have hκ0nn : 0 ≤ κ0 := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  obtain ⟨hdom, hprod⟩ := expm1_dom_prod μ (sup := fun X : NePoly B => X.1)
    (d := stSizeG H) hmeas hH0 hH0log hκ0nn (by linarith) (fun Y => stSizeG_nonneg Y) hbd
  have hmain := steinerGen_gas μ hconn hdeg hq hκ0 hκ' hκ hH0 hH0K
    (fun X Φ => Complex.exp (Ht X Φ) - 1)
    (fun X Φ Φ' hΦ => by
      show Complex.exp (Ht X Φ) - 1 = Complex.exp (Ht X Φ') - 1
      rw [hloc X Φ Φ' hΦ])
    (fun X => (Complex.measurable_exp.comp (hmeas X)).sub_const 1) hdom hprod
  have hf : ∀ Φ : ∀ b, Ω b, Complex.exp (∑ X, Ht X Φ) =
      ∏ X, (1 + (Complex.exp (Ht X Φ) - 1)) := by
    intro Φ
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl (fun X _ => by ring)
  simp_rw [hf]
  exact hmain

end Consumer

end Balaban.Polymer
