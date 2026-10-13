/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0F1Assembly
public import Balaban.LargeField.Base.KF0CutoffSplit
public import Balaban.Polymer.MayerPE
public import Balaban.Polymer.Bridge
public import Balaban.Polymer.Hole
public import Balaban.Fluctuation.ClusterUnion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0AllGoodGas`: the all-plus, all-small sector as a polymer gas (blocks and geometry)

Only the all-plus, all-`ψ`-small sector of the bare one-scale model is treated; the heavy sectors,
the minus sheets and the one-scale theorem are NOT proved here.

## T1. The consumer

The landed abstract theorem turning `E_μ[exp(∑_t H_t)]`, for a product probability measure
`μ = ⨂_b μ_b` and bounded measurable local functions `H_t` (`DepOn (sup t) (H t)`) of small
weighted norm, into `exp` of a cluster sum is `Balaban.Polymer.mayer_pe`
(`Balaban/Polymer/MayerPE.lean`); it is the theorem invoked by `labelAct_integral_eq_exp`
(`Balaban/Fluctuation/StepNonvanishCluster.lean`), the cluster expansion of the zero-class step.
Its form: for a `Fintype` `B` of blocks, factor spaces `Ω b`, a `Fintype` `T` of terms with nonempty
supports `sup t : Finset B`, `H t : (∀ b, Ω b) → ℂ` measurable with `DepOn (sup t) (H t)`, a size
`d : Finset B → ℝ` and the bounds
`‖H t Φ‖ ≤ H0 e^{-(κ0+κ1) d (sup t)}` for ALL `Φ` (`hH`),
(G2) `∑_{t ∋ b} e^{-κ0 d (sup t)} ≤ K0`, (G3) `d (∪ C) ≤ ∑ d + c (|C| - 1)` for connected families,
(G1) `|Y| ≤ c1 (1 + d Y)`, the entropy (G2) and the union bound (G3) once more for all nonempty
`Y ⊆ B`, the numerics `H0 ≤ log 2`, `2 H0 K0 e^{κ1 c} c1 ≤ 1/2`,
`κ' + κ0P + c1 ≤ κ1 - 3/2`, `2 (2 H0 K0 e^{κ1 c}) c1 K0P e^{c1 + κ' cP} ≤ 1`, it gives
`∫ exp (∑_t H t Φ) d(⨂ μ) = exp (logSeries …)` with
`∑_{Y ∋ b} ‖P(Y)‖ e^{κ' d Y} ≤ 2 (2 H0 K0 e^{κ1 c}) c1 K0P e^{c1 + κ' cP} e^{-κ' cP}`.

## T2. The block product space

`BlockSpace` is the family of factor spaces `Ω_b = (sites of the block b → W)`;
`blockRef γ` its product reference (each factor the product of the one-site measures `γ` over the
sites of the block); `toSites` the restriction map from block configurations to site
configurations; `map_toSites_pi` identifies the image of the block product measure with the site
product measure; `depOn_comp_toSites` says that a function of the sites `H` composed with `toSites`
depends only on the blocks meeting `H`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory

namespace Balaban.LargeField.KF0Gas

open Balaban Balaban.Polymer

variable (d s m' : ℕ) [NeZero s] [NeZero m']

/-- The sites of the block `b` of side `s` of the torus of side `s m'`. -/
abbrev Fibre (b : Balaban.Torus d m') : Type := {x : Balaban.Torus d (s * m') // blockOf d s m' x = b}

/-- The block configuration space: on the block `b`, one value in `W` for each site of `b`. -/
abbrev BlockSpace (W : Type*) : Balaban.Torus d m' → Type _ := fun b => Fibre d s m' b → W

variable {d s m'}

section Space

variable {W : Type*} [MeasurableSpace W]

/-- The site configuration of a block configuration. -/
def toSites (Φ : ∀ b, BlockSpace d s m' W b) : Balaban.Torus d (s * m') → W :=
  fun x => Φ (blockOf d s m' x) ⟨x, rfl⟩

/-- The product reference on blocks: on each block the product of the one-site measure `γ` over
the sites of the block. -/
def blockRef (γ : Measure W) : ∀ b, Measure (BlockSpace d s m' W b) :=
  fun _ => Measure.pi fun _ => γ

instance blockRef_sigmaFinite (γ : Measure W) [SigmaFinite γ] (b : Balaban.Torus d m') :
    SigmaFinite (blockRef (d := d) (s := s) (m' := m') γ b) :=
  inferInstanceAs (SigmaFinite (Measure.pi fun _ : Fibre d s m' b => γ))

omit [NeZero s] [NeZero m'] in
theorem measurable_toSites : Measurable (toSites (d := d) (s := s) (m' := m') (W := W)) := by
  refine Measurable.of_eval fun x => ?_
  exact (measurable_pi_apply (⟨x, rfl⟩ : Fibre d s m' (blockOf d s m' x))).comp
    (measurable_pi_apply (blockOf d s m' x))

/-- The image of the block product measure under the restriction map is the site product
measure. -/
theorem map_toSites_pi (γ : Measure W) [SigmaFinite γ] :
    (Measure.pi (blockRef (d := d) (s := s) (m' := m') γ)).map toSites =
      Measure.pi fun _ : Balaban.Torus d (s * m') => γ := by
  symm
  refine Measure.pi_eq fun t ht => ?_
  rw [Measure.map_apply measurable_toSites (MeasurableSet.univ_pi ht)]
  have hpre : toSites ⁻¹' (Set.pi Set.univ t) = Set.pi Set.univ
      (fun b : Balaban.Torus d m' => Set.pi Set.univ (fun x : Fibre d s m' b => t x.1)) := by
    ext Φ
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, toSites]
    constructor
    · intro h b x
      obtain ⟨x, hb⟩ := x
      subst hb
      exact h x
    · intro h x
      exact h _ ⟨x, rfl⟩
  rw [hpre, Measure.pi_pi]
  simp only [blockRef, Measure.pi_pi]
  exact Fintype.prod_fiberwise (blockOf d s m') (fun x => γ (t x))

omit [NeZero s] [NeZero m'] [MeasurableSpace W] in
/-- A function of the sites in `H` composed with the restriction map depends only on the blocks
meeting `H`. -/
theorem depOn_comp_toSites {H : Finset (Balaban.Torus d (s * m'))}
    {F : (Balaban.Torus d (s * m') → W) → ℂ}
    (hF : ∀ ψ ψ' : Balaban.Torus d (s * m') → W, (∀ x ∈ H, ψ x = ψ' x) → F ψ = F ψ') :
    DepOn (H.image (blockOf d s m')) (fun Φ : ∀ b, BlockSpace d s m' W b => F (toSites Φ)) := by
  intro Φ Φ' h
  refine hF _ _ fun x hx => ?_
  exact congrFun (h _ (Finset.mem_image_of_mem _ hx)) ⟨x, rfl⟩

end Space

/-! ### Geometry of the block torus: the Steiner size and the hypotheses (G1)-(G3) -/

section Geometry

variable (d m')

/-- The block torus is connected for its nearest-neighbour graph. -/
theorem blockGraph_connected : (blockGraph d m').Connected := by
  have hstep : ∀ (x : Balaban.Torus d m') (μ : Fin d),
      (blockGraph d m').Reachable x (x + Pi.single μ 1) := by
    intro x μ
    by_cases h : x = x + Pi.single μ 1
    · rw [← h]
    · exact SimpleGraph.Adj.reachable ⟨h, μ, Or.inl rfl⟩
  have hnat : ∀ (x : Balaban.Torus d m') (μ : Fin d) (n : ℕ),
      (blockGraph d m').Reachable x (x + n • Pi.single μ 1) := by
    intro x μ n
    induction n with
    | zero => simp
    | succ n ih =>
      refine ih.trans ?_
      have := hstep (x + n • Pi.single μ 1) μ
      rwa [add_assoc, ← succ_nsmul] at this
  have hsum : ∀ (T : Finset (Fin d)) (n : Fin d → ℕ) (x : Balaban.Torus d m'),
      (blockGraph d m').Reachable x (x + ∑ μ ∈ T, n μ • Pi.single μ 1) := by
    intro T n
    induction T using Finset.induction_on with
    | empty => intro x; simp
    | insert μ T hμ ih =>
      intro x
      rw [Finset.sum_insert hμ, ← add_assoc]
      exact (hnat x μ (n μ)).trans (ih _)
  have h0 : ∀ a : Balaban.Torus d m', (blockGraph d m').Reachable 0 a := by
    intro a
    have := hsum Finset.univ (fun μ => (a μ).val) 0
    rw [zero_add] at this
    convert this using 1
    funext ν
    rw [Finset.sum_apply, Finset.sum_eq_single ν]
    · simp
    · intro μ _ hμ
      simp [hμ.symm]
    · simp
  have : Nonempty (Balaban.Torus d m') := ⟨0⟩
  exact ⟨fun a b => (h0 a).symm.trans (h0 b)⟩

variable {d m'}

/-- The Steiner size of a set of blocks of the torus: the smallest number of blocks of a connected
block set containing it. -/
def stSize (Y : Finset (Balaban.Torus d m')) : ℝ := (steiner (blockGraph d m') Y : ℝ)

omit [NeZero m'] in
theorem stSize_nonneg (Y : Finset (Balaban.Torus d m')) : 0 ≤ stSize Y := Nat.cast_nonneg _

theorem isAnimal_univ : IsAnimal (blockGraph d m') (Finset.univ : Finset (Balaban.Torus d m')) := by
  refine ⟨Finset.univ_nonempty, ?_⟩
  rw [Finset.coe_univ]
  exact (SimpleGraph.induceUnivIso _).connected_iff.2 (blockGraph_connected d m')

theorem exists_animal_supset (Y : Finset (Balaban.Torus d m')) :
    ∃ W : Finset (Balaban.Torus d m'), IsAnimal (blockGraph d m') W ∧ Y ⊆ W :=
  ⟨Finset.univ, isAnimal_univ, Finset.subset_univ _⟩

/-- (G1) with `c1 = 1`. -/
theorem card_le_stSize (Y : Finset (Balaban.Torus d m')) :
    (Y.card : ℝ) ≤ 1 * (1 + stSize Y) := by
  have := card_le_steiner (exists_animal_supset Y)
  unfold stSize
  have h : (Y.card : ℝ) ≤ (steiner (blockGraph d m') Y : ℝ) := by exact_mod_cast this
  linarith

theorem stSize_union_le {X Y : Finset (Balaban.Torus d m')} (_hX : X.Nonempty) (_hY : Y.Nonempty)
    (h : ¬ Disjoint X Y) : stSize (X ∪ Y) ≤ stSize X + stSize Y + 0 := by
  have key := steiner_union_le (H := blockGraph d m') (n := 1) ![X, Y]
    (fun i => exists_animal_supset _) ⊤ (by
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
  have key' : steiner (blockGraph d m') (X ∪ Y) ≤
      steiner (blockGraph d m') X + steiner (blockGraph d m') Y := by
    rw [Fin.sum_univ_two] at key
    convert key using 2 <;> first | rfl | (ext x; simp [Fin.exists_fin_two])
  unfold stSize
  have : ((steiner (blockGraph d m') (X ∪ Y) : ℕ) : ℝ) ≤
      ((steiner (blockGraph d m') X + steiner (blockGraph d m') Y : ℕ) : ℝ) := by exact_mod_cast key'
  simpa using this

end Geometry

end Balaban.LargeField.KF0Gas
