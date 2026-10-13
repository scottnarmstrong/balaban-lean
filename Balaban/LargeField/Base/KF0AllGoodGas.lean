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

## T3. What is supplied

For the block torus `Torus d m'` (`ℓ = s m'`) with the nearest-neighbour graph `blockGraph` and the
Steiner size `stSize` (smallest connected block set containing a given block set), the hypotheses of
`mayer_pe` for the terms indexed by `NePoly B` with `sup X = X` are supplied, with `c = cP = 0`,
`c1 = 1`, `K0 = K0P = 4 e^{-κ0}`:

* `blockGraph_connected`, `isAnimal_univ`: every block set lies in a connected one;
* (G1) `card_le_stSize`; (G2) `card_sets_le`, `sum_exp_stSize_le` (uses the landed animal count
  `card_animals_le`, needs `(2 d)² · 2 · e^{-κ0} ≤ 1/2`); (G3) `stSize_union_le`,
  `stSize_unionCs_le` (families) and `stSize_union_cluster` (clusters), from `steiner_union_le`
  and `phi_union_le`;
* `block_gas`: the resulting theorem, for ANY measurable local terms `H X` on a product of
  probability spaces with `DepOn X (H X)` and the bound `‖H X Φ‖ ≤ H0 e^{-(κ0+κ1) |X|_St}` for all
  `Φ`; `block_gas_hypotheses_d3` shows its numerical hypotheses are satisfiable for `d = 3`;
* `isAnimal_image_blockOf_of_nnConnected`: the blocks of a nearest-neighbour connected site set form
  a connected block set (so the halo terms `F_H` live on animals, where the Steiner size is `|X|`).

## T4. The target statement, and what is not proved in this file

Target (not proved here).  For `γ` the one-site tangent Gaussian, `p` the cutoff, `X ↦ H_X` the
function `H_X(Φ) = ∑_{anchors a} ∑_{H : blocks(H) = X} F^a_H(clip_p (toSites Φ))`
(`F^a_H` = `f1SiteHalo` or `f1BondHalo`), and `μ = blockRef (γ(· | ‖ψ‖ ≤ p))`:
`Z_good(g) = (1 - τ)^n e^{sourceConst} · ∫ exp (∑_X H_X) d⨂μ = (1 - τ)^n e^{sourceConst}
exp (∑_Y P(Y))` with `∑_{Y ∋ b} ‖P(Y)‖ e^{κ' |Y|_St} ≤ 64 e H0 e^{-2κ0}`, `H0 = A ε`,
`A = (1 + 2 d) s^d`.  Not supplied here, each needed to apply `block_gas` to this `H_X`:
(i) measurability of `ψ ↦ F_H(ψ)` (a `tsum` over the countable walk index of continuous terms; the
landed `f1SiteHalo`, `f1BondHalo` have no measurability theorem);
(ii) the clipping `clip_p` (radial retraction onto `‖w‖ ≤ p`), so that the bound `‖H_X Φ‖ ≤ ...`
holds for ALL `Φ` (the landed bounds are `cutoffSup`, on the cutoff event only), and the
agreement `H_X = ∑ F` almost everywhere for the conditioned measure (`restrict_pi_smallSet_eq`);
(iii) `‖H_X Φ‖ ≤ H0 e^{-(κ0+κ1)|X|}` from `site_halo_decomposition` and `bond_halo_decomposition`:
at most `(1 + 2 d) s^d |X|` anchors have a nonzero halo term with blocks `X`; this needs
`κ ≥ 1 + κ0 + κ1`, hence `s ≥ κ 3^d/γ` large (`f1_instance` has `s = 9`, `κ = 1/300`, far from it);
(iv) the regrouping of `f1_integrand_eq` by block set, `H_X = 0` for non-connected `X`;
(v) the transfer of the real integral to `Complex.exp`, `map_toSites_pi`, and the normalization
`integral_indicator_small_eq`.

The heavy sectors, the minus sheets and the one-scale theorem are NOT proved here.
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

instance blockRef_isProbabilityMeasure (γ : Measure W) [IsProbabilityMeasure γ]
    (b : Balaban.Torus d m') : IsProbabilityMeasure (blockRef (d := d) (s := s) (m' := m') γ b) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fibre d s m' b => γ))

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

/-- (G3) for the Steiner size, clusters (`hG3P`), with `cP = 0`. -/
theorem stSize_union_cluster {n : ℕ} (X : Fin (n + 1) → NePoly (Balaban.Torus d m'))
    (hc : (clusterGraph (shareBlock (Subtype.val : NePoly (Balaban.Torus d m') →
      Finset (Balaban.Torus d m'))) X).Connected) :
    stSize (unionOf (Subtype.val : NePoly (Balaban.Torus d m') → Finset (Balaban.Torus d m')) X) ≤
      ∑ i, stSize (X i).1 + 0 * n := by
  have key := Balaban.Fluctuation.phi_union_le (stSize (d := d) (m' := m')) 0
    (fun X Y hX hY h => stSize_union_le hX hY h)
    (clusterGraph (shareBlock (Subtype.val : NePoly (Balaban.Torus d m') →
      Finset (Balaban.Torus d m'))) X) (fun i => (X i).1)
    (fun i => (X i).2) (fun i j hij => by
      have := ((clusterGraph_adj _ X i j).1 hij).2
      exact (lnk_shareBlock _ _ _).1 this) n Finset.univ (by simp)
    (by
      rw [Finset.coe_univ]
      exact (SimpleGraph.induceUnivIso _).connected_iff.2 hc)
  convert key using 3
  ext x; simp [unionOf]

/-- (G3) for the Steiner size, connected families of terms (`hG3T`), with `c = 0`. -/
theorem stSize_unionCs_le (C : Finset (NePoly (Balaban.Torus d m')))
    (hC : ConnSet (Subtype.val : NePoly (Balaban.Torus d m') → Finset (Balaban.Torus d m')) C) :
    stSize (unionCs (Subtype.val : NePoly (Balaban.Torus d m') → Finset (Balaban.Torus d m')) C) ≤
      ∑ t ∈ C, stSize t.1 + 0 * ((C.card : ℝ) - 1) := by
  obtain ⟨hne, hreach⟩ := hC
  let Gc : SimpleGraph (NePoly (Balaban.Torus d m')) :=
    SimpleGraph.fromRel (Contact (Subtype.val : NePoly (Balaban.Torus d m') →
      Finset (Balaban.Torus d m')))
  have hconn : (Gc.induce (C : Set (NePoly (Balaban.Torus d m')))).Connected := by
    obtain ⟨x₀, hx₀⟩ := hne
    have : Nonempty (C : Set (NePoly (Balaban.Torus d m'))) := ⟨⟨x₀, hx₀⟩⟩
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    have key : ∀ y, Relation.ReflTransGen
        (fun x y => x ∈ C ∧ y ∈ C ∧ Contact (Subtype.val : NePoly (Balaban.Torus d m') →
          Finset (Balaban.Torus d m')) x y) a y →
        ∀ hy : y ∈ C, (Gc.induce (C : Set (NePoly (Balaban.Torus d m')))).Reachable
          ⟨a, ha⟩ ⟨y, hy⟩ := by
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
  have := Balaban.Fluctuation.phi_union_le (stSize (d := d) (m' := m')) 0
    (fun X Y hX hY h => stSize_union_le hX hY h) Gc (fun t => t.1) (fun t => t.2)
    (fun i j hij => by
      rw [SimpleGraph.fromRel_adj] at hij
      rcases hij.2 with h | h
      · exact h
      · exact fun hd => h hd.symm) (C.card - 1) C
    (Nat.sub_add_cancel (Finset.card_pos.2 hne)).symm hconn
  have hc : ((C.card - 1 : ℕ) : ℝ) = (C.card : ℝ) - 1 := by
    rw [Nat.cast_sub (Finset.card_pos.2 hne)]; simp
  rw [hc] at this
  convert this using 3
  ext x; simp [unionCs]

theorem degree_le (a : Balaban.Torus d m') : (blockGraph d m').degree a ≤ 2 * d :=
  blockGraph_degree_le d m' a

/-- The number of nonempty block sets through `b` of Steiner size `n + 1`. -/
theorem card_sets_le (b : Balaban.Torus d m') (n : ℕ) :
    ((Finset.univ : Finset (NePoly (Balaban.Torus d m'))).filter
      (fun Y => b ∈ Y.1 ∧ steiner (blockGraph d m') Y.1 = n + 1)).card ≤
      (2 * d) ^ (2 * n) * 2 ^ (n + 1) := by
  set 𝒴 : Finset (Finset (Balaban.Torus d m')) :=
    (animals (blockGraph d m') b (n + 1)).biUnion (fun W => W.powerset) with h𝒴
  have hmaps : ∀ Y ∈ (Finset.univ : Finset (NePoly (Balaban.Torus d m'))).filter
      (fun Y => b ∈ Y.1 ∧ steiner (blockGraph d m') Y.1 = n + 1), Y.1 ∈ 𝒴 := by
    intro Y hY
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY
    obtain ⟨W, hW, hYW, hWc⟩ := steiner_spec (exists_animal_supset Y.1)
    rw [h𝒴, Finset.mem_biUnion]
    refine ⟨W, ?_, Finset.mem_powerset.mpr hYW⟩
    rw [mem_animals]
    exact ⟨hYW hY.1, by rw [hWc, hY.2], hW.2⟩
  have hcard : 𝒴.card ≤ (2 * d) ^ (2 * n) * 2 ^ (n + 1) := by
    calc 𝒴.card ≤ ∑ W ∈ animals (blockGraph d m') b (n + 1), (W.powerset).card :=
          Finset.card_biUnion_le
      _ = ∑ W ∈ animals (blockGraph d m') b (n + 1), 2 ^ (n + 1) :=
          Finset.sum_congr rfl (fun W hW => by
            rw [Finset.card_powerset, ((mem_animals _).mp hW).2.1])
      _ = (animals (blockGraph d m') b (n + 1)).card * 2 ^ (n + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (2 * d) ^ (2 * n) * 2 ^ (n + 1) := by
          refine Nat.mul_le_mul_right _ ?_
          have := card_animals_le (blockGraph d m') degree_le b (n + 1)
          simpa using this
  exact (Finset.card_le_card_of_injOn (fun Y => Y.1) (fun Y hY => hmaps Y hY)
    (fun Y _ Y' _ h => Subtype.ext h)).trans hcard

/-- (G2): the entropy sum over nonempty block sets through a block, in the Steiner size. -/
theorem sum_exp_stSize_le {κ0 : ℝ}
    (hq : ((2 * d : ℕ) : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2) (b : Balaban.Torus d m') :
    ∑ Y : NePoly (Balaban.Torus d m'),
      (if b ∈ Y.1 then Real.exp (-κ0 * stSize Y.1) else 0) ≤ 4 * Real.exp (-κ0) := by
  set f : ℕ → ℝ := fun n => Real.exp (-κ0 * (n : ℝ)) with hf
  have h1 : ∑ Y : NePoly (Balaban.Torus d m'),
      (if b ∈ Y.1 then Real.exp (-κ0 * stSize Y.1) else 0) =
      ∑ Y ∈ (Finset.univ : Finset (NePoly (Balaban.Torus d m'))).filter (fun Y => b ∈ Y.1),
        f (steiner (blockGraph d m') Y.1) := by
    rw [Finset.sum_filter]; rfl
  rw [h1]
  have hpos : ∀ Y : NePoly (Balaban.Torus d m'), b ∈ Y.1 → 1 ≤ steiner (blockGraph d m') Y.1 := by
    intro Y hb
    have := card_le_steiner (exists_animal_supset Y.1)
    have h2 : 0 < Y.1.card := Finset.card_pos.mpr ⟨b, hb⟩
    omega
  have hmaps : ∀ Y ∈ (Finset.univ : Finset (NePoly (Balaban.Torus d m'))).filter
      (fun Y => b ∈ Y.1), steiner (blockGraph d m') Y.1 - 1 ∈
        range (Fintype.card (Balaban.Torus d m')) := by
    intro Y hY
    rw [Finset.mem_filter] at hY
    have h3 : steiner (blockGraph d m') Y.1 ≤ Fintype.card (Balaban.Torus d m') :=
      (steiner_le isAnimal_univ (Finset.subset_univ _)).trans (Finset.card_le_univ _)
    have h4 := hpos Y hY.2
    have h5 : 0 < Fintype.card (Balaban.Torus d m') := Fintype.card_pos_iff.mpr ⟨b⟩
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  set q : ℝ := ((2 * d : ℕ) : ℝ) ^ 2 * 2 * Real.exp (-κ0) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hterm : ∀ n ∈ range (Fintype.card (Balaban.Torus d m')),
      ∑ Y ∈ ((Finset.univ : Finset (NePoly (Balaban.Torus d m'))).filter
        (fun Y => b ∈ Y.1)).filter (fun Y => steiner (blockGraph d m') Y.1 - 1 = n),
        f (steiner (blockGraph d m') Y.1) ≤ 2 * Real.exp (-κ0) * q ^ n := by
    intro n _
    have hval : ∀ Y ∈ ((Finset.univ : Finset (NePoly (Balaban.Torus d m'))).filter
        (fun Y => b ∈ Y.1)).filter (fun Y => steiner (blockGraph d m') Y.1 - 1 = n),
        f (steiner (blockGraph d m') Y.1) = f (n + 1) := by
      intro Y hY
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY
      have h4 := hpos Y hY.1
      congr 2; omega
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    have hc : ((((Finset.univ : Finset (NePoly (Balaban.Torus d m'))).filter
        (fun Y => b ∈ Y.1)).filter (fun Y => steiner (blockGraph d m') Y.1 - 1 = n)).card : ℝ) ≤
        (((2 * d) ^ (2 * n) * 2 ^ (n + 1) : ℕ) : ℝ) := by
      refine Nat.cast_le.mpr (le_trans (le_of_eq ?_) (card_sets_le b n))
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
    have h8 : ((2 : ℝ) * 2 ^ 2) ^ n = 2 ^ n * 4 ^ n := by
      rw [← mul_pow]; norm_num
    ring_nf
    rw [show ((8 : ℝ)) ^ n = 2 ^ n * 4 ^ n by rw [← mul_pow]; norm_num]
    ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have h3 : ∑ i ∈ range (Fintype.card (Balaban.Torus d m')), q ^ i ≤ (1 - q)⁻¹ :=
    sum_le_hasSum _ (fun i _ => by positivity) (hasSum_geometric_of_lt_one hq0 (by linarith))
  have h4 : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h5 : ∑ i ∈ range (Fintype.card (Balaban.Torus d m')), q ^ i ≤ 2 := h3.trans h4
  nlinarith [Real.exp_pos (-κ0)]

end Geometry


/-! ### The consumer on the block torus: `mayer_pe` with the Steiner size -/

section Consumer

variable {Ω : Balaban.Torus d m' → Type*} [∀ b, MeasurableSpace (Ω b)]
  (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]

/-- **The block gas theorem (T1, T3).**  On the torus of blocks with the Steiner size, local terms
`H X`, one for each nonempty set `X` of blocks, measurable, depending only on the blocks of `X`
and bounded for all configurations by `H0 e^{-(κ0 + κ1) |X|_St}`, with the numerical conditions
below, satisfy `∫ exp (∑_X H X) d⨂μ = exp (∑_Y P(Y))` with `∑_{Y ∋ b} ‖P(Y)‖ e^{κ' |Y|_St} ≤
64 e H0 e^{-2 κ0}`.  The hypotheses (G1)-(G3) of `mayer_pe` are supplied by the Steiner geometry
(`card_le_stSize`, `sum_exp_stSize_le`, `stSize_unionCs_le`, `stSize_union_cluster`) with
`c = cP = 0`, `c1 = 1`, `K0 = K0P = 4 e^{-κ0}`. -/
theorem block_gas {κ0 κ1 κ' H0 : ℝ}
    (hq : ((2 * d : ℕ) : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2)
    (hκ0 : Real.log 4 + 1 ≤ κ0) (hκ' : 0 ≤ κ') (hκ : κ' + κ0 + 1 ≤ κ1 - 3 / 2)
    (hH0 : 0 ≤ H0) (hH0log : H0 ≤ Real.log 2) (hH0K : H0 * (4 * Real.exp (-κ0)) ≤ 1 / 4)
    (H : NePoly (Balaban.Torus d m') → (∀ b, Ω b) → ℂ)
    (hloc : ∀ X, DepOn X.1 (H X)) (hmeas : ∀ X, Measurable (H X))
    (hbd : ∀ X Φ, ‖H X Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * stSize X.1)) :
    ∫ Φ, Complex.exp (∑ X, H X Φ) ∂(Measure.pi μ) =
      Complex.exp (logSeries (shareBlock (Subtype.val : NePoly (Balaban.Torus d m') →
        Finset (Balaban.Torus d m'))) (mayerK μ (fun X : NePoly (Balaban.Torus d m') => X.1) H)) ∧
    ∀ b : Balaban.Torus d m', ∑ Y ∈ (Finset.univ : Finset (Finset (Balaban.Torus d m'))).filter
        (fun Y => b ∈ Y),
      ‖PY (shareBlock (Subtype.val : NePoly (Balaban.Torus d m') → Finset (Balaban.Torus d m')))
          Subtype.val (mayerK μ (fun X : NePoly (Balaban.Torus d m') => X.1) H) Y‖ *
        Real.exp (κ' * stSize Y) ≤ 64 * Real.exp 1 * H0 * Real.exp (-(2 * κ0)) := by
  have hκ0nn : 0 ≤ κ0 := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hκ1nn : 0 ≤ κ1 := by linarith
  have hK0 : 0 ≤ 4 * Real.exp (-κ0) := by positivity
  have hKle : 4 * Real.exp (-κ0) ≤ Real.exp (-1) := by
    have h4 : (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
    rw [h4, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hG2 : ∀ b : Balaban.Torus d m', ∑ Y : NePoly (Balaban.Torus d m'),
      (if b ∈ Y.1 then Real.exp (-κ0 * stSize Y.1) else 0) ≤ 4 * Real.exp (-κ0) :=
    fun b => sum_exp_stSize_le hq b
  have hq' : 2 * H0 * (4 * Real.exp (-κ0)) * Real.exp (κ1 * 0) * 1 ≤ 1 / 2 := by
    simp only [mul_zero, Real.exp_zero, mul_one]; nlinarith
  have hα : 2 * (2 * H0 * (4 * Real.exp (-κ0)) * Real.exp (κ1 * 0)) * 1 * (4 * Real.exp (-κ0)) *
      Real.exp (1 + κ' * 0) ≤ 1 := by
    simp only [mul_zero, Real.exp_zero, mul_one, add_zero]
    have h1 : 4 * Real.exp (-κ0) * Real.exp 1 ≤ 1 := by
      calc 4 * Real.exp (-κ0) * Real.exp 1 ≤ Real.exp (-1) * Real.exp 1 :=
            mul_le_mul_of_nonneg_right hKle (Real.exp_pos 1).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have h2 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    nlinarith [mul_nonneg hH0 hK0]
  have hmain := mayer_pe (μ := μ) (sup := fun X : NePoly (Balaban.Torus d m') => X.1) (H := H)
    (d := stSize) (H0 := H0) (κ0 := κ0) (κ1 := κ1) (c := 0) (K0 := 4 * Real.exp (-κ0))
    (c1 := 1) (κ' := κ') (κ0P := κ0) (K0P := 4 * Real.exp (-κ0)) (cP := 0)
    (fun X => X.2) hloc hmeas hH0 hH0log hκ0nn hκ1nn le_rfl (fun Y => stSize_nonneg Y)
    (fun X Φ => by simpa using hbd X Φ) hK0
    (fun b => by rw [Finset.sum_filter]; convert hG2 b)
    (fun C hC => by simpa using stSize_unionCs_le C hC) zero_le_one hq'
    (fun Y => card_le_stSize Y.1) hK0 hκ' le_rfl
    (fun b => by convert hG2 b) (fun n X hX => by simpa using stSize_union_cluster X hX)
    hκ hα
  obtain ⟨h1, h2, -⟩ := hmain
  refine ⟨h1, fun b => ?_⟩
  have h4 : 2 * (2 * H0 * (4 * Real.exp (-κ0)) * Real.exp (κ1 * 0)) * 1 * (4 * Real.exp (-κ0)) *
      Real.exp (1 + κ' * 0) * Real.exp (-(κ' * 0)) ≤
      64 * Real.exp 1 * H0 * Real.exp (-(2 * κ0)) := by
    simp only [mul_zero, Real.exp_zero, mul_one, neg_zero, add_zero]
    have e : 2 * (2 * H0 * (4 * Real.exp (-κ0))) * (4 * Real.exp (-κ0)) * Real.exp 1 =
        64 * Real.exp 1 * H0 * Real.exp (-(2 * κ0)) := by
      rw [show -(2 * κ0) = -κ0 + -κ0 by ring, Real.exp_add]; ring
    exact le_of_eq e
  convert (h2 b).trans h4

end Consumer


/-! ### Halos and non-vacuity -/

section Halo

/-- The blocks of a nearest-neighbour connected nonempty set of sites form a connected block
set. -/
theorem isAnimal_image_blockOf_of_nnConnected {H : Finset (Balaban.Torus d (s * m'))}
    (hne : H.Nonempty) (hH : Balaban.Green.NNConnected H) :
    IsAnimal (blockGraph d m') (H.image (blockOf d s m')) := by
  rw [isAnimal_iff]
  refine ⟨hne.image _, fun b₁ hb₁ b₂ hb₂ => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb₁
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb₂
  refine site_rtg_to_block (H.image (blockOf d s m')) (s := s) ?_
  refine Relation.ReflTransGen.mono (fun a b hab => ?_) _ _ (hH x hx y hy)
  obtain ⟨ha, hb, μ, hμ⟩ := hab
  rw [mem_siteSet, mem_siteSet]
  exact ⟨Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb, μ, hμ⟩

/-- Non-vacuity of the numerical hypotheses of `block_gas` for `d = 3` (every `m'`), with all
local terms zero. -/
theorem block_gas_hypotheses_d3 :
    ∃ κ0 κ1 κ' H0 : ℝ, ((2 * 3 : ℕ) : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2 ∧
      Real.log 4 + 1 ≤ κ0 ∧ 0 ≤ κ' ∧ κ' + κ0 + 1 ≤ κ1 - 3 / 2 ∧ 0 ≤ H0 ∧ H0 ≤ Real.log 2 ∧
      H0 * (4 * Real.exp (-κ0)) ≤ 1 / 4 := by
  have hl4 := Balaban.LargeField.log_four_bounds
  have hl2 := Real.log_two_gt_d9
  have he : Real.exp (-10) ≤ 1 / 200 := by
    rw [Real.exp_neg, inv_eq_one_div]
    refine one_div_le_one_div_of_le (by norm_num) ?_
    have h1 : (2.7 : ℝ) < Real.exp 1 := lt_of_lt_of_le (by norm_num) Real.exp_one_gt_d9.le
    have h2 : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    calc (200 : ℝ) ≤ 2.7 ^ 10 := by norm_num
      _ ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) h1.le 10
  refine ⟨10, 13, 0, 1 / 100, ?_, by linarith [hl4.2], le_rfl, by norm_num, by norm_num,
    by linarith, ?_⟩
  · norm_num; linarith
  · norm_num; linarith

end Halo

end Balaban.LargeField.KF0Gas
