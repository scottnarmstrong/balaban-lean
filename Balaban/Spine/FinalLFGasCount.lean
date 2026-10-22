/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalLFGasWeight
public import Balaban.Spine.FinalLFGasGeom

/-!
# The weighted counts of the records, in cubes (A6-4)

The weighted counts of the heavy objects of the record gas, with the size of a record measured by
its number `v` of `k`-cubes: the sum of the expectations `E |τ_r|` over the realized records whose
support `dblNbhd ω_k Y` contains a site `b` of the doubled torus and whose cubes `Y` number `v` is
at most `m · K^{v-1} · e^{-A₂ λ_{k₀}^{p₂} - H_k |Y|_k}` (`sum_integral_norm_recTauG_le`), with
`m = (2ω_k - 1)^d` (the cubes whose doubled image lies within `ω_k - 1` of `b`) and
`K = m^2`. The per-cube decay is `H_k M^d` itself; the separation range enters only through the
prefactor `m` and the entropy `K` of the `ω_k`-connected sets (logarithmic in `ω_k`).

The ingredients: `E |τ_r| ≤ e^{-κ(r)}` (`integral_norm_recTauG_le`, the bound (1.26)); the sum over
the records with the cubes `Y` of `e^{-κ}` (`sum_exp_neg_kappa_lfSrc_le`, Lemma II.5.15 with labels,
under `D6Flat`); and the number of `ω_k`-components of `v` cubes whose support contains `b`
(`card_comps_through_le`): such a component contains one of the `m` cubes near `b`, and it is a
connected set of `v` vertices of the graph of index distance `< ω_k` (`omegaGraph`, degree `< m`;
`isAnimal_of_mem_comps`), of which there are at most `m^{2(v-1)}` through a vertex
(`card_animals_le`).

* `tDouble_injective`, `omegaGraph`, `omegaGraph_degree_le`, `isAnimal_of_mem_comps`,
  **`card_comps_through_le`**;
* `lfSrc_mem_comps`, **`sum_integral_norm_recTauG_le`**.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Polymer RegionHistory

namespace Balaban.RootFSpine

section Count

variable {d n : ℕ} [NeZero n]

/-- The doubling of the torus is injective. -/
theorem tDouble_injective : Function.Injective (tDouble (d := d) (n := n)) := by
  intro x y h
  funext i
  have hv := congrArg ZMod.val (congrFun h i)
  change (zDouble n (x i)).val = (zDouble n (y i)).val at hv
  rw [zDouble_val, zDouble_val] at hv
  exact ZMod.val_injective n (by omega)

variable (d n) in
/-- **The graph of the separation**: distinct points of the torus at index distance `< ω`. -/
def omegaGraph (ω : ℕ) : SimpleGraph (Torus d n) where
  Adj a b := a ≠ b ∧ supDist a b < ω
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [supDist_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable instance (ω : ℕ) : (omegaGraph d n ω).LocallyFinite := fun _ => Fintype.ofFinite _

open Classical in
/-- The graph of the separation has degree at most `(2ω - 1)^d`. -/
theorem omegaGraph_degree_le {ω : ℕ} (hω : 1 ≤ ω) (a : Torus d n) :
    (omegaGraph d n ω).degree a ≤ (2 * (ω - 1) + 1) ^ d := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  calc ((omegaGraph d n ω).neighborFinset a).card ≤
      (Finset.univ.filter fun b : Torus d n => supDist a b ≤ ω - 1).card := by
        refine Finset.card_le_card fun b hb => ?_
        rw [SimpleGraph.mem_neighborFinset] at hb
        have := (show a ≠ b ∧ supDist a b < ω from hb).2
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩
    _ ≤ (2 * (ω - 1) + 1) ^ d := card_ball_le a (ω - 1)

/-- **An `ω`-component is connected in the graph of the separation.** -/
theorem isAnimal_of_mem_comps {ω : ℕ} {X Y : Finset (Torus d n)} (hY : Y ∈ comps ω X) :
    IsAnimal (omegaGraph d n ω) Y := by
  rw [isAnimal_iff]
  refine ⟨comp_nonempty hY, fun x hx y hy => ?_⟩
  have hxy := ((mem_comp_iff hY hx).1 hy).2
  have key : ∀ z, Linked ω (X : Set (Torus d n)) x z → z ∈ Y →
      Relation.ReflTransGen (fun a b => a ∈ Y ∧ b ∈ Y ∧ (omegaGraph d n ω).Adj a b) x z := by
    intro z hz
    induction hz with
    | refl => intro _; exact Relation.ReflTransGen.refl
    | @tail b c hxb hbc ih =>
      intro hc
      have hb : b ∈ Y := (mem_comp_iff hY hx).2 ⟨hbc.1, hxb⟩
      by_cases hbc' : b = c
      · subst hbc'
        exact ih hb
      · exact (ih hb).tail ⟨hb, hc, (show (omegaGraph d n ω).Adj b c from ⟨hbc', hbc.2.2⟩)⟩
  exact key y hxy hy

open Classical in
/-- **The number of `ω`-components of `v` cubes whose support contains a site**: at most
`m · m^{2(v-1)}`, `m = (2ω - 1)^d`. -/
theorem card_comps_through_le {ω : ℕ} (hω : 1 ≤ ω) (𝒴 : Finset (Finset (Torus d n)))
    (h𝒴 : ∀ Y ∈ 𝒴, ∃ X, Y ∈ comps ω X) (b : Torus d (2 * n)) (v : ℕ) :
    (𝒴.filter fun Y => b ∈ dblNbhd ω Y ∧ Y.card = v).card ≤
      (2 * (ω - 1) + 1) ^ d * ((2 * (ω - 1) + 1) ^ d) ^ (2 * (v - 1)) := by
  set Sb := Finset.univ.filter fun x : Torus d n => supDist (tDouble x) b ≤ ω - 1 with hSb
  have hsub : (𝒴.filter fun Y => b ∈ dblNbhd ω Y ∧ Y.card = v) ⊆
      Sb.biUnion fun x => animals (omegaGraph d n ω) x v := by
    intro Y hY
    obtain ⟨hY𝒴, hb, hv⟩ := Finset.mem_filter.1 hY
    obtain ⟨X, hX⟩ := h𝒴 Y hY𝒴
    obtain ⟨x, hx, hxb⟩ := (Finset.mem_filter.1 hb).2
    exact Finset.mem_biUnion.2 ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, hxb⟩,
      (mem_animals _).2 ⟨hx, hv, (isAnimal_of_mem_comps hX).2⟩⟩
  have hSbcard : Sb.card ≤ (2 * (ω - 1) + 1) ^ d := by
    refine (Finset.card_le_card_of_injOn tDouble (t := Finset.univ.filter
      fun w : Torus d (2 * n) => supDist b w ≤ ω - 1) (fun x hx => ?_)
      (fun x _ y _ h => tDouble_injective h)).trans (card_ball_le b (ω - 1))
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [supDist_comm]
    exact (Finset.mem_filter.1 hx).2
  calc _ ≤ (Sb.biUnion fun x => animals (omegaGraph d n ω) x v).card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ Sb, (animals (omegaGraph d n ω) x v).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ Sb, ((2 * (ω - 1) + 1) ^ d) ^ (2 * (v - 1)) :=
        Finset.sum_le_sum fun x _ => card_animals_le _ (fun a => omegaGraph_degree_le hω a) x v
    _ = Sb.card * ((2 * (ω - 1) + 1) ^ d) ^ (2 * (v - 1)) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hSbcard

end Count

section Records

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  (rep : Rep S n R k0 K M N geo cs P k) (hkK : k ≤ K)

/-- The cubes of a realized record are an `ω_k`-component. -/
theorem lfSrc_mem_comps (r : ↥(lfAllRecs (M := M) rep.hist k)) :
    ∃ X : Finset (Torus S.d (n k)), r.1.1 ∈ comps (S.omega k) X :=
  ⟨_, lfSrc_cubes rep r ▸ (lfSrc r).2.2⟩

open Classical in
/-- **The weighted counts of the records, in cubes**: the sum of `E |τ_r|` over the realized
records whose support contains the site `b` and whose cubes number `v` is at most
`m · m^{2(v-1)} · e^{-A₂ λ_{k₀}^{p₂} - H_k |Y|_k}`, `m = (2ω_k - 1)^d`, `|Y|_k = M^d v`. -/
theorem sum_integral_norm_recTauG_le (hN : 1 ≤ N) (hD5 : D5Bound (k + 1) hkK rep) {khat : ℕ}
    (hD6 : D6Flat khat rep) (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    (hg : g ∈ l1Ball (GIdx S n M K N)) (b : Torus S.d (2 * n k)) (v : ℕ) :
    ∑ r ∈ (Finset.univ : Finset ↥(lfAllRecs (M := M) rep.hist k)).filter (fun r =>
        b ∈ dblNbhd (S.omega k) r.1.1 ∧ r.1.1.card = v),
        ∫ Φ, ‖recTauG rep hkK r hv g Φ‖ ∂(pProb S n M K k N) ≤
      ((2 * (S.omega k - 1) + 1) ^ S.d * ((2 * (S.omega k - 1) + 1) ^ S.d) ^ (2 * (v - 1)) : ℕ) *
        Real.exp (-(S.A2 * S.lam k0 ^ S.p2 + HRun P.H0 P.beta k * BudgetConsts.cubeVol S v)) := by
  set ω := S.omega k with hωdef
  set F := (Finset.univ : Finset ↥(lfAllRecs (M := M) rep.hist k)).filter (fun r =>
    b ∈ dblNbhd ω r.1.1 ∧ r.1.1.card = v) with hF
  set 𝒴 := F.image fun r => r.1.1 with h𝒴
  set E := Real.exp (-(S.A2 * S.lam k0 ^ S.p2 + HRun P.H0 P.beta k * BudgetConsts.cubeVol S v))
    with hE
  have hY : ∀ Y ∈ 𝒴, ∑ r ∈ F.filter (fun r => r.1.1 = Y),
      Real.exp (-rep.kappaH (lfSrc r).1 k (lfSrc r).2) ≤ E := by
    intro Y hYm
    obtain ⟨r₀, hr₀, rfl⟩ := Finset.mem_image.1 hYm
    have hv0 : r₀.1.1.card = v := ((Finset.mem_filter.1 hr₀).2).2
    calc ∑ r ∈ F.filter (fun r => r.1.1 = r₀.1.1),
          Real.exp (-rep.kappaH (lfSrc r).1 k (lfSrc r).2) ≤
        ∑ r ∈ (Finset.univ : Finset ↥(lfAllRecs (M := M) rep.hist k)).filter
          (fun r => r.1.1 = r₀.1.1), Real.exp (-rep.kappaH (lfSrc r).1 k (lfSrc r).2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun r hr => Finset.mem_filter.2
            ⟨Finset.mem_univ _, (Finset.mem_filter.1 hr).2⟩) (fun _ _ _ => (Real.exp_pos _).le)
      _ ≤ _ := sum_exp_neg_kappa_lfSrc_le rep hD6 hkK r₀.1.1
      _ = E := by rw [hv0]
  have hcard𝒴 : (𝒴.card : ℝ) ≤
      ((2 * (ω - 1) + 1) ^ S.d * ((2 * (ω - 1) + 1) ^ S.d) ^ (2 * (v - 1)) : ℕ) := by
    have h1 : 𝒴 ⊆ 𝒴.filter fun Y => b ∈ dblNbhd ω Y ∧ Y.card = v := by
      intro Y hYm
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hYm
      exact Finset.mem_filter.2 ⟨hYm, (Finset.mem_filter.1 hr).2⟩
    have h2 := card_comps_through_le (one_le_omega S k) 𝒴 (fun Y hYm => by
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hYm
      exact lfSrc_mem_comps rep r) b v
    exact_mod_cast (Finset.card_le_card h1).trans h2
  calc ∑ r ∈ F, ∫ Φ, ‖recTauG rep hkK r hv g Φ‖ ∂(pProb S n M K k N) ≤
      ∑ r ∈ F, Real.exp (-rep.kappaH (lfSrc r).1 k (lfSrc r).2) :=
        Finset.sum_le_sum fun r _ => integral_norm_recTauG_le rep hkK hN hD5 r hv g hg
    _ = ∑ Y ∈ 𝒴, ∑ r ∈ F.filter (fun r => r.1.1 = Y),
          Real.exp (-rep.kappaH (lfSrc r).1 k (lfSrc r).2) :=
        (Finset.sum_fiberwise_of_maps_to (fun r hr => Finset.mem_image_of_mem _ hr) _).symm
    _ ≤ ∑ _Y ∈ 𝒴, E := Finset.sum_le_sum hY
    _ = 𝒴.card * E := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard𝒴 (by rw [hE]; positivity)

end Records

end Balaban.RootFSpine
