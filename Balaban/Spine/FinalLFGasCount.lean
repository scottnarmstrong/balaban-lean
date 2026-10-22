/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalLFGasWeight
public import Balaban.Spine.FinalLFGasGeom

/-!
# The weighted counts of the records (A6-4)

The heavy-object hypothesis `hcount` of B2's operator gas (`actGasOp_pe_hole`): the sum, over the
realized records whose support `dblNbhd ω_k Y` contains a site `b` and has `v` sites, of the
expectations `E |τ_r|` is at most `(3^d)^{2(v-1)} 2^v e^{-A₂ λ_{k₀}^{p₂}} e^{-h v}`, with
`h = H_k M^d / (2ω_k - 1)^d` (`sum_integral_norm_recTauG_le`). The ingredients:
`E |τ_r| ≤ e^{-κ(r)}`
(`integral_norm_recTauG_le`, the bound (1.26)); the sum over the records with the cubes `Y` of
`e^{-κ}` (`sum_exp_neg_kappa_lfSrc_le`, Lemma II.5.15 with labels, under `D6Flat`); the size
`v ≤ (2ω_k - 1)^d |Y|` of the support (`card_dblNbhd_le`); and the number of `ω_k`-components with a
support of `v` sites through `b` (`card_comps_supp_le`): the support is a connected set of `v`
sites of the doubled torus through `b` (`isAnimal_dblNbhd`; at most `(3^d)^{2(v-1)}` of them,
`card_animals_le`), and the component is a set of points whose doubled images lie in it (at most
`2^v`).

* `tDouble_injective`, **`card_comps_supp_le`**;
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

open Classical in
/-- **The number of `ω`-components with a support of `v` sites through a site**: at most
`(3^d)^{2(v-1)} 2^v`. -/
theorem card_comps_supp_le {ω : ℕ} (hω : 1 ≤ ω) (𝒴 : Finset (Finset (Torus d n)))
    (h𝒴 : ∀ Y ∈ 𝒴, ∃ X, Y ∈ comps ω X) (b : Torus d (2 * n)) (v : ℕ) :
    (𝒴.filter fun Y => b ∈ dblNbhd ω Y ∧ (dblNbhd ω Y).card = v).card ≤
      (3 ^ d) ^ (2 * (v - 1)) * 2 ^ v := by
  set T := (animals (kingGraph d (2 * n)) b v).biUnion fun D =>
    (Finset.univ.filter fun x : Torus d n => tDouble x ∈ D).powerset with hT
  have hsub : (𝒴.filter fun Y => b ∈ dblNbhd ω Y ∧ (dblNbhd ω Y).card = v) ⊆ T := by
    intro Y hY
    obtain ⟨hY𝒴, hb, hv⟩ := Finset.mem_filter.1 hY
    obtain ⟨X, hX⟩ := h𝒴 Y hY𝒴
    refine Finset.mem_biUnion.2 ⟨dblNbhd ω Y, (mem_animals _).2 ⟨hb, hv,
      (isAnimal_dblNbhd hω hX).2⟩, Finset.mem_powerset.2 fun x hx => ?_⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, x, hx, ?_⟩⟩
    rw [supDist_self]
    exact Nat.zero_le _
  have hfib : ∀ D ∈ animals (kingGraph d (2 * n)) b v,
      ((Finset.univ.filter fun x : Torus d n => tDouble x ∈ D).powerset).card ≤ 2 ^ v := by
    intro D hD
    rw [Finset.card_powerset]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    rw [← ((mem_animals _).1 hD).2.1]
    exact Finset.card_le_card_of_injOn tDouble (fun x hx => (Finset.mem_filter.1 hx).2)
      (fun x _ y _ h => tDouble_injective h)
  calc _ ≤ T.card := Finset.card_le_card hsub
    _ ≤ ∑ D ∈ animals (kingGraph d (2 * n)) b v,
          ((Finset.univ.filter fun x : Torus d n => tDouble x ∈ D).powerset).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _D ∈ animals (kingGraph d (2 * n)) b v, 2 ^ v := Finset.sum_le_sum hfib
    _ = (animals (kingGraph d (2 * n)) b v).card * 2 ^ v := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (3 ^ d) ^ (2 * (v - 1)) * 2 ^ v :=
        Nat.mul_le_mul_right _ (card_animals_le _ (fun a => kingGraph_degree_le a) b v)

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
/-- **The weighted counts of the records** (`hcount` of `actGasOp_pe_hole`): the sum of `E |τ_r|`
over the realized records whose support contains the site `b` and has `v` sites is at most
`(3^d)^{2(v-1)} 2^v e^{-A₂ λ_{k₀}^{p₂}} e^{-h v}`, `h = H_k M^d / (2ω_k - 1)^d`. -/
theorem sum_integral_norm_recTauG_le (hN : 1 ≤ N) (hD5 : D5Bound (k + 1) hkK rep) {khat : ℕ}
    (hD6 : D6Flat khat rep) (hH : 0 ≤ HRun P.H0 P.beta k) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N)) (b : Torus S.d (2 * n k))
    (v : ℕ) :
    ∑ r ∈ (Finset.univ : Finset ↥(lfAllRecs (M := M) rep.hist k)).filter (fun r =>
        b ∈ dblNbhd (S.omega k) r.1.1 ∧ (dblNbhd (S.omega k) r.1.1).card = v),
        ∫ Φ, ‖recTauG rep hkK r hv g Φ‖ ∂(pProb S n M K k N) ≤
      ((3 ^ S.d) ^ (2 * (v - 1)) * 2 ^ v : ℕ) * Real.exp (-(S.A2 * S.lam k0 ^ S.p2)) *
        Real.exp (-(HRun P.H0 P.beta k * (S.M : ℝ) ^ S.d /
          ((2 * (S.omega k - 1) + 1) ^ S.d : ℕ) * v)) := by
  set ω := S.omega k with hωdef
  have hω : 1 ≤ ω := one_le_omega S k
  set F := (Finset.univ : Finset ↥(lfAllRecs (M := M) rep.hist k)).filter (fun r =>
    b ∈ dblNbhd ω r.1.1 ∧ (dblNbhd ω r.1.1).card = v) with hF
  set 𝒴 := F.image fun r => r.1.1 with h𝒴
  set c : ℝ := (((2 * (ω - 1) + 1) ^ S.d : ℕ) : ℝ) with hc
  have hcpos : 0 < c := by rw [hc]; exact_mod_cast pow_pos (by omega) _
  set E := Real.exp (-(S.A2 * S.lam k0 ^ S.p2)) *
    Real.exp (-(HRun P.H0 P.beta k * (S.M : ℝ) ^ S.d / c * v)) with hE
  -- the bound for each set of cubes
  have hY : ∀ Y ∈ 𝒴, ∑ r ∈ F.filter (fun r => r.1.1 = Y),
      Real.exp (-rep.kappaH (lfSrc r).1 k (lfSrc r).2) ≤ E := by
    intro Y hYm
    obtain ⟨r₀, hr₀, rfl⟩ := Finset.mem_image.1 hYm
    have hv0 : (dblNbhd ω r₀.1.1).card = v := ((Finset.mem_filter.1 hr₀).2).2
    calc ∑ r ∈ F.filter (fun r => r.1.1 = r₀.1.1),
          Real.exp (-rep.kappaH (lfSrc r).1 k (lfSrc r).2) ≤
        ∑ r ∈ (Finset.univ : Finset ↥(lfAllRecs (M := M) rep.hist k)).filter
          (fun r => r.1.1 = r₀.1.1), Real.exp (-rep.kappaH (lfSrc r).1 k (lfSrc r).2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun r hr => Finset.mem_filter.2
            ⟨Finset.mem_univ _, (Finset.mem_filter.1 hr).2⟩) (fun _ _ _ => (Real.exp_pos _).le)
      _ ≤ Real.exp (-(S.A2 * S.lam k0 ^ S.p2 +
            HRun P.H0 P.beta k * BudgetConsts.cubeVol S r₀.1.1.card)) :=
          sum_exp_neg_kappa_lfSrc_le rep hD6 hkK r₀.1.1
      _ ≤ E := by
          rw [hE, ← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          have hcard : (v : ℝ) ≤ c * r₀.1.1.card := by
            rw [← hv0, hc]
            exact_mod_cast card_dblNbhd_le ω r₀.1.1
          have h1 : HRun P.H0 P.beta k * (S.M : ℝ) ^ S.d / c * v ≤
              HRun P.H0 P.beta k * BudgetConsts.cubeVol S r₀.1.1.card := by
            unfold BudgetConsts.cubeVol
            rw [div_mul_eq_mul_div, div_le_iff₀ hcpos]
            have hM : 0 ≤ HRun P.H0 P.beta k * (S.M : ℝ) ^ S.d := mul_nonneg hH (by positivity)
            nlinarith [mul_le_mul_of_nonneg_left hcard hM]
          linarith
  -- the number of sets of cubes
  have hcard𝒴 : (𝒴.card : ℝ) ≤ ((3 ^ S.d) ^ (2 * (v - 1)) * 2 ^ v : ℕ) := by
    have h1 : 𝒴 ⊆ 𝒴.filter fun Y => b ∈ dblNbhd ω Y ∧ (dblNbhd ω Y).card = v := by
      intro Y hYm
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hYm
      exact Finset.mem_filter.2 ⟨hYm, (Finset.mem_filter.1 hr).2⟩
    have h2 := card_comps_supp_le hω 𝒴 (fun Y hYm => by
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
    _ ≤ ((3 ^ S.d) ^ (2 * (v - 1)) * 2 ^ v : ℕ) * E :=
        mul_le_mul_of_nonneg_right hcard𝒴 (by rw [hE]; positivity)
    _ = _ := by rw [hE, mul_assoc]

end Records

end Balaban.RootFSpine
