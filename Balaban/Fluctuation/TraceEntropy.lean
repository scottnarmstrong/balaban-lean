/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.TraceEntropyCells
public import Balaban.Fluctuation.BackgroundChangeExpansion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 4.2, Step 4: the entropy sum for a fixed trace and the regrouped expansion
(FLUCTUATION.md §4.2, Step 4)

* `trace_entropy`: for a nonempty `S`, `κ' ≥ 0` and `a_ms + 1 ≤ 2κ - κ'`,
  `∑_{Y multiscale polymer domain, Y ∩ Ω = S} e^{-2κ d̃^cov(Y)} ≤ K₀^{ms} e^{-κ' d_Ω(S)}`.
  The proof is `dOmega_le_treeLenCov` (`d_Ω(S) ≤ d̃^cov(Y)` when `Y ∩ Ω = S`, (G4)) together
  with `multiscale_entropy` (every such `Y` contains a fixed point of `S`).
* `X1_connected`, `polymerDomain_isMultiDom`: the polymer domains `Y[𝒞]` of the localization
  expansion are multiscale polymer domains.
* `cube_expansion_traces`: from `cube_expansion`, the expansion regrouped over the traces
  `S = Y ∩ Ω ≠ ∅` with the bound `|𝓔_S| ≤ E_b K₀^{ms} e^{-κ₀ d^cov_j(X)} e^{-κ' d_Ω(S)}`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Analysis

section Trace

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)

open Classical in
/-- **Entropy of multiscale polymer domains with a fixed trace on `Ω`.** -/
theorem trace_entropy (hN : L ^ m₀ ∣ N₁)
    (hϱ : (4 * d * L * (L : ℝ) ^ (m₀ + m₁) : ℝ) ≤ ϱ) (hK : 1 ≤ K)
    {Ω : Set (CTorus d L N₁ m₁ K)} (hΩ : Ω ⊆ (G.layer K : Set (CTorus d L N₁ m₁ K)))
    {S : Set (CTorus d L N₁ m₁ K)} (hS : S.Nonempty)
    {κ κ' : ℝ} (hκ' : 0 ≤ κ') (hκ : aMulti d L + 1 ≤ 2 * κ - κ') :
    ∑ Y ∈ Finset.univ.filter (fun Y : Set (CTorus d L N₁ m₁ K) =>
        IsMultiDom G m₀ Y ∧ Y ∩ Ω = S), Real.exp (-(2 * κ) * treeLenCov G m₀ Y) ≤
      K0Multi d L * Real.exp (-κ' * (dOmega m₀ K Ω S).toReal) := by
  obtain ⟨x₀, hx₀⟩ := hS
  have hbound : ∀ Y ∈ Finset.univ.filter (fun Y : Set (CTorus d L N₁ m₁ K) =>
      IsMultiDom G m₀ Y ∧ Y ∩ Ω = S), Real.exp (-(2 * κ) * treeLenCov G m₀ Y) ≤
      Real.exp (-κ' * (dOmega m₀ K Ω S).toReal) *
        Real.exp (-(2 * κ - κ') * treeLenCov G m₀ Y) := by
    intro Y hY
    obtain ⟨hMD, hYS⟩ := (Finset.mem_filter.1 hY).2
    have hne : (Y ∩ Ω).Nonempty := by rw [hYS]; exact ⟨x₀, hx₀⟩
    have hle := dOmega_le_treeLenCov G m₀ hK hΩ hMD.2.1 hne hMD.2.2
    rw [hYS] at hle
    have hT := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rw [ENNReal.toReal_ofReal (treeLenCov_nonneg G m₀ Y)] at hT
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  refine (Finset.sum_le_sum hbound).trans ?_
  rw [← Finset.mul_sum]
  rw [mul_comm]
  refine mul_le_mul ?_ le_rfl (Real.exp_nonneg _) (K0Multi_nonneg d L)
  have hsub : Finset.univ.filter (fun Y : Set (CTorus d L N₁ m₁ K) =>
        IsMultiDom G m₀ Y ∧ Y ∩ Ω = S) ⊆ Finset.univ.filter (fun Y : Set (CTorus d L N₁ m₁ K) =>
        IsMultiDom G m₀ Y ∧ x₀ ∈ Y) := by
    intro Y hY
    obtain ⟨hMD, hYS⟩ := (Finset.mem_filter.1 hY).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hMD, ?_⟩
    have : x₀ ∈ Y ∩ Ω := by rw [hYS]; exact hx₀
    exact this.1
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Real.exp_nonneg _)).trans ?_
  exact multiscale_entropy G m₀ hN hϱ (κ := 2 * κ - κ') hκ


end Trace

section Polymers

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι] (c : ι → ℕ × CTorus d L N₁ m₁ K)
variable {j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]

/-- `X₁ = ⋃ 𝒬₀` is connected when a connected structure in `X` meets every cube of `𝒦_X`
(every coarse cube of `𝒬₀` contains a cube of `𝒦_X`, which the structure meets). -/
theorem X1_connected (hS : CovSetup G m₀ j X 𝒦X)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X) :
    ∀ x ∈ X1 G m₀ j 𝒦X, ∀ y ∈ X1 G m₀ j 𝒦X, Relation.ReflTransGen
      (fun a b => (latGraph d ((N₁ * L ^ m₁) * L ^ K)).Adj a b ∧ a ∈ X1 G m₀ j 𝒦X ∧
        b ∈ X1 G m₀ j 𝒦X) x y := by
  obtain ⟨W₀, E₀, hΓ, hWX, hmeet, -⟩ := hopt
  set X₁ := X1 G m₀ j 𝒦X with hX₁
  set r := fun a b : CTorus d L N₁ m₁ K =>
    (latGraph d ((N₁ * L ^ m₁) * L ^ K)).Adj a b ∧ a ∈ X₁ ∧ b ∈ X₁ with hr
  have hsymm : ∀ a b, r a b → r b a := fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  -- every point of `X₁` is joined to a point of `W₀`
  have hjoin : ∀ x ∈ X₁, ∃ y ∈ W₀, Relation.ReflTransGen r x y := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨-, -, q, hq, hqb⟩ := id hb
    obtain ⟨y, hyW, hyq⟩ := hmeet q hq
    have hbox : box b (L * cellSide L m₀ m₁ K) ⊆ X₁ := fun z hz => Set.mem_iUnion₂.2 ⟨b, hb, hz⟩
    exact ⟨y, hyW, chain_in_box b _ X₁ hbox hxb (hqb hyq)⟩
  -- the points of `W₀` are mutually joined
  have hW : ∀ y ∈ W₀, ∀ y' ∈ W₀, Relation.ReflTransGen r y y' := by
    intro y hy y' hy'
    have h := hΓ.2.2 y hy y' hy'
    have key : ∀ z, Relation.ReflTransGen (fun a b => (a, b) ∈ E₀ ∨ (b, a) ∈ E₀) y z →
        z ∈ W₀ ∧ Relation.ReflTransGen r y z := by
      intro z h
      induction h with
      | refl => exact ⟨hy, Relation.ReflTransGen.refl⟩
      | @tail b c _ hbc ih => ?_
      obtain ⟨-, ih⟩ := ih
      have hbc' : b ∈ W₀ ∧ c ∈ W₀ ∧ Nbr b c := by
        rcases hbc with h | h
        · exact hΓ.2.1 _ h
        · obtain ⟨h1, h2, h3⟩ := hΓ.2.1 _ h
          exact ⟨h2, h1, h3.symm⟩
      refine ⟨hbc'.2.1, ih.trans ?_⟩
      by_cases hbc0 : b = c
      · rw [hbc0]
      · exact Relation.ReflTransGen.single ⟨⟨hbc0, hbc'.2.2⟩, hS.X_sub (hWX hbc'.1),
          hS.X_sub (hWX hbc'.2.1)⟩
    exact (key y' h).2
  intro x hx y hy
  obtain ⟨x', hx'W, hx'⟩ := hjoin x hx
  obtain ⟨y', hy'W, hy'⟩ := hjoin y hy
  exact (hx'.trans (hW x' hx'W y' hy'W)).trans (rtg_symm hsymm hy')


open Classical in
/-- **Every polymer domain `Y[𝒞]` of the localization expansion is a multiscale polymer domain.** -/
theorem polymerDomain_isMultiDom (hS : CovSetup G m₀ j X 𝒦X) (hd : 3 ≤ d)
    (hc : ∀ i, c i ∈ cubeIdx G)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : Y ∈ polymerDomains c G m₀ (X1 G m₀ j 𝒦X)) :
    IsMultiDom G m₀ Y := by
  have hK : 1 ≤ K := by have := hS.hjK; omega
  obtain ⟨C, hCmem, rfl⟩ := Finset.mem_image.1 hY
  have hconn := (Finset.mem_filter.1 hCmem).2
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rcases hz with hz | hz
    · exact G.layer_subset hK le_rfl (Finset.mem_coe.1 (X1_layer hz))
    · obtain ⟨i, -, hzi⟩ := Set.mem_iUnion₂.1 hz
      obtain ⟨⟨h1, h2⟩, -⟩ := (mem_cubeIdx G).1 (hc i)
      exact G.layer_subset h1 h2 (Finset.mem_coe.1 (Dsites_subset_layer (c i) hzi))
  · intro x hx y hy
    exact Relation.ReflTransGen.mono (fun a b h => ⟨h.2.1, h.2.2, h.1.2⟩) x y
      (Ysites_preconnected hS.hU hS.hN hc _ hconn (X1_connected hS hopt) x hx y hy)
  · obtain ⟨W₀, E₀, hW1, hW2, hW3, hW4⟩ := hopt
    obtain ⟨W, E, hW1', hW2', hW3', -⟩ := gm2_tree hS hd hc C hconn hW1 hW2 hW3
    exact ⟨_, W, E, chosen_KY hc, hW1', hW2', hW3'⟩


open Classical in
/-- The multiscale polymer domains of the expansion meeting `Ω`. -/
noncomputable def meetingDomains (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)
    (X₁ Ω : Set (CTorus d L N₁ m₁ K)) : Finset (Set (CTorus d L N₁ m₁ K)) :=
  (polymerDomains c G m₀ X₁).filter fun Y => (Y ∩ Ω).Nonempty

open Classical in
/-- The traces `S = Y ∩ Ω ≠ ∅` of the polymer domains. -/
noncomputable def traceSet (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)
    (X₁ Ω : Set (CTorus d L N₁ m₁ K)) : Finset (Set (CTorus d L N₁ m₁ K)) :=
  (meetingDomains c G m₀ X₁ Ω).image fun Y => Y ∩ Ω

open Classical in
/-- **The terms of the regrouped expansion**: `∑_{Y : Y ∩ Ω = S} 𝓔(Y)`. -/
noncomputable def traceTerm (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)
    (X₁ Ω : Set (CTorus d L N₁ m₁ K)) (F : U → (ι → ℂ) → ℂ)
    (T : Set (CTorus d L N₁ m₁ K)) (u : U) : ℂ :=
  ∑ Y ∈ (meetingDomains c G m₀ X₁ Ω).filter (fun Y => Y ∩ Ω = T), evTerm c G m₀ X₁ F Y u

open Classical in
/-- **Theorem 4.2, Step 4: the expansion of one cube term regrouped by the trace `S = Y ∩ Ω`.**
Hypotheses are those of `cube_expansion` and the separation of the generating set.  For
`κ' ≥ 0` with `a_ms + 1 ≤ 2 κ - κ'` (the rate of (4.3) is any `κ' ≤ 2κ - 1 - κ₀`):

* `F u 1 = ∑_{Y ∩ Ω = ∅} 𝓔(Y) + ∑_{S ≠ ∅} 𝓔_S(u)`, `𝓔_S = ∑_{Y ∩ Ω = S} 𝓔(Y)`;
* `|𝓔_S(u)| ≤ Eb K₀^{ms} e^{-κ₀ d_cov(X)} e^{-κ' d_Ω(S)}` and `d_Ω(S) < ∞`;
* each `𝓔_S` is analytic on `S`, and local: it depends on `u` only through the agreement
  relations `AgY Y` of the domains `Y` with `Y ∩ Ω = S`. -/
theorem cube_expansion_traces (Ω : Set (CTorus d L N₁ m₁ K))
    (hΩ : Ω ⊆ (G.layer K : Set (CTorus d L N₁ m₁ K)))
    (hϱ : (4 * d * L * (L : ℝ) ^ (m₀ + m₁) : ℝ) ≤ ϱ)
    (hS : CovSetup G m₀ j X 𝒦X) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hc : ∀ i, c i ∈ cubeIdx G) (hcinj : Function.Injective c)
    (hdisj : ∀ i, Disjoint (Pset m₁ (c i)) (X1 G m₀ j 𝒦X))
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κ κ₀ κ₁ Eb κ' : ℝ} (hκ₀ : 0 ≤ κ₀) (hκ : 3 * κ₀ + 3 ≤ κ)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κ ≤ κ₁)
    (h1 : 1 ≤ (κ₁ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) (hκ'0 : 0 ≤ κ') (hκm : aMulti d L + 1 ≤ 2 * κ - κ')
    {S : Set U} {F : U → (ι → ℂ) → ℂ}
    {Ag : Finset ι → U → U → Prop} {AgY : Set (CTorus d L N₁ m₁ K) → U → U → Prop}
    (hrefl : ∀ C u, u ∈ S → Ag C u u)
    (hlink : ∀ C u u', AgY (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) u u' → Ag C u u')
    (hana : AnalyticOnNhd ℂ (fun p : U × (ι → ℂ) => F p.1 p.2)
      (S ×ˢ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁)))
    (hbd : ∀ u ∈ S, ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁),
      ‖F u s‖ ≤ Eb * Real.exp (-(κ - 1) * treeLenCovOne m₀ j X))
    (hloc : LocalityAEOn (Real.exp κ₁) S (fun i => Pset m₁ (c i)) (compY c (X1 G m₀ j 𝒦X)) Ag F) :
    (∀ u ∈ S, F u 1 =
      ∑ Y ∈ (polymerDomains c G m₀ (X1 G m₀ j 𝒦X)).filter (fun Y => Y ∩ Ω = ∅),
        evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y u +
      ∑ T ∈ traceSet c G m₀ (X1 G m₀ j 𝒦X) Ω, traceTerm c G m₀ (X1 G m₀ j 𝒦X) Ω F T u) ∧
    (∀ T ∈ traceSet c G m₀ (X1 G m₀ j 𝒦X) Ω, T.Nonempty ∧ dOmega m₀ K Ω T ≠ ⊤ ∧ ∀ u ∈ S,
      ‖traceTerm c G m₀ (X1 G m₀ j 𝒦X) Ω F T u‖ ≤ Eb * K0Multi d L *
        Real.exp (-κ₀ * treeLenCovOne m₀ j X) *
          Real.exp (-κ' * (dOmega m₀ K Ω T).toReal)) ∧
    (∀ T, AnalyticOnNhd ℂ (traceTerm c G m₀ (X1 G m₀ j 𝒦X) Ω F T) S) ∧
    (∀ T, ∀ u ∈ S, ∀ u' ∈ S, (∀ Y ∈ polymerDomains c G m₀ (X1 G m₀ j 𝒦X), Y ∩ Ω = T → AgY Y u u') →
      traceTerm c G m₀ (X1 G m₀ j 𝒦X) Ω F T u = traceTerm c G m₀ (X1 G m₀ j 𝒦X) Ω F T u') := by
  have hK : 1 ≤ K := by have := hS.hjK; omega
  obtain ⟨hsum, hlocY, hbound, hanY, -⟩ := cube_expansion (c := c) (AgY := AgY) Ω hS hd hL hc hcinj
    hdisj hopt hκ₀ hκ hκ₁ h1 hlog hEb hrefl hlink hana hbd hloc
  have hMD : ∀ Y ∈ polymerDomains c G m₀ (X1 G m₀ j 𝒦X), IsMultiDom G m₀ Y :=
    fun Y hY => polymerDomain_isMultiDom c hS hd hc hopt hY
  have hmaps : ∀ Y ∈ meetingDomains c G m₀ (X1 G m₀ j 𝒦X) Ω,
      (fun Y => Y ∩ Ω) Y ∈ traceSet c G m₀ (X1 G m₀ j 𝒦X) Ω :=
    fun Y hY => Finset.mem_image_of_mem _ hY
  refine ⟨fun u hu => ?_, fun T hT => ?_, fun T => ?_, fun T u hu u' hu' hag => ?_⟩
  · rw [hsum u hu]
    congr 1
    unfold traceTerm
    exact (Finset.sum_fiberwise_of_maps_to (g := fun Y => Y ∩ Ω) hmaps
      (fun Y => evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y u)).symm
  · obtain ⟨Y0, hY0, rfl⟩ := Finset.mem_image.1 hT
    obtain ⟨hY0PD, hY0ne⟩ := Finset.mem_filter.1 hY0
    refine ⟨hY0ne, ?_, fun u hu => ?_⟩
    · have hle := dOmega_le_treeLenCov G m₀ hK hΩ (hMD Y0 hY0PD).2.1 hY0ne (hMD Y0 hY0PD).2.2
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    · set T := Y0 ∩ Ω with hTdef
      have hsub : (meetingDomains c G m₀ (X1 G m₀ j 𝒦X) Ω).filter (fun Y => Y ∩ Ω = T) ⊆
          Finset.univ.filter (fun Y : Set (CTorus d L N₁ m₁ K) => IsMultiDom G m₀ Y ∧ Y ∩ Ω = T) := by
        intro Y hY
        obtain ⟨hYM, hYT⟩ := Finset.mem_filter.1 hY
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hMD Y (Finset.mem_filter.1 hYM).1, hYT⟩
      have hent := trace_entropy G m₀ hS.hN hϱ hK hΩ (S := T) hY0ne hκ'0 hκm
      calc ‖traceTerm c G m₀ (X1 G m₀ j 𝒦X) Ω F T u‖
          ≤ ∑ Y ∈ (meetingDomains c G m₀ (X1 G m₀ j 𝒦X) Ω).filter (fun Y => Y ∩ Ω = T),
              ‖evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y u‖ := norm_sum_le _ _
        _ ≤ ∑ Y ∈ (meetingDomains c G m₀ (X1 G m₀ j 𝒦X) Ω).filter (fun Y => Y ∩ Ω = T),
              Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X) *
                Real.exp (-(2 * κ) * treeLenCov G m₀ Y) := by
            refine Finset.sum_le_sum fun Y hY => ?_
            refine (hbound Y u hu).trans (le_of_eq ?_)
            rw [mul_assoc Eb, ← Real.exp_add]
            congr 2
            ring
        _ = Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X) *
              ∑ Y ∈ (meetingDomains c G m₀ (X1 G m₀ j 𝒦X) Ω).filter (fun Y => Y ∩ Ω = T),
                Real.exp (-(2 * κ) * treeLenCov G m₀ Y) := by rw [Finset.mul_sum]
        _ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X) *
              (K0Multi d L * Real.exp (-κ' * (dOmega m₀ K Ω T).toReal)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun _ _ _ => Real.exp_nonneg _)).trans hent
        _ = _ := by ring
  · unfold traceTerm
    have := Finset.analyticOnNhd_sum
      ((meetingDomains c G m₀ (X1 G m₀ j 𝒦X) Ω).filter (fun Y => Y ∩ Ω = T)) fun Y _ => hanY Y
    convert this using 1
    funext u
    simp [Finset.sum_apply]
  · unfold traceTerm
    refine Finset.sum_congr rfl fun Y hY => ?_
    obtain ⟨hYM, hYT⟩ := Finset.mem_filter.1 hY
    exact hlocY Y u hu u' hu' (hag Y (Finset.mem_filter.1 hYM).1 hYT)

end Polymers

end Balaban.Fluctuation
