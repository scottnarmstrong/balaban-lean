/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Theorem42Input
public import Balaban.Fluctuation.BackgroundChangeLate
public import Balaban.Fluctuation.CubeAction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 4.2 (O-2′): the expansion (4.2) and the bound (4.3) (FLUCTUATION.md §4.2)

Undecoupled form, conditional on the one named input `DecoupledCubeResponse` (the decoupled
weighted response, OPEN-NC-MIXED), used only in the `*_of_input` theorems.

For the action cubes `X_b = box b (L a_j)`, `b ∈ 𝒬`, with decoupled cube differences `F b`:

* `emptyTraceTerm`: the terms with `Y ∩ Ω = ∅` (the internal complement terms, allocated to `b_k`);
* `traceTermAll T`: `Δ(T) = ∑_b ∑_{Y : Y ∩ Ω = T} 𝓔_b(Y)`, the term of (4.2) of the trace
  `T = Y ∩ Ω ≠ ∅` (the polymer `Ŷ(T)` of `𝒟(mod Ω^c)`, of modular size `d_Ω(T)`);
* `theorem42_of_input`: **(4.2)** `∑_b act b = b_k + ∑_T Δ(T)`, **(4.3), first bound**
  `|Δ(T)| ≤ C_b c_cube K₀ e^{-κ' d_Ω(T)}` (the factor `c_cube` is the number of cubes `□ ⊂ Y` per
  unit of `d̃^cov(Y)`: (G1); the pre-summation over `Y` with trace `T` is (G2), `trace_entropy`),
  analyticity and locality of each `Δ(T)`;
* `theorem42_late_of_input`: **(4.3), second bound**, from the late threshold (Λ28′).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Analysis Balaban.Background

section Main

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ j : ℕ)
variable {ι : Type*} [DecidableEq ι] [Fintype ι] (c : ι → ℕ × CTorus d L N₁ m₁ K)
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]

open Classical in
/-- The terms of the expansions of the cubes `b ∈ 𝒬` supported away from `Ω`
(`Y ∩ Ω = ∅`): the internal complement terms, which go to `b_k`. -/
noncomputable def emptyTraceTerm (𝒬 : Finset (CTorus d L N₁ m₁ K)) (Ω : Set (CTorus d L N₁ m₁ K))
    (F : CTorus d L N₁ m₁ K → U → (ι → ℂ) → ℂ) (u : U) : ℂ :=
  ∑ b ∈ 𝒬, ∑ Y ∈ (polymerDomains c G m₀ (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K)))).filter
      (fun Y => Y ∩ Ω = ∅),
    evTerm c G m₀ (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K))) (F b) Y u

/-- The traces `T = Y ∩ Ω ≠ ∅` of the polymer domains of all the cubes. -/
noncomputable def traceSetAll (𝒬 : Finset (CTorus d L N₁ m₁ K)) (Ω : Set (CTorus d L N₁ m₁ K)) :
    Finset (Set (CTorus d L N₁ m₁ K)) :=
  open Classical in
  𝒬.biUnion fun b => traceSet c G m₀ (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K))) Ω

/-- **`Δ(T)`**: the term of (4.2) of the trace `T`, summed over the cubes. -/
noncomputable def traceTermAll (𝒬 : Finset (CTorus d L N₁ m₁ K)) (Ω : Set (CTorus d L N₁ m₁ K))
    (F : CTorus d L N₁ m₁ K → U → (ι → ℂ) → ℂ) (T : Set (CTorus d L N₁ m₁ K)) (u : U) : ℂ :=
  ∑ b ∈ 𝒬, traceTerm c G m₀ (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K))) Ω (F b) T u

/-- The number of cubes `□ ⊂ Y` per unit of `d̃^cov(Y)`: `L^{(K-j)d} · L^{2d} 3^{d+1} L`
((G1): the aligned cubes of side `a_j` in a cell of side `a_K`, and the block count). -/
noncomputable def cubeCount (d L K j : ℕ) : ℝ :=
  ((L ^ (K - j)) ^ d : ℕ) * ((L : ℝ) ^ (2 * d) * (3 ^ (d + 1) * L))

theorem cubeCount_nonneg (d L K j : ℕ) : 0 ≤ cubeCount d L K j := by
  unfold cubeCount; positivity

variable {G m₀ j c}

omit [NormedAddCommGroup U] [NormedSpace ℂ U] in
open Classical in
theorem traceTerm_eq_zero_of_not_mem {X₁ Ω : Set (CTorus d L N₁ m₁ K)}
    {F : U → (ι → ℂ) → ℂ} {T : Set (CTorus d L N₁ m₁ K)} (hT : T ∉ traceSet c G m₀ X₁ Ω)
    (u : U) : traceTerm c G m₀ X₁ Ω F T u = 0 := by
  unfold traceTerm
  refine Finset.sum_eq_zero fun Y hY => ?_
  obtain ⟨hYm, hYT⟩ := Finset.mem_filter.1 hY
  exact absurd (hYT ▸ Finset.mem_image_of_mem (fun Y => Y ∩ Ω) hYm) hT

omit [NormedAddCommGroup U] [NormedSpace ℂ U] [DecidableEq ι] in
/-- The base `b` of an action cube lies in every polymer domain of its expansion. -/
theorem base_mem_domain {b : CTorus d L N₁ m₁ K}
    (hS : CovSetup G m₀ j (box b (L * cellSide L m₀ m₁ j)) {b})
    {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : Y ∈ polymerDomains c G m₀ (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K)))) :
    b ∈ Y ∧ b ∈ (G.layer K : Set (CTorus d L N₁ m₁ K)) := by
  classical
  obtain ⟨C, -, rfl⟩ := Finset.mem_image.1 hY
  have hpos : 0 < L * cellSide L m₀ m₁ j :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ j)
  have hb : b ∈ X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K)) := hS.X_sub (mem_box_self b hpos)
  exact ⟨Or.inl hb, X1_layer hb⟩

omit [NormedAddCommGroup U] [NormedSpace ℂ U] [DecidableEq ι] in
open Classical in
/-- **(G1), the number of action cubes whose expansion contains `Y`.** -/
theorem card_cubes_domain (𝒬 : Finset (CTorus d L N₁ m₁ K))
    (hS : ∀ b ∈ 𝒬, CovSetup G m₀ j (box b (L * cellSide L m₀ m₁ j)) {b})
    (hϱ : (4 * d * L * (L : ℝ) ^ (m₀ + m₁) : ℝ) ≤ ϱ) (hL : 1 ≤ L)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsMultiDom G m₀ Y) :
    ((𝒬.filter fun b => Y ∈ polymerDomains c G m₀ (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K)))).card
      : ℝ) ≤ cubeCount d L K j * (treeLenCov G m₀ Y + 1) := by
  set 𝒬' := 𝒬.filter fun b => Y ∈ polymerDomains c G m₀ (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K)))
    with h𝒬'
  by_cases hne : 𝒬'.Nonempty
  · obtain ⟨b₀, hb₀⟩ := hne
    have hb₀S := hS b₀ (Finset.mem_filter.1 hb₀).1
    have hK : 1 ≤ K := by have := hb₀S.hjK; omega
    have hjK : j ≤ K := by have := hb₀S.hjK; omega
    have hN := hb₀S.hN
    have h1 := card_cubes_le_cells G m₀ hN hjK hY 𝒬' (fun q hq => by
      obtain ⟨hqQ, hqY⟩ := Finset.mem_filter.1 hq
      have hqS := hS q hqQ
      obtain ⟨hqm, hql⟩ := base_mem_domain hqS hqY
      exact ⟨(hqS.chosen.1 q rfl).1, hqm, hql⟩) hK
    have h2 := blockCount_fam (G := G) (m₀ := m₀) hN hϱ hL hY.2.2
    rw [← card_cellsOf] at h2
    unfold cubeCount
    calc (𝒬'.card : ℝ) ≤ _ := h1
      _ ≤ ((L ^ (K - j)) ^ d : ℕ) * ((L : ℝ) ^ (2 * d) * (3 ^ (d + 1) * L) *
            (treeLenCov G m₀ Y + 1)) := by gcongr
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    have := cubeCount_nonneg d L K j
    have := treeLenCov_nonneg G m₀ Y
    positivity

variable (G m₀ j c) in
/-- **The conclusion of Theorem 4.2** for the action cubes `𝒬` with cube differences `act`,
decoupled extensions `F`, rate `κ'` and bound constant `B`: (4.2) the expansion
`∑_b act b = b_k + ∑_T Δ(T)`, (4.3) the bound `|Δ(T)| ≤ B e^{-κ' d_Ω(T)}` (first bound), holomorphy
and locality of each `Δ(T)`. -/
def Expansion42 (𝒬 : Finset (CTorus d L N₁ m₁ K)) (Ω : Set (CTorus d L N₁ m₁ K))
    (κ' B : ℝ) (S : Set U) (act : CTorus d L N₁ m₁ K → U → ℂ)
    (F : CTorus d L N₁ m₁ K → U → (ι → ℂ) → ℂ)
    (AgY : Set (CTorus d L N₁ m₁ K) → U → U → Prop) : Prop :=
  (∀ u ∈ S, ∑ b ∈ 𝒬, act b u = emptyTraceTerm G m₀ j c 𝒬 Ω F u +
      ∑ T ∈ traceSetAll G m₀ j c 𝒬 Ω, traceTermAll G m₀ j c 𝒬 Ω F T u) ∧
  (∀ T ∈ traceSetAll G m₀ j c 𝒬 Ω, T.Nonempty ∧ dOmega m₀ K Ω T ≠ ⊤ ∧ ∀ u ∈ S,
    ‖traceTermAll G m₀ j c 𝒬 Ω F T u‖ ≤ B * Real.exp (-κ' * (dOmega m₀ K Ω T).toReal)) ∧
  (∀ T, AnalyticOnNhd ℂ (traceTermAll G m₀ j c 𝒬 Ω F T) S) ∧
  (∀ T, ∀ u ∈ S, ∀ u' ∈ S, (∀ b ∈ 𝒬, ∀ Y ∈ polymerDomains c G m₀
      (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K))), Y ∩ Ω = T → AgY Y u u') →
    traceTermAll G m₀ j c 𝒬 Ω F T u = traceTermAll G m₀ j c 𝒬 Ω F T u')

open Classical in
/-- **Theorem 4.2 (O-2′), undecoupled form, conditional on the decoupled weighted response.**

Let `𝒬` be a finite set of aligned action cubes `X_b = box b (L a_j)` with the localization
setups `CovSetup` (each cube lies in a `π'_K`-cube of `Λ_K`), `Ω ⊆ Λ_K`, and let
`R : DecoupledCubeResponse` be the decoupled cube differences `F b` with bound `C_b`
(`C_b = C_F' β r_H² e^{-γ_w D_k}` of Step 3).  For `κ ≥ 3` and `κ' ≥ 0` with
`a_ms + 2 ≤ 2κ - κ'`:

1. **(4.2)**: `∑_b act b u = b_k(u) + ∑_{T} Δ(T)(u)`, `T` over the traces `Y ∩ Ω ≠ ∅`;
2. **(4.3), first bound**: `|Δ(T)(u)| ≤ C_b c_cube K₀ e^{-κ' d_Ω(T)}` with `d_Ω(T) < ∞`;
3. each `Δ(T)` is holomorphic on `S`;
4. each `Δ(T)` is local: it depends on `u` only through the agreement relations `AgY` of the
   polymer domains with trace `T`. -/
theorem theorem42_of_input (𝒬 : Finset (CTorus d L N₁ m₁ K)) (Ω : Set (CTorus d L N₁ m₁ K))
    (hΩ : Ω ⊆ (G.layer K : Set (CTorus d L N₁ m₁ K)))
    (hϱ : (4 * d * L * (L : ℝ) ^ (m₀ + m₁) : ℝ) ≤ ϱ) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hS : ∀ b ∈ 𝒬, CovSetup G m₀ j (box b (L * cellSide L m₀ m₁ j)) {b})
    (hc : ∀ i, c i ∈ cubeIdx G) (hcinj : Function.Injective c)
    (hdisj : ∀ b ∈ 𝒬, ∀ i, Disjoint (Pset m₁ (c i))
      (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K))))
    {κ κ₁ Cb κ' : ℝ} (hκ : 3 ≤ κ)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κ ≤ κ₁)
    (h1 : 1 ≤ (κ₁ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2)
    (hCb : 0 ≤ Cb) (hκ'0 : 0 ≤ κ') (hκm : aMulti d L + 2 ≤ 2 * κ - κ')
    {S : Set U} {act : CTorus d L N₁ m₁ K → U → ℂ}
    {F : CTorus d L N₁ m₁ K → U → (ι → ℂ) → ℂ}
    {Ag : Finset ι → U → U → Prop} {AgY : Set (CTorus d L N₁ m₁ K) → U → U → Prop}
    (hrefl : ∀ C u, u ∈ S → Ag C u u)
    (hlink : ∀ b ∈ 𝒬, ∀ C u u',
      AgY (Ysites G m₀ c (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K))) C) u u' → Ag C u u')
    (R : DecoupledCubeResponse G m₀ j c 𝒬 S κ₁ Cb Ag act F) :
    Expansion42 G m₀ j c 𝒬 Ω κ' (Cb * cubeCount d L K j * K0Multi d L) S act F AgY := by
  have hL1 : 1 ≤ L := by omega
  -- per-cube applications of the localization expansion
  have hal : ∀ b ∈ 𝒬, Aligned (cellSide L m₀ m₁ j) b := fun b hb => (hS b hb).chosen.1 b rfl |>.1
  have hbd : ∀ b ∈ 𝒬, ∀ u ∈ S, ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁),
      ‖F b u s‖ ≤ Cb * Real.exp (-(κ - 1) * treeLenCovOne m₀ j
        (box b (L * cellSide L m₀ m₁ j))) := fun b hb u hu s hs => by
    rw [treeLenCovOne_box b (hal b hb)]; simpa using R.bound b hb u hu s hs
  have hexp : ∀ b ∈ 𝒬, _ := fun b hb => cube_expansion (c := c) (AgY := AgY) Ω (hS b hb) hd hL hc
    hcinj (hdisj b hb) (hopt_box b (hal b hb)) (κ₀ := 0) le_rfl (by linarith) hκ₁ h1 hlog hCb
    hrefl (hlink b hb) (R.analytic b hb) (hbd b hb) (R.loc b hb)
  have htr : ∀ b ∈ 𝒬, _ := fun b hb => cube_expansion_traces (c := c) (AgY := AgY) Ω hΩ hϱ (hS b hb)
    hd hL hc hcinj (hdisj b hb) (hopt_box b (hal b hb)) (κ₀ := 0) le_rfl (by linarith) hκ₁ h1 hlog
    hCb hκ'0 (by linarith) hrefl (hlink b hb) (R.analytic b hb) (hbd b hb) (R.loc b hb)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (4.2)
    intro u hu
    have hsum : ∀ b ∈ 𝒬, act b u = ∑ Y ∈ (polymerDomains c G m₀ (X1 G m₀ j
          ({b} : Set (CTorus d L N₁ m₁ K)))).filter (fun Y => Y ∩ Ω = ∅),
          evTerm c G m₀ (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K))) (F b) Y u +
        ∑ T ∈ traceSetAll G m₀ j c 𝒬 Ω, traceTerm c G m₀ (X1 G m₀ j
          ({b} : Set (CTorus d L N₁ m₁ K))) Ω (F b) T u := by
      intro b hb
      rw [← R.at_one b hb u hu, (htr b hb).1 u hu]
      congr 1
      refine Finset.sum_subset (fun T hT => ?_) fun T _ hT => ?_
      · exact Finset.mem_biUnion.2 ⟨b, hb, hT⟩
      exact traceTerm_eq_zero_of_not_mem hT u
    rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib, Finset.sum_comm]
    rfl
  · intro T hT
    obtain ⟨b₀, hb₀, hTb₀⟩ := Finset.mem_biUnion.1 hT
    obtain ⟨hTne, hdO, -⟩ := (htr b₀ hb₀).2.1 T hTb₀
    refine ⟨hTne, hdO, fun u hu => ?_⟩
    have hb₀S := hS b₀ hb₀
    have hK : 1 ≤ K := by have := hb₀S.hjK; omega
    have hN := hb₀S.hN
    set 𝓜 : Finset (Set (CTorus d L N₁ m₁ K)) := Finset.univ.filter
      (fun Y : Set (CTorus d L N₁ m₁ K) => IsMultiDom G m₀ Y ∧ Y ∩ Ω = T) with h𝓜
    set A : CTorus d L N₁ m₁ K → Finset (Set (CTorus d L N₁ m₁ K)) := fun b =>
      (meetingDomains c G m₀ (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K))) Ω).filter
        (fun Y => Y ∩ Ω = T) with hA
    have hMD : ∀ b ∈ 𝒬, ∀ Y ∈ polymerDomains c G m₀ (X1 G m₀ j
        ({b} : Set (CTorus d L N₁ m₁ K))), IsMultiDom G m₀ Y := fun b hb Y hY =>
      polymerDomain_isMultiDom c (hS b hb) hd (hc) (hopt_box b (hal b hb)) hY
    have hAsub : ∀ b ∈ 𝒬, A b ⊆ 𝓜 := by
      intro b hb Y hY
      obtain ⟨hYm, hYT⟩ := Finset.mem_filter.1 hY
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hMD b hb Y (Finset.mem_filter.1 hYm).1, hYT⟩
    have hev : ∀ b ∈ 𝒬, ∀ Y, ‖evTerm c G m₀ (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K)))
        (F b) Y u‖ ≤ Cb * Real.exp (-(2 * κ) * treeLenCov G m₀ Y) := by
      intro b hb Y
      have := (hexp b hb).2.2.1 Y u hu
      rw [treeLenCovOne_box b (hal b hb)] at this
      simpa using this
    set f : Set (CTorus d L N₁ m₁ K) → ℝ := fun Y => Cb * Real.exp (-(2 * κ) * treeLenCov G m₀ Y)
      with hf
    have hf0 : ∀ Y, 0 ≤ f Y := fun Y => mul_nonneg hCb (Real.exp_nonneg _)
    have step1 : ‖traceTermAll G m₀ j c 𝒬 Ω F T u‖ ≤ ∑ b ∈ 𝒬, ∑ Y ∈ A b, f Y := by
      unfold traceTermAll
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun Y _ => hev b hb Y)
    have step2 : ∑ b ∈ 𝒬, ∑ Y ∈ A b, f Y = ∑ Y ∈ 𝓜, ∑ b ∈ 𝒬, (if Y ∈ A b then f Y else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (hAsub b hb)]
    have step3 : ∀ Y ∈ 𝓜, ∑ b ∈ 𝒬, (if Y ∈ A b then f Y else 0) ≤
        Cb * cubeCount d L K j * Real.exp (-(2 * (κ - 1 / 2)) * treeLenCov G m₀ Y) := by
      intro Y hY
      obtain ⟨hYM, hYT⟩ := (Finset.mem_filter.1 hY).2
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hcard : ((𝒬.filter fun b => Y ∈ A b).card : ℝ) ≤ cubeCount d L K j *
          (treeLenCov G m₀ Y + 1) := by
        refine le_trans ?_ (card_cubes_domain (c := c) 𝒬 hS hϱ hL1 hYM)
        refine Nat.cast_le.2 (Finset.card_le_card fun b hb => ?_)
        obtain ⟨hbQ, hbA⟩ := Finset.mem_filter.1 hb
        exact Finset.mem_filter.2 ⟨hbQ, (Finset.mem_filter.1 (Finset.mem_filter.1 hbA).1).1⟩
      have ht0 := treeLenCov_nonneg G m₀ Y
      have hexp1 : treeLenCov G m₀ Y + 1 ≤ Real.exp (treeLenCov G m₀ Y) := by
        linarith [Real.add_one_le_exp (treeLenCov G m₀ Y)]
      have hcc := cubeCount_nonneg d L K j
      calc (𝒬.filter fun b => Y ∈ A b).card * f Y ≤ cubeCount d L K j *
            (treeLenCov G m₀ Y + 1) * f Y := mul_le_mul_of_nonneg_right hcard (hf0 Y)
        _ ≤ cubeCount d L K j * Real.exp (treeLenCov G m₀ Y) * f Y := by gcongr
        _ = Cb * cubeCount d L K j * (Real.exp (treeLenCov G m₀ Y) *
              Real.exp (-(2 * κ) * treeLenCov G m₀ Y)) := by simp only [hf]; ring
        _ = _ := by
          rw [← Real.exp_add]; congr 2; ring
    have hent := trace_entropy G m₀ hN hϱ hK hΩ hTne (κ := κ - 1 / 2) hκ'0 (by linarith)
    calc ‖traceTermAll G m₀ j c 𝒬 Ω F T u‖ ≤ _ := step1
      _ = _ := step2
      _ ≤ ∑ Y ∈ 𝓜, Cb * cubeCount d L K j *
            Real.exp (-(2 * (κ - 1 / 2)) * treeLenCov G m₀ Y) := by
          exact Finset.sum_le_sum step3
      _ = Cb * cubeCount d L K j * ∑ Y ∈ 𝓜,
            Real.exp (-(2 * (κ - 1 / 2)) * treeLenCov G m₀ Y) := by rw [Finset.mul_sum]
      _ ≤ Cb * cubeCount d L K j * (K0Multi d L * Real.exp (-κ' * (dOmega m₀ K Ω T).toReal)) := by
          exact mul_le_mul_of_nonneg_left hent (mul_nonneg hCb (cubeCount_nonneg d L K j))
      _ = _ := by ring
  · intro T
    unfold traceTermAll
    have := Finset.analyticOnNhd_sum 𝒬 fun b hb => (htr b hb).2.2.1 T
    convert this using 1
    funext u
    simp [Finset.sum_apply]
  · intro T u hu u' hu' hag
    unfold traceTermAll
    exact Finset.sum_congr rfl fun b hb => (htr b hb).2.2.2 T u hu u' hu' (hag b hb)

/-- **Theorem 4.2, (4.3) second bound, from the late threshold (Λ28′).**  In the setting of
`theorem42_of_input`, let the bound constant be `C_b ≤ C_F β r² e^{-γ_w D}` with the background
change at distance `D ≥ D'` from the cubes, `β ≤ C_L a⁻¹ e^x`, `r ≤ C_H α₀`, and assume the late
condition (Λ28′) with the constant `C_F c_cube K₀` and `3κ/2 ≤ κ'`.  Then every trace term satisfies
`|Δ(T)| ≤ e^{-R̂/2} e^{-(3/2) κ d_Ω(T)}`. -/
theorem theorem42_late_of_input (𝒬 : Finset (CTorus d L N₁ m₁ K)) (Ω : Set (CTorus d L N₁ m₁ K))
    (hΩ : Ω ⊆ (G.layer K : Set (CTorus d L N₁ m₁ K)))
    (hϱ : (4 * d * L * (L : ℝ) ^ (m₀ + m₁) : ℝ) ≤ ϱ) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hS : ∀ b ∈ 𝒬, CovSetup G m₀ j (box b (L * cellSide L m₀ m₁ j)) {b})
    (hc : ∀ i, c i ∈ cubeIdx G) (hcinj : Function.Injective c)
    (hdisj : ∀ b ∈ 𝒬, ∀ i, Disjoint (Pset m₁ (c i))
      (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K))))
    {κ κ₁ Cb κ' : ℝ} (hκ : 3 ≤ κ)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κ ≤ κ₁)
    (h1 : 1 ≤ (κ₁ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2)
    (hCb : 0 ≤ Cb) (hκ'0 : 0 ≤ κ') (hκm : aMulti d L + 2 ≤ 2 * κ - κ')
    {S : Set U} {act : CTorus d L N₁ m₁ K → U → ℂ}
    {F : CTorus d L N₁ m₁ K → U → (ι → ℂ) → ℂ}
    {Ag : Finset ι → U → U → Prop} {AgY : Set (CTorus d L N₁ m₁ K) → U → U → Prop}
    (hrefl : ∀ C u, u ∈ S → Ag C u u)
    (hlink : ∀ b ∈ 𝒬, ∀ C u u',
      AgY (Ysites G m₀ c (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K))) C) u u' → Ag C u u')
    (R : DecoupledCubeResponse G m₀ j c 𝒬 S κ₁ Cb Ag act F)
    {CF CH CL a α₀ β r γ D D' x Rh : ℝ} (hCF : 0 ≤ CF) (ha : 0 ≤ a) (hCL : 0 ≤ CL) (hr0 : 0 ≤ r)
    (hβ : β ≤ CL * a⁻¹ * Real.exp x) (hr : r ≤ CH * α₀) (hD : D' ≤ D) (hγ : 0 ≤ γ)
    (hCbF : Cb ≤ CF * β * r ^ 2 * Real.exp (-γ * D)) (hκ32 : 3 * κ / 2 ≤ κ')
    (hΛ : CF * cubeCount d L K j * K0Multi d L * CH ^ 2 * CL * a⁻¹ * α₀ ^ 2 * Real.exp x *
      Real.exp (-γ * D') ≤ Real.exp (-Rh / 2)) :
    ∀ T ∈ traceSetAll G m₀ j c 𝒬 Ω, ∀ u ∈ S, ‖traceTermAll G m₀ j c 𝒬 Ω F T u‖ ≤
      Real.exp (-Rh / 2) * Real.exp (-(3 / 2) * κ * (dOmega m₀ K Ω T).toReal) := by
  intro T hT u hu
  obtain ⟨-, hb, -, -⟩ := theorem42_of_input 𝒬 Ω hΩ hϱ hd hL hS hc hcinj hdisj hκ hκ₁ h1 hlog hCb
    hκ'0 hκm hrefl hlink R
  obtain ⟨-, -, hbT⟩ := hb T hT
  refine (hbT u hu).trans ?_
  have hcc := cubeCount_nonneg d L K j
  have hK0 := K0Multi_nonneg d L
  have hdd : 0 ≤ (dOmega m₀ K Ω T).toReal := ENNReal.toReal_nonneg
  have hsec := delta_second_bound (CF := CF * cubeCount d L K j * K0Multi d L) (CH := CH) (CL := CL)
    (a := a) (α₀ := α₀) (β := β) (r := r) (γ := γ) (D := D) (D' := D') (x := x) (κ := κ)
    (κ₀ := 2 * κ - 1 - κ') (d := (dOmega m₀ K Ω T).toReal) (Rh := Rh) (by positivity) ha hCL hr0 hβ hr
    hD hγ hdd (by linarith) (by
      calc _ = _ := by ring
        _ ≤ _ := hΛ)
  have e : -(2 * κ - 1 - (2 * κ - 1 - κ')) * (dOmega m₀ K Ω T).toReal =
      -κ' * (dOmega m₀ K Ω T).toReal := by ring
  rw [e] at hsec
  refine le_trans ?_ hsec
  have h3 : Cb * cubeCount d L K j * K0Multi d L ≤
      CF * cubeCount d L K j * K0Multi d L * β * r ^ 2 * Real.exp (-γ * D) := by
    calc Cb * cubeCount d L K j * K0Multi d L ≤ (CF * β * r ^ 2 * Real.exp (-γ * D)) *
          cubeCount d L K j * K0Multi d L := by gcongr
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)

/-- **Corollary 4.3 (P6 (2.12)–(2.17)), conditional on the same decoupled input.**  The two
background changes of P6 -- (2.12) `𝔹'_{k+1} → 𝔹_{k+1}(W_{k+1})` and (2.16)
`𝔹'_{k+1} → 𝔹_{k+1}(∂Ω_{k+1})` -- are two instances of the same theorem with their own decoupled
responses (their own bound constants `C_b`, i.e. margins of `W_{k+1}`, resp. of `W_k ∩ U_{k+1}`):
both produce the expansion (4.2) and the bound (4.3).  (The late bound of (4.3) for each instance is
`theorem42_late_of_input` with the corresponding margin `R̂`.) -/
theorem corollary43_of_input (𝒬 : Finset (CTorus d L N₁ m₁ K)) (Ω : Set (CTorus d L N₁ m₁ K))
    (hΩ : Ω ⊆ (G.layer K : Set (CTorus d L N₁ m₁ K)))
    (hϱ : (4 * d * L * (L : ℝ) ^ (m₀ + m₁) : ℝ) ≤ ϱ) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hS : ∀ b ∈ 𝒬, CovSetup G m₀ j (box b (L * cellSide L m₀ m₁ j)) {b})
    (hc : ∀ i, c i ∈ cubeIdx G) (hcinj : Function.Injective c)
    (hdisj : ∀ b ∈ 𝒬, ∀ i, Disjoint (Pset m₁ (c i))
      (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K))))
    {κ κ₁ κ' : ℝ} (hκ : 3 ≤ κ)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κ ≤ κ₁)
    (h1 : 1 ≤ (κ₁ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2)
    (hκ'0 : 0 ≤ κ') (hκm : aMulti d L + 2 ≤ 2 * κ - κ')
    {S : Set U} {Ag : Finset ι → U → U → Prop}
    {AgY : Set (CTorus d L N₁ m₁ K) → U → U → Prop}
    (hrefl : ∀ C u, u ∈ S → Ag C u u)
    (hlink : ∀ b ∈ 𝒬, ∀ C u u',
      AgY (Ysites G m₀ c (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K))) C) u u' → Ag C u u')
    {Cb₁ Cb₂ : ℝ} (hCb₁ : 0 ≤ Cb₁) (hCb₂ : 0 ≤ Cb₂)
    {act₁ act₂ : CTorus d L N₁ m₁ K → U → ℂ}
    {F₁ F₂ : CTorus d L N₁ m₁ K → U → (ι → ℂ) → ℂ}
    (R₁ : DecoupledCubeResponse G m₀ j c 𝒬 S κ₁ Cb₁ Ag act₁ F₁)
    (R₂ : DecoupledCubeResponse G m₀ j c 𝒬 S κ₁ Cb₂ Ag act₂ F₂) :
    Expansion42 G m₀ j c 𝒬 Ω κ' (Cb₁ * cubeCount d L K j * K0Multi d L) S act₁ F₁ AgY ∧
      Expansion42 G m₀ j c 𝒬 Ω κ' (Cb₂ * cubeCount d L K j * K0Multi d L) S act₂ F₂ AgY :=
  ⟨theorem42_of_input 𝒬 Ω hΩ hϱ hd hL hS hc hcinj hdisj hκ hκ₁ h1 hlog hCb₁ hκ'0 hκm hrefl hlink
      R₁,
    theorem42_of_input 𝒬 Ω hΩ hϱ hd hL hS hc hcinj hdisj hκ hκ₁ h1 hlog hCb₂ hκ'0 hκm hrefl hlink
      R₂⟩

end Main

section Partition

variable {B : Type*} {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

open Classical in
/-- **The cube actions of a partition into cubes add up to the action** (P5 (1.5), the cubes
`□ ∈ 𝒬` partition the lattice, half bonds on the star counted once). -/
theorem sum_cubeActionC_eq_actionC (𝒬 : Finset B) (Q : B → Finset (Torus d (N₀ * L ^ k)))
    (hpart : ∀ x, ∃! b, b ∈ 𝒬 ∧ x ∈ Q b) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    ∑ b ∈ 𝒬, cubeActionC G a ν (Q b) D φ = actionC G a ν D φ := by
  have key : ∀ (x : Torus d (N₀ * L ^ k)) (t : ℂ), ∑ b ∈ 𝒬, (if x ∈ Q b then t else 0) = t := by
    intro x t
    obtain ⟨b₀, ⟨hb₀, hx⟩, hu⟩ := hpart x
    rw [Finset.sum_eq_single b₀]
    · simp [hx]
    · intro b hb hne
      have : x ∉ Q b := fun h => hne (hu b ⟨hb, h⟩)
      simp [this]
    · intro h; exact absurd hb₀ h
  rw [← cubeActionC_univ]
  unfold cubeActionC cubeActionR
  simp only [Finset.mem_univ, ↓reduceIte, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  congr 1
  · congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => key _ _
  · congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => key _ _
  · congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => key _ _

/-- The left side of (4.2) for a partition into cubes: `∑_□ β F_□ = β (A(φ') - A(φ))`. -/
theorem sum_cubeDiff_eq_actionDiff (𝒬 : Finset B) (Q : B → Finset (Torus d (N₀ * L ^ k)))
    (hpart : ∀ x, ∃! b, b ∈ 𝒬 ∧ x ∈ Q b) (D : BgData G N) (φ φ' : G.Ω 1 × Fin N → ℂ) (β : ℂ) :
    ∑ b ∈ 𝒬, β * (cubeActionC G a ν (Q b) D φ' - cubeActionC G a ν (Q b) D φ) =
      β * (actionC G a ν D φ' - actionC G a ν D φ) := by
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_cubeActionC_eq_actionC 𝒬 Q hpart D φ',
    sum_cubeActionC_eq_actionC 𝒬 Q hpart D φ]

end Partition

end Balaban.Fluctuation
