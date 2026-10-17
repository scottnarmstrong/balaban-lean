/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ActionConvWitness

/-!
# The window setup indexed by the pieces of the window (W958, S3)

`notes/phase1/LF4R-PLAN.md` §9.3, item S3 (route A′).  The steps `j ∈ [k₁, k)` of a window have
several components each; the per-step data of `WindowSetup` are therefore indexed here by the
pieces `i = (j, P, c)` of the window, a finite type `ι` with the scale `sc i` of the step of the
piece.  The chain of conversions of a piece lives on the generating set of its own step (the local
family `G^{c}_{j+1}` of level `j + 1`), so the side `N₀c i` and the level `Kc i` of the generating
set depend on the piece.

* `PieceWindowSetup`: the typing data — the window generating set `Gw` with the regions `X_i` of
  the pieces and `X_win = ⊔_i X_i`, the scale-`k` data, and for every piece its generating set, its
  region, its chain of conversions from scale `sc i + 1` to `k`, its cube/wall decomposition and its
  mixed count;
* `PieceWindowSetup.nonempty`: hard rule 10 (one piece on the empty generating set, all named inputs
  of `window_conversion_pieces` hold);
* `window_conversion_pieces`: P631 (8)-(9) / LFR (2.15′) for the pieces, from the shared core
  `window_conversion_core`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.SmallField Finset

/-- **Typing data of the window, indexed by its pieces** (route A′ of `LF4R-PLAN.md` §9.3;
P631 §3, LFR Definition III.2.1, Lemma III.2.2): the window generating set `Gw` (`𝔹_{k₁,k}`) with
the regions `X_i` of the pieces `i ∈ ι` and `X_win = ⊔_i X_i`, the scale-`k` data `(ψ, φ_{k₁,k})`
at the points `u` of the parameter domain `S`, and for every piece `i` (of the step of scale
`sc i ∈ [k₁, k)`) the generating set `Gc i` of its step, the region `Xc i` (the same cubes on that
generating set), the chain of conversions from scale `sc i + 1` to `k`, the cube/wall
decomposition and the mixed count `|X_i|_{sc i + 1}`. -/
structure PieceWindowSetup (d L N₀ K N : ℕ) [NeZero N₀] [NeZero L] {U : Type*} (S : Set U)
    (ι : Type*) [Fintype ι] (sc : ι → ℕ) (k1 k : ℕ) where
  sc_mem : ∀ i, sc i ∈ Finset.Ico k1 k
  ϱw : ℝ
  Gw : GeneratingSet d L N₀ K ϱw
  Xw : ι → Region Gw
  Xwin : Region Gw
  Xwin_sites : Xwin.sites = Finset.univ.biUnion fun i => (Xw i).sites
  Xw_disj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint fun i => (Xw i).sites
  ak : ℕ → ℝ
  νk : ℝ
  βk : ℝ
  Datw : U → BgData Gw N
  φw : U → Gw.Ω 1 × Fin N → ℂ
  N₀c : ι → ℕ
  [neN₀c : ∀ i, NeZero (N₀c i)]
  Kc : ι → ℕ
  ϱc : ι → ℝ
  Gc : (i : ι) → GeneratingSet d L (N₀c i) (Kc i) (ϱc i)
  Xc : (i : ι) → Region (Gc i)
  br : ι → MassBranch
  chain : (i : ι) → ConvChain S (sc i) k (Gc i) (Xc i) (br i) N
  decomp : (i : ι) → StepDecomp (Xc i)
  mcount : ι → ℝ
  mcount_eq : ∀ i, mcount i = (decomp i).total

attribute [instance] PieceWindowSetup.neN₀c

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {U : Type*} {S : Set U} {ι : Type*} [Fintype ι]
  {sc : ι → ℕ} {k1 k : ℕ}

namespace PieceWindowSetup

variable (W : PieceWindowSetup d L N₀ K N S ι sc k1 k)

theorem mcount_nonneg (i : ι) : 0 ≤ W.mcount i := by
  rw [W.mcount_eq]; exact (W.decomp i).total_nonneg

include W in
theorem sc_lt (i : ι) : sc i < k := (Finset.mem_Ico.1 (W.sc_mem i)).2

/-- The window action is the sum of the actions of the pieces: `β_k A*_k(X_win) = ∑_i β_k A*_k(X_i)`
(additivity of the restricted action over the disjoint regions of the pieces). -/
theorem windowAction_eq_sum (u : U) :
    (W.βk : ℂ) * actionRegionC W.Xwin W.ak W.νk (W.Datw u) (W.φw u) =
      ∑ i, (W.βk : ℂ) * actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u) := by
  classical
  have hX : W.Xwin = Region.iUnion Finset.univ W.Xw := by
    ext1; exact W.Xwin_sites
  rw [hX, (Region.actionRegionC_additive W.ak W.νk (W.Datw u) (W.φw u)).iUnion
    Finset.univ W.Xw W.Xw_disj, Finset.mul_sum]

end PieceWindowSetup

variable [NormedAddCommGroup U] [NormedSpace ℂ U]

/-- **The window action theorem for the pieces** (P631 (8)-(9); LFR (2.15′); route A′ of
`LF4R-PLAN.md` §9.3): conditional on the named source estimates of `ActionConvInput` for the
chains of the pieces (`analytic_T`, `p7_first` (P7 (2.11), with the couplings `βs i n` of the
scales `n`, of the P4 (H.6) form `hflow`), `window_decay` (W) for the background replacement
remainder `T_{i,k} - β_k A*_k(X_i; ψ, φ_{k₁,k})`, `analytic_win`), on the window configurations of
the complex domain `S`,
`β_k A*_k(X_win, 𝔹_{k₁,k}; ψ, φ_{k₁,k}) = ∑_i T_{i, sc i + 1}(ψ) + C_{k₁,k}(ψ)` with `C_{k₁,k}`
analytic on `S` and `|C_{k₁,k}| ≤ C₁₅ ∑_i |X_i|_{sc i + 1}`,
`C₁₅ = 9 e^{2η} K_conv/(1 - L^{-2γ}) + K_bg` (the constant of `window_conversion`). -/
theorem window_conversion_pieces (W : PieceWindowSetup d L N₀ K N S ι sc k1 k)
    {Kconv Kbg γw M M₁ : ℝ} {ε Rhat : ℕ → ℝ} (βs : ι → ℕ → ℝ)
    (analytic_T : ∀ i, ∀ n, sc i + 1 ≤ n → n ≤ k →
      AnalyticOnNhd ℂ (fun u => (W.chain i).T u n) S)
    (p7_first : ∀ i, ∀ n, sc i + 2 ≤ n → n ≤ k → ∀ u ∈ S,
      ‖(W.chain i).cost u n‖ ≤ Kconv *
        ((βs i (sc i + 1) * ε (sc i + 1) ^ 2) / (βs i n * ε n ^ 2)) * W.mcount i)
    (window_decay : ∀ i, ∀ u ∈ S,
      ‖(W.chain i).T u k - (W.βk : ℂ) * actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)‖ ≤
        Kbg * Real.exp (-γw * (M * (Rhat (sc i - 1) - 1) - 2 * M₁)) * W.mcount i)
    (analytic_win : ∀ i,
      AnalyticOnNhd ℂ (fun u => (W.βk : ℂ) * actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)) S)
    {γ η α α₀ : ℝ} (hd : 2 ≤ d) (hL : 1 < L) (hγ : 0 < γ) (hα₀ : 0 < α₀)
    (hε : ε = epsSeq L α α₀) (hγα : (d : ℝ) - 2 - 2 * α = 2 * γ)
    (hflow : ∀ i, ∃ B : ℝ, 0 < B ∧ ∃ g : ℕ → ℝ,
      (∀ m, Real.exp (-η) ≤ g m ∧ g m ≤ Real.exp η) ∧
      ∀ n, sc i + 1 ≤ n → n ≤ k → βs i n = B * (L : ℝ) ^ ((d - 2) * n) * g n)
    (hKc : 0 ≤ Kconv) (hKb : 0 ≤ Kbg) (hγw : 0 ≤ γw)
    (hsep : ∀ i, 0 ≤ M * (Rhat (sc i - 1) - 1) - 2 * M₁) :
    ∃ C : U → ℂ,
      (∀ u ∈ S, (W.βk : ℂ) * actionRegionC W.Xwin W.ak W.νk (W.Datw u) (W.φw u) =
        ∑ i, (W.chain i).T u (sc i + 1) + C u) ∧ AnalyticOnNhd ℂ C S ∧
      ∀ u ∈ S, ‖C u‖ ≤ (9 * Real.exp (2 * η) * Kconv / (1 - (L : ℝ) ^ (-(2 * γ))) + Kbg) *
        ∑ i, W.mcount i := by
  obtain ⟨C, hC, hCa, hCb⟩ := window_conversion_core Finset.univ sc (fun i _ => PieceWindowSetup.sc_lt W i)
    W.chain (fun i u => (W.βk : ℂ) * actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u))
    W.mcount (fun i _ => W.mcount_nonneg i) βs (fun i _ => analytic_T i) (fun i _ => p7_first i)
    (fun i _ => window_decay i) (fun i _ => analytic_win i) hd hL hγ hα₀ hε hγα
    (fun i _ => hflow i) hKc hKb hγw (fun i _ => hsep i)
  exact ⟨C, fun u hu => by rw [W.windowAction_eq_sum u, hC u hu], hCa, hCb⟩

/-- **Inhabitation of `PieceWindowSetup`** (hard rule 10): one piece of scale `0` (`k₁ = 0`,
`k = 1`) on the empty generating set; for it the named inputs of `window_conversion_pieces` hold
(`p7_first` is vacuous, the background replacement remainder is `0`, all actions are `0`). -/
theorem PieceWindowSetup.nonempty (S : Set U) :
    ∃ W : PieceWindowSetup d L N₀ K N S Unit (fun _ => 0) 0 1,
      (∀ i, ∀ n, 0 + 1 ≤ n → n ≤ 1 → AnalyticOnNhd ℂ (fun u => (W.chain i).T u n) S) ∧
      (∀ i, ∀ u ∈ S, (W.chain i).T u 1 -
        (W.βk : ℂ) * actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u) = 0) ∧
      (∀ i, AnalyticOnNhd ℂ
        (fun u => (W.βk : ℂ) * actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)) S) := by
  let G : GeneratingSet d L N₀ K (0 : ℝ) := GeneratingSet.emptySet
  let W : PieceWindowSetup d L N₀ K N S Unit (fun _ => 0) 0 1 :=
    { sc_mem := fun _ => by simp
      ϱw := 0
      Gw := G
      Xw := fun _ => Region.bot
      Xwin := Region.bot
      Xwin_sites := by simp [Region.bot]
      Xw_disj := fun _ _ _ _ _ => by simp [Region.bot]
      ak := fun _ => 0
      νk := 0
      βk := 1
      Datw := fun _ => zeroData
      φw := fun _ => 0
      N₀c := fun _ => N₀
      neN₀c := fun _ => inferInstance
      Kc := fun _ => K
      ϱc := fun _ => 0
      Gc := fun _ => G
      Xc := fun _ => Region.bot
      br := fun _ => MassBranch.complete
      chain := fun _ =>
        { β := fun _ => 1
          a := fun _ _ => 0
          ν := fun _ => 0
          e := fun _ => 0
          Dat := fun _ _ => zeroData
          φ := fun _ _ => 0
          α := fun _ _ => 0
          β_ne := fun _ _ _ => one_ne_zero
          coeff := fun n h1 h2 => by omega
          mass := fun n h1 h2 => by omega
          same_h := fun n h1 h2 => by omega
          el := fun n h1 h2 => by omega
          unit := fun n h1 h2 => by omega }
      decomp := fun _ => StepDecomp.empty
      mcount := fun _ => 0
      mcount_eq := fun _ => (Finset.sum_eq_zero fun i _ => (i : Empty).elim).symm }
  have hA : ∀ (i : Unit) (u : U) (n : ℕ), (W.chain i).T u n = 0 := fun i u n => by
    simp [ConvChain.T, W, actionRegionC_bot]
  have hB : ∀ (i : Unit) (u : U),
      (W.βk : ℂ) * actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u) = 0 :=
    fun i u => by simp [W, actionRegionC_bot]
  refine ⟨W, fun i n _ _ => ?_, fun i u _ => by rw [hA, hB, sub_zero], fun i => ?_⟩
  · have : (fun u => (W.chain i).T u n) = fun _ => (0 : ℂ) := funext fun u => hA i u n
    rw [this]; exact analyticOnNhd_const
  · have : (fun u => (W.βk : ℂ) * actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)) =
        fun _ => (0 : ℂ) := funext fun u => hB i u
    rw [this]; exact analyticOnNhd_const

end Balaban.LargeField.ActionConv
