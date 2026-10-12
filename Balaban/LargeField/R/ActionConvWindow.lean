/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ActionConvChain
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The single-conversion estimate and the window action theorem (P631 §§2-3; LFR (2.15′))

Typing data.  `StepDecomp`: the decomposition of a region `X_j` into the P6 (2.31) cubes and of
`st(X_j)` into the `M`-cube walls, with the bounded wall-to-cube incidence (P631 §2 (L)).
`WindowSetup`: the generating sets, regions, scale-`k` data and the chains of conversions of the
steps `j ∈ [k₁, k)`.

The input `ActionConvInput` (ONE structure, fields = the named source estimates):
* (V) P2 Proposition 3.1: the bounds `‖w‖_*, |t|₂ ≤ K₂ δ₁` of the small solution and its analytic
  dependence on the datum (`variational_bound`, `analytic_T`);
* (L) P6 (2.25) cube bound and the wall estimate after (2.25) (`cube_bound`, `wall_bound`);
* P7 (2.11): `p7_first`, `p7_ratio`;
* (W) the window decay input, P7 (2.14) with P3 (2.55)-(2.56), P6 (2.13)-(2.14): `window_decay`,
  with the analyticity of the scale-`k` window action (`analytic_win`).

Theorems: `StepDecomp.cost_le` (the single-conversion bound
`|R_{j,n}| ≤ (c_C + c_W·inc) |X_j|`, from (L)); `window_conversion` ((8)-(9)).
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

namespace Region

variable {G : GeneratingSet d L N₀ K ϱ}

/-- The sum of `⟨w̄, ∂φ⟩` over a set `B` of crossing bonds. -/
noncomputable def starPairOn (D : Region G) (B : Finset (Torus d (N₀ * L ^ K) × Fin d))
    (w f : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℂ :=
  ∑ b ∈ B, ∑ i, ((w b.1 i + w (b.1 + Pi.single b.2 1) i) / 2) * D.outwardDeriv f b i

end Region

/-- **Cube and wall decomposition of a region** (P631 §2 (L)): `X` is the disjoint union of the
cubes `cube i` (each of mixed-count weight `wt i`), `st(X)` is the disjoint union of the walls
`wall w`, each wall charged to the cube `wallCube w`, at most `inc` walls per cube. -/
structure StepDecomp {G : GeneratingSet d L N₀ K ϱ} (X : Region G) where
  ι : Type
  κ : Type
  [fι : Fintype ι]
  [dι : DecidableEq ι]
  [fκ : Fintype κ]
  [dκ : DecidableEq κ]
  cube : ι → Region G
  wt : ι → ℝ
  wt_nonneg : ∀ i, 0 ≤ wt i
  cube_disj : Pairwise fun i i' => Disjoint (cube i).sites (cube i').sites
  cube_union : X.sites = Finset.univ.biUnion fun i => (cube i).sites
  wall : κ → Finset (Torus d (N₀ * L ^ K) × Fin d)
  wall_disj : Pairwise fun w w' => Disjoint (wall w) (wall w')
  wall_union : X.crossing = Finset.univ.biUnion wall
  wallCube : κ → ι
  inc : ℕ
  inc_le : ∀ i, (Finset.univ.filter fun w => wallCube w = i).card ≤ inc

namespace StepDecomp

attribute [instance] StepDecomp.fι StepDecomp.dι StepDecomp.fκ StepDecomp.dκ

variable {G : GeneratingSet d L N₀ K ϱ} {X : Region G} (Dc : StepDecomp X)

/-- The mixed cube count `|X|_{mix} = ∑ wt`. -/
noncomputable def total : ℝ := ∑ i, Dc.wt i

theorem total_nonneg : 0 ≤ Dc.total := Finset.sum_nonneg fun i _ => Dc.wt_nonneg i

theorem eq_iUnion : X = Region.iUnion Finset.univ Dc.cube := by
  ext1; exact Dc.cube_union

/-- Cube decomposition of any additive functional of the region. -/
theorem additive_sum {F : Region G → ℂ} (hF : Region.IsAdditive F) :
    F X = ∑ i, F (Dc.cube i) := by
  have h : F X = F (Region.iUnion Finset.univ Dc.cube) := congrArg F Dc.eq_iUnion
  rw [h, hF.iUnion _ _ (fun i _ i' _ h => Dc.cube_disj h)]

/-- Wall decomposition of the surface term. -/
theorem starPair_sum (w f : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    X.starPair w f = ∑ q, X.starPairOn (Dc.wall q) w f := by
  unfold Region.starPair Region.starPairOn
  rw [Dc.wall_union, Finset.sum_biUnion (fun q _ q' _ h => Dc.wall_disj h)]

/-- **The single-conversion estimate** (P631 §2): from the cube bounds and the wall bounds,
`‖c₁ C_X + c₂ S_X‖ ≤ (c_C + c_W · inc) · |X|_{mix}`. -/
theorem sum_le {cC cW : ℝ} (hcW : 0 ≤ cW) {c₁ c₂ : ℂ} (Cx : Region G → ℂ) (hC : Region.IsAdditive Cx)
    (S : Finset (Torus d (N₀ * L ^ K) × Fin d) → ℂ) (hS : S X.crossing = ∑ q, S (Dc.wall q))
    (hcube : ∀ i, ‖c₁ * Cx (Dc.cube i)‖ ≤ cC * Dc.wt i)
    (hwall : ∀ q, ‖c₂ * S (Dc.wall q)‖ ≤ cW * Dc.wt (Dc.wallCube q)) :
    ‖c₁ * Cx X + c₂ * S X.crossing‖ ≤ (cC + cW * Dc.inc) * Dc.total := by
  have h1 : ‖c₁ * Cx X‖ ≤ cC * Dc.total := by
    rw [Dc.additive_sum hC, Finset.mul_sum]
    unfold StepDecomp.total
    rw [Finset.mul_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hcube i)
  have h2 : ‖c₂ * S X.crossing‖ ≤ cW * Dc.inc * Dc.total := by
    rw [hS, Finset.mul_sum]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun q _ => hwall q).trans ?_)
    rw [← Finset.mul_sum]
    have hfib : ∑ q, Dc.wt (Dc.wallCube q) =
        ∑ i, ((Finset.univ.filter fun q => Dc.wallCube q = i).card : ℝ) * Dc.wt i := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := Dc.wallCube) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_congr rfl (g := fun _ => Dc.wt i) (fun q hq => by
        rw [(Finset.mem_filter.1 hq).2]), Finset.sum_const, nsmul_eq_mul]
    have hle : ∑ q, Dc.wt (Dc.wallCube q) ≤ Dc.inc * Dc.total := by
      rw [hfib]
      unfold StepDecomp.total
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (by exact_mod_cast Dc.inc_le i) (Dc.wt_nonneg i)
    calc cW * ∑ q, Dc.wt (Dc.wallCube q) ≤ cW * (Dc.inc * Dc.total) :=
          mul_le_mul_of_nonneg_left hle hcW
      _ = cW * Dc.inc * Dc.total := by ring
  calc _ ≤ ‖c₁ * Cx X‖ + ‖c₂ * S X.crossing‖ := norm_add_le _ _
    _ ≤ cC * Dc.total + cW * Dc.inc * Dc.total := add_le_add h1 h2
    _ = _ := by ring

end StepDecomp

/-- The geometric sum `∑_{n=j+2}^{j+1+m} q^{n-j-1} = (q - q^{m+1})/(1 - q)`. -/
theorem geom_Ioc (q : ℝ) (j : ℕ) (m : ℕ) :
    (∑ n ∈ Finset.Ioc (j + 1) (j + 1 + m), q ^ (n - j - 1)) * (1 - q) = q - q ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show j + 1 + (m + 1) = (j + 1 + m) + 1 by ring,
      Finset.sum_Ioc_succ_top (by omega)]
    have e : j + 1 + m + 1 - j - 1 = m + 1 := by omega
    rw [e, add_mul, ih]
    ring

theorem geom_Ioc_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (j k : ℕ) :
    ∑ n ∈ Finset.Ioc (j + 1) k, q ^ (n - j - 1) ≤ 1 / (1 - q) := by
  have hpos : 0 < 1 - q := by linarith
  rcases le_or_gt k (j + 1) with h | h
  · rw [Finset.Ioc_eq_empty_of_le h]
    simp only [Finset.sum_empty]
    positivity
  · obtain ⟨m, rfl⟩ : ∃ m, k = j + 1 + m := ⟨k - (j + 1), by omega⟩
    have := geom_Ioc q j m
    rw [le_div_iff₀ hpos, this]
    have : 0 ≤ q ^ (m + 1) := pow_nonneg hq0 _
    linarith

section Window

/-- **Typing data of the window** (P631 §3; LFR Definition III.2.1, Lemma III.2.2): the window
generating set `Gw` (`𝔹_{k₁,k}`) with the regions `X_j` and `X_win = ⊔ X_j`, the scale-`k` data
`(ψ, φ_{k₁,k})` at the points `u` of the parameter domain `S`, and for every step `j` the generating
set `Gc j`, the region `Xc j` (the same cubes on the step's generating set), the chain of
conversions, the cube/wall decomposition and the mixed count `|X_j|_{j+1}`. -/
structure WindowSetup (d L N₀ K N : ℕ) [NeZero N₀] [NeZero L] {U : Type*} (S : Set U)
    (k1 k : ℕ) where
  ϱw : ℝ
  Gw : GeneratingSet d L N₀ K ϱw
  Xw : ℕ → Region Gw
  Xwin : Region Gw
  Xwin_sites : Xwin.sites = (Finset.Ico k1 k).biUnion fun j => (Xw j).sites
  Xw_disj : ((Finset.Ico k1 k : Finset ℕ) : Set ℕ).PairwiseDisjoint fun j => (Xw j).sites
  ak : ℕ → ℝ
  νk : ℝ
  βk : ℝ
  Datw : U → BgData Gw N
  φw : U → Gw.Ω 1 × Fin N → ℂ
  ϱc : ℕ → ℝ
  Gc : (j : ℕ) → GeneratingSet d L N₀ K (ϱc j)
  Xc : (j : ℕ) → Region (Gc j)
  br : ℕ → MassBranch
  chain : (j : ℕ) → ConvChain S j k (Gc j) (Xc j) (br j) N
  decomp : (j : ℕ) → StepDecomp (Xc j)
  mcount : ℕ → ℝ
  mcount_eq : ∀ j, mcount j = (decomp j).total

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {U : Type*} {S : Set U} {k1 k : ℕ}
  (W : WindowSetup d L N₀ K N S k1 k)

namespace WindowSetup

theorem mcount_nonneg (j : ℕ) : 0 ≤ W.mcount j := by
  rw [W.mcount_eq]; exact (W.decomp j).total_nonneg

/-- `β_k A*_k(X_win, 𝔹_{k₁,k}; ψ, φ_{k₁,k})`. -/
noncomputable def windowAction (u : U) : ℂ :=
  (W.βk : ℂ) * actionRegionC W.Xwin W.ak W.νk (W.Datw u) (W.φw u)

/-- `𝒜_{win}(ψ) = ∑_j 𝒜_{j+1}(X_j; ψ)`, `𝒜_{j+1}(X_j;ψ) = T_{j,j+1}` the original step action. -/
noncomputable def Awin (u : U) : ℂ := ∑ j ∈ Finset.Ico k1 k, (W.chain j).T u (j + 1)

/-- The background replacement remainder `B_j = T_{j,k} - β_k A*_k(X_j; ψ, φ_{k₁,k})`. -/
noncomputable def bgRem (u : U) (j : ℕ) : ℂ :=
  (W.chain j).T u k -
    (W.βk : ℂ) * actionRegionC (W.Xw j) W.ak W.νk (W.Datw u) (W.φw u)

theorem windowAction_eq_sum (u : U) :
    W.windowAction u = ∑ j ∈ Finset.Ico k1 k,
      (W.βk : ℂ) * actionRegionC (W.Xw j) W.ak W.νk (W.Datw u) (W.φw u) := by
  unfold windowAction
  have hX : W.Xwin = Region.iUnion (Finset.Ico k1 k) W.Xw := by
    ext1; exact W.Xwin_sites
  rw [hX, (Region.actionRegionC_additive W.ak W.νk (W.Datw u) (W.φw u)).iUnion
    (Finset.Ico k1 k) W.Xw W.Xw_disj, Finset.mul_sum]

end WindowSetup

variable [NormedAddCommGroup U] [NormedSpace ℂ U]
  (Kconv γ Kbg γw M M₁ cC cW : ℝ) (ε Rhat : ℕ → ℝ) (δ₁ : ℕ → ℕ → U → ℝ)

/-- **The input of the action conversion** (ONE structure; fields = the named source estimates).

* `variational_bound`, `analytic_T`: (V), P2 Proposition 3.1 (3.47) for the P6 (2.24) solution
  `(w, t) = (φ_{n-1} - φ_n, α_{n-1} - α_n)` and the analytic dependence of the converted actions;
* `cube_bound`: P6 (2.25) for the cube terms of `β_n C_X`; `wall_bound`: the wall estimate after
  (2.25) for the walls of `β_{n-1} S_X`;
* `p7_first`, `p7_ratio`: P7 (2.11), the cost `R_{j,n}` and the running-radius bound;
* `window_decay`: (W) (7), the background replacement remainder, `analytic_win`: analyticity of the
  scale-`k` window action on the complex domain `S` (P5 (1.32)). -/
structure ActionConvInput : Prop where
  variational_bound : ∀ j ∈ Finset.Ico k1 k, ∀ n, j + 2 ≤ n → n ≤ k → ∀ u ∈ S,
    Small (W.Gc j) ((W.chain j).α u (n - 1) - (W.chain j).α u n) (cK2 d L N * δ₁ j n u) ∧
    SupBounds (W.Gc j) ((W.chain j).φ u (n - 1) - (W.chain j).φ u n) (cK2 d L N * δ₁ j n u)
  analytic_T : ∀ j ∈ Finset.Ico k1 k, ∀ n, j + 1 ≤ n → n ≤ k →
    AnalyticOnNhd ℂ (fun u => (W.chain j).T u n) S
  cube_bound : ∀ j ∈ Finset.Ico k1 k, ∀ n, j + 2 ≤ n → n ≤ k → ∀ u ∈ S, ∀ i,
    ‖((W.chain j).β n : ℂ) * counterC ((W.decomp j).cube i) ((W.chain j).a n) ((W.chain j).ν n)
        ((W.chain j).β n) ((W.chain j).β (n - 1) - (W.chain j).β n) ((W.chain j).e n)
        ((W.chain j).Dat u n) ((W.chain j).Dat u (n - 1)) ((W.chain j).φ u n)
        ((W.chain j).φ u (n - 1)) ((W.chain j).α u n) (W.br j)‖ ≤ cC * (W.decomp j).wt i
  wall_bound : ∀ j ∈ Finset.Ico k1 k, ∀ n, j + 2 ≤ n → n ≤ k → ∀ u ∈ S, ∀ q,
    ‖((W.chain j).β (n - 1) : ℂ) * (W.Xc j).starPairOn ((W.decomp j).wall q)
        (wExt ((W.chain j).Dat u n) ((W.chain j).Dat u (n - 1)) ((W.chain j).φ u n)
          ((W.chain j).φ u (n - 1)))
        (barField (W.Gc j) ((W.chain j).Dat u n).Ψ ((W.chain j).φ u n))‖ ≤
      cW * (W.decomp j).wt ((W.decomp j).wallCube q)
  p7_first : ∀ j ∈ Finset.Ico k1 k, ∀ n, j + 2 ≤ n → n ≤ k → ∀ u ∈ S,
    ‖(W.chain j).cost u n‖ ≤ Kconv *
      (((W.chain j).β (j + 1) * ε (j + 1) ^ 2) / ((W.chain j).β n * ε n ^ 2)) * W.mcount j
  p7_ratio : ∀ j ∈ Finset.Ico k1 k, ∀ n, j + 2 ≤ n → n ≤ k →
    ((W.chain j).β (j + 1) * ε (j + 1) ^ 2) / ((W.chain j).β n * ε n ^ 2) ≤
      ((L : ℝ) ^ (-(2 * γ))) ^ (n - j - 1)
  window_decay : ∀ j ∈ Finset.Ico k1 k, ∀ u ∈ S,
    ‖W.bgRem u j‖ ≤ Kbg * Real.exp (-γw * (M * (Rhat (j - 1) - 1) - 2 * M₁)) * W.mcount j
  analytic_win : ∀ j ∈ Finset.Ico k1 k,
    AnalyticOnNhd ℂ (fun u => (W.βk : ℂ) * actionRegionC (W.Xw j) W.ak W.νk (W.Datw u) (W.φw u)) S

variable {W Kconv γ Kbg γw M M₁ cC cW ε Rhat δ₁}

/-- **The single-conversion estimate** (P631 §2, "the sum is bounded by a fixed constant times
`|D ∩ Ω_r^c|_η + |D ∩ Ω_r|`"): from the cube bounds and the wall bounds,
`|R_{j,n}| ≤ (c_C + c_W · inc) |X_j|_{j+1}`. -/
theorem ActionConvInput.cost_le (I : ActionConvInput W Kconv γ Kbg γw M M₁ cC cW ε Rhat δ₁)
    (hcW : 0 ≤ cW) {j : ℕ} (hj : j ∈ Finset.Ico k1 k) {n : ℕ} (hn2 : j + 2 ≤ n) (hnk : n ≤ k)
    {u : U} (hu : u ∈ S) :
    ‖(W.chain j).cost u n‖ ≤ (cC + cW * (W.decomp j).inc) * W.mcount j := by
  set C := W.chain j
  have key := (W.decomp j).sum_le (cC := cC) (cW := cW) hcW
    (c₁ := (C.β n : ℂ)) (c₂ := (C.β (n - 1) : ℂ))
    (fun D => counterC D (C.a n) (C.ν n) (C.β n) (C.β (n - 1) - C.β n) (C.e n) (C.Dat u n)
      (C.Dat u (n - 1)) (C.φ u n) (C.φ u (n - 1)) (C.α u n) (W.br j))
    (Region.counterC_additive _ _ _ _ _ _ _ _ _ _ _)
    (fun B => (W.Xc j).starPairOn B (wExt (C.Dat u n) (C.Dat u (n - 1)) (C.φ u n) (C.φ u (n - 1)))
      (barField (W.Gc j) (C.Dat u n).Ψ (C.φ u n)))
    ((W.decomp j).starPair_sum _ _)
    (fun i => I.cube_bound j hj n hn2 hnk u hu i)
    (fun q => I.wall_bound j hj n hn2 hnk u hu q)
  rw [W.mcount_eq]
  exact key

/-- **The window action theorem** (P631 (8)-(9); LFR (2.15′)): conditional on the input
`ActionConvInput`, on the window configurations in the complex domain `S`,
`β_k A*_k(X_win, 𝔹_{k₁,k}; ψ, φ_{k₁,k}) = 𝒜_win(ψ) + C_{k₁,k}(ψ)` with `C_{k₁,k}` analytic on `S`
and `|C_{k₁,k}| ≤ C₁₅ ∑_j |X_j|_{j+1}`, `C₁₅ = K_conv/(1 - L^{-2γ}) + K_bg`.  The constant `C₁₅`
is a function of `K_conv, K_bg, L, γ` only. -/
theorem window_conversion (I : ActionConvInput W Kconv γ Kbg γw M M₁ cC cW ε Rhat δ₁)
    (hL : 1 < L) (hγ : 0 < γ) (hKc : 0 ≤ Kconv) (hKb : 0 ≤ Kbg) (hγw : 0 ≤ γw)
    (hsep : ∀ j ∈ Finset.Ico k1 k, 0 ≤ M * (Rhat (j - 1) - 1) - 2 * M₁) :
    ∃ C : U → ℂ, (∀ u ∈ S, W.windowAction u = W.Awin u + C u) ∧ AnalyticOnNhd ℂ C S ∧
      ∀ u ∈ S, ‖C u‖ ≤ (Kconv / (1 - (L : ℝ) ^ (-(2 * γ))) + Kbg) *
        ∑ j ∈ Finset.Ico k1 k, W.mcount j := by
  set q : ℝ := (L : ℝ) ^ (-(2 * γ)) with hq
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by linarith) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith)
  refine ⟨fun u => W.windowAction u - W.Awin u, fun u _ => by ring, ?_, ?_⟩
  · have h1 : AnalyticOnNhd ℂ W.windowAction S := by
      have : W.windowAction = ∑ j ∈ Finset.Ico k1 k, fun u =>
          (W.βk : ℂ) * actionRegionC (W.Xw j) W.ak W.νk (W.Datw u) (W.φw u) := by
        funext u
        rw [W.windowAction_eq_sum u, Finset.sum_apply]
      rw [this]
      exact Finset.analyticOnNhd_sum _ fun j hj => I.analytic_win j hj
    have h2 : AnalyticOnNhd ℂ W.Awin S := by
      have : W.Awin = ∑ j ∈ Finset.Ico k1 k, fun u => (W.chain j).T u (j + 1) := by
        funext u
        rw [Finset.sum_apply]; rfl
      rw [this]
      exact Finset.analyticOnNhd_sum _ fun j hj =>
        I.analytic_T j hj (j + 1) le_rfl (by have := (Finset.mem_Ico.1 hj).2; omega)
    exact h1.sub h2
  · intro u hu
    -- the per-step identity
    have hstep : ∀ j ∈ Finset.Ico k1 k,
        (W.βk : ℂ) * actionRegionC (W.Xw j) W.ak W.νk (W.Datw u) (W.φw u) - (W.chain j).T u (j + 1) =
          -(∑ n ∈ Finset.Ioc (j + 1) k, (W.chain j).cost u n + W.bgRem u j) := by
      intro j hj
      have hjk := (Finset.mem_Ico.1 hj).2
      have := (W.chain j).telescope hu (m := k) (by omega) le_rfl
      unfold WindowSetup.bgRem
      linear_combination -this
    have hsum : W.windowAction u - W.Awin u = -∑ j ∈ Finset.Ico k1 k,
        (∑ n ∈ Finset.Ioc (j + 1) k, (W.chain j).cost u n + W.bgRem u j) := by
      rw [W.windowAction_eq_sum u]
      unfold WindowSetup.Awin
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl hstep
    have hnorm : ∀ j ∈ Finset.Ico k1 k,
        ‖∑ n ∈ Finset.Ioc (j + 1) k, (W.chain j).cost u n + W.bgRem u j‖ ≤
          (Kconv / (1 - q) + Kbg) * W.mcount j := by
      intro j hj
      have hjk := (Finset.mem_Ico.1 hj).2
      have hm := W.mcount_nonneg j
      have hcost : ∀ n ∈ Finset.Ioc (j + 1) k, ‖(W.chain j).cost u n‖ ≤ Kconv * q ^ (n - j - 1) * W.mcount j := by
        intro n hn
        obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.1 hn
        calc ‖(W.chain j).cost u n‖ ≤ _ := I.p7_first j hj n (by omega) hn2 u hu
          _ ≤ Kconv * q ^ (n - j - 1) * W.mcount j := by
            apply mul_le_mul_of_nonneg_right _ hm
            exact mul_le_mul_of_nonneg_left (I.p7_ratio j hj n (by omega) hn2) hKc
      have h1 : ‖∑ n ∈ Finset.Ioc (j + 1) k, (W.chain j).cost u n‖ ≤ Kconv / (1 - q) * W.mcount j := by
        refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hcost).trans ?_)
        have : ∑ n ∈ Finset.Ioc (j + 1) k, Kconv * q ^ (n - j - 1) * W.mcount j =
            Kconv * W.mcount j * ∑ n ∈ Finset.Ioc (j + 1) k, q ^ (n - j - 1) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n _ => by ring
        rw [this]
        have hg := geom_Ioc_le hq0.le hq1 j k
        calc Kconv * W.mcount j * ∑ n ∈ Finset.Ioc (j + 1) k, q ^ (n - j - 1)
            ≤ Kconv * W.mcount j * (1 / (1 - q)) :=
              mul_le_mul_of_nonneg_left hg (mul_nonneg hKc hm)
          _ = Kconv / (1 - q) * W.mcount j := by ring
      have h2 : ‖W.bgRem u j‖ ≤ Kbg * W.mcount j := by
        refine (I.window_decay j hj u hu).trans ?_
        have : Real.exp (-γw * (M * (Rhat (j - 1) - 1) - 2 * M₁)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          nlinarith [hsep j hj]
        calc Kbg * Real.exp (-γw * (M * (Rhat (j - 1) - 1) - 2 * M₁)) * W.mcount j
            ≤ Kbg * 1 * W.mcount j := by
              apply mul_le_mul_of_nonneg_right _ hm
              exact mul_le_mul_of_nonneg_left this hKb
          _ = Kbg * W.mcount j := by ring
      calc _ ≤ ‖∑ n ∈ Finset.Ioc (j + 1) k, (W.chain j).cost u n‖ + ‖W.bgRem u j‖ := norm_add_le _ _
        _ ≤ Kconv / (1 - q) * W.mcount j + Kbg * W.mcount j := add_le_add h1 h2
        _ = _ := by ring
    show ‖W.windowAction u - W.Awin u‖ ≤ _
    rw [hsum, norm_neg]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hnorm).trans ?_)
    rw [Finset.mul_sum]

end Window

end Balaban.LargeField.ActionConv
