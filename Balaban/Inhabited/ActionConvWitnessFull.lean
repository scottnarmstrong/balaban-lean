/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.CancelWitness
public import Balaban.LargeField.R.ActionConvWitness

/-!
# A non-degenerate inhabitant of `ActionConvInput` (hard rule 10) and of `window_conversion`

Instance (`PsiZeroWitness`): `d ≥ 3`, `L ≥ 3`, `N₀ = N₁ L^{m₁}`, torus level `K ≥ 1`, `N = 2`,
generating set `G = levelGS K` (every site has layer `K`, `Ω₁` = the whole torus), window
`k₁ = 0`, `k = 2` (so the steps are `j ∈ {0, 1}` and `j + 2 ≤ n ≤ 2` is nonempty for `j = 0`, `n = 2`).

* Regions: `X_0 = Xc 0 = ` the `K`-block of the origin (nonempty: `XR_zero_nonempty`; its boundary
  `st(X_0)` is nonempty when the torus has more than one block, not proved here), `X_1 = Xc 1 = ∅`.  `Xwin = X_0`.
* `StepDecomp` of `X_0`: one cube (`X_0`, weight `1`), one wall per crossing bond, `inc = |st(X_0)|`;
  so `mcount 0 = 1`.  `StepDecomp.empty` for `X_1`.
* Couplings: `β_n = L^{(d-2) n}` (the P4 form with `B = 1`, `g ≡ 1`, `η = 0`), `a_n = β_2 a / β_n`
  (`a = compWeight L 1`, admissible), `ν_n = β_2 / β_n` (nonzero), `e_n = 0`, so
  `coeff`, `mass` hold exactly; the branch is `massless` (the Euler-Lagrange mass is `0`; `ν_n ≠ 0`
  still enters the action and the counterterm).
* Data: `Ψ ≡ e₀` on `Ω₁ ∪ C`, `h ≡ 0`, backgrounds `φ_n ≡ e₀` (`unitPhi`), multiplier
  `α_n = bgMult` of the datum (independent of `n`); `IsEL` from `theorem71`.  The action is
  *not* zero on this datum: `h = 0` gives `A_X = (ν/2)|X|`, so `windowAction = Awin ≠ 0`.
* Everything else (`cost`, `bgRem`) vanishes because `φ_{n-1} = φ_n`, `Dat_{n-1} = Dat_n`,
  `e = 0`, `α` is independent of `n`, and `φ` is constant (`counterC_const`, `starPair_const`,
  `cost_eq_zero`, `bgRem_eq_zero`).

Results: `actionConvInput_full` (per-field comments in its doc-string), `window_conversion_full`
(generic `d ≥ 3`, `L ≥ 3`, `K ≥ 1`, any normed parameter space `S`), the concrete hypothesis-free
`window_conversion_witness`, `actionConvInput_witness` (`d = L = 3`, `N₁ = 6`, `m₁ = 0`, `K = 2`,
`S = ℂ`), and `windowAction_eq_Awin_ne_zero` (both sides are equal and nonzero, so `C = 0`).

## Findings (tension report)

* (i) No field of `ActionConvInput`, `WindowSetup`, `ConvChain`, `StepDecomp` is forced trivial or
  unsatisfiable once `X_0` is nonempty (`chainF`, `Wd`, `stepSingle` are the proofs).  Caveats:
  `el` is only required for `n ≥ j + 2`, so only `a_2` has to be admissible while `a_1 = L^{d-2} a_2`
  is not; the branch is `massless` so `el` does not see `ν_n` (we use `ν_n ≠ 0` only in the action).
  The estimates `cube_bound`, `wall_bound`, `p7_first`, `window_decay` are upper bounds and are
  met here because the quantities are `0`; the instance does not test their sharpness.
* (ii) `hflow` (`g ≡ 1`, `η = 0`, `B = 1`), `coeff` (`a_n = β_2 a / β_n`), `mass` (`ν_n = β_2/β_n`,
  `e_n = 0`, so `β_n ν_n` is constant) and `same_h` hold jointly with `ν_n ≠ 0`.
* (iii) `window_decay` holds with `γ_w = 1 > 0` and exponent `M (R̂ - 1) - 2 M₁ = 1 > 0`, but only
  because `bgRem = 0` identically (the scale-`k` window data coincide with the chain data); it is
  not tested as a decay statement.
* (iv) The conclusion is not `0 = 0 + 0` (`windowAction = Awin = β_2 |X_0| / 2 ≠ 0`), but `C ≡ 0`
  (`windowAction_eq_Awin_ne_zero`).  A nonzero `C` needs `cost ≠ 0` or `bgRem ≠ 0`: two different
  Euler-Lagrange configurations `φ_{n-1} ≠ φ_n` on a region with boundary (so `w̄ ≠ 0`; e.g. data
  `e₀` at one scale and a rotated constant `e₁` at the other, as in `CancelWitness`), or scale-`k`
  window data `(Datw, φw)` differing from `(Dat u k, φ u k)` on `X_j`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.Inhabited.ActionConvFull

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.LargeField
  Balaban.LargeField.ActionConv Balaban.SmallField Balaban.Inhabited Finset

section Data

variable (d L N₁ m₁ K : ℕ) [NeZero L] [NeZero N₁]

/-- The generating set `levelGS K` of the `PsiZeroWitness` instance. -/
noncomputable abbrev GG : GeneratingSet d L (N₁ * L ^ m₁) K (PsiZeroWitness.ϱ d L) :=
  PsiZeroWitness.G d L N₁ m₁ K

/-- The constant unit datum with `h = 0`. -/
noncomputable def Dd : BgData (GG d L N₁ m₁ K) 2 :=
  unitBg (GG d L N₁ m₁ K) PsiZeroWitness.hN2' (fun _ => 0)

/-- The constant background `φ ≡ e₀`. -/
noncomputable def phi : (GG d L N₁ m₁ K).Ω 1 × Fin 2 → ℂ :=
  unitPhi (GG d L N₁ m₁ K) PsiZeroWitness.hN2'

/-- The multiplier of the datum `Dd` for the weights `compWeight L 1`. -/
noncomputable def alphaF : (GG d L N₁ m₁ K).Ω 1 → ℂ :=
  bgMult (GG d L N₁ m₁ K) (compWeight L 1) 0 (Dd d L N₁ m₁ K)

/-- The couplings `β_n = L^{(d-2) n}`. -/
noncomputable def betaF (n : ℕ) : ℝ := (L : ℝ) ^ ((d - 2) * n)

/-- `a_n = β_2 a / β_n`. -/
noncomputable def aF (n : ℕ) (m : ℕ) : ℝ := betaF d L 2 * compWeight L 1 m / betaF d L n

/-- `ν_n = β_2 / β_n`. -/
noncomputable def nuF (n : ℕ) : ℝ := betaF d L 2 / betaF d L n

variable {d L N₁ m₁ K}

theorem betaF_pos (hL : 1 < L) (n : ℕ) : 0 < betaF d L n := by
  unfold betaF
  have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  positivity

theorem aF_two : aF d L 2 = compWeight L 1 := by
  funext m
  have : betaF d L 2 ≠ 0 := by
    unfold betaF
    have : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    positivity
  unfold aF
  field_simp

theorem nuF_two : nuF d L 2 = 1 := by
  have : betaF d L 2 ≠ 0 := by
    unfold betaF
    have : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    positivity
  unfold nuF
  field_simp

end Data

section Zero

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁]

theorem svec_zero' {G : GeneratingSet d L (N₁ * L ^ m₁) K (PsiZeroWitness.ϱ d L)} (y : Torus d (N₁ * L ^ m₁ * L ^ K))
    (i : Fin 2) : svec G (0 : G.Ω 1 × Fin 2 → ℂ) y i = 0 := by
  simp [svec, zeroExt]

theorem blockAvg_zero' {G : GeneratingSet d L (N₁ * L ^ m₁) K (PsiZeroWitness.ϱ d L)}
    (x : Torus d (N₁ * L ^ m₁ * L ^ K)) (i : Fin 2) :
    blockAvg G (0 : G.Ω 1 × Fin 2 → ℂ) x i = 0 := by
  simp [blockAvg, svec_zero']

theorem barField_const (hK : 1 ≤ K) (y : Torus d (N₁ * L ^ m₁ * L ^ K)) (i : Fin 2) :
    barField (GG d L N₁ m₁ K) (Dd d L N₁ m₁ K).Ψ (phi d L N₁ m₁ K) y i =
      (unitVec PsiZeroWitness.hN2' i : ℂ) :=
  barField_unit (PsiZeroWitness.isLevel_G hK) PsiZeroWitness.hN2' _ y i

theorem bondPair_const (hK : 1 ≤ K) (D : Region (GG d L N₁ m₁ K)) :
    D.bondPair (barField (GG d L N₁ m₁ K) (Dd d L N₁ m₁ K).Ψ (phi d L N₁ m₁ K))
      (barField (GG d L N₁ m₁ K) (Dd d L N₁ m₁ K).Ψ (phi d L N₁ m₁ K)) = 0 := by
  unfold Region.bondPair
  simp [barField_const hK]

theorem bulkDiv_const (hK : 1 ≤ K) (x : Torus d (N₁ * L ^ m₁ * L ^ K)) (i : Fin 2) :
    bulkDiv (Dd d L N₁ m₁ K) (phi d L N₁ m₁ K) x i = 0 := by
  unfold bulkDiv negLap
  simp only [barField_const hK]
  exact Finset.sum_eq_zero fun μ _ => by ring

/-- The counterterm vanishes on the constant configuration (`e = 0`). -/
theorem counterC_const (hK : 1 ≤ K) (D : Region (GG d L N₁ m₁ K)) (br : MassBranch) (a : ℕ → ℝ)
    (ν β b : ℝ) :
    counterC D a ν β b 0 (Dd d L N₁ m₁ K) (Dd d L N₁ m₁ K) (phi d L N₁ m₁ K) (phi d L N₁ m₁ K)
      (alphaF d L N₁ m₁ K) br = 0 := by
  have hw : wExt (Dd d L N₁ m₁ K) (Dd d L N₁ m₁ K) (phi d L N₁ m₁ K) (phi d L N₁ m₁ K) =
      fun _ _ => 0 := by
    funext x i; simp [wExt]
  have hdi : dataInc (Dd d L N₁ m₁ K) (Dd d L N₁ m₁ K) = fun _ _ => 0 := by
    funext x i; simp [dataInc]
  unfold counterC counterP counterQ counterR
  simp [hw, hdi, blockAvg_zero', bulkDiv_const hK, svec_zero', Region.blockPair,
    Region.massPair, Region.sitePair, Region.bondPair, barField_const hK]

theorem starPairOn_const (D : Region (GG d L N₁ m₁ K)) (B : Finset (Torus d (N₁ * L ^ m₁ * L ^ K) × Fin d))
    (f : Torus d (N₁ * L ^ m₁ * L ^ K) → Fin 2 → ℂ) :
    D.starPairOn B (wExt (Dd d L N₁ m₁ K) (Dd d L N₁ m₁ K) (phi d L N₁ m₁ K) (phi d L N₁ m₁ K)) f = 0 := by
  unfold Region.starPairOn wExt
  simp

end Zero

section Geometry

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁]

/-- The `K`-block of the sites above `z`, as a region (a cube of the generating set). -/
noncomputable def blockRegion (hK : 1 ≤ K) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - K))) :
    Region (GG d L N₁ m₁ K) where
  sites := Finset.univ.filter fun x => jBlock d L (N₁ * L ^ m₁) K K x = z
  sub_Ω := fun x _ => (PsiZeroWitness.isLevel_G hK x).1
  blockClosed := by
    intro x hx y hy
    have h1 := GeneratingSet.mem_blk.1 hy
    rw [(PsiZeroWitness.isLevel_G hK x).2] at h1
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact h1.trans hx

/-- The regions: `X_0 =` the block of the origin, `X_j = ∅` for `j ≥ 1`. -/
noncomputable def XR (hK : 1 ≤ K) : (j : ℕ) → Region (GG d L N₁ m₁ K)
  | 0 => blockRegion hK (jBlock d L (N₁ * L ^ m₁) K K (fun _ => 0))
  | _ + 1 => Region.bot

theorem XR_zero_nonempty (hK : 1 ≤ K) : (XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0).sites.Nonempty :=
  ⟨fun _ => 0, by simp [XR, blockRegion]⟩

/-- The one-cube decomposition of a region, with one wall per crossing bond. -/
noncomputable def stepSingle {G : GeneratingSet d L (N₁ * L ^ m₁) K (PsiZeroWitness.ϱ d L)}
    (X : Region G) : StepDecomp X where
  ι := Unit
  κ := {b // b ∈ X.crossing}
  cube := fun _ => X
  wt := fun _ => 1
  wt_nonneg := fun _ => zero_le_one
  cube_disj := fun i i' h => (h (Subsingleton.elim i i')).elim
  cube_union := by ext x; simp
  wall := fun q => {q.1}
  wall_disj := fun q q' h => by
    simp only [Finset.disjoint_singleton]
    exact fun e => h (Subtype.ext e)
  wall_union := by
    ext b
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hb => ⟨⟨b, hb⟩, rfl⟩, fun ⟨q, hq⟩ => hq ▸ q.2⟩
  wallCube := fun _ => ()
  inc := X.crossing.card
  inc_le := fun i => by
    calc _ ≤ (Finset.univ : Finset {b // b ∈ X.crossing}).card := Finset.card_filter_le _ _
      _ = X.crossing.card := by simp

theorem stepSingle_total {G : GeneratingSet d L (N₁ * L ^ m₁) K (PsiZeroWitness.ϱ d L)}
    (X : Region G) : (stepSingle X).total = 1 := by
  unfold StepDecomp.total
  show ∑ _i : Unit, (1 : ℝ) = 1
  simp

/-- The decompositions: `stepSingle` for `X_0`, the empty one for `X_j = ∅`. -/
noncomputable def DR (hK : 1 ≤ K) : (j : ℕ) → StepDecomp (XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK j)
  | 0 => stepSingle _
  | _ + 1 => StepDecomp.empty

end Geometry

section Chain

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁]

theorem isEL_const (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hK : 1 ≤ K) :
    IsEL (GG d L N₁ m₁ K) (compWeight L 1) 0 (Dd d L N₁ m₁ K) (phi d L N₁ m₁ K)
      (alphaF d L N₁ m₁ K) := by
  have hc1 : 0 < bgC1 d L 2 :=
    Balaban.Localization.bgC1_pos' (d := d) (L := L) (N := 2) (by omega)
  have hD : InUnionDomainR (GG d L N₁ m₁ K) (bgC1 d L 2) 0 (Dd d L N₁ m₁ K) := by
    unfold Dd
    rw [← dataR_constBlock]
    exact inUnionDomainR_of_tube _ hc1 le_rfl (tube_constBlock _ PsiZeroWitness.hN2' hc1 Set.univ)
  have h := (theorem71 (PsiZeroWitness.H (d := d) (L := L) (k := K) hd3 hL) hD).2.2.1.1
  have hb : bgField (GG d L N₁ m₁ K) (PsiZeroWitness.a L) 0 (Dd d L N₁ m₁ K) =
      phi d L N₁ m₁ K := PsiZeroWitness.bgField_unitW hd3 hL hK
  rw [hb] at h
  exact h

/-- The chain of the step `j` (all `n`, `u`): the constant configuration. -/
noncomputable def chainF {U : Type*} (S : Set U) (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hK : 1 ≤ K) (j : ℕ) :
    ConvChain S j 2 (GG d L N₁ m₁ K) (XR hK j) MassBranch.massless 2 where
  β := betaF d L
  a := aF d L
  ν := nuF d L
  e := fun _ => 0
  Dat := fun _ _ => Dd d L N₁ m₁ K
  φ := fun _ _ => phi d L N₁ m₁ K
  α := fun _ _ => alphaF d L N₁ m₁ K
  β_ne := fun n _ _ => (betaF_pos (by omega) n).ne'
  coeff := fun n _ _ m => by
    have h1 := (betaF_pos (d := d) (by omega : 1 < L) (n - 1)).ne'
    have h2 := (betaF_pos (d := d) (by omega : 1 < L) n).ne'
    unfold aF
    field_simp
  mass := fun n _ _ => by
    have h1 := (betaF_pos (d := d) (by omega : 1 < L) (n - 1)).ne'
    have h2 := (betaF_pos (d := d) (by omega : 1 < L) n).ne'
    unfold nuF
    field_simp
    ring
  same_h := fun _ _ _ _ _ _ _ => rfl
  el := fun n h1 h2 u _ => by
    have : n = 2 := by omega
    subst this
    show IsEL _ (aF d L 2) 0 _ _ _
    rw [aF_two]
    exact isEL_const hd3 hL hK
  unit := fun n _ _ u _ x => by
    have h := sum_sq_unitVec PsiZeroWitness.hN2'
    have e : ∑ i, (unitVec PsiZeroWitness.hN2' i : ℂ) * (unitVec PsiZeroWitness.hN2' i : ℂ) =
        ((∑ i, unitVec PsiZeroWitness.hN2' i ^ 2 : ℝ) : ℂ) := by
      push_cast; simp [sq]
    show ∑ i, (unitVec PsiZeroWitness.hN2' i : ℂ) * (unitVec PsiZeroWitness.hN2' i : ℂ) = 1
    rw [e, h]; simp

end Chain

section Window

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {U : Type*}

/-- **The window setup** (`k₁ = 0`, `k = 2`): the regions `X_0 =` block of the origin, `X_1 = ∅`;
`Gw = Gc j = levelGS K`; the scale-`2` data `(a_2, ν_2 = 1, β_2 = L^{2(d-2)})` with the constant
configuration. -/
noncomputable def Wd (S : Set U) (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hK : 1 ≤ K) :
    WindowSetup d L (N₁ * L ^ m₁) K 2 S 0 2 where
  ϱw := PsiZeroWitness.ϱ d L
  Gw := GG d L N₁ m₁ K
  Xw := XR hK
  Xwin := XR hK 0
  Xwin_sites := by
    ext x
    refine ⟨fun h => Finset.mem_biUnion.2 ⟨0, by simp, h⟩, fun h => ?_⟩
    obtain ⟨j, hj, hx⟩ := Finset.mem_biUnion.1 h
    have : j = 0 ∨ j = 1 := by simp at hj; omega
    rcases this with rfl | rfl
    · exact hx
    · simp [XR, Region.bot] at hx
  Xw_disj := by
    intro i hi j hj hij
    simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
    have : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Function.onFun, XR, Region.bot]
  ak := aF d L 2
  νk := nuF d L 2
  βk := betaF d L 2
  Datw := fun _ => Dd d L N₁ m₁ K
  φw := fun _ => phi d L N₁ m₁ K
  ϱc := fun _ => PsiZeroWitness.ϱ d L
  Gc := fun _ => GG d L N₁ m₁ K
  Xc := XR hK
  br := fun _ => MassBranch.massless
  chain := chainF S hd3 hL hK
  decomp := DR hK
  mcount := fun j => (DR hK j).total
  mcount_eq := fun _ => rfl

variable (S : Set U) (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hK : 1 ≤ K)

theorem starPair_const (D : Region (GG d L N₁ m₁ K))
    (f : Torus d (N₁ * L ^ m₁ * L ^ K) → Fin 2 → ℂ) :
    D.starPair (wExt (Dd d L N₁ m₁ K) (Dd d L N₁ m₁ K) (phi d L N₁ m₁ K) (phi d L N₁ m₁ K)) f = 0 := by
  unfold Region.starPair wExt
  simp

/-- **The cost vanishes** on the constant configuration: `φ_{n-1} = φ_n`, same data, `e = 0`. -/
theorem cost_eq_zero (j n : ℕ) (u : U) : ((Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).chain j).cost u n = 0 := by
  simp [ConvChain.cost, Wd, chainF, counterC_const hK, starPair_const]

/-- **The background replacement remainder vanishes**: the scale-`k` window action agrees with
`T_{j,k}` since the generating sets, regions, coefficients, data and fields coincide. -/
theorem bgRem_eq_zero (u : U) (j : ℕ) : (Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).bgRem u j = 0 := by
  simp [WindowSetup.bgRem, ConvChain.T, Wd, chainF]

theorem supBounds_zero' {V : ℝ} (hV : 0 ≤ V) :
    SupBounds (GG d L N₁ m₁ K) (0 : (GG d L N₁ m₁ K).Ω 1 × Fin 2 → ℂ) V := by
  refine ⟨fun y i => ?_, fun x _ μ i => ?_, fun x _ μ i => ?_, fun x _ i => ?_⟩ <;>
    simp [svec_zero', hV]

variable [NormedAddCommGroup U] [NormedSpace ℂ U]

/-- **`ActionConvInput` holds on the non-degenerate window** for every `ε`.  Constants:
`K_conv = K_bg = γ_w = c_C = c_W = 1`, `M = 3`, `M₁ = 1`, `R̂ ≡ 2` (so `M (R̂ - 1) - 2 M₁ = 1 > 0`),
`δ₁ ≡ 1`.  Per field (all `u`-independent, since the configuration is constant in `u`):
* `variational_bound`: `α_{n-1} - α_n = 0` and `φ_{n-1} - φ_n = 0` (same multiplier and field), so
  `Small`/`SupBounds` hold with `V = c_{K₂} > 0` because the quantities vanish;
* `analytic_T`, `analytic_win`: constant in `u`;
* `cube_bound`: `counterC` of every cube vanishes (`counterC_const`: `e = 0`, `φ_u = φ`, same data,
  constant field, so every pairing is of a zero field), and `c_C wt ≥ 0`;
* `wall_bound`: `starPairOn` of every wall vanishes since `w̄ = wExt = 0`, and `c_W wt ≥ 0`
  (the walls are the genuine crossing bonds of the block region `X_0`);
* `p7_first`: `cost = 0`, and the right side is a nonnegative product (`β > 0`, squares);
* `window_decay`: `bgRem = 0` (the same expression in `W.chain j` and `W`), and the right side
  `K_bg e^{-γ_w ⋯} mcount ≥ 0`. -/
theorem actionConvInput_full (ε : ℕ → ℝ) :
    Nonempty (ActionConvInput (Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)) 1 1 1 3 1 1 1 ε
      (fun _ => 2) (fun _ _ _ => 1)) := by
  have hV : 0 ≤ cK2 d L 2 * 1 := by have := cK2_pos d L 2; positivity
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro j _ n _ _ u _
    refine ⟨?_, ?_⟩
    · show Small (GG d L N₁ m₁ K) (alphaF d L N₁ m₁ K - alphaF d L N₁ m₁ K) (cK2 d L 2 * 1)
      intro x
      simpa using hV
    · show SupBounds (GG d L N₁ m₁ K) (phi d L N₁ m₁ K - phi d L N₁ m₁ K) (cK2 d L 2 * 1)
      rw [sub_self]
      exact supBounds_zero' hV
  · intro j _ n _ _
    have h : AnalyticOnNhd ℂ (fun _ : U => ((Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).chain j).T 0 n) S :=
      analyticOnNhd_const
    exact h
  · intro j _ n _ _ u _ i
    refine le_trans (le_of_eq ?_) (mul_nonneg zero_le_one
      (((Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).decomp j).wt_nonneg i))
    simp [Wd, chainF, counterC_const hK]
  · intro j _ n _ _ u _ q
    refine le_trans (le_of_eq ?_) (mul_nonneg zero_le_one
      (((Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).decomp j).wt_nonneg _))
    simp [Wd, chainF, starPairOn_const]
  · intro j _ n _ _ u _
    rw [cost_eq_zero, norm_zero]
    have hb : ∀ n, 0 ≤ ((Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).chain j).β n :=
      fun n => (betaF_pos (by omega) n).le
    exact mul_nonneg (mul_nonneg zero_le_one (div_nonneg (mul_nonneg (hb _) (sq_nonneg _))
      (mul_nonneg (hb _) (sq_nonneg _)))) ((Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).mcount_nonneg j)
  · intro j _ u _
    rw [bgRem_eq_zero, norm_zero]
    exact mul_nonneg (mul_nonneg zero_le_one (Real.exp_pos _).le)
      ((Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).mcount_nonneg j)
  · intro j _
    have h : AnalyticOnNhd ℂ (fun _ : U => ((Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).βk : ℂ) *
        actionRegionC ((Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).Xw j)
          (Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).ak (Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).νk
          ((Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).Datw 0)
          ((Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).φw 0)) S := analyticOnNhd_const
    exact h

/-- **`window_conversion` on the non-degenerate window**, constants `K_conv = K_bg = 1`, `η = 0`
(`g ≡ 1`, `B = 1`), `γ = α = (d - 2)/4`, `α₀ = 1`, `ε = epsSeq L α α₀`, `γ_w = 1`, `M = 3`, `M₁ = 1`,
`R̂ ≡ 2`.  All hypotheses of `window_conversion` are discharged: `hflow` (`β_n = L^{(d-2)n}`, so
`g ≡ 1`, compatible with `coeff` through `a_n = β_2 a / β_n`), `hε`, `hγα`, `hsep`. -/
theorem window_conversion_full :
    ∃ C : U → ℂ, (∀ u ∈ S, (Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).windowAction u =
        (Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).Awin u + C u) ∧ AnalyticOnNhd ℂ C S ∧
      ∀ u ∈ S, ‖C u‖ ≤ (9 * Real.exp (2 * 0) * 1 / (1 - (L : ℝ) ^ (-(2 * (((d : ℝ) - 2) / 4)))) + 1) *
        ∑ j ∈ Finset.Ico 0 2, (Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).mcount j := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd3
  exact window_conversion (actionConvInput_full S hd3 hL hK (epsSeq L (((d : ℝ) - 2) / 4) 1)).some
    (γ := ((d : ℝ) - 2) / 4) (η := 0) (α := ((d : ℝ) - 2) / 4) (α₀ := 1)
    (by omega) (by omega) (by linarith) one_pos rfl (by ring)
    (fun j _ => ⟨1, one_pos, fun _ => 1, fun _ => by simp, fun n _ _ => by
      simp [Wd, chainF, betaF]⟩)
    zero_le_one zero_le_one zero_le_one (fun j _ => by norm_num)

theorem sum_unit_sq : ∑ i, (unitVec PsiZeroWitness.hN2' i : ℂ) * (unitVec PsiZeroWitness.hN2' i : ℂ) = 1 := by
  have h := sum_sq_unitVec PsiZeroWitness.hN2'
  have e : ∑ i, (unitVec PsiZeroWitness.hN2' i : ℂ) * (unitVec PsiZeroWitness.hN2' i : ℂ) =
      ((∑ i, unitVec PsiZeroWitness.hN2' i ^ 2 : ℝ) : ℂ) := by
    push_cast; simp [sq]
  simp [e, h]

/-- **The action on the constant configuration is not zero**: with `h = 0`,
`A_D(a, ν; ψ, φ) = (ν/2) |D|`. -/
theorem actionRegionC_const (hK : 1 ≤ K) (D : Region (GG d L N₁ m₁ K)) (a : ℕ → ℝ) (ν : ℝ) :
    actionRegionC D a ν (Dd d L N₁ m₁ K) (phi d L N₁ m₁ K) = (ν : ℂ) / 2 * (D.sites.card : ℂ) := by
  have hG := PsiZeroWitness.isLevel_G (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK
  have h1 : ∀ x i, (Dd d L N₁ m₁ K).Ψ x i - blockAvg (GG d L N₁ m₁ K) (phi d L N₁ m₁ K) x i = 0 := by
    intro x i
    unfold Dd phi
    rw [blockAvg_unit hG, unitBg_Ψ_of_mem _ _ _ ((mem_dataSites _).2 (Or.inl (hG x).1)), sub_self]
  have h3 : ∀ x i, svec (GG d L N₁ m₁ K) (phi d L N₁ m₁ K) x i - (Dd d L N₁ m₁ K).h x i =
      (unitVec PsiZeroWitness.hN2' i : ℂ) := by
    intro x i
    unfold Dd phi
    rw [svec_unitPhi hG, unitBg_h_of_mem _ _ _ (hG x).1]
    simp
  unfold actionRegionC
  simp only [h1, h3, bondPair_const hK, Region.blockPair, Region.massPair, mul_zero, Finset.sum_const_zero,
    sum_unit_sq, Finset.sum_const, nsmul_eq_mul, mul_one, add_zero, zero_add]

/-- Sum of the mixed counts: `mcount 0 = 1`, `mcount 1 = 0`. -/
theorem mcount_sum : ∑ j ∈ Finset.Ico 0 2,
    (Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).mcount j = 1 := by
  have h0 : (Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).mcount 0 = 1 := stepSingle_total _
  have h1 : (Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).mcount 1 = 0 := by
    show (StepDecomp.empty (G := GG d L N₁ m₁ K)).total = 0
    exact Finset.sum_eq_zero fun i _ => (i : Empty).elim
  have : Finset.Ico 0 2 = {0, 1} := by decide
  rw [this, Finset.sum_pair (by norm_num), h0, h1]; norm_num

/-- **The window action is not zero** (`= β_2 |X_0| / 2 > 0`) and equals `Awin`: on this instance
the correction `C` of `window_conversion` is identically `0`, while both sides are nonzero. -/
theorem windowAction_eq_Awin_ne_zero (u : U) :
    (Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).windowAction u =
        (Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).Awin u ∧
      (Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).windowAction u ≠ 0 := by
  have hb : ∀ n, betaF d L n ≠ 0 := fun n => (betaF_pos (d := d) (by omega : 1 < L) n).ne'
  have hbC : ∀ n, (betaF d L n : ℂ) ≠ 0 := fun n => by exact_mod_cast hb n
  have hT : ∀ n : ℕ, ((chainF S hd3 hL hK (m₁ := m₁) (N₁ := N₁) 0).T u n) =
      (betaF d L n : ℂ) * ((nuF d L n : ℂ) / 2 * ((XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0).sites.card : ℂ)) :=
    fun n => by
      unfold ConvChain.T
      exact congrArg _ (actionRegionC_const hK _ _ _)
  have hcard : ((XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0).sites.card : ℂ) ≠ 0 := by
    exact_mod_cast (XR_zero_nonempty (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK).card_pos.ne'
  have hWA : (Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).windowAction u =
      (betaF d L 2 : ℂ) * ((nuF d L 2 : ℂ) / 2 *
        ((XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0).sites.card : ℂ)) := by
    unfold WindowSetup.windowAction
    exact congrArg _ (actionRegionC_const hK _ _ _)
  refine ⟨?_, ?_⟩
  · have e : Finset.Ico 0 2 = {0, 1} := by decide
    unfold WindowSetup.Awin
    rw [e, Finset.sum_pair (by norm_num), hWA]
    have h1 : ((Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).chain 0).T u 1 =
        (betaF d L 1 : ℂ) * ((nuF d L 1 : ℂ) / 2 *
          ((XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0).sites.card : ℂ)) := hT 1
    have h2 : ((Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁)).chain 1).T u 2 = 0 := by
      show (betaF d L 2 : ℂ) * actionRegionC (Region.bot : Region (GG d L N₁ m₁ K)) (aF d L 2)
        (nuF d L 2) (Dd d L N₁ m₁ K) (phi d L N₁ m₁ K) = 0
      rw [actionRegionC_bot, mul_zero]
    rw [h1, h2, add_zero]
    have h1' := hbC 1
    have h2' := hbC 2
    unfold nuF
    push_cast
    field_simp
  · rw [hWA]
    have : (nuF d L 2 : ℂ) = 1 := by rw [nuF_two]; simp
    rw [this]
    exact mul_ne_zero (hbC 2) (mul_ne_zero (by norm_num) hcard)

end Window

/-- **`window_conversion_witness`**: the window action theorem on the concrete instance
`d = L = 3`, `N₁ = 6`, `m₁ = 0`, torus level `K = 2`, window `[k₁, k) = [0, 2)`, parameter domain
`S = ℂ ⊂ ℂ`, `γ = α = 1/4`, `α₀ = 1`, `η = 0`, `K_conv = K_bg = 1`, `ε = epsSeq 3 (1/4) 1`.  Hypothesis-free. -/
theorem window_conversion_witness :
    ∃ C : ℂ → ℂ, (∀ u ∈ (Set.univ : Set ℂ),
        (Wd (Set.univ : Set ℂ) (d := 3) (L := 3) (N₁ := 6) (m₁ := 0) (K := 2) (by norm_num)
          (by norm_num) (by norm_num)).windowAction u =
        (Wd (Set.univ : Set ℂ) (d := 3) (L := 3) (N₁ := 6) (m₁ := 0) (K := 2) (by norm_num)
          (by norm_num) (by norm_num)).Awin u + C u) ∧
      AnalyticOnNhd ℂ C Set.univ ∧
      ∀ u ∈ (Set.univ : Set ℂ), ‖C u‖ ≤
        (9 * Real.exp (2 * 0) * 1 / (1 - ((3 : ℕ) : ℝ) ^ (-(2 * ((((3 : ℕ) : ℝ) - 2) / 4)))) + 1) *
        ∑ j ∈ Finset.Ico 0 2,
          (Wd (Set.univ : Set ℂ) (d := 3) (L := 3) (N₁ := 6) (m₁ := 0) (K := 2) (by norm_num)
            (by norm_num) (by norm_num)).mcount j :=
  window_conversion_full (U := ℂ) Set.univ (d := 3) (L := 3) (N₁ := 6) (m₁ := 0) (K := 2)
    (by norm_num) (by norm_num) (by norm_num)

/-- The input holds on the concrete instance. -/
theorem actionConvInput_witness (ε : ℕ → ℝ) :
    Nonempty (ActionConvInput (Wd (Set.univ : Set ℂ) (d := 3) (L := 3) (N₁ := 6) (m₁ := 0) (K := 2)
      (by norm_num) (by norm_num) (by norm_num)) 1 1 1 3 1 1 1 ε (fun _ => 2) (fun _ _ _ => 1)) :=
  actionConvInput_full (U := ℂ) Set.univ (d := 3) (L := 3) (N₁ := 6) (m₁ := 0) (K := 2)
    (by norm_num) (by norm_num) (by norm_num) ε

end Balaban.Inhabited.ActionConvFull
