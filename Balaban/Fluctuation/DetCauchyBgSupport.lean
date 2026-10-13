/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCauchyChart
public import Balaban.Fluctuation.DetCauchyGraph
public import Balaban.Fluctuation.ExpansionQuad
public import Balaban.Localization.RowsBg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Support of the rooted trace expansion with cut-dependent backgrounds

For a datum `D` of the chart and cut parameters `s`, `rootTraceBg B D s` is the rooted trace of the
block set `B` at the decoupled background `(φ_s, α_s)` of `D` (`DetCauchyChart`).  This file proves
that its mixed differences have the same support as those of the rooted trace at fixed fields
(`DetCauchyGraph`): a non-zero `Δ_J` forces every parameter cube of `J` to be joined to one block of
`B` by a chain of centres with footprints in `J`.

## The component statement that is used

The landed locality theorems for the decoupled background (`i4b_local`, `i4b_local_rows`,
`i4b_local_of_rows`, `i4b_local_of_agree_on_component`, `Dec2.i4b_local_fp`) are stated for a union
`Y` of nearest-neighbour components of `V(X₁, 𝒞) ∩ Ω₁`, where `V(X₁, 𝒞) = X₁ ∪ ⋃_{P ∈ 𝒞} P` is a
union of **cubes** of the cover, and give equality of the multipliers on the interaction boxes
`S_Y` only.  The root component `Y'` of `exists_root_comp` is a union of **thickened** cubes
`□̂_w ∩ Ω₁` of active centres, i.e. a union of components of `Yreg`.  A thickened cube ends inside
the cubes of the third ring around its centre, and those cubes are switched on (they belong to the
footprint of an active centre); so `Y'` is in general *not* a union of components of
`V(X₁, 𝒞) ∩ Ω₁` for any admissible `(X₁, 𝒞)` (every such `V` contains all cubes that are switched
on), and the component of `V` containing `Y'` may contain the cube `p` that is switched.  Moreover
the decoupled logarithm reads the multiplier on all of `Y'`, not only on `S_Y`.  The landed
theorems are therefore not applied.  Instead the comparison argument of Theorem I-4a (e) is run
again for components of `Yreg`:

* `not_mem_Core_of_row`: a site outside a union `Y'` of components of `Yreg s` that is read by the
  row of `H_D` at a site of `Y'` lies outside `Core s`, so the correction `δφ_s` vanishes there
  (`dphi_eq_zero_of_not_mem_Core`).  Proof: `H_D` is symmetric, the row of a core site of `□_z`
  lies in `□̂_z` (`row_mem_hatBox`), and `□̂_z ∩ Ω₁` is connected.
* `local_step_yreg`, `i4a_local_yreg`: the paired Picard iteration with `T = Y'`.  Conclusions:
  `δα(s) = δα(s')` on **all of** `Y'` and `δφ(s) = δφ(s')` on `Y'`.
* `i4b_local_yreg`: the same for the decoupled background of two data that agree on the sets
  `resDep x`, `x ∈ Y'`.

## Results on the chart

* `decBg_eq_on_comp`: for two data of the chart, two parameter vectors in the polydisc, and a
  common union `Y'` of components of `Yreg` at both, with equal cut factors on the cubes inside
  `Y'` and data agreeing on `resDep x`, `x ∈ Y'`: `decBgMult` and `decBgField` agree on `Y'`.
* `decBgMult_cut_insert_eq_on`, `decBgField_cut_insert_eq_on`, `exists_root_comp_decBg_eq`: the
  background at the cut points `1_I` and `1_{I ∪ {p}}` agrees on the root component, for `p` not
  joined to the root.
* `rootTraceBg_eq_of_comp`, `rootTraceBg_eq_baseline_of_not_label`: the rooted trace with its
  background depends only on the component; without a labelled block it is the baseline.
* `exists_rootChain_of_mixDiff_rootTraceBg_ne_zero`: the support theorem.

The read set of the rooted trace is exactly `Y'` (multiplier and field, `CovStanding.decLog_agree`).

## What is not proved here

The identification of `rootTraceBg` at `s = 1` with the determinant term of the step identity (only
`rootTraceBg_one_eq*` of `DetCauchyChart`), the resummation over many blocks, and the absorption of
the prefactor.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Finset Matrix

/-! ### Locality of the decoupled system on components of `Yreg` -/

section YregLocal

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- The sites in `Ω₁` of the thickened cube of a centre with non-zero cut factor lie in `Yreg`. -/
theorem hatI_subset_Yreg_of_mem_Zs {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    {z : ℕ × CTorus d L N₁ m₁ K} (hz : z ∈ Zs G s) : hatI G z ⊆ Yreg G s := by
  classical
  intro x hx
  unfold hatI at hx
  rw [Finset.mem_filter] at hx
  unfold Yreg
  rw [Finset.mem_filter, Finset.mem_biUnion]
  exact ⟨⟨z, hz, hx.1⟩, hx.2⟩

/-- Every interaction cube with a non-zero cut factor lies inside or outside a union of components
of `Yreg s` (general level `K`). -/
theorem subI_or_disjI_of_isNnComp_Yreg (hconn : HatConn G) {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    {Y' : Finset (CTorus d L N₁ m₁ K)} (hY : IsNnComp (Yreg G s) Y')
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) (hs : sProd G s q ≠ 0) :
    SubI G (intBox q) Y' ∨ DisjI G (intBox q) Y' := by
  classical
  have hzZ : q ∈ Zs G s := Finset.mem_filter.2 ⟨hq, hs⟩
  rcases connIn_dichotomy (hconn q hq) (hatI_subset_Yreg_of_mem_Zs hzZ) hY with h | h
  · left
    intro y hy
    exact h (by
      unfold hatI
      rw [Finset.mem_filter]
      exact ⟨box_subset_hatBox q hy, y.2⟩)
  · right
    intro y hy hyY
    exact Finset.disjoint_left.1 h (by
      unfold hatI
      rw [Finset.mem_filter]
      exact ⟨box_subset_hatBox q hy, y.2⟩) hyY

/-- **A site read from a component and lying outside it is not a core site.**  Let `Y'` be a union
of nearest-neighbour components of `Yreg s`, `x ∈ Y'` and `y ∉ Y'` with `H_D(α) x y ≠ 0`.  Then
`y ∉ Core s`: otherwise `y` is a core site of an active centre `z`, the row of `H_D` at `y` lies in
the thickened cube `□̂_z`, which contains `x` and is connected, hence lies in `Y'`. -/
theorem not_mem_Core_of_row (S : DGSetting G a ν) (hconn : HatConn G)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {Y' : Finset (CTorus d L N₁ m₁ K)}
    (hY : IsNnComp (Yreg G s) Y') (α : G.Ω 1 → ℂ) {x y : G.Ω 1}
    (hx : (x : CTorus d L N₁ m₁ K) ∈ Y') (hxy : dirichletOperator G a ν α x y ≠ 0)
    (hy : (y : CTorus d L N₁ m₁ K) ∉ Y') : (y : CTorus d L N₁ m₁ K) ∉ Core G s := by
  classical
  intro hcore
  unfold Core at hcore
  rw [Finset.mem_biUnion] at hcore
  obtain ⟨z, hzZ, hyz⟩ := hcore
  have hz : z ∈ cubeIdx G := (Finset.mem_filter.1 hzZ).1
  have hyx : dirichletOperator G a ν α y x ≠ 0 := by
    have e := congrFun (congrFun (dirichletOperator_transpose (G := G) a ν α) y) x
    rw [Matrix.transpose_apply] at e
    rw [← e]
    exact hxy
  have hxh := row_mem_hatBox S hz α (coreBox_subset_box hyz) hyx
  have hxI : (x : CTorus d L N₁ m₁ K) ∈ hatI G z := by
    unfold hatI
    rw [Finset.mem_filter]
    exact ⟨hxh, x.2⟩
  have hyI : (y : CTorus d L N₁ m₁ K) ∈ hatI G z := by
    unfold hatI
    rw [Finset.mem_filter]
    exact ⟨box_subset_hatBox z (coreBox_subset_box hyz), y.2⟩
  rcases connIn_dichotomy (hconn z hz) (hatI_subset_Yreg_of_mem_Zs hzZ) hY with h | h
  · exact hy (h hyI)
  · exact Finset.disjoint_left.1 h hxI hx

/-- The correction `δφ = G_s(α₀ + δα)(F_s - δα φ₀)` vanishes outside `Core s`. -/
theorem dphi_eq_zero_of_not_mem_Core {s : DecParams G} {α₀ δα : G.Ω 1 → ℂ}
    {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ} {Fs : G.Ω 1 × Fin N → ℂ} (x : G.Ω 1)
    (hx : (x : CTorus d L N₁ m₁ K) ∉ Core G (extS G s)) (i : Fin N) :
    dphi G (decG G a ν s) α₀ φ₀ Fs δα (x, i) = 0 := by
  unfold dphi
  rw [liftOp_mulVec]
  by_contra hne
  exact hx (dg5_support (G := G) (a := a) (ν := ν) (α := α₀ + δα) (extS G s) _ x hne)

/-- **One step of the comparison, for a component of `Yreg`.**  Let `Y'` be a union of
nearest-neighbour components of both `Yreg s` and `Yreg s'`, with equal cut factors on the cubes
inside `Y'`, and let the data agree on `Y'` (`α₀`, the source) and on the sites read by the rows at
the sites of `Y'` (`φ₀`).  If the rescaled potentials `ξ`, `η` agree on `Y'` then `𝒩_s(ξ)` and
`𝒩_{s'}(η)` agree on `Y'`. -/
theorem local_step_yreg {cstar BG : ℝ} (hF : FamSpec d L cstar BG) (S : DGSetting G a ν)
    (hconn : HatConn G) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s s' : DecParams G} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ α₀' : G.Ω 1 → ℂ} {φ₀ φ₀' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {Fs Fs' : G.Ω 1 × Fin N → ℂ} {δ₀ ρ : ℝ} (hα0 : Small G α₀ δ₀) (hα0' : Small G α₀' δ₀)
    (hρ : δ₀ + ρ ≤ gamma1 d / 8)
    {Y' : Finset (CTorus d L N₁ m₁ K)} (hY : IsNnComp (Yreg G (extS G s)) Y')
    (hY' : IsNnComp (Yreg G (extS G s')) Y')
    (hsP : ∀ q ∈ cubeIdx G, SubI G (intBox q) Y' →
      sProd G (extS G s) q = sProd G (extS G s') q)
    (hDα : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y' → α₀ x = α₀' x)
    (hDφ : ∀ y : G.Ω 1, RowSite G a ν α₀ Y' y → φ₀ y = φ₀' y)
    (hDF : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y' → ∀ i : Fin N, Fs (x, i) = Fs' (x, i))
    {ξ η : G.Ω 1 → ℂ} (hξ : ∀ x, ‖ξ x‖ ≤ ρ) (hη : ∀ x, ‖η x‖ ≤ ρ)
    (hξη : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y' → ξ x = η x) :
    ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y' →
      Smap G (decG G a ν s) (dirichletOperator G a ν α₀) ιU α₀ φ₀ Fs ξ x =
      Smap G (decG G a ν s') (dirichletOperator G a ν α₀') ιU α₀' φ₀' Fs' η x := by
  classical
  intro x hxY
  have hd0 : 0 < d := by have := S.hd; omega
  obtain ⟨-, hunit⟩ := hF.2.2 G S hκ hM hs N
  obtain ⟨-, hunit'⟩ := hF.2.2 G S hκ hM hs' N
  have hδα : Small G (toAlpha G ξ) ρ := small_toAlpha G ξ hξ
  have hδα' : Small G (toAlpha G η) ρ := small_toAlpha G η hη
  have hA : Small G (α₀ + toAlpha G ξ) (gamma1 d / 8) := fun y =>
    ((Small.add hα0 hδα) y).trans hρ
  have hA' : Small G (α₀' + toAlpha G η) (gamma1 d / 8) := fun y =>
    ((Small.add hα0' hδα') y).trans hρ
  have hAeq : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y' →
      (α₀ + toAlpha G ξ) y = (α₀' + toAlpha G η) y := by
    intro y hy
    simp only [Pi.add_apply]
    rw [hDα y hy, show toAlpha G ξ y = toAlpha G η y by
      unfold toAlpha; rw [hξη y hy]]
  have hdich : ∀ q ∈ cubeIdx G, (sProd G (extS G s) q ≠ 0 ∨ sProd G (extS G s') q ≠ 0) →
      SubI G (intBox q) Y' ∨ DisjI G (intBox q) Y' := by
    intro q hq hne
    rcases hne with h | h
    · exact subI_or_disjI_of_isNnComp_Yreg hconn hY hq h
    · exact subI_or_disjI_of_isNnComp_Yreg hconn hY' hq h
  have hdphi : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y' → ∀ i : Fin N,
      dphi G (decG G a ν s) α₀ φ₀ Fs (toAlpha G ξ) (y, i) =
      dphi G (decG G a ν s') α₀' φ₀' Fs' (toAlpha G η) (y, i) := by
    intro y hy i
    unfold dphi
    rw [liftOp_mulVec, liftOp_mulVec]
    refine Gs_local S (admPot_of_small hd0 hA) (admPot_of_small hd0 hA')
      (hunit (admPot_of_small hd0 hA)) (hunit' (admPot_of_small hd0 hA')) hdich hsP hAeq
      (f := fun b => Fsrc φ₀ Fs (toAlpha G ξ) (b, i))
      (f' := fun b => Fsrc φ₀' Fs' (toAlpha G η) (b, i)) ?_ y hy
    intro b hb
    simp only [Fsrc]
    rw [hDF b hb i, hDφ b (Or.inl hb)]
    congr 2
    unfold toAlpha; rw [hξη b hb]
  unfold Smap
  rw [Nmap_explicit, Nmap_explicit]
  congr 1
  refine Nexp_congr ιU ?_ (fun i => by rw [hDφ x (Or.inl hxY)]) (fun i => hDF x hxY i)
    (fun i => hdphi x hxY i) (fun y hy => ?_)
  · intro y
    rw [dirichletOperator_eq_add a ν α₀, dirichletOperator_eq_add a ν α₀']
    simp only [Matrix.add_apply, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst hxy; simp [hDα x hxY]
    · simp [hxy]
  · have hrow : RowSite G a ν α₀ Y' y := Or.inr ⟨x, hxY, hy⟩
    refine ⟨fun i => by rw [hDφ y hrow], fun i => ?_⟩
    by_cases hyY : (y : CTorus d L N₁ m₁ K) ∈ Y'
    · exact hdphi y hyY i
    · rw [dphi_eq_zero_of_not_mem_Core y (not_mem_Core_of_row S hconn hY α₀ hxY hy hyY) i,
        dphi_eq_zero_of_not_mem_Core y (not_mem_Core_of_row S hconn hY' α₀ hxY hy hyY) i]

/-- **Theorem I-4a (e) for components of `Yreg`.**  Let `Y'` be a union of nearest-neighbour
components of both `Yreg s` and `Yreg s'`, with equal cut factors `s_q = s'_q` on the cubes `q`
with `□_q ⊆ Y'`, and two data sets agreeing on `Y'` (`α₀`, the source) and on the sites read by the
rows at `Y'` (`φ₀`).  Then the solutions of the two decoupled systems satisfy `δα(s) = δα(s')` on
all of `Y'` and `δφ(s) = δφ(s')` on `Y'`. -/
theorem i4a_local_yreg {cstar BG : ℝ} (hF : FamSpec d L cstar BG) (S : DGSetting G a ν)
    (hconn : HatConn G) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s s' : DecParams G} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ α₀' : G.Ω 1 → ℂ} {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ f₁' : G.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ}
    (H : DecHyp G a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁) (H' : DecHyp G a ν ιU α₀' φ₀' δΨ' f₁' δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {Y' : Finset (CTorus d L N₁ m₁ K)} (hY : IsNnComp (Yreg G (extS G s)) Y')
    (hY' : IsNnComp (Yreg G (extS G s')) Y')
    (hsP : ∀ q ∈ cubeIdx G, SubI G (intBox q) Y' →
      sProd G (extS G s) q = sProd G (extS G s') q)
    (hDα : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y' → α₀ x = α₀' x)
    (hDφ : ∀ y : G.Ω 1, RowSite G a ν α₀ Y' y → φ₀ y = φ₀' y)
    (hDF : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y' → ∀ i : Fin N,
      pertSource G a δΨ f₁ (x, i) = pertSource G a δΨ' f₁' (x, i))
    {δα δα' : G.Ω 1 → ℂ}
    (hfix : DecFixed G a ν s ιU α₀ φ₀ (pertSource G a δΨ f₁) δα)
    (hsm : Small G δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (hfix' : DecFixed G a ν s' ιU α₀' φ₀' (pertSource G a δΨ' f₁') δα')
    (hsm' : Small G δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) :
    (∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y' → δα x = δα' x) ∧
    (∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y' → ∀ i : Fin N,
      dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα (y, i) =
      dphi G (decG G a ν s') α₀' φ₀' (pertSource G a δΨ' f₁') δα' (y, i)) := by
  classical
  have hBG := hF.2.1
  have hd0 : 0 < d := by have := S.hd; omega
  set B : ℝ := famConst d L BG κ with hB
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hB0 : 0 ≤ B := by have := famConst_ge_one (L := L) hBG κ hd0; linarith
  have hΓ : 0 < Γ := by have := gamma1_pos hd0; positivity
  have hC := coreHyp'_small (d := d) (L := L) (N := N) hB0 hΓ H.δ₀_nn H.δ₁_nn hδ₀ hδ₁
  obtain ⟨⟨hfam, -⟩, hunit⟩ := hF.2.2 G S hκ hM hs N
  obtain ⟨⟨hfam', -⟩, hunit'⟩ := hF.2.2 G S hκ hM hs' N
  obtain ⟨ξ, hξB, hξfix, hξuniq, hit⟩ := smap_fixed_iterates hfam H.setup hC
  obtain ⟨ξ', hξB', hξfix', hξuniq', hit'⟩ := smap_fixed_iterates hfam' H'.setup hC
  -- identify `toAlpha ξ` with `δα`
  have hid : ∀ {s₀ : DecParams G} {α₀₀ : G.Ω 1 → ℂ} {φ₀₀ : CTorus d L N₁ m₁ K → Fin N → ℂ}
      {Fs₀ : G.Ω 1 × Fin N → ℂ} {ξ₀ δα₀ : G.Ω 1 → ℂ},
      Smap G (decG G a ν s₀) (dirichletOperator G a ν α₀₀) ιU α₀₀ φ₀₀ Fs₀ ξ₀ = ξ₀ →
      ξ₀ ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) (c6' d L N B Γ) →
      (∀ ξ' ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) (c6' d L N B Γ),
        Smap G (decG G a ν s₀) (dirichletOperator G a ν α₀₀) ιU α₀₀ φ₀₀ Fs₀ ξ' = ξ' → ξ' = ξ₀) →
      DecFixed G a ν s₀ ιU α₀₀ φ₀₀ Fs₀ δα₀ → Small G δα₀ (c6' d L N B Γ) →
      toAlpha G ξ₀ = δα₀ := by
    intro s₀ α₀₀ φ₀₀ Fs₀ ξ₀ δα₀ _ _ huniq hf hsm₀
    have hm : ofAlpha G δα₀ ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) (c6' d L N B Γ) := by
      rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg (c6'_pos (d := d) (L := L) (N := N) hB0 hΓ).le).2
        fun x => ?_
      rw [norm_ofAlpha]; exact hsm₀ x
    have hf' : Smap G (decG G a ν s₀) (dirichletOperator G a ν α₀₀) ιU α₀₀ φ₀₀ Fs₀
        (ofAlpha G δα₀) = ofAlpha G δα₀ := by
      funext x
      unfold Smap
      rw [toAlpha_ofAlpha]
      unfold DecFixed at hf
      rw [hf]
      rfl
    rw [← huniq _ hm hf', toAlpha_ofAlpha]
  have e1 : toAlpha G ξ = δα := hid hξfix hξB hξuniq hfix hsm
  have e2 : toAlpha G ξ' = δα' := hid hξfix' hξB' hξuniq' hfix' hsm'
  have hpoly : δ₀ + c6' d L N B Γ ≤ Γ := by linarith [hC.poly, hC.ρ_nn]
  -- the pair induction
  have hagreeξ : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y' → ξ x = ξ' x := by
    refine fixed_agree_of_step (T := fun x : G.Ω 1 => (x : CTorus d L N₁ m₁ K) ∈ Y')
      (fun u v hu hv huv i hi => ?_) (fun n => ⟨(hit n).1, (hit n).2⟩)
      (fun n => ⟨(hit' n).1, (hit' n).2⟩) hC.ρ_nn
    exact local_step_yreg hF S hconn hκ hM hs hs' H.alpha0 H'.alpha0 hpoly
      hY hY' hsP hDα hDφ hDF hu hv huv i hi
  have hδ : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y' → δα x = δα' x := by
    intro x hx
    rw [← e1, ← e2]
    unfold toAlpha
    rw [hagreeξ x hx]
  refine ⟨hδ, fun y hy i => ?_⟩
  have hA : Small G (α₀ + δα) Γ := fun z => ((Small.add H.alpha0 hsm) z).trans hpoly
  have hA' : Small G (α₀' + δα') Γ := fun z => ((Small.add H'.alpha0 hsm') z).trans hpoly
  have hdich : ∀ q ∈ cubeIdx G, (sProd G (extS G s) q ≠ 0 ∨ sProd G (extS G s') q ≠ 0) →
      SubI G (intBox q) Y' ∨ DisjI G (intBox q) Y' := by
    intro q hq hne
    rcases hne with h | h
    · exact subI_or_disjI_of_isNnComp_Yreg hconn hY hq h
    · exact subI_or_disjI_of_isNnComp_Yreg hconn hY' hq h
  unfold dphi
  rw [liftOp_mulVec, liftOp_mulVec]
  refine Gs_local S (admPot_of_small hd0 hA) (admPot_of_small hd0 hA')
    (hunit (admPot_of_small hd0 hA)) (hunit' (admPot_of_small hd0 hA')) hdich hsP
    (fun z hz => ?_) (f := fun b => Fsrc φ₀ (pertSource G a δΨ f₁) δα (b, i))
    (f' := fun b => Fsrc φ₀' (pertSource G a δΨ' f₁') δα' (b, i)) (fun b hb => ?_) y hy
  · simp only [Pi.add_apply]
    rw [hDα z hz, hδ z hz]
  · simp only [Fsrc]
    rw [hDF b hb i, hDφ b (Or.inl hb), hδ b hb]

/-- **Theorem I-4b (iv) for components of `Yreg`.**  Let `s`, `s'` be two parameter vectors, `Y'` a
union of nearest-neighbour components of both `Yreg s` and `Yreg s'` with equal cut factors on the
cubes `q` with `□_q ⊆ Y'`, and `D`, `D₂` two data of `Ψ̃^c(δ, ε)` whose raw data agree on the
dependency sets `resDep x` of the sites `x` of `Y'`.  Then the decoupled background fields satisfy
`α_k(s; D) = α_k(s'; D₂)` and `φ_k(s; D) = φ_k(s'; D₂)` at every site of `Y'`. -/
theorem i4b_local_yreg {c BG : ℝ} (hS : DecSpecs d L c BG) (S : DGSetting G a ν)
    (hconn : HatConn G) (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s s' : DecParams G}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D D₂ : BgData G N}
    (hD : InDomainC G ν δ ε D) (hD₂ : InDomainC G ν δ ε D₂)
    {Y' : Finset (CTorus d L N₁ m₁ K)} (hY : IsNnComp (Yreg G (extS G s)) Y')
    (hY' : IsNnComp (Yreg G (extS G s')) Y')
    (hsP : ∀ q ∈ cubeIdx G, SubI G (intBox q) Y' →
      sProd G (extS G s) q = sProd G (extS G s') q)
    (hdata : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y' →
      ∀ y ∈ resDep G (x : CTorus d L N₁ m₁ K), D.Ψ y = D₂.Ψ y ∧ (y ∈ G.Ω 1 → D.h y = D₂.h y))
    {φ φ₂ : G.Ω 1 × Fin N → ℂ} {α α₂ : G.Ω 1 → ℂ}
    (h : IsDecBg G a ν (rho4 d L N BG κ) s D φ α)
    (h₂ : IsDecBg G a ν (rho4 d L N BG κ) s' D₂ φ₂ α₂) :
    (∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y' → α x = α₂ x) ∧
    (∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y' → ∀ i : Fin N, φ (y, i) = φ₂ (y, i)) := by
  classical
  have hd0 : 0 < d := by have := HB.hd; omega
  have hBG := hS.fam.2.1
  obtain ⟨W⟩ := DataWit.exists hD
  obtain ⟨W₂⟩ := DataWit.exists hD₂
  have Hd := decHyp_of_data (N := N) HB hBG hδ0 hδε hε hδ hνε W
  have Hd₂ := decHyp_of_data (N := N) HB hBG hδ0 hδε hε hδ hνε W₂
  obtain ⟨-, h2, -⟩ := c7_facts (L := L) (N := N) hd0 hBG hδ0.le hδ
  have hCδ : 0 < lemma53Const d L * δ := mul_pos (lemma53Const_pos d L) hδ0
  have hdc := deltaClose_le_deltaStar' (d := d) (L := L) (N := N) (BG := BG) (κ := κ)
  have hdcp := deltaClose_pos (d := d) (L := L) (N := N) (κ := κ) hd0 hBG
  have hle : lemma53Const d L * δ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) := by
    linarith
  have hfix : DecFixed G a ν s true (0 : G.Ω 1 → ℂ) (approxField G a ν D.Ψ D.h)
      (pertSource G a (0 : CTorus d L N₁ m₁ K → Fin N → ℂ)
        (residual G a ν D (approxField G a ν D.Ψ D.h))) α := by
    rw [pertSource_zeroΨ]; exact h.fixed
  have hfix₂ : DecFixed G a ν s' true (0 : G.Ω 1 → ℂ) (approxField G a ν D₂.Ψ D₂.h)
      (pertSource G a (0 : CTorus d L N₁ m₁ K → Fin N → ℂ)
        (residual G a ν D₂ (approxField G a ν D₂.Ψ D₂.h))) α₂ := by
    rw [pertSource_zeroΨ]; exact h₂.fixed
  have hphi : ∀ y : G.Ω 1, RowSite G a ν (0 : G.Ω 1 → ℂ) Y' y →
      approxField G a ν D.Ψ D.h y = approxField G a ν D₂.Ψ D₂.h y := by
    rintro y (hy | ⟨x, hx, hxy⟩)
    · exact approxField_congr fun z hz => hdata y hy z
        (approxDep_subset_resDep (mem_resSites_self _) hz)
    · exact approxField_congr fun z hz => hdata x hx z
        (approxDep_subset_resDep (mem_resSites_of_entry_ne_zero hxy) hz)
  obtain ⟨hα, hφ⟩ := i4a_local_yreg hS.fam S hconn hκ hM hs hs' Hd Hd₂ hle hle hY hY' hsP
    (fun _ _ => rfl) hphi (fun x hx i => by
      rw [pertSource_zeroΨ, pertSource_zeroΨ]
      exact residual_congr x i (hdata x hx)) hfix h.small hfix₂ h₂.small
  refine ⟨hα, fun y hy i => ?_⟩
  have e := hφ y hy i
  rw [pertSource_zeroΨ, pertSource_zeroΨ] at e
  rw [h.field, h₂.field]
  simp only
  rw [hphi y (Or.inl hy), e]

end YregLocal

/-! ### The decoupled background of the chart on a component -/

section ChartLocal

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- A cut point lies in the open polydisc of radius `e^κ`, `κ > 0`. -/
theorem norm_cutPt_lt_exp (hκ : 0 < κ) (I : Finset (cubeIdx Gp)) (P : cubeIdx Gp) :
    ‖cutPt I P‖ < Real.exp κ := by
  unfold cutPt
  split_ifs
  · simpa using Real.one_lt_exp_iff.2 hκ
  · simpa using Real.exp_pos κ

/-- **The decoupled background of the chart depends only on the component.**  Let `D`, `D₂` be data
of the chart `Ξ^c(𝔹_{k+1}; 1, ε)`, `s`, `s'` parameters with `|s_P|, |s'_P| < e^κ`, and `Y'` a union
of nearest-neighbour components of both `Yreg s` and `Yreg s'` such that the cut factors of the
cubes `q` with `□_q ⊆ Y'` agree, and the raw data agree on `resDep x` for the sites `x` of `Y'`.
Then `α_s(D) = α_{s'}(D₂)` and `φ_s(D) = φ_{s'}(D₂)` at every site of `Y'`. -/
theorem decBg_eq_on_comp
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hconn : HatConn Gp)
    {s s' : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D D₂ : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD₂ : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D₂)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg Gp (extS Gp s)) Y')
    (hY' : IsNnComp (Yreg Gp (extS Gp s')) Y')
    (hsP : ∀ q ∈ cubeIdx Gp, SubI Gp (intBox q) Y' →
      sProd Gp (extS Gp s) q = sProd Gp (extS Gp s') q)
    (hdata : ∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ Y' →
      ∀ y ∈ resDep Gp (x : CTorus d L N₁ m₁ (k + 1)),
        D.Ψ y = D₂.Ψ y ∧ (y ∈ Gp.Ω 1 → D.h y = D₂.h y)) :
    (∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ Y' →
      decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D x =
        decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D₂ x) ∧
    (∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ Y' → ∀ i : Fin N,
      decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D (x, i) =
        decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D₂ (x, i)) := by
  obtain ⟨φ, α, hI, h1, h2⟩ := exists_isDecBg_of_flCore hC hs hD
  obtain ⟨φ₂, α₂, hI₂, h1₂, h2₂⟩ := exists_isDecBg_of_flCore hC hs' hD₂
  obtain ⟨hδ0, hδ0', hδ1, hνε⟩ := xiC_numerics hC
  rw [h1, h2, h1₂, h2₂]
  exact i4b_local_yreg hC.hS hC.Sp hconn hC.HBp hC.hκ.le hC.hM (fun P => (hs P).le)
    (fun P => (hs' P).le) hδ0 le_rfl hδ0' hδ1 hνε (xiCData_inDomainC hC.HBp hC.small1 hD)
    (xiCData_inDomainC hC.HBp hC.small1 hD₂) hY hY' hsP hdata hI hI₂

/-- **Agreement of the decoupled multiplier at two cut points on a common component.**  For a datum
`D` of the chart and a union `Y'` of components of `Yreg` at both cut points `1_I`, `1_{I ∪ {p}}`
with equal cut factors on the cubes inside `Y'` (the three properties of the root component of
`exists_root_comp`): `α_{1_I} = α_{1_{I ∪ {p}}}` at every site of `Y'`. -/
theorem decBgMult_cut_insert_eq_on
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hconn : HatConn Gp)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {I : Finset (cubeIdx Gp)} {p : cubeIdx Gp} {Y' : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp (Yreg Gp (extS Gp (cutPt I))) Y')
    (hY' : IsNnComp (Yreg Gp (extS Gp (cutPt (insert p I)))) Y')
    (hsP : ∀ q ∈ cubeIdx Gp, SubI Gp (intBox q) Y' →
      sProd Gp (extS Gp (cutPt I)) q = sProd Gp (extS Gp (cutPt (insert p I))) q)
    (x : Gp.Ω 1) (hx : (x : CTorus d L N₁ m₁ (k + 1)) ∈ Y') :
    decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) (cutPt I) D x =
      decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) (cutPt (insert p I)) D x :=
  (decBg_eq_on_comp hC hconn (norm_cutPt_lt_exp hC.hκ I) (norm_cutPt_lt_exp hC.hκ (insert p I))
    hD hD hY hY' hsP (fun _ _ _ _ => ⟨rfl, fun _ => rfl⟩)).1 x hx

/-- **Agreement of the decoupled background field at two cut points on a common component**:
`φ_{1_I} = φ_{1_{I ∪ {p}}}` at every site of `Y'`, under the hypotheses of
`decBgMult_cut_insert_eq_on`. -/
theorem decBgField_cut_insert_eq_on
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hconn : HatConn Gp)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {I : Finset (cubeIdx Gp)} {p : cubeIdx Gp} {Y' : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp (Yreg Gp (extS Gp (cutPt I))) Y')
    (hY' : IsNnComp (Yreg Gp (extS Gp (cutPt (insert p I)))) Y')
    (hsP : ∀ q ∈ cubeIdx Gp, SubI Gp (intBox q) Y' →
      sProd Gp (extS Gp (cutPt I)) q = sProd Gp (extS Gp (cutPt (insert p I))) q)
    (x : Gp.Ω 1) (hx : (x : CTorus d L N₁ m₁ (k + 1)) ∈ Y') (i : Fin N) :
    decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) (cutPt I) D (x, i) =
      decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) (cutPt (insert p I)) D (x, i) :=
  (decBg_eq_on_comp hC hconn (norm_cutPt_lt_exp hC.hκ I) (norm_cutPt_lt_exp hC.hκ (insert p I))
    hD hD hY hY' hsP (fun _ _ _ _ => ⟨rfl, fun _ => rfl⟩)).2 x hx i

/-- **The root component with its background.**  Let `I ⊆ J`, `p ∈ J`, and suppose no centre whose
footprint contains `p` is joined to the unit block `y` by a chain in `J`.  If `y` is attached to an
active centre at the cut point `1_I`, there is a set `Y'` which is a union of nearest-neighbour
components of `Yreg` at both cut points `1_I`, `1_{I ∪ {p}}`, carries the label of `y`, on whose
cubes the cut factors agree, and on which the decoupled background `(φ_s, α_s)` of the datum `D`
is the same at the two cut points. -/
theorem exists_root_comp_decBg_eq
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hconn : HatConn Gp)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {J I : Finset (cubeIdx Gp)} {p : cubeIdx Gp} (hpJ : p ∈ J) (hIJ : I ⊆ J) (y : unitPts Gp)
    (hnc : ∀ q, RootChain Gp J y q → p ∉ QsetP Gp q)
    (hatt : ∃ q0 ∈ Zs Gp (extS Gp (cutPt I)), HatAttached Gp y q0) :
    ∃ Y' : Finset (CTorus d L N₁ m₁ (k + 1)),
      IsNnComp (Yreg Gp (extS Gp (cutPt I))) Y' ∧
      IsNnComp (Yreg Gp (extS Gp (cutPt (insert p I)))) Y' ∧ unitLabel Gp Y' y ∧
      (∀ q ∈ cubeIdx Gp, SubI Gp (intBox q) Y' →
        sProd Gp (extS Gp (cutPt I)) q = sProd Gp (extS Gp (cutPt (insert p I))) q) ∧
      (∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ Y' →
        decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) (cutPt I) D x =
          decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) (cutPt (insert p I)) D x) ∧
      (∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ Y' → ∀ i : Fin N,
        decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) (cutPt I) D (x, i) =
          decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) (cutPt (insert p I)) D (x, i)) := by
  obtain ⟨Y', hY, hY', hl, hsP⟩ := exists_root_comp hC.Sp hpJ hIJ y hnc hatt
  exact ⟨Y', hY, hY', hl, hsP, decBgMult_cut_insert_eq_on hC hconn hD hY hY' hsP,
    decBgField_cut_insert_eq_on hC hconn hD hY hY' hsP⟩

end ChartLocal

/-! ### The rooted trace with its background on a component -/

section TraceLocal

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- The standing hypotheses of the decoupled covariance hold at the decoupled background of a datum
of the chart, for every `s` in the polydisc of radius `e^κ` and the unit-lattice matrices. -/
theorem covStanding_rootTraceBg
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) :
    CovStanding Gp (compWeight L a₁) a₁ ν
      (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D) κ (extS Gp s) δc
      (barField Gp D.Ψ (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D))
      (unitQ Gp) (unitP Gp) :=
  covStanding_of_mem (N := N) (xSetting_of_flCore hC hk) hC.hκ.le hcap hδc hsm
    (isUnitLatticeB_unit (G := Gp)).toIsUnitLattice
    (e := ((s, (barField Gp D.Ψ (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D),
      decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D)) : DecData Gp N))
    (mem_decDom_rootTraceBg hC hs hD hmar hα)

/-- **The rooted trace with its background depends only on the component.**  Two data `D`, `D₂` of
the chart and two parameter vectors `s`, `s'` in the polydisc; `Y'` a union of components of both
`Yreg s` and `Yreg s'` with equal cut factors on the cubes inside `Y'`; the raw data agree on
`resDep x` for the sites `x` of `Y'`.  Then the rooted traces (each at its own decoupled
background) of a set `B` of unit blocks lying in `Y'` are equal. -/
theorem rootTraceBg_eq_of_comp
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2) (hconn : HatConn Gp)
    {s s' : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D D₂ : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD₂ : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D₂)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg Gp (extS Gp s)) Y')
    (hY' : IsNnComp (Yreg Gp (extS Gp s')) Y')
    (hsP : ∀ q ∈ cubeIdx Gp, SubI Gp (intBox q) Y' →
      sProd Gp (extS Gp s) q = sProd Gp (extS Gp s') q)
    (hdata : ∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ Y' →
      ∀ y ∈ resDep Gp (x : CTorus d L N₁ m₁ (k + 1)),
        D.Ψ y = D₂.Ψ y ∧ (y ∈ Gp.Ω 1 → D.h y = D₂.h y))
    (B : Finset (unitPts Gp)) (hB : ∀ y ∈ B, unitLabel Gp Y' y) :
    rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp) (unitP Gp) B D s =
      rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp) (unitP Gp) B D₂ s' := by
  classical
  have H := covStanding_rootTraceBg hC hk hδc hcap hsm hmar hα hD hs
  have H' := covStanding_rootTraceBg hC hk hδc hcap hsm hmar hα hD₂ hs'
  obtain ⟨hmult, hfield⟩ := decBg_eq_on_comp hC hconn hs hs' hD hD₂ hY hY' hsP hdata
  have hUT := unionOfTopBlocks_of_isNnComp hC.Sp hconn hY
  have hbar : ∀ z : CTorus d L N₁ m₁ (k + 1), z ∈ Y' →
      barField Gp D.Ψ (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D) z =
        barField Gp D₂.Ψ (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D₂) z := by
    intro z hz
    have hzΩ : z ∈ Gp.Ω 1 := (mem_Yreg_iff.1 (hY.1 hz)).1
    funext i
    simp only [barField, hzΩ, ↓reduceDIte]
    exact hfield ⟨z, hzΩ⟩ hz i
  have key : ∀ y ∈ B, ∀ i : Fin N,
      decLog Gp (compWeight L a₁) a₁ ν (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D)
        (extS Gp s) (barField Gp D.Ψ (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D))
        (unitQ Gp) (unitP Gp) (y, i) (y, i) =
      decLog Gp (compWeight L a₁) a₁ ν (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D₂)
        (extS Gp s') (barField Gp D₂.Ψ (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D₂))
        (unitQ Gp) (unitP Gp) (y, i) (y, i) := fun y hy i =>
    H.decLog_agree H' hconn hY hY' hsP hmult hbar (unitLabel Gp Y')
      (unitQ_label_top hUT) (unitP_label_top hUT) (y, i) (y, i) (hB y hy) (hB y hy)
  unfold rootTraceBg rootTrace
  rw [Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl (fun i _ => key y hy i)]

/-- **Without a labelled block the rooted trace is the baseline.**  For a datum `D` of the chart
and `s` in the polydisc, if no block of `B` lies in `Yreg s` then the rooted trace of `B` at the
decoupled background is the baseline `-(1/2) ∑_{y ∈ B} ∑_i (log a_k (1 - P) + log(a_k + a₁/L²) P)`
(which involves neither `s` nor the datum). -/
theorem rootTraceBg_eq_baseline_of_not_label
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2) (hconn : HatConn Gp)
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (B : Finset (unitPts Gp)) (hB : ∀ y ∈ B, ¬ unitLabel Gp (Yreg Gp (extS Gp s)) y) :
    rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp) (unitP Gp) B D s =
      -(1 / 2 : ℂ) * ∑ y ∈ B, ∑ i : Fin N,
        (((Real.log (compWeight L a₁ k) : ℝ) : ℂ) • (1 - liftOp N (unitP Gp)) +
          ((Real.log (compWeight L a₁ k + a₁ / (L : ℝ) ^ 2) : ℝ) : ℂ) • liftOp N (unitP Gp))
            (y, i) (y, i) := by
  have H := covStanding_rootTraceBg hC hk hδc hcap hsm hmar hα hD hs
  have hYr : IsNnComp (Yreg Gp (extS Gp s)) (Yreg Gp (extS Gp s)) :=
    ⟨subset_rfl, fun _ _ y' hy' _ => hy'⟩
  have hUT := unionOfTopBlocks_of_isNnComp hC.Sp hconn hYr
  unfold rootTraceBg
  exact rootTrace_eq_baseline_of_not_label H hconn (unitLabel Gp (Yreg Gp (extS Gp s)))
    (unitQ_label_top hUT) (unitP_label_top hUT) B hB

end TraceLocal

/-! ### Support of the mixed differences -/

section Support

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- The rooted trace with its background is the sum over the blocks of `B`. -/
theorem rootTraceBg_eq_sum_single (a : ℕ → ℝ) (aT ν ρ : ℝ) (B : Finset (unitPts Gp))
    (D : BgData Gp N) (s : DecParams Gp) :
    rootTraceBg Gp a aT ν ρ (unitQ Gp) (unitP Gp) B D s =
      ∑ y ∈ B, rootTraceBg Gp a aT ν ρ (unitQ Gp) (unitP Gp) {y} D s := by
  unfold rootTraceBg
  exact rootTrace_eq_sum_single B s _ _

/-- The mixed differences of the rooted trace with its background are the sums over the blocks. -/
theorem mixDiff_rootTraceBg_eq_sum (a : ℕ → ℝ) (aT ν ρ : ℝ) (B : Finset (unitPts Gp))
    (J : Finset (cubeIdx Gp)) (D : BgData Gp N) :
    mixDiff J (rootTraceBg Gp a aT ν ρ (unitQ Gp) (unitP Gp) B D) =
      ∑ y ∈ B, mixDiff J (rootTraceBg Gp a aT ν ρ (unitQ Gp) (unitP Gp) {y} D) := by
  have hfun : rootTraceBg Gp a aT ν ρ (unitQ Gp) (unitP Gp) B D =
      fun s => ∑ y ∈ B, rootTraceBg Gp a aT ν ρ (unitQ Gp) (unitP Gp) {y} D s :=
    funext fun s => rootTraceBg_eq_sum_single a aT ν ρ B D s
  rw [hfun]
  unfold mixDiff
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
  (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2) (hconn : HatConn Gp)
  {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)

include hC hk hδc hcap hsm hmar hα hconn hD

/-- **Switching on a parameter cube not joined to the root does not change the rooted trace with
its background.**  Let `I ⊆ J`, `p ∈ J`, and suppose no centre with `p` in its footprint is joined
to the unit block `y` by a chain in `J`.  Then the rooted traces of `{y}`, each at the decoupled
background of its own cut point, agree at `1_{I ∪ {p}}` and `1_I`. -/
theorem rootTraceBg_cut_insert_eq {J I : Finset (cubeIdx Gp)} {p : cubeIdx Gp}
    (hpJ : p ∈ J) (hIJ : I ⊆ J) (y : unitPts Gp)
    (hnc : ∀ q, RootChain Gp J y q → p ∉ QsetP Gp q) :
    rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp) (unitP Gp) {y} D
        (cutPt (insert p I)) =
      rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp) (unitP Gp) {y} D
        (cutPt I) := by
  classical
  have hsI : ∀ I' : Finset (cubeIdx Gp), ∀ P, ‖cutPt I' P‖ < Real.exp κ :=
    fun I' P => norm_cutPt_lt_exp hC.hκ I' P
  by_cases hatt : ∃ q0 ∈ Zs Gp (extS Gp (cutPt I)), HatAttached Gp y q0
  · obtain ⟨Y', hY, hY', hl, hsP⟩ := exists_root_comp hC.Sp hpJ hIJ y hnc hatt
    exact (rootTraceBg_eq_of_comp hC hk hδc hcap hsm hmar hα hconn (hsI I) (hsI (insert p I))
      hD hD hY hY' hsP (fun _ _ _ _ => ⟨rfl, fun _ => rfl⟩) {y}
      (fun y' hy' => by rw [Finset.mem_singleton.1 hy']; exact hl)).symm
  · -- no active centre is attached to `y`, at either cut point: both are the baseline
    have hatt' : ¬ ∃ q0 ∈ Zs Gp (extS Gp (cutPt (insert p I))), HatAttached Gp y q0 := by
      rintro ⟨q0, hq0, ha⟩
      have hq0' := mem_Zs_cutPt_iff.1 hq0
      have hact : ActIn Gp J q0 := by
        refine ⟨hq0'.1, hq0'.2.trans ?_⟩
        intro r hr
        rcases Finset.mem_insert.1 hr with h | h
        · exact h ▸ hpJ
        · exact hIJ h
      have hnp := hnc q0 (RootChain.of_attached hact ha)
      refine hatt ⟨q0, mem_Zs_cutPt_iff.2 ⟨hq0'.1, fun P hP => ?_⟩, ha⟩
      rcases Finset.mem_insert.1 (hq0'.2 hP) with h | h
      · exact absurd (h ▸ hP) hnp
      · exact h
    have hnl : ∀ I' : Finset (cubeIdx Gp),
        (¬ ∃ q0 ∈ Zs Gp (extS Gp (cutPt I')), HatAttached Gp y q0) →
        ∀ y' ∈ ({y} : Finset (unitPts Gp)), ¬ unitLabel Gp (Yreg Gp (extS Gp (cutPt I'))) y' := by
      intro I' hna y' hy' hlab
      rw [Finset.mem_singleton.1 hy'] at hlab
      obtain ⟨x₀, hx₀l, hx₀b⟩ := (mem_unitPts Gp).1 y.2
      have hx₀Ω : x₀ ∈ Gp.Ω 1 := Gp.layer_subset (by omega) le_rfl hx₀l
      obtain ⟨-, z, hz, hxz⟩ := mem_Yreg_iff.1 (hlab ⟨x₀, hx₀Ω⟩ hx₀b)
      exact hna ⟨z, hz, ⟨x₀, hx₀Ω⟩, hx₀b, hxz⟩
    rw [rootTraceBg_eq_baseline_of_not_label hC hk hδc hcap hsm hmar hα hconn
        (hsI (insert p I)) hD {y} (hnl _ hatt'),
      rootTraceBg_eq_baseline_of_not_label hC hk hδc hcap hsm hmar hα hconn
        (hsI I) hD {y} (hnl _ hatt)]

/-- **Vanishing for a block that is not joined to some `p ∈ J`** (cut-dependent background). -/
theorem mixDiff_rootTraceBg_single_eq_zero {J : Finset (cubeIdx Gp)} {p : cubeIdx Gp}
    (hpJ : p ∈ J) (y : unitPts Gp) (hnc : ∀ q, RootChain Gp J y q → p ∉ QsetP Gp q) :
    mixDiff J (rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp) (unitP Gp)
      {y} D) = 0 :=
  mixDiff_eq_zero_of_insert_eq hpJ _ fun _ hI =>
    rootTraceBg_cut_insert_eq hC hk hδc hcap hsm hmar hα hconn hD hpJ
      (hI.trans (Finset.erase_subset _ _)) y hnc

/-- **Support of the mixed differences of the rooted trace with cut-dependent backgrounds.**  Let
`D` be a datum of the chart `Ξ^c(𝔹_{k+1}; 1, ε)` and `F(s) = rootTraceBg B D s` the rooted trace of
the set `B` of unit blocks at the decoupled background `(φ_s, α_s)` of `D`.  If `Δ_J F ≠ 0` then
there is a block `y ∈ B` such that every parameter cube `p ∈ J` lies in the footprint of a centre
`q` which is joined to `y` by a chain of centres with footprints in `J` and consecutive `HatAdj`
thickened cubes, the last attached to `y` (`RootChain Gp J y q`). -/
theorem exists_rootChain_of_mixDiff_rootTraceBg_ne_zero (B : Finset (unitPts Gp))
    {J : Finset (cubeIdx Gp)}
    (hne : mixDiff J (rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp)
      (unitP Gp) B D) ≠ 0) :
    ∃ y ∈ B, ∀ p ∈ J, ∃ q, RootChain Gp J y q ∧ p ∈ QsetP Gp q := by
  by_contra h
  push Not at h
  apply hne
  rw [mixDiff_rootTraceBg_eq_sum]
  refine Finset.sum_eq_zero fun y hy => ?_
  obtain ⟨p, hpJ, hp⟩ := h y hy
  exact mixDiff_rootTraceBg_single_eq_zero hC hk hδc hcap hsm hmar hα hconn hD hpJ y hp

end Support

end Balaban.Fluctuation
