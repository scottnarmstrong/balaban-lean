/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RGasRepR4Fresh

/-!
# The new boundary term `ℬ′` as a sum of root coefficients (P7 (3.22)–(3.25))

P7 pp. 526–527 "pre-localizes" the difference of the old and the new exponent in cubes and in the
localized terms of the effective action, constructs the localization expansion of each piece
(P3 §4, Proposition 4.3; `Localization.localization_expansion`) and resums the terms with the same
final localization domain.  A piece is a *root* `r` with its cut parameters `ι r` (the cubes `c r i`
of the cover off the root region `X₁ r`) and its decoupled extension `F r S` (the root summand of the
residual at the decoupled fields, `S` the set of removed members).  The new boundary term at the
final domain `Y` is the sum over the roots of the P3 coefficients:
`ℬ′_Y(S) = ∑_r r4Fresh_r(S, Y)` (`bPrime`).

* `bPrime_aggregate_of_localization`: under the P3 premises of every root (`RootLocPremises`), the
  sum of the root summands at `s = 1` is the sum of `ℬ′_Y(S)` over the final domains, each `ℬ′_Y(S)`
  depends on the data only through the agreement `AgY Y`, is bounded by the sum of the root bounds
  `Eb_r e^{-κ₀ Δ_r - 2κ d̃^cov(Y)}`, and is analytic;
* `bPrime_congr_cut`: `ℬ′_Y(S) = ℬ′_Y(S')` when every root extension of `S` and of `S'` agrees on
  the cuts of each connected family ending at `Y` (P7 p. 528: a boundary term depends on the removed
  members only through those it meets);
* `bPrime_empty`: `ℬ′_Y(∅) = 0` when the root extensions vanish for no removed member;
* `r4Coupling_bPrime_empty`: the decorated coupling with `fresh = ℬ′` vanishes for no removed member.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Analysis Finset

/-! ### The coefficient of the zero function -/

section Zero

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

omit [Fintype ι] in
theorem pderList_zero_fun : ∀ (l : List ι), pderList l (fun _ : ι → ℂ => (0 : ℂ)) = fun _ => 0
  | [] => rfl
  | i :: l => by
    have h : pder i (fun _ : ι → ℂ => (0 : ℂ)) = fun _ => 0 := by
      funext s
      simp [pder]
    rw [pderList_cons, h]
    exact pderList_zero_fun l

omit [Fintype ι] in
theorem iterInt_zero_fun :
    ∀ (l : List ι) (s : ι → ℂ), iterInt l (fun _ : ι → ℂ => (0 : ℂ)) s = 0
  | [], _ => rfl
  | j :: l, s => by
    simp only [iterInt]
    have h : ∀ t : ℝ, iterInt l (fun _ : ι → ℂ => (0 : ℂ)) (Function.update s j (t : ℂ)) = 0 :=
      fun t => iterInt_zero_fun l _
    simp [h]

/-- The P3 coefficient of the zero function is zero. -/
theorem coef_zero_fun (C : Finset ι) : coef (fun _ : ι → ℂ => (0 : ℂ)) C = 0 := by
  unfold coef
  rw [pderList_zero_fun]
  exact iterInt_zero_fun _ _

end Zero

/-! ### `ℬ′` -/

section Sum

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}
  {Rt : Type*} {ι : Rt → Type*} [∀ r, DecidableEq (ι r)] [∀ r, Fintype (ι r)] {Zt U : Type*}

variable (G m₀) in
/-- **The new boundary term `ℬ′_Y(S)`** (P7 (3.22)–(3.25)): the sum over the roots `r` of the P3
coefficients `r4Fresh` of the root extensions `F r` at the final domain `Y` and the removed members
`S`. -/
noncomputable def bPrime (roots : Finset Rt) (c : ∀ r, ι r → ℕ × CTorus d L N₁ m₁ K)
    (X₁ : Rt → Set (CTorus d L N₁ m₁ K)) (F : ∀ r, Finset Zt → U → (ι r → ℂ) → ℂ)
    (S : Finset Zt) (Y : Set (CTorus d L N₁ m₁ K)) (u : U) : ℂ :=
  ∑ r ∈ roots, r4Fresh (G := G) (m₀ := m₀) (c r) (X₁ r) (F r) S Y u

variable (G m₀) in
/-- The final domains of the roots: the union of the polymer domains of the connected families of
every root. -/
noncomputable def bPrimeDomains [DecidableEq (Set (CTorus d L N₁ m₁ K))] (roots : Finset Rt)
    (c : ∀ r, ι r → ℕ × CTorus d L N₁ m₁ K) (X₁ : Rt → Set (CTorus d L N₁ m₁ K)) :
    Finset (Set (CTorus d L N₁ m₁ K)) :=
  roots.biUnion fun r => polymerDomains (c r) G m₀ (X₁ r)

theorem bPrime_apply (roots : Finset Rt) (c : ∀ r, ι r → ℕ × CTorus d L N₁ m₁ K)
    (X₁ : Rt → Set (CTorus d L N₁ m₁ K)) (F : ∀ r, Finset Zt → U → (ι r → ℂ) → ℂ)
    (S : Finset Zt) (Y : Set (CTorus d L N₁ m₁ K)) (u : U) :
    bPrime G m₀ roots c X₁ F S Y u =
      ∑ r ∈ roots, r4Fresh (G := G) (m₀ := m₀) (c r) (X₁ r) (F r) S Y u := rfl

omit [∀ r, Fintype (ι r)] in
/-- A coefficient vanishes at a domain that is not the domain of a connected family. -/
theorem r4Fresh_eq_zero_of_not_mem {ι₀ : Type*} [DecidableEq ι₀] [Fintype ι₀]
    (c : ι₀ → ℕ × CTorus d L N₁ m₁ K) (X₁ : Set (CTorus d L N₁ m₁ K))
    (F : Finset Zt → U → (ι₀ → ℂ) → ℂ) (S : Finset Zt) {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : Y ∉ polymerDomains c G m₀ X₁) (u : U) :
    r4Fresh (G := G) (m₀ := m₀) c X₁ F S Y u = 0 := by
  classical
  rw [r4Fresh_apply]
  refine Finset.sum_eq_zero fun C hC => ?_
  exfalso
  obtain ⟨hconn, hYC⟩ := (mem_connFams c).1 hC
  refine hY ?_
  unfold polymerDomains
  rw [← hYC]
  exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hconn⟩)

omit [∀ r, Fintype (ι r)] in
/-- A coefficient of an extension vanishing identically is zero. -/
theorem r4Fresh_eq_zero_of_zero {ι₀ : Type*} [DecidableEq ι₀] [Fintype ι₀]
    (c : ι₀ → ℕ × CTorus d L N₁ m₁ K) (X₁ : Set (CTorus d L N₁ m₁ K))
    (F : Finset Zt → U → (ι₀ → ℂ) → ℂ) (S : Finset Zt) (Y : Set (CTorus d L N₁ m₁ K)) (u : U)
    (h0 : ∀ w, F S u w = 0) :
    r4Fresh (G := G) (m₀ := m₀) c X₁ F S Y u = 0 := by
  rw [r4Fresh_apply]
  refine Finset.sum_eq_zero fun C _ => ?_
  rw [show F S u = fun _ => 0 from funext h0]
  exact coef_zero_fun C

/-- **`ℬ′_Y(∅) = 0`**: if every root extension vanishes for no removed member, so does `ℬ′`. -/
theorem bPrime_empty (roots : Finset Rt) (c : ∀ r, ι r → ℕ × CTorus d L N₁ m₁ K)
    (X₁ : Rt → Set (CTorus d L N₁ m₁ K)) (F : ∀ r, Finset Zt → U → (ι r → ℂ) → ℂ)
    (h0 : ∀ r ∈ roots, ∀ u w, F r ∅ u w = 0) (Y : Set (CTorus d L N₁ m₁ K)) (u : U) :
    bPrime G m₀ roots c X₁ F ∅ Y u = 0 :=
  Finset.sum_eq_zero fun r hr => r4Fresh_eq_zero_of_zero (G := G) (m₀ := m₀) (c r) (X₁ r) (F r)
    ∅ Y u (h0 r hr u)

/-- **Cut-locality of `ℬ′`** (P7 p. 528): if, for every root, the extensions of `S` and of `S'`
agree on the cuts of every connected family ending at `Y`, then `ℬ′_Y(S) = ℬ′_Y(S')`.  The
application takes for `S'` the members of `S` that meet `Y`. -/
theorem bPrime_congr_cut (roots : Finset Rt) (c : ∀ r, ι r → ℕ × CTorus d L N₁ m₁ K)
    (X₁ : Rt → Set (CTorus d L N₁ m₁ K)) (F : ∀ r, Finset Zt → U → (ι r → ℂ) → ℂ)
    (S S' : Finset Zt) (Y : Set (CTorus d L N₁ m₁ K)) (u : U)
    (hcut : ∀ r ∈ roots, ∀ C ∈ connFams (c r) G m₀ (X₁ r) Y,
      ∀ w ∈ supportedOn C, F r S u w = F r S' u w) :
    bPrime G m₀ roots c X₁ F S Y u = bPrime G m₀ roots c X₁ F S' Y u :=
  Finset.sum_congr rfl fun r hr =>
    r4Fresh_congr_cut (G := G) (m₀ := m₀) (c r) (X₁ r) (F r) S S' Y u (hcut r hr)

/-- **The decorated coupling with `fresh = ℬ′` vanishes for no removed member** (the hypothesis
`hfresh` of `gasR4Decor_eq`), when the old coupling at no removed member is the kept one. -/
theorem r4Coupling_bPrime_empty {Xt : Type*} (roots : Finset Rt)
    (c : ∀ r, ι r → ℕ × CTorus d L N₁ m₁ K) (X₁ : Rt → Set (CTorus d L N₁ m₁ K))
    (F : ∀ r, Finset Zt → U → (ι r → ℂ) → ℂ) (h0 : ∀ r ∈ roots, ∀ u w, F r ∅ u w = 0)
    (dom : Xt → Set (CTorus d L N₁ m₁ K)) (u : U) (old : Xt → Finset Zt → ℂ) (kept : Xt → ℂ)
    (hbase : ∀ x, old x ∅ = kept x) (x : Xt) :
    r4Coupling old (fun x S => bPrime G m₀ roots c X₁ F S (dom x) u) kept x ∅ = 0 :=
  r4Coupling_empty old _ kept hbase (fun x => bPrime_empty roots c X₁ F h0 (dom x) u) x

/-- **The resummation over the roots** (algebra): if the extension of every root at `s = 1` is the
sum of its coefficients over its polymer domains, the sum of the root extensions at `s = 1` is the
sum of `ℬ′` over the final domains of all roots. -/
theorem sum_one_eq_sum_bPrime [DecidableEq (Set (CTorus d L N₁ m₁ K))] (roots : Finset Rt)
    (c : ∀ r, ι r → ℕ × CTorus d L N₁ m₁ K) (X₁ : Rt → Set (CTorus d L N₁ m₁ K))
    (F : ∀ r, Finset Zt → U → (ι r → ℂ) → ℂ) (S : Finset Zt) (u : U)
    (h : ∀ r ∈ roots, F r S u 1 = ∑ Y ∈ polymerDomains (c r) G m₀ (X₁ r),
      r4Fresh (G := G) (m₀ := m₀) (c r) (X₁ r) (F r) S Y u) :
    ∑ r ∈ roots, F r S u 1 =
      ∑ Y ∈ bPrimeDomains G m₀ roots c X₁, bPrime G m₀ roots c X₁ F S Y u := by
  unfold bPrime
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [h r hr]
  refine Finset.sum_subset (fun Y hY => Finset.mem_biUnion.2 ⟨r, hr, hY⟩) fun Y _ hY => ?_
  exact r4Fresh_eq_zero_of_not_mem (G := G) (m₀ := m₀) (c r) (X₁ r) (F r) S hY u

end Sum

/-! ### The P3 premises of one root and the aggregate identity -/

section Aggregate

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ} {U : Type*}
  [NormedAddCommGroup U] [NormedSpace ℂ U]

variable (G m₀) in
/-- **The P3 §4 premises of one root** (the hypotheses of `localization_expansion` other than the
numerical constants): the root `X` at the level `j` with its chosen family `𝒦X` (`CovSetup`), the cut
cubes `c i` of the cover, distinct and off the root region `X₁ = X1 G m₀ j 𝒦X`, the tree-length
witness of `X`; the agreement relations `Ag` of the data on the families and `AgY` on the domains;
the extension `F` analytic on `Su ×` the polydisc `|s_i| < e^{κ₁}`, bounded there by
`Eb e^{-(κ-1) d^cov_j(X)}`, and local (AE2). -/
structure RootLocPremises {ι : Type*} [DecidableEq ι] [Fintype ι]
    (c : ι → ℕ × CTorus d L N₁ m₁ K) (j : ℕ) (X 𝒦X : Set (CTorus d L N₁ m₁ K))
    (κ κ₁ Eb : ℝ) (Su : Set U) (Ag : Finset ι → U → U → Prop)
    (AgY : Set (CTorus d L N₁ m₁ K) → U → U → Prop) (F : U → (ι → ℂ) → ℂ) : Prop where
  cov : CovSetup G m₀ j X 𝒦X
  mem : ∀ i, c i ∈ cubeIdx G
  inj : Function.Injective c
  disj : ∀ i, Disjoint (Pset m₁ (c i)) (X1 G m₀ j 𝒦X)
  opt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X
  Eb_nonneg : 0 ≤ Eb
  refl : ∀ C u, u ∈ Su → Ag C u u
  link : ∀ C u u', AgY (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) u u' → Ag C u u'
  ana : AnalyticOnNhd ℂ (fun p : U × (ι → ℂ) => F p.1 p.2)
    (Su ×ˢ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁))
  bd : ∀ u ∈ Su, ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁),
    ‖F u s‖ ≤ Eb * Real.exp (-(κ - 1) * treeLenCovOne m₀ j X)
  loc : LocalityAEOn (Real.exp κ₁) Su (fun i => Pset m₁ (c i)) (compY c (X1 G m₀ j 𝒦X)) Ag F

variable {Rt : Type*} {ι : Rt → Type*} [∀ r, DecidableEq (ι r)] [∀ r, Fintype (ι r)] {Zt : Type*}

/-- **The aggregate identity of P7 (3.22)–(3.25) for `ℬ′`**, from the P3 premises of every root.
With the root regions `X₁ r = X1 G m₀ (j r) (𝒦X r)`:
1. `∑_r F_r(S; u, 1) = ∑_{Y} ℬ′_Y(S; u)` over the final domains of all roots;
2. `ℬ′_Y(S)` depends on the data only through `AgY Y`;
3. `‖ℬ′_Y(S; u)‖ ≤ ∑_r Eb_r e^{-κ₀ d^cov_{j_r}(X_r) - 2κ d̃^cov(Y)}`;
4. `ℬ′_Y(S)` is analytic on `Su`. -/
theorem bPrime_aggregate_of_localization [DecidableEq (Set (CTorus d L N₁ m₁ K))]
    (hd : 3 ≤ d) (hL : 3 ≤ L)
    {κ κ₀ κ₁ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκ : 3 * κ₀ + 3 ≤ κ)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κ ≤ κ₁)
    (h1 : 1 ≤ (κ₁ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2)
    {roots : Finset Rt} {c : ∀ r, ι r → ℕ × CTorus d L N₁ m₁ K} {j : Rt → ℕ}
    {X 𝒦X : Rt → Set (CTorus d L N₁ m₁ K)} {Eb : Rt → ℝ} {Su : Set U}
    {Ag : ∀ r, Finset (ι r) → U → U → Prop} {AgY : Set (CTorus d L N₁ m₁ K) → U → U → Prop}
    {F : ∀ r, Finset Zt → U → (ι r → ℂ) → ℂ} {S : Finset Zt}
    (hR : ∀ r ∈ roots, RootLocPremises G m₀ (c r) (j r) (X r) (𝒦X r) κ κ₁ (Eb r) Su (Ag r) AgY
      (F r S)) :
    (∀ u ∈ Su, ∑ r ∈ roots, F r S u 1 =
      ∑ Y ∈ bPrimeDomains G m₀ roots c (fun r => X1 G m₀ (j r) (𝒦X r)),
        bPrime G m₀ roots c (fun r => X1 G m₀ (j r) (𝒦X r)) F S Y u) ∧
    (∀ Y, ∀ u ∈ Su, ∀ u' ∈ Su, AgY Y u u' →
      bPrime G m₀ roots c (fun r => X1 G m₀ (j r) (𝒦X r)) F S Y u =
        bPrime G m₀ roots c (fun r => X1 G m₀ (j r) (𝒦X r)) F S Y u') ∧
    (∀ Y, ∀ u ∈ Su, ‖bPrime G m₀ roots c (fun r => X1 G m₀ (j r) (𝒦X r)) F S Y u‖ ≤
      ∑ r ∈ roots, Eb r * Real.exp (-κ₀ * treeLenCovOne m₀ (j r) (X r) -
        2 * κ * treeLenCov G m₀ Y)) ∧
    (∀ Y, AnalyticOnNhd ℂ (bPrime G m₀ roots c (fun r => X1 G m₀ (j r) (𝒦X r)) F S Y) Su) := by
  have hloc : ∀ r ∈ roots, _ := fun r hr =>
    r4Fresh_aggregate_of_localization (G := G) (m₀ := m₀) (c r) (hR r hr).cov hd hL (hR r hr).mem
      (hR r hr).inj (hR r hr).disj (hR r hr).opt hκ₀ hκ hκ₁ h1 hlog (hR r hr).Eb_nonneg (F r) S
      (hR r hr).refl (hR r hr).link (hR r hr).ana (hR r hr).bd (hR r hr).loc
  refine ⟨fun u hu => ?_, fun Y u hu u' hu' huu => ?_, fun Y u hu => ?_, fun Y => ?_⟩
  · exact sum_one_eq_sum_bPrime roots c _ F S u fun r hr => (hloc r hr).1 u hu
  · exact Finset.sum_congr rfl fun r hr => (hloc r hr).2.1 Y u hu u' hu' huu
  · unfold bPrime
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => (hloc r hr).2.2.1 Y u hu)
  · unfold bPrime
    intro u hu
    have := Finset.analyticAt_fun_sum (𝕜 := ℂ) roots
      (f := fun r u => r4Fresh (G := G) (m₀ := m₀) (c r) (X1 G m₀ (j r) (𝒦X r)) (F r) S Y u)
      (fun r hr => (hloc r hr).2.2.2 Y u hu)
    exact this

end Aggregate

end Balaban.LargeField
