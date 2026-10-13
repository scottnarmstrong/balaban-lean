/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatLabelsGeom
public import Balaban.Fluctuation.RootActiveSize
public import Balaban.Fluctuation.DetOutputTerms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The collar hull of a set of cubes and the regrouped determinant terms

A term of the localized determinant expansion (`DetExpansionLocC`) for a set `T` of cubes of the
cover at scale `K` depends on the datum of the chart on the cells equal or `*`-adjacent to the
cells of `T`, which is wider than the polymer `sitesOf T` itself.  Here the polymer is replaced by
its *collar hull* `H(T)`: `sitesOf T` together with, for each cube `b` of `T` (a cell of side
`a = cellSide L m₀ m₁ K`), the aligned box of side `L a` based at `b - a (1, …, 1)`.  For `L ≥ 3`
this box contains the cell of `b` and all cells `*`-adjacent to it, also across a torus seam.

* `detCollarHull`: the hull; `detCollarHull_geometry` (contains `sitesOf T`, every site
  `CellNear` a site of `sitesOf T`, the root cube if `T` contains it; admissible, a polymer, when
  `sitesOf T` is a polymer).
* `detCollarHull_sizeJ_le`: `sizeJ H(T) ≤ dExt T + q |T| ≤ (1 + B) dExt T + B`, `q = cG d L`,
  `B = q c₁`.
* `detCollarHull_fibre`: the number of `T` with `H(T) = X` is at most `2^{c₁ (1 + sizeJ X)}`.
* `detCollarGrouped_bound`: for a family `e(T)` with `‖e T‖ ≤ c e^{-λ dExt T}`, supported on
  polymers, the regrouped family `e⁺(X) = ∑_{H(T) = X} e(T)` has the same total sum and
  `‖e⁺(X)‖ ≤ C_hull e^{-λ_hull sizeJ X}`, `λ_hull = λ/(1+B) - c₁ log 2`,
  `C_hull = c exp(λ B/(1+B) + c₁ log 2)`.
* `DetExpansionLocC.detGrouped_*`: the same for the terms of a `DetExpansionLocC`, and locality
  of the regrouped terms on the hull itself: two data of the chart that agree at the sites of
  `X` have the same regrouped term at `X`.

## What is not proved

Bounds and locality are on data of the chart only.  The inclusion of the class domain in the
chart, the rate requirement `λ_hull ≥ κ_out` (which needs the shared numerical tower) and the
symmetry of the regrouped terms are not proved here.  Nothing depends on the generator.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.SmallField
  Balaban.SmallField.Def6

section Hull

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

/-- The base of the centered collar box of the cell based at `c`: `c - a (1, …, 1)`. -/
def collarBase (a : ℕ) (c : CTorus d L N₁ m₁ K) : CTorus d L N₁ m₁ K :=
  pBase a c (fun _ => true)

/-- The bases of the collar boxes of a set of cubes. -/
noncomputable def collarBases (T : Finset 𝔅) : Finset (CTorus d L N₁ m₁ K) :=
  open Classical in T.image fun b => collarBase (cellSide L m₀ m₁ K) b.1

/-- **The collar hull** of a set `T` of cubes: the sites of `T` and, for each cube of `T`, the
aligned box of side `L a` based at its base minus `a (1, …, 1)`. -/
noncomputable def detCollarHull (T : Finset 𝔅) : Set (CTorus d L N₁ m₁ K) :=
  sitesOf T ∪ ⋃ p ∈ collarBases T, box p (L * cellSide L m₀ m₁ K)

omit [NeZero N₁] [NeZero L] in
theorem sitesOf_subset_detCollarHull (T : Finset 𝔅) : sitesOf T ⊆ detCollarHull T :=
  Set.subset_union_left

/-- The aligned box of side `L a` based at `c - a` contains the cells at index distance one. -/
theorem box_adj_subset_collar (hL : 3 ≤ L) {a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K)
    (c : CTorus d L N₁ m₁ K) (q : Fin d → ℤ) (hq : ∀ μ, |q μ| ≤ 1) :
    box (c + fun μ => (((a : ℤ) * q μ : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ K))) a ⊆
      box (collarBase a c) (L * a) := by
  rintro x ⟨w, hw, rfl⟩
  have hc := eq_pBase_add ha c (fun _ => true)
  refine ⟨(fun μ => a * (q μ + 1).toNat) + w, fun μ => ?_, ?_⟩
  · have h1 := abs_le.1 (hq μ)
    have h2 : (q μ + 1).toNat ≤ 2 := by omega
    have h3 : a * (q μ + 1).toNat ≤ a * 2 := Nat.mul_le_mul_left a h2
    have h4 : 3 * a ≤ L * a := Nat.mul_le_mul_right a hL
    have := hw μ
    simp only [Pi.add_apply]
    omega
  · rw [natT_add]
    funext μ
    have e1 : c μ = (collarBase a c) μ + ((a : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ K)) := by
      have := congrFun hc μ
      simp only [Pi.add_apply, natT_apply, ite_true] at this
      exact this
    have ht : (((q μ + 1).toNat : ℕ) : ℤ) = q μ + 1 :=
      Int.toNat_of_nonneg (by have := abs_le.1 (hq μ); omega)
    have e2 : (((a * (q μ + 1).toNat : ℕ) : ℤ)) = a * q μ + a := by
      push_cast; rw [ht]; ring
    have e3 := congrArg (Int.cast : ℤ → ZMod (N₁ * L ^ m₁ * L ^ K)) e2
    push_cast at e3
    simp only [Pi.add_apply, natT_apply]
    push_cast
    generalize (collarBase a c) μ = P at e1 ⊢
    rw [e1]
    linear_combination (-1 : ZMod (N₁ * L ^ m₁ * L ^ K)) * e3

omit [NeZero N₁] [NeZero L] in
theorem mem_collarBases_of_mem {T : Finset 𝔅} {b : 𝔅} (hb : b ∈ T) :
    collarBase (cellSide L m₀ m₁ K) b.1 ∈ collarBases T := by
  classical
  exact Finset.mem_image.2 ⟨b, hb, rfl⟩

/-- Every site `v` whose cell is equal or `*`-adjacent to the cell of a site of `T` lies in the
collar hull of `T`: the dependency set of a determinant term is inside the hull. -/
theorem cellNear_mem_detCollarHull (hL : 3 ≤ L) (hN : L ^ m₀ ∣ N₁) {T : Finset 𝔅}
    {x v : CTorus d L N₁ m₁ K} (hx : x ∈ sitesOf T) (hxv : CellNear m₀ K x v) :
    v ∈ detCollarHull T := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  obtain ⟨b, hb, hxb⟩ := mem_sitesOf.1 hx
  have e := cbase_eq_of_mem_box hdvd b.2.1 hxb
  obtain ⟨q, hq, hqv⟩ := hxv
  refine Or.inr (Set.mem_iUnion₂.2 ⟨_, mem_collarBases_of_mem hb, ?_⟩)
  refine box_adj_subset_collar hL hdvd b.1 q hq ?_
  have hm := mem_box_cbase ha0 v
  rw [hqv, e] at hm
  exact hm

omit [NeZero N₁] [NeZero L] in
/-- A cube of `T` (for instance the root cube) lies in the hull of `T`. -/
theorem box_subset_detCollarHull {T : Finset 𝔅} {b : 𝔅} (hb : b ∈ T) :
    box b.1 (cellSide L m₀ m₁ K) ⊆ detCollarHull T :=
  fun _ hz => Or.inl (mem_sitesOf.2 ⟨b, hb, hz⟩)

omit [NeZero N₁] [NeZero L] in
/-- A set in `𝒟_K` is a polymer: the cubes contained in it are a chosen family. -/
theorem isPolyDom_of_isDj {X : Set (CTorus d L N₁ m₁ K)} (hX : IsDj m₀ K X) :
    IsPolyDom m₀ K X := by
  obtain ⟨hne, hpi, hcon⟩ := hX
  refine ⟨hne, ⟨{b | Aligned (cellSide L m₀ m₁ K) b ∧
    box b (L * cellSide L m₀ m₁ K) ⊆ X}, fun b hb => hb, fun z hz => ?_⟩, hcon⟩
  obtain ⟨b, h1, h2, h3⟩ := hpi z hz
  exact ⟨b, ⟨h1, h3⟩, h2⟩

theorem detCollarHull_isDj (hL : 3 ≤ L) (hN : L ^ m₀ ∣ N₁) {T : Finset 𝔅}
    (hT : IsPolyDom m₀ K (sitesOf T)) :
    IsDj m₀ K (detCollarHull T) ∧
      treeLenCovOne m₀ K (detCollarHull T) ≤
        treeLenCovOne m₀ K (sitesOf T) + (collarBases T).card * cG d L := by
  classical
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  refine thick_union (m₀ := m₀) (j := K) (isDj_of_isPolyDom hT) (collarBases T) ?_
  intro p hp
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hp
  refine ⟨pBase_aligned hdvd b.2.1 _, b.1, b.2.1, fun x hx => ⟨?_, ?_⟩⟩
  · exact (mem_sitesOf.2 ⟨b, hb, hx⟩)
  · exact box_subset_of_offset (by omega) (eq_pBase_add hdvd b.1 (fun _ => true))
      (fun μ => by simp) hx

/-- The collar cost constant `B = q c₁`, with `q = cG d L` the cost of one added box. -/
noncomputable def collarB (d L : ℕ) : ℝ := cG d L * c1 d L

omit [NeZero N₁] in
theorem collarB_nonneg (d L : ℕ) [NeZero L] : 0 ≤ collarB d L := by
  have h1 := one_le_c1 d L
  unfold collarB cG
  positivity

/-- **Size of the hull.**  For a polymer `sitesOf T`:
`sizeJ H(T) ≤ dExt T + q |T| ≤ (1 + B) dExt T + B`. -/
theorem detCollarHull_sizeJ_le (hL : 3 ≤ L) (hN : L ^ m₀ ∣ N₁) {T : Finset 𝔅}
    (hT : IsPolyDom m₀ K (sitesOf T)) :
    sizeJ m₀ K (detCollarHull T) ≤ dExt T + (T.card : ℝ) * cG d L ∧
      sizeJ m₀ K (detCollarHull T) ≤ (1 + collarB d L) * dExt T + collarB d L := by
  classical
  have hg : 0 ≤ cG d L := by unfold cG; positivity
  have h1 := (detCollarHull_isDj hL hN hT).2
  have h2 : ((collarBases T).card : ℝ) ≤ T.card := by
    exact_mod_cast (Finset.card_image_le : (collarBases T).card ≤ T.card)
  have hd := dExt_eq_sizeJ_of_isPolyDom hT
  have h3 : sizeJ m₀ K (detCollarHull T) ≤ dExt T + (T.card : ℝ) * cG d L := by
    have h1' : sizeJ m₀ K (detCollarHull T) ≤ sizeJ m₀ K (sitesOf T) +
        ((collarBases T).card : ℝ) * cG d L := h1
    rw [hd]
    nlinarith [mul_le_mul_of_nonneg_right h2 hg]
  refine ⟨h3, ?_⟩
  have h4 := card_le_dExt (m₀ := m₀) (j := K) hN (le_refl K) T
  have h5 : (T.card : ℝ) * cG d L ≤ collarB d L * (1 + dExt T) := by
    unfold collarB
    nlinarith [mul_le_mul_of_nonneg_right h4 hg]
  nlinarith

section Fibre

variable (m₀)

/-- The finset of sets of cubes with hull `X`. -/
noncomputable def detCollarFibre (X : Set (CTorus d L N₁ m₁ K)) : Finset (Finset 𝔅) :=
  open Classical in Finset.univ.filter fun T => detCollarHull T = X

variable {m₀}

theorem mem_detCollarFibre {X : Set (CTorus d L N₁ m₁ K)} {T : Finset 𝔅} :
    T ∈ detCollarFibre m₀ X ↔ detCollarHull T = X := by
  classical
  simp [detCollarFibre]

end Fibre

/-- **Fibre count.**  For `X ∈ 𝒟_K`, the number of sets `T` of cubes with `H(T) = X` is at most
`2^{c₁ (1 + sizeJ X)}`: every such `T` is a set of cells of `X`. -/
theorem detCollarHull_fibre (hN : L ^ m₀ ∣ N₁) {X : Set (CTorus d L N₁ m₁ K)}
    (hX : IsDj m₀ K X) :
    ((detCollarFibre m₀ X).card : ℝ) ≤ (2 : ℝ) ^ (c1 d L * (1 + sizeJ m₀ K X)) := by
  classical
  have hsub : detCollarFibre m₀ X ⊆ (blocksOf m₀ K Set.univ X).powerset := by
    intro T hT
    rw [mem_detCollarFibre] at hT
    refine Finset.mem_powerset.2 fun b hb => mem_blocksOf.2 ?_
    rw [← hT]
    exact box_subset_detCollarHull hb
  have h1 : (detCollarFibre m₀ X).card ≤ 2 ^ (blocksOf m₀ K Set.univ X).card := by
    simpa using Finset.card_le_card hsub
  have h2 : (((blocksOf m₀ K Set.univ X).card : ℕ) : ℝ) ≤ c1 d L * (1 + sizeJ m₀ K X) :=
    card_blocksOf_le hN (le_refl K) hX
  calc ((detCollarFibre m₀ X).card : ℝ) ≤ ((2 ^ (blocksOf m₀ K Set.univ X).card : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ = (2 : ℝ) ^ (((blocksOf m₀ K Set.univ X).card : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; push_cast; rfl
    _ ≤ (2 : ℝ) ^ (c1 d L * (1 + sizeJ m₀ K X)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h2

/-- The regrouped family `e⁺(X) = ∑_{H(T) = X} e(T)`. -/
noncomputable def detCollarGrouped {E : Type*} [AddCommMonoid E] (e : Finset 𝔅 → E)
    (X : Set (CTorus d L N₁ m₁ K)) : E :=
  ∑ T ∈ detCollarFibre m₀ X, e T

/-- The hull rate `λ_hull = λ/(1 + B) - c₁ log 2`. -/
noncomputable def hullRate (d L : ℕ) (lam : ℝ) : ℝ :=
  lam / (1 + collarB d L) - c1 d L * Real.log 2

/-- The hull constant `C_hull = c exp(λ B/(1 + B) + c₁ log 2)`. -/
noncomputable def hullConst (d L : ℕ) (lam c : ℝ) : ℝ :=
  c * Real.exp (lam * collarB d L / (1 + collarB d L) + c1 d L * Real.log 2)

/-- **The sum identity**: regrouping does not change the total. -/
theorem sum_detCollarGrouped {E : Type*} [AddCommMonoid E] (e : Finset 𝔅 → E) :
    ∑ X ∈ (Finset.univ : Finset (Finset 𝔅)).image detCollarHull, detCollarGrouped e X =
      ∑ T, e T := by
  classical
  have := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Finset 𝔅)))
    (t := (Finset.univ : Finset (Finset 𝔅)).image detCollarHull) (g := detCollarHull) (f := e)
    (fun T hT => Finset.mem_image_of_mem _ hT)
  rw [← this]
  refine Finset.sum_congr rfl fun X _ => ?_
  unfold detCollarGrouped
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext T
  rw [mem_detCollarFibre]
  simp

/-- **The regrouped bound.**  If `‖e T‖ ≤ c e^{-λ dExt T}` and `e T ≠ 0` only for polymers
`sitesOf T`, then `‖e⁺(X)‖ ≤ C_hull e^{-λ_hull sizeJ X}`. -/
theorem detCollarGrouped_bound (hL : 3 ≤ L) (hN : L ^ m₀ ∣ N₁) {c lam : ℝ} (hc : 0 ≤ c)
    (hlam : 0 ≤ lam) (e : Finset 𝔅 → ℂ)
    (hsupp : ∀ T, e T ≠ 0 → IsPolyDom m₀ K (sitesOf T))
    (hb : ∀ T, ‖e T‖ ≤ c * Real.exp (-lam * dExt T)) (X : Set (CTorus d L N₁ m₁ K)) :
    ‖detCollarGrouped e X‖ ≤ hullConst d L lam c * Real.exp (-hullRate d L lam * sizeJ m₀ K X) := by
  classical
  have hB := collarB_nonneg d L
  have hpos : 0 ≤ hullConst d L lam c * Real.exp (-hullRate d L lam * sizeJ m₀ K X) := by
    unfold hullConst; positivity
  by_cases hex : ∃ T ∈ detCollarFibre m₀ X, e T ≠ 0
  swap
  · push Not at hex
    have : detCollarGrouped e X = 0 := Finset.sum_eq_zero hex
    rw [this, norm_zero]; exact hpos
  obtain ⟨T0, hT0, hne⟩ := hex
  have hX : IsDj m₀ K X := by
    rw [← mem_detCollarFibre.1 hT0]
    exact (detCollarHull_isDj hL hN (hsupp T0 hne)).1
  set s := sizeJ m₀ K X with hs
  set M : ℝ := c * Real.exp (-lam * (s - collarB d L) / (1 + collarB d L)) with hM
  have hterm : ∀ T ∈ detCollarFibre m₀ X, ‖e T‖ ≤ M := by
    intro T hT
    by_cases h0 : e T = 0
    · rw [h0, norm_zero, hM]; positivity
    · have hTX := mem_detCollarFibre.1 hT
      have h1 := (detCollarHull_sizeJ_le hL hN (hsupp T h0)).2
      rw [hTX] at h1
      refine (hb T).trans ?_
      rw [hM]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc
      have hp : 0 < 1 + collarB d L := by linarith
      rw [le_div_iff₀ hp]
      nlinarith
  have hfib := detCollarHull_fibre hN hX
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  calc ‖detCollarGrouped e X‖ ≤ ∑ T ∈ detCollarFibre m₀ X, ‖e T‖ := norm_sum_le _ _
    _ ≤ ∑ T ∈ detCollarFibre m₀ X, M := Finset.sum_le_sum hterm
    _ = (detCollarFibre m₀ X).card * M := by simp
    _ ≤ (2 : ℝ) ^ (c1 d L * (1 + s)) * M := mul_le_mul_of_nonneg_right hfib hM0
    _ = hullConst d L lam c * Real.exp (-hullRate d L lam * s) := by
        rw [Real.rpow_def_of_pos (by norm_num), hM, hullConst, hullRate]
        have hp : (1 + collarB d L) ≠ 0 := by linarith
        have : Real.log 2 * (c1 d L * (1 + s)) + -lam * (s - collarB d L) / (1 + collarB d L) =
            (lam * collarB d L / (1 + collarB d L) + c1 d L * Real.log 2) +
              -(lam / (1 + collarB d L) - c1 d L * Real.log 2) * s := by
          field_simp
          ring
        calc Real.exp (Real.log 2 * (c1 d L * (1 + s))) *
              (c * Real.exp (-lam * (s - collarB d L) / (1 + collarB d L)))
            = c * Real.exp (Real.log 2 * (c1 d L * (1 + s)) +
                -lam * (s - collarB d L) / (1 + collarB d L)) := by
              rw [Real.exp_add]; ring
          _ = _ := by rw [this, Real.exp_add]; ring

end Hull

section DetStep

open Balaban.Background Balaban.Analysis Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {m₀ : ℕ}
  {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} {eps κ'' cdet : ℝ}

/-- **The regrouped determinant terms**: `det⁺(X; D) = ∑_{H(T) = X} term D T`. -/
noncomputable def DetExpansionLocC.detGrouped (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (D : BgData S.G' N) (X : Set (CTorus d L N₁ m₁ (k + 1))) : ℂ :=
  detCollarGrouped (fun T => E.term D T) X

/-- The regrouped terms have the same total as the original ones, which is the root trace. -/
theorem DetExpansionLocC.detGrouped_sum (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    {D : BgData S.G' N} (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D) :
    ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := k + 1) m₀ (k + 1) Set.univ))).image detCollarHull, E.detGrouped D X =
      rootTrace S.G' S.a S.a₁ S.ν (unitQ S.G') (unitP S.G') (S.blockU z) (fun _ => 1)
        (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) D))
        (bgMultC S.G' S.a S.ν (bgC0 d L N) D) := by
  rw [E.sum_eq D hD]
  exact sum_detCollarGrouped (fun T => E.term D T)

/-- **The regrouped bound** for the determinant terms: if `3 ≤ L`, `0 ≤ c_det`, `0 ≤ κ''`,
then `‖det⁺(X; D)‖ ≤ C_hull e^{-λ_hull sizeJ X}`, `λ = κ''`. -/
theorem DetExpansionLocC.detGrouped_bound (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (hL : 3 ≤ L) (hN : L ^ m₀ ∣ N₁) (hc : 0 ≤ cdet) (hκ : 0 ≤ κ'')
    {D : BgData S.G' N} (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (X : Set (CTorus d L N₁ m₁ (k + 1))) :
    ‖E.detGrouped D X‖ ≤
      hullConst d L κ'' cdet * Real.exp (-hullRate d L κ'' * sizeJ m₀ (k + 1) X) :=
  detCollarGrouped_bound hL hN hc hκ (fun T => E.term D T)
    (fun T hT => (E.anchor D hD T hT).2) (E.bound D hD) X

/-- **The root clause**: a nonzero regrouped term sits on a polymer hull containing the root cube
(all of its sites). -/
theorem DetExpansionLocC.detGrouped_anchor (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (hL : 3 ≤ L) (hN : L ^ m₀ ∣ N₁)
    {D : BgData S.G' N} (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    {X : Set (CTorus d L N₁ m₁ (k + 1))} (hX : E.detGrouped D X ≠ 0) :
    IsPolyDom m₀ (k + 1) X ∧
      box (rootCube (m₀ := m₀) (K := k + 1) z).1 (cellSide L m₀ m₁ (k + 1)) ⊆ X := by
  obtain ⟨T, hT, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hX
  have hTX := mem_detCollarFibre.1 hT
  obtain ⟨hroot, hpoly⟩ := E.anchor D hD T hne
  subst hTX
  exact ⟨isPolyDom_of_isDj (detCollarHull_isDj hL hN hpoly).1, box_subset_detCollarHull hroot⟩

/-- **Locality on the hull itself** (chart data): two data of the chart that agree at every site
of `X` have the same regrouped term at `X`. -/
theorem DetExpansionLocC.detGrouped_local (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (hL : 3 ≤ L) (hN : L ^ m₀ ∣ N₁) (h3 : 3 ≤ L ^ (m₀ + m₁))
    {D D₂ : BgData S.G' N} (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (hD₂ : XiCData S.G' S.a S.ν (k + 1) 1 eps D₂)
    {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (h : ∀ v ∈ X, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) :
    E.detGrouped D X = E.detGrouped D₂ X := by
  unfold DetExpansionLocC.detGrouped detCollarGrouped
  refine Finset.sum_congr rfl fun T hT => ?_
  have hTX := mem_detCollarFibre.1 hT
  refine E.term_eq_of_agree_cellNear hN h3 hD hD₂ T fun v ⟨x, hx, hxv⟩ => h v ?_
  rw [← hTX]
  exact cellNear_mem_detCollarHull hL hN hx hxv

end DetStep

end Balaban.Fluctuation
