/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseTwoTorusGreen
public import Balaban.Polymer.TwoTorusDecCov
public import Balaban.LargeField.Base.BaseXLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The constrained correction `Z_{x,s} = Ĝ_{k,x,s} - Π_{x,s}` of the x-variant on two tori

For the top-level generating sets `levelGS (k + 1)` of two tori `CTorus d L N₁ m₁ (k + 1)` and
`CTorus d L N₁' m₁ (k + 1)`, identified on a centred box by `boxMap`, this file compares the rows of
the operators entering the first step's shifted covariance (`BaseXCov`, `BaseXLocal`): the Green
function `Ĝ_{k,x,s}`, the commutator term `K_x(φ₀)`, `N_{x,s}`, `M_{x,s}`, `M_{x,s}⁻¹` and
`Z_{x,s}`.  The reading set is that of `baseCovX_exact`: sets `Sr ⊆ Y` of sites such that every
active interaction cube lies inside `Sr` or is disjoint from `Y`, and the rows of the x-variant
operator from the sites of `Sr` stay in `Y`.  The parameters are compared on the cubes inside `Sr`,
the potentials on `Sr`, the fields on `Y`, and the sources on `Sr`; the outputs are compared on
`Y`.  The covers need no mass bound (`Dec2.XCover`).

* `dich_of_subDisj`: the dichotomy for `(Sr, Y)` gives that for `Sr` and the reading of the rows;
* `Gsx_lift_rows_Sr`, `commKx_rows_Sr`, `decN_rows_Sr`, `decM_rows_Sr`, `decM_apply_eq_zero_Sr`,
  `decM_inv_rows_Sr`, `decZ_rows_Sr`: the rows on `Sr` (resp. `Y`) correspond.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.LargeField.Base.XC

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background Matrix Balaban.Polymer.TwoTorusStep

section Dich

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}

/-- **The dichotomy for `(Sr, Y)` on the top level.**  If every active interaction cube lies inside
`Sr` or is disjoint from `Y ⊇ Sr`, then it lies inside `Sr` or is disjoint from `Sr`, and it meets
`Y` only inside `Sr`. -/
theorem dich_of_subDisj (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (hΩ : ∀ x, x ∈ G.Ω 1)
    {Sr Y : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} (hSY : Sr ⊆ Y)
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) Sr ∨ DisjI G (intBox q) Y) :
    (∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) Sr ∨ DisjI G (intBox q) Sr) ∧
      (∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ Sr) := by
  refine ⟨fun q hq hs => ?_, fun q hq hs x hxY hxq => ?_⟩
  · rcases hdich q hq hs with h | h
    · exact Or.inl h
    · exact Or.inr fun x hx hxS => h x hx (hSY hxS)
  · rcases hdich q hq hs with h | h
    · exact h ⟨x, hΩ x⟩ hxq
    · exact absurd hxY (h ⟨x, hΩ x⟩ hxq)

end Dich

section OneTorus

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {Cx : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x₀ ν : ℝ}

/-- **`M_{x,s}` does not couple `Sr` to its complement.**  If every active cube lies inside `Sr` or
is disjoint from `Y ⊇ Sr` and the rows of `H_{k,x}(A)` from `Sr` stay in `Y`, the entries of
`M_{x,s} = φ₀² - K_x(φ₀) Ĝ_{k,x,s} φ₀` from a row in `Sr` to a column outside `Sr` vanish. -/
theorem decM_apply_eq_zero_Sr (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hx₀ : 0 ≤ x₀)
    (hΩ : ∀ x, x ∈ G.Ω 1)
    {Sr Y : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} (hSY : Sr ⊆ Y)
    {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ} {α : G.Ω 1 → ℂ}
    (hα : AdmPot G α) (hU : IsUnit (1 - Kcalx G a aT x₀ ν α s))
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) Sr ∨ DisjI G (intBox q) Y)
    (hrow : ∀ z y : G.Ω 1, (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr →
      xDirichletOperator G a aT x₀ ν α z y ≠ 0 →
      (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Y)
    (φ : Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) {z w : G.Ω 1}
    (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr)
    (hw : (w : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∉ Sr) :
    decM G a aT x₀ ν α s φ z w = 0 := by
  obtain ⟨hdichT, hrowG⟩ := dich_of_subDisj G hΩ hSY hdich
  have e : decM G a aT x₀ ν α s φ z w =
      (decM G a aT x₀ ν α s φ *ᵥ Pi.single w 1) z := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hzw : z ≠ w := fun h => hw (by rw [← h]; exact hz)
  have hv : ∀ b : G.Ω 1, (b : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr →
      (Pi.single w 1 : G.Ω 1 → ℂ) b = 0 := fun b hb =>
    Pi.single_eq_of_ne (fun h : b = w => hw (by rw [← h]; exact hb)) _
  rw [e, decM_mulVec_eq, Pi.sub_apply, fieldMul_transpose_mulVec, commK_mulVec]
  have t1 : ∑ i, restrictField G φ z i *
      (fieldMul (restrictField G φ) *ᵥ (Pi.single w 1 : G.Ω 1 → ℂ)) (z, i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [fieldMul_mulVec, Pi.single_eq_of_ne hzw, mul_zero, mul_zero]
  have t2 : ∀ y : G.Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i,
      (liftOp N (Gsx G a aT x₀ ν α s) *ᵥ (fieldMul (restrictField G φ) *ᵥ
        (Pi.single w 1 : G.Ω 1 → ℂ))) (y, i) = 0 := by
    intro y hyY i
    rw [liftOp_mulVec]
    by_cases hyT : (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr
    · have key : ∀ f : G.Ω 1 → ℂ, (∀ b : G.Ω 1,
          (b : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr → f b = 0) →
          (Gsx G a aT x₀ ν α s *ᵥ f) y = 0 := by
        intro f hf
        simp only [Matrix.mulVec, dotProduct]
        refine Finset.sum_eq_zero fun b _ => ?_
        by_cases hb : (b : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr
        · rw [hf b hb, mul_zero]
        · rw [Gsx_apply_eq_zero_of_mem S hx₀ hα hU hdichT hyT hb, zero_mul]
      exact key _ fun b hb => by rw [fieldMul_mulVec, hv b hb, mul_zero]
    · exact Gsx_apply_eq_zero_of_not_mem S hx₀ hα hrowG _ hyY hyT
  have t3 : ∑ y, ∑ i, xDirichletOperator G a aT x₀ ν α z y *
      (restrictField G φ z i - restrictField G φ y i) *
      (liftOp N (Gsx G a aT x₀ ν α s) *ᵥ (fieldMul (restrictField G φ) *ᵥ
        (Pi.single w 1 : G.Ω 1 → ℂ))) (y, i) = 0 := by
    refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun i _ => ?_
    by_cases h0 : xDirichletOperator G a aT x₀ ν α z y = 0
    · rw [h0, zero_mul, zero_mul]
    · rw [t2 y (hrow z y hz h0) i, mul_zero]
  rw [t1, t3, sub_zero]

/-- `Z_{x,s} w = Ĝ w - Ĝ φ₀ M⁻¹ N w`. -/
theorem decZ_mulVec_eq (α : G.Ω 1 → ℂ) (s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ)
    (φ : Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (w : G.Ω 1 × Fin N → ℂ) :
    decZ G a aT x₀ ν α s φ *ᵥ w = liftOp N (Gsx G a aT x₀ ν α s) *ᵥ w -
      liftOp N (Gsx G a aT x₀ ν α s) *ᵥ (fieldMul (restrictField G φ) *ᵥ
        ((decM G a aT x₀ ν α s φ)⁻¹ *ᵥ (decN G a aT x₀ ν α s φ *ᵥ w))) := by
  unfold decZ decPi
  rw [Matrix.sub_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

end OneTorus

section TwoTori

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {Cx : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "ιb" x:max => Subtype.mk (bm (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) (ϱ := ϱ)
    (Nat.le_add_left 1 k) le_rfl _)

/-- `boxMap` is a bijection of a set `T` of sites of the box onto its image, as a map of the sites
`Ω₁` of the top levels. -/
theorem boxMap_bij_Sr {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {R : ℕ} (hT : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1)) :
    (∀ a b : (GA).Ω 1, (a : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T →
      (b : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T → (ιb a : (GB).Ω 1) = ιb b →
        a = b) ∧
    (∀ a : (GA).Ω 1, (a : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T →
      ((ιb a : (GB).Ω 1) : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈ T.image bm) ∧
    (∀ b : (GB).Ω 1, (b : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈ T.image bm →
      ∃ a : (GA).Ω 1, (a : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T ∧
        (ιb a : (GB).Ω 1) = b) :=
  boxMap_bij_top (ϱ := ϱ) rfl hT hm'

variable {a : ℕ → ℝ} {aT x₀ ν : ℝ}
  {Sr Y : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} {R : ℕ}
  {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
  {s' : ℕ × Balaban.Localization.CTorus d L N₁' m₁ (k + 1) → ℂ}
  {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
  {φ : Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
  {φ' : Balaban.Localization.CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}

variable (SA : Dec2.XCover (coverOf (GA)) (GA) a aT ν Cx) (SB : Dec2.XCover (coverOf (GB)) (GB) a aT ν Cx)
  (hx₀ : 0 ≤ x₀) (hSY : Sr ⊆ Y)
  (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
  (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
  (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
  (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
  (hα : ∀ x : (GA).Ω 1, (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr →
    α' (ιb x) = α x)
  (hU : IsUnit (1 - Kcalx (GA) a aT x₀ ν α s)) (hU' : IsUnit (1 - Kcalx (GB) a aT x₀ ν α' s'))
  (hdich : ∀ q ∈ cubeIdx (GA), sProd (GA) s q ≠ 0 → SubI (GA) (intBox q) Sr ∨
    DisjI (GA) (intBox q) Y)
  (hdich' : ∀ q ∈ cubeIdx (GB), sProd (GB) s' q ≠ 0 → SubI (GB) (intBox q) (Sr.image bm) ∨
    DisjI (GB) (intBox q) (Y.image bm))
  (hrow : ∀ z y : (GA).Ω 1, (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr →
    xDirichletOperator (GA) a aT x₀ ν α z y ≠ 0 →
    (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Y)
  (hrow' : ∀ z y : (GB).Ω 1, (z : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈ Sr.image bm →
    xDirichletOperator (GB) a aT x₀ ν α' z y ≠ 0 →
    (y : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈ Y.image bm)
  (hagree : ∀ q ∈ innerCentres (GA) Sr, sProd (GB) s' (Prod.map id bm q) = sProd (GA) s q)
include SA SB hx₀ hSY hYR hn hn' hαA hαB hα hU hU' hdich hdich' hrow hrow' hagree

omit hrow hrow' in
/-- **The rows of `Ĝ_{k,x,s} w` on `Y`, on two tori**: for `w` corresponding on `Sr`, the outputs
correspond at every site of `Y` (`xGreen_rows_transport` with `T = Sr`; the dichotomy and the rows
outside `Sr` from `dich_of_subDisj`). -/
theorem Gsx_lift_rows_Sr {w : (GA).Ω 1 × Fin N → ℂ} {w' : (GB).Ω 1 × Fin N → ℂ}
    (hw : ∀ y : (GA).Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr → ∀ i,
      w' (ιb y, i) = w (y, i))
    (y : (GA).Ω 1) (hy : (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Y) (i : Fin N) :
    (liftOp N (Gsx (GB) a aT x₀ ν α' s') *ᵥ w') (ιb y, i) =
      (liftOp N (Gsx (GA) a aT x₀ ν α s) *ᵥ w) (y, i) := by
  obtain ⟨h1, h2⟩ := dich_of_subDisj (GA) (fun x => levelGS_mem_Ω_one (Nat.le_add_left 1 k)
    le_rfl x) hSY hdich
  obtain ⟨h1', h2'⟩ := dich_of_subDisj (GB) (fun x => levelGS_mem_Ω_one (Nat.le_add_left 1 k)
    le_rfl x) (Finset.image_subset_image hSY) hdich'
  rw [liftOp_mulVec, liftOp_mulVec]
  exact xGreen_rows_transport SA SB hx₀ rfl rfl hSY hYR hn hn' hαA hαB hα hU hU' h1 h1' h2 h2'
    hagree (f := fun b => w (b, i)) (f' := fun b => w' (b, i)) (fun x hx => hw x hx i) y hy

omit SA SB hx₀ hαA hαB hU hU' hdich hdich' hagree in
/-- **The rows of `K_x(φ₀) u` at `Sr`, on two tori.**  The row of the commutator at a site of `Sr`
reads `u` and `φ₀` at the sites `y` with `H_{k,x}(A) z y ≠ 0`, which lie in `Y`. -/
theorem commKx_rows_Sr (hφ : ∀ u ∈ Y, φ' (bm u) = φ u)
    {u : (GA).Ω 1 × Fin N → ℂ} {u' : (GB).Ω 1 × Fin N → ℂ}
    (hu : ∀ y : (GA).Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i,
      u' (ιb y, i) = u (y, i))
    {z : (GA).Ω 1} (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr) :
    (commK (xDirichletOperator (GB) a aT x₀ ν α') (restrictField (GB) φ') *ᵥ u') (ιb z) =
      (commK (xDirichletOperator (GA) a aT x₀ ν α) (restrictField (GA) φ) *ᵥ u) z := by
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  obtain ⟨hinj, hmap, hsurj⟩ := boxMap_bij_Sr (ϱ := ϱ) (N₁' := N₁') hYR
    (by omega : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
  have hz' : ((ιb z : (GB).Ω 1) : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈
      Sr.image bm := Finset.mem_image_of_mem _ hz
  rw [commK_mulVec, commK_mulVec]
  refine sum_transport (fun y : (GA).Ω 1 =>
      (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Y)
    (fun y : (GB).Ω 1 => (y : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈ Y.image bm)
    (fun y => ιb y) hinj hmap hsurj _ _ (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_)
  · refine Finset.sum_eq_zero fun i _ => ?_
    have h0 : xDirichletOperator (GA) a aT x₀ ν α z y = 0 := by
      by_contra h0
      exact hy (hrow z y hz h0)
    rw [h0, zero_mul, zero_mul]
  · refine Finset.sum_eq_zero fun i _ => ?_
    have h0 : xDirichletOperator (GB) a aT x₀ ν α' (ιb z) y = 0 := by
      by_contra h0
      exact hy (hrow' _ y hz' h0)
    rw [h0, zero_mul, zero_mul]
  · have hzR := hYR _ (hSY hz)
    have hyR := hYR _ hy
    rw [xDirichletOperator_boxMap_row (ρ := R) a aT x₀ ν (by omega) (by omega) z y (hα z hz) hzR
      hyR]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h0 : xDirichletOperator (GA) a aT x₀ ν α z y = 0
    · rw [h0, zero_mul, zero_mul, zero_mul, zero_mul]
    · have e1 : φ' (bm (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1))) = φ z :=
        hφ _ (hSY hz)
      have e2 : φ' (bm (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1))) = φ y := hφ _ hy
      simp only [restrictField]
      rw [e1, e2, hu y hy i]

/-- **The rows of `N_{x,s} w` at `Sr`, on two tori**, for `w` corresponding on `Sr` and the field
corresponding on `Y`. -/
theorem decN_rows_Sr (hφ : ∀ u ∈ Y, φ' (bm u) = φ u)
    {w : (GA).Ω 1 × Fin N → ℂ} {w' : (GB).Ω 1 × Fin N → ℂ}
    (hw : ∀ y : (GA).Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr → ∀ i,
      w' (ιb y, i) = w (y, i))
    {z : (GA).Ω 1} (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr) :
    (decN (GB) a aT x₀ ν α' s' φ' *ᵥ w') (ιb z) = (decN (GA) a aT x₀ ν α s φ *ᵥ w) z := by
  rw [decN_mulVec_eq, decN_mulVec_eq, Pi.sub_apply, Pi.sub_apply, fieldMul_transpose_mulVec,
    fieldMul_transpose_mulVec]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : φ' (bm (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1))) = φ z :=
      hφ _ (hSY hz)
    simp only [restrictField]
    rw [e1, hw z hz i]
  · exact commKx_rows_Sr hSY hYR hn hn' hα hrow hrow' hφ
      (fun y hy i => Gsx_lift_rows_Sr SA SB hx₀ hSY hYR hn hn' hαA hαB hα hU hU' hdich hdich'
        hagree hw y hy i) hz

/-- **The rows of `M_{x,s} v` at `Sr`, on two tori**, for `v` corresponding on `Sr`:
`M_{x,s} v = N_{x,s} (φ₀ v)`. -/
theorem decM_rows_Sr (hφ : ∀ u ∈ Y, φ' (bm u) = φ u)
    {v : (GA).Ω 1 → ℂ} {v' : (GB).Ω 1 → ℂ}
    (hv : ∀ y : (GA).Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr →
      v' (ιb y) = v y)
    {z : (GA).Ω 1} (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr) :
    (decM (GB) a aT x₀ ν α' s' φ' *ᵥ v') (ιb z) = (decM (GA) a aT x₀ ν α s φ *ᵥ v) z := by
  have e : ∀ {N₁ : ℕ} [NeZero N₁] {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
      (β : G.Ω 1 → ℂ) (ψ : Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
      (σ : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ) (u : G.Ω 1 → ℂ),
      decM G a aT x₀ ν β σ ψ *ᵥ u =
        decN G a aT x₀ ν β σ ψ *ᵥ (fieldMul (restrictField G ψ) *ᵥ u) := by
    intro N₁ _ G β ψ σ u
    rw [decM_mulVec_eq, decN_mulVec_eq]
  rw [e, e]
  refine decN_rows_Sr SA SB hx₀ hSY hYR hn hn' hαA hαB hα hU hU' hdich hdich' hrow hrow' hagree
    hφ (fun y hy i => ?_) hz
  rw [fieldMul_mulVec, fieldMul_mulVec, hv y hy]
  have e1 : φ' (bm (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1))) = φ y := hφ _ (hSY hy)
  simp only [restrictField]
  rw [e1]

/-- **The rows of `M_{x,s}⁻¹ f` on `Sr`, on two tori.**  `M_{x,s}` does not couple `Sr` to its
complement (`decM_apply_eq_zero_Sr`), its entries on `Sr × Sr` correspond (`decM_rows_Sr`), so the
`Sr`-blocks of the inverses correspond (`inv_mulVec_transport_of_triangular`). -/
theorem decM_inv_rows_Sr (hφ : ∀ u ∈ Y, φ' (bm u) = φ u)
    (hM : IsUnit (decM (GA) a aT x₀ ν α s φ)) (hM' : IsUnit (decM (GB) a aT x₀ ν α' s' φ'))
    {f : (GA).Ω 1 → ℂ} {f' : (GB).Ω 1 → ℂ}
    (hf : ∀ y : (GA).Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr →
      f' (ιb y) = f y)
    {z : (GA).Ω 1} (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr) :
    ((decM (GB) a aT x₀ ν α' s' φ')⁻¹ *ᵥ f') (ιb z) =
      ((decM (GA) a aT x₀ ν α s φ)⁻¹ *ᵥ f) z := by
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hΩA : ∀ x, x ∈ (GA).Ω 1 := fun x => levelGS_mem_Ω_one (Nat.le_add_left 1 k) le_rfl x
  have hΩB : ∀ x, x ∈ (GB).Ω 1 := fun x => levelGS_mem_Ω_one (Nat.le_add_left 1 k) le_rfl x
  obtain ⟨hinj, hmap, hsurj⟩ := boxMap_bij_Sr (ϱ := ϱ) (N₁' := N₁') (T := Sr)
    (fun x hx => hYR x (hSY hx)) (by omega : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
  refine inv_mulVec_transport_of_triangular
    (fun y : (GA).Ω 1 => (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr)
    (fun y : (GB).Ω 1 => (y : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈ Sr.image bm)
    (fun y => ιb y) hinj hmap hsurj _ _
    (fun x z hx hz => decM_apply_eq_zero_Sr SA hx₀ hΩA hSY hαA hU hdich hrow φ hx hz)
    (fun x z hx hz => decM_apply_eq_zero_Sr SB hx₀ hΩB (Finset.image_subset_image hSY) hαB hU'
      hdich' hrow' φ' hx hz)
    (fun x w hx hw => ?_) hM hM' hf hz
  have h1 : decM (GB) a aT x₀ ν α' s' φ' (ιb x) (ιb w) =
      (decM (GB) a aT x₀ ν α' s' φ' *ᵥ Pi.single (ιb w) 1) (ιb x) := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have h2 : decM (GA) a aT x₀ ν α s φ x w = (decM (GA) a aT x₀ ν α s φ *ᵥ Pi.single w 1) x := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  refine h1.trans (Eq.trans ?_ h2.symm)
  refine decM_rows_Sr SA SB hx₀ hSY hYR hn hn' hαA hαB hα hU hU' hdich hdich' hrow hrow' hagree
    hφ (fun y hy => ?_) hx
  by_cases hyw : y = w
  · subst hyw; simp
  · rw [Pi.single_eq_of_ne hyw, Pi.single_eq_of_ne (fun h => hyw (hinj y w hy hw h))]

/-- **The rows of `Z_{x,s} w = Ĝ_{k,x,s} w - Π_{x,s} w` on `Y`, on two tori.**  For `w`
corresponding on `Sr`, the parameters on the cubes inside `Sr`, the potentials on `Sr` and the
fields on `Y`, the outputs correspond at every site of `Y`. -/
theorem decZ_rows_Sr (hφ : ∀ u ∈ Y, φ' (bm u) = φ u)
    (hM : IsUnit (decM (GA) a aT x₀ ν α s φ)) (hM' : IsUnit (decM (GB) a aT x₀ ν α' s' φ'))
    {w : (GA).Ω 1 × Fin N → ℂ} {w' : (GB).Ω 1 × Fin N → ℂ}
    (hw : ∀ y : (GA).Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr → ∀ i,
      w' (ιb y, i) = w (y, i))
    (y : (GA).Ω 1) (hy : (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Y) (i : Fin N) :
    (decZ (GB) a aT x₀ ν α' s' φ' *ᵥ w') (ιb y, i) = (decZ (GA) a aT x₀ ν α s φ *ᵥ w) (y, i) := by
  have hv : ∀ z : (GA).Ω 1, (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr →
      ((decM (GB) a aT x₀ ν α' s' φ')⁻¹ *ᵥ (decN (GB) a aT x₀ ν α' s' φ' *ᵥ w')) (ιb z) =
        ((decM (GA) a aT x₀ ν α s φ)⁻¹ *ᵥ (decN (GA) a aT x₀ ν α s φ *ᵥ w)) z :=
    fun z hz => decM_inv_rows_Sr SA SB hx₀ hSY hYR hn hn' hαA hαB hα hU hU' hdich hdich' hrow
      hrow' hagree hφ hM hM' (fun x hx => decN_rows_Sr SA SB hx₀ hSY hYR hn hn' hαA hαB hα hU hU'
        hdich hdich' hrow hrow' hagree hφ hw hx) hz
  rw [decZ_mulVec_eq, decZ_mulVec_eq, Pi.sub_apply, Pi.sub_apply,
    Gsx_lift_rows_Sr SA SB hx₀ hSY hYR hn hn' hαA hαB hα hU hU' hdich hdich' hagree hw
      y hy i,
    Gsx_lift_rows_Sr SA SB hx₀ hSY hYR hn hn' hαA hαB hα hU hU' hdich hdich' hagree
      (fun z hz j => ?_) y hy i]
  rw [fieldMul_mulVec, fieldMul_mulVec, hv z hz]
  have e1 : φ' (bm (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1))) = φ z := hφ _ (hSY hz)
  simp only [restrictField]
  rw [e1]

end TwoTori

end Balaban.LargeField.Base.XC
