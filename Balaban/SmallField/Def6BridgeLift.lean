/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6BridgeDomain
public import Balaban.SmallField.RenormTermwiseDefs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The bridge Def-6 to I-6: the lifted term family and the analytic premises

For a member of the small-field class on a torus (`IsSF`) at the scale `j`, the centred `ℤ^d` term
family `liftTF` of the termwise I-6 (`TermFamily`):

* sites of `ℤ^d` are the `j`-blocks, `unlift` the centred integer position of the block of a fine
  site (representative of minimal absolute value), `Ypoly j X'` the torus polymer of the shape
  `X'`, `fieldOf`/`hOf` the torus fields of a configuration (`c` on the blocks of `X'`, the
  constant `e_{i₀}` elsewhere; `h = b / ν_j`);
* `liftPolys`: the shapes `X' ∋ 0` that do not wind around the torus and whose torus polymer is in
  `𝒟_j` (polymers aligned at the origin, the polymers of `Eloc m₀ Tm j 0`);
* `termL`: on the tube the class term at a complex orthogonal `R` of bounded entries that carries the
  configuration into the ball (well defined, `LiftCtx.termL_eq`, from the class rotation invariance
  (H.3) `rotE`), elsewhere the class term; `Represents` says that a family is `liftTF`.

Results: `LiftCtx.analytic`, `bdd_tube`, `bdd_dom`, `rot_inv` (premises (H.2)-(H.4) on the tube and
the data domain `liftDom`), assembled in `LiftCtx.premisesTerm` and `IsSFFamily.premisesTerm`.
The radius of the tube is `ρ ≍ ε_j²` (`Def6BridgeDomain`).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.SmallField Balaban.Multiscale Balaban.Background Balaban.Localization Metric Set

variable {d L N₁ m₁ k N : ℕ} {ϱ : ℝ}

/-! ### The dictionary: the torus `j`-blocks and the lattice `ℤ^d` -/

/-- The torus field of a configuration `c` of the polymer `X'`: `c` on the blocks of `X'`, the
constant `e_{i₀}` elsewhere. -/
def fieldOf (j : ℕ) (i₀ : Fin N) (X' : Finset (Site d)) (c : Cfg d N X') :
    Fld d L N₁ m₁ k N :=
  fun x i => if h : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x ∈ X' then
    c (Sum.inl (⟨_, h⟩, i)) else (Pi.single i₀ 1 : Fin N → ℂ) i

/-- The field `h = b / ν_j` of a configuration (a constant). -/
noncomputable def hOf (νj : ℝ) (X' : Finset (Site d)) (c : Cfg d N X') : Fld d L N₁ m₁ k N :=
  fun _ i => c (Sum.inr i) / (νj : ℂ)

theorem fieldOf_block {j : ℕ} {i₀ : Fin N} {X' : Finset (Site d)} (c : Cfg d N X')
    {x x' : CTorus d L N₁ m₁ k}
    (h : jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x') :
    fieldOf j i₀ X' c x = fieldOf j i₀ X' c x' := by
  have : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x = unlift j x' := by
    unfold unlift; rw [h]
  funext i
  simp only [fieldOf, this]

theorem refPt_inl (i₀ : Fin N) (ν : ℝ) (X : Finset (Site d)) (p : ↥X × Fin N) :
    refPt i₀ ν X (Sum.inl p) = (Pi.single i₀ 1 : Fin N → ℂ) p.2 := rfl

theorem refPt_inr (i₀ : Fin N) (ν : ℝ) (X : Finset (Site d)) (i : Fin N) :
    refPt i₀ ν X (Sum.inr i) = (ν : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i := by
  simp [refPt, pack]

theorem fieldOf_sub_le {j : ℕ} {i₀ : Fin N} {X' : Finset (Site d)} {νj ρ : ℝ} {c : Cfg d N X'}
    (hc : c ∈ ball (refPt i₀ νj X') ρ) (hρ : 0 ≤ ρ) (x : CTorus d L N₁ m₁ k) (i : Fin N) :
    ‖fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' c x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ := by
  unfold fieldOf
  split_ifs with h
  · have := (dist_le_pi_dist c (refPt i₀ νj X') (Sum.inl (⟨_, h⟩, i))).trans (mem_ball.1 hc).le
    rwa [dist_eq_norm, refPt_inl] at this
  · simpa using hρ


theorem unlift_zero (j : ℕ) :
    unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (0 : CTorus d L N₁ m₁ k) = 0 := by
  funext μ
  simp [unlift, jBlock, blockMap, blockCoord]

theorem zero_mem_Ypoly {j : ℕ} {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X') :
    (0 : CTorus d L N₁ m₁ k) ∈ Ypoly j X' := by
  show unlift j (0 : CTorus d L N₁ m₁ k) ∈ X'
  rw [unlift_zero]; exact h0

theorem fieldOf_rot {j : ℕ} {i₀ : Fin N} {X' : Finset (Site d)} (M : Matrix (Fin N) (Fin N) ℂ)
    (c : Cfg d N X') {x : CTorus d L N₁ m₁ k}
    (hx : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x ∈ X') :
    fieldOf j i₀ X' (rotCfgL M X' c) x = rotField M (fieldOf j i₀ X' c) x := by
  funext i
  simp [fieldOf, hx, rotField, rotCfgL_apply_inl, Matrix.mulVec, dotProduct]

theorem hOf_rot {X' : Finset (Site d)} (νj : ℝ) (M : Matrix (Fin N) (Fin N) ℂ) (c : Cfg d N X') :
    hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) νj X' (rotCfgL M X' c) =
      rotField M (hOf νj X' c) := by
  funext x i
  simp [hOf, rotField, rotCfgL_apply_inr, Matrix.mulVec, dotProduct, Finset.sum_div, mul_div_assoc]

section Core

variable [NeZero L] [NeZero N₁]

theorem bgMass_mul_le_nuIdeal {βk νk : ℝ} (hν : 0 ≤ νk) {j : ℕ} (hjk : j ≤ k) :
    bgMass L k βk νk * ((L : ℝ) ^ j) ^ 2 ≤ nuIdeal L k νk j := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold bgMass nuIdeal
  split_ifs
  · simp only [zero_mul]; positivity
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hjk
    rw [Nat.add_sub_cancel_left]
    have e : νk * ((L : ℝ) ^ (j + t))⁻¹ ^ 2 * ((L : ℝ) ^ j) ^ 2 = νk * ((L : ℝ) ^ t)⁻¹ ^ 2 := by
      rw [pow_add]; field_simp
    rw [e]

/-- The class term in the centred form for the representative at the origin. -/
noncomputable def Eaux (Tm : Terms d L N₁ m₁ k N ϱ) (j : ℕ) (i₀ : Fin N) (νj : ℝ)
    (X' : Finset (Site d)) (c : Cfg d N X') : ℂ :=
  Tm.E j 0 (Ypoly j X') (fieldOf j i₀ X' c) (hOf νj X' c)

variable {P : Consts} {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ}

/-- **The domain inclusion** (field form): a torus field `Ψ`, constant on the `j`-blocks, within
`ρ₂` of the constant `e_{i₀}`, and a field `h = b / ν_j` with `|b - ν_j e_{i₀}| < ρ₂` lie in
`Ξ^c_j(𝔹_j(Z); 1, ε_j)` for a polymer `Z`; here `N ρ₂ < δ²`, `0 < δ ≤ min (c₀, c₁)`,
`(2 K₁ + 2) δ ≤ ε_j`. -/
theorem xiDom_of_field (hsf : IsSF P β ν a Tm ρd Ek)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {Z : Set (CTorus d L N₁ m₁ k)}
    (hZ : IsPolyDom P.m₀ j Z) (i₀ : Fin N)
    {δ ρ₂ : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N) (hρ0 : 0 < ρ₂)
    (hρ : (N : ℝ) * ρ₂ < δ ^ 2) (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ)
    (hΨ : ∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ₂)
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    (hb : ∀ i, ‖b i - (nuIdeal L k (ν k) j : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i‖ < ρ₂) :
    XiDom (Tm.gs j Z) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ
      (fun _ i => b i / (nuIdeal L k (ν k) j : ℂ)) := by
  have hspec := (hsf.gs_spec j hj1 hjk _ hZ).2
  refine xiDom_of_close hBg hspec hjk i₀ hδ0 hδc0 hδc1 hρ0 hρ hε Ψ
    (fun i => b i / (nuIdeal L k (ν k) j : ℂ)) hΨ hΨb (fun i => ?_)
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hνj : 0 < nuIdeal L k (ν k) j := by unfold nuIdeal; positivity
  have hm := bgMass_mul_le_nuIdeal (L := L) (k := k) (βk := β k) hν.le hjk
  have e : b i / (nuIdeal L k (ν k) j : ℂ) - (Pi.single i₀ 1 : Fin N → ℂ) i =
      (b i - (nuIdeal L k (ν k) j : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i) /
        (nuIdeal L k (ν k) j : ℂ) := by
    have hνc : (nuIdeal L k (ν k) j : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
    field_simp
  rw [e, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hνj]
  calc _ = (bgMass L k (β k) (ν k) * ((L : ℝ) ^ j) ^ 2 / nuIdeal L k (ν k) j) *
        ‖b i - (nuIdeal L k (ν k) j : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i‖ := by
        field_simp
    _ ≤ 1 * ‖b i - (nuIdeal L k (ν k) j : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i‖ := by
        gcongr
        rw [div_le_one hνj]; exact hm
    _ ≤ ρ₂ := by linarith [hb i]

/-- **The domain inclusion in the centred coordinates**: a configuration of the polymer `X'` in
the ball of radius `ρ₂` around the reference point gives torus fields in `Ξ^c_j(𝔹_j(Y); 1, ε_j)`. -/
theorem fp_mem_xiDom (hsf : IsSF P β ν a Tm ρd Ek)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) (i₀ : Fin N)
    {δ ρ₂ : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N) (hρ0 : 0 < ρ₂)
    (hρ : (N : ℝ) * ρ₂ < δ ^ 2) (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    {c : Cfg d N X'} (hc : c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ₂) :
    XiDom (Tm.gs j (Ypoly j X')) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
      (fieldOf j i₀ X' c) (hOf (nuIdeal L k (ν k) j) X' c) :=
  xiDom_of_field hsf hBg hν hj1 hjk hX i₀ hδ0 hδc0 hδc1 hρ0 hρ hε (fieldOf j i₀ X' c)
    (fun i => c (Sum.inr i)) (fun x i => fieldOf_sub_le hc hρ0.le x i)
    (fun x x' h => fieldOf_block c h) (fun i => by
      have := (dist_le_pi_dist c (refPt i₀ (nuIdeal L k (ν k) j) X') (Sum.inr i)).trans_lt
        (mem_ball.1 hc)
      rwa [dist_eq_norm, refPt_inr] at this)


/-- **Rotation invariance of the centred term** (from (H.3) `rotE`): two configurations in the
ball of radius `ρ` around the reference point, related by a matrix `M` of `IsRot` type with entries
bounded by `B`, have the same term.  The domain lemma is used at the radius `ρ₂ ≥ ρ (1 + N B)`. -/
theorem Eaux_rot (hsf : IsSF P β ν a Tm ρd Ek)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') (i₀ : Fin N)
    {δ ρ ρ₂ B : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N)
    (hρ0 : 0 < ρ) (hB : 0 ≤ B) (hρ₂ : ρ * (1 + N * B) ≤ ρ₂) (hρ : (N : ℝ) * ρ₂ < δ ^ 2)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsRot M) (hMb : ∀ i k, ‖M i k‖ ≤ B)
    {u u' : Cfg d N X'} (hu : u ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ)
    (hu' : u' ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ) (hrot : rotCfgL M X' u = u') :
    Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' u' = Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' u := by
  have hNB : 0 ≤ (N : ℝ) * B := by positivity
  have hρρ₂ : ρ ≤ ρ₂ := by nlinarith
  have hρ₂0 : 0 < ρ₂ := lt_of_lt_of_le hρ0 hρρ₂
  have ball_mono : ∀ {c : Cfg d N X'}, c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ →
      c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ₂ := fun hc => ball_subset_ball hρρ₂ hc
  have hXi := fp_mem_xiDom hsf hBg hν hj1 hjk hX i₀ hδ0 hδc0 hδc1 hρ₂0 hρ hε (ball_mono hu)
  have h0u : fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u' 0 = M.mulVec (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u 0) := by
    have := fieldOf_rot (j := j) (i₀ := i₀) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) M u
      (x := 0) (by rw [unlift_zero]; exact h0)
    rw [← hrot, this]; rfl
  have hMe : ∀ i, ‖(M.mulVec (Pi.single i₀ 1 : Fin N → ℂ)) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤
      ρ * (1 + N * B) := by
    intro i
    have h1 := fieldOf_sub_le (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (j := j) hu' hρ0.le 0 i
    have h2 := fun k' => fieldOf_sub_le (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (j := j) hu hρ0.le 0 k'
    have e1 : (M.mulVec (Pi.single i₀ 1 : Fin N → ℂ)) i - (Pi.single i₀ 1 : Fin N → ℂ) i =
        (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u' 0 i - (Pi.single i₀ 1 : Fin N → ℂ) i) -
          ∑ k', M i k' * (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u (0 : CTorus d L N₁ m₁ k) k' - (Pi.single i₀ 1 : Fin N → ℂ) k') := by
      rw [h0u]
      simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [e1]
    calc _ ≤ ‖fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u' 0 i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ +
          ‖∑ k', M i k' * (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u (0 : CTorus d L N₁ m₁ k) k' - (Pi.single i₀ 1 : Fin N → ℂ) k')‖ :=
          norm_sub_le _ _
      _ ≤ ρ + ∑ _k' : Fin N, B * ρ := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k' _ => ?_)
          rw [norm_mul]
          exact mul_le_mul (hMb i k') (h2 k') (norm_nonneg _) hB
      _ = ρ * (1 + N * B) := by simp; ring
  have hXirot : XiDom (Tm.gs j (Ypoly j X')) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j
      (P.eps d L j) (rotField M (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u)) (rotField M (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k (ν k) j) X' u)) := by
    rw [← hOf_rot, hrot]
    refine xiDom_of_field hsf hBg hν hj1 hjk hX i₀ hδ0 hδc0 hδc1 hρ₂0 hρ hε _ (fun i => u' (Sum.inr i))
      (fun x i => ?_) (fun x x' h => ?_) (fun i => ?_)
    · by_cases hx : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x ∈ X'
      · rw [← fieldOf_rot M u hx, hrot]
        exact (fieldOf_sub_le hu' hρ0.le x i).trans hρρ₂
      · have : fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u x = (Pi.single i₀ 1 : Fin N → ℂ) := by
          funext i; simp [fieldOf, hx]
        have e : rotField M (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u) x = M.mulVec (Pi.single i₀ 1 : Fin N → ℂ) := by
          simp [rotField, this]
        rw [e]; exact (hMe i).trans hρ₂
    · simp only [rotField]
      rw [fieldOf_block u h]
    · have := (dist_le_pi_dist u' (refPt i₀ (nuIdeal L k (ν k) j) X') (Sum.inr i)).trans_lt
        (mem_ball.1 hu')
      rw [dist_eq_norm, refPt_inr] at this
      exact this.trans_le hρρ₂
  have hr := hsf.rotE j hj1 hjk 0 (Ypoly j X') hX (zero_mem_Ypoly h0) M hM _ _ hXi hXirot
  unfold Eaux
  rw [← hr]
  refine hsf.localE j 0 (Ypoly j X') _ _ _ _ (fun x hx => ⟨?_, ?_⟩)
  · rw [← hrot, fieldOf_rot M u hx]
  · rw [← hrot, hOf_rot]


/-- The reflection of the coordinate `p`. -/
noncomputable def reflP (N : ℕ) (p : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => if i = p then (-1 : ℂ) else 1

omit [NeZero L] [NeZero N₁] in
theorem reflP_mul_self (p : Fin N) : reflP N p * reflP N p = 1 := by
  unfold reflP
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; by_cases h : i = p <;> simp [h]

omit [NeZero L] [NeZero N₁] in
theorem reflP_transpose (p : Fin N) : (reflP N p).transpose = reflP N p := by
  unfold reflP; exact Matrix.diagonal_transpose _

omit [NeZero L] [NeZero N₁] in
theorem reflP_det (p : Fin N) : (reflP N p).det = -1 := by
  unfold reflP
  rw [Matrix.det_diagonal]
  simp [Finset.prod_ite_eq']

omit [NeZero L] [NeZero N₁] in
theorem isRot_reflP (p : Fin N) : IsRot (reflP N p) := by
  refine ⟨by rw [reflP_transpose, reflP_mul_self], Or.inl fun i j => ?_⟩
  unfold reflP
  simp only [Matrix.diagonal_apply]
  split_ifs <;> simp

omit [NeZero L] [NeZero N₁] in
theorem reflP_norm_le (p : Fin N) (i k : Fin N) : ‖reflP N p i k‖ ≤ 1 := by
  unfold reflP
  simp only [Matrix.diagonal_apply]
  split_ifs <;> simp

omit [NeZero L] [NeZero N₁] in
theorem rotCfgL_reflP_norm_le (p : Fin N) (X' : Finset (Site d)) (v : Cfg d N X') :
    ‖rotCfgL (reflP N p) X' v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun x => ?_
  rcases x with ⟨z, i⟩ | i
  · rw [rotCfgL_apply_inl]
    simp only [reflP, Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte]
    split_ifs <;> simp <;> exact norm_le_pi_norm v _
  · rw [rotCfgL_apply_inr]
    simp only [reflP, Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte]
    split_ifs <;> simp <;> exact norm_le_pi_norm v _


omit [NeZero L] [NeZero N₁] in
theorem reflP_refPt {p i₀ : Fin N} (hp : p ≠ i₀) (ν : ℝ) (X' : Finset (Site d)) :
    rotCfgL (reflP N p) X' (refPt i₀ ν X') = refPt i₀ ν X' := by
  have h1 : (reflP N p).mulVec (Pi.single i₀ 1 : Fin N → ℂ) = Pi.single i₀ 1 := by
    unfold reflP
    funext i
    rw [Matrix.mulVec_diagonal]
    by_cases h : i = i₀
    · subst h; simp [hp.symm]
    · simp [h]
  unfold refPt
  rw [rotCfgL_pack, h1, Matrix.mulVec_smul, h1]

omit [NeZero L] [NeZero N₁] in
theorem det_isOrth {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsOrth M) : M.det = 1 ∨ M.det = -1 := by
  have h := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  exact mul_self_eq_one_iff.1 h

/-- **Rotation invariance for `O(N, ℂ)`**: as `Eaux_rot`, for any complex orthogonal `M`
(determinant `±1`), using one real reflection `P` of a coordinate `p ≠ i₀`. -/
theorem Eaux_orth (hsf : IsSF P β ν a Tm ρd Ek)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') {i₀ p : Fin N} (hp : p ≠ i₀)
    {δ ρ ρ₂ B : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N)
    (hρ0 : 0 < ρ) (hB : 1 ≤ B) (hρ₂ : ρ * (1 + N * B) ≤ ρ₂) (hρ : (N : ℝ) * ρ₂ < δ ^ 2)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsOrth M) (hMb : ∀ i k, ‖M i k‖ ≤ B)
    {u u' : Cfg d N X'} (hu : u ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ)
    (hu' : u' ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ) (hrot : rotCfgL M X' u = u') :
    Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' u' = Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' u := by
  have hB0 : 0 ≤ B := by linarith
  rcases det_isOrth hM with hd | hd
  · exact Eaux_rot hsf hBg hν hj1 hjk hX h0 i₀ hδ0 hδc0 hδc1 hρ0 hB0 hρ₂ hρ hε ⟨hM, Or.inr hd⟩
      hMb hu hu' hrot
  · -- reflect first
    set Pm := reflP N p with hPm
    have hPball : rotCfgL Pm X' u ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ := by
      rw [mem_ball, dist_eq_norm] at hu ⊢
      have e : rotCfgL Pm X' u - refPt i₀ (nuIdeal L k (ν k) j) X' =
          rotCfgL Pm X' (u - refPt i₀ (nuIdeal L k (ν k) j) X') := by
        rw [map_sub, hPm, reflP_refPt hp]
      rw [e]
      exact (rotCfgL_reflP_norm_le p X' _).trans_lt hu
    have h1 := Eaux_rot hsf hBg hν hj1 hjk hX h0 i₀ hδ0 hδc0 hδc1 hρ0 hB0 hρ₂ hρ hε
      (isRot_reflP p) (fun i k => (reflP_norm_le p i k).trans hB) hu hPball rfl
    have hMP : IsRot (M * Pm) := by
      refine ⟨?_, Or.inr ?_⟩
      · rw [Matrix.transpose_mul, hPm, reflP_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc M.transpose,
          hM, Matrix.one_mul, reflP_mul_self]
      · rw [Matrix.det_mul, hd, hPm, reflP_det]; norm_num
    have hMPb : ∀ i k, ‖(M * Pm) i k‖ ≤ B := by
      intro i k
      rw [hPm]
      unfold reflP
      rw [Matrix.mul_diagonal]
      by_cases h : k = p
      · simp [h]; exact hMb i p
      · simp [h]; exact hMb i k
    have h2 := Eaux_rot hsf hBg hν hj1 hjk hX h0 i₀ hδ0 hδc0 hδc1 hρ0 hB0 hρ₂ hρ hε hMP hMPb hPball
      hu' (by
        have hPP : Pm * Pm = 1 := by rw [hPm]; exact reflP_mul_self p
        rw [← rotCfgL_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]; exact hrot)
    rw [h2, h1]


theorem analyticAt_proj {X' : Finset (Site d)} (idx : Idx d N X') (c₀ : Cfg d N X') :
    AnalyticAt ℂ (fun c : Cfg d N X' => c idx) c₀ :=
  (analyticAt_pi_iff.1 analyticAt_id) idx

theorem analyticAt_fp (j : ℕ) (i₀ : Fin N) (νj : ℝ) (X' : Finset (Site d)) (c₀ : Cfg d N X') :
    AnalyticAt ℂ (fun c : Cfg d N X' =>
      ((fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' c,
        hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) νj X' c) : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N))
      c₀ := by
  refine AnalyticAt.prod ?_ ?_
  · refine analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_
    by_cases h : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x ∈ X'
    · simp only [fieldOf, h, dite_true]
      exact analyticAt_proj _ c₀
    · simp only [fieldOf, h, dite_false]
      exact analyticAt_const
  · refine analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_
    simp only [hOf]
    exact (analyticAt_proj _ c₀).div_const


/-- The entry bound used for the composite rotations: `64000 N²`. -/
def rotB (N : ℕ) : ℝ := 64000 * (N : ℝ) ^ 2

omit [NeZero L] [NeZero N₁] in
theorem one_le_rotB (i₀ : Fin N) : 1 ≤ rotB N := by
  have : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  unfold rotB; nlinarith

omit [NeZero L] [NeZero N₁] in
theorem mul_entry_le {A B : Matrix (Fin N) (Fin N) ℂ} {a b : ℝ} (hA : ∀ i k, ‖A i k‖ ≤ a)
    (hB : ∀ i k, ‖B i k‖ ≤ b) (ha : 0 ≤ a) (i k : Fin N) : ‖(A * B) i k‖ ≤ N * (a * b) := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ l, ‖A i l * B l k‖ ≤ ∑ _l : Fin N, a * b :=
        Finset.sum_le_sum fun l _ => by
          rw [norm_mul]; exact mul_le_mul (hA i l) (hB l k) (norm_nonneg _) ha
    _ = N * (a * b) := by simp

omit [NeZero L] [NeZero N₁] in
theorem transpose_entry_le {A : Matrix (Fin N) (Fin N) ℂ} {a : ℝ} (hA : ∀ i k, ‖A i k‖ ≤ a)
    (i k : Fin N) : ‖A.transpose i k‖ ≤ a := hA k i

omit [NeZero L] [NeZero N₁] in
theorem isOrth_mul_transpose {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsOrth R) :
    R * R.transpose = 1 := mul_eq_one_comm.1 hR

omit [NeZero N₁] in
theorem eps_pos {P : Consts} (hα : 0 < P.α₀) (j : ℕ) : 0 < P.eps d L j := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold Consts.eps epsSeq
  have := epsTail_pos j
  have h2 : 0 < ((L : ℝ) ^ (-(P.alpha d))) := Real.rpow_pos_of_pos hL _
  positivity

/-- **The radius of the tube**: `ρ_j = (ε_j / (2 K₁ + 2))² / (2 N (1 + N · rotB N))`, of order
`ε_j²`; it satisfies the radius relation of `LiftCtx` (`liftRadius_spec`). -/
noncomputable def liftRadius (d L N : ℕ) [NeZero L] (P : Consts) (j : ℕ) : ℝ :=
  (P.eps d L j / (2 * bgK1 d L N + 2)) ^ 2 / (2 * N * (1 + N * rotB N))

omit [NeZero N₁] in
theorem liftRadius_pos {P : Consts} {j : ℕ} (hε : 0 < P.eps d L j) (i₀ : Fin N) :
    0 < liftRadius d L N P j := by
  have hK := bgK1_pos d L N
  have hN : 0 < N := Fin.pos i₀
  unfold liftRadius rotB
  positivity

omit [NeZero N₁] in
/-- The radius relation holds for `liftRadius` as soon as `ε_j ≤ (2 K₁ + 2) min (c₀, c₁)`. -/
theorem liftRadius_spec {P : Consts} {j : ℕ} (hε : 0 < P.eps d L j) (i₀ : Fin N)
    (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ bgC0 d L N ∧ δ ≤ bgC1 d L N ∧
      (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j ∧
      (N : ℝ) * (liftRadius d L N P j * (1 + N * rotB N)) < δ ^ 2 := by
  have hK := bgK1_pos d L N
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hK2 : 0 < 2 * bgK1 d L N + 2 := by positivity
  refine ⟨P.eps d L j / (2 * bgK1 d L N + 2), by positivity, ?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hK2]; exact hsmall.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hK2.le)
      |>.trans_eq (by ring)
  · rw [div_le_iff₀ hK2]; exact hsmall.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hK2.le)
      |>.trans_eq (by ring)
  · rw [mul_div_cancel₀ _ hK2.ne']
  · unfold liftRadius
    have hpos : 0 < (1 + N * rotB N) := by unfold rotB; positivity
    have hδ : 0 < (P.eps d L j / (2 * bgK1 d L N + 2)) ^ 2 := by positivity
    have : (N : ℝ) * ((P.eps d L j / (2 * bgK1 d L N + 2)) ^ 2 / (2 * N * (1 + N * rotB N)) *
        (1 + N * rotB N)) = (P.eps d L j / (2 * bgK1 d L N + 2)) ^ 2 / 2 := by
      field_simp
    rw [this]; linarith

/-- The class context: the class (per-torus form), the background hypotheses, the scale, and the
radius relation `N ρ (1 + N · rotB N) < δ²`, `0 < δ ≤ min (c₀, c₁)`, `(2 K₁ + 2) δ ≤ ε_j`. -/
structure LiftCtx (P : Consts) (β ν a : ℕ → ℝ) (Tm : Terms d L N₁ m₁ k N ϱ)
    (ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ)
    (Ek : ℝ) (j : ℕ) (ρ : ℝ) : Prop where
  sf : IsSF P β ν a Tm ρd Ek
  bg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k))
  nu_pos : 0 < ν k
  j1 : 1 ≤ j
  jk : j ≤ k
  rho_pos : 0 < ρ
  radius : ∃ δ : ℝ, 0 < δ ∧ δ ≤ bgC0 d L N ∧ δ ≤ bgC1 d L N ∧
    (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j ∧
    (N : ℝ) * (ρ * (1 + N * rotB N)) < δ ^ 2

variable {j : ℕ} {ρ : ℝ}

theorem LiftCtx.mem_xiDom (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ : Fin N) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    {c : Cfg d N X'} (hc : c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ) :
    XiDom (Tm.gs j (Ypoly j X')) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
      (fieldOf j i₀ X' c) (hOf (nuIdeal L k (ν k) j) X' c) := by
  obtain ⟨δ, hδ0, hδ1, hδ2, hδ3, hδ4⟩ := ctx.radius
  have hN : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
  have hρρ₂ : ρ ≤ ρ * (1 + N * rotB N) := by nlinarith [ctx.rho_pos]
  exact fp_mem_xiDom ctx.sf ctx.bg ctx.nu_pos ctx.j1 ctx.jk hX i₀ hδ0 hδ1 hδ2
    (by nlinarith [ctx.rho_pos]) hδ4 hδ3 (ball_subset_ball hρρ₂ hc)

theorem LiftCtx.orth (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') {i₀ p : Fin N} (hp : p ≠ i₀) {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : IsOrth M) (hMb : ∀ i k, ‖M i k‖ ≤ rotB N)
    {u u' : Cfg d N X'} (hu : u ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ)
    (hu' : u' ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ) (hrot : rotCfgL M X' u = u') :
    Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' u' = Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' u := by
  obtain ⟨δ, hδ0, hδ1, hδ2, hδ3, hδ4⟩ := ctx.radius
  exact Eaux_orth ctx.sf ctx.bg ctx.nu_pos ctx.j1 ctx.jk hX h0 hp hδ0 hδ1 hδ2 ctx.rho_pos
    (one_le_rotB i₀) le_rfl hδ4 hδ3 hM hMb hu hu' hrot


theorem LiftCtx.witness (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') {i₀ p : Fin N} (hp : p ≠ i₀) {c : Cfg d N X'}
    {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsOrth A) (hB : IsOrth B) {ma mb : ℝ}
    (hAb : ∀ i k, ‖A i k‖ ≤ ma) (hBb : ∀ i k, ‖B i k‖ ≤ mb) (ha : 0 ≤ ma)
    (hab : (N : ℝ) * (ma * mb) ≤ rotB N)
    (hcA : rotCfgL A X' c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ)
    (hcB : rotCfgL B X' c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ) :
    Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' (rotCfgL A X' c) =
      Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' (rotCfgL B X' c) := by
  have hBBt : B * B.transpose = 1 := isOrth_mul_transpose hB
  have hM : IsOrth (A * B.transpose) := by
    unfold IsOrth
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc A.transpose, hA, Matrix.one_mul, hBBt]
  refine ctx.orth hX h0 hp hM (fun i k => (mul_entry_le hAb (transpose_entry_le hBb) ha i k).trans hab)
    hcB hcA ?_
  rw [← rotCfgL_mul, Matrix.mul_assoc, show B.transpose * B = 1 from hB,
    Matrix.mul_one]

open Classical in
/-- **The term of the lifted family**: on the tube, the term at a rotation carrying the
configuration into the ball (well defined by `Eaux_witness`); elsewhere the term itself. -/
noncomputable def termL (Tm : Terms d L N₁ m₁ k N ϱ) (j : ℕ) (i₀ : Fin N) (νj ρ : ℝ)
    (X' : Finset (Site d)) (c : Cfg d N X') : ℂ :=
  if h : ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
      rotCfgL R X' c ∈ ball (refPt i₀ νj X') ρ then
    Eaux Tm j i₀ νj X' (rotCfgL (Classical.choose h) X' c)
  else Eaux Tm j i₀ νj X' c

theorem entryBd_bound {A : Matrix (Fin N) (Fin N) ℂ} (h : EntryBd N A) :
    ∀ i k, ‖A i k‖ ≤ 40 := h

/-- On the tube the term is the term at any admissible witness rotation. -/
theorem LiftCtx.termL_eq (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') {i₀ p : Fin N} (hp : p ≠ i₀) {c : Cfg d N X'}
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsOrth R) (hRb : EntryBd N R)
    (hRc : rotCfgL R X' c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ) :
    termL Tm j i₀ (nuIdeal L k (ν k) j) ρ X' c =
      Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' (rotCfgL R X' c) := by
  have hex : ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
      rotCfgL R X' c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ := ⟨R, hR, hRb, hRc⟩
  unfold termL
  simp only [hex, dite_true]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec hex
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  refine ctx.witness hX h0 hp h1 hR (entryBd_bound h2) (entryBd_bound hRb) (by norm_num) ?_ h3 hRc
  unfold rotB; nlinarith


theorem LiftCtx.analyticAt_Eaux (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ : Fin N)
    {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') {u₀ : Cfg d N X'}
    (hu : u₀ ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ) :
    AnalyticAt ℂ (Eaux Tm j i₀ (nuIdeal L k (ν k) j) X') u₀ := by
  have hXi := ctx.mem_xiDom i₀ hX hu
  have hE := ctx.sf.analyticE j ctx.j1 ctx.jk 0 (Ypoly j X') hX (zero_mem_Ypoly h0)
    (fieldOf j i₀ X' u₀, hOf (nuIdeal L k (ν k) j) X' u₀) hXi
  exact AnalyticAt.comp (g := fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
    Tm.E j 0 (Ypoly j X') p.1 p.2)
    (f := fun c : Cfg d N X' => ((fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' c,
      hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k (ν k) j) X' c) :
        Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N)) (x := u₀) hE
    (analyticAt_fp j i₀ (nuIdeal L k (ν k) j) X' u₀)

/-- **Analyticity on the tube** (premise (H.2)/(H.4) of I-6). -/
theorem LiftCtx.analytic (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') :
    AnalyticOnNhd ℂ (termL Tm j i₀ (nuIdeal L k (ν k) j) ρ X')
      (Tube i₀ (nuIdeal L k (ν k) j) ρ X') := by
  intro c₀ hc₀
  obtain ⟨R₀, h1, h2, h3⟩ := hc₀
  have hcont : Continuous (rotCfgL R₀ X') := LinearMap.continuous_of_finiteDimensional _
  have hopen : IsOpen {c : Cfg d N X' | rotCfgL R₀ X' c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ} :=
    isOpen_ball.preimage hcont
  have hAn : AnalyticAt ℂ (fun c => Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' (rotCfgL R₀ X' c)) c₀ :=
    AnalyticAt.comp (g := Eaux Tm j i₀ (nuIdeal L k (ν k) j) X')
      (ctx.analyticAt_Eaux i₀ hX h0 h3)
      ((LinearMap.toContinuousLinearMap (rotCfgL R₀ X')).analyticAt c₀)
  refine hAn.congr ?_
  filter_upwards [hopen.mem_nhds h3] with c hc
  exact (ctx.termL_eq hX h0 hne h1 h2 hc).symm


theorem LiftCtx.norm_Eaux_le (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ : Fin N) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') {c : Cfg d N X'}
    (hXi : XiDom (Tm.gs j (Ypoly j X')) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j
      (P.eps d L j) (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' c)
      (hOf (nuIdeal L k (ν k) j) X' c)) :
    ‖Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' c‖ ≤
      P.E₀ * Real.exp (-P.κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X')) :=
  ctx.sf.boundE j ctx.j1 ctx.jk 0 (Ypoly j X') hX (zero_mem_Ypoly h0) _ _ hXi

/-- **The bound (H.4) on the tube.** -/
theorem LiftCtx.bdd_tube (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') {c : Cfg d N X'} (hc : c ∈ Tube i₀ (nuIdeal L k (ν k) j) ρ X') :
    ‖termL Tm j i₀ (nuIdeal L k (ν k) j) ρ X' c‖ ≤
      P.E₀ * Real.exp (-P.κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X')) := by
  obtain ⟨R, h1, h2, h3⟩ := hc
  rw [ctx.termL_eq hX h0 hne h1 h2 h3]
  exact ctx.norm_Eaux_le i₀ hX h0 (ctx.mem_xiDom i₀ hX h3)

/-- **Rotation invariance on the tube** (premise (H.3)). -/
theorem LiftCtx.rot_inv (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') {c : Cfg d N X'} (hc : c ∈ Tube i₀ (nuIdeal L k (ν k) j) ρ X')
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsOrth R) (hRb : EntryBd N R)
    (hRc : rotCfgL R X' c ∈ Tube i₀ (nuIdeal L k (ν k) j) ρ X') :
    termL Tm j i₀ (nuIdeal L k (ν k) j) ρ X' (rotCfgL R X' c) =
      termL Tm j i₀ (nuIdeal L k (ν k) j) ρ X' c := by
  obtain ⟨W, hW1, hW2, hW3⟩ := hc
  obtain ⟨W', hW1', hW2', hW3'⟩ := hRc
  rw [ctx.termL_eq hX h0 hne hW1' hW2' hW3', ctx.termL_eq hX h0 hne hW1 hW2 hW3]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hWR : IsOrth (W' * R) := by
    unfold IsOrth
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc W'.transpose, hW1', Matrix.one_mul,
      hR]
  have := ctx.witness hX h0 hne hWR hW1 (ma := (N : ℝ) * (40 * 40)) (mb := 40)
    (mul_entry_le (entryBd_bound hW2') (entryBd_bound hRb) (by norm_num))
    (entryBd_bound hW2) (by positivity) (by unfold rotB; nlinarith)
    (by rw [rotCfgL_mul]; exact hW3') hW3
  rw [rotCfgL_mul] at this
  exact this


/-- **The shapes of the lifted family** (offset `0`): the finite sets `X' ⊆ ℤ^d` of `j`-blocks
containing the origin, not winding around the torus, whose torus polymer `Ypoly j X'` is a
polymer of `𝒟_j`. -/
def liftPolys (P : Consts) (j : ℕ) : Set (Finset (Site d)) :=
  {X' | (0 : Site d) ∈ X' ∧ NonWind L N₁ m₁ k j X' ∧
    IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')}

/-- **The centred `ℤ^d` term family of the class at the scale `j`** (the lift of the torus terms
`ℰ^{(j)}(0, X; ·)`, polymers aligned at the origin): shapes `liftPolys`, size
`d_j = sizeJ` of the torus polymer, term `termL`. -/
noncomputable def liftTF (P : Consts) (j : ℕ) (i₀ : Fin N) (νj ρ : ℝ)
    (Tm : Terms d L N₁ m₁ k N ϱ) : TermFamily d N where
  polys := liftPolys (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j
  dist X' := sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X')
  term := termL Tm j i₀ νj ρ

/-- **`T` represents the class term at the scale `j`**: `T` is the lifted family. -/
def Represents (T : TermFamily d N) (P : Consts) (j : ℕ) (i₀ : Fin N) (νj ρ : ℝ)
    (Tm : Terms d L N₁ m₁ k N ϱ) : Prop :=
  T = liftTF P j i₀ νj ρ Tm

/-- The weight of a shape in the counting premise (with `κ = P.κ`). -/
noncomputable def liftWt (P : Consts) (j : ℕ)
    (X : ↥(liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j)) : ℝ :=
  wt P.κ X.1 (sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X.1))

/-- **The data domain of the lifted family**: the configurations `(ψ, b)` such that for every
shape, the restriction to the polymer extends to torus fields in `Ξ^c_j(𝔹_j(Y); 1, ε_j)`
(`ℰ` depends on the restriction to `Y` only, by locality). -/
def liftDom (P : Consts) (β ν a : ℕ → ℝ) (Tm : Terms d L N₁ m₁ k N ϱ) (j : ℕ) (i₀ : Fin N) :
    Set ((Site d → Spin N) × Spin N) :=
  {p | ∀ X' ∈ liftPolys (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j,
    ∃ (Ψ h : Fld d L N₁ m₁ k N),
      (∀ x ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X',
        Ψ x = fieldOf j i₀ X' (pack X' p.1 p.2) x ∧
          h x = hOf (nuIdeal L k (ν k) j) X' (pack X' p.1 p.2) x) ∧
      XiDom (Tm.gs j (Ypoly j X')) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        Ψ h}

/-- On the ball the term of the lifted family is the class term (the representative at the
origin). -/
theorem LiftCtx.termL_of_ball (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') {c : Cfg d N X'}
    (hc : c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ) :
    termL Tm j i₀ (nuIdeal L k (ν k) j) ρ X' c =
      Tm.E j 0 (Ypoly j X') (fieldOf j i₀ X' c) (hOf (nuIdeal L k (ν k) j) X' c) := by
  rw [ctx.termL_eq hX h0 hne isOrth_one entryBd_one (by rwa [rotCfgL_one])]
  rw [rotCfgL_one]; rfl

/-- **The bound (H.4) on the data domain.** -/
theorem LiftCtx.bdd_dom (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {X' : Finset (Site d)} (hX' : X' ∈ liftPolys (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j)
    {p : (Site d → Spin N) × Spin N} (hp : p ∈ liftDom P β ν a Tm j i₀) :
    ‖termL Tm j i₀ (nuIdeal L k (ν k) j) ρ X' (pack X' p.1 p.2)‖ ≤
      P.E₀ * Real.exp (-P.κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X')) := by
  obtain ⟨h0, hnw, hX⟩ := hX'
  by_cases hex : ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
      rotCfgL R X' (pack X' p.1 p.2) ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ
  · obtain ⟨R, h1, h2, h3⟩ := hex
    rw [ctx.termL_eq hX h0 hne h1 h2 h3]
    exact ctx.norm_Eaux_le i₀ hX h0 (ctx.mem_xiDom i₀ hX h3)
  · unfold termL
    simp only [hex, dite_false]
    obtain ⟨Ψ, h, hag, hXi⟩ := hp X' ⟨h0, hnw, hX⟩
    have hloc : Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' (pack X' p.1 p.2) =
        Tm.E j 0 (Ypoly j X') Ψ h := by
      unfold Eaux
      exact (ctx.sf.localE j 0 (Ypoly j X') _ _ _ _ (fun x hx => ⟨(hag x hx).1.symm, (hag x hx).2.symm⟩))
    rw [hloc]
    exact ctx.sf.boundE j ctx.j1 ctx.jk 0 (Ypoly j X') hX (zero_mem_Ypoly h0) Ψ h hXi


/-- **`PremisesTerm` without the point-group invariance**: the fields of `PremisesTerm` other than
`sym_mem`, `sym_inv`. -/
structure PremisesCore (T : TermFamily d N) (i₀ i₁ : Fin N) (ν ρ E₀ κ A K₀ : ℝ)
    (Dom : Set ((Site d → Spin N) × Spin N)) : Prop where
  ne : i₀ ≠ i₁
  zero_mem : ∀ X ∈ T.polys, (0 : Site d) ∈ X
  dist_nonneg : ∀ X ∈ T.polys, 0 ≤ T.dist X
  diam : ∀ X ∈ T.polys, ∀ x ∈ X, ((∑ μ, |x μ| : ℤ) : ℝ) ≤ A * (1 + T.dist X)
  count_summable : Summable fun X : T.polys => wt κ X.1 (T.dist X.1)
  count_le : ∑' X : T.polys, wt κ X.1 (T.dist X.1) ≤ K₀
  analytic : ∀ X ∈ T.polys, AnalyticOnNhd ℂ (T.term X) (Tube i₀ ν ρ X)
  bdd_tube : ∀ X ∈ T.polys, ∀ c ∈ Tube i₀ ν ρ X, ‖T.term X c‖ ≤ E₀ * Real.exp (-κ * T.dist X)
  bdd_dom : ∀ X ∈ T.polys, ∀ p ∈ Dom,
    ‖T.term X (pack X p.1 p.2)‖ ≤ E₀ * Real.exp (-κ * T.dist X)
  rot_inv : ∀ X ∈ T.polys, ∀ c ∈ Tube i₀ ν ρ X, ∀ R : Matrix (Fin N) (Fin N) ℂ,
    IsOrth R → EntryBd N R → rotCfgL R X c ∈ Tube i₀ ν ρ X → T.term X (rotCfgL R X c) = T.term X c

/-- The core fields together with the point-group invariance (H.3) are `PremisesTerm`. -/
theorem PremisesCore.toPremisesTerm {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)} (h : PremisesCore T i₀ i₁ ν ρ E₀ κ A K₀ Dom)
    (sym_mem : ∀ r : Site d → Site d, IsLatGen r → ∀ X ∈ T.polys, X.image r ∈ T.polys)
    (sym_inv : ∀ r : Site d → Site d, IsLatGen r → ∀ X ∈ T.polys, ∀ (ψ : Site d → Spin N)
      (b : Spin N), T.term (X.image r) (pack (X.image r) (fun x => ψ (r x)) b) =
        T.term X (pack X ψ b)) :
    PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom :=
  ⟨h.ne, h.zero_mem, h.dist_nonneg, h.diam, h.count_summable, h.count_le, h.analytic, h.bdd_tube,
    h.bdd_dom, h.rot_inv, sym_mem, sym_inv⟩

/-- **The core premises supplied by the class** for the lifted family: the geometry
(`zero_mem`, `dist_nonneg`; `diam`, `count_*` as hypotheses, discharged in `Def6BridgeGeom`) and
the analytic fields (`analytic`, `bdd_tube`, `bdd_dom`, `rot_inv`). -/
theorem LiftCtx.premisesCore (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {i₀ i₁ : Fin N}
    (hne : i₁ ≠ i₀) {A K₀ : ℝ}
    (geo_diam : ∀ X ∈ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j, ∀ x ∈ X,
      ((∑ μ, |x μ| : ℤ) : ℝ) ≤ A * (1 + sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X)))
    (geo_summable : Summable (liftWt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j))
    (geo_le : (∑' X, liftWt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j X) ≤ K₀) :
    PremisesCore (liftTF P j i₀ (nuIdeal L k (ν k) j) ρ Tm) i₀ i₁ (nuIdeal L k (ν k) j) ρ P.E₀
      P.κ A K₀ (liftDom P β ν a Tm j i₀) where
  ne := hne.symm
  zero_mem := fun _ hX => hX.1
  dist_nonneg := fun _ _ => treeLenCovOne_nonneg _ _ _
  diam := geo_diam
  count_summable := geo_summable
  count_le := geo_le
  analytic := fun _ hX => ctx.analytic hne hX.2.2 hX.1
  bdd_tube := fun _ hX _ hc => ctx.bdd_tube hne hX.2.2 hX.1 hc
  bdd_dom := fun _ hX _ hp => ctx.bdd_dom hne hX hp
  rot_inv := fun _ hX _ hc _ hR hRb hRc => ctx.rot_inv hne hX.2.2 hX.1 hc hR hRb hRc

/-- **The context from class membership.**  A member of the class on the torus `N₁` (the per-torus
form of `IsSFFamily`) gives the context at the scale `j` whenever the numerical conditions on the
parameters hold: `d ≥ 3`, `L ≥ 3`, `ϱ ≥ R₀(d, L)`, and the radius relation. -/
theorem IsSFFamily.liftCtx {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
    {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
    {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
      (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
    (hF : IsSFFamily P β ν a Tm ρd Ek) (N₁ : ℕ) [NeZero N₁] (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hϱ : bgR0 d L ≤ ϱ) (hj1 : 1 ≤ j) (hjk : j ≤ k) (hρ0 : 0 < ρ)
    (hrad : ∃ δ : ℝ, 0 < δ ∧ δ ≤ bgC0 d L N ∧ δ ≤ bgC1 d L N ∧
      (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j ∧ (N : ℝ) * (ρ * (1 + N * rotB N)) < δ ^ 2) :
    LiftCtx P β ν a (Tm N₁) (ρd N₁) (Ek N₁) j ρ :=
  ⟨hF.torus N₁, bgHyp_of_class hF.admissible hF.coeff hd hL hϱ, hF.coeff.nu_pos, hj1, hjk, hρ0,
    hrad⟩


end Core




end Balaban.SmallField.Def6
