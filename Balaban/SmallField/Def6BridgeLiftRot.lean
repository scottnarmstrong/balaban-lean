/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6BridgeLift
public import Balaban.SmallField.Def6AvgLiftC
public import Balaban.SmallField.Def6RotFrames
public import Balaban.Inhabited.XiCRawOpenWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The complex rotation invariance of the centred term, from the real clause and a polar path

The frame bridges of the renormalization step (`Def6BridgeLift`, `Def6AvgLiftC`) apply the
rotation invariance of the class term `ℰ` to a complex orthogonal `M` relating two points of the
ball of radius `ρ` around the reference point.  The landed versions (`Eaux_rot`, `EauxC_rot`) take it
from the clause `IsSF.rotE` for `IsCRot` matrices, which the real-rotation clause of the source
(`SFTermClauses.rotE`) does not give.  Here the same invariance is proved from the term clauses on
the landed domain (`LandedTermClauses`: the clauses of `Def6v2.SFTermClauses`, real `rotE` only) with
no hypothesis `CRotE` (`notes/phase1/CROTE.md` §4 item 1):

* `E_rot_at`: invariance at any centre `x₀` of the polymer, by `Def6v2.rotE_of_near_within` along the
  polar path of `M` (`Def6RotFrames`); the path stays in the polydisc of radius `rotRad N B ρ`,
  which lies in the domain `Ξ^c_j` by `dom_of_close` once `N · 2 rotRad N B ρ < δ²`;
* `Eaux_rot_of_clauses`, `EauxC_rot_of_clauses`: the statements of `Eaux_rot`, `EauxC_rot` for the
  term clauses;
* `liftRadiusRot`, `liftRadiusRot_spec`: the shrunk tube radius for which the relation
  `N · 2 rotRad N (rotB N) ρ < δ²` holds.

The domain `Ξ^c_j` is open only relative to the layer-constant pairs (`xiDom_eventually`); the
neighbourhood of the start point needed by the identity theorem is therefore taken relative to the
pairs of block-constant fields with a constant `h` (`Def6v2.eq_of_rotation_family_within`).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.SmallField Balaban.Multiscale Balaban.Background Balaban.Localization Metric Set
  Topology

variable {d L N₁ m₁ k N : ℕ} {ϱ : ℝ}

section Core

variable [NeZero L] [NeZero N₁] {P : Consts} {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}

/-- **The term clauses on the landed domain.**  The clauses (H.2)-(H.4), (H.7) of the small-field
class (`Def6v2.SFTermClauses`) on the field domain `Ξ^c_j(𝔹_j(X); 1, ε_j)` with the running-test mass
`bgMass`: what the frame bridges use of a member of the class (`IsSF.termClauses`). -/
abbrev LandedTermClauses (P : Consts) (β ν a : ℕ → ℝ)
    (Tm : Terms d L N₁ m₁ k N ϱ) : Prop :=
  Def6v2.SFTermClauses P
    (Def6v2.xiFieldDom (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) (P.eps d L)) Tm

/-- **The domain inclusion** (field form): a torus field `Ψ`, constant on the `j`-blocks, within
`ρ₂` of the constant `e_{i₀}`, and a field `h = b / ν_j` with `|b - ν_j e_{i₀}| < ρ₂` lie in
`Ξ^c_j(𝔹_j(Z); 1, ε_j)` for a polymer `Z`; here `N ρ₂ < δ²`, `0 < δ ≤ min (c₀, c₁)`,
`(2 K₁ + 2) δ ≤ ε_j`. -/
theorem xiDom_of_field_clauses (hT : LandedTermClauses P β ν a Tm)
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
  have hspec := (hT.gs_spec j hj1 hjk _ hZ).2
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
theorem fp_mem_xiDom_clauses (hT : LandedTermClauses P β ν a Tm)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) (i₀ : Fin N)
    {δ ρ₂ : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N) (hρ0 : 0 < ρ₂)
    (hρ : (N : ℝ) * ρ₂ < δ ^ 2) (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    {c : Cfg d N X'} (hc : c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ₂) :
    XiDom (Tm.gs j (Ypoly j X')) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
      (fieldOf j i₀ X' c) (hOf (nuIdeal L k (ν k) j) X' c) :=
  xiDom_of_field_clauses hT hBg hν hj1 hjk hX i₀ hδ0 hδc0 hδc1 hρ0 hρ hε (fieldOf j i₀ X' c)
    (fun i => c (Sum.inr i)) (fun x i => fieldOf_sub_le hc hρ0.le x i)
    (fun x x' h => fieldOf_block c h) (fun i => by
      have := (dist_le_pi_dist c (refPt i₀ (nuIdeal L k (ν k) j) X') (Sum.inr i)).trans_lt
        (mem_ball.1 hc)
      rwa [dist_eq_norm, refPt_inr] at this)


/-- **The radius of the polydisc of the complex rotation path**: the polar path of a complex
orthogonal `M` with entries `≤ B` relating two points of the ball of radius `ρ` stays in the ball of
radius `rotRad N B ρ = √N ρ (3 + 4x + 2x²)`, `x = N B` (`Def6v2.rotE_of_near_within`). -/
noncomputable def rotRad (N : ℕ) (B ρ : ℝ) : ℝ :=
  Real.sqrt N * ρ * (3 + 4 * (N * B) + 2 * (N * B) ^ 2)

omit [NeZero L] [NeZero N₁] in
theorem mulVec_single_sub_le {M : Matrix (Fin N) (Fin N) ℂ} {B r : ℝ} (hB : 0 ≤ B)
    (hMb : ∀ i k, ‖M i k‖ ≤ B) (i₀ : Fin N) {a a' : Fin N → ℂ}
    (ha : ∀ i, ‖a i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ r)
    (ha' : ∀ i, ‖a' i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ r) (hMa : a' = M.mulVec a) (i : Fin N) :
    ‖(M.mulVec (Pi.single i₀ 1 : Fin N → ℂ)) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤
      r * (1 + N * B) := by
  have e1 : (M.mulVec (Pi.single i₀ 1 : Fin N → ℂ)) i - (Pi.single i₀ 1 : Fin N → ℂ) i =
      (a' i - (Pi.single i₀ 1 : Fin N → ℂ) i) -
        ∑ k', M i k' * (a k' - (Pi.single i₀ 1 : Fin N → ℂ) k') := by
    rw [hMa]
    simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [e1]
  calc _ ≤ ‖a' i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ +
        ‖∑ k', M i k' * (a k' - (Pi.single i₀ 1 : Fin N → ℂ) k')‖ := norm_sub_le _ _
    _ ≤ r + ∑ _k' : Fin N, B * r := by
        gcongr
        · exact ha' i
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k' _ => ?_)
        rw [norm_mul]
        exact mul_le_mul (hMb i k') (ha k') (norm_nonneg _) hB
    _ = r * (1 + N * B) := by simp; ring

omit [NeZero L] [NeZero N₁] in
theorem hOf_sub_le {i₀ : Fin N} {X' : Finset (Site d)} {νj ρ : ℝ} {c : Cfg d N X'}
    (hc : c ∈ ball (refPt i₀ νj X') ρ) (hν : 0 < νj) (x : CTorus d L N₁ m₁ k) (i : Fin N) :
    ‖hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) νj X' c x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤
      ρ / νj := by
  have h1 := (dist_le_pi_dist c (refPt i₀ νj X') (Sum.inr i)).trans (mem_ball.1 hc).le
  rw [dist_eq_norm, refPt_inr] at h1
  have e : hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) νj X' c x i -
      (Pi.single i₀ 1 : Fin N → ℂ) i =
      (c (Sum.inr i) - (νj : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i) / (νj : ℂ) := by
    have hνc : (νj : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
    simp only [hOf]
    field_simp
  rw [e, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hν]
  exact div_le_div_of_nonneg_right h1 hν.le

/-- **The domain inclusion for a field and a constant `h`** with the closeness conditions of
`xiDom_of_field`, in the variable `h` (`ν_j |h - e_{i₀}| < ρ₂`). -/
theorem dom_of_close (hT : LandedTermClauses P β ν a Tm)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {Z : Set (CTorus d L N₁ m₁ k)}
    (hZ : IsPolyDom P.m₀ j Z) (i₀ : Fin N)
    {δ ρ₂ : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N) (hρ0 : 0 < ρ₂)
    (hρ : (N : ℝ) * ρ₂ < δ ^ 2) (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    (Ψ h : Fld d L N₁ m₁ k N)
    (hΨ : ∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ₂)
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    (hh : ∀ x x', h x = h x')
    (hhc : ∀ x i, nuIdeal L k (ν k) j * ‖h x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ < ρ₂) :
    (Def6v2.xiFieldDom (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (N := N) (ϱ := ϱ)
      (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) (P.eps d L)).dom j (Tm.gs j Z) Ψ h := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hνj : 0 < nuIdeal L k (ν k) j := by unfold nuIdeal; positivity
  have hνc : (nuIdeal L k (ν k) j : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
  have := xiDom_of_field_clauses hT hBg hν hj1 hjk hZ i₀ hδ0 hδc0 hδc1 hρ0 hρ hε Ψ
    (fun i => (nuIdeal L k (ν k) j : ℂ) * h 0 i) hΨ hΨb (fun i => by
      have e : (nuIdeal L k (ν k) j : ℂ) * h 0 i - (nuIdeal L k (ν k) j : ℂ) *
          (Pi.single i₀ 1 : Fin N → ℂ) i =
          (nuIdeal L k (ν k) j : ℂ) * (h 0 i - (Pi.single i₀ 1 : Fin N → ℂ) i) := by ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hνj]
      exact hhc 0 i)
  have e : (fun (_ : CTorus d L N₁ m₁ k) i => (nuIdeal L k (ν k) j : ℂ) * h 0 i /
      (nuIdeal L k (ν k) j : ℂ)) = h := by
    funext x i
    rw [mul_div_cancel_left₀ _ hνc, hh 0 x]
  rw [e] at this
  exact this

/-- **Rotation invariance of the term at a centre `x₀`** (from the real clause `rotE` and the polar path
`Def6v2.rotE_of_near_within`): two configurations in the ball of radius `ρ` around the reference
point, related by a matrix `M` of `IsCRot` type with entries bounded by `B`, have the same term.
The domain lemma is used at the radius `ρ₂ ≥ 2 rotRad N B ρ`.  No path in the domain is assumed:
the polar path of `M` stays in the polydisc of radius `rotRad N B ρ` (`rotRad`). -/
theorem E_rot_at (hT : LandedTermClauses P β ν a Tm)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (x₀ : CTorus d L N₁ m₁ k)
    (hx₀ : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x₀ ∈ X') (i₀ : Fin N)
    {δ ρ ρ₂ B : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N)
    (hρ0 : 0 < ρ) (hB : 0 ≤ B) (hρ₂ : 2 * rotRad N B ρ ≤ ρ₂) (hρ : (N : ℝ) * ρ₂ < δ ^ 2)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsCRot M) (hMb : ∀ i k, ‖M i k‖ ≤ B)
    {u u' : Cfg d N X'} (hu : u ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ)
    (hu' : u' ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ) (hrot : rotCfgL M X' u = u') :
    Tm.E j x₀ (Ypoly j X') (fieldOf j i₀ X' u') (hOf (nuIdeal L k (ν k) j) X' u') =
      Tm.E j x₀ (Ypoly j X') (fieldOf j i₀ X' u) (hOf (nuIdeal L k (ν k) j) X' u) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hνj : 0 < nuIdeal L k (ν k) j := by unfold nuIdeal; positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hs1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hN1
  set x : ℝ := (N : ℝ) * B with hx
  have hx0 : 0 ≤ x := by positivity
  set r1 : ℝ := rotRad N B ρ with hr1
  have hr1e : r1 = Real.sqrt N * ρ * (3 + 4 * x + 2 * x ^ 2) := rfl
  have hq1 : (1 : ℝ) ≤ 3 + 4 * x + 2 * x ^ 2 := by nlinarith
  have hρr1 : ρ ≤ r1 := by
    rw [hr1e]
    calc ρ = 1 * ρ * 1 := by ring
      _ ≤ Real.sqrt N * ρ * (3 + 4 * x + 2 * x ^ 2) := by gcongr
  have hr1pos : 0 < r1 := lt_of_lt_of_le hρ0 hρr1
  have hρ₂1 : 2 * r1 ≤ ρ₂ := hρ₂
  have hρ₂0 : 0 < ρ₂ := by linarith
  have hρρ₂ : ρ ≤ ρ₂ := by linarith
  have ball_mono : ∀ {c : Cfg d N X'}, c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ →
      c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ₂ := fun hc => ball_subset_ball hρρ₂ hc
  have hXi := fp_mem_xiDom_clauses hT hBg hν hj1 hjk hX i₀ hδ0 hδc0 hδc1 hρ₂0 hρ hε (ball_mono hu)
  have h0u : fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u' x₀ =
      M.mulVec (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u x₀) := by
    have := fieldOf_rot (j := j) (i₀ := i₀) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) M u
      (x := x₀) hx₀
    rw [← hrot, this]; rfl
  have hhu : hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k (ν k) j) X' u' =
      rotField M (hOf (nuIdeal L k (ν k) j) X' u) := by rw [← hrot, hOf_rot]
  have hMe1 := mulVec_single_sub_le (r := ρ) hB hMb i₀
    (a := fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u x₀)
    (a' := fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u' x₀)
    (fun i => fieldOf_sub_le hu hρ0.le x₀ i) (fun i => fieldOf_sub_le hu' hρ0.le x₀ i) h0u
  have hMe2 := mulVec_single_sub_le (r := ρ / nuIdeal L k (ν k) j) hB hMb i₀
    (a := hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k (ν k) j) X' u x₀)
    (a' := hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k (ν k) j) X' u' x₀)
    (fun i => hOf_sub_le hu hνj x₀ i) (fun i => hOf_sub_le hu' hνj x₀ i)
    (by rw [hhu]; rfl)
  set re : ℝ := min (ρ * (1 + x)) (ρ / nuIdeal L k (ν k) j * (1 + x)) with hre
  have hre0 : 0 ≤ re := le_min (by positivity) (by positivity)
  have hMe : ∀ i, ‖(M.mulVec (Pi.single i₀ 1 : Fin N → ℂ)) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤
      re := fun i => le_min (hMe1 i) (hMe2 i)
  have hre1 : re ≤ ρ * (1 + x) := min_le_left _ _
  have hre2 : re ≤ ρ / nuIdeal L k (ν k) j * (1 + x) := min_le_right _ _
  set r1h : ℝ := Real.sqrt N * ρ * (3 + 3 * x + 2 * x ^ 2) / nuIdeal L k (ν k) j with hr1h
  have hr₁ : Real.sqrt N * (ρ + ρ * (1 + x) + (1 + 2 * x) * re) ≤ r1 := by
    calc _ ≤ Real.sqrt N * (ρ + ρ * (1 + x) + (1 + 2 * x) * (ρ * (1 + x))) := by gcongr
      _ = r1 := by rw [hr1e]; ring
  have hr₁h : Real.sqrt N * (ρ / nuIdeal L k (ν k) j + ρ / nuIdeal L k (ν k) j +
      (1 + 2 * x) * re) ≤ r1h := by
    calc _ ≤ Real.sqrt N * (ρ / nuIdeal L k (ν k) j + ρ / nuIdeal L k (ν k) j +
          (1 + 2 * x) * (ρ / nuIdeal L k (ν k) j * (1 + x))) := by gcongr
      _ = r1h := by rw [hr1h]; ring
  have hνr1h : nuIdeal L k (ν k) j * r1h = Real.sqrt N * ρ * (3 + 3 * x + 2 * x ^ 2) := by
    rw [hr1h]; field_simp
  have hνr1h_lt : nuIdeal L k (ν k) j * r1h < ρ₂ := by
    rw [hνr1h]
    have : Real.sqrt N * ρ * (3 + 3 * x + 2 * x ^ 2) ≤ r1 := by
      rw [hr1e]; gcongr; linarith
    linarith
  -- the class of the polydisc: block-constant fields with a constant `h`
  set P' : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → Prop := fun Ψ' h' =>
    (∀ y y', jBlock d L (N₁ * L ^ m₁) k j y = jBlock d L (N₁ * L ^ m₁) k j y' → Ψ' y = Ψ' y') ∧
      (∀ y y', h' y = h' y') with hP'
  have hP : ∀ (R : Matrix (Fin N) (Fin N) ℂ) Ψ' h', P' Ψ' h' →
      P' (rotField R Ψ') (rotField R h') := fun R Ψ' h' hh =>
    ⟨fun y y' hy => by simp only [rotField]; rw [hh.1 y y' hy],
      fun y y' => by simp only [rotField]; rw [hh.2 y y']⟩
  have hdomC : ∀ Ψ' h', P' Ψ' h' → (∀ y i, ‖Ψ' y i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ r1) →
      (∀ y i, ‖h' y i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ r1h) →
      (Def6v2.xiFieldDom (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (N := N) (ϱ := ϱ)
        (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) (P.eps d L)).dom j (Tm.gs j (Ypoly j X'))
        Ψ' h' := by
    intro Ψ' h' hP1 hΨ' hh'
    refine dom_of_close hT hBg hν hj1 hjk hX i₀ hδ0 hδc0 hδc1 hρ₂0 hρ hε Ψ' h'
      (fun y i => (hΨ' y i).trans (by linarith)) hP1.1 hP1.2 (fun y i => ?_)
    calc _ ≤ nuIdeal L k (ν k) j * r1h := mul_le_mul_of_nonneg_left (hh' y i) hνj.le
      _ < ρ₂ := hνr1h_lt
  have hPu : P' (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u)
      (hOf (nuIdeal L k (ν k) j) X' u) :=
    ⟨fun y y' hy => by
      have := fieldOf_block (j := j) (i₀ := i₀) u hy
      exact funext fun i => congrFun this i, fun _ _ => rfl⟩
  have hDn : {p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N |
      (Def6v2.xiFieldDom (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (N := N) (ϱ := ϱ)
        (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) (P.eps d L)).dom j (Tm.gs j (Ypoly j X'))
        p.1 p.2} ∈ 𝓝[{p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N | P' p.1 p.2}]
        (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u,
          hOf (nuIdeal L k (ν k) j) X' u) := by
    have hev := Balaban.Fluctuation.xiDom_eventually hBg hXi
    have hΩ := (hT.gs_spec j hj1 hjk _ hX).2
    have hsub : {p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N | P' p.1 p.2} ⊆
        Balaban.Fluctuation.layerSub (Tm.gs j (Ypoly j X')) := fun p hp =>
      ⟨isLayerConstant_of_jBlock hjk hΩ hp.1, isLayerConstant_of_jBlock hjk hΩ
        (fun y y' _ => hp.2 y y')⟩
    exact hev.filter_mono (nhdsWithin_mono _ hsub)
  have he : ∀ i, star ((Pi.single i₀ 1 : Fin N → ℂ) i) = (Pi.single i₀ 1 : Fin N → ℂ) i := by
    intro i; by_cases h : i = i₀ <;> simp [h]
  have hr := hT.rotE_of_near_within hj1 hjk hX hx₀ hM.1 hB hMb he
    (r := ρ) (r' := ρ * (1 + x)) (rh := ρ / nuIdeal L k (ν k) j) (rh' := ρ / nuIdeal L k (ν k) j)
    (re := re) (r₁ := r1) (r₁h := r1h) hρ0.le (by positivity) (by positivity) (by positivity)
    hre0 hMe hr₁ hr₁h P' hP hdomC hDn hPu (fun y i => fieldOf_sub_le hu hρ0.le y i)
    (fun y i => hOf_sub_le hu hνj y i)
    (fun y i => by
      by_cases hy : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y ∈ X'
      · rw [← fieldOf_rot M u hy, hrot]
        calc _ ≤ ρ := fieldOf_sub_le hu' hρ0.le y i
          _ ≤ ρ * (1 + x) := by nlinarith [hρ0]
      · have : fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u y =
            (Pi.single i₀ 1 : Fin N → ℂ) := by
          funext i; simp [fieldOf, hy]
        have e : rotField M (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u) y =
            M.mulVec (Pi.single i₀ 1 : Fin N → ℂ) := by
          simp [rotField, this]
        rw [e]; exact (hMe i).trans hre1)
    (fun y i => by rw [← hhu]; exact hOf_sub_le hu' hνj y i)
  rw [← hr]
  refine hT.localE j x₀ (Ypoly j X') _ _ _ _ (fun y hy => ⟨?_, ?_⟩)
  · rw [← hrot, fieldOf_rot M u hy]
  · rw [← hrot, hOf_rot]


/-- **Rotation invariance of the centred term** (centre `0`) from the term clauses; see `E_rot_at`. -/
theorem Eaux_rot_of_clauses (hT : LandedTermClauses P β ν a Tm)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : Site d) ∈ X') (i₀ : Fin N)
    {δ ρ ρ₂ B : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N)
    (hρ0 : 0 < ρ) (hB : 0 ≤ B) (hρ₂ : 2 * rotRad N B ρ ≤ ρ₂) (hρ : (N : ℝ) * ρ₂ < δ ^ 2)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsCRot M) (hMb : ∀ i k, ‖M i k‖ ≤ B)
    {u u' : Cfg d N X'} (hu : u ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ)
    (hu' : u' ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ) (hrot : rotCfgL M X' u = u') :
    Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' u' = Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' u :=
  E_rot_at hT hBg hν hj1 hjk hX 0 (by rw [unlift_zero]; exact h0) i₀ hδ0 hδc0 hδc1 hρ0 hB hρ₂ hρ hε
    hM hMb hu hu' hrot

/-- **Rotation invariance of the centred term** (from the real clause `rotE` and the polar path,
`E_rot_at`): two configurations in the ball of radius `ρ` around the reference point, related by a
matrix `M` of `IsCRot` type with entries bounded by `B`, have the same term.  The domain lemma is
used at the radius `ρ₂ ≥ 2 rotRad N B ρ`. -/
theorem EauxC_rot_of_clauses (hT : LandedTermClauses P β ν a Tm)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (y : Site d) (hnw : NonWind L N₁ m₁ k j X') (hy : y ∈ X') (i₀ : Fin N)
    {δ ρ ρ₂ B : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N)
    (hρ0 : 0 < ρ) (hB : 0 ≤ B) (hρ₂ : 2 * rotRad N B ρ ≤ ρ₂) (hρ : (N : ℝ) * ρ₂ < δ ^ 2)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsCRot M) (hMb : ∀ i k, ‖M i k‖ ≤ B)
    {u u' : Cfg d N X'} (hu : u ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ)
    (hu' : u' ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ) (hrot : rotCfgL M X' u = u') :
    EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X' u' = EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X' u :=
  E_rot_at hT hBg hν hj1 hjk hX (blockPt j y) (blockPt_mem_Ypoly hjk hnw hy) i₀ hδ0 hδc0 hδc1 hρ0
    hB hρ₂ hρ hε hM hMb hu hu' hrot

/-- **The radius of the tube**:
`ρ_j = (ε_j / (2 K₁ + 2))² / (4 N √N (3 + 4x + 2x²))`, `x = N · rotB N`, of order `ε_j²`; it
satisfies the radius relation `N · 2 rotRad N (rotB N) ρ < δ²` of `E_rot_at`
(`liftRadiusRot_spec`). -/
noncomputable def liftRadiusRot (d L N : ℕ) [NeZero L] (P : Consts) (j : ℕ) : ℝ :=
  (P.eps d L j / (2 * bgK1 d L N + 2)) ^ 2 /
    (4 * N * Real.sqrt N * (3 + 4 * (N * rotB N) + 2 * (N * rotB N) ^ 2))

omit [NeZero N₁] in
theorem liftRadiusRot_pos {P : Consts} {j : ℕ} (hε : 0 < P.eps d L j) (i₀ : Fin N) :
    0 < liftRadiusRot d L N P j := by
  have hK := bgK1_pos d L N
  have hN : 0 < N := Fin.pos i₀
  unfold liftRadiusRot rotB
  positivity

omit [NeZero N₁] in
theorem le_rotRad {B ρ : ℝ} (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (i₀ : Fin N) : ρ ≤ rotRad N B ρ := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hs1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hN1
  have hx0 : 0 ≤ (N : ℝ) * B := by positivity
  unfold rotRad
  calc ρ = 1 * ρ * 1 := by ring
    _ ≤ Real.sqrt N * ρ * (3 + 4 * (N * B) + 2 * (N * B) ^ 2) := by gcongr; nlinarith

omit [NeZero N₁] in
/-- The radius relation holds for `liftRadius` as soon as `ε_j ≤ (2 K₁ + 2) min (c₀, c₁)`. -/
theorem liftRadiusRot_spec {P : Consts} {j : ℕ} (hε : 0 < P.eps d L j) (i₀ : Fin N)
    (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ bgC0 d L N ∧ δ ≤ bgC1 d L N ∧
      (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j ∧
      (N : ℝ) * (2 * rotRad N (rotB N) (liftRadiusRot d L N P j)) < δ ^ 2 := by
  have hK := bgK1_pos d L N
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hK2 : 0 < 2 * bgK1 d L N + 2 := by positivity
  refine ⟨P.eps d L j / (2 * bgK1 d L N + 2), by positivity, ?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hK2]; exact hsmall.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hK2.le)
      |>.trans_eq (by ring)
  · rw [div_le_iff₀ hK2]; exact hsmall.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hK2.le)
      |>.trans_eq (by ring)
  · rw [mul_div_cancel₀ _ hK2.ne']
  · unfold rotRad liftRadiusRot
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
    have hC : 0 < 3 + 4 * ((N : ℝ) * rotB N) + 2 * ((N : ℝ) * rotB N) ^ 2 := by
      unfold rotB; positivity
    have hδ : 0 < (P.eps d L j / (2 * bgK1 d L N + 2)) ^ 2 := by positivity
    have hN0 : (0 : ℝ) < N := by linarith
    generalize (3 + 4 * ((N : ℝ) * rotB N) + 2 * ((N : ℝ) * rotB N) ^ 2) = C at hC ⊢
    have : (N : ℝ) * (2 * (Real.sqrt N * ((P.eps d L j / (2 * bgK1 d L N + 2)) ^ 2 /
        (4 * N * Real.sqrt N * C)) * C)) =
        (P.eps d L j / (2 * bgK1 d L N + 2)) ^ 2 / 2 := by
      field_simp
      ring
    rw [this]; linarith


end Core

end Balaban.SmallField.Def6
