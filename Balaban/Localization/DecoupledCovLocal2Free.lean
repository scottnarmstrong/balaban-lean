/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCovLocal2

/-!
# I-4c (v), two backgrounds: blocks next to `Y`

The two-background locality of `DecoupledCovLocal2` controls `C^{1/2}` at the unit points whose
`(k+1)`-block lies in `Y`.  The fluctuation problem also reads the field on the neighbours of `Y`.
Here the blocks that meet `Y` or a neighbour of `Y` but are not contained in `Y` are treated: no
active centre of either parameter vector has its cube meeting such a block (`free_of_block`: the
dichotomy of `hdich_aux` and the fact that a block lies in the thickened cube of every centre whose
cube meets it), so the operator `Z_s` vanishes on the block (`decZ_apply_eq_zero`), and
`C_x(s) h = A h` there, independently of the background (`decCov_free`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Free

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x₀ ν : ℝ}

/-- A site of the top layer lies, together with its neighbours, in the thickened cube of every
centre whose cube contains a site of its `(k+1)`-block. -/
theorem mem_hat_of_block (S : DGSetting G a ν) {z : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hz : z ∈ cubeIdx G) {y u : CTorus d L N₁ m₁ (k + 1)} (hyz : y ∈ intBox z)
    (hyl : y ∈ G.layer (k + 1))
    (hjb : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) u = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y)
    (v : Fin d → ℤ) (hv : ∀ μ, |(v μ : ℝ)| ≤ 1) :
    u + (intTorus v : CTorus d L N₁ m₁ (k + 1)) ∈ hatBox z := by
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast S.hL
  have hLr : (1 : ℝ) ≤ L := by linarith
  have hnle : k + 1 ≤ z.1 + 1 :=
    layer_le_of_mem_box S.cover_sep (by have := S.hL; omega) hz (by omega) le_rfl hyl hyz
  have hcell : SameCell (L ^ (k + 1)) u y := sameCell_of_jBlock_eq (le_refl _) hjb
  have hlpos : 0 < L ^ (k + 1) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  obtain ⟨w, hw, hwb⟩ := exists_int_of_sameCell hlpos hcell
  have hsum : u + (intTorus v : CTorus d L N₁ m₁ (k + 1)) =
      y + (intTorus (w + v) : CTorus d L N₁ m₁ (k + 1)) := by
    rw [hw, add_assoc, intTorus_add_aux]
  rw [hsum]
  refine inBox_hat_of_add_int hyz (w + v) (B := (L : ℝ) ^ (k + 1)) (fun μ => ?_) ?_
  · have h1 := hwb μ
    have h2 := hv μ
    have h1' : |w μ| < ((L ^ (k + 1) : ℕ) : ℤ) := by
      have : |((w μ : ℤ) : ℝ)| < (((L ^ (k + 1) : ℕ) : ℤ) : ℝ) := by simpa using h1
      exact_mod_cast this
    have h2' : |v μ| ≤ 1 := by exact_mod_cast h2
    have h3 : |(w + v) μ| ≤ ((L ^ (k + 1) : ℕ) : ℤ) := by
      have := abs_add_le (w μ) (v μ)
      simp only [Pi.add_apply]
      omega
    have h4 : |(((w + v) μ : ℤ) : ℝ)| ≤ (((L ^ (k + 1) : ℕ) : ℤ) : ℝ) := by
      have := (Int.cast_le (R := ℝ)).2 h3
      simpa using this
    simpa using h4
  · calc (L : ℝ) ^ (k + 1) ≤ (L : ℝ) ^ (z.1 + 1) := pow_le_pow_right₀ hLr hnle
      _ = L * (L : ℝ) ^ z.1 := by ring
      _ ≤ 3 * (L : ℝ) ^ 2 * (L : ℝ) ^ z.1 := by
        have hp : (0 : ℝ) ≤ (L : ℝ) ^ z.1 := by positivity
        nlinarith [mul_nonneg hp (by linarith : (0:ℝ) ≤ L)]

variable {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}

/-- **No active centre meets a block that sticks out of `Y` but touches `Y`.**  Let `y₀` be a site
of `Ω₁`, `x₀ ∈ Y` a site with `x₀ = y₀ + v`, `|v| ≤ 1` (so `y₀ ∈ Y` or `y₀` is a neighbour of
`Y`), and suppose the `(k+1)`-block of `y₀` is not contained in `Y`.  Then no site of this block
lies in the core of a parameter vector vanishing on `𝔓 ∖ 𝒞`. -/
theorem free_of_block (S : DGSetting G a ν) (hconn : HatConn G)
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1) Y)
    {u : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} (hu : ∀ P ∈ parCubes G X₁, P ∉ 𝒞 → u P = 0)
    {y₀ : G.Ω 1} (hy₀ : (y₀ : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1))
    {x₀ : CTorus d L N₁ m₁ (k + 1)} (hx₀ : x₀ ∈ Y) {v : Fin d → ℤ} (hv : ∀ μ, |(v μ : ℝ)| ≤ 1)
    (hx₀v : x₀ = (y₀ : CTorus d L N₁ m₁ (k + 1)) + (intTorus v : CTorus d L N₁ m₁ (k + 1)))
    (hnot : ¬ ∀ y' : G.Ω 1, jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (y' : CTorus d L N₁ m₁ (k + 1)) =
      jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (y₀ : CTorus d L N₁ m₁ (k + 1)) →
        (y' : CTorus d L N₁ m₁ (k + 1)) ∈ Y) :
    ∀ y' : G.Ω 1, jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (y' : CTorus d L N₁ m₁ (k + 1)) =
      jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (y₀ : CTorus d L N₁ m₁ (k + 1)) →
        (y' : CTorus d L N₁ m₁ (k + 1)) ∉ Core G u := by
  classical
  intro y' hy'b hcore
  unfold Core at hcore
  obtain ⟨z, hzZ, hyz⟩ := Finset.mem_biUnion.1 hcore
  have hzZ' := Finset.mem_filter.1 hzZ
  have hP := hact_aux u hu z hzZ'.2
  have hybox : (y' : CTorus d L N₁ m₁ (k + 1)) ∈ intBox z := coreBox_subset_box hyz
  have hy'l : (y' : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) :=
    layer_top_of_jBlock G hy'b.symm hy₀
  rcases hdich_aux S hconn hY z hzZ'.1 hP with h | h
  · apply hnot
    intro y'' hy''b
    apply h y''
    have := mem_hat_of_block S hzZ'.1 hybox hy'l (u := (y'' : CTorus d L N₁ m₁ (k + 1)))
      (hy''b.trans hy'b.symm) 0 (fun μ => by simp)
    have h0 : (intTorus (0 : Fin d → ℤ) : CTorus d L N₁ m₁ (k + 1)) = 0 := by
      funext μ; simp [intTorus_apply]
    rwa [h0, add_zero] at this
  · have hx₀hat : x₀ ∈ hatBox z := by
      rw [hx₀v]
      exact mem_hat_of_block S hzZ'.1 hybox hy'l (hy'b.symm) v hv
    have hx₀Ω : x₀ ∈ G.Ω 1 := (Finset.mem_filter.1 (hY.1 hx₀)).2
    exact h ⟨x₀, hx₀Ω⟩ hx₀hat hx₀

end Free

section FreeCov

open MeasureTheory Set

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x₀ ν : ℝ}
variable {φ φ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {α α' : G.Ω 1 → ℂ}
  {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}

/-- `Z_s w` vanishes at the sites outside the core of `s` (DG5, support). -/
theorem decZ_apply_eq_zero (w : G.Ω 1 × Fin N → ℂ) {y : G.Ω 1}
    (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∉ Core G s) (i : Fin N) :
    (decZ G a aT x₀ ν α s φ *ᵥ w) (y, i) = 0 := by
  have hz : ∀ f : G.Ω 1 → ℂ, (Gsx G a aT x₀ ν α s *ᵥ f) y = 0 := fun f => by
    by_contra hne
    exact hy (dg5x_support (x := x₀) (α := α) (a := a) (aT := aT) (ν := ν) s f y hne)
  unfold decZ decPi
  rw [Matrix.sub_mulVec, Pi.sub_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, liftOp_mulVec, liftOp_mulVec, hz, hz, sub_zero]

/-- The unit points whose `(k+1)`-block contains no site of the cores of `u` and `u'`. -/
def FreeBlk (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (u u' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (b : unitPts G) : Prop :=
  ∀ y : G.Ω 1, unitBlock1 (unitBlock (y : CTorus d L N₁ m₁ (k + 1))) = unitBlock1 b.1 →
    (y : CTorus d L N₁ m₁ (k + 1)) ∉ Core G u ∧ (y : CTorus d L N₁ m₁ (k + 1)) ∉ Core G u'

/-- **Covariance at a free block**: if the `(k+1)`-block of the unit point `b` avoids the cores,
`C_x(s) h = A h` there, whatever the backgrounds, so the outputs agree as soon as the inputs agree
on the unit points of the block. -/
theorem decCov_free (b : unitPts G)
    (hb : FreeBlk G s s' b) (h h' : unitPts G × Fin N → ℂ)
    (hh : ∀ b' : unitPts G, unitBlock1 b.1 = unitBlock1 b'.1 → ∀ i, h (b', i) = h' (b', i))
    (i : Fin N) :
    (decCov G a aT x₀ ν α s φ (unitQ G) (unitP G) *ᵥ h) (b, i) =
      (decCov G a aT x₀ ν α' s' φ' (unitQ G) (unitP G) *ᵥ h') (b, i) := by
  classical
  rw [decCov_mulVec_eq, decCov_mulVec_eq, Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
  have hbo : ∀ b3 : unitPts G, unitP G b b3 ≠ 0 → unitBlock1 b.1 = unitBlock1 b3.1 :=
    fun b3 hP => unitP_ne_zero_imp hP
  have t0 : (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h) (b, i) =
      (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h') (b, i) := by
    refine covA_apply_congr _ _ _ _ _ _ _ (hh b rfl i) ?_
    rintro ⟨b3, j⟩ hq
    obtain ⟨hj, hP⟩ := liftOp_ne_zero_imp _ hq
    simp only at hj hP
    subst hj
    exact hh b3 (hbo b3 hP) _
  -- the `Z`-term vanishes on the whole block
  have zero : ∀ (ss : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (aa : G.Ω 1 → ℂ)
      (pp : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (hss : ∀ y : G.Ω 1,
        unitBlock1 (unitBlock (y : CTorus d L N₁ m₁ (k + 1))) = unitBlock1 b.1 →
        (y : CTorus d L N₁ m₁ (k + 1)) ∉ Core G ss) (g : unitPts G × Fin N → ℂ),
      (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ
        (liftRect N (unitQ G) *ᵥ (decZ G a aT x₀ ν aa ss pp *ᵥ
          ((liftRect N (unitQ G))ᵀ *ᵥ g)))) (b, i) = 0 := by
    intro ss aa pp hss g
    have hW : ∀ b3 : unitPts G, unitBlock1 b.1 = unitBlock1 b3.1 → ∀ j,
        (liftRect N (unitQ G) *ᵥ (decZ G a aT x₀ ν aa ss pp *ᵥ
          ((liftRect N (unitQ G))ᵀ *ᵥ g))) (b3, j) = 0 := by
      intro b3 hb3 j
      have e0 : (liftRect N (unitQ G) *ᵥ (0 : G.Ω 1 × Fin N → ℂ)) (b3, j) = 0 := by simp
      rw [← e0]
      refine mulVec_apply_congr _ _ _ _ ?_
      rintro ⟨y, j'⟩ hq
      obtain ⟨hj, hQ⟩ := liftRect_ne_zero_imp _ hq
      simp only at hj hQ
      subst hj
      exact decZ_apply_eq_zero _ (hss y (by rw [unitQ_ne_zero_imp hQ]; exact hb3.symm)) _
    have e1 := covA_apply_congr (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G))
      (liftRect N (unitQ G) *ᵥ (decZ G a aT x₀ ν aa ss pp *ᵥ
          ((liftRect N (unitQ G))ᵀ *ᵥ g))) 0 (b, i) (by rw [hW b rfl i]; rfl) (by
        rintro ⟨b3, j⟩ hq
        obtain ⟨hj, hP⟩ := liftOp_ne_zero_imp _ hq
        simp only at hj hP
        subst hj
        rw [hW b3 (hbo b3 hP) _]; rfl)
    rw [e1]; simp
  rw [t0, zero s α φ (fun y hy => (hb y hy).1) _, zero s' α' φ' (fun y hy => (hb y hy).2) _]

end FreeCov

section FreeSqrt

open MeasureTheory Set

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}
variable {φ φ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {α α' : G.Ω 1 → ℂ}
  {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
  {δ κ : ℝ}

/-- **I-4c (v), two backgrounds, at the blocks next to `Y`: locality of `C^{1/2}`.**  The output
point `b` is either a unit point with its `(k+1)`-block in `Y` (the inputs then agree on the unit
points of the output blocks and of the blocks meeting `S_Y`), or a unit point whose block avoids the
cores of both parameter vectors (the inputs then agree on the unit points of this block). -/
theorem I4c_local_sqrt3 (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α κ s)
    (hfam' : ∀ x, 0 ≤ x → XData G a aT ν x α' κ s')
    (H : LocHyp G X₁ 𝒞 Y α s s')
    (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → α x = α' x)
    (hφY : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → φ y = φ' y)
    (hφ : IsConstraintField G δ φ) (hφ' : IsConstraintField G δ φ') (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (h h' : unitPts G × Fin N → ℂ) {b : unitPts G}
    (hb : UnitOut G Y b ∨ FreeBlk G s s' b)
    (hh : ∀ b' : unitPts G, (UnitOut G Y b' ∨ UnitIn G X₁ 𝒞 Y b' ∨ unitBlock1 b.1 = unitBlock1 b'.1) →
      ∀ i, h (b', i) = h' (b', i))
    (i : Fin N) :
    (decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) *ᵥ h) (b, i) =
      (decCovSqrt G a aT ν α' s' φ' (unitQ G) (unitP G) *ᵥ h') (b, i) := by
  rcases hb with hb | hb
  · exact I4c_local_sqrt2 hfam hfam' H hA hφY hφ hφ' hδ hsm h h'
      (fun b' hb' => hh b' (by rcases hb' with h1 | h1; exact Or.inl h1; exact Or.inr (Or.inl h1)))
      hb i
  · classical
    have Hs := (standing_pair hfam hφ hδ hsm).1
    have Hs' := (standing_pair hfam' hφ' hδ hsm).1
    have e1 := intMat_mulVec_apply (integrable_decSqrtInt Hs) h (b, i)
    have e2 := intMat_mulVec_apply (integrable_decSqrtInt Hs') h' (b, i)
    have e3 : ∫ x in Ioi (0:ℝ), (decSqrtInt G a aT ν α s φ (unitQ G) (unitP G) x *ᵥ h) (b, i) =
        ∫ x in Ioi (0:ℝ), (decSqrtInt G a aT ν α' s' φ' (unitQ G) (unitP G) x *ᵥ h') (b, i) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      simp only [decSqrtInt, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
      rw [decCov_free b hb h h' (fun b' hb' => hh b' (Or.inr (Or.inr hb'))) i]
    simp only [decCovSqrt, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
    rw [e1, e2, e3]

end FreeSqrt

end Balaban.Localization
