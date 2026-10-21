/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkClusterReal
public import Balaban.Inhabited.E0CoeffFamilyRotBlock
public import Balaban.Localization.DecEquivRot

/-!
# Invariance of the cluster terms under a change of the cube variables (Theorem 3.4)

The local terms of the cluster expansion with one mark are integrals over the product measure of the
cubes; a family of measure-preserving equivalences of the variables of the cubes that carries the
activities and the mark of one system to those of another leaves them unchanged.

* `Gst_equiv`, `markTerm_equiv`;
* `HoleStep.markOf_rot`: the cut-off mark under a rotation of the fluctuation field by an isometry of
  `ℝ^N` with a real orthogonal matrix, with the fixed values and the function rotated.
-/

@[expose] public section

open MeasureTheory

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.Localization.DecEquiv
  Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

/-- **Invariance of `G*(Y₀, S)` under a measure-preserving change of the cube variables**: if a
family of measure-preserving equivalences `E` of the variables of the cubes carries the activities
`H₁` and the mark `G₁` to `H₂` and `G₂` (on a set `Q` of full measure), the local terms agree. -/
theorem Gst_equiv {Lb : Type*} [Fintype Lb] {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] (Lab : CubeLabels m₀ j Ω Lb)
    (E : ∀ b, Ωb b ≃ᵐ Ωb b) (hE : ∀ b, MeasurePreserving (E b) (μ b) (μ b))
    {Q : Set (∀ b, Ωb b)} (hQ : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Q)
    (H₁ H₂ : Lb → (∀ b, Ωb b) → ℂ) (S₀ : Finset 𝔅) (G₁ G₂ : (∀ b, Ωb b) → ℂ) (S : Finset 𝔅)
    (hH : ∀ y, ∀ Φ ∈ Q, H₂ y (fun b => E b (Φ b)) = H₁ y Φ)
    (hG : ∀ Φ ∈ Q, G₂ (fun b => E b (Φ b)) = G₁ Φ) :
    Gst μ Lab H₂ S₀ G₂ S = Gst μ Lab H₁ S₀ G₁ S := by
  have hF : Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
      (marksK μ Subtype.val (presum Lab H₂) (gMark S₀ G₂)) S =
      Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
      (marksK μ Subtype.val (presum Lab H₁) (gMark S₀ G₁)) S := by
    funext l
    unfold Ff
    refine PY_congr _ _ S fun Z _ => ?_
    unfold marksK mayerK
    refine integral_comp_of_pi_equiv μ E hE hQ fun Φ hΦ => ?_
    unfold mayerAct polyAct
    refine Finset.sum_congr rfl fun C _ => Finset.prod_congr rfl fun t _ => ?_
    unfold Hlam presum gMark
    simp only [hH _ Φ hΦ, hG Φ hΦ]
  unfold Gst
  rw [hF]

variable {Lb : Type*} [Fintype Lb]
  {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω Lb}
  {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
  [∀ b, MeasurableSpace (Ωb b)] {εH κH κ0 Kc : ℝ}

/-- **Invariance of the cluster term of one mark under a measure-preserving change of the cube
variables** (`Gst_equiv` at every value of the interpolation parameter). -/
theorem markTerm_equiv (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (E : ∀ b, Ωb b ≃ᵐ Ωb b) (hE : ∀ b, MeasurePreserving (E b) (μ b) (μ b))
    {Q : Set (∀ b, Ωb b)} (hQ : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Q)
    (A₁ A₂ : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (V : Set (CTorus d L N₁ m₁ K))
    (G₁ G₂ : (∀ b, Ωb b) → ℂ) (S : Finset 𝔅)
    (hA : ∀ (u : ℝ) y, ∀ Φ ∈ Q, (A₂ (u : ℂ)).H y (fun b => E b (Φ b)) = (A₁ (u : ℂ)).H y Φ)
    (hG : ∀ Φ ∈ Q, G₂ (fun b => E b (Φ b)) = G₁ Φ) :
    markTerm μ A₂ V G₂ S = markTerm μ A₁ V G₁ S := by
  unfold markTerm
  exact intervalIntegral.integral_congr fun u _ =>
    Gst_equiv μ Lab E hE hQ _ _ _ G₁ G₂ S (hA u) hG

namespace HoleStep

variable {k N : ℕ} {ϱ ϱ' : ℝ} (S : HoleStep d L N₁ m₁ k N ϱ ϱ') {Cb : Type*}

/-- **The cut-off mark under a rotation of the field**: rotating the variables of the cubes by the
isometry `e` of `ℝ^N` with complex matrix `R` (`hR`, a real orthogonal matrix, `hRv`), the fixed
values by `R` and the function by `R` on the ball of the mark leaves the mark unchanged. -/
theorem markOf_rot (inner : Finset S.U) (cb : inner → Cb) {ψout₁ ψout₂ : S.U → Fin N → ℂ}
    (U₀ : Finset S.U) (r : ℝ) {T₁ T₂ : (S.U → Fin N → ℂ) → ℂ} (e : Rn N ≃ₗᵢ[ℝ] Rn N)
    (R : Matrix (Fin N) (Fin N) ℂ)
    (hR : ∀ v : Rn N, R *ᵥ (fun i => ((v i : ℝ) : ℂ)) = fun i => ((e v i : ℝ) : ℂ))
    (hRv : ∀ v, vn (R *ᵥ v) = vn v) (hout : ψout₂ = rotSite R ψout₁)
    (hT : ∀ ψ : S.U → Fin N → ℂ, (∀ b ∈ U₀, vn (ψ b) < r) → T₂ (rotSite R ψ) = T₁ ψ)
    (Φ : ∀ b, {u : inner // cb u = b} → Rn N) :
    S.markOf inner cb ψout₂ U₀ r T₂ (fun b u => e (Φ b u)) = S.markOf inner cb ψout₁ U₀ r T₁ Φ := by
  have hfill : S.fill inner (ungroup cb fun b u => e (Φ b u)) ψout₂ =
      rotSite R (S.fill inner (ungroup cb Φ) ψout₁) := by
    funext b i
    unfold fill
    by_cases hb : b ∈ inner
    · simp only [hb, ↓reduceDIte, rotSite_apply]
      have := congrFun (hR (ungroup cb Φ ⟨b, hb⟩)) i
      rw [Matrix.mulVec, dotProduct] at this
      rw [this]
      rfl
    · simp only [hb, ↓reduceDIte, rotSite_apply, hout]
  unfold markOf
  rw [hfill]
  have hcond : (∀ b ∈ U₀, vn (rotSite R (S.fill inner (ungroup cb Φ) ψout₁) b) < r) ↔
      (∀ b ∈ U₀, vn (S.fill inner (ungroup cb Φ) ψout₁ b) < r) := by
    simp only [rotSite, hRv]
  split_ifs with h1 h2 h2
  · exact hT _ h2
  · exact absurd (hcond.1 h1) h2
  · exact absurd (hcond.2 h2) h1
  · rfl

end HoleStep

end Balaban.Fluctuation
