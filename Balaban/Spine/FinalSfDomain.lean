/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfBound
public import Balaban.LargeField.R.PsiZeroBlocks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The domain facts on the `χ`-support

A6-3 (a), item 1: from the level-`k` real domain of the datum on the support of `χ_k(univ)`
(`inPsiTilde_genW_univ_late`) the facts used by the measurability and the boundedness of
`sfFactor2`: the datum is in the real domain `𝒟_ℝ` (`DomSet`), the real background `φ̄_k` is a unit
field, and the block field is bounded.
-/

@[expose] public section

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.LargeField.Def7
  Balaban.SmallField.Def6v2 Balaban.Localization

namespace Balaban.RootFSpine

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N (j + 1) m₁ ϱ)
  (hv : EuclideanSpace ℝ (Fin N))
  (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N))

/-- The datum is in the real domain `𝒟_ℝ` when the field is in the data domain `Ψ̃`. -/
theorem mem_DomSet_of_inPsiTilde {m η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ bgC1 S.d S.L N)
    (hP : InPsiTilde (C.genW (Set.univ : Set (Torus S.d (n (j + 1))))) m η (parentPsi C ψk)
      (fun i => hv i)) : ψk ∈ DomSet C hv m :=
  ⟨η, hη0, hη1, parentPsi C ψk, fun i => hv i, hP,
    fun x hx i => liftSingle_Ψ_eq_parentPsi C _ ψk hv hx i,
    fun x hx i => by unfold Dfam; rw [liftSingle_h _ _ _ hx]; rfl⟩

/-- **The real background `φ̄_k` is a unit field** on the domain (coordinates of modulus `≤ 1`). -/
theorem abs_phiBar_le_one
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    (hψ : ψk ∈ DomSet C hv (C.cs.muBg (j + 1))) (z : BgT C.geo (j + 1)) (i : Fin N) :
    |(C.phiBar (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv z) i| ≤ 1 := by
  obtain ⟨δ, hδ0, hδc, hD⟩ := hψ
  obtain ⟨φ, α, hs, hb, hu, hunit, -, -⟩ := bg_real HB hδ0 hδc hD
  obtain ⟨hfC, -⟩ := bgFieldC_eq hs hu
  have hz : z ∈ (C.genW (Set.univ : Set (Torus S.d (n (j + 1))))).Ω 1 := by
    rw [genW_Ω_univ C (by omega)]; exact Finset.mem_univ _
  have hphiK : C.phiK (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv = φ := hfC
  have key : (C.phiBar (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv z) i =
      (φ (⟨z, hz⟩, i)).re := by
    show (barField (C.genW (Set.univ : Set (Torus S.d (n (j + 1))))) (Dfam C hv ψk).Ψ
      (C.phiK (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv) z i).re = _
    rw [hphiK]
    simp [barField, hz]
  rw [key]
  have h1 := hunit ⟨z, hz⟩
  have h2 : ‖φ (⟨z, hz⟩, i)‖ ^ 2 ≤ 1 := by
    rw [← h1.2]
    exact Finset.single_le_sum (f := fun i => ‖φ (⟨z, hz⟩, i)‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h3 : ‖φ (⟨z, hz⟩, i)‖ ≤ 1 := by nlinarith [norm_nonneg (φ (⟨z, hz⟩, i))]
  exact (Complex.abs_re_le_norm _).trans h3

/-- **A block field in the data domain is bounded**: `‖ψ_k(b)‖ ≤ 2` for `η ≤ 1`. -/
theorem norm_le_two_of_inPsiTilde {m η : ℝ} (hη1 : η ≤ 1)
    (hP : InPsiTilde (C.genW (Set.univ : Set (Torus S.d (n (j + 1))))) m η (parentPsi C ψk)
      (fun i => hv i)) (b : BlockAt S n M K (j + 1)) : ‖ψk b‖ ≤ 2 := by
  obtain ⟨y0, hy0⟩ : ∃ y0, blkToBlock C.geo C.hnn C.hkK y0 = b :=
    (torusCast_surjective' _) b
  obtain ⟨x, hx⟩ := Balaban.exists_blockMap_eq (fine_eq_block S.L (C.geo.M1 * (C.geo.c * n (j + 1)))
    (j + 1)) (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) (j + 1)) y0
  have hx' : jBlock S.d S.L (C.geo.M1 * (C.geo.c * n (j + 1))) (j + 1) (j + 1) x = y0 := hx
  have hxd : x ∈ dataSites (C.genW (Set.univ : Set (Torus S.d (n (j + 1))))) := by
    refine (mem_dataSites _).2 (Or.inl ?_)
    rw [genW_Ω_univ C (by omega)]; exact Finset.mem_univ _
  have h2 := hP.r2 x hxd
  have e : parentPsi C ψk x = fun i => ψk b i := by
    funext i
    unfold parentPsi
    rw [hx', hy0]
  rw [e] at h2
  have h3 : ∑ i, ψk b i ^ 2 = ‖ψk b‖ ^ 2 := parent_sum_sq_eq_norm_sq (ψk b)
  rw [h3] at h2
  have h4 := (abs_lt.1 h2).2
  nlinarith [norm_nonneg (ψk b)]

/-- The numerical hypotheses of the domain transport (radii against the tolerance):
`t = 4 (d+1) δ_k`, the child radius `η_c = C₄ K₁ t`. -/
theorem parent_of_mem_Asupp (hL : 2 ≤ S.L) {ν : ℝ} (hν : 0 < ν) (hunit : ‖hv‖ = 1)
    (hδ : 0 < C.cs.delta (j + 1)) (hδ1 : (S.d + 1) * C.cs.delta (j + 1) ≤ 1)
    (hμ : C.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (hμBg : C.cs.muBg (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    (hψ : ψk ∈ Asupp C hv) :
    InPsiTilde (C.genW (Set.univ : Set (Torus S.d (n (j + 1)))))
      (sfBgMassAt S.L (j + 1) ν) (4 * (S.d + 1) * C.cs.delta (j + 1)) (parentPsi C ψk)
      (fun i => hv i) := by
  have HBmu : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.mu (j + 1)) := by
    rw [hμ, ← hμBg]; exact HB
  exact inPsiTilde_genW_univ_late C ψk hv hL hν hunit hδ hδ1 hμ hψ HBmu

end Ctx

end Balaban.RootFSpine
