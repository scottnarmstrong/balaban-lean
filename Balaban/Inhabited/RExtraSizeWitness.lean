module

public import Balaban.LargeField.R.RExtraSize
public import Balaban.Inhabited.RRipeCardWitness
public import Balaban.Inhabited.SizeModExtendWitness

/-!
# Non-vacuity of `RExtraSize`

On the landed admissible history `RipeRemoval.ripeRemHistory` (genuine radii, `k₀ = T`,
`K = T + 1`, one removed component at scale `T`), with a fine frame of `m₀ = m₁ = 0`, `M = 1`
and the label `X` of all cubes of `𝕋_T` (its fine lift is the whole fine torus, a member of
`𝒟_T`), all hypotheses of `d7Size_le_d7SizePre_add`, `d7SizePre_le_d7Size_le` and
`d7Size_le_d7SizePre_add_removed` hold.  The increment is not zero: `Ω_T^post ≠ Ω_T^pre`
(`ripeRemHistory_omegaPost_ne`), so `X ∩ (⋃ Rem_T ∖ Ω_T^pre)` is nonempty (at least one cube);
its exact size is not computed here.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.LargeField RadiiHist RipeRemoval RadiiSet Def7

/-- **Non-vacuity of `RExtraSize`.** -/
theorem rExtraSize_instance :
    ∃ (A : LabHist wS (side wS (bigN wS) (Tstar wS + 1)) wR (Tstar wS) (Tstar wS + 1))
      (F : FineSizeFrame wS (side wS (bigN wS) (Tstar wS + 1)) 1 (Tstar wS + 1) 0 0)
      (X : Finset (Torus wS.d (side wS (bigN wS) (Tstar wS + 1) (Tstar wS)))),
      A.H = ripeRemHistory ∧ 1 ≤ (A.H.newlyActive X).card ∧
      d7SizePre F A (Tstar wS) X ≤ d7Size F A (Tstar wS) X ∧
      d7Size F A (Tstar wS) X ≤ d7SizePre F A (Tstar wS) X +
        ((wS.d : ℝ) * wS.L + wS.d + 3) * ((A.H.newlyActive X).card : ℝ) ∧
      d7Size F A (Tstar wS) X ≤ d7SizePre F A (Tstar wS) X +
        ((wS.d : ℝ) * wS.L + wS.d + 3) *
          (((A.H.remMeeting X).card : ℝ) * ((2 * wS.rho (Tstar wS) + 10 : ℕ) ^ wS.d : ℕ)) := by
  obtain ⟨F⟩ : Nonempty (FineSizeFrame wS (side wS (bigN wS) (Tstar wS + 1)) 1 (Tstar wS + 1) 0 0) :=
    FineSizeFrame.nonempty (by simp)
  let A : LabHist wS (side wS (bigN wS) (Tstar wS + 1)) wR (Tstar wS) (Tstar wS + 1) :=
    ⟨ripeRemHistory, ripeRemHistory_admissible, fun _ _ => 0⟩
  have hk : 1 ≤ Tstar wS := one_le_Tstar _
  have hkK : Tstar wS ≤ Tstar wS + 1 := Nat.le_succ _
  have hX : Fluctuation.IsDj 0 (Tstar wS)
      (d7Pull F (Tstar wS) ((Finset.univ : Finset (Torus wS.d
        (side wS (bigN wS) (Tstar wS + 1) (Tstar wS)))) : Set _)) := by
    rw [Finset.coe_univ, d7Pull_univ]
    exact Fluctuation.isDj_univ
  have hfin : d7SizeE F A (Tstar wS) Finset.univ ≠ ⊤ :=
    Fluctuation.dcovModE_ne_top_of_IsDj hX
  refine ⟨A, F, Finset.univ, rfl, ?_, d7SizePre_le_d7Size hfin,
    d7Size_le_d7SizePre_add F A hk hkK hX,
    d7Size_le_d7SizePre_add_removed F A wS_good ripeRem_thickness hk hkK hX⟩
  -- some cube becomes active
  obtain ⟨x, hx⟩ : (A.H.omegaPost (Tstar wS) \ OmegaCube A.H (Tstar wS)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at h
    exact ripeRemHistory_omegaPost_ne (Set.Subset.antisymm h
      (A.H.OmegaCube_subset_omegaPost _))
  refine Finset.card_pos.2 ⟨x, A.H.mem_newlyActive.2 ⟨Finset.mem_univ x, ?_, hx.2⟩⟩
  rcases hx.1 with h | h
  · exact absurd h hx.2
  · exact h

end Balaban.Inhabited
