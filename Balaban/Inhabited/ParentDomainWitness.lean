/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.SFCtxMulti
public import Balaban.LargeField.History.ParentDomain
import Balaban.LargeField.History.InhabitedJoint

/-!
# Non-vacuity of `inDomainR_genW_of_factors`

On the multi-cube small-field context `ctxMulti` (`d = L = 3`, `N = 2`, scale `k = 1`), with the
region history without large-field cubes (`Z^pre_k = Z_k = ∅` for all `k`, so `Y = Z_kᶜ` is the
whole torus), with `ψ_1` the constant unit field, `h⋆ = ψ_1`, mass `ν = 0` and `η_Y = 1`:
all hypotheses of `inDomainR_genW_of_factors` hold.  `hAct` is vacuous (there is no retained
component), `hR2Y` and `hR1Y` hold since `Ψ` is a constant unit vector, `hmass` holds since `ν = 0`
(any `ν` with `2 ν 3² < η²` works).  Hence the datum lies in the real domain.  This tests only
the clauses over `Y`; no landed `SFCtx` has a retained component (the witness of
`TopBlockTransportWitness` is cube-level).  Whether `χ_1(Y) ≠ 0` at the constant field is not
decided here: the assembly takes no hypothesis on `chiY`, its content enters through `hR1Y`,
`hR2Y`.
-/

@[expose] public section

namespace Balaban.LargeField.Def7

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.LargeField.Def7.Wit
  RegionHistory

/-- The flow steps without large-field cubes on the torus of `ctxMulti`. -/
noncomputable def emptyFlow : FlowSteps wS (sides wS.L 1 nMulti) wR 0 1 where
  ok := wS_ok
  s4 := le_rfl
  s5 := le_rfl
  RH := wRH
  hnn := fun k hk => sides_hnn wS.L 1 nMulti k hk
  step := fun k => RegionHistory.emptyStep wS (sides wS.L 1 nMulti) wR k ∅

theorem emptyFlow_Zpre (k : ℕ) : emptyFlow.Zpre k = ∅ := by
  cases k with
  | zero => rfl
  | succ k => exact JointWitness.emptyStep_Zpre_empty wS (sides wS.L 1 nMulti) wR k (wS.omega (k + 1)) (critOpt wS 0 (k + 1))

/-- The region history without large-field cubes on the torus of `ctxMulti`. -/
noncomputable def emptyHist : RegionHistory wS (sides wS.L 1 nMulti) wR 0 1 where
  F := emptyFlow
  rem := fun _ => ∅
  rem_sub := fun _ => Finset.empty_subset _
  rem_empty := fun _ _ => rfl
  Z_eq := fun k => by
    rw [emptyFlow_Zpre]
    simp [emptyFlow, RegionHistory.emptyStep]

/-- **Non-vacuity.**  In the multi-cube context, with the history without large-field cubes, the
constant unit field `ψ_1`, `h⋆ = ψ_1`, `ν = 0` and `η_Y = 1`, the datum lies in the real domain
(all hypotheses of `inDomainR_genW_of_factors` hold). -/
theorem parentDomain_witness :
    InDomainR (ctxMulti.genW ((emptyHist.step (0 + 1)).Z)ᶜ) 0
      (max (3 * wS.d * wS.L * ctxMulti.cs.delta 0) 1)
      (liftSingle (ctxMulti.genW ((emptyHist.step (0 + 1)).Z)ᶜ)
        (ctxMulti.liftData (fun _ => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))
        (hC (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))) := by
  have hpsi : ∀ s, parentPsi ctxMulti (fun _ => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) s =
      fun i => (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) i := fun s => rfl
  have hsum : ∑ i : Fin 2, ((EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) i) ^ 2 = 1 := by
    simp
  refine inDomainR_genW_of_factors emptyHist ctxMulti
    (fun _ => EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
    (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 0 1 le_rfl (by simp) one_pos ?_ ?_ ?_ ?_
  · have h1 : (1 : ℝ) ≤ max (3 * wS.d * wS.L * ctxMulti.cs.delta 0) 1 := le_max_right _ _
    nlinarith
  · intro C hC ⟨t, ht, hq⟩
    exfalso
    have h := comp_subset C.2 hq
    rw [mem_finOf] at h
    exact (emptyFlow_Zpre 1 ▸ h : _)
  · intro s hs hY
    rw [hpsi, hsum]
    simp
  · intro s s' hp h1 h2
    rw [hpsi, hpsi]
    simp [rn]

end Balaban.LargeField.Def7
