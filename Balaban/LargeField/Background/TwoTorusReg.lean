/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusRegField

/-!
# The regularity predicate of two agreeing generating sets

`GenAgree.reg_iff`: for generating sets `G₁`, `G₂` and data `D₁`, `D₂` that agree on the box, and
finite sets of sites `T`, `S` that correspond, `Reg_q(G₁, D₁, δ; T₁, S₁)` iff
`Reg_q(G₂, D₂, δ; T₂, S₂)` (Definition II.3.1). The same holds for the mixed inequalities
`RegMixedIneq` of Definition II.3.2 item 3 (`GenAgree.regMixedIneq_iff`) and the domain conjunct
(`GenAgree.inUnionDomainR_iff`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField

section Quant

variable {d m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂] {c : Fin d → ℤ}

theorem forall_setCorr {T₁ : Set (Torus d m₁)} {T₂ : Set (Torus d m₂)} (hT : SetCorr c T₁ T₂)
    {P₁ : Torus d m₁ → Prop} {P₂ : Torus d m₂ → Prop}
    (hP : ∀ x₁ x₂, PtCorr c x₁ x₂ → (P₁ x₁ ↔ P₂ x₂)) :
    (∀ x ∈ T₁, P₁ x) ↔ ∀ x ∈ T₂, P₂ x := by
  constructor
  · intro h x₂ hx₂
    have hp := ptCorr_transp (m₁ := m₂) (m₂ := m₁) (x := x₂) (hT.2.1 x₂ hx₂).symm
    have hp' := ptCorr_symm hp
    exact (hP _ _ hp').1 (h _ ((hT.2.2 _ _ hp'.1).2 hx₂))
  · intro h x₁ hx₁
    have hp := ptCorr_transp (m₁ := m₁) (m₂ := m₂) (x := x₁) (hT.1 x₁ hx₁)
    exact (hP _ _ hp).2 (h _ ((hT.2.2 _ _ hp.1).1 hx₁))

end Quant

section Ineq

variable {d L N₁ N₂ k Nv : ℕ} [NeZero N₁] [NeZero N₂] [NeZero L] {ϱ₁ ϱ₂ : ℝ}
  {G₁ : GeneratingSet d L N₁ k ϱ₁} {G₂ : GeneratingSet d L N₂ k ϱ₂} {c : Fin d → ℤ}
  {D₁ : BgData G₁ Nv} {D₂ : BgData G₂ Nv}

theorem forall_omega_setCorr (hA : GenAgree G₁ G₂ c) {S₁ : Set (Torus d (N₁ * L ^ k))}
    {S₂ : Set (Torus d (N₂ * L ^ k))} (hS : SetCorr c S₁ S₂) {P₁ : G₁.Ω 1 → Prop}
    {P₂ : G₂.Ω 1 → Prop} (hP : ∀ y₁ y₂, PtCorr c y₁.1 y₂.1 → (P₁ y₁ ↔ P₂ y₂)) :
    (∀ x : G₁.Ω 1, x.1 ∈ S₁ → P₁ x) ↔ ∀ y : G₂.Ω 1, y.1 ∈ S₂ → P₂ y := by
  constructor
  · intro h y hy
    have hb := (hA.symm.supp₁ y.1 y.2).inBox
    have hp := ptCorr_symm (ptCorr_transp (m₂ := N₁ * L ^ k) hb)
    have hx : transp (N₁ * L ^ k) c y.1 ∈ G₁.Ω 1 := (hA.omega_iff le_rfl (Nat.le_add_left 1 k) hp).2 y.2
    exact (hP ⟨_, hx⟩ y hp).1 (h ⟨_, hx⟩ ((hS.2.2 _ _ hp.1).2 hy))
  · intro h x hx
    have hb := (hA.supp₁ x.1 x.2).inBox
    have hp := ptCorr_transp (m₂ := N₂ * L ^ k) hb
    have hy : transp (N₂ * L ^ k) c x.1 ∈ G₂.Ω 1 := (hA.omega_iff le_rfl (Nat.le_add_left 1 k) hp).1 x.2
    exact (hP x ⟨_, hy⟩ hp).2 (h ⟨_, hy⟩ ((hS.2.2 _ _ hp.1).1 hx))

variable (hA : GenAgree G₁ G₂ c) (hD : DataAgree G₁ G₂ c D₁ D₂) (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂)
  (a : ℕ → ℝ) (ν c₀ : ℝ)

include hA hD hN₁ hN₂ in
theorem GenAgree.blockDev_ptCorr {x₁ : Torus d (N₁ * L ^ k)} {x₂ : Torus d (N₂ * L ^ k)}
    (hp : PtCorr c x₁ x₂) :
    blockDev G₂ D₂ (bgFieldC G₂ a ν c₀ D₂) x₂ = blockDev G₁ D₁ (bgFieldC G₁ a ν c₀ D₁) x₁ := by
  unfold blockDev
  congr 1
  funext i
  rw [hD.psi_ptCorr hA hp i, congrFun (hA.blockAvg_ptCorr hN₁ hN₂
    (fun y₁ y₂ hq i => hA.bgFieldC_ptCorr hD hN₁ hN₂ a ν c₀ hq i) hp) i]

include hA hD hN₁ hN₂ in
theorem GenAgree.blockClose_iff {T₁ : Finset (Torus d (N₁ * L ^ k))}
    {T₂ : Finset (Torus d (N₂ * L ^ k))} (hT : SetCorr c (T₁ : Set (Torus d (N₁ * L ^ k))) (T₂ : Set (Torus d (N₂ * L ^ k)))) (δ : ℝ) :
    BlockClose G₁ D₁ (bgFieldC G₁ a ν c₀ D₁) T₁ δ ↔ BlockClose G₂ D₂ (bgFieldC G₂ a ν c₀ D₂) T₂ δ := by
  unfold BlockClose
  have := forall_setCorr (P₁ := fun x => blockDev G₁ D₁ (bgFieldC G₁ a ν c₀ D₁) x < δ)
    (P₂ := fun x => blockDev G₂ D₂ (bgFieldC G₂ a ν c₀ D₂) x < δ) hT (fun x₁ x₂ hp => by
      rw [hA.blockDev_ptCorr hD hN₁ hN₂ a ν c₀ hp])
  simpa using this

include hA hD hN₁ hN₂ in
theorem GenAgree.barLap_ptCorr {x₁ : Torus d (N₁ * L ^ k)} {x₂ : Torus d (N₂ * L ^ k)}
    (hp : PtCorr c x₁ x₂) (hm : InBoxK 1 (N₁ * L ^ k) (N₂ * L ^ k) c (liftNear c x₁)) :
    barLap G₂ D₂ (bgFieldC G₂ a ν c₀ D₂) x₂ = barLap G₁ D₁ (bgFieldC G₁ a ν c₀ D₁) x₁ := by
  unfold barLap
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [hA.barVec_ptCorr hD hN₁ hN₂ a ν c₀ (ptCorr_add_single hp hm μ),
    hA.barVec_ptCorr hD hN₁ hN₂ a ν c₀ (ptCorr_sub_single hp hm μ),
    hA.barVec_ptCorr hD hN₁ hN₂ a ν c₀ hp]

include hA hD hN₁ hN₂ in
theorem GenAgree.gradClose_iff {S₁ : Finset (Torus d (N₁ * L ^ k))}
    {S₂ : Finset (Torus d (N₂ * L ^ k))} (hS : SetCorr c (S₁ : Set (Torus d (N₁ * L ^ k))) (S₂ : Set (Torus d (N₂ * L ^ k)))) (ℓ δ : ℝ) :
    GradClose G₁ D₁ (bgFieldC G₁ a ν c₀ D₁) (bgMultC G₁ a ν c₀ D₁) ℓ S₁ δ ↔
      GradClose G₂ D₂ (bgFieldC G₂ a ν c₀ D₂) (bgMultC G₂ a ν c₀ D₂) ℓ S₂ δ := by
  unfold GradClose
  refine forall_omega_setCorr hA hS fun y₁ y₂ hp => ?_
  have hm : InBoxK 1 (N₁ * L ^ k) (N₂ * L ^ k) c (liftNear c y₁.1) :=
    (hA.supp₁ y₁.1 y₁.2).mono (by omega)
  rw [hA.barLap_ptCorr hD hN₁ hN₂ a ν c₀ hp hm, hA.bgMultC_ptCorr hD hN₁ hN₂ a ν c₀ hp]
  simp only [hA.barVec_ptCorr hD hN₁ hN₂ a ν c₀ (ptCorr_add_single hp hm _),
    hA.barVec_ptCorr hD hN₁ hN₂ a ν c₀ (ptCorr_sub_single hp hm _),
    hA.barVec_ptCorr hD hN₁ hN₂ a ν c₀ hp]

include hA hD hN₁ hN₂ in
theorem GenAgree.fieldClose_iff {S₁ : Finset (Torus d (N₁ * L ^ k))}
    {S₂ : Finset (Torus d (N₂ * L ^ k))} (hS : SetCorr c (S₁ : Set (Torus d (N₁ * L ^ k))) (S₂ : Set (Torus d (N₂ * L ^ k)))) (ν' δ : ℝ) :
    FieldClose G₁ D₁ (bgFieldC G₁ a ν c₀ D₁) ν' S₁ δ ↔
      FieldClose G₂ D₂ (bgFieldC G₂ a ν c₀ D₂) ν' S₂ δ := by
  unfold FieldClose
  refine imp_congr_right fun _ => forall_omega_setCorr hA hS fun y₁ y₂ hp => ?_
  simp only [hA.bgFieldC_ptCorr hD hN₁ hN₂ a ν c₀ hp, hD.h_ptCorr hA hp]

include hA hD hN₁ hN₂ in
theorem GenAgree.regIneq_iff {T₁ S₁ : Finset (Torus d (N₁ * L ^ k))}
    {T₂ S₂ : Finset (Torus d (N₂ * L ^ k))} (hT : SetCorr c (T₁ : Set (Torus d (N₁ * L ^ k))) (T₂ : Set (Torus d (N₂ * L ^ k))))
    (hS : SetCorr c (S₁ : Set (Torus d (N₁ * L ^ k))) (S₂ : Set (Torus d (N₂ * L ^ k)))) (μ δ : ℝ) :
    RegIneq G₁ a μ D₁ δ T₁ S₁ ↔ RegIneq G₂ a μ D₂ δ T₂ S₂ := by
  unfold RegIneq
  rw [hA.blockClose_iff hD hN₁ hN₂ a μ (bgC0 d L Nv) hT, hA.gradClose_iff hD hN₁ hN₂ a μ
    (bgC0 d L Nv) hS, hA.fieldClose_iff hD hN₁ hN₂ a μ (bgC0 d L Nv) hS]

include hA hD hN₁ hN₂ in
/-- **Transport of the regularity predicate** `Reg_q(G, D, δ; T, S)` between two tori. -/
theorem GenAgree.reg_iff {T₁ S₁ : Finset (Torus d (N₁ * L ^ k))}
    {T₂ S₂ : Finset (Torus d (N₂ * L ^ k))} (hT : SetCorr c (T₁ : Set (Torus d (N₁ * L ^ k))) (T₂ : Set (Torus d (N₂ * L ^ k))))
    (hS : SetCorr c (S₁ : Set (Torus d (N₁ * L ^ k))) (S₂ : Set (Torus d (N₂ * L ^ k)))) (μ δ : ℝ) :
    Reg G₁ a μ D₁ δ T₁ S₁ ↔ Reg G₂ a μ D₂ δ T₂ S₂ := by
  unfold Reg
  rw [hA.inUnionDomainR_iff hN₁ hN₂ hD, hA.regIneq_iff hD hN₁ hN₂ a hT hS]

include hA hD hN₁ hN₂ in
theorem GenAgree.regMixedIneq_iff {Tf₁ Tn₁ S₁ : Finset (Torus d (N₁ * L ^ k))}
    {Tf₂ Tn₂ S₂ : Finset (Torus d (N₂ * L ^ k))} (hTf : SetCorr c (Tf₁ : Set (Torus d (N₁ * L ^ k))) (Tf₂ : Set (Torus d (N₂ * L ^ k))))
    (hTn : SetCorr c (Tn₁ : Set (Torus d (N₁ * L ^ k))) (Tn₂ : Set (Torus d (N₂ * L ^ k)))) (hS : SetCorr c (S₁ : Set (Torus d (N₁ * L ^ k))) (S₂ : Set (Torus d (N₂ * L ^ k))))
    (μ ℓ νk δ : ℝ) :
    RegMixedIneq G₁ a μ D₁ ℓ νk δ Tf₁ Tn₁ S₁ ↔ RegMixedIneq G₂ a μ D₂ ℓ νk δ Tf₂ Tn₂ S₂ := by
  unfold RegMixedIneq
  rw [hA.blockClose_iff hD hN₁ hN₂ a μ (bgC0 d L Nv) hTf, hA.blockClose_iff hD hN₁ hN₂ a μ
    (bgC0 d L Nv) hTn, hA.gradClose_iff hD hN₁ hN₂ a μ (bgC0 d L Nv) hS,
    hA.fieldClose_iff hD hN₁ hN₂ a μ (bgC0 d L Nv) hS]

end Ineq

end Balaban.RootFSpine
