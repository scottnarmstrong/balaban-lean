module

public import Balaban.LargeField.Background.Lift
public import Balaban.Background.EquivarianceLat

/-!
# Lattice-symmetry covariance of the lifted data

For a lattice symmetry `S : LatSymm G G' σ` and block permutations `β` induced by `σ` on the
blocks of the lifted scales, the transported single-scale lift `S.sym (liftSingle G ψ h)` is
`liftSingle G' ψ' h` when `ψ' ∘ β = ψ` (`liftSingle_sym`), and likewise for the mixed lift
(`liftMixed_sym`, with the block union `Ω` transported to `Ω' = σ Ω`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

set_option linter.unusedSectionVars false

section LiftSymm

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G G' : GeneratingSet d L N₀ k ϱ} {σ : Equiv.Perm (Torus d (N₀ * L ^ k))}
  (S : LatSymm G G' σ)

include S

/-- **Lattice covariance of the single-scale lift**: if the block permutation `β` of the `k`-blocks
is induced by `σ` and `ψ' ∘ β = ψ`, the transported lift is the lift of `ψ'`. -/
theorem _root_.Balaban.Background.LatSymm.liftSingle_sym
    (β : Equiv.Perm (Torus d (N₀ * L ^ (k - k))))
    (hβ : ∀ x, jBlock d L N₀ k k (σ x) = β (jBlock d L N₀ k k x))
    (ψ ψ' : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) (hψ : ∀ y, ψ' (β y) = ψ y)
    (h : Fin N → ℂ) :
    S.sym (liftSingle G ψ h) = liftSingle G' ψ' h := by
  classical
  refine Balaban.Background.BgData.ext' (funext fun y => ?_) (funext fun y => ?_)
  · obtain ⟨x, rfl⟩ := σ.surjective y
    simp only [Balaban.Background.LatSymm.sym, Equiv.symm_apply_apply, liftSingle, BgData.clip,
      S.mem_dataSites, blockLift, hβ, hψ]
  · obtain ⟨x, rfl⟩ := σ.surjective y
    simp only [Balaban.Background.LatSymm.sym, Equiv.symm_apply_apply, liftSingle, BgData.clip,
      S.mem_Ω1]


end LiftSymm

section LiftMixedSymm

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G G' : GeneratingSet d L N₀ (k + 1) ϱ} {σ : Equiv.Perm (Torus d (N₀ * L ^ (k + 1)))}
  (S : LatSymm G G' σ)

include S

/-- **Lattice covariance of the mixed lift**. -/
theorem _root_.Balaban.Background.LatSymm.liftMixed_sym
    {Ω : Finset (Torus d (N₀ * L ^ (k + 1)))} (hΩ : IsBlockUnion L N₀ (k + 1) (k + 1) Ω)
    (hG : G.Ω (k + 1) ⊆ Ω)
    {Ω' : Finset (Torus d (N₀ * L ^ (k + 1)))} (hΩ' : IsBlockUnion L N₀ (k + 1) (k + 1) Ω')
    (hG' : G'.Ω (k + 1) ⊆ Ω') (hΩΩ : ∀ x, σ x ∈ Ω' ↔ x ∈ Ω)
    (βk : Equiv.Perm (Torus d (N₀ * L ^ (k + 1 - k))))
    (βk1 : Equiv.Perm (Torus d (N₀ * L ^ (k + 1 - (k + 1)))))
    (hβk : ∀ x, jBlock d L N₀ (k + 1) k (σ x) = βk (jBlock d L N₀ (k + 1) k x))
    (hβk1 : ∀ x, jBlock d L N₀ (k + 1) (k + 1) (σ x) = βk1 (jBlock d L N₀ (k + 1) (k + 1) x))
    (ψ ψ' : Torus d (N₀ * L ^ (k + 1 - k)) → Fin N → ℂ) (hψ : ∀ y, ψ' (βk y) = ψ y)
    (ϑ ϑ' : Torus d (N₀ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (hϑ : ∀ y, ϑ' (βk1 y) = ϑ y)
    (h : Fin N → ℂ) :
    S.sym (liftMixed G hΩ hG ψ ϑ h) = liftMixed G' hΩ' hG' ψ' ϑ' h := by
  classical
  refine Balaban.Background.BgData.ext' (funext fun y => ?_) (funext fun y => ?_)
  · obtain ⟨x, rfl⟩ := σ.surjective y
    simp only [Balaban.Background.LatSymm.sym, Equiv.symm_apply_apply, liftMixed, BgData.clip,
      S.mem_dataSites, mixedLift, hΩΩ, blockLift, hβk, hβk1, hψ, hϑ]
  · obtain ⟨x, rfl⟩ := σ.surjective y
    simp only [Balaban.Background.LatSymm.sym, Equiv.symm_apply_apply, liftMixed, BgData.clip,
      S.mem_Ω1]

end LiftMixedSymm
end Balaban.LargeField
