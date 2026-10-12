module

public import Balaban.LargeField.Operators.Ancestors
public import Balaban.LargeField.Region.Generating
public import Balaban.LargeField.Characteristic.Analytic

/-!
# The generating set of a localized history

A region history without removals (the lineage localization `locRH`, whose `rem` is empty) is a
`RegionSeq` (`RegionHistory.toSeq`), so Lemma I.3.10 (`flowGeneratingSet`) gives its generating
set `𝔹_K` (layers `Ω_1 ⊇ ⋯ ⊇ Ω_K` of the history).  `GeneratingSet.castSites` transports a
generating set along an equality of the numbers `N₀` of coarsest blocks (the level-`q` tori of the
characteristic functions are `Torus d (M₁ (c n_q) L^q)`, those of the history
`Torus d (M n_K L^K)` with `M = c M₁`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  (H : RegionHistory S n R k0)

/-- A region history without removals is a region sequence (Lemma I.3.10's input). -/
noncomputable def toSeq (hrem : ∀ k, H.rem k = ∅) :
    RegionSeq S.d S.L n S.Rb S.lam R (critOpt S k0) where
  hnn := H.F.hnn
  step := H.F.step
  Z_zero := by
    have h := H.Z_eq 0
    rw [hrem 0] at h
    simpa [FlowSteps.Zpre] using h
  Z_succ := fun i => by
    have h := H.Z_eq (i + 1)
    rw [hrem (i + 1)] at h
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.sdiff_empty] at h
    rw [h]
    simp only [FlowSteps.Zpre, Setting.omega_eq_omegaW]

variable {M : ℕ} [NeZero M] [NeZero S.L]

/-- The generating set `𝔹_K` of a region history without removals (Lemma I.3.10). -/
noncomputable def histGen (hrem : ∀ k, H.rem k = ∅) (hL : 2 ≤ S.L) (K : ℕ)
    (hR : ∀ j, 1 ≤ j → j < K → S.Rb ≤ R j) :
    Multiscale.GeneratingSet S.d S.L (M * n K) K ((S.L : ℝ) * M * S.Rb) :=
  flowGeneratingSet M (H.toSeq hrem) hL K hR

theorem mem_histGen (hrem : ∀ k, H.rem k = ∅) (hL : 2 ≤ S.L) (K : ℕ)
    (hR : ∀ j, 1 ≤ j → j < K → S.Rb ≤ R j) (j : ℕ) (x : Torus S.d (M * n K * S.L ^ K)) :
    x ∈ (H.histGen (M := M) hrem hL K hR).Ω j ↔
      j ≤ K ∧ cubeMap n S.L M K j x ∈ (H.toSeq hrem).OmegaAt j :=
  mem_flowOmega M (H.toSeq hrem)

end RegionHistory

/-- Transport of a generating set along an equality of the numbers of coarsest blocks. -/
noncomputable def castGen {d L k : ℕ} {ϱ : ℝ} {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] [NeZero L]
    (h : N₀ = N₀') (G : Multiscale.GeneratingSet d L N₀ k ϱ) :
    Multiscale.GeneratingSet d L N₀' k ϱ := h ▸ G

theorem mem_castGen {d L k : ℕ} {ϱ : ℝ} {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] [NeZero L]
    (h : N₀ = N₀') (G : Multiscale.GeneratingSet d L N₀ k ϱ) (j : ℕ)
    (x : Torus d (N₀' * L ^ k)) :
    x ∈ (castGen h G).Ω j ↔
      torusCast (congrArg (· * L ^ k) h.symm) x ∈ G.Ω j := by
  subst h
  rfl

end Balaban.LargeField
