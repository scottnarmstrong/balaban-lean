/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.TraceEntropy
public import Balaban.Localization.I5Inhabited

/-!
# `IsMultiDom` is inhabited (hard rule 10)

For the generating set `GP` of `Localization/I5Inhabited.lean` (`d = L = 3`, `N₁ = 6`, `K = 2`,
`Ω₁ = Ω₂ =` the whole torus) with the compatible cover `GP_covSetup`, the domain `X₁` (the polymer
domain of the empty family) is a multiscale polymer domain: `IsMultiDom (GP m₁ ϱ) 0 X₁`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Localization.I5Inhabited

theorem isMultiDom_nonempty (m₁ : ℕ) (ϱ : ℝ) :
    ∃ Y : Set (CTorus 3 3 6 m₁ 2), IsMultiDom (GP m₁ ϱ) 0 Y := by
  classical
  let c : Empty → ℕ × CTorus 3 3 6 m₁ 2 := fun e => e.elim
  refine ⟨X1 (GP m₁ ϱ) 0 1 ({0} : Set (CTorus 3 3 6 m₁ 2)), ?_⟩
  refine polymerDomain_isMultiDom c GP_covSetup (le_refl 3) (fun e => e.elim) GP_hopt ?_
  unfold polymerDomains
  refine Finset.mem_image.2 ⟨∅, ?_, ?_⟩
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  · simp [Ysites]

end Balaban.Fluctuation
