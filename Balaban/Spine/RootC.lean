/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RootF
public import Balaban.Correlations.RootCFromFlow

/-!
# Root-C from the spine

The consumer `rootC_of_rootFAndC1Star` (`Correlations/RootCFromFlow.lean`) derives Root-C
(`RootCStatement`, definitionally the type of the frozen `Balaban.lowTemperature_correlations`) from
`RootFAndC1Star d N hN`: Root-F's clauses at `κ = κ_* = kappaStar d`, `c₉ = 1` with `L ≥ 3`,
together with the interface `C1Star d N L M hN` for the same `L, M`. Beyond the inputs of the Root-F
spine, it needs exactly two more: `3 ≤ L` at `(κ_*, 1)` (LFR row 3) and an inhabitant of `C1Star`
(the observable layer, LFR Theorem IV.5.4: OBS Theorems 3.1, 5.2, Proposition IV.4.4 and the
continuity in `ν` of LF-7 (e)). -/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Correlations Balaban.LargeField Balaban.LargeField.Def7

/-- **`RootFAndC1Star` from the spine**: the inputs of `rootF_of_spine`, `3 ≤ L` at `(κ_*, 1)` and
the interface `C1Star` for `L, M` of the prefix at `(κ_*, 1)`. -/
theorem rootFAndC1Star_of_spine (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N) (δ : ℝ) (hδ : 0 < δ)
    (Ty : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → SmallField.Def6.Consts) (C7 : ℝ → ℝ → Consts7)
    (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts) (M1 c : ℝ → ℝ → ℕ)
    (rH ϱ : ℝ → ℝ → ℝ)
    (hA1 : PrefixInput Ty P6)
    (hA3 : BaseStepInput d N Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA4 : ClassStepInput d N Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA4t : TransferInput d N Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA4f : FrozenStepInput d N Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA6 : LastIntegralInput d N δ Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA7 : KfZeroInput d N δ Ty)
    (hL3 : 3 ≤ (Ty (kappaStar d) 1).L)
    (hC1 : Nonempty (@C1Star d N (Ty (kappaStar d) 1).L (Ty (kappaStar d) 1).M ⟨by omega⟩ hN)) :
    RootFAndC1Star d N hN := by
  have hκ : 0 < kappaStar d := kappaStar_pos (by omega)
  obtain ⟨-, hM1, -⟩ := hA1 (kappaStar d) hκ 1 one_pos
  obtain ⟨β₀, hβ₀⟩ := rootF_clauses_of_spine d N hd hN δ Ty P6 C7 PB cs₀ M1 c rH ϱ hA1 hA3 hA4
    hA4t hA4f hA6 hA7 (kappaStar d) hκ 1 one_pos
  exact ⟨δ, hδ, (Ty (kappaStar d) 1).L, (Ty (kappaStar d) 1).M, hL3, hM1, β₀, hβ₀, hC1⟩

/-- **Root-C from the spine** (`rootC_of_rootFAndC1Star` applied to `rootFAndC1Star_of_spine`). -/
theorem rootC_of_spine (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N) (δ : ℝ) (hδ : 0 < δ)
    (Ty : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → SmallField.Def6.Consts) (C7 : ℝ → ℝ → Consts7)
    (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts) (M1 c : ℝ → ℝ → ℕ)
    (rH ϱ : ℝ → ℝ → ℝ)
    (hA1 : PrefixInput Ty P6)
    (hA3 : BaseStepInput d N Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA4 : ClassStepInput d N Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA4t : TransferInput d N Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA4f : FrozenStepInput d N Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA6 : LastIntegralInput d N δ Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA7 : KfZeroInput d N δ Ty)
    (hL3 : 3 ≤ (Ty (kappaStar d) 1).L)
    (hC1 : Nonempty (@C1Star d N (Ty (kappaStar d) 1).L (Ty (kappaStar d) 1).M ⟨by omega⟩ hN)) :
    RootCStatement d N :=
  rootC_of_rootFAndC1Star d N hd hN (rootFAndC1Star_of_spine d N hd hN δ hδ Ty P6 C7 PB cs₀ M1 c
    rH ϱ hA1 hA3 hA4 hA4t hA4f hA6 hA7 hL3 hC1)

end Balaban.RootFSpine
