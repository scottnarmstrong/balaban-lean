/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.V2EnergySource
public import Balaban.LargeField.Def7v2

/-!
# The clause (D1-corr) at a nonzero energy

The small-field data whose terms are the nonzero energy terms `eTerms` (nonzero on the torus
`N₁ = 1`, zero on the others), with the pair term `corr = 0`.  The thermodynamic limits of the
coefficients `v₁`, `v₂` are taken along the tori `N₁ = L^{m₀}(n+1)`, on which the energy term
vanishes for `n ≥ 1`, so the limit coefficients are zero (`eD1Corr`).
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.LargeField.Def7 Filter Topology

/-- The small-field data with the nonzero energy terms (`d = L = 3`, `N = 2`). -/
noncomputable def eSF (m₁ k : ℕ) (ϱ : ℝ) : SFData 3 3 m₁ k 2 ϱ where
  β := witnessβ
  ν := witnessν k
  z := fun _ => 1
  a := witnessa
  E := fun _ => 0
  Tm := fun N₁ _ => eTerms 3 3 N₁ m₁ k 2 ϱ (eConsts (wideα₀ k)) (witCj 3)
  Rt := fun _ _ _ _ _ _ _ => 0
  corr := fun _ _ _ _ _ _ _ => 0

theorem eD1Corr (m₁ k : ℕ) (ϱ : ℝ) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin 2)) :
    D1Corr m₀ (eSF m₁ k ϱ) (fun N₁ _ => sourceOf (eSF m₁ k ϱ).ν ((eSF m₁ k ϱ).Tm N₁)) hv
      ⟨fun _ _ => 0, fun _ _ => 0⟩ where
  src_pos := fun _ _ _ _ _ _ _ _ _ _ => rfl
  v1_lim := by
    intro j _ _ z
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : NeZero (torusSeq 3 m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
    have hne := torusSeq_ne_one (L := 3) m₀ n hn
    symm
    unfold v1T
    refine finsum_mem_eq_zero_of_forall_eq_zero fun X _ => ?_
    have hE : (sourceOf (eSF m₁ k ϱ).ν ((eSF m₁ k ϱ).Tm (torusSeq 3 m₀ n))).E j
        0 X = fun _ _ => 0 := by
      funext Ψ b
      show (eTerms 3 3 (torusSeq 3 m₀ n) m₁ k 2 ϱ (eConsts (wideα₀ k)) (witCj 3)).E j 0 X Ψ _ = 0
      rw [E_eTerms]
      exact ite_eq_right_iff.2 (fun h => absurd h.1 hne)
    rw [hE]
    exact v1Loc_zero _ _ _ _
  v2_lim := by
    intro j _ _ e₂ _ _ z
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : NeZero (torusSeq 3 m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
    have hne := torusSeq_ne_one (L := 3) m₀ n hn
    symm
    unfold v2T
    refine finsum_mem_eq_zero_of_forall_eq_zero fun X _ => ?_
    have hE : (sourceOf (eSF m₁ k ϱ).ν ((eSF m₁ k ϱ).Tm (torusSeq 3 m₀ n))).E j
        0 X = fun _ _ => 0 := by
      funext Ψ b
      show (eTerms 3 3 (torusSeq 3 m₀ n) m₁ k 2 ϱ (eConsts (wideα₀ k)) (witCj 3)).E j 0 X Ψ _ = 0
      rw [E_eTerms]
      exact ite_eq_right_iff.2 (fun h => absurd h.1 hne)
    rw [hE]
    exact v2Loc_zero _ _ _ _ _
  corr_eq := by
    intro N₁ _ j _ _ y x ψ _ _
    show (0 : ℂ) = _
    simp [corrPair]

end Balaban.LargeField.Def7v2
