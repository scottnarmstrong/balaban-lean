/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.LayerV2Renorm

/-!
# The observable layer of the second version: comparison with the landed layer

In the complete regime of the landed class (`β_k ν_k > 1`: its running-test mass is the physical
mass, `physMass_eq_bgMass_of_lt`) the landed observable layer `IsObs` is an observable layer of the
second version on the wide domain at the complete mass:

* `Mk2_bgMass`, `Gk2_bgMass`: the objects (2.4), (2.5) of the second version at the mass `bgMass`
  are the landed `Mk`, `Gk`;
* `IsObs.toObs2`: the comparison theorem.  The statements of `LayerV2Renorm` (`IsObs2.sum_R_le`,
  `IsSFObs2.M_const_diff_le`, …) then apply to the landed layer in that regime, where they are the
  landed `sum_R_le`, `M_const_diff_le` (the latter also by `M_const_diff_le_of_mass`).

Below the switch of the landed class (`β_k ν_k ≤ 1`) there is no comparison: the landed layer is
stated on the domain of mass `0`, on which `M^{(j)}(x; e, w) = 0` for every constant `w`
(`Mobs_const_eq_zero_massFree`).
-/

@[expose] public section

namespace Balaban.Observables

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
open Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {Q : ObsConsts} {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {Ot : ObsTerms d L N₁ m₁ k N}
  {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}

/-- `M_k` of the second version at the running-test mass is the landed `M_k`. -/
theorem Mk2_bgMass (P : Consts) (β ν a : ℕ → ℝ) (Ot : ObsTerms d L N₁ m₁ k N)
    (D : BgData (topGS d L N₁ m₁ k ϱ) N) (x : CTorus d L N₁ m₁ k) :
    Mk2 P β a (Def6.bgMass L k (β k) (ν k)) Ot D x = Mk P β ν a Ot D x := by
  funext i
  simp only [Mk2, Mk, Complex.ofReal_inv]

/-- `G_k` of the second version at the running-test mass is the landed `G_k`. -/
theorem Gk2_bgMass (P : Consts) (β ν a : ℕ → ℝ) (Ot : ObsTerms d L N₁ m₁ k N)
    (Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
      Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ)
    (D : BgData (topGS d L N₁ m₁ k ϱ) N) (x x' : CTorus d L N₁ m₁ k) :
    Gk2 P β a (Def6.bgMass L k (β k) (ν k)) Ot Gker D x x' = Gk P β ν a Ot Gker D x x' := rfl

/-- **Comparison theorem for the observable layer**: in the complete regime of the landed class
(`physMass = bgMass` at `k`, e.g. `β_k ν_k > 1`), the landed observable layer `IsObs` is an
observable layer `IsObs2` of the second version on the wide domain `Ξ^c_j` at the complete mass,
for the regime `(k₀, ν)` with any a priori index `k₀`. -/
theorem IsObs.toObs2 (h : IsObs P Q β ν a Tm Ot Gker) (k₀ : ℕ)
    (hμ : physMass L k (ν k) = Def6.bgMass L k (β k) (ν k)) :
    IsObs2 P Q ⟨k₀, ν⟩ β a
      (xiFieldDom (aIdeal L k (a k)) (physMass L k (ν k)) (P.eps d L)) Tm Ot Gker := by
  have hs : (⟨k₀, ν⟩ : Regime L).sfBgMass k = Def6.bgMass L k (β k) (ν k) := hμ
  rw [hμ]
  exact
    { μ_euc := h.μ_euc
      μ_bound := h.μ_bound
      analyticM := h.analyticM
      analyticR := h.analyticR
      rotM := h.rotM
      rotR := h.rotR
      eucM := h.eucM
      eucR := h.eucR
      eucMloc := h.eucMloc
      eucRloc := h.eucRloc
      localM := h.localM
      localR := h.localR
      realM := h.realM
      realR := h.realR
      boundM := h.boundM
      boundR := h.boundR
      normM := fun j hj1 hjk x v _ hv => h.normM j hj1 hjk x v hv
      ident := fun Ψ₀ h₀ D _ hR hX => by
        rw [hs] at hX ⊢
        obtain ⟨h1, h2, h3⟩ := h.ident Ψ₀ h₀ D hR hX
        refine ⟨h1, fun u => ?_, fun u v => ?_⟩
        · rw [h2 u]
          simp only [Mk2_bgMass]
        · rw [h3 u v]
          simp only [Gk2_bgMass] }

end Balaban.Observables
