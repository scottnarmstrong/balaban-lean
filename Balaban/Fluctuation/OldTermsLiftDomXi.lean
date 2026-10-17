/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftDomBounds

/-!
# The wide chart at the next scale lies in the wide chart at the old scale

For a generating set `G` at scale `k` and its transport `liftOldGS G` to scale `k + 1`, a field pair
in `Ξᶜ_j(liftOldGS G; a, μ, 1, ε)` pulls back by `oldTorusEquiv` to a pair in `Ξᶜ_j(G; a, μ, 1, ε)`,
for a nonnegative mass `μ` and the same kernel sequence `a`.  The converse fails in general: the
clauses of the real and complex domains that carry the factor `L ^ k` are stronger at scale `k + 1`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Matrix Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

theorem liftOldGS_exists_bgData (G : GeneratingSet d L ((L * N₁) * L ^ m₁) k ϱ)
    (D' : BgData (liftOldGS G) N) :
    ∃ D : BgData G N, (∀ x, D'.Ψ (oldTorusEquiv x) = D.Ψ x) ∧
      ∀ x, D'.h (oldTorusEquiv x) = D.h x :=
  ⟨{ Ψ := fun x => D'.Ψ (oldTorusEquiv x)
     h := fun x => D'.h (oldTorusEquiv x)
     Ψ_layerConst := liftOldGS_isLayerConstant G D'.Ψ_layerConst
     h_layerConst := liftOldGS_isLayerConstant G D'.h_layerConst
     Ψ_zero := fun x hx => D'.Ψ_zero _ (fun h => hx ((liftOldGS_mem_dataSites G x).1 h))
     h_zero := fun x hx => D'.h_zero _ (fun h =>
       hx ((liftOldGS_mem_Ω_le G (by omega) x).1 h)) }, fun _ => rfl, fun _ => rfl⟩

theorem liftOldGS_xiDom (G : GeneratingSet d L ((L * N₁) * L ^ m₁) k ϱ) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) {j : ℕ} {ε : ℝ} {Ψ h : Fld d L N₁ m₁ (k + 1) N}
    (hx : XiDom (liftOldGS G) a ν j ε Ψ h) :
    XiDom G a ν j ε (lowerNewField Ψ) (lowerNewField h) := by
  obtain ⟨e, he⟩ := exists_Ω_one_equiv G
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hΨ, hh, hσ, hε, Dr', Dc', ⟨hreal, hunionR, hxib⟩, hrc, hunionC,
    hbounds⟩ := hx
  obtain ⟨Dr, hΨr, hhr⟩ := liftOldGS_exists_bgData G Dr'
  obtain ⟨Dc, hΨc, hhc⟩ := liftOldGS_exists_bgData G Dc'
  refine ⟨fun x => Ψ₀ (oldTorusEquiv x), h₀, fun x => Ψ'' (oldTorusEquiv x),
    fun x => h'' (oldTorusEquiv x), fun x i => hΨ _ i, fun x i => hh _ i, hσ, hε, Dr, Dc,
    ⟨⟨fun x hx i => ?_, fun x hx i => ?_⟩, liftOldGS_inUnionDomainR hν hΨr hhr hunionR, ?_⟩,
    ⟨fun x hx i => ?_, fun x hx i => ?_⟩, liftOldGS_inUnionDomainC hν hΨc hhc hunionC, ?_⟩
  · rw [← hΨr]; exact hreal.1 _ ((liftOldGS_mem_dataSites G x).2 hx) i
  · rw [← hhr]; exact hreal.2 _ ((liftOldGS_mem_Ω_le G (by omega) x).2 hx) i
  · exact liftOldGS_xiBounds e he hΨr
      (liftOldGS_bgField e he a ν Dr Dr' hΨr hhr) (liftOldGS_bgMult e he a ν Dr Dr' hΨr hhr) hxib
  · rw [← hΨc]; exact hrc.1 _ ((liftOldGS_mem_dataSites G x).2 hx) i
  · rw [← hhc]; exact hrc.2 _ ((liftOldGS_mem_Ω_le G (by omega) x).2 hx) i
  · exact liftOldGS_xiCBounds e he hΨr hΨc (fun _ => rfl) (fun _ => rfl)
      (liftOldGS_bgField e he a ν Dr Dr' hΨr hhr)
      (liftOldGS_bgFieldC e he a ν _ Dc Dc' hΨc hhc)
      (liftOldGS_bgMult e he a ν Dr Dr' hΨr hhr)
      (liftOldGS_bgMultC e he a ν _ Dc Dc' hΨc hhc) hbounds

end Balaban.Fluctuation
