/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftDomBg
public import Balaban.SmallField.Xi

/-!
# The inequalities of the wide chart on a transported generating set

The real and complex inequalities of `Ξ_n` and `Ξᶜ_n` on `liftOldGS G` imply those on `G`, for the
fields and background solutions relabeled by `oldTorusEquiv`.  The two clauses that involve the
scale index `k` (the norm of the constant `h₀` and the union-domain inequality) carry `L ^ (k + 1)`
on the new side and `L ^ k` on the old side; they pass from the new to the old side for a
nonnegative mass, so only this inclusion holds.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Matrix Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

section
variable {G : GeneratingSet d L ((L * N₁) * L ^ m₁) k ϱ}
  (e : G.Ω 1 ≃ (liftOldGS G).Ω 1)
  (he : ∀ x, (e x : CTorus d L N₁ m₁ (k + 1)) = oldTorusEquiv x)

include he

theorem liftOldGS_xiBounds {ν σ ε : ℝ} {n : ℕ} {D : BgData G N} {D' : BgData (liftOldGS G) N}
    (hΨ : ∀ x, D'.Ψ (oldTorusEquiv x) = D.Ψ x) {h₀ : Fin N → ℝ}
    {φ : G.Ω 1 × Fin N → ℂ} {φ' : (liftOldGS G).Ω 1 × Fin N → ℂ}
    (hφ : ∀ x i, φ' (e x, i) = φ (x, i)) {α : G.Ω 1 → ℂ} {α' : (liftOldGS G).Ω 1 → ℂ}
    (hα : ∀ x, α' (e x) = α x)
    (h : XiBounds (liftOldGS G) ν n σ ε D' h₀ φ' α') : XiBounds G ν n σ ε D h₀ φ α := by
  have hmem : ∀ x ∈ G.Ω 1, oldTorusEquiv x ∈ (liftOldGS G).Ω 1 := fun x hx =>
    (liftOldGS_mem_Ω_le G (by omega) x).2 hx
  refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x => ?_, fun x hx => ?_, fun z hz z' hz' hadj => ?_,
    fun z => ?_, ?_⟩
  · have := h.grad _ (hmem x hx) μ
    simpa only [← oldTorusEquiv_single, ← oldTorusEquiv_add, ← oldTorusEquiv_sub,
      liftOldGS_barField e he hΨ hφ, liftOldGS_spacing] using this
  · have := h.lap _ (hmem x hx)
    simpa only [← oldTorusEquiv_single, ← oldTorusEquiv_add, ← oldTorusEquiv_sub,
      liftOldGS_barField e he hΨ hφ, liftOldGS_spacing] using this
  · simpa only [he, liftOldGS_spacing, hα] using h.mult (e x)
  · simpa only [liftOldGS_blockAvg e he hφ, hΨ] using h.close _ (hmem x hx)
  · have := h.collarBond (oldTorusEquiv z) ((liftOldGS_mem_collar G z).2 hz)
      (oldTorusEquiv z') ((liftOldGS_mem_collar G z').2 hz') ((oldTorusEquiv_adj_iff z z').2 hadj)
    simpa only [hΨ] using this
  · simpa only [he, liftOldGS_spacing, hφ] using h.mass (e z)
  · exact h.hnorm

theorem liftOldGS_xiCBounds {ν σ ε : ℝ} {Dr Dc : BgData G N} {Dr' Dc' : BgData (liftOldGS G) N}
    (hΨr : ∀ x, Dr'.Ψ (oldTorusEquiv x) = Dr.Ψ x) (hΨc : ∀ x, Dc'.Ψ (oldTorusEquiv x) = Dc.Ψ x)
    {Ψ'' h'' : CTorus d L (L * N₁) m₁ k → Fin N → ℂ}
    {Ψ3 h3 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    (hΨ'' : ∀ x, Ψ3 (oldTorusEquiv x) = Ψ'' x) (hh'' : ∀ x, h3 (oldTorusEquiv x) = h'' x)
    {φr φc : G.Ω 1 × Fin N → ℂ} {φr' φc' : (liftOldGS G).Ω 1 × Fin N → ℂ}
    (hφr : ∀ x i, φr' (e x, i) = φr (x, i)) (hφc : ∀ x i, φc' (e x, i) = φc (x, i))
    {αr αc : G.Ω 1 → ℂ} {αr' αc' : (liftOldGS G).Ω 1 → ℂ}
    (hαr : ∀ x, αr' (e x) = αr x) (hαc : ∀ x, αc' (e x) = αc x)
    (h : XiCBounds (liftOldGS G) ν σ ε Dr' Dc' Ψ3 h3 φr' φc' αr' αc') :
    XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc := by
  have hmem : ∀ x ∈ G.Ω 1, oldTorusEquiv x ∈ (liftOldGS G).Ω 1 := fun x hx =>
    (liftOldGS_mem_Ω_le G (by omega) x).2 hx
  refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x => ?_, fun x => ?_, fun x hx => ?_,
    fun z hz z' hz' hadj => ?_, fun x hx => ?_, fun x => ?_⟩
  · have := h.grad _ (hmem x hx) μ
    simpa only [← oldTorusEquiv_single, ← oldTorusEquiv_add, ← oldTorusEquiv_sub,
      liftOldGS_barField e he hΨr hφr, liftOldGS_barField e he hΨc hφc,
      liftOldGS_spacing] using this
  · have := h.lap _ (hmem x hx)
    simpa only [← oldTorusEquiv_single, ← oldTorusEquiv_add, ← oldTorusEquiv_sub,
      liftOldGS_barField e he hΨr hφr, liftOldGS_barField e he hΨc hφc,
      liftOldGS_spacing] using this
  · simpa only [he, liftOldGS_spacing, hαr, hαc] using h.mult (e x)
  · simpa only [hφr, hφc] using h.val (e x)
  · simpa only [liftOldGS_blockAvg e he (φ := φc - φr) (φ' := φc' - φr')
        (fun x i => by simp only [Pi.sub_apply, hφc, hφr]),
      hΨ''] using h.close _ (hmem x hx)
  · have := h.collarBond (oldTorusEquiv z) ((liftOldGS_mem_collar G z).2 hz)
      (oldTorusEquiv z') ((liftOldGS_mem_collar G z').2 hz') ((oldTorusEquiv_adj_iff z z').2 hadj)
    simpa only [hΨ''] using this
  · simpa only [liftOldGS_layerIndex_all, hh''] using h.hAbs _ (hmem x hx)
  · simpa only [he, liftOldGS_layerIndex_all, hh'', hφr] using h.hDot (e x)

omit he in
theorem pow_sq_le_succ (ν : ℝ) (hν : 0 ≤ ν) (A : ℝ) (hA : 0 ≤ A) :
    ν * ((L : ℝ) ^ k) ^ 2 * A ≤ ν * ((L : ℝ) ^ (k + 1)) ^ 2 * A := by
  have h1 : (1 : ℝ) ≤ L := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  have h2 : (L : ℝ) ^ k ≤ (L : ℝ) ^ (k + 1) := pow_le_pow_right₀ h1 (Nat.le_succ k)
  have h3 : ((L : ℝ) ^ k) ^ 2 ≤ ((L : ℝ) ^ (k + 1)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hν) hA

omit he in
theorem liftOldGS_inPsiTilde {ν δ : ℝ} (hν : 0 ≤ ν) {Ψ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ}
    {h₀ : Fin N → ℝ} (h : InPsiTilde (liftOldGS G) ν δ Ψ h₀) :
    InPsiTilde G ν δ (fun x => Ψ (oldTorusEquiv x)) h₀ where
  layerConst := liftOldGS_isLayerConstant G h.layerConst
  r1 x x' hx := h.r1 _ _ ((liftOldGS_isInterfacePair_iff G x x').2 hx)
  r2 x hx := h.r2 _ ((liftOldGS_mem_dataSites G x).2 hx)
  r3 x hx := by
    simpa only [liftOldGS_layerIndex_all] using h.r3 _ ((liftOldGS_mem_dataSites G x).2 hx)
  r4 := lt_of_le_of_lt (pow_sq_le_succ (L := L) (k := k) ν hν _ (abs_nonneg _)) h.r4

omit he in
theorem liftOldGS_inPsiTildeC {ν δ ε : ℝ} (hν : 0 ≤ ν)
    {Ψ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ' h' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    (h : InPsiTildeC (liftOldGS G) ν δ ε Ψ h₀ Ψ' h') :
    InPsiTildeC G ν δ ε (fun x => Ψ (oldTorusEquiv x)) h₀ (fun x => Ψ' (oldTorusEquiv x))
      (fun x => h' (oldTorusEquiv x)) where
  toInPsiTilde := liftOldGS_inPsiTilde hν h.toInPsiTilde
  eps_pos := h.eps_pos
  layerConst' := liftOldGS_isLayerConstant G h.layerConst'
  hLayerConst' := liftOldGS_isLayerConstant G h.hLayerConst'
  c1 x x' hx := h.c1 _ _ ((liftOldGS_isInterfacePair_iff G x x').2 hx)
  c2a x hx := h.c2a _ ((liftOldGS_mem_dataSites G x).2 hx)
  c2b x hx := h.c2b _ ((liftOldGS_mem_dataSites G x).2 hx)
  c3a x hx := by
    simpa only [liftOldGS_layerIndex_all] using
      h.c3a _ ((liftOldGS_mem_Ω_le G (by omega) x).2 hx)
  c3b x hx := by
    simpa only [liftOldGS_layerIndex_all] using
      h.c3b _ ((liftOldGS_mem_Ω_le G (by omega) x).2 hx)

omit he in
theorem liftOldGS_inUnionDomainR {ν c₁ : ℝ} (hν : 0 ≤ ν) {D : BgData G N}
    {D' : BgData (liftOldGS G) N} (hΨ : ∀ x, D'.Ψ (oldTorusEquiv x) = D.Ψ x)
    (hh : ∀ x, D'.h (oldTorusEquiv x) = D.h x) (h : InUnionDomainR (liftOldGS G) c₁ ν D') :
    InUnionDomainR G c₁ ν D := by
  obtain ⟨δ, hδ, hδc, Ψ, h₀, hP, hΨ', hh'⟩ := h
  refine ⟨δ, hδ, hδc, fun x => Ψ (oldTorusEquiv x), h₀, liftOldGS_inPsiTilde hν hP,
    fun x hx i => ?_, fun x hx i => ?_⟩
  · rw [← hΨ]; exact hΨ' _ ((liftOldGS_mem_dataSites G x).2 hx) i
  · rw [← hh]; exact hh' _ ((liftOldGS_mem_Ω_le G (by omega) x).2 hx) i

omit he in
theorem liftOldGS_inUnionDomainC {ν c₀ c₁ : ℝ} (hν : 0 ≤ ν) {D : BgData G N}
    {D' : BgData (liftOldGS G) N} (hΨ : ∀ x, D'.Ψ (oldTorusEquiv x) = D.Ψ x)
    (hh : ∀ x, D'.h (oldTorusEquiv x) = D.h x) (h : InUnionDomainC (liftOldGS G) c₀ c₁ ν D') :
    InUnionDomainC G c₀ c₁ ν D := by
  obtain ⟨δ, ε, hδ, hδε, hεc, hδc, hνε, Ψ, h₀, Ψ', h', hP, hΨ', hh'⟩ := h
  refine ⟨δ, ε, hδ, hδε, hεc, hδc,
    le_trans (pow_sq_le_succ (L := L) (k := k) ν hν (ε ^ 2) (sq_nonneg _)) hνε,
    fun x => Ψ (oldTorusEquiv x), h₀, fun x => Ψ' (oldTorusEquiv x),
    fun x => h' (oldTorusEquiv x), liftOldGS_inPsiTildeC hν hP, fun x hx i => ?_,
    fun x hx i => ?_⟩
  · rw [← hΨ]; exact hΨ' _ ((liftOldGS_mem_dataSites G x).2 hx) i
  · rw [← hh]; exact hh' _ ((liftOldGS_mem_Ω_le G (by omega) x).2 hx) i

end

end Balaban.Fluctuation
