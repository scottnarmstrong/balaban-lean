/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.Lift
public import Balaban.Background.Def5
public import Balaban.Background.Equivariance
public import Balaban.Background.EquivarianceDomain


/-!
# The effective action of Lemma III.3.3 (P7 (2.34)): data and tube

For a generating set `G` at level `k` (the set `𝔹_k(U_k)`), block fields `ψ_k` on the `k`-blocks, the lifted
data `ψ̃_k = Q* ψ_k` (`dataR`, Definition II.2.1 (a), massless) and the effective action
`effAction G a ψ_k = A_k(𝔹; ψ̃_k, φ_k(𝔹; ψ̃_k))` (the BG action at the Def-5 background `bgField`).
`TubeOn X δ ψ` is the tube `Ψ̃(X; δ)` (conditions (R1), (R2); (R3), (R4) are void for `ν = 0`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section Eff

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- Real block fields `ψ_k : 𝕋^{(k)} → ℝ^N` on the `k`-blocks of the level-`k` torus. -/
abbrev BlockField (d L N₀ k N : ℕ) : Type := Torus d (N₀ * L ^ (k - k)) → Fin N → ℝ

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The complex data `lift_k ψ_k` (Definition II.2.1 (a)) with the constant `h = 0` (the mass term is absent). -/
noncomputable def dataC (ψ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) : BgData G N :=
  liftSingle G ψ 0

/-- The real data of a real block field. -/
noncomputable def dataR (ψ : BlockField d L N₀ k N) : BgData G N :=
  dataC G (fun z i => (ψ z i : ℂ))

/-- The lifted field `Ψ = Q* ψ_k` on the fine sites. -/
def liftR (ψ : BlockField d L N₀ k N) : Torus d (N₀ * L ^ k) → Fin N → ℝ :=
  fun x i => ψ (jBlock d L N₀ k k x) i

/-- **The effective action** `ψ_k ↦ A_k(𝔹; ψ̃_k, φ_k(𝔹; ψ̃_k))` of P7 (2.34): the BG action (`action`) of the
Def-5 background field `bgField` for the lifted data, massless (`ν = 0`). -/
noncomputable def effAction (a : ℕ → ℝ) (ψ : BlockField d L N₀ k N) : ℝ :=
  action G a 0 (dataR G ψ) (bgField G a 0 (dataR G ψ))

/-- The tube conditions (R1), (R2) of `Ψ̃(X; δ)` for the lifted field, imposed over the block set `X`
(R3), (R4) are void for `ν = 0`. -/
def TubeOn (X : Set (Torus d (N₀ * L ^ (k - k)))) (δ : ℝ) (ψ : BlockField d L N₀ k N) : Prop :=
  (∀ x x', IsInterfacePair G x x' → jBlock d L N₀ k k x ∈ X → jBlock d L N₀ k k x' ∈ X →
      rn (fun i => liftR ψ x i - liftR ψ x' i) < δ) ∧
    ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X → |∑ i, ψ (jBlock d L N₀ k k x) i ^ 2 - 1| < δ

theorem tubeOn_univ_iff {δ : ℝ} (hδ : 0 < δ) (ψ : BlockField d L N₀ k N) :
    TubeOn G Set.univ δ ψ ↔ InPsiTilde G 0 δ (liftR ψ) 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨liftSingle_layerConst G (fun z => ψ z), fun x x' h => h1 x x' h trivial trivial,
      fun x hx => h2 x hx trivial, fun x _ => by simpa using pow_pos hδ 2, by simpa using pow_pos hδ 2⟩
  · intro h
    exact ⟨fun x x' hp _ _ => h.r1 x x' hp, fun x hx _ => h.r2 x hx⟩

theorem dataR_Ψ (ψ : BlockField d L N₀ k N) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ dataSites G) (i : Fin N) :
    (dataR G ψ).Ψ x i = (liftR ψ x i : ℂ) := by
  simp [dataR, dataC, liftSingle_Ψ G _ _ hx, liftR]

theorem dataR_h (ψ : BlockField d L N₀ k N) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (i : Fin N) :
    (dataR G ψ).h x i = ((0 : ℝ) : ℂ) := by
  simp [dataR, dataC, liftSingle_h G _ _ hx]

theorem inDomainR_of_tube {δ : ℝ} (hδ : 0 < δ) {ψ : BlockField d L N₀ k N}
    (ht : TubeOn G Set.univ δ ψ) : InDomainR G 0 δ (dataR G ψ) :=
  ⟨liftR ψ, 0, (tubeOn_univ_iff G hδ ψ).1 ht, fun x hx i => dataR_Ψ G ψ hx i,
    fun x hx i => by simpa using dataR_h G ψ hx i⟩

theorem inUnionDomainR_of_tube {δ c₁ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ c₁) {ψ : BlockField d L N₀ k N}
    (ht : TubeOn G Set.univ δ ψ) : InUnionDomainR G c₁ 0 (dataR G ψ) :=
  ⟨δ, hδ, hδ1, inDomainR_of_tube G hδ ht⟩

theorem inUnionDomainC_of_tube {δ c₀ c₁ : ℝ} (hδ : 0 < δ) (hδ0 : δ ≤ c₀) (hδ1 : δ ≤ c₁)
    {ψ : BlockField d L N₀ k N} (ht : TubeOn G Set.univ δ ψ) :
    InUnionDomainC G c₀ c₁ 0 (dataR G ψ) := by
  refine ⟨δ, δ, hδ, le_rfl, hδ0, hδ1, by simpa using sq_nonneg δ, ?_⟩
  have hR := (tubeOn_univ_iff G hδ ψ).1 ht
  refine ⟨liftR ψ, 0, 0, 0, ⟨hR, hδ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun x hx i => ?_, fun x hx i => ?_⟩
  · intro n _ _ x _ x' _; rfl
  · intro n _ _ x _ x' _; rfl
  · intro x x' _; simpa [vn] using hδ
  · intro x _; simpa [vn] using add_pos hδ hδ
  · intro x _; simpa using hδ
  · intro x _; simpa using by positivity
  · intro x _; simpa using by positivity
  · simpa using dataR_Ψ G ψ hx i
  · simpa using dataR_h G ψ hx i

end Eff

end Balaban.LargeField
