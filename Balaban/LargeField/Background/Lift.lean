module

public import Balaban.Background.Composition
public import Balaban.Background.Data
import Mathlib.Tactic.Linarith

/-!
# Lifted data (Part II, Definition II.2.1)

For a generating set `G` at level `q` the data `Ψ` of the background variational problem are
lifts of block-spin fields:

* `liftSingle` (P5 (1.4)): `q = k`, `Ψ(x) = ψ_k(y_k(x))`, `y_k(x)` the `k`-block of `x`;
* `liftMixed` (P5 (2.11)-(2.12)): `q = k + 1`, a set `Ω` of sites that is a union of
  `(k+1)`-blocks containing the top layer `Ω_{k+1}(G)`, fields `ψ_k` on the `k`-blocks and `ϑ` on
  the `(k+1)`-blocks: `Ψ(x) = ϑ(y_{k+1}(x))` on `Ω` and `ψ_k(y_k(x))` off `Ω`.

Both are layer-constant for `G` (`liftSingle_layerConst`, `liftMixed_layerConst`), hence give
`BgData G N` (clipped to the data sites; the constant field `h̃ ≡ h`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The pullback of a field on the `k`-blocks to the fine torus: `x ↦ ψ_k(y_k(x))`. -/
def blockLift (j : ℕ) {β : Type*} (ψ : Torus d (N₀ * L ^ (k - j)) → β)
    (x : Torus d (N₀ * L ^ k)) : β := ψ (jBlock d L N₀ k j x)

/-- A block lift is constant on blocks of every smaller scale. -/
theorem blockLift_eq_of_le {j n : ℕ} (hnj : n ≤ j) (hjk : j ≤ k) {β : Type*}
    (ψ : Torus d (N₀ * L ^ (k - j)) → β) {x x' : Torus d (N₀ * L ^ k)}
    (h : jBlock d L N₀ k n x = jBlock d L N₀ k n x') : blockLift j ψ x = blockLift j ψ x' := by
  unfold blockLift
  rw [jBlock_eq_of_le hnj hjk h]

/-- **Definition II.2.1 (a)** (single-scale lift): the lift of `ψ_k` to a layer-constant field. -/
theorem liftSingle_layerConst (G : GeneratingSet d L N₀ k ϱ) {β : Type*}
    (ψ : Torus d (N₀ * L ^ (k - k)) → β) : IsLayerConstant G (blockLift k ψ) := by
  intro n hn1 hnk x _ x' hx'
  exact blockLift_eq_of_le hnk le_rfl ψ (GeneratingSet.mem_blk.1 hx')

/-- **Definition II.2.1 (a)**: the data `(Ψ, h̃) = (lift_k ψ_k, h)` as `BgData` (clipped to the data
sites; the field `h̃` is the constant `h`). -/
noncomputable def liftSingle (G : GeneratingSet d L N₀ k ϱ)
    (ψ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) (h : Fin N → ℂ) : BgData G N :=
  BgData.clip G (blockLift k ψ) (fun _ => h) (liftSingle_layerConst G ψ)
    (fun _ _ _ _ _ _ _ => rfl)

theorem liftSingle_Ψ (G : GeneratingSet d L N₀ k ϱ) (ψ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ)
    (h : Fin N → ℂ) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ dataSites G) :
    (liftSingle G ψ h).Ψ x = ψ (jBlock d L N₀ k k x) := by
  classical
  simp [liftSingle, BgData.clip, hx, blockLift]

theorem liftSingle_h (G : GeneratingSet d L N₀ k ϱ) (ψ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ)
    (h : Fin N → ℂ) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    (liftSingle G ψ h).h x = h := by
  classical
  simp [liftSingle, BgData.clip, hx]

/-- The mixed lift: `ϑ(y_{k+1}(x))` on `Ω`, `ψ_k(y_k(x))` off `Ω` (P5 (2.11)-(2.12)). -/
noncomputable def mixedLift {β : Type*} (Ω : Finset (Torus d (N₀ * L ^ (k + 1))))
    (ψ : Torus d (N₀ * L ^ (k + 1 - k)) → β) (ϑ : Torus d (N₀ * L ^ (k + 1 - (k + 1))) → β)
    (x : Torus d (N₀ * L ^ (k + 1))) : β := by
  classical
  exact if x ∈ Ω then blockLift (k + 1) ϑ x else blockLift k ψ x

/-- **Definition II.2.1 (b)**: the mixed lift is layer-constant for a level-`(k+1)` generating set
`G` when `Ω` is a union of `(k+1)`-blocks containing the top layer `Ω_{k+1}(G)`. -/
theorem liftMixed_layerConst (G : GeneratingSet d L N₀ (k + 1) ϱ) {β : Type*}
    {Ω : Finset (Torus d (N₀ * L ^ (k + 1)))} (hΩ : IsBlockUnion L N₀ (k + 1) (k + 1) Ω)
    (hG : G.Ω (k + 1) ⊆ Ω) (ψ : Torus d (N₀ * L ^ (k + 1 - k)) → β)
    (ϑ : Torus d (N₀ * L ^ (k + 1 - (k + 1))) → β) :
    IsLayerConstant G (mixedLift Ω ψ ϑ) := by
  classical
  intro n hn1 hnk x hx x' hx'
  have hb : jBlock d L N₀ (k + 1) n x' = jBlock d L N₀ (k + 1) n x := GeneratingSet.mem_blk.1 hx'
  have hb1 : jBlock d L N₀ (k + 1) (k + 1) x' = jBlock d L N₀ (k + 1) (k + 1) x :=
    jBlock_eq_of_le hnk le_rfl hb
  have hiff : x' ∈ Ω ↔ x ∈ Ω := hΩ x' x hb1
  unfold mixedLift
  by_cases hxΩ : x ∈ Ω
  · simp only [hxΩ, hiff.2 hxΩ, ↓reduceIte]
    exact blockLift_eq_of_le le_rfl le_rfl ϑ hb1
  · have hn : n ≤ k := by
      by_contra hcon
      have hnk1 : n = k + 1 := by omega
      subst hnk1
      exact hxΩ (hG (G.mem_layer.1 hx).1)
    have hx'Ω : x' ∉ Ω := fun h => hxΩ (hiff.1 h)
    simp only [hxΩ, hx'Ω, ↓reduceIte]
    exact blockLift_eq_of_le hn (Nat.le_succ k) ψ hb

/-- **Definition II.2.1 (b)**: the mixed lift as `BgData`. -/
noncomputable def liftMixed (G : GeneratingSet d L N₀ (k + 1) ϱ)
    {Ω : Finset (Torus d (N₀ * L ^ (k + 1)))} (hΩ : IsBlockUnion L N₀ (k + 1) (k + 1) Ω)
    (hG : G.Ω (k + 1) ⊆ Ω) (ψ : Torus d (N₀ * L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ : Torus d (N₀ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h : Fin N → ℂ) : BgData G N :=
  BgData.clip G (mixedLift Ω ψ ϑ) (fun _ => h) (liftMixed_layerConst G hΩ hG ψ ϑ)
    (fun _ _ _ _ _ _ _ => rfl)

theorem liftMixed_Ψ (G : GeneratingSet d L N₀ (k + 1) ϱ)
    {Ω : Finset (Torus d (N₀ * L ^ (k + 1)))} (hΩ : IsBlockUnion L N₀ (k + 1) (k + 1) Ω)
    (hG : G.Ω (k + 1) ⊆ Ω) (ψ : Torus d (N₀ * L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ : Torus d (N₀ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h : Fin N → ℂ)
    {x : Torus d (N₀ * L ^ (k + 1))} (hx : x ∈ dataSites G) :
    (liftMixed G hΩ hG ψ ϑ h).Ψ x = mixedLift Ω ψ ϑ x := by
  classical
  simp [liftMixed, BgData.clip, hx]

theorem liftMixed_h (G : GeneratingSet d L N₀ (k + 1) ϱ)
    {Ω : Finset (Torus d (N₀ * L ^ (k + 1)))} (hΩ : IsBlockUnion L N₀ (k + 1) (k + 1) Ω)
    (hG : G.Ω (k + 1) ⊆ Ω) (ψ : Torus d (N₀ * L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ : Torus d (N₀ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h : Fin N → ℂ)
    {x : Torus d (N₀ * L ^ (k + 1))} (hx : x ∈ G.Ω 1) :
    (liftMixed G hΩ hG ψ ϑ h).h x = h := by
  classical
  simp [liftMixed, BgData.clip, hx]

end Balaban.LargeField
