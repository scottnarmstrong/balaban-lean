module

public import Balaban.LargeField.R.ChainGraph
public import Balaban.LargeField.R.SmallFactorTilde
public import Balaban.LargeField.R.WindowGenSingle
public import Balaban.LargeField.Background.Lift
public import Balaban.Background.Def5
public import Balaban.Background.Composition
import Mathlib.Tactic.Linarith

/-!
# The window field `δψ` (Part III, §III.4.4, P7 (2.46))

`δψ := ψ̃ - ψ⁰_{k₁,k}` on `𝔹_{k₁,k}`, where `ψ̃ = Q*(𝔹_{k₁,k}, 𝔹_k) ψ` is the multiscale field read on the
sites of the window generating set, and `ψ⁰_{k₁,k} = ψ(𝔹_{k₁,k}, 𝔹_k(U_k); ψ̃⁰_k)` is the composed field
(BG (6.2), `composeField`) of the block field `ψ̃⁰_k` of Lemma III.3.3 through its background
`φ_k(𝔹_k(U_k); ψ̃⁰_k)` (Def-5, massless).

* `psiTilde`: the field `ψ̃` on the sites of a generating set;
* `psiZeroData`, `psiZeroWin`: the data `lift_k ψ̃⁰_k` and the composed field `ψ⁰_{k₁,k}` (P7 (2.40));
* `deltaPsi`: `δψ`, zero off `𝔹_{k₁,k}`;
* `PsiZeroSpec` (Lemma III.3.3, cited): the properties of the block field `ψ⁰_k` used in Lemma III.4.6;
* `WinBond` (Definition II.3.4 (1.24), contained in `𝒳_win`): adjacent blocks of the multiscale field
  differ by `< c δ`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section Def

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

open Classical in
/-- `ψ̃ = Q*(𝔹, 𝔹_k) ψ` at a site `x`: the value of the multiscale field `ψ` on the block of layer
`n(x)` containing `x` for `x ∈ Ω₁` (P7 (2.46), `ψ̃(x) = ψ_j(y)` for the window block `y ∋ x`), and the
value of the layer `0` (the fine-scale field `ψ_0(x)`) outside `Ω₁`, in particular on the collar. -/
noncomputable def psiTilde (G : GeneratingSet d L N₀ k ϱ)
    (ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (x : Torus d (N₀ * L ^ k)) : Fin N → ℝ :=
  fun i => if x ∈ G.Ω 1 then ψ (blockOf d L N₀ k (G.layerIndex x) x) i
    else ψ (⟨0, x⟩ : BlockV d L N₀ k) i

theorem psiTilde_of_mem (G : GeneratingSet d L N₀ k ϱ)
    (ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (i : Fin N) : psiTilde G ψ x i = ψ (blockOf d L N₀ k (G.layerIndex x) x) i := by
  simp [psiTilde, hx]

/-- The data `(Ψ, h̃) = lift_k ψ̃⁰_k` of the generating set `𝔹_k(U_k)` from the block field `ψ̃⁰_k`
(only its values on `k`-blocks enter). -/
noncomputable def psiZeroData (G' : GeneratingSet d L N₀ k ϱ')
    (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ) : BgData G' N :=
  liftSingle G' (fun z i => ((ψ0 ⟨k, z⟩ i : ℝ) : ℂ)) (fun i => ((h i : ℝ) : ℂ))

/-- **`ψ⁰_{k₁,k}`** (P7 (2.40)): the composed field (BG (6.2)) of the data `lift_k ψ̃⁰_k` through the
massless background `φ_k(𝔹_k(U_k); ψ̃⁰_k)` of Def-5, from the window generating set `G`. -/
noncomputable def psiZeroWin (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')
    (a : ℕ → ℝ) (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ) :
    Torus d (N₀ * L ^ k) → Fin N → ℂ :=
  composeField G G' a (bgField G' a 0 (psiZeroData G' ψ0 h)) (psiZeroData G' ψ0 h).Ψ

open Classical in
/-- **`δψ`** (P7 (2.46)): `ψ̃ - ψ⁰_{k₁,k}` on the sites of the window generating set `G` (zero
elsewhere). -/
noncomputable def deltaPsi (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')
    (a : ℕ → ℝ) (ψ ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    (x : Torus d (N₀ * L ^ k)) : Fin N → ℂ :=
  fun i => if x ∈ G.Ω 1 then ((psiTilde G ψ x i : ℝ) : ℂ) - psiZeroWin G G' a ψ0 h x i else 0

theorem deltaPsi_of_mem (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')
    (a : ℕ → ℝ) (ψ ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (i : Fin N) :
    deltaPsi G G' a ψ ψ0 h x i = ((psiTilde G ψ x i : ℝ) : ℂ) - psiZeroWin G G' a ψ0 h x i := by
  simp [deltaPsi, hx]

end Def

section Spec

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' ϱ'' : ℝ}

/-- **The properties of the block field `ψ⁰_k` of Lemma III.3.3 used in Lemma III.4.6** (P7 Lemma 2.1,
cited; the field itself, the solution of (2.34), is not constructed here): `ψ⁰_k ∈ Ψ̃(U^∼_k; θ)`
(`θ = 3 K₆ δ_k`, the data of the generating set `𝔹_k(U_k)` live in `U^∼_k`, and `U^∼_k ⊇ Z`), and
`ψ⁰_k = ψ_k` on the terminal blocks (the `k`-blocks of `Ω_k ∩ Z`, which lie off `Z₀`).
`Gk` is the generating set `𝔹_k` (it defines the terminal blocks), `G'` is `𝔹_k(U_k)`, `Zf` the fine
set of `Z`. -/
def PsiZeroSpec (Gk : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')
    (Zf : Set (Torus d (N₀ * L ^ k))) (θ : ℝ)
    (ψ ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) : Prop :=
  ∃ Ut : Set (Torus d (N₀ * L ^ (k - k))),
    (∀ x ∈ Zf, jBlock d L N₀ k k x ∈ Ut) ∧ (∀ x ∈ dataSites G', jBlock d L N₀ k k x ∈ Ut) ∧
    PsiTildeSet Ut (fun z => ψ0 ⟨k, z⟩) θ ∧ ∀ b, IsTerminalBlock Gk Zf b → ψ0 b = ψ b

/-- **Definition II.3.4 (1.24) on the window blocks** (contained in the window characteristic
function `𝒳_win`; LFR §III.4.4): adjacent blocks of the multiscale field in layers `{n, n-1}` differ by
`< c δ`, here `c = 3dL`, with the tolerance `δ_n` of the lower layer.  Intra part: translates
`y' = y ± L^i e_μ` of one layer; cross part: nearest-neighbour adjacent blocks of the layers `i + 1`
and `i`. -/
def WinBond (G : GeneratingSet d L N₀ k ϱ) (Zc Zf : Set (Torus d (N₀ * L ^ k))) (k1 : ℕ) (c : ℝ)
    (δ : ℕ → ℝ) (ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) : Prop :=
  (∀ (i : ℕ) (u v : Torus d (N₀ * L ^ (k - i))), IsChainVertex G Zc Zf k1 ⟨i, u⟩ →
      IsChainVertex G Zc Zf k1 ⟨i, v⟩ → AdjT u v → dist (ψ ⟨i, u⟩) (ψ ⟨i, v⟩) < c * δ i) ∧
  (∀ (i : ℕ) (u : Torus d (N₀ * L ^ (k - (i + 1)))) (v : Torus d (N₀ * L ^ (k - i))),
      IsChainVertex G Zc Zf k1 ⟨i + 1, u⟩ → IsChainVertex G Zc Zf k1 ⟨i, v⟩ →
      (∃ x ∈ BlockV.sites (⟨i + 1, u⟩ : BlockV d L N₀ k), ∃ y ∈ BlockV.sites (⟨i, v⟩ : BlockV d L N₀ k),
        NNAdj x y) →
      dist (ψ ⟨i + 1, u⟩) (ψ ⟨i, v⟩) < c * δ i)

/-- `PsiZeroSpec` is inhabited (for every choice of the generating sets, the fine set and `θ > 0`): the
constant unit field. -/
theorem psiZeroSpec_nonempty (Gk : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')
    (Zf : Set (Torus d (N₀ * L ^ k))) {θ : ℝ} (hθ : 0 < θ) (hN : 0 < N) :
    ∃ ψ ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N), PsiZeroSpec Gk G' Zf θ ψ ψ0 := by
  let e : EuclideanSpace ℝ (Fin N) := EuclideanSpace.single ⟨0, hN⟩ 1
  refine ⟨fun _ => e, fun _ => e, Set.univ, fun _ _ => trivial, fun _ _ => trivial, ⟨?_, ?_⟩,
    fun _ _ => rfl⟩
  · intro y _ y' _ _; simpa using hθ
  · intro y _; simpa [e] using hθ

/-- `WinBond` is inhabited: the constant field, for positive `c δ_i`. -/
theorem winBond_nonempty (G : GeneratingSet d L N₀ k ϱ) (Zc Zf : Set (Torus d (N₀ * L ^ k)))
    (k1 : ℕ) {c : ℝ} {δ : ℕ → ℝ} (hc : 0 < c) (hδ : ∀ i, 0 < δ i) (hN : 0 < N) :
    ∃ ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N), WinBond G Zc Zf k1 c δ ψ := by
  let e : EuclideanSpace ℝ (Fin N) := EuclideanSpace.single ⟨0, hN⟩ 1
  refine ⟨fun _ => e, ?_, ?_⟩
  · intro i u v _ _ _; simpa using mul_pos hc (hδ i)
  · intro i u v _ _ _; simpa using mul_pos hc (hδ i)

end Spec

end Balaban.LargeField
