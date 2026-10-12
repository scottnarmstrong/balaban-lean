module

public import Balaban.LargeField.R.DeltaPsiDef
public import Balaban.LargeField.R.ChiBridge
public import Balaban.Background.CompositionDomain
public import Balaban.Background.CompositionEstimates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The composed field is close to its data (P7 (2.43))

For `ψ⁰_{k₁,k} = ψ(𝔹_{k₁,k}, 𝔹_k(U_k); ψ̃⁰_k)` (BG (6.2)) and a block field `ψ̃⁰_k ∈ Ψ̃(T; θ)`:
`|ψ⁰_{k₁,k}(x) - ψ̃⁰_k(x)| ≤ 2 K₁ · 3θ` for `x ∈ Ω₁(𝔹_{k₁,k})` (`psiZeroWin_sub_le`), from the
bounds of BG Theorem 5.2 (3) for the background `φ_k(𝔹_k(U_k); ψ̃⁰_k)` (the lifted data lie in
`Ψ̃(𝔹_k(U_k); 3θ)`, `inDomainR_liftSingle`, so the bounds are `K₁ · 3θ`) and the estimate (E1) of the
composed field (`CompHyp.compVec_sub_mean`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section Comp

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {a : ℕ → ℝ} {η : ℝ}
  {Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φ' : G'.Ω 1 × Fin N → ℂ}

/-- The composed field is within `2η` of the data `Ψ'` on `Ω₁` (`θ = 1`, `Ψ'` constant on the blocks of
`𝔹'_k`): `|Ψ - Q_n φ'| ≤ η` (E1) and `|Q_n φ̄' - Ψ'| ≤ η`. -/
theorem compHyp_vn_sub_data (H : CompHyp G G' a 1 η Ψ' φ') {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) :
    vn (fun i => compVec G G' a φ' Ψ' x i - Ψ' x i) ≤ 2 * η := by
  have h1 := H.compVec_sub_mean hx
  have hmean : vn (fun i => meanVec G (Background.barVec G' Ψ' φ') x i - Ψ' x i) ≤ η := by
    obtain ⟨hn1, hnk, -⟩ := G.layerIndex_spec hx
    refine vn_blockMean_sub_le (G := G) hnk (Background.barVec G' Ψ' φ') x (Ψ' x) fun y hy => ?_
    obtain ⟨hy1, hy2⟩ := blk_mem_Ω1' H.prec hx hy
    obtain ⟨-, -, -, -, hb2⟩ := H.prec.block_compat hx hy
    obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec (H.prec.mem_Ω1 hx)
    have hyb : y ∈ G'.blk (G'.layerIndex x) x := by
      rw [← hb2]; exact x_mem_blk _ y
    have hc : Ψ' y = Ψ' x := H.layerConst _ hp1 hpk x hxp y hyb
    have e : (fun i => Background.barVec G' Ψ' φ' y i - Ψ' x i) = fun i => φ' (⟨y, hy2⟩, i) - Ψ' y i := by
      funext i; rw [Background.barVec_of_mem Ψ' φ' hy2, hc]
    rw [e]
    exact H.bounds.close ⟨y, hy2⟩
  have h3 := vn_triangle (compVec G G' a φ' Ψ' x) (meanVec G (Background.barVec G' Ψ' φ') x) (Ψ' x)
  have h1' : vn (compVec G G' a φ' Ψ' x - meanVec G (Background.barVec G' Ψ' φ') x) ≤ η := by
    have := H.η_nn
    nlinarith
  have e1 : (fun i => compVec G G' a φ' Ψ' x i - Ψ' x i) = compVec G G' a φ' Ψ' x - Ψ' x := rfl
  have e2 : (fun i => meanVec G (Background.barVec G' Ψ' φ') x i - Ψ' x i) =
      meanVec G (Background.barVec G' Ψ' φ') x - Ψ' x := rfl
  rw [e1]
  rw [e2] at hmean
  linarith

end Comp

section Window

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

/-- **(2.43)**: `|ψ⁰_{k₁,k}(x) - ψ̃⁰_k(x)| ≤ 2 K₁ (3θ)` on `Ω₁(𝔹_{k₁,k})`, for `ψ̃⁰_k ∈ Ψ̃(T; θ)`,
`θ ≤ 1`, `3θ ≤ c₁`, with `𝔹_{k₁,k} ≺ 𝔹_k(U_k)`, the weights `a = compWeight L a₁` and the Green's function
setting of `𝔹_k(U_k)`. -/
theorem psiZeroWin_sub_le (hL : 2 ≤ L) {a₁ : ℝ} (ha₁ : 0 < a₁) (hprec : Precedes G G')
    (H : BgHyp d L k ϱ' (compWeight L a₁) 0) (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N))
    (h : Fin N → ℝ) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (h3 : 3 * θ ≤ bgC1 d L N)
    {T : Set (Torus d (N₀ * L ^ (k - k)))} (hT : ∀ x ∈ dataSites G', jBlock d L N₀ k k x ∈ T)
    (hψ : PsiTildeSet T (fun z => ψ0 ⟨k, z⟩) θ) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    vn (fun i => psiZeroWin G G' (compWeight L a₁) ψ0 h x i - ((ψ0 ⟨k, jBlock d L N₀ k k x⟩ i : ℝ) : ℂ))
      ≤ 2 * (bgK1 d L N * (3 * θ)) := by
  have hD : InDomainR G' 0 (3 * θ) (psiZeroData G' ψ0 h) :=
    inDomainR_liftSingle G' (fun z i => ψ0 ⟨k, z⟩ i) h T hθ0 hθ1 hT hψ
  obtain ⟨φ, α, -, hb, -, hunit, hmin, huniq⟩ := bg_real H (by positivity) h3 hD
  have hbg : bgField G' (compWeight L a₁) 0 (psiZeroData G' ψ0 h) = φ := bgField_eq hmin huniq
  have hFB : FieldBounds G' (bgK1 d L N * (3 * θ)) (psiZeroData G' ψ0 h).Ψ φ :=
    fieldBounds_of_bgBounds (fun x _ i => rfl) hb (dot_eq_one_of_unit hunit)
  have hK := bgK1_pos d L N
  have hCH : CompHyp G G' (compWeight L a₁) 1 (bgK1 d L N * (3 * θ)) (psiZeroData G' ψ0 h).Ψ φ :=
    { prec := hprec, θ_pos := one_pos, η_nn := by positivity, gap := scaleGap_one hprec
      ratio := fun y hy => compWeight_ratio hL ha₁ (G.layerIndex_spec hy).1
        (hprec.layerIndex_le hy)
      layerConst := (psiZeroData G' ψ0 h).Ψ_layerConst, bounds := hFB }
  have hmain := compHyp_vn_sub_data hCH hx
  have hxd : x ∈ dataSites G' := (mem_dataSites G').2 (Or.inl (hprec.mem_Ω1 hx))
  have e : (fun i => psiZeroWin G G' (compWeight L a₁) ψ0 h x i -
        ((ψ0 ⟨k, jBlock d L N₀ k k x⟩ i : ℝ) : ℂ)) =
      fun i => compVec G G' (compWeight L a₁) φ (psiZeroData G' ψ0 h).Ψ x i -
        (psiZeroData G' ψ0 h).Ψ x i := by
    funext i
    have h1 : psiZeroWin G G' (compWeight L a₁) ψ0 h x i =
        compVec G G' (compWeight L a₁) φ (psiZeroData G' ψ0 h).Ψ x i := by
      unfold psiZeroWin compVec
      rw [hbg]
    rw [h1]
    have h2 : (psiZeroData G' ψ0 h).Ψ x i = ((ψ0 ⟨k, jBlock d L N₀ k k x⟩ i : ℝ) : ℂ) := by
      unfold psiZeroData
      rw [liftSingle_Ψ G' _ _ hxd]
    rw [h2]
  rw [e]
  exact hmain

end Window

end Balaban.LargeField
