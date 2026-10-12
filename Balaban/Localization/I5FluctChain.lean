/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5FluctSol
public import Balaban.Localization.DomainLemma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The chain of the analyticity spaces with the fluctuation (LOCALIZATION.md §4.3, P3 (4.41))

The datum of `𝔹_k(X)` in the composite `F(s)` of P3 (4.41) is
`ψ(𝔹_k(X), 𝔹_{k+1}; Θ, s) + δψ(𝔹_k(X), 𝔹_k; ψ', s)`, where (P3 (4.17); FLDATUM (2))
`δψ = Q(𝔹_k(X)) δφ + a(𝔹_k(X))⁻¹ Q*(𝔹_k, 𝔹_k(X)) a(𝔹_k) (ψ' - Q(𝔹_k) δφ)` is the composed field
`composeField Gk Hm a δφ ψ'` of the pair `(δφ, ψ')`.  For a layer-constant `ψ'` it is a
layer-constant perturbation of the datum of the background part (`flDatum`), of size at most
`N (5 V + δ₁)` on the data sites if `|δφ| ≤ V` and `|ψ'| ≤ δ₁` (`flPsi_bound`), so it stays in
`Ξ^c_K(𝔹_k(X); 1, ε₃)` (`xiCData_perturb`), by (Ξ2).

* `flDatum`: the perturbed datum (FLDATUM (3)), `flDatum_Ψ`;
* `flPsi_bound`: the bound FLDATUM (4);
* `composeField_trans`: the composition identity `ψ(𝔹₁, 𝔹; ψ(𝔹, 𝔹'; Ψ')) = ψ(𝔹₁, 𝔹'; Ψ')`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset Matrix

section Perturb

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- (Ξ2) for realizations: `Ξ^c_K(𝔹; 1, ε')` is stable under layer-constant perturbations. -/
theorem xiCData_perturb (H : BgHyp d L K ϱ a ν) {ε' δ₃ : ℝ} (hδ₃ : 0 ≤ δ₃) (hδ₃1 : δ₃ ≤ 1)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε') ≤ 1)
    (hδ₂ : xiC1 d * ε' + 5 * δ₃ ≤ bgC1 d L N)
    (hstar : δ₃ ≤ deltaStar d L N) (hK1s : bgK1 d L N * (xiC1 d * ε') ≤ deltaStar d L N)
    (hsm : bgK1 d L N * (xiC1 d * ε') + cK2 d L N * δ₃ < bgC0 d L N)
    {δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} (hδΨc : IsLayerConstant G δΨ)
    (hδΨ : ∀ x ∈ dataSites G, vn (δΨ x) ≤ δ₃) {D : BgData G N}
    (hX : XiCData G a ν K 1 ε' D) :
    XiCData G a ν K 1 (ε' + xiK2 d L N * δ₃) (perturbData G D δΨ hδΨc) := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hX, hR⟩ := hX
  refine ⟨Ψ₀, h₀, fun x i => Ψ'' x i + δΨ x i, h'',
    xiC_perturb H hδ₃ hδ₃1 hsmall hδ₂ hstar hK1s hsm hδΨc hδΨ hX, ⟨fun x hx i => ?_, fun x hx i => ?_⟩⟩
  · rw [perturbData_Ψ hx, hR.1 x hx i]; ring
  · exact hR.2 x hx i

end Perturb

section Stage

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}

/-- **The composed fluctuation** `δψ(𝔹_k(X), 𝔹_k; ψ', s) = composeField 𝔹_k(X) 𝔹_k a δφ ψ'`
(P3 (4.17)) is layer-constant on `𝔹_k(X)` if `ψ'` is layer-constant on `𝔹_k`. -/
theorem flPsi_layerConst (hPm : Precedes Gk Hm) (a : ℕ → ℝ) (δφ : Hm.Ω 1 × Fin N → ℂ)
    {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ} (hψ' : IsLayerConstant Hm ψ') :
    IsLayerConstant Gk (fun x i => composeField Gk Hm a δφ ψ' x i) :=
  composeField_layerConst hPm a δφ hψ'

/-- **The size of the composed fluctuation** (FLDATUM (4)): `|δψ(x)| ≤ N (5 V + δ₁)` at every site,
if `|δφ| ≤ V` and `|ψ'| ≤ δ₁` on the data sites of `𝔹_k`.  On `Ω₁(𝔹_k(X))` the weight
`κ_{n,p} = (a_p / a_n) L^{2(n-p)}` lies in `[0, 1]` (`compWeight_kappa_mem`); on the collar of
`𝔹_k(X)` the composed field is `δφ` (on `Ω₁(𝔹_k)`) or `ψ'` (on the collar of `𝔹_k`). -/
theorem flPsi_bound (hPm : Precedes Gk Hm) (hL : 2 ≤ L) {a₁ : ℝ} (ha₁ : 0 < a₁)
    {δφ : Hm.Ω 1 × Fin N → ℂ} {V δ₁ : ℝ} (hV : 0 ≤ V) (hδ₁ : 0 ≤ δ₁)
    (hδ : ∀ (y : CTorus d L N₁ m₁ K) (i : Fin N), ‖svec Hm δφ y i‖ ≤ V)
    {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ} (hψ : ∀ x ∈ dataSites Hm, vn (ψ' x) ≤ δ₁)
    (x : CTorus d L N₁ m₁ K) :
    vn (fun i => composeField Gk Hm (compWeight L a₁) δφ ψ' x i) ≤ N * (5 * V + δ₁) := by
  classical
  refine vn_le_card_mul (by positivity) fun i => ?_
  by_cases hx : x ∈ Gk.Ω 1
  · rw [composeField_of_mem (compWeight L a₁) δφ ψ' hx i]
    obtain ⟨hn1, hnk, -⟩ := Gk.layerIndex_spec hx
    have hxH : x ∈ Hm.Ω 1 := hPm.mem_Ω1 hx
    obtain ⟨-, hpk, -⟩ := Hm.layerIndex_spec hxH
    obtain ⟨hκ0, hκ1⟩ := compWeight_kappa_mem hL ha₁ hn1 (hPm.layerIndex_le hx)
    have b1 : ‖blockMean Gk (Gk.layerIndex x) (fun y => svec Hm δφ y i) x‖ ≤ V :=
      norm_blockMean_le (G := Gk) _ hnk _ x fun y _ => hδ y i
    have b2 : ‖blockMean Hm (Hm.layerIndex x) (fun y => svec Hm δφ y i) x‖ ≤ V :=
      norm_blockMean_le (G := Hm) _ hpk _ x fun y _ => hδ y i
    have hψx : ‖ψ' x i‖ ≤ δ₁ :=
      (norm_le_vn _ i).trans (hψ x ((mem_dataSites Hm).2 (Or.inl hxH)))
    have hc : ‖(((compWeight L a₁ (Hm.layerIndex x) / compWeight L a₁ (Gk.layerIndex x) *
        (((L : ℝ) ^ Gk.layerIndex x) ^ 2 / ((L : ℝ) ^ Hm.layerIndex x) ^ 2) : ℝ)) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg hκ0]; exact hκ1
    calc _ ≤ V + 1 * (δ₁ + V) := by
          refine (norm_add_le _ _).trans (add_le_add b1 ?_)
          rw [norm_mul]
          exact mul_le_mul hc ((norm_sub_le _ _).trans (add_le_add hψx b2)) (norm_nonneg _)
            zero_le_one
      _ ≤ 5 * V + δ₁ := by linarith
  · by_cases hc : x ∈ collar Gk
    · rw [composeField_of_collar (compWeight L a₁) δφ ψ' hc i]
      unfold barField
      by_cases hxH : x ∈ Hm.Ω 1
      · simp only [hxH, ↓reduceDIte]
        have := hδ x i
        rw [svec_of_mem' δφ hxH i] at this
        linarith
      · simp only [hxH, ↓reduceDIte]
        obtain ⟨-, y, hy, hadj⟩ := (mem_collar Gk).1 hc
        have hxc : x ∈ collar Hm := mem_collar_of_adj Hm (hPm.mem_Ω1 hy) hxH hadj
        have := (norm_le_vn _ i).trans (hψ x ((mem_dataSites Hm).2 (Or.inr hxc)))
        linarith
    · have hd : x ∉ dataSites Gk := fun h => by
        rcases (mem_dataSites Gk).1 h with h | h
        · exact hx h
        · exact hc h
      rw [composeField_of_not_mem (compWeight L a₁) δφ ψ' hd i, norm_zero]
      positivity

variable (Gk) in
/-- **The datum of `𝔹_k(X)` with the fluctuation** (FLDATUM (3); P3 (4.16), (4.17), (4.21)): the
background composition `ψ(𝔹_k(X), 𝔹_{k+1}; Θ) = composeData` perturbed by the composed
fluctuation `δψ(𝔹_k(X), 𝔹_k; ψ') = composeField 𝔹_k(X) 𝔹_k a δφ ψ'` of the pair `(δφ, ψ')`
(P3 (4.17): `Q(𝔹_k(X)) δφ + a(𝔹_k(X))⁻¹ Q*(𝔹_k, 𝔹_k(X)) a(𝔹_k) (ψ' - Q(𝔹_k) δφ)`), for a
fluctuation `ψ'` constant on the blocks of `𝔹_k` (the lift of a field of the lattice of `𝔹_k`).
The `h̃`-component is that of the background composition. -/
noncomputable def flDatum (hP : Precedes Gk Gp) (hPm : Precedes Gk Hm) (a : ℕ → ℝ)
    (φ : Gp.Ω 1 × Fin N → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ) (D : BgData Gp N)
    (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ) (hψ' : IsLayerConstant Hm ψ') : BgData Gk N :=
  perturbData Gk (composeData hP a φ D)
    (fun x i => composeField Gk Hm a δφ ψ' x i) (flPsi_layerConst hPm a δφ hψ')

/-- **FLDATUM (3)**: the spin datum of `flDatum` is the sum of the two compositions of P3 (4.21). -/
theorem flDatum_Ψ (hP : Precedes Gk Gp) (hPm : Precedes Gk Hm) (a : ℕ → ℝ)
    (φ : Gp.Ω 1 × Fin N → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ) (D : BgData Gp N)
    (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ) (hψ' : IsLayerConstant Hm ψ')
    (x : CTorus d L N₁ m₁ K) (i : Fin N) :
    (flDatum Gk hP hPm a φ δφ D ψ' hψ').Ψ x i = composeField Gk Gp a φ D.Ψ x i +
      composeField Gk Hm a δφ ψ' x i := by
  classical
  by_cases hx : x ∈ dataSites Gk
  · rw [flDatum, perturbData_Ψ hx]; rfl
  · simp [flDatum, perturbData, composeData, hx, composeField_of_not_mem _ _ _ hx]

theorem flDatum_h (hP : Precedes Gk Gp) (hPm : Precedes Gk Hm) (a : ℕ → ℝ)
    (φ : Gp.Ω 1 × Fin N → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ) (D : BgData Gp N)
    (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ) (hψ' : IsLayerConstant Hm ψ') :
    (flDatum Gk hP hPm a φ δφ D ψ' hψ').h = (composeData hP a φ D).h := rfl

end Stage

section Trans

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ₁ ϱ' : ℝ}
variable {G₁ : GeneratingSet d L N₀ k ϱ₁} {G : GeneratingSet d L N₀ k ϱ}
  {G' : GeneratingSet d L N₀ k ϱ'}

theorem svec_restrictφ (h : Precedes G G') (φ' : G'.Ω 1 × Fin N → ℂ) {y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.Ω 1) (i : Fin N) : svec G (h.restrictφ φ') y i = svec G' φ' y i := by
  rw [svec_of_mem G (h.restrictφ φ') ⟨y, hy⟩ i, svec_of_mem' φ' (h.mem_Ω1 hy) i]
  rfl

/-- **The composition identity** (P3 (4.16); BG §6): for `𝔹₁ ≺ 𝔹 ≺ 𝔹'` and weights `a_j ≠ 0`,
composing in two steps is composing in one step,
`ψ(𝔹₁, 𝔹; φ'|_{Ω₁(𝔹)}, ψ(𝔹, 𝔹'; φ', Ψ')) = ψ(𝔹₁, 𝔹'; φ', Ψ')`
(`κ_{n,m} κ_{m,p} = κ_{n,p}` for the layers `n ≤ m ≤ p` of a site). -/
theorem composeField_trans (h₁ : Precedes G₁ G) (h : Precedes G G') {a : ℕ → ℝ}
    (ha : ∀ j, 1 ≤ j → j ≤ k → a j ≠ 0) (φ' : G'.Ω 1 × Fin N → ℂ)
    (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    composeField G₁ G a (h.restrictφ φ') (fun y j => composeField G G' a φ' Ψ' y j) x i =
      composeField G₁ G' a φ' Ψ' x i := by
  classical
  by_cases hx : x ∈ G₁.Ω 1
  · have hxG : x ∈ G.Ω 1 := h₁.mem_Ω1 hx
    rw [composeField_of_mem a _ _ hx i, composeField_of_mem a _ _ hx i,
      composeField_of_mem a φ' Ψ' hxG i]
    have e1 : blockMean G₁ (G₁.layerIndex x) (fun y => svec G (h.restrictφ φ') y i) x =
        blockMean G₁ (G₁.layerIndex x) (fun y => svec G' φ' y i) x := by
      unfold blockMean
      congr 1
      refine Finset.sum_congr rfl fun y hy => ?_
      obtain ⟨hy1, -⟩ := h₁.block_compat hx hy
      exact svec_restrictφ h φ' (h₁.mem_Ω1 hy1) i
    have e2 : blockMean G (G.layerIndex x) (fun y => svec G (h.restrictφ φ') y i) x =
        blockMean G (G.layerIndex x) (fun y => svec G' φ' y i) x := by
      unfold blockMean
      congr 1
      refine Finset.sum_congr rfl fun y hy => ?_
      obtain ⟨hy1, -⟩ := h.block_compat hxG hy
      exact svec_restrictφ h φ' hy1 i
    rw [e1, e2]
    obtain ⟨hn1, hnk, -⟩ := G₁.layerIndex_spec hx
    obtain ⟨hm1, hmk, -⟩ := G.layerIndex_spec hxG
    have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    have hκ : (a (G.layerIndex x) / a (G₁.layerIndex x) *
          (((L : ℝ) ^ G₁.layerIndex x) ^ 2 / ((L : ℝ) ^ G.layerIndex x) ^ 2)) *
        (a (G'.layerIndex x) / a (G.layerIndex x) *
          (((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2)) =
        a (G'.layerIndex x) / a (G₁.layerIndex x) *
          (((L : ℝ) ^ G₁.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2) := by
      have h1 := ha _ hn1 hnk
      have h2 := ha _ hm1 hmk
      field_simp
    have hκC : ((a (G.layerIndex x) / a (G₁.layerIndex x) *
          (((L : ℝ) ^ G₁.layerIndex x) ^ 2 / ((L : ℝ) ^ G.layerIndex x) ^ 2) : ℝ) : ℂ) *
        ((a (G'.layerIndex x) / a (G.layerIndex x) *
          (((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2) : ℝ) : ℂ) =
        ((a (G'.layerIndex x) / a (G₁.layerIndex x) *
          (((L : ℝ) ^ G₁.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2) : ℝ) : ℂ) := by
      rw [← hκ]; push_cast; ring
    rw [← hκC]
    ring
  · by_cases hc : x ∈ collar G₁
    · rw [composeField_of_collar a _ _ hc i, composeField_of_collar a _ _ hc i]
      have hxd : x ∈ dataSites G := by
        by_cases hxG : x ∈ G.Ω 1
        · exact (mem_dataSites G).2 (Or.inl hxG)
        · obtain ⟨-, y, hy, hadj⟩ := (mem_collar G₁).1 hc
          exact (mem_dataSites G).2 (Or.inr (mem_collar_of_adj G (h₁.mem_Ω1 hy) hxG hadj))
      exact barField_compose h a φ' Ψ' hxd i
    · have hd : x ∉ dataSites G₁ := fun h' => by
        rcases (mem_dataSites G₁).1 h' with h' | h'
        · exact hx h'
        · exact hc h'
      rw [composeField_of_not_mem a _ _ hd i, composeField_of_not_mem a _ _ hd i]

end Trans

end Balaban.Localization
