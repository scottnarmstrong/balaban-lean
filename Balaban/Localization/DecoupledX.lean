/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.XCutOperator
public import Balaban.Localization.XCommutator
public import Balaban.Localization.DecoupledMain
public import Balaban.Localization.DecoupledLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The x-variant decoupled Green's operator `G_{k,x,s}(A)`: definitions and algebra (DG7)

LOCALIZATION.md §3.1 (DG7): the cube operators `H_{k,x,z}(A)` are built from the x-variant
`H_{k,x}` of GREEN.md (1.7) by the same cut as `H_z(A)` (`cubeHx = cutXOperator ... (cubeCut ...)`),
the commutators are `K^x_z = χ_z H_{k,x} - H_{k,x} χ_z` (`Kzx`), and

`G*_{x,s}(A) = ∑_z s_z χ_z G^{(z)}_x(A) c_z`, `𝒦_{x,s}(A) = ∑_z s_z K^x_z G^{(z)}_x(A) c_z`,
`G_{k,x,s}(A) = G*_{x,s}(A) (1 - 𝒦_{x,s}(A))⁻¹`.

Here the generating set has `K = k + 1` layers (`Ω_{k+1}` is the top layer), `x ≥ 0`.

* `XSetting`: the standing hypotheses (`DGSetting`, `1 ≤ k`, `a_{k+1} ∈ [1/2, 2]`);
* `cubeHx_isUnit` (NC1), `cubeGx_supp`, `cubeHx_cubeGx`;
* `chiD_xDirichlet_cubeGx`: `χ_z H_{k,x} G^{(z)}_x c_z = χ_z`;
* `inner_of_Kzx_ne_zero`: the support of the commutator;
* `parametrix_x`: `H_{k,x}(A) G*_{x,1}(A) = 1 - 𝒦_{x,1}(A)`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-! ### Definitions -/

section Defs

variable (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)

/-- The x-variant Neumann cube operator `H_{k,x,z}(A)`. -/
noncomputable def cubeHx (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    (q : ℕ × CTorus d L N₁ m₁ (k + 1)) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  cutXOperator G a aT x ν (cubeCut G (intBox q)) α

/-- `G^{(z)}_x(A) c_z`. -/
noncomputable def cubeGx (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    (q : ℕ × CTorus d L N₁ m₁ (k + 1)) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  (cubeHx G a aT x ν α q)⁻¹ * cD G q

/-- The commutator `K^x_z = χ_z H_{k,x} - H_{k,x} χ_z` (independent of the potential). -/
noncomputable def Kzx (a : ℕ → ℝ) (aT x ν : ℝ) (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  chiD G q * xDirichletOperator G a aT x ν 0 - xDirichletOperator G a aT x ν 0 * chiD G q

/-- `G*_{x,s}(A) = ∑_z s_z χ_z G^{(z)}_x(A) c_z`. -/
noncomputable def Gstarx (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  ∑ q ∈ cubeIdx G, sProd G s q • (chiD G q * cubeGx G a aT x ν α q)

/-- `𝒦_{x,s}(A) = ∑_z s_z K^x_z G^{(z)}_x(A) c_z`. -/
noncomputable def Kcalx (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  ∑ q ∈ cubeIdx G, sProd G s q • (Kzx G a aT x ν q * cubeGx G a aT x ν α q)

/-- **The x-variant decoupled Green's operator** `G_{k,x,s}(A) = G*_{x,s}(A) (1 - 𝒦_{x,s}(A))⁻¹`. -/
noncomputable def Gsx (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  Gstarx G a aT x ν α s * (1 - Kcalx G a aT x ν α s)⁻¹

end Defs

/-- The standing hypotheses of DG7: the hypotheses of `DGSetting` for the generating set of level
`k + 1`, `k ≥ 1` and the coefficient `a_{k+1} = aT ∈ [1/2, 2]` of the top layer. -/
structure XSetting (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ) (aT ν : ℝ) :
    Prop where
  dg : DGSetting G a ν
  hk : 1 ≤ k
  haT1 : 1 / 2 ≤ aT
  haT2 : aT ≤ 2

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}
  {α : G.Ω 1 → ℂ}

theorem XSetting.ha (S : XSetting G a aT ν) : IsAdmissibleWeights k a :=
  fun j h1 h2 => S.dg.weights j h1 (by omega)

theorem AdmPot.le_eighth (S : DGSetting G a ν) (hα : AdmPot G α) (y : G.Ω 1) :
    ‖α y‖ ≤ (1 / 8) / (G.spacing y) ^ 2 := by
  refine (hα y).trans ?_
  have hd : 0 < d := by have := S.hd; omega
  have hp := poincareConst_le_half d
  have hs : 0 < (G.spacing (y : CTorus d L N₁ m₁ (k + 1))) ^ 2 := by
    have := spacing_pos G (x := (y : CTorus d L N₁ m₁ (k + 1))); positivity
  have : coerciveConst d ≤ 1 / 4 := by unfold coerciveConst; linarith
  rw [div_le_div_iff₀ (by positivity) hs]
  nlinarith

/-! ### The cut x-variant is block diagonal -/

section Decouple

theorem xAvg_apply_eq_zero_of_sides (a : ℕ → ℝ) (s₁ s₂ : ℝ)
    {Λ : Finset (CTorus d L N₁ m₁ (k + 1))} (hΛ : BlockAligned G Λ)
    {y y' : CTorus d L N₁ m₁ (k + 1)} (hy : y ∈ G.Ω 1) (hside : (y ∈ Λ ↔ ¬ y' ∈ Λ)) :
    xAvgMatrix G a s₁ s₂ y y' = 0 := by
  obtain ⟨hj1, hjK, hyl⟩ := G.layerIndex_spec hy
  set j := G.layerIndex y with hj
  have hLB : ∀ m : ℕ, (∀ z, jBlock d L (N₁ * L ^ m₁) (k + 1) m z =
        jBlock d L (N₁ * L ^ m₁) (k + 1) m y → jBlock d L (N₁ * L ^ m₁) (k + 1) j z =
        jBlock d L (N₁ * L ^ m₁) (k + 1) j y) → layerBlockMatrix G j m y y' = 0 := by
    intro m hnest
    unfold layerBlockMatrix blockProjMatrix
    by_cases hc : y ∈ G.layer j ∧ y' ∈ G.layer j
    · by_cases hb : blockMap (L ^ m) ((N₁ * L ^ m₁) * L ^ (k + 1 - m)) y =
          blockMap (L ^ m) ((N₁ * L ^ m₁) * L ^ (k + 1 - m)) y'
      · exfalso
        have h1 := hnest y' hb.symm
        have := hΛ j hj1 hjK y y' hyl h1
        tauto
      · simp [hb]
    · simp [hc]
  by_cases hjk : j ≤ k
  · rw [xAvg_apply_low G a s₁ s₂ hj1 hjk hyl, hLB j (fun z h => h)]
    simp
  · have hjk' : j = k + 1 := by omega
    rw [hjk'] at hyl hj1 hjK hLB
    rw [xAvg_apply_top G a s₁ s₂ hyl, hLB k, hLB (k + 1) (fun z h => h)]
    · simp
    · intro z h
      exact GeneratingSet.jBlock_succ_eq (by omega) h

theorem cutXFullMatrix_bilinear_decouple {Λ : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hΛ : BlockAligned G Λ) (s : Prop) (a : ℕ → ℝ) (aT x ν : ℝ)
    {g φ : CTorus d L N₁ m₁ (k + 1) → ℝ}
    (hg : ∀ z, g z ≠ 0 → z ∈ G.Ω 1 ∧ (z ∈ Λ ↔ s))
    (hφ : ∀ z, φ z ≠ 0 → z ∈ G.Ω 1 ∧ (z ∈ Λ ↔ ¬ s)) :
    g ⬝ᵥ cutXFullMatrix G a aT x ν (cubeCut G Λ) *ᵥ φ = 0 := by
  unfold cutXFullMatrix
  rw [Matrix.add_mulVec, dotProduct_add, cutLaplacian_bilinear_decouple G s ν hg hφ, zero_add]
  simp only [dotProduct, Matrix.mulVec]
  refine Finset.sum_eq_zero fun z _ => ?_
  by_cases hgz : g z = 0
  · simp [hgz]
  obtain ⟨hzΩ, hzs⟩ := hg z hgz
  have : ∑ z', xAvgMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) z z' * φ z' = 0 := by
    refine Finset.sum_eq_zero fun z' _ => ?_
    by_cases hφz : φ z' = 0
    · simp [hφz]
    obtain ⟨hz'Ω, hz's⟩ := hφ z' hφz
    rw [xAvg_apply_eq_zero_of_sides a _ _ hΛ hzΩ (by tauto), zero_mul]
  rw [this, mul_zero]

theorem cutXFullMatrix_row_decouple {Λ : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hΛ : BlockAligned G Λ) (s : Prop) (a : ℕ → ℝ) (aT x ν : ℝ)
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : y ∈ G.Ω 1) (hys : y ∈ Λ ↔ s)
    {ψ : CTorus d L N₁ m₁ (k + 1) → ℂ} (hψ : ∀ z, ψ z ≠ 0 → z ∈ G.Ω 1 ∧ (z ∈ Λ ↔ ¬ s)) :
    ((cutXFullMatrix G a aT x ν (cubeCut G Λ)).map (algebraMap ℝ ℂ) *ᵥ ψ) y = 0 := by
  have key : ∀ φ : CTorus d L N₁ m₁ (k + 1) → ℝ,
      (∀ z, φ z ≠ 0 → z ∈ G.Ω 1 ∧ (z ∈ Λ ↔ ¬ s)) →
      (cutXFullMatrix G a aT x ν (cubeCut G Λ) *ᵥ φ) y = 0 := by
    intro φ hφ
    have h := cutXFullMatrix_bilinear_decouple hΛ s a aT x ν (g := Pi.single y 1) (φ := φ)
      (fun z hz => by
        have : z = y := by
          by_contra hne
          exact hz (by simp [hne])
        subst this
        exact ⟨hy, hys⟩) hφ
    simpa [single_dotProduct] using h
  apply Complex.ext
  · rw [re_mulVec_map]
    exact (key _ fun z hz => hψ z fun h0 => hz (by simp [h0])).trans (by simp)
  · rw [im_mulVec_map]
    exact (key _ fun z hz => hψ z fun h0 => hz (by simp [h0])).trans (by simp)

theorem cutXOperator_mulVec_apply_of_not_mem {Λ : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hΛ : BlockAligned G Λ) {u : G.Ω 1 → ℂ}
    (hu : ∀ z : G.Ω 1, (z : CTorus d L N₁ m₁ (k + 1)) ∉ Λ → u z = 0) (y : G.Ω 1)
    (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∉ Λ) :
    (cutXOperator G a aT x ν (cubeCut G Λ) α *ᵥ u) y = 0 := by
  have h := cutXOperator_eq G (u := u) (f := cutXOperator G a aT x ν (cubeCut G Λ) α *ᵥ u) rfl y
  rw [hu y hy, mul_zero, add_zero] at h
  rw [← h]
  refine cutXFullMatrix_row_decouple hΛ False a aT x ν y.2 (by simpa using hy) fun z hz => ?_
  by_cases hzΩ : z ∈ G.Ω 1
  · refine ⟨hzΩ, ?_⟩
    simp only [not_false_eq_true, iff_true]
    by_contra hzΛ
    exact hz (by simp only [zeroExt, hzΩ, ↓reduceDIte]; exact hu ⟨z, hzΩ⟩ hzΛ)
  · exact absurd (by simp [zeroExt, hzΩ]) hz

theorem cutXOperator_mulVec_apply_of_mem {Λ : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hΛ : BlockAligned G Λ) {u : G.Ω 1 → ℂ}
    (hu : ∀ z : G.Ω 1, (z : CTorus d L N₁ m₁ (k + 1)) ∈ Λ → u z = 0) (y : G.Ω 1)
    (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Λ) :
    (cutXOperator G a aT x ν (cubeCut G Λ) α *ᵥ u) y = 0 := by
  have h := cutXOperator_eq G (u := u) (f := cutXOperator G a aT x ν (cubeCut G Λ) α *ᵥ u) rfl y
  rw [hu y hy, mul_zero, add_zero] at h
  rw [← h]
  refine cutXFullMatrix_row_decouple hΛ True a aT x ν y.2 (by simpa using hy) fun z hz => ?_
  by_cases hzΩ : z ∈ G.Ω 1
  · refine ⟨hzΩ, ?_⟩
    simp only [not_true_eq_false, iff_false]
    intro hzΛ
    exact hz (by simp only [zeroExt, hzΩ, ↓reduceDIte]; exact hu ⟨z, hzΩ⟩ hzΛ)
  · exact absurd (by simp [zeroExt, hzΩ]) hz

/-- **The Green's function of the x-variant cube is supported in the cube.** -/
theorem cutXOperator_inv_supported {Λ : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hΛ : BlockAligned G Λ) (hU : IsUnit (cutXOperator G a aT x ν (cubeCut G Λ) α))
    {f : G.Ω 1 → ℂ} (hf : ∀ z : G.Ω 1, (z : CTorus d L N₁ m₁ (k + 1)) ∉ Λ → f z = 0)
    {u : G.Ω 1 → ℂ} (hu : cutXOperator G a aT x ν (cubeCut G Λ) α *ᵥ u = f) :
    ∀ z : G.Ω 1, (z : CTorus d L N₁ m₁ (k + 1)) ∉ Λ → u z = 0 := by
  classical
  set H := cutXOperator G a aT x ν (cubeCut G Λ) α with hH
  set w : G.Ω 1 → ℂ := fun z => if (z : CTorus d L N₁ m₁ (k + 1)) ∈ Λ then u z else 0 with hw
  set v : G.Ω 1 → ℂ := fun z => if (z : CTorus d L N₁ m₁ (k + 1)) ∈ Λ then 0 else u z with hv
  have huv : u = w + v := by
    funext z
    by_cases h : (z : CTorus d L N₁ m₁ (k + 1)) ∈ Λ <;> simp [hw, hv, h]
  have hHv : H *ᵥ v = 0 := by
    funext y
    have hsplit : (H *ᵥ u) y = (H *ᵥ w) y + (H *ᵥ v) y := by
      rw [huv, Matrix.mulVec_add]; rfl
    by_cases hy : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Λ
    · exact cutXOperator_mulVec_apply_of_mem hΛ (fun z hz => by simp [hv, hz]) y hy
    · have h1 : (H *ᵥ w) y = 0 :=
        cutXOperator_mulVec_apply_of_not_mem hΛ (fun z hz => by simp [hw, hz]) y hy
      have h2 : (H *ᵥ u) y = 0 := by rw [hu]; exact hf y hy
      rw [h1, h2, zero_add] at hsplit
      exact hsplit.symm
  have hdet : H.det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 hU
    exact this.ne_zero
  have hv0 : v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hHv
  intro z hz
  have := congrFun hv0 z
  simpa [hv, hz] using this

end Decouple


/-! ### The cube operator -/

section Algebra

theorem cutXFullMatrix_mulVec_apply {cut : Finset (Torus d ((N₁ * L ^ m₁) * L ^ (k + 1)) × Fin d)}
    {p : Torus d ((N₁ * L ^ m₁) * L ^ (k + 1))} (hc : NoCutAt cut p) (a : ℕ → ℝ) (aT x ν : ℝ)
    (ψ : Torus d ((N₁ * L ^ m₁) * L ^ (k + 1)) → ℂ) :
    ((cutXFullMatrix G a aT x ν cut).map (algebraMap ℝ ℂ) *ᵥ ψ) p =
      ((xFullMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) ν).map
        (algebraMap ℝ ℂ) *ᵥ ψ) p := by
  apply Complex.ext
  · rw [re_mulVec_map, re_mulVec_map]
    unfold cutXFullMatrix xFullMatrix
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Pi.add_apply, Pi.add_apply,
      cutLaplacian_mulVec_apply hc]
  · rw [im_mulVec_map, im_mulVec_map]
    unfold cutXFullMatrix xFullMatrix
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Pi.add_apply, Pi.add_apply,
      cutLaplacian_mulVec_apply hc]

theorem xDirichlet_row_eq_cutX_row
    {cut : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d)} {y : G.Ω 1}
    (hc : NoCutAt cut (y : CTorus d L N₁ m₁ (k + 1))) (u : G.Ω 1 → ℂ) :
    (xDirichletOperator G a aT x ν α *ᵥ u) y = (cutXOperator G a aT x ν cut α *ᵥ u) y := by
  have h1 := cutXOperator_eq G (a := a) (aT := aT) (x := x) (ν := ν) (cut := ∅) (α := α)
    (u := u) (f := xDirichletOperator G a aT x ν α *ᵥ u) (by rw [cutXOperator_empty]) y
  have h2 := cutXOperator_eq G (a := a) (aT := aT) (x := x) (ν := ν) (cut := cut) (α := α)
    (u := u) (f := cutXOperator G a aT x ν cut α *ᵥ u) rfl y
  rw [cutXFullMatrix_empty] at h1
  rw [cutXFullMatrix_mulVec_apply (G := G) hc a aT x ν] at h2
  rw [← h1, ← h2]

theorem cubeHx_isUnit (S : XSetting G a aT ν) (hα : AdmPot G α) (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx G) :
    IsUnit (cubeHx G a aT x ν α q) :=
  cutXOperator_isUnit G (cubeCut_aligned G (box_blockAligned S.dg.aligned S.dg.cover_sep
    (by have := S.dg.hL; omega) hq)) S.dg.hL S.hk S.dg.mass S.ha S.haT1 S.haT2 hx α
    (AdmPot.le_eighth S.dg hα)

theorem cubeGx_mulVec (q : ℕ × CTorus d L N₁ m₁ (k + 1)) (f : G.Ω 1 → ℂ) :
    cubeGx G a aT x ν α q *ᵥ f = (cubeHx G a aT x ν α q)⁻¹ *ᵥ (cD G q *ᵥ f) := by
  unfold cubeGx
  rw [Matrix.mulVec_mulVec]

theorem cubeGx_mul_cD (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    cubeGx G a aT x ν α q * cD G q = cubeGx G a aT x ν α q := by
  unfold cubeGx
  rw [Matrix.mul_assoc, cD_mul_self]

theorem cubeHx_cubeGx (S : XSetting G a aT ν) (hα : AdmPot G α) (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx G) (f : G.Ω 1 → ℂ) :
    cubeHx G a aT x ν α q *ᵥ (cubeGx G a aT x ν α q *ᵥ f) = cD G q *ᵥ f := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 (cubeHx_isUnit S hα hx hq)
  rw [cubeGx_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- **`G^{(z)}_x(A) c_z f` is supported in the interaction cube.** -/
theorem cubeGx_supp (S : XSetting G a aT ν) (hα : AdmPot G α) (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx G) (f : G.Ω 1 → ℂ) (z : G.Ω 1)
    (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∉ intBox q) :
    (cubeGx G a aT x ν α q *ᵥ f) z = 0 :=
  cutXOperator_inv_supported (box_blockAligned S.dg.aligned S.dg.cover_sep
    (by have := S.dg.hL; omega) hq) (cubeHx_isUnit S hα hx hq)
    (f := cD G q *ᵥ f) (fun w hw => by rw [cD_mulVec]; simp [hw])
    (cubeHx_cubeGx S hα hx hq f) z hz

/-- **`χ_z H_{k,x} G^{(z)}_x c_z = χ_z`.** -/
theorem chiD_xDirichlet_cubeGx (S : XSetting G a aT ν) (hα : AdmPot G α) (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx G) :
    chiD G q * xDirichletOperator G a aT x ν α * cubeGx G a aT x ν α q = chiD G q := by
  refine matrix_ext_mulVec fun f => ?_
  funext y
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, chiD_mulVec, chiD_mulVec]
  by_cases h0 : chi G q y = 0
  · simp [h0]
  · have hin := inner_of_chi_ne_zero S.dg hq y.2 h0
    have hrow := xDirichlet_row_eq_cutX_row (G := G) (a := a) (aT := aT) (x := x) (ν := ν)
      (α := α) (cut := cubeCut G (intBox q)) (y := y) hin.noCut (cubeGx G a aT x ν α q *ᵥ f)
    have h1 := cubeHx_cubeGx S hα hx hq f
    have h2 := congrFun h1 y
    simp only [cD_mulVec, hin.self, ite_true] at h2
    change ((chi G q y : ℝ) : ℂ) *
      (xDirichletOperator G a aT x ν α *ᵥ (cubeGx G a aT x ν α q *ᵥ f)) y = _
    rw [hrow]
    unfold cubeHx at h2
    rw [h2]

end Algebra

/-! ### The commutators -/

section Commutator

theorem Kzx_eq (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    Kzx G a aT x ν q = chiD G q * xDirichletOperator G a aT x ν α -
      xDirichletOperator G a aT x ν α * chiD G q := by
  have hdec : xDirichletOperator G a aT x ν α = xDirichletOperator G a aT x ν 0 +
      Matrix.diagonal α := by
    unfold xDirichletOperator
    simp
  have hc : chiD G q * Matrix.diagonal α = Matrix.diagonal α * chiD G q := by
    unfold chiD
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext z; exact mul_comm _ _
  unfold Kzx
  rw [hdec, mul_add, add_mul, hc]
  abel

theorem Kzx_apply (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ (k + 1))
    (y y' : G.Ω 1) :
    Kzx G a aT x ν q y y' = xDirichletOperator G a aT x ν α y y' *
      (((chi G q y : ℝ) : ℂ) - ((chi G q y' : ℝ) : ℂ)) := by
  rw [Kzx_eq a aT x ν α q]
  unfold chiD
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

theorem Kzx_mulVec_eq_commK (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    (q : ℕ × CTorus d L N₁ m₁ (k + 1)) (u : G.Ω 1 → ℂ) (y : G.Ω 1) :
    (Kzx G a aT x ν q *ᵥ u) y =
      (commK (xDirichletOperator G a aT x ν α) (restrictField G (chiField G q)) *ᵥ
        (fun p : G.Ω 1 × Fin 1 => u p.1)) y := by
  rw [commK_mulVec]
  simp only [Matrix.mulVec, dotProduct, Kzx_apply a aT x ν α q, Finset.univ_unique,
    Finset.sum_singleton]
  refine Finset.sum_congr rfl fun y' _ => ?_
  simp [restrictField, chiField]

theorem LB_ne_zero_blk {K : ℕ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {j m : ℕ}
    {y y' : Torus d ((N₁ * L ^ m₁) * L ^ K)} (h : layerBlockMatrix G j m y y' ≠ 0) :
    y' ∈ G.blk m y := by
  rw [GeneratingSet.mem_blk]
  unfold layerBlockMatrix blockProjMatrix at h
  by_contra hne
  apply h
  have : blockMap (L ^ m) ((N₁ * L ^ m₁) * L ^ (K - m)) y ≠
      blockMap (L ^ m) ((N₁ * L ^ m₁) * L ^ (K - m)) y' := fun h' => hne h'.symm
  simp [this]

theorem xAvg_ne_zero_blk (a : ℕ → ℝ) (s₁ s₂ : ℝ) {y y' : CTorus d L N₁ m₁ (k + 1)}
    (hy : y ∈ G.Ω 1) (h : xAvgMatrix G a s₁ s₂ y y' ≠ 0) :
    y' ∈ G.blk (G.layerIndex y) y := by
  obtain ⟨hj1, hjK, hyl⟩ := G.layerIndex_spec hy
  set j := G.layerIndex y with hj
  by_cases hjk : j ≤ k
  · rw [xAvg_apply_low G a s₁ s₂ hj1 hjk hyl] at h
    exact LB_ne_zero_blk (right_ne_zero_of_mul h)
  · have hjk' : j = k + 1 := by omega
    rw [hjk'] at hyl ⊢
    rw [xAvg_apply_top G a s₁ s₂ hyl] at h
    by_cases h1 : layerBlockMatrix G (k + 1) k y y' = 0
    · rw [h1, mul_zero, zero_add] at h
      exact LB_ne_zero_blk (right_ne_zero_of_mul h)
    · have := LB_ne_zero_blk h1
      rw [GeneratingSet.mem_blk] at this ⊢
      exact GeneratingSet.jBlock_succ_eq (by omega) this

theorem commKx_apply_eq_zero (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) {N : ℕ}
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (s : G.Ω 1 × Fin N → ℂ) (y : G.Ω 1)
    (hstar : ∀ μ : Fin d, φ ((y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1) = φ y ∧
      φ ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1) = φ y)
    (hblk : ∀ z ∈ G.blk (G.layerIndex (y : CTorus d L N₁ m₁ (k + 1))) y, φ z = φ y) :
    (commK (xDirichletOperator G a aT x ν α) (restrictField G φ) *ᵥ s) y = 0 := by
  rw [commK_xOperator_split]
  have h1 : lapTerm G φ s y = 0 := by
    unfold lapTerm
    refine Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun i _ => ?_
    rw [(hstar μ).1, (hstar μ).2]
    ring
  have h2 : ((xAvgMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x)).map
      (algebraMap ℝ ℂ) *ᵥ commArg G φ s y) y = 0 := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hz : xAvgMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) y z = 0
    · simp [hz]
    · have hzb := xAvg_ne_zero_blk a _ _ y.2 hz
      have : commArg G φ s y z = 0 := by
        unfold commArg
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hblk z hzb]; ring
      rw [this, mul_zero]
  rw [h1, h2, add_zero]

/-- **Support of the commutator.** If `K^x_z u (y) ≠ 0` then `y` is an interior point of `□_z`. -/
theorem inner_of_Kzx_ne_zero (S : XSetting G a aT ν) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ cubeIdx G) (u : G.Ω 1 → ℂ) (y : G.Ω 1)
    (h : (Kzx G a aT x ν q *ᵥ u) y ≠ 0) : Inner q y := by
  by_contra hI
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec y.2
  set n := G.layerIndex (y : CTorus d L N₁ m₁ (k + 1)) with hn
  have hz : ∀ z : CTorus d L N₁ m₁ (k + 1),
      ((∃ μ : Fin d, z = (y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1 ∨
        z = (y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1) ∨
        SameCell (L ^ n) (y : CTorus d L N₁ m₁ (k + 1)) z) → chi G q z = 0 := by
    intro z hnear
    by_contra hne
    exact hI (inner_of_near S.dg.cover_sep S.dg.hM (by have := S.dg.hL; omega) hq hn1 hnK hxl
      (inBox_of_chi_ne_zero hne) hnear)
  have hx0 : chi G q (y : CTorus d L N₁ m₁ (k + 1)) = 0 := hz _ (Or.inr (SameCell.refl _ _))
  have e : ∀ z : CTorus d L N₁ m₁ (k + 1), chi G q z = 0 → chiField G q z = fun _ => 0 := by
    intro z hz0; funext i; unfold chiField; rw [hz0]; simp
  apply h
  rw [Kzx_mulVec_eq_commK a aT x ν (0 : G.Ω 1 → ℂ) q u y]
  refine commKx_apply_eq_zero a aT x ν 0 _ y (fun μ => ?_) (fun z hz' => ?_)
  · have h1 := hz _ (Or.inl ⟨μ, Or.inl rfl⟩)
    have h2 := hz _ (Or.inl ⟨μ, Or.inr rfl⟩)
    rw [e _ h1, e _ h2, e _ hx0]; exact ⟨rfl, rfl⟩
  · have hy' := GeneratingSet.mem_blk.1 hz'
    have h1 := hz z (Or.inr (sameCell_of_jBlock_eq hnK hy'.symm))
    rw [e _ h1, e _ hx0]

end Commutator

/-! ### The parametrix identity -/

section Parametrix

theorem parametrix_algebra_x (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    (hχG : ∀ q ∈ cubeIdx G, chiD G q * xDirichletOperator G a aT x ν α *
      cubeGx G a aT x ν α q = chiD G q) (hsum : ∑ q ∈ cubeIdx G, chiD G q = 1) :
    xDirichletOperator G a aT x ν α * Gstarx G a aT x ν α (fun _ => 1) =
      1 - Kcalx G a aT x ν α (fun _ => 1) := by
  have h1 : ∀ q ∈ cubeIdx G, xDirichletOperator G a aT x ν α *
      (chiD G q * cubeGx G a aT x ν α q) =
      chiD G q - Kzx G a aT x ν q * cubeGx G a aT x ν α q := by
    intro q hq
    have e : Kzx G a aT x ν q * cubeGx G a aT x ν α q = chiD G q *
        xDirichletOperator G a aT x ν α * cubeGx G a aT x ν α q -
        xDirichletOperator G a aT x ν α * (chiD G q * cubeGx G a aT x ν α q) := by
      rw [Kzx_eq a aT x ν α q]; noncomm_ring
    rw [e, hχG q hq]; abel
  unfold Gstarx Kcalx
  simp only [sProd, Finset.prod_const_one, one_smul]
  rw [Finset.mul_sum, Finset.sum_congr rfl h1, Finset.sum_sub_distrib, hsum]

/-- **The parametrix identity** `H_{k,x}(A) G*_{x,1}(A) = 1 - 𝒦_{x,1}(A)`. -/
theorem parametrix_x (S : XSetting G a aT ν) (hα : AdmPot G α) (hx : 0 ≤ x) :
    xDirichletOperator G a aT x ν α * Gstarx G a aT x ν α (fun _ => 1) =
      1 - Kcalx G a aT x ν α (fun _ => 1) :=
  parametrix_algebra_x a aT x ν α (fun q hq => chiD_xDirichlet_cubeGx S hα hx hq)
    (sum_chiD (by have := S.dg.hd; omega) (by have := S.dg.hL; omega) S.dg.aligned)

end Parametrix

end Balaban.Localization
