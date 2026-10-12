/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.PsiGeomPath
public import Balaban.SmallField.Def6BridgeDomain
public import Balaban.SmallField.XiProps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# P1 Lemma 3.6 and (3.55)-(3.58): the slice of a small-field datum stays in the data domain

For a datum `(Ψ₀ + Ψ'', h₀ + h')` of `Ψ̃^c(𝔹; δ, ε)` (the landed `InPsiTildeC`, which is the space
`Ψ̄^c_j(δ, ε)` of P1 (3.19)), a polymer `X` in the top layer of `𝔹`, a point `y ∈ X`, and `c = Ψ(y)`,
the *truncated slice*
`S_t(z) = c + t (Ψ(z) - c)` for `z ∈ X`, `S_t(z) = c` for `z ∉ X`
(P1 (3.58): "extended by constants outside `X`", `Ψ_t = Ψ(y) + tδΨ`) lies in `Ψ̃^c(𝔹; δ₀, δ₀)`
as soon as the size of the deviation `|t| sup_X |Ψ - Ψ(y)|` is small against `δ₀`
(`inPsiTildeC_slice`, the analogue of P1 Lemma 3.6, with (3.57) as hypothesis).  By the landed (D2)
`psiTildeC_subset_xiC` it lies in `Ξ^c_j(𝔹; 1, ε_j)` when `(2 K₁ + 2) δ₀ ≤ ε_j`
(`xiDom_slice`).  The deviation bound is the path estimate (3.54), `psi_path_le`.

Constant configurations (`t = 0`) are always in the domain (`inPsiTildeC_const`): the space
`Ψ^c_{j,const}` of P1 p. 125 (the derivative conditions are void).
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField.Def6
  Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

section Defs

open Classical in
/-- The real part of the truncated slice: `Ψ₀` on `X`, the constant `Ψ₀(y)` off `X`. -/
noncomputable def sliceBase (X : Set (CTorus d L N₁ m₁ k)) (Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ)
    (y : CTorus d L N₁ m₁ k) : CTorus d L N₁ m₁ k → Fin N → ℝ :=
  fun z => if z ∈ X then Ψ₀ z else Ψ₀ y

open Classical in
/-- The complex part of the truncated slice over `sliceBase`: with `a = Ψ₀ - Ψ₀(y)`,
`b = Ψ'' - Ψ''(y)` on `X`, it is `Ψ''(y) + t b - (1 - t) a`, and `Ψ''(y)` off `X`; so that
`sliceBase + slicePert = c + t (Ψ - c)` on `X` and `= c` off `X`, `c = Ψ₀(y) + Ψ''(y)`. -/
noncomputable def slicePert (X : Set (CTorus d L N₁ m₁ k)) (Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ)
    (Ψ'' : CTorus d L N₁ m₁ k → Fin N → ℂ) (y : CTorus d L N₁ m₁ k) (t : ℂ) :
    CTorus d L N₁ m₁ k → Fin N → ℂ :=
  fun z => if z ∈ X then
    fun i => Ψ'' y i + t * (Ψ'' z i - Ψ'' y i) - (1 - t) * ((Ψ₀ z i - Ψ₀ y i : ℝ) : ℂ)
  else Ψ'' y

end Defs

section Aux

/-- **Cauchy-Schwarz for the bilinear form**: `‖∑ a_i b_i‖ ≤ |a| |b|`. -/
theorem norm_sum_mul_le_vn (a b : Fin N → ℂ) : ‖∑ i, a i * b i‖ ≤ vn a * vn b := by
  have h1 : ‖∑ i, a i * b i‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_mul _ _).le)
  refine h1.trans ?_
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin N)) (fun i => ‖a i‖)
    (fun i => ‖b i‖)
  have e1 : Real.sqrt (∑ i, ‖a i‖ ^ 2) = vn a := by rw [← vn_sq, Real.sqrt_sq (vn_nonneg _)]
  have e2 : Real.sqrt (∑ i, ‖b i‖ ^ 2) = vn b := by rw [← vn_sq, Real.sqrt_sq (vn_nonneg _)]
  rw [e1, e2] at h2
  exact h2

/-- `|s a + t b| ≤ |s| |a| + |t| |b|`. -/
theorem vn_lin_le (s t : ℂ) (a b : Fin N → ℂ) :
    vn (fun i => s * a i + t * b i) ≤ ‖s‖ * vn a + ‖t‖ * vn b := by
  have h := vn_add' (fun i => s * a i) (fun i => t * b i)
  rw [vn_smul_complex, vn_smul_complex] at h
  exact h

/-- Sites of the data region have layer index at most `j`. -/
theorem layerIndex_le_of_dataSites {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {j : ℕ}
    (hΩ : ∀ i, j < i → G.Ω i = ∅) {x : CTorus d L N₁ m₁ k} (hx : x ∈ dataSites G) :
    G.layerIndex x ≤ j := by
  rcases (mem_dataSites G).1 hx with h1 | h1
  · obtain ⟨-, -, hxl⟩ := G.layerIndex_spec h1
    by_contra h
    have := hΩ (G.layerIndex x) (by omega)
    have h2 := (G.mem_layer.1 hxl).1
    rw [this] at h2; simp at h2
  · have h2 : x ∉ G.Ω 1 := ((mem_collar G).1 h1).1
    rw [layerIndex_of_not_mem G h2]; exact Nat.zero_le _

/-- The weights `ν ℓ(x)²` of the data region are at most `ν L^{2j}`. -/
theorem weight_le_of_dataSites {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {j : ℕ}
    (hΩ : ∀ i, j < i → G.Ω i = ∅) {ν : ℝ} (hν : 0 ≤ ν) {x : CTorus d L N₁ m₁ k}
    (hx : x ∈ dataSites G) :
    ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ ν * ((L : ℝ) ^ j) ^ 2 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  refine mul_le_mul_of_nonneg_left ?_ hν
  exact pow_le_pow_left₀ (by positivity)
    (pow_le_pow_right₀ hL1 (layerIndex_le_of_dataSites hΩ hx)) 2

theorem rn_zero_fun : rn (fun _ : Fin N => (0 : ℝ)) = 0 := by simp [rn]

theorem rn_sub_comm_aux (a b : Fin N → ℝ) :
    rn (fun i => a i - b i) = rn (fun i => b i - a i) := by
  unfold rn
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The expansion `∑ (c + Δ)² - ∑ x² = (∑ c² - ∑ u²) + (∑ u² - ∑ x²) + 2 ∑ c Δ + ∑ Δ²`, bounded. -/
theorem sum_sq_perturb (x u : Fin N → ℝ) (w Δ S : Fin N → ℂ)
    (hS : ∀ i, S i = (u i : ℂ) + w i + Δ i) :
    ‖∑ i, S i * S i - ∑ i, (x i : ℂ) * (x i : ℂ)‖ ≤
      ‖∑ i, ((u i : ℂ) + w i) * ((u i : ℂ) + w i) - ∑ i, (u i : ℂ) * (u i : ℂ)‖ +
        |∑ i, u i ^ 2 - ∑ i, x i ^ 2| + 2 * (rn u + vn w) * vn Δ + vn Δ ^ 2 := by
  set c : Fin N → ℂ := fun i => (u i : ℂ) + w i with hc
  have key : ∑ i, S i * S i - ∑ i, (x i : ℂ) * (x i : ℂ) =
      (∑ i, c i * c i - ∑ i, (u i : ℂ) * (u i : ℂ)) +
      (∑ i, (u i : ℂ) * (u i : ℂ) - ∑ i, (x i : ℂ) * (x i : ℂ)) +
      (2 * ∑ i, c i * Δ i + ∑ i, Δ i * Δ i) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hS i]; simp only [hc]; ring
  have h2 : ‖∑ i, (u i : ℂ) * (u i : ℂ) - ∑ i, (x i : ℂ) * (x i : ℂ)‖ =
      |∑ i, u i ^ 2 - ∑ i, x i ^ 2| := by
    have : ∑ i, (u i : ℂ) * (u i : ℂ) - ∑ i, (x i : ℂ) * (x i : ℂ) =
        ((∑ i, u i ^ 2 - ∑ i, x i ^ 2 : ℝ) : ℂ) := by push_cast; simp [sq]
    rw [this, Complex.norm_real, Real.norm_eq_abs]
  have hcn : vn c ≤ rn u + vn w := by
    have := vn_add' (fun i => (u i : ℂ)) w
    rwa [vn_ofReal] at this
  have h3 : ‖∑ i, c i * Δ i‖ ≤ (rn u + vn w) * vn Δ :=
    (norm_sum_mul_le_vn c Δ).trans (mul_le_mul_of_nonneg_right hcn (vn_nonneg _))
  have h4 : ‖∑ i, Δ i * Δ i‖ ≤ vn Δ ^ 2 := by
    refine (norm_sum_mul_le_vn Δ Δ).trans (le_of_eq (by ring))
  rw [key]
  calc _ ≤ ‖∑ i, c i * c i - ∑ i, (u i : ℂ) * (u i : ℂ)‖ +
        ‖∑ i, (u i : ℂ) * (u i : ℂ) - ∑ i, (x i : ℂ) * (x i : ℂ)‖ +
        (2 * ‖∑ i, c i * Δ i‖ + ‖∑ i, Δ i * Δ i‖) := by
        refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) ?_)
        refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) le_rfl)
        rw [norm_mul]; simp
    _ ≤ _ := by rw [h2]; nlinarith [h3, h4]

end Aux

section Slice

variable {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {j : ℕ}

/-- **The truncated slice lies in `Ψ̃^c(𝔹; δ₀, δ₀)`** (P1 Lemma 3.6 with (3.55)-(3.58)).

Let `(Ψ₀ + Ψ'', h₀ + h')` be in `Ψ̃^c(𝔹; δ, ε)` (`h'` constant, as in P1 (3.14), (3.19)), `X` a union
of `j`-blocks contained in the top layer `j` of `𝔹`, `y ∈ X`, and suppose the field varies on `X`
by at most `Q` from its value at `y`, separately for `Ψ₀` and `Ψ''` (this is (3.54)-(3.55), see
`psi_path_le`).  If `4 δ ≤ δ₀`, `ε ≤ δ₀` and `(1 + 2 |t|) Q ≤ δ₀ / 32` (P1 (3.57)), then the data
`(sliceBase + slicePert t, h₀ + h')` are in `Ψ̃^c(𝔹; δ₀, δ₀)`. -/
theorem inPsiTildeC_slice (hjk : j ≤ k) (hΩ : ∀ i, j < i → G.Ω i = ∅)
    {ν δ ε δ₀ Q : ℝ} (hν : 0 ≤ ν)
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' : CTorus d L N₁ m₁ k → Fin N → ℂ} {h' : Fin N → ℂ}
    (hP : InPsiTildeC G ν δ ε Ψ₀ h₀ Ψ'' (fun _ => h'))
    {X : Set (CTorus d L N₁ m₁ k)} (hXΩ : X ⊆ ↑(G.Ω 1)) (hlayer : ∀ z ∈ X, G.layerIndex z = j)
    (hblock : ∀ z z', jBlock d L (N₁ * L ^ m₁) k j z = jBlock d L (N₁ * L ^ m₁) k j z' →
      z ∈ X → z' ∈ X)
    {y : CTorus d L N₁ m₁ k} (hy : y ∈ X)
    (hpath0 : ∀ z ∈ X, rn (fun i => Ψ₀ z i - Ψ₀ y i) ≤ Q)
    (hpath1 : ∀ z ∈ X, vn (fun i => Ψ'' z i - Ψ'' y i) ≤ Q)
    (hδ : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ δ₀) (hδQ : δ ≤ Q) (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1 / 16)
    (h4δ : 4 * δ ≤ δ₀) (t : ℂ) (hT : (1 + 2 * ‖t‖) * Q ≤ δ₀ / 32) :
    InPsiTildeC G ν δ₀ δ₀ (sliceBase X Ψ₀ y) h₀ (slicePert X Ψ₀ Ψ'' y t) (fun _ => h') := by
  classical
  have h4 : 4 * δ ≤ δ₀ := h4δ
  have hyΩ : y ∈ G.Ω 1 := hXΩ hy
  have hyD : y ∈ dataSites G := (mem_dataSites G).2 (Or.inl hyΩ)
  have hyj : G.layerIndex y = j := hlayer y hy
  have hT0 : 0 ≤ ‖t‖ := norm_nonneg _
  have hQ0 : 0 ≤ Q := by
    have := hpath0 y hy
    simpa [sub_self, rn_zero_fun] using this
  have hQ' : Q ≤ δ₀ / 32 := by nlinarith
  have hTQ : 2 * ‖t‖ * Q ≤ δ₀ / 32 := by nlinarith
  -- constancy on blocks
  have hcst : ∀ z z', jBlock d L (N₁ * L ^ m₁) k j z = jBlock d L (N₁ * L ^ m₁) k j z' → z ∈ X →
      Ψ₀ z' = Ψ₀ z ∧ Ψ'' z' = Ψ'' z := by
    intro z z' h hz
    obtain ⟨h1, hk, hzl⟩ := G.layerIndex_spec (hXΩ hz)
    rw [hlayer z hz] at h1 hk hzl
    exact ⟨hP.layerConst j h1 hk z hzl z' (G.mem_blk.2 h.symm),
      hP.layerConst' j h1 hk z hzl z' (G.mem_blk.2 h.symm)⟩
  have hnot : ∀ z z', jBlock d L (N₁ * L ^ m₁) k j z = jBlock d L (N₁ * L ^ m₁) k j z' →
      z ∉ X → z' ∉ X := fun z z' h hz hz' => hz (hblock z' z h.symm hz')
  have hLC0 : IsLayerConstant G (sliceBase X Ψ₀ y) := by
    refine isLayerConstant_of_jBlock hjk hΩ (fun z z' h => ?_)
    by_cases hz : z ∈ X
    · have hz' := hblock z z' h hz
      simp only [sliceBase, hz, hz', ↓reduceIte]
      exact ((hcst z z' h hz).1).symm
    · have hz' := hnot z z' h hz
      simp only [sliceBase, hz, hz', ↓reduceIte]
  have hLC1 : IsLayerConstant G (slicePert X Ψ₀ Ψ'' y t) := by
    refine isLayerConstant_of_jBlock hjk hΩ (fun z z' h => ?_)
    by_cases hz : z ∈ X
    · have hz' := hblock z z' h hz
      obtain ⟨e1, e2⟩ := hcst z z' h hz
      simp only [slicePert, hz, hz', ↓reduceIte]
      rw [e1, e2]
    · have hz' := hnot z z' h hz
      simp only [slicePert, hz, hz', ↓reduceIte]
  -- the deviation bound
  have hP1 : ∀ z ∈ X, vn (fun i => slicePert X Ψ₀ Ψ'' y t z i - Ψ'' y i) ≤ (1 + 2 * ‖t‖) * Q := by
    intro z hz
    have e : (fun i => slicePert X Ψ₀ Ψ'' y t z i - Ψ'' y i) =
        fun i => t * (Ψ'' z i - Ψ'' y i) + (-(1 - t)) * (((Ψ₀ z i - Ψ₀ y i : ℝ) : ℂ)) := by
      funext i; simp only [slicePert, hz, ↓reduceIte]; ring
    rw [e]
    refine (vn_lin_le _ _ _ _).trans ?_
    rw [vn_ofReal, norm_neg]
    have h1 : ‖1 - t‖ ≤ 1 + ‖t‖ := by
      calc ‖1 - t‖ ≤ ‖(1 : ℂ)‖ + ‖t‖ := norm_sub_le _ _
        _ = 1 + ‖t‖ := by simp
    have h2 := hpath1 z hz
    have h3 := hpath0 z hz
    nlinarith [mul_le_mul h1 h3 (rn_nonneg _) (by linarith), mul_le_mul_of_nonneg_left h2 hT0]
  have hP0 : ∀ z ∈ X, vn (fun i => slicePert X Ψ₀ Ψ'' y t z i - Ψ'' y i) ≤ δ₀ / 32 :=
    fun z hz => (hP1 z hz).trans hT
  have hu1 : ∀ z ∉ X, slicePert X Ψ₀ Ψ'' y t z = Ψ'' y := fun z hz => by
    simp only [slicePert, hz, ↓reduceIte]
  refine
    { layerConst := hLC0
      r1 := ?_, r2 := ?_, r3 := ?_, r4 := ?_
      eps_pos := hδ₀
      layerConst' := hLC1
      hLayerConst' := fun n _ _ x _ x' _ => rfl
      c1 := ?_, c2a := ?_, c2b := ?_, c3a := ?_, c3b := ?_ }
  · -- r1
    intro x x' hxx
    by_cases hx : x ∈ X <;> by_cases hx' : x' ∈ X
    · simp only [sliceBase, hx, hx', ↓reduceIte]
      exact (hP.r1 x x' hxx).trans_le (by linarith)
    · simp only [sliceBase, hx, hx', ↓reduceIte]
      exact lt_of_le_of_lt (hpath0 x hx) (by linarith)
    · simp only [sliceBase, hx, hx', ↓reduceIte]
      rw [rn_sub_comm_aux]
      exact lt_of_le_of_lt (hpath0 x' hx') (by linarith)
    · simp only [sliceBase, hx, hx', sub_self, ↓reduceIte]
      rw [rn_zero_fun]; exact hδ₀
  · -- r2
    intro x hxD
    by_cases hx : x ∈ X
    · simp only [sliceBase, hx, ↓reduceIte]
      exact (hP.r2 x hxD).trans_le (by linarith)
    · simp only [sliceBase, hx, ↓reduceIte]
      exact (hP.r2 y hyD).trans_le (by linarith)
  · -- r3
    intro x hxD
    have hδ2 : δ ^ 2 ≤ δ₀ ^ 2 := pow_le_pow_left₀ hδ.le (by linarith) 2
    by_cases hx : x ∈ X
    · simp only [sliceBase, hx, ↓reduceIte]
      exact (hP.r3 x hxD).trans_le hδ2
    · simp only [sliceBase, hx, ↓reduceIte]
      have h1 := hP.r3 y hyD
      rw [hyj] at h1
      have h2 := weight_le_of_dataSites hΩ hν hxD
      calc _ ≤ ν * ((L : ℝ) ^ j) ^ 2 * |1 - (∑ i, Ψ₀ y i * h₀ i) / rn (Ψ₀ y)| :=
            mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
        _ < δ ^ 2 := h1
        _ ≤ δ₀ ^ 2 := hδ2
  · -- r4
    exact hP.r4.trans_le (pow_le_pow_left₀ hδ.le (by linarith) 2)
  · -- c1
    intro x x' hxx
    by_cases hx : x ∈ X <;> by_cases hx' : x' ∈ X
    · have e : slicePert X Ψ₀ Ψ'' y t x - slicePert X Ψ₀ Ψ'' y t x' =
          fun i => t * (Ψ'' x i - Ψ'' x' i) + (-(1 - t)) * (((Ψ₀ x i - Ψ₀ x' i : ℝ) : ℂ)) := by
        funext i; simp only [slicePert, hx, hx', Pi.sub_apply, ↓reduceIte]; push_cast; ring
      rw [e]
      refine lt_of_le_of_lt ((vn_lin_le _ _ _ _).trans ?_) (show δ₀ / 32 < δ₀ by linarith)
      rw [vn_ofReal, norm_neg]
      have h1 : ‖1 - t‖ ≤ 1 + ‖t‖ := by
        calc ‖1 - t‖ ≤ ‖(1 : ℂ)‖ + ‖t‖ := norm_sub_le _ _
          _ = 1 + ‖t‖ := by simp
      have h2 := (hP.c1 x x' hxx).le
      have h3 := (hP.r1 x x' hxx).le
      have h2' : vn (fun i => Ψ'' x i - Ψ'' x' i) ≤ δ := h2
      nlinarith [mul_le_mul h1 h3 (rn_nonneg _) (by linarith), mul_le_mul_of_nonneg_left h2' hT0]
    · have e : slicePert X Ψ₀ Ψ'' y t x - slicePert X Ψ₀ Ψ'' y t x' =
          fun i => slicePert X Ψ₀ Ψ'' y t x i - Ψ'' y i := by
        funext i; simp only [Pi.sub_apply, hu1 x' hx']
      rw [e]; exact lt_of_le_of_lt (hP0 x hx) (by linarith)
    · have e : slicePert X Ψ₀ Ψ'' y t x - slicePert X Ψ₀ Ψ'' y t x' =
          -(fun i => slicePert X Ψ₀ Ψ'' y t x' i - Ψ'' y i) := by
        funext i; simp only [Pi.sub_apply, Pi.neg_apply, hu1 x hx]; ring
      rw [e, show -(fun i => slicePert X Ψ₀ Ψ'' y t x' i - Ψ'' y i) =
        fun i => -(slicePert X Ψ₀ Ψ'' y t x' i - Ψ'' y i) from rfl, vn_neg]
      exact lt_of_le_of_lt (hP0 x' hx') (by linarith)
    · simp only [hu1 x hx, hu1 x' hx', sub_self]
      rw [show (0 : Fin N → ℂ) = 0 from rfl, vn_zero]; exact hδ₀
  · -- c2a
    intro x hxD
    have hy2 := hP.c2a y hyD
    by_cases hx : x ∈ X
    · have e : slicePert X Ψ₀ Ψ'' y t x =
          fun i => Ψ'' y i + (slicePert X Ψ₀ Ψ'' y t x i - Ψ'' y i) := by funext i; ring
      rw [e]
      refine lt_of_le_of_lt (vn_add' _ _) ?_
      have := hP0 x hx
      linarith
    · rw [hu1 x hx]; linarith
  · -- c2b
    intro x hxD
    by_cases hx : x ∈ X
    · simp only [sliceBase, hx, ↓reduceIte]
      have hS : ∀ i, ((Ψ₀ x i : ℂ) + slicePert X Ψ₀ Ψ'' y t x i) =
          (Ψ₀ y i : ℂ) + Ψ'' y i +
            t * (((Ψ₀ x i - Ψ₀ y i : ℝ) : ℂ) + (Ψ'' x i - Ψ'' y i)) := by
        intro i; simp only [slicePert, hx, ↓reduceIte]; push_cast; ring
      have h1 := sum_sq_perturb (Ψ₀ x) (Ψ₀ y) (Ψ'' y)
        (fun i => t * (((Ψ₀ x i - Ψ₀ y i : ℝ) : ℂ) + (Ψ'' x i - Ψ'' y i)))
        (fun i => (Ψ₀ x i : ℂ) + slicePert X Ψ₀ Ψ'' y t x i) hS
      have hΔ : vn (fun i => t * (((Ψ₀ x i - Ψ₀ y i : ℝ) : ℂ) + (Ψ'' x i - Ψ'' y i))) ≤
          2 * ‖t‖ * Q := by
        rw [vn_smul_complex]
        have := vn_add' (fun i => ((Ψ₀ x i - Ψ₀ y i : ℝ) : ℂ)) (fun i => Ψ'' x i - Ψ'' y i)
        rw [vn_ofReal] at this
        have h2 := hpath0 x hx
        have h3 := hpath1 x hx
        nlinarith [mul_le_mul_of_nonneg_left (this.trans (add_le_add h2 h3)) hT0]
      have hΔ0 := vn_nonneg (fun i => t * (((Ψ₀ x i - Ψ₀ y i : ℝ) : ℂ) + (Ψ'' x i - Ψ'' y i)))
      have hT1 := hP.c2b y hyD
      have hr2y := hP.r2 y hyD
      have hr2x := hP.r2 x hxD
      have hu : |∑ i, Ψ₀ y i ^ 2 - ∑ i, Ψ₀ x i ^ 2| < 2 * δ := by
        rw [abs_lt] at hr2y hr2x ⊢; constructor <;> linarith [hr2y.1, hr2y.2, hr2x.1, hr2x.2]
      have hrn : rn (Ψ₀ y) ≤ 2 := by
        have h := rn_sq_sum (Ψ₀ y)
        have h' : rn (Ψ₀ y) ^ 2 ≤ 4 := by
          rw [h]; rw [abs_lt] at hr2y; linarith [hr2y.2]
        nlinarith [rn_nonneg (Ψ₀ y)]
      have hw : vn (Ψ'' y) ≤ 1 := by
        have := hP.c2a y hyD; linarith
      calc _ ≤ _ := h1
        _ < δ₀ := by
          have hcoef : 2 * (rn (Ψ₀ y) + vn (Ψ'' y)) * vn (fun i => t * (((Ψ₀ x i - Ψ₀ y i : ℝ) : ℂ) +
              (Ψ'' x i - Ψ'' y i))) ≤ 6 * (2 * ‖t‖ * Q) := by
            have : 0 ≤ 2 * ‖t‖ * Q := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hΔ (show 0 ≤ 2 * (rn (Ψ₀ y) + vn (Ψ'' y)) by
              nlinarith [rn_nonneg (Ψ₀ y), vn_nonneg (Ψ'' y)])]
          have hsq : vn (fun i => t * (((Ψ₀ x i - Ψ₀ y i : ℝ) : ℂ) + (Ψ'' x i - Ψ'' y i))) ^ 2 ≤
              (δ₀ / 32) ^ 2 := by
            have : vn (fun i => t * (((Ψ₀ x i - Ψ₀ y i : ℝ) : ℂ) + (Ψ'' x i - Ψ'' y i))) ≤ δ₀ / 32 :=
              hΔ.trans hTQ
            exact pow_le_pow_left₀ hΔ0 this 2
          nlinarith [hT1, hu, hcoef, hsq, h4δ]
    · simp only [sliceBase, hx, hu1 x hx, ↓reduceIte]
      exact hP.c2b y hyD |>.trans_le (by linarith)
  · -- c3a
    intro x hx
    have h := hP.c3a x hx
    have hδ' : δ ^ 2 / ε ≤ δ := by
      rw [div_le_iff₀ (hδ.trans_le hδε)]; nlinarith
    have : δ₀ ^ 2 / δ₀ = δ₀ := by field_simp
    rw [this]
    exact h.trans_le (hδ'.trans (by linarith))
  · -- c3b
    intro x hx
    have hxD : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    have hδ2 : δ ^ 2 ≤ δ₀ ^ 2 := pow_le_pow_left₀ hδ.le (by linarith) 2
    by_cases hxX : x ∈ X
    · simp only [sliceBase, hxX, ↓reduceIte]
      exact (hP.c3b x hx).trans_le hδ2
    · simp only [sliceBase, hxX, ↓reduceIte]
      have h1 := hP.c3b y hyΩ
      rw [hyj] at h1
      have h2 := weight_le_of_dataSites hΩ hν hxD
      calc _ ≤ ν * ((L : ℝ) ^ j) ^ 2 *
            ‖∑ i, ((Ψ₀ y i / rn (Ψ₀ y) : ℝ) : ℂ) * h' i‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ < δ ^ 2 := h1
        _ ≤ δ₀ ^ 2 := hδ2

/-- **The constant configurations of `Ψ^c_{j,const}`** (P1 p. 125): if `(Ψ₀ + Ψ'', h₀ + h')` is in
`Ψ̃^c(𝔹; δ, ε)` and `y` is a site of the top layer `j`, the constant configuration
`(Ψ₀(y), Ψ''(y))` with the same `(h₀, h')` is in `Ψ̃^c(𝔹; δ, ε)`.  (There are no derivative
conditions on constants, and the conditions with the weights `ν ℓ(x)²` are inherited from `y`.) -/
theorem inPsiTildeC_const (hΩ : ∀ i, j < i → G.Ω i = ∅)
    {ν δ ε : ℝ} (hν : 0 ≤ ν) {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' : CTorus d L N₁ m₁ k → Fin N → ℂ} {h' : Fin N → ℂ}
    (hP : InPsiTildeC G ν δ ε Ψ₀ h₀ Ψ'' (fun _ => h'))
    {y : CTorus d L N₁ m₁ k} (hyΩ : y ∈ G.Ω 1) (hyj : G.layerIndex y = j) :
    InPsiTildeC G ν δ ε (fun _ => Ψ₀ y) h₀ (fun _ => Ψ'' y) (fun _ => h') := by
  have hyD : y ∈ dataSites G := (mem_dataSites G).2 (Or.inl hyΩ)
  have hδ0 : 0 < δ := by
    have := hP.r2 y hyD
    exact lt_of_le_of_lt (abs_nonneg _) this
  refine
    { layerConst := fun n _ _ x _ x' _ => rfl
      r1 := fun x x' _ => ?_, r2 := fun x _ => hP.r2 y hyD, r3 := fun x hxD => ?_,
      r4 := hP.r4, eps_pos := hP.eps_pos
      layerConst' := fun n _ _ x _ x' _ => rfl
      hLayerConst' := fun n _ _ x _ x' _ => rfl
      c1 := fun x x' _ => ?_, c2a := fun x _ => hP.c2a y hyD, c2b := fun x _ => ?_,
      c3a := fun x hx => ?_, c3b := fun x hx => ?_ }
  · simp only [sub_self]; rw [rn_zero_fun]; exact hδ0
  · have h1 := hP.r3 y hyD
    rw [hyj] at h1
    calc _ ≤ ν * ((L : ℝ) ^ j) ^ 2 * |1 - (∑ i, Ψ₀ y i * h₀ i) / rn (Ψ₀ y)| :=
          mul_le_mul_of_nonneg_right (weight_le_of_dataSites hΩ hν hxD) (abs_nonneg _)
      _ < δ ^ 2 := h1
  · simp only [sub_self]; rw [show (0 : Fin N → ℂ) = 0 from rfl, vn_zero]; exact hδ0
  · exact hP.c2b y hyD
  · have hxD : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    have h1 := hP.c3a y hyΩ
    rw [hyj] at h1
    calc _ ≤ ν * ((L : ℝ) ^ j) ^ 2 * vn h' :=
          mul_le_mul_of_nonneg_right (weight_le_of_dataSites hΩ hν hxD) (vn_nonneg _)
      _ < _ := h1
  · have hxD : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    have h1 := hP.c3b y hyΩ
    rw [hyj] at h1
    calc _ ≤ ν * ((L : ℝ) ^ j) ^ 2 * ‖∑ i, ((Ψ₀ y i / rn (Ψ₀ y) : ℝ) : ℂ) * h' i‖ :=
          mul_le_mul_of_nonneg_right (weight_le_of_dataSites hΩ hν hxD) (norm_nonneg _)
      _ < _ := h1

end Slice

section ToXi

variable {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {j : ℕ} {a : ℕ → ℝ} {ν : ℝ}

/-- The level `n` of `Ξ^c_n` is monotone: the mass condition `ν L^{2n} | |h₀|² - 1 | < (σε)²` at
level `k` implies it at every level `j ≤ k` (for `ν ≥ 0`). -/
theorem xiC_level_mono {ε : ℝ} (hν : 0 ≤ ν) (hjk : j ≤ k)
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : CTorus d L N₁ m₁ k → Fin N → ℂ}
    (h : XiC G a ν k 1 ε Ψ₀ h₀ Ψ'' h'') : XiC G a ν j 1 ε Ψ₀ h₀ Ψ'' h'' := by
  obtain ⟨hσ, hε, Dr, Dc, ⟨hR, hU, hb⟩, hC, hDc, hbC⟩ := h
  refine ⟨hσ, hε, Dr, Dc, ⟨hR, hU, { hb with hnorm := ?_ }⟩, hC, hDc, hbC⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hw : ν * ((L : ℝ) ^ j) ^ 2 ≤ ν * ((L : ℝ) ^ k) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 hjk) 2) hν
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hw (abs_nonneg _)) hb.hnorm

/-- **(D2) at the level `j`**: a datum of `Ψ̃^c(𝔹; δ, ε)` lies in `Ξ^c_j(𝔹; 1, ε̄)` if
`ε + (2 K₁ + 1) δ ≤ ε̄` (P1 (3.21); the landed `psiTildeC_subset_xiC`, with the level `k` of the
mass condition lowered to `j`). -/
theorem xiDom_of_psiTildeC (H : BgHyp d L k ϱ a ν) (hjk : j ≤ k) {δ ε εb : ℝ} (hδ0 : 0 < δ)
    (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδc : δ ≤ bgC1 d L N)
    (hνε : ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2)
    (hεb : ε + (2 * bgK1 d L N + 1) * δ ≤ εb)
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : CTorus d L N₁ m₁ k → Fin N → ℂ} (hP : InPsiTildeC G ν δ ε Ψ₀ h₀ Ψ'' h'') :
    XiDom G a ν j εb (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) (fun z i => (h₀ i : ℂ) + h'' z i) :=
  ⟨Ψ₀, h₀, Ψ'', h'', fun _ _ => rfl, fun _ _ => rfl,
    xiC_level_mono H.mass hjk (psiTildeC_subset_xiC H hδ0 hδε hε hδc hνε hP hεb)⟩

end ToXi

end Balaban.SmallField
