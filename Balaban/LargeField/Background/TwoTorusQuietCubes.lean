/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusChiProd
public import Balaban.LargeField.Background.TwoTorusGauss

/-!
# The cube factors of the quiet kernel on two tori

The four products of characteristic functions of cubes in the quiet kernel
(`χ_k(Z^c_k ∩ Z' ∩ (Ω^{∼3})^c)`, `χ'_{k+1}` on two index sets, `χ_{k+1}(Ω^{∼-3} ∩ Z')`) agree on
two tori at corresponding configurations.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField RegionHistory

section Cubes

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {R : ℕ → ℝ}
  {M K N : ℕ} [NeZero M] [NeZero S.L] {cc : Fin S.d → ℤ} {k : ℕ}

omit [NeZero M] [∀ k, NeZero (n₁ k)] in
theorem n_ge_of_le (hnn : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1)) (hk : k + 1 ≤ K) {j : ℕ}
    (hj : j ≤ k + 1) : n₁ (k + 1) ≤ n₁ j := by
  have := nn_eq_pow hnn j (k + 1 - j) (by omega)
  rw [show j + (k + 1 - j) = k + 1 by omega] at this
  rw [this]
  exact Nat.le_mul_of_pos_right _ (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) _)

omit [∀ k, NeZero (n₁ k)] in
theorem four_le_block (hnn : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1)) (hk : k + 1 ≤ K)
    (h32 : 32 ≤ n₁ (k + 1)) {j : ℕ} (hj : j ≤ k + 1) : 4 ≤ M * n₁ K * S.L ^ (K - j) := by
  have h1 := n_ge_of_le (S := S) hnn hk hj
  have h2 := nn_eq_pow' hnn (show j ≤ K by omega)
  have h3 : 1 ≤ M := Nat.pos_of_ne_zero (NeZero.ne _)
  have h4 : M * n₁ K * S.L ^ (K - j) = M * n₁ j := by rw [h2]; ring
  rw [h4]
  nlinarith

/-- **The margin of a cube of a set contained in the component.** -/
theorem margin_cube (hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1)) (hL : 2 ≤ S.L) (hk : k + 1 ≤ K)
    {j : ℕ} (hj : j ≤ k + 1) {ℓ' : ℕ} {Zc : Set (Torus S.d (n₁ (k + 1)))}
    {X : Set (Torus S.d (M * n₁ K * S.L ^ K))}
    (hX : ∀ x ∈ X, cubeMap n₁ S.L M K (k + 1) x ∈ Zc)
    (hZone : ∀ w, InBox (M * n₁ K * S.L ^ K) ℓ' cc w →
      cubeMap n₁ S.L M K (k + 1) (zcast (M * n₁ K * S.L ^ K) w) ∈ Zc →
        InBoxK (6 * (S.L ^ (k + 1) * M)) (M * n₁ K * S.L ^ K) ℓ' cc w) {w₀ : Fin S.d → ℤ}
    (hw : InBox (M * n₁ K * S.L ^ K) ℓ' cc w₀)
    (hy : CubeSub (S := S) (n := n₁) M K j (zcast (n₁ j) (bidx (S.L ^ j * M) w₀)) X) :
    InBoxK (5 * (S.L ^ j * M) + 2) (M * n₁ K * S.L ^ K) ℓ' cc w₀ := by
  have hs : zcast (M * n₁ K * S.L ^ K) w₀ ∈ X :=
    hy _ (cubeMap_zcast hnn₁ (by omega) w₀)
  have hc := hX _ hs
  refine (hZone w₀ hw hc).mono ?_
  have h1 : S.L ^ j ≤ S.L ^ (k + 1) := Nat.pow_le_pow_right (by omega) hj
  have h2 : S.L ^ j * M ≤ S.L ^ (k + 1) * M := Nat.mul_le_mul_right _ h1
  have h3 : 2 ≤ S.L ^ (k + 1) * M := by
    have : 2 ≤ S.L ^ (k + 1) := by
      calc 2 ≤ S.L := hL
        _ = S.L ^ 1 := (pow_one _).symm
        _ ≤ S.L ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hM : 1 ≤ M := Nat.pos_of_ne_zero (NeZero.ne _)
    nlinarith
  omega

/-- **The `χ_k` factor of the quiet kernel agrees on two tori.** -/
theorem factor_chiK_k (g₁ : Geo S n₁ R M) (g₂ : Geo S n₂ R M) (h1 : g₂.M1 = g₁.M1)
    (h2 : g₂.c = g₁.c) (hL : 2 ≤ S.L) (hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1))
    (hnn₂ : ∀ i, i < K → n₂ i = S.L * n₂ (i + 1)) (hk : k + 1 ≤ K) (cs : OpConsts)
    (hv : EuclideanSpace ℝ (Fin N)) {a₁ : LocalHistory S n₁ M K} {a₂ : LocalHistory S n₂ M K}
    (hH : HistCorr cc a₁ a₂) (h32₁ : 32 ≤ n₁ (k + 1)) (h32₂ : 32 ≤ n₂ (k + 1))
    {Zc₁ : Set (Torus S.d (n₁ (k + 1)))}
    (hZ₁ : ∀ x ∈ a₁.Z (k + 1), cubeMap n₁ S.L M K (k + 1) x ∈ Zc₁)
    (hZone : ∀ w, InBox (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) cc w →
      cubeMap n₁ S.L M K (k + 1) (zcast (M * n₁ K * S.L ^ K) w) ∈ Zc₁ →
        InBoxK (6 * (S.L ^ (k + 1) * M)) (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) cc w)
    {x₁ : NewCfg N a₁ k} {x₂ : NewCfg N a₂ k} (hcfg : CfgCorr cc x₁ x₂) :
    cubeProd (fun y0 => chiK (M1 := g₁.M1) (N₁ := g₁.c * n₁ k) (L := S.L) (q := k) (N := N) cs.aw
        (cs.mu k) (cs.delta k) (fun i => hv i) g₁.c (n₁ k) y0)
      (cubeFin (quietA1 a₁ k))
      (blockCfgOf g₁ hnn₁ (le_refl k) ((Nat.le_succ k).trans hk) (subVarField N x₁ k)) =
    cubeProd (fun y0 => chiK (M1 := g₂.M1) (N₁ := g₂.c * n₂ k) (L := S.L) (q := k) (N := N) cs.aw
        (cs.mu k) (cs.delta k) (fun i => hv i) g₂.c (n₂ k) y0)
      (cubeFin (quietA1 a₂ k))
      (blockCfgOf g₂ hnn₂ (le_refl k) ((Nat.le_succ k).trans hk) (subVarField N x₂ k)) := by
  have hkK : k ≤ K := (Nat.le_succ k).trans hk
  have hn₁ := hnn₁ k (by omega)
  have hn₂ := hnn₂ k (by omega)
  have hL1 : 1 ≤ S.L := Nat.pos_of_ne_zero (NeZero.ne _)
  have h12₁ : 12 ≤ n₁ k := by rw [hn₁]; nlinarith
  have h12₂ : 12 ≤ n₂ k := by rw [hn₂]; nlinarith
  unfold cubeProd cubeFin
  refine cubeProd_chiK_corr g₁ g₂ h1 h2 hL hnn₁ hnn₂ hkK h12₁ h12₂ cs.aw (cs.mu k) (cs.delta k) hv
    (cSetCorr_quietA1 hnn₁ hnn₂ hk hH (by omega) (by omega)) ?_ _ _ ?_
  · intro w₀ hw hy
    exact margin_cube hnn₁ hL hk (j := k) (by omega) hZ₁ hZone hw (fun x hx => (hy.1 x hx).1)
  · intro y₁ y₂ hy
    exact subVarField_corr hH hcfg (fun p₁ p₂ h => newVars_iff p₁ p₂ h) hkK
      (four_le_block hnn₁ hk h32₁ (by omega)) (four_le_block hnn₂ hk h32₂ (by omega)) hy

end Cubes

end Balaban.RootFSpine
