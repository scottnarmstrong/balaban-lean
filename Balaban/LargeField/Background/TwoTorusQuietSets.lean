/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusVars
public import Balaban.LargeField.Operators.Quiet

/-!
# The cube sets of the quiet kernel on two tori

For corresponding localized histories, the sets of cubes `quietA₁ … quietA₄` over which the
characteristic functions of the quiet kernel are multiplied correspond (`CSetCorr`), and so do
the neighbourhoods `Ω^{∼3}`, `(Ω^c)^{∼3}` (`CIff`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField RegionHistory

section Sets

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {M K : ℕ}
  [NeZero M] [NeZero S.L] {cc : Fin S.d → ℤ} {a₁ : LocalHistory S n₁ M K}
  {a₂ : LocalHistory S n₂ M K} {k : ℕ}

theorem pos_cubeSide (j : ℕ) : 0 < S.L ^ j * M :=
  Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) _) (Nat.pos_of_ne_zero (NeZero.ne _))

/-- The cubes of `𝕋_j` inside a set of fine sites correspond when the sets do. -/
theorem cSetCorr_cubeSub (hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1))
    (hnn₂ : ∀ i, i < K → n₂ i = S.L * n₂ (i + 1)) {j : ℕ} (hj : j ≤ K) (hq₁ : 4 ≤ n₁ j)
    (hq₂ : 4 ≤ n₂ j) {X₁ : Set (Torus S.d (M * n₁ K * S.L ^ K))}
    {X₂ : Set (Torus S.d (M * n₂ K * S.L ^ K))} (hX : SetCorr cc X₁ X₂) {E₁ : Set (Torus S.d (n₁ j))}
    {E₂ : Set (Torus S.d (n₂ j))}
    (hE : ∀ y₁ y₂, CCorr cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ j * M) (n₁ j)
      (n₂ j) y₁ y₂ → CubeSub (S := S) (n := n₁) M K j y₁ X₁ → (y₁ ∈ E₁ ↔ y₂ ∈ E₂)) :
    CSetCorr cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ j * M) (n₁ j) (n₂ j)
      {y | CubeSub (S := S) (n := n₁) M K j y X₁ ∧ y ∈ E₁}
      {y | CubeSub (S := S) (n := n₂) M K j y X₂ ∧ y ∈ E₂} :=
  cSetCorr_bsub (pos_cubeSide j) (Balaban.LargeField.fine_eq hnn₁ hj)
    (Balaban.LargeField.fine_eq hnn₂ hj) hq₁ hq₂ hX hE

theorem cSetCorr_cubeSub_plain (hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1))
    (hnn₂ : ∀ i, i < K → n₂ i = S.L * n₂ (i + 1)) {j : ℕ} (hj : j ≤ K) (hq₁ : 4 ≤ n₁ j)
    (hq₂ : 4 ≤ n₂ j) {X₁ : Set (Torus S.d (M * n₁ K * S.L ^ K))}
    {X₂ : Set (Torus S.d (M * n₂ K * S.L ^ K))} (hX : SetCorr cc X₁ X₂) :
    CSetCorr cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ j * M) (n₁ j) (n₂ j)
      {y | CubeSub (S := S) (n := n₁) M K j y X₁} {y | CubeSub (S := S) (n := n₂) M K j y X₂} :=
  cSetCorr_bsub_plain (pos_cubeSide j) (Balaban.LargeField.fine_eq hnn₁ hj)
    (Balaban.LargeField.fine_eq hnn₂ hj) hq₁ hq₂ hX

/-- The `r`-neighbourhoods of the cubes inside corresponding sets correspond (`r ≤ 3`...). -/
theorem ciff_nbhd_cubeSub (hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1))
    (hnn₂ : ∀ i, i < K → n₂ i = S.L * n₂ (i + 1)) {j : ℕ} (hj : j ≤ K) (r : ℕ)
    (hr₁ : 2 * r + 4 ≤ n₁ j) (hr₂ : 2 * r + 4 ≤ n₂ j) {X₁ : Set (Torus S.d (M * n₁ K * S.L ^ K))}
    {X₂ : Set (Torus S.d (M * n₂ K * S.L ^ K))} (hX : SetCorr cc X₁ X₂) :
    CIff cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ j * M) (n₁ j) (n₂ j)
      (nbhd r {y | CubeSub (S := S) (n := n₁) M K j y X₁})
      (nbhd r {y | CubeSub (S := S) (n := n₂) M K j y X₂}) :=
  ccorr_nbhd_iff (Balaban.LargeField.fine_eq hnn₁ hj) (Balaban.LargeField.fine_eq hnn₂ hj) r hr₁
    hr₂ (pos_cubeSide j) (cSetCorr_cubeSub_plain hnn₁ hnn₂ hj (by omega) (by omega) hX)

omit [NeZero M] in
theorem ciff_comap_coarse (hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1))
    (hnn₂ : ∀ i, i < K → n₂ i = S.L * n₂ (i + 1)) (hk : k + 1 ≤ K)
    {E₁ : Set (Torus S.d (n₁ (k + 1)))} {E₂ : Set (Torus S.d (n₂ (k + 1)))}
    (hE : CIff cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ (k + 1) * M) (n₁ (k + 1))
      (n₂ (k + 1)) E₁ E₂) :
    CIff cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ k * M) (n₁ k) (n₂ k)
      {y | blockMap S.L (n₁ (k + 1)) y ∈ E₁} {y | blockMap S.L (n₂ (k + 1)) y ∈ E₂} := by
  intro y₁ y₂ hy
  have h := ccorr_coarsen (Nat.pos_of_ne_zero (NeZero.ne S.L)) (hnn₁ k (by omega))
    (hnn₂ k (by omega)) hy
  have e : S.L ^ k * M * S.L = S.L ^ (k + 1) * M := by ring
  rw [e] at h
  exact hE _ _ h

omit [∀ k, NeZero (n₁ k)] [NeZero M] [NeZero S.L] in
theorem omegaNb_succ_eq (a : LocalHistory S n₁ M K) :
    omegaNb a (k + 1) 3 (k + 1) = nbhd 3 {y | CubeSub (S := S) (n := n₁) M K (k + 1) y (a.Omega k)} := by
  unfold omegaNb
  have h : ¬ (k + 1 = k + 1 + 1) := by omega
  simp only [h, ↓reduceIte]
  rfl

omit [∀ k, NeZero (n₁ k)] [NeZero M] [NeZero S.L] in
theorem omegaCNb_succ_eq (a : LocalHistory S n₁ M K) :
    omegaCNb a 3 (k + 1) =
      nbhd 3 {y | CubeSub (S := S) (n := n₁) M K (k + 1) y (a.Z (k + 1) \ a.Omega k)} := rfl

theorem ciff_omegaNb (hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1))
    (hnn₂ : ∀ i, i < K → n₂ i = S.L * n₂ (i + 1)) (hk : k + 1 ≤ K) (hH : HistCorr cc a₁ a₂)
    (h₁ : 10 ≤ n₁ (k + 1)) (h₂ : 10 ≤ n₂ (k + 1)) :
    CIff cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ (k + 1) * M) (n₁ (k + 1))
      (n₂ (k + 1)) (omegaNb a₁ (k + 1) 3 (k + 1)) (omegaNb a₂ (k + 1) 3 (k + 1)) := by
  rw [omegaNb_succ_eq, omegaNb_succ_eq]
  exact ciff_nbhd_cubeSub hnn₁ hnn₂ hk 3 (by omega) (by omega) (hH.Omega_corr k)

theorem ciff_omegaCNb (hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1))
    (hnn₂ : ∀ i, i < K → n₂ i = S.L * n₂ (i + 1)) (hk : k + 1 ≤ K) (hH : HistCorr cc a₁ a₂)
    (h₁ : 10 ≤ n₁ (k + 1)) (h₂ : 10 ≤ n₂ (k + 1)) :
    CIff cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ (k + 1) * M) (n₁ (k + 1))
      (n₂ (k + 1)) (omegaCNb a₁ 3 (k + 1)) (omegaCNb a₂ 3 (k + 1)) := by
  rw [omegaCNb_succ_eq, omegaCNb_succ_eq]
  exact ciff_nbhd_cubeSub hnn₁ hnn₂ hk 3 (by omega) (by omega)
    ((hH.Z_corr (k + 1)).sdiff_iff (hH.Omega_corr k).setIff)

/-- The cubes of `quietA₁` correspond. -/
theorem cSetCorr_quietA1 (hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1))
    (hnn₂ : ∀ i, i < K → n₂ i = S.L * n₂ (i + 1)) (hk : k + 1 ≤ K) (hH : HistCorr cc a₁ a₂)
    (h₁ : 10 ≤ n₁ (k + 1)) (h₂ : 10 ≤ n₂ (k + 1)) :
    CSetCorr cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ k * M) (n₁ k) (n₂ k)
      (quietA1 a₁ k) (quietA1 a₂ k) := by
  have hn₁ := hnn₁ k (by omega)
  have hn₂ := hnn₂ k (by omega)
  have hL1 : 1 ≤ S.L := Nat.pos_of_ne_zero (NeZero.ne _)
  have h4₁ : 4 ≤ n₁ k := by rw [hn₁]; nlinarith
  have h4₂ : 4 ≤ n₂ k := by rw [hn₂]; nlinarith
  have hE := (ciff_comap_coarse hnn₁ hnn₂ hk (ciff_omegaNb hnn₁ hnn₂ hk hH h₁ h₂)).compl
  exact cSetCorr_cubeSub hnn₁ hnn₂ (by omega) h4₁ h4₂
    ((hH.Z_corr (k + 1)).sdiff_iff (hH.Z_corr k).setIff) (fun y₁ y₂ h _ => hE y₁ y₂ h)

/-- The cubes of `quietA₂` correspond. -/
theorem cSetCorr_quietA2 (hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1))
    (hnn₂ : ∀ i, i < K → n₂ i = S.L * n₂ (i + 1)) (hk : k + 1 ≤ K) (hH : HistCorr cc a₁ a₂)
    (h₁ : 10 ≤ n₁ (k + 1)) (h₂ : 10 ≤ n₂ (k + 1)) :
    CSetCorr cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ (k + 1) * M) (n₁ (k + 1))
      (n₂ (k + 1)) (quietA2 a₁ k) (quietA2 a₂ k) :=
  cSetCorr_cubeSub hnn₁ hnn₂ hk (by omega) (by omega)
    ((hH.Z_corr (k + 1)).sdiff_iff (hH.Omega_corr k).setIff)
    (fun y₁ y₂ h _ => ciff_omegaNb hnn₁ hnn₂ hk hH h₁ h₂ y₁ y₂ h)

/-- The cubes of `quietA₃` correspond. -/
theorem cSetCorr_quietA3 (hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1))
    (hnn₂ : ∀ i, i < K → n₂ i = S.L * n₂ (i + 1)) (hk : k + 1 ≤ K) (hH : HistCorr cc a₁ a₂)
    (h₁ : 10 ≤ n₁ (k + 1)) (h₂ : 10 ≤ n₂ (k + 1)) :
    CSetCorr cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ (k + 1) * M) (n₁ (k + 1))
      (n₂ (k + 1)) (quietA3 a₁ k) (quietA3 a₂ k) :=
  cSetCorr_cubeSub hnn₁ hnn₂ hk (by omega) (by omega) (hH.Omega_corr k)
    (fun y₁ y₂ h _ => ciff_omegaCNb hnn₁ hnn₂ hk hH h₁ h₂ y₁ y₂ h)

/-- The cubes of `quietA₄` correspond. -/
theorem cSetCorr_quietA4 (hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1))
    (hnn₂ : ∀ i, i < K → n₂ i = S.L * n₂ (i + 1)) (hk : k + 1 ≤ K) (hH : HistCorr cc a₁ a₂)
    (h₁ : 10 ≤ n₁ (k + 1)) (h₂ : 10 ≤ n₂ (k + 1)) :
    CSetCorr cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ (k + 1) * M) (n₁ (k + 1))
      (n₂ (k + 1)) (quietA4 a₁ k) (quietA4 a₂ k) :=
  cSetCorr_cubeSub hnn₁ hnn₂ hk (by omega) (by omega) (hH.Z_corr (k + 1))
    (fun y₁ y₂ h _ => (ciff_omegaCNb hnn₁ hnn₂ hk hH h₁ h₂).compl y₁ y₂ h)

end Sets

end Balaban.RootFSpine
