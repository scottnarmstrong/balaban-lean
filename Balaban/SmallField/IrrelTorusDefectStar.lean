/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusDefectBirthCapMain

/-!
# The filed torus defect with the data on `st₊(y)` only

The filed sum `Σ_{Z ∋ y} (T_Z + Φ_{y,Z})` of the cell label reads the field only at the centre `y`
and at its forward neighbours `y + L^j e_μ` (with the source `hv`), and its bound
`C_R E₀ L^{-(d+α₃)(k-j)}` (`norm_filed_le_power`, `norm_filed_le_power_birth`,
`norm_filed_le_power_birth_cap`) depends on the data only through `Λ`.  So the data hypothesis is
needed on `st₊(y)` only: the corollaries `…_star` take the point properties at `y` and the first
differences `‖Ψ(y + L^j e_μ) - Ψ(y)‖ ≤ δ`, with `(2 + 5N) δ ≤ min(Λ r_j, 1/4)`.

* `dataHypAniso_of_near`: a field within `δ` of its value at the origin (with the point
  properties there) satisfies `DataHypAniso` on all of `ℤ^d` with `σ = 1`, `ε = (2 + 5N) δ`,
  `K₂ = 4 δ`;
* `starExt j y Ψ`: the field equal to `Ψ` on `st₊(y)` and to `Ψ(y)` elsewhere.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Metric Set Filter

section Near

variable {d N : ℕ}

/-- The second difference of four vectors within `δ` of a common point is at most `4 δ`. -/
theorem norm_sec_le_of_near {δ : ℝ} {a b c e p : Spin N} (ha : ‖a - p‖ ≤ δ) (hb : ‖b - p‖ ≤ δ)
    (hc : ‖c - p‖ ≤ δ) (he : ‖e - p‖ ≤ δ) : ‖a - b - c + e‖ ≤ 4 * δ := by
  have h : a - b - c + e = (a - p) - (b - p) - (c - p) + (e - p) := by abel
  rw [h]
  have h1 := norm_add_le ((a - p) - (b - p) - (c - p)) (e - p)
  have h2 := norm_sub_le ((a - p) - (b - p)) (c - p)
  have h3 := norm_sub_le (a - p) (b - p)
  linarith

/-- **A field near its value at the origin satisfies the data hypothesis on all of `ℤ^d`**: if
`‖φ(s) - φ(0)‖ ≤ δ ≤ 1` for every `s`, with the point properties at the origin at the size `δ`,
then `DataHypAniso` holds with `σ = 1`, `ε = (2 + 5N) δ` and `K₂ = 4 δ`. -/
theorem dataHypAniso_of_near {Dom : Set ((Site d → Spin N) × Spin N)} {ν δ : ℝ}
    {φ : Site d → Spin N} {b : Spin N} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hnear : ∀ s, ‖φ s - φ 0‖ ≤ δ)
    (hsq0 : ‖dot (φ 0) (φ 0) - 1‖ ≤ δ) (hbdd0 : ‖φ 0‖ ≤ 2)
    (hbc : ‖b - (ν : ℂ) • φ 0‖ ≤ δ) (hbl : ‖vInv φ b - ν‖ ≤ δ ^ 2)
    (hmem : (φ, b) ∈ Dom) (hmemc : ((fun _ => φ 0), b) ∈ Dom) :
    DataHypAniso Dom ν 1 ((2 + 5 * N) * δ) (4 * δ) φ b := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hC1 : (1 : ℝ) ≤ 2 + 5 * N := by linarith
  have hCδ : δ ≤ (2 + 5 * N) * δ := by nlinarith
  refine ⟨⟨by positivity, fun x => ?_, hbdd0, fun x μ => ?_, ?_, fun x μ μ' => ?_, hmem, hmemc⟩,
    ?_⟩
  · -- (Σ1): `dot a a - dot p p = dot (a - p) a + dot p (a - p)`
    set p := φ 0
    have hid : dot (φ x) (φ x) - 1 = (dot p p - 1) + (dot (φ x - p) (φ x) + dot p (φ x - p)) := by
      unfold dot
      simp only [Pi.sub_apply]
      rw [← sub_eq_zero]
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
      ring
    have hx : ‖φ x‖ ≤ 3 := by
      have h1 : ‖φ x‖ ≤ ‖φ x - p‖ + ‖p‖ := by
        calc ‖φ x‖ = ‖(φ x - p) + p‖ := by abel_nf
          _ ≤ ‖φ x - p‖ + ‖p‖ := norm_add_le _ _
      linarith [hnear x]
    have t1 := norm_dot_le (φ x - p) (φ x)
    have t2 := norm_dot_le p (φ x - p)
    have hxp := hnear x
    rw [hid]
    calc ‖(dot p p - 1) + (dot (φ x - p) (φ x) + dot p (φ x - p))‖
        ≤ ‖dot p p - 1‖ + (‖dot (φ x - p) (φ x)‖ + ‖dot p (φ x - p)‖) :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ δ + (N * (δ * 3) + N * (2 * δ)) := by
          gcongr
          · exact t1.trans (mul_le_mul_of_nonneg_left
              (mul_le_mul hxp hx (norm_nonneg _) hδ0) hN0)
          · exact t2.trans (mul_le_mul_of_nonneg_left
              (mul_le_mul hbdd0 hxp (norm_nonneg _) (by norm_num)) hN0)
      _ ≤ 1 ^ 2 * ((2 + 5 * N) * δ) := by nlinarith
  · -- the first differences
    have h := norm_sub_le (φ (x + Pi.single μ 1) - φ 0) (φ x - φ 0)
    have e : φ (x + Pi.single μ 1) - φ 0 - (φ x - φ 0) = φ (x + Pi.single μ 1) - φ x := by abel
    rw [e] at h
    have := hnear (x + Pi.single μ 1)
    have := hnear x
    nlinarith
  · calc ‖b - (ν : ℂ) • φ 0‖ ≤ δ := hbc
      _ ≤ 1 ^ 2 * ((2 + 5 * N) * δ) := by rw [one_pow, one_mul]; exact hCδ
  · exact norm_sec_le_of_near (hnear _) (hnear _) (hnear _) (hnear _)
  · calc ‖vInv φ b - ν‖ ≤ δ ^ 2 := hbl
      _ ≤ 1 ^ 2 * ((2 + 5 * N) * δ) ^ 2 := by
          rw [one_pow, one_mul]; exact pow_le_pow_left₀ hδ0 hCδ 2

end Near

section Star

variable {d L N₁ m₁ k N : ℕ}

open Classical in
/-- The field equal to `Ψ` on `st₊(y) = {y} ∪ {y + L^j e_μ}` and to `Ψ(y)` elsewhere. -/
noncomputable def starExt (j : ℕ) (y : CTorus d L N₁ m₁ k) (Ψ : Fld d L N₁ m₁ k N) :
    Fld d L N₁ m₁ k N := fun z =>
  if ∃ μ : Fin d, z = y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k) then Ψ z else Ψ y

theorem starExt_self (j : ℕ) (y : CTorus d L N₁ m₁ k) (Ψ : Fld d L N₁ m₁ k N) :
    starExt j y Ψ y = Ψ y := by
  unfold starExt; split_ifs <;> rfl

theorem starExt_star (j : ℕ) (y : CTorus d L N₁ m₁ k) (Ψ : Fld d L N₁ m₁ k N) (μ : Fin d) :
    starExt j y Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) =
      Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) := by
  unfold starExt
  split_ifs with h
  · rfl
  · exact absurd ⟨μ, rfl⟩ h

theorem starExt_near (j : ℕ) (y : CTorus d L N₁ m₁ k) (Ψ : Fld d L N₁ m₁ k N) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hgrad : ∀ μ : Fin d,
      ‖Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ y‖ ≤ δ)
    (z : CTorus d L N₁ m₁ k) : ‖starExt j y Ψ z - Ψ y‖ ≤ δ := by
  unfold starExt
  split_ifs with h
  · obtain ⟨μ, rfl⟩ := h
    exact hgrad μ
  · simpa using hδ

theorem starExt_ibase_zero (j : ℕ) (y : CTorus d L N₁ m₁ k) (Ψ : Fld d L N₁ m₁ k N) :
    starExt j y Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (0 : Site d)) = Ψ y := by
  rw [ibase_zero, add_zero, starExt_self]

end Star

section Filed

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ}
  {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

open Classical in
/-- **`norm_filed_le_power` with the data on `st₊(y)` only**: the filed sum reads `Ψ` only at `y` and at
the `y + L^j e_μ` (and the source `hv`), so the data hypothesis is needed there only — the point
properties at `y` and the first differences `‖Ψ(y + L^j e_μ) - Ψ(y)‖ ≤ δ`, with
`(2 + 5N) δ ≤ min(Λ r_j, 1/4)`.  Proof: `norm_filed_le_power` at the field `starExt j y Ψ` (equal to `Ψ` on
`st₊(y)` and to `Ψ(y)` elsewhere), whose pulled-back datum satisfies `DataHypAniso` on all of
`ℤ^d` with `σ = 1`, `ε = (2 + 5N) δ`, `K₂ = 4 δ` (`dataHypAniso_of_near`). -/
theorem norm_filed_le_power_star
    (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {N₁ : ℕ} [NeZero N₁] (hN : L ^ P.m₀ ∣ N₁)
    {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    (Ψ : Fld d L N₁ m₁ k N) (hv : Fin N → ℂ)
    {δ Λ : ℝ} (hδ : 0 < δ) (hδΛ : (2 + 5 * N) * δ ≤ Λ * anisoRadius d L N P j)
    (hδτ : (2 + 5 * N) * δ ≤ 1 / 4)
    (hsq0 : ‖dot (Ψ y) (Ψ y) - 1‖ ≤ δ) (hbdd0 : ‖Ψ y‖ ≤ 2)
    (hgrad : ∀ μ : Fin d,
      ‖Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ y‖ ≤ δ)
    (hbc : ‖((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv - ((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • Ψ y‖ ≤ δ)
    (hbl : ‖dot (Ψ y) (((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv) / sqrtC (dot (Ψ y) (Ψ y)) - nuIdeal L k (Rg.ν k) j‖ ≤ δ ^ 2) :
    ‖∑ᶠ Z ∈ polysAt P.m₀ j y,
        (let e : Fld d L N₁ m₁ k N := constFld (Pi.single i₀ 1)
       let blk : Set (CTorus d L N₁ m₁ k) → Finset (CTorus d L N₁ m₁ k) := fun Z' =>
         Finset.univ.filter fun x => Aligned (L ^ j) x ∧ x ∈ Z'
       let u : ℂ := sqrtC (dot (Ψ y) (Ψ y))
       let dΨ : Fin d → Fin N → ℂ := fun μ =>
         Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ y
       let g : Fin d → Fin d → ℂ := fun μ μ' =>
         dot (dΨ μ) (dΨ μ') - dot (Ψ y) (dΨ μ) * dot (Ψ y) (dΨ μ') /
           dot (Ψ y) (Ψ y)
       let lift : CTorus d L N₁ m₁ k → Fin d → ℂ := fun z μ =>
         ((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) μ : ℤ) : ℂ)
       let a : Set (CTorus d L N₁ m₁ k) → CTorus d L N₁ m₁ k → ℂ := fun Z' x =>
         fderiv ℂ (fun Ψ' => (Tm N₁).E j y Z' Ψ' e) e (blockDir L j x i₀)
       (Tm N₁).E j y Z e e + (u - 1) * ∑ x ∈ blk Z, a Z x
             + (dot (Ψ y) ((constFld hv : Fld d L N₁ m₁ k N) y) / u - 1) *
               fderiv ℂ (fun h' => (Tm N₁).E j y Z e h') e e
             - (1 / 4 : ℂ) * ∑ μ, ∑ μ', g μ μ' * ∑ x ∈ blk Z, ∑ x' ∈ blk Z,
                 D2 (fun Ψ' => (Tm N₁).E j y Z Ψ' e) e (blockDir L j x i₁)
                   (blockDir L j x' i₁) *
                   ((lift x μ - lift x' μ) * (lift x μ' - lift x' μ')))‖ ≤
      (2 * (24 * Real.exp 1 * (16 * (1 + Λ * (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) + Λ ^ 2 + (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (2 * diamA d L P.m₀ m₁) ^ 2 * (N * (N * 40 * Λ) ^ 2))) * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2)) * (Real.exp ((4 * (((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ)) + 4) / (8 * (diamA d L P.m₀ m₁)) + 1 / 2) * ((((d : ℝ) + (1 - 2 * P.γ - P.α₁))) / (Real.exp 1 * (((L : ℝ) ^ (P.m₀ + m₁)) / (8 * (diamA d L P.m₀ m₁))))) ^ (((d : ℝ) + (1 - 2 * P.γ - P.α₁)))))) * P.E₀ *
        (((L : ℝ) ^ (k - j)) ^ (-(((d : ℝ) + (1 - 2 * P.γ - P.α₁))))) := by
  classical
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hδ1 : δ ≤ 1 := by nlinarith
  have hφ0 := starExt_ibase_zero (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y Ψ
  refine (le_of_eq ?_).trans (norm_filed_le_power (σ := 1) (ε := (2 + 5 * N) * δ)
    (K₂ := 4 * δ) (Λ := Λ)
    hF hn hne hN hy (starExt j y Ψ) hv one_pos le_rfl (by positivity) hδΛ
    (by rw [one_pow, one_mul]; exact hδτ) (fun {Dom} hm _ => ?_) (fun x μ μ' => ?_))
  · simp only [starExt_self, starExt_star]
  · refine dataHypAniso_of_near hδ.le hδ1 ?_ ?_ ?_ ?_ ?_ hm.1 hm.2
    · intro s
      rw [hφ0]
      exact starExt_near j y Ψ hδ.le hgrad _
    · rw [hφ0]; exact hsq0
    · rw [hφ0]; exact hbdd0
    · rw [hφ0]; exact hbc
    · simp only [vInv, uInv, hφ0]; exact hbl
  · exact norm_sec_le_of_near (p := Ψ y) (starExt_near j y Ψ hδ.le hgrad _)
      (starExt_near j y Ψ hδ.le hgrad _) (starExt_near j y Ψ hδ.le hgrad _) (starExt_near j y Ψ hδ.le hgrad _)

open Classical in
/-- **`norm_filed_le_power_birth` with the data on `st₊(y)` only**: the filed sum reads `Ψ` only at `y` and at
the `y + L^j e_μ` (and the source `hv`), so the data hypothesis is needed there only — the point
properties at `y` and the first differences `‖Ψ(y + L^j e_μ) - Ψ(y)‖ ≤ δ`, with
`(2 + 5N) δ ≤ min(Λ r_j, 1/4)`.  Proof: `norm_filed_le_power_birth` at the field `starExt j y Ψ` (equal to `Ψ` on
`st₊(y)` and to `Ψ(y)` elsewhere), whose pulled-back datum satisfies `DataHypAniso` on all of
`ℤ^d` with `σ = 1`, `ε = (2 + 5N) δ`, `K₂ = 4 δ` (`dataHypAniso_of_near`). -/
theorem norm_filed_le_power_birth_star
    (hF : IsSFFamily2 P Rg β a (birthXiDom P Rg a) Tm ρd Ek)
    (hcap : physMass L j (Rg.ν j) ≤ P.νbar * ((L : ℝ) ^ k)⁻¹ ^ 2)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {N₁ : ℕ} [NeZero N₁] (hN : L ^ P.m₀ ∣ N₁)
    {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    (Ψ : Fld d L N₁ m₁ k N) (hv : Fin N → ℂ)
    {δ Λ : ℝ} (hδ : 0 < δ) (hδΛ : (2 + 5 * N) * δ ≤ Λ * anisoRadius d L N P j)
    (hδτ : (2 + 5 * N) * δ ≤ 1 / 4)
    (hsq0 : ‖dot (Ψ y) (Ψ y) - 1‖ ≤ δ) (hbdd0 : ‖Ψ y‖ ≤ 2)
    (hgrad : ∀ μ : Fin d,
      ‖Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ y‖ ≤ δ)
    (hbc : ‖((Rg.ν j : ℝ) : ℂ) • hv - ((Rg.ν j : ℝ) : ℂ) • Ψ y‖ ≤ δ)
    (hbl : ‖dot (Ψ y) (((Rg.ν j : ℝ) : ℂ) • hv) / sqrtC (dot (Ψ y) (Ψ y)) - Rg.ν j‖ ≤ δ ^ 2) :
    ‖∑ᶠ Z ∈ polysAt P.m₀ j y,
        (let e : Fld d L N₁ m₁ k N := constFld (Pi.single i₀ 1)
       let blk : Set (CTorus d L N₁ m₁ k) → Finset (CTorus d L N₁ m₁ k) := fun Z' =>
         Finset.univ.filter fun x => Aligned (L ^ j) x ∧ x ∈ Z'
       let u : ℂ := sqrtC (dot (Ψ y) (Ψ y))
       let dΨ : Fin d → Fin N → ℂ := fun μ =>
         Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ y
       let g : Fin d → Fin d → ℂ := fun μ μ' =>
         dot (dΨ μ) (dΨ μ') - dot (Ψ y) (dΨ μ) * dot (Ψ y) (dΨ μ') /
           dot (Ψ y) (Ψ y)
       let lift : CTorus d L N₁ m₁ k → Fin d → ℂ := fun z μ =>
         ((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) μ : ℤ) : ℂ)
       let a : Set (CTorus d L N₁ m₁ k) → CTorus d L N₁ m₁ k → ℂ := fun Z' x =>
         fderiv ℂ (fun Ψ' => (Tm N₁).E j y Z' Ψ' e) e (blockDir L j x i₀)
       (Tm N₁).E j y Z e e + (u - 1) * ∑ x ∈ blk Z, a Z x
             + (dot (Ψ y) ((constFld hv : Fld d L N₁ m₁ k N) y) / u - 1) *
               fderiv ℂ (fun h' => (Tm N₁).E j y Z e h') e e
             - (1 / 4 : ℂ) * ∑ μ, ∑ μ', g μ μ' * ∑ x ∈ blk Z, ∑ x' ∈ blk Z,
                 D2 (fun Ψ' => (Tm N₁).E j y Z Ψ' e) e (blockDir L j x i₁)
                   (blockDir L j x' i₁) *
                   ((lift x μ - lift x' μ) * (lift x μ' - lift x' μ')))‖ ≤
      (2 * (24 * Real.exp 1 * (16 * (1 + Λ * (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) + Λ ^ 2 + (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (2 * diamA d L P.m₀ m₁) ^ 2 * (N * (N * 40 * Λ) ^ 2))) * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2)) * (Real.exp ((4 * (((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ)) + 4) / (8 * (diamA d L P.m₀ m₁)) + 1 / 2) * ((((d : ℝ) + (1 - 2 * P.γ - P.α₁))) / (Real.exp 1 * (((L : ℝ) ^ (P.m₀ + m₁)) / (8 * (diamA d L P.m₀ m₁))))) ^ (((d : ℝ) + (1 - 2 * P.γ - P.α₁)))))) * P.E₀ *
        (((L : ℝ) ^ (k - j)) ^ (-(((d : ℝ) + (1 - 2 * P.γ - P.α₁))))) := by
  classical
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hδ1 : δ ≤ 1 := by nlinarith
  have hφ0 := starExt_ibase_zero (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y Ψ
  refine (le_of_eq ?_).trans (norm_filed_le_power_birth (σ := 1) (ε := (2 + 5 * N) * δ)
    (K₂ := 4 * δ) (Λ := Λ)
    hF hcap hn hne hN hy (starExt j y Ψ) hv one_pos le_rfl (by positivity) hδΛ
    (by rw [one_pow, one_mul]; exact hδτ) (fun {Dom} hm _ => ?_) (fun x μ μ' => ?_))
  · simp only [starExt_self, starExt_star]
  · refine dataHypAniso_of_near hδ.le hδ1 ?_ ?_ ?_ ?_ ?_ hm.1 hm.2
    · intro s
      rw [hφ0]
      exact starExt_near j y Ψ hδ.le hgrad _
    · rw [hφ0]; exact hsq0
    · rw [hφ0]; exact hbdd0
    · rw [hφ0]; exact hbc
    · simp only [vInv, uInv, hφ0]; exact hbl
  · exact norm_sec_le_of_near (p := Ψ y) (starExt_near j y Ψ hδ.le hgrad _)
      (starExt_near j y Ψ hδ.le hgrad _) (starExt_near j y Ψ hδ.le hgrad _) (starExt_near j y Ψ hδ.le hgrad _)

open Classical in
/-- **`norm_filed_le_power_birth_cap` with the data on `st₊(y)` only**: the filed sum reads `Ψ` only at `y` and at
the `y + L^j e_μ` (and the source `hv`), so the data hypothesis is needed there only — the point
properties at `y` and the first differences `‖Ψ(y + L^j e_μ) - Ψ(y)‖ ≤ δ`, with
`(2 + 5N) δ ≤ min(Λ r_j, 1/4)`.  Proof: `norm_filed_le_power_birth_cap` at the field `starExt j y Ψ` (equal to `Ψ` on
`st₊(y)` and to `Ψ(y)` elsewhere), whose pulled-back datum satisfies `DataHypAniso` on all of
`ℤ^d` with `σ = 1`, `ε = (2 + 5N) δ`, `K₂ = 4 δ` (`dataHypAniso_of_near`). -/
theorem norm_filed_le_power_birth_cap_star
    (hF : IsSFFamily2 P Rg β a (birthXiDom P Rg a) Tm ρd Ek)
    (hνbar : Real.exp 2 * P.νbar ≤ 7 / 8 * ((L : ℝ) ^ 2)⁻¹)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {N₁ : ℕ} [NeZero N₁] (hN : L ^ P.m₀ ∣ N₁)
    {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    (Ψ : Fld d L N₁ m₁ k N) (hv : Fin N → ℂ)
    {δ Λ : ℝ} (hδ : 0 < δ) (hδΛ : (2 + 5 * N) * δ ≤ Λ * anisoRadius d L N P j)
    (hδτ : (2 + 5 * N) * δ ≤ 1 / 4)
    (hsq0 : ‖dot (Ψ y) (Ψ y) - 1‖ ≤ δ) (hbdd0 : ‖Ψ y‖ ≤ 2)
    (hgrad : ∀ μ : Fin d,
      ‖Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ y‖ ≤ δ)
    (hbc : ‖((Rg.ν j : ℝ) : ℂ) • hv - ((Rg.ν j : ℝ) : ℂ) • Ψ y‖ ≤ δ)
    (hbl : ‖dot (Ψ y) (((Rg.ν j : ℝ) : ℂ) • hv) / sqrtC (dot (Ψ y) (Ψ y)) - Rg.ν j‖ ≤ δ ^ 2) :
    ‖∑ᶠ Z ∈ polysAt P.m₀ j y,
        (let e : Fld d L N₁ m₁ k N := constFld (Pi.single i₀ 1)
       let blk : Set (CTorus d L N₁ m₁ k) → Finset (CTorus d L N₁ m₁ k) := fun Z' =>
         Finset.univ.filter fun x => Aligned (L ^ j) x ∧ x ∈ Z'
       let u : ℂ := sqrtC (dot (Ψ y) (Ψ y))
       let dΨ : Fin d → Fin N → ℂ := fun μ =>
         Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ y
       let g : Fin d → Fin d → ℂ := fun μ μ' =>
         dot (dΨ μ) (dΨ μ') - dot (Ψ y) (dΨ μ) * dot (Ψ y) (dΨ μ') /
           dot (Ψ y) (Ψ y)
       let lift : CTorus d L N₁ m₁ k → Fin d → ℂ := fun z μ =>
         ((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) μ : ℤ) : ℂ)
       let a : Set (CTorus d L N₁ m₁ k) → CTorus d L N₁ m₁ k → ℂ := fun Z' x =>
         fderiv ℂ (fun Ψ' => (Tm N₁).E j y Z' Ψ' e) e (blockDir L j x i₀)
       (Tm N₁).E j y Z e e + (u - 1) * ∑ x ∈ blk Z, a Z x
             + (dot (Ψ y) ((constFld hv : Fld d L N₁ m₁ k N) y) / u - 1) *
               fderiv ℂ (fun h' => (Tm N₁).E j y Z e h') e e
             - (1 / 4 : ℂ) * ∑ μ, ∑ μ', g μ μ' * ∑ x ∈ blk Z, ∑ x' ∈ blk Z,
                 D2 (fun Ψ' => (Tm N₁).E j y Z Ψ' e) e (blockDir L j x i₁)
                   (blockDir L j x' i₁) *
                   ((lift x μ - lift x' μ) * (lift x μ' - lift x' μ')))‖ ≤
      (2 * (24 * Real.exp 1 * (16 * (1 + Λ * (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) + Λ ^ 2 + (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (2 * diamA d L P.m₀ m₁) ^ 2 * (N * (N * 40 * Λ) ^ 2))) * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2)) * (Real.exp ((4 * (((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ)) + 4) / (8 * (diamA d L P.m₀ m₁)) + 1 / 2) * ((((d : ℝ) + (1 - 2 * P.γ - P.α₁))) / (Real.exp 1 * (((L : ℝ) ^ (P.m₀ + m₁)) / (8 * (diamA d L P.m₀ m₁))))) ^ (((d : ℝ) + (1 - 2 * P.γ - P.α₁)))))) * P.E₀ *
        (((L : ℝ) ^ (k - j)) ^ (-(((d : ℝ) + (1 - 2 * P.γ - P.α₁))))) := by
  classical
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hδ1 : δ ≤ 1 := by nlinarith
  have hφ0 := starExt_ibase_zero (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y Ψ
  refine (le_of_eq ?_).trans (norm_filed_le_power_birth_cap (σ := 1) (ε := (2 + 5 * N) * δ)
    (K₂ := 4 * δ) (Λ := Λ)
    hF hνbar hn hne hN hy (starExt j y Ψ) hv one_pos le_rfl (by positivity) hδΛ
    (by rw [one_pow, one_mul]; exact hδτ) (fun {Dom} hm _ => ?_) (fun x μ μ' => ?_))
  · simp only [starExt_self, starExt_star]
  · refine dataHypAniso_of_near hδ.le hδ1 ?_ ?_ ?_ ?_ ?_ hm.1 hm.2
    · intro s
      rw [hφ0]
      exact starExt_near j y Ψ hδ.le hgrad _
    · rw [hφ0]; exact hsq0
    · rw [hφ0]; exact hbdd0
    · rw [hφ0]; exact hbc
    · simp only [vInv, uInv, hφ0]; exact hbl
  · exact norm_sec_le_of_near (p := Ψ y) (starExt_near j y Ψ hδ.le hgrad _)
      (starExt_near j y Ψ hδ.le hgrad _) (starExt_near j y Ψ hδ.le hgrad _) (starExt_near j y Ψ hδ.le hgrad _)

end Filed

end Balaban.SmallField.Def6v2
