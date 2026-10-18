/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusDefectBirthSurrogate
public import Balaban.SmallField.IrrelTorusDefectFiledAll
public import Balaban.SmallField.IrrelTorusDefectMatch

/-!
# The filed torus defect bound on the birth-mass domains

`norm_filed_le_power_birth` is `norm_filed_le_power` for a member of `IsSFFamily2` on the birth
domains `birthXiDom` (author ruling R6): the conclusion is the same bound on the filed sum at an
aligned centre `y`, with `C_R E₀ L^{-(d+α₃)(k-j)}`, for the terms of the level `j` born at the mass
`μ_j = ν_j L⁻²ʲ`.  The data hypothesis is stated at the birth source scale `ν_j` (the source is
`b = ν_j h`; `nuIdeal L k ν'_k j = ν_j` for the regime `ν'_k = ν_j L^{2(k-j)}` of
`IsSFFamily2.exists_levelOnly`).  The proof reads the terms at the level `j` only: they are the terms
of a member of the complete regime of the mass `μ_j`, to which `norm_filed_le_power` applies.  The
extra premise `hcap` is the coefficient bound `ν'_k ≤ ν̄` of that regime, i.e. that the birth mass
of the level is at most the cap `ν̄ L⁻²ᵏ` of the current scale.  The same holds for
`norm_filed_origin_le_birth`, `norm_filed_origin_le_power_birth`, `IsSFFamily2.tsum_filed_inf_birth` and
`IsSFFamily2.norm_filed_inf_le_birth`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Metric Set Filter

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ}
  {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

theorem nuIdeal_levelOnly (j k : ℕ) (ν : ℝ) :
    nuIdeal L k (ν * (L : ℝ) ^ (2 * (k - j))) j = ν := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold nuIdeal
  rw [show 2 * (k - j) = (k - j) * 2 by ring, pow_mul]
  field_simp

open Classical in
/-- **norm filed origin le birth**: norm_filed_origin_le on the birth domains (see the module doc-string). -/
theorem norm_filed_origin_le_birth
    (hF : IsSFFamily2 P Rg β a (birthXiDom P Rg a) Tm ρd Ek)
    (hCR : ∀ (N₁ : ℕ) [NeZero N₁], CRotE P (birthXiDom P Rg a N₁) (Tm N₁))
    (hcap : physMass L j (Rg.ν j) ≤ P.νbar * ((L : ℝ) ^ k)⁻¹ ^ 2)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {N₁ : ℕ} [NeZero N₁] (hN : L ^ P.m₀ ∣ N₁)
    (Ψ : Fld d L N₁ m₁ k N) (hv : Fin N → ℂ)
    {σ ε K₂ Λ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    (hεΛ : ε ≤ Λ * anisoRadius d L N P j) (hτ : σ ^ 2 * ε ≤ 1 / 4)
    (hdat : ∀ {Dom : Set ((Site d → Spin N) × Spin N)},
      ((fun s => Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)),
          ((Rg.ν j : ℝ) : ℂ) • hv) ∈ Dom ∧
        ((fun _ => Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j 0)),
          ((Rg.ν j : ℝ) : ℂ) • hv) ∈ Dom →
      (∀ (x : Site d) (μ μ' : Fin d),
        ‖Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) →
      DataHypAniso Dom (Rg.ν j) σ ε K₂
        (fun s => Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s))
        (((Rg.ν j : ℝ) : ℂ) • hv))
    (hsec : ∀ (x : Site d) (μ μ' : Fin d),
        ‖Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) :
    ‖∑ᶠ Z ∈ polysAt P.m₀ j (0 : CTorus d L N₁ m₁ k),
        (let e : Fld d L N₁ m₁ k N := constFld (Pi.single i₀ 1)
       let blk : Set (CTorus d L N₁ m₁ k) → Finset (CTorus d L N₁ m₁ k) := fun Z' =>
         Finset.univ.filter fun x => Aligned (L ^ j) x ∧ x ∈ Z'
       let u : ℂ := sqrtC (dot (Ψ 0) (Ψ 0))
       let dΨ : Fin d → Fin N → ℂ := fun μ =>
         Ψ (0 + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ 0
       let g : Fin d → Fin d → ℂ := fun μ μ' =>
         dot (dΨ μ) (dΨ μ') - dot (Ψ 0) (dΨ μ) * dot (Ψ 0) (dΨ μ') /
           dot (Ψ 0) (Ψ 0)
       let lift : CTorus d L N₁ m₁ k → Fin d → ℂ := fun z μ =>
         ((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - 0) μ : ℤ) : ℂ)
       let a : Set (CTorus d L N₁ m₁ k) → CTorus d L N₁ m₁ k → ℂ := fun Z' x =>
         fderiv ℂ (fun Ψ' => (Tm N₁).E j 0 Z' Ψ' e) e (blockDir L j x i₀)
       (Tm N₁).E j 0 Z e e + (u - 1) * ∑ x ∈ blk Z, a Z x
             + (dot (Ψ 0) ((constFld hv : Fld d L N₁ m₁ k N) 0) / u - 1) *
               fderiv ℂ (fun h' => (Tm N₁).E j 0 Z e h') e e
             - (1 / 4 : ℂ) * ∑ μ, ∑ μ', g μ μ' * ∑ x ∈ blk Z, ∑ x' ∈ blk Z,
                 D2 (fun Ψ' => (Tm N₁).E j 0 Z Ψ' e) e (blockDir L j x i₁)
                   (blockDir L j x' i₁) *
                   ((lift x μ - lift x' μ) * (lift x μ' - lift x' μ')))‖ ≤
      2 * (24 * Real.exp 1 *
        (16 * (1 + Λ * (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) + Λ ^ 2 +
          (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (2 * diamA d L P.m₀ m₁) ^ 2 *
            (N * (N * 40 * Λ) ^ 2))) * P.E₀ *
        Real.exp (-((((((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) -
          4 * ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) - 4) / (4 * diamA d L P.m₀ m₁) - 1) / 2))) *
        ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
          K0 d L (P.κ - 2))) := by
  obtain ⟨Rg', β', Tm', hν, hT, hF', hCR'⟩ :=
    hF.exists_levelOnly hCR (by have := hn.hL; omega) hn.hj1 hn.hjk hcap
  have hE : ∀ (N₁ : ℕ) [NeZero N₁], (Tm' N₁).E j = (Tm N₁).E j := fun N₁ _ => (hT N₁).1
  have hnu : nuIdeal L k (Rg'.ν k) j = Rg.ν j := by rw [hν]; exact nuIdeal_levelOnly j k _
  have hdat' := @hdat
  rw [← hnu] at hdat'
  have hn' : MomNum d L N k j ϱ { P with p := fun _ => 0, c₉ := |P.c₉| + 1 } :=
    ⟨hn.hd, hn.hL, hn.hϱ, hn.hκ, hn.hj1, hn.hjk, hn.hsmall⟩
  have h := norm_filed_origin_le hF' hCR' hn' hne hN Ψ hv hσ hσ1 hε hεΛ hτ hdat' hsec
  simp only [hE] at h
  exact h

open Classical in
/-- **norm filed origin le power birth**: norm_filed_origin_le_power on the birth domains (see the module doc-string). -/
theorem norm_filed_origin_le_power_birth
    (hF : IsSFFamily2 P Rg β a (birthXiDom P Rg a) Tm ρd Ek)
    (hCR : ∀ (N₁ : ℕ) [NeZero N₁], CRotE P (birthXiDom P Rg a N₁) (Tm N₁))
    (hcap : physMass L j (Rg.ν j) ≤ P.νbar * ((L : ℝ) ^ k)⁻¹ ^ 2)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {N₁ : ℕ} [NeZero N₁] (hN : L ^ P.m₀ ∣ N₁)
    (Ψ : Fld d L N₁ m₁ k N) (hv : Fin N → ℂ)
    {σ ε K₂ Λ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    (hεΛ : ε ≤ Λ * anisoRadius d L N P j) (hτ : σ ^ 2 * ε ≤ 1 / 4)
    (hdat : ∀ {Dom : Set ((Site d → Spin N) × Spin N)},
      ((fun s => Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)),
          ((Rg.ν j : ℝ) : ℂ) • hv) ∈ Dom ∧
        ((fun _ => Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j 0)),
          ((Rg.ν j : ℝ) : ℂ) • hv) ∈ Dom →
      (∀ (x : Site d) (μ μ' : Fin d),
        ‖Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) →
      DataHypAniso Dom (Rg.ν j) σ ε K₂
        (fun s => Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s))
        (((Rg.ν j : ℝ) : ℂ) • hv))
    (hsec : ∀ (x : Site d) (μ μ' : Fin d),
        ‖Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) :
    ‖∑ᶠ Z ∈ polysAt P.m₀ j (0 : CTorus d L N₁ m₁ k),
        (let e : Fld d L N₁ m₁ k N := constFld (Pi.single i₀ 1)
       let blk : Set (CTorus d L N₁ m₁ k) → Finset (CTorus d L N₁ m₁ k) := fun Z' =>
         Finset.univ.filter fun x => Aligned (L ^ j) x ∧ x ∈ Z'
       let u : ℂ := sqrtC (dot (Ψ 0) (Ψ 0))
       let dΨ : Fin d → Fin N → ℂ := fun μ =>
         Ψ (0 + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ 0
       let g : Fin d → Fin d → ℂ := fun μ μ' =>
         dot (dΨ μ) (dΨ μ') - dot (Ψ 0) (dΨ μ) * dot (Ψ 0) (dΨ μ') /
           dot (Ψ 0) (Ψ 0)
       let lift : CTorus d L N₁ m₁ k → Fin d → ℂ := fun z μ =>
         ((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - 0) μ : ℤ) : ℂ)
       let a : Set (CTorus d L N₁ m₁ k) → CTorus d L N₁ m₁ k → ℂ := fun Z' x =>
         fderiv ℂ (fun Ψ' => (Tm N₁).E j 0 Z' Ψ' e) e (blockDir L j x i₀)
       (Tm N₁).E j 0 Z e e + (u - 1) * ∑ x ∈ blk Z, a Z x
             + (dot (Ψ 0) ((constFld hv : Fld d L N₁ m₁ k N) 0) / u - 1) *
               fderiv ℂ (fun h' => (Tm N₁).E j 0 Z e h') e e
             - (1 / 4 : ℂ) * ∑ μ, ∑ μ', g μ μ' * ∑ x ∈ blk Z, ∑ x' ∈ blk Z,
                 D2 (fun Ψ' => (Tm N₁).E j 0 Z Ψ' e) e (blockDir L j x i₁)
                   (blockDir L j x' i₁) *
                   ((lift x μ - lift x' μ) * (lift x μ' - lift x' μ')))‖ ≤
      (2 * (24 * Real.exp 1 * (16 * (1 + Λ * (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) + Λ ^ 2 + (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (2 * diamA d L P.m₀ m₁) ^ 2 * (N * (N * 40 * Λ) ^ 2))) * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2)) * (Real.exp ((4 * (((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ)) + 4) / (8 * (diamA d L P.m₀ m₁)) + 1 / 2) * ((((d : ℝ) + (1 - 2 * P.γ - P.α₁))) / (Real.exp 1 * (((L : ℝ) ^ (P.m₀ + m₁)) / (8 * (diamA d L P.m₀ m₁))))) ^ (((d : ℝ) + (1 - 2 * P.γ - P.α₁)))))) * P.E₀ *
        (((L : ℝ) ^ (k - j)) ^ (-(((d : ℝ) + (1 - 2 * P.γ - P.α₁))))) := by
  obtain ⟨Rg', β', Tm', hν, hT, hF', hCR'⟩ :=
    hF.exists_levelOnly hCR (by have := hn.hL; omega) hn.hj1 hn.hjk hcap
  have hE : ∀ (N₁ : ℕ) [NeZero N₁], (Tm' N₁).E j = (Tm N₁).E j := fun N₁ _ => (hT N₁).1
  have hnu : nuIdeal L k (Rg'.ν k) j = Rg.ν j := by rw [hν]; exact nuIdeal_levelOnly j k _
  have hdat' := @hdat
  rw [← hnu] at hdat'
  have hn' : MomNum d L N k j ϱ { P with p := fun _ => 0, c₉ := |P.c₉| + 1 } :=
    ⟨hn.hd, hn.hL, hn.hϱ, hn.hκ, hn.hj1, hn.hjk, hn.hsmall⟩
  have h := norm_filed_origin_le_power hF' hCR' hn' hne hN Ψ hv hσ hσ1 hε hεΛ hτ hdat' hsec
  simp only [hE] at h
  exact h

open Classical in
/-- **norm filed le power birth**: norm_filed_le_power on the birth domains (see the module doc-string). -/
theorem norm_filed_le_power_birth
    (hF : IsSFFamily2 P Rg β a (birthXiDom P Rg a) Tm ρd Ek)
    (hCR : ∀ (N₁ : ℕ) [NeZero N₁], CRotE P (birthXiDom P Rg a N₁) (Tm N₁))
    (hcap : physMass L j (Rg.ν j) ≤ P.νbar * ((L : ℝ) ^ k)⁻¹ ^ 2)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {N₁ : ℕ} [NeZero N₁] (hN : L ^ P.m₀ ∣ N₁)
    {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    (Ψ : Fld d L N₁ m₁ k N) (hv : Fin N → ℂ)
    {σ ε K₂ Λ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    (hεΛ : ε ≤ Λ * anisoRadius d L N P j) (hτ : σ ^ 2 * ε ≤ 1 / 4)
    (hdat : ∀ {Dom : Set ((Site d → Spin N) × Spin N)},
      ((fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)),
          ((Rg.ν j : ℝ) : ℂ) • hv) ∈ Dom ∧
        ((fun _ => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j 0)),
          ((Rg.ν j : ℝ) : ℂ) • hv) ∈ Dom →
      (∀ (x : Site d) (μ μ' : Fin d),
        ‖Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) →
      DataHypAniso Dom (Rg.ν j) σ ε K₂
        (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s))
        (((Rg.ν j : ℝ) : ℂ) • hv))
    (hsec : ∀ (x : Site d) (μ μ' : Fin d),
        ‖Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) :
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
  obtain ⟨Rg', β', Tm', hν, hT, hF', hCR'⟩ :=
    hF.exists_levelOnly hCR (by have := hn.hL; omega) hn.hj1 hn.hjk hcap
  have hE : ∀ (N₁ : ℕ) [NeZero N₁], (Tm' N₁).E j = (Tm N₁).E j := fun N₁ _ => (hT N₁).1
  have hnu : nuIdeal L k (Rg'.ν k) j = Rg.ν j := by rw [hν]; exact nuIdeal_levelOnly j k _
  have hdat' := @hdat
  rw [← hnu] at hdat'
  have hn' : MomNum d L N k j ϱ { P with p := fun _ => 0, c₉ := |P.c₉| + 1 } :=
    ⟨hn.hd, hn.hL, hn.hϱ, hn.hκ, hn.hj1, hn.hjk, hn.hsmall⟩
  have h := norm_filed_le_power hF' hCR' hn' hne hN hy Ψ hv hσ hσ1 hε hεΛ hτ hdat' hsec
  simp only [hE] at h
  exact h

theorem EauxInf_levelOnly_eq {Tm Tm' : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
    (hE : ∀ (N₁ : ℕ) [NeZero N₁], (Tm' N₁).E j = (Tm N₁).E j) (m₀ : ℕ) (i₀ : Fin N) (νj : ℝ)
    (X' : Finset (Fin d → ℤ)) (c : Cfg d N X') :
    EauxInf (L := L) (m₁ := m₁) (k := k) Tm' m₀ j i₀ νj X' c = EauxInf Tm m₀ j i₀ νj X' c := by
  simp only [EauxInf, Einf, Eseq_levelOnly_eq hE]

theorem liftInfA_levelOnly {P' : Consts} (hm : P'.m₀ = P.m₀)
    {Tm Tm' : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
    (hE : ∀ (N₁ : ℕ) [NeZero N₁], (Tm' N₁).E j = (Tm N₁).E j) (i₀ : Fin N) (νj r : ℝ) :
    liftInfA (L := L) (m₁ := m₁) (k := k) P' Tm' j i₀ νj r =
      liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ νj r := by
  have h : termLInfA Tm' P.m₀ j i₀ νj r = termLInfA Tm P.m₀ j i₀ νj r := by
    funext X' c
    simp only [termLInfA, EauxInf_levelOnly_eq hE]
  simp only [liftInfA, hm, h]

section Inf

variable (hF : IsSFFamily2 P Rg β a (birthXiDom P Rg a) Tm ρd Ek)
  (hCR : ∀ (N₁ : ℕ) [NeZero N₁], CRotE P (birthXiDom P Rg a N₁) (Tm N₁))
  (hcap : physMass L j (Rg.ν j) ≤ P.νbar * ((L : ℝ) ^ k)⁻¹ ^ 2)
  (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
include hF hCR hcap hn hne

open Classical in
/-- **The sum over the infinite shapes of the filed term vanishes**, birth-mass domains
(`IsSFFamily2.tsum_filed_inf`). -/
theorem IsSFFamily2.tsum_filed_inf_birth (ψ : Site d → Spin N) (b : Spin N) :
    Summable (fun X : (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀
        (Rg.ν j) (anisoRadius d L N P j)).polys =>
      Ttw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (Rg.ν j)
        (anisoRadius d L N P j)) i₀ (Rg.ν j) X.1 ψ b +
      Phitw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (Rg.ν j)
        (anisoRadius d L N P j)) i₀ i₁ (Rg.ν j) X.1 ψ) ∧
    ∑' X : (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (Rg.ν j)
        (anisoRadius d L N P j)).polys,
      (Ttw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (Rg.ν j)
        (anisoRadius d L N P j)) i₀ (Rg.ν j) X.1 ψ b +
      Phitw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (Rg.ν j)
        (anisoRadius d L N P j)) i₀ i₁ (Rg.ν j) X.1 ψ) = 0 := by
  obtain ⟨Rg', β', Tm', hν, hT, hF', hCR'⟩ :=
    hF.exists_levelOnly hCR (by have := hn.hL; omega) hn.hj1 hn.hjk hcap
  have hE : ∀ (N₁ : ℕ) [NeZero N₁], (Tm' N₁).E j = (Tm N₁).E j := fun N₁ _ => (hT N₁).1
  have hnu : nuIdeal L k (Rg'.ν k) j = Rg.ν j := by rw [hν]; exact nuIdeal_levelOnly j k _
  have hn' : MomNum d L N k j ϱ { P with p := fun _ => 0, c₉ := |P.c₉| + 1 } :=
    ⟨hn.hd, hn.hL, hn.hϱ, hn.hκ, hn.hj1, hn.hjk, hn.hsmall⟩
  have h := IsSFFamily2.tsum_filed_inf hF' hCR' hn' hne ψ b
  rw [hnu, liftInfA_levelOnly rfl hE] at h
  exact h

/-- **The filed term of one infinite shape in the Cauchy form**, birth-mass domains
(`IsSFFamily2.norm_filed_inf_le`). -/
theorem IsSFFamily2.norm_filed_inf_le_birth {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    {ψ : Site d → Spin N} {b : Spin N} {σ ε K₂ Λ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)}
    (dat : DataHypAniso Dom (Rg.ν j) σ ε K₂ ψ b) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hε : 0 < ε) (hεΛ : ε ≤ Λ * anisoRadius d L N P j) (hτ : σ ^ 2 * ε ≤ 1 / 4) :
    ‖Ttw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (Rg.ν j)
        (anisoRadius d L N P j)) i₀ (Rg.ν j) X' ψ b +
      Phitw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (Rg.ν j)
        (anisoRadius d L N P j)) i₀ i₁ (Rg.ν j) X' ψ‖ ≤
      (1 + Λ * (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) + Λ ^ 2 +
          (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (2 * diamA d L P.m₀ m₁) ^ 2 *
            (N * (N * 40 * Λ) ^ 2)) *
        (P.E₀ * Real.exp (-P.κ * dInf L m₁ k P.m₀ j X') * (1 + dInf L m₁ k P.m₀ j X') ^ 4) := by
  obtain ⟨Rg', β', Tm', hν, hT, hF', hCR'⟩ :=
    hF.exists_levelOnly hCR (by have := hn.hL; omega) hn.hj1 hn.hjk hcap
  have hE : ∀ (N₁ : ℕ) [NeZero N₁], (Tm' N₁).E j = (Tm N₁).E j := fun N₁ _ => (hT N₁).1
  have hnu : nuIdeal L k (Rg'.ν k) j = Rg.ν j := by rw [hν]; exact nuIdeal_levelOnly j k _
  have hn' : MomNum d L N k j ϱ { P with p := fun _ => 0, c₉ := |P.c₉| + 1 } :=
    ⟨hn.hd, hn.hL, hn.hϱ, hn.hκ, hn.hj1, hn.hjk, hn.hsmall⟩
  rw [← hnu] at dat
  have h := IsSFFamily2.norm_filed_inf_le hF' hCR' hn' hne h0 hX dat hσ hσ1 hε hεΛ hτ
  rw [hnu, liftInfA_levelOnly rfl hE] at h
  exact h

end Inf

end Balaban.SmallField.Def6v2
