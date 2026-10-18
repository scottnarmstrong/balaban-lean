/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusDefectFiledPower
public import Balaban.SmallField.IrrelTorusDefectDensitySum

/-!
# The filed torus defect at every aligned centre

`norm_filed_le_power`: the bound `C_R E₀ L^{-(d+α₃)(k-j)}` of `norm_filed_origin_le_power` for the
filed sum at an arbitrary aligned centre `y`. By `LiftCtx.sum_filed_translate` the sum at `y` is the
sum at the origin with the same coefficients, i.e. the sum at the origin for the translated field
`x ↦ Ψ (y + x)`, whose pulled-back datum at the origin is the pulled-back datum at `y`.
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

open Classical in
/-- **The filed torus defect at every aligned centre** (P1 pp. 118–119 (H.6)–(H.7), pp. 152–153
Prop. 3.10, (3.126)–(3.128); blocker 6): for a member of the second version, `N₁` with
`L^{m₀} ∣ N₁`, `1 ≤ j ≤ k`, and every aligned centre `y`,
`|∑ᶠ Z ∈ polysAt m₀ j y, (T_Z + Φ_{y,Z})| ≤ C_R E₀ L^{-(d+α₃)(k-j)}`, `α₃ = 1 - 2γ - α₁`, with
`C_R` depending only on `d, L, N, m₀, m₁`, the class constants and `Λ`: not on `N₁`, `k`, `j`,
`y` or the datum. The datum is the pulled-back datum at `y`, entering through `DataHypAniso` in the
conclusion shape of `xiC_dataHypAniso_of_levelGS` (any domain containing the two points), with the
second difference bound `K₂` and the numerical conditions of the termwise bound. The filed sum at
`y` is the filed sum at the origin of the translated field: the four jets of the density do not
depend on the aligned centre. -/
theorem norm_filed_le_power
    (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek)
    (hCR : ∀ (N₁ : ℕ) [NeZero N₁], CRotE P (completeXiDom P Rg a N₁) (Tm N₁))
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {N₁ : ℕ} [NeZero N₁] (hN : L ^ P.m₀ ∣ N₁)
    {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    (Ψ : Fld d L N₁ m₁ k N) (hv : Fin N → ℂ)
    {σ ε K₂ Λ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    (hεΛ : ε ≤ Λ * anisoRadius d L N P j) (hτ : σ ^ 2 * ε ≤ 1 / 4)
    (hdat : ∀ {Dom : Set ((Site d → Spin N) × Spin N)},
      ((fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)),
          ((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv) ∈ Dom ∧
        ((fun _ => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j 0)),
          ((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv) ∈ Dom →
      (∀ (x : Site d) (μ μ' : Fin d),
        ‖Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) →
      DataHypAniso Dom (nuIdeal L k (Rg.ν k) j) σ ε K₂
        (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s))
        (((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv))
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
  classical
  obtain ⟨β', ν', hν, -, hL⟩ := hF.toLanded hCR
  have hn' := hn.noChi
  have hε' := eps_pos (d := d) (L := L) hL.admissible.α₀_pos j
  have hρ0 := liftRadius_pos (d := d) (L := L) (N := N) hε' i₀
  have hrad := liftRadius_spec (d := d) (L := L) (N := N) hε' i₀ hn'.hsmall
  have ctx := hL.liftCtx N₁ hn'.hd hn'.hL hn'.hϱ hn'.hj1 hn'.hjk hρ0 hrad
  have key := ctx.sum_filed_translate hN i₀ i₁ hy (sqrtC (dot (Ψ y) (Ψ y)))
    (dot (Ψ y) ((constFld hv : Fld d L N₁ m₁ k N) y) / sqrtC (dot (Ψ y) (Ψ y)))
    (fun μ μ' => dot (Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ y)
        (Ψ (y + (L ^ j) • (Pi.single μ' 1 : CTorus d L N₁ m₁ k)) - Ψ y) -
      dot (Ψ y) (Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ y) *
        dot (Ψ y) (Ψ (y + (L ^ j) • (Pi.single μ' 1 : CTorus d L N₁ m₁ k)) - Ψ y) /
        dot (Ψ y) (Ψ y))
    (fun μ μ' s s' => (((s μ : ℤ) : ℂ) - ((s' μ : ℤ) : ℂ)) * (((s μ' : ℤ) : ℂ) - ((s' μ' : ℤ) : ℂ)))
  refine le_of_eq_of_le (congrArg norm key) ?_
  have horig := norm_filed_origin_le_power (K₂ := K₂) hF hCR hn hne hN (fun x => Ψ (y + x)) hv hσ hσ1 hε hεΛ hτ
    ?_ ?_
  · simp only [add_zero, zero_add] at horig
    exact horig
  · intro Dom hm hs
    have h1 : ∀ s : Site d, Ψ (y + (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)) =
        Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s) := fun s => by
      rw [zero_add]
    simp only [h1] at hm hs ⊢
    exact hdat hm hs
  · intro x μ μ'
    have h1 : ∀ s : Site d, Ψ (y + (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)) =
        Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s) := fun s => by
      rw [zero_add]
    simp only [h1]
    exact hsec x μ μ'

end Balaban.SmallField.Def6v2
