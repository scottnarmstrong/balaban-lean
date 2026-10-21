/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusBoxBound
public import Balaban.SmallField.IrrelTorusDefectFiledAll

/-!
# The cell term of the label functional for the members of the class

For a member of the second version of the class (`IsSFFamily2` on the complete domains), whose
renormalization conditions hold in infinite volume only (`RenormCondAlong`):

* `norm_filed_relBox_le_power`: the filed sum of the selection `relBox` at an aligned centre,
  `Σ_{Z ∋ y, relBox y Z} (T_Z + Φ_{y,Z})`, is bounded by `C E₀ L^{-(k-j)(d+α₃)}`: it is the complete
  filed sum (`norm_filed_le_power`) minus the kept relevant parts of the large polymers
  (`norm_sum_not_relBox_le_power`);
* `irrelTorus_bound_cell_of_dataHyp`: **the cell label of `irrelTorus`** satisfies P1 (3.128) with
  the infinite-volume conditions only: `|ℰ_{irrel}(y, □(y))| ≤ C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(□(y))}
  + C_R E₀ L^{-(k-j)(d+α₃)}`;
* `irrelTorusB_bound_of_class`: **the label bound of `irrelTorusB` at every label**:
  `|ℰ^B_{irrel}(y, X)| ≤ C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(X)} + C E₀ L^{-(k-j)(d+α₃)} e^{-(κ-1) d_j(X)}
  + 1_{X = □(y)} C' E₀ L^{-(k-j)(d+α₃)}`.

The data enter as in the landed theorems: `DataHypAniso` at the pulled-back datum (the open input
P-2) in the form of `irrelTorus_bound_of_dataHyp_of_threshold` for the termwise part, and in the
form of `norm_filed_le_power` for the filed sum.  The constants `filedPowerConst`,
`relBoxLargeConst`, `relBoxTailConst` depend on `d, L, N, m₀, m₁`, the class constants and `Λ` only.
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

/-- The constant of the complete filed sum at a centre (`norm_filed_le_power`). -/
noncomputable def filedPowerConst (d L N : ℕ) (P : Consts) (m₁ : ℕ) (Λ : ℝ) : ℝ :=
  2 * (24 * Real.exp 1 * (16 * (1 + Λ * (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) + Λ ^ 2 +
    (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (2 * diamA d L P.m₀ m₁) ^ 2 *
      (N * (N * 40 * Λ) ^ 2))) *
    ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
      K0 d L (P.κ - 2)) *
    (Real.exp ((4 * (((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ)) + 4) / (8 * (diamA d L P.m₀ m₁)) + 1 / 2) *
      ((((d : ℝ) + (1 - 2 * P.γ - P.α₁))) /
        (Real.exp 1 * (((L : ℝ) ^ (P.m₀ + m₁)) / (8 * (diamA d L P.m₀ m₁))))) ^
        (((d : ℝ) + (1 - 2 * P.γ - P.α₁)))))

open Classical in
/-- **The filed sum of the selection `relBox` at an aligned centre** (blocker 6, P1 (3.128) at the
cell label): for a member of the second version, `N₁` with `L^{m₀} ∣ N₁`, `1 ≤ j ≤ k` and an aligned
centre `y`, `|Σ_{Z ∋ y, relBox y Z} (T_Z + Φ_{y,Z})| ≤ C E₀ L^{-(k-j)(d+α₃)}`,
`C = filedPowerConst + relBoxTailConst`, independent of `N₁`, `k`, `j`, `y` and the datum; the
premises are those of `norm_filed_le_power`. -/
theorem norm_filed_relBox_le_power
    (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek)
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
        ‖Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
            (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) →
      DataHypAniso Dom (nuIdeal L k (Rg.ν k) j) σ ε K₂
        (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s))
        (((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv))
    (hsec : ∀ (x : Site d) (μ μ' : Fin d),
        ‖Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
            (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) :
    ‖∑ᶠ Z ∈ polysAt P.m₀ j y,
        (if relBox P.m₀ y Z then relPartTorus (Tm N₁) i₀ i₁ j y Ψ (constFld hv) Z else 0)‖ ≤
      (filedPowerConst d L N P m₁ Λ + relBoxTailConst d L N P m₁ Λ) * P.E₀ *
        (((L : ℝ) ^ (k - j)) ^ (-(((d : ℝ) + (1 - 2 * P.γ - P.α₁))))) := by
  have hjk := hn.hjk
  have hcl : SFTermClauses P (xiFieldDom (aIdeal L k (a k)) (Rg.sfBgMass k) (P.eps d L))
      (Tm N₁) := (hF.torus N₁).terms
  have hBg := bgHyp_of_class2 hF.admissible hF.coeff hn.hd hn.hL hn.hϱ
  have hν : 0 < nuIdeal L k (Rg.ν k) j := nuIdeal_pos' (L := L) hF.coeff.nu_pos j
  have hμν := (Rg.sfBgMass_mul_sq hjk).le
  have hνb := hF.coeff.nuIdeal_le_one hF.admissible j
  have hrad := hF.anisoRadiusOK hn.hsmall i₀
  have dat := hdat (Dom := Set.univ) ⟨trivial, trivial⟩ hsec
  have hfull : ‖∑ᶠ Z ∈ polysAt P.m₀ j y, relPartTorus (Tm N₁) i₀ i₁ j y Ψ (constFld hv) Z‖ ≤
      filedPowerConst d L N P m₁ Λ * P.E₀ *
        (((L : ℝ) ^ (k - j)) ^ (-(((d : ℝ) + (1 - 2 * P.γ - P.α₁))))) :=
    norm_filed_le_power hF hn hne hN hy Ψ hv hσ hσ1 hε hεΛ hτ hdat hsec
  have htail := norm_sum_not_relBox_le_power hF.admissible hn.hκ hcl hBg hν hμν hνb hn.hj1 hjk hN
    hy hne hrad Ψ hv dat hσ hσ1 hε hεΛ hτ
  have hfin := Set.toFinite (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j y)
  have e : ∑ᶠ Z ∈ polysAt P.m₀ j y,
      (if relBox P.m₀ y Z then relPartTorus (Tm N₁) i₀ i₁ j y Ψ (constFld hv) Z else 0) =
      ∑ᶠ Z ∈ polysAt P.m₀ j y, relPartTorus (Tm N₁) i₀ i₁ j y Ψ (constFld hv) Z -
        ∑ᶠ Z ∈ polysAt P.m₀ j y,
          (if relBox P.m₀ y Z then 0 else relPartTorus (Tm N₁) i₀ i₁ j y Ψ (constFld hv) Z) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
      finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun Z _ => ?_
    split_ifs <;> ring
  rw [e]
  refine (norm_sub_le _ _).trans ((add_le_add hfull htail).trans (le_of_eq ?_))
  ring


open Classical in
/-- **The label bound of `irrelTorusB` for the members of the class** (blocker 6, P1 Corollary 3.11,
(3.128); conditional on the data hypotheses, the open input P-2): at every label `(j, y, X)`,
`|ℰ^B_{irrel}(y, X)| ≤ C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(X)} + C E₀ L^{-(k-j)(d+α₃)} e^{-(κ-1) d_j(X)}
+ 1_{X = □(y)} C' E₀ L^{-(k-j)(d+α₃)}`, with `C = relBoxLargeConst`,
`C' = filedPowerConst + relBoxTailConst` (independent of the torus, `k`, `j`, the label and the
datum) and `C_I` as in `irrelTorus_bound_of_dataHyp_of_threshold`.  Only the infinite-volume
renormalization conditions of the class enter (through `norm_filed_le_power`). -/
theorem irrelTorusB_bound_of_class
    (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {N₁ : ℕ} [NeZero N₁] (hN : L ^ P.m₀ ∣ N₁)
    {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hSdef : S = (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
      (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)))
    {Ψ : Fld d L N₁ m₁ k N} {hv : Fin N → ℂ}
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x =
      jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    {Λ Ksig γ C₀ KR s σ ε K₂ q ρ Cρ : ℝ}
    (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) (hC₀ : 0 < C₀)
    (dat : DataHypAniso {p | ∃ Ψ' h' : Fld d L N₁ m₁ k N,
        (∀ z ∈ X, Ψ' z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
            (pack S p.1 p.2) (z - y) ∧
          h' z = hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k (Rg.ν k) j) S
            (pack S p.1 p.2) z) ∧
        XiDom ((Tm N₁).gs j X) (aIdeal L k (a k)) (Rg.sfBgMass k) j (P.eps d L j) Ψ' h'}
      (nuIdeal L k (Rg.ν k) j) σ ε K₂
      (fun v => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v))
      (((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv))
    (hs : 0 < s) (hσs : σ = C₀ * s)
    (hR : ε / anisoRadius d L N P j ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ))
    (hε : 0 < ε) (hεΛ : ε ≤ Λ * anisoRadius d L N P j) (hσ1 : σ ≤ 1)
    (hτ : σ ^ 2 * ε ≤ 1 / 4) (hνσ : nuIdeal L k (Rg.ν k) j ≤ σ ^ 2)
    (hK : K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε)
    (hcentre : ∀ i, ‖Ψ y i - (Pi.single i₀ 1 : Spin N) i‖ ≤ q)
    (hb : ∀ i, ‖(((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv) i -
      ((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) * (Pi.single i₀ 1 : Spin N) i‖ ≤ anisoRadius d L N P j)
    (hbl : ‖(((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv) i₀ - ((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ)‖ <
      anisoRadius d L N P j ^ 2)
    (hρ : 0 < ρ)
    (hbase : q + diamA d L P.m₀ m₁ * (σ * ε) / ρ ≤ anisoRadius d L N P j)
    (hCρ : 0 ≤ Cρ)
    (hρpow : ρ ^ 3 ≤ Cρ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)))
    (hdat : ∀ {Dom : Set ((Site d → Spin N) × Spin N)},
      ((fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)),
          ((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv) ∈ Dom ∧
        ((fun _ => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j 0)),
          ((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv) ∈ Dom →
      (∀ (x : Site d) (μ μ' : Fin d),
        ‖Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
            (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) →
      DataHypAniso Dom (nuIdeal L k (Rg.ν k) j) σ ε K₂
        (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s))
        (((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv))
    (hsec : ∀ (x : Site d) (μ μ' : Fin d),
        ‖Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
            (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) :
    ∃ CI : ℝ, 0 ≤ CI ∧
      ‖irrelTorusB P.m₀ (Tm N₁) i₀ i₁ j y X Ψ (constFld hv)‖ ≤
        CI * P.E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)) *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) +
        relBoxLargeConst d L N P m₁ Λ * P.E₀ *
          ((L : ℝ) ^ (k - j)) ^ (-((d : ℝ) + (1 - 2 * P.γ - P.α₁))) *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) +
        (if X = box (cbase (cellSide L P.m₀ m₁ j) y -
            natT fun _ => L / 2 * cellSide L P.m₀ m₁ j) (L * cellSide L P.m₀ m₁ j) then
          (filedPowerConst d L N P m₁ Λ + relBoxTailConst d L N P m₁ Λ) * P.E₀ *
            ((L : ℝ) ^ (k - j)) ^ (-((d : ℝ) + (1 - 2 * P.γ - P.α₁)))
          else 0) := by
  have hjk := hn.hjk
  have hcl : SFTermClauses P (xiFieldDom (aIdeal L k (a k)) (Rg.sfBgMass k) (P.eps d L))
      (Tm N₁) := (hF.torus N₁).terms
  have hBg := bgHyp_of_class2 hF.admissible hF.coeff hn.hd hn.hL hn.hϱ
  have hν : 0 < nuIdeal L k (Rg.ν k) j := nuIdeal_pos' (L := L) hF.coeff.nu_pos j
  have hμν := (Rg.sfBgMass_mul_sq hjk).le
  have hνb := hF.coeff.nuIdeal_le_one hF.admissible j
  have hrad := hF.anisoRadiusOK hn.hsmall i₀
  have hσ : 0 < σ := by rw [hσs]; positivity
  have hfiled := norm_filed_relBox_le_power hF hn hne hN hy Ψ hv hσ hσ1 hε hεΛ hτ hdat hsec
  obtain ⟨CI, hCI0, hCI⟩ := irrelTorusB_bound_of_dataHyp_of_threshold hF.admissible hcl hBg hN hν
    hμν hνb hn.hj1 hjk hy hX hyX hSdef hne hrad hΨb hΛ hKsig hC₀ dat hs hσs hR hε hεΛ hσ1 hτ hνσ hK
    hcentre hb hbl hρ hbase hCρ hρpow
  refine ⟨CI, hCI0, hCI.trans (add_le_add le_rfl ?_)⟩
  by_cases hXc : X = box (cbase (cellSide L P.m₀ m₁ j) y -
      natT fun _ => L / 2 * cellSide L P.m₀ m₁ j) (L * cellSide L P.m₀ m₁ j)
  · rw [ite_eq_left hXc, ite_eq_left hXc]
    exact hfiled
  · rw [ite_eq_right hXc, ite_eq_right hXc, norm_zero]

open Classical in
/-- **The cell label of `irrelTorus` satisfies P1 (3.128) with the infinite-volume renormalization
conditions only** (blocker 6): for the members of the class, at the cell `□(y)` of an aligned
centre, `|ℰ_{irrel}(y, □(y))| ≤ C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(□(y))} + C_R E₀ L^{-(k-j)(d+α₃)}`,
`C_R = filedPowerConst` (`norm_filed_le_power`), with the data hypotheses of
`irrelTorus_bound_of_dataHyp_of_threshold` and of `norm_filed_le_power`. -/
theorem irrelTorus_bound_cell_of_dataHyp
    (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {N₁ : ℕ} [NeZero N₁] (hN : L ^ P.m₀ ∣ N₁)
    {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}
    (hy : Aligned (L ^ j) y)
    (hXc : X = box (cbase (cellSide L P.m₀ m₁ j) y -
      natT fun _ => L / 2 * cellSide L P.m₀ m₁ j) (L * cellSide L P.m₀ m₁ j))
    (hSdef : S = (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
      (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)))
    {Ψ : Fld d L N₁ m₁ k N} {hv : Fin N → ℂ}
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x =
      jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    {Λ Ksig γ C₀ KR s σ ε K₂ q ρ Cρ : ℝ}
    (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) (hC₀ : 0 < C₀)
    (dat : DataHypAniso {p | ∃ Ψ' h' : Fld d L N₁ m₁ k N,
        (∀ z ∈ X, Ψ' z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
            (pack S p.1 p.2) (z - y) ∧
          h' z = hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k (Rg.ν k) j) S
            (pack S p.1 p.2) z) ∧
        XiDom ((Tm N₁).gs j X) (aIdeal L k (a k)) (Rg.sfBgMass k) j (P.eps d L j) Ψ' h'}
      (nuIdeal L k (Rg.ν k) j) σ ε K₂
      (fun v => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v))
      (((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv))
    (hs : 0 < s) (hσs : σ = C₀ * s)
    (hR : ε / anisoRadius d L N P j ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ))
    (hε : 0 < ε) (hεΛ : ε ≤ Λ * anisoRadius d L N P j) (hσ1 : σ ≤ 1)
    (hτ : σ ^ 2 * ε ≤ 1 / 4) (hνσ : nuIdeal L k (Rg.ν k) j ≤ σ ^ 2)
    (hK : K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε)
    (hcentre : ∀ i, ‖Ψ y i - (Pi.single i₀ 1 : Spin N) i‖ ≤ q)
    (hb : ∀ i, ‖(((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv) i -
      ((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) * (Pi.single i₀ 1 : Spin N) i‖ ≤ anisoRadius d L N P j)
    (hbl : ‖(((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv) i₀ - ((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ)‖ <
      anisoRadius d L N P j ^ 2)
    (hρ : 0 < ρ)
    (hbase : q + diamA d L P.m₀ m₁ * (σ * ε) / ρ ≤ anisoRadius d L N P j)
    (hCρ : 0 ≤ Cρ)
    (hρpow : ρ ^ 3 ≤ Cρ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)))
    (hdat : ∀ {Dom : Set ((Site d → Spin N) × Spin N)},
      ((fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)),
          ((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv) ∈ Dom ∧
        ((fun _ => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j 0)),
          ((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv) ∈ Dom →
      (∀ (x : Site d) (μ μ' : Fin d),
        ‖Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
            (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) →
      DataHypAniso Dom (nuIdeal L k (Rg.ν k) j) σ ε K₂
        (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s))
        (((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv))
    (hsec : ∀ (x : Site d) (μ μ' : Fin d),
        ‖Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
            (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) :
    ∃ CI : ℝ, 0 ≤ CI ∧
      ‖irrelTorus P.m₀ (Tm N₁) i₀ i₁ j y X Ψ (constFld hv)‖ ≤
        CI * P.E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)) *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) +
        filedPowerConst d L N P m₁ Λ * P.E₀ *
          ((L : ℝ) ^ (k - j)) ^ (-((d : ℝ) + (1 - 2 * P.γ - P.α₁))) := by
  have hjk := hn.hjk
  have hcl : SFTermClauses P (xiFieldDom (aIdeal L k (a k)) (Rg.sfBgMass k) (P.eps d L))
      (Tm N₁) := (hF.torus N₁).terms
  have hBg := bgHyp_of_class2 hF.admissible hF.coeff hn.hd hn.hL hn.hϱ
  have hν : 0 < nuIdeal L k (Rg.ν k) j := nuIdeal_pos' (L := L) hF.coeff.nu_pos j
  have hμν := (Rg.sfBgMass_mul_sq hjk).le
  have hνb := hF.coeff.nuIdeal_le_one hF.admissible j
  have hrad := hF.anisoRadiusOK hn.hsmall i₀
  have hσ : 0 < σ := by rw [hσs]; positivity
  have hfull : ‖∑ᶠ Z ∈ polysAt P.m₀ j y, relPartTorus (Tm N₁) i₀ i₁ j y Ψ (constFld hv) Z‖ ≤
      filedPowerConst d L N P m₁ Λ * P.E₀ *
        (((L : ℝ) ^ (k - j)) ^ (-(((d : ℝ) + (1 - 2 * P.γ - P.α₁))))) :=
    norm_filed_le_power hF hn hne hN hy Ψ hv hσ hσ1 hε hεΛ hτ hdat hsec
  have hX : IsPolyDom P.m₀ j X := by rw [hXc]; exact isPolyDom_cubeAt hN hjk y
  have hyX : y ∈ X := by rw [hXc]; exact mem_cubeAt y
  obtain ⟨CI, hCI0, hCI⟩ := irrelTorusOn_bound_of_dataHyp_of_threshold (fun _ _ => True)
    hF.admissible hcl hBg hN hν hμν hνb hn.hj1 hjk hy hX hyX trivial hSdef hne hrad hΨb hΛ hKsig hC₀
    dat hs hσs hR hε hεΛ hσ1 hτ hνσ hK hcentre hb hbl hρ hbase hCρ hρpow
  refine ⟨CI, hCI0, ?_⟩
  rw [irrelTorus_eq_irrelTorusOn]
  refine hCI.trans (add_le_add le_rfl ?_)
  rw [ite_eq_left hXc]
  simpa only [ite_true] using hfull

end Balaban.SmallField.Def6v2
