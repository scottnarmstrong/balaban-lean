/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomBound
public import Balaban.SmallField.IrrelTorusDefectFiledId
public import Balaban.SmallField.IrrelTorusDefectCauchy
public import Balaban.SmallField.IrrelTorusDefectFiledPower
public import Balaban.Green.FinalCountPolymers
public import Balaban.Fluctuation.SizeModEntropy
public import Balaban.Fluctuation.SizeModG5

/-!
# The label bound of the box-renormalized functional (P1 (3.128))

For the selection `relBox` (the polymers within `r_k = ⌊L^{m₀+m₁+k}/8⌋` of the centre), the label
functional `irrelTorusB` differs from the termwise part `ℰ(y,X) - (T_X + Φ_{y,X}) - A_{y,X}` by the
relevant part of an unselected polymer and, at the cell `□(y)`, by the filed sum of the selection
(`irrelTorusOn_eq_split`).  The unselected polymers are large:

* `sizeJ_ge_of_not_relBox`: a polymer through `y` not in the box of half-side `r_k` around `y` has
  `d_j(X) ≥ τ_{jk} = (r_k + 1)/(M L^j) - 2√d L` (from (G5)), and
  `exp_neg_half_relBoxThreshold_le`: `e^{-τ_{jk}/2} ≤ C L^{-p(k-j)}` for every `p > 0`;
* `norm_relPartTorus_le_of_data`: the relevant part of one polymer at any aligned centre is bounded
  in the Cauchy form `C E₀ (1 + d_j)^4 e^{-κ d_j}` (`norm_ttw_add_phitw_le_of_data`);
* `sum_exp_polysAt_le`: the polymers through a site are counted by (G2);
* `norm_relPartTorus_le_of_not_relBox`: the kept relevant part of a large polymer is bounded by
  `C E₀ L^{-(k-j)(d+α₃)} e^{-(κ-1) d_j(X)}`, `α₃ = 1 - 2γ - α₁`;
* `norm_sum_not_relBox_le_power`: so is the sum over the large polymers through `y` of their
  relevant parts (without the factor `e^{-(κ-1) d_j}`);
* `norm_E_sub_aTermTorus_le_of_not_relBox`: for a large label, `ℰ(y,X) - A_{y,X}` (the label
  functional of `irrelTorusB` away from the cell) is bounded by
  `C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(X)} + C E₀ L^{-(k-j)(d+α₃)} e^{-(κ-1) d_j(X)}`;
* `irrelTorusB_bound_of_dataHyp_of_threshold`: **the label bound of `irrelTorusB`** at every
  polymer `X ∋ y`: `C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(X)} + C E₀ L^{-(k-j)(d+α₃)} e^{-(κ-1) d_j(X)}`
  plus, at the cell, the filed sum of the selection.

All constants depend on `d, L, N, m₀, m₁`, the class constants and the numerical parameters only:
not on the torus, `k`, `j`, the label or the data.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Metric Set Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-! ### The size of the unselected polymers -/

/-- The covering-size threshold of the polymers through a centre that leave the box of half-side
`r_k = ⌊L^{m₀+m₁+k}/8⌋`: `τ_{jk} = (r_k + 1)/(M L^j) - 2√d L`, `M L^j = cellSide`. -/
noncomputable def relBoxThreshold (d L m₀ m₁ k j : ℕ) : ℝ :=
  ((L ^ (m₀ + m₁ + k) / 8 + 1 : ℕ) : ℝ) / (cellSide L m₀ m₁ j : ℝ) - 2 * Real.sqrt d * L

omit [NeZero L] [NeZero N₁] in
theorem cycNorm_eq_natAbs_valMinAbs {n : ℕ} [NeZero n] (a : ZMod n) :
    LargeField.cycNorm n a = a.valMinAbs.natAbs := by
  rw [ZMod.valMinAbs_natAbs_eq_min]
  rfl

/-- **A polymer through `y` leaving the box around `y` is large** (from (G5)):
`d_j(X) ≥ τ_{jk}`. -/
theorem sizeJ_ge_of_not_relBox {m₀ j : ℕ} {y : CTorus d L N₁ m₁ k}
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom m₀ j X) (hyX : y ∈ X)
    (h : ¬ relBox m₀ y X) : relBoxThreshold d L m₀ m₁ k j ≤ sizeJ m₀ j X := by
  unfold relBox at h
  push Not at h
  obtain ⟨z, hz, hzb⟩ := h
  unfold Balaban.Polymer.InBox at hzb
  push Not at hzb
  obtain ⟨μ, hμ⟩ := hzb
  have hc : (L ^ (m₀ + m₁ + k) / 8 + 1 : ℕ) ≤
      LargeField.cycNorm ((N₁ * L ^ m₁) * L ^ k) (z μ - y μ) := by
    rw [cycNorm_eq_natAbs_valMinAbs]
    have e : (z - y) μ = z μ - y μ := rfl
    rw [← e]
    have habs := Int.abs_eq_natAbs ((z - y) μ).valMinAbs
    omega
  have hG := G5 (isDj_of_isPolyDom hX) hz hyX
  have hE : (LargeField.cycNorm ((N₁ * L ^ m₁) * L ^ k) (z μ - y μ) : ℝ) ≤ euclDist z y := by
    unfold euclDist
    apply Real.le_sqrt_of_sq_le
    exact Finset.single_le_sum (f := fun ν =>
      ((LargeField.cycNorm ((N₁ * L ^ m₁) * L ^ k) (z ν - y ν) : ℕ) : ℝ) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
  have hcs : (0 : ℝ) < (cellSide L m₀ m₁ j : ℝ) := by exact_mod_cast cellSide_pos m₀ m₁ j
  unfold relBoxThreshold sizeJ
  rw [sub_le_iff_le_add, div_le_iff₀ hcs]
  calc ((L ^ (m₀ + m₁ + k) / 8 + 1 : ℕ) : ℝ)
      ≤ (LargeField.cycNorm ((N₁ * L ^ m₁) * L ^ k) (z μ - y μ) : ℝ) := by exact_mod_cast hc
    _ ≤ euclDist z y := hE
    _ ≤ ((cellSide L m₀ m₁ j : ℕ) : ℝ) *
        (treeLenCovOne (L := L) (N₁ := N₁) (m₁ := m₁) (K := k) m₀ j X +
          2 * Real.sqrt d * L) := hG
    _ = _ := by ring

omit [NeZero N₁] in
/-- **The threshold of the large polymers is a power of `L^{k-j}`**: for `p > 0`,
`e^{-τ_{jk}/2} ≤ e^{√d L} (16 p / e)^p L^{-p (k-j)}`. -/
theorem exp_neg_half_relBoxThreshold_le {m₀ j : ℕ} (hjk : j ≤ k) {p : ℝ} (hp : 0 < p) :
    Real.exp (-(relBoxThreshold d L m₀ m₁ k j / 2)) ≤
      Real.exp (Real.sqrt d * L) * (p / (Real.exp 1 * (1 / 16))) ^ p *
        ((L : ℝ) ^ (k - j)) ^ (-p) := by
  set yL : ℝ := (L : ℝ) ^ (k - j) with hyL
  have hL : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
  have hy : 0 < yL := by positivity
  have hcs : (cellSide L m₀ m₁ j : ℝ) = (L : ℝ) ^ (j + m₀ + m₁) := by
    unfold cellSide; push_cast; rfl
  have hr : (L : ℝ) ^ (m₀ + m₁ + k) / 8 ≤ ((L ^ (m₀ + m₁ + k) / 8 + 1 : ℕ) : ℝ) := by
    have h1 : L ^ (m₀ + m₁ + k) ≤ (L ^ (m₀ + m₁ + k) / 8 + 1) * 8 := by omega
    have h2 : ((L ^ (m₀ + m₁ + k) : ℕ) : ℝ) ≤ ((L ^ (m₀ + m₁ + k) / 8 + 1 : ℕ) : ℝ) * 8 := by
      exact_mod_cast h1
    push_cast at h2 ⊢
    linarith
  have hpow : (L : ℝ) ^ (m₀ + m₁ + k) = (L : ℝ) ^ (j + m₀ + m₁) * yL := by
    rw [hyL, ← pow_add]
    congr 1
    omega
  have hcpos : 0 < (L : ℝ) ^ (j + m₀ + m₁) := by positivity
  have hτ : yL / 16 - Real.sqrt d * L ≤ relBoxThreshold d L m₀ m₁ k j / 2 := by
    unfold relBoxThreshold
    rw [hcs]
    have h8 : yL / 8 ≤ ((L ^ (m₀ + m₁ + k) / 8 + 1 : ℕ) : ℝ) / (L : ℝ) ^ (j + m₀ + m₁) := by
      rw [le_div_iff₀ hcpos]
      calc yL / 8 * (L : ℝ) ^ (j + m₀ + m₁) = (L : ℝ) ^ (m₀ + m₁ + k) / 8 := by
            rw [hpow]; ring
        _ ≤ _ := hr
    linarith
  have h2 := Balaban.SmallField.Def6.rpow_mul_exp_neg_le hp (by norm_num : (0 : ℝ) < 1 / 16) hy
  have hyp : 0 < yL ^ p := Real.rpow_pos_of_pos hy p
  have h3 : Real.exp (-(1 / 16 * yL)) ≤ (p / (Real.exp 1 * (1 / 16))) ^ p * yL ^ (-p) := by
    rw [Real.rpow_neg hy.le, ← div_eq_mul_inv, le_div_iff₀ hyp]
    linarith
  calc Real.exp (-(relBoxThreshold d L m₀ m₁ k j / 2))
      ≤ Real.exp (Real.sqrt d * L + -(1 / 16 * yL)) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (Real.sqrt d * L) * Real.exp (-(1 / 16 * yL)) := Real.exp_add _ _
    _ ≤ Real.exp (Real.sqrt d * L) * ((p / (Real.exp 1 * (1 / 16))) ^ p * yL ^ (-p)) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = _ := by ring

/-- `(1 + t)^4 e^{-κ t} ≤ 384 √e e^{-t/2} e^{-(κ-1) t}` for `t ≥ 0`. -/
theorem one_add_pow_four_mul_exp_le {t κ : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ 4 * Real.exp (-κ * t) ≤
      384 * Real.exp (1 / 2) * Real.exp (-(t / 2)) * Real.exp (-(κ - 1) * t) := by
  have h1 := Real.pow_div_factorial_le_exp ((1 + t) / 2) (by linarith) 4
  rw [div_le_iff₀ (by norm_num [Nat.factorial])] at h1
  norm_num [Nat.factorial] at h1
  have hpow : (1 + t) ^ 4 ≤ 384 * Real.exp ((1 + t) / 2) := by
    have e : (1 + t) ^ 4 = 16 * ((1 + t) / 2) ^ 4 := by ring
    rw [e]
    linarith
  have e2 : Real.exp ((1 + t) / 2) * Real.exp (-κ * t) =
      Real.exp (1 / 2) * Real.exp (-(t / 2)) * Real.exp (-(κ - 1) * t) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc (1 + t) ^ 4 * Real.exp (-κ * t) ≤ 384 * Real.exp ((1 + t) / 2) * Real.exp (-κ * t) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = 384 * (Real.exp ((1 + t) / 2) * Real.exp (-κ * t)) := by ring
    _ = _ := by rw [e2]; ring

/-! ### The relevant part of one polymer, in the Cauchy form -/

/-- The constant of the Cauchy form of the relevant part of one polymer: with the block count
constant `H = M^d c₁` (`M = L^{m₀+m₁}`) and the path constant `A = diamA`,
`1 + Λ H + Λ² + H² (2A)² N (40 N Λ)²`. -/
noncomputable def relPartCauchyConst (d L N m₀ m₁ : ℕ) (Λ : ℝ) : ℝ :=
  1 + Λ * ((L : ℝ) ^ ((m₀ + m₁) * d) * c1 d L) + Λ ^ 2 +
    ((L : ℝ) ^ ((m₀ + m₁) * d) * c1 d L) ^ 2 * (2 * diamA d L m₀ m₁) ^ 2 *
      (N * (N * 40 * Λ) ^ 2)

theorem relPartCauchyConst_nonneg (d L N m₀ m₁ : ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    0 ≤ relPartCauchyConst d L N m₀ m₁ Λ := by
  have hc : 0 ≤ c1 d L := by unfold c1; positivity
  unfold relPartCauchyConst
  positivity

section Single

variable {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)}

open Classical in
/-- **The relevant part of one polymer at any aligned centre, in the Cauchy form**: for a polymer
`X ∋ y` and a datum with the anisotropic data properties at the field pulled back at `y`,
`|T_X + Φ_{y,X}| ≤ C E₀ (1 + d_j(X))^4 e^{-κ d_j(X)}`, `C = relPartCauchyConst`. -/
theorem norm_relPartTorus_le_of_data (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ 1) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hN : L ^ P.m₀ ∣ N₁) (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    (Ψ : Fld d L N₁ m₁ k N) (hv : Fin N → ℂ) {σ ε K₂ Λ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)}
    (dat : DataHypAniso Dom ν σ ε K₂
      (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)) ((ν : ℂ) • hv))
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε) (hεΛ : ε ≤ Λ * r) (hτ : σ ^ 2 * ε ≤ 1 / 4) :
    ‖relPartTorus Tm i₀ i₁ j y Ψ (constFld hv) X‖ ≤
      relPartCauchyConst d L N P.m₀ m₁ Λ *
        (P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X) * (1 + sizeJ P.m₀ j X) ^ 4) := by
  set S : Finset (Site d) := (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
    (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)) with hSdef
  have hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S :=
    fun z hz => by rw [hSdef]; exact mem_placeSet hN hjk hy hX hz
  have hS' : ∀ s ∈ S, ∃ x ∈ X, Aligned (L ^ j) x ∧
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) = s := by
    intro s hs
    rw [hSdef] at hs
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hs
    exact ⟨x, (Finset.mem_filter.1 hx).2.2, (Finset.mem_filter.1 hx).2.1, rfl⟩
  have hP := premisesTermAniso_centred hcl hBg hν hμν hνb hj1 hjk hy hX hyX hS hS' hne hrad
  have hmem : S ∈ ({S} : Set (Finset (Site d))) := Set.mem_singleton S
  have han := (hP.analytic S hmem).mono polyAniso_subset_tubeAniso
  have hM := fun c hc => hP.bdd_tube S hmem c (polyAniso_subset_tubeAniso hc)
  have hdiam : ∀ x ∈ S, ((l1 x : ℕ) : ℝ) ≤ diamA d L P.m₀ m₁ * (1 + sizeJ P.m₀ j X) := by
    intro x hx
    rw [l1_cast]
    exact hP.diam S hmem x hx
  have hs0 : 0 ≤ sizeJ P.m₀ j X := treeLenCovOne_nonneg _ _ _
  have hH : 0 ≤ (L : ℝ) ^ ((P.m₀ + m₁) * d) * c1 d L := by
    have : 0 ≤ c1 d L := by unfold c1; positivity
    positivity
  have hcard : (S.card : ℝ) ≤ (L : ℝ) ^ ((P.m₀ + m₁) * d) * c1 d L * (1 + sizeJ P.m₀ j X) := by
    refine le_trans ?_ (Balaban.Green.card_aligned_polyDom_le hjk hN hX)
    exact_mod_cast Finset.card_image_le
  have h := norm_ttw_add_phitw_le_of_data (i₁ := i₁) dat hσ hσ1 hε hεΛ hτ hrad.1 han hM hdiam
    (by linarith) hH hcard
  rw [show relPartTorus Tm i₀ i₁ j y Ψ (constFld hv) X = _ from
    (TPhi_eq_Ttw_add_Phitw hcl hBg hν hμν hνb hj1 hjk hN hy hX hyX hSdef hne hrad Ψ hv).symm]
  exact h

/-- The constant of the kept relevant part of a large polymer:
`relPartCauchyConst · 384 √e · e^{√d L} (16 p/e)^p`, `p = d + α₃`. -/
noncomputable def relBoxLargeConst (d L N : ℕ) (P : Consts) (m₁ : ℕ) (Λ : ℝ) : ℝ :=
  relPartCauchyConst d L N P.m₀ m₁ Λ * (384 * Real.exp (1 / 2)) *
    (Real.exp (Real.sqrt d * L) *
      (((d : ℝ) + (1 - 2 * P.γ - P.α₁)) / (Real.exp 1 * (1 / 16))) ^
        ((d : ℝ) + (1 - 2 * P.γ - P.α₁)))

open Classical in
/-- **The kept relevant part of a large polymer** (a polymer through `y` leaving the box of
half-side `r_k` around `y`): `|T_X + Φ_{y,X}| ≤ C E₀ L^{-(k-j)(d+α₃)} e^{-(κ-1) d_j(X)}`,
`C = relBoxLargeConst`, independent of the torus, `k`, `j`, the label and the datum. -/
theorem norm_relPartTorus_le_of_not_relBox (hP : P.Admissible d L)
    (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ 1) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hN : L ^ P.m₀ ∣ N₁) (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hrel : ¬ relBox P.m₀ y X)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    (Ψ : Fld d L N₁ m₁ k N) (hv : Fin N → ℂ) {σ ε K₂ Λ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)}
    (dat : DataHypAniso Dom ν σ ε K₂
      (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)) ((ν : ℂ) • hv))
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε) (hεΛ : ε ≤ Λ * r) (hτ : σ ^ 2 * ε ≤ 1 / 4) :
    ‖relPartTorus Tm i₀ i₁ j y Ψ (constFld hv) X‖ ≤
      relBoxLargeConst d L N P m₁ Λ * P.E₀ *
        ((L : ℝ) ^ (k - j)) ^ (-((d : ℝ) + (1 - 2 * P.γ - P.α₁))) *
        Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) := by
  have hp : 0 < (d : ℝ) + (1 - 2 * P.γ - P.α₁) := by
    have := hP.α₁_lt
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hΛ : 0 ≤ Λ := by
    have hr := hrad.1
    by_contra hneg
    push Not at hneg
    nlinarith
  have hCc := relPartCauchyConst_nonneg d L N P.m₀ m₁ hΛ
  have hE0 := hP.E₀_nonneg
  set t := sizeJ P.m₀ j X with ht
  have ht0 : 0 ≤ t := treeLenCovOne_nonneg _ _ _
  have h1 := norm_relPartTorus_le_of_data hcl hBg hν hμν hνb hj1 hjk hN hy hX hyX hne hrad Ψ hv dat
    hσ hσ1 hε hεΛ hτ
  have h2 := one_add_pow_four_mul_exp_le (κ := P.κ) ht0
  have h3 : Real.exp (-(t / 2)) ≤ Real.exp (-(relBoxThreshold d L P.m₀ m₁ k j / 2)) :=
    Real.exp_le_exp.2 (by linarith [sizeJ_ge_of_not_relBox hX hyX hrel])
  have h4 := exp_neg_half_relBoxThreshold_le (d := d) (L := L) (k := k) (m₀ := P.m₀) (m₁ := m₁) hjk hp
  set Q : ℝ := Real.exp (Real.sqrt d * L) *
      (((d : ℝ) + (1 - 2 * P.γ - P.α₁)) / (Real.exp 1 * (1 / 16))) ^
        ((d : ℝ) + (1 - 2 * P.γ - P.α₁)) with hQ
  have hY : 0 ≤ ((L : ℝ) ^ (k - j)) ^ (-((d : ℝ) + (1 - 2 * P.γ - P.α₁))) :=
    Real.rpow_nonneg (by positivity) _
  have h5 : (1 + t) ^ 4 * Real.exp (-P.κ * t) ≤
      384 * Real.exp (1 / 2) *
        (Q * ((L : ℝ) ^ (k - j)) ^ (-((d : ℝ) + (1 - 2 * P.γ - P.α₁)))) *
        Real.exp (-(P.κ - 1) * t) := by
    refine h2.trans ?_
    have hA : 0 ≤ 384 * Real.exp (1 / 2) := by positivity
    have h34 : Real.exp (-(t / 2)) ≤ Q * ((L : ℝ) ^ (k - j)) ^ (-((d : ℝ) + (1 - 2 * P.γ - P.α₁))) := by
      refine h3.trans ?_
      rw [hQ]
      exact h4
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h34 hA) (Real.exp_pos _).le
  calc ‖relPartTorus Tm i₀ i₁ j y Ψ (constFld hv) X‖
      ≤ relPartCauchyConst d L N P.m₀ m₁ Λ * (P.E₀ * Real.exp (-P.κ * t) * (1 + t) ^ 4) := h1
    _ = relPartCauchyConst d L N P.m₀ m₁ Λ * P.E₀ * ((1 + t) ^ 4 * Real.exp (-P.κ * t)) := by ring
    _ ≤ relPartCauchyConst d L N P.m₀ m₁ Λ * P.E₀ *
        (384 * Real.exp (1 / 2) *
          (Q * ((L : ℝ) ^ (k - j)) ^ (-((d : ℝ) + (1 - 2 * P.γ - P.α₁)))) *
          Real.exp (-(P.κ - 1) * t)) :=
        mul_le_mul_of_nonneg_left h5 (mul_nonneg hCc hE0)
    _ = _ := by unfold relBoxLargeConst; rw [← hQ]; ring

end Single

/-! ### The polymers through a site, counted -/

open Classical in
/-- **The polymers through a site are counted by (G2)**: for `κ₀ ≥ a_ent + 1` and any finite family
of polymers of `𝒟_j` through `y`, `Σ e^{-κ₀ d_j(Z)} ≤ K₀`, independently of the torus and of `j`. -/
theorem sum_exp_polysAt_le {m₀ j : ℕ} (hN : L ^ m₀ ∣ N₁) (hjk : j ≤ k) {κ₀ : ℝ}
    (hκ : aEnt d L + 1 ≤ κ₀) (y : CTorus d L N₁ m₁ k) (S : Finset (Set (CTorus d L N₁ m₁ k)))
    (hS : ∀ Z ∈ S, IsPolyDom m₀ j Z ∧ y ∈ Z) :
    ∑ Z ∈ S, Real.exp (-κ₀ * sizeJ m₀ j Z) ≤ K0 d L κ₀ := by
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hdvd := cellSide_dvd (K := k) (m₁ := m₁) (L := L) (N₁ := N₁) hN hjk
  have hΩ : IsPiUnion (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k) m₀ j Set.univ :=
    fun z _ => ⟨cbase (cellSide L m₀ m₁ j) z, aligned_cbase z, mem_box_cbase ha0 z,
      Set.subset_univ _⟩
  have hG2 := G2_X (m₀ := m₀) (j := j) hN hjk hΩ (aligned_cbase (a := cellSide L m₀ m₁ j) y)
    (Set.subset_univ _) hκ
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.univ.filter
    (fun Z : Set (CTorus d L N₁ m₁ k) => DjMod m₀ j Set.univ Z ∧
      box (cbase (cellSide L m₀ m₁ j) y) (cellSide L m₀ m₁ j) ⊆ Z)) ?_
    (fun _ _ _ => (Real.exp_pos _).le)) ?_
  · intro Z hZ
    obtain ⟨hpd, hyZ⟩ := hS Z hZ
    have hDj := isDj_of_isPolyDom hpd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨hDj, fun z hz => absurd (Set.mem_univ z) hz⟩, ?_⟩
    obtain ⟨b, hb, hzb, hsub⟩ := hDj.2.1 y hyZ
    exact (cell_subset_cube hdvd ha0 hb hzb).trans hsub
  · refine le_trans (le_of_eq (Finset.sum_congr rfl fun Z _ => ?_)) hG2
    rw [dcovMod_of_subset (Set.subset_univ Z)]
    rfl

/-! ### The large polymers through a centre -/

/-- The constant of the sum of the kept relevant parts through a centre:
`24 e · relPartCauchyConst · e^{√d L} (16 p/e)^p · K₀`, `p = d + α₃`. -/
noncomputable def relBoxTailConst (d L N : ℕ) (P : Consts) (m₁ : ℕ) (Λ : ℝ) : ℝ :=
  24 * Real.exp 1 * relPartCauchyConst d L N P.m₀ m₁ Λ *
    (Real.exp (Real.sqrt d * L) *
      (((d : ℝ) + (1 - 2 * P.γ - P.α₁)) / (Real.exp 1 * (1 / 16))) ^
        ((d : ℝ) + (1 - 2 * P.γ - P.α₁))) * K0 d L (P.κ - 2)

section Tail

variable {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k}

open Classical in
/-- **The kept relevant parts of the large polymers through a centre**: the sum over the polymers
through `y` that leave the box of half-side `r_k` around `y` of `T_Z + Φ_{y,Z}` is bounded by
`C E₀ L^{-(k-j)(d+α₃)}`, `C = relBoxTailConst`, independent of the torus, `k`, `j`, `y` and the
datum (Cauchy form of each term, the count (G2) and the size threshold). -/
theorem norm_sum_not_relBox_le_power (hP : P.Admissible d L) (hκ : aEnt d L + 3 ≤ P.κ)
    (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ 1) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hN : L ^ P.m₀ ∣ N₁) (hy : Aligned (L ^ j) y)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    (Ψ : Fld d L N₁ m₁ k N) (hv : Fin N → ℂ) {σ ε K₂ Λ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)}
    (dat : DataHypAniso Dom ν σ ε K₂
      (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)) ((ν : ℂ) • hv))
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε) (hεΛ : ε ≤ Λ * r) (hτ : σ ^ 2 * ε ≤ 1 / 4) :
    ‖∑ᶠ Z ∈ polysAt P.m₀ j y,
        (if relBox P.m₀ y Z then 0 else relPartTorus Tm i₀ i₁ j y Ψ (constFld hv) Z)‖ ≤
      relBoxTailConst d L N P m₁ Λ * P.E₀ *
        ((L : ℝ) ^ (k - j)) ^ (-((d : ℝ) + (1 - 2 * P.γ - P.α₁))) := by
  have hp : 0 < (d : ℝ) + (1 - 2 * P.γ - P.α₁) := by
    have := hP.α₁_lt
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hΛ : 0 ≤ Λ := by
    have hr := hrad.1
    by_contra hneg
    push Not at hneg
    nlinarith
  have hCc := relPartCauchyConst_nonneg d L N P.m₀ m₁ hΛ
  have hE0 := hP.E₀_nonneg
  have hfin := Set.toFinite (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j y)
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have e : ∑ Z ∈ hfin.toFinset,
      (if relBox P.m₀ y Z then 0 else relPartTorus Tm i₀ i₁ j y Ψ (constFld hv) Z) =
      ∑ Z ∈ hfin.toFinset.filter (fun Z => ¬ relBox P.m₀ y Z),
        relPartTorus Tm i₀ i₁ j y Ψ (constFld hv) Z := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun Z _ => ?_
    by_cases h : relBox P.m₀ y Z <;> simp [h]
  rw [e]
  have hmemS : ∀ Z ∈ hfin.toFinset.filter (fun Z => ¬ relBox P.m₀ y Z),
      IsPolyDom P.m₀ j Z ∧ y ∈ Z ∧ ¬ relBox P.m₀ y Z := by
    intro Z hZ
    obtain ⟨hZ1, hZ2⟩ := Finset.mem_filter.1 hZ
    exact ⟨(hfin.mem_toFinset.1 hZ1).1, (hfin.mem_toFinset.1 hZ1).2, hZ2⟩
  have hW := Balaban.SmallField.Def6.norm_sum_winding_le
    (hfin.toFinset.filter (fun Z => ¬ relBox P.m₀ y Z)) (fun Z => sizeJ P.m₀ j Z)
    (fun Z => relPartTorus Tm i₀ i₁ j y Ψ (constFld hv) Z)
    (M := relPartCauchyConst d L N P.m₀ m₁ Λ) (κ := P.κ) (κ₀ := P.κ - 2)
    (τ := relBoxThreshold d L P.m₀ m₁ k j / 2) (K₀ := K0 d L (P.κ - 2)) hCc hE0 (by linarith)
    (fun Z _ => treeLenCovOne_nonneg _ _ _)
    (fun Z hZ => by
      obtain ⟨hpd, hyZ, hrel⟩ := hmemS Z hZ
      have h1 := sizeJ_ge_of_not_relBox hpd hyZ hrel
      have h2 : 0 ≤ sizeJ P.m₀ j Z := treeLenCovOne_nonneg _ _ _
      linarith)
    (fun Z hZ => by
      obtain ⟨hpd, hyZ, -⟩ := hmemS Z hZ
      refine (norm_relPartTorus_le_of_data hcl hBg hν hμν hνb hj1 hjk hN hy hpd hyZ hne hrad Ψ hv
        dat hσ hσ1 hε hεΛ hτ).trans (le_of_eq ?_)
      ring)
    (sum_exp_polysAt_le hN hjk (by linarith) y _ fun Z hZ =>
      ⟨(hmemS Z hZ).1, (hmemS Z hZ).2.1⟩)
  refine hW.trans ?_
  have h4 := exp_neg_half_relBoxThreshold_le (d := d) (L := L) (k := k) (m₀ := P.m₀) (m₁ := m₁) hjk hp
  have hK : 0 ≤ K0 d L (P.κ - 2) := by
    unfold K0
    have : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
    exact div_nonneg (Real.exp_pos _).le (by linarith)
  have hA : 0 ≤ 24 * Real.exp 1 * relPartCauchyConst d L N P.m₀ m₁ Λ * P.E₀ := by positivity
  calc 24 * Real.exp 1 * relPartCauchyConst d L N P.m₀ m₁ Λ * P.E₀ *
        Real.exp (-(relBoxThreshold d L P.m₀ m₁ k j / 2)) * K0 d L (P.κ - 2)
      ≤ 24 * Real.exp 1 * relPartCauchyConst d L N P.m₀ m₁ Λ * P.E₀ *
        (Real.exp (Real.sqrt d * L) *
          (((d : ℝ) + (1 - 2 * P.γ - P.α₁)) / (Real.exp 1 * (1 / 16))) ^
            ((d : ℝ) + (1 - 2 * P.γ - P.α₁)) *
          ((L : ℝ) ^ (k - j)) ^ (-((d : ℝ) + (1 - 2 * P.γ - P.α₁)))) * K0 d L (P.κ - 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hA) hK
    _ = _ := by unfold relBoxTailConst; ring

end Tail

/-! ### The label bound -/

section Label

variable {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}

open Classical in
/-- **A large label: `ℰ(y,X) - A_{y,X}`** (blocker 6, the labels kept unrenormalized by the
selection `relBox`): for a polymer `X ∋ y` leaving the box of half-side `r_k` around `y`,
`|ℰ(y,X) - A_{y,X}| ≤ C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(X)} + C E₀ L^{-(k-j)(d+α₃)} e^{-(κ-1) d_j(X)}`,
`C = relBoxLargeConst`: the termwise part plus the relevant part of a large polymer. -/
theorem norm_E_sub_aTermTorus_le_of_not_relBox
    (hP : P.Admissible d L)
    (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hN : L ^ P.m₀ ∣ N₁)
    (hν : 0 < ν) (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ 1)
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hrel : ¬ relBox P.m₀ y X)
    (hSdef : S = (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
      (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    {Ψ : Fld d L N₁ m₁ k N} {hv : Fin N → ℂ}
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x =
      jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    {Λ Ksig γ C₀ KR s σ ε K₂ q ρ Cρ : ℝ}
    (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) (hC₀ : 0 < C₀)
    (dat : DataHypAniso {p | ∃ Ψ' h' : Fld d L N₁ m₁ k N,
        (∀ z ∈ X, Ψ' z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
            (pack S p.1 p.2) (z - y) ∧
          h' z = hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S
            (pack S p.1 p.2) z) ∧
        XiDom (Tm.gs j X) a μ j (P.eps d L j) Ψ' h'} ν σ ε K₂
      (fun v => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v))
      ((ν : ℂ) • hv))
    (hs : 0 < s) (hσs : σ = C₀ * s)
    (hR : ε / r ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ))
    (hε : 0 < ε) (hεΛ : ε ≤ Λ * r) (hσ1 : σ ≤ 1)
    (hτ : σ ^ 2 * ε ≤ 1 / 4) (hνσ : ν ≤ σ ^ 2)
    (hK : K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε)
    (hcentre : ∀ i, ‖Ψ y i - (Pi.single i₀ 1 : Spin N) i‖ ≤ q)
    (hb : ∀ i, ‖((ν : ℂ) • hv) i -
      (ν : ℂ) * (Pi.single i₀ 1 : Spin N) i‖ ≤ r)
    (hbl : ‖((ν : ℂ) • hv) i₀ - (ν : ℂ)‖ < r ^ 2)
    (hρ : 0 < ρ)
    (hbase : q + diamA d L P.m₀ m₁ * (σ * ε) / ρ ≤ r)
    (hCρ : 0 ≤ Cρ)
    (hρpow : ρ ^ 3 ≤ Cρ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁))) :
    ∃ CI : ℝ, 0 ≤ CI ∧
      ‖Tm.E j y X Ψ (constFld hv) - aTermTorus Tm i₀ j y Ψ X‖ ≤
        CI * P.E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)) *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) +
        relBoxLargeConst d L N P m₁ Λ * P.E₀ *
          ((L : ℝ) ^ (k - j)) ^ (-((d : ℝ) + (1 - 2 * P.γ - P.α₁))) *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) := by
  obtain ⟨CI, hCI0, hCI⟩ := norm_termPart_le_of_dataHyp_of_threshold hP hcl hBg hN hν hμν hνb hj1
    hjk hy hX hyX hSdef hne hrad hΨb hΛ hKsig hC₀ dat hs hσs hR hε hεΛ hσ1 hτ hνσ hK hcentre hb hbl
    hρ hbase hCρ hρpow
  refine ⟨CI, hCI0, ?_⟩
  have hσ : 0 < σ := by rw [hσs]; positivity
  have e : Tm.E j y X Ψ (constFld hv) - aTermTorus Tm i₀ j y Ψ X =
      (Tm.E j y X Ψ (constFld hv) - relPartTorus Tm i₀ i₁ j y Ψ (constFld hv) X -
        aTermTorus Tm i₀ j y Ψ X) + relPartTorus Tm i₀ i₁ j y Ψ (constFld hv) X := by ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add hCI (norm_relPartTorus_le_of_not_relBox hP hcl hBg hν
    hμν hνb hj1 hjk hN hy hX hyX hrel hne hrad Ψ hv dat hσ hσ1 hε hεΛ hτ))

open Classical in
/-- **The label bound of the box-renormalized functional** (P1 Corollary 3.11, (3.128), for
`irrelTorusB`; conditional on the anisotropic data hypothesis `DataHypAniso`, the open input P-2, as
in `irrelTorus_bound_of_dataHyp_of_threshold`): at every polymer `X ∋ y`,
`|ℰ^B_{irrel}(y, X)| ≤ C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(X)} + C E₀ L^{-(k-j)(d+α₃)} e^{-(κ-1) d_j(X)}`
plus, at the cell `□(y)`, the filed sum `Σ_{Z ∋ y, relBox} (T_Z + Φ_{y,Z})`;
`C = relBoxLargeConst` (the second term is present only for the large polymers). -/
theorem irrelTorusB_bound_of_dataHyp_of_threshold
    (hP : P.Admissible d L)
    (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hN : L ^ P.m₀ ∣ N₁)
    (hν : 0 < ν) (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ 1)
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hSdef : S = (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
      (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    {Ψ : Fld d L N₁ m₁ k N} {hv : Fin N → ℂ}
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x =
      jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    {Λ Ksig γ C₀ KR s σ ε K₂ q ρ Cρ : ℝ}
    (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) (hC₀ : 0 < C₀)
    (dat : DataHypAniso {p | ∃ Ψ' h' : Fld d L N₁ m₁ k N,
        (∀ z ∈ X, Ψ' z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
            (pack S p.1 p.2) (z - y) ∧
          h' z = hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S
            (pack S p.1 p.2) z) ∧
        XiDom (Tm.gs j X) a μ j (P.eps d L j) Ψ' h'} ν σ ε K₂
      (fun v => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v))
      ((ν : ℂ) • hv))
    (hs : 0 < s) (hσs : σ = C₀ * s)
    (hR : ε / r ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ))
    (hε : 0 < ε) (hεΛ : ε ≤ Λ * r) (hσ1 : σ ≤ 1)
    (hτ : σ ^ 2 * ε ≤ 1 / 4) (hνσ : ν ≤ σ ^ 2)
    (hK : K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε)
    (hcentre : ∀ i, ‖Ψ y i - (Pi.single i₀ 1 : Spin N) i‖ ≤ q)
    (hb : ∀ i, ‖((ν : ℂ) • hv) i -
      (ν : ℂ) * (Pi.single i₀ 1 : Spin N) i‖ ≤ r)
    (hbl : ‖((ν : ℂ) • hv) i₀ - (ν : ℂ)‖ < r ^ 2)
    (hρ : 0 < ρ)
    (hbase : q + diamA d L P.m₀ m₁ * (σ * ε) / ρ ≤ r)
    (hCρ : 0 ≤ Cρ)
    (hρpow : ρ ^ 3 ≤ Cρ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁))) :
    ∃ CI : ℝ, 0 ≤ CI ∧
      ‖irrelTorusB P.m₀ Tm i₀ i₁ j y X Ψ (constFld hv)‖ ≤
        CI * P.E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)) *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) +
        relBoxLargeConst d L N P m₁ Λ * P.E₀ *
          ((L : ℝ) ^ (k - j)) ^ (-((d : ℝ) + (1 - 2 * P.γ - P.α₁))) *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) +
        ‖if X = box (cbase (cellSide L P.m₀ m₁ j) y -
            natT fun _ => L / 2 * cellSide L P.m₀ m₁ j) (L * cellSide L P.m₀ m₁ j) then
          ∑ᶠ Z ∈ polysAt P.m₀ j y,
            (if relBox P.m₀ y Z then relPartTorus Tm i₀ i₁ j y Ψ (constFld hv) Z else 0)
          else 0‖ := by
  obtain ⟨CI, hCI0, hCI⟩ := norm_termPart_le_of_dataHyp_of_threshold hP hcl hBg hN hν hμν hνb hj1
    hjk hy hX hyX hSdef hne hrad hΨb hΛ hKsig hC₀ dat hs hσs hR hε hεΛ hσ1 hτ hνσ hK hcentre hb hbl
    hρ hbase hCρ hρpow
  refine ⟨CI, hCI0, ?_⟩
  have hσ : 0 < σ := by rw [hσs]; positivity
  have hlarge : ‖if relBox P.m₀ y X then 0 else relPartTorus Tm i₀ i₁ j y Ψ (constFld hv) X‖ ≤
      relBoxLargeConst d L N P m₁ Λ * P.E₀ *
        ((L : ℝ) ^ (k - j)) ^ (-((d : ℝ) + (1 - 2 * P.γ - P.α₁))) *
        Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) := by
    by_cases hrel : relBox P.m₀ y X
    · have hΛ0 : 0 ≤ Λ := by linarith
      have hCc := relPartCauchyConst_nonneg d L N P.m₀ m₁ hΛ0
      have hY : 0 ≤ ((L : ℝ) ^ (k - j)) ^ (-((d : ℝ) + (1 - 2 * P.γ - P.α₁))) :=
        Real.rpow_nonneg (by positivity) _
      have hE0 := hP.E₀_nonneg
      have hp : 0 < (d : ℝ) + (1 - 2 * P.γ - P.α₁) := by
        have := hP.α₁_lt
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        linarith
      have hQ : 0 ≤ (((d : ℝ) + (1 - 2 * P.γ - P.α₁)) / (Real.exp 1 * (1 / 16))) ^
          ((d : ℝ) + (1 - 2 * P.γ - P.α₁)) :=
        Real.rpow_nonneg (div_nonneg hp.le (by positivity)) _
      simp only [hrel, ↓reduceIte, norm_zero]
      unfold relBoxLargeConst
      have h1 : 0 ≤ relPartCauchyConst d L N P.m₀ m₁ Λ * (384 * Real.exp (1 / 2)) *
          (Real.exp (Real.sqrt d * L) *
            (((d : ℝ) + (1 - 2 * P.γ - P.α₁)) / (Real.exp 1 * (1 / 16))) ^
              ((d : ℝ) + (1 - 2 * P.γ - P.α₁))) :=
        mul_nonneg (mul_nonneg hCc (by positivity)) (mul_nonneg (Real.exp_pos _).le hQ)
      exact mul_nonneg (mul_nonneg (mul_nonneg h1 hE0) hY) (Real.exp_pos _).le
    · simp only [hrel, ↓reduceIte]
      exact norm_relPartTorus_le_of_not_relBox hP hcl hBg hν hμν hνb hj1 hjk hN hy hX hyX hrel hne
        hrad Ψ hv dat hσ hσ1 hε hεΛ hτ
  rw [irrelTorusB, irrelTorusOn_eq_split]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hCI hlarge))
    le_rfl)

end Label

end Balaban.SmallField.Def6v2
