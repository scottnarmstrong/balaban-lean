/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomSplit
public import Balaban.SmallField.RenormAnisoIrrel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The non-special label bound with a quantitative real-frame threshold
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Metric Set Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}

open Classical in
/-- The termwise anisotropic bound and the tube discrepancy yield the non-special
label estimate without a polydisc-or-tube-exterior premise. The threshold and source-frame
coordinate bounds are explicit quantitative hypotheses. -/
theorem irrelTorus_bound_of_dataHyp_of_threshold
    (hP : P.Admissible d L)
    (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hN : L ^ P.m₀ ∣ N₁)
    (hν : 0 < ν) (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν)
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hXne : X ≠ box (cbase (cellSide L P.m₀ m₁ j) y -
      natT fun _ => L / 2 * cellSide L P.m₀ m₁ j) (L * cellSide L P.m₀ m₁ j))
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
      ‖irrelTorus P.m₀ Tm i₀ i₁ j y X Ψ (constFld hv)‖ ≤
        CI * P.E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)) *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) := by
  have hα1 : P.α₁ < 1 := by
    have := hP.α₁_lt
    have := hP.γ_pos
    linarith
  obtain ⟨CItw, hCI0, hCI⟩ := termwise_irrelevant_aniso_scaled d N
    (diamA d L P.m₀ m₁) Λ Ksig P.α₁ γ C₀ KR
    (diamA_nonneg d L P.m₀ m₁) hΛ hKsig hP.α₁_pos hα1 hC₀
  let CI : ℝ := CItw + 12 * Real.exp 1 * Cρ
  have hE0 := hP.E₀_nonneg
  have hCIpos : 0 ≤ CI := by dsimp [CI]; positivity
  refine ⟨CI, hCIpos, ?_⟩
  let ψ : Site d → Spin N :=
    fun v => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v)
  let b : Spin N := (ν : ℂ) • hv
  have hψ0 : ψ 0 = Ψ y := by simp only [ψ, ibase_zero, add_zero]
  have hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k) j (z - y) ∈ S := by
    intro z hz
    rw [hSdef]
    exact mem_placeSet hN hjk hy hX hz
  have hS' : ∀ v ∈ S, ∃ x ∈ X, Aligned (L ^ j) x ∧
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) = v := by
    intro v hvS
    rw [hSdef] at hvS
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hvS
    exact ⟨x, (Finset.mem_filter.1 hx).2.2,
      (Finset.mem_filter.1 hx).2.1, rfl⟩
  have hσε : 0 ≤ σ * ε := by rw [hσs]; positivity
  have hchart : ∃ Ψ' h' : Fld d L N₁ m₁ k N,
      (∀ z ∈ X, Ψ' z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k) j i₀ S (pack S ψ b) (z - y) ∧
        h' z = hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
          ν S (pack S ψ b) z) ∧
      XiDom (Tm.gs j X) a μ j (P.eps d L j) Ψ' h' := dat.mem
  have hcenter' : ∀ i, ‖ψ 0 i - (Pi.single i₀ 1 : Spin N) i‖ ≤ q := by
    simpa only [hψ0] using hcentre
  have hdisc := shiftTerm_discrepancy_bound_of_threshold hP hcl hBg hν hμν
    hj1 hjk hy hX hyX hS hS' hne hrad dat hσε hcenter' hb hbl hρ hbase hchart
  have hItw := hCI
    (⟨{S}, fun _ => sizeJ P.m₀ j X, fun S' c => trickFnA i₀ ν r (fun c' : Cfg d N S' =>
      Tm.E j y X
        (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S' c' (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S' c')) c⟩ : TermFamily d N)
    i₀ i₁ ν r P.E₀ P.κ _ _
    (premisesTermAniso_centred hcl hBg hν hμν hj1 hjk hy hX hyX
      hS hS' hne hrad) ψ b s σ ε K₂ dat S (Set.mem_singleton S)
    hs hσs hR hrad.1 hrad.2.1 hε hεΛ hσ1 hτ hν.le hνσ hP.E₀_nonneg hK
  have hEq := irrelTorus_eq_Itw_centred_add_discrepancy hcl hBg hν hμν
    hj1 hjk hN hy hX hyX hXne hSdef hne hrad (Ψ := Ψ) hv
  have hF : Tm.E j y X
      (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
        (pack S ψ b) (z - y))
      (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (pack S ψ b)) =
      Tm.E j y X Ψ (constFld hv) := by
    refine hcl.localE j y X _ _ _ _ fun z hz =>
      ⟨shiftField_pack hjk hy hS hΨb _ hz, ?_⟩
    rw [hOf_pack_smul hν.ne']
  rw [hEq, ← hF]
  calc
    ‖Itw (⟨{S}, fun _ => sizeJ P.m₀ j X, fun S' c => trickFnA i₀ ν r
        (fun c' : Cfg d N S' => Tm.E j y X
          (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S' c' (z - y))
          (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S' c')) c⟩ : TermFamily d N)
        i₀ i₁ ν S ψ b +
      Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k) j i₀ S (pack S ψ b) (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (pack S ψ b)) -
      trickFnA i₀ ν r (fun c' : Cfg d N S => Tm.E j y X
        (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c'))
        (pack S ψ b)‖
        ≤ CItw * P.E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)) *
            Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) +
          12 * Real.exp 1 * P.E₀ * ρ ^ 3 *
            Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) := by
          have ht := norm_add_le
            (Itw (⟨{S}, fun _ => sizeJ P.m₀ j X, fun S' c => trickFnA i₀ ν r
              (fun c' : Cfg d N S' => Tm.E j y X
                (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k) j i₀ S' c' (z - y))
                (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S' c')) c⟩ : TermFamily d N)
              i₀ i₁ ν S ψ b)
            (Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁)
                (m₁ := m₁) (k := k) j i₀ S (pack S ψ b) (z - y))
              (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (pack S ψ b)) -
              trickFnA i₀ ν r (fun c' : Cfg d N S => Tm.E j y X
                (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k) j i₀ S c' (z - y))
                (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c'))
                (pack S ψ b))
          rw [add_sub_assoc]
          exact ht.trans (add_le_add hItw hdisc)
    _ ≤ CI * P.E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)) *
        Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) := by
          have hp : 12 * Real.exp 1 * P.E₀ * ρ ^ 3 *
              Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) ≤
              12 * Real.exp 1 * P.E₀ *
                (Cρ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁))) *
                  Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) := by
            gcongr
          dsimp [CI]
          nlinarith [hp]

end Balaban.SmallField.Def6v2
