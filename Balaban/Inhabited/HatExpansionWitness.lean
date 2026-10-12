/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.HatExpansionWitnessNum
public import Balaban.Fluctuation.InteractionHatAssemble
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# The hypotheses of `interaction_expansion_hat_dm` are jointly satisfiable

`interaction_expansion_hat_hyps_nonempty`: at `d = L = 3`, `N₁ = 9`, `k = 1`, `a₁ = 1`,
`ν = 1/81`, `m₀ = 1`, `R_σ = 1`, `R₁ = 2`, `r = 1`, `R = 2`, `κ_dec` as in
`hatWitness_core`, `c_c = 1` and a hat radius `c_ψ > 0` with `√N ‖c_c‖ C c_ψ < δ₁`, with empty
families of old energy terms and of observable terms, every premise of
`interaction_expansion_hat_dm` holds (bundles `FlCore`, `HatConn`, `RowInHat`, `BgHyp`; cover data
of the potential part and of the source sites; the numerical tower), and the conclusion is
instantiated for every `c_β`, `c_ν`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Filter Topology

/-- A positive hat radius with `a (C c_ψ) < t`. -/
theorem exists_cpsi (a C : ℝ) {t : ℝ} (ht : 0 < t) :
    ∃ cψ : ℝ, 0 < cψ ∧ a * (‖(1 : ℂ)‖ * (C * cψ)) < t := by
  have e := ev_lt (f := fun x : ℝ => a * (‖(1 : ℂ)‖ * (C * x))) (by fun_prop) (c := t)
    (by simpa using ht)
  have hp : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
  exact ((eventually_nhdsWithin_of_eventually_nhds e).and hp).exists.imp
    fun _ h => ⟨h.2, h.1⟩

open Classical in
/-- **The hypotheses of `interaction_expansion_hat_dm` are jointly satisfiable**, and its conclusion
holds for the resulting data, for every `c_β`, `c_ν`. -/
theorem interaction_expansion_hat_hyps_nonempty (N : ℕ) :
    ∃ (m₁ : ℕ) (c BG κ eps c₂ BG₂ κdec cψ : ℝ)
      (_ : FlCore N (Gp m₁ (rhoSep m₁)) (Hm m₁ (rhoSep m₁)) 1 nuW c BG κ eps (levelKc 3 3)
        (Cchi 3 3) c₂ BG₂ eps),
      0 < eps ∧ 3 ≤ κdec ∧ 0 < cψ ∧
      ∀ cβ cν : ℂ, ∃ (𝒴 : Finset (Set (CTorus 3 3 9 m₁ 2)))
        (T : Set (CTorus 3 3 9 m₁ 2) →
          ((unitPts (Gp m₁ (rhoSep m₁)) × Fin N → ℂ) × (unitPts (Gp m₁ (rhoSep m₁)) × Fin N → ℂ)) →
          ((unitPts (Gp m₁ (rhoSep m₁)) × Fin N → ℂ) × (unitPts (Gp m₁ (rhoSep m₁)) × Fin N → ℂ)) →
          ℂ → RawData 3 3 (9 * 3 ^ m₁) 2 N × (CTorus 3 3 9 m₁ 2 → Fin N → ℂ) → ℂ),
        LocIntDm (IsDj 1 (1 + 1))
          (fun ψ : unitPts (Gp m₁ (rhoSep m₁)) × Fin N → ℂ => (ψ, ψ))
          (XiCRaw (Gp m₁ (rhoSep m₁)) (compWeight 3 1) nuW (1 + 1) 1 eps ×ˢ l1Ball 3 3 9 m₁ 2 N)
          {xw : ((unitPts (Gp m₁ (rhoSep m₁)) × Fin N → ℂ) × (unitPts (Gp m₁ (rhoSep m₁)) × Fin N → ℂ)) ×
              ((unitPts (Gp m₁ (rhoSep m₁)) × Fin N → ℂ) × (unitPts (Gp m₁ (rhoSep m₁)) × Fin N → ℂ)) |
            (xw.1.1, xw.2.1) ∈ HatRaysO (Gp m₁ (rhoSep m₁)) cψ 2 1 1 ∧
              (xw.1.2, xw.2.2) ∈ HatRaysO (Gp m₁ (rhoSep m₁)) cψ 2 1 1}
          1 𝒴 T
          (fun x w σ p =>
            (-cβ) * raySrc3 (hatFun (Gp m₁ (rhoSep m₁)) 1 nuW eps (isLevel_Gp (m₁ := m₁) (ϱ := rhoSep m₁)) 1
                (interactionOne (isLevel_Hm (m₁ := m₁) (ϱ := rhoSep m₁))
                  (isLevel_Gp (m₁ := m₁) (ϱ := rhoSep m₁)) le_rfl 1 nuW eps))
              taylorWeight x.1 w.1 σ p.1 +
            cβ * (∑ s : CTorus 3 3 9 m₁ 2 × Fin N, p.2 s.1 s.2 *
              dirTermSrc (hatFun (Gp m₁ (rhoSep m₁)) 1 nuW eps (isLevel_Gp (m₁ := m₁) (ϱ := rhoSep m₁)) 1
                (onXi (Gp m₁ (rhoSep m₁)) 1 nuW eps
                  (fun D ψ' => svec (Hm m₁ (rhoSep m₁)) (flFieldOne (Gp m₁ (rhoSep m₁))
                    (Hm m₁ (rhoSep m₁)) BG₂ κ 1 nuW D ψ') s.1 s.2)))
                (fun _ => (1 : ℂ)) x.2 w.2 σ p.1) +
            cν * dirTermSrc (hatFun (Gp m₁ (rhoSep m₁)) 1 nuW eps (isLevel_Gp (m₁ := m₁) (ϱ := rhoSep m₁)) 1
              (onXi (Gp m₁ (rhoSep m₁)) 1 nuW eps
                (fun D ψ' => nuTotal (Gp m₁ (rhoSep m₁)) (Hm m₁ (rhoSep m₁)) 1 nuW BG₂ κ D ψ')))
              (fun _ => (1 : ℂ)) x.1 w.1 σ p.1)
          (fun Y => prop33Eps 3 3 N m₁ 1 1 1 nuW BG BG₂ κ eps 1 0 0 * ‖cβ‖ *
              Real.exp (-(2 * κdec - 1) * treeLenCovOne 1 (1 + 1) Y) +
            ‖cν‖ * (1 * (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + m₁)) ^ 3 *
              nuBd 3 3 N 1 (cK2' 3 3 N (famConst 3 3 BG₂ κ) * eps)
                (K4 3 3 N BG κ * (xiC1 3 * eps) + (1 + 3 * (xiC1 3 * eps)) + (1 + 2 / nuW)) / 1) *
              Real.exp (-(2 * κdec - 1) * treeLenCovOne 1 (1 + 1) Y)))
          (fun Y p p' => agreeOn (thickSet (Gp m₁ (rhoSep m₁)) Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
          (fun Y a a' => AgHatF (Gp m₁ (rhoSep m₁)) isLevel_Gp Y a.1 a'.1 ∧
            AgHatF (Gp m₁ (rhoSep m₁)) isLevel_Gp Y a.2 a'.2) := by
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa⟩ := hatWitness_core N
  obtain ⟨cψ, hcψ0, hδ₁⟩ := exists_cpsi (Real.sqrt N)
    (covSupConstC 3 3 N (compWeight 3 (1 : ℝ) 1) κ) ht0
  refine ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, cψ, hC, ht0, by linarith [aEnt_nonneg 3 3], hcψ0,
    fun cβ cν => ?_⟩
  have hxi1 : xiC1 3 * t ≤ 1 := by
    have h1 := hC.c7le
    have h2 := c7_le_bgC1 3 3 N BG κ
    have h3 := bgC1_le_small 3 3 N (by norm_num)
    linarith
  have hBh := hBh_of_xi (N := N) (Gp := Gp m₁ (rhoSep m₁)) (bgHypNu m₁) nuW_pos hC.small1
    hC.eps_pos hxi1
  have key := interaction_expansion_hat_dm (Rσ := 1) (R₁ := 2) (r := 1) (R := 2)
    (m₀ := 1) (κdec := κdec) (κ₀ := κ0) (ρE := 0) (ρM := 0) (Bh := 1 + 2 / nuW)
    (δc := δc) (cψ := cψ)
    (jV := fun _ => 1) (XV := fun _ => Xr) (𝒦XV := fun _ => {0})
    (X₁V := fun _ => Finset.univ) (jF := fun _ => 1) (XF := fun _ => Xr)
    (𝒦XF := fun _ => {0}) (X₁F := fun _ => Finset.univ)
    (τι := PEmpty.{1}) (μι := PEmpty.{1}) (ϱ₁ := fun _ => 0) (ϱ₂ := fun _ => 0)
    (GkE := fun τ => PEmpty.elim τ) (GjE := fun τ => PEmpty.elim τ) (r₀ := 0) (δ₃ := 0)
    (δfl := 0) (X₀E := fun _ => ∅) (X₁E := fun _ => ∅) (jE := fun _ => 0) (XE := fun _ => ∅)
    (𝒦XE := fun _ => ∅) (EbE := fun _ => 0) (EE := fun _ _ => 0)
    (ϱ₁M := fun _ => 0) (ϱ₂M := fun _ => 0)
    (GkM := fun τ => PEmpty.elim τ) (GjM := fun τ => PEmpty.elim τ)
    (X₀M := fun _ => ∅) (X₁M := fun _ => ∅) (jM := fun _ => 0) (XM := fun _ => ∅)
    (𝒦XM := fun _ => ∅) (EbM := fun _ => 0) (EM := fun _ _ => 0)
    hC cβ hatConn (rowInHat_level (dgSettingNu h4) isLevel_Hm isLevel_Gp) hκ0
    hκdec (by exact_mod_cast hκ) h1 (by norm_num) (by norm_num) le_rfl isLevel_Hm isLevel_Gp 1
    hcψ0.le hMX hdm hα hsmX hδ₁ one_pos (bgHypNu m₁) hc7 le_rfl g1 g2 g3 g4 g5
    (fun _ => covSetup)
    (fun _ => by rw [Finset.coe_univ, X1_eq_univ]) (fun _ => hopt)
    (fun _ => treeLen_zero) (fun _ => hlog)
    (fun z _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    (fun z => blockMargin_univ fun x _ _ => mem_some_intBox h4 x)
    (∅ : Finset PEmpty.{1}) (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
    (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
    (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
    (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
    (fun τ hτ => absurd hτ (by simp))
    (fun _ => covSetup) (fun _ => by rw [Finset.coe_univ, X1_eq_univ]) (fun _ => hopt)
    (fun _ => treeLen_zero) (fun _ => hlog) (fun s => Finset.mem_univ _)
    (∅ : Finset PEmpty.{1}) (fun τ => PEmpty.elim τ) (fun τ => PEmpty.elim τ)
    (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
    (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
    (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
    (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
    (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
    (fun τ => PEmpty.elim τ) (fun τ hτ => absurd hτ (by simp)) le_rfl (fun x => by simp) le_rfl
    (fun p => by simp) (by unfold nuW; norm_num) hBh cν
    (fun z x _ => Finset.mem_coe.2 (Finset.mem_univ _))
  obtain ⟨𝒴, T, hL⟩ := key
  exact ⟨𝒴, T, hL.congr_val (fun xw hxw σ hσ p hp => by simp)⟩

end Balaban.Inhabited
