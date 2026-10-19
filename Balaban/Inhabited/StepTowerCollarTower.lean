/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerScaleT
public import Balaban.Inhabited.StepTowerDecoupleRoom
public import Balaban.Fluctuation.Prop33CloseWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Towers with a large block at the collar `r₀ = 327` (`StepTowerCollarTower`)

At the collar `r₀ = 4 d L³ + L = 327` the closeness bound of the composed backgrounds carries the
factor `exp(-γ_w L^{m₁})` (FLUCTUATION §1.4, §1.5 row 6), so its ratio to the step radius is small
once the block `L^{m₁}` is large against the other constants of the tower (`exists_pow_close_le`).
The block index `m₁` of a tower is chosen together with its decoupling rate; here it is enlarged
afterwards.

* `exists_stepTower_grow`: every tower `T` has a tower `T'` with `T'.m₁ ≥ T.m₁`, `3^{T'.m₁} ≥ M`, a
  smaller step radius and the other constants of `T`, for which an eventual predicate on the step
  radius holds.  The core `FlCore` at the new block index comes from `flCore_level_eventually`
  (the block-size conditions are monotone in `m₁`), the other conditions on the step radius from
  `exists_stepTower_shrink`.
* `exists_stepTower_collar`: for every cover index `m₀`, floor `κlo` and `θ > 0` there is a tower
  with the label rate of `exists_stepTower_labelRate`, the numerics `ChainNum`, `FlNum` at the
  collar `327` and `K₂ · 2 · composedCloseBound(…, C_{Ξ1}, 327) ≤ θ`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Filter
  Topology

/-- **A general tower with a larger block.**  For every tower `T`, bound `M` and predicate `Pr` on
`(m₁, BG, BG₂, κ, t)` that holds eventually as `t → 0+`, there is a tower `T'` with
`M ≤ L^{T'.m₁}`, `T.m₁ ≤ T'.m₁`, `T'.t ≤ T.t`, the other constants of `T`, and
`Pr T'.m₁ T'.BG T'.BG₂ T'.κ T'.t`. -/
theorem StepTowerG.exists_grow {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    (M : ℝ) (Pr : ℕ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hP : ∀ m₁ BG BG₂ κ, ∀ᶠ t in 𝓝[>] (0 : ℝ), Pr m₁ BG BG₂ κ t) :
    ∃ T' : StepTowerG d L N κmin, M ≤ (L : ℝ) ^ T'.m₁ ∧ T.m₁ ≤ T'.m₁ ∧ T'.t ≤ T.t ∧
      T'.c = T.c ∧ T'.BG = T.BG ∧ T'.κ = T.κ ∧ T'.c₂ = T.c₂ ∧ T'.BG₂ = T.BG₂ ∧
      T'.δc = T.δc ∧ T'.δ = T.δ ∧ T'.δ' = T.δ' ∧ Pr T'.m₁ T'.BG T'.BG₂ T'.κ T'.t ∧
      T'.κ0 = T.κ0 ∧ T'.m₀ = T.m₀ := by
  have hLr : (1 : ℝ) < (L : ℝ) := by exact_mod_cast (by have := T.hL; omega : 1 < L)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hLr
  set m : ℕ := max T.m₁ n with hm
  have hTm : T.m₁ ≤ m := le_max_left _ _
  have h4 : 4 ≤ m := T.m₁_four.trans hTm
  have hMm : M ≤ (L : ℝ) ^ m := hn.le.trans (pow_le_pow_right₀ hLr.le (le_max_right _ _))
  have hpow : (L : ℝ) ^ T.m₁ ≤ (L : ℝ) ^ m := pow_le_pow_right₀ hLr.le hTm
  obtain ⟨hC⟩ := T.core
  have hν0 : 0 ≤ νref L := by unfold νref; positivity
  have hν : νref L * (L : ℝ) ^ (2 * (1 + 1)) ≤ 1 := by
    unfold νref
    rw [one_div, inv_mul_eq_div, div_le_one (by positivity)]
  obtain ⟨n', ⟨S⟩, ⟨SH⟩, hG, hG', HBp⟩ := LevelStep.hpair_lvG T.hd T.hL hν0 hν m h4
  have hev := flCore_level_eventually (N := N) S SH hG hG' HBp hC.hS hC.hκ (hC.hM.trans hpow)
    hC.hS2 (hC.hM2.trans hpow)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ T.t :=
    eventually_nhdsWithin_of_eventually_nhds ((eventually_lt_nhds T.t_pos).mono fun _ h => h.le)
  obtain ⟨t', ⟨hC'⟩, hPt, ht0, htT⟩ :=
    (hev.and ((hP m T.BG T.BG₂ T.κ).and (hpos.and hle))).exists
  obtain ⟨Ts, hTst, hTsm, hTsc, hTsB, hTsκ, hTsc₂, hTsB₂, hTsδc, hTsδ, hTsδ', hTs0, hTsm₀⟩ :=
    T.exists_shrink ht0 htT
  have hcore : Nonempty (FlCore N (LevelStep.GpG d L 9 m 1) (LevelStep.HmG d L 9 m 1) 1 (νref L) Ts.c Ts.BG Ts.κ
      Ts.t (levelKc d L) (Cchi d L) Ts.c₂ Ts.BG₂ Ts.t) := by
    rw [hTsc, hTsB, hTsκ, hTst, hTsc₂, hTsB₂]
    exact ⟨hC'⟩
  have hpow' : (L : ℝ) ^ Ts.m₁ ≤ (L : ℝ) ^ m := by rw [hTsm]; exact hpow
  refine ⟨{ Ts with
    m₁ := m
    m₁_four := h4
    core := hcore
    large_block := Ts.large_block.trans hpow'
    block_base := Ts.block_base.trans hpow' }, hMm, hTm, ?_, hTsc, hTsB, hTsκ, hTsc₂, hTsB₂,
    hTsδc, hTsδ, hTsδ', ?_, hTs0, hTsm₀⟩
  · show Ts.t ≤ T.t
    rw [hTst]; exact htT
  · show Pr m Ts.BG Ts.BG₂ Ts.κ Ts.t
    rw [hTsB, hTsB₂, hTsκ, hTst]
    exact hPt

/-- **A tower with a larger block.**  For every tower `T`, bound `M` and predicate `Pr` on
`(m₁, BG, BG₂, κ, t)` that holds eventually as `t → 0+`, there is a tower `T'` with
`M ≤ 3^{T'.m₁}`, `T.m₁ ≤ T'.m₁`, `T'.t ≤ T.t`, the other constants of `T`, and
`Pr T'.m₁ T'.BG T'.BG₂ T'.κ T'.t`. -/
theorem exists_stepTower_grow {κmin : ℝ} (T : StepTower κmin) (M : ℝ)
    (Pr : ℕ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hP : ∀ m₁ BG BG₂ κ, ∀ᶠ t in 𝓝[>] (0 : ℝ), Pr m₁ BG BG₂ κ t) :
    ∃ T' : StepTower κmin, M ≤ (3 : ℝ) ^ T'.m₁ ∧ T.m₁ ≤ T'.m₁ ∧ T'.t ≤ T.t ∧ T'.c = T.c ∧
      T'.BG = T.BG ∧ T'.κ = T.κ ∧ T'.c₂ = T.c₂ ∧ T'.BG₂ = T.BG₂ ∧ T'.δc = T.δc ∧
      T'.δ = T.δ ∧ T'.δ' = T.δ' ∧ Pr T'.m₁ T'.BG T'.BG₂ T'.κ T'.t := by
  obtain ⟨T', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
    T.toG.exists_grow M Pr hP
  exact ⟨T'.ofThree (h13.trans T.κ0_eq) (h14.trans rfl), by show M ≤ (3 : ℝ) ^ T'.m₁; exact_mod_cast h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11, h12⟩

/-- **General towers at the collar `4 d L³ + L` with a large block.**  For every cover index `m₀`,
floor `κlo` and `θ > 0` there are `κmin ≥ κlo`, a tower `T : StepTowerG d L N κmin` with `κ₀ = a_Ent + 2`
and `m₀ = 1`, and constants `δ₃`, `δ_fl`, `κ_dec` with `ChainNum`, `FlNum` at the collar
`4 d L³ + L` and the step radius `T.t`, the two label-rate inequalities at `m₀`, and the closeness ratio
`K₂ · 2 · composedCloseBound(…, C_{Ξ1}, 4 d L³ + L) ≤ θ`. -/
theorem StepTowerG.exists_collar (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
    (m₀ : ℕ) (κlo : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ (κmin : ℝ) (_ : κlo ≤ κmin) (T : StepTowerG d L N κmin) (δ₃ δfl κdec : ℝ),
      T.m₀ = 1 ∧ T.κ0 = aEnt d L + 2 ∧
      ChainNum d L N T.m₁ T.BG T.κ (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) T.t δ₃ ∧
      FlNum d L N T.BG T.BG₂ T.κ T.t δ₃ T.t δfl ∧
      4 * (d : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ T.κ ∧
      (2 * T.κdec - 1) * ((L : ℝ) ^ (m₀ - 1) + 2 * (d : ℝ) * (L : ℝ) ^ m₀ *
        ((((L ^ (m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L) + 1 ≤ 2 * κdec ∧
      xiK2 d L N * (2 * composedCloseBound d L N T.m₁ T.BG T.κ (xiC1 d)
        (4 * (d : ℝ) * (L : ℝ) ^ 3 + L)) ≤ θ := by
  obtain ⟨κmin, hlo, hk⟩ := StepTowerG.exists_labelRate d L N m₀ κlo
  obtain ⟨T₁, -, hm₁, h₁⟩ := StepTowerG.exists_pred d L N hd hL hN κmin
    (fun _ _ _ _ _ => True) (fun _ _ _ _ => Filter.Eventually.of_forall fun _ => trivial)
  obtain ⟨hC₁⟩ := T₁.core
  obtain ⟨M, hM⟩ := exists_pow_close_leG (d := d) (L := L) (N := N) (BG := T₁.BG) (κ := T₁.κ)
    hd hL hC₁.hS.fam.2.1 hθ
  obtain ⟨T, hMT, -, -, -, hB, hκ, -, -, -, -, -, hPr, h0, hm⟩ := T₁.exists_grow M
    (fun m₁ BG BG₂ κ t => 0 ≤ BG → 0 ≤ BG₂ → ∃ δ₃ δfl : ℝ,
      ChainNum d L N m₁ BG κ (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) t δ₃ ∧
      FlNum d L N BG BG₂ κ t δ₃ t δfl)
    (fun m₁ BG BG₂ κ => by
      by_cases h : 0 ≤ BG ∧ 0 ≤ BG₂
      · exact (BgSettingData.joint_num_eventually d L N m₁ (by omega) h.1 h.2 κ
          (4 * (d : ℝ) * (L : ℝ) ^ 3 + L)).mono fun t ht _ _ => ht
      · exact Eventually.of_forall fun t h1 h2 => absurd ⟨h1, h2⟩ h)
  obtain ⟨hC⟩ := T.core
  obtain ⟨δ₃, δfl, h1, h2⟩ := hPr hC.hS.fam.2.1 hC.hS2.fam.2.1
  obtain ⟨κdec, h3, h4⟩ := hk T (h0.trans h₁)
  refine ⟨κmin, hlo, T, δ₃, δfl, κdec, hm.trans hm₁, h0.trans h₁, h1, h2, h3, h4, ?_⟩
  rw [hB, hκ]
  exact hM T.m₁ hMT

/-- **Towers at the collar `327` with a large block.**  For every cover index `m₀`, floor `κlo`
and `θ > 0` there are `κmin ≥ κlo`, a tower `T : StepTower κmin` and constants `δ₃`, `δ_fl`,
`κ_dec` with `ChainNum`, `FlNum` at the collar `327` and the step radius `T.t`, the two label-rate
inequalities at `m₀`, and the closeness ratio `K₂ · 2 · composedCloseBound(…, C_{Ξ1}, 327) ≤ θ`. -/
theorem exists_stepTower_collar (m₀ : ℕ) (κlo : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ (κmin : ℝ) (_ : κlo ≤ κmin) (T : StepTower κmin) (δ₃ δfl κdec : ℝ),
      ChainNum 3 3 2 T.m₁ T.BG T.κ 327 T.t δ₃ ∧ FlNum 3 3 2 T.BG T.BG₂ T.κ T.t δ₃ T.t δfl ∧
      4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ T.κ ∧
      (2 * T.κdec - 1) * (((3 : ℕ) : ℝ) ^ (m₀ - 1) + 2 * ((3 : ℕ) : ℝ) *
        ((3 : ℕ) : ℝ) ^ m₀ * ((((3 ^ (m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3) + 1 ≤ 2 * κdec ∧
      xiK2 3 3 2 * (2 * composedCloseBound 3 3 2 T.m₁ T.BG T.κ (xiC1 3) 327) ≤ θ := by
  obtain ⟨κmin, hlo, T, δ₃, δfl, κdec, hm, h0, h1, h2, h3, h4, h5⟩ :=
    StepTowerG.exists_collar 3 3 2 le_rfl le_rfl le_rfl m₀ κlo hθ
  have e : (4 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 3 + ((3 : ℕ) : ℝ)) = 327 := by norm_num
  rw [e] at h1 h5
  exact ⟨κmin, hlo, T.ofThree h0 hm, δ₃, δfl, κdec, h1, h2, h3, h4, h5⟩

end Balaban.Inhabited
