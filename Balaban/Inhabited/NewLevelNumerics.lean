/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerCollarTower
public import Balaban.Inhabited.StepTowerSmall
public import Balaban.Inhabited.BgSettingDataNum
public import Balaban.Fluctuation.Prop33CloseC7
public import Balaban.Localization.Decoupled2Background
public import Balaban.Localization.Decoupled2Self
public import Balaban.Localization.P6PairLocFinal

/-!
# The numerics of the new level on the local generating sets (route R-LOC, ruling R3)

The final theorem of the new level on the local generating sets `Gb(T′)`
(`NewLevelSystem.localFamily_castLocal_of`) takes, besides the numerics of the chain at the step
radius `t`, the numerics at the gate radius `ε′ = (2 K₁ + 2) C₁ t` and at the cover constants of
the local pairs (`mixedKc`, `selfKc`).  They are bundled here (`NewLevelNumerics`) and shown to be
satisfiable together with the conditions of the chain's towers (`exists_newLevelNumerics`, hard
rule 10).

* `DecSpecs.mono`, `Dec2.DecSpecs.mono`: the specifications are monotone in `(c, B_G)`;
* `FlNum.mono_δ₁`: `FlNum` at a smaller radius `δ₁` of the fluctuation ball;
* `StepTowerG.exists_upgrade`: a tower with larger constants `(c, B_G, c₂, B_{G₂})` satisfying the
  specifications, a larger block and a smaller step radius, with an eventual predicate;
* `NewLevelNumerics`, `exists_newLevelNumerics` (its core `exists_newLevelNumerics_gen`, with a
  predicate on the block).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Filter
  Topology

section Mono

/-- **The specifications of Theorem I-4a are monotone in the constants.** -/
theorem _root_.Balaban.Localization.DecSpecs.mono {d L : ℕ} [NeZero L] {c c' BG BG' : ℝ}
    (h : DecSpecs d L c BG) (hc : c ≤ c') (hB : BG ≤ BG') : DecSpecs d L c' BG' :=
  ⟨(h.fam.mono_c hc).mono_BG hB, h.dg2.mono hc hB, h.close.mono hc hB, h.one.mono_c hc,
    h.an.mono_c hc⟩

/-- **The cover specifications of Theorem I-4a are monotone in the constants.** -/
theorem _root_.Balaban.Localization.Dec2.DecSpecs.mono {d L : ℕ} [NeZero L] {Kc Cx c c' BG BG' : ℝ}
    (h : Dec2.DecSpecs d L Kc Cx c BG) (hc : c ≤ c') (hB : BG ≤ BG') :
    Dec2.DecSpecs d L Kc Cx c' BG' :=
  ⟨(h.fam.mono_c hc).mono_BG hB, h.dg2.mono hc hB, h.close.mono hc hB, h.one.mono_c hc,
    h.an.mono_c hc⟩

/-- **`FlNum` at a smaller radius of the fluctuation ball.** -/
theorem _root_.Balaban.Localization.FlNum.mono_δ₁ {d L N : ℕ} [NeZero L]
    {BG BG₂ κ eps δ₃ δ₁ δ₁' δfl : ℝ} (h : FlNum d L N BG BG₂ κ eps δ₃ δ₁' δfl) (hd : 0 < d)
    (hBG₂ : 0 ≤ BG₂) (h0 : 0 < δ₁) (hle : δ₁ ≤ δ₁') : FlNum d L N BG BG₂ κ eps δ₃ δ₁ δfl where
  δ₁_pos := h0
  δ₁_le := hle.trans h.δ₁_le
  B_le := h.B_le
  B_one := h.B_one
  phi_lt := h.phi_lt
  flb := by
    have hB0 : 0 ≤ famConst d L BG₂ κ := by
      have := famConst_ge_one (L := L) hBG₂ κ hd; linarith
    have hk := cK2'_nonneg (d := d) (L := L) (N := N) hB0
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    refine le_trans ?_ h.flb
    apply mul_le_mul_of_nonneg_left _ hN
    nlinarith
  δfl_nn := h.δfl_nn
  δfl_le_one := h.δfl_le_one
  c1_f := h.c1_f
  star_f := h.star_f
  K1s_f := h.K1s_f
  sm_f := h.sm_f
  small₃ := h.small₃
  th₃ := h.th₃

end Mono

section Upgrade

/-- **A tower with larger constants.**  For a tower `T` and constants `(c′, B_G′, c₂′, B_{G₂}′)`
with the specifications of Theorem I-4a (`DecSpecs`, the cover specification at `levelKc`) and
`c₇(B_G′, κ) ≤ C₃`, a bound `M` and a predicate `Pr` holding eventually as `t → 0+`, there is a
tower `T′` with these constants, the same `κ, κ₀, m₀, δ_c, δ, δ′`, a block `M ≤ L^{m₁′}`,
`m₁ ≤ m₁′`, a smaller step radius and `Pr` at its constants. -/
theorem StepTowerG.exists_upgrade {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    {c' BG' c₂' BG₂' : ℝ} (hS' : DecSpecs d L c' BG')
    (hS2' : Dec2.DecSpecs d L (levelKc d L) (Cchi d L) c₂' BG₂')
    (hc7 : c7 d L N BG' T.κ ≤ thm73C3 d L N) (M : ℝ) (Pr : ℕ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hP : ∀ m₁ BG BG₂ κ, ∀ᶠ t in 𝓝[>] (0 : ℝ), Pr m₁ BG BG₂ κ t) :
    ∃ T' : StepTowerG d L N κmin, T'.c = c' ∧ T'.BG = BG' ∧ T'.c₂ = c₂' ∧ T'.BG₂ = BG₂' ∧
      T'.κ = T.κ ∧ T'.κ0 = T.κ0 ∧ T'.m₀ = T.m₀ ∧ T'.δc = T.δc ∧ T'.δ = T.δ ∧ T'.δ' = T.δ' ∧
      T.m₁ ≤ T'.m₁ ∧ M ≤ (L : ℝ) ^ T'.m₁ ∧ T'.t ≤ T.t ∧ Pr T'.m₁ T'.BG T'.BG₂ T'.κ T'.t := by
  have hd0 : 0 < d := by have := T.hd; omega
  have hLr : (1 : ℝ) < (L : ℝ) := by exact_mod_cast (by have := T.hL; omega : 1 < L)
  obtain ⟨hC⟩ := T.core
  have hκ : 0 < T.κ := hC.hκ
  set E := Real.exp (N0 d L * T.κ) with hE
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max M (max (c' * E) (c₂' * E))) hLr
  set m : ℕ := max T.m₁ n with hm
  have hTm : T.m₁ ≤ m := le_max_left _ _
  have h4 : 4 ≤ m := T.m₁_four.trans hTm
  have hnm : (L : ℝ) ^ n ≤ (L : ℝ) ^ m := pow_le_pow_right₀ hLr.le (le_max_right _ _)
  have hMm : M ≤ (L : ℝ) ^ m := (le_max_left _ _).trans (hn.le.trans hnm)
  have hcm : c' * E ≤ (L : ℝ) ^ m :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (hn.le.trans hnm)
  have hc₂m : c₂' * E ≤ (L : ℝ) ^ m :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (hn.le.trans hnm)
  have hpow : (L : ℝ) ^ T.m₁ ≤ (L : ℝ) ^ m := pow_le_pow_right₀ hLr.le hTm
  have hν0 : 0 ≤ νref L := by unfold νref; positivity
  have hν : νref L * (L : ℝ) ^ (2 * (1 + 1)) ≤ 1 := by
    unfold νref
    rw [one_div, inv_mul_eq_div, div_le_one (by positivity)]
  obtain ⟨n', ⟨Sg⟩, ⟨SH⟩, hG, hG', HBp⟩ := LevelStep.hpair_lvG T.hd T.hL hν0 hν m h4
  have hev := flCore_level_eventually (N := N) Sg SH hG hG' HBp hS' hκ hcm hS2' hc₂m
  -- the margins at the new constants hold for small step radii
  have hBG' : 0 ≤ BG' := hS'.fam.2.1
  have hBG₂' : 0 ≤ BG₂' := hS2'.fam.2.1
  have hK4 : 0 < K4 d L N BG' T.κ := K4_pos hBG' hd0
  have hB1 : 0 ≤ famConst d L BG₂' T.κ := by
    have := famConst_ge_one (L := L) hBG₂' T.κ hd0; linarith
  have hB1' : 0 ≤ famConst d L BG' T.κ := by
    have := famConst_ge_one (L := L) hBG' T.κ hd0; linarith
  have hc6 : 0 < c6' d L N (famConst d L BG₂' T.κ) (gamma1 d / 8) :=
    c6'_pos hB1 (by have := gamma1_pos hd0; positivity)
  have hδc : 0 < T.δc := by
    have hK40 : 0 ≤ K4 d L N T.BG T.κ := (K4_pos hC.hS.fam.2.1 hd0).le
    have hx : 0 ≤ xiC1 d * T.t := by have := one_le_xiC1 d; have := T.t_pos; positivity
    have : 0 ≤ decDomMargin d L N T.BG T.κ (xiC1 d * T.t) := by unfold decDomMargin; positivity
    linarith [T.dom_margin]
  have hco : 0 < coerciveConst d := coerciveConst_pos hd0
  have e1 := ev_lt (f := fun t : ℝ => decDomMargin d L N BG' T.κ (xiC1 d * t))
    (by unfold decDomMargin; fun_prop) (c := T.δc) (by simpa [decDomMargin] using hδc)
  have e2 := ev_lt (f := fun t : ℝ => K4 d L N BG' T.κ * (xiC1 d * t)) (by fun_prop)
    (c := coerciveConst d / 2) (by simpa using half_pos hco)
  have e3 := ev_lt (f := fun t : ℝ => cK2 d L N * t) (by fun_prop)
    (c := c6' d L N (famConst d L BG₂' T.κ) (gamma1 d / 8)) (by simpa using hc6)
  have e4 := ev_lt (f := fun t : ℝ => cK2' d L N (famConst d L BG₂' T.κ) * t) (by fun_prop)
    (c := c6' d L N (famConst d L BG₂' T.κ) (gamma1 d / 8)) (by simpa using hc6)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ T.t :=
    eventually_nhdsWithin_of_eventually_nhds ((eventually_lt_nhds T.t_pos).mono fun _ h => h.le)
  have wk : ∀ {p : ℝ → Prop}, (∀ᶠ t in 𝓝 (0 : ℝ), p t) → ∀ᶠ t in 𝓝[>] (0 : ℝ), p t :=
    fun h => eventually_nhdsWithin_of_eventually_nhds h
  obtain ⟨t', ⟨hC'⟩, hPt, h1, h2, h3, h5, ht0, htT⟩ :=
    (hev.and ((hP m BG' BG₂' T.κ).and ((wk e1).and ((wk e2).and ((wk e3).and ((wk e4).and
      (hpos.and hle))))))).exists
  have hcK2 : 0 < cK2 d L N := cK2_pos d L N
  have hK1 : 0 < bgK1 d L N := bgK1_pos d L N
  have hX : 0 ≤ xiC1 d := by have := one_le_xiC1 d; linarith
  have hC4 : (8 : ℝ) ≤ compC4 d := compC4_ge d
  have hxt : xiC1 d * t' ≤ xiC1 d * T.t := mul_le_mul_of_nonneg_left htT hX
  refine ⟨{ T with
    m₁ := m
    c := c'
    BG := BG'
    c₂ := c₂'
    BG₂ := BG₂'
    t := t'
    m₁_four := h4
    t_pos := ht0
    core := ⟨hC'⟩
    c7_cap := hc7
    large_block := T.large_block.trans hpow
    dom_margin := h1
    coer_margin := h2
    t_cap := by linarith [T.t_cap]
    bg0_cap := by nlinarith [T.bg0_cap]
    cK2_cap := h3.le
    cK2'_cap := h5.le
    bg1_cap := by nlinarith [T.bg1_cap, mul_le_mul_of_nonneg_left hxt hK1.le]
    fam_nonneg := hB1
    block_base := T.block_base.trans hpow
    xi_small := by nlinarith [T.xi_small]
    rho_nonneg := by
      unfold rho4
      exact (c6'_pos hB1' (by have := gamma1_pos hd0; positivity)).le },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hTm, hMm, htT, hPt⟩

end Upgrade

section Numerics

/-- **The numerics of the new level on the local generating sets** at the constants
`(m₁, c, B_G, κ, t, c₂, B_{G₂}, δ_c)` of a tower, the collar `r₀` and the gate radius `ε′`: the
cover specifications of the decoupling pairs of the local pairs (`mixedKc`) and of the determinant part
(`selfKc`) with their block caps, the cap `c*_X(C_χ) e^{N₀κ} ≤ L^{m₁}` of the local `HatConn`
theory, and at the gate radius `ε′ ≥ (2 K₁ + 2) C₁ t ≥ t` the conditions `ChainNum`, `FlNum` and the
margins of the covariance chart (the smallness of the source, "for `β` large"). -/
structure NewLevelNumerics (d L N m₁ : ℕ) [NeZero L] (c BG κ t c₂ BG₂ δc r₀ eps' : ℝ) where
  /-- the cover specification of the background pairs of a local set -/
  hSm : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG
  /-- the constant of the cover specification of the fluctuation pairs of a local set -/
  c₂m : ℝ
  hS2m : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂m BG₂
  hM2m : c₂m * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁
  /-- the constant of the self cover of the determinant part -/
  c₃ : ℝ
  hS3 : Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c₃ BG
  hM3 : c₃ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁
  hMXd : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁
  /-- the gate radius -/
  hle : t ≤ eps'
  hεr : (2 * bgK1 d L N + 2) * xiC1 d * t ≤ eps'
  /-- the settings of the terms at the gate radius -/
  δ₃' : ℝ
  δfl' : ℝ
  chain' : ChainNum d L N m₁ BG κ r₀ eps' δ₃'
  fl' : FlNum d L N BG BG₂ κ eps' δ₃' eps' δfl'
  /-- the margins of the covariance chart at the gate radius -/
  dm' : decDomMargin d L N BG κ (xiC1 d * eps') < δc
  α' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2

/-- **Core of `exists_newLevelNumerics`: the numerics of the new level at a tower with a large block.**
For every `κ_min ≥ 1/C₃`, collar `r₀` and predicate `PM B_G κ m₁` on the block exponent that holds for
every large block (`L^{m₁} ≥ M(B_G, κ)`, `B_G ≥ 0`), there is a tower `T : StepTowerG d L N κ_min`
(with `m₀ = 1`, `κ₀ = a_Ent + 2`, `ChainNum` and `FlNum` at its step radius) whose constants satisfy
`NewLevelNumerics` at the gate radius `ε′ = (2 K₁ + 2) C₁ T.t` and `PM T.BG T.κ T.m₁`. -/
theorem exists_newLevelNumerics_gen (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
    {κmin : ℝ} (hκmin : 1 / thm73C3 d L N ≤ κmin) (r₀ : ℝ) (PM : ℝ → ℝ → ℕ → Prop)
    (hPM : ∀ BG κ : ℝ, 0 ≤ BG → ∃ M : ℝ, ∀ m₁ : ℕ, M ≤ (L : ℝ) ^ m₁ → PM BG κ m₁) :
    ∃ (T : StepTowerG d L N κmin) (δ₃ δfl : ℝ), T.m₀ = 1 ∧ T.κ0 = aEnt d L + 2 ∧
      ChainNum d L N T.m₁ T.BG T.κ r₀ T.t δ₃ ∧ FlNum d L N T.BG T.BG₂ T.κ T.t δ₃ T.t δfl ∧
      Nonempty (NewLevelNumerics d L N T.m₁ T.c T.BG T.κ T.t T.c₂ T.BG₂ T.δc r₀
        ((2 * bgK1 d L N + 2) * xiC1 d * T.t)) ∧ PM T.BG T.κ T.m₁ := by
  have hd0 : 0 < d := by omega
  obtain ⟨T₀, -, hm₀, h0⟩ := StepTowerG.exists_pred d L N hd hL hN κmin
    (fun _ _ _ _ _ => True) (fun _ _ _ _ => Eventually.of_forall fun _ => trivial)
  obtain ⟨hC₀⟩ := T₀.core
  obtain ⟨cm, BGm, hSm⟩ := Dec2.decSpecs_exists (d := d) (L := L) (Kc := Dec2.mixedKc d L)
    (Cx := Cchi d L) hd hL (mixedKc_nonneg L hd) (Cchi_nonneg d L)
  obtain ⟨cs, BGs, hSs⟩ := Dec2.decSpecs_exists (d := d) (L := L) (Kc := Dec2.selfKc d L)
    (Cx := Cchi d L) hd hL (Dec2.selfKc_nonneg hd hL) (Cchi_nonneg d L)
  set c' := max T₀.c (max cm cs) with hc'
  set BG' := max (max T₀.BG (max BGm BGs)) 1 with hBG'
  set c₂' := max T₀.c₂ cm with hc₂'
  set BG₂' := max T₀.BG₂ BGm with hBG₂'
  have hS' : DecSpecs d L c' BG' := hC₀.hS.mono (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_left _ _))
  have hS2' : Dec2.DecSpecs d L (levelKc d L) (Cchi d L) c₂' BG₂' :=
    hC₀.hS2.mono (le_max_left _ _) (le_max_left _ _)
  have hc7 : c7 d L N BG' T₀.κ ≤ thm73C3 d L N :=
    c7_le_thm73C3_of_large hd0 (le_max_right _ _) (hκmin.trans T₀.κmin_le)
  obtain ⟨M₁, hM₁⟩ := hPM BG' T₀.κ (le_trans zero_le_one (le_max_right _ _))
  set Kg : ℝ := (2 * bgK1 d L N + 2) * xiC1 d with hKg
  have hK1 := bgK1_pos d L N
  have hX1 := one_le_xiC1 d
  have hKg1 : 1 ≤ Kg := by rw [hKg]; nlinarith
  have hKg0 : 0 < Kg := by linarith
  have hδc : 0 < T₀.δc := by
    have hK40 : 0 ≤ K4 d L N T₀.BG T₀.κ := (K4_pos hC₀.hS.fam.2.1 hd0).le
    have hx : 0 ≤ xiC1 d * T₀.t := by have := T₀.t_pos; positivity
    have : 0 ≤ decDomMargin d L N T₀.BG T₀.κ (xiC1 d * T₀.t) := by
      unfold decDomMargin; positivity
    linarith [T₀.dom_margin]
  have hco : 0 < coerciveConst d := coerciveConst_pos hd0
  -- the gate radius tends to `0+` with the step radius
  have hT : Tendsto (fun t : ℝ => Kg * t) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h : Tendsto (fun t : ℝ => Kg * t) (𝓝 (0 : ℝ)) (𝓝 (Kg * 0)) :=
        tendsto_id.const_mul Kg
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos hKg0 ht
  set Pr : ℕ → ℝ → ℝ → ℝ → ℝ → Prop := fun m₁ BG BG₂ κ t =>
    (0 ≤ BG → 0 ≤ BG₂ → ∃ δ₃ δfl : ℝ, ChainNum d L N m₁ BG κ r₀ t δ₃ ∧
      FlNum d L N BG BG₂ κ t δ₃ t δfl) ∧
    (0 ≤ BG → 0 ≤ BG₂ → ∃ δ₃ δfl : ℝ, ChainNum d L N m₁ BG κ r₀ (Kg * t) δ₃ ∧
      FlNum d L N BG BG₂ κ (Kg * t) δ₃ (Kg * t) δfl) ∧
    (0 ≤ BG → decDomMargin d L N BG κ (xiC1 d * (Kg * t)) < T₀.δc ∧
      K4 d L N BG κ * (xiC1 d * (Kg * t)) < coerciveConst d / 2) with hPr
  have hP : ∀ m₁ BG BG₂ κ, ∀ᶠ t in 𝓝[>] (0 : ℝ), Pr m₁ BG BG₂ κ t := by
    intro m₁ BG BG₂ κ
    have wk : ∀ {p : ℝ → Prop}, (∀ᶠ t in 𝓝 (0 : ℝ), p t) → ∀ᶠ t in 𝓝[>] (0 : ℝ), p t :=
      fun h => eventually_nhdsWithin_of_eventually_nhds h
    by_cases h : 0 ≤ BG ∧ 0 ≤ BG₂
    · have e1 := BgSettingData.joint_num_eventually d L N m₁ hd0 h.1 h.2 κ r₀
      have e2 := hT.eventually e1
      have e3 := ev_lt (f := fun t : ℝ => decDomMargin d L N BG κ (xiC1 d * (Kg * t)))
        (by unfold decDomMargin; fun_prop) (c := T₀.δc) (by simpa [decDomMargin] using hδc)
      have e4 := ev_lt (f := fun t : ℝ => K4 d L N BG κ * (xiC1 d * (Kg * t))) (by fun_prop)
        (c := coerciveConst d / 2) (by simpa using half_pos hco)
      filter_upwards [e1, e2, wk e3, wk e4] with t h1 h2 h3 h4
      exact ⟨fun _ _ => h1, fun _ _ => h2, fun _ => ⟨h3, h4⟩⟩
    · by_cases hB : 0 ≤ BG
      · have e3 := ev_lt (f := fun t : ℝ => decDomMargin d L N BG κ (xiC1 d * (Kg * t)))
          (by unfold decDomMargin; fun_prop) (c := T₀.δc) (by simpa [decDomMargin] using hδc)
        have e4 := ev_lt (f := fun t : ℝ => K4 d L N BG κ * (xiC1 d * (Kg * t)))
          (by fun_prop) (c := coerciveConst d / 2) (by simpa using half_pos hco)
        filter_upwards [wk e3, wk e4] with t h3 h4
        exact ⟨fun h1 h2 => absurd ⟨h1, h2⟩ h, fun h1 h2 => absurd ⟨h1, h2⟩ h,
          fun _ => ⟨h3, h4⟩⟩
      · exact Eventually.of_forall fun t => ⟨fun h1 => absurd h1 hB, fun h1 => absurd h1 hB,
          fun h1 => absurd h1 hB⟩
  obtain ⟨T, hTc, hTB, hTc₂, hTB₂, hTκ, hT0, hTm₀, hTδc, -, -, -, hMT, -, hPT⟩ :=
    T₀.exists_upgrade hS' hS2' hc7
      (max M₁ (Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * T₀.κ))) Pr hP
  obtain ⟨hCT⟩ := T.core
  have hBT : 0 ≤ T.BG := hCT.hS.fam.2.1
  have hBT₂ : 0 ≤ T.BG₂ := hCT.hS2.fam.2.1
  obtain ⟨δ₃, δfl, h1, h2⟩ := hPT.1 hBT hBT₂
  obtain ⟨δ₃', δfl', h3, h4⟩ := hPT.2.1 hBT hBT₂
  obtain ⟨h5, h6⟩ := hPT.2.2 hBT
  refine ⟨T, δ₃, δfl, hTm₀.trans hm₀, hT0.trans h0, h1, h2, ⟨{
    hSm := by
      rw [hTc, hTB]
      exact hSm.mono ((le_max_left _ _).trans (le_max_right _ _))
        (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _))
    c₂m := T.c₂
    hS2m := by
      rw [hTc₂, hTB₂]
      exact hSm.mono (le_max_right _ _) (le_max_right _ _)
    hM2m := hCT.hM2
    c₃ := T.c
    hS3 := by
      rw [hTc, hTB]
      exact hSs.mono ((le_max_right _ _).trans (le_max_right _ _))
        (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _))
    hM3 := hCT.hM
    hMXd := by rw [hTκ]; exact (le_max_right _ _).trans hMT
    hle := by
      have := T.t_pos
      nlinarith
    hεr := le_rfl
    δ₃' := δ₃'
    δfl' := δfl'
    chain' := h3
    fl' := h4
    dm' := by rw [hTδc]; exact h5
    α' := h6 }⟩, ?_⟩
  rw [hTB, hTκ]
  exact hM₁ T.m₁ ((le_max_left _ _).trans hMT)

/-- **The numerics of the new level are satisfiable by the chain's towers** (hard rule 10): for
every `κ_min ≥ 1/C₃` and collar `r₀` there is a tower `T : StepTowerG d L N κ_min` (with
`m₀ = 1`, `κ₀ = a_Ent + 2`, `ChainNum` and `FlNum` at its step radius, as in
`StepTowerG.exists_base`) whose constants satisfy `NewLevelNumerics` at the gate radius
`ε′ = (2 K₁ + 2) C₁ T.t`. -/
theorem exists_newLevelNumerics (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
    {κmin : ℝ} (hκmin : 1 / thm73C3 d L N ≤ κmin) (r₀ : ℝ) :
    ∃ (T : StepTowerG d L N κmin) (δ₃ δfl : ℝ), T.m₀ = 1 ∧ T.κ0 = aEnt d L + 2 ∧
      ChainNum d L N T.m₁ T.BG T.κ r₀ T.t δ₃ ∧ FlNum d L N T.BG T.BG₂ T.κ T.t δ₃ T.t δfl ∧
      Nonempty (NewLevelNumerics d L N T.m₁ T.c T.BG T.κ T.t T.c₂ T.BG₂ T.δc r₀
        ((2 * bgK1 d L N + 2) * xiC1 d * T.t)) := by
  obtain ⟨T, δ₃, δfl, h1, h2, h3, h4, h5, -⟩ := exists_newLevelNumerics_gen d L N hd hL hN hκmin r₀
    (fun _ _ _ => True) (fun _ _ _ => ⟨0, fun _ _ => trivial⟩)
  exact ⟨T, δ₃, δfl, h1, h2, h3, h4, h5⟩

end Numerics

end Balaban.Inhabited
