/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassCentre
public import Balaban.SmallField.LocalGeneratorRadius
public import Balaban.Fluctuation.ClassOldBirthConsts
public import Balaban.LargeField.R.ActionConvRatio
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The whole-level chart of the new level and the local charts of its terms

Input `hchart` of `localClass_centre_Eloc_eq`, `localClass_eucEloc_centre`,
`localClass_centre_Edens_eq`, `localClass_site_Mloc_eq` and `localClass_eucMloc_site`
(`LocalClassCentre.lean`): every pair of the domain `Ξ^c_{k+1}(levelGS (k + 1); 1, ε_{k+1})` lies in
the class domain `Ξ^c_{k+1}(𝔹_{k+1}(Y⁺); 1, ε_{k+1})` of every polymer `Y`, at the **same** radius.

**What the restriction route gives.**  Restricting the datum of a whole-level pair to the data sites
of the local generating set and recomputing its backgrounds there (P3 (4.44); landed
`localB_xiCData_restrict`) gives:

* the crude form `localB_xiDom_of_ambient_xiDom`: local radius `c₀ + (2 K₁ + 1) c₁`, independent of
  the ambient radius.  For the class radius `ε_j` of P4 (H.1) this is **false at every level** under
  the smallness of `α₀` used below (`not_crudeBudget_le_eps`), and false at all large levels for
  every `α₀` (`eventually_eps_lt`): `ε_j → 0`, the budget is a fixed positive number;
* the sharp form (data estimate (Ξ1), `xiC_one_subset`, then (D2), `psiTildeC_subset_xiC`):
  `Ξ^c_K(levelGS K; 1, ε) ⊆ Ξ^c_K(localB K X; 1, K_loc ε)`, `K_loc = (2 K₁ + 2) C₁`
  (`localB_xiDom_top_linear`: the top level `j = K` at any background mass `ν` with
  `ν L^{2K} ≤ 1`; the landed `localB_xiDom_massless_linear` is the case `ν = 0` at every level).

So `hchart` at one radius is not derivable from the restriction route, and the loss `K_loc > 1`
cannot be placed on the successor class either: its terms would have to be analytic on the local
chart at `K_loc ε_{k+1}`, which needs `K_loc ε_{k+1} + δ ≤ ε_k` (P3 (4.37)), false for the class
sequence (landed `not_localLoss_eps_succ_le`).

**The replacement used for the new level (`LocalClassDensityCentre.lean`).**  The chart inclusion
is needed only to show that the completed term `TE ∘ cpl` takes the value `TE` at the pairs of the
whole-level domain.  Completing in the **larger** local chart `Ξ^c_{k+1}(𝔹_{k+1}(Y⁺); 1, εL)`,
`εL ≥ K_loc ε_{k+1}`, whose pairs contain the whole-level pairs (`levelGS_xiFieldDom_sub_localB`),
this needs of `TE` only its **locality** on the larger chart, not its analyticity or its bound there.
Locality on a chart of radius `eps` requires only the numerical smallness of `eps` (the landed
`localB_eTermHat_evTerm_local` takes the old-term functional as an arbitrary function), so (4.37)
does not enter.  The analyticity, the bound and the rotation invariance stay at the class radius.

* `localB_xiDom_top_linear`, `levelGS_xiFieldDom_sub_localB`: the sharp chart inclusion with the
  loss `K_loc`, at the top level, in the form of the class domains of the polymers of level `k + 1`;
* `Consts.eps_le_three_mul`, `levelGS_xiFieldDom_sub_localB_eps`: the same for the class sequence
  `ε_j = P.eps d L j` and `εL = K_loc ε`, under the smallness of `α₀`;
* `not_crudeBudget_le_eps`, `eventually_eps_lt`: the crude loss is not available for the class;
* `eventually_exists_completion_witness`, `fieldDom_completion_analytic_param_of_sub`,
  `fieldDom_completion_extension_of_sub`: the completion in a larger field domain `Dom₂ ⊇ Dom₁` of
  a term analytic on `Dom₁` and local on `Dom₂` (the landed `fieldDom_completion_analytic_param`,
  `fieldDom_completion_extension` are the case `Dom₂ = Dom₁`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.LargeField Balaban.Fluctuation
  Filter Topology

/-! ### The sharp chart inclusion at the top level -/

section TopLoss

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁]

/-- **The whole-level chart of the top level lies in the local chart with the loss
`K_loc = (2 K₁ + 2) C₁`** (P3 (4.44); (Ξ1) and (D2)): for `1 ≤ K`, a background mass `ν` with
`BgHyp` (so `ν L^{2K} ≤ 1`) and `C₁ ε ≤ c₀, c₁`,
`Ξ^c_K(levelGS K; 1, ε) ⊆ Ξ^c_K(localB K X; 1, εb)` whenever `K_loc ε ≤ εb`.  The datum is
restricted to the data sites of `localB K X` and its backgrounds are recomputed there. -/
theorem localB_xiDom_top_linear (hK1 : 1 ≤ K) {X : Set (CTorus d L N₁ m₁ K)} {ϱ : ℝ}
    {hsep : ϱ ≤ minSep L (L ^ m₁)} {a : ℕ → ℝ} {ν ε εb : ℝ} (H : BgHyp d L K ϱ a ν)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1)
    (hc0 : xiC1 d * ε ≤ bgC0 d L N) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    (hεb : (2 * bgK1 d L N + 2) * (xiC1 d * ε) ≤ εb) {Ψ h : Fld d L N₁ m₁ K N}
    (hAmb : XiDom (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) K le_rfl)
      a ν K ε Ψ h) :
    XiDom (localB K le_rfl X hsep) a ν K εb Ψ h := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hΨ, hh, hXi⟩ := hAmb
  have hεpos : 0 < ε := hXi.2.1
  have hData := xiC_one_subset H hsmall hXi
  obtain ⟨_, _, Dr, Dc, hXR, hC, hU, hBC⟩ := hXi
  have hδpos : 0 < xiC1 d * ε := mul_pos (lt_of_lt_of_le zero_lt_one (one_le_xiC1 d)) hεpos
  have hmass : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * ε) ^ 2 ≤ (xiC1 d * ε) ^ 2 := by
    have h1 := H.massLe
    have h2 := sq_nonneg (xiC1 d * ε)
    nlinarith
  have hLoc : XiCData (localB K le_rfl X hsep) a ν K 1 εb
      (localBRestrict (X := X) (hsep := hsep) hK1 Dc) :=
    localB_xiCData_restrict hK1 H H.mass hδpos le_rfl hc0 hc1 hmass (by linarith) Dc
      ⟨Ψ₀, h₀, Ψ'', h'', hData, hC⟩
  refine localB_xiDom_of_xiCData_one le_rfl hLoc (fun x hx i => ?_) (fun x hx i => ?_)
  · rw [localBRestrict_Ψ hK1 Dc hx, hΨ x i, hC.1 x ((mem_dataSites _).2
      (Or.inl (localB_dataSites_subset_levelGS_omega_one hK1 le_rfl hx))) i]
  · rw [localBRestrict_h hK1 Dc hx, hh x i, hC.2 x (by simp [levelGS, hK1]) i]

end TopLoss

/-! ### The inclusion in the class domains of the polymers of the new level -/

section ClassForm

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

/-- **The whole-level domain of the new level lies in the larger local domain of every polymer**:
for two radius sequences with `K_loc ε_{k+1} ≤ εL_{k+1}` and `C₁ ε_{k+1} ≤ c₀, c₁`, every pair of
`Ξ^c_{k+1}(levelGS (k + 1); 1, ε_{k+1})` lies in `Ξ^c_{k+1}(localB (k + 1) X; 1, εL_{k+1})`, for every
set `X` (in the class: `X = Y⁺`). -/
theorem levelGS_xiFieldDom_sub_localB {a : ℕ → ℝ} {ν : ℝ} {εseq εL : ℕ → ℝ}
    (HB : BgHyp d L (k + 1) (minSep L (L ^ m₁)) a ν)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * εseq (k + 1)) ≤ 1)
    (hc0 : xiC1 d * εseq (k + 1) ≤ bgC0 d L N) (hc1 : xiC1 d * εseq (k + 1) ≤ bgC1 d L N)
    (hεL : (2 * bgK1 d L N + 2) * (xiC1 d * εseq (k + 1)) ≤ εL (k + 1))
    (X : Set (CTorus d L N₁ m₁ (k + 1))) {q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hq : (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
      (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
      q.1 q.2) :
    (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
      (localB (k + 1) (le_refl (k + 1)) X (le_refl (minSep L (L ^ m₁)))) q.1 q.2 :=
  localB_xiDom_top_linear (Nat.succ_pos k) HB hsmall hc0 hc1 hεL hq

end ClassForm

/-! ### The class sequence -/

section ClassSequence

/-- **The class radius is at most `3 α₀`**: `ε_j = α₀ (1 + ∑_{m ≥ j} m^{-2}) L^{-jα} ≤ 3 α₀` for
`α₀, α ≥ 0` (P4 (H.1)). -/
theorem Consts.eps_le_three_mul {d L : ℕ} [NeZero L] (P : Consts) (hα₀ : 0 ≤ P.α₀)
    (hα : 0 ≤ P.alpha d) (j : ℕ) : P.eps d L j ≤ 3 * P.α₀ := by
  have h1 := epsSeq_le_tail_zero L (P.alpha d) P.α₀ hα₀ hα j
  have h2 := ActionConv.epsTail_lt_three 0
  have h3 : P.α₀ * epsTail 0 ≤ P.α₀ * 3 := mul_le_mul_of_nonneg_left h2.le hα₀
  unfold Consts.eps
  linarith

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

/-- **`hchart` with the loss `K_loc` for the class sequence**: for `ε_j = P.eps d L j`, the larger
sequence `εL_j = K_loc ε_j` and `α₀` small (`(4d+6)(2d+1) 3α₀ ≤ 1`, `C₁ 3α₀ ≤ c₀, c₁`), every
pair of the whole-level domain of level `k + 1` lies in the local domain at radius `εL` of every
set `X`. -/
theorem levelGS_xiFieldDom_sub_localB_eps (P : Consts) {a : ℕ → ℝ} {ν : ℝ}
    (HB : BgHyp d L (k + 1) (minSep L (L ^ m₁)) a ν) (hα₀ : 0 ≤ P.α₀) (hα : 0 ≤ P.alpha d)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * (3 * P.α₀)) ≤ 1)
    (hc0 : xiC1 d * (3 * P.α₀) ≤ bgC0 d L N) (hc1 : xiC1 d * (3 * P.α₀) ≤ bgC1 d L N)
    (X : Set (CTorus d L N₁ m₁ (k + 1))) {q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hq : (xiFieldDom a ν (P.eps d L) :
      FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
      (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
      q.1 q.2) :
    (xiFieldDom a ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
      FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
      (localB (k + 1) (le_refl (k + 1)) X (le_refl (minSep L (L ^ m₁)))) q.1 q.2 := by
  have he := Consts.eps_le_three_mul (L := L) P hα₀ hα (k + 1)
  have hx := one_le_xiC1 d
  have hd0 : (0 : ℝ) ≤ (4 * d + 6) * (2 * d + 1) := by positivity
  refine levelGS_xiFieldDom_sub_localB HB ?_ ?_ ?_ ?_ X hq
  rotate_left 3
  · show (2 * bgK1 d L N + 2) * (xiC1 d * P.eps d L (k + 1)) ≤
      (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L (k + 1)
    exact le_of_eq (mul_assoc _ _ _).symm
  · have : (4 * d + 6) * ((2 * d + 1) * P.eps d L (k + 1)) ≤
        (4 * d + 6) * ((2 * d + 1) * (3 * P.α₀)) := by
      have := mul_le_mul_of_nonneg_left he hd0
      nlinarith
    linarith
  · exact (mul_le_mul_of_nonneg_left he (by linarith)).trans hc0
  · exact (mul_le_mul_of_nonneg_left he (by linarith)).trans hc1

/-- **The crude loss of `localB_xiDom_of_ambient_xiDom` is not available at the class radius**:
under the smallness `C₁ 3 α₀ ≤ c₀` of `levelGS_xiFieldDom_sub_localB_eps`, the budget
`c₀ + (2 K₁ + 1) c₁ ≤ ε_j` fails at every level `j`. -/
theorem not_crudeBudget_le_eps {d L N : ℕ} [NeZero L] (hd : 0 < d) (P : Consts)
    (hα₀ : 0 ≤ P.α₀) (hα : 0 ≤ P.alpha d) (hc0 : xiC1 d * (3 * P.α₀) ≤ bgC0 d L N) (j : ℕ) :
    ¬ (bgC0 d L N + (2 * bgK1 d L N + 1) * bgC1 d L N ≤ P.eps d L j) := by
  intro h
  have he := Consts.eps_le_three_mul (L := L) P hα₀ hα j
  have hx := one_le_xiC1 d
  have h3 : 3 * P.α₀ ≤ xiC1 d * (3 * P.α₀) := le_mul_of_one_le_left (by linarith) hx
  have hc1 : 0 < bgC1 d L N := bgC1_pos' hd
  have hK := bgK1_pos d L N
  have hb : 0 < (2 * bgK1 d L N + 1) * bgC1 d L N := by positivity
  linarith

/-- **The class radius tends to zero**: for `L ≥ 2`, `α > 0` and every `c > 0`, `ε_j < c` for all
large `j`.  In particular the crude budget `c₀ + (2 K₁ + 1) c₁ > 0` of
`localB_xiDom_of_ambient_xiDom` exceeds `ε_j` at all large levels, for every `α₀`. -/
theorem eventually_eps_lt {d L : ℕ} [NeZero L] (hL : 2 ≤ L) (P : Consts) (hα₀ : 0 ≤ P.α₀)
    (hα : 0 < P.alpha d) {c : ℝ} (hc : 0 < c) : ∀ᶠ j in atTop, P.eps d L j < c := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hq0 : 0 ≤ (L : ℝ) ^ (-P.alpha d) := Real.rpow_nonneg (by linarith) _
  have hq1 : (L : ℝ) ^ (-P.alpha d) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith)
  have ht : Tendsto (fun j : ℕ => 3 * P.α₀ * ((L : ℝ) ^ (-P.alpha d)) ^ j) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (3 * P.α₀)
    simpa using this
  filter_upwards [ht.eventually (gt_mem_nhds hc)] with j hj
  have h2 := ActionConv.epsTail_lt_three j
  have hp : 0 ≤ ((L : ℝ) ^ (-P.alpha d)) ^ j := pow_nonneg hq0 j
  have h3 : P.α₀ * epsTail j * ((L : ℝ) ^ (-P.alpha d)) ^ j ≤
      3 * P.α₀ * ((L : ℝ) ^ (-P.alpha d)) ^ j := by
    have := mul_le_mul_of_nonneg_left h2.le hα₀
    exact mul_le_mul_of_nonneg_right (by linarith) hp
  unfold Consts.eps epsSeq
  linarith

end ClassSequence

/-! ### The completion in a larger field domain -/

section Completion

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **Near a point of a field domain open relative to the layer-constant pairs, every projection
`Q p` has a witness in the domain**: `p₀ + Q p - Q p₀` lies in the domain for `p` near `p₀`, and it
equals `Q p` on `Y`. -/
theorem eventually_exists_completion_witness (Dom : FieldDom d L N₁ m₁ K N ϱ) (j : ℕ)
    (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (Y : Set (CTorus d L N₁ m₁ K))
    (hDL : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom.dom j G p.1 p.2 → p ∈ layerSub G)
    (hDo : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom.dom j G p.1 p.2 →
      ∀ᶠ q in 𝓝[layerSub G] p, Dom.dom j G q.1 q.2)
    {p₀ : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N} (hp₀ : Dom.dom j G p₀.1 p₀.2) :
    ∀ᶠ p in 𝓝 p₀, ∃ q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom.dom j G q.1 q.2 ∧
      ∀ z ∈ Y, q.1 z = (Classical.choose (exists_layerProj (N := N) G Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) G Y) p).2 z := by
  obtain ⟨hQU, -, hQid⟩ := Classical.choose_spec (exists_layerProj (N := N) G Y)
  set Q := Classical.choose (exists_layerProj (N := N) G Y) with hQ
  have hQc : Continuous Q := LinearMap.continuous_of_finiteDimensional Q
  have hφ : Tendsto (fun p => p₀ + (Q p - Q p₀)) (𝓝 p₀) (𝓝[layerSub G] p₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun p =>
      add_sub_mem_layerSub (hDL p₀ hp₀) (hQU p) (hQU p₀)⟩
    have hφc : Continuous (fun p => p₀ + (Q p - Q p₀)) :=
      continuous_const.add (hQc.sub continuous_const)
    have h := hφc.tendsto p₀
    simp only [sub_self, add_zero] at h
    exact h
  filter_upwards [hφ.eventually (hDo p₀ hp₀)] with p hp
  refine ⟨_, hp, fun z hz => ?_⟩
  obtain ⟨e1, e2⟩ := hQid p₀ (hDL p₀ hp₀) z hz
  simp only [Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub, Pi.add_apply,
    Pi.sub_apply, e1, e2]
  exact ⟨by abel, by abel⟩

/-- **The completion in a larger domain, with a parameter**: let `Dom₁ ⊆ Dom₂` be field domains
in the layer-constant pairs, `Dom₁` open relative to them, `cpl` the completion in `Dom₂`
(`fieldDom_completion_spec`), `T` analytic on `Dom₁ × Sp` and depending only on the restriction to
`Y` for pairs of `Dom₂`.  Then `(p, g) ↦ T (cpl p, g)` equals `T` on `Dom₂` and is analytic on
`Dom₁ × Sp`.  Near a point of `Dom₁` the completion in `Dom₁` exists, and the two completions give
the same value by the locality on `Dom₂`. -/
theorem fieldDom_completion_analytic_param_of_sub {S F : Type*} [NormedAddCommGroup S]
    [NormedSpace ℂ S] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Dom₁ Dom₂ : FieldDom d L N₁ m₁ K N ϱ) (j : ℕ)
    (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (Y : Set (CTorus d L N₁ m₁ K))
    (c : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N)
    (hc : ∀ p, c p = Classical.epsilon (fun q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N =>
      Dom₂.dom j G q.1 q.2 ∧ ∀ z ∈ Y,
        q.1 z = (Classical.choose (exists_layerProj (N := N) G Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) G Y) p).2 z))
    (h12 : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₁.dom j G p.1 p.2 →
      Dom₂.dom j G p.1 p.2)
    (hDL : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₂.dom j G p.1 p.2 → p ∈ layerSub G)
    (hDo : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₁.dom j G p.1 p.2 →
      ∀ᶠ q in 𝓝[layerSub G] p, Dom₁.dom j G q.1 q.2)
    {Sp : Set S} (T : (Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) × S → F)
    (hT : AnalyticOnNhd ℂ T ({p | Dom₁.dom j G p.1 p.2} ×ˢ Sp))
    (hloc : ∀ p p' : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₂.dom j G p.1 p.2 →
      Dom₂.dom j G p'.1 p'.2 → (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) →
      ∀ g, T (p, g) = T (p', g)) :
    (∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₂.dom j G p.1 p.2 → ∀ g,
      T (c p, g) = T (p, g)) ∧
    AnalyticOnNhd ℂ (fun q : (Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) × S => T (c q.1, q.2))
      ({p | Dom₁.dom j G p.1 p.2} ×ˢ Sp) := by
  obtain ⟨-, c2⟩ := fieldDom_completion_spec Dom₂ j G Y c hc hDL
  refine ⟨fun p hp g => hloc _ _ (c2 p hp).1 hp (c2 p hp).2 g, ?_⟩
  -- the completion in `Dom₁`
  set c₁ : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N :=
    fun p => Classical.epsilon (fun q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N =>
      Dom₁.dom j G q.1 q.2 ∧ ∀ z ∈ Y,
        q.1 z = (Classical.choose (exists_layerProj (N := N) G Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) G Y) p).2 z) with hc₁
  have hA := fieldDom_completion_analytic_param Dom₁ j G Y c₁ (fun _ => rfl)
    (fun p hp => hDL p (h12 p hp)) hDo T hT
    (fun p p' hp hp' hY g => hloc p p' (h12 _ hp) (h12 _ hp') hY g)
  rintro ⟨p₀, g₀⟩ ⟨hp₀, hg₀⟩
  refine (hA (p₀, g₀) ⟨hp₀, hg₀⟩).congr ?_
  have hev := (continuous_fst.tendsto (p₀, g₀)).eventually
    (eventually_exists_completion_witness Dom₁ j G Y (fun p hp => hDL p (h12 p hp)) hDo hp₀)
  filter_upwards [hev] with q hq
  obtain ⟨d1, d2⟩ := Classical.epsilon_spec hq
  obtain ⟨w, hw1, hw2⟩ := hq
  obtain ⟨e1, e2⟩ := Classical.epsilon_spec (p := fun q' : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N =>
      Dom₂.dom j G q'.1 q'.2 ∧ ∀ z ∈ Y,
        q'.1 z = (Classical.choose (exists_layerProj (N := N) G Y) q.1).1 z ∧
        q'.2 z = (Classical.choose (exists_layerProj (N := N) G Y) q.1).2 z)
    ⟨w, h12 w hw1, hw2⟩
  rw [← hc] at e1 e2
  exact hloc _ _ (h12 _ d1) e1 (fun z hz => ⟨(d2 z hz).1.trans (e2 z hz).1.symm,
    (d2 z hz).2.trans (e2 z hz).2.symm⟩) q.2

/-- **The completion in a larger domain** (`fieldDom_completion_analytic_param_of_sub` for a
function of the pair alone): `T ∘ cpl` depends only on the restriction to `Y` for all pairs, equals
`T` on `Dom₂` and is analytic on `Dom₁`. -/
theorem fieldDom_completion_extension_of_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Dom₁ Dom₂ : FieldDom d L N₁ m₁ K N ϱ) (j : ℕ)
    (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (Y : Set (CTorus d L N₁ m₁ K))
    (c : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N)
    (hc : ∀ p, c p = Classical.epsilon (fun q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N =>
      Dom₂.dom j G q.1 q.2 ∧ ∀ z ∈ Y,
        q.1 z = (Classical.choose (exists_layerProj (N := N) G Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) G Y) p).2 z))
    (h12 : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₁.dom j G p.1 p.2 →
      Dom₂.dom j G p.1 p.2)
    (hDL : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₂.dom j G p.1 p.2 → p ∈ layerSub G)
    (hDo : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₁.dom j G p.1 p.2 →
      ∀ᶠ q in 𝓝[layerSub G] p, Dom₁.dom j G q.1 q.2)
    (T : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → F)
    (hT : AnalyticOnNhd ℂ T {p | Dom₁.dom j G p.1 p.2})
    (hloc : ∀ p p' : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₂.dom j G p.1 p.2 →
      Dom₂.dom j G p'.1 p'.2 → (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → T p = T p') :
    (∀ Ψ Ψ' h h' : Fld d L N₁ m₁ K N, (∀ x ∈ Y, Ψ x = Ψ' x ∧ h x = h' x) →
      T (c (Ψ, h)) = T (c (Ψ', h'))) ∧
    (∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₂.dom j G p.1 p.2 → T (c p) = T p) ∧
    AnalyticOnNhd ℂ (fun p => T (c p)) {p | Dom₁.dom j G p.1 p.2} := by
  obtain ⟨c1, -⟩ := fieldDom_completion_spec Dom₂ j G Y c hc hDL
  obtain ⟨e, ha⟩ := fieldDom_completion_analytic_param_of_sub (S := ℂ) (Sp := Set.univ)
    Dom₁ Dom₂ j G Y c hc h12 hDL hDo (fun q => T q.1)
    (fun q hq => (hT q.1 hq.1).comp_of_eq analyticAt_fst rfl)
    (fun p p' hp hp' hY _ => hloc p p' hp hp' hY)
  refine ⟨fun Ψ Ψ' h h' hY => by rw [c1 Ψ Ψ' h h' hY], fun p hp => e p hp 0, ?_⟩
  intro p₀ hp₀
  exact (ha (p₀, 0) ⟨hp₀, Set.mem_univ _⟩).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl

end Completion

end Balaban.Localization
