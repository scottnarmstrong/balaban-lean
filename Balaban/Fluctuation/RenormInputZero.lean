/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormExpG
import Mathlib.Tactic.Positivity

/-!
# The renormalization input at the zero class (LOCREN leaf 13b)

`RenormExpInput` has seven fields (`locC1`, `locC2`, `expE0`, `expOld`, `locDφ`, `expM0`,
`expOldM`).  For the zero class, in which the old energy terms `oldE` and the old observable terms
`oldM` vanish identically (and `Bold = BoldM = 0`), the two old-term fields hold on every cover
`Ys`, `YsM` and for every size function `dY`: the zero family of terms is an expansion
(`isLocExp_zero_cover`; the landed `isLocExp_zero` is the same statement for the cover `{𝕋}` and
`dY = 0` only).  Five fields remain: `locC1`, `locC2`, `locDφ`, `expE0`, `expM0`.

**What is proved here is conditional.**  `renormExpInput_zero_of_fields` builds the record from five
hypotheses of exactly the types of those fields, and `thm31g_C1_zero_of_fields` and its three
companions state the four landed consumer bounds with the old-term contributions removed.  Nothing
in this file proves a localization principle; the five fields remain open, and the statements are
for the zero class and do not depend on the choice of generating sets for the class terms.

The consumers use of the cover and of the size function nothing beyond `0 ≤ Kloc` (see
`HasLocPrinciple.isLocExp`): the cover is any finite set of finite sets and `dY` is any real
function; no nonnegativity of `dY`, no membership of a root and no covering property is used.
`HasLocPrinciple.of_single` shows that the record does not force the single-set cover: a
principle for the cover `{𝕋}` extends to any cover containing `𝕋` whose size function vanishes on
`𝕋`, with the new terms equal to `0`; `renormExpInput_zero_pair_cover` is the resulting
inhabitation on the cover `{𝕋, Y₀}`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Balaban.SmallField Matrix

section Cover

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The zero family of terms is an expansion of the zero function on every cover, for every size
function and every rate, with bound `0`. -/
theorem isLocExp_zero_cover {Dom : BgData G N → Prop} {r κ : ℝ}
    (Ys : Finset (Finset (Torus d (N₀ * L ^ k)))) (dY : Finset (Torus d (N₀ * L ^ k)) → ℝ) :
    IsLocExp G Dom r Ys dY κ 0 (fun _ _ => (0 : E)) (fun _ _ => 0) where
  sum_eq D _ ξ _ := by simp
  analytic Y _ := analyticOnNhd_const
  local_ Y _ q _ q' _ _ _ := rfl
  bound Y _ q _ := by simp

variable {U : Type*} {Dom : BgData G N → Prop} {r κ Kloc : ℝ}
  {Kcl : BgData G N → (Fin 3 → ℂ) → Set U} {f : BgData G N → U → (Fin 3 → ℂ) → E}
  {u : BgData G N → (Fin 3 → ℂ) → U}

/-- A localization principle for the cover `{𝕋}` (size `0`) gives one for any cover containing
`𝕋` whose size function vanishes on `𝕋`: the terms on the other sets are `0`. -/
theorem HasLocPrinciple.of_single
    (h : HasLocPrinciple G Dom r {Finset.univ} (fun _ => 0) κ Kloc Kcl f u)
    (Ys : Finset (Finset (Torus d (N₀ * L ^ k)))) (hu : Finset.univ ∈ Ys)
    (dY : Finset (Torus d (N₀ * L ^ k)) → ℝ) (hd : dY Finset.univ = 0) :
    HasLocPrinciple G Dom r Ys dY κ Kloc Kcl f u := by
  obtain ⟨term, hsum, han, hloc, hbd⟩ := h
  refine ⟨fun Y q => if Y = Finset.univ then term Finset.univ q else 0, ?_, ?_, ?_, ?_⟩
  · intro D hD ξ hξ
    rw [Finset.sum_eq_single Finset.univ (fun Y _ hY => by simp [hY]) (fun h => absurd hu h)]
    simpa using hsum D hD ξ hξ
  · intro Y hY
    by_cases e : Y = Finset.univ
    · subst e; simpa using han _ (Finset.mem_singleton_self _)
    · simp only [e, ite_false]; exact analyticOnNhd_const
  · intro Y hY q hq q' hq' h2 hag
    by_cases e : Y = Finset.univ
    · subst e; simpa using hloc _ (Finset.mem_singleton_self _) q hq q' hq' h2 hag
    · simp [e]
  · intro ξ hξ M hM Y hY D hD
    have h0 := hbd ξ hξ M hM Finset.univ (Finset.mem_singleton_self _) D hD
    by_cases e : Y = Finset.univ
    · subst e; simpa [hd] using h0
    · simp only [e, ite_false, norm_zero]
      have : 0 ≤ Kloc * M := by simpa using (norm_nonneg _).trans h0
      exact mul_nonneg this (Real.exp_pos _).le

end Cover

section Zero

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {a : ℕ → ℝ} {ν ε r₀ cK B : ℝ}
  {F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
  {ι : Type*} {blk : ι → Finset (Torus d (N₀ * L ^ k))}
  {Ys : ι → Finset (Finset (Torus d (N₀ * L ^ k)))}
  {YsM : G.Ω 1 × Fin N → Finset (Finset (Torus d (N₀ * L ^ k)))}
  {dY : Finset (Torus d (N₀ * L ^ k)) → ℝ} {κa κb Kloc BE0 BM0 : ℝ}
  {E0θ : ι → BgData G N → (Fin 3 → ℂ) → ℂ}
  {M0θ : G.Ω 1 × Fin N → BgData G N → (Fin 3 → ℂ) → ℂ}

/-- **Reduction at the zero class** (conditional): the old-term fields hold by
`isLocExp_zero_cover` for any covers and any size function; the record is built from the five
remaining fields.  Conditional on the open localization principles `locC1`, `locC2`, `locDφ` and
the open expansions `expE0`, `expM0`. -/
theorem renormExpInput_zero_of_fields
    (locC1 : ∀ z, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa Kloc
      (fun D _ => bgClass G ν (cK * ε) D) (fun D φ ξ => renC1On G a ν ε (blk z) D.Ψ D.h φ ξ)
      (fun D _ => bgFieldC G a ν (bgC0 d L N) D))
    (locC2 : ∀ z, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa Kloc
      (fun _ ξ => pertClass G (cK * (cK2 d L N * (B * ‖ξ‖)))
        (bgK1 d L N * (xiC1 d * ε) + cK * cK2 d L N * B * r₀ + 2) (renMassU ν ξ))
      (fun _ v ξ => renC2On G a (blk z) ξ (renMassU ν ξ) v.2 v.1)
      (fun D ξ => ((F ((D.Ψ, D.h), ξ)).1, bgMultC G a ν (bgC0 d L N) D + (F ((D.Ψ, D.h), ξ)).2)))
    (expE0 : ∀ z, ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa BE0 (E0θ z) term)
    (locDφ : ∀ p, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (YsM p) dY κb Kloc
      (fun _ ξ => {v | SupBounds G v (cK * (cK2 d L N * (B * ‖ξ‖)))}) (fun _ v _ => v p)
      (fun D ξ => (F ((D.Ψ, D.h), ξ)).1))
    (expM0 : ∀ p, ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) r₀ (YsM p) dY κb BM0 (M0θ p)
      term) :
    RenormExpInput G a ν ε r₀ cK B F blk Ys YsM dY κa κb Kloc BE0 0 BM0 0 E0θ
      (fun _ _ _ => 0) M0θ (fun _ _ _ => 0) :=
  ⟨locC1, locC2, expE0, fun _ => ⟨_, isLocExp_zero_cover _ _, fun _ _ _ _ => rfl⟩, locDφ, expM0,
    fun _ => ⟨_, isLocExp_zero_cover _ _, fun _ _ _ _ => rfl⟩⟩

variable (I : RenormExpInput G a ν ε r₀ cK B F blk Ys YsM dY κa κb Kloc BE0 0 BM0 0 E0θ
      (fun _ _ _ => 0) M0θ (fun _ _ _ => 0))

include I

/-- **Theorem 3.1 (g), `C₁(z)`, zero class**: the landed bound, which has no old-term part. -/
theorem thm31g_C1_zero_of_fields (H : BgHyp d L k ϱ a ν) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    (hr₀ : r₀ ≤ 1 / 16) (hK : 0 ≤ Kloc) (hcK : 1 ≤ cK) {εR : ℝ} (hεR : εR ≤ r₀) (z : ι) :
    ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) εR (Ys z) dY κa
      (Kloc * ((d + 6) * (cK * ε) ^ 2 * blockWeight G (blk z)) * εR ^ 1)
      (fun D ξ => renC1On G a ν ε (blk z) D.Ψ D.h (bgFieldC G a ν (bgC0 d L N) D) ξ) term :=
  thm31g_C1_of_input H hε hsm hc1 hr₀ I hK hcK hεR z

/-- **Theorem 3.1 (g), `C₂(z)`, zero class**. -/
theorem thm31g_C2_zero_of_fields (H : BgHyp d L k ϱ a ν) (hε : 0 < ε) (hr₀ : r₀ ≤ 1 / 16)
    (hK : 0 ≤ Kloc) (hB0 : 0 ≤ B) (hcK : 1 ≤ cK) {εR : ℝ} (hεR0 : 0 ≤ εR) (hεR : εR ≤ r₀)
    (z : ι) :
    ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) εR (Ys z) dY κa
      (Kloc * (17 / 32 * (N * ((3 + (bgK1 d L N * (xiC1 d * ε) + cK * cK2 d L N * B * r₀ + 2)) *
        (cK * cK2 d L N * B) ^ 2)) * blockWeight G (blk z)) * εR ^ 2)
      (fun D ξ => renC2On G a (blk z) ξ (renMassU ν ξ)
        (bgMultC G a ν (bgC0 d L N) D + (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term :=
  thm31g_C2_of_input H hε hr₀ I hK hB0 hcK hεR0 hεR z

/-- **Theorem 3.1 (g), `ℰ_u(z)`, zero class**: bound `B_{E0}`, no old term. -/
theorem thm31g_Eu_zero_of_fields (hr₀ : 0 < r₀) {εR : ℝ} (hεR : εR ≤ r₀) (z : ι) :
    ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) εR (Ys z) dY κa BE0
      (fun D ξ => E0θ z D ξ) term := by
  obtain ⟨term, h⟩ := thm31g_Eu_of_input I hr₀ hεR z
  refine ⟨term, ?_⟩
  simpa using h

/-- **Theorem 3.1 (h), zero class**: bound `B_{M0} + K_loc c_K K₂ B ε_R`, no old term. -/
theorem thm31h_zero_of_fields (hK : 0 ≤ Kloc) (hB0 : 0 ≤ B) (hcK : 1 ≤ cK) (hr₀ : 0 < r₀)
    {εR : ℝ} (hεR : εR ≤ r₀) (p : G.Ω 1 × Fin N) :
    ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) εR (YsM p) dY κb
      (BM0 + Kloc * (cK * cK2 d L N * B) * εR ^ 1)
      (fun D ξ => M0θ p D ξ + (F ((D.Ψ, D.h), ξ)).1 p) term := by
  obtain ⟨term, h⟩ := thm31h_of_input I hK hB0 hcK hr₀ hεR p
  refine ⟨term, ?_⟩
  simpa using h

end Zero

section Witness

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  (a : ℕ → ℝ)

/-- **Inhabitation on a cover that is not `{𝕋}`**: the landed witness setting with the cover
`{𝕋, Y₀}` (`Y₀ ≠ 𝕋` any set) for every block and every site, the size function `0` on `𝕋` and
`c ≥ 0` elsewhere, the terms on `Y₀` equal to `0`.  The five hypotheses of
`renormExpInput_zero_of_fields` hold here, so the zero-class record does not force the one-set
cover. -/
theorem renormExpInput_zero_pair_cover {ν ε r B r₀ : ℝ} (H : BgHyp d L k ϱ a ν) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    {F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    (hF : IsRenSol G a ν ε ε r B F) (hB0 : 0 ≤ B) (hr₀ : r₀ ≤ r) (hr16 : r₀ ≤ 1 / 16)
    {ι : Type*} (blk : ι → Finset (Torus d (N₀ * L ^ k))) (κa κb : ℝ)
    (Y₀ : Finset (Torus d (N₀ * L ^ k))) (hY₀ : Y₀ ≠ Finset.univ) (c : ℝ) (hc : 0 ≤ c) :
    ∃ dY : Finset (Torus d (N₀ * L ^ k)) → ℝ,
      dY Finset.univ = 0 ∧ dY Y₀ = c ∧ (∀ Y, 0 ≤ dY Y) ∧
      RenormExpInput G a ν ε r₀ 2 B F blk (fun _ => {Finset.univ, Y₀})
        (fun _ => {Finset.univ, Y₀}) dY κa κb 1 0 0 0 0 (fun _ _ _ => 0) (fun _ _ _ => 0)
        (fun _ _ _ => 0) (fun _ _ _ => 0) := by
  classical
  have W := renormExpInput_witness (N := N) a H hε hsm hc1 hF hB0 hr₀ hr16 blk κa κb
  let dY : Finset (Torus d (N₀ * L ^ k)) → ℝ := fun Y => if Y = Finset.univ then 0 else c
  have hu : Finset.univ ∈ ({Finset.univ, Y₀} : Finset (Finset (Torus d (N₀ * L ^ k)))) := by simp
  have hd : dY Finset.univ = 0 := by simp [dY]
  refine ⟨dY, hd, by simp [dY, hY₀], fun Y => ?_,
    renormExpInput_zero_of_fields (fun z => (W.locC1 z).of_single _ hu dY hd)
      (fun z => (W.locC2 z).of_single _ hu dY hd) (fun z => ⟨_, isLocExp_zero_cover _ _⟩)
      (fun p => (W.locDφ p).of_single _ hu dY hd) (fun p => ⟨_, isLocExp_zero_cover _ _⟩)⟩
  by_cases e : Y = Finset.univ <;> simp [dY, e, hc]

end Witness

end Balaban.Fluctuation
