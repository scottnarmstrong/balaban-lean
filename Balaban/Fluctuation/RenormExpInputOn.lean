/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormInputZero

/-!
# The renormalization input with the expansions on a sub-domain

A localization principle (`HasLocPrinciple`) does not restrict to a smaller set of data: its
transfer clause assumes a bound on the whole domain.  A localized expansion (`IsLocExp`) does
(`IsLocExp.mono_dom`).  `RenormExpInputOn` therefore keeps the three localization principles on
the full domain `Ξ^c_{k+1}(1, ε)` (`XiCOneReal`) and states the four expansions on a sub-domain
`Dom`; with `Dom` the data of constant real field `h = h₀` it is the input for the physical new
terms.

* `IsLocExp.mono_dom`: an expansion on `Dom` is an expansion on every `Dom' ⊆ Dom`;
* `RenormExpInputOn`, `RenormExpInput.toOn`, `nonempty_renormExpInputOn_fibre` (hard rule 10);
* `thm31g_C1_on`, `thm31g_C2_on`, `thm31g_Eu_on`, `thm31h_on`: the four consumers of Theorem 3.1
  (g), (h) with the expansions on `Dom`;
* `renormExpInputOn_zero_of_fields`, `thm31g_Eu_zero_of_fields_on`, `thm31h_zero_of_fields_on`:
  the zero class (old terms zero).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Balaban.SmallField

section MonoDom

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {Dom Dom' : BgData G N → Prop} {r κ B : ℝ}
  {Ys : Finset (Finset (Torus d (N₀ * L ^ k)))}
  {dY : Finset (Torus d (N₀ * L ^ k)) → ℝ} {f : BgData G N → (Fin 3 → ℂ) → E}
  {term : Finset (Torus d (N₀ * L ^ k)) → RawData d L N₀ k N × (Fin 3 → ℂ) → E}

/-- The domain of an expansion is monotone in the set of data. -/
theorem expDom_mono_dom (h : ∀ D, Dom' D → Dom D) (r : ℝ) :
    expDom G Dom' r ⊆ expDom (N := N) G Dom r := by
  rintro q ⟨D, hD, h1, h2⟩
  exact ⟨D, h D hD, h1, h2⟩

/-- **An expansion restricts to a sub-domain of the data.** -/
theorem IsLocExp.mono_dom (h : IsLocExp G Dom r Ys dY κ B f term) (hD : ∀ D, Dom' D → Dom D) :
    IsLocExp G Dom' r Ys dY κ B f term where
  sum_eq D hD' ξ hξ := h.sum_eq D (hD D hD') ξ hξ
  analytic Y hY := (h.analytic Y hY).mono (expDom_mono_dom hD r)
  local_ Y hY q hq q' hq' := h.local_ Y hY q (expDom_mono_dom hD r hq) q'
    (expDom_mono_dom hD r hq')
  bound Y hY q hq := h.bound Y hY q (expDom_mono_dom hD r hq)

end MonoDom

section Input

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)

/-- **The open inputs of Theorem 3.1 (g), (h) with the expansions on a sub-domain `Dom`**: the
fields of `RenormExpInput`, with the three localization principles on the full domain
`XiCOneReal G a ν ε` and the four expansions (with the vanishing at `ξ = 0` of the old terms) on
the data `D` with `Dom D`, where `Dom ⊆ XiCOneReal G a ν ε` (`sub`). -/
structure RenormExpInputOn (ν ε r₀ cK B : ℝ)
    (F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))
    {ι : Type*} (blk : ι → Finset (Torus d (N₀ * L ^ k)))
    (Ys : ι → Finset (Finset (Torus d (N₀ * L ^ k))))
    (YsM : G.Ω 1 × Fin N → Finset (Finset (Torus d (N₀ * L ^ k))))
    (dY : Finset (Torus d (N₀ * L ^ k)) → ℝ) (κa κb Kloc BE0 Bold BM0 BoldM : ℝ)
    (E0θ oldE : ι → BgData G N → (Fin 3 → ℂ) → ℂ)
    (M0θ oldM : G.Ω 1 × Fin N → BgData G N → (Fin 3 → ℂ) → ℂ)
    (Dom : BgData G N → Prop) : Prop where
  /-- The sub-domain lies in the full domain. -/
  sub : ∀ D : BgData G N, Dom D → XiCOneReal G a ν ε D
  /-- As `RenormExpInput.locC1`, on the full domain. -/
  locC1 : ∀ z, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa Kloc
    (fun D _ => bgClass G ν (cK * ε) D) (fun D φ ξ => renC1On G a ν ε (blk z) D.Ψ D.h φ ξ)
    (fun D _ => bgFieldC G a ν (bgC0 d L N) D)
  /-- As `RenormExpInput.locC2`, on the full domain. -/
  locC2 : ∀ z, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa Kloc
    (fun _ ξ => pertClass G (cK * (cK2 d L N * (B * ‖ξ‖)))
      (bgK1 d L N * (xiC1 d * ε) + cK * cK2 d L N * B * r₀ + 2) (renMassU ν ξ))
    (fun _ v ξ => renC2On G a (blk z) ξ (renMassU ν ξ) v.2 v.1)
    (fun D ξ => ((F ((D.Ψ, D.h), ξ)).1, bgMultC G a ν (bgC0 d L N) D + (F ((D.Ψ, D.h), ξ)).2))
  /-- The expansion of `ℰ''₀(z)(θ)` on `Dom`. -/
  expE0 : ∀ z, ∃ term, IsLocExp (N := N) G Dom r₀ (Ys z) dY κa BE0 (E0θ z) term
  /-- The expansion of the old-term differences on `Dom`, terms vanishing at `ξ = 0`. -/
  expOld : ∀ z, ∃ term, IsLocExp (N := N) G Dom r₀ (Ys z) dY κa Bold (oldE z) term ∧
    ∀ Y ∈ Ys z, ∀ D : BgData G N, Dom D → term Y ((D.Ψ, D.h), 0) = 0
  /-- As `RenormExpInput.locDφ`, on the full domain. -/
  locDφ : ∀ p, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (YsM p) dY κb Kloc
    (fun _ ξ => {v | SupBounds G v (cK * (cK2 d L N * (B * ‖ξ‖)))}) (fun _ v _ => v p)
    (fun D ξ => (F ((D.Ψ, D.h), ξ)).1)
  /-- The expansion of `β_k^{-1/2} ℳ''₀(x)(θ)` on `Dom`. -/
  expM0 : ∀ p, ∃ term, IsLocExp (N := N) G Dom r₀ (YsM p) dY κb BM0 (M0θ p) term
  /-- The expansion of the `ℳ^{(j)}`-differences on `Dom`, terms vanishing at `ξ = 0`. -/
  expOldM : ∀ p, ∃ term, IsLocExp (N := N) G Dom r₀ (YsM p) dY κb BoldM (oldM p) term ∧
    ∀ Y ∈ YsM p, ∀ D : BgData G N, Dom D → term Y ((D.Ψ, D.h), 0) = 0

variable {G a} {ν ε r₀ cK B : ℝ}
  {F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
  {ι : Type*} {blk : ι → Finset (Torus d (N₀ * L ^ k))}
  {Ys : ι → Finset (Finset (Torus d (N₀ * L ^ k)))}
  {YsM : G.Ω 1 × Fin N → Finset (Finset (Torus d (N₀ * L ^ k)))}
  {dY : Finset (Torus d (N₀ * L ^ k)) → ℝ} {κa κb Kloc BE0 Bold BM0 BoldM : ℝ}
  {E0θ oldE : ι → BgData G N → (Fin 3 → ℂ) → ℂ}
  {M0θ oldM : G.Ω 1 × Fin N → BgData G N → (Fin 3 → ℂ) → ℂ}

/-- A `RenormExpInput` gives a `RenormExpInputOn` for every sub-domain of the full domain. -/
theorem RenormExpInput.toOn
    (I : RenormExpInput G a ν ε r₀ cK B F blk Ys YsM dY κa κb Kloc BE0 Bold BM0 BoldM E0θ oldE
      M0θ oldM)
    {Dom : BgData G N → Prop} (hDom : ∀ D, Dom D → XiCOneReal G a ν ε D) :
    RenormExpInputOn G a ν ε r₀ cK B F blk Ys YsM dY κa κb Kloc BE0 Bold BM0 BoldM E0θ oldE
      M0θ oldM Dom where
  sub := hDom
  locC1 := I.locC1
  locC2 := I.locC2
  expE0 z := (I.expE0 z).imp fun _ h => h.mono_dom hDom
  expOld z := (I.expOld z).imp fun _ h =>
    ⟨h.1.mono_dom hDom, fun Y hY D hD => h.2 Y hY D (hDom D hD)⟩
  locDφ := I.locDφ
  expM0 p := (I.expM0 p).imp fun _ h => h.mono_dom hDom
  expOldM p := (I.expOldM p).imp fun _ h =>
    ⟨h.1.mono_dom hDom, fun Y hY D hD => h.2 Y hY D (hDom D hD)⟩

/-- **`RenormExpInputOn` has an instance on the fibre**: for admissible parameters and every real
constant field `h₀`, there is an input on the fibre domain `Ξ^c_{k+1}(1, ε) ∩ {h = h₀}`.

This does NOT show that the fibre domain contains a datum (audit `notes/phase1/AUDIT-OBS.md`,
A3): the record is obtained by restriction and exists also over an empty domain. The datum in the
fibre is supplied separately at the tower. -/
theorem nonempty_renormExpInputOn_fibre {ν : ℝ} (H : BgHyp d L k ϱ a ν) {ι : Type*}
    (blk : ι → Finset (Torus d (N₀ * L ^ k))) (κa κb : ℝ) (h₀ : Fin N → ℝ) :
    ∃ ε r₀ : ℝ, 0 < ε ∧ 0 < r₀ ∧ ∃ F, IsRenSol (N := N) G a ν ε ε r₀ (8 * ε) F ∧
      RenormExpInputOn G a ν ε r₀ 2 (8 * ε) F blk (fun _ => {Finset.univ})
        (fun _ => {Finset.univ}) (fun _ => 0) κa κb 1 0 0 0 0 (fun _ _ _ => 0) (fun _ _ _ => 0)
        (fun _ _ _ => 0) (fun _ _ _ => 0)
        (fun D => XiCOneReal G a ν ε D ∧ ∀ x i, D.h x i = (h₀ i : ℂ)) := by
  obtain ⟨ε, r₀, hε, hr, F, hF, I⟩ := nonempty_renormExpInput (N := N) (G := G) a H blk κa κb
  exact ⟨ε, r₀, hε, hr, F, hF, I.toOn fun _ h => h.1⟩

end Input

section Consumers

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν ε r₀ cK B : ℝ}
  {F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
  {ι : Type*} {blk : ι → Finset (Torus d (N₀ * L ^ k))}
  {Ys : ι → Finset (Finset (Torus d (N₀ * L ^ k)))}
  {YsM : G.Ω 1 × Fin N → Finset (Finset (Torus d (N₀ * L ^ k)))}
  {dY : Finset (Torus d (N₀ * L ^ k)) → ℝ} {κa κb Kloc BE0 Bold BM0 BoldM : ℝ}
  {E0θ oldE : ι → BgData G N → (Fin 3 → ℂ) → ℂ}
  {M0θ oldM : G.Ω 1 × Fin N → BgData G N → (Fin 3 → ℂ) → ℂ}
  {Dom : BgData G N → Prop}

/-- **Theorem 3.1 (g), `C₁(z)`, on the sub-domain**: the landed bound, as an expansion on `Dom`.
The localization principle and the pointwise bound use the full domain; the restriction to `Dom`
is the last step. -/
theorem thm31g_C1_on (H : BgHyp d L k ϱ a ν) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    (hr₀ : r₀ ≤ 1 / 16)
    (I : RenormExpInputOn G a ν ε r₀ cK B F blk Ys YsM dY κa κb Kloc BE0 Bold BM0 BoldM E0θ oldE
      M0θ oldM Dom)
    (hK : 0 ≤ Kloc) (hcK : 1 ≤ cK) {εR : ℝ} (hεR : εR ≤ r₀) (z : ι) :
    ∃ term, IsLocExp (N := N) G Dom εR (Ys z) dY κa
      (Kloc * ((d + 6) * (cK * ε) ^ 2 * blockWeight G (blk z)) * εR ^ 1)
      (fun D ξ => renC1On G a ν ε (blk z) D.Ψ D.h (bgFieldC G a ν (bgC0 d L N) D) ξ) term := by
  have hW : 0 ≤ blockWeight G (blk z) := Finset.sum_nonneg fun x _ => by
    have := spacing_pos G (x := x); positivity
  refine (fun ⟨term, h⟩ => ⟨term, h.mono_dom I.sub⟩) ((I.locC1 z).isLocExp (c := (d + 6) * (cK * ε) ^ 2 * blockWeight G (blk z)) (p := 1) hK
    (by positivity) (fun ξ hξ D hD φ hφ => ?_) hεR)
  have hΨ := (hD.factors H hε hsm hc1).2.2.2
  have hc0 : 0 ≤ cK * ε := by positivity
  have := norm_renC1On_le_of_mem H.weights H.mass hΨ hc0 hφ hε.le
    (le_mul_of_one_le_left hε.le hcK) (hξ.le.trans hr₀) (blk z)
  calc _ ≤ (d + 6) * (cK * ε) ^ 2 * ‖ξ‖ * blockWeight G (blk z) := this
    _ = (d + 6) * (cK * ε) ^ 2 * blockWeight G (blk z) * ‖ξ‖ ^ 1 := by ring

/-- **Theorem 3.1 (g), `C₂(z)`, on the sub-domain**. -/
theorem thm31g_C2_on (H : BgHyp d L k ϱ a ν) (hε : 0 < ε) (hr₀ : r₀ ≤ 1 / 16)
    (I : RenormExpInputOn G a ν ε r₀ cK B F blk Ys YsM dY κa κb Kloc BE0 Bold BM0 BoldM E0θ oldE
      M0θ oldM Dom)
    (hK : 0 ≤ Kloc) (hB0 : 0 ≤ B) (hcK : 1 ≤ cK) {εR : ℝ} (hεR0 : 0 ≤ εR) (hεR : εR ≤ r₀)
    (z : ι) :
    ∃ term, IsLocExp (N := N) G Dom εR (Ys z) dY κa
      (Kloc * (17 / 32 * (N * ((3 + (bgK1 d L N * (xiC1 d * ε) + cK * cK2 d L N * B * r₀ + 2)) *
        (cK * cK2 d L N * B) ^ 2)) * blockWeight G (blk z)) * εR ^ 2)
      (fun D ξ => renC2On G a (blk z) ξ (renMassU ν ξ)
        (bgMultC G a ν (bgC0 d L N) D + (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term := by
  have hW : 0 ≤ blockWeight G (blk z) := Finset.sum_nonneg fun x _ => by
    have := spacing_pos G (x := x); positivity
  have hK2 := cK2_pos d L N
  have hK1 := bgK1_pos d L N
  have hX := one_le_xiC1 d
  have hr0 : 0 ≤ r₀ := hεR0.trans hεR
  have hcK0 : 0 ≤ cK := by linarith
  have hA0 : 0 ≤ bgK1 d L N * (xiC1 d * ε) + cK * cK2 d L N * B * r₀ + 2 := by positivity
  refine (fun ⟨term, h⟩ => ⟨term, h.mono_dom I.sub⟩) ((I.locC2 z).isLocExp (c := 17 / 32 * (N * ((3 + (bgK1 d L N * (xiC1 d * ε) + cK * cK2 d L N * B * r₀ + 2)) *
        (cK * cK2 d L N * B) ^ 2)) * blockWeight G (blk z)) (p := 2) hK (by positivity)
    (fun ξ hξ D _ v hv => ?_) hεR)
  have hV : 0 ≤ cK * (cK2 d L N * (B * ‖ξ‖)) := by positivity
  have := norm_renC2On_le_of_mem (a := a) H.weights hV hA0 hv (hξ.le.trans hr₀) (blk z)
  calc _ ≤ _ := this
    _ = 17 / 32 * (N * ((3 + (bgK1 d L N * (xiC1 d * ε) + cK * cK2 d L N * B * r₀ + 2)) *
          (cK * cK2 d L N * B) ^ 2)) * blockWeight G (blk z) * ‖ξ‖ ^ 2 := by ring

/-- **Theorem 3.1 (g), `ℰ_u(z)`, on the sub-domain**: the new contribution and the Cauchy-bounded
old-term differences, both on `Dom`. -/
theorem thm31g_Eu_on
    (I : RenormExpInputOn G a ν ε r₀ cK B F blk Ys YsM dY κa κb Kloc BE0 Bold BM0 BoldM E0θ oldE
      M0θ oldM Dom)
    (hr₀ : 0 < r₀) {εR : ℝ} (hεR : εR ≤ r₀) (z : ι) :
    ∃ term, IsLocExp (N := N) G Dom εR (Ys z) dY κa (BE0 + Bold * (εR / r₀))
      (fun D ξ => E0θ z D ξ + oldE z D ξ) term := by
  obtain ⟨t1, h1⟩ := I.expE0 z
  obtain ⟨t2, h2, h20⟩ := I.expOld z
  exact ⟨_, (h1.mono_radius hεR).add (h2.cauchy hr₀ hεR h20)⟩

/-- **Theorem 3.1 (h), on the sub-domain**. -/
theorem thm31h_on
    (I : RenormExpInputOn G a ν ε r₀ cK B F blk Ys YsM dY κa κb Kloc BE0 Bold BM0 BoldM E0θ oldE
      M0θ oldM Dom)
    (hK : 0 ≤ Kloc) (hB0 : 0 ≤ B) (hcK : 1 ≤ cK) (hr₀ : 0 < r₀) {εR : ℝ} (hεR : εR ≤ r₀)
    (p : G.Ω 1 × Fin N) :
    ∃ term, IsLocExp (N := N) G Dom εR (YsM p) dY κb
      (BM0 + Kloc * (cK * cK2 d L N * B) * εR ^ 1 + BoldM * (εR / r₀))
      (fun D ξ => M0θ p D ξ + (F ((D.Ψ, D.h), ξ)).1 p + oldM p D ξ) term := by
  obtain ⟨t1, h1⟩ := I.expM0 p
  obtain ⟨t3, h3, h30⟩ := I.expOldM p
  have hK2 := cK2_pos d L N
  have hcK0 : 0 ≤ cK := by linarith
  obtain ⟨t2, h2⟩ := (I.locDφ p).isLocExp (c := cK * cK2 d L N * B) (p := 1) hK (by positivity)
    (fun ξ _ D _ v hv => by
      have hs := hv.val (p.1 : Torus d (N₀ * L ^ k)) p.2
      rw [svec_of_mem] at hs
      calc ‖v p‖ ≤ cK * (cK2 d L N * (B * ‖ξ‖)) := hs
        _ = cK * cK2 d L N * B * ‖ξ‖ ^ 1 := by ring) hεR
  exact ⟨_, ((h1.mono_radius hεR).add (h2.mono_dom I.sub)).add (h3.cauchy hr₀ hεR h30)⟩

/-- **Reduction at the zero class on the sub-domain** (conditional): the old-term fields hold by
`isLocExp_zero_cover`. -/
theorem renormExpInputOn_zero_of_fields
    (sub : ∀ D : BgData G N, Dom D → XiCOneReal G a ν ε D)
    (locC1 : ∀ z, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa Kloc
      (fun D _ => bgClass G ν (cK * ε) D) (fun D φ ξ => renC1On G a ν ε (blk z) D.Ψ D.h φ ξ)
      (fun D _ => bgFieldC G a ν (bgC0 d L N) D))
    (locC2 : ∀ z, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa Kloc
      (fun _ ξ => pertClass G (cK * (cK2 d L N * (B * ‖ξ‖)))
        (bgK1 d L N * (xiC1 d * ε) + cK * cK2 d L N * B * r₀ + 2) (renMassU ν ξ))
      (fun _ v ξ => renC2On G a (blk z) ξ (renMassU ν ξ) v.2 v.1)
      (fun D ξ => ((F ((D.Ψ, D.h), ξ)).1, bgMultC G a ν (bgC0 d L N) D + (F ((D.Ψ, D.h), ξ)).2)))
    (expE0 : ∀ z, ∃ term, IsLocExp (N := N) G Dom r₀ (Ys z) dY κa BE0 (E0θ z) term)
    (locDφ : ∀ p, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (YsM p) dY κb Kloc
      (fun _ ξ => {v | SupBounds G v (cK * (cK2 d L N * (B * ‖ξ‖)))}) (fun _ v _ => v p)
      (fun D ξ => (F ((D.Ψ, D.h), ξ)).1))
    (expM0 : ∀ p, ∃ term, IsLocExp (N := N) G Dom r₀ (YsM p) dY κb BM0 (M0θ p) term) :
    RenormExpInputOn G a ν ε r₀ cK B F blk Ys YsM dY κa κb Kloc BE0 0 BM0 0 E0θ
      (fun _ _ _ => 0) M0θ (fun _ _ _ => 0) Dom :=
  ⟨sub, locC1, locC2, expE0, fun _ => ⟨_, isLocExp_zero_cover _ _, fun _ _ _ _ => rfl⟩, locDφ,
    expM0, fun _ => ⟨_, isLocExp_zero_cover _ _, fun _ _ _ _ => rfl⟩⟩

/-- **Theorem 3.1 (g), `ℰ_u(z)`, zero class, on the sub-domain**: bound `B_{E0}`. -/
theorem thm31g_Eu_zero_of_fields_on
    (I : RenormExpInputOn G a ν ε r₀ cK B F blk Ys YsM dY κa κb Kloc BE0 0 BM0 0 E0θ
      (fun _ _ _ => 0) M0θ (fun _ _ _ => 0) Dom)
    (hr₀ : 0 < r₀) {εR : ℝ} (hεR : εR ≤ r₀) (z : ι) :
    ∃ term, IsLocExp (N := N) G Dom εR (Ys z) dY κa BE0 (fun D ξ => E0θ z D ξ) term := by
  obtain ⟨term, h⟩ := thm31g_Eu_on I hr₀ hεR z
  refine ⟨term, ?_⟩
  simpa using h

/-- **Theorem 3.1 (h), zero class, on the sub-domain**: bound `B_{M0} + K_loc c_K K₂ B ε_R`. -/
theorem thm31h_zero_of_fields_on
    (I : RenormExpInputOn G a ν ε r₀ cK B F blk Ys YsM dY κa κb Kloc BE0 0 BM0 0 E0θ
      (fun _ _ _ => 0) M0θ (fun _ _ _ => 0) Dom)
    (hK : 0 ≤ Kloc) (hB0 : 0 ≤ B) (hcK : 1 ≤ cK) (hr₀ : 0 < r₀)
    {εR : ℝ} (hεR : εR ≤ r₀) (p : G.Ω 1 × Fin N) :
    ∃ term, IsLocExp (N := N) G Dom εR (YsM p) dY κb
      (BM0 + Kloc * (cK * cK2 d L N * B) * εR ^ 1)
      (fun D ξ => M0θ p D ξ + (F ((D.Ψ, D.h), ξ)).1 p) term := by
  obtain ⟨term, h⟩ := thm31h_on I hK hB0 hcK hr₀ hεR p
  refine ⟨term, ?_⟩
  simpa using h

end Consumers

end Balaban.Fluctuation
