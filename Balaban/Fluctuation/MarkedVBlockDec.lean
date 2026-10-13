/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedEvParam
public import Balaban.Fluctuation.SharpAssemblyScaled

/-!
# The block expansion along the masked decoupled tangent (`MarkedVBlockDec`)

The marked analogue of `SharpAssemblyScaled.vblock_expansion_hat_dir_scaled`.  For one old block
`z` the block functional `blockEnergyFun Gp Hm (compWeight L a₁) ν k z` is expanded along the masked
tangent `markedHatPsiF … Zm um tm` of the decoupled step: the landed
`i5_functional_hat_marked_exposed` is applied with `Φ = blockEnergyFun …`, the analyticity
(`blockEnergyFun_analytic`), the scaled bound (`blockEnergyFun_bound_scaled`) and the locality
(`blockEnergyFun_local_dir`) of the block functional, exactly as the landed theorem is obtained
from `i5_functional_hat_dir`.  The constants are those of the landed theorem.

* `markedTangDec`, `markedFunDec`, `evDec`: the masked tangent as a function of the data, the value
  of the block functional along it, and the localized term `evTerm … (FFmarked …)`.
* `vblock_expansion_hat_marked_scaled`: sum identity, locality, scaled bound on closed bidiscs,
  analyticity in the marks, Cauchy estimate for the `t`-derivative at `0`, and the sum identity for
  the `t`-derivatives.

`MARK-PARAM` and the marked family are NOT proved here; zero class only; nothing depends on a
choice of generating sets for the class terms.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.Polymer Finset Matrix

section Defs

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}

/-- The radius quantity `√N · ‖cc‖ · C_sup · cψ`: marks `(um, tm)` with
`(‖um‖ + ‖tm‖) · markedRad < δ₁` are admissible. -/
noncomputable abbrev markedRad (d L N k : ℕ) (a₁ κ cψ : ℝ) (cc : ℂ) : ℝ :=
  Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))

/-- **The masked decoupled tangent at the physical cut point**, as a function of the data
`(D, ψ̂)`: `lift (um · cc · K ψ̂ + tm · M_Z (cc · K ψ̂))`. -/
noncomputable abbrev markedTangDec (hG' : IsLevel Gp (k + 1)) (cc : ℂ) (a₁ ν : ℝ)
    (Zm : Finset (unitPts Gp)) (um tm : ℂ) (D : BgData Gp N) (ψh : unitPts Gp × Fin N → ℂ) :
    CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ :=
  liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
    (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
    (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
    (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
    tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
    (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
    (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
    (unitQ Gp) (unitP Gp) *ᵥ ψh)))

/-- **The value of a block functional along the masked tangent** at the data `(D, ψ̂)`. -/
noncomputable abbrev markedFunDec (hG' : IsLevel Gp (k + 1)) (cc : ℂ) (a₁ ν BG₂ κ : ℝ)
    (Zm : Finset (unitPts Gp)) (um tm : ℂ)
    (Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (D : BgData Gp N) (ψh : unitPts Gp × Fin N → ℂ) : ℂ :=
  Φ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D, bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
    (flFieldOne Gp Hm BG₂ κ a₁ ν D (markedTangDec hG' cc a₁ ν Zm um tm D ψh))
    (rawOf D, markedTangDec hG' cc a₁ ν Zm um tm D ψh)

/-- **The localized term of the block expansion along the masked tangent**:
`evTerm … (FFmarked …) Y u`. -/
noncomputable abbrev evDec (X₁f : Finset (CTorus d L N₁ m₁ (k + 1))) (m₀ j : ℕ)
    (𝒦X : Set (CTorus d L N₁ m₁ (k + 1))) (a₁ ν : ℝ) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (Zm : Finset (unitPts Gp)) (um tm : ℂ) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) : ℂ :=
  evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
    (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y u

end Defs

section Block

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The block expansion along the masked tangent** (the conclusion of `vblock_expansion_hat_marked_scaled`)
(`vblock_expansion_hat_dir_scaled` with the masked decoupled tangent `markedHatPsiF … Zm um tm`).
The hypotheses are those of the landed theorem, with the radius inequality
`(‖um‖ + ‖tm‖) · markedRad < δ₁` (a condition on the marks, in the conclusion) in place of its
`hδ₁`, and an arbitrary mask set `Zm`.  There are maps `F₁`, `Sol` (not depending on the marks)
such that for the localized terms `evDec … Y`:

1. sum identity: the block functional along the masked tangent is the sum over `Y ∈ polyDom` of the
   terms, at every mark of the radius set;
2. locality: `AgHatDir Y` at fixed marks;
3. bound `E*·e^{-2κ_dec d(Y)}` (`E* = energyBdScaled …`) on every closed bidisc in the radius set;
4. analyticity in the marks at fixed data, on the radius set;
5. Cauchy estimate `‖∂_t evDec|₀‖ ≤ E* e^{-2κ_dec d(Y)}/t₀`;
6. sum identity for the `t`-derivatives at `0`. -/
def MarkedBlockExpansionDec (N : ℕ) (Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm)
    (hG' : IsLevel Gp (k + 1)) (cc : ℂ) (a₁ ν BG BG₂ κ eps δ₁ κdec cψ : ℝ)
    (Zm : Finset (unitPts Gp)) (X₁f : Finset (CTorus d L N₁ m₁ (k + 1))) (m₀ j : ℕ)
    (𝒦X : Set (CTorus d L N₁ m₁ (k + 1))) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    Prop :=
    ∃ (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
      (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
      -- 1. sum identity
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        markedFunDec hG' cc a₁ ν BG₂ κ Zm um tm (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) D ψh =
        ∑ Y ∈ polyDom Gp X₁f m₀ j 𝒦X,
          evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
            um tm Y (rawOf D, ψh)) ∧
      -- 2. locality
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir hG' Y u u' →
          evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
            um tm Y u =
          evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
            um tm Y u') ∧
      -- 3. bound on closed bidiscs
      (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        ∀ um tm : ℂ, ‖um‖ ≤ a → ‖tm‖ ≤ b →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
            um tm Y u‖ ≤
          energyBdScaled d L N (compWeight L a₁) k
            (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
            Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
      -- 4. analyticity in the marks
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AnalyticOnNhd ℂ (fun w : ℂ × ℂ =>
          evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
            w.1 w.2 Y u)
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}) ∧
      -- 5. Cauchy estimate
      (∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b → 0 < t₀ → t₀ ≤ b →
        (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        ∀ um : ℂ, ‖um‖ ≤ a →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖deriv (fun t : ℂ =>
          evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
            um t Y u) 0‖ ≤
          energyBdScaled d L N (compWeight L a₁) k
            (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
            Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / t₀) ∧
      -- 6. sum identity for the derivatives
      (∀ um : ℂ, (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        deriv (fun tm : ℂ =>
          markedFunDec hG' cc a₁ ν BG₂ κ Zm um tm (blockEnergyFun Gp Hm (compWeight L a₁) ν k z)
            D ψh) 0 =
        ∑ Y ∈ polyDom Gp X₁f m₀ j 𝒦X, deriv (fun t : ℂ =>
          evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
            um t Y (rawOf D, ψh)) 0)

/-- **The block energy expands along the masked tangent over the domains `Y ⊃ X₁`**
(`vblock_expansion_hat_dir_scaled` with the masked decoupled tangent), the clauses being those of
`MarkedBlockExpansionDec`.  The hypotheses are those of the landed theorem, with the radius
inequality on the marks (in the conclusion) in place of its `hδ₁`, and an arbitrary mask set
`Zm`. -/
theorem vblock_expansion_hat_marked_scaled
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ) (Zm : Finset (unitPts Gp))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hZ : readSites Hm k z ⊆ ↑X₁f)
    (hmar : BlockMargin Gp X₁f (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1)))) :
    MarkedBlockExpansionDec N Hm hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z := by
  unfold MarkedBlockExpansionDec
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hρ : 0 ≤ rho4 d L N BG κ := by
    have hBG := hC.hS.fam.2.1
    have hB1 : 0 ≤ famConst d L BG κ := by
      have := famConst_ge_one (L := L) hBG κ hd0; linarith
    unfold rho4
    exact (c6'_pos hB1 (by have := gamma1_pos hd0; positivity)).le
  have ha : 0 ≤ compWeight L a₁ k :=
    (hC.HBp.weights k hk (by omega)).1.trans' (by norm_num)
  have hEb := energyBdScaled_nonneg (d := d) (L := L) (N := N) ha hV hC.δ₁_pos.le hρ
  obtain ⟨F₁, Sol, e1, e2, e3, e4, e5, e6, e7, e8⟩ := i5_functional_hat_marked_exposed hC hk hG hG'
    cc hcψ Zm hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb
    (Φ := blockEnergyFun Gp Hm (compWeight L a₁) ν k z)
    ((blockEnergyFun_analytic _ ν k z).mono (Set.subset_univ _))
    (fun t ht => by
      rw [hΔ]; simpa using blockEnergyFun_bound_scaled hC hG hG' hk le_rfl z ht)
    (Z := readSites Hm k z) (Zα := ↑(blockSites d L N₁ m₁ (k + 1) k z)) hZ hmar
    (fun t _ t' _ _ hα hδ _ hψ => blockEnergyFun_local_dir _ ν k z hα hδ hψ)
  have hexp : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y) =
        Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) := by
    intro Y; rw [hΔ]; congr 1; ring
  refine ⟨F₁, Sol, e1, e2, ?_, e6, ?_, e8⟩
  · intro a b ha hb hab um tm hu ht Y u hu'
    have := e4 a b ha hb hab um tm hu ht Y u hu'
    rwa [hexp] at this
  · intro a b t₀ ha hb ht₀ htb hab um hu Y u hu'
    have := e7 a b t₀ ha hb ht₀ htb hab um hu Y u hu'
    rwa [hexp] at this

end Block

end Balaban.Localization
