/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapScales
public import Balaban.Fluctuation.InteractionSymmLat
public import Balaban.Localization.DecEquivTranslatePolymer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Translation covariance of the step terms by cell-aligned translations

The paving symmetries of the landed covariance (`pavingSymGroup`, the lattice symmetries
`LatSymm.ofTranslateLevel`, `CoverSymm.ofTranslate`, `BlockSymm.ofTranslate`,
`PolymerSymm.ofTranslate`) contain every translation `x ↦ x + t` of the step torus by a vector `t`
with `L ^ (n + m₀ + m₁) ∣ t_μ` for all `μ` (`n` the level of the top generating set, so
`L ^ (n + m₀ + m₁)` is the cell side `a_n`), provided `L ^ m₀ ∣ N₁`.

* `evTerm_translate_step`: the expansion term of the step function of a background functional is
  invariant under such a translation, `𝓔(X + t, Y + t)(τ_t u) = 𝓔(X, Y)(u)`; it is the landed
  `evTerm_sym` at `σ = x ↦ x + t`.
* `evTerm_translate_aligned`: the same for an arbitrary function of the cut parameters that is
  transported by the relabelling of the parameters.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background

section Cov

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ} {m₀ n : ℕ}

/-- **Translation covariance of the step terms** (item 24, part 1).  Let `Gp` be a level set
of level `n`, `Sm`, `S` the translation lattice symmetries of `Hm`, `Gp` (`LatSymm.ofTranslateLevel`), `L ^ m₀ ∣ N₁`, and `t` a translation of the torus with
`L ^ (n + m₀ + m₁) ∣ t_μ` (a multiple of the cell side `a_n`).  Then
`𝓔(X + t, Y + t)(τ_t u) = 𝓔(X, Y)(u)` for the expansion terms of the step function of a
background functional which is invariant under the translation (`hΦ`); this is `evTerm_sym` at
`σ = x ↦ x + t`, whose lattice, cover, block and polymer symmetries are the translation ones. -/
theorem evTerm_translate_step
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hGp : IsLevel Gp n) (hN : L ^ m₀ ∣ N₁)
    (t : CTorus d L N₁ m₁ K) (ht : ∀ μ, L ^ (n + m₀ + m₁) ∣ (t μ).val)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol Sol' : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (S : LatSymm Gp Gp (Equiv.addRight t)) (Sm : LatSymm Hm Hm (Equiv.addRight t))
    {X₁f X₁f' : Finset (CTorus d L N₁ m₁ K)}
    (hX : (↑X₁f' : Set (CTorus d L N₁ m₁ K)) =
      (Equiv.addRight t) '' (↑X₁f : Set (CTorus d L N₁ m₁ K)))
    {Φb : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) u,
      Φb (S.fld bg.1, S.mul bg.2) (symU (Equiv.addRight t) u) = Φb bg u)
    (hana : AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
          (CTorus d L N₁ m₁ K → Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
        fnOfDec Gp Hm X₁f F₁ Sol (fun bg _ u => Φb bg u) p.1 p.2)
        ((XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁) ×ˢ
          polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) (fun _ => Real.exp κ)))
    (hana' : AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
          (CTorus d L N₁ m₁ K → Fin N → ℂ)) × (ParIdx Gp (↑X₁f' : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
        fnOfDec Gp Hm X₁f' F₁ Sol' (fun bg _ u => Φb bg u) p.1 p.2)
        ((XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁) ×ˢ
          polydisc (0 : ParIdx Gp (↑X₁f' : Set (CTorus d L N₁ m₁ K)) → ℂ) (fun _ => Real.exp κ)))
    (X₁ Y : Set (CTorus d L N₁ m₁ K))
    {u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁) :
    evTerm (fun i : ParIdx Gp (↑X₁f' : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
        ((Equiv.addRight t) '' X₁)
        (fnOfDec Gp Hm X₁f' F₁ Sol' (fun bg _ u => Φb bg u)) ((Equiv.addRight t) '' Y)
        (symU (Equiv.addRight t) u) =
      evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀ X₁
        (fnOfDec Gp Hm X₁f F₁ Sol (fun bg _ u => Φb bg u)) Y u := by
  have ht1 : ∀ μ, L ^ (n + m₁) ∣ (t μ).val := fun μ =>
    (pow_dvd_pow L (by omega)).trans (ht μ)
  exact evTerm_sym hC hF₁ S Sm
    (DecEquiv.CoverSymm.ofTranslate hGp t ht1)
    (DecEquiv.BlockSymm.ofTranslate hGp t (fun μ => (pow_dvd_pow L (by omega)).trans (ht μ)))
    (DecEquiv.PolymerSymm.ofTranslate hGp hN t ht) hX hΦ hana hana' X₁ Y hu

/-- **Translation covariance of the expansion terms of an arbitrary function of the cut
parameters**: if `F' u'` is `F u` composed with the relabelling `parEquiv` of the parameters at the
points of the unit polydisc, then `𝓔(X + t, Y + t)(F') = 𝓔(X, Y)(F)`, for `t` a multiple of the
cell side `a_n`. -/
theorem evTerm_translate_aligned {R : ℝ} (hR : 1 < R)
    (hGp : IsLevel Gp n) (hN : L ^ m₀ ∣ N₁)
    (t : CTorus d L N₁ m₁ K) (ht : ∀ μ, L ^ (n + m₀ + m₁) ∣ (t μ).val)
    (S : LatSymm Gp Gp (Equiv.addRight t))
    {X₁' : Set (CTorus d L N₁ m₁ K)} (X₁ Y : Set (CTorus d L N₁ m₁ K))
    (hX : X₁' = (Equiv.addRight t) '' X₁)
    {U U' : Type*} {F : U → (ParIdx Gp X₁ → ℂ) → ℂ} {F' : U' → (ParIdx Gp X₁' → ℂ) → ℂ}
    {u : U} {u' : U'}
    (hF : AnalyticOnNhd ℂ (F u) (polydisc (0 : ParIdx Gp X₁ → ℂ) (fun _ => R)))
    (hF' : AnalyticOnNhd ℂ (F' u') (polydisc (0 : ParIdx Gp X₁' → ℂ) (fun _ => R)))
    (hff : ∀ s ∈ unitCube (ParIdx Gp X₁'), F' u' s = F u (s ∘ parEquiv
      (DecEquiv.CoverSymm.ofTranslate hGp t (fun μ => (pow_dvd_pow L (by omega)).trans (ht μ)))
      (DecEquiv.PolymerSymm.ofTranslate hGp hN t ht) hX)) :
    evTerm (fun i : ParIdx Gp X₁' => i.1.1) Gp m₀ ((Equiv.addRight t) '' X₁) F'
        ((Equiv.addRight t) '' Y) u' =
      evTerm (fun i : ParIdx Gp X₁ => i.1.1) Gp m₀ X₁ F Y u :=
  evTerm_relabel (fun i : ParIdx Gp X₁ => i.1.1) (fun i : ParIdx Gp X₁' => i.1.1) _ hR
    (DecEquiv.PolymerSymm.ofTranslate hGp hN t ht) S (fun _ => rfl) (fun i => i.1.2) X₁ Y hF hF'
    hff

end Cov


/-- A function of the parameters analytic on a polydisc stays analytic after relabelling the
parameters by a bijection. -/
theorem analyticOnNhd_comp_relabel {ι ι' : Type*} [Fintype ι] [Fintype ι'] (κ : ι ≃ ι') {R : ℝ}
    {f : (ι → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f (polydisc (0 : ι → ℂ) (fun _ => R))) :
    AnalyticOnNhd ℂ (fun s : ι' → ℂ => f (s ∘ κ)) (polydisc (0 : ι' → ℂ) (fun _ => R)) := by
  let ℓ : (ι' → ℂ) →L[ℂ] (ι → ℂ) := LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ κ)
  have hℓ : ∀ s, ℓ s = s ∘ κ := fun s => rfl
  have h := hf.comp (fun s _ => (ℓ.analyticAt s)) (s := polydisc (0 : ι' → ℂ) (fun _ => R))
    (fun s hs i => by simpa [hℓ] using hs (κ i))
  simpa [Function.comp_def, hℓ] using h

section Cast

variable {d : ℕ}

/-- A multiple `z` of a divisor `a` of `n` has a representative in `ZMod n` divisible by `a`. -/
theorem dvd_val_intCast {n a : ℕ} [NeZero n] (han : a ∣ n) {z : ℤ} (hz : (a : ℤ) ∣ z) :
    a ∣ ((z : ZMod n)).val := by
  have h1 : (((z : ZMod n)).val : ℤ) = z % (n : ℤ) := ZMod.val_intCast z
  have h2 : (a : ℤ) ∣ (((z : ZMod n)).val : ℤ) := by
    rw [h1, Int.emod_def]
    exact dvd_sub hz (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 han) _)
  exact Int.natCast_dvd_natCast.1 h2

/-- **The transport map commutes with the translation by an integer vector near the origin.**
If `c` and `c + z` lie in the centred box of radius `r` of the torus of side `m` (that is, the
centred representatives of `c + z` are the sums `c_μ + z_μ`) and `2 r + 1 < m`, then
`boxMap (c + z) = boxMap c + z`, the same integer vector `z` being added on the two tori.
Only the torus of side `m` is constrained by `2 r + 1 < m`. -/
theorem boxMap_add_intCast {m m' r : ℕ} [NeZero m] (hm : 2 * r + 1 < m) (c : Torus d m)
    (z : Fin d → ℤ) (hc : ∀ μ, |(c μ).valMinAbs + z μ| ≤ r) :
    boxMap m m' (c + fun μ => ((z μ : ℤ) : ZMod m)) =
      boxMap m m' c + fun μ => ((z μ : ℤ) : ZMod m') := by
  funext μ
  have h1 : (c + fun μ => ((z μ : ℤ) : ZMod m)) μ = (((c μ).valMinAbs + z μ : ℤ) : ZMod m) := by
    simp
  show ((((c + fun μ => ((z μ : ℤ) : ZMod m)) μ).valMinAbs : ℤ) : ZMod m') = _
  rw [h1]
  rw [valMinAbs_intCast_of_abs_le hm (hc μ)]
  simp [boxMap]

end Cast


section Recentre

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl

/-- **Recentring the transport of one step term** (item 24, part 2, general form).  Let `tA`, `tB`
be translations of the two step tori by multiples of the cell side `a_{k+1}`, and let the cover
`X₁` and the domain `Y` of the term lie, after the translation `x ↦ x + tA`, in the centred box of
radius `R` with `20 R + 20` below both torus sides; `X₁` contains a box of side `L a_{k+1}`.
The transport map recentred at `tA`, `tB` is `φ x = bm (x + tA) - tB` (equal to `bm x` where the
translations do not wrap, `boxMap_add_intCast`).  If the recentred functions
`F̃ = F ∘ κA` and `F̃' = F' ∘ κB` (the functions of the translated parameters) have corresponding
coefficients (`hcoef`, the hypothesis of `evTerm_boxMap_of_width` at the translated sets), then the
term of `φ '' Y` on the second torus equals the term of `Y` on the first. -/
theorem evTerm_boxMap_recentred {U U' : Type*} {m₀ : ℕ} {R : ℕ} {ρ : ℝ} (hρ : 1 < ρ)
    (hd : 0 < d) (hL : 2 ≤ L)
    (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁) (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hn : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))}
    (hbox : ∃ b, box b (L * cellSide L m₀ m₁ (k + 1)) ⊆ X₁)
    (hX : ∀ x ∈ X₁, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA))
    {S' : Set (CTorus d L N₁' m₁ (k + 1))}
    (hS' : S' = (fun x => bm (x + tA) - tB) '' X₁)
    {F : U → (ParIdx (GA) X₁ → ℂ) → ℂ} {F' : U' → (ParIdx (GB) S' → ℂ) → ℂ} {u : U} {u' : U'}
    (hF : AnalyticOnNhd ℂ (F u) (polydisc (0 : ParIdx (GA) X₁ → ℂ) (fun _ => ρ)))
    (hF' : AnalyticOnNhd ℂ (F' u') (polydisc (0 : ParIdx (GB) S' → ℂ) (fun _ => ρ)))
    {FA : U → (ParIdx (GA) ((Equiv.addRight tA) '' X₁) → ℂ) → ℂ}
    {FB : U' → (ParIdx (GB) ((Equiv.addRight tB) '' S') → ℂ) → ℂ}
    (hFA : FA = fun u s => F u (s ∘ parEquiv
      (DecEquiv.CoverSymm.ofTranslate (isLevel_levelGS (by omega) le_rfl) tA
        (fun μ => (pow_dvd_pow L (by omega)).trans (htA μ)))
      (DecEquiv.PolymerSymm.ofTranslate (isLevel_levelGS (by omega) le_rfl) hN tA htA) rfl))
    (hFB : FB = fun u s => F' u (s ∘ parEquiv
      (DecEquiv.CoverSymm.ofTranslate (isLevel_levelGS (by omega) le_rfl) tB
        (fun μ => (pow_dvd_pow L (by omega)).trans (htB μ)))
      (DecEquiv.PolymerSymm.ofTranslate (isLevel_levelGS (by omega) le_rfl) hN' tB htB) rfl))
    (hcoef : ∀ C ∈ connFams (fun i : ParIdx (GA) ((Equiv.addRight tA) '' X₁) => i.1.1) (GA) m₀
        ((Equiv.addRight tA) '' X₁) ((Equiv.addRight tA) '' Y),
      ∀ C' : Finset (ParIdx (GB) ((Equiv.addRight tB) '' S')),
        (∀ i ∈ C, ∃ i' ∈ C', i'.1.1 = Prod.map id bm i.1.1) →
        (∀ i' ∈ C', ∃ i ∈ C, i'.1.1 = Prod.map id bm i.1.1) →
        coef (FB u') C' = coef (FA u) C) :
    evTerm (fun i : ParIdx (GB) S' => i.1.1) (GB) m₀ S' F'
        ((fun x => bm (x + tA) - tB) '' Y) u' =
      evTerm (fun i : ParIdx (GA) X₁ => i.1.1) (GA) m₀ X₁ F Y u := by
  have hGA : IsLevel (GA) (k + 1) := isLevel_levelGS (by omega) le_rfl
  have hGB : IsLevel (GB) (k + 1) := isLevel_levelGS (by omega) le_rfl
  have hSA := DecEquiv.LatSymm.ofTranslateLevel hGA tA (fun μ => (pow_dvd_pow L (by omega)).trans (htA μ))
  have hSB := DecEquiv.LatSymm.ofTranslateLevel hGB tB (fun μ => (pow_dvd_pow L (by omega)).trans (htB μ))
  -- the two translations
  have hA := evTerm_translate_aligned (R := ρ) hρ hGA hN tA htA hSA (X₁' := (Equiv.addRight tA) '' X₁) X₁ Y rfl
    (F := F) (F' := FA) (u := u) (u' := u) hF (by rw [hFA]; exact analyticOnNhd_comp_relabel _ hF)
    (by intro s _; rw [hFA])
  have hB := evTerm_translate_aligned (R := ρ) hρ hGB hN' tB htB hSB (X₁' := (Equiv.addRight tB) '' S') S'
    ((fun x => bm (x + tA) - tB) '' Y) rfl
    (F := F') (F' := FB) (u := u') (u' := u') hF' (by rw [hFB]; exact analyticOnNhd_comp_relabel _ hF')
    (by intro s _; rw [hFB])
  have hSt : (Equiv.addRight tB) '' S' = bm '' ((Equiv.addRight tA) '' X₁) := by
    rw [hS', Set.image_image, Set.image_image]
    exact Set.image_congr (fun x _ => by simp)
  have hYt : (Equiv.addRight tB) '' ((fun x => bm (x + tA) - tB) '' Y) =
      bm '' ((Equiv.addRight tA) '' Y) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr (fun x _ => by simp)
  have hbox' : ∃ b, box b (L * cellSide L m₀ m₁ (k + 1)) ⊆ (Equiv.addRight tA) '' X₁ := by
    obtain ⟨b, hb⟩ := hbox
    refine ⟨b + tA, fun x hx => ?_⟩
    refine ⟨x - tA, hb ?_, by simp⟩
    exact (DecEquiv.mem_box_add_iff b tA (x - tA) _).1 (by simpa using hx)
  have hmain := evTerm_boxMap_of_width (U := U) (U' := U') (m₀ := m₀) (R := R) (L := L) (N₁ := N₁)
    (N₁' := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) hd hL hm₀ hm₁ hN hN' hn hn' hbox'
    (X₁ := (Equiv.addRight tA) '' X₁)
    (fun x hx => by obtain ⟨y, hy, rfl⟩ := hx; exact hX y hy)
    (Y := (Equiv.addRight tA) '' Y) (fun x hx => by obtain ⟨y, hy, rfl⟩ := hx; exact hY y hy)
    (S' := (Equiv.addRight tB) '' S') hSt (F := FA) (F' := FB) (u := u) (u' := u') hcoef
  rw [← hB, hYt]
  exact hmain.trans hA

end Recentre

end Balaban.Polymer.TwoTorusStep
