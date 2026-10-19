/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityMarks
public import Balaban.Fluctuation.LocalPairCast
public import Balaban.Fluctuation.MarkedVBlockDec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The marked terms of the old labels recomputed on a local generating set (`NewLevelOldTermsBg`)

P3 pp. 78-79, (4.44)-(4.47): the terms of the new level are recomputed with the local generating set
`𝔹_{k+1}(Y)` of their polymer.  For the activities and marks built from the localized old terms
(the decoupled terms `evDec` of the labels `Y` of the expansion of an old term `E` along the masked
tangent), the recomputed term is `evDecBg` on a generating set `Gl` with the canonical transport
(`BgTransport.canon`: the parameters `s` on the cubes based in the top layer of `Gl`, `0` on the
others; the extension by zero off the unit blocks of `Gl`; the restriction of the hat variable; the
datum cut off to the data of `Gl`) and the preimage `maskPre` of the mask.

* `markedHatPsiFBg_canon_res`: the masked tangent of the canonical transport at the restricted hat
  variable, in the explicit form of the local side of `coef_eTermFun_replacement_marked_gen`;
* `evDecBg_canon_eq_evDec`: **the replacement identity for the marked term of a label `Y`**.  If
  `Gl` is cube aligned and sup-separated, `Gd ≺ Gl` has the layer `k` of `Gl` and no layer `k + 1`,
  the cubes meeting the set `X₁` of the old term and the data sites of its generating set `Gk` lie
  in `Y`, and the `2 M₁ L^{k+1}`-neighbourhood of `Y` lies in the top layer of `Gl` (the margin), then
  at a datum `D` of the step chart of radius `ε` and a hat variable of the box, the term recomputed on
  `(Gl, Gd)` at the read datum (radius `ε′ ≥ (2 K₁ + 2) C₁ ε`) and the restricted hat variable equals
  the step's term, for every pair of marks of the radius set;
* `deriv_evDecBg_canon_eq_deriv_evDec`: the same for the mark derivative `∂_t|₀`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset
  Balaban.LargeField Balaban.SmallField.GsSpec Balaban.Fluctuation Matrix

section Tangent

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱl : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}

/-- **The masked tangent of the canonical transport at the restricted hat variable**: the marked
hat field `markedHatPsiFBg Gl … (canon).lift … (maskPre hG' Gl Zm) u t s Θ ((canon).res ψ̂)` is
`(u + 1[unitPt x ∈ Zm] t)` times the local hat lift of `cc • C^{1/2}_{Gl}(s) ψ̂′`, `ψ̂′` the
restriction of `ψ̂` to the unit lattice of `Gl` (zero off the unit blocks of `Gl`). -/
theorem markedHatPsiFBg_canon_res (hG' : IsLevel Gp (k + 1)) (a₁ ν : ℝ) (cc : ℂ)
    (F₁ : DecParams Gl × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ))
    (Zm : Finset (unitPts Gp)) (u t : ℂ) (s : DecParams Gl)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (ψh : unitPts Gp × Fin N → ℂ) :
    markedHatPsiFBg Gl a₁ ν (BgTransport.canon Gp Gl N).lift cc F₁ (maskPre hG' Gl Zm) u t s Θ
        ((BgTransport.canon Gp Gl N).res ψh) =
      fun x i => (u + if unitPt hG' x ∈ Zm then t else 0) *
        (if h : unitBlock x ∈ unitPts Gl then
          (cc • (decCovSqrt Gl (compWeight L a₁) a₁ ν (F₁ (s, Θ)).2 (Dec2.extS (coverOf Gl) s)
            (barField Gl Θ.1 (F₁ (s, Θ)).1) (unitQ Gl) (unitP Gl) *ᵥ
            (fun p => if hp : p.1.1 ∈ unitPts Gp then ψh (⟨p.1.1, hp⟩, p.2) else 0)))
            (⟨unitBlock x, h⟩, i)
        else 0) := by
  have hres : (fun p : unitPts Gl × Fin N =>
      if hp : p.1.1 ∈ unitPts Gp then ψh (⟨p.1.1, hp⟩, p.2) else 0) =
      (BgTransport.canon Gp Gl N).res ψh :=
    funext fun p => (resZ_apply ψh p).symm
  have hlift : (BgTransport.canon Gp Gl N).lift = liftZ (N := N) Gl := rfl
  funext x i
  rw [hres, hlift, markedHatPsiFBg_liftZ_preimage_mask hG' a₁ ν cc F₁ Zm u t s Θ _ x i]
  rfl

end Tangent

section Term

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm ϱ₁ ϱ₂ ϱl ϱl' : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
  {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
  {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl'} {ν : ℝ}

/-- **The marked term of an old label recomputed on a local generating set** (P3 pp. 78-79, (4.46),
along the masked tangent `u ψ' + t M_Z ψ'`).  Let `𝔹_{k+1} = Gp` be a level set, `Hm` a level set of
level `k` (`k ≥ 1`), `Gl` a cube-aligned, sup-separated generating set and `Gd ≺ Gl` with the layer
`k` of `Gl` and no layer `k + 1`.  For a label `Y` of the expansion of the old term `E` (generating
sets `Gk`, `Gj`, set `X₁`) whose `2 M₁ L^{k+1}`-neighbourhood lies in the top layer of `Gl`, with the
cubes meeting `X₁` and the data sites of `Gk` inside `Y`, the decoupled maps `F₁`, `Sol` of the step
and `F₁'`, `Sol'` of `(Gl, Gd)` given by their specifications: at a datum `D` of the step chart of
radius `ε`, a hat variable `ψ̂` of the box `|ψ̂| ≤ c_ψ` and marks `(um, tm)` of the radius set, the
term `evDecBg` recomputed on `Gl` with the canonical transport (at the read datum, of radius
`ε′ ≥ (2 K₁ + 2) C₁ ε`, and the restricted hat variable) equals the step's term `evDec`.  The
hypotheses on `ε′` are smallness conditions against absolute constants. -/
theorem evDecBg_canon_eq_evDec (hG' : IsLevel Gp (k + 1)) (hG : IsLevel Hm k) (hk1 : 1 ≤ k)
    (hA : CubeAligned Gl m₁) (hSS : SupSep Gl m₁) (hPd : Precedes Gd Gl)
    (hdk : Gd.Ω k = Gl.Ω k) (hdtop : Gd.Ω (k + 1) = ∅)
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl - 1))
    (hagd : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl' - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (HB' : BgHyp d L (k + 1) ϱl (compWeight L a₁) ν)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ)
          s D φ α → F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L a₁) ν (rho4 d L N BG κ)
          s D φ α → F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf Gl) × Edat Gd N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Gd (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small Gd (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {eps eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hεr : (2 * bgK1 d L N + 2) * xiC1 d * eps ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀)
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (Zm : Finset (unitPts Gp)) (um tm : ℂ)
    (hδ₁m : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hU : LayerUnion Gp m₀) (hNm : L ^ m₀ ∣ N₁) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hXY : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) →
      ∀ y ∈ Pset m₁ P, y ∈ Y)
    (hkY : ∀ x ∈ dataSites Gk, x ∈ Y)
    (hYmar : ∀ x ∈ Y, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) → y ∈ Gl.Ω (k + 1))
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (ψh : unitPts Gp × Fin N → ℂ) (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    evDecBg Gp X₁f m₀ j 𝒦X Gl a₁ ν (BgTransport.canon Gp Gl N) cc F₁' Sol'
        (eTermFun Gl Gk Gj Gd ac Fk E) (maskPre hG' Gl Zm) um tm Y
        (rawOf D, (BgTransport.canon Gp Gl N).res ψh) =
      evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (eTermFun Gp Gk Gj Hm ac Fk E) Zm um tm Y
        (rawOf D, ψh) := by
  classical
  have hd0 : 0 < d := by have := HB.hd; omega
  have hxi := one_le_xiC1 d
  have hK1 : 0 < bgK1 d L N := bgK1_pos d L N
  have hle : eps ≤ eps' := by
    have h1 : eps ≤ xiC1 d * eps := le_mul_of_one_le_left heps.le hxi
    have h2 : xiC1 d * eps ≤ (2 * bgK1 d L N + 2) * xiC1 d * eps := by
      have h0 : 0 ≤ xiC1 d * eps := by positivity
      nlinarith
    linarith
  have hc1 : xiC1 d * eps ≤ bgC1 d L N := hc7.trans (c7_le_bgC1 d L N BG κ)
  have hc0 : xiC1 d * eps ≤ bgC0 d L N := hc1.trans (bgC1_le_bgC0 d L N hd0)
  have hD'x := canon_gdat_xiCData_of_xiCData (Gb := Gl) hG' HB HB' heps hsmall hc0 hc1 hεr D hD
  have hD' : ∀ x ∈ Gl.Ω (k + 1),
      ((BgTransport.canon Gp Gl N).gdat (BgTransport.reads_canon hG') D).Ψ x = D.Ψ x ∧
        ((BgTransport.canon Gp Gl N).gdat (BgTransport.reads_canon hG') D).h x = D.h x :=
    fun x hx => by
      have h := canon_gdat_eq_of_mem_one hG' D (Gl.Ω_antitone le_rfl (Nat.le_add_left 1 k)
        (by omega) hx)
      exact ⟨h.1.symm, h.2.symm⟩
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  unfold evDecBg evDec evTerm FFmarked
  refine Finset.sum_congr rfl fun C hC => ?_
  have hY := ((mem_connFams _).1 hC).2
  have key := coef_eTermFun_replacement_marked_gen (Gj := Gj) hG' hG hk1 hA hSS hPd hdk hdtop hN hm₁
    hM hag hagm hagl hagd hS HB HB' ha₁ ha₂ hκ hMc hMX hF₁ hF₁' hF₂ hM₂ h0 h1 hδ₀ hδ₁ hSol hSol' ac
    Fk E C hE1 le_rfl heps hsmall hc7 hphi hle hsmall' hc7' hphi' hδ₀e hD hD'x hD' hmarD' hαD' hsm cc hcψ
    Zm um tm hδ₁m ψh hψh (R := Finset.univ.filter (· ∈ Y))
    (fun i hi y hy => by
      rw [Finset.mem_filter, ← hY]
      exact ⟨Finset.mem_univ _,
        Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, Pset_subset_Dsites hU hNm i.1.2 hy⟩)⟩)
    (fun P hP hdis y hy => Finset.mem_filter.2 ⟨Finset.mem_univ _, hXY P hP hdis y hy⟩)
    (fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, hkY x hx⟩)
    (fun x hx => hYmar x (Finset.mem_filter.1 hx).2)
  refine Eq.trans ?_ key.symm
  refine congrArg (fun f => coef f C) (funext fun w => ?_)
  simp only [FFmarkedBg]
  rw [markedHatPsiFBg_canon_res hG' a₁ ν cc F₁' Zm um tm
    ((BgTransport.canon Gp Gl N).par (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w))
    ((BgTransport.canon Gp Gl N).dat (rawOf D)) ψh]
  rfl

end Term

end Balaban.Localization
