/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalIsoEvStd
public import Balaban.Polymer.LocalIsoEnergy
public import Balaban.Polymer.TwoTorusDirectTerms
public import Balaban.Fluctuation.NewLevelZeroSourceBg
import Mathlib.Tactic.Linarith

/-!
# Local generating sets on two tori: the zero-source activities

The zero-source term `zeroTermBg` of a domain `Y` recomputed on a local pair `(Gl, Gd)` with the
canonical transport is `-β ∑_z [Y ∈ polyDom_z] σ ∫₀¹ ω(t) ∂_w³ Ev_z(Θ, σ t x₀) dt`, with `Ev_z` the
term `evDecBg` of the block energy of the block `z` (local cover of its corner, marks `(1, 0)`, no
mask).  For `(Gl, Gd)` carried onto `(Gl', Gd')` by the box map, the terms of `bm '' Y` on the second
torus and of `Y` on the first agree: the blocks `z` with `Y` as a domain correspond to the blocks
`bc z` (`mem_polyDom_blockSite_boxMap`), the third derivative reads the term on a disc of the ray
(`rayTerm_dl3_eq_of_line`), and on that disc the terms agree (`OmegaIso.evDecBg_canon_twoTorus` with
the block energy functional, `OmegaIso.blockEnergyFun_eq`, and the empty frozen region).

* `OmegaIso.zeroBlockTerm_twoTorus`: the ray term of one block;
* `OmegaIso.zeroSum_twoTorus`: the sum over the blocks;
* `OmegaIso.zeroActBg_twoTorus`: the zero-source activities of the steps `hatStepKG` of the two
  tori, at parameters of the two local charts whose raw data correspond on the box and block
  variables corresponding at the unit points of the box, for `‖u‖ ≤ 1`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Polymer
  Balaban.Polymer.TwoTorusStep Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Analysis Matrix

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱb ϱb' ϱm ϱm' : ℝ}

set_option hygiene false in
local notation "bk" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "ρ₁" => R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)
set_option hygiene false in
local notation "SA" => Balaban.Inhabited.LevelStep.hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k
  m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => Balaban.Inhabited.LevelStep.hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2
  k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))

namespace OmegaIso

variable {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Gb' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱb'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'} {ρ : ℕ}

/-- **The ray term of one block on two tori** (local pairs).  For a block `z` whose expansion (local
cover of its corner) has the domain `Y` of the box of radius `R`, the ray terms
`σ ∫₀¹ ω(t) ∂_w³ evDecBg(…)(Θ, σ t x₀) dt` of the block energy of `bc z` at `bm '' Y` on `(Gb', Hm')`
and of `z` at `Y` on `(Gb, Hm)` agree, for data of the charts corresponding on the box of radius
`ρ + 1`, hat fields of size `≤ ρ₀` (`2 ρ₀ ≤ c_ψ`) corresponding on the box of radius `ρ` and
`‖σ‖ ≤ 1`. -/
theorem zeroBlockTerm_twoTorus (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    {a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁ Kc Cx : ℝ} (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    (hC : FlCore N Gb Hm a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hC' : FlCore N Gb' Hm' a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hHm : Hm.Ω (k + 1) = ∅) (hHm' : Hm'.Ω (k + 1) = ∅)
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L a₁) ν Kc Cx)
    (Sb' : Dec2.CoverBase (coverOf Gb') Gb' (compWeight L a₁) ν Kc Cx)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX' : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hrad : markedRad d L N k a₁ κ cψ cc < δ₁)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    {F₁' : DecParams Gb' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gb N,
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf Gb')) (D : BgData Gb' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb'.Ω 1 × Fin N → ℂ)
        (α : Gb'.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb') Gb' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf Gb') × Edat Hm' N → (Hm'.Ω 1 × Fin N → ℂ) × (Hm'.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf Gb) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf Gb') × Edat Hm' N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm' N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi Hm' (Dec2.decG (coverOf Gb') Hm' (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm' (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf Gb') Hm' (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm' (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small Hm' (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm' (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm' (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm'.Ω 1 → ℂ, Small Hm' δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb') Hm' (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm' (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {R : ℕ} (hρR : ρ ≤ R)
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnE : 2 * (R + L ^ k + L ^ (k + 1) + 1) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnE' : 2 * (R + L ^ k + L ^ (k + 1) + 1) + 3 * L ^ (k + 1) + 5 <
      (N₁' * L ^ m₁) * L ^ (k + 1))
    (z : TA) {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hY : Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
      (LocalCover.fam m₀ (LocalCover.blockSite k z)))
    {D : BgData Gb N} {D' : BgData Gb' N}
    (hD : XiCData Gb (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gb' (compWeight L a₁) ν (k + 1) 1 eps D')
    (hΨ : FieldCorr (ρ + 1) D.Ψ D'.Ψ) (hh : FieldCorr (ρ + 1) D.h D'.h)
    {x₀ w : unitPts (GA) × Fin N → ℂ} {x₀' w' : unitPts (GB) × Fin N → ℂ} {ρ₀ : ℝ}
    (hx₀ : ∀ p, ‖x₀ p‖ ≤ ρ₀) (hw : ∀ p, ‖w p‖ ≤ ρ₀) (hx₀' : ∀ p, ‖x₀' p‖ ≤ ρ₀)
    (hw' : ∀ p, ‖w' p‖ ≤ ρ₀) (hρ₀ : 2 * ρ₀ ≤ cψ)
    (hhx : ∀ x, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, x₀' (unitPt hGB (bk x), i) = x₀ (unitPt hGA x, i))
    (hhw : ∀ x, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, w' (unitPt hGB (bk x), i) = w (unitPt hGA x, i))
    (ω : ℂ → ℂ) {σ : ℂ} (hσ : ‖σ‖ ≤ 1) :
    rayTerm (dl3 (fun u : RawData d L (N₁' * L ^ m₁) (k + 1) N × (unitPts (GB) × Fin N → ℂ) =>
        evDecBg (GB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k (bc z))) m₀ k
          (LocalCover.fam m₀ (LocalCover.blockSite k (bc z))) Gb' a₁ ν
          (BgTransport.canon (GB) Gb' N) cc F₁' Sol'
          (blockEnergyFun Gb' Hm' (compWeight L a₁) ν k (bc z)) ∅ 1 0 (bk '' Y)
          (u.1, (BgTransport.canon (GB) Gb' N).res u.2)) w') ω x₀' σ (rawOf D') =
      rayTerm (dl3 (fun u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts (GA) × Fin N → ℂ) =>
        evDecBg (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
          (LocalCover.fam m₀ (LocalCover.blockSite k z)) Gb a₁ ν
          (BgTransport.canon (GA) Gb N) cc F₁ Sol
          (blockEnergyFun Gb Hm (compWeight L a₁) ν k z) ∅ 1 0 Y
          (u.1, (BgTransport.canon (GA) Gb N).res u.2)) w) ω x₀ σ (rawOf D) := by
  classical
  obtain ⟨hz, hX, -⟩ := mem_polyDom_blockSite_boxMap (ϱ := ϱ) hN hN' hnF hnF' z hYR hY
  have hcs : (L - 1) * cellSide L m₀ m₁ (k + 1) ≤ L * cellSide L m₀ m₁ (k + 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le L 1)
  have hc1 : 1 ≤ 5 * (L * cellSide L m₀ m₁ (k + 1)) :=
    Nat.succ_le_of_lt (Nat.mul_pos (by norm_num)
      (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ (k + 1))))
  have hs : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hbs : LocalCover.blockSite k (bc z) = bk (LocalCover.blockSite k z) :=
    blockSite_boxMap le_rfl z hz (Nat.mul_div_le R _) hs
  obtain ⟨hcov, hX₁, hcov', hX₁'⟩ := covSetup_localCover_image (ϱ := ϱ) hN hN' (j := k) le_rfl
    (R := R) (by omega) (LocalCover.blockSite k z) hX
  have hF := nbhdF_image_finset hN hN' (R := R) (by omega) (LocalCover.blockSite k z) hX
  have hXR : ∀ x ∈ LocalCover.nbhdF m₀ (LocalCover.blockSite k z),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := fun x hx =>
    hX x (by rw [← LocalCover.coe_nbhdF]; exact hx)
  have hzR : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (LocalCover.blockSite k z) :=
    hX _ (cell_subset_nbhd _ (LocalCover.mem_cell m₀ _))
  have hjb : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (LocalCover.blockSite k z) = z :=
    LocalCover.jBlock_blockSite le_rfl z
  have hjb' : jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bk (LocalCover.blockSite k z)) = bc z := by
    rw [← hbs]; exact LocalCover.jBlock_blockSite le_rfl (bc z)
  -- the block energy functional on corresponding inputs
  have hΦ : ∀ (t : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))
      (t' : ((Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)) × (Hm'.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ))),
      (∀ x, t'.1.2 (hI.e x) = t.1.2 x) → (∀ y i, t'.2.1 (hH.e y, i) = t.2.1 (y, i)) →
      FieldCorr (ρ + 1) t.2.2.2 t'.2.2.2 →
      blockEnergyFun Gb' Hm' (compWeight L a₁) ν k (bc z) t'.1 t'.2.1 t'.2.2 =
        blockEnergyFun Gb Hm (compWeight L a₁) ν k z t.1 t.2.1 t.2.2 := by
    intro t t' hα' hδ' hψ'
    have := hI.blockEnergyFun_eq hH (compWeight L a₁) ν (R := R + L ^ k) (by omega) hnE hnE'
      (inBox_mono (by omega) hzR) t t' hα' hδ' hψ'
    rwa [hjb, hjb'] at this
  refine rayTerm_dl3_eq_of_line _ _ ω x₀ w x₀' w' σ _ _ fun t ht τ hτ => ?_
  have hst : ‖σ * (t : ℂ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    nlinarith [norm_nonneg σ, ht.2]
  have h := hI.evDecBg_canon_twoTorus hH hk hGA hGB ha₁ ha₂ hC hC' hHm hHm' hS Sb Sb' hMX hMX' hCx
    hmar hα hsm cc hcψ hF₁an (hF₁) (hF₁') hSolan hSol hSol' hcov hX₁ hcov' hX₁'
    (X₁g := ∅) (fun x hx => by simp at hx) (fun x hx => by simp at hx) hρR
    (fun x hx => hXR x hx) hYR hnS hnS' hnF hnF'
    (Φ := blockEnergyFun Gb Hm (compWeight L a₁) ν k z)
    (Φ' := blockEnergyFun Gb' Hm' (compWeight L a₁) ν k (bc z))
    ((blockEnergyFun_analytic (compWeight L a₁) ν k z).mono (Set.subset_univ _))
    (fun t _ t' _ _ hα' hδ' _ _ hψ' => hΦ t t' hα' hδ' hψ') ∅ (um := 1) (tm := 0)
    (by simpa using hrad) hD hD' hΨ hh
    (ψh := (σ * (t : ℂ)) • x₀ + τ • w) (ψh' := (σ * (t : ℂ)) • x₀' + τ • w')
    (fun p => (norm_ray_add_le hx₀ hw hst hτ p).trans hρ₀)
    (fun p => (norm_ray_add_le hx₀' hw' hst hτ p).trans hρ₀)
    (fun x hx i => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hhx x hx i, hhw x hx i])
  rw [Finset.map_empty, hF, ← hbs] at h
  exact h

/-- **The zero-source sum over the blocks on two tori** (local pairs).  For a domain `Y` of the box of
radius `R`, the sum over the blocks `z'` of the second torus with `bm '' Y` as a domain of the ray
terms of `zeroBlockTerm_twoTorus` equals the sum over the blocks `z` of the first torus with `Y` as a
domain: the blocks correspond by `bc` (`mem_polyDom_blockSite_boxMap` in both directions). -/
theorem zeroSum_twoTorus (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    {a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁ Kc Cx : ℝ} (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    (hC : FlCore N Gb Hm a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hC' : FlCore N Gb' Hm' a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hHm : Hm.Ω (k + 1) = ∅) (hHm' : Hm'.Ω (k + 1) = ∅)
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L a₁) ν Kc Cx)
    (Sb' : Dec2.CoverBase (coverOf Gb') Gb' (compWeight L a₁) ν Kc Cx)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX' : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hrad : markedRad d L N k a₁ κ cψ cc < δ₁)
    {F₁ : TA → DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    {F₁' : TB → DecParams Gb' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
    (hF₁an : ∀ z, AnalyticOnNhd ℂ (F₁ z) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gb N,
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ z (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ z (s, rawOf D) = (φ, α))
    (hF₁' : ∀ z' (s : Dec2.DecParams (coverOf Gb')) (D : BgData Gb' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb'.Ω 1 × Fin N → ℂ)
        (α : Gb'.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb') Gb' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' z' (s, rawOf D) = (φ, α))
    {Sol : TA → Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : TB → Dec2.DecParams (coverOf Gb') × Edat Hm' N →
      (Hm'.Ω 1 × Fin N → ℂ) × (Hm'.Ω 1 → ℂ)}
    (hSolan : ∀ z, AnalyticOnNhd ℂ (Sol z) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ z (p : Dec2.DecParams (coverOf Gb) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol z p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Small Hm (Sol z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2))
    (hSol' : ∀ z' (p : Dec2.DecParams (coverOf Gb') × Edat Hm' N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm' N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' z' p).1 = dphi Hm' (Dec2.decG (coverOf Gb') Hm' (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource Hm' (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' z' p).2 ∧
        Dec2.DecFixed (coverOf Gb') Hm' (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm' (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' z' p).2 ∧
        Small Hm' (Sol' z' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm' (Sol' z' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm' (Sol' z' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm'.Ω 1 → ℂ, Small Hm' δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb') Hm' (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm' (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' z' p).2))
    {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {R : ℕ} (hρR : ρ ≤ R)
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnE : 2 * (R + L ^ k + L ^ (k + 1) + 1) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnE' : 2 * (R + L ^ k + L ^ (k + 1) + 1) + 3 * L ^ (k + 1) + 5 <
      (N₁' * L ^ m₁) * L ^ (k + 1))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    {D : BgData Gb N} {D' : BgData Gb' N}
    (hD : XiCData Gb (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gb' (compWeight L a₁) ν (k + 1) 1 eps D')
    (hΨ : FieldCorr (ρ + 1) D.Ψ D'.Ψ) (hh : FieldCorr (ρ + 1) D.h D'.h)
    {x₀ w : unitPts (GA) × Fin N → ℂ} {x₀' w' : unitPts (GB) × Fin N → ℂ} {ρ₀ : ℝ}
    (hx₀ : ∀ p, ‖x₀ p‖ ≤ ρ₀) (hw : ∀ p, ‖w p‖ ≤ ρ₀) (hx₀' : ∀ p, ‖x₀' p‖ ≤ ρ₀)
    (hw' : ∀ p, ‖w' p‖ ≤ ρ₀) (hρ₀ : 2 * ρ₀ ≤ cψ)
    (hhx : ∀ x, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, x₀' (unitPt hGB (bk x), i) = x₀ (unitPt hGA x, i))
    (hhw : ∀ x, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, w' (unitPt hGB (bk x), i) = w (unitPt hGA x, i))
    (ω : ℂ → ℂ) {σ : ℂ} (hσ : ‖σ‖ ≤ 1) :
    (∑ z' : TB, if bk '' Y ∈ polyDom (GB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z')) m₀ k
          (LocalCover.fam m₀ (LocalCover.blockSite k z')) then
        rayTerm (dl3 (fun u : RawData d L (N₁' * L ^ m₁) (k + 1) N × (unitPts (GB) × Fin N → ℂ) =>
          evDecBg (GB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z')) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k z')) Gb' a₁ ν
            (BgTransport.canon (GB) Gb' N) cc (F₁' z') (Sol' z')
            (blockEnergyFun Gb' Hm' (compWeight L a₁) ν k z') ∅ 1 0 (bk '' Y)
            (u.1, (BgTransport.canon (GB) Gb' N).res u.2)) w') ω x₀' σ (rawOf D')
      else 0) =
      ∑ z : TA, if Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
          (LocalCover.fam m₀ (LocalCover.blockSite k z)) then
        rayTerm (dl3 (fun u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts (GA) × Fin N → ℂ) =>
          evDecBg (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k z)) Gb a₁ ν
            (BgTransport.canon (GA) Gb N) cc (F₁ z) (Sol z)
            (blockEnergyFun Gb Hm (compWeight L a₁) ν k z) ∅ 1 0 Y
            (u.1, (BgTransport.canon (GA) Gb N).res u.2)) w) ω x₀ σ (rawOf D)
      else 0 := by
  have hc1 : L ^ (k + 1) ≤ 5 * (L * cellSide L m₀ m₁ (k + 1)) := by
    have h1 : L ^ (k + 1) ≤ cellSide L m₀ m₁ (k + 1) := by
      unfold cellSide
      exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega)
    have h2 : cellSide L m₀ m₁ (k + 1) ≤ L * cellSide L m₀ m₁ (k + 1) :=
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne L))
    omega
  have hcA := coarse_margin (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (r := R) (by omega)
  have hcB := coarse_margin (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (r := R) (by omega)
  have hsB : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hYR' : ∀ y ∈ bk '' Y, InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) y := by
    rintro _ ⟨y, hy, rfl⟩
    exact inBox_boxMap hsB (hYR y hy)
  have hYY : boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) '' (bk '' Y) =
      Y := image_image_boxMap hsB hYR
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun z => bc z)
    (fun z' => boxMap (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
      (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z') ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨Finset.mem_univ _,
      (mem_polyDom_blockSite_boxMap (ϱ := ϱ) hN hN' hnF hnF' z hYR hz.2).2.2⟩
  · intro z' hz'
    rw [Finset.mem_filter] at hz' ⊢
    have h := (mem_polyDom_blockSite_boxMap (ϱ := ϱ) hN' hN hnF' hnF z' hYR' hz'.2).2.2
    rw [hYY] at h
    exact ⟨Finset.mem_univ _, h⟩
  · intro z hz
    exact boxMap_boxMap hcB (mem_polyDom_blockSite_boxMap (ϱ := ϱ) hN hN' hnF hnF' z hYR
      (Finset.mem_filter.1 hz).2).1
  · intro z' hz'
    exact boxMap_boxMap hcA (mem_polyDom_blockSite_boxMap (ϱ := ϱ) hN' hN hnF' hnF z' hYR'
      (Finset.mem_filter.1 hz').2).1
  · intro z hz
    rw [Finset.mem_filter] at hz
    exact (hI.zeroBlockTerm_twoTorus hH hk hGA hGB ha₁ ha₂ hC hC' hHm hHm' hS Sb Sb' hMX hMX' hCx
      hmar hα hsm cc hcψ hrad (hF₁an z) (hF₁ z) (hF₁' (bc z)) (hSolan z) (hSol z) (hSol' (bc z))
      hN hN' hρR hnS hnS' hnF hnF' hnE hnE' z hYR hz.2 hD hD' hΨ hh hx₀ hw hx₀' hw' hρ₀ hhx hhw
      ω hσ).symm

/-- **The zero-source activities of the steps of two tori recomputed on corresponding local pairs.**
For the steps `hatStepKG` on the tori `N₁`, `N₁'`, the local pairs `(Gb, Hm)`, `(Gb', Hm')` carried
onto each other by the box map with their standing hypotheses and the decoupling pairs `(F₂, Sol₂)`,
`(F₂', Sol₂')` of all blocks with their defining properties: at parameters `θ`, `θ'` of the two local
charts whose raw data correspond on the box of radius `ρ + 1`, block variables corresponding at the
unit points of the box of radius `ρ`, the hat radius `ρ_h` with `2 ρ_h ≤ c_ψ` and `‖u‖ ≤ 1`, the
zero-source activities of `bm '' Y` on the second torus and of `Y` on the first agree. -/
theorem zeroActBg_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    {c BG κ eps Kc' Cx' c₂ BG₂ δ₁ Kc Cx : ℝ}
    (hC : FlCore N Gb Hm (SA).a₁ (SA).ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hC' : FlCore N Gb' Hm' (SA).a₁ (SA).ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hHm : Hm.Ω (k + 1) = ∅) (hHm' : Hm'.Ω (k + 1) = ∅)
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L (SA).a₁) (SA).ν Kc Cx)
    (Sb' : Dec2.CoverBase (coverOf Gb') Gb' (compWeight L (SA).a₁) (SA).ν Kc Cx)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX' : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hrad : markedRad d L N k (SA).a₁ κ cψ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    {F₂ : TA → DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    {F₂' : TB → DecParams Gb' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
    (hF₂an : ∀ z, AnalyticOnNhd ℂ (F₂ z) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gb N,
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) (SA).ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₂ : ∀ z (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) (SA).ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L (SA).a₁) (SA).ν (rho4 d L N BG κ) s D φ α →
        F₂ z (s, rawOf D) = (φ, α))
    (hF₂' : ∀ z' (s : Dec2.DecParams (coverOf Gb')) (D : BgData Gb' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb' (bgC0 d L N) (c7 d L N BG κ) (SA).ν D → ∀ (φ : Gb'.Ω 1 × Fin N → ℂ)
        (α : Gb'.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb') Gb' (compWeight L (SA).a₁) (SA).ν (rho4 d L N BG κ) s D φ α →
        F₂' z' (s, rawOf D) = (φ, α))
    {Sol₂ : TA → Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol₂' : TB → Dec2.DecParams (coverOf Gb') × Edat Hm' N →
      (Hm'.Ω 1 × Fin N → ℂ) × (Hm'.Ω 1 → ℂ)}
    (hSol₂an : ∀ z, AnalyticOnNhd ℂ (Sol₂ z) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol₂ : ∀ z (p : Dec2.DecParams (coverOf Gb) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₂ z p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
        Small Hm (Sol₂ z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol₂ z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol₂ z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ z p).2))
    (hSol₂' : ∀ z' (p : Dec2.DecParams (coverOf Gb') × Edat Hm' N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm' N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₂' z' p).1 = dphi Hm' (Dec2.decG (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' z' p).2 ∧
        Dec2.DecFixed (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' z' p).2 ∧
        Small Hm' (Sol₂' z' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm' (Sol₂' z' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm' (Sol₂' z' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm'.Ω 1 → ℂ, Small Hm' δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' →
            δα' = (Sol₂' z' p).2))
    {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {R : ℕ} (hρR : ρ ≤ R)
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnE : 2 * (R + L ^ k + L ^ (k + 1) + 1) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnE' : 2 * (R + L ^ k + L ^ (k + 1) + 1) + 3 * L ^ (k + 1) + 5 <
      (N₁' * L ^ m₁) * L ^ (k + 1))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    {θ : physParamBg N Gb} {θ' : physParamBg N Gb'}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb' (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps)
    (hraw₁ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).1)
    (hraw₂ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).2)
    {ρh : ℝ} (hρh : 0 < ρh) (hρc : 2 * ρh ≤ cψ) (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (Φ : ∀ b, ((SA).blockSplit m₀ hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit m₀ hp').Ωb b)
    (hΦ : ∀ x, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Φ' ((SB).cellOf m₀ (unitPt hGB (bk x))) ⟨unitPt hGB (bk x), rfl⟩ =
        Φ ((SA).cellOf m₀ (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩)
    (ω : ℂ → ℂ) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    zeroActBg (SB) Gb' (BgTransport.canon (SB).G' Gb' N)
        (fun b => LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) (fun _ => k)
        (fun b => LocalCover.fam m₀ (LocalCover.blockSite k b)) m₀ F₂' Sol₂' ω ρh hp' eps θ' u
        (bk '' Y) Φ' =
      zeroActBg (SA) Gb (BgTransport.canon (SA).G' Gb N)
        (fun b => LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) (fun _ => k)
        (fun b => LocalCover.fam m₀ (LocalCover.blockSite k b)) m₀ F₂ Sol₂ ω ρh hp eps θ u Y Φ := by
  have hu2 : ‖u‖ < 2 := by linarith
  have hc1 : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps ∧ ‖u‖ < 2 := ⟨hθ, hu2⟩
  have hc2 : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb' (compWeight L (SB).a₁) (SB).ν (k + 1) 1 eps ∧ ‖u‖ < 2 := ⟨hθ', hu2⟩
  obtain ⟨D, hD, hDe⟩ := hθ
  obtain ⟨D', hD', hDe'⟩ := hθ'
  unfold zeroActBg
  rw [ite_eq_left hc1, ite_eq_left hc2]
  congr 1
  unfold zeroTermBg
  congr 1
  rw [hDe, hDe']
  have hΨ : FieldCorr (ρ + 1) D.Ψ D'.Ψ := by
    intro z hz
    have := hraw₁ z hz
    rw [hDe, hDe'] at this
    exact this
  have hh : FieldCorr (ρ + 1) D.h D'.h := by
    intro z hz
    have := hraw₂ z hz
    rw [hDe, hDe'] at this
    exact this
  have hhat := hatOf_boxMap hGA hGB hN2 hk νS β p₁ δ m₀ ρh hp hp' Φ Φ' hΦ
  exact hI.zeroSum_twoTorus hH hk hGA hGB (by show (1 / 2 : ℝ) ≤ 1; norm_num)
    (by show (1 : ℝ) ≤ 2; norm_num) hC hC' hHm hHm' hS Sb Sb'
    hMX hMX' hCx hmar hα hsm _ hcψ hrad hF₂an hF₂ hF₂' hSol₂an hSol₂ hSol₂' hN hN' hρR hnS hnS'
    hnF hnF' hnE hnE' hYR hD hD' hΨ hh (fun p => (SA).hatOf_mem m₀ hρh hp Φ p)
    (fun p => (SA).hatOf_mem m₀ hρh hp Φ p) (fun p => (SB).hatOf_mem m₀ hρh hp' Φ' p)
    (fun p => (SB).hatOf_mem m₀ hρh hp' Φ' p) hρc hhat hhat ω (σ := u) hu

end OmegaIso

end Balaban.Polymer.LocalIso
