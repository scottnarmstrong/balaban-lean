/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.NewLevelBlockTermsBg
public import Balaban.Fluctuation.LocalSetActRay
public import Balaban.Inhabited.StepTowerThetaDetG

/-!
# The zero-source activities recomputed on a background generating set (`NewLevelZeroSourceBg`)

P3 pp. 78-79, (4.44)-(4.47) and P6 Lemma 4.1 for the zero-source activities of the new level.  At
zero source the term of a domain `Y` is the potential part
`-β ∑_z [Y ∈ polyDom_z] σ ∫₀¹ ω(t) ∂_w³ evTerm_z(Y)(Θ, σ t x₀) dt`
of the localized block energies (`zeroSourceActivity_common_fromTowerG_core`): the ray integrals of
the third derivatives of the terms `evTerm_z(Y)` of the localization expansion of the block energy of
the block `B_{k+1}(z)`.  Recomputed on a background generating set `Gb` with a transport `Tr`, the
term of `Y` is the term `evDecBg` of the block energy of `Gb` at the marks `(1, 0)` (the unmasked
tangent), read at the restriction `Tr.res` of the step's hat variable.

* `zeroTermBg`: the zero-source term of a domain `Y` on `Gb`;
* `zeroTermBg_self`: at the step's own set and transport it is the step's formula (the terms of the
  block energy with the hat field `hatPsiF`, `FFmarked_one_zero`);
* `zeroTermBg_canon_eq`: **the replacement identity**: recomputed on a local generating set `Gl` with
  the canonical transport, at the datum read from a datum of the step chart, it equals the step's
  term, for a ray inside the box of the hat variables and a domain `Y` whose
  `2 M₁ L^{k+1}`-neighbourhood lies in the top layer of `Gl`;
* `zeroActBg`: the zero-source activity of a domain on `Gb` as a function of a parameter of `Gb`,
  `u² · zeroTermBg … Y (ψ̂, ψ̂) u` on the chart of `Gb` and the disc `‖u‖ < 2` (`ψ̂` the step's
  clamped hat field of the block configuration), `0` otherwise;
* `zeroActBg_canon_eq`: the replacement identity for the zero-source activities.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
  Balaban.LargeField Finset

section Defs

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb ϱm : ℝ}

/-- **The zero-source term of a domain `Y` on a background generating set `Gb`** (P3 pp. 78-79,
(4.46); P6 Lemma 4.1): `-β ∑_z [Y ∈ polyDom_z] σ ∫₀¹ ω(t) ∂_w³ Ev_z(Θ, σ t x₀) dt`, where
`Ev_z(Θ, ψ̂) = evDecBg … (blockEnergyFun Gb Hm … k z) ∅ 1 0 Y (Θ, Tr.res ψ̂)` is the term of the label
`Y` of the step's expansion of the block `z` (cover data `(m₀, j z, 𝒦_X z)`, region `X₁ z`),
computed on `Gb` with the transport `Tr` and the pair `(F₁ z, Sol z)` of `Gb`, at the unmasked
tangent and the restriction of the step's hat variable.  At `Gb = S.G'` with `BgTransport.self` it
is the step's term (`zeroTermBg_self`). -/
noncomputable def zeroTermBg (S : StepSetting d L N₁ m₁ k N ϱ)
    (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb) (Tr : BgTransport S.G' Gb N)
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    (X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1)))
    (jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ)
    (𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)))
    (m₀ : ℕ)
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (ω : ℂ → ℂ) (Y : Set (CTorus d L N₁ m₁ (k + 1))) (x₀ w : unitPts S.G' × Fin N → ℂ) (σ : ℂ)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) : ℂ :=
  -(S.β : ℂ) * ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
    if Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z) then
      rayTerm (dl3 (fun u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) =>
        evDecBg S.G' (X₁V z) m₀ (jV z) (𝒦XV z) Gb S.a₁ S.ν Tr
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ z) (Sol z)
          (blockEnergyFun Gb Hm (compWeight L S.a₁) S.ν k z) ∅ 1 0 Y (u.1, Tr.res u.2)) w)
        ω x₀ σ Θ
    else 0

open Classical in
/-- **The zero-source activity of a domain `Y` on a background generating set `Gb`, as a function of
a parameter `θ` of `Gb`** (P3 pp. 78-79): at the parameters whose datum lies in the chart
`Ξ^c_{k+1}(Gb; 1, ε)` and `‖u‖ < 2`, `u² · zeroTermBg … Y (ψ̂, ψ̂) u θ.raw`, `ψ̂ = S.hatOf m₀ ρ hp Φ`
the step's clamped hat field of the block configuration `Φ`; `0` otherwise (the zero-source family
`u² A((θ, 0), u)` of the direct terms, `zeroSourceAct`). -/
noncomputable def zeroActBg (S : StepSetting d L N₁ m₁ k N ϱ)
    (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb) (Tr : BgTransport S.G' Gb N)
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    (X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1)))
    (jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ)
    (𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)))
    (m₀ : ℕ)
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (ω : ℂ → ℂ) (ρ : ℝ) (hp : 0 < S.p₁) (eps : ℝ) (θ : physParamBg N Gb) (u : ℂ)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) : ℂ :=
  if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < 2 then
    u ^ 2 * zeroTermBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω Y (S.hatOf m₀ ρ hp Φ)
      (S.hatOf m₀ ρ hp Φ) u (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
  else 0

end Defs

section Self

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}

/-- **Instance lemma**: at the step's own set with the transport `BgTransport.self` the zero-source
term is the step's formula: the ray integrals of the third derivatives of the terms of the block
energy with the hat field `hatPsiF` (the potential part of the direct terms of
`zeroSourceActivity_common_fromTowerG_core`). -/
theorem zeroTermBg_self (S : StepSetting d L N₁ m₁ k N ϱ)
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    (X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1)))
    (jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ)
    (𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)))
    (m₀ : ℕ)
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (ω : ℂ → ℂ) (Y : Set (CTorus d L N₁ m₁ (k + 1))) (x₀ w : unitPts S.G' × Fin N → ℂ) (σ : ℂ)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) :
    zeroTermBg S S.G' (BgTransport.self S.hG') X₁V jV 𝒦XV m₀ F₁ Sol ω Y x₀ w σ Θ =
      -(S.β : ℂ) * ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        if Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z) then
          rayTerm (dl3 (evTerm
            (fun i : ParIdx S.G' (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) S.G' m₀
            (X1 S.G' m₀ (jV z) (𝒦XV z))
            (fun u s => blockEnergyFun S.G' Hm (compWeight L S.a₁) S.ν k z
              (F₁ z (extParams S.G' (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
              (Sol z (extParams S.G' (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s,
                flEdat S.G' Hm
                  (F₁ z (extParams S.G' (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
                  u.1.1 (hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ z)
                    (extParams S.G' (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
              (u.1, hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ z)
                (extParams S.G' (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))
            Y) w) ω x₀ σ Θ
        else 0 := by
  unfold zeroTermBg
  refine congrArg (fun x => -(S.β : ℂ) * x) (Finset.sum_congr rfl fun z _ => ?_)
  split_ifs
  · refine congrArg (fun Ev => rayTerm (dl3 Ev w) ω x₀ σ Θ) (funext fun u => ?_)
    show evTerm _ S.G' m₀ _ (FFmarked (X₁V z) S.a₁ S.ν S.hG' _ (F₁ z) (Sol z) _ ∅ 1 0) Y
        (u.1, u.2) = _
    rw [FFmarked_one_zero]
  · rfl

end Self

section Canon

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm ϱl ϱl' : ℝ}

/-- The preimage of the empty mask is empty. -/
theorem maskPre_empty {ϱb : ℝ} {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hG' : IsLevel Gp (k + 1)) (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb) :
    maskPre hG' Gb ∅ = ∅ := by
  classical
  ext q
  simp [maskPre]

/-- **The zero-source term recomputed on a local generating set equals the step's** (P3 pp. 78-79,
(4.46); P6 Lemma 4.1).  Let `Gl` be cube aligned and sup-separated, `Gd ≺ Gl` with the layer `k` of
`Gl` and no layer `k + 1`, the maps `F₁ z`, `Sol z` of the step and `F₁' z`, `Sol' z` of `(Gl, Gd)`
given by their specifications (the step's at the levels `(δ₀, δ₁)`, the recomputed ones at
`(δ₀', δ₁)`), and the cover data `(m₀, j z, X z, 𝒦_X z)` with region `X₁ z` containing the block
`B_{k+1}(z)`.  For a datum `D` of the step chart of radius `ε`, a domain `Y` whose
`2 M₁ L^{k+1}`-neighbourhood lies in the top layer of `Gl` and a ray inside the box of the hat
variables (`|σ| |x₀ q| < c_ψ`), the zero-source term recomputed on `Gl` with the canonical transport
at the read datum `clipRaw Gl (rawOf D)` (of radius `ε′ ≥ (2 K₁ + 2) C₁ ε`) equals the step's term at
`rawOf D`.  The hypotheses on `ε′` are smallness conditions against absolute constants. -/
theorem zeroTermBg_canon_eq (S : StepSetting d L N₁ m₁ k N ϱ)
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} (hG : IsLevel Hm k)
    {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
    {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl'}
    (hA : CubeAligned Gl m₁) (hSS : SupSep Gl m₁) (hPd : Precedes Gd Gl)
    (hdk : Gd.Ω k = Gl.Ω k) (hdtop : Gd.Ω (k + 1) = ∅)
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl - 1))
    (hagd : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl' - 1))
    {c BG : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
    (HB' : BgHyp d L (k + 1) ϱl (compWeight L S.a₁) S.ν)
    (ha₁ : 1 / 2 ≤ S.a₁) (ha₂ : S.a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    {F₁' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₁ : ∀ z (s : Dec2.DecParams (coverOf S.G')) (D : BgData S.G' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), Dec2.IsDecBg (coverOf S.G') S.G' (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₁ z (s, rawOf D) = (φ, α))
    (hF₁' : ∀ z (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₁' z (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₀' δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h0' : 0 ≤ δ₀')
    (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₀' : δ₀' ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSol : ∀ z (p : Dec2.DecParams (coverOf S.G') × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol z p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Small Hm (Sol z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2))
    (hSol' : ∀ z (p : Dec2.DecParams (coverOf Gl) × Edat Gd N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false δ₀' δ₁ p.2 →
        (Sol' z p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol' z p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol' z p).2 ∧
        Small Gd (Sol' z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (Sol' z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (Sol' z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' z p).2))
    {eps eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hεr : (2 * bgK1 d L N + 2) * xiC1 d * eps ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀a : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤ δ₀)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀')
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁c : markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    {m₀ : ℕ}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcov : ∀ z, CovSetup S.G' m₀ (jV z) (XV z) (𝒦XV z))
    (hX₁ : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV z) (𝒦XV z))
    (hzX : ∀ z, ∀ x ∈ blockSites d L N₁ m₁ (k + 1) k z, x ∈ X1 S.G' m₀ (jV z) (𝒦XV z))
    (ω : ℂ → ℂ) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYmar : ∀ x ∈ Y, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) → y ∈ Gl.Ω (k + 1))
    (x₀ w : unitPts S.G' × Fin N → ℂ) (σ : ℂ) (hσx : ∀ q, ‖σ‖ * ‖x₀ q‖ < cψ)
    {D : BgData S.G' N} (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D) :
    zeroTermBg S Gl (BgTransport.canon S.G' Gl N) X₁V jV 𝒦XV m₀ F₁' Sol' ω Y x₀ w σ
        (clipRaw Gl (rawOf D)) =
      zeroTermBg S S.G' (BgTransport.self S.hG') X₁V jV 𝒦XV m₀ F₁ Sol ω Y x₀ w σ (rawOf D) := by
  classical
  have hdat : (BgTransport.canon S.G' Gl N).dat (clipRaw Gl (rawOf D)) =
      (BgTransport.canon S.G' Gl N).dat (rawOf D) := by
    show clipRaw Gl _ = clipRaw Gl _
    rw [clipRaw_clipRaw]
  have hδ₁m : (‖(1 : ℂ)‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ := by
    rw [norm_one, norm_zero, add_zero, one_mul]
    exact hδ₁c
  unfold zeroTermBg
  refine congrArg (fun x => -(S.β : ℂ) * x) (Finset.sum_congr rfl fun z _ => ?_)
  by_cases hY : Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z)
  · simp only [hY, ↓reduceIte]
    have hXY := subset_polyDom hY
    refine rayTerm_dl3_congr_of_box ω (fun ψ hψ => ?_) hσx
    refine (evDecBg_congr_dat (X₁V z) m₀ (jV z) (𝒦XV z) S.a₁ S.ν (BgTransport.canon S.G' Gl N) _
      (F₁' z) (Sol' z) _ ∅ 1 0 Y hdat _).trans ?_
    rw [← maskPre_empty S.hG' Gl]
    exact evDecBg_canon_eq_evDec_block S.hG' hG S.hk1 hA hSS hPd hdk hdtop hN hm₁ hM hag hagm hagl
      hagd hS HB HB' ha₁ ha₂ hκ hMc hMX (hF₁ z) (hF₁' z) hF₂ hM₂ h0 h0' h1 hδ₀ hδ₀' hδ₁ (hSol z)
      (hSol' z) heps hsmall hc7 hphi hεr hsmall' hc7' hphi' hδ₀a hδ₀e hmarD' hαD' hsm _ hcψ ∅ 1 0
      hδ₁m (hcov z).hU (hcov z).hN Y
      (fun P hP hdis y hy => by
        rw [hX₁ z] at hdis
        exact hXY (Pset_subset_of_not_disjoint (hcov z).polySetup hP hdis hy))
      (Nat.le_succ k) z (fun x hx => hXY (hzX z x hx)) hYmar hD ψ hψ
  · simp only [hY, ↓reduceIte]

/-- **The zero-source activities recomputed on a local generating set equal the step's** (P3
pp. 78-79, (4.46)): the statement of `zeroTermBg_canon_eq` for the activities `zeroActBg` of the
parameter `θ_b` of `Gl` with the read datum (gate radius `ε′`) and the step's parameter `θ` with the
datum `D` (gate radius `ε₀ ≥ ε`), when the clamped hat field of radius `ρ` stays in the box:
`2 ρ ≤ c_ψ`. -/
theorem zeroActBg_canon_eq (S : StepSetting d L N₁ m₁ k N ϱ)
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} (hG : IsLevel Hm k)
    {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
    {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl'}
    (hA : CubeAligned Gl m₁) (hSS : SupSep Gl m₁) (hPd : Precedes Gd Gl)
    (hdk : Gd.Ω k = Gl.Ω k) (hdtop : Gd.Ω (k + 1) = ∅)
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl - 1))
    (hagd : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl' - 1))
    {c BG : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
    (HB' : BgHyp d L (k + 1) ϱl (compWeight L S.a₁) S.ν)
    (ha₁ : 1 / 2 ≤ S.a₁) (ha₂ : S.a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    {F₁' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₁ : ∀ z (s : Dec2.DecParams (coverOf S.G')) (D : BgData S.G' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), Dec2.IsDecBg (coverOf S.G') S.G' (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₁ z (s, rawOf D) = (φ, α))
    (hF₁' : ∀ z (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N BG κ) s D φ α → F₁' z (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₀' δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h0' : 0 ≤ δ₀')
    (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₀' : δ₀' ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSol : ∀ z (p : Dec2.DecParams (coverOf S.G') × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol z p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Small Hm (Sol z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2))
    (hSol' : ∀ z (p : Dec2.DecParams (coverOf Gl) × Edat Gd N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false δ₀' δ₁ p.2 →
        (Sol' z p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol' z p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol' z p).2 ∧
        Small Gd (Sol' z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (Sol' z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (Sol' z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' z p).2))
    {eps eps₀ eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (heps₀ : eps ≤ eps₀) (hεr : (2 * bgK1 d L N + 2) * xiC1 d * eps ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀a : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤ δ₀)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀')
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ ρ : ℝ} (hρ : 0 < ρ) (hρc : 2 * ρ ≤ cψ)
    (hδ₁c : markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (hp : 0 < S.p₁) {m₀ : ℕ}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcov : ∀ z, CovSetup S.G' m₀ (jV z) (XV z) (𝒦XV z))
    (hX₁ : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV z) (𝒦XV z))
    (hzX : ∀ z, ∀ x ∈ blockSites d L N₁ m₁ (k + 1) k z, x ∈ X1 S.G' m₀ (jV z) (𝒦XV z))
    (ω : ℂ → ℂ) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYmar : ∀ x ∈ Y, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) → y ∈ Gl.Ω (k + 1))
    {D : BgData S.G' N} (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D)
    (θ : physParam N S) (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D)
    (θb : physParamBg N Gl)
    (hθb : (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = clipRaw Gl (rawOf D))
    (u : ℂ) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    zeroActBg S Gl (BgTransport.canon S.G' Gl N) X₁V jV 𝒦XV m₀ F₁' Sol' ω ρ hp eps' θb u Y Φ =
      zeroActBg S S.G' (BgTransport.self S.hG') X₁V jV 𝒦XV m₀ F₁ Sol ω ρ hp eps₀ θ u Y Φ := by
  classical
  obtain ⟨⟨θr, hθr⟩, θs⟩ := θ
  obtain ⟨⟨θbr, hθbr⟩, θbs⟩ := θb
  simp only at hθ hθb
  subst hθ hθb
  by_cases hu : ‖u‖ < 2
  · obtain ⟨-, hD'x, -⟩ := canon_gdat_read (Gl := Gl) S.hG' HB HB' heps hsmall hc7 hεr hD
    have hgate : rawOf D ∈ XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps₀ :=
      ⟨D, Balaban.Inhabited.xiCData_mono_radius zero_le_one heps₀ hD, rfl⟩
    have hgateb : clipRaw Gl (rawOf D) ∈ XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 eps' :=
      ⟨_, hD'x, rfl⟩
    have hσx : ∀ q, ‖u‖ * ‖S.hatOf m₀ ρ hp Φ q‖ < cψ := fun q => by
      have hq := S.hatOf_mem m₀ hρ hp Φ q
      have hq0 := norm_nonneg (S.hatOf m₀ ρ hp Φ q)
      nlinarith [norm_nonneg u]
    simp only [zeroActBg, hgate, hgateb, hu, and_self, ↓reduceIte]
    rw [zeroTermBg_canon_eq S hG hA hSS hPd hdk hdtop hN hm₁ hM hag hagm hagl hagd hS HB HB' ha₁ ha₂
      hκ hMc hMX hF₁ hF₁' hF₂ hM₂ h0 h0' h1 hδ₀ hδ₀' hδ₁ hSol hSol' heps hsmall hc7 hphi hεr hsmall'
      hc7' hphi' hδ₀a hδ₀e hmarD' hαD' hsm (by linarith) hδ₁c hcov hX₁ hzX ω Y hYmar _ _ u hσx hD]
  · simp only [zeroActBg, hu, and_false, ↓reduceIte]

end Canon

end Balaban.Fluctuation
