/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassLatFan

/-!
# Lattice covariance of the local terms: the hat variable and the `ψ̂`-integral

* `localHatLift_sym_pair`: the local hat lift `cc C^{1/2}(s) ψ̂` of `𝔹 = 𝔹_{k+1}(Y⁺)` at a datum
  `Θ` is carried by the lattice symmetry `σ` to the local hat lift of `𝔹' = 𝔹_{k+1}((σ Y)⁺)` at the
  datum `σ Θ`, with the hat variable relabelled by the bijection `u` of the unit points
  (`decCovSqrt_rm_pair`; the square root is an entrywise integral, so no integrability is needed);
* `measurableEmbedding_hatRelabel`: the relabelling `ψ̂ ↦ ψ̂ ∘ (u × 1)⁻¹` is a measurable embedding;
* `localHat_integral_sym_pair`: the `ψ̂`-integral `G(Θ, w)` of the local term of `Y` and the
  `ψ̂`-integral `G'(Θ', w')` of the local term of `σ Y` agree at `Θ' = σ Θ` and transported
  parameters, for a compact set `K'` and a measure `γ'` that are the images of `K`, `γ`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Balaban.Localization.DecEquiv
  Balaban.Localization.DetDecCov Balaban.Localization.DetUnitIncidence MeasureTheory Finset Matrix

section HatPair

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp Gp₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))} {τ : Equiv.Perm (ℕ × CTorus d L N₁ m₁ (k + 1))}

omit [NeZero N₁] [NeZero L] in
/-- `(rm e M v')(e p) = (M v)(p)` for `v' = v ∘ e⁻¹`. -/
theorem rm_mulVec_apply {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (M : Matrix ι ι ℂ) (v : ι → ℂ) (p : ι) :
    (rm e M *ᵥ (fun q => v (e.symm q))) (e p) = (M *ᵥ v) p := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [rm]

/-- The unit block of `σ x` is a unit point of `𝔹'` iff the unit block of `x` is one of `𝔹`. -/
theorem unitBlock_mem_unitPts_pair {u : unitPts Gp ≃ unitPts Gp₂}
    (hu : ∀ (y : unitPts Gp) (x : CTorus d L N₁ m₁ (k + 1)),
      unitBlock (σ x) = (u y : UnitTorus d L N₁ m₁ k) ↔ unitBlock x = (y : UnitTorus d L N₁ m₁ k))
    (x : CTorus d L N₁ m₁ (k + 1)) :
    unitBlock (σ x) ∈ unitPts Gp₂ ↔ unitBlock x ∈ unitPts Gp := by
  constructor
  · intro h
    have e := (hu (u.symm ⟨unitBlock (σ x), h⟩) x).1 (by simp)
    rw [e]
    exact (u.symm ⟨unitBlock (σ x), h⟩).2
  · intro h
    have e := (hu ⟨unitBlock x, h⟩ x).2 rfl
    rw [e]
    exact (u ⟨unitBlock x, h⟩).2

/-- **The local hat lift is transported** (two-set form of `localHatLift_rot_cover`): the lift of
`𝔹'` at the datum `σ Θ`, the background `(σ φ, σ α)` and the parameters `s'` with `s' ∘ τ = s`, of
the hat variable `ψ̂ ∘ (u × 1)⁻¹`, is the transport `x ↦ (lift of 𝔹 at Θ of ψ̂)(σ⁻¹ x)`. -/
theorem localHatLift_sym_pair (S : LatSymm Gp Gp₂ σ) (hU : UnitBlockPres σ)
    (hidx : ∀ q, τ q ∈ cubeIdx Gp₂ ↔ q ∈ cubeIdx Gp)
    (hchi : ∀ q x, chi Gp₂ (τ q) (σ x) = chi Gp q x)
    (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (hqset : ∀ q q', τ q' ∈ Qset Gp₂ (τ q) ↔ q' ∈ Qset Gp q)
    {u : unitPts Gp ≃ unitPts Gp₂}
    (hu : ∀ (y : unitPts Gp) (x : CTorus d L N₁ m₁ (k + 1)),
      unitBlock (σ x) = (u y : UnitTorus d L N₁ m₁ k) ↔ unitBlock x = (y : UnitTorus d L N₁ m₁ k))
    (a : ℕ → ℝ) (a₁ ν : ℝ) {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hss : ∀ P, s' (τ P) = s P) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N)
    (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ) (cc : ℂ) (ψ : unitPts Gp × Fin N → ℝ) :
    (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts Gp₂ then
        (cc • (decCovSqrt Gp₂ a a₁ ν (S.mul α) s' (barField Gp₂ (symRaw σ Θ).1 (S.fld φ))
          (unitQ Gp₂) (unitP Gp₂) *ᵥ
            (fun r => ((ψ ((u.prodCongr (Equiv.refl (Fin N))).symm r)) : ℂ))))
          (⟨unitBlock x, h⟩, i)
      else 0) =
    symSite σ (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts Gp then
        (cc • (decCovSqrt Gp a a₁ ν α s (barField Gp Θ.1 φ) (unitQ Gp) (unitP Gp) *ᵥ
          (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
      else 0) := by
  classical
  have hbar : barField Gp₂ (symRaw σ Θ).1 (S.fld φ) = symSite σ (barField Gp Θ.1 φ) := by
    funext y i
    obtain ⟨x, rfl⟩ := σ.surjective y
    show barField Gp₂ (fun z => Θ.1 (σ.symm z)) (S.fld φ) (σ x) i =
      barField Gp Θ.1 φ (σ.symm (σ x)) i
    rw [barField_sym_raw_pair S, Equiv.symm_apply_apply]
  rw [hbar, decCovSqrt_rm_pair S hU hidx hchi hbox hqset hu a a₁ ν α hss]
  funext y i
  obtain ⟨x, rfl⟩ := σ.surjective y
  simp only [symSite, Equiv.symm_apply_apply]
  by_cases h : unitBlock x ∈ unitPts Gp
  · have h' : unitBlock (σ x) ∈ unitPts Gp₂ := (unitBlock_mem_unitPts_pair hu x).2 h
    have hux : (⟨unitBlock (σ x), h'⟩ : unitPts Gp₂) = u ⟨unitBlock x, h⟩ :=
      Subtype.ext ((hu ⟨unitBlock x, h⟩ x).2 rfl)
    simp only [h, h', ↓reduceDIte, Pi.smul_apply, smul_eq_mul]
    rw [hux]
    congr 1
    have := rm_mulVec_apply (u.prodCongr (Equiv.refl (Fin N)))
      (decCovSqrt Gp a a₁ ν α s (barField Gp Θ.1 φ) (unitQ Gp) (unitP Gp))
      (fun r => (ψ r : ℂ)) (⟨unitBlock x, h⟩, i)
    simpa using this
  · have h' : unitBlock (σ x) ∉ unitPts Gp₂ := fun h' => h ((unitBlock_mem_unitPts_pair hu x).1 h')
    simp [h, h']

/-- The relabelling of the hat variables by a bijection of the unit points is a measurable
embedding (a homeomorphism). -/
theorem measurableEmbedding_hatRelabel {I I' : Type*} [Fintype I] [Fintype I'] (u : I ≃ I') :
    MeasurableEmbedding (fun (ψ : I × Fin N → ℝ) (r : I' × Fin N) =>
      ψ ((u.prodCongr (Equiv.refl (Fin N))).symm r)) := by
  let e : (I × Fin N → ℝ) ≃ₜ (I' × Fin N → ℝ) :=
    { toFun := fun ψ r => ψ ((u.prodCongr (Equiv.refl (Fin N))).symm r)
      invFun := fun ψ r => ψ ((u.prodCongr (Equiv.refl (Fin N))) r)
      left_inv := fun ψ => by
        funext r
        exact congrArg ψ ((u.prodCongr (Equiv.refl (Fin N))).symm_apply_apply r)
      right_inv := fun ψ => by
        funext r
        exact congrArg ψ ((u.prodCongr (Equiv.refl (Fin N))).apply_symm_apply r)
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact e.measurableEmbedding

end HatPair

section HatIntegralPair

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp Gp₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm Hm₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν Kc Cx : ℝ} {ι ι' : Type*} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable {τ τb : Equiv.Perm (ℕ × CTorus d L N₁ m₁ (k + 1))}

/-- **The `ψ̂`-integral of a local term is transported between two generating sets** (two-set form
of `localHat_integral_rot_cover`).  Let `G(Θ, w)` be the `ψ̂`-integral over `K` (measure `γ`) of the
functional `Φ` of the decoupled objects of `𝔹` at the parameters `σ w`, and `G'(Θ', w')` the
`ψ̂`-integral over `K'` (measure `γ'`) of `Φ'` of the decoupled objects of `𝔹'` at the parameters
`σ' w'`.  If `K'`, `γ'` are the images of `K`, `γ` under the relabelling `ψ̂ ↦ ψ̂ ∘ (u × 1)⁻¹` of the
unit points, `Φ'` is the transport of `Φ` on the realizable triples, and the parameters correspond
(`σ' w' ∘ τ = σ w`), then `G'(σ Θ, w') = G(Θ, w)` at the data `Θ` of the chart. -/
theorem localHat_integral_sym_pair (hk1 : 1 ≤ k) (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sc : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (Sc₂ : Dec2.CoverBase (coverOf Gp₂) Gp₂ (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hPmp : Precedes Hm Gp) (hHm : Hm.Ω (k + 1) = ∅) (hPmp₂ : Precedes Hm₂ Gp₂)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {F₁' : Dec2.DecParams (coverOf Gp₂) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp₂.Ω 1 × Fin N → ℂ) × (Gp₂.Ω 1 → ℂ)}
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf Gp₂)) (D : BgData Gp₂ N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp₂ (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp₂.Ω 1 × Fin N → ℂ)
        (α : Gp₂.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp₂) Gp₂ (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
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
    {Sol' : Dec2.DecParams (coverOf Gp₂) × Edat Hm₂ N → (Hm₂.Ω 1 × Fin N → ℂ) × (Hm₂.Ω 1 → ℂ)}
    (hSol' : ∀ p : Dec2.DecParams (coverOf Gp₂) × Edat Hm₂ N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm₂ N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi Hm₂ (Dec2.decG (coverOf Gp₂) Hm₂ (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm₂ (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf Gp₂) Hm₂ (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm₂ (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small Hm₂ (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm₂ (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm₂ (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm₂.Ω 1 → ℂ, Small Hm₂ δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp₂) Hm₂ (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm₂ (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {X₁f X₁f₂ : Finset (CTorus d L N₁ m₁ (k + 1))}
    {σp : (ι → ℂ) → Dec2.DecParams (coverOf Gp)} {σp' : (ι' → ℂ) → Dec2.DecParams (coverOf Gp₂)}
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σp w P‖ < Real.exp κ)
    (hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁f → σp w ⟨P, hP⟩ = 1)
    (hσ1' : ∀ w' (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gp₂).cubeIdx),
      P ∉ (coverOf Gp₂).parCubes X₁f₂ → σp' w' ⟨P, hP⟩ = 1)
    (S : LatSymm Gp Gp₂ σ) (Sm : LatSymm Hm Hm₂ σ) (hU : UnitBlockPres σ)
    (hidx : ∀ q, τ q ∈ (coverOf Gp₂).cubeIdx ↔ q ∈ (coverOf Gp).cubeIdx)
    (hchi : ∀ q x, (coverOf Gp₂).chi (τ q) (σ x) = (coverOf Gp).chi q x)
    (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (hqset : ∀ q q', τ q' ∈ (coverOf Gp₂).Qset (τ q) ↔ q' ∈ (coverOf Gp).Qset q)
    (hbidx : ∀ q, τb q ∈ blockIdx Gp₂ ↔ q ∈ blockIdx Gp) (hblayer : ∀ q, (τb q).1 = q.1)
    (hbump : ∀ q x, Background.bump (τb q).1 (τb q).2 (σ x) = Background.bump q.1 q.2 x)
    (hbbase : ∀ q ∈ blockIdx Gp, jBlock d L (N₁ * L ^ m₁) (k + 1) q.1 (σ.symm (τb q).2) =
      jBlock d L (N₁ * L ^ m₁) (k + 1) q.1 q.2)
    {u : unitPts Gp ≃ unitPts Gp₂}
    (hu : ∀ (y : unitPts Gp) (x : CTorus d L N₁ m₁ (k + 1)),
      unitBlock (σ x) = (u y : UnitTorus d L N₁ m₁ k) ↔ unitBlock x = (y : UnitTorus d L N₁ m₁ k))
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : ((Gp₂.Ω 1 × Fin N → ℂ) × (Gp₂.Ω 1 → ℂ)) → (Hm₂.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) δφ u,
      (bg, δφ, u) ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ →
      ((S.fld bg.1, S.mul bg.2), Sm.fld δφ, symU σ u) ∈
        FlRealLC Gp₂ Hm₂ a₁ ν BG κ eps X₁f₂ BG₂ δ₁ →
      Φ' (S.fld bg.1, S.mul bg.2) (Sm.fld δφ) (symU σ u) = Φ bg δφ u)
    {γ : Measure (unitPts Gp × Fin N → ℝ)} {K : Set (unitPts Gp × Fin N → ℝ)}
    {γ' : Measure (unitPts Gp₂ × Fin N → ℝ)} {K' : Set (unitPts Gp₂ × Fin N → ℝ)}
    (hKc : IsCompact K) (hKb : ∀ ψ ∈ K, ∀ r, |ψ r| ≤ cψ)
    (hKu : ∀ ψ : unitPts Gp × Fin N → ℝ,
      (fun r : unitPts Gp₂ × Fin N => ψ ((u.prodCongr (Equiv.refl (Fin N))).symm r)) ∈ K' ↔
        ψ ∈ K)
    (hγu : Measure.map (fun (ψ : unitPts Gp × Fin N → ℝ) (r : unitPts Gp₂ × Fin N) =>
      ψ ((u.prodCongr (Equiv.refl (Fin N))).symm r)) γ = γ')
    (Gf : RawData d L (N₁ * L ^ m₁) (k + 1) N → (ι → ℂ) → ℂ)
    (hGf : ∀ (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ), Gf Θ w =
      ∫ ψ in K,
        Φ (F₁ (σp w, Θ))
          (Sol (σp w, flEdat Gp Hm (F₁ (σp w, Θ)) Θ.1
            (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp then
                (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σp w, Θ)).2
                  (Dec2.extS (coverOf Gp) (σp w)) (barField Gp Θ.1 (F₁ (σp w, Θ)).1)
                  (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0))).1
          (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp then
                (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σp w, Θ)).2
                  (Dec2.extS (coverOf Gp) (σp w)) (barField Gp Θ.1 (F₁ (σp w, Θ)).1)
                  (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0) ∂γ)
    (Gf' : RawData d L (N₁ * L ^ m₁) (k + 1) N → (ι' → ℂ) → ℂ)
    (hGf' : ∀ (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι' → ℂ), Gf' Θ w =
      ∫ ψ in K',
        Φ' (F₁' (σp' w, Θ))
          (Sol' (σp' w, flEdat Gp₂ Hm₂ (F₁' (σp' w, Θ)) Θ.1
            (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp₂ then
                (cc • (decCovSqrt Gp₂ (compWeight L a₁) a₁ ν (F₁' (σp' w, Θ)).2
                  (Dec2.extS (coverOf Gp₂) (σp' w)) (barField Gp₂ Θ.1 (F₁' (σp' w, Θ)).1)
                  (unitQ Gp₂) (unitP Gp₂) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0))).1
          (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp₂ then
                (cc • (decCovSqrt Gp₂ (compWeight L a₁) a₁ ν (F₁' (σp' w, Θ)).2
                  (Dec2.extS (coverOf Gp₂) (σp' w)) (barField Gp₂ Θ.1 (F₁' (σp' w, Θ)).1)
                  (unitQ Gp₂) (unitP Gp₂) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0) ∂γ')
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) {w : ι → ℂ}
    (hw : w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)) {w' : ι' → ℂ}
    (hww : ∀ P, Dec2.extS (coverOf Gp₂) (σp' w') (τ P) = Dec2.extS (coverOf Gp) (σp w) P) :
    Gf' (symRaw σ (rawOf D)) w' = Gf (rawOf D) w := by
  classical
  have hs : ∀ P, ‖σp w P‖ < Real.exp κ := hσκ w hw
  have hd0 : 0 < d := by have := HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * eps := by positivity
  obtain ⟨φ, α, hI, -, -⟩ := coverBg_exists hS Sc HBp hκ.le hM heps hsmall hc7 hs hD
  have hUd : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC HBp hδ0
      (hc7.trans ((c7_le_bgC1 d L N BG κ).trans (bgC1_le_bgC0 d L N hd0))) hc7
      (xiCData_inDomainC HBp hsmall hD)
  have hFe : F₁ (σp w, rawOf D) = (φ, α) :=
    hF₁ (σp w) D hs hUd φ α ⟨hI.small, hI.fixed, hI.field⟩
  have hFr : F₁' (σp' w', symRaw σ (rawOf D)) = (S.fld φ, S.mul α) := by
    rw [← rawOf_sym_pair S D, F₁_sym_cover_pair hS Sc HBp hκ hM heps hsmall hc7 hF₁ hF₁' S hidx
      hchi hbox hqset hbidx hblayer hbump hbbase hww hs hD, hFe]
  let lift : (unitPts Gp × Fin N → ℝ) → CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ :=
    fun ψ' (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts Gp then
        (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σp w, rawOf D)).2
          (Dec2.extS (coverOf Gp) (σp w)) (barField Gp D.Ψ (F₁ (σp w, rawOf D)).1)
          (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ' r : ℂ)))) (⟨unitBlock x, h⟩, i)
      else 0
  let Hf : (unitPts Gp × Fin N → ℝ) → ℂ := fun ψ' =>
    Φ (F₁ (σp w, rawOf D)) (Sol (σp w, flEdat Gp Hm (F₁ (σp w, rawOf D)) D.Ψ (lift ψ'))).1
      (rawOf D, lift ψ')
  let e : (unitPts Gp × Fin N → ℝ) → (unitPts Gp₂ × Fin N → ℝ) :=
    fun ψ r => ψ ((u.prodCongr (Equiv.refl (Fin N))).symm r)
  let lift' : (unitPts Gp₂ × Fin N → ℝ) → CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ :=
    fun ψ' (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts Gp₂ then
        (cc • (decCovSqrt Gp₂ (compWeight L a₁) a₁ ν (F₁' (σp' w', symRaw σ (rawOf D))).2
          (Dec2.extS (coverOf Gp₂) (σp' w'))
          (barField Gp₂ (symRaw σ (rawOf D)).1 (F₁' (σp' w', symRaw σ (rawOf D))).1)
          (unitQ Gp₂) (unitP Gp₂) *ᵥ (fun r => (ψ' r : ℂ)))) (⟨unitBlock x, h⟩, i)
      else 0
  let Hf' : (unitPts Gp₂ × Fin N → ℝ) → ℂ := fun ψ' =>
    Φ' (F₁' (σp' w', symRaw σ (rawOf D)))
      (Sol' (σp' w', flEdat Gp₂ Hm₂ (F₁' (σp' w', symRaw σ (rawOf D)))
        (symRaw σ (rawOf D)).1 (lift' ψ'))).1 (symRaw σ (rawOf D), lift' ψ')
  have e2 : Gf (rawOf D) w = ∫ ψ in K, Hf ψ ∂γ := hGf _ _
  have e1 : Gf' (symRaw σ (rawOf D)) w' = ∫ ψ in K', Hf' ψ ∂γ' := hGf' _ _
  have hlift : ∀ ψ, lift' (e ψ) = symSite σ (lift ψ) := by
    intro ψ
    have h := localHatLift_sym_pair S hU (fun q => hidx q) (fun q x => hchi q x) hbox
      (fun q q' => hqset q q') hu (compWeight L a₁) a₁ ν (hww) (rawOf D) φ α cc ψ
    simp only [lift', lift, hFr, hFe]
    exact h
  have hpt : ∀ ψ ∈ K, Hf' (e ψ) = Hf ψ := by
    intro ψ hψ
    have hψ' : lift ψ ∈ FlBallLC Hm δ₁ := by
      refine localHatLift_mem_flBallLC_of_spec hHm hk1 ha₁ ha₂ hS Sc HBp hκ.le hM hMX hCx hF₁
        heps hsmall hc7 hphi hmarD hαD hsm hs hD cc hcψ hδ₁0 hδ₁
        (ψh := fun r => (ψ r : ℂ)) fun r => ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hKb ψ hψ r
    show Φ' (F₁' (σp' w', symRaw σ (rawOf D)))
      (Sol' (σp' w', flEdat Gp₂ Hm₂ (F₁' (σp' w', symRaw σ (rawOf D)))
        (symRaw σ (rawOf D)).1 (lift' (e ψ)))).1 (symRaw σ (rawOf D), lift' (e ψ)) = Hf ψ
    rw [hlift ψ]
    exact fanLC_sym_cover_pair hS Sc Sc₂ HBp hκ hM heps hsmall hc7 hphi hδ₁0 hPmp hPmp₂ hF₁ hF₁'
      hSol hSol' S Sm hidx hchi hbox hqset hbidx hblayer hbump hbbase hΦ hww hs (hσ1 w) (hσ1' w')
      hD hψ'
  rw [e1, e2, ← hγu]
  have hemb := measurableEmbedding_hatRelabel (N := N) u
  have h3 := hemb.setIntegral_map (μ := γ) Hf' K'
  have hpre : (fun (ψ : unitPts Gp × Fin N → ℝ) (r : unitPts Gp₂ × Fin N) =>
      ψ ((u.prodCongr (Equiv.refl (Fin N))).symm r)) ⁻¹' K' = K := Set.ext fun ψ => hKu ψ
  rw [hpre] at h3
  rw [h3]
  exact setIntegral_congr_fun hKc.isClosed.measurableSet fun ψ hψ => hpt ψ hψ

end HatIntegralPair

end Balaban.Localization
