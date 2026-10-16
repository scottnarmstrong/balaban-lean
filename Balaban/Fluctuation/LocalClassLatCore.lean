/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.LatPairCov
public import Balaban.Fluctuation.LocalClassRot
public import Balaban.Fluctuation.InteractionSymmLat

/-!
# Lattice covariance of the local terms: the decoupled objects between two generating sets

For the local terms of the polymers `Y` and `σ Y` the decoupled objects live on two different
generating sets `𝔹 = 𝔹_{k+1}(Y⁺)` and `𝔹' = 𝔹_{k+1}((σ Y)⁺)`.  For lattice symmetries
`LatSymm 𝔹 𝔹' σ` (and between the other generating sets of the two terms) and the transport of the
covers and the blocks (`LatPairCover.lean`, `LatPairBg.lean`):

* `xiCData_sym_pair`: the chart `Ξ^c_n` is carried to the chart of the image set;
* `composeField_sym_pair`, `composeData_sym_pair`, `d1Triple_sym_pair`: the compositions;
* `flEdat_sym_pair`: the data of the fluctuation problem;
* `F₁_sym_cover_pair`: the decoupled background map (cover form, Theorem I-4b);
* `Sol_sym_pair`: the fluctuation solution map (Theorem I-4a, mode P), on strict data;
* `clipRaw_act_pair`: the cut-off of a pair of fields.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Balaban.Localization.DecEquiv Finset Matrix

section Data

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
variable {g : Equiv.Perm (CTorus d L N₁ m₁ K)}

/-- **`Ξ^c_n(𝔹; σ, ε)` is carried to `Ξ^c_n(𝔹'; σ, ε)` by a lattice symmetry `𝔹 → 𝔹'`.** -/
theorem xiCData_sym_pair (S : LatSymm G G' g) {n : ℕ} {σ ε : ℝ} {D : BgData G N}
    (h : XiCData G a ν n σ ε D) : XiCData G' a ν n σ ε (S.sym D) := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hX, hR⟩ := h
  exact ⟨fun y => Ψ₀ (g.symm y), h₀, fun y => Ψ'' (g.symm y), fun y => h'' (g.symm y),
    xiC_sym S a ν hX, realizesC_sym S hR⟩

theorem rawOf_sym_pair (S : LatSymm G G' g) (D : BgData G N) :
    rawOf (S.sym D) = symRaw g (rawOf D) := rfl

end Data

section Compose

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
variable {G G₂ : GeneratingSet d L N₀ k ϱ} {H H₂ : GeneratingSet d L N₀ k ϱ'}
variable {σ : Equiv.Perm (Torus d (N₀ * L ^ k))}

/-- The block mean is transported by a lattice symmetry preserving the blocks of the scale. -/
theorem blockMean_sym_pair (S : LatSymm G G₂ σ) {n : ℕ} (h1 : 1 ≤ n) (hk : n ≤ k)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n) (w : Torus d (N₀ * L ^ k) → ℂ) :
    blockMean G₂ n (fun y => w (σ.symm y)) (σ x) = blockMean G n w x := by
  unfold blockMean
  congr 1
  refine (Finset.sum_equiv σ (fun y => ?_) (fun y _ => ?_)).symm
  · rw [S.blk_iff h1 hk ⟨x, hx⟩ x (σ y)]; simp
  · simp

theorem svec_sym_pair (T : LatSymm H H₂ σ) (φ : H.Ω 1 × Fin N → ℂ) (i : Fin N) :
    (fun y => svec H₂ (T.fld φ) y i) = fun y => svec H φ (σ.symm y) i := by
  funext y
  obtain ⟨z, rfl⟩ := σ.surjective y
  rw [T.svec_sym φ z i, Equiv.symm_apply_apply]

theorem barField_sym_raw_pair (T : LatSymm H H₂ σ) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (φ : H.Ω 1 × Fin N → ℂ) (w : Torus d (N₀ * L ^ k)) (i : Fin N) :
    barField H₂ (fun y => Ψ (σ.symm y)) (T.fld φ) (σ w) i = barField H Ψ φ w i := by
  by_cases hw : w ∈ H.Ω 1
  · have h' : σ w ∈ H₂.Ω 1 := (T.mem_Ω1 w).2 hw
    have := T.fld_apply φ ⟨w, hw⟩ i
    have e : (T.Ω1Equiv ⟨w, hw⟩ : H₂.Ω 1) = ⟨σ w, h'⟩ := rfl
    rw [e] at this
    simp only [barField, hw, h', ↓reduceDIte]
    exact this
  · have h' : σ w ∉ H₂.Ω 1 := fun h => hw ((T.mem_Ω1 w).1 h)
    simp [barField, hw, h']

/-- **The composed field is transported by a lattice symmetry between two pairs of generating
sets** (`Precedes G H`): `ψ(σ 𝔹_j, σ 𝔹'_k; σ Ψ', σ φ') = σ ψ(𝔹_j, 𝔹'_k; Ψ', φ')`. -/
theorem composeField_sym_pair (S : LatSymm G G₂ σ) (T : LatSymm H H₂ σ) (hGH : Precedes G H)
    (a : ℕ → ℝ) (φ : H.Ω 1 × Fin N → ℂ) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    composeField G₂ H₂ a (T.fld φ) (fun y => Ψ (σ.symm y)) (σ x) i =
      composeField G H a φ Ψ x i := by
  classical
  unfold composeField
  by_cases hx : x ∈ G.Ω 1
  · have hx' : σ x ∈ G₂.Ω 1 := (S.mem_Ω1 x).2 hx
    have hxH : x ∈ H.Ω 1 := hGH.mem_Ω1 hx
    obtain ⟨n1, nk, hn⟩ := G.layerIndex_spec hx
    obtain ⟨p1, pk, hp⟩ := H.layerIndex_spec hxH
    simp only [hx, hx', ↓reduceIte, S.layerIndex_eq, T.layerIndex_eq, svec_sym_pair T,
      Equiv.symm_apply_apply]
    have e1 := blockMean_sym_pair S n1 nk hn (fun y => svec H φ y i)
    have e2 := blockMean_sym_pair T p1 pk hp (fun y => svec H φ y i)
    rw [e1, e2]
  · have hx' : σ x ∉ G₂.Ω 1 := fun h => hx ((S.mem_Ω1 x).1 h)
    by_cases hc : x ∈ collar G
    · have hc' : σ x ∈ collar G₂ := (S.mem_collar x).2 hc
      simp only [hx, hx', hc, hc', ↓reduceIte]
      exact barField_sym_raw_pair T Ψ φ x i
    · have hc' : σ x ∉ collar G₂ := fun h => hc ((S.mem_collar x).1 h)
      simp [hx, hx', hc, hc']

/-- The composed datum is transported. -/
theorem composeData_sym_pair (S : LatSymm G G₂ σ) (T : LatSymm H H₂ σ) (h : Precedes G H)
    (h₂ : Precedes G₂ H₂) (a : ℕ → ℝ) (φ : H.Ω 1 × Fin N → ℂ) (D : BgData H N) :
    composeData h₂ a (T.fld φ) (T.sym D) = S.sym (composeData h a φ D) := by
  classical
  refine Background.BgData.ext' ?_ ?_
  · funext y i
    obtain ⟨x, rfl⟩ := σ.surjective y
    show composeField G₂ H₂ a (T.fld φ) (fun y => D.Ψ (σ.symm y)) (σ x) i =
      composeField G H a φ D.Ψ (σ.symm (σ x)) i
    rw [composeField_sym_pair S T h, Equiv.symm_apply_apply]
  · funext y i
    obtain ⟨x, rfl⟩ := σ.surjective y
    show (if σ x ∈ G₂.Ω 1 then D.h (σ.symm (σ x)) i else 0) =
      (if σ.symm (σ x) ∈ G.Ω 1 then D.h (σ.symm (σ x)) i else 0)
    simp only [Equiv.symm_apply_apply, S.mem_Ω1]

end Compose

section Triple

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp Gp₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk Gk₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj Gj₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm Hm₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}

/-- **The raw datum of `𝔹_k(X)` composed from a triple is transported.** -/
theorem d1Triple_sym_pair (Sp : LatSymm Gp Gp₂ σ) (Sk : LatSymm Gk Gk₂ σ)
    (Sm : LatSymm Hm Hm₂ σ) (hP : Precedes Gk Gp) (hPm : Precedes Gk Hm) (a : ℕ → ℝ)
    (φ : Gp.Ω 1 × Fin N → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ)
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) :
    d1Triple Gp₂ Gk₂ Hm₂ a (Sp.fld φ) (Sm.fld δφ) (symU σ u) =
      symRaw σ (d1Triple Gp Gk Hm a φ δφ u) := by
  classical
  refine Prod.ext ?_ ?_
  · funext y i
    obtain ⟨x, rfl⟩ := σ.surjective y
    show composeField Gk₂ Gp₂ a (Sp.fld φ) (fun z => u.1.1 (σ.symm z)) (σ x) i +
      composeField Gk₂ Hm₂ a (Sm.fld δφ) (fun z => u.2 (σ.symm z)) (σ x) i =
        composeField Gk Gp a φ u.1.1 (σ.symm (σ x)) i +
          composeField Gk Hm a δφ u.2 (σ.symm (σ x)) i
    rw [composeField_sym_pair Sk Sp hP, composeField_sym_pair Sk Sm hPm, Equiv.symm_apply_apply]
  · funext y i
    obtain ⟨x, rfl⟩ := σ.surjective y
    show (if σ x ∈ Gk₂.Ω 1 then u.1.2 (σ.symm (σ x)) i else 0) =
      (if σ.symm (σ x) ∈ Gk.Ω 1 then u.1.2 (σ.symm (σ x)) i else 0)
    simp only [Equiv.symm_apply_apply, Sk.mem_Ω1]

/-- The multiplier of `𝔹_{k+1}` restricted to `H⁻` is transported. -/
theorem flAlpha_sym_pair (Sp : LatSymm Gp Gp₂ σ) (Sm : LatSymm Hm Hm₂ σ) (α : Gp.Ω 1 → ℂ) :
    flAlpha Gp₂ Hm₂ (Sp.mul α) = Sm.mul (flAlpha Gp Hm α) := by
  classical
  funext y
  obtain ⟨x, rfl⟩ := Sm.Ω1Equiv.surjective y
  rw [LatSymm.mul_apply]
  unfold flAlpha
  simp only [LatSymm.coe_Ω1Equiv]
  by_cases hx : (x : CTorus d L N₁ m₁ (k + 1)) ∈ Gp.Ω 1
  · have hx' : σ (x : CTorus d L N₁ m₁ (k + 1)) ∈ Gp₂.Ω 1 := (Sp.mem_Ω1 _).2 hx
    simp only [hx, hx', ↓reduceDIte]
    have e : (⟨σ (x : CTorus d L N₁ m₁ (k + 1)), hx'⟩ : Gp₂.Ω 1) = Sp.Ω1Equiv ⟨x, hx⟩ := rfl
    rw [e, LatSymm.mul_apply]
  · have hx' : σ (x : CTorus d L N₁ m₁ (k + 1)) ∉ Gp₂.Ω 1 := fun h => hx ((Sp.mem_Ω1 _).1 h)
    simp [hx, hx']

/-- **The data of the fluctuation problem are transported.** -/
theorem flEdat_sym_pair (Sp : LatSymm Gp Gp₂ σ) (Sm : LatSymm Hm Hm₂ σ)
    (φα : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) (Ψ ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    flEdat Gp₂ Hm₂ (Sp.fld φα.1, Sp.mul φα.2) (symSite σ Ψ) (symSite σ ψ') =
      (symSite σ (flEdat Gp Hm φα Ψ ψ').1, Sm.mul (flEdat Gp Hm φα Ψ ψ').2.1,
        symSite σ (flEdat Gp Hm φα Ψ ψ').2.2.1, Sm.fld (flEdat Gp Hm φα Ψ ψ').2.2.2) := by
  unfold flEdat
  refine Prod.ext ?_ (Prod.ext (flAlpha_sym_pair Sp Sm φα.2) (Prod.ext rfl ?_))
  · funext y i
    obtain ⟨x, rfl⟩ := σ.surjective y
    show barField Gp₂ (fun z => Ψ (σ.symm z)) (Sp.fld φα.1) (σ x) i =
      barField Gp Ψ φα.1 (σ.symm (σ x)) i
    rw [barField_sym_raw_pair Sp, Equiv.symm_apply_apply]
  · funext p
    simp [LatSymm.fld]

end Triple

section Bg

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp Gp₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm Hm₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν Kc Cx : ℝ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable {τ τb : Equiv.Perm (ℕ × CTorus d L N₁ m₁ (k + 1))}

omit [NeZero N₁] [NeZero L] in
/-- Transported parameters with `s' ∘ τ = s` keep the bound `|s_P| < e^κ`. -/
theorem norm_lt_of_extS_pair {C C' : DecCover d L N₁ m₁ (k + 1)}
    (hidx : ∀ q, τ q ∈ C'.cubeIdx ↔ q ∈ C.cubeIdx) {s : Dec2.DecParams C}
    {s' : Dec2.DecParams C'} (hss : ∀ P, Dec2.extS C' s' (τ P) = Dec2.extS C s P) {κ : ℝ}
    (hs : ∀ P, ‖s P‖ < Real.exp κ) : ∀ P, ‖s' P‖ < Real.exp κ := by
  classical
  intro P'
  have hP : τ.symm P'.1 ∈ C.cubeIdx := (hidx _).1 (by simp)
  have h := hss (τ.symm P'.1)
  rw [Equiv.apply_symm_apply] at h
  unfold Dec2.extS at h
  simp only [P'.2, hP, ↓reduceDIte] at h
  rw [h]
  exact hs _

/-- **The decoupled background map is transported between two generating sets** (cover form of
Theorem I-4b): `F₁' (s', σ Θ) = (σ φ_{k+1}(s), σ α_{k+1}(s))` for `s' ∘ τ = s` and `Θ` a datum of the
chart `Ξ^c(𝔹; 1, ε')`. -/
theorem F₁_sym_cover_pair {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sc : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
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
    (S : LatSymm Gp Gp₂ σ)
    (hidx : ∀ q, τ q ∈ (coverOf Gp₂).cubeIdx ↔ q ∈ (coverOf Gp).cubeIdx)
    (hchi : ∀ q x, (coverOf Gp₂).chi (τ q) (σ x) = (coverOf Gp).chi q x)
    (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (hqset : ∀ q q', τ q' ∈ (coverOf Gp₂).Qset (τ q) ↔ q' ∈ (coverOf Gp).Qset q)
    (hbidx : ∀ q, τb q ∈ blockIdx Gp₂ ↔ q ∈ blockIdx Gp) (hblayer : ∀ q, (τb q).1 = q.1)
    (hbump : ∀ q x, Background.bump (τb q).1 (τb q).2 (σ x) = Background.bump q.1 q.2 x)
    (hbbase : ∀ q ∈ blockIdx Gp, jBlock d L (N₁ * L ^ m₁) (k + 1) q.1 (σ.symm (τb q).2) =
      jBlock d L (N₁ * L ^ m₁) (k + 1) q.1 q.2)
    {s : Dec2.DecParams (coverOf Gp)} {s' : Dec2.DecParams (coverOf Gp₂)}
    (hss : ∀ P, Dec2.extS (coverOf Gp₂) s' (τ P) = Dec2.extS (coverOf Gp) s P)
    (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) :
    F₁' (s', rawOf (S.sym D)) = (S.fld (F₁ (s, rawOf D)).1, S.mul (F₁ (s, rawOf D)).2) := by
  have hd0 : 0 < d := by have := HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC HBp hδ0
      (hc7.trans ((c7_le_bgC1 d L N BG κ).trans (bgC1_le_bgC0 d L N hd0))) hc7
      (xiCData_inDomainC HBp hsmall hD)
  obtain ⟨φ, α, hI, -, -⟩ := coverBg_exists hS Sc HBp hκ.le hM heps hsmall hc7 hs hD
  have hFe : F₁ (s, rawOf D) = (φ, α) := hF₁ s D hs hU φ α ⟨hI.small, hI.fixed, hI.field⟩
  rw [hFe]
  have hI' := (isDecBg2_sym_iff_pair S hidx hchi hbox hqset hbidx hblayer hbump hbbase hss
    (rho4 d L N BG κ) D φ α).2 ⟨hI.small, hI.fixed, hI.field⟩
  exact hF₁' s' (S.sym D) (norm_lt_of_extS_pair hidx hss hs) (inUnionDomainC_sym S hU) _ _ hI'

/-- **The fluctuation solution map is transported between two pairs** on strict data. -/
theorem Sol_sym_pair {BG BG₂ κ eps δ₁ : ℝ}
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
    (Sm : LatSymm Hm Hm₂ σ)
    (hidx : ∀ q, τ q ∈ (coverOf Gp₂).cubeIdx ↔ q ∈ (coverOf Gp).cubeIdx)
    (hchi : ∀ q x, (coverOf Gp₂).chi (τ q) (σ x) = (coverOf Gp).chi q x)
    (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (hqset : ∀ q q', τ q' ∈ (coverOf Gp₂).Qset (τ q) ↔ q' ∈ (coverOf Gp).Qset q)
    {s : Dec2.DecParams (coverOf Gp)} {s' : Dec2.DecParams (coverOf Gp₂)}
    (hss : ∀ P, Dec2.extS (coverOf Gp₂) s' (τ P) = Dec2.extS (coverOf Gp) s P)
    (hs : ∀ P, ‖s P‖ < Real.exp κ)
    {φ₀ δΨ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {α₀ : Hm.Ω 1 → ℂ} {f₁ : Hm.Ω 1 × Fin N → ℂ}
    (he : StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ (φ₀, α₀, δΨ, f₁))
    (he' : StrictDataM Hm₂ N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁
      (symSite σ φ₀, Sm.mul α₀, symSite σ δΨ, Sm.fld f₁)) :
    Sol' (s', (symSite σ φ₀, Sm.mul α₀, symSite σ δΨ, Sm.fld f₁)) =
      (Sm.fld (Sol (s, (φ₀, α₀, δΨ, f₁))).1, Sm.mul (Sol (s, (φ₀, α₀, δΨ, f₁))).2) := by
  have hs' := norm_lt_of_extS_pair hidx hss hs
  obtain ⟨hfld, hfix, hs6, -, -, -⟩ := hSol (s, (φ₀, α₀, δΨ, f₁)) hs he
  obtain ⟨hfld', hfix', hs6', -, -, huniq'⟩ :=
    hSol' (s', (symSite σ φ₀, Sm.mul α₀, symSite σ δΨ, Sm.fld f₁)) hs' he'
  simp only at hfld hfix hfld' hfix' huniq'
  have hsm : Small Hm₂ (Sm.mul (Sol (s, (φ₀, α₀, δΨ, f₁))).2)
      (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) := by
    intro y
    obtain ⟨x, rfl⟩ := Sm.Ω1Equiv.surjective y
    simpa [Sm.spacing_eq] using hs6 x
  have hδ : (Sol' (s', (symSite σ φ₀, Sm.mul α₀, symSite σ δΨ, Sm.fld f₁))).2 =
      Sm.mul (Sol (s, (φ₀, α₀, δΨ, f₁))).2 :=
    (huniq' _ hsm ((fluctFixed_sym_iff_pair Sm hidx hchi hbox hqset hss false α₀ φ₀ δΨ f₁
      _).2 hfix)).symm
  refine Prod.ext ?_ hδ
  show (Sol' (s', (symSite σ φ₀, Sm.mul α₀, symSite σ δΨ, Sm.fld f₁))).1 =
    Sm.fld (Sol (s, (φ₀, α₀, δΨ, f₁))).1
  rw [hfld', hδ, pertSource_symField_pair Sm,
    dphi_sym_pair Sm (decG2_sym_pair Sm hidx hchi hbox hqset hss), ← hfld]

end Bg

section Clip

open Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G G' : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {σ : Equiv.Perm (CTorus d L N₁ m₁ k)}

/-- **The cut-off `clipRaw` commutes with the lattice symmetry**: `clipRaw 𝔹' (σ Ψ, σ h) =
σ (clipRaw 𝔹 (Ψ, h))`. -/
theorem clipRaw_act_pair (S : LatSymm G G' σ) (p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N) :
    clipRaw G' (actField σ p.1, actField σ p.2) = symRaw σ (clipRaw G p) := by
  classical
  refine Prod.ext (funext fun y => funext fun i => ?_) (funext fun y => funext fun i => ?_)
  · obtain ⟨x, rfl⟩ := σ.surjective y
    show (if σ x ∈ dataSites G' then p.1 (σ.symm (σ x)) i else 0) =
      (if σ.symm (σ x) ∈ dataSites G then p.1 (σ.symm (σ x)) i else 0)
    simp only [Equiv.symm_apply_apply, S.mem_dataSites]
  · obtain ⟨x, rfl⟩ := σ.surjective y
    show (if σ x ∈ G'.Ω 1 then p.2 (σ.symm (σ x)) i else 0) =
      (if σ.symm (σ x) ∈ G.Ω 1 then p.2 (σ.symm (σ x)) i else 0)
    simp only [Equiv.symm_apply_apply, S.mem_Ω1]

end Clip

end Balaban.Localization
