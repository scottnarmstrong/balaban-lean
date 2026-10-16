/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionSymm
public import Balaban.SmallField.XiSymm

/-!
# `O(N)` covariance and reality of the decoupled background map `F₁` and of the expansion terms

For the decoupled background `F₁ (s, Θ) = (φ_{k+1}(s), α_{k+1}(s))` (Theorem I-4b) and a functional
`Φ` of the background and the data `u = (Θ, ψ')`:

* `F₁_rot`: `F₁ (s, R Θ) = (R φ_{k+1}(s), α_{k+1}(s))` for real orthogonal `R`;
* `F₁_conj`: `F₁ (conj s, Θ) = conj F₁ (s, Θ)` for real `Θ`;
* `evTerm_rot`, `evTerm_conj`: the expansion terms `𝓔(X, Y)` of `Φ(φ_{k+1}(s), u)` inherit the
  `O(N)`-invariance and reality of `Φ`.

Only the background objects are treated; the fluctuation field `δφ` needs the fluctuation datum
(`flEdat`), which is not part of this file.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix
  Balaban.Fluctuation

section Data

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- `O(N)` acts on raw data `(Ψ, h̃)` pointwise. -/
def rotRaw (R : Matrix (Fin N) (Fin N) ℂ) (Θ : RawData d L (N₁ * L ^ m₁) K N) :
    RawData d L (N₁ * L ^ m₁) K N := (fun x => R *ᵥ Θ.1 x, fun x => R *ᵥ Θ.2 x)

theorem rawOf_rot (R : Matrix (Fin N) (Fin N) ℂ) (D : BgData G N) :
    rawOf (D.rot R) = rotRaw R (rawOf D) := rfl

/-- **`Ξ^c_n(𝔹; σ, ε)` is stable under real orthogonal rotations of the datum.** -/
theorem xiCData_rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {n : ℕ} {σ ε : ℝ}
    {D : BgData G N} (h : XiCData G a ν n σ ε D) : XiCData G a ν n σ ε (D.rot (cmat Q)) := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hX, hR⟩ := h
  exact ⟨fun x => Q *ᵥ Ψ₀ x, Q *ᵥ h₀, fun x => cmat Q *ᵥ Ψ'' x, fun x => cmat Q *ᵥ h'' x,
    xiC_rot G a ν hQ hX, realizesC_rot hR⟩

theorem xiCData_rot_iff {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {n : ℕ} {σ ε : ℝ}
    {D : BgData G N} : XiCData G a ν n σ ε (D.rot (cmat Q)) ↔ XiCData G a ν n σ ε D := by
  refine ⟨fun h => ?_, xiCData_rot hQ⟩
  have := xiCData_rot (orth_transpose_real hQ) h
  rwa [rot_rot_cmat hQ] at this

end Data

section BackgroundCore

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
variable {a₁ ν BG κ : ℝ}

/-- **The rotation step of `F₁_rot`**, for any notion `P s D φ α` of decoupled background that is
carried to itself by the rotation of the datum and of the field (the notion `IsDecBg` of the
one-generating-set chain, or `Dec2.IsDecBg (coverOf Gp) Gp` of the cover form): if `F₁` returns
`(φ, α)` at every `(s, D)` with `P s D φ α`, and `(φ, α)` is such a background of `D` at `s`, then
`F₁` returns `(R φ, α)` at the rotated datum.  Shared by `F₁_rot` and its cover form. -/
theorem F₁_rot_of_isBg
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    {P : DecParams Gp → BgData Gp N → (Gp.Ω 1 × Fin N → ℂ) → (Gp.Ω 1 → ℂ) → Prop}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), P s D φ α → F₁ (s, rawOf D) = (φ, α))
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (hP : ∀ (s : DecParams Gp) (D : BgData Gp N) (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ),
      P s D φ α → P s (D.rot (cmat Q)) (rotFld (cmat Q) φ) α)
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData Gp N}
    (hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D)
    {φ : Gp.Ω 1 × Fin N → ℂ} {α : Gp.Ω 1 → ℂ} (hI : P s D φ α) :
    F₁ (s, rotRaw (cmat Q) (rawOf D)) = (rotFld (cmat Q) φ, α) :=
  hF₁ s (D.rot (cmat Q)) hs ((inUnionDomainC_rot_iff hQ).2 hU) _ _ (hP s D φ α hI)

end BackgroundCore

section Background

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ}
variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **The decoupled background of a datum of `Ξ^c_K(𝔹; 1, ε)`**: the datum lies in the union data
domain, and the decoupled system `IsDecBg` has a solution, which `F₁` returns. -/
theorem bg_point
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D) :
    InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D ∧
      ∃ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ),
        IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α ∧ F₁ (s, rawOf D) = (φ, α) := by
  classical
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC hC.HBp hδ0 hδ0' hδ1 hDom
  have hsle : ∀ P, ‖s P‖ ≤ Real.exp κ := fun P => (hs P).le
  obtain ⟨φ, α, hI, -, -, -, -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    hsle hδ0 le_rfl hδ0' hδ1 hνε hDom
  exact ⟨hU, φ, α, hI, hF₁ s D hs hU φ α hI⟩

/-- **`O(N)` covariance of the decoupled background**: `F₁ (s, R Θ) = (R φ_{k+1}(s), α_{k+1}(s))`
for a real orthogonal `R` and `Θ` a datum of `Ξ^c_K(𝔹; 1, ε)`. -/
theorem F₁_rot
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D) {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Qᵀ * Q = 1) :
    F₁ (s, rotRaw (cmat Q) (rawOf D)) =
      (rotFld (cmat Q) (F₁ (s, rawOf D)).1, (F₁ (s, rawOf D)).2) := by
  obtain ⟨hU, φ, α, hI, hFeq⟩ := bg_point hC hF₁ hs hD
  rw [hFeq]
  exact F₁_rot_of_isBg (P := fun s D φ α => IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α)
    hF₁ hQ (fun s D φ α h =>
      (DecEquiv.isDecBg_rot_iff (isRealOrth_ofReal hQ).1 _ s D φ α).2 h) hs hU hI

/-- **Reality of the decoupled background**: `F₁ (conj s, Θ) = conj F₁ (s, Θ)` for real `Θ`. -/
theorem F₁_conj
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D) (hreal : D.IsReal) :
    F₁ (fun P => starRingEnd ℂ (s P), rawOf D) =
      (fun p => starRingEnd ℂ ((F₁ (s, rawOf D)).1 p),
        fun x => starRingEnd ℂ ((F₁ (s, rawOf D)).2 x)) := by
  obtain ⟨hU, φ, α, hI, hFeq⟩ := bg_point hC hF₁ hs hD
  rw [hFeq]
  have hI' := DecEquiv.isDecBg_conj hreal hI
  exact hF₁ _ D (fun P => by simpa using hs P) hU _ _ hI'

end Background

section Terms

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ K)}
variable {m₀ : ℕ} {X₁ : Set (CTorus d L N₁ m₁ K)}

/-- `O(N)` acts on the data `u = (Θ, ψ')` of the expansion. -/
def rotU (R : Matrix (Fin N) (Fin N) ℂ)
    (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) :
    RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) :=
  (rotRaw R u.1, fun x => R *ᵥ u.2 x)

theorem rotU_mem {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁) :
    rotU (cmat Q) u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁ := by
  obtain ⟨⟨D, hD, hDu⟩, hψ⟩ := hu
  refine ⟨⟨D.rot (cmat Q), xiCData_rot hQ hD, ?_⟩, fun x hx => ?_⟩
  · rw [rawOf_rot, ← hDu]; rfl
  · show vn (cmat Q *ᵥ u.2 x) < δ₁
    rw [vn_rot (isRealOrth_ofReal hQ)]
    exact hψ x hx

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **The function expanded for a background functional is `O(N)`-invariant** on the polydisc. -/
theorem fnOfDec_rot
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {Φb : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) u,
      Φb (rotFld (cmat Q) bg.1, bg.2) (rotU (cmat Q) u) = Φb bg u)
    {u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁)
    {s : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ}
    (hs : s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ)
      (fun _ => Real.exp κ)) :
    fnOfDec Gp Hm X₁f F₁ Sol (fun bg _ u => Φb bg u) (rotU (cmat Q) u) s =
      fnOfDec Gp Hm X₁f F₁ Sol (fun bg _ u => Φb bg u) u s := by
  obtain ⟨⟨D, hD, hDu⟩, hψ⟩ := hu
  have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 hs'
  have hrot := F₁_rot hC hF₁ hsx hD hQ
  have hu1 : u.1 = rawOf D := hDu
  unfold fnOfDec
  show Φb (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, rotRaw (cmat Q) u.1)) _ = _
  rw [hu1, hrot]
  rw [← hu1]
  exact (hΦ _ u).trans rfl

/-- **The expansion terms of a background functional inherit its `O(N)`-invariance**:
`𝓔(X, Y)(R u) = 𝓔(X, Y)(u)` whenever `Φ(R φ, α; R u) = Φ(φ, α; u)`. -/
theorem evTerm_rot
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {Φb : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) u,
      Φb (rotFld (cmat Q) bg.1, bg.2) (rotU (cmat Q) u) = Φb bg u)
    (Y : Set (CTorus d L N₁ m₁ K))
    {u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁) :
    evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀ X₁
        (fnOfDec Gp Hm X₁f F₁ Sol (fun bg _ u => Φb bg u)) Y (rotU (cmat Q) u) =
      evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀ X₁
        (fnOfDec Gp Hm X₁f F₁ Sol (fun bg _ u => Φb bg u)) Y u :=
  evTerm_congr_polydisc _ (Real.one_lt_exp_iff.2 hC.hκ) X₁ Y
    fun _ hs => fnOfDec_rot hC hF₁ hQ hΦ hu hs

/-- Raw data with real entries. -/
def IsRealRaw (Θ : RawData d L (N₁ * L ^ m₁) K N) : Prop :=
  ∀ x i, (Θ.1 x i).im = 0 ∧ (Θ.2 x i).im = 0

/-- **The function expanded for a background functional is real** on the polydisc:
`F(u, conj s) = conj F(u, s)` for real data, if `Φ` is. -/
theorem fnOfDec_conj
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Φb : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) u, IsRealRaw u.1 →
      starRingEnd ℂ (Φb bg u) =
        Φb (fun p => starRingEnd ℂ (bg.1 p), fun x => starRingEnd ℂ (bg.2 x)) u)
    {u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁) (hreal : IsRealRaw u.1)
    {s : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ}
    (hs : s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ)
      (fun _ => Real.exp κ)) :
    fnOfDec Gp Hm X₁f F₁ Sol (fun bg _ u => Φb bg u) u (cjv s) =
      starRingEnd ℂ (fnOfDec Gp Hm X₁f F₁ Sol (fun bg _ u => Φb bg u) u s) := by
  obtain ⟨⟨D, hD, hDu⟩, hψ⟩ := hu
  have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 hs'
  have hu1 : u.1 = rawOf D := hDu
  have hDreal : D.IsReal := fun x i => by
    have := hreal x i
    rw [hu1] at this
    exact this
  have hext : extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (cjv s) =
      fun P => starRingEnd ℂ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s P) := by
    classical
    funext P
    unfold extParams cjv
    split_ifs <;> simp
  have hcj := F₁_conj hC hF₁ hsx hD hDreal
  unfold fnOfDec
  show Φb (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (cjv s), u.1)) u = _
  show _ = starRingEnd ℂ (Φb (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, u.1)) u)
  rw [hext, hu1, hcj, hΦ _ u hreal]

/-- **The expansion terms of a background functional are real for real data.** -/
theorem evTerm_real
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Φb : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) u, IsRealRaw u.1 →
      starRingEnd ℂ (Φb bg u) =
        Φb (fun p => starRingEnd ℂ (bg.1 p), fun x => starRingEnd ℂ (bg.2 x)) u)
    (Y : Set (CTorus d L N₁ m₁ K))
    {u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁) (hreal : IsRealRaw u.1) :
    starRingEnd ℂ (evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀ X₁
        (fnOfDec Gp Hm X₁f F₁ Sol (fun bg _ u => Φb bg u)) Y u) =
      evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀ X₁
        (fnOfDec Gp Hm X₁f F₁ Sol (fun bg _ u => Φb bg u)) Y u :=
  evTerm_conj _ (Real.one_lt_exp_iff.2 hC.hκ) X₁ Y
    fun _ hs => fnOfDec_conj hC hF₁ hΦ hu hreal hs

end Terms

end Balaban.Localization
