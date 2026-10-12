/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RopConcreteMeas
public import Balaban.LargeField.R.DenominatorRot
public import Balaban.LargeField.R.PositiveMassFacts
import Mathlib
import Balaban.LargeField.R.PsiZeroSmooth
import Balaban.LargeField.R.PsiZeroAnalytic

/-!
# The reference density with the physical mass term (Definition III.8.1, P7 (3.1)-(3.5))

The landed `rhoZero` has mass zero in its action.  P7 (3.1) and LF-RECONSTRUCTION Definition III.8.1 keep the
physical mass term `(ν_k/2) Σ |φ - h|²` of the main action in the reference density, evaluated at the **massless**
reference background (the centre `ψ⁰_k` and the sharp cutoff stay massless; the author's ruling, AGENTS.md, Q13).

* `massFunctional G a ν h ψ`: `L^{-k(d-2)} (ν/2) Σ_{x∈Ω₁} Σ_i |φ⁰(ψ)(x,i) - h_i|²` with `φ⁰(ψ) = bgField G a 0 (dataR ψ)`
  the massless Def-5 background of the lifted block field.  `ν` is the mass in fine units, exactly the `ν` of `action`
  (`ν = ν_k L^{-2k}`), and the factor `L^{-k(d-2)}` is the normalization of `effActionNorm`, so the coefficient is
  `ν_k L^{-kd}/2` of P7 (3.1).  The sites are the sites of the region `Ω₁` of the action `A_k(𝔹)` (the sites the
  landed `action` sums its mass term over).  Alternative reading (not implemented): the half-star convention of P7
  could enlarge the site set; the landed action has none for the mass term.
* `rhoZeroPhysical`: the cutoff `χ_{Z₀}` about `ψ⁰_k = psiZero` times `exp(-β (A*_k + massFunctional))` at the merged
  field, `A*_k = effActionNorm`.  `rhoZeroPhysical_mass_zero`: at `ν = 0` it is the landed `rhoZero`.
* `massFunctional_nonneg`, `continuousOn_massFunctional`, `massFunctional_le` (W193's `real_mass_cost`).
* `measurable_rhoZeroPhysicalTot`, `rhoZeroPhysical_bounds`, `integral_rhoZeroPhysical_bounds`.
* `denominatorPhysical_bounds`: `∫ρ^ph = exp(-β A*(ψ⁰) - (N/2) log β |Z₀| + Ẽ₀^ph)` with the crude real bound
  `|Ẽ₀^ph| ≤ C_Ẽ D₀^d + 2 E n`.  The sharp statement (Q13-REEXPAND (3.6)-(3.7), retaining the linear term of the
  Taylor expansion of the mass functional at `ψ⁰_k`) needs the localized response estimate (3.4), which is not proved.
* `tildeE0Phys_rot_joint`: `Ẽ₀^ph(Qψ, Qh) = Ẽ₀^ph(ψ, h)`.  Invariance under `ψ ↦ Qψ` alone fails in general: for one
  spin the minimizer `positiveMass_minimizer_ne` moves with `h`, so `massFunctional (Qψ) h` differs from
  `massFunctional ψ h`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Balaban Balaban.Multiscale Balaban.Background MeasureTheory Matrix

namespace Balaban.LargeField

section Mass

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)

/-- **The physical mass term of P7 (3.1)** at the massless background of the lifted block field:
`L^{-k(d-2)} (ν/2) Σ_{x∈Ω₁} Σ_i |φ⁰(ψ)(x,i) - h_i|²`, `φ⁰(ψ) = bgField G a 0 (dataR ψ)`, `ν` the mass in fine units
(`ν_k L^{-2k}`) and `h ∈ ℝ^N` the external field. -/
noncomputable def massFunctional (ν : ℝ) (h : Fin N → ℝ) (ψ : BlockField d L N₀ k N) : ℝ :=
  (ν / 2 * ∑ x : G.Ω 1, ∑ i, ‖bgField G a 0 (dataR G ψ) (x, i) - (h i : ℂ)‖ ^ 2) / (L : ℝ) ^ (k * (d - 2))

variable {G a}

theorem massFunctional_zero (h : Fin N → ℝ) (ψ : BlockField d L N₀ k N) :
    massFunctional G a 0 h ψ = 0 := by
  simp [massFunctional]

theorem massFunctional_nonneg {ν : ℝ} (hν : 0 ≤ ν) (h : Fin N → ℝ) (ψ : BlockField d L N₀ k N) :
    0 ≤ massFunctional G a ν h ψ := by
  unfold massFunctional
  positivity

theorem massFunctional_congr {ν : ℝ} (h : Fin N → ℝ) {ψ ψ' : BlockField d L N₀ k N}
    (hψ : ∀ x ∈ dataSites G, ψ (jBlock d L N₀ k k x) = ψ' (jBlock d L N₀ k k x)) :
    massFunctional G a ν h ψ = massFunctional G a ν h ψ' := by
  unfold massFunctional
  rw [dataR_congr G hψ]

/-- **Joint `O(N)`-covariance** of the mass functional: `(ψ, h) ↦ (Qψ, Qh)`. -/
theorem massFunctional_rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (ν : ℝ) (h : Fin N → ℝ)
    (ψ : BlockField d L N₀ k N) :
    massFunctional G a ν (Q *ᵥ h) (rotBlock Q ψ) = massFunctional G a ν h ψ := by
  have hR := isRealOrth_ofReal hQ
  unfold massFunctional
  rw [dataR_rot, bgField_rot a 0 hR]
  have hx : ∀ x : G.Ω 1, ∑ i, ‖rotFld (cmat Q) (bgField G a 0 (dataR G ψ)) (x, i) - ((Q *ᵥ h) i : ℂ)‖ ^ 2 =
      ∑ i, ‖bgField G a 0 (dataR G ψ) (x, i) - (h i : ℂ)‖ ^ 2 := by
    intro x
    rw [← normSq_rot hR (fun i => bgField G a 0 (dataR G ψ) (x, i) - (h i : ℂ))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [rotFld, Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
  simp only [hx]

end Mass

section MassReg

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}

/-- The massless background field is continuous in the block field on the tube `Ψ̃(𝔹; τ)`,
`τ ≤ min (c₀, c₁)` (Theorem 5.2 (2): analytic in the data). -/
theorem continuousOn_bgField (H : BgHyp d L k ϱ a 0) {τ : ℝ} (hτ : 0 < τ) (hτ0 : τ ≤ bgC0 d L N)
    (hτ1 : τ ≤ bgC1 d L N) :
    ContinuousOn (fun ψ : BlockField d L N₀ k N => bgField G a 0 (dataR G ψ))
      {ψ | TubeOn G Set.univ τ ψ} := by
  obtain ⟨Φ, hΦ, hΦe⟩ := theorem72_analytic (G := G) (N := N) H
  have hmaps : Set.MapsTo (rawMap G (N := N)) {ψ | TubeOn G Set.univ τ ψ}
      {p | ∃ D : BgData G N, InUnionDomainC G (bgC0 d L N) (bgC1 d L N) 0 D ∧ p = (D.Ψ, D.h)} :=
    fun ψ hψ => ⟨dataR G ψ, inUnionDomainC_of_tube G hτ hτ0 hτ1 hψ, rfl⟩
  have hΦr : ContDiffOn ℝ 0 Φ
      {p | ∃ D : BgData G N, InUnionDomainC G (bgC0 d L N) (bgC1 d L N) 0 D ∧ p = (D.Ψ, D.h)} :=
    fun p hp => ((hΦ p hp).contDiffAt.restrict_scalars ℝ).contDiffWithinAt
  have hΦ' : ContDiffOn ℝ 0 (fun ψ => Φ (rawMap G ψ)) {ψ | TubeOn G Set.univ τ ψ} :=
    hΦr.comp (contDiff_rawMap G).contDiffOn hmaps
  have hc : ContinuousOn (fun ψ => (Φ (rawMap G ψ)).1) {ψ | TubeOn G Set.univ τ ψ} :=
    continuous_fst.comp_continuousOn hΦ'.continuousOn
  refine hc.congr fun ψ hψ => ?_
  have hR := inUnionDomainR_of_tube G hτ hτ1 hψ
  have hC := inUnionDomainC_of_tube G hτ hτ0 hτ1 hψ
  have e1 := (theorem72_real H hR).1
  have e2 := hΦe (dataR G ψ) hC
  show bgField G a 0 (dataR G ψ) = (Φ ((dataR G ψ).Ψ, (dataR G ψ).h)).1
  rw [e2, e1]

/-- **The mass functional is continuous on the tube** (same route as `continuousOn_effAction`). -/
theorem continuousOn_massFunctional (H : BgHyp d L k ϱ a 0) {τ : ℝ} (hτ : 0 < τ) (hτ0 : τ ≤ bgC0 d L N)
    (hτ1 : τ ≤ bgC1 d L N) (ν : ℝ) (h : Fin N → ℝ) :
    ContinuousOn (massFunctional G a ν h) {ψ | TubeOn G Set.univ τ ψ} := by
  have hb := continuousOn_bgField (G := G) (a := a) H hτ hτ0 hτ1
  unfold massFunctional
  refine ContinuousOn.div_const (ContinuousOn.mul continuousOn_const ?_) _
  refine continuousOn_finsetSum _ fun x _ => continuousOn_finsetSum _ fun i _ => ?_
  have := ((continuous_apply (x, i)).comp_continuousOn hb).sub
    (continuousOn_const (c := ((h i : ℝ) : ℂ)))
  exact this.norm.pow 2

/-- **Bounds on the mass term (W193's `real_mass_cost`)**: for a block field of the tube, real unit `h` and
`β ν L^{-k(d-2)} ≤ E`: `0 ≤ β · massFunctional ≤ 2 E |Ω₁|`. -/
theorem massFunctional_bounds (H : BgHyp d L k ϱ a 0) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ bgC1 d L N)
    {ψ : BlockField d L N₀ k N} (ht : TubeOn G Set.univ τ ψ) {ν β E : ℝ} (h : Fin N → ℝ)
    (hh : ∑ i, h i ^ 2 = 1) (hβ : 0 ≤ β) (hν : 0 ≤ ν)
    (hE : β * (ν / (L : ℝ) ^ (k * (d - 2))) ≤ E) :
    0 ≤ β * massFunctional G a ν h ψ ∧
      β * massFunctional G a ν h ψ ≤ 2 * E * (Fintype.card (G.Ω 1) : ℝ) := by
  have hunit := (theorem71 H (inUnionDomainR_of_tube G hτ hτ1 ht)).2.1
  set φ := bgField G a 0 (dataR G ψ) with hφ
  let v : G.Ω 1 → EuclideanSpace ℂ (Fin N) := fun x => WithLp.toLp 2 fun i => φ (x, i)
  let hv : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 fun i => ((h i : ℝ) : ℂ)
  have hsq : ∀ x : G.Ω 1, ‖v x - hv‖ ^ 2 = ∑ i, ‖φ (x, i) - (h i : ℂ)‖ ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  have hv1 : ∀ x ∈ (Finset.univ : Finset (G.Ω 1)), ‖v x‖ = 1 := by
    intro x _
    have : ‖v x‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact (hunit x).2
    nlinarith [norm_nonneg (v x)]
  have hh1 : ‖hv‖ = 1 := by
    have : ‖hv‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq, ← hh]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [hv]
    nlinarith [norm_nonneg hv]
  have hL : 0 ≤ ν / (L : ℝ) ^ (k * (d - 2)) := by positivity
  obtain ⟨h1, h2⟩ := real_mass_cost Finset.univ v hv hv1 hh1 hβ hL hE
  have heq : β * massFunctional G a ν h ψ =
      1 / 2 * β * (ν / (L : ℝ) ^ (k * (d - 2))) * ∑ x ∈ Finset.univ, ‖v x - hv‖ ^ 2 := by
    simp only [hsq]
    unfold massFunctional
    ring
  rw [heq]
  rw [Finset.card_univ] at h2
  exact ⟨h1, h2⟩

end MassReg

section Density

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)

/-- **The reference density with the physical mass term, for an arbitrary centre `ψ⁰`**:
`χ_{Z₀} · exp(-β_k (A*_k + massFunctional))` at the merged field; the cutoff and the centre are the massless ones of
`rhoZeroWith`. -/
noncomputable def rhoZeroPhysicalWith (Zf : Finset (Torus d (N₀ * L ^ (k - k)))) (ψ0 ψk : BlockField d L N₀ k N)
    (ν : ℝ) (h : Fin N → ℝ) (C6 β p0 : ℝ) (u : SuppSpace Zf N) : ℝ :=
  chiZeroCut ψ0 (zeroRadius C6 β p0) u *
    Real.exp (-β * (effActionNorm G a (mergeField Zf ψk u) + massFunctional G a ν h (mergeField Zf ψk u)))

theorem rhoZeroPhysicalWith_eq_mul (Zf : Finset (Torus d (N₀ * L ^ (k - k)))) (ψ0 ψk : BlockField d L N₀ k N)
    (ν : ℝ) (h : Fin N → ℝ) (C6 β p0 : ℝ) (u : SuppSpace Zf N) :
    rhoZeroPhysicalWith G a Zf ψ0 ψk ν h C6 β p0 u =
      rhoZeroWith G a Zf ψ0 ψk C6 β p0 u * Real.exp (-β * massFunctional G a ν h (mergeField Zf ψk u)) := by
  unfold rhoZeroPhysicalWith rhoZeroWith
  have : -β * (effActionNorm G a (mergeField Zf ψk u) + massFunctional G a ν h (mergeField Zf ψk u)) =
      -β * effActionNorm G a (mergeField Zf ψk u) + -β * massFunctional G a ν h (mergeField Zf ψk u) := by ring
  rw [this, Real.exp_add]
  ring

section Source

variable [NeZero N] {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
  (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
  {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
  (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
  (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0)

/-- **Definition III.8.1 with the physical mass term (P7 (3.1)): `ρ_{k,0}^{ph}(Z)`** for `Z₀ = box b₀ w`: the cutoff about
the massless centre `ψ⁰_k = psiZero` (`C₆ = 3dD₀(K₆+1)`) times `exp(-β_k (A*_k + massFunctional))`, the mass term
evaluated at the massless background of the merged field.  `ν` is the mass in fine units, `h ∈ ℝ^N` the external field.
At `ν = 0` it is the landed `rhoZero` (`rhoZeroPhysical_mass_zero`). -/
noncomputable def rhoZeroPhysical {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (ν : ℝ) (h : Fin N → ℝ) (β p0 : ℝ)
    (u : SuppSpace (boxFinset b0 w) N) : ℝ :=
  rhoZeroPhysicalWith G a (boxFinset b0 w) (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk) ψk ν h
    (cSix d D (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)) β p0 u

theorem rhoZeroPhysical_eq_mul {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (ν : ℝ) (h : Fin N → ℝ) (β p0 : ℝ)
    (u : SuppSpace (boxFinset b0 w) N) :
    rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 u =
      rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 u *
        Real.exp (-β * massFunctional G a ν h (mergeField (boxFinset b0 w) ψk u)) :=
  rhoZeroPhysicalWith_eq_mul G a _ _ _ ν h _ β p0 u

/-- **At mass `0` the physical reference density is the landed `rhoZero`.** -/
theorem rhoZeroPhysical_mass_zero {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (h : Fin N → ℝ) (β p0 : ℝ) :
    rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk 0 h β p0 =
      rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 := by
  funext u
  rw [rhoZeroPhysical_eq_mul]
  simp [massFunctional_zero]

theorem rhoZeroPhysical_nonneg {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (ν : ℝ) (h : Fin N → ℝ) (β p0 : ℝ)
    (u : SuppSpace (boxFinset b0 w) N) :
    0 ≤ rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 u := by
  rw [rhoZeroPhysical_eq_mul]
  exact mul_nonneg (rhoZeroWith_nonneg _ _ _ _ _ _ _ _ _) (Real.exp_pos _).le

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **Locality of the physical reference density** (Lemma III.1.5; cf. `rhoZero_congr`): the mass functional reads the
lifted field on the same data sites as `effAction`, so `ρ^{ph}_{k,0}(Z)` depends on the outside field only through
`ψ_k↾(X ∖ Z₀)`. -/
theorem rhoZeroPhysical_congr {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk ψk' : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (hψk' : TubeOn G (X \ box b0 w) δ ψk')
    (hxx : ∀ z ∈ X \ box b0 w, ψk z = ψk' z) (ν : ℝ) (h : Fin N → ℝ) (β p0 : ℝ) :
    rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk' ν h β p0 =
      rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 := by
  funext u
  rw [rhoZeroPhysical_eq_mul, rhoZeroPhysical_eq_mul,
    congrFun (rhoZero_congr G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk hψk' hxx β p0) u]
  congr 3
  refine massFunctional_congr h fun x hx => ?_
  have hxX := hdata x hx
  by_cases hz : jBlock d L N₀ k k x ∈ box b0 w
  · have hz' := mem_boxFinset.2 hz
    funext i
    rw [mergeField_of_mem hz' i, mergeField_of_mem hz' i]
  · have hz' : jBlock d L N₀ k k x ∉ boxFinset (L := L) (N₀ := N₀) (k := k) b0 w :=
      fun hh => hz (mem_boxFinset.1 hh)
    rw [mergeField_of_not_mem hz', mergeField_of_not_mem hz']
    exact (hxx _ ⟨hxX, hz⟩).symm

end Source

end Density

section Bounds

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)
  [NeZero N] {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
  (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
  {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
  (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
  (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0)

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **The support of the cutoff lies in the tube**: under the parameter conditions of `denominator_eq`, the
merged field of a point of the cutoff lies in `Ψ̃(𝔹; etaDen)`, and `etaDen` is a valid tube width for the
background (`0 < η ≤ min (c₀, c₁)`). -/
theorem tube_of_cutoff {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) {β p0 : ℝ} (hβ : 0 < β)
    (hp0 : 1 ≤ cSix d D (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) * p0)
    (hrad : psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H * δ +
      5 * zeroRadius (cSix d D (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)) β p0 ≤ etaDen d L N D) :
    0 < etaDen d L N D ∧ etaDen d L N D ≤ bgC0 d L N ∧ etaDen d L N D ≤ bgC1 d L N ∧
      ∀ u : SuppSpace (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) N,
        ZeroCutoff (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk)
          (zeroRadius (cSix d D (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)) β p0) u →
        TubeOn G Set.univ (etaDen d L N D) (mergeField (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) ψk u) := by
  set K := psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H with hKdef
  have hK : 0 < K := psiZeroK_pos N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H
  have hd0 : 0 < d := by omega
  have hD1 : 1 ≤ D := (hw1 ⟨0, hd0⟩).trans (hwD _)
  have hC6 : 0 < cSix d D K := by
    unfold cSix
    have : (0 : ℝ) < d := by exact_mod_cast hd0
    have : (0 : ℝ) < D := by exact_mod_cast hD1
    positivity
  have hp0pos : 0 < p0 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hC6.le h]
  set ρ := zeroRadius (cSix d D K) β p0 with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]; unfold zeroRadius; positivity
  set η := etaDen d L N D with hηdef
  have hη1 : η ≤ bgC1 d L N := min_le_left _ _
  have hη0 : η ≤ bgC0 d L N := hη1.trans (bgC1_le_bgC0 d L N hd0)
  have hKδ : 0 < K * δ := mul_pos hK hδ
  have hηpos : 0 < η := by linarith
  have hη16 : η ≤ 1 := hη0.trans ((bgC0_le d L N).trans (by norm_num))
  have hKδ1 : K * δ ≤ 1 := by linarith
  have hρ1 : ρ ≤ 1 := by linarith
  refine ⟨hηpos, hη0, hη1, fun u hc => ?_⟩
  obtain ⟨hsol, -⟩ := psiZero_spec N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk
  set ψ0 := psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk with hψ0
  have ht0 : TubeOn G Set.univ (K * δ) ψ0 := tubeOn_univ_of_data G hdata hsol.1
  refine tubeOn_mono G hrad (tubeOn_perturb G hKδ1 hρpos.le hρ1 ht0 ?_)
  intro z
  by_cases hz : z ∈ boxFinset (L := L) (N₀ := N₀) (k := k) b0 w
  · have h1 : (fun i => mergeField (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) ψk u z i - ψ0 z i) =
        fun i => u (⟨z, hz⟩, i) - ψ0 z i := by
      funext i; rw [mergeField_of_mem hz i]
    rw [h1]; exact (hc ⟨z, hz⟩).le
  · have h1 : (fun i => mergeField (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) ψk u z i - ψ0 z i) =
        fun _ => 0 := by
      funext i
      rw [mergeField_of_not_mem hz, hsol.2.1 z (fun h => hz (mem_boxFinset.2 h))]
      simp
    rw [h1]
    simp [rn, hρpos.le]

end Bounds

section Meas

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)
  [NeZero N] {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
  (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
  {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
  (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
  (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0)

open Classical in
/-- The mass functional cut off to the tube `Ψ̃(𝔹; τ)` (`0` outside). -/
noncomputable def massTube (τ ν : ℝ) (h : Fin N → ℝ) (ψ : BlockField d L N₀ k N) : ℝ :=
  if TubeOn G Set.univ τ ψ then massFunctional G a ν h ψ else 0

theorem massTube_eq {τ ν : ℝ} (h : Fin N → ℝ) {ψ : BlockField d L N₀ k N} (ht : TubeOn G Set.univ τ ψ) :
    massTube G a τ ν h ψ = massFunctional G a ν h ψ := by
  simp [massTube, ht]

include H in
theorem measurable_massTube {τ : ℝ} (hτ : 0 < τ) (hτ0 : τ ≤ bgC0 d L N) (hτ1 : τ ≤ bgC1 d L N) (ν : ℝ)
    (h : Fin N → ℝ) : Measurable (massTube G a τ ν h : BlockField d L N₀ k N → ℝ) := by
  classical
  have hm := ContinuousOn.measurable_piecewise (s := {ψ : BlockField d L N₀ k N | TubeOn G Set.univ τ ψ})
    (f := massFunctional G a ν h) (g := fun _ => (0 : ℝ)) (continuousOn_massFunctional (G := G) (a := a) H hτ hτ0 hτ1 ν h)
    continuous_const.continuousOn (measurableSet_tubeOn N G _ _)
  convert hm using 1
  funext ψ
  simp [massTube, Set.piecewise]

local notation "Kz" => psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H

open Classical in
/-- `ρ^{ph}_{k,0}(Z)` as a total function of `(u, ψ_k)` (`0` off the tube `Ψ̃(X ∖ Z₀; δ)`). -/
noncomputable def rhoZeroPhysicalTot {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) (ν : ℝ) (h : Fin N → ℝ) (β p0 : ℝ)
    (p : SuppSpace (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) N × BlockField d L N₀ k N) : ℝ :=
  if hT : TubeOn G (X \ box b0 w) δ p.2 then
    rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hT ν h β p0 p.1 else 0

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **The physical reference density is jointly Borel in `(ψ_k↾Z₀, ψ_k)`** (Definition III.8.1): W208's
`measurable_rhoZeroTot` times the exponential of the (continuous on the tube) mass term. -/
theorem measurable_rhoZeroPhysicalTot {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) (ν : ℝ) (h : Fin N → ℝ) {β p0 : ℝ}
    (hβ : 0 < β) (hp0 : 1 ≤ cSix d D Kz * p0)
    (hrad : Kz * δ + 5 * zeroRadius (cSix d D Kz) β p0 ≤ etaDen d L N D) :
    Measurable (rhoZeroPhysicalTot G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc ν h β p0) := by
  classical
  have hT0 := measurable_rhoZeroTot N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hβ hp0 hrad
  by_cases hex : ∃ ψk : BlockField d L N₀ k N, TubeOn G (X \ box b0 w) δ ψk
  swap
  · have : rhoZeroPhysicalTot G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc ν h β p0 = fun _ => 0 := by
      funext p
      have hT : ¬ TubeOn G (X \ box b0 w) δ p.2 := fun hT => hex ⟨p.2, hT⟩
      simp [rhoZeroPhysicalTot, hT]
    rw [this]; exact measurable_const
  obtain ⟨ψ1, hψ1⟩ := hex
  obtain ⟨hηpos, hη0, hη1, -⟩ :=
    tube_of_cutoff G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψ1 hβ hp0 hrad
  set Zb := boxFinset (L := L) (N₀ := N₀) (k := k) b0 w with hZb
  have hmergeM : Measurable fun p : SuppSpace Zb N × BlockField d L N₀ k N => mergeField Zb p.2 p.1 :=
    (continuous_mergeField (N := N) Zb).measurable
  have hmt := measurable_massTube G a H hηpos hη0 hη1 ν h
  have heq : rhoZeroPhysicalTot G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc ν h β p0 =
      fun p => rhoZeroTot N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc β p0 p *
        Real.exp (-β * massTube G a (etaDen d L N D) ν h (mergeField Zb p.2 p.1)) := by
    funext p
    by_cases hT : TubeOn G (X \ box b0 w) δ p.2
    · have h1 : rhoZeroTot N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc β p0 p =
          rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hT β p0 p.1 := by
        simp [rhoZeroTot, hT]
      have h2 : rhoZeroPhysicalTot G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc ν h β p0 p =
          rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hT ν h β p0 p.1 := by
        simp [rhoZeroPhysicalTot, hT]
      rw [h1, h2, rhoZeroPhysical_eq_mul]
      by_cases hc : ZeroCutoff (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hT)
          (zeroRadius (cSix d D Kz) β p0) p.1
      · obtain ⟨-, -, -, hcut⟩ :=
          tube_of_cutoff G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hT hβ hp0 hrad
        rw [massTube_eq G a h (hcut p.1 hc)]
      · have : rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hT β p0 p.1 = 0 :=
          rhoZeroWith_eq_zero G a _ _ _ _ β p0 _ hc
        rw [this]; simp
    · simp [rhoZeroPhysicalTot, rhoZeroTot, hT]
  rw [heq]
  exact hT0.mul (Real.measurable_exp.comp (measurable_const.mul (hmt.comp hmergeM)))

include hd hk hw1 hwD hm hXreg hΩ hdata H in
theorem measurable_rhoZeroPhysical {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (ν : ℝ) (h : Fin N → ℝ) {β p0 : ℝ}
    (hβ : 0 < β) (hp0 : 1 ≤ cSix d D Kz * p0)
    (hrad : Kz * δ + 5 * zeroRadius (cSix d D Kz) β p0 ≤ etaDen d L N D) :
    Measurable (rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0) := by
  have := (measurable_rhoZeroPhysicalTot G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc ν h hβ hp0 hrad).comp
    (measurable_id.prodMk (measurable_const (a := ψk)))
  convert this using 1
  funext u
  simp [rhoZeroPhysicalTot, hψk]

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **Two-sided pointwise bound** (W193's `real_mass_cost`): for real unit `h`, `0 ≤ ν` and
`β ν L^{-k(d-2)} ≤ E`: `e^{-2E n} ρ_{k,0} ≤ ρ^{ph}_{k,0} ≤ ρ_{k,0}`, `n = |Ω₁|`. -/
theorem rhoZeroPhysical_bounds {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) {ν : ℝ} (hν : 0 ≤ ν) (h : Fin N → ℝ) (hh : ∑ i, h i ^ 2 = 1)
    {β p0 E : ℝ} (hβ : 0 < β) (hE : β * (ν / (L : ℝ) ^ (k * (d - 2))) ≤ E)
    (hp0 : 1 ≤ cSix d D Kz * p0)
    (hrad : Kz * δ + 5 * zeroRadius (cSix d D Kz) β p0 ≤ etaDen d L N D)
    (u : SuppSpace (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) N) :
    Real.exp (-(2 * E * (Fintype.card (G.Ω 1) : ℝ))) *
        rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 u ≤
      rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 u ∧
    rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 u ≤
      rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 u := by
  rw [rhoZeroPhysical_eq_mul]
  have hr0 : 0 ≤ rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 u :=
    rhoZeroWith_nonneg _ _ _ _ _ _ _ _ _
  by_cases hc : ZeroCutoff (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk)
      (zeroRadius (cSix d D Kz) β p0) u
  · obtain ⟨hηpos, -, hη1, hcut⟩ :=
      tube_of_cutoff G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk hβ hp0 hrad
    obtain ⟨h1, h2⟩ := massFunctional_bounds (a := a) H hηpos hη1 (hcut u hc) h hh hβ.le hν hE
    set m := massFunctional G a ν h (mergeField (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) ψk u)
    have e1 : Real.exp (-(2 * E * (Fintype.card (G.Ω 1) : ℝ))) ≤ Real.exp (-β * m) :=
      Real.exp_le_exp.2 (by linarith)
    have e2 : Real.exp (-β * m) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    constructor
    · exact (mul_le_mul_of_nonneg_right e1 hr0).trans_eq (mul_comm _ _)
    · exact mul_le_of_le_one_right hr0 e2
  · have : rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 u = 0 :=
      rhoZeroWith_eq_zero G a _ _ _ _ β p0 _ hc
    rw [this]; simp


include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **Integrability, positivity and two-sided bound of `∫ρ^{ph}_{k,0}`** from the landed `denominator_eq` for
`rhoZero` and the pointwise bounds. -/
theorem integral_rhoZeroPhysical_bounds {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) {ν : ℝ} (hν : 0 ≤ ν) (h : Fin N → ℝ) (hh : ∑ i, h i ^ 2 = 1)
    {β p0 E : ℝ} (hβ : 0 < β) (hE : β * (ν / (L : ℝ) ^ (k * (d - 2))) ≤ E)
    (hp0 : 1 ≤ cSix d D Kz * p0)
    (hrad : Kz * δ + 5 * zeroRadius (cSix d D Kz) β p0 ≤ etaDen d L N D) :
    Integrable (rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0) volume ∧
    0 < ∫ u, rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 u ∧
    Real.exp (-(2 * E * (Fintype.card (G.Ω 1) : ℝ))) *
        ∫ u, rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 u ≤
      ∫ u, rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 u ∧
    ∫ u, rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 u ≤
      ∫ u, rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 u := by
  obtain ⟨-, hpos, -⟩ := denominator_eq G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk hβ hp0 hrad
  have hint : Integrable (rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0) volume := by
    by_contra hni
    have := integral_undef hni
    linarith
  have hb := rhoZeroPhysical_bounds G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk hν h hh hβ hE hp0 hrad
  have hmeas := measurable_rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h hβ hp0 hrad
  have hpint : Integrable (rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0) volume := by
    refine hint.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (rhoZeroPhysical_nonneg G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 u)]
    exact (hb u).2
  have hlow : Real.exp (-(2 * E * (Fintype.card (G.Ω 1) : ℝ))) *
        ∫ u, rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 u ≤
      ∫ u, rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 u := by
    rw [← integral_const_mul]
    exact integral_mono (hint.const_mul _) hpint fun u => (hb u).1
  refine ⟨hpint, lt_of_lt_of_le (mul_pos (Real.exp_pos _) hpos) hlow, hlow, ?_⟩
  exact integral_mono hpint hint fun u => (hb u).2

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **`Ẽ₀^{ph}`** (Q13-REEXPAND (3.2), measured against the massless centre value): defined by the identity of
`denominatorPhysical_bounds`, `Ẽ₀^{ph} = log ∫ρ^{ph}_{k,0} + β A*_k(Z; ψ⁰_k) + (N/2) log β |Z₀|`. -/
noncomputable def tildeE0Phys {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (ν : ℝ) (h : Fin N → ℝ) (β p0 : ℝ) : ℝ :=
  Real.log (∫ u, rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 u) +
    β * effActionNorm G a (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk) +
    (N : ℝ) / 2 * Real.log β * ((boxFinset (L := L) (N₀ := N₀) (k := k) b0 w).card : ℝ)


include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **The denominator with the physical mass term** (Lemma III.8.2; P7 (3.1)-(3.3), Q13-REEXPAND): with
`β ν L^{-k(d-2)} ≤ E`, real unit `h`,
`∫ ρ^{ph}_{k,0}(Z) = exp(-β A*_k(Z; ψ⁰_k) - (N/2) log β |Z₀| + Ẽ₀^{ph})`, the integral is positive, and
`Ẽ₀ - 2 E n ≤ Ẽ₀^{ph} ≤ Ẽ₀`, hence `|Ẽ₀^{ph}| ≤ C_Ẽ D₀^d + 2 E n` (`n = |Ω₁|`).
This is the **crude real bound**: the sharp one, Q13-REEXPAND (3.6)-(3.7) with the linear term of the mass functional at
`ψ⁰_k` retained, needs the localized response estimate (3.4), which is open and not attempted here. -/
theorem denominatorPhysical_bounds {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) {ν : ℝ} (hν : 0 ≤ ν) (h : Fin N → ℝ) (hh : ∑ i, h i ^ 2 = 1)
    {β p0 E : ℝ} (hβ : 0 < β) (hE : β * (ν / (L : ℝ) ^ (k * (d - 2))) ≤ E)
    (hp0 : 1 ≤ cSix d D Kz * p0)
    (hrad : Kz * δ + 5 * zeroRadius (cSix d D Kz) β p0 ≤ etaDen d L N D) :
    ∫ u, rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 u =
      Real.exp (-β * effActionNorm G a (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk)
        - (N : ℝ) / 2 * Real.log β * ((boxFinset (L := L) (N₀ := N₀) (k := k) b0 w).card : ℝ) +
        tildeE0Phys G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0) ∧
    0 < ∫ u, rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 u ∧
    tildeE0 G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 - 2 * E * (Fintype.card (G.Ω 1) : ℝ) ≤
      tildeE0Phys G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 ∧
    tildeE0Phys G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 ≤
      tildeE0 G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 ∧
    |tildeE0Phys G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0| ≤
      cTildeE N d D * (D : ℝ) ^ d + 2 * E * (Fintype.card (G.Ω 1) : ℝ) := by
  obtain ⟨-, hpos0, hE0⟩ := denominator_eq G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk hβ hp0 hrad
  obtain ⟨-, hpos, hlow, hup⟩ :=
    integral_rhoZeroPhysical_bounds G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk hν h hh hβ hE hp0 hrad
  set I := ∫ u, rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 u with hI
  set I0 := ∫ u, rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 u with hI0
  have hdiff : tildeE0Phys G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 -
      tildeE0 G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 = Real.log I - Real.log I0 := by
    unfold tildeE0Phys tildeE0
    ring
  have hl1 : Real.log I ≤ Real.log I0 := Real.log_le_log hpos hup
  have hl2 : -(2 * E * (Fintype.card (G.Ω 1) : ℝ)) + Real.log I0 ≤ Real.log I := by
    have := Real.log_le_log (mul_pos (Real.exp_pos _) hpos0) hlow
    rwa [Real.log_mul (Real.exp_pos _).ne' hpos0.ne', Real.log_exp] at this
  have hn : 0 ≤ 2 * E * (Fintype.card (G.Ω 1) : ℝ) := by
    have : 0 ≤ E := le_trans (mul_nonneg hβ.le (by positivity)) hE
    positivity
  refine ⟨?_, hpos, by linarith, by linarith, ?_⟩
  · have : -β * effActionNorm G a (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk)
        - (N : ℝ) / 2 * Real.log β * ((boxFinset (L := L) (N₀ := N₀) (k := k) b0 w).card : ℝ) +
        tildeE0Phys G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 = Real.log I := by
      unfold tildeE0Phys; rw [← hI]; ring
    rw [this, Real.exp_log hpos]
  · rw [abs_le] at hE0 ⊢
    constructor <;> linarith [hE0.1, hE0.2]


include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **Joint `O(N)`-covariance of the physical reference density**:
`ρ^{ph}_{k,0}(Z)(Qψ_k, Qh)(Q u) = ρ^{ph}_{k,0}(Z)(ψ_k, h)(u)`. -/
theorem rhoZeroPhysical_rot {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (hψk' : TubeOn G (X \ box b0 w) δ (rotBlock Q ψk)) (ν : ℝ) (h : Fin N → ℝ) (β p0 : ℝ)
    (u : SuppSpace (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) N) :
    rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk' ν (Q *ᵥ h) β p0 (rotSuppFun Q u) =
      rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 u := by
  rw [rhoZeroPhysical_eq_mul, rhoZeroPhysical_eq_mul,
    rhoZero_rot G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk hQ hψk' β p0 u, merge_rot,
    massFunctional_rot hQ]

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **Joint `O(N)`-invariance of `Ẽ₀^{ph}`** (Lemma III.8.2): `Ẽ₀^{ph}(Qψ_k, Qh) = Ẽ₀^{ph}(ψ_k, h)`.

*Remark.*  Invariance under `ψ_k ↦ Qψ_k` alone (with `h` fixed) is false in general, in contrast to the landed
`tildeE0_rot` (which has no `h`): the mass term `(ν/2) Σ |φ⁰(ψ) - h|²` is not invariant under `φ⁰ ↦ Qφ⁰`.  In the one-spin
example of `positiveMass_minimizer_ne` the minimizer depends on the direction of `h`, so `massFunctional (Qψ) h` and
`massFunctional ψ h` differ. -/
theorem tildeE0Phys_rot_joint {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (hψk' : TubeOn G (X \ box b0 w) δ (rotBlock Q ψk)) (ν : ℝ) (h : Fin N → ℝ) (β p0 : ℝ) :
    tildeE0Phys G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk' ν (Q *ᵥ h) β p0 =
      tildeE0Phys G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 := by
  have hmp := (rotSupp (Zf := boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) hQ).measurePreserving
  have hint : ∫ v, rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk' ν (Q *ᵥ h) β p0 v =
      ∫ u, rhoZeroPhysical G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk ν h β p0 u := by
    rw [← hmp.integral_comp
      (rotSupp (Zf := boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) hQ).toHomeomorph.measurableEmbedding]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    exact rhoZeroPhysical_rot G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk hQ hψk' ν h β p0 u
  unfold tildeE0Phys
  rw [hint, psiZero_equivariant N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk hQ hψk',
    effActionNorm_rot G a hQ]


end Meas

end Balaban.LargeField
