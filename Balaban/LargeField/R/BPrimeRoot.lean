/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.BPrimeLocal
public import Balaban.LargeField.R.BPrimeSum

/-!
# The P3 premises of a root functional of two decoupled background fields

A root summand of the P7 (3.22)–(3.25) residual is a functional `Φ u φ₁ φ₂` of the data `u` and of
the background fields `φ₁`, `φ₂` of two generating sets (the old and the new background of `R`),
reading the fields only on the root region `X₁`.  Its decoupled extension (P3 §4) is
`pairExt … Φ u s = Φ u φ₁(s) φ₂(s)`, the fields being the decoupled background fields of the two
pairs `(C₁, H₁)`, `(C₂, H₂)` at the labelled cut parameters `labParams Cᵢ πᵢ lab s`.

`rootLocPremises_pairExt`: if `Φ` is analytic and bounded where the fields are within the I-4b
bound of the approximate fields, and reads the fields only on `X₁`, then the extension satisfies
the P3 premises `RootLocPremises` of the root (analyticity on `Su ×` the polydisc, the bound,
(AE2) with the agreement of the data on the `resDep`-thickening of `Y(𝒞)`), so that its
coefficients `r4Fresh` enter `bPrime` (`bPrime_aggregate_of_localization`).  The value at all
parameters `1` is `Φ` at the background fields `bgFieldC` (`pairExt_one`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis Finset

section Root

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ₁ ϱ₂ : ℝ}
  {C₁ C₂ : DecCover d L N₁ m₁ K} {H₁ : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
  {H₂ : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂} {a : ℕ → ℝ} {ν Kc Cx : ℝ} {U : Type*}

variable (H₁ H₂) in
/-- **Agreement of two data points on a region** for the two pairs: the data of both generating sets
agree on the dependency sets `resDep` of the sites of `A`, and the further agreement `AgΦ A` of the
root functionals on `A` holds. -/
def pairAgree (D₁ : U → BgData H₁ N) (D₂ : U → BgData H₂ N)
    (AgΦ : Set (CTorus d L N₁ m₁ K) → U → U → Prop) (A : Set (CTorus d L N₁ m₁ K)) (u u' : U) :
    Prop :=
  (∀ x ∈ A, x ∈ H₁.Ω 1 → ∀ y ∈ resDep H₁ x, (D₁ u).Ψ y = (D₁ u').Ψ y ∧ (D₁ u).h y = (D₁ u').h y) ∧
  (∀ x ∈ A, x ∈ H₂.Ω 1 → ∀ y ∈ resDep H₂ x, (D₂ u).Ψ y = (D₂ u').Ψ y ∧ (D₂ u).h y = (D₂ u').h y) ∧
  AgΦ A u u'

theorem pairAgree_mono {D₁ : U → BgData H₁ N} {D₂ : U → BgData H₂ N}
    {AgΦ : Set (CTorus d L N₁ m₁ K) → U → U → Prop}
    (hmono : ∀ A A' u u', A ⊆ A' → AgΦ A' u u' → AgΦ A u u')
    {A A' : Set (CTorus d L N₁ m₁ K)} (hA : A ⊆ A') {u u' : U}
    (h : pairAgree H₁ H₂ D₁ D₂ AgΦ A' u u') : pairAgree H₁ H₂ D₁ D₂ AgΦ A u u' :=
  ⟨fun x hx => h.1 x (hA hx), fun x hx => h.2.1 x (hA hx), hmono A A' u u' hA h.2.2⟩

/-- The fields within `r` of the approximate field of the datum `D` (the region of Theorem I-4b). -/
def NearApprox (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁) (a : ℕ → ℝ) (ν : ℝ) (D : BgData H N)
    (r : ℝ) (φ : H.Ω 1 × Fin N → ℂ) : Prop :=
  SupBounds H (fun p => φ p - approxField H a ν D.Ψ D.h p.1 p.2) r

variable {ι : Type*}

variable (C₁ H₁ C₂ H₂ a ν) in
/-- **The decoupled extension of a root functional of two background fields**: `Φ` at the decoupled
background fields of the pairs `(C₁, H₁)`, `(C₂, H₂)` at the labelled cut parameters. -/
noncomputable def pairExt (ρ : ℝ) (π₁ π₂ : ℕ × CTorus d L N₁ m₁ K → ℕ × CTorus d L N₁ m₁ K)
    (lab : ι → ℕ × CTorus d L N₁ m₁ K) (D₁ : U → BgData H₁ N) (D₂ : U → BgData H₂ N)
    (Φ : U → (H₁.Ω 1 × Fin N → ℂ) → (H₂.Ω 1 × Fin N → ℂ) → ℂ) (u : U) (s : ι → ℂ) : ℂ :=
  Φ u (Dec2.decBgField C₁ H₁ a ν ρ (labParams C₁ π₁ lab s) (D₁ u))
    (Dec2.decBgField C₂ H₂ a ν ρ (labParams C₂ π₂ lab s) (D₂ u))

/-- **The value at all parameters `1`**: `Φ` at the background fields of Theorem 5.2. -/
theorem pairExt_one {c₀ BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c₀ BG)
    (S₁ : Dec2.CoverBase C₁ H₁ a ν Kc Cx) (S₂ : Dec2.CoverBase C₂ H₂ a ν Kc Cx)
    (HB₁ : BgHyp d L K ϱ₁ a ν) (HB₂ : BgHyp d L K ϱ₂ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c₀ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (π₁ π₂ : ℕ × CTorus d L N₁ m₁ K → ℕ × CTorus d L N₁ m₁ K) (lab : ι → ℕ × CTorus d L N₁ m₁ K)
    (D₁ : U → BgData H₁ N) (D₂ : U → BgData H₂ N)
    (Φ : U → (H₁.Ω 1 × Fin N → ℂ) → (H₂.Ω 1 × Fin N → ℂ) → ℂ) {u : U}
    (hD₁ : InUnionDomainC H₁ (bgC0 d L N) (c7 d L N BG κ) ν (D₁ u))
    (hD₂ : InUnionDomainC H₂ (bgC0 d L N) (c7 d L N BG κ) ν (D₂ u)) :
    pairExt C₁ C₂ H₁ H₂ a ν (rho4 d L N BG κ) π₁ π₂ lab D₁ D₂ Φ u 1 =
      Φ u (bgFieldC H₁ a ν (bgC0 d L N) (D₁ u)) (bgFieldC H₂ a ν (bgC0 d L N) (D₂ u)) := by
  unfold pairExt
  rw [show (1 : ι → ℂ) = fun _ => 1 from rfl, labParams_one, labParams_one,
    decBgField_one_eq hS S₁ HB₁ hκ hM hD₁, decBgField_one_eq hS S₂ HB₂ hκ hM hD₂]

variable {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ} [DecidableEq ι] [Fintype ι]
  [NormedAddCommGroup U] [NormedSpace ℂ U]

/-- **The P3 premises of a root functional of two decoupled background fields.**  Let the root
`X` (level `j`, chosen family `𝒦X`, `X₁ = X1 G m₀ j 𝒦X` as the finite set `X₁f`) and the cut labels
`lab` (cubes of `G`, distinct, off `X₁`) satisfy the geometric premises, and let the two pairs have
`Dec2.CoverLocal`, `HatConn`, `BgHyp` with one set of I-4b constants at the polydisc radius
`e^{κ₁}`, the label maps `πᵢ` with `hπsubᵢ`, `hπparᵢ`.  Let the data maps `Dᵢ` be analytic on the
open set `Su` with values in `Ψ̃^c(δ, ε)`.  If the root functional `Φ` is analytic and bounded by
`Eb e^{-(κ-1) d^cov_j(X)}` where both fields are within `r = K₂' C₅₃ δ` of the approximate fields,
and reads the fields only on `X₁` and the data only through `AgΦ X₁` (`AgΦ` reflexive and
monotone in the region), then its decoupled extension
satisfies `RootLocPremises` with the agreement `pairAgree` of the data on the regions. -/
theorem rootLocPremises_pairExt {c₀ BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c₀ BG)
    (S₁ : Dec2.CoverLocal C₁ H₁ a ν Kc Cx) (S₂ : Dec2.CoverLocal C₂ H₂ a ν Kc Cx)
    (hconn₁ : Dec2.HatConn C₁ H₁) (hconn₂ : Dec2.HatConn C₂ H₂)
    (HB₁ : BgHyp d L K ϱ₁ a ν) (HB₂ : BgHyp d L K ϱ₂ a ν) {κ κ₁ : ℝ} (hκ₁ : 0 < κ₁)
    (hM : c₀ * Real.exp (N0 d L * κ₁) ≤ (L : ℝ) ^ m₁)
    {j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)} (hcov : CovSetup G m₀ j X 𝒦X)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {X₁f : Finset (CTorus d L N₁ m₁ K)} (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X1 G m₀ j 𝒦X)
    {lab : ι → ℕ × CTorus d L N₁ m₁ K} (hmem : ∀ i, lab i ∈ cubeIdx G)
    (hinj : Function.Injective lab) (hdisj : ∀ i, Disjoint (Pset m₁ (lab i)) (X1 G m₀ j 𝒦X))
    {π₁ π₂ : ℕ × CTorus d L N₁ m₁ K → ℕ × CTorus d L N₁ m₁ K}
    (hπsub₁ : ∀ P ∈ C₁.cubeIdx, ∀ x ∈ cubeP P, x ∈ Pset m₁ (π₁ P))
    (hπpar₁ : ∀ P ∈ C₁.cubeIdx, ¬ cubeP P ⊆ X₁f → ∃ i, lab i = π₁ P)
    (hπsub₂ : ∀ P ∈ C₂.cubeIdx, ∀ x ∈ cubeP P, x ∈ Pset m₁ (π₂ P))
    (hπpar₂ : ∀ P ∈ C₂.cubeIdx, ¬ cubeP P ⊆ X₁f → ∃ i, lab i = π₂ P)
    {Su : Set U} (hSu : IsOpen Su) {D₁ : U → BgData H₁ N} {D₂ : U → BgData H₂ N}
    (hD₁an : AnalyticOnNhd ℂ (fun u => ((D₁ u).Ψ, (D₁ u).h)) Su)
    (hD₂an : AnalyticOnNhd ℂ (fun u => ((D₂ u).Ψ, (D₂ u).h)) Su)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ₁)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2)
    (hD₁ : ∀ u ∈ Su, InDomainC H₁ ν δ ε (D₁ u)) (hD₂ : ∀ u ∈ Su, InDomainC H₂ ν δ ε (D₂ u))
    {Φ : U → (H₁.Ω 1 × Fin N → ℂ) → (H₂.Ω 1 × Fin N → ℂ) → ℂ} {Eb : ℝ} (hEb : 0 ≤ Eb)
    (hΦan : ∀ u ∈ Su, ∀ φ₁ φ₂,
      NearApprox H₁ a ν (D₁ u) (cK2' d L N (famConst d L BG κ₁) * (lemma53Const d L * δ)) φ₁ →
      NearApprox (ϱ₁ := ϱ₂) H₂ a ν (D₂ u)
        (cK2' d L N (famConst d L BG κ₁) * (lemma53Const d L * δ)) φ₂ →
      AnalyticAt ℂ (fun q : U × (H₁.Ω 1 × Fin N → ℂ) × (H₂.Ω 1 × Fin N → ℂ) => Φ q.1 q.2.1 q.2.2)
        (u, φ₁, φ₂))
    (hΦbd : ∀ u ∈ Su, ∀ φ₁ φ₂,
      NearApprox H₁ a ν (D₁ u) (cK2' d L N (famConst d L BG κ₁) * (lemma53Const d L * δ)) φ₁ →
      NearApprox (ϱ₁ := ϱ₂) H₂ a ν (D₂ u)
        (cK2' d L N (famConst d L BG κ₁) * (lemma53Const d L * δ)) φ₂ →
      ‖Φ u φ₁ φ₂‖ ≤ Eb * Real.exp (-(κ - 1) * treeLenCovOne m₀ j X))
    {AgΦ : Set (CTorus d L N₁ m₁ K) → U → U → Prop} (hAgΦ : ∀ A u, AgΦ A u u)
    (hAgmono : ∀ A A' u u', A ⊆ A' → AgΦ A' u u' → AgΦ A u u')
    (hΦloc : ∀ u u' φ₁ φ₁' φ₂ φ₂',
      (∀ y : H₁.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ X₁f → ∀ i, φ₁ (y, i) = φ₁' (y, i)) →
      (∀ y : H₂.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ X₁f → ∀ i, φ₂ (y, i) = φ₂' (y, i)) →
      AgΦ (↑X₁f) u u' → Φ u φ₁ φ₂ = Φ u' φ₁' φ₂') :
    RootLocPremises G m₀ lab j X 𝒦X κ κ₁ Eb Su
      (fun C u u' => pairAgree H₁ H₂ D₁ D₂ AgΦ (compY lab (X1 G m₀ j 𝒦X) C) u u')
      (fun Y u u' => pairAgree H₁ H₂ D₁ D₂ AgΦ Y u u')
      (pairExt C₁ C₂ H₁ H₂ a ν (rho4 d L N BG κ₁) π₁ π₂ lab D₁ D₂ Φ) := by
  have hE1 : (1 : ℝ) < Real.exp κ₁ := Real.one_lt_exp_iff.2 hκ₁
  have hκ0 : 0 ≤ κ₁ := hκ₁.le
  have hU₁ : ∀ u ∈ Su, InUnionDomainC H₁ (bgC0 d L N) (c7 d L N BG κ₁) ν (D₁ u) :=
    fun u hu => ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hD₁ u hu⟩
  have hU₂ : ∀ u ∈ Su, InUnionDomainC H₂ (bgC0 d L N) (c7 d L N BG κ₁) ν (D₂ u) :=
    fun u hu => ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hD₂ u hu⟩
  -- the decoupled fields at a point of the domain: value and bounds
  have hnear₁ : ∀ u ∈ Su, ∀ s : ι → ℂ, (∀ i, ‖s i‖ < Real.exp κ₁) →
      NearApprox H₁ a ν (D₁ u) (cK2' d L N (famConst d L BG κ₁) * (lemma53Const d L * δ))
        (Dec2.decBgField C₁ H₁ a ν (rho4 d L N BG κ₁) (labParams C₁ π₁ lab s) (D₁ u)) := by
    intro u hu s hs
    obtain ⟨φ, α, hI, hun, -, hsup, -⟩ := Dec2.i4b_exists_unique hS S₁.toCoverBase HB₁ hκ0 hM
      (s := labParams C₁ π₁ lab s) (fun P => (norm_labParams_lt C₁ π₁ lab hE1 hs P).le)
      hδ0 hδε hε hδ hνε (hD₁ u hu)
    rw [(Dec2.decBg_eq hI hun).1]
    exact hsup
  have hnear₂ : ∀ u ∈ Su, ∀ s : ι → ℂ, (∀ i, ‖s i‖ < Real.exp κ₁) →
      NearApprox (ϱ₁ := ϱ₂) H₂ a ν (D₂ u)
        (cK2' d L N (famConst d L BG κ₁) * (lemma53Const d L * δ))
        (Dec2.decBgField C₂ H₂ a ν (rho4 d L N BG κ₁) (labParams C₂ π₂ lab s) (D₂ u)) := by
    intro u hu s hs
    obtain ⟨φ, α, hI, hun, -, hsup, -⟩ := Dec2.i4b_exists_unique hS S₂.toCoverBase HB₂ hκ0 hM
      (s := labParams C₂ π₂ lab s) (fun P => (norm_labParams_lt C₂ π₂ lab hE1 hs P).le)
      hδ0 hδε hε hδ hνε (hD₂ u hu)
    rw [(Dec2.decBg_eq hI hun).1]
    exact hsup
  have hpoly : ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁), ∀ i, ‖s i‖ < Real.exp κ₁ :=
    fun s hs i => by simpa using hs i
  have hpolyOpen : IsOpen (polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁)) := by
    have : polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁) =
        ⋂ i, {s : ι → ℂ | ‖s i - 0‖ < Real.exp κ₁} := by
      ext s; simp [polydisc]
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt (continuous_norm.comp ((continuous_apply i).sub continuous_const)) continuous_const
  -- the analyticity of the two fields
  have hφ₁an := analyticOnNhd_decBgField_comp hS S₁.toCoverBase HB₁ hκ0 hM hSu hpolyOpen hD₁an hU₁
    (p := fun s => labParams C₁ π₁ lab s) (fun s _ => analyticAt_labParams C₁ π₁ lab s)
    (fun s hs P => norm_labParams_lt C₁ π₁ lab hE1 (hpoly s hs) P)
  have hφ₂an := analyticOnNhd_decBgField_comp hS S₂.toCoverBase HB₂ hκ0 hM hSu hpolyOpen hD₂an hU₂
    (p := fun s => labParams C₂ π₂ lab s) (fun s _ => analyticAt_labParams C₂ π₂ lab s)
    (fun s hs P => norm_labParams_lt C₂ π₂ lab hE1 (hpoly s hs) P)
  refine
    { cov := hcov
      mem := hmem
      inj := hinj
      disj := hdisj
      opt := hopt
      Eb_nonneg := hEb
      refl := fun C u _ => ⟨fun _ _ _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ _ => ⟨rfl, rfl⟩, hAgΦ _ u⟩
      link := fun C u u' h =>
        pairAgree_mono hAgmono (compY_subset_Ysites hcov.hU hcov.hN hmem _ C) h
      ana := ?_
      bd := ?_
      loc := ?_ }
  · intro q hq
    have hin : AnalyticAt ℂ (fun q : U × (ι → ℂ) =>
        (q.1, Dec2.decBgField C₁ H₁ a ν (rho4 d L N BG κ₁) (labParams C₁ π₁ lab q.2) (D₁ q.1),
          Dec2.decBgField C₂ H₂ a ν (rho4 d L N BG κ₁) (labParams C₂ π₂ lab q.2) (D₂ q.1))) q :=
      analyticAt_fst.prod ((hφ₁an q hq).prod (hφ₂an q hq))
    have hΦq := hΦan q.1 hq.1 _ _ (hnear₁ q.1 hq.1 q.2 (hpoly q.2 hq.2))
      (hnear₂ q.1 hq.1 q.2 (hpoly q.2 hq.2))
    exact AnalyticAt.comp (g := fun q : U × (H₁.Ω 1 × Fin N → ℂ) × (H₂.Ω 1 × Fin N → ℂ) =>
      Φ q.1 q.2.1 q.2.2) (f := fun q : U × (ι → ℂ) =>
        (q.1, Dec2.decBgField C₁ H₁ a ν (rho4 d L N BG κ₁) (labParams C₁ π₁ lab q.2) (D₁ q.1),
          Dec2.decBgField C₂ H₂ a ν (rho4 d L N BG κ₁) (labParams C₂ π₂ lab q.2) (D₂ q.1)))
      hΦq hin
  · intro u hu s hs
    exact hΦbd u hu _ _ (hnear₁ u hu s (hpoly s hs)) (hnear₂ u hu s (hpoly s hs))
  · intro C u u' hu hu' s s' hs hs' hag hAg
    have hlabK : ∀ i, (lab i).1 ≤ K := fun i => ((mem_cubeIdx G).1 (hmem i)).1.2
    have hoff : ∀ i, Disjoint (Pset m₁ (lab i)) (↑X₁f : Set (CTorus d L N₁ m₁ K)) := by
      intro i; rw [hX₁]; exact hdisj i
    have hag' : ∀ i ∈ C, Pset m₁ (lab i) ⊆ compY lab (↑X₁f : Set (CTorus d L N₁ m₁ K)) C →
        s i = s' i := by
      intro i hi hsub; rw [hX₁] at hsub; exact hag i hi hsub
    have hY : compY lab (↑X₁f : Set (CTorus d L N₁ m₁ K)) C = compY lab (X1 G m₀ j 𝒦X) C := by
      rw [hX₁]
    have k₁ := decBgField_lab_local hS S₁ hconn₁ HB₁ hκ0 hM hinj hlabK hoff hπsub₁ hπpar₁
      (Cf := C) (fun i hi => hs.1 i hi) (fun i hi => hs'.1 i hi) (fun i => (hs.2 i).le)
      (fun i => (hs'.2 i).le) hag' hδ0 hδε hε hδ hνε (hD₁ u hu) (hD₁ u' hu')
      (fun x hx => by rw [hY] at hx; exact hAg.1 x hx)
    have k₂ := decBgField_lab_local hS S₂ hconn₂ HB₂ hκ0 hM hinj hlabK hoff hπsub₂ hπpar₂
      (Cf := C) (fun i hi => hs.1 i hi) (fun i hi => hs'.1 i hi) (fun i => (hs.2 i).le)
      (fun i => (hs'.2 i).le) hag' hδ0 hδε hε hδ hνε (hD₂ u hu) (hD₂ u' hu')
      (fun x hx => by rw [hY] at hx; exact hAg.2.1 x hx)
    have hX₁sub : (↑X₁f : Set (CTorus d L N₁ m₁ K)) ⊆ compY lab (X1 G m₀ j 𝒦X) C := by
      rw [← hY]; exact subset_compY _ _
    exact hΦloc u u' _ _ _ _ k₁ k₂ (hAgmono _ _ u u' hX₁sub hAg.2.2)

end Root

/-! ### All roots: the aggregate identity for root functionals of two background fields -/

section Roots

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}
  {C₁ C₂ : DecCover d L N₁ m₁ K} {H₁ : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
  {H₂ : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂} {a : ℕ → ℝ} {ν Kc Cx : ℝ}
  {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
  {Rt : Type*} {ι : Rt → Type*} [∀ r, DecidableEq (ι r)] [∀ r, Fintype (ι r)] {Zt : Type*}

/-- **The aggregate identity of P7 (3.22)–(3.25) for root functionals of two background fields.**
For a finite set of roots `r` (each with its P3 geometry, cut labels and root functional `Φ r`
satisfying the premises of `rootLocPremises_pairExt`), the sum of the root functionals at the
background fields of Theorem 5.2 of the two generating sets is the sum over the final domains `Y`
of `ℬ′_Y = ∑_r r4Fresh_r(Y)` of their decoupled extensions; `ℬ′_Y` depends on the data only through
the agreement on `Y`, is bounded by `∑_r Eb_r e^{-κ₀ d^cov(X_r) - 2κ d̃^cov(Y)}` and is analytic. -/
theorem bPrime_pairs_aggregate [DecidableEq (Set (CTorus d L N₁ m₁ K))] (hd : 3 ≤ d) (hL : 3 ≤ L)
    {κ κ₀ κ₁ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκ : 3 * κ₀ + 3 ≤ κ)
    (hκκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κ ≤ κ₁) (h1 : 1 ≤ (κ₁ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2)
    {c₀ BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c₀ BG)
    (S₁ : Dec2.CoverLocal C₁ H₁ a ν Kc Cx) (S₂ : Dec2.CoverLocal C₂ H₂ a ν Kc Cx)
    (hconn₁ : Dec2.HatConn C₁ H₁) (hconn₂ : Dec2.HatConn C₂ H₂)
    (HB₁ : BgHyp d L K ϱ₁ a ν) (HB₂ : BgHyp d L K ϱ₂ a ν) (hκ₁ : 0 < κ₁)
    (hM : c₀ * Real.exp (N0 d L * κ₁) ≤ (L : ℝ) ^ m₁)
    {π₁ π₂ : ℕ × CTorus d L N₁ m₁ K → ℕ × CTorus d L N₁ m₁ K}
    (hπsub₁ : ∀ P ∈ C₁.cubeIdx, ∀ x ∈ cubeP P, x ∈ Pset m₁ (π₁ P))
    (hπsub₂ : ∀ P ∈ C₂.cubeIdx, ∀ x ∈ cubeP P, x ∈ Pset m₁ (π₂ P))
    {roots : Finset Rt} {lab : ∀ r, ι r → ℕ × CTorus d L N₁ m₁ K} {j : Rt → ℕ}
    {X 𝒦X : Rt → Set (CTorus d L N₁ m₁ K)} {X₁f : Rt → Finset (CTorus d L N₁ m₁ K)}
    (hcov : ∀ r ∈ roots, CovSetup G m₀ (j r) (X r) (𝒦X r))
    (hopt : ∀ r ∈ roots, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X r) ∧ MeetsOne m₀ (j r) (𝒦X r) W₀ ∧
        bondCost (scaleW L m₀ m₁ (j r)) E₀ = treeLenCovOne m₀ (j r) (X r))
    (hX₁ : ∀ r ∈ roots, (↑(X₁f r) : Set (CTorus d L N₁ m₁ K)) = X1 G m₀ (j r) (𝒦X r))
    (hmem : ∀ r ∈ roots, ∀ i, lab r i ∈ cubeIdx G)
    (hinj : ∀ r ∈ roots, Function.Injective (lab r))
    (hdisj : ∀ r ∈ roots, ∀ i, Disjoint (Pset m₁ (lab r i)) (X1 G m₀ (j r) (𝒦X r)))
    (hπpar₁ : ∀ r ∈ roots, ∀ P ∈ C₁.cubeIdx, ¬ cubeP P ⊆ X₁f r → ∃ i, lab r i = π₁ P)
    (hπpar₂ : ∀ r ∈ roots, ∀ P ∈ C₂.cubeIdx, ¬ cubeP P ⊆ X₁f r → ∃ i, lab r i = π₂ P)
    {Su : Set U} (hSu : IsOpen Su) {D₁ : U → BgData H₁ N} {D₂ : U → BgData H₂ N}
    (hD₁an : AnalyticOnNhd ℂ (fun u => ((D₁ u).Ψ, (D₁ u).h)) Su)
    (hD₂an : AnalyticOnNhd ℂ (fun u => ((D₂ u).Ψ, (D₂ u).h)) Su)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ₁)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2)
    (hD₁ : ∀ u ∈ Su, InDomainC H₁ ν δ ε (D₁ u)) (hD₂ : ∀ u ∈ Su, InDomainC H₂ ν δ ε (D₂ u))
    {Φ : Rt → U → (H₁.Ω 1 × Fin N → ℂ) → (H₂.Ω 1 × Fin N → ℂ) → ℂ} {Eb : Rt → ℝ}
    (hEb : ∀ r ∈ roots, 0 ≤ Eb r)
    (hΦan : ∀ r ∈ roots, ∀ u ∈ Su, ∀ φ₁ φ₂,
      NearApprox H₁ a ν (D₁ u) (cK2' d L N (famConst d L BG κ₁) * (lemma53Const d L * δ)) φ₁ →
      NearApprox (ϱ₁ := ϱ₂) H₂ a ν (D₂ u)
        (cK2' d L N (famConst d L BG κ₁) * (lemma53Const d L * δ)) φ₂ →
      AnalyticAt ℂ (fun q : U × (H₁.Ω 1 × Fin N → ℂ) × (H₂.Ω 1 × Fin N → ℂ) =>
        Φ r q.1 q.2.1 q.2.2) (u, φ₁, φ₂))
    (hΦbd : ∀ r ∈ roots, ∀ u ∈ Su, ∀ φ₁ φ₂,
      NearApprox H₁ a ν (D₁ u) (cK2' d L N (famConst d L BG κ₁) * (lemma53Const d L * δ)) φ₁ →
      NearApprox (ϱ₁ := ϱ₂) H₂ a ν (D₂ u)
        (cK2' d L N (famConst d L BG κ₁) * (lemma53Const d L * δ)) φ₂ →
      ‖Φ r u φ₁ φ₂‖ ≤ Eb r * Real.exp (-(κ - 1) * treeLenCovOne m₀ (j r) (X r)))
    {AgΦ : Set (CTorus d L N₁ m₁ K) → U → U → Prop} (hAgΦ : ∀ A u, AgΦ A u u)
    (hAgmono : ∀ A A' u u', A ⊆ A' → AgΦ A' u u' → AgΦ A u u')
    (hΦloc : ∀ r ∈ roots, ∀ u u' φ₁ φ₁' φ₂ φ₂',
      (∀ y : H₁.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ X₁f r → ∀ i, φ₁ (y, i) = φ₁' (y, i)) →
      (∀ y : H₂.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ X₁f r → ∀ i, φ₂ (y, i) = φ₂' (y, i)) →
      AgΦ (↑(X₁f r)) u u' → Φ r u φ₁ φ₂ = Φ r u' φ₁' φ₂')
    (S : Finset Zt) :
    (∀ u ∈ Su, ∑ r ∈ roots, Φ r u (bgFieldC H₁ a ν (bgC0 d L N) (D₁ u))
        (bgFieldC H₂ a ν (bgC0 d L N) (D₂ u)) =
      ∑ Y ∈ bPrimeDomains G m₀ roots lab (fun r => X1 G m₀ (j r) (𝒦X r)),
        bPrime G m₀ roots lab (fun r => X1 G m₀ (j r) (𝒦X r))
          (fun r (_ : Finset Zt) => pairExt C₁ C₂ H₁ H₂ a ν (rho4 d L N BG κ₁) π₁ π₂ (lab r) D₁ D₂
            (Φ r)) S Y u) ∧
    (∀ Y, ∀ u ∈ Su, ∀ u' ∈ Su, pairAgree H₁ H₂ D₁ D₂ AgΦ Y u u' →
      bPrime G m₀ roots lab (fun r => X1 G m₀ (j r) (𝒦X r))
          (fun r (_ : Finset Zt) => pairExt C₁ C₂ H₁ H₂ a ν (rho4 d L N BG κ₁) π₁ π₂ (lab r) D₁ D₂
            (Φ r)) S Y u =
        bPrime G m₀ roots lab (fun r => X1 G m₀ (j r) (𝒦X r))
          (fun r (_ : Finset Zt) => pairExt C₁ C₂ H₁ H₂ a ν (rho4 d L N BG κ₁) π₁ π₂ (lab r) D₁ D₂
            (Φ r)) S Y u') ∧
    (∀ Y, ∀ u ∈ Su, ‖bPrime G m₀ roots lab (fun r => X1 G m₀ (j r) (𝒦X r))
          (fun r (_ : Finset Zt) => pairExt C₁ C₂ H₁ H₂ a ν (rho4 d L N BG κ₁) π₁ π₂ (lab r) D₁ D₂
            (Φ r)) S Y u‖ ≤
      ∑ r ∈ roots, Eb r * Real.exp (-κ₀ * treeLenCovOne m₀ (j r) (X r) -
        2 * κ * treeLenCov G m₀ Y)) ∧
    (∀ Y, AnalyticOnNhd ℂ (bPrime G m₀ roots lab (fun r => X1 G m₀ (j r) (𝒦X r))
          (fun r (_ : Finset Zt) => pairExt C₁ C₂ H₁ H₂ a ν (rho4 d L N BG κ₁) π₁ π₂ (lab r) D₁ D₂
            (Φ r)) S Y) Su) := by
  have hR : ∀ r ∈ roots, RootLocPremises G m₀ (lab r) (j r) (X r) (𝒦X r) κ κ₁ (Eb r) Su
      (fun C u u' => pairAgree H₁ H₂ D₁ D₂ AgΦ (compY (lab r) (X1 G m₀ (j r) (𝒦X r)) C) u u')
      (fun Y u u' => pairAgree H₁ H₂ D₁ D₂ AgΦ Y u u')
      ((fun r (_ : Finset Zt) => pairExt C₁ C₂ H₁ H₂ a ν (rho4 d L N BG κ₁) π₁ π₂ (lab r) D₁ D₂
        (Φ r)) r S) := fun r hr =>
    rootLocPremises_pairExt hS S₁ S₂ hconn₁ hconn₂ HB₁ HB₂ hκ₁ hM (hcov r hr) (hopt r hr)
      (hX₁ r hr) (hmem r hr) (hinj r hr) (hdisj r hr) hπsub₁ (hπpar₁ r hr) hπsub₂ (hπpar₂ r hr)
      hSu hD₁an hD₂an hδ0 hδε hε hδ hνε hD₁ hD₂ (hEb r hr) (hΦan r hr) (hΦbd r hr) hAgΦ hAgmono
      (hΦloc r hr)
  obtain ⟨hsum, hloc, hbd, han⟩ := bPrime_aggregate_of_localization (G := G) (m₀ := m₀) hd hL hκ₀ hκ
    hκκ₁ h1 hlog (S := S) (roots := roots) (c := lab) (j := j) (X := X) (𝒦X := 𝒦X) (Eb := Eb)
    (Su := Su)
    (Ag := fun r C u u' => pairAgree H₁ H₂ D₁ D₂ AgΦ (compY (lab r) (X1 G m₀ (j r) (𝒦X r)) C) u u')
    (AgY := fun Y u u' => pairAgree H₁ H₂ D₁ D₂ AgΦ Y u u')
    (F := fun r (_ : Finset Zt) => pairExt C₁ C₂ H₁ H₂ a ν (rho4 d L N BG κ₁) π₁ π₂ (lab r) D₁ D₂
      (Φ r)) hR
  refine ⟨fun u hu => ?_, hloc, hbd, han⟩
  rw [← hsum u hu]
  refine Finset.sum_congr rfl fun r hr => ?_
  exact (pairExt_one hS S₁.toCoverBase S₂.toCoverBase HB₁ HB₂ hκ₁.le hM π₁ π₂ (lab r) D₁ D₂ (Φ r)
    ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hD₁ u hu⟩ ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hD₂ u hu⟩).symm

end Roots

end Balaban.LargeField
