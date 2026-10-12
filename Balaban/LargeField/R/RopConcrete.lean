/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RopConcreteDecomp
public import Balaban.LargeField.R.RopConcreteLocal
public import Balaban.LargeField.R.RopConcreteNorm
import Mathlib

/-!
# The operation `R` for the concrete reference densities (Definitions III.8.1, III.8.3; Lemma III.8.4)

Conventions: the landed objects are used unchanged, in particular the **massless reference** of P7 (`effAction` has
zero mass term, `ν = 0`), `rhoZero` is the density `χ_{Z₀} exp(-β_k A*_k)` about `ψ⁰_k = psiZero`.

**Setting.**  A finite family `ι` of ripe components of `Z^pre_k(𝔸)`, each with its own generating set `G c`, its box
`Z₀(c) = box (b0 c) (w c)` of `k`-blocks, its region `X c = U^∼_k(c)`, and `δ c` below the constant `c₁₁` of
Lemma III.3.3.  The geometric premise (the source input of Lemma III.5.0 (`ZzeroDD_sep`), in the form in which it
enters here) is the separation `hsep : Disjoint (X c) (box (b0 c') (w c'))` for `c ≠ c'`: the zero-domain `Z₀(Z')` of
another component does not meet the region `U^∼_k(Z)` containing the window of `Z` (`hXreg`, `hdata`).  `ZzeroDD_sep`
is a statement about the history torus and `Zzero`; the passage from it to `hsep` (that `U^∼_k(Z)` lies in the
`3`-neighbourhood of the cubes of `Z_{k₃}`) is not landed, so `hsep` is a hypothesis.

**What is proved.**
* *Independence* (`famRho_eq_rhoZero`, `rhoZero_indep_other_components`; the locality theorem `rhoZero_congr` of
  `RopConcreteLocal.lean`): the reference density `ρ_{k,0}(Z)` of a field `ψ_k` of the tube is a function of
  `(ψ_k↾Z₀, ψ_k↾(⋃_{Z'∈𝒵_σ} Z₀(Z'))ᶜ)`; it does not read the variables `ψ_k↾Z₀(Z')` of the other components.
  Consequently the denominators `∫ρ_{k,0}(Z)` do not depend on them (`integral_rhoZero_indep_other_components`).
* *The decomposition* `famDecomp`: an `RDecomp` for the subfamily `σ ⊆ ι` sent to `R`, with the field space
  `Ψ̃ = ⋂_c Ψ̃(X c ∖ Z₀(c); δ c)` (`famTubeSet`) with Lebesgue measure, `W c = SuppSpace (Z₀(c))`, the outside
  variables `ZeroOutIdx → ℝ` and `r c = famRho` (the reference density, `0` off the tube, a null set).
  `Rop_famDecomp_apply` is the formula (1.6) with `ρ_{k,0}(Z) = rhoZero`.
* *Normalization* (`R_normalization_of_measurable`, `R_normalization_sum_of_measurable`, one component:
  `R_normalization_one_of_measurable`) from `denominator_eq` (integrability and positivity of `∫ρ_{k,0}(Z)`).
* *Non-degeneracy* (`rhoZero_nonconstant`, `famDecomp_nondegenerate`, `rdecomp_one_nondegenerate`).

**What remains a hypothesis.**  The joint measurability `hmeas` of `(ψ_k↾Z₀, y) ↦ ρ_{k,0}(Z)` (needed for Fubini):
it needs the measurability of `y ↦ ψ⁰_k(y)` (the unique minimizer; the analyticity of Lemma III.3.3 is landed only
locally with constants not identified with `psiZeroK`) and of `effAction` on the tube.  The results carrying it are
named `_of_measurable`.  The parameter conditions of `denominator_eq` (`hβ`, `hp0`, `hrad`) and the integrability of
`ρ` are the source premises.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Balaban Balaban.Multiscale Balaban.Background MeasureTheory

namespace Balaban.LargeField

section Fam

variable (N : ℕ) {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] [NeZero N] {ϱ : ℝ} {ι : Type} [Fintype ι]
  (G : ι → GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k)
  (b0 : ι → Torus d (N₀ * L ^ (k - k))) (w : ι → Fin d → ℕ)
  (hw1 : ∀ c i, 1 ≤ w c i) (hwD : ∀ c i, w c i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
  (X : ι → Set (Torus d (N₀ * L ^ (k - k))))
  (hXreg : ∀ c, box (b0 c) (w c) ∪ shellOut (box (b0 c) (w c)) ⊆ X c)
  (hsep : ∀ c c', c ≠ c' → Disjoint (X c) (box (b0 c') (w c')))
  (hΩ : ∀ c, OverTop (G c) (box (b0 c) (w c) ∪ shellOut (box (b0 c) (w c))))
  (hdata : ∀ c, ∀ x ∈ dataSites (G c), jBlock d L N₀ k k x ∈ X c) (H : BgHyp d L k ϱ a 0)
  (δ : ι → ℝ) (hδ : ∀ c, 0 < δ c)
  (hδc : ∀ c, δ c ≤ psiZeroC11 N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H)

/-- The block set `Z₀(c)`. -/
noncomputable abbrev zb (b0 : ι → Torus d (N₀ * L ^ (k - k))) (w : ι → Fin d → ℕ) (c : ι) :
    Finset (Torus d (N₀ * L ^ (k - k))) := boxFinset (L := L) (N₀ := N₀) (k := k) (b0 c) (w c)

/-- The tube condition `ψ_k ∈ Ψ̃(X ∖ Z₀; δ)` of the component `c`. -/
abbrev FamTube (G : ι → GeneratingSet d L N₀ k ϱ) (b0 : ι → Torus d (N₀ * L ^ (k - k)))
    (w : ι → Fin d → ℕ) (X : ι → Set (Torus d (N₀ * L ^ (k - k)))) (δ : ι → ℝ) (c : ι)
    (ψ : BlockField d L N₀ k N) : Prop :=
  TubeOn (G c) (X c \ box (b0 c) (w c)) (δ c) ψ

/-- The tube of all components. -/
def famTubeSet (G : ι → GeneratingSet d L N₀ k ϱ) (b0 : ι → Torus d (N₀ * L ^ (k - k)))
    (w : ι → Fin d → ℕ) (X : ι → Set (Torus d (N₀ * L ^ (k - k)))) (δ : ι → ℝ) :
    Set (BlockField d L N₀ k N) := {ψ | ∀ c, FamTube N G b0 w X δ c ψ}

theorem measurableSet_imp {α : Type*} [MeasurableSpace α] (P : Prop) {S : Set α}
    (h : P → MeasurableSet S) : MeasurableSet {a | P → a ∈ S} := by
  by_cases hP : P
  · simpa [hP] using h hP
  · simp [hP]

theorem measurableSet_tubeOn (G : GeneratingSet d L N₀ k ϱ) (X : Set (Torus d (N₀ * L ^ (k - k)))) (δ : ℝ) :
    MeasurableSet {ψ : BlockField d L N₀ k N | TubeOn G X δ ψ} := by
  have hmeasv : ∀ (z : Torus d (N₀ * L ^ (k - k))) (i : Fin N), Measurable fun ψ : BlockField d L N₀ k N => ψ z i :=
    fun z i => (measurable_pi_apply i).comp (measurable_pi_apply z)
  have hrn : ∀ (x x' : Torus d (N₀ * L ^ k)), Measurable fun ψ : BlockField d L N₀ k N =>
      rn (fun i => liftR ψ x i - liftR ψ x' i) := by
    intro x x'
    unfold rn
    refine Real.continuous_sqrt.measurable.comp (Finset.measurable_sum _ fun i _ => ?_)
    exact ((hmeasv _ i).sub (hmeasv _ i)).pow_const 2
  have hab : Measurable fun ψ : BlockField d L N₀ k N => fun x : Torus d (N₀ * L ^ k) =>
      |∑ i, ψ (jBlock d L N₀ k k x) i ^ 2 - 1| := by
    refine measurable_pi_iff.2 fun x => ?_
    exact ((Finset.measurable_sum _ fun i _ => (hmeasv _ i).pow_const 2).sub_const 1).abs
  have h1 : MeasurableSet {ψ : BlockField d L N₀ k N | ∀ x x', IsInterfacePair G x x' →
      jBlock d L N₀ k k x ∈ X → jBlock d L N₀ k k x' ∈ X →
        rn (fun i => liftR ψ x i - liftR ψ x' i) < δ} := by
    have : {ψ : BlockField d L N₀ k N | ∀ x x', IsInterfacePair G x x' →
      jBlock d L N₀ k k x ∈ X → jBlock d L N₀ k k x' ∈ X →
        rn (fun i => liftR ψ x i - liftR ψ x' i) < δ} = ⋂ x, ⋂ x', {ψ | IsInterfacePair G x x' →
      jBlock d L N₀ k k x ∈ X → jBlock d L N₀ k k x' ∈ X →
        rn (fun i => liftR ψ x i - liftR ψ x' i) < δ} := by ext; simp
    rw [this]
    exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun x' => measurableSet_imp _ fun _ =>
      measurableSet_imp _ fun _ => measurableSet_imp _ fun _ => measurableSet_lt (hrn x x') measurable_const
  have h2 : MeasurableSet {ψ : BlockField d L N₀ k N | ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X →
      |∑ i, ψ (jBlock d L N₀ k k x) i ^ 2 - 1| < δ} := by
    have : {ψ : BlockField d L N₀ k N | ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X →
      |∑ i, ψ (jBlock d L N₀ k k x) i ^ 2 - 1| < δ} = ⋂ x, {ψ | x ∈ dataSites G → jBlock d L N₀ k k x ∈ X →
      |∑ i, ψ (jBlock d L N₀ k k x) i ^ 2 - 1| < δ} := by ext; simp
    rw [this]
    exact MeasurableSet.iInter fun x => measurableSet_imp _ fun _ => measurableSet_imp _ fun _ =>
      measurableSet_lt ((measurable_pi_apply x).comp hab) measurable_const
  exact h1.inter h2


include hXreg hsep in
theorem fam_disjoint (σ : Finset ι) :
    ∀ c c' : σ, c ≠ c' → Disjoint (zb b0 w c.1) (zb b0 w c'.1) := by
  intro c c' hne
  rw [Finset.disjoint_left]
  intro z hz hz'
  have h1 : z ∈ box (b0 c.1) (w c.1) := mem_boxFinset.1 hz
  have h2 : z ∈ box (b0 c'.1) (w c'.1) := mem_boxFinset.1 hz'
  exact Set.disjoint_left.1 (hsep c.1 c'.1 (fun h => hne (Subtype.ext h))) (hXreg c.1 (Or.inl h1)) h2

/-- The identification of the field space with `(ψ_k↾Z₀(c))_{c∈σ} × ψ_k↾(⋃ Z₀)ᶜ`. -/
noncomputable def famEquiv (σ : Finset ι) :
    BlockField d L N₀ k N ≃ᵐ ((c : σ) → SuppSpace (zb b0 w c.1) N) ×
      (ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ) :=
  decompME (fam_disjoint b0 w X hXreg hsep σ)

/-- The block field with the outside data `y` and zero on the components. -/
noncomputable def famOut (σ : Finset ι) (y : ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ) :
    BlockField d L N₀ k N :=
  (famEquiv N b0 w X hXreg hsep σ).symm (fun _ => 0, y)

theorem famEquiv_fst (σ : Finset ι) (ψ : BlockField d L N₀ k N) (c : σ) :
    (famEquiv N b0 w X hXreg hsep σ ψ).1 c = restrictSupp (zb b0 w c.1) ψ := rfl

theorem famEquiv_snd (σ : Finset ι) (ψ : BlockField d L N₀ k N)
    (j : ZeroOutIdx (fun c : σ => zb b0 w c.1) N) :
    (famEquiv N b0 w X hXreg hsep σ ψ).2 j = ψ j.1.1 j.1.2 := rfl

theorem famOut_apply (σ : Finset ι) (y : ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ)
    (j : ZeroOutIdx (fun c : σ => zb b0 w c.1) N) :
    famOut N b0 w X hXreg hsep σ y j.1.1 j.1.2 = y j := by
  have := famEquiv_snd N b0 w X hXreg hsep σ (famOut N b0 w X hXreg hsep σ y) j
  rw [← this]
  simp [famOut]

theorem famOut_eq (σ : Finset ι) (ψ : BlockField d L N₀ k N) (z : Torus d (N₀ * L ^ (k - k)))
    (hz : ∀ c : σ, z ∉ zb b0 w c.1) :
    famOut N b0 w X hXreg hsep σ (famEquiv N b0 w X hXreg hsep σ ψ).2 z = ψ z := by
  funext i
  have := famOut_apply N b0 w X hXreg hsep σ (famEquiv N b0 w X hXreg hsep σ ψ).2 ⟨⟨z, i⟩, hz⟩
  exact this.trans (famEquiv_snd N b0 w X hXreg hsep σ ψ ⟨⟨z, i⟩, hz⟩)

theorem fam_tube_iff (σ : Finset ι) (ψ : BlockField d L N₀ k N) (c : ι) :
    FamTube N G b0 w X δ c ψ ↔
      FamTube N G b0 w X δ c (famOut N b0 w X hXreg hsep σ (famEquiv N b0 w X hXreg hsep σ ψ).2) := by
  refine tubeOn_congr (G c) (fun z hz => ?_)
  refine (famOut_eq N b0 w X hXreg hsep σ ψ z (fun c' hz' => ?_)).symm
  have h2 : z ∈ box (b0 c'.1) (w c'.1) := mem_boxFinset.1 hz'
  by_cases hc : c'.1 = c
  · subst hc; exact hz.2 h2
  · exact Set.disjoint_left.1 (hsep c c'.1 (Ne.symm hc)) hz.1 h2

theorem famOut_measurable (σ : Finset ι) : Measurable (famOut N b0 w X hXreg hsep σ) :=
  (famEquiv N b0 w X hXreg hsep σ).symm.measurable.comp (measurable_prodMk_left)

theorem measurableSet_famOut_tube (σ : Finset ι) :
    MeasurableSet {y | ∀ c, FamTube N G b0 w X δ c (famOut N b0 w X hXreg hsep σ y)} := by
  have : {y | ∀ c, FamTube N G b0 w X δ c (famOut N b0 w X hXreg hsep σ y)} =
      ⋂ c, (famOut N b0 w X hXreg hsep σ) ⁻¹' {ψ | TubeOn (G c) (X c \ box (b0 c) (w c)) (δ c) ψ} := by
    ext; simp
  rw [this]
  exact MeasurableSet.iInter fun c =>
    famOut_measurable N b0 w X hXreg hsep σ (measurableSet_tubeOn N (G c) _ _)


open Classical in
/-- **The reference density of the component `c` as a function of `(ψ_k↾Z₀(c), ψ_k↾(⋃_{c'∈σ} Z₀(c'))ᶜ)`**
(Definition III.8.1): `rhoZero` for the field with outside data `y` and zero on the components; `0` off the tube
(a null set for `νY`). -/
noncomputable def famRho (σ : Finset ι) (β p0 : ℝ) (c : ι)
    (y : ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ) (u : SuppSpace (zb b0 w c) N) : ℝ :=
  if h : FamTube N G b0 w X δ c (famOut N b0 w X hXreg hsep σ y) then
    rhoZero (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c) h β p0 u
  else 0

theorem famEquiv_preimage (σ : Finset ι) :
    (famEquiv N b0 w X hXreg hsep σ) ⁻¹' (Set.univ ×ˢ {y | ∀ c, FamTube N G b0 w X δ c (famOut N b0 w X hXreg hsep σ y)}) =
      famTubeSet N G b0 w X δ := by
  ext ψ
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, Set.mem_ofPred_eq, famTubeSet]
  exact forall_congr' fun c => (fam_tube_iff N G b0 w X hXreg hsep δ σ ψ c).symm

/-- **The `RDecomp` of the concrete reference densities** (Definition III.8.3): the components `σ ⊆ ι` sent to `R`,
the variables `ψ_k↾Z₀(c)`, the outside variables `ψ_k↾(⋃_{c∈σ} Z₀(c))ᶜ`, and the densities `famRho`; the field space
is `Ψ̃ = ⋂_c Ψ̃(X_c ∖ Z₀(c); δ_c)` with Lebesgue measure. -/
noncomputable def famDecomp (σ : Finset ι) (β p0 : ℝ) :
    RDecomp (volume.restrict (famTubeSet N G b0 w X δ)) where
  ι := σ
  W := fun c => SuppSpace (zb b0 w c.1) N
  μ := fun _ => volume
  Y := ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ
  νY := volume.restrict {y | ∀ c, FamTube N G b0 w X δ c (famOut N b0 w X hXreg hsep σ y)}
  e := famEquiv N b0 w X hXreg hsep σ
  mp := by
    have h := (decompME_mp (N := N) (fam_disjoint b0 w X hXreg hsep σ)).restrict_preimage
      (MeasurableSet.univ.prod (measurableSet_famOut_tube N G b0 w X hXreg hsep δ σ))
    have e1 := famEquiv_preimage N G b0 w X hXreg hsep δ σ
    have e2 := Measure.prod_restrict (μ := (volume : Measure ((c : σ) → SuppSpace (zb b0 w c.1) N)))
      (ν := (volume : Measure (ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ))) Set.univ
      {y | ∀ c, FamTube N G b0 w X δ c (famOut N b0 w X hXreg hsep σ y)}
    rw [Measure.restrict_univ] at e2
    unfold famEquiv at e1 ⊢
    rw [← e2, e1] at h
    exact h
  r := fun c u y => famRho N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0 c.1 y u


local notation "Kc[" c "]" => psiZeroK N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H

theorem famOut_eq_of_mem (σ : Finset ι) (ψ : BlockField d L N₀ k N) (c : ι) {z}
    (hz : z ∈ X c \ box (b0 c) (w c)) :
    famOut N b0 w X hXreg hsep σ (famEquiv N b0 w X hXreg hsep σ ψ).2 z = ψ z := by
  refine famOut_eq N b0 w X hXreg hsep σ ψ z (fun c' hz' => ?_)
  have h2 : z ∈ box (b0 c'.1) (w c'.1) := mem_boxFinset.1 hz'
  by_cases hc : c'.1 = c
  · subst hc; exact hz.2 h2
  · exact Set.disjoint_left.1 (hsep c c'.1 (Ne.symm hc)) hz.1 h2

/-- **Independence (Lemma III.1.5, Definition III.5.1, used in Lemma III.8.4)**: for a field `ψ_k` in the tube,
`ρ_{k,0}(Z)(ψ_k↾Z₀, ψ_k↾𝒵^c_{σ,0})` is the reference density `rhoZero` of `ψ_k` itself; it does not read the
variables `ψ_k↾Z₀(Z')` of the other components. -/
theorem famRho_eq_rhoZero (σ : Finset ι) (β p0 : ℝ) (c : ι) {ψ : BlockField d L N₀ k N}
    (hψ : FamTube N G b0 w X δ c ψ) :
    famRho N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0 c
        (famEquiv N b0 w X hXreg hsep σ ψ).2 =
      rhoZero (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c) hψ β p0 := by
  have hT := (fam_tube_iff N G b0 w X hXreg hsep δ σ ψ c).1 hψ
  funext u
  unfold famRho
  simp only [hT, ↓reduceDIte]
  exact congrFun (rhoZero_congr (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c)
    hψ hT (fun z hz => (famOut_eq_of_mem N b0 w X hXreg hsep σ ψ c hz).symm) β p0) u


theorem famRho_good (σ : Finset ι) {β p0 : ℝ} (hβ : 0 < β) {c : ι}
    (hp0 : 1 ≤ cSix d D Kc[c] * p0)
    (hrad : Kc[c] * δ c + 5 * zeroRadius (cSix d D Kc[c]) β p0 ≤ etaDen d L N D)
    {y : ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ}
    (hy : FamTube N G b0 w X δ c (famOut N b0 w X hXreg hsep σ y)) :
    Integrable (famRho N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0 c y) volume ∧
      0 < ∫ u, famRho N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0 c y u := by
  have hfun : famRho N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0 c y =
      rhoZero (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c) hy β p0 := by
    funext u
    simp only [famRho, hy, ↓reduceDIte]
  rw [hfun]
  obtain ⟨-, hpos, -⟩ := denominator_eq (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H
    (hδ c) (hδc c) hy hβ hp0 hrad
  refine ⟨?_, hpos⟩
  by_contra hni
  have := integral_undef hni
  linarith

/-- **Lemma III.8.4 (normalization) for the concrete reference densities**, conditional on the measurability of the
reference densities `ρ_{k,0}(Z)` jointly in `(ψ_k↾Z₀, ψ_k↾𝒵^c_{σ,0})`: `∫ R[ρ] = ∫ ρ` over `Ψ̃`, with the integrability
of `ρ`, the geometry (`hsep`, the ripe data) and the parameter conditions of `denominator_eq` as the only other
premises.  The independence facts of the source proof are theorems (`famRho_eq_rhoZero`). -/
theorem R_normalization_of_measurable (σ : Finset ι) {β p0 : ℝ} (hβ : 0 < β)
    (hp0 : ∀ c ∈ σ, 1 ≤ cSix d D Kc[c] * p0)
    (hrad : ∀ c ∈ σ, Kc[c] * δ c + 5 * zeroRadius (cSix d D Kc[c]) β p0 ≤ etaDen d L N D)
    {ρ : BlockField d L N₀ k N → ℝ} (hρ : Integrable ρ (volume.restrict (famTubeSet N G b0 w X δ)))
    (hmeas : ∀ c : σ, Measurable (fun p : SuppSpace (zb b0 w c.1) N ×
        (ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ) =>
      famRho N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0 c.1 p.2 p.1)) :
    Integrable (Rop (famDecomp N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0) ρ)
        (volume.restrict (famTubeSet N G b0 w X δ)) ∧
      ∫ ψ, Rop (famDecomp N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0) ρ ψ
          ∂(volume.restrict (famTubeSet N G b0 w X δ)) =
        ∫ ψ, ρ ψ ∂(volume.restrict (famTubeSet N G b0 w X δ)) := by
  have hS := measurableSet_famOut_tube N G b0 w X hXreg hsep δ σ
  refine R_normalization_ae (famDecomp N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0) hρ
    hmeas ?_ ?_ ?_
  · intro c u y
    show 0 ≤ famRho N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0 c.1 y u
    unfold famRho
    split_ifs
    · unfold rhoZero; exact rhoZeroWith_nonneg _ _ _ _ _ _ _ _ _
    · exact le_rfl
  · refine (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun y hy c => ?_)
    exact (famRho_good N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ hβ (hp0 c.1 c.2)
      (hrad c.1 c.2) (hy c.1)).1
  · refine (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun y hy c => ?_)
    exact (famRho_good N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ hβ (hp0 c.1 c.2)
      (hrad c.1 c.2) (hy c.1)).2


/-- **Lemma III.8.4 for `ρ' = Σ_{(𝔸,σ)} R[ρ(𝔸,σ)]`**, the terms indexed by the subsets `σ_t ⊆ ι` of ripe components
sent to `R`, conditional on measurability as in `R_normalization_of_measurable`. -/
theorem R_normalization_sum_of_measurable {T : Type} [Fintype T] (σ : T → Finset ι) {β p0 : ℝ} (hβ : 0 < β)
    (hp0 : ∀ t, ∀ c ∈ σ t, 1 ≤ cSix d D Kc[c] * p0)
    (hrad : ∀ t, ∀ c ∈ σ t, Kc[c] * δ c + 5 * zeroRadius (cSix d D Kc[c]) β p0 ≤ etaDen d L N D)
    {ρ : T → BlockField d L N₀ k N → ℝ}
    (hρ : ∀ t, Integrable (ρ t) (volume.restrict (famTubeSet N G b0 w X δ)))
    (hmeas : ∀ t, ∀ c : σ t, Measurable (fun p : SuppSpace (zb b0 w c.1) N ×
        (ZeroOutIdx (fun c : σ t => zb b0 w c.1) N → ℝ) =>
      famRho N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc (σ t) β p0 c.1 p.2 p.1)) :
    Integrable (RopSum (fun t => famDecomp N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc (σ t) β p0) ρ)
        (volume.restrict (famTubeSet N G b0 w X δ)) ∧
      ∫ ψ, RopSum (fun t => famDecomp N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc (σ t) β p0) ρ ψ
          ∂(volume.restrict (famTubeSet N G b0 w X δ)) =
        ∫ ψ, (∑ t, ρ t ψ) ∂(volume.restrict (famTubeSet N G b0 w X δ)) := by
  refine R_normalization_sum_ae (fun t => famDecomp N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc
    (σ t) β p0) hρ hmeas ?_ ?_ ?_
  · intro t c u y
    show 0 ≤ famRho N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc (σ t) β p0 c.1 y u
    unfold famRho
    split_ifs
    · unfold rhoZero; exact rhoZeroWith_nonneg _ _ _ _ _ _ _ _ _
    · exact le_rfl
  · intro t
    refine (ae_restrict_iff' (measurableSet_famOut_tube N G b0 w X hXreg hsep δ (σ t))).2
      (Filter.Eventually.of_forall fun y hy c => ?_)
    exact (famRho_good N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc (σ t) hβ (hp0 t c.1 c.2)
      (hrad t c.1 c.2) (hy c.1)).1
  · intro t
    refine (ae_restrict_iff' (measurableSet_famOut_tube N G b0 w X hXreg hsep δ (σ t))).2
      (Filter.Eventually.of_forall fun y hy c => ?_)
    exact (famRho_good N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc (σ t) hβ (hp0 t c.1 c.2)
      (hrad t c.1 c.2) (hy c.1)).2

/-- **The operation `R` with the concrete reference densities** (P7 (1.6)): at a field `ψ_k` in the tube,
`R[ρ](ψ_k) = ∏_Z ρ_{k,0}(Z)(ψ_k↾Z₀) · (∫ dψ_k↾𝒵_{σ,0} ρ) / ∏_Z ∫ dψ_k↾Z₀ ρ_{k,0}(Z)` with `ρ_{k,0}(Z)` the
reference density `rhoZero` of `ψ_k` itself. -/
theorem Rop_famDecomp_apply (σ : Finset ι) (β p0 : ℝ) (ρ : BlockField d L N₀ k N → ℝ)
    {ψ : BlockField d L N₀ k N} (hψ : ψ ∈ famTubeSet N G b0 w X δ) :
    Rop (famDecomp N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0) ρ ψ =
      (∏ c : σ, rhoZero (G c.1) a hd hk (b0 c.1) (w c.1) (hw1 c.1) (hwD c.1) hm (hXreg c.1) (hΩ c.1) (hdata c.1) H
          (hδ c.1) (hδc c.1) (hψ c.1) β p0 (restrictSupp (zb b0 w c.1) ψ)) *
        ((∫ x, ρ ((famEquiv N b0 w X hXreg hsep σ).symm (x, (famEquiv N b0 w X hXreg hsep σ ψ).2))
            ∂(Measure.pi fun c : σ => (volume : Measure (SuppSpace (zb b0 w c.1) N)))) /
          ∏ c : σ, ∫ u, rhoZero (G c.1) a hd hk (b0 c.1) (w c.1) (hw1 c.1) (hwD c.1) hm (hXreg c.1) (hΩ c.1)
            (hdata c.1) H (hδ c.1) (hδc c.1) (hψ c.1) β p0 u) := by
  have hr : ∀ c : σ, famRho N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0 c.1
      (famEquiv N b0 w X hXreg hsep σ ψ).2 =
      rhoZero (G c.1) a hd hk (b0 c.1) (w c.1) (hw1 c.1) (hwD c.1) hm (hXreg c.1) (hΩ c.1) (hdata c.1) H
        (hδ c.1) (hδc c.1) (hψ c.1) β p0 := fun c =>
    famRho_eq_rhoZero N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0 c.1 (hψ c.1)
  have key : Rop (famDecomp N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0) ρ ψ =
      (∏ c : σ, famRho N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0 c.1
        (famEquiv N b0 w X hXreg hsep σ ψ).2 (restrictSupp (zb b0 w c.1) ψ)) *
        ((∫ x, ρ ((famEquiv N b0 w X hXreg hsep σ).symm (x, (famEquiv N b0 w X hXreg hsep σ ψ).2))
            ∂(Measure.pi fun c : σ => (volume : Measure (SuppSpace (zb b0 w c.1) N)))) /
          ∏ c : σ, ∫ u, famRho N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0 c.1
            (famEquiv N b0 w X hXreg hsep σ ψ).2 u) := rfl
  rw [key]
  simp only [hr]

include hsep in
/-- **Lemma III.8.4, independence of the denominators**: `∫ dψ_k↾Z₀ ρ_{k,0}(Z)` does not depend on the variables of
the other components: the reference density `ρ_{k,0}(Z)` of `ψ_k` and of `ψ'_k` coincide when `ψ_k, ψ'_k` agree off
`⋃_{Z'≠Z} Z₀(Z')`. -/
theorem rhoZero_indep_other_components (c : ι) {ψ ψ' : BlockField d L N₀ k N}
    (hψ : FamTube N G b0 w X δ c ψ) (hψ' : FamTube N G b0 w X δ c ψ')
    (h : ∀ z, (∀ c', c' ≠ c → z ∉ box (b0 c') (w c')) → ψ z = ψ' z) (β p0 : ℝ) :
    rhoZero (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c) hψ' β p0 =
      rhoZero (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c) hψ β p0 :=
  rhoZero_congr (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c)
    hψ hψ' (fun z hz => h z fun c' hne hz' => Set.disjoint_left.1 (hsep c c' (Ne.symm hne)) hz.1 hz') β p0

include hsep in
theorem integral_rhoZero_indep_other_components (c : ι) {ψ ψ' : BlockField d L N₀ k N}
    (hψ : FamTube N G b0 w X δ c ψ) (hψ' : FamTube N G b0 w X δ c ψ')
    (h : ∀ z, (∀ c', c' ≠ c → z ∉ box (b0 c') (w c')) → ψ z = ψ' z) (β p0 : ℝ) :
    ∫ u, rhoZero (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c) hψ' β p0 u =
      ∫ u, rhoZero (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c) hψ β p0 u := by
  rw [rhoZero_indep_other_components N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc c hψ hψ' h β p0]


theorem zeroRadius_pos_of_params {β p0 : ℝ} (hβ : 0 < β) (c : ι) (hp0 : 1 ≤ cSix d D Kc[c] * p0) :
    0 < zeroRadius (cSix d D Kc[c]) β p0 := by
  have hK : 0 < Kc[c] := psiZeroK_pos N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H
  have hd0 : 0 < d := by omega
  have hD1 : 1 ≤ D := (hw1 c ⟨0, hd0⟩).trans (hwD c _)
  have hC6 : 0 < cSix d D Kc[c] := by
    unfold cSix
    have : (0 : ℝ) < d := by exact_mod_cast hd0
    have : (0 : ℝ) < D := by exact_mod_cast hD1
    positivity
  have hp0pos : 0 < p0 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hC6.le h]
  unfold zeroRadius
  positivity

/-- **Non-degeneracy**: the reference density `ρ_{k,0}(Z)` is not constant in `ψ_k↾Z₀`: it is positive at the centre
`ψ⁰_k↾Z₀` of the cutoff and vanishes outside the cutoff. -/
theorem rhoZero_nonconstant {β p0 : ℝ} (hβ : 0 < β) (c : ι) (hp0 : 1 ≤ cSix d D Kc[c] * p0)
    {ψ : BlockField d L N₀ k N} (hψ : FamTube N G b0 w X δ c ψ) :
    ∃ u u' : SuppSpace (zb b0 w c) N,
      rhoZero (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c) hψ β p0 u ≠
        rhoZero (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c) hψ β p0 u' := by
  have hr := zeroRadius_pos_of_params N G a hd hk b0 w hw1 hwD hm X hXreg hΩ hdata H hβ c hp0
  set r := zeroRadius (cSix d D Kc[c]) β p0 with hrdef
  set ψ0 := psiZero N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c) hψ
    with hψ0
  have hd0 : 0 < d := by omega
  have hz0 : b0 c ∈ zb b0 w c := mem_boxFinset.2 (fun i => ⟨0, Nat.lt_of_lt_of_le one_pos (hw1 c i), by simp⟩)
  let z0 : ↥(zb b0 w c) := ⟨b0 c, hz0⟩
  let i0 : Fin N := ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩
  refine ⟨restrictSupp (zb b0 w c) ψ0, restrictSupp (zb b0 w c) ψ0 + r • EuclideanSpace.single (z0, i0) (1 : ℝ), ?_⟩
  have h1 : ZeroCutoff ψ0 r (restrictSupp (zb b0 w c) ψ0) := by
    intro z
    have : (fun i => restrictSupp (zb b0 w c) ψ0 (z, i) - ψ0 (z : Torus d (N₀ * L ^ (k - k))) i) = fun _ => 0 := by
      funext i; simp [restrictSupp]
    rw [this]
    unfold rn
    simpa using hr
  have h2 : ¬ ZeroCutoff ψ0 r (restrictSupp (zb b0 w c) ψ0 + r • EuclideanSpace.single (z0, i0) (1 : ℝ)) := by
    intro h
    have := h z0
    have e : (fun i => (restrictSupp (zb b0 w c) ψ0 + r • EuclideanSpace.single (z0, i0) (1 : ℝ)) (z0, i) -
        ψ0 (z0 : Torus d (N₀ * L ^ (k - k))) i) = fun i => r * (if i = i0 then 1 else 0) := by
      funext i
      simp [restrictSupp]
    rw [e] at this
    unfold rn at this
    have e2 : ∑ i : Fin N, (r * (if i = i0 then (1 : ℝ) else 0)) ^ 2 = r ^ 2 := by
      simp [Finset.sum_ite_eq']
    rw [e2, Real.sqrt_sq hr.le] at this
    exact lt_irrefl _ this
  intro hEq
  have hpos : 0 < rhoZero (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c) hψ β p0
      (restrictSupp (zb b0 w c) ψ0) := by
    unfold rhoZero
    rw [rhoZeroWith_of_cutoff _ _ _ _ _ _ _ _ _ h1]
    exact Real.exp_pos _
  have hzero : rhoZero (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c) hψ β p0
      (restrictSupp (zb b0 w c) ψ0 + r • EuclideanSpace.single (z0, i0) (1 : ℝ)) = 0 := by
    unfold rhoZero
    exact rhoZeroWith_eq_zero _ _ _ _ _ _ _ _ _ h2
  rw [hzero] at hEq
  exact hpos.ne' hEq

/-- The `RDecomp` of the concrete densities is non-degenerate: its component set contains `c` and its reference
density is not constant in the variable of `c` (at the outside data of any field of the tube). -/
theorem famDecomp_nondegenerate (σ : Finset ι) {β p0 : ℝ} (hβ : 0 < β) (c : σ)
    (hp0 : 1 ≤ cSix d D Kc[c.1] * p0) {ψ : BlockField d L N₀ k N} (hψ : FamTube N G b0 w X δ c.1 ψ) :
    ∃ y : (famDecomp N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0).Y,
      ∃ u u' : (famDecomp N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0).W c,
        (famDecomp N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0).r c u y ≠
          (famDecomp N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0).r c u' y := by
  obtain ⟨u, u', hne⟩ := rhoZero_nonconstant N G a hd hk b0 w hw1 hwD hm X hXreg hΩ hdata H δ hδ hδc hβ c.1 hp0 hψ
  refine ⟨(famEquiv N b0 w X hXreg hsep σ ψ).2, u, u', ?_⟩
  have hf := famRho_eq_rhoZero N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0 c.1 hψ
  show famRho N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0 c.1
      (famEquiv N b0 w X hXreg hsep σ ψ).2 u ≠ famRho N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0 c.1
      (famEquiv N b0 w X hXreg hsep σ ψ).2 u'
  rw [hf]
  exact hne

end Fam







section One

variable (N : ℕ) {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] [NeZero N] {ϱ : ℝ}
  (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k)
  (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
  (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
  {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
  (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
  (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0)
  {δ : ℝ} (hδ : 0 < δ) (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)

/-- **Lemma III.8.1/III.8.3 for one ripe component** (`𝒵_σ = {Z}`): the `RDecomp` whose component set is a point,
whose variable space is `ψ_k↾Z₀` and whose reference density is `rhoZero`. -/
noncomputable def oneDecomp (β p0 : ℝ) :
    RDecomp (volume.restrict (famTubeSet N (fun _ : Unit => G) (fun _ => b0) (fun _ => w) (fun _ => X)
      (fun _ => δ))) :=
  famDecomp N (fun _ : Unit => G) a hd hk (fun _ => b0) (fun _ => w) (fun _ => hw1) (fun _ => hwD) hm
    (fun _ => X) (fun _ => hXreg) (fun c c' h => absurd (Subsingleton.elim c c') h) (fun _ => hΩ) (fun _ => hdata) H
    (fun _ => δ) (fun _ => hδ) (fun _ => hδc) Finset.univ β p0

/-- The reference density `ρ_{k,0}(Z)(ψ_k↾Z₀; ψ_k↾Z₀ᶜ)` of the single component. -/
noncomputable def oneRho (β p0 : ℝ) (y : ZeroOutIdx (fun c : (Finset.univ : Finset Unit) =>
    zb (fun _ : Unit => b0) (fun _ => w) c.1) N → ℝ) (u : SuppSpace (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) N) :
    ℝ :=
  famRho N (fun _ : Unit => G) a hd hk (fun _ => b0) (fun _ => w) (fun _ => hw1) (fun _ => hwD) hm
    (fun _ => X) (fun _ => hXreg) (fun c c' h => absurd (Subsingleton.elim c c') h) (fun _ => hΩ) (fun _ => hdata) H
    (fun _ => δ) (fun _ => hδ) (fun _ => hδc) Finset.univ β p0 () y u

theorem mem_famTubeSet_unit (ψ : BlockField d L N₀ k N) :
    ψ ∈ famTubeSet N (fun _ : Unit => G) (fun _ => b0) (fun _ => w) (fun _ => X) (fun _ => δ) ↔
      TubeOn G (X \ box b0 w) δ ψ :=
  ⟨fun h => h (), fun h _ => h⟩

/-- **Lemma III.8.4 for one component** (normalization), conditional on the joint measurability of `ρ_{k,0}(Z)` in
`(ψ_k↾Z₀, ψ_k↾Z₀ᶜ)`. -/
theorem R_normalization_one_of_measurable {β p0 : ℝ} (hβ : 0 < β)
    (hp0 : 1 ≤ cSix d D (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) * p0)
    (hrad : psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H * δ +
      5 * zeroRadius (cSix d D (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)) β p0 ≤ etaDen d L N D)
    {ρ : BlockField d L N₀ k N → ℝ}
    (hρ : Integrable ρ (volume.restrict (famTubeSet N (fun _ : Unit => G) (fun _ => b0) (fun _ => w)
      (fun _ => X) (fun _ => δ))))
    (hmeas : Measurable (fun p : SuppSpace (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) N ×
        (ZeroOutIdx (fun c : (Finset.univ : Finset Unit) =>
          zb (fun _ : Unit => b0) (fun _ => w) c.1) N → ℝ) => oneRho N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H
            hδ hδc β p0 p.2 p.1)) :
    Integrable (Rop (oneDecomp N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc β p0) ρ)
        (volume.restrict (famTubeSet N (fun _ : Unit => G) (fun _ => b0) (fun _ => w) (fun _ => X)
          (fun _ => δ))) ∧
      ∫ ψ, Rop (oneDecomp N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc β p0) ρ ψ
          ∂(volume.restrict (famTubeSet N (fun _ : Unit => G) (fun _ => b0) (fun _ => w) (fun _ => X)
            (fun _ => δ))) =
        ∫ ψ, ρ ψ ∂(volume.restrict (famTubeSet N (fun _ : Unit => G) (fun _ => b0) (fun _ => w) (fun _ => X)
          (fun _ => δ))) :=
  R_normalization_of_measurable N (fun _ : Unit => G) a hd hk (fun _ => b0) (fun _ => w) (fun _ => hw1)
    (fun _ => hwD) hm (fun _ => X) (fun _ => hXreg) (fun c c' h => absurd (Subsingleton.elim c c') h)
    (fun _ => hΩ) (fun _ => hdata) H (fun _ => δ) (fun _ => hδ) (fun _ => hδc) Finset.univ hβ
    (fun _ _ => hp0) (fun _ _ => hrad) hρ (fun c => by obtain ⟨⟨⟩, hc⟩ := c; exact hmeas)

/-- **`rdecomp_one_nondegenerate`**: `RDecomp` has a non-degenerate witness: the component set of `oneDecomp` is a
point and its reference density is not constant (at the outside data of any field `ψ_k` of the tube). -/
theorem rdecomp_one_nondegenerate {β p0 : ℝ} (hβ : 0 < β)
    (hp0 : 1 ≤ cSix d D (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) * p0)
    {ψ : BlockField d L N₀ k N} (hψ : TubeOn G (X \ box b0 w) δ ψ) :
    Nonempty (oneDecomp N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc β p0).ι ∧
      ∃ y : (oneDecomp N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc β p0).Y,
        ∃ u u' : (oneDecomp N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc β p0).W ⟨(), Finset.mem_univ _⟩,
          (oneDecomp N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc β p0).r ⟨(), Finset.mem_univ _⟩ u y ≠
            (oneDecomp N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc β p0).r ⟨(), Finset.mem_univ _⟩ u' y :=
  ⟨⟨⟨(), Finset.mem_univ _⟩⟩,
    famDecomp_nondegenerate N (fun _ : Unit => G) a hd hk (fun _ => b0) (fun _ => w) (fun _ => hw1)
      (fun _ => hwD) hm (fun _ => X) (fun _ => hXreg) (fun c c' h => absurd (Subsingleton.elim c c') h)
      (fun _ => hΩ) (fun _ => hdata) H (fun _ => δ) (fun _ => hδ) (fun _ => hδc) Finset.univ hβ
      ⟨(), Finset.mem_univ _⟩ hp0 (ψ := ψ) hψ⟩

end One


end Balaban.LargeField
