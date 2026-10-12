module

public import Balaban.LargeField.Base.BaseMarkedFootprint
public import Balaban.LargeField.Base.BaseMarked
public import Balaban.LargeField.Base.BaseSmallField
public import Balaban.LargeField.Base.BaseS5
public import Balaban.LargeField.Base.Prop279Counter
public import Balaban.Polymer.MarkedCubes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Proposition II.7.9, conditional form (BASE-KERNEL-4 §4, Proposition 4.1)

LF-RECONSTRUCTION Proposition II.7.9 (the base small-field proposition) is **not** proved: no theorem
in the sources supplies the model-specific estimates for every base record
(`notes/phase1/BASE-KERNEL-4.md`).  This file formalizes the conditional form of BASE-KERNEL-4 with
the missing inputs made explicit:

* `Prop279Cut` (CT), `Prop279Cut.deletes`: the support-local cutoff transfer (Lemma 2.2) from the
  landed `chiPrimeZero_eq_one_of_margins`, `baseOldFactor_eq_deleted`, `baseDeleted_indep`;
  `baseCutoffMargins_of_convenient`, `chartRadius_le_quarter`, `sqrtNu_chartRadius_le_quarter` are the
  numerics (2.6) and (2.8);
* `Prop279Marks` (PE), `Prop279Marks.remainder_half`: the marked-cube data and the half budget (4.3),
  from the landed `markSum_add_det_half`;
* `Prop279Phys` (PHYS): the physical `BaseSmallFieldInput` with the source-strength `b_0` bound
  (4.1b), the `Ω_1 ∩ V` support of `b_0` and `BaseS5`;
* `Prop279Input` bundles the three; `prop279Input_nonempty` is its inhabitation;
* `prop279_of_input` : `Prop279Conclusion`.  The name `prop279` is reserved for the unconditional
  form.

Not in the conclusion: the one-step bound (S2) (Lemma II.7.8 integrated), the I-7 solution (RG), the
boundary terms with (D7), and the equality with `ρ_1` (see `Prop279Conclusion`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Background

/-! ### Numerics of (CT): the sufficient margins (2.6) and the chart radius (2.8) -/

section CTNumerics

variable {d N : ℕ} (nn : ℕ → ℕ) (L M K : ℕ) [∀ k, NeZero (nn k)] [NeZero M] [NeZero L]

/-- **BASE-KERNEL-4 (2.6) implies (2.4).**  The convenient margins `|θ - Qe| < 3δ₀/2`,
`|e_z - e_w| < δ₀/2`, `√ν|e_z - h| < δ₀/2` with `r ≤ δ₀/4` and `√ν r ≤ δ₀/4` give the three strict
margins of `BaseCutoffMargins`. -/
theorem baseCutoffMargins_of_convenient {regimeB : Prop} {ν δ₀ r : ℝ} {h : Fin N → ℝ}
    {P : Set (Torus d (nn 1))} {Dplus : Set (Torus d (M * nn K * L ^ K))}
    {φ e : Torus d (M * nn K * L ^ K) → Fin N → ℝ}
    {θ : Torus d (M * nn K * L ^ (K - 1)) → Fin N → ℝ}
    (hδ : 0 < δ₀) (hr : r ≤ δ₀ / 4) (hνr : Real.sqrt ν * r ≤ δ₀ / 4)
    (unit : ∀ c ∈ baseJPlus nn L M K regimeB P Dplus, ∀ x ∈ baseFootprint nn L M K regimeB c,
      ∑ i, e x i ^ 2 = 1)
    (close : ∀ c ∈ baseJPlus nn L M K regimeB P Dplus, ∀ x ∈ baseFootprint nn L M K regimeB c,
      rn (fun i => φ x i - e x i) ≤ r)
    (block : ∀ c ∈ baseJPlus nn L M K regimeB P Dplus, ∀ y : Torus d (M * nn K * L ^ (K - 1)),
      blockMap M (nn 1) y = c →
        rn (fun i => θ y i - spinAverage nn L M K e y i) < 3 / 2 * δ₀)
    (bond : ∀ c ∈ baseJPlus nn L M K regimeB P Dplus, ∀ (x : Torus d (M * nn K * L ^ K))
      (μ : Fin d), (cubeMap nn L M K 1 x = c ∨ cubeMap nn L M K 1 (x + Pi.single μ 1) = c) →
        rn (fun i => e (x + Pi.single μ 1) i - e x i) < δ₀ / 2)
    (site : ∀ c ∈ baseJPlus nn L M K regimeB P Dplus, regimeB →
      ∀ x : Torus d (M * nn K * L ^ K), cubeMap nn L M K 1 x = c →
        Real.sqrt ν * rn (fun i => e x i - h i) < δ₀ / 2) :
    BaseCutoffMargins nn L M K regimeB ν δ₀ r h P Dplus φ e θ where
  unit := unit
  close := close
  block := fun c hc y hy => by linarith [block c hc y hy]
  bond := fun c hc x μ hx => by linarith [bond c hc x μ hx]
  site := fun c hc hB x hx => by linarith [site c hc hB x hx, hνr, Real.sqrt_nonneg ν]

/-- **BASE-KERNEL-4 (2.8): the chart radius is a quarter of `δ₀`.**  If
`r ≤ 2 B₅ √a (A₁/A₀) δ₀` with `A₀ = 4 K₂ B₅ A₁` and `K₂ ≥ 2√a`, then `r ≤ δ₀/4`. -/
theorem chartRadius_le_quarter {a B5 A0 A1 K2 δ₀ r : ℝ} (hδ : 0 < δ₀) (hB5 : 0 < B5)
    (hA1 : 0 < A1) (hK2 : 0 < K2) (hA0 : A0 = 4 * K2 * B5 * A1) (hK : 2 * Real.sqrt a ≤ K2)
    (hr : r ≤ 2 * B5 * Real.sqrt a * (A1 / A0) * δ₀) : r ≤ δ₀ / 4 := by
  have e : 2 * B5 * Real.sqrt a * (A1 / A0) = Real.sqrt a / (2 * K2) := by
    rw [hA0]; field_simp; ring
  rw [e] at hr
  have h1 : Real.sqrt a / (2 * K2) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  nlinarith

/-- **The same with the mass:** for `ν > 1` the requirement is `K₂ ≥ 2√(aν)`, and then
`√ν r ≤ δ₀/4`. -/
theorem sqrtNu_chartRadius_le_quarter {a ν B5 A0 A1 K2 δ₀ r : ℝ} (hδ : 0 < δ₀) (hB5 : 0 < B5)
    (hA1 : 0 < A1) (hK2 : 0 < K2) (ha : 0 ≤ a) (hA0 : A0 = 4 * K2 * B5 * A1)
    (hK : 2 * Real.sqrt (a * ν) ≤ K2)
    (hr : r ≤ 2 * B5 * Real.sqrt a * (A1 / A0) * δ₀) : Real.sqrt ν * r ≤ δ₀ / 4 := by
  have e : 2 * B5 * Real.sqrt a * (A1 / A0) = Real.sqrt a / (2 * K2) := by
    rw [hA0]; field_simp; ring
  rw [e] at hr
  have hs : Real.sqrt (a * ν) = Real.sqrt a * Real.sqrt ν := Real.sqrt_mul ha ν
  have h1 : Real.sqrt ν * (Real.sqrt a / (2 * K2)) ≤ 1 / 4 := by
    have : Real.sqrt ν * (Real.sqrt a / (2 * K2)) = Real.sqrt a * Real.sqrt ν / (2 * K2) := by
      ring
    rw [this, div_le_iff₀ (by positivity)]; rw [hs] at hK; linarith
  have hsn := Real.sqrt_nonneg ν
  calc Real.sqrt ν * r ≤ Real.sqrt ν * (Real.sqrt a / (2 * K2) * δ₀) :=
        mul_le_mul_of_nonneg_left hr hsn
    _ = Real.sqrt ν * (Real.sqrt a / (2 * K2)) * δ₀ := by ring
    _ ≤ 1 / 4 * δ₀ := mul_le_mul_of_nonneg_right h1 hδ.le
    _ = δ₀ / 4 := by ring

end CTNumerics


/-! ### (CT): the cutoff-margin input -/

section Cut

variable {d N : ℕ} (nn : ℕ → ℕ) (L M K : ℕ) [∀ k, NeZero (nn k)] [NeZero M] [NeZero L]

/-- The integrated fine sites `D₊ = Ω''₁ ∩ Z'` of a component `Z'` (a set of cubes of `𝕋_1`) of the
base record `br`. -/
def baseDplus {Rk : ℝ} (br : BaseRecord d L (nn 1) Rk) (Zc : Set (Torus d (nn 1))) :
    Set (Torus d (M * nn K * L ^ K)) :=
  {x | cubeMap nn L M K 1 x ∈ br.OmegaDD ∧ cubeMap nn L M K 1 x ∈ Zc}

/-- **Input (CT)** of BASE-KERNEL-4 Proposition 4.1 (BASE-KERNEL-2 Lemma 2.1, BASE-KERNEL-3 §2,
BASE-KERNEL-4 Lemma 2.2, (2.4)-(2.6)): the real chart and the retained output restrictions give a
real unit background `bg` such that, on the support domain `Dom` of the integrand (the
configurations `(φ, θ)` satisfying the fluctuation cutoff and the retained output cutoffs), the
three strict margins (2.4) hold on the full footprint of every cube of `𝒥₊`, including the bonds
across `∂Ω''₁`, with the chart radius `r` of (2.8).  `Dom` is nonempty.  The record-wide
implication from `BaseRecord` alone is false (`baseMargin_counterexample`). -/
structure Prop279Cut (regimeB : Prop) (ν δ₀ r : ℝ) (h : Fin N → ℝ) {Rk : ℝ}
    (br : BaseRecord d L (nn 1) Rk) (Zc : Set (Torus d (nn 1))) where
  /-- the real unit background determined by the configuration -/
  bg : BaseCfg d N nn L M K → Torus d (M * nn K * L ^ K) → Fin N → ℝ
  /-- the support domain of the integrand -/
  Dom : Set (BaseCfg d N nn L M K)
  Dom_nonempty : Dom.Nonempty
  margins : ∀ p ∈ Dom, BaseCutoffMargins nn L M K regimeB ν δ₀ r h br.P
    (baseDplus nn L M K br Zc) p.1 (bg p) p.2

variable {nn L M K}

/-- **`Prop279Cut` is inhabited** (rule 10), for every unit external field `h`: the constant unit
background `e ≡ h` with `φ = e` and `θ = Qe` satisfies all margins with `r = 0`. -/
theorem prop279Cut_nonempty (regimeB : Prop) (ν : ℝ) {δ₀ : ℝ} (hδ : 0 < δ₀) (h : Fin N → ℝ)
    (hh : ∑ i, h i ^ 2 = 1) {Rk : ℝ} (br : BaseRecord d L (nn 1) Rk) (Zc : Set (Torus d (nn 1))) :
    Nonempty (Prop279Cut nn L M K regimeB ν δ₀ 0 h br Zc) := by
  have hz : ∀ a : Fin N → ℝ, rn (fun i => a i - a i) = 0 := fun a => by simp [rn]
  refine ⟨fun _ _ => h, ({((fun _ => h : Torus d (M * nn K * L ^ K) → Fin N → ℝ),
    (fun y => spinAverage nn L M K (fun _ => h) y))} :
      Set (BaseCfg d N nn L M K)), ⟨_, rfl⟩, ?_⟩
  intro p hp
  rw [Set.mem_singleton_iff.1 hp]
  exact
    { unit := fun _ _ _ _ => hh
      close := fun _ _ _ _ => by rw [hz]
      block := fun _ _ y _ => by rw [hz]; linarith
      bond := fun _ _ x μ _ => by rw [hz]; linarith
      site := fun _ _ _ _ _ => by rw [hz, mul_zero]; linarith }

/-- The statement of Lemma 2.2: on the support domain, the old base factor (2.1) equals the factor
with all good cubes of `𝒥₊` deleted, and the deleted factor does not read the integrated spins. -/
def Prop279Cut.Deletes {regimeB : Prop} {ν δ₀ r : ℝ} {h : Fin N → ℝ} {Rk : ℝ}
    {br : BaseRecord d L (nn 1) Rk} {Zc : Set (Torus d (nn 1))}
    (C : Prop279Cut nn L M K regimeB ν δ₀ r h br Zc) : Prop :=
  ∀ p ∈ C.Dom,
    baseOldFactor regimeB ν δ₀ h (Set.toFinite br.P).toFinset p =
      baseDeletedFactor regimeB ν δ₀ h (Set.toFinite br.P).toFinset
        (baseDplus nn L M K br Zc) p ∧
    ∀ φ' : Torus d (M * nn K * L ^ K) → Fin N → ℝ,
      (∀ x ∉ baseDplus nn L M K br Zc, p.1 x = φ' x) →
      baseDeletedFactor regimeB ν δ₀ h (Set.toFinite br.P).toFinset
          (baseDplus nn L M K br Zc) (φ', p.2) =
        baseDeletedFactor regimeB ν δ₀ h (Set.toFinite br.P).toFinset
          (baseDplus nn L M K br Zc) p

/-- **Consequence of (CT)** (BASE-KERNEL-4 Lemma 2.2): `Prop279Cut.Deletes`. -/
theorem Prop279Cut.deletes {regimeB : Prop} {ν δ₀ r : ℝ} {h : Fin N → ℝ} {Rk : ℝ}
    {br : BaseRecord d L (nn 1) Rk} {Zc : Set (Torus d (nn 1))}
    (C : Prop279Cut nn L M K regimeB ν δ₀ r h br Zc)
    (hnn : ∀ i, i < K → nn i = L * nn (i + 1)) (hK : 1 ≤ K) (hν : 0 ≤ ν) : C.Deletes := by
  intro p hp
  have hP : (((Set.toFinite br.P).toFinset : Finset (Torus d (nn 1))) : Set (Torus d (nn 1))) =
      br.P := Set.Finite.coe_toFinset _
  refine ⟨?_, fun φ' hφ' => ?_⟩
  · have hm := C.margins p hp
    have hm' : BaseCutoffMargins nn L M K regimeB ν δ₀ r h
        (((Set.toFinite br.P).toFinset : Finset (Torus d (nn 1))) : Set (Torus d (nn 1)))
        (baseDplus nn L M K br Zc) p.1 (C.bg p) p.2 := by rw [hP]; exact hm
    exact baseOldFactor_eq_deleted hK hν _ hm'
  · have hD : ∀ x ∈ baseDplus nn L M K br Zc, cubeMap nn L M K 1 x ∈ br.Omega :=
      fun x hx => cubeMap_mem_Omega_of_DD br hx.1
    have := baseDeleted_indep (regimeB := regimeB) hnn hK ν δ₀ h br
      ((Set.toFinite br.P).toFinset) hP hD p.1 φ' p.2 hφ'
    exact this.symm

end Cut


/-! ### (PE): the marked-cube input and the half budget -/

open MeasureTheory Balaban.Localization Balaban.Polymer Balaban.Fluctuation

section Marks

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (Balaban.Localization.CTorus d L N₁ m₁ K)}

local notation "𝔅" => Balaban.Fluctuation.CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

/-- **Input (PE)** of BASE-KERNEL-4 Proposition 4.1 (BASE-KERNEL-3 §3, Lemma 3.1, Corollary 3.2;
P5 (3.9), Proposition 3.2 at `k = 0`; P6 Lemma 4.2; FLUCTUATION Theorem 3.4): the first small-field
integral, after (CT) and (LC), is a product-reference polymer integral: product probability
measures `μ_b`, labels `Lab`, measurable local activities `A` with the entropy bound, marks `G_y`
(measurable, `DepOn` the blocks of the mark) with `|G_y| ≤ C_m β₀^{-m-3/2} e^{-κ_G 𝗱(y)}` (4.1),
a determinant coefficient `det(Y)` with `|det(Y)| ≤ C_det β₀^{-m-3/2} e^{-κ_b d_Ext(Y)}` on every
domain including whole-torus ones, and the remainder coefficient `ℛ^{(1)}_m(Y) = R(Y) + det(Y)`
(the identification with P5 (3.9) and the modular-size bridge are the content of `Rm_eq`).
The fields after `A, G` are the numerical premises (3.2) of `marked_cubes_explicit` and (4.2). -/
structure Prop279Marks (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω) (m : ℕ) where
  /-- the finite label type -/
  Lb : Type
  [fin : Fintype Lb]
  /-- the block spaces of the product reference measure -/
  Ωb : 𝔅 → Type
  [meas : ∀ b, MeasurableSpace (Ωb b)]
  /-- the product reference measure -/
  μ : ∀ b, Measure (Ωb b)
  [prob : ∀ b, IsProbabilityMeasure (μ b)]
  /-- the labels -/
  Lab : CubeLabels m₀ j Ω Lb
  εH : ℝ
  κH : ℝ
  κG : ℝ
  κ0 : ℝ
  κ' : ℝ
  Kc : ℝ
  Cm : ℝ
  Cdet : ℝ
  β0 : ℝ
  β1 : ℝ
  /-- the exponent `κ` of the framework: `κ_b ≥ 3κ/2` in (4.2) -/
  κ : ℝ
  /-- the activities -/
  A : LabelAct Lab Ωb εH κH κ0 Kc
  /-- the marks -/
  G : Lb → (∀ b, Ωb b) → ℂ
  G_meas : ∀ y, Measurable (G y)
  G_dep : ∀ y, DepOn (blocksOf m₀ j Ω (Lab.ysite y)) (G y)
  G_bound : ∀ y Φ, ‖G y Φ‖ ≤ Cm * β0 ^ (-(m : ℝ) - 3 / 2) * Real.exp (-κG * Lab.dl y)
  /-- the determinant coefficient -/
  det : Finset 𝔅 → ℂ
  det_bound : ∀ Y, Y.Nonempty →
    ‖det Y‖ ≤ Cdet * β0 ^ (-(m : ℝ) - 3 / 2) * Real.exp (-(κ' - 1) * dExt Y)
  /-- the remainder coefficient `ℛ^{(1)}_m(Y)` -/
  Rm : Finset 𝔅 → ℂ
  Rm_eq : ∀ Y, Y.Nonempty → Rm Y = markSum μ Lab A.H G Y + det Y
  hβ0 : 0 < β0
  hβ1 : 0 < β1
  hCm : 0 < Cm
  hCdet : 0 ≤ Cdet
  hκ0 : aEnt d L + 1 ≤ κ0
  hKc : K0 d L κ0 + 1 ≤ Kc
  hεpos : 0 < εH
  hκ' : 1 ≤ κ'
  hκG : κH ≤ κG
  hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH
  hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
    Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))
  hratio : β1 / β0 ≤ 2 * (L : ℝ) ^ (d - 2)
  hβ : (2 * (CPE d L Kc κH κ0 κ' * Kc * c1 d L * Cm + Cdet) *
    (2 * (L : ℝ) ^ (d - 2)) ^ (m + 1)) ^ 2 ≤ β0
  hκb : 3 / 2 * κ ≤ κ' - 1

attribute [instance] Prop279Marks.fin Prop279Marks.meas Prop279Marks.prob

/-- **(4.3), the half-budget bound for the base remainder**, from (PE): for every nonempty `Y`,
`|ℛ^{(1)}_m(Y)| ≤ ½ β₁^{-m-1} e^{-κ_b d_Ext(Y)}` with `κ_b = κ' - 1 ≥ 3κ/2`; and the one-mark
part vanishes unless `Y` contains the block support of a mark. -/
theorem Prop279Marks.remainder_half {hN : L ^ m₀ ∣ N₁} {hj : j ≤ K} {hΩ : IsPiUnion m₀ j Ω} {m : ℕ}
    (P : Prop279Marks hN hj hΩ m) (Y : Finset 𝔅) (hY : Y.Nonempty) :
    ‖P.Rm Y‖ ≤ 1 / 2 * (P.β1 ^ (m + 1))⁻¹ * Real.exp (-(P.κ' - 1) * dExt Y) := by
  rw [P.Rm_eq Y hY]
  exact markSum_add_det_half (Lab := P.Lab) (εH := P.εH) (κH := P.κH) (κG := P.κG)
    (κ0 := P.κ0) (κ' := P.κ') (Kc := P.Kc) (m := m) (β0 := P.β0) (β1 := P.β1)
    (Cm := P.Cm) (Cdet := P.Cdet) P.μ hN hj hΩ P.A P.G P.G_meas P.G_dep P.hβ0 P.hβ1 P.hCm
    P.hCdet P.G_bound P.hκ0 P.hKc P.hεpos P.hκ' P.hκG P.hκ P.hε P.hratio P.hβ Y hY (P.det Y)
    (P.det_bound Y hY)

/-- The exponent is at least `3κ/2`, so the bound (4.3) holds with `κ_b ≥ 3κ/2` (the exponent
`κ_+` of (D7)). -/
theorem Prop279Marks.remainder_half_kappa {hN : L ^ m₀ ∣ N₁} {hj : j ≤ K} {hΩ : IsPiUnion m₀ j Ω}
    {m : ℕ} (P : Prop279Marks hN hj hΩ m) (Y : Finset 𝔅) (hY : Y.Nonempty) :
    ‖P.Rm Y‖ ≤ 1 / 2 * (P.β1 ^ (m + 1))⁻¹ * Real.exp (-(3 / 2 * P.κ) * dExt Y) := by
  refine (P.remainder_half Y hY).trans ?_
  have hβ1 := P.hβ1
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  nlinarith [dExt_nonneg Y, P.hκb]

/-- The vanishing part of Lemma 3.1: the summed one-mark coefficient is zero unless `Y` contains
the block support of at least one mark. -/
theorem Prop279Marks.markSum_eq_zero {hN : L ^ m₀ ∣ N₁} {hj : j ≤ K} {hΩ : IsPiUnion m₀ j Ω}
    {m : ℕ} (P : Prop279Marks hN hj hΩ m) (Y : Finset 𝔅) (hY : Y.Nonempty)
    (h : ∀ y, ¬ blocksOf m₀ j Ω (P.Lab.ysite y) ⊆ Y) : markSum P.μ P.Lab P.A.H P.G Y = 0 := by
  have hF0 : 0 < P.Cm * P.β0 ^ (-(m : ℝ) - 3 / 2) := by
    have := P.hCm; have := P.hβ0; positivity
  exact (sum_gst_marks_bound P.μ hN hj hΩ P.A P.G P.G_meas P.G_dep P.G_bound P.hκ0 P.hKc
    P.hεpos hF0 P.hκ' P.hκG P.hκ P.hε Y hY).1 h

/-- **`Prop279Marks` is inhabited** (rule 10), for every admissible choice of the typing data
`hN, hj, hΩ`: the instance has no marks (`Lb` empty), so it is degenerate in the marks; a
non-degenerate instance needs the physical activities of BASE-KERNEL-3 (3.1)-(3.2), which are
exactly the model-specific content of (PE). -/
theorem prop279Marks_nonempty (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω) (m : ℕ) :
    Nonempty (Prop279Marks hN hj hΩ m) := by
  classical
  set κ0 : ℝ := aEnt d L + 1 with hκ0
  set Kc : ℝ := max 1 (K0 d L κ0 + 1) with hKc
  have hKc1 : 1 ≤ Kc := le_max_left _ _
  have hc1 := one_le_c1 d L
  set κ' : ℝ := 1 with hκ'
  set κH : ℝ := κ' + 3 * κ0 + c1 d L + 3 / 2 with hκH
  set εH : ℝ := 1 / (8 * Kc ^ 3 * c1 d L *
    Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)) with hεH
  have hεpos : 0 < εH := by
    rw [hεH]; have : 0 < Kc := by linarith
    positivity
  set β0 : ℝ := max 1 ((2 * (CPE d L Kc κH κ0 κ' * Kc * c1 d L * 1 + 0) *
    (2 * (L : ℝ) ^ (d - 2)) ^ (m + 1)) ^ 2) with hβ0
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ (d - 2) :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L))
  let Lab : CubeLabels m₀ j Ω Empty :=
    { ysite := fun y => y.elim, dl := fun y => y.elim, isDj := fun y => y.elim,
      meets := fun y => y.elim, size := fun y => y.elim }
  have hKc0 : 0 ≤ Kc := by linarith
  let A : LabelAct Lab (fun _ : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω => Unit)
      εH κH κ0 Kc :=
    { H := fun y => y.elim, meas := fun y => y.elim, dep := fun y => y.elim,
      bound := fun y => y.elim, entropy := fun b => by simpa using hKc0 }
  refine ⟨
    { Lb := Empty
      Ωb := (fun _ => Unit)
      μ := (fun _ => Measure.dirac ())
      Lab := Lab
      εH := εH
      κH := κH
      κG := κH
      κ0 := κ0
      κ' := κ'
      Kc := Kc
      Cm := 1
      Cdet := 0
      β0 := β0
      β1 := β0
      κ := 0
      A := A
      G := fun y => y.elim
      G_meas := fun y => y.elim
      G_dep := fun y => y.elim
      G_bound := fun y => y.elim
      det := fun _ => 0
      det_bound := fun Y _ => by simp [hκ']
      Rm := fun _ => 0
      Rm_eq := fun Y _ => by simp [markSum]
      hβ0 := lt_of_lt_of_le one_pos (le_max_left _ _)
      hβ1 := lt_of_lt_of_le one_pos (le_max_left _ _)
      hCm := one_pos
      hCdet := le_rfl
      hκ0 := le_rfl
      hKc := le_max_right _ _
      hεpos := hεpos
      hκ' := le_rfl
      hκG := le_rfl
      hκ := le_rfl
      hε := le_rfl
      hratio := ?_
      hβ := le_max_right _ _
      hκb := by simp [hκ'] }⟩
  have hβpos : 0 < β0 := lt_of_lt_of_le one_pos (le_max_left _ _)
  rw [div_self hβpos.ne']
  linarith

end Marks


/-! ### (PHYS): the physical first-step data -/

section Phys

open MeasureTheory Balaban.Multiscale RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {k0 : ℕ} {geo : Geo S n R M} {cs : OpConsts}

/-- The volume `|X|_1` of the new part `Z_1 ∖ Z_0` of a localized history, as in (S0). -/
noncomputable def baseVol (S : Setting) {M K : ℕ} {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    (a : LocalHistory S n M K) : ℝ :=
  volScale S (0 + 1) {z | z ∈ a.Z (0 + 1) ∧ z ∉ a.Z 0}

/-- The constant `L^d log(2^{N+1} N v_N)` of (4.1b), `v_N` the volume of the unit ball of `ℝ^N`. -/
noncomputable def baseVolConst (S : Setting) (N : ℕ) : ℝ :=
  (S.L : ℝ) ^ S.d * Real.log (2 ^ (N + 1) * N *
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal)

/-- **Input (PHYS)** of BASE-KERNEL-4 Proposition 4.1 (BASE-KERNEL §§1-3, §5; LF-RECONSTRUCTION
Definition II.7.6, Lemma II.7.7): the remainder `K̃^w_0` and the boundary exponent `b_0`, defined
by the physical retained-factor and chart-integral formulas, as a `BaseSmallFieldInput` (the
fields (S0), (S1), (S4)), together with

* `b0_reads`: `b_0` reads the output `ψ_1` only on `Ω_1 ∩ V`;
* `b0_sf`: the source-strength bound `|b_0| ≤ C_{b,sf}(log β_0 + 1)|X|_1` (Lemma II.7.7 (b));
* `Cb_ge` (4.1b): `C_b ≥ C_{b,sf} + max{0, L^d log(2^{N+1} N v_N)}`;
* `s5`: in regime (A) the rotation form `BaseS5` of (S5), Lemma II.7.7 (e).

The equality of `∑_{records} ∏ K_0` with the exact transform `ρ_1` of (II.7.1) is **not
representable here**: the exact first transform is not yet formalized as an object of the
large-field layer.  `zero_input_kernel_eq_zero` and `positive_transform_pos` show that the
`BaseSmallFieldInput` fields alone do not imply it. -/
structure Prop279Phys (K k0 : ℕ) (geo : Geo S n R M) (cs : OpConsts) (N : ℕ) (regimeA : Prop)
    (eps : ℕ → ℝ) (hz : 0 ≤ cs.z (0 + 1))
    (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) where
  inp : BaseSmallFieldInput K k0 geo cs N
  /-- the source-strength constant `C_{b,sf}` -/
  Csf : ℝ
  b0_reads : ∀ (a : LocalHistory S n M K) (o o' : OutT N R a (0 + 1)) (x : NewCfg N a 0)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ),
    (∀ y : Vblk R a (0 + 1),
      BlockSub (S := S) (n := n) (M := M) (K := K) (0 + 1) y.1 (a.Omega 0) → o y = o' y) →
    inp.b0 a o x hv g = inp.b0 a o' x hv g
  b0_sf : ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (Z' : H.Comp (0 + 1)) o x hv
    (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) → ChiNewAt geo cs H 0 Z' o x →
    ‖inp.b0 (H.localHistory M K (0 + 1) Z') o x hv g‖ ≤
      Csf * (Real.log (cs.beta 0) + 1) * baseVol S (H.localHistory M K (0 + 1) Z')
  Cb_ge : Csf + max 0 (baseVolConst S N) ≤ cs.Cb
  s5 : regimeA → ∀ a : LocalHistory S n M K,
    BaseS5 eps (baseVol S a) a (baseKernel_of_input inp hz hc a)

/-- **`Prop279Phys` is inhabited** (rule 10), for `C_b ≥ max{0, L^d log(2^{N+1}Nv_N)}`, `B_0 ≥ 0`,
`β_0 ≥ 1`: by the zero input, hence degenerate (see the docstring of `Prop279Phys`; a
non-degenerate member is the physical chart integral). -/
theorem prop279Phys_nonempty (regimeA : Prop) (eps : ℕ → ℝ) (hCb : 0 ≤ cs.Cb) (hB0 : 0 ≤ cs.B0)
    (hβ : 1 ≤ cs.beta 0) (hCb' : max 0 (baseVolConst S N) ≤ cs.Cb)
    (hz : 0 ≤ cs.z (0 + 1)) (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) :
    Nonempty (Prop279Phys (K := K) k0 geo cs N regimeA eps hz hc) := by
  have hlog : 0 ≤ Real.log (cs.beta 0) := Real.log_nonneg hβ
  refine ⟨{ inp := zeroBaseSmallFieldInput (K := K) (k0 := k0) geo cs N hCb hB0 hβ
            Csf := 0
            b0_reads := fun _ _ _ _ _ _ _ => rfl
            b0_sf := ?_
            Cb_ge := by simpa using hCb'
            s5 := ?_ }⟩
  · intro H hH Z' o x hv g hg hc'
    show ‖(0 : ℂ)‖ ≤ _
    simp
  · intro _ a
    refine ⟨Empty, inferInstance, fun i => i.elim, fun i => i.elim, fun i => i.elim,
      fun i => i.elim, fun i => i.elim, ?_, fun i => i.elim, fun i => i.elim, fun i => i.elim,
      fun i => i.elim⟩
    intro o x hv _
    rw [zero_input_kernel_eq_zero (K := K) (k0 := k0) geo cs hCb hB0 hβ hz hc a o x hv]
    simp

end Phys


/-! ### The conditional Proposition II.7.9 -/

section Main

open MeasureTheory Balaban.Multiscale RegionHistory Balaban.Localization Balaban.Fluctuation

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {k0 : ℕ} {geo : Geo S n R M} {cs : OpConsts}
  {N₁ m₁ m₀ j : ℕ} [NeZero N₁] {Ω : Set (Balaban.Localization.CTorus S.d S.L N₁ m₁ K)}

/-- **The input of the conditional Proposition II.7.9** (BASE-KERNEL-4 Proposition 4.1) for one base
record `br` and one component `Zc`: the model-specific estimates (CT), (PE), (PHYS) that the
landed Lean files do not supply.  `regimeA`/`regimeB` select the mass regime; `ν, δ₀, r, h` are the
base constants and the physical field; `hz, hc` are the sign data of `baseKernel_of_input`; the
marked-cube data `marks` live on the cube torus `CTorus d L N₁ m₁ K`.  The remaining analytic
inputs of Proposition 4.1 (LC, RG, WG) are not fields: they are the inputs of the three steps that
are *not* in the conclusion (see `Prop279Conclusion`). -/
structure Prop279Input (k0 : ℕ) (geo : Geo S n R M) (cs : OpConsts) (N : ℕ)
    (regimeA regimeB : Prop) (eps : ℕ → ℝ) (hz : 0 ≤ cs.z (0 + 1))
    (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (ν δ₀ r : ℝ) (h : Fin N → ℝ)
    {Rk : ℝ} (br : BaseRecord S.d S.L (n 1) Rk) (Zc : Set (Torus S.d (n 1)))
    (hN : S.L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω) (m : ℕ) where
  /-- (CT) the cutoff margins -/
  cut : Prop279Cut n S.L M K regimeB ν δ₀ r h br Zc
  /-- (PE) the marked-cube data and the half-budget numerics -/
  marks : Prop279Marks (Ω := Ω) hN hj hΩ m
  /-- (PHYS) the physical remainder and boundary exponent -/
  phys : Prop279Phys (K := K) k0 geo cs N regimeA eps hz hc

/-- **The conclusion of the conditional Proposition II.7.9** that is proved from the landed base
step and the input:

* `stepData`: the base step data (S0), (S1), (S4) at `k = 0`, with kernel `baseKernel_of_input`;
* `b0_source`: the source-strength bound `|b_0| ≤ C_b(log β_0 + 1)|X|_1` of Lemma II.7.7 (b);
* `s5`: the rotation form (S5) in regime (A);
* `cutoff`: the cutoff transfer (Lemma 2.2: old factor = factor with `𝒥₊` deleted, independent of
  the integrated spins);
* `remainder`: (4.3), `|ℛ^{(1)}_m(Y)| ≤ ½ β_1^{-m-1} e^{-κ_b d_Ext(Y)}` with `κ_b = κ' - 1 ≥ 3κ/2`,
  and its form with the finite modular size `d_Ω(sites Y)`.

Not in the conclusion (BASE-KERNEL-4 rows 5-12 of §5, open): the one-step bound (S2) of Lemma II.7.8
(the integrated witness bound, (Λ17′), (Λ27)), the I-7 solution `(β_1, ν_1, z_1, E_1)` with
Def-6/D2-flat (RG), the boundary terms `ℬ^{(1)}` with (D7), and the equality with `ρ_1`. -/
structure Prop279Conclusion {regimeA regimeB : Prop} {eps : ℕ → ℝ} {hz : 0 ≤ cs.z (0 + 1)}
    {hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2)} {ν δ₀ r : ℝ} {h : Fin N → ℝ}
    {Rk : ℝ} {br : BaseRecord S.d S.L (n 1) Rk} {Zc : Set (Torus S.d (n 1))}
    {hN : S.L ^ m₀ ∣ N₁} {hj : j ≤ K} {hΩ : IsPiUnion m₀ j Ω} {m : ℕ}
    (I : Prop279Input k0 geo cs N regimeA regimeB eps hz hc ν δ₀ r h br Zc hN hj hΩ m) :
    Prop where
  stepData : ∃ D : BaseStepData K k0 geo cs N,
    ∀ a, D.ker a = baseKernel_of_input I.phys.inp hz hc a
  b0_source : ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (Z' : H.Comp (0 + 1)) o x hv
    (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) → ChiNewAt geo cs H 0 Z' o x →
    ‖I.phys.inp.b0 (H.localHistory M K (0 + 1) Z') o x hv g‖ ≤
      cs.Cb * (Real.log (cs.beta 0) + 1) * baseVol S (H.localHistory M K (0 + 1) Z')
  s5 : regimeA → ∀ a : LocalHistory S n M K,
    BaseS5 eps (baseVol S a) a (baseKernel_of_input I.phys.inp hz hc a)
  cutoff : I.cut.Deletes
  remainder : ∀ Y : Finset (CubeB (L := S.L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω), Y.Nonempty →
    ‖I.marks.Rm Y‖ ≤ 1 / 2 * (I.marks.β1 ^ (m + 1))⁻¹ *
        Real.exp (-(I.marks.κ' - 1) * dExt Y) ∧
    ‖I.marks.Rm Y‖ ≤ 1 / 2 * (I.marks.β1 ^ (m + 1))⁻¹ * Real.exp (-(3 / 2 * I.marks.κ) * dExt Y) ∧
    (dOmega m₀ j Ω (sitesOf Y) ≠ ⊤ →
      ‖I.marks.Rm Y‖ ≤ 1 / 2 * (I.marks.β1 ^ (m + 1))⁻¹ *
        Real.exp (-(I.marks.κ' - 1) * (dOmega m₀ j Ω (sitesOf Y)).toReal))

/-- **Proposition II.7.9, conditional form (`prop279_of_input`)**: from the input (CT), (PE), (PHYS)
and the typing data (`hnn`, `K ≥ 1`, `ν ≥ 0`, `β_0 ≥ 1`), the conclusion `Prop279Conclusion`.
The unconditional `prop279` is reserved: it needs the input to be proved from the model. -/
theorem prop279_of_input {regimeA regimeB : Prop} {eps : ℕ → ℝ} {hz : 0 ≤ cs.z (0 + 1)}
    {hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2)} {ν δ₀ r : ℝ} {h : Fin N → ℝ}
    {Rk : ℝ} {br : BaseRecord S.d S.L (n 1) Rk} {Zc : Set (Torus S.d (n 1))}
    {hN : S.L ^ m₀ ∣ N₁} {hj : j ≤ K} {hΩ : IsPiUnion m₀ j Ω} {m : ℕ}
    (I : Prop279Input k0 geo cs N regimeA regimeB eps hz hc ν δ₀ r h br Zc hN hj hΩ m)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hK : 1 ≤ K) (hν : 0 ≤ ν)
    (hβ : 1 ≤ cs.beta 0) : Prop279Conclusion I where
  stepData := ⟨baseStepData_of_input I.phys.inp hz hc, fun a => rfl⟩
  b0_source := by
    intro H hH Z' o x hv g hg hnew
    refine (I.phys.b0_sf H hH Z' o x hv g hg hnew).trans ?_
    have hlog : 0 ≤ Real.log (cs.beta 0) + 1 := by
      have := Real.log_nonneg hβ; linarith
    have hvol : 0 ≤ baseVol S (H.localHistory M K (0 + 1) Z') := by
      unfold baseVol volScale; positivity
    have hCsf : I.phys.Csf ≤ cs.Cb := by
      have := I.phys.Cb_ge; have := le_max_left 0 (baseVolConst S N); linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCsf hlog) hvol
  s5 := I.phys.s5
  cutoff := I.cut.deletes hnn hK hν
  remainder := fun Y hY => ⟨I.marks.remainder_half Y hY, I.marks.remainder_half_kappa Y hY,
    fun hfin => by rw [← dExt_eq_toReal hfin]; exact I.marks.remainder_half Y hY⟩

/-- **`Prop279Input` is inhabited** (rule 10), in every regime: for a unit field `h`, `δ₀ > 0`,
`r = 0`, `C_b ≥ max{0, L^d log(2^{N+1}Nv_N)}`, `B_0 ≥ 0`, `β_0 ≥ 1`.  Degenerate in (PHYS) and in
the marks of (PE) (zero input, no marks); non-degenerate in (CT). -/
theorem prop279Input_nonempty {regimeA regimeB : Prop} (eps : ℕ → ℝ)
    (hz : 0 ≤ cs.z (0 + 1)) (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (ν : ℝ) {δ₀ : ℝ} (hδ : 0 < δ₀) (h : Fin N → ℝ) (hh : ∑ i, h i ^ 2 = 1) {Rk : ℝ}
    (br : BaseRecord S.d S.L (n 1) Rk) (Zc : Set (Torus S.d (n 1)))
    (hN : S.L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω) (m : ℕ)
    (hCb : 0 ≤ cs.Cb) (hB0 : 0 ≤ cs.B0) (hβ : 1 ≤ cs.beta 0)
    (hCb' : max 0 (baseVolConst S N) ≤ cs.Cb) :
    Nonempty (Prop279Input k0 geo cs N regimeA regimeB eps hz hc ν δ₀ 0 h br Zc hN hj hΩ m) := by
  obtain ⟨c⟩ := prop279Cut_nonempty (nn := n) (L := S.L) (M := M) (K := K) regimeB ν hδ h hh br Zc
  obtain ⟨mk⟩ := prop279Marks_nonempty (Ω := Ω) hN hj hΩ m
  obtain ⟨ph⟩ := prop279Phys_nonempty (K := K) (k0 := k0) (geo := geo) (cs := cs) (N := N)
    regimeA eps hCb hB0 hβ hCb' hz hc
  exact ⟨⟨c, mk, ph⟩⟩

end Main

end Balaban.LargeField
