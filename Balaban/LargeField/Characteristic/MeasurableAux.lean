module

public import Balaban.LargeField.Characteristic.RealDomain
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Measurability of `Reg` for continuous families of data (auxiliary lemmas)

Let `Y` be a measurable space with a topology (`OpensMeasurableSpace`, e.g. a space of real
configurations), `D : Y → BgData G N` with continuous coordinates, and `E ⊂ Y` the measurable set
where `D y ∈ 𝒟_ℝ(G)`.  On `E` the background `y ↦ bgFieldC (D y)`, `bgMultC (D y)` is continuous
(Theorem 7.2: it is the restriction of an analytic function of the raw data), hence every
strict inequality of `Reg` defines a set `E ∩ {f < c}` with `f` continuous on `E`, which is
measurable (`measurableSet_inter_lt`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background MeasureTheory

set_option linter.unusedSectionVars false

section General

variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]

theorem measurableSet_inter_lt {E : Set Y} (hE : MeasurableSet E) {f : Y → ℝ}
    (hf : ContinuousOn f E) (c : ℝ) : MeasurableSet (E ∩ {y | f y < c}) := by
  classical
  have hm : Measurable (E.piecewise f (fun _ => c)) :=
    hf.measurable_piecewise continuousOn_const hE
  have : E ∩ {y | f y < c} = E ∩ {y | E.piecewise f (fun _ => c) y < c} := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hy, h⟩; exact ⟨hy, by rwa [Set.piecewise_eq_of_mem _ _ _ hy]⟩
    · rintro ⟨hy, h⟩; exact ⟨hy, by rwa [Set.piecewise_eq_of_mem _ _ _ hy] at h⟩
  rw [this]
  exact hE.inter (measurableSet_lt hm measurable_const)

theorem measurableSet_forall_lt {ι : Type*} [Finite ι] {E : Set Y} (hE : MeasurableSet E)
    {f : ι → Y → ℝ} {p : ι → Prop} {c : ι → ℝ} (hf : ∀ i, p i → ContinuousOn (f i) E) :
    MeasurableSet {y | y ∈ E ∧ ∀ i, p i → f i y < c i} := by
  have : {y | y ∈ E ∧ ∀ i, p i → f i y < c i} =
      E ∩ ⋂ i, {y | p i → y ∈ E ∩ {y | f i y < c i}} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hy, h⟩; exact ⟨hy, fun i hp => ⟨hy, h i hp⟩⟩
    · rintro ⟨hy, h⟩; exact ⟨hy, fun i hp => (h i hp).2⟩
  rw [this]
  refine hE.inter (MeasurableSet.iInter fun i => ?_)
  by_cases hp : p i
  · simp only [hp, forall_true_left]
    exact measurableSet_inter_lt hE (hf i hp) _
  · simp [hp]

end General

section Continuity

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem continuous_vn : Continuous (vn : (Fin N → ℂ) → ℝ) :=
  continuous_norm.comp (PiLp.continuous_toLp 2 (fun _ : Fin N => ℂ))

variable {Y : Type*} [TopologicalSpace Y] {E : Set Y}

theorem ContinuousOn.vn' {v : Y → Fin N → ℂ} (h : ∀ i, ContinuousOn (fun y => v y i) E) :
    ContinuousOn (fun y => vn (v y)) E :=
  continuous_vn.comp_continuousOn (continuousOn_pi.2 h)

variable {G : GeneratingSet d L N₀ q ϱ} {D : Y → BgData G N} {φ : Y → G.Ω 1 × Fin N → ℂ}

theorem contOn_coord (hφ : ContinuousOn φ E) (p : G.Ω 1 × Fin N) :
    ContinuousOn (fun y => φ y p) E :=
  (continuous_apply p).comp_continuousOn hφ

theorem contOn_svec (hφ : ContinuousOn φ E) (z : Torus d (N₀ * L ^ q)) (i : Fin N) :
    ContinuousOn (fun y => svec G (φ y) z i) E := by
  classical
  unfold svec zeroExt
  by_cases hz : z ∈ G.Ω 1
  · simp only [hz, ↓reduceDIte]
    exact contOn_coord hφ _
  · simp only [hz, ↓reduceDIte]
    exact continuousOn_const

theorem contOn_blockAvg (hφ : ContinuousOn φ E) (x : Torus d (N₀ * L ^ q)) (i : Fin N) :
    ContinuousOn (fun y => blockAvg G (φ y) x i) E := by
  unfold blockAvg
  refine continuousOn_const.mul ?_
  exact continuousOn_finsetSum _ fun z _ => contOn_svec hφ z i

theorem contOn_blockDev (hφ : ContinuousOn φ E) (hΨ : ∀ x i, Continuous fun y => (D y).Ψ x i)
    (x : Torus d (N₀ * L ^ q)) : ContinuousOn (fun y => blockDev G (D y) (φ y) x) E :=
  ContinuousOn.vn' fun i => (hΨ x i).continuousOn.sub (contOn_blockAvg hφ x i)

theorem contOn_barVec (hφ : ContinuousOn φ E) (hΨ : ∀ x i, Continuous fun y => (D y).Ψ x i)
    (x : Torus d (N₀ * L ^ q)) (i : Fin N) :
    ContinuousOn (fun y => barVec G (D y) (φ y) x i) E := by
  classical
  unfold barVec barField
  by_cases hx : x ∈ G.Ω 1
  · simp only [hx, ↓reduceDIte]
    exact contOn_coord hφ _
  · simp only [hx, ↓reduceDIte]
    exact (hΨ x i).continuousOn

theorem contOn_barLap (hφ : ContinuousOn φ E) (hΨ : ∀ x i, Continuous fun y => (D y).Ψ x i)
    (x : Torus d (N₀ * L ^ q)) (i : Fin N) :
    ContinuousOn (fun y => barLap G (D y) (φ y) x i) E := by
  unfold barLap
  simp only [Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  refine continuousOn_finsetSum _ fun μ _ => ?_
  exact ((contOn_barVec hφ hΨ _ i).add (contOn_barVec hφ hΨ _ i)).sub
    (continuousOn_const.smul (contOn_barVec hφ hΨ x i) |>.congr fun y _ => rfl)

theorem contOn_gradDiff (hφ : ContinuousOn φ E) (hΨ : ∀ x i, Continuous fun y => (D y).Ψ x i)
    (ℓ : ℝ) (x x' : Torus d (N₀ * L ^ q)) :
    ContinuousOn (fun y => ℓ * vn (barVec G (D y) (φ y) x' - barVec G (D y) (φ y) x)) E := by
  refine continuousOn_const.mul (ContinuousOn.vn' fun i => ?_)
  simp only [Pi.sub_apply]
  exact (contOn_barVec hφ hΨ x' i).sub (contOn_barVec hφ hΨ x i)

theorem contOn_lapScaled (hφ : ContinuousOn φ E) (hΨ : ∀ x i, Continuous fun y => (D y).Ψ x i)
    (ℓ : ℝ) (x : Torus d (N₀ * L ^ q)) :
    ContinuousOn (fun y => ℓ ^ 2 * vn (barLap G (D y) (φ y) x)) E :=
  continuousOn_const.mul (ContinuousOn.vn' fun i => contOn_barLap hφ hΨ x i)

end Continuity


/-! ### The background is continuous on the real domain -/

section Background

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {Y : Type*} [TopologicalSpace Y] {G : GeneratingSet d L N₀ q ϱ} {a : ℕ → ℝ} {μ : ℝ}
  (D : Y → BgData G N)

/-- The continuity of the data `y ↦ (Ψ, h)` as a map into the space of raw data. -/
theorem continuous_raw (hΨ : ∀ x i, Continuous fun y => (D y).Ψ x i)
    (hh : ∀ x i, Continuous fun y => (D y).h x i) :
    Continuous fun y => ((D y).Ψ, (D y).h) :=
  continuous_prodMk.2 ⟨continuous_pi fun x => continuous_pi fun i => hΨ x i,
    continuous_pi fun x => continuous_pi fun i => hh x i⟩

/-- **Theorem 7.2 (analyticity), used for continuity**: on the set where `D y ∈ 𝒟_ℝ(G)` the
maps `y ↦ bgFieldC (D y)` and `y ↦ bgMultC (D y)` are continuous. -/
theorem contOn_bg (H : BgHyp d L q ϱ a μ) (hΨ : ∀ x i, Continuous fun y => (D y).Ψ x i)
    (hh : ∀ x i, Continuous fun y => (D y).h x i) :
    ContinuousOn (fun y => bgFieldC G a μ (bgC0 d L N) (D y))
        {y | InUnionDomainR G (bgC1 d L N) μ (D y)} ∧
      ContinuousOn (fun y => bgMultC G a μ (bgC0 d L N) (D y))
        {y | InUnionDomainR G (bgC1 d L N) μ (D y)} := by
  obtain ⟨F, hF, hFe⟩ := theorem72_analytic (G := G) H
  have hcont : ContinuousOn (fun y => F ((D y).Ψ, (D y).h))
      {y | InUnionDomainR G (bgC1 d L N) μ (D y)} :=
    hF.continuousOn.comp (continuous_raw D hΨ hh).continuousOn
      (fun y hy => ⟨D y, inUnionDomainC_of_R H hy, rfl⟩)
  refine ⟨continuous_fst.comp_continuousOn hcont |>.congr fun y hy => ?_,
    continuous_snd.comp_continuousOn hcont |>.congr fun y hy => ?_⟩
  · simp only [Function.comp, hFe (D y) (inUnionDomainC_of_R H hy)]
  · simp only [Function.comp, hFe (D y) (inUnionDomainC_of_R H hy)]

end Background

end Balaban.LargeField
