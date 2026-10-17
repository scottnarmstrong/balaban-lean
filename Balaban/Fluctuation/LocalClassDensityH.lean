/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexOffFibreE1Loc
public import Balaban.Localization.XiCRawOpen
public import Balaban.Fluctuation.RenormThetaDatum

/-!
# Where the external field enters the step (blocker 6, item (1))

The landed step `StepSetting` stores a real constant field `h₀` together with a block datum `θ`
with `θ.h = h₀`.  This file records, with proofs, the exact places where the field `h` of the
block datum enters the objects of one step, and that the landed complex constructions are already
analytic in `h` on a complex neighbourhood containing non-constant fields.

**Where `h` enters.**
* *The background equation.*  The source of (EL) is `Q* a Ψ + ν h + 𝔟(Ψ)` (`source`); the small
  solution `(φ, α) = (bgFieldC, bgMultC)` depends on the datum only through `Ψ` and `ν h`
  (`bgFieldC_eq_of_source_eq`, `bgMultC_eq_of_source_eq`, `source_eq_of_nu_mul_h_eq`); at zero
  mass it does not depend on `h` (`bgFieldC_eq_of_nu_eq_zero`).  The covariance `C^{(k)1/2}`
  (`covSqrtC`, `hatCovSqrt`), the logarithm `𝕃` (`logAC`) and `½ log det C^{(k)}` are functions of
  this background only (definitions), hence of `h` only through `ν h`.
* *The critical point and the old datum.*  The critical point `ψ^{(k)}(θ)` is `composeData` of the
  background and of `θ`: its field is `θ.h` on `Ω₁` (`StepSettingH.dataUCH_psi0C`).  The old datum
  `(ψ, h)` of the fluctuation integral (the argument of `φ_k`, `ℰ_k`, `ℱ_k`, `A_k`) carries the
  field `θ.h` (`StepSettingH.dataUCH_h`), whereas the landed `StepSetting.dataUC` carries the
  constant `h₀` (`StepSetting.dataUC_h`): the two differ at every block datum whose field is not
  `h₀` at some site (`StepSettingH.dataUCH_ne_dataUC`).  This, and the field `hh₀` of
  `StepSetting`, are the only places where the landed step is restricted to the fibre.
* *The old class terms.*  The composed pairs `(ψ_k^{(j)}, h)` of (H.2) carry the raw field of the
  block datum restricted to `Ω₁` of level `j` (`JointRep.PJ_snd`); the class terms `ℰ^{(j)}`,
  `ℱ^{(j)}`, `ℳ^{(j)}` are evaluated there, so `h` enters them directly.  The old action contains
  the mass term `ν/2 Σ (φ - h)·(φ - h)` (`actionC`).
* *Not through:* the kernel `∏ t_k` (it reads `θ.Ψ` and `ψ` only), the measure `ν_{p₁}`, the numbers
  `β_k`, `a`, `ν`, `|T^{(k)}_1|` and the vacuum constants (fields of the step, the same for every
  block datum: `StepSetting.withDatum` changes only `θ`), and the renormalization of the block
  datum, which rescales `θ.Ψ` and keeps `θ.h` (`renThetaDatum_h`).

**Analyticity in `h`.**  The representatives of `StepComplexJoint.JointRep` (`F₀`, `Mx`, `Pc`, `Fb`
and the joint functions `VJ`, `PJ`, `EJ`, `W1`, `W2`, `McJ`) are functions of the whole raw datum
`Θ = (Ψ, h̃)`, analytic at every point of the chart `Ξ^c(𝔹_{k+1}; 1, ε)`.  The chart contains, near
each of its points, every raw datum of the data subspace `rawSub` (`xiCRaw_eventually`); in
particular every line `c ↦ rawOf D + c (0, w)` in a field direction `w` (constant on the blocks,
zero off `Ω₁`, otherwise arbitrary complex) stays in the chart for small `c`
(`eventually_add_smul_mem_xiCRaw`, `fieldDir_mem_rawSub`), and the representatives are analytic
along it (`JointRep.analyticAt_F₀_line`, `JointRep.analyticAt_Mx_line`).  Starting from a datum
with constant field, the line meets data whose field is not constant
(`exists_xiCRaw_field_ne`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Matrix Filter Topology

/-! ### The background equation: `h` enters through the source `ν h` -/

section Source

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {a : ℕ → ℝ} {ν : ℝ}

/-- **The source of (EL) depends on the field only through `ν h`**: two data with the same spin
and the same `ν h` on `Ω₁` have the same source `Q* a Ψ + ν h + 𝔟(Ψ)`. -/
theorem source_eq_of_nu_mul_h_eq {D D' : BgData G N} (hΨ : D.Ψ = D'.Ψ)
    (hh : ∀ (x : G.Ω 1) (i : Fin N), (ν : ℂ) * D.h x i = (ν : ℂ) * D'.h x i) :
    source G a ν D = source G a ν D' := by
  funext p
  simp only [source, hΨ, hh p.1 p.2]

/-- The small solutions of (EL) depend on the datum only through the source. -/
theorem isSmallSolution_iff_of_source_eq {c₀ : ℝ} {D D' : BgData G N}
    (hs : source G a ν D = source G a ν D') (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) :
    IsSmallSolution G a ν c₀ D φ α ↔ IsSmallSolution G a ν c₀ D' φ α := by
  simp only [IsSmallSolution, IsEL, hs]

/-- A choice from a unique existence depends only on the predicate. -/
theorem dite_existsUnique_congr {α β : Type*} [Zero β] {P Q : α → Prop} (hPQ : ∀ s, P s ↔ Q s)
    (f : α → β) {_ : Decidable (∃! s, P s)} {_ : Decidable (∃! s, Q s)} :
    (if H : ∃! s, P s then f H.exists.choose else 0) =
      (if H : ∃! s, Q s then f H.exists.choose else 0) := by
  have e : P = Q := funext fun s => propext (hPQ s)
  subst e
  congr

/-- **The complex background field depends on the datum only through the source** (Def-5(b)). -/
theorem bgFieldC_eq_of_source_eq {c₀ : ℝ} {D D' : BgData G N}
    (hs : source G a ν D = source G a ν D') : bgFieldC G a ν c₀ D = bgFieldC G a ν c₀ D' := by
  unfold bgFieldC
  exact dite_existsUnique_congr
    (P := fun s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ) => IsSmallSolution G a ν c₀ D s.1 s.2)
    (Q := fun s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ) => IsSmallSolution G a ν c₀ D' s.1 s.2)
    (fun s => isSmallSolution_iff_of_source_eq hs s.1 s.2) (fun s => s.1)

/-- The complex multiplier depends on the datum only through the source. -/
theorem bgMultC_eq_of_source_eq {c₀ : ℝ} {D D' : BgData G N}
    (hs : source G a ν D = source G a ν D') : bgMultC G a ν c₀ D = bgMultC G a ν c₀ D' := by
  unfold bgMultC
  exact dite_existsUnique_congr
    (P := fun s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ) => IsSmallSolution G a ν c₀ D s.1 s.2)
    (Q := fun s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ) => IsSmallSolution G a ν c₀ D' s.1 s.2)
    (fun s => isSmallSolution_iff_of_source_eq hs s.1 s.2) (fun s => s.2)

/-- **At zero mass the background does not depend on the field**: two data with the same spin
have the same complex background field and multiplier. -/
theorem bgFieldC_eq_of_nu_eq_zero {c₀ : ℝ} {D D' : BgData G N} (hν : ν = 0)
    (hΨ : D.Ψ = D'.Ψ) :
    bgFieldC G a ν c₀ D = bgFieldC G a ν c₀ D' ∧ bgMultC G a ν c₀ D = bgMultC G a ν c₀ D' := by
  have hs : source G a ν D = source G a ν D' :=
    source_eq_of_nu_mul_h_eq hΨ fun x i => by simp [hν]
  exact ⟨bgFieldC_eq_of_source_eq hs, bgMultC_eq_of_source_eq hs⟩

end Source

/-! ### The old datum and the composed pairs -/

namespace StepSettingH

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {S : StepSetting d L N₁ m₁ k N ϱ}

/-- **The landed old datum is the old datum of the step only on the fibre**: the old datum
`dataUCH` of a block datum `D` carries the field `D.h`, the landed `dataUC` the constant `h₀`; they
differ as soon as `D.h` differs from `h₀` at one site. -/
theorem dataUCH_ne_dataUC (D : BgData S.G' N) {x : CTorus d L N₁ m₁ (k + 1)} {i : Fin N}
    (hx : D.h x i ≠ (S.h₀ i : ℂ)) (ψ : S.EC) : (S.withDatumH D).dataUCH ψ ≠ S.dataUC ψ := by
  intro e
  have h1 := congrArg (fun B : BgData (stepG d L N₁ m₁ k ϱ) N => B.h x i) e
  rw [dataUCH_h, StepSetting.dataUC_h] at h1
  exact hx h1

end StepSettingH

namespace StepSetting.JointRep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp)

/-- **The field of the composed pairs is the raw field of the block datum**: for `j ≤ k`, the
second component of `(ψ_k^{(j)}, h)` (H.2) at the raw datum `Θ` is `Θ.2` restricted to `Ω₁` of
level `j`, for every hat variable. -/
theorem PJ_snd {j : ℕ} (hj : j ≤ k) (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    (Jr.PJ j q).2 y i =
      if y ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j
          (hj.trans (Nat.le_succ k))).Ω 1 then q.1.2 y i else 0 := by
  classical
  unfold PJ gJ
  simp only [hj, ↓reduceDIte]

end StepSetting.JointRep

/-! ### Lines in a field direction stay in the chart -/

section Lines

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- A field direction `(0, w)` with `w` constant on the blocks and zero off `Ω₁` lies in the
subspace of data. -/
theorem fieldDir_mem_rawSub {w : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ}
    (hw : IsLayerConstant G w) (hw0 : ∀ x, x ∉ G.Ω 1 → w x = 0) :
    ((0, w) : RawData d L (N₁ * L ^ m₁) K N) ∈ rawSub N G :=
  ⟨fun _ _ _ _ _ _ _ => rfl, hw, fun _ _ => rfl, hw0⟩

/-- **A line through a chart datum in a direction of the data subspace stays in the chart near the
datum** (relative openness of the chart, `xiCRaw_eventually`). -/
theorem eventually_add_smul_mem_xiCRaw {a : ℕ → ℝ} {ν σ ε : ℝ} {n : ℕ}
    (H : BgHyp d L K ϱ a ν) {D : BgData G N} (hD : XiCData G a ν n σ ε D)
    {v : RawData d L (N₁ * L ^ m₁) K N} (hv : v ∈ rawSub N G) :
    ∀ᶠ c in 𝓝 (0 : ℂ), rawOf D + c • v ∈ XiCRaw G a ν n σ ε := by
  have hT : Tendsto (fun c : ℂ => rawOf D + c • v) (𝓝 0)
      (𝓝[(rawSub N G : Set (RawData d L (N₁ * L ^ m₁) K N))] (rawOf D)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun c =>
      (rawSub N G).add_mem (rawOf_mem_rawSub D) ((rawSub N G).smul_mem c hv)⟩
    have hc : Continuous (fun c : ℂ => rawOf D + c • v) := by fun_prop
    simpa using hc.tendsto 0
  exact hT.eventually (xiCRaw_eventually H hD)

/-- **The chart contains data with non-constant field near every datum with constant field**: if
the field of a chart datum `D` takes the same value at two sites `x`, `x'` and a field direction
`w` of the data subspace separates them, then arbitrarily close to `rawOf D` on the line
`c ↦ rawOf D + c (0, w)` there is a raw datum of the chart whose field differs at `x` and `x'`. -/
theorem exists_xiCRaw_field_ne {a : ℕ → ℝ} {ν σ ε : ℝ} {n : ℕ}
    (H : BgHyp d L K ϱ a ν) {D : BgData G N} (hD : XiCData G a ν n σ ε D)
    {w : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ}
    (hw : IsLayerConstant G w) (hw0 : ∀ x, x ∉ G.Ω 1 → w x = 0)
    {x x' : Torus d ((N₁ * L ^ m₁) * L ^ K)} {i : Fin N} (hDx : D.h x i = D.h x' i)
    (hwx : w x i ≠ w x' i) {r : ℝ} (hr : 0 < r) :
    ∃ c : ℂ, ‖c‖ < r ∧ c ≠ 0 ∧
      rawOf D + c • ((0, w) : RawData d L (N₁ * L ^ m₁) K N) ∈ XiCRaw G a ν n σ ε ∧
      (rawOf D + c • ((0, w) : RawData d L (N₁ * L ^ m₁) K N)).2 x i ≠
        (rawOf D + c • ((0, w) : RawData d L (N₁ * L ^ m₁) K N)).2 x' i := by
  have hev := eventually_add_smul_mem_xiCRaw H hD (fieldDir_mem_rawSub hw hw0)
  have hball : ∀ᶠ c in 𝓝 (0 : ℂ), ‖c‖ < r := by
    have := Metric.ball_mem_nhds (0 : ℂ) hr
    filter_upwards [this] with c hc
    simpa using hc
  have h1 : ∀ᶠ c in 𝓝[≠] (0 : ℂ),
      (rawOf D + c • ((0, w) : RawData d L (N₁ * L ^ m₁) K N) ∈ XiCRaw G a ν n σ ε ∧
        ‖c‖ < r) ∧ c ∈ ({0}ᶜ : Set ℂ) :=
    ((hev.and hball).filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  obtain ⟨c, ⟨hcX, hcr⟩, hc0⟩ := h1.exists
  refine ⟨c, hcr, hc0, hcX, ?_⟩
  intro e
  have e' : D.h x i + c * w x i = D.h x' i + c * w x' i := by simpa [rawOf] using e
  rw [hDx] at e'
  exact hwx (mul_left_cancel₀ hc0 (add_left_cancel e'))

end Lines

namespace StepSetting.JointRep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp)

/-- **The background representative is analytic along every line of the data subspace** through a
chart datum (in particular along the field directions `(0, w)`, `w` complex and non-constant). -/
theorem analyticAt_F₀_line {D : BgData S.G' N} (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (v : RawData d L (N₁ * L ^ m₁) (k + 1) N) :
    AnalyticAt ℂ (fun c : ℂ => Jr.F₀ (rawOf D + c • v)) 0 := by
  have hF : AnalyticAt ℂ Jr.F₀ (rawOf D + (0 : ℂ) • v) := by
    rw [zero_smul, add_zero]
    exact Jr.F₀_an _ ⟨D, hD, rfl⟩
  have hl : AnalyticAt ℂ (fun c : ℂ => rawOf D + c • v) 0 := by fun_prop
  exact hF.comp_of_eq hl (by simp)

/-- The entries of the square-root representative are analytic along every line of the data
subspace through a chart datum. -/
theorem analyticAt_Mx_line {D : BgData S.G' N} (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (v : RawData d L (N₁ * L ^ m₁) (k + 1) N) (p q : S.U × Fin N) :
    AnalyticAt ℂ (fun c : ℂ => Jr.Mx (rawOf D + c • v) p q) 0 := by
  have hF : AnalyticAt ℂ (fun Θ => Jr.Mx Θ p q) (rawOf D + (0 : ℂ) • v) := by
    rw [zero_smul, add_zero]
    exact Jr.Mx_an p q _ ⟨D, hD, rfl⟩
  have hl : AnalyticAt ℂ (fun c : ℂ => rawOf D + c • v) 0 := by fun_prop
  exact hF.comp_of_eq hl (by simp)

end StepSetting.JointRep

end Balaban.Fluctuation
