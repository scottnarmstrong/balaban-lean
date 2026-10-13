/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5Chain
public import Balaban.Fluctuation.InteractionFPart
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Is the chart `Ξ^c` an open set of raw data?

**Answer.**  The chart `XiCRaw G a ν K σ ε` is *not* open in the space `RawData` of all pairs of
fields `(Ψ, h̃)` (a finite product of copies of `ℂ`): it lies in the linear subspace `rawSub N G` of
raw data that are constant on blocks and vanish off the data sites (`Ψ` off `Ω₁ ∪ C(Ω₁)`, `h̃` off
`Ω₁`), because it consists of the raw data of `BgData`, and whenever that subspace is proper the
chart has empty interior (`interior_xiCRaw_eq_empty`).  It is, however, open *relative to the
subspace* `rawSub N G`: for every raw datum of the chart there is a neighbourhood in `RawData` whose
trace on `rawSub N G` lies in the chart (`xiCRaw_relOpen`, under the standing hypothesis `BgHyp`).
All inequalities defining the chart are strict, and the background of the complex datum is
continuous in the datum (`theorem72_analytic`).

* `mem_xiCRaw_iff`: the explicit description of the chart.
* `isOpen_l1Ball`: the unit `ℓ¹` ball of sources is open.
* `XiCRaw_subset_rawSub`, `interior_xiCRaw_eq_empty`, `xiCRaw_relOpen`: the answer.

The landed analyticity statements `AnalyticOnNhd ℂ F (XiCRaw …)` assert analyticity at each point
of the chart as a function on the whole of `RawData` (the functions are defined on all raw data,
see the docstring of `theorem52_analytic`); they are meaningful, and are not statements on an open
subset of `RawData`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Filter Topology

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

section Sub

variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (N)

/-- **The subspace of raw data of data.**  The pairs `(Ψ, h̃)` that are constant on the blocks of
every layer, with `Ψ` zero off `Ω₁ ∪ C(Ω₁)` and `h̃` zero off `Ω₁`: exactly the raw data of
`BgData`. -/
def rawSub : Submodule ℂ (RawData d L (N₁ * L ^ m₁) K N) where
  carrier := {p | IsLayerConstant G p.1 ∧ IsLayerConstant G p.2 ∧
    (∀ x, x ∉ dataSites G → p.1 x = 0) ∧ ∀ x, x ∉ G.Ω 1 → p.2 x = 0}
  add_mem' := by
    rintro p q ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨fun n hn hk x hx x' hx' => ?_, fun n hn hk x hx x' hx' => ?_,
      fun x hx => ?_, fun x hx => ?_⟩
    · simp only [Prod.fst_add, Pi.add_apply, a1 n hn hk x hx x' hx', b1 n hn hk x hx x' hx']
    · simp only [Prod.snd_add, Pi.add_apply, a2 n hn hk x hx x' hx', b2 n hn hk x hx x' hx']
    · simp [a3 x hx, b3 x hx]
    · simp [a4 x hx, b4 x hx]
  zero_mem' := ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c p ⟨a1, a2, a3, a4⟩
    refine ⟨fun n hn hk x hx x' hx' => ?_, fun n hn hk x hx x' hx' => ?_,
      fun x hx => ?_, fun x hx => ?_⟩
    · simp only [Prod.smul_fst, Pi.smul_apply, a1 n hn hk x hx x' hx']
    · simp only [Prod.smul_snd, Pi.smul_apply, a2 n hn hk x hx x' hx']
    · simp [a3 x hx]
    · simp [a4 x hx]

variable {G N}

theorem mem_rawSub {p : RawData d L (N₁ * L ^ m₁) K N} :
    p ∈ rawSub N G ↔ IsLayerConstant G p.1 ∧ IsLayerConstant G p.2 ∧
      (∀ x, x ∉ dataSites G → p.1 x = 0) ∧ ∀ x, x ∉ G.Ω 1 → p.2 x = 0 := Iff.rfl

theorem rawOf_mem_rawSub (D : BgData G N) : rawOf D ∈ rawSub N G :=
  ⟨D.Ψ_layerConst, D.h_layerConst, D.Ψ_zero, D.h_zero⟩

/-- The datum with prescribed raw data in `rawSub`. -/
def bgOfRaw (p : RawData d L (N₁ * L ^ m₁) K N) (hp : p ∈ rawSub N G) : BgData G N :=
  ⟨p.1, p.2, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩

theorem rawOf_bgOfRaw (p : RawData d L (N₁ * L ^ m₁) K N) (hp : p ∈ rawSub N G) :
    rawOf (bgOfRaw p hp) = p := rfl

variable (G) (a : ℕ → ℝ) (ν : ℝ) (σ ε : ℝ) (n : ℕ)

/-- **The chart as an explicit set of raw data.**  `Θ = (Ψ, h̃)` lies in `Ξ^c_n(𝔹; σ, ε)` iff it is
constant on blocks, vanishes off the data sites, and there are a real centre `(Ψ₀, h₀)` and a
complex displacement `(Ψ'', h'')` with `XiC` such that `Ψ = Ψ₀ + Ψ''` on `Ω₁ ∪ C(Ω₁)` and
`h̃ = h₀ + h''` on `Ω₁`. -/
theorem mem_xiCRaw_iff {p : RawData d L (N₁ * L ^ m₁) K N} :
    p ∈ XiCRaw (N := N) G a ν n σ ε ↔ p ∈ rawSub N G ∧
      ∃ (Ψ₀ : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℝ) (h₀ : Fin N → ℝ)
        (Ψ'' h'' : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ),
        XiC G a ν n σ ε Ψ₀ h₀ Ψ'' h'' ∧
        (∀ x ∈ dataSites G, ∀ i, p.1 x i = (Ψ₀ x i : ℂ) + Ψ'' x i) ∧
        ∀ x ∈ G.Ω 1, ∀ i, p.2 x i = (h₀ i : ℂ) + h'' x i := by
  constructor
  · rintro ⟨D, ⟨Ψ₀, h₀, Ψ'', h'', hX, hR⟩, rfl⟩
    exact ⟨rawOf_mem_rawSub D, Ψ₀, h₀, Ψ'', h'', hX, hR.1, hR.2⟩
  · rintro ⟨hp, Ψ₀, h₀, Ψ'', h'', hX, h1, h2⟩
    exact ⟨bgOfRaw p hp, ⟨Ψ₀, h₀, Ψ'', h'', hX, h1, h2⟩, rfl⟩

theorem XiCRaw_subset_rawSub : XiCRaw (N := N) G a ν n σ ε ⊆ (rawSub N G : Set _) :=
  fun _ hp => ((mem_xiCRaw_iff G a ν σ ε n).1 hp).1

/-- **The chart has empty interior** as soon as the subspace of data is proper in `RawData`
(for instance when some site is not in `Ω₁`, or some block has two sites). -/
theorem interior_xiCRaw_eq_empty (hproper : ∃ q : RawData d L (N₁ * L ^ m₁) K N, q ∉ rawSub N G) :
    interior (XiCRaw (N := N) G a ν n σ ε) = ∅ := by
  obtain ⟨q, hq⟩ := hproper
  refine Set.eq_empty_of_forall_notMem fun p hp => ?_
  have hpS : p ∈ rawSub N G := XiCRaw_subset_rawSub G a ν σ ε n (interior_subset hp)
  have hnhds : XiCRaw (N := N) G a ν n σ ε ∈ 𝓝 p := mem_interior_iff_mem_nhds.1 hp
  have hc : Continuous fun t : ℂ => p + t • q := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), p + t • q ∈ XiCRaw (N := N) G a ν n σ ε :=
    hc.continuousAt.eventually (by simpa using hnhds)
  have hev' : ∀ᶠ t in 𝓝[≠] (0 : ℂ), p + t • q ∈ XiCRaw (N := N) G a ν n σ ε :=
    nhdsWithin_le_nhds hev
  obtain ⟨t, ht, htne⟩ := (hev'.and self_mem_nhdsWithin).exists
  have hmem : p + t • q ∈ rawSub N G := XiCRaw_subset_rawSub G a ν σ ε n ht
  have : t • q ∈ rawSub N G := by simpa using (rawSub N G).sub_mem hmem hpS
  have h2 := (rawSub N G).smul_mem t⁻¹ this
  rw [smul_smul, inv_mul_cancel₀ htne, one_smul] at h2
  exact hq h2

end Sub

section L1

/-- The unit `ℓ¹` ball of sources is open: a strict inequality on a finite sum of norms. -/
theorem isOpen_l1Ball : IsOpen (l1Ball d L N₁ m₁ K N) :=
  isOpen_lt (by fun_prop) continuous_const

end L1

section Open

variable {X : Type*} [TopologicalSpace X]

/-- Finitely many strict inequalities between functions continuous at `x₀` persist near `x₀`. -/
theorem eventually_forall_lt {ι : Type*} [Finite ι] {x₀ : X} (P : ι → Prop) (f : ι → X → ℝ)
    (c : ι → ℝ) (hf : ∀ i, P i → ContinuousAt (f i) x₀) (h0 : ∀ i, P i → f i x₀ < c i) :
    ∀ᶠ x in 𝓝 x₀, ∀ i, P i → f i x < c i := by
  refine eventually_all.2 fun i => ?_
  by_cases hi : P i
  · filter_upwards [(hf i hi).eventually_lt continuousAt_const (h0 i hi)] with x hx _ using hx
  · exact Eventually.of_forall fun _ h => absurd h hi

theorem continuousAt_vn' {x₀ : X} {f : X → Fin N → ℂ} (h : ∀ i, ContinuousAt (fun x => f x i) x₀) :
    ContinuousAt (fun x => vn (f x)) x₀ :=
  continuous_vn.continuousAt.comp (continuousAt_pi.2 h)

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

theorem continuousAt_barField {x₀ : X} {A : X → Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ}
    {B : X → G.Ω 1 × Fin N → ℂ} (x : Torus d ((N₁ * L ^ m₁) * L ^ K)) (i : Fin N)
    (hA : ContinuousAt (fun q => A q x i) x₀)
    (hB : ∀ z i', ContinuousAt (fun q => B q (z, i')) x₀) :
    ContinuousAt (fun q => barField G (A q) (B q) x i) x₀ := by
  by_cases hx : x ∈ G.Ω 1
  · simp only [barField, hx, dite_true]; exact hB _ _
  · simp only [barField, hx, dite_false]; exact hA

theorem continuousAt_blockAvg {x₀ : X} {B : X → G.Ω 1 × Fin N → ℂ}
    (x : Torus d ((N₁ * L ^ m₁) * L ^ K)) (i : Fin N)
    (hB : ∀ z i', ContinuousAt (fun q => B q (z, i')) x₀) :
    ContinuousAt (fun q => blockAvg G (B q) x i) x₀ := by
  unfold blockAvg
  refine continuousAt_const.mul (tendsto_finsetSum _ fun y _ => ?_)
  unfold svec zeroExt
  by_cases hy : y ∈ G.Ω 1
  · simp only [hy, dite_true]; exact hB _ _
  · simp only [hy, dite_false]; exact continuousAt_const

end Open

section RelOpen

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- The field `A` shifted by `B - C` (the displacement of a nearby raw datum from the datum
`C`, added to a fixed displacement `A`). -/
def shiftF (A B C : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ) :
    Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ := fun x i => A x i + (B x i - C x i)

omit [NeZero N₁] [NeZero L] in
theorem shiftF_apply (A B C : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ) (x i) :
    shiftF A B C x i = A x i + (B x i - C x i) := rfl

omit [NeZero N₁] [NeZero L] in
theorem shiftF_self (A B : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ) :
    shiftF A B B = A := by
  funext x i; simp [shiftF_apply]

theorem isLayerConstant_shiftF {A B C : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ}
    (hA : IsLayerConstant G A) (hB : IsLayerConstant G B) (hC : IsLayerConstant G C) :
    IsLayerConstant G (shiftF A B C) := by
  intro n hn hk x hx x' hx'
  funext i
  simp only [shiftF_apply, hA n hn hk x hx x' hx', hB n hn hk x hx x' hx', hC n hn hk x hx x' hx']

/-- **The complex domain is open in the subspace of data**: if `D` lies in `Ψ̃^c(δ, ε')`, so does
every datum whose raw data are close to those of `D` (the same `δ, ε'`; the real part is kept and
the complex perturbation is shifted by the difference of the data). -/
theorem eventually_inDomainC_raw {ν δ ε' : ℝ} {D : BgData G N} (hD : InDomainC G ν δ ε' D) :
    ∀ᶠ q in 𝓝 (D.Ψ, D.h), q ∈ rawSub N G →
      ∃ (Ψ : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℝ) (h : Fin N → ℝ)
        (Ψ' h' : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ), InPsiTildeC G ν δ ε' Ψ h Ψ' h' ∧
        (∀ x ∈ dataSites G, ∀ i, q.1 x i = (Ψ x i : ℂ) + Ψ' x i) ∧
        ∀ x ∈ G.Ω 1, ∀ i, q.2 x i = (h i : ℂ) + h' x i := by
  classical
  obtain ⟨Ψ, h, Ψ', h', hP, hΨ, hh⟩ := hD
  have hq1 : ∀ x i, Continuous fun q : RawData d L (N₁ * L ^ m₁) K N => q.1 x i := fun x i => by
    fun_prop
  have hq2 : ∀ x i, Continuous fun q : RawData d L (N₁ * L ^ m₁) K N => q.2 x i := fun x i => by
    fun_prop
  have e1 := eventually_forall_lt (x₀ := ((D.Ψ, D.h) : RawData d L (N₁ * L ^ m₁) K N))
    (ι := Torus d ((N₁ * L ^ m₁) * L ^ K) × Torus d ((N₁ * L ^ m₁) * L ^ K))
    (fun xx => IsInterfacePair G xx.1 xx.2)
    (fun xx q => vn (fun i => shiftF Ψ' q.1 D.Ψ xx.1 i - shiftF Ψ' q.1 D.Ψ xx.2 i))
    (fun _ => δ)
    (fun xx _ => continuousAt_vn' fun i => by
      have := (hq1 xx.1 i); have := (hq1 xx.2 i)
      exact (by simp only [shiftF_apply]; fun_prop : Continuous fun q : RawData d L (N₁ * L ^ m₁) K N =>
        shiftF Ψ' q.1 D.Ψ xx.1 i - shiftF Ψ' q.1 D.Ψ xx.2 i).continuousAt)
    (fun xx hxx => by simp only [shiftF_self]; exact hP.c1 xx.1 xx.2 hxx)
  have e2 := eventually_forall_lt (x₀ := ((D.Ψ, D.h) : RawData d L (N₁ * L ^ m₁) K N))
    (ι := Torus d ((N₁ * L ^ m₁) * L ^ K)) (fun x => x ∈ dataSites G)
    (fun x q => vn (shiftF Ψ' q.1 D.Ψ x)) (fun _ => ε' + δ)
    (fun x _ => continuousAt_vn' fun i => by
      have := hq1 x i
      exact (by simp only [shiftF_apply]; fun_prop : Continuous fun q : RawData d L (N₁ * L ^ m₁) K N =>
        shiftF Ψ' q.1 D.Ψ x i).continuousAt)
    (fun x hx => by simp only [shiftF_self]; exact hP.c2a x hx)
  have e3 := eventually_forall_lt (x₀ := ((D.Ψ, D.h) : RawData d L (N₁ * L ^ m₁) K N))
    (ι := Torus d ((N₁ * L ^ m₁) * L ^ K)) (fun x => x ∈ dataSites G)
    (fun x q => ‖∑ i, ((Ψ x i : ℂ) + shiftF Ψ' q.1 D.Ψ x i) * ((Ψ x i : ℂ) + shiftF Ψ' q.1 D.Ψ x i) -
        ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ)‖) (fun _ => δ)
    (fun x _ => by
      have := hq1 x
      exact (by simp only [shiftF_apply]; fun_prop : Continuous fun q : RawData d L (N₁ * L ^ m₁) K N =>
        ‖∑ i, ((Ψ x i : ℂ) + shiftF Ψ' q.1 D.Ψ x i) * ((Ψ x i : ℂ) + shiftF Ψ' q.1 D.Ψ x i) -
        ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ)‖).continuousAt)
    (fun x hx => by simp only [shiftF_self]; exact hP.c2b x hx)
  have e4 := eventually_forall_lt (x₀ := ((D.Ψ, D.h) : RawData d L (N₁ * L ^ m₁) K N))
    (ι := Torus d ((N₁ * L ^ m₁) * L ^ K)) (fun x => x ∈ G.Ω 1)
    (fun x q => ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (shiftF h' q.2 D.h x))
    (fun _ => δ ^ 2 / ε')
    (fun x _ => continuousAt_const.mul (continuousAt_vn' fun i => by
      have := hq2 x i
      exact (by simp only [shiftF_apply]; fun_prop : Continuous fun q : RawData d L (N₁ * L ^ m₁) K N =>
        shiftF h' q.2 D.h x i).continuousAt))
    (fun x hx => by simp only [shiftF_self]; exact hP.c3a x hx)
  have e5 := eventually_forall_lt (x₀ := ((D.Ψ, D.h) : RawData d L (N₁ * L ^ m₁) K N))
    (ι := Torus d ((N₁ * L ^ m₁) * L ^ K)) (fun x => x ∈ G.Ω 1)
    (fun x q => ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
      ‖∑ i, ((Ψ x i / rn (Ψ x) : ℝ) : ℂ) * shiftF h' q.2 D.h x i‖)
    (fun _ => δ ^ 2)
    (fun x _ => by
      have := hq2 x
      exact (by simp only [shiftF_apply]; fun_prop : Continuous fun q : RawData d L (N₁ * L ^ m₁) K N =>
        ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
        ‖∑ i, ((Ψ x i / rn (Ψ x) : ℝ) : ℂ) * shiftF h' q.2 D.h x i‖).continuousAt)
    (fun x hx => by simp only [shiftF_self]; exact hP.c3b x hx)
  filter_upwards [e1, e2, e3, e4, e5] with q f1 f2 f3 f4 f5 hq
  refine ⟨Ψ, h, shiftF Ψ' q.1 D.Ψ, shiftF h' q.2 D.h,
    { toInPsiTilde := hP.toInPsiTilde, eps_pos := hP.eps_pos
      layerConst' := isLayerConstant_shiftF hP.layerConst' hq.1 D.Ψ_layerConst
      hLayerConst' := isLayerConstant_shiftF hP.hLayerConst' hq.2.1 D.h_layerConst
      c1 := fun x x' hxx => f1 (x, x') hxx
      c2a := fun x hx => f2 x hx
      c2b := fun x hx => f3 x hx
      c3a := fun x hx => f4 x hx
      c3b := fun x hx => f5 x hx }, fun x hx i => ?_, fun x hx i => ?_⟩
  · simp only [shiftF_apply]; linear_combination hΨ x hx i
  · simp only [shiftF_apply]; linear_combination hh x hx i

section Bounds

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
  {ν σ ε : ℝ} {Dr Dc : BgData G N} {Ψ'' h'' : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ}
  {φr φc : G.Ω 1 × Fin N → ℂ} {αr αc : G.Ω 1 → ℂ}
  (F : RawData d L (N₁ * L ^ m₁) K N → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))

theorem continuousAt_F_fst (hFc : ContinuousAt F (Dc.Ψ, Dc.h)) (z : G.Ω 1) (i : Fin N) :
    ContinuousAt (fun q : RawData d L (N₁ * L ^ m₁) K N => (F q).1 (z, i)) (Dc.Ψ, Dc.h) :=
  (((continuous_apply (z, i)).comp continuous_fst).continuousAt).comp hFc

theorem continuousAt_F_snd (hFc : ContinuousAt F (Dc.Ψ, Dc.h)) (z : G.Ω 1) :
    ContinuousAt (fun q : RawData d L (N₁ * L ^ m₁) K N => (F q).2 z) (Dc.Ψ, Dc.h) :=
  (((continuous_apply z).comp continuous_snd).continuousAt).comp hFc

theorem continuousAt_diffField (hFc : ContinuousAt F (Dc.Ψ, Dc.h)) (x : Torus d ((N₁ * L ^ m₁) * L ^ K))
    (i : Fin N) :
    ContinuousAt (fun q : RawData d L (N₁ * L ^ m₁) K N =>
      barField G q.1 (F q).1 x i - barField G Dr.Ψ φr x i) (Dc.Ψ, Dc.h) :=
  (continuousAt_barField x i (by fun_prop : Continuous fun q : RawData d L (N₁ * L ^ m₁) K N =>
    q.1 x i).continuousAt (continuousAt_F_fst F hFc)).sub continuousAt_const

variable (hFc : ContinuousAt F (Dc.Ψ, Dc.h)) (hF0 : F (Dc.Ψ, Dc.h) = (φc, αc))
  (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc)

include hFc hF0 hb in
theorem ev_grad : ∀ᶠ q in 𝓝 ((Dc.Ψ, Dc.h) : RawData d L (N₁ * L ^ m₁) K N), ∀ xb : (Torus d ((N₁ * L ^ m₁) * L ^ K) × Fin d) × Bool, xb.1.1 ∈ G.Ω 1 →
    (if xb.2 then
      vn (fun i => (barField G q.1 (F q).1 (xb.1.1 + Pi.single xb.1.2 1) i -
          barField G Dr.Ψ φr (xb.1.1 + Pi.single xb.1.2 1) i) -
        (barField G q.1 (F q).1 xb.1.1 i - barField G Dr.Ψ φr xb.1.1 i))
      else vn (fun i => (barField G q.1 (F q).1 (xb.1.1 - Pi.single xb.1.2 1) i -
          barField G Dr.Ψ φr (xb.1.1 - Pi.single xb.1.2 1) i) -
        (barField G q.1 (F q).1 xb.1.1 i - barField G Dr.Ψ φr xb.1.1 i))) <
      σ * ε / G.spacing xb.1.1 := by
  refine eventually_forall_lt (x₀ := ((Dc.Ψ, Dc.h) : RawData d L (N₁ * L ^ m₁) K N)) _ _ _ (fun xb _ => ?_) (fun xb hx => ?_)
  · cases xb.2
    · exact continuousAt_vn' fun i => (continuousAt_diffField F hFc _ i).sub
        (continuousAt_diffField F hFc _ i)
    · exact continuousAt_vn' fun i => (continuousAt_diffField F hFc _ i).sub
        (continuousAt_diffField F hFc _ i)
  · obtain ⟨⟨x, μ⟩, b⟩ := xb
    have := hb.grad x hx μ
    rw [hF0] at *
    cases b
    · exact this.2
    · exact this.1

include hFc hF0 hb in
theorem ev_lap : ∀ᶠ q in 𝓝 ((Dc.Ψ, Dc.h) : RawData d L (N₁ * L ^ m₁) K N), ∀ x : Torus d ((N₁ * L ^ m₁) * L ^ K), x ∈ G.Ω 1 →
    vn (fun i => ∑ μ : Fin d,
      ((barField G q.1 (F q).1 (x + Pi.single μ 1) i - barField G Dr.Ψ φr (x + Pi.single μ 1) i) +
        (barField G q.1 (F q).1 (x - Pi.single μ 1) i - barField G Dr.Ψ φr (x - Pi.single μ 1) i) -
        2 * (barField G q.1 (F q).1 x i - barField G Dr.Ψ φr x i))) <
      σ ^ 2 * ε / G.spacing x ^ 2 := by
  refine eventually_forall_lt (x₀ := ((Dc.Ψ, Dc.h) : RawData d L (N₁ * L ^ m₁) K N)) _ _ _ (fun x _ => ?_) (fun x hx => ?_)
  · exact continuousAt_vn' fun i => tendsto_finsetSum _ fun μ _ =>
      ((continuousAt_diffField F hFc _ i).add (continuousAt_diffField F hFc _ i)).sub
        (continuousAt_const.mul (continuousAt_diffField F hFc _ i))
  · have := hb.lap x hx
    rw [hF0] at *
    exact this

include hFc hF0 hb in
theorem ev_mult : ∀ᶠ q in 𝓝 ((Dc.Ψ, Dc.h) : RawData d L (N₁ * L ^ m₁) K N), ∀ x : G.Ω 1,
    G.spacing (x : Torus d ((N₁ * L ^ m₁) * L ^ K)) ^ 2 * ‖(F q).2 x - αr x‖ < σ ^ 2 * ε := by
  have := eventually_forall_lt (x₀ := ((Dc.Ψ, Dc.h) : RawData d L (N₁ * L ^ m₁) K N)) (ι := G.Ω 1) (fun _ => True)
    (fun x q => G.spacing (x : Torus d ((N₁ * L ^ m₁) * L ^ K)) ^ 2 * ‖(F q).2 x - αr x‖) (fun _ => σ ^ 2 * ε)
    (fun x _ => continuousAt_const.mul (((continuousAt_F_snd F hFc x).sub continuousAt_const).norm))
    (fun x _ => by have := hb.mult x; rw [hF0] at *; exact this)
  filter_upwards [this] with q hq x using hq x trivial

include hFc hF0 hb in
theorem ev_val : ∀ᶠ q in 𝓝 ((Dc.Ψ, Dc.h) : RawData d L (N₁ * L ^ m₁) K N), ∀ x : G.Ω 1,
    vn (fun i => (F q).1 (x, i) - φr (x, i)) < ε := by
  have := eventually_forall_lt (x₀ := ((Dc.Ψ, Dc.h) : RawData d L (N₁ * L ^ m₁) K N)) (ι := G.Ω 1) (fun _ => True)
    (fun x q => vn (fun i => (F q).1 (x, i) - φr (x, i))) (fun _ => ε)
    (fun x _ => continuousAt_vn' fun i => (continuousAt_F_fst F hFc x i).sub continuousAt_const)
    (fun x _ => by have := hb.val x; rw [hF0] at *; exact this)
  filter_upwards [this] with q hq x using hq x trivial

include hFc hF0 hb in
theorem ev_close : ∀ᶠ q in 𝓝 ((Dc.Ψ, Dc.h) : RawData d L (N₁ * L ^ m₁) K N), ∀ x : Torus d ((N₁ * L ^ m₁) * L ^ K), x ∈ G.Ω 1 →
    vn (fun i => shiftF Ψ'' q.1 Dc.Ψ x i - blockAvg G ((F q).1 - φr) x i) < σ ^ 2 * ε := by
  refine eventually_forall_lt (x₀ := ((Dc.Ψ, Dc.h) : RawData d L (N₁ * L ^ m₁) K N)) _ _ _ (fun x _ => ?_) (fun x hx => ?_)
  · exact continuousAt_vn' fun i =>
      (by simp only [shiftF_apply]; have := (by fun_prop : Continuous fun q : RawData d L (N₁ * L ^ m₁) K N => q.1 x i)
          fun_prop :
        Continuous fun q : RawData d L (N₁ * L ^ m₁) K N => shiftF Ψ'' q.1 Dc.Ψ x i).continuousAt.sub
        (continuousAt_blockAvg x i fun z i' =>
          (continuousAt_F_fst F hFc z i').sub continuousAt_const)
  · have := hb.close x hx
    rw [hF0] at *
    simpa [shiftF_self] using this

include hb in
theorem ev_collar : ∀ᶠ q in 𝓝 ((Dc.Ψ, Dc.h) : RawData d L (N₁ * L ^ m₁) K N), ∀ zz : Torus d ((N₁ * L ^ m₁) * L ^ K) × Torus d ((N₁ * L ^ m₁) * L ^ K),
    (zz.1 ∈ collar G ∧ zz.2 ∈ collar G ∧ Adj zz.1 zz.2) →
    vn (fun i => shiftF Ψ'' q.1 Dc.Ψ zz.1 i - shiftF Ψ'' q.1 Dc.Ψ zz.2 i) < σ * ε := by
  refine eventually_forall_lt (x₀ := ((Dc.Ψ, Dc.h) : RawData d L (N₁ * L ^ m₁) K N)) _ _ _ (fun zz _ => ?_) (fun zz hz => ?_)
  · exact continuousAt_vn' fun i =>
      (by simp only [shiftF_apply]
          have := (by fun_prop : Continuous fun q : RawData d L (N₁ * L ^ m₁) K N => q.1 zz.1 i)
          have := (by fun_prop : Continuous fun q : RawData d L (N₁ * L ^ m₁) K N => q.1 zz.2 i)
          fun_prop :
        Continuous fun q : RawData d L (N₁ * L ^ m₁) K N => shiftF Ψ'' q.1 Dc.Ψ zz.1 i - shiftF Ψ'' q.1 Dc.Ψ zz.2 i).continuousAt
  · have := hb.collarBond zz.1 hz.1 zz.2 hz.2.1 hz.2.2
    simp only [shiftF_self]
    exact this

include hb in
theorem ev_hAbs : ∀ᶠ q in 𝓝 ((Dc.Ψ, Dc.h) : RawData d L (N₁ * L ^ m₁) K N), ∀ x : Torus d ((N₁ * L ^ m₁) * L ^ K), x ∈ G.Ω 1 →
    ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (shiftF h'' q.2 Dc.h x) < (σ * ε) ^ 2 / ε := by
  refine eventually_forall_lt (x₀ := ((Dc.Ψ, Dc.h) : RawData d L (N₁ * L ^ m₁) K N)) _ _ _ (fun x _ => ?_) (fun x hx => ?_)
  · exact continuousAt_const.mul (continuousAt_vn' fun i =>
      (by simp only [shiftF_apply]; have := (by fun_prop : Continuous fun q : RawData d L (N₁ * L ^ m₁) K N => q.2 x i)
          fun_prop :
        Continuous fun q : RawData d L (N₁ * L ^ m₁) K N => shiftF h'' q.2 Dc.h x i).continuousAt)
  · have := hb.hAbs x hx
    simp only [shiftF_self]
    exact this

include hb in
theorem ev_hDot : ∀ᶠ q in 𝓝 ((Dc.Ψ, Dc.h) : RawData d L (N₁ * L ^ m₁) K N), ∀ x : G.Ω 1,
    ν * ((L : ℝ) ^ G.layerIndex (x : Torus d ((N₁ * L ^ m₁) * L ^ K))) ^ 2 * ‖∑ i, φr (x, i) * shiftF h'' q.2 Dc.h x i‖ <
      (σ * ε) ^ 2 := by
  have := eventually_forall_lt (x₀ := ((Dc.Ψ, Dc.h) : RawData d L (N₁ * L ^ m₁) K N)) (ι := G.Ω 1) (fun _ => True)
    (fun x q => ν * ((L : ℝ) ^ G.layerIndex (x : Torus d ((N₁ * L ^ m₁) * L ^ K))) ^ 2 *
      ‖∑ i, φr (x, i) * shiftF h'' q.2 Dc.h x i‖) (fun _ => (σ * ε) ^ 2)
    (fun x _ => continuousAt_const.mul (tendsto_finsetSum _ fun i _ =>
      continuousAt_const.mul
        (by simp only [shiftF_apply]; have := (by fun_prop : Continuous fun q : RawData d L (N₁ * L ^ m₁) K N => q.2 x i)
            fun_prop :
          Continuous fun q : RawData d L (N₁ * L ^ m₁) K N => shiftF h'' q.2 Dc.h x i).continuousAt).norm)
    (fun x _ => by have := hb.hDot x; simp only [shiftF_self]; exact this)
  filter_upwards [this] with q hq x using hq x trivial

end Bounds

/-- **The chart is open in the subspace of data.**  If `D` realizes a member of `Ξ^c_n(𝔹; σ, ε)`
then every raw datum `q` of the subspace `rawSub N G` near those of `D` lies in `XiCRaw` (same
centre `(Ψ₀, h₀)` and constants `σ, ε`; the displacement is shifted by `q - rawOf D`).  All
inequalities of `XiC` that involve the datum are strict, and the background
`(bgFieldC, bgMultC)` is continuous in the raw data on the domain (`theorem72_analytic`). -/
theorem xiCRaw_eventually {a : ℕ → ℝ} {ν : ℝ} {σ ε : ℝ} {n : ℕ}
    (H : BgHyp d L K ϱ a ν) {D : BgData G N} (hD : XiCData G a ν n σ ε D) :
    ∀ᶠ q in 𝓝[(rawSub N G : Set (RawData d L (N₁ * L ^ m₁) K N))] (rawOf D),
      q ∈ XiCRaw G a ν n σ ε := by
  classical
  obtain ⟨Ψ₀, h₀, Ψ'', h'', ⟨hσ, hε, Dr, Dc, hXr, hC, hDcU, hb⟩, hRD⟩ := hD
  obtain rfl : Dc = D := BgData.eq_of_realizesC hC hRD
  obtain ⟨F, hFan, hFe⟩ := theorem72_analytic (G := G) (a := a) (ν := ν) H
  have hF0 : F (Dc.Ψ, Dc.h) = (bgFieldC G a ν (bgC0 d L N) Dc, bgMultC G a ν (bgC0 d L N) Dc) :=
    hFe Dc hDcU
  have hFc : ContinuousAt F (Dc.Ψ, Dc.h) := (hFan _ ⟨Dc, hDcU, rfl⟩).continuousAt
  obtain ⟨δ, ε', hδ0, hδε, hε'c, hδc, hνε, hdom⟩ := hDcU
  have eDom := eventually_inDomainC_raw hdom
  have e1 := ev_grad F hFc hF0 hb
  have e2 := ev_lap F hFc hF0 hb
  have e3 := ev_mult F hFc hF0 hb
  have e4 := ev_val F hFc hF0 hb
  have e5 := ev_close F hFc hF0 hb
  have e6 := ev_collar (Dc := Dc) hb
  have e7 := ev_hAbs (Dc := Dc) hb
  have e8 := ev_hDot (Dc := Dc) hb
  show ∀ᶠ q in 𝓝[(rawSub N G : Set (RawData d L (N₁ * L ^ m₁) K N))] ((Dc.Ψ, Dc.h) : RawData d L (N₁ * L ^ m₁) K N), _
  filter_upwards [nhdsWithin_le_nhds eDom, nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2,
    nhdsWithin_le_nhds e3, nhdsWithin_le_nhds e4, nhdsWithin_le_nhds e5,
    nhdsWithin_le_nhds e6, nhdsWithin_le_nhds e7, nhdsWithin_le_nhds e8,
    self_mem_nhdsWithin] with q hdq g l m v c col ha hd hqS
  obtain ⟨Ψ, h, Ψ', h', hP, hΨ, hh⟩ := hdq hqS
  have hU : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν (bgOfRaw q hqS) :=
    ⟨δ, ε', hδ0, hδε, hε'c, hδc, hνε, Ψ, h, Ψ', h', hP, hΨ, hh⟩
  have hFq := hFe (bgOfRaw q hqS) hU
  have h1 : (F q).1 = bgFieldC G a ν (bgC0 d L N) (bgOfRaw q hqS) := congrArg Prod.fst hFq
  have h2 : (F q).2 = bgMultC G a ν (bgC0 d L N) (bgOfRaw q hqS) := congrArg Prod.snd hFq
  refine (mem_xiCRaw_iff G a ν σ ε n).2 ⟨hqS, Ψ₀, h₀, shiftF Ψ'' q.1 Dc.Ψ, shiftF h'' q.2 Dc.h,
    ⟨hσ, hε, Dr, bgOfRaw q hqS, hXr, ⟨fun x hx i => ?_, fun x hx i => ?_⟩, hU, ?_⟩,
    fun x hx i => ?_, fun x hx i => ?_⟩
  · have := hC.1 x hx i
    show q.1 x i = _
    simp only [shiftF_apply]; linear_combination this
  · have := hC.2 x hx i
    show q.2 x i = _
    simp only [shiftF_apply]; linear_combination this
  · rw [← h1, ← h2]
    exact
      { grad := fun x hx μ => ⟨by have h := g ((x, μ), true) hx; simp only [↓reduceIte] at h; exact h,
          by have h := g ((x, μ), false) hx; simp only [↓reduceIte, Bool.false_eq_true] at h; exact h⟩
        lap := fun x hx => l x hx
        mult := fun x => m x
        val := fun x => v x
        close := fun x hx => c x hx
        collarBond := fun z hz z' hz' hadj => col (z, z') ⟨hz, hz', hadj⟩
        hAbs := fun x hx => ha x hx
        hDot := fun x => hd x }
  · have := hC.1 x hx i
    simp only [shiftF_apply]; linear_combination this
  · have := hC.2 x hx i
    simp only [shiftF_apply]; linear_combination this

/-- **Relative openness of the chart** (`XiCRaw` is open in the subspace `rawSub N G`): in the
subspace topology, the chart is an open subset of the subspace of data. -/
theorem isOpen_preimage_xiCRaw {a : ℕ → ℝ} {ν : ℝ} {σ ε : ℝ} {n : ℕ} (H : BgHyp d L K ϱ a ν) :
    IsOpen (((↑) : (rawSub N G) → RawData d L (N₁ * L ^ m₁) K N) ⁻¹' XiCRaw G a ν n σ ε) := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨p, hpS⟩ hp
  obtain ⟨D, hD, rfl⟩ := hp
  have := xiCRaw_eventually H hD
  rw [nhdsWithin_eq_map_subtype_coe hpS] at this
  exact Filter.mem_map.1 this

end RelOpen

end Balaban.Localization
