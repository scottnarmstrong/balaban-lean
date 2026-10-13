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

end Balaban.Localization
