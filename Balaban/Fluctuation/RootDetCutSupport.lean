/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RootDetChart
public import Balaban.Localization.DecLogCutFactor
import Mathlib.Tactic.Linarith

/-!
# Support of the rooted trace on the cut chart (DET-CUT-FACTOR, consequences)

Consequences of `Balaban/Localization/DecLogCutFactor.lean` for `rootTrace` and the mixed
differences of `RootDetChart.lean`.

* `rootTrace_eq_of_comp` (T5, locality): the rooted trace over coarse sites carrying the label of a
  union `Y'` of components of `Yreg s` and `Yreg s'` is the same for two data whose cut factors
  agree on the cubes inside `Y'` and whose potentials and fields agree on `Y'`.
* `rootTrace_eq_baseline_of_not_label`: for sites whose label is false the rooted trace is the
  cut-independent baseline.
* `mixDiff_eq_zero_of_update_invariant` (T6, algebra): a function that does not depend on the
  variable `p` on the cube `{0,1}^𝒫` has vanishing mixed difference for every `J ∋ p`.
* `mixDiff_rootTrace_eq_zero_of_separated`: the mixed difference of the rooted trace vanishes when
  `J` contains `p` and, at every cut point, the component structure separates `p` from `B`.
* `mixDiff_rootTrace_eq_zero_of_not_attached`: it vanishes for non-empty `J` when no coarse site of
  `B` is attached to `Yreg` at any cut point of a subset of `J`; for `|J| = 1` this says that the
  region of the parameter cube does not meet the blocks of `B`.

The decay (forest) bound and the count of cut sets per cube set are not proved here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Finset Matrix

section Algebra


variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- **Vanishing of mixed differences.** If `F` does not depend on the variable `p` on the cube
`{0,1}^ι` then `mixDiff J F = 0` for every `J ∋ p`. -/
theorem mixDiff_eq_zero_of_update_invariant {p : ι} {J : Finset ι} (hp : p ∈ J)
    (F : (ι → ℂ) → ℂ)
    (hF : ∀ σ : ι → ℂ, (∀ q, σ q = 0 ∨ σ q = 1) → ∀ t : ℂ, (t = 0 ∨ t = 1) →
      F (Function.update σ p t) = F σ) : mixDiff J F = 0 := by
  classical
  obtain ⟨J', hpJ', rfl⟩ : ∃ J', p ∉ J' ∧ J = insert p J' :=
    ⟨J.erase p, Finset.notMem_erase p J, (Finset.insert_erase hp).symm⟩
  rw [mixDiff_insert hpJ']
  unfold mixDiff cutDiff
  refine Finset.sum_eq_zero fun I _ => ?_
  have h01 : ∀ q, cutPt I q = 0 ∨ cutPt I q = 1 := by
    intro q; unfold cutPt; split_ifs <;> simp
  rw [hF _ h01 1 (Or.inr rfl), hF _ h01 0 (Or.inl rfl)]
  simp

end Algebra

section Trace

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν κ κ' δ δ' : ℝ}
variable {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}

/-- **T5. The rooted trace depends only on the data near the component.** Two data
`(s, α, φ)`, `(s', α', φ')` satisfy `CovStanding`; `Y'` is a union of nearest-neighbour components
of `Yreg (extS s)` and of `Yreg (extS s')`; the parameters agree on the footprints `Qset q` of the
cubes `q` of the cover that lie inside `Y'` (so the cut factors `sProd` agree there); the potentials
and the fields agree on `Y'`; `Q`, `P` respect the labels `cκ`. Then the rooted trace over a set
`B` of coarse sites with label `cκ` is the same for both data. -/
theorem rootTrace_eq_of_comp {s s' : DecParams G}
    {α α' : G.Ω 1 → ℂ} {φ φ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    (H : CovStanding G a aT ν α κ (extS G s) δ φ Q P)
    (H' : CovStanding G a aT ν α' κ' (extS G s') δ' φ' Q P) (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G (extS G s)) Y')
    (hY' : IsNnComp (Yreg G (extS G s')) Y')
    (hs : ∀ q ∈ cubeIdx G, SubI G (intBox q) Y' → ∀ R ∈ Qset G q, extS G s R = extS G s' R)
    (hA : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' → α y = α' y)
    (hφ : ∀ y : CTorus d L N₁ m₁ (k + 1), y ∈ Y' → φ y = φ' y) (cκ : κι → Prop)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') Q) (hP : BD cκ cκ P)
    (B : Finset κι) (hB : ∀ y ∈ B, cκ y) :
    rootTrace G a aT ν Q P B s φ α = rootTrace G a aT ν Q P B s' φ' α' := by
  have key : ∀ y ∈ B, ∀ i : Fin N, decLog G a aT ν α (extS G s) φ Q P (y, i) (y, i) =
      decLog G a aT ν α' (extS G s') φ' Q P (y, i) (y, i) := fun y hy i =>
    H.decLog_agree H' hconn hY hY'
      (fun q hq hsub => Finset.prod_congr rfl (hs q hq hsub)) hA hφ cκ hQ hP (y, i) (y, i)
      (hB y hy) (hB y hy)
  unfold rootTrace
  rw [Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl (fun i _ => key y hy i)]

/-- The cut-independent baseline blocks of `decLog`, as a function of the parameters. -/
theorem rootTrace_eq_baseline_of_not_label {s : DecParams G}
    {α : G.Ω 1 → ℂ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    (H : CovStanding G a aT ν α κ (extS G s) δ φ Q P) (hconn : HatConn G) (cκ : κι → Prop)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Yreg G (extS G s)) Q)
    (hP : BD cκ cκ P) (B : Finset κι) (hB : ∀ y ∈ B, ¬ cκ y) :
    rootTrace G a aT ν Q P B s φ α =
      -(1 / 2 : ℂ) * ∑ y ∈ B, ∑ i : Fin N,
        (((Real.log (a k) : ℝ) : ℂ) • (1 - liftOp N P) +
          ((Real.log (a k + aT / (L : ℝ) ^ 2) : ℝ) : ℂ) • liftOp N P) (y, i) (y, i) := by
  have key : ∀ y ∈ B, ∀ i : Fin N, decLog G a aT ν α (extS G s) φ Q P (y, i) (y, i) =
      (((Real.log (a k) : ℝ) : ℂ) • (1 - liftOp N P) +
          ((Real.log (a k + aT / (L : ℝ) ^ 2) : ℝ) : ℂ) • liftOp N P) (y, i) (y, i) :=
    fun y hy i => H.decLog_row_eq_baseline hconn cκ hQ hP (p := (y, i)) (hB y hy) (y, i)
  unfold rootTrace
  rw [Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl (fun i _ => key y hy i)]


section Cuts

variable (S : XSetting G a aT ν) {κ : ℝ} (hκ : 0 < κ)
  (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hU : IsUnitLattice G Q P)
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hφ : IsConstraintFieldStrict G δ φ)
  {α : G.Ω 1 → ℂ}
  (hα : ∀ w, ‖α w‖ < coerciveConst d / (2 * (G.spacing (w : CTorus d L N₁ m₁ (k + 1))) ^ 2))

include S hκ hM hδ hsm hU hφ hα

/-- The standing hypotheses hold at every `{0,1}`-valued cut point. -/
theorem covStanding_of_zero_one {σ : DecParams G} (h01 : ∀ q, σ q = 0 ∨ σ q = 1) :
    CovStanding G a aT ν α κ (extS G σ) δ φ Q P := by
  refine covStanding_of_mem (N := N) S hκ.le hM hδ hsm hU (e := ((σ, (φ, α)) : DecData G N))
    ⟨fun R => ?_, hφ, hα⟩
  rcases h01 R with h | h
  · simp [h, Real.exp_pos]
  · simp [h, Real.one_lt_exp_iff.2 hκ]

/-- **T6. Vanishing of the mixed difference of the rooted trace (separation form).** Let `J`
contain the parameter cube `p`. Suppose that at every `{0,1}`-valued cut point `σ`, and for both
values `t ∈ {0, 1}` of the cut parameter `p`, there is a union `Y'` of components of both
`Yreg (extS σ)` and `Yreg (extS (σ[p ↦ t]))` carrying the labels of `B`, on whose cubes the
parameters of the two cut points agree (the parameter cube `p` is not attached to the component of
`B`); and `Q`, `P` respect the labels. Then `mixDiff J` of the rooted trace vanishes. -/
theorem mixDiff_rootTrace_eq_zero_of_separated (B : Finset κι) (hconn : HatConn G)
    {J : Finset (cubeIdx G)} {p : cubeIdx G} (hp : p ∈ J)
    (hsep : ∀ σ : DecParams G, (∀ q, σ q = 0 ∨ σ q = 1) → ∀ t : ℂ, (t = 0 ∨ t = 1) →
      ∃ (Y' : Finset (CTorus d L N₁ m₁ (k + 1))) (cκ : κι → Prop),
        IsNnComp (Yreg G (extS G σ)) Y' ∧
        IsNnComp (Yreg G (extS G (Function.update σ p t))) Y' ∧
        (∀ q ∈ cubeIdx G, SubI G (intBox q) Y' →
          ∀ R ∈ Qset G q, extS G σ R = extS G (Function.update σ p t) R) ∧
        BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') Q ∧ BD cκ cκ P ∧
        ∀ y ∈ B, cκ y) :
    mixDiff J (fun s => rootTrace G a aT ν Q P B s φ α) = 0 := by
  refine mixDiff_eq_zero_of_update_invariant hp _ fun σ h01 t ht => ?_
  have h01' : ∀ q, Function.update σ p t q = 0 ∨ Function.update σ p t q = 1 := by
    intro q
    by_cases h : q = p
    · subst h; simpa using ht
    · rw [Function.update_of_ne h]; exact h01 q
  obtain ⟨Y', cκ, hY, hY', hs, hQ, hP, hB⟩ := hsep σ h01 t ht
  exact (rootTrace_eq_of_comp (covStanding_of_zero_one S hκ hM hδ hsm hU hφ hα h01)
    (covStanding_of_zero_one S hκ hM hδ hsm hU hφ hα h01') hconn hY hY' hs (fun _ _ => rfl)
    (fun _ _ => rfl) cκ hQ hP B hB).symm

/-- **T6, non-attachment form.** If `J` is non-empty and, at the cut point `1_{J'}` of every
`J' ⊆ J`, no coarse site of `B` carries a label of `Yreg` (no patch of the cut point reaches `B`),
then all the values of the rooted trace on the cube `{0,1}^J` are the cut-independent baseline and
`mixDiff J` vanishes. For `J = {p}` this says that the region `Yreg` of the single parameter cube
does not meet the blocks of `B`. -/
theorem mixDiff_rootTrace_eq_zero_of_not_attached (B : Finset κι) (hconn : HatConn G)
    {J : Finset (cubeIdx G)} (hJ : J.Nonempty)
    (hna : ∀ J' ⊆ J, ∃ cκ : κι → Prop,
      BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈
        Yreg G (extS G (cutPt J'))) Q ∧ BD cκ cκ P ∧ ∀ y ∈ B, ¬ cκ y) :
    mixDiff J (fun s => rootTrace G a aT ν Q P B s φ α) = 0 := by
  classical
  set b : ℂ := -(1 / 2 : ℂ) * ∑ y ∈ B, ∑ i : Fin N,
        (((Real.log (a k) : ℝ) : ℂ) • (1 - liftOp N P) +
          ((Real.log (a k + aT / (L : ℝ) ^ 2) : ℝ) : ℂ) • liftOp N P) (y, i) (y, i) with hb
  have hval : ∀ J' ∈ J.powerset, rootTrace G a aT ν Q P B (cutPt J') φ α = b := by
    intro J' hJ'
    obtain ⟨cκ, hQ, hP, hB⟩ := hna J' (Finset.mem_powerset.1 hJ')
    have h01 : ∀ q, cutPt J' q = 0 ∨ cutPt J' q = 1 := by
      intro q; unfold cutPt; split_ifs <;> simp
    exact rootTrace_eq_baseline_of_not_label
      (covStanding_of_zero_one S hκ hM hδ hsm hU hφ hα h01) hconn cκ hQ hP B hB
  unfold mixDiff
  rw [Finset.sum_congr rfl fun J' hJ' => by simp only []; rw [hval J' hJ']]
  have hsign : ∀ I ∈ J.powerset, (-1 : ℂ) ^ (J.card - I.card) =
      (-1) ^ J.card * (-1) ^ I.card := by
    intro I hI
    have hle := Finset.card_le_card (Finset.mem_powerset.1 hI)
    have h1 : (-1 : ℂ) ^ I.card * (-1) ^ I.card = 1 := by
      rw [← mul_pow]; norm_num
    calc (-1 : ℂ) ^ (J.card - I.card) = (-1) ^ (J.card - I.card) * ((-1) ^ I.card * (-1) ^ I.card) := by
          rw [h1, mul_one]
      _ = ((-1) ^ (J.card - I.card) * (-1) ^ I.card) * (-1) ^ I.card := by ring
      _ = _ := by rw [← pow_add, Nat.sub_add_cancel hle]
  have hz : ∑ I ∈ J.powerset, (-1 : ℂ) ^ I.card = 0 := by
    have := Finset.sum_powerset_neg_one_pow_card_of_nonempty hJ
    exact_mod_cast this
  rw [← Finset.sum_mul, Finset.sum_congr rfl hsign, ← Finset.mul_sum, hz, mul_zero, zero_mul]

end Cuts

end Trace


section NonVacuity

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

theorem extS_cutPt_of_mem {J : Finset (cubeIdx G)} {R : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hR : R ∈ cubeIdx G) : extS G (cutPt J) R = if (⟨R, hR⟩ : cubeIdx G) ∈ J then 1 else 0 := by
  classical
  simp [extS, cutPt, hR]

/-- **The active centres at the cut point `1_J`.** A centre `z` has non-zero factor `s_z` at the cut
point that is `1` on `J` and `0` on the other parameter cubes iff every parameter cube of its
footprint `𝒬(z)` lies in `J`. -/
theorem mem_Zs_extS_cutPt_iff {J : Finset (cubeIdx G)} {z : ℕ × CTorus d L N₁ m₁ (k + 1)} :
    z ∈ Zs G (extS G (cutPt J)) ↔
      z ∈ cubeIdx G ∧ ∀ R (hR : R ∈ cubeIdx G), R ∈ Qset G z → (⟨R, hR⟩ : cubeIdx G) ∈ J := by
  classical
  unfold Zs
  rw [Finset.mem_filter, sProd_ne_zero_iff]
  refine and_congr_right fun _ => ⟨fun h R hR hRz => ?_, fun h R hRz => ?_⟩
  · have := h R hRz
    rw [extS_cutPt_of_mem hR] at this
    by_contra hJ
    exact this (by simp [hJ])
  · have hR := Qset_subset_cubeIdx z hRz
    rw [extS_cutPt_of_mem hR]
    simp [h R hR hRz]

/-- **A non-trivial cut point.** For every centre `z` of the cover, the cut point that switches on
exactly the parameter cubes of the footprint of `z` has `z` active, so the thickened cube of `z`
lies in `Yreg`. (At the zero cut point `Yreg` is empty: `Yreg_zeroCuts`.) -/
theorem hatI_subset_Yreg_cutPt {z : ℕ × CTorus d L N₁ m₁ (k + 1)} (hz : z ∈ cubeIdx G) :
    hatI G z ⊆ Yreg G (extS G (cutPt ((Qset G z).subtype (· ∈ cubeIdx G)))) := by
  classical
  have hzZ : z ∈ Zs G (extS G (cutPt ((Qset G z).subtype (· ∈ cubeIdx G)))) := by
    rw [mem_Zs_extS_cutPt_iff]
    exact ⟨hz, fun R hR hRz => by simp [hRz]⟩
  intro y hy
  unfold hatI at hy
  rw [Finset.mem_filter] at hy
  unfold Yreg
  rw [Finset.mem_filter, Finset.mem_biUnion]
  exact ⟨⟨z, hzZ, hy.1⟩, hy.2⟩

end NonVacuity

end Balaban.Fluctuation
