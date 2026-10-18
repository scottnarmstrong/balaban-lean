/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.Witness
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The last integral of the spine from four sub-inputs

`lastIntegralInput_of_parts` proves the spine input `LastIntegralInput` (A6, LF-8 (a),
`Spine/RootFInputs.lean`) from four named sub-inputs, following LFR Theorem IV.4.1, Definition
IV.5.2 and Theorem IV.5.3. For a member `ρ` of `ℛ♭_k` at the stopping scale, with a
representation `F`, the activities of Root-F are split by scale and, at the last scale, by the
two parts of the last integral of P7 §4:

* for `1 ≤ j ≤ k`, the inherited observable activities
  `q_j(X; g) = ∑_{x ∈ X} ⟨g(x), ℳ^{(j)}(x, X; h, h, g)⟩` (`inhObs`): the terms (H.7) of the
  small-field datum `𝔰 = F.sf` at the constant configuration, read on Root-F's torus (LFR Definition
  IV.5.2, first item; P4 (H.7), P7 (4.17); they are not changed after their creation, P4 (1.8));
* at the scale `k + 1`, the activities of the small-field part `Ξ^sf` of the last integral
  (`sfIntegral`: the integral of the small-field factor `χ_k(T) exp(𝒜_k + ℱ_k + ℛ^{(k)})(T)` of
  (D1) on the whole torus, the term of P7 (4.1)–(4.9) with no large-field region), which collect
  `ℳ^{(k+1)}_0` and the polymer terms `ℛ^{(k+1)}_n` (P7 (4.9), (4.15)–(4.17)), plus the
  activities `𝒫^{(k+1)}` of the large-field part `∫ ρ / Ξ^sf` (the linked gas of P7 (4.11)–(4.14)).

The sub-inputs:

* `InheritedBoundInput` (the conversion of the observable terms; LFR Theorem IV.5.3 items 2, 4, 5
  for `j ≤ k_f`): `inhObs` vanishes off scale-`j` polymers, is analytic on the unit `ℓ¹` ball,
  and is bounded by `(c₉/2) L^{-j((d-2)/2+δ)} e^{-κ|X|/(M L^j)^d}`. In the source this is the bound
  (H.7) of the class at the constant configuration with the ties of `PrefixInput` (`δ ≤ γ - α₁`,
  `κ_flow ≥ C_{d,L}(κ + 1)`, `c₉^{flow} ≤ (c₉/2) e^{-κ_flow}`) and the comparison of the covering
  size with the volume (FLUCTUATION Lemma 1.2 (G1); `G1_card`, `rootRate_of_sizeJ`).
* `InheritedAgreeInput` (the exact two-torus agreement of the inherited activities; LFR Theorem IV.5.3
  item 7 for `j ≤ k_f`): from the small-field half of (D8) of the class (`D8SF.M_eq`), transported to
  Root-F's quarter box.
* `FinalSmallFieldInput` (the small-field last integral; P4 §6 (6.1)–(6.7), P7 (4.1)–(4.9) and
  (4.15)–(4.17), LFR Theorem IV.4.1; blocker 5, small-field half):
  `Ξ^sf = exp(E + ⟨g, h⟩ + ∑_{j ≤ k} ∑_X q_j(X; g) + ∑_X a(X; g))` with scale-`(k+1)` activities
  `a` in Root-F's form at half the amplitude.
* `FinalLargeFieldInput` (the large-field part: the final-scale fluctuation representation and the
  linked gas; P7 (4.9)–(4.14), P5 (3.18), LFR Lemma IV.4.2 and the proof of Theorem IV.4.1; blocker 5,
  item 18): `∫ ρ = Ξ^sf exp(∑_X b(X; g))` with scale-`(k+1)` activities `b` in Root-F's form at half
  the amplitude.

The clause of locality in `g` of the inherited activities is proved here from the clause `localM`
of the class (`inhObs_actLocal`). The assembly (`lastIntegralInput_of_parts`) builds the activities
`p = q + 1_{j = k+1} (a + b)`, proves the five clauses of `ObservableActivities` for them
(`ActSupport`, `ActAnalytic`, `ActLocal`, `ActBound`, `ActAgree`, its conjuncts:
`observableActivities_iff`) and the exponential identity. `FlatRep` is the body of `FlatClassAt` for
given witnesses (`flatClassAt_iff_exists_flatRep`), so that the sub-inputs can read the representation
`F`. The sub-inputs are spine-local; the list and the status of each are in `notes/phase1/SPINE.md`,
section "LastIntegralInput sub-inputs". -/

@[expose] public section

namespace Balaban.RootFSpine

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6v2

/-!
### The clauses of `ObservableActivities`, one by one
-/

section Clauses

/-- **Support** (the first clause of `ObservableActivities`, top scale `J`): on every admissible
torus the increment of `p_j(X; ·)` vanishes unless `1 ≤ j ≤ J` and `X` is a scale-`j` polymer. -/
def ActSupport (d N L M J kf : ℕ)
    (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) : Prop :=
  ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ →
    ∀ j X, ¬ (j ∈ Finset.Icc 1 J ∧ IsPolymer d ℓ (M * L ^ j) X) → ∀ g, p ℓ j X g = p ℓ j X 0

/-- **Analyticity** (the second clause of `ObservableActivities`): on every admissible torus
`p_j(X; ·)` is analytic on the unit `ℓ¹` ball. -/
def ActAnalytic (d N L M kf : ℕ)
    (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) : Prop :=
  ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ →
    ∀ j X, AnalyticOnNhd ℂ (p ℓ j X) {g | ∑ y, ∑ i, ‖g y i‖ < 1}

/-- **Locality** (the third clause of `ObservableActivities`): on every admissible torus
`p_j(X; g)` depends on `g|_X` only. -/
def ActLocal (d N L M kf : ℕ)
    (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) : Prop :=
  ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ →
    ∀ j X (g g' : Torus d ℓ → Fin N → ℂ), (∀ y ∈ X, g y = g' y) → p ℓ j X g = p ℓ j X g'

/-- **The bound** (the fourth clause of `ObservableActivities`, top scale `J`): on every admissible
torus and for `1 ≤ j ≤ J`, the increment is at most
`(c₉/2) L^{-j((d-2)/2+δ)} e^{-κ|X|/(M L^j)^d}` on the unit `ℓ¹` ball. -/
def ActBound (d N L M : ℕ) (κ c₉ δ : ℝ) (J kf : ℕ)
    (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) : Prop :=
  ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ →
    ∀ j ∈ Finset.Icc 1 J, ∀ X (g : Torus d ℓ → Fin N → ℂ), ∑ y, ∑ i, ‖g y i‖ < 1 →
      ‖p ℓ j X g - p ℓ j X 0‖ ≤ c₉ / 2 * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
        * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d)

/-- **The two-torus agreement** (the last clause of `ObservableActivities`): the increments on two
admissible tori agree on the images of a finite set `A ⊂ ℤ^d` in the common quarter box. -/
def ActAgree (d N L M kf : ℕ)
    (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) : Prop :=
  ∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], M * L ^ (kf + 1) ∣ ℓ → M * L ^ (kf + 1) ∣ ℓ' →
    ∀ (j : ℕ) (a : Fin d → ℤ) (A : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → Fin N → ℂ),
      a ∈ A → (∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ) ∧ 4 * |y μ| < (ℓ' : ℤ)) →
      p ℓ j (A.image fun y μ => (y μ : ZMod ℓ))
          (fun z => g fun μ => ZMod.valMinAbs (n := ℓ) (z μ)) -
          p ℓ j (A.image fun y μ => (y μ : ZMod ℓ)) 0 =
        p ℓ' j (A.image fun y μ => (y μ : ZMod ℓ'))
          (fun z => g fun μ => ZMod.valMinAbs (n := ℓ') (z μ)) -
          p ℓ' j (A.image fun y μ => (y μ : ZMod ℓ')) 0

/-- `ObservableActivities` is the conjunction of its five clauses. -/
theorem observableActivities_iff (d N L M : ℕ) (κ c₉ δ : ℝ) (J kf : ℕ)
    (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) :
    ObservableActivities d N L M κ c₉ δ J kf p ↔
      ActSupport d N L M J kf p ∧ ActAnalytic d N L M kf p ∧ ActLocal d N L M kf p ∧
        ActBound d N L M κ c₉ δ J kf p ∧ ActAgree d N L M kf p := by
  constructor
  · rintro ⟨h, hag⟩
    exact ⟨fun ℓ _ hℓ => (h ℓ hℓ).1, fun ℓ _ hℓ => (h ℓ hℓ).2.1, fun ℓ _ hℓ => (h ℓ hℓ).2.2.1,
      fun ℓ _ hℓ => (h ℓ hℓ).2.2.2, hag⟩
  · rintro ⟨h1, h2, h3, h4, hag⟩
    exact ⟨fun ℓ _ hℓ => ⟨h1 ℓ hℓ, h2 ℓ hℓ, h3 ℓ hℓ, h4 ℓ hℓ⟩, hag⟩

end Clauses

/-!
### Sums of activity families and their scale-`J` parts
-/

section Combine

variable {d N : ℕ}

/-- The sum of two activity families. -/
def actAdd (p q : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) :
    (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ :=
  fun ℓ j X g => p ℓ j X g + q ℓ j X g

/-- The scale-`J` part of an activity family: `p_J`, and zero at the other scales. -/
def actAt (J : ℕ) (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) :
    (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ :=
  fun ℓ j X g => if j = J then p ℓ j X g else 0

variable {L M J kf : ℕ}
  {p q : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ}

theorem ActSupport.add (hp : ActSupport d N L M J kf p) (hq : ActSupport d N L M J kf q) :
    ActSupport d N L M J kf (actAdd p q) := fun ℓ _ hℓ j X hX g => by
  simp only [actAdd]
  rw [hp ℓ hℓ j X hX g, hq ℓ hℓ j X hX g]

theorem ActSupport.mono {J' : ℕ} (hp : ActSupport d N L M J kf p) (hJ : J ≤ J') :
    ActSupport d N L M J' kf p := fun ℓ _ hℓ j X hX g =>
  hp ℓ hℓ j X (fun h => hX ⟨Finset.Icc_subset_Icc le_rfl hJ h.1, h.2⟩) g

theorem ActSupport.actAt (J' : ℕ) (hp : ActSupport d N L M J kf p) :
    ActSupport d N L M J kf (actAt J' p) := fun ℓ _ hℓ j X hX g => by
  simp only [RootFSpine.actAt]
  split_ifs
  · exact hp ℓ hℓ j X hX g
  · rfl

theorem ActAnalytic.add (hp : ActAnalytic d N L M kf p) (hq : ActAnalytic d N L M kf q) :
    ActAnalytic d N L M kf (actAdd p q) := fun ℓ _ hℓ j X =>
  (hp ℓ hℓ j X).add (hq ℓ hℓ j X)

theorem ActAnalytic.actAt (J' : ℕ) (hp : ActAnalytic d N L M kf p) :
    ActAnalytic d N L M kf (actAt J' p) := fun ℓ _ hℓ j X => by
  by_cases hj : j = J'
  · have e : RootFSpine.actAt J' p ℓ j X = p ℓ j X := funext fun g => ite_eq_left hj
    rw [e]
    exact hp ℓ hℓ j X
  · have e : RootFSpine.actAt J' p ℓ j X = fun _ => 0 := funext fun g => ite_eq_right hj
    rw [e]
    exact analyticOnNhd_const

theorem ActLocal.add (hp : ActLocal d N L M kf p) (hq : ActLocal d N L M kf q) :
    ActLocal d N L M kf (actAdd p q) := fun ℓ _ hℓ j X g g' hgg => by
  simp only [actAdd]
  rw [hp ℓ hℓ j X g g' hgg, hq ℓ hℓ j X g g' hgg]

theorem ActLocal.actAt (J' : ℕ) (hp : ActLocal d N L M kf p) :
    ActLocal d N L M kf (actAt J' p) := fun ℓ _ hℓ j X g g' hgg => by
  simp only [RootFSpine.actAt]
  split_ifs
  · exact hp ℓ hℓ j X g g' hgg
  · rfl

theorem ActAgree.add (hp : ActAgree d N L M kf p) (hq : ActAgree d N L M kf q) :
    ActAgree d N L M kf (actAdd p q) := fun ℓ ℓ' _ _ hℓ hℓ' j a A g ha hbox => by
  have e1 := hp ℓ ℓ' hℓ hℓ' j a A g ha hbox
  have e2 := hq ℓ ℓ' hℓ hℓ' j a A g ha hbox
  simp only [actAdd]
  linear_combination e1 + e2

theorem ActAgree.actAt (J' : ℕ) (hp : ActAgree d N L M kf p) :
    ActAgree d N L M kf (actAt J' p) := fun ℓ ℓ' _ _ hℓ hℓ' j a A g ha hbox => by
  simp only [RootFSpine.actAt]
  split_ifs
  · exact hp ℓ ℓ' hℓ hℓ' j a A g ha hbox
  · simp

theorem ActBound.add {κ c₁ c₂ δ : ℝ} (hp : ActBound d N L M κ c₁ δ J kf p)
    (hq : ActBound d N L M κ c₂ δ J kf q) : ActBound d N L M κ (c₁ + c₂) δ J kf (actAdd p q) :=
  fun ℓ _ hℓ j hj X g hg => by
    have h1 := hp ℓ hℓ j hj X g hg
    have h2 := hq ℓ hℓ j hj X g hg
    have e : actAdd p q ℓ j X g - actAdd p q ℓ j X 0 =
        (p ℓ j X g - p ℓ j X 0) + (q ℓ j X g - q ℓ j X 0) := by
      simp only [actAdd]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ c₁ / 2 * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
            * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d) +
          c₂ / 2 * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
            * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d) := add_le_add h1 h2
      _ = _ := by ring

/-- **The bounds of the two parts of the scale range** (top scale `k + 1`): a family `q` supported
on the scales `≤ k` with the bound up to `k`, plus the scale-`(k+1)` part of a family `r` with the
bound up to `k + 1`. -/
theorem ActBound.add_actAt_succ {κ c₉ δ : ℝ} {k : ℕ} (hqs : ActSupport d N L M k kf q)
    (hq : ActBound d N L M κ c₉ δ k kf q) (hr : ActBound d N L M κ c₉ δ (k + 1) kf p) :
    ActBound d N L M κ c₉ δ (k + 1) kf (actAdd q (actAt (k + 1) p)) :=
  fun ℓ _ hℓ j hj X g hg => by
    simp only [actAdd, RootFSpine.actAt]
    by_cases hjk : j = k + 1
    · subst hjk
      have hq0 : q ℓ (k + 1) X g = q ℓ (k + 1) X 0 :=
        hqs ℓ hℓ (k + 1) X (fun h => by simp at h) g
      rw [ite_eq_left rfl, ite_eq_left rfl, hq0, add_sub_add_left_eq_sub]
      exact hr ℓ hℓ (k + 1) hj X g hg
    · rw [ite_eq_right hjk, ite_eq_right hjk, add_zero, add_zero]
      have hj' : j ∈ Finset.Icc 1 k := by
        rw [Finset.mem_Icc] at hj ⊢
        omega
      exact hq ℓ hℓ j hj' X g hg

/-- The sum over the scales `1 ≤ j ≤ k + 1` of `q + 1_{j = k+1} (a + b)`, for `q` vanishing at
the scale `k + 1`. -/
theorem sum_actAdd_actAt {ℓ k : ℕ} [NeZero ℓ]
    (q a b : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ)
    (g : Torus d ℓ → Fin N → ℂ) (hq : ∀ X, q ℓ (k + 1) X g = 0) :
    ∑ j ∈ Finset.Icc 1 (k + 1), ∑ X, actAdd q (actAt (k + 1) (actAdd a b)) ℓ j X g =
      ∑ j ∈ Finset.Icc 1 k, ∑ X, q ℓ j X g + ∑ X, a ℓ (k + 1) X g + ∑ X, b ℓ (k + 1) X g := by
  rw [Finset.sum_Icc_succ_top (by omega)]
  have h1 : ∑ j ∈ Finset.Icc 1 k, ∑ X, actAdd q (actAt (k + 1) (actAdd a b)) ℓ j X g =
      ∑ j ∈ Finset.Icc 1 k, ∑ X, q ℓ j X g := by
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun X _ => ?_
    have hjk : j ≠ k + 1 := by
      rw [Finset.mem_Icc] at hj
      omega
    simp only [actAdd, RootFSpine.actAt, ite_eq_right hjk, add_zero]
  have h2 : ∑ X, actAdd q (actAt (k + 1) (actAdd a b)) ℓ (k + 1) X g =
      ∑ X, a ℓ (k + 1) X g + ∑ X, b ℓ (k + 1) X g := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun X _ => ?_
    simp only [actAdd, RootFSpine.actAt, ↓reduceIte, hq X, zero_add]
  rw [h1, h2]
  ring

end Combine

/-!
### The inherited observable activities
-/

section Inherited

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- A site of the Def-6 torus `CTorus d L N₁ m₁ k = 𝕋_{N₁ L^{m₁} L^k}` read on the torus `𝕋_ℓ`
through its coordinates `0 ≤ x_μ < N₁ L^{m₁} L^k` (the identity when `ℓ = N₁ L^{m₁} L^k`). -/
def sfSite {N₁ : ℕ} (ℓ : ℕ) (x : Localization.CTorus d L N₁ m₁ k) : Torus d ℓ :=
  fun μ => ((x μ).val : ZMod ℓ)

/-- The set of sites of the Def-6 torus `CTorus d L N₁ m₁ k` read off a set `X` of sites of
`𝕋_ℓ`. -/
def sfPre (N₁ ℓ : ℕ) (X : Finset (Torus d ℓ)) : Set (Localization.CTorus d L N₁ m₁ k) :=
  {x | sfSite ℓ x ∈ X}

open Classical in
/-- **The inherited observable activities** (LFR Definition IV.5.2, first item; P4 (H.7);
P7 (4.17)) of a small-field datum `𝔰` at the scale `k`, on the torus `𝕋_ℓ`:
`q_j(X; g) = ∑_{x ∈ X} ⟨g(x), ℳ^{(j)}(x, X; h, h, g)⟩` for `1 ≤ j ≤ k` and `X` a polymer of `𝒟_j`
(`IsPolyDom`), and `0` otherwise. The terms `ℳ^{(j)}(x, X; ψ, h, g)` of (H.7) are those of `𝔰` on
the Def-6 torus `N₁ = ℓ/(L^{m₁} L^k)` (whose sites are those of `𝕋_ℓ` when `L^{m₁} L^k ∣ ℓ`), at the
constant configuration `ψ^{(j)} = h` with the constant external field `h`; `m₀` is the polymer
exponent of Def-6. On a torus with `ℓ < L^{m₁} L^k` the activities are `0`. -/
noncomputable def inhObs (sf : SFData d L m₁ k N ϱ) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N))
    (ℓ j : ℕ) (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ) : ℂ :=
  if hN : ℓ / (L ^ m₁ * L ^ k) = 0 then 0 else
    haveI : NeZero (ℓ / (L ^ m₁ * L ^ k)) := ⟨hN⟩
    if 1 ≤ j ∧ j ≤ k ∧
        Def6.IsPolyDom (L := L) (N₁ := ℓ / (L ^ m₁ * L ^ k)) (m₁ := m₁) (k := k) m₀ j
          (sfPre (ℓ / (L ^ m₁ * L ^ k)) ℓ X) then
      ∑ x : Localization.CTorus d L (ℓ / (L ^ m₁ * L ^ k)) m₁ k,
        if sfSite ℓ x ∈ X then
          ∑ i, g (sfSite ℓ x) i * (sf.Tm (ℓ / (L ^ m₁ * L ^ k))).M j x
            (sfPre (ℓ / (L ^ m₁ * L ^ k)) ℓ X) (Def6.constFld (hC hv))
            (Def6.constFld (hC hv)) (fun y => g (sfSite ℓ y)) i
        else 0
    else 0

/-- The inherited activities vanish above the scale `k`. -/
theorem inhObs_of_lt (sf : SFData d L m₁ k N ϱ) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N))
    {ℓ j : ℕ} (hj : k < j) (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ) :
    inhObs sf m₀ hv ℓ j X g = 0 := by
  unfold inhObs
  split_ifs with hN hc
  · rfl
  · exact absurd hc.2.1 (by omega)
  · rfl

/-- **The inherited activities depend on `g|_X` only**, by the locality clause `localM` of (H.7) on
every Def-6 torus. -/
theorem inhObs_local (sf : SFData d L m₁ k N ϱ) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N))
    (hloc : ∀ (N₁ : ℕ) [NeZero N₁] j x X Ψ Ψ' h h' g g',
      (∀ z ∈ X, Ψ z = Ψ' z ∧ h z = h' z ∧ g z = g' z) →
      (sf.Tm N₁).M j x X Ψ h g = (sf.Tm N₁).M j x X Ψ' h' g')
    {ℓ j : ℕ} (X : Finset (Torus d ℓ)) (g g' : Torus d ℓ → Fin N → ℂ)
    (hgg : ∀ y ∈ X, g y = g' y) : inhObs sf m₀ hv ℓ j X g = inhObs sf m₀ hv ℓ j X g' := by
  unfold inhObs
  split_ifs with hN hc
  · rfl
  · have : NeZero (ℓ / (L ^ m₁ * L ^ k)) := ⟨hN⟩
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · rw [hloc (ℓ / (L ^ m₁ * L ^ k)) j x (sfPre (ℓ / (L ^ m₁ * L ^ k)) ℓ X)
        (Def6.constFld (hC hv)) (Def6.constFld (hC hv)) (Def6.constFld (hC hv))
        (Def6.constFld (hC hv)) (fun y => g (sfSite ℓ y)) (fun y => g' (sfSite ℓ y))
        fun z hz => ⟨rfl, rfl, hgg _ hz⟩, hgg _ hx]
    · rfl
  · rfl

/-- **The locality clause of the inherited activities** from (D2♭) of the class: the clause
`localM` of (H.7) on every Def-6 torus (`SFFlat2.torus`). -/
theorem inhObs_actLocal {P6 : Def6.Consts} {k0 : ℕ} {sf : SFData d L m₁ k N ϱ}
    (hsf : SFFlat2 P6 k0 sf) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N)) (Lr Mr kf : ℕ) :
    ActLocal d N Lr Mr kf (inhObs sf m₀ hv) := by
  obtain ⟨_, hρsf⟩ := hsf.torus
  exact fun ℓ _ _ j X g g' hgg =>
    inhObs_local sf m₀ hv (fun N₁ _ => (hρsf N₁).terms.localM) X g g' hgg

end Inherited

/-!
### The small-field part of the last integral
-/

section SmallField

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}
  {P6 : Def6.Consts} {C7 : Consts7} {k : ℕ} {ϱ : ℝ}

/-- **The small-field part of the last integral** on the torus `n_K` (P7 (4.1)–(4.9) with no
large-field region; P4 §6 (6.1)–(6.7)): `Ξ^sf(g) = ∫ χ_k(T) exp(𝒜_k + ℱ_k + ℛ^{(k)})(T; ψ_k, h, g)
dψ_k`, the integral over the fields of the `k`-blocks of the small-field factor of (D1) (second
version, `sfFactor2`) on the whole torus, for the representation `F`, the correction coefficients
`vc` and the physical field `hv`. -/
noncomputable def sfIntegral (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ)
    (hM6 : M = S.L ^ (P6.m₀ + C7.m₁)) (hkK : k ≤ K) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N)) (nK : ℕ) [NeZero nK] (g : GIdx S (sides S.L K nK) M K N → ℂ) :
    ℂ :=
  ∫ ψ, sfFactor2 (F.ctx hM6 hkK nK) vc Set.univ ψ hv g

end SmallField

/-!
### The class at given witnesses
-/

/-- **The body of `FlatClassAt` for given witnesses** `hM6, hkK, R, geo, cs, P, F, St, vc`: the
representation `F` of `ρ` in `ℛ♭_k` with the outer constants of the prefix, `β_0 = β`, `ν_0 = ν`,
`ν_k = νk`, (I.2) up to `k` and the large-field half of (D8). `FlatClassAt` is the existence of
witnesses (`flatClassAt_iff_exists_flatRep`). -/
def FlatRep (d N : ℕ) (T : Typing) (P6 : Def6.Consts) (C7 : Consts7) (PB : BudgetConsts)
    (cs₀ : OpConsts) (M1 c : ℕ) (rH ϱ : ℝ) (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf k : ℕ)
    [NeZero T.M] [NeZero T.L] (hM6 : T.M = T.L ^ (P6.m₀ + C7.m₁)) (hkK : k ≤ kf + 1)
    (R : ℕ → ℝ)
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo 𝒮[d, T, β, cs₀.aKer] (sides T.L (kf + 1) nK) R T.M)
    (cs : OpConsts) (P : BudgetConsts)
    (F : RepFam 𝒮[d, T, β, cs₀.aKer] R (kZero d T.L β ν) (kf + 1) T.M N geo cs P k C7.m₁ ϱ)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d T.L N₁ C7.m₁ k N) (vc : CorrCoef d)
    (ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k]) (νk : ℝ) : Prop :=
  (∀ (nK : ℕ) [NeZero nK], (geo nK).M1 = M1 ∧ (geo nK).c = c) ∧
    cs.aKer = cs₀.aKer ∧ cs.Cpsi = cs₀.Cpsi ∧ cs.Cb = cs₀.Cb ∧ cs.aw = cs₀.aw ∧
    P.c1 = PB.c1 ∧ P.c2 = PB.c2 ∧ P.H0 = PB.H0 ∧
    IsRepFlat2 𝒮[d, T, β, cs₀.aKer] R (kZero d T.L β ν) (kf + 1) T.M N geo cs P P6 C7 β ν h rH k
      kf hM6 hkK F ρ St vc ∧
    F.sf.β 0 = β ∧ F.sf.ν 0 = ν ∧ F.sf.ν k = νk ∧
    RunningHypTo d T.L β ν cs₀.aKer (1 / 20) F.sf.β F.sf.ν k ∧ LFCoherent F

/-- `FlatClassAt` is the existence of witnesses of `FlatRep`. -/
theorem flatClassAt_iff_exists_flatRep {d N : ℕ} {T : Typing} {P6 : Def6.Consts} {C7 : Consts7}
    {PB : BudgetConsts} {cs₀ : OpConsts} {M1 c : ℕ} {rH ϱ β ν : ℝ}
    {h : EuclideanSpace ℝ (Fin N)} {kf k : ℕ} [NeZero T.M] [NeZero T.L]
    {ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k]} {νk : ℝ} :
    FlatClassAt d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k ρ νk ↔
      ∃ hM6 hkK R geo cs P F St vc,
        FlatRep d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k hM6 hkK R geo cs P F St vc ρ νk :=
  Iff.rfl

/-- The small-field data of a member of `FlatRep` satisfy (D2♭). -/
theorem FlatRep.sfFlat {d N : ℕ} {T : Typing} {P6 : Def6.Consts} {C7 : Consts7}
    {PB : BudgetConsts} {cs₀ : OpConsts} {M1 c : ℕ} {rH ϱ β ν : ℝ}
    {h : EuclideanSpace ℝ (Fin N)} {kf k : ℕ} [NeZero T.M] [NeZero T.L]
    {hM6 : T.M = T.L ^ (P6.m₀ + C7.m₁)} {hkK : k ≤ kf + 1} {R : ℕ → ℝ}
    {geo : ∀ (nK : ℕ) [NeZero nK], Geo 𝒮[d, T, β, cs₀.aKer] (sides T.L (kf + 1) nK) R T.M}
    {cs : OpConsts} {P : BudgetConsts}
    {F : RepFam 𝒮[d, T, β, cs₀.aKer] R (kZero d T.L β ν) (kf + 1) T.M N geo cs P k C7.m₁ ϱ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d T.L N₁ C7.m₁ k N} {vc : CorrCoef d}
    {ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k]} {νk : ℝ}
    (hF : FlatRep d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k hM6 hkK R geo cs P F St vc ρ νk) :
    SFFlat2 P6 (kZero d T.L β ν) F.sf :=
  hF.2.2.2.2.2.2.2.2.1.sfData

/-!
### The sub-inputs
-/

section Inputs

variable (d N : ℕ) (δ : ℝ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- **A6-1, the inherited observable terms in Root-F's form (the conversion; LFR Theorem IV.5.3
items 2, 4, 5 for `j ≤ k_f`; P4 (H.7); FLUCTUATION Lemma 1.2 (G1)).** For a member `ρ` of `ℛ♭_k`
at the stopping scale, with a representation `F`, the inherited observable activities
`q_j(X; g) = ∑_{x ∈ X} ⟨g(x), ℳ^{(j)}(x, X; h, h, g)⟩` (`inhObs`, scales `1 ≤ j ≤ k`) vanish off
the scale-`j` polymers of Root-F (`IsPolymer d ℓ (M L^j)`; the polymers of `𝒟_j` are unions of
cubes of side `M L^j`), are analytic on the unit `ℓ¹` ball, and are bounded there by
`(c₉/2) L^{-j((d-2)/2+δ)} e^{-κ|X|/(M L^j)^d}`. The source argument: the constant configuration
lies in the domain `Ξ^c_j(𝔹_j(X); 1, ε_j)` of the terms (`sfDom`), where (H.7) gives analyticity and
`|ℳ^{(j)}(x, X)| < c₉^{flow} L^{-j((d-2)/2+γ-α₁)} e^{-κ_flow d_j(X)}`; then `‖g‖₁ < 1`, the ties of
`PrefixInput` and `|X| ≤ c₁ (M L^j)^d (1 + d_j(X))` (`G1_card`). -/
def InheritedBoundInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → k ≤ kf →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ) hM6 hkK R geo cs P F St vc,
    FlatRep d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k hM6 hkK R geo cs P F St vc ρ νk →
    7 / 8 < νk * ((T κ c₉).L : ℝ) ^ 2 →
    ActSupport d N (T κ c₉).L (T κ c₉).M k kf (inhObs F.sf (P6 κ c₉).m₀ h) ∧
      ActAnalytic d N (T κ c₉).L (T κ c₉).M kf (inhObs F.sf (P6 κ c₉).m₀ h) ∧
      ActBound d N (T κ c₉).L (T κ c₉).M κ c₉ δ k kf (inhObs F.sf (P6 κ c₉).m₀ h)

/-- **A6-2, the exact two-torus agreement of the inherited observable terms (LFR Theorem IV.5.3
item 7 for `j ≤ k_f`; P4 (H.4); (D8), D-IV.9).** For a member `ρ` of `ℛ♭_k` at the stopping scale,
with a representation `F`, the increments of the inherited observable activities (`inhObs`) on two
admissible tori agree on the images of a finite set `A ⊂ ℤ^d` in the common quarter box. The source
argument: the small-field half of (D8) of the class (`D8SF.M_eq`: the terms `ℳ^{(j)}(x, X)` of a
polymer that does not wind around either torus are the same on both, at data pulled back from
`ℤ^d`), with the support of `inhObs` on polymers of `𝒟_j` and the identification of the quarter box
with its images. Closeness of the terms on two tori is not enough (W1088): Root-F fixes its terms
before the pair of tori. -/
def InheritedAgreeInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → k ≤ kf →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ) hM6 hkK R geo cs P F St vc,
    FlatRep d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k hM6 hkK R geo cs P F St vc ρ νk →
    7 / 8 < νk * ((T κ c₉).L : ℝ) ^ 2 →
    ActAgree d N (T κ c₉).L (T κ c₉).M kf (inhObs F.sf (P6 κ c₉).m₀ h)

/-- **A6-3, the small-field part of the last integral (P4 §6 (6.1)–(6.7); P7 (4.1)–(4.9) with no
large-field region and (4.15)–(4.17); LFR Theorem IV.4.1; blocker 5, small-field half).** For a
member `ρ` of `ℛ♭_k` at the stopping scale (`ν_k > 7/8 L⁻²`, so the variational problem of the last
integral is massive), with a representation `F`: on every torus of the family and every source of
the unit `ℓ¹` ball, the integral `Ξ^sf` of the small-field factor on the whole torus (`sfIntegral`)
is `exp(E + ⟨g, h⟩ + ∑_{j=1}^{k} ∑_X q_j(X; g) + ∑_X a(X; g))`, where `q_j` are the inherited
observable activities (`inhObs`; the terms `⟨g, ℳ^{(j)}(·; h, h, g)⟩` of `ℱ_{k+1,0}`, P7 (4.17)) and
`a` are activities of the scale `k + 1` in Root-F's form (`ObservableActivities` with top scale
`k + 1` and half the amplitude `c₉`): the term `ℳ^{(k+1)}_0` and the polymer terms `ℛ^{(k+1)}_n`
(P7 (4.9)), regrouped by the scale-`(k+1)` polymer `Ȳ` of their localization domain (LFR Definition
IV.5.2). The agreement clause of `a` comes from (D8) of the class and the locality of the last
integral (LFR Theorem IV.5.3 item 7). -/
def FinalSmallFieldInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → k ≤ kf →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ) hM6 hkK R geo cs P F St vc,
    FlatRep d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k hM6 hkK R geo cs P F St vc ρ νk →
    7 / 8 < νk * ((T κ c₉).L : ℝ) ^ 2 →
    ∃ (a : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) (E : ℕ → ℂ),
      ObservableActivities d N (T κ c₉).L (T κ c₉).M κ (c₉ / 2) δ (k + 1) kf a ∧
      ∀ (nK : ℕ) [NeZero nK]
        (g : GIdx 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
          (kf + 1) N → ℂ), g ∈ l1Ball _ →
        sfIntegral F hM6 hkK vc h nK g = Complex.exp (E nK + ∑ x, ∑ i, g (x, i) * (h i : ℂ)
          + ∑ j ∈ Finset.Icc 1 k, ∑ X,
            inhObs F.sf (P6 κ c₉).m₀ h
              ((T κ c₉).M * sides (T κ c₉).L (kf + 1) nK (kf + 1) * (T κ c₉).L ^ (kf + 1)) j X
              (fun x i => g (x, i))
          + ∑ X, a ((T κ c₉).M * sides (T κ c₉).L (kf + 1) nK (kf + 1) * (T κ c₉).L ^ (kf + 1))
              (k + 1) X (fun x i => g (x, i)))

/-- **A6-4, the large-field part of the last integral (the final-scale fluctuation representation
and the linked gas; P7 (4.9)–(4.14), P5 (3.18); LFR Lemma IV.4.2 and the proof of Theorem IV.4.1;
blocker 5, item 18).** For a member `ρ` of `ℛ♭_k` at the stopping scale, with a representation `F`:
on every torus of the family and every source of the unit `ℓ¹` ball,
`∫ ρ dψ_k = Ξ^sf exp(∑_X b(X; g))`, where `Ξ^sf` is the small-field part (`sfIntegral`) and `b`
are activities of the scale `k + 1` in Root-F's form (`ObservableActivities` with top scale `k + 1`
and half the amplitude `c₉`). In the source: the last integral of every history (P7 (4.1)–(4.9):
the operators `𝕋'_{k+1}(Z', 𝔸')` with no free variable), the completion of the small-field functions
to the whole torus (P7 (4.11): the term with no large-field region is `Ξ^sf`), the gas of the heavy
objects `Z'` with weights bounded by (IV.4.1) `e^{-p₂(β_{k₀})/2 - H^{fin}|Z'|}` and the couplings
`ℬ''` (linked: activating set and footprint), and its exponentiation (PE-L; P7 (4.12)–(4.14)) into
`𝒫^{(k+1)}`, regrouped by scale-`(k+1)` polymers. -/
def FinalLargeFieldInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → k ≤ kf →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ) hM6 hkK R geo cs P F St vc,
    FlatRep d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k hM6 hkK R geo cs P F St vc ρ νk →
    7 / 8 < νk * ((T κ c₉).L : ℝ) ^ 2 →
    ∃ b : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ,
      ObservableActivities d N (T κ c₉).L (T κ c₉).M κ (c₉ / 2) δ (k + 1) kf b ∧
      ∀ (nK : ℕ) [NeZero nK]
        (g : GIdx 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
          (kf + 1) N → ℂ), g ∈ l1Ball _ →
        ∫ ψ, ρ nK ψ g = sfIntegral F hM6 hkK vc h nK g *
          Complex.exp (∑ X, b ((T κ c₉).M * sides (T κ c₉).L (kf + 1) nK (kf + 1) *
            (T κ c₉).L ^ (kf + 1)) (k + 1) X (fun x i => g (x, i)))

/-- **The last integral from its sub-inputs** (LFR Theorem IV.4.1 with Definition IV.5.2 and Theorem
IV.5.3): the activities are `p = q + 1_{j = k+1} (a + b)`, with `q` the inherited observable
activities (`inhObs`; A6-1, A6-2, and locality from the class, `inhObs_actLocal`), `a` the
activities of the small-field part `Ξ^sf` (A6-3) and `b` those of the large-field part `∫ ρ / Ξ^sf`
(A6-4); `E` is the vacuum term of A6-3. The bounds: `q` at the scales `≤ k`, `a + b` at the scale
`k + 1` with the amplitudes `c₉/4 + c₉/4`. The threshold is the largest of the four thresholds. -/
theorem lastIntegralInput_of_parts (hB : InheritedBoundInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ)
    (hA : InheritedAgreeInput d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hS : FinalSmallFieldInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ)
    (hL : FinalLargeFieldInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ) :
    LastIntegralInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ := by
  intro κ hκ c₉ hc₉
  obtain ⟨β₁, h₁⟩ := hB κ hκ c₉ hc₉
  obtain ⟨β₂, h₂⟩ := hA κ hκ c₉ hc₉
  obtain ⟨β₃, h₃⟩ := hS κ hκ c₉ hc₉
  obtain ⟨β₄, h₄⟩ := hL κ hκ c₉ hc₉
  refine ⟨max (max β₁ β₂) (max β₃ β₄),
    fun β hβ ν hν hνL h hh kf hkf _ _ k hk1 hk ρ νk hρ hstop => ?_⟩
  simp only [max_le_iff] at hβ
  obtain ⟨⟨hβ₁, hβ₂⟩, hβ₃, hβ₄⟩ := hβ
  obtain ⟨hM6, hkK, R, geo, cs, P, F, St, vc, hrep⟩ := flatClassAt_iff_exists_flatRep.1 hρ
  obtain ⟨hsupp, hana, hbd⟩ :=
    h₁ β hβ₁ ν hν hνL h hh kf hkf k hk1 hk ρ νk hM6 hkK R geo cs P F St vc hrep hstop
  have hagr := h₂ β hβ₂ ν hν hνL h hh kf hkf k hk1 hk ρ νk hM6 hkK R geo cs P F St vc hrep hstop
  obtain ⟨a, E, hobsA, hidA⟩ :=
    h₃ β hβ₃ ν hν hνL h hh kf hkf k hk1 hk ρ νk hM6 hkK R geo cs P F St vc hrep hstop
  obtain ⟨b, hobsB, hidB⟩ :=
    h₄ β hβ₄ ν hν hνL h hh kf hkf k hk1 hk ρ νk hM6 hkK R geo cs P F St vc hrep hstop
  have hloc := inhObs_actLocal hrep.sfFlat (P6 κ c₉).m₀ h (T κ c₉).L (T κ c₉).M kf
  rw [observableActivities_iff] at hobsA hobsB
  obtain ⟨hsA, haA, hlA, hbA, hgA⟩ := hobsA
  obtain ⟨hsB, haB, hlB, hbB, hgB⟩ := hobsB
  have hbAB := hbA.add hbB
  rw [add_halves] at hbAB
  refine ⟨actAdd (inhObs F.sf (P6 κ c₉).m₀ h) (actAt (k + 1) (actAdd a b)), E, ?_, ?_⟩
  · rw [observableActivities_iff]
    exact ⟨(hsupp.mono (Nat.le_succ k)).add ((hsA.add hsB).actAt (k + 1)),
      hana.add ((haA.add haB).actAt (k + 1)), hloc.add ((hlA.add hlB).actAt (k + 1)),
      ActBound.add_actAt_succ hsupp hbd hbAB, hagr.add ((hgA.add hgB).actAt (k + 1))⟩
  · intro nK _ g hg
    rw [hidB nK g hg, hidA nK g hg, ← Complex.exp_add,
      sum_actAdd_actAt _ _ _ _ fun X => inhObs_of_lt _ _ _ (Nat.lt_succ_self k) X _]
    congr 1
    ring

end Inputs

/-!
### Inhabitation (rule 10)
-/

open Balaban.LargeField.Def7.Wit Balaban.LargeField.Def7v2.Wit in
/-- **`FlatRep` is inhabited**: the witness of `FlatClassAt` (`flatClassAt_witness`: the landed
witness of `IsRepFlat2` at `ν = 1/(27β)`, horizon `kf = 0`, scale `k = 1`). -/
theorem flatRep_witness (rH : ℝ) :
    ∃ (ρ : 𝒟[3, 2, typing, wβ, (wCs wν₀ (kZero 3 3 wβ wν₀)).aKer, 0 + 1, 1]) (νk : ℝ),
      ∃ hM6 hkK R geo cs P F St vc,
        @FlatRep 3 2 typing wP6 wC7 (budgetConsts wβ) (wCs wν₀ (kZero 3 3 wβ wν₀)) 1 27 rH
          (Background.bgR0 3 3) wβ wν₀ whv 0 1 ⟨by norm_num [typing, typing0]⟩
          ⟨by norm_num [typing, typing0]⟩ hM6 hkK R geo cs P F St vc ρ νk :=
  flatClassAt_witness rH

/-- **The five clauses of `ObservableActivities` are inhabited**: zero activities satisfy all of
them (`observableActivities_zero`). -/
theorem actClauses_zero (d N L M : ℕ) (κ c₉ δ : ℝ) (hc₉ : 0 < c₉) (J kf : ℕ) :
    ActSupport d N L M J kf (fun _ _ _ _ => 0) ∧ ActAnalytic d N L M kf (fun _ _ _ _ => 0) ∧
      ActLocal d N L M kf (fun _ _ _ _ => 0) ∧
      ActBound d N L M κ c₉ δ J kf (fun _ _ _ _ => 0) ∧ ActAgree d N L M kf (fun _ _ _ _ => 0) :=
  (observableActivities_iff d N L M κ c₉ δ J kf _).1
    (observableActivities_zero d N L M κ c₉ δ hc₉ J kf)

end Balaban.RootFSpine
