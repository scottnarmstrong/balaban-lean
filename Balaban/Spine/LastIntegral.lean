/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RootFInputs
public import Balaban.Green.FinalSpinCurry
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
* at the scale `k + 1`, the activities of the small-field part `Ξ_box` of the last integral
  (`sfBoxIntegral`: the fluctuation integral of the small-field factor
  `χ_k(T) exp(𝒜_k + ℱ_k + ℛ^{(k)})(T)` of (D1) on the whole torus around the constant saddle, in the
  variable `w = K^{1/2}(ψ_k - h)` of the final Hessian `K = β_k D`, with the cutoff `|w| ≤ p₁` of
  P4 (6.6): the term of P7 (4.9)–(4.11) with no final large-field region), which collect
  `ℳ^{(k+1)}_0` and the polymer terms `ℛ^{(k+1)}_n` (P7 (4.9), (4.15)–(4.17)), plus the
  activities `𝒫^{(k+1)}` of the large-field part `∫ ρ / Ξ_box` (the linked gas of P7 (4.11)–(4.14);
  it contains the part of `{χ_k ≠ 0}` outside the box, where P7 (4.9) creates the final large-field
  regions).

The sub-inputs:

* `InheritedBoundInput` (the conversion of the observable terms; LFR Theorem IV.5.3 items 2, 4, 5
  for `j ≤ k_f`): `inhObs` vanishes off scale-`j` polymers, is analytic on the unit `ℓ¹` ball,
  and is bounded by `(c₉/2) L^{-j((d-2)/2+δ)} e^{-κ|X|/(M L^j)^d}`. In the source this is the bound
  (H.7) of the class at the constant configuration with the ties of `PrefixInput` (`δ ≤ γ - α₁`,
  `κ_flow ≥ C_{d,L}(κ + 1)`, `c₉^{flow} ≤ (c₉/2) e^{-κ_flow}`) and the comparison of the covering
  size with the volume (FLUCTUATION Lemma 1.2 (G1); `G1_card`, `rootRate_of_sizeJ`).
* `InheritedAgreeInput` (the exact two-torus agreement of the inherited activities; LFR Theorem
  IV.5.3 item 7 for `j ≤ k_f`): from the small-field half of (D8) of the class (`D8SF.M_eq`),
  transported to Root-F's quarter box.
* `FinalSmallFieldInput` (the small-field last integral; P4 §6 (6.1)–(6.7), P7 (4.1)–(4.9) and
  (4.15)–(4.17), LFR Theorem IV.4.1; blocker 5, small-field half):
  `Ξ_box = exp(E + ⟨g, h⟩ + ∑_{j ≤ k} ∑_X q_j(X; g) + ∑_X a(X; g))` with scale-`(k+1)` activities
  `a` in Root-F's form at half the amplitude.
* `FinalLargeFieldInput` (the large-field part: the final-scale fluctuation representation and the
  linked gas; P7 (4.9)–(4.14), P5 (3.18), LFR Lemma IV.4.2 and the proof of Theorem IV.4.1;
  blocker 5, item 18): `∫ ρ = Ξ_box exp(∑_X b(X; g))` with scale-`(k+1)` activities `b` in Root-F's
  form at half the amplitude.

Both halves take the cutoff `p₁ = cut κ c₉ β_k` of the box as a parameter, and
`lastIntegralInput_of_parts` combines them at the same cutoff.

The clause of locality in `g` of the inherited activities is proved here from the clause `localM`
of the class (`inhObs_actLocal`). The assembly (`lastIntegralInput_of_parts`) builds the activities
`p = q + 1_{j = k+1} (a + b)`, proves the clauses of `ObservableActivities` for them (on each
admissible torus `ActSupportAt`, `ActAnalyticAt`, `ActLocalAt`, `ActBoundAt`, and `ActAgree`; all in
`Spine/RootFInputs.lean`) and the exponential identity. The sub-inputs read the representation `F`
through `FlatRep`, the body of `FlatClassAt` (`Spine/RootFInputs.lean`). Rule 10: the clause
predicates are inhabited by `observableActivities_zero`, `FlatRep` by `flatClassAt_witness`
(`Spine/Witness.lean`). The sub-inputs are spine-local; the list and the status of each are in
`notes/phase1/SPINE.md`, section "LastIntegralInput sub-inputs". -/

@[expose] public section

namespace Balaban.RootFSpine

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6v2

/-!
### Sums of activity families and their scale-`J` parts

The clauses `ActSupportAt`, `ActAnalyticAt`, `ActLocalAt`, `ActBoundAt`, `ActAgree` of
`ObservableActivities` (`Spine/RootFInputs.lean`) for sums of families and for the part of a family
at one scale.
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

/-- **The observable form at the single scale `J`**: `p` satisfies the clauses of
`ObservableActivities` (top scale `J`) after its parts at the scales `j ≠ J` are replaced by zero
(`actAt J p`). The clauses of support, analyticity, locality and bound then constrain `p` at the
scale `J` only, and the two-torus agreement `ActAgree d N L M kf (actAt J p)` is the one agreement
obligation (LFR Theorem IV.5.3 item 7) that remains. -/
def ObservableActivitiesAt (d N L M : ℕ) (κ c₉ δ : ℝ) (J kf : ℕ)
    (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) : Prop :=
  ObservableActivities d N L M κ c₉ δ J kf (actAt J p)

/-- The scale-`J` part of a sum is the sum of the scale-`J` parts. -/
theorem actAt_actAdd (J : ℕ)
    (p q : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) :
    actAt J (actAdd p q) = actAdd (actAt J p) (actAt J q) := by
  funext ℓ j X g
  simp only [actAt, actAdd]
  split_ifs <;> simp

/-- Taking the scale-`J` part twice. -/
theorem actAt_actAt (J : ℕ)
    (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) :
    actAt J (actAt J p) = actAt J p := by
  funext ℓ j X g
  simp only [actAt]
  split_ifs <;> rfl

variable {L M J kf : ℕ}
  {p q : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ}

theorem ActSupportAt.add {ℓ : ℕ} [NeZero ℓ] (hp : ActSupportAt d N L M J ℓ p)
    (hq : ActSupportAt d N L M J ℓ q) : ActSupportAt d N L M J ℓ (actAdd p q) :=
  fun j X hX g => by
    simp only [actAdd]
    rw [hp j X hX g, hq j X hX g]

theorem ActSupportAt.mono {ℓ J' : ℕ} [NeZero ℓ] (hp : ActSupportAt d N L M J ℓ p) (hJ : J ≤ J') :
    ActSupportAt d N L M J' ℓ p := fun j X hX g =>
  hp j X (fun h => hX ⟨Finset.Icc_subset_Icc le_rfl hJ h.1, h.2⟩) g

theorem ActSupportAt.actAt {ℓ : ℕ} [NeZero ℓ] (J' : ℕ) (hp : ActSupportAt d N L M J ℓ p) :
    ActSupportAt d N L M J ℓ (actAt J' p) := fun j X hX g => by
  simp only [RootFSpine.actAt]
  split_ifs
  · exact hp j X hX g
  · rfl

theorem ActAnalyticAt.add {ℓ : ℕ} [NeZero ℓ] (hp : ActAnalyticAt d N ℓ p)
    (hq : ActAnalyticAt d N ℓ q) : ActAnalyticAt d N ℓ (actAdd p q) := fun j X =>
  (hp j X).add (hq j X)

theorem ActAnalyticAt.actAt {ℓ : ℕ} [NeZero ℓ] (J' : ℕ) (hp : ActAnalyticAt d N ℓ p) :
    ActAnalyticAt d N ℓ (actAt J' p) := fun j X => by
  by_cases hj : j = J'
  · have e : RootFSpine.actAt J' p ℓ j X = p ℓ j X := funext fun g => ite_eq_left hj
    rw [e]
    exact hp j X
  · have e : RootFSpine.actAt J' p ℓ j X = fun _ => 0 := funext fun g => ite_eq_right hj
    rw [e]
    exact analyticOnNhd_const

theorem ActLocalAt.add {ℓ : ℕ} (hp : ActLocalAt d N ℓ p) (hq : ActLocalAt d N ℓ q) :
    ActLocalAt d N ℓ (actAdd p q) := fun j X g g' hgg => by
  simp only [actAdd]
  rw [hp j X g g' hgg, hq j X g g' hgg]

theorem ActLocalAt.actAt {ℓ : ℕ} (J' : ℕ) (hp : ActLocalAt d N ℓ p) :
    ActLocalAt d N ℓ (actAt J' p) := fun j X g g' hgg => by
  simp only [RootFSpine.actAt]
  split_ifs
  · exact hp j X g g' hgg
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

theorem ActBoundAt.add {κ c₁ c₂ δ : ℝ} {ℓ : ℕ} [NeZero ℓ] (hp : ActBoundAt d N L M κ c₁ δ J ℓ p)
    (hq : ActBoundAt d N L M κ c₂ δ J ℓ q) :
    ActBoundAt d N L M κ (c₁ + c₂) δ J ℓ (actAdd p q) := fun j hj X g hg => by
  have h1 := hp j hj X g hg
  have h2 := hq j hj X g hg
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
theorem ActBoundAt.add_actAt_succ {κ c₉ δ : ℝ} {k ℓ : ℕ} [NeZero ℓ]
    (hqs : ActSupportAt d N L M k ℓ q) (hq : ActBoundAt d N L M κ c₉ δ k ℓ q)
    (hr : ActBoundAt d N L M κ c₉ δ (k + 1) ℓ p) :
    ActBoundAt d N L M κ c₉ δ (k + 1) ℓ (actAdd q (actAt (k + 1) p)) := fun j hj X g hg => by
  simp only [actAdd, RootFSpine.actAt]
  by_cases hjk : j = k + 1
  · subst hjk
    have hq0 : q ℓ (k + 1) X g = q ℓ (k + 1) X 0 := hqs (k + 1) X (fun h => by simp at h) g
    rw [ite_eq_left rfl, ite_eq_left rfl, hq0, add_sub_add_left_eq_sub]
    exact hr (k + 1) hj X g hg
  · rw [ite_eq_right hjk, ite_eq_right hjk, add_zero, add_zero]
    have hj' : j ∈ Finset.Icc 1 k := by
      rw [Finset.mem_Icc] at hj ⊢
      omega
    exact hq j hj' X g hg

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
/-- **The activities of a family of polymer terms read on the torus `𝕋_ℓ`**: for a family `T` of
terms on the sets `X` of sites of `𝕋_ℓ` and the Def-6 tori `N₁` (`T ℓ N₁ j X g`), the activity of
the scale `1 ≤ j ≤ k` of `X` is `T ℓ N₁ j X g` on the Def-6 torus `N₁ = ℓ/(L^{m₁} L^k)` when the
sites of that torus in `X` form a polymer of `𝒟_j` (`IsPolyDom`), and `0` otherwise (and `0` on a
torus with `ℓ < L^{m₁} L^k`). The inherited observable activities `inhObs` and the remainder
activities of the last scale are instances. -/
noncomputable def polyObs (m₀ : ℕ)
    (T : (ℓ N₁ : ℕ) → [NeZero N₁] → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ)
    (ℓ j : ℕ) (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ) : ℂ :=
  if hN : ℓ / (L ^ m₁ * L ^ k) = 0 then 0 else
    haveI : NeZero (ℓ / (L ^ m₁ * L ^ k)) := ⟨hN⟩
    if 1 ≤ j ∧ j ≤ k ∧
        Def6.IsPolyDom (L := L) (N₁ := ℓ / (L ^ m₁ * L ^ k)) (m₁ := m₁) (k := k) m₀ j
          (sfPre (ℓ / (L ^ m₁ * L ^ k)) ℓ X) then
      T ℓ (ℓ / (L ^ m₁ * L ^ k)) j X g
    else 0

open Classical in
/-- The term of the inherited observable activities: `∑_{x ∈ X} ⟨g(x), ℳ^{(j)}(x, X; h, h, g)⟩`
on the Def-6 torus `N₁`, at the constant configuration. -/
noncomputable def inhTerm (sf : SFData d L m₁ k N ϱ) (hv : EuclideanSpace ℝ (Fin N))
    (ℓ N₁ : ℕ) [NeZero N₁] (j : ℕ) (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ) : ℂ :=
  ∑ x : Localization.CTorus d L N₁ m₁ k,
    if sfSite ℓ x ∈ X then
      ∑ i, g (sfSite ℓ x) i * (sf.Tm N₁).M j x (sfPre N₁ ℓ X) (Def6.constFld (hC hv))
        (Def6.constFld (hC hv)) (fun y => g (sfSite ℓ y)) i
    else 0

/-- **The inherited observable activities** (LFR Definition IV.5.2, first item; P4 (H.7);
P7 (4.17)) of a small-field datum `𝔰` at the scale `k`, on the torus `𝕋_ℓ`:
`q_j(X; g) = ∑_{x ∈ X} ⟨g(x), ℳ^{(j)}(x, X; h, h, g)⟩` for `1 ≤ j ≤ k` and `X` a polymer of `𝒟_j`
(`IsPolyDom`), and `0` otherwise (`polyObs` of the terms `inhTerm`). The terms
`ℳ^{(j)}(x, X; ψ, h, g)` of (H.7) are those of `𝔰` on the Def-6 torus `N₁ = ℓ/(L^{m₁} L^k)` (whose
sites are those of `𝕋_ℓ` when `L^{m₁} L^k ∣ ℓ`), at the constant configuration `ψ^{(j)} = h` with
the constant external field `h`; `m₀` is the polymer exponent of Def-6. On a torus with
`ℓ < L^{m₁} L^k` the activities are `0`. -/
noncomputable def inhObs (sf : SFData d L m₁ k N ϱ) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N))
    (ℓ j : ℕ) (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ) : ℂ :=
  polyObs (L := L) (m₁ := m₁) (k := k) m₀ (fun ℓ N₁ _ => inhTerm sf hv ℓ N₁) ℓ j X g

omit [NeZero L] in
/-- The activities of a family of terms vanish above the scale `k`. -/
theorem polyObs_of_lt (m₀ : ℕ)
    (T : (ℓ N₁ : ℕ) → [NeZero N₁] → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ)
    {ℓ j : ℕ} (hj : k < j) (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ) :
    polyObs (L := L) (m₁ := m₁) (k := k) m₀ T ℓ j X g = 0 := by
  unfold polyObs
  split_ifs with hN hc
  · rfl
  · exact absurd hc.2.1 (by omega)
  · rfl

omit [NeZero L] in
open Classical in
/-- **The activities of a family of terms when `ℓ / (L^{m₁} L^k) = N₁`**, with the `ℓ`-dependent
case split resolved. -/
theorem polyObs_eq_of_div (m₀ : ℕ)
    (T : (ℓ N₁ : ℕ) → [NeZero N₁] → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ)
    {ℓ N₁ : ℕ} [NeZero N₁] (e : ℓ / (L ^ m₁ * L ^ k) = N₁) (j : ℕ) (X : Finset (Torus d ℓ))
    (g : Torus d ℓ → Fin N → ℂ) :
    polyObs (L := L) (m₁ := m₁) (k := k) m₀ T ℓ j X g =
      if 1 ≤ j ∧ j ≤ k ∧ Def6.IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
          (sfPre N₁ ℓ X) then T ℓ N₁ j X g else 0 := by
  subst e
  unfold polyObs
  simp only [NeZero.ne _, ↓reduceDIte]

omit [NeZero L] in
/-- **Locality of the activities of a family of terms**: if the terms on the torus of the
activities depend on `g|_X` only, so do the activities. -/
theorem polyObs_local (m₀ : ℕ)
    (T : (ℓ N₁ : ℕ) → [NeZero N₁] → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ)
    {ℓ j : ℕ} (X : Finset (Torus d ℓ)) {g g' : Torus d ℓ → Fin N → ℂ}
    (hT : ∀ (hN : ℓ / (L ^ m₁ * L ^ k) ≠ 0),
      haveI : NeZero (ℓ / (L ^ m₁ * L ^ k)) := ⟨hN⟩
      T ℓ (ℓ / (L ^ m₁ * L ^ k)) j X g = T ℓ (ℓ / (L ^ m₁ * L ^ k)) j X g') :
    polyObs (L := L) (m₁ := m₁) (k := k) m₀ T ℓ j X g =
      polyObs (L := L) (m₁ := m₁) (k := k) m₀ T ℓ j X g' := by
  unfold polyObs
  split_ifs with hN hc
  · rfl
  · exact hT hN
  · rfl

/-- The inherited activities vanish above the scale `k`. -/
theorem inhObs_of_lt (sf : SFData d L m₁ k N ϱ) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N))
    {ℓ j : ℕ} (hj : k < j) (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ) :
    inhObs sf m₀ hv ℓ j X g = 0 :=
  polyObs_of_lt m₀ _ hj X g

/-- The inherited activities vanish at the source `g = 0` (every term carries a factor `g`), so
their increments are their values. -/
theorem inhObs_zero (sf : SFData d L m₁ k N ϱ) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N))
    {ℓ j : ℕ} (X : Finset (Torus d ℓ)) : inhObs sf m₀ hv ℓ j X 0 = 0 := by
  unfold inhObs polyObs inhTerm
  split_ifs <;> simp

/-- **The Def-6 torus of the inherited activities on the torus `n_K` of the family** is the Def-6
torus `N₁ = L^{m₀} n_k` (`sfIdx`) of the context `RepFam.ctx` of the representation: for
`M = L^{m₀ + m₁}` and `k ≤ K`, `(M n_K L^K)/(L^{m₁} L^k) = L^{m₀} n_K L^{K-k}`. -/
theorem sideDiv_eq_sfIdx {M m₀ K : ℕ} (hM : M = L ^ (m₀ + m₁)) (hk : k ≤ K) (nK : ℕ) :
    M * sides L K nK K * L ^ K / (L ^ m₁ * L ^ k) = sfIdx L m₀ (sides L K nK) k := by
  have hpos : 0 < L ^ m₁ * L ^ k :=
    Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ (NeZero.ne L)) (pow_ne_zero _ (NeZero.ne L)))
  have e : M * sides L K nK K * L ^ K = sfIdx L m₀ (sides L K nK) k * (L ^ m₁ * L ^ k) := by
    have hK : L ^ K = L ^ (K - k) * L ^ k := by rw [← pow_add]; congr 1; omega
    rw [sides_self, sfIdx, sides_of_le hk]
    rw [hM, hK, pow_add]
    ring
  rw [e, Nat.mul_div_cancel _ hpos]

/-- **The inherited activities depend on `g|_X` only**, by the locality clause `localM` of (H.7) on
the read Def-6 tori (ruling R-N₁). -/
theorem inhObs_local (sf : SFData d L m₁ k N ϱ) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N))
    {Sel : ℕ → Prop}
    (hloc : ∀ (N₁ : ℕ) [NeZero N₁], Sel N₁ → ∀ j x X Ψ Ψ' h h' g g',
      (∀ z ∈ X, Ψ z = Ψ' z ∧ h z = h' z ∧ g z = g' z) →
      (sf.Tm N₁).M j x X Ψ h g = (sf.Tm N₁).M j x X Ψ' h' g')
    {ℓ : ℕ} (hℓ : Sel (ℓ / (L ^ m₁ * L ^ k))) {j : ℕ} (X : Finset (Torus d ℓ)) (g g' : Torus d ℓ → Fin N → ℂ)
    (hgg : ∀ y ∈ X, g y = g' y) : inhObs sf m₀ hv ℓ j X g = inhObs sf m₀ hv ℓ j X g' := by
  refine polyObs_local m₀ _ X fun hN => ?_
  have : NeZero (ℓ / (L ^ m₁ * L ^ k)) := ⟨hN⟩
  unfold inhTerm
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hx
  · rw [hloc (ℓ / (L ^ m₁ * L ^ k)) hℓ j x (sfPre (ℓ / (L ^ m₁ * L ^ k)) ℓ X)
      (Def6.constFld (hC hv)) (Def6.constFld (hC hv)) (Def6.constFld (hC hv))
      (Def6.constFld (hC hv)) (fun y => g (sfSite ℓ y)) (fun y => g' (sfSite ℓ y))
      fun z hz => ⟨rfl, rfl, hgg _ hz⟩, hgg _ hx]
  · rfl

/-- **The locality clause of the inherited activities** from (D2♭) of the class: the clause
`localM` of (H.7) on the read Def-6 tori (`SFFlat2.torus`), the torus `ℓ / (L^{m₁} L^k)` of the
activities being read. -/
theorem inhObs_actLocal {P6 : Def6.Consts} {k0 : ℕ} {sf : SFData d L m₁ k N ϱ}
    (hsf : SFFlat2 P6 k0 sf) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N)) (ℓ : ℕ)
    (hℓ : ReadTorus L P6.m₀ (ℓ / (L ^ m₁ * L ^ k))) :
    ActLocalAt d N ℓ (inhObs sf m₀ hv) := by
  obtain ⟨_, hρsf⟩ := hsf.torus
  exact fun j X g g' hgg =>
    inhObs_local sf m₀ hv (fun N₁ _ hN => (hρsf N₁ hN).terms.localM) hℓ X g g' hgg

/-- **The torus of the activities on an admissible torus is read**: if `ℓ` is divisible by
`L^{m₀+m₁} L^{K}` with `k ≤ K`, then `ℓ / (L^{m₁} L^k)` is divisible by `L^{m₀}`
(`sideDiv_eq_sfIdx`). -/
theorem readTorus_div {m₀ K : ℕ} (hk : k ≤ K) {ℓ : ℕ} (hℓ : L ^ (m₀ + m₁) * L ^ K ∣ ℓ) :
    ReadTorus L m₀ (ℓ / (L ^ m₁ * L ^ k)) := by
  obtain ⟨c, rfl⟩ := hℓ
  have hpos : 0 < L ^ m₁ * L ^ k :=
    Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ (NeZero.ne L)) (pow_ne_zero _ (NeZero.ne L)))
  have e : L ^ (m₀ + m₁) * L ^ K * c = (L ^ (m₀ + K - k) * c) * (L ^ m₁ * L ^ k) := by
    have : L ^ (m₀ + m₁) * L ^ K = L ^ (m₀ + K - k) * (L ^ m₁ * L ^ k) := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega
    rw [this]
    ring
  rw [e, Nat.mul_div_cancel _ hpos]
  exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _

end Inherited

/-!
### The small-field part of the last integral
-/

section Whiten

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- **The normalizer of a whitening** `A` of fields of `N`-vectors on `ι`: `|det A| (2π)^{n/2}`,
`n = |ι| N` (the Jacobian of `ψ = ψ₀ + A w` times the normalizer of the standard Gaussian). -/
noncomputable def whitenNorm (A : Matrix (ι × Fin N) (ι × Fin N) ℝ) : ℝ :=
  |A.det| * (2 * Real.pi) ^ ((Green.pdDim (ι × Fin N) ℝ : ℝ) / 2)

/-- **The mismatch of a whitening** `A` against a form `Kq`: `Aᵀ Kq A - 1` (zero for
`A = Kq^{-1/2}`). -/
noncomputable def whitenMismatch {κ : Type*} [Fintype κ] [DecidableEq κ] (Kq A : Matrix κ κ ℝ) :
    Matrix κ κ ℝ :=
  A.transpose * Kq * A - 1

/-- **The mismatch factor** `exp(-½ ⟨w, (Aᵀ Kq A - 1) w⟩)` of the whitening `A` against `Kq`: with
it, `exp(½ Q_{Kq}(A w)) · mismatch(w) = exp(½ |w|²)`. -/
noncomputable def mismatchFactor {κ : Type*} [Fintype κ] [DecidableEq κ] (Kq A : Matrix κ κ ℝ)
    (w : κ → ℝ) : ℝ :=
  Real.exp (-(1 / 2) * Green.pdQuad (whitenMismatch Kq A) w)

end Whiten

section Gauss

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ}

/-- **The integrand of the small-field factor at a whitening** `A` (cut `Y`, form `Kq`, centre
`ψ₀`): `sfFactor2 C vc Y (ψ₀ + A w) · exp(½ Q_{Kq}(A w))`, the small-field factor at the field
`ψ = ψ₀ + A w` with the Gaussian part of the form `Kq` divided out. Times the mismatch factor
`mismatchFactor Kq A` and the normalizer `whitenNorm A`, its average against the standard Gaussian
is the integral of the small-field factor over the fields `ψ_k` (`integral_mul_sfFactor2_whiten`). -/
noncomputable def sfGaussIntegrandL (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (Y : Set (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    (Kq A : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ)
    (ψ0 : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (w : BlockAt S n M K k × Fin N → ℝ) : ℂ :=
  sfFactor2 C vc Y ((Green.spinField (BlockAt S n M K k) N).symm
      (Green.spinField (BlockAt S n M K k) N ψ0 + matAct A w)) hv g *
    ((Real.exp ((1 / 2) * Green.pdQuad Kq (matAct A w)) : ℝ) : ℂ)

/-- **The integrand of the small-field factor in the Gaussian variable** (cut `Y`, form `Kq`,
centre `ψ₀`): `sfFactor2 C vc Y (ψ₀ + Kq^{-1/2} w) · exp(½ Q_{Kq}(Kq^{-1/2} w))`, the integrand at
the whitening `A = Kq^{-1/2}` (`sfGaussIntegrandL`; the mismatch vanishes). Its average
against the standard Gaussian `γ`, times `Z_{Kq}`, is the integral of the small-field factor over
the fields `ψ_k` (`integral_sfFactor2_gauss`). -/
noncomputable def sfGaussIntegrand (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (Y : Set (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    (Kq : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ)
    (ψ0 : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (w : BlockAt S n M K k × Fin N → ℝ) : ℂ :=
  sfGaussIntegrandL C vc Y hv g Kq (Green.pdSqrtInv Kq) ψ0 w

/-- **The box of the Gaussian variable**: `{w | |w_p| ≤ p₁}` for every index `p` (every block and
spin component). In P4 (6.6) this is the characteristic function `χ({|ψ| < p₁(β_k)})` of the
fluctuation field after the change of variables `ψ' = β_k^{-1/2} C^{1/2} ψ`. -/
def gaussBox (ι : Type*) (p1 : ℝ) : Set (ι → ℝ) := {w | ∀ p, |w p| ≤ p1}

/-- A `k`-block of the fine torus as a site of the unit-lattice torus
`𝕋_{M₁ (c n_k)} = Torus d (M₁ (c n_k) L^{k-k})` of the final Hessian: the inverse of the
identification of `blockCfgOf` at `q = i = k` (`histScale_eq`). -/
def sfBlockSite (C : SFCtx S n R M K N k m₁ ϱ) (y : BlockAt S n M K k) :
    Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) :=
  torusCast (histScale_eq C.geo.hM C.hnn le_rfl C.hkK).symm y

/-- **The quadratic form of the last integral** (P4 (6.4)–(6.6), P7 (4.3)–(4.7)): `K = β_k D` on
`k`-blocks and spin components, with `D` the final Hessian (`finalHessian`;
`D = a_k - a_k² Q G Q* + a_k² Q G h (h* G h)⁻¹ h* G Q*`, P4 (2.23) at the constant saddle `h`, with
no next-scale averaging term) on the unit lattice, at the background mass `ν_k = μ_k L^{2k}` and the
weight `a_k` of the class, read on the `k`-blocks through `sfBlockSite`. The coupling `β_k` is the
class's (`C.sf.β k`). In the exponent of the small-field factor the action enters as
`-β_k L^{-k(d-2)} A*_k` (`Ares2`), and `A*_k(h + v) = ½ L^{k(d-2)} ⟨v, D v⟩ + O(v³)` at equal action
and background masses (`actStar2_univ_hessian`; the masses are equal for the members of the class,
`sfActMass2_eq_muBg`): `½ Q_K(v)` is the quadratic part of `β_k L^{-k(d-2)} A*_k(h + v)`
(`sfFinalK_hessian`). -/
noncomputable def sfFinalK (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N)) :
    Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ :=
  Matrix.submatrix (C.sf.β k • finalHessian S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ k) (S.L ^ k)
      (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2)
      (C.weights k) (fun i => hv i))
    (fun p => (sfBlockSite C p.1, p.2)) (fun p => (sfBlockSite C p.1, p.2))

/-- **The box integral of one torus at a whitening** `A` (P4 (6.6); P7 (4.9) with no final
large-field region; P5 (2.39)): `|det A| (2π)^{n/2} ∫ 1_{box(p₁)}(w) sfGaussIntegrandL(w) mismatch(w)
dγ(w)`, the Gaussian average over the box `|w| ≤ p₁` of the whitened variable `w` of
`ψ_k = h + A w` of the integrand of the small-field factor of the whole torus (`Y = univ`), with the
Gaussian part of the form `K = β_k D` (`sfFinalK`) divided out and the mismatch factor
`exp(-½⟨w, (Aᵀ K A - 1) w⟩)` (`mismatchFactor`). In the source `A = β_k^{-1/2} L` with `L` the
localized square root of the covariance (P5 (2.39), P7 §4). -/
noncomputable def ctxBoxIntegralL (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N))
    (A : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ) (p1 : ℝ)
    (g : GIdx S n M K N → ℂ) : ℂ :=
  (whitenNorm A : ℂ) *
    ∫ w in gaussBox (BlockAt S n M K k × Fin N) p1,
      sfGaussIntegrandL C vc Set.univ hv g (sfFinalK C hv) A (fun _ => hv) w *
        (mismatchFactor (sfFinalK C hv) A w : ℂ)
        ∂(Green.pdGaussian (BlockAt S n M K k × Fin N) ℝ)

/-- **The box integral of one torus** (P4 (6.6); P7 (4.9) with no final large-field region): the
box integral at the exact whitening `A = K^{-1/2}`, `K = β_k D` (`sfFinalK`), centre `ψ₀ ≡ h`
(`ctxBoxIntegralL`; equal to `Z_K ∫ 1_{box(p₁)} sfGaussIntegrand dγ`). -/
noncomputable def ctxBoxIntegral (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N)) (p1 : ℝ) (g : GIdx S n M K N → ℂ) : ℂ :=
  ctxBoxIntegralL C vc hv (Green.pdSqrtInv (sfFinalK C hv)) p1 g

end Gauss

section SmallField

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}
  {P6 : Def6.Consts} {C7 : Consts7} {k : ℕ} {ϱ : ℝ}

/-- **The integral of the small-field factor over the whole torus** on the torus `n_K`:
`∫ χ_k(T) exp(𝒜_k + ℱ_k + ℛ^{(k)})(T; ψ_k, h, g) dψ_k`, the integral over the fields of the
`k`-blocks of the small-field factor of (D1) (second version, `sfFactor2`) on the whole torus, for
the representation `F`, the correction coefficients `vc` and the physical field `hv`. It is the
weight of the histories with no large-field region (`lastRegionWeight_empty_eq_sfIntegral`). It is
not the small-field part of the last integral: on `{χ_k ≠ 0}` outside the box `|w| ≤ p₁` of the
Gaussian variable (`sfBoxIntegral`) the source creates new large-field regions (P7 (4.9): the
fluctuation integral is analyzed as in P5 §3, whose cutoff failures are the final large-field
regions). -/
noncomputable def sfIntegral (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ)
    (hM6 : M = S.L ^ (P6.m₀ + C7.m₁)) (hkK : k ≤ K) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N)) (nK : ℕ) [NeZero nK] (g : GIdx S (sides S.L K nK) M K N → ℂ) :
    ℂ :=
  ∫ ψ, sfFactor2 (F.ctx hM6 hkK nK) vc Set.univ ψ hv g

/-- **The small-field part of the last integral** on the torus `n_K` (P7 (4.9)–(4.11): the term
with no final large-field region; P4 §6 (6.6)): `Ξ_box(g) = Z_K ∫ 1_{box(p₁)}(w) sfGaussIntegrand(w)
dγ(w)`, the fluctuation integral of the small-field factor of the whole torus around the constant
saddle `ψ_k ≡ h`, in the variable `w = K^{1/2}(ψ_k - h)` with `K = β_k D` the final Hessian of the
class (`sfFinalK`), with the cutoff `|w| ≤ p₁` on every block and component (`gaussBox`), for the
representation `F`, the correction coefficients `vc` and the physical field `hv`
(`ctxBoxIntegral` of the context `F.ctx` of the torus). -/
noncomputable def sfBoxIntegral (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ)
    (hM6 : M = S.L ^ (P6.m₀ + C7.m₁)) (hkK : k ≤ K) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N)) (p1 : ℝ) (nK : ℕ) [NeZero nK]
    (g : GIdx S (sides S.L K nK) M K N → ℂ) : ℂ :=
  ctxBoxIntegral (F.ctx hM6 hkK nK) vc hv p1 g

end SmallField

/-!
### The class at given witnesses
-/

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
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ) (cut : ℝ → ℝ → ℝ → ℝ)

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
    ∀ (ℓ : ℕ) [NeZero ℓ], (T κ c₉).M * (T κ c₉).L ^ (kf + 1) ∣ ℓ →
      ActSupportAt d N (T κ c₉).L (T κ c₉).M k ℓ (inhObs F.sf (P6 κ c₉).m₀ h) ∧
        ActAnalyticAt d N ℓ (inhObs F.sf (P6 κ c₉).m₀ h) ∧
        ActBoundAt d N (T κ c₉).L (T κ c₉).M κ c₉ δ k ℓ (inhObs F.sf (P6 κ c₉).m₀ h)

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

/-- **A6-3, the small-field part of the last integral (P4 §6 (6.1)–(6.7); P7 (4.1)–(4.11), the
term with no final large-field region, and (4.15)–(4.17); LFR Theorem IV.4.1; blocker 5, small-field
half).** For a member `ρ` of `ℛ♭_k` at the stopping scale (`ν_k > 7/8 L⁻²`, so the variational problem
of the last integral is massive), with a representation `F`: on every torus of the family and every
source of the unit `ℓ¹` ball, the box integral `Ξ_box` (`sfBoxIntegral`: the fluctuation integral of
the small-field factor of the whole torus in the variable `w = K^{1/2}(ψ_k - h)`, `K = β_k D` the final
Hessian, with the cutoff `|w| ≤ p₁` of P4 (6.6), at the cutoff `p₁ = cut κ c₉ β_k`) is
`exp(E + ⟨g, h⟩ + ∑_{j=1}^{k} ∑_X q_j(X; g) + ∑_X a(X; g))`, where `q_j` are the inherited
observable activities (`inhObs`; the terms `⟨g, ℳ^{(j)}(·; h, h, g)⟩` of `ℱ_{k+1,0}`, P7 (4.17); they
are created at the scales `j ≤ k` and not changed afterwards, LFR Definition IV.5.2 first item, so the
pin `q = inhObs` is the source's) and `a` are activities of the scale `k + 1` in Root-F's form
(`ObservableActivitiesAt`: the clauses of `ObservableActivities` with top scale `k + 1` and half the
amplitude `c₉`, at the scale `k + 1` only): the term `ℳ^{(k+1)}_0` and the polymer terms
`ℛ^{(k+1)}_n` (P7 (4.9)), regrouped by the scale-`(k+1)` polymer `Ȳ` of their localization domain
(LFR Definition IV.5.2). The agreement clause of `a` (`ActAgree` of `actAt (k + 1) a`, the one
agreement obligation) comes from (D8) of the class and the locality of the last integral (LFR Theorem
IV.5.3 item 7). The part of `{χ_k ≠ 0}` outside the box is not here: there the source creates new
large-field regions (P7 (4.9)), and it belongs to the large-field half (`FinalLargeFieldInput`, at the
same cutoff). -/
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
      ObservableActivitiesAt d N (T κ c₉).L (T κ c₉).M κ (c₉ / 2) δ (k + 1) kf a ∧
      ∀ (nK : ℕ) [NeZero nK]
        (g : GIdx 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
          (kf + 1) N → ℂ), g ∈ l1Ball _ →
        sfBoxIntegral F hM6 hkK vc h (cut κ c₉ (F.sf.β k)) nK g =
          Complex.exp (E nK + ∑ x, ∑ i, g (x, i) * (h i : ℂ)
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
`∫ ρ dψ_k = Ξ_box exp(∑_X b(X; g))`, where `Ξ_box` is the small-field part (`sfBoxIntegral`, at the
cutoff `p₁ = cut κ c₉ β_k` of `FinalSmallFieldInput`) and `b` are activities of the scale `k + 1` in
Root-F's form (`ObservableActivitiesAt`: the clauses of `ObservableActivities` with top scale `k + 1`
and half the amplitude `c₉`, at the scale `k + 1` only). In the source: the last integral of every
history (P7 (4.1)–(4.9): the operators `𝕋'_{k+1}(Z', 𝔸')` with no free variable), including the
histories with no large-field region outside the box of the Gaussian variable (the part of
`{χ_k ≠ 0}` where the fluctuation field exceeds `p₁` creates the final large-field regions, P7 (4.9)),
the completion of the small-field functions to the whole torus (P7 (4.11): the term with no final
large-field region is `Ξ_box`), the gas of the heavy objects `Z'` with weights bounded by (IV.4.1)
`e^{-p₂(β_{k₀})/2 - H^{fin}|Z'|}` and the couplings `ℬ''` (linked: activating set and footprint), and
its exponentiation (PE-L; P7 (4.12)–(4.14)) into `𝒫^{(k+1)}`, regrouped by scale-`(k+1)` polymers. -/
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
      ObservableActivitiesAt d N (T κ c₉).L (T κ c₉).M κ (c₉ / 2) δ (k + 1) kf b ∧
      ∀ (nK : ℕ) [NeZero nK]
        (g : GIdx 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
          (kf + 1) N → ℂ), g ∈ l1Ball _ →
        ∫ ψ, ρ nK ψ g = sfBoxIntegral F hM6 hkK vc h (cut κ c₉ (F.sf.β k)) nK g *
          Complex.exp (∑ X, b ((T κ c₉).M * sides (T κ c₉).L (kf + 1) nK (kf + 1) *
            (T κ c₉).L ^ (kf + 1)) (k + 1) X (fun x i => g (x, i)))

/-- **The last integral from its sub-inputs** (LFR Theorem IV.4.1 with Definition IV.5.2 and Theorem
IV.5.3): the activities are `p = q + 1_{j = k+1} (a + b)`, with `q` the inherited observable
activities (`inhObs`; A6-1, A6-2, and locality from the class, `inhObs_actLocal`), `a` the
activities of the small-field part `Ξ_box` (A6-3) and `b` those of the large-field part `∫ ρ / Ξ_box`
(A6-4), the two halves at the same cutoff `cut`; `E` is the vacuum term of A6-3. The bounds: `q` at
the scales `≤ k`, `a + b` at the scale `k + 1` with the amplitudes `c₉/4 + c₉/4`. The threshold is the
largest of the four thresholds. -/
theorem lastIntegralInput_of_parts (hB : InheritedBoundInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ)
    (hA : InheritedAgreeInput d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hS : FinalSmallFieldInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ cut)
    (hL : FinalLargeFieldInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ cut) :
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
  obtain ⟨hM6, hkK, R, geo, cs, P, F, St, vc, hrep⟩ := hρ
  have hinh := h₁ β hβ₁ ν hν hνL h hh kf hkf k hk1 hk ρ νk hM6 hkK R geo cs P F St vc hrep hstop
  have hagr := h₂ β hβ₂ ν hν hνL h hh kf hkf k hk1 hk ρ νk hM6 hkK R geo cs P F St vc hrep hstop
  obtain ⟨a, E, ⟨hA, hgA⟩, hidA⟩ :=
    h₃ β hβ₃ ν hν hνL h hh kf hkf k hk1 hk ρ νk hM6 hkK R geo cs P F St vc hrep hstop
  obtain ⟨b, ⟨hB', hgB⟩, hidB⟩ :=
    h₄ β hβ₄ ν hν hνL h hh kf hkf k hk1 hk ρ νk hM6 hkK R geo cs P F St vc hrep hstop
  have e : actAt (k + 1) (actAdd a b) =
      actAt (k + 1) (actAdd (actAt (k + 1) a) (actAt (k + 1) b)) := by
    rw [actAt_actAdd, actAt_actAdd, actAt_actAt, actAt_actAt]
  refine ⟨actAdd (inhObs F.sf (P6 κ c₉).m₀ h) (actAt (k + 1) (actAdd a b)), E,
    ⟨fun ℓ _ hℓ => ?_, by rw [e]; exact hagr.add ((hgA.add hgB).actAt (k + 1))⟩, ?_⟩
  · rw [e]
    obtain ⟨hs, han, hbd⟩ := hinh ℓ hℓ
    obtain ⟨hsA, haA, hlA, hbA⟩ := hA ℓ hℓ
    obtain ⟨hsB, haB, hlB, hbB⟩ := hB' ℓ hℓ
    have hbAB := hbA.add hbB
    rw [add_halves] at hbAB
    exact ⟨(hs.mono (Nat.le_succ k)).add ((hsA.add hsB).actAt (k + 1)),
      han.add ((haA.add haB).actAt (k + 1)),
      (inhObs_actLocal hrep.sfFlat (P6 κ c₉).m₀ h ℓ
        (readTorus_div (m₀ := (P6 κ c₉).m₀) hkK (by rw [← hM6]; exact hℓ))).add ((hlA.add hlB).actAt (k + 1)),
      ActBoundAt.add_actAt_succ hs hbd hbAB⟩
  · intro nK _ g hg
    rw [hidB nK g hg, hidA nK g hg, ← Complex.exp_add,
      sum_actAdd_actAt _ _ _ _ fun X => inhObs_of_lt _ _ _ (Nat.lt_succ_self k) X _]
    congr 1
    ring

end Inputs

end Balaban.RootFSpine
