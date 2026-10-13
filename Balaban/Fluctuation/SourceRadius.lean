/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SourceFamilyRelative
public import Balaban.Inhabited.SourceExponentFamily
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The physical source carriers at a general radius

The landed carriers of the source lane (`l1Ball`, `physSΛ`, `physV`, `physVq`, `physFibre`) use the
unit ball `∑ |g| < 1` of sources.  Here the same carriers are defined at a general radius `ρ`; at
`ρ = 1` each is the landed carrier (`l1BallRho_one`, ..., `physFibreRho_one`, all by `rfl`).  The
normalized carriers `l1BallEta`, `physSΛEta` of the sources `g/β` are unchanged.

* `l1BallRho`, `physSΛRho`, `physVRho`, `physVqRho`, `physFibreRho`;
* monotonicity in `ρ`, `physVqRho_self`, openness (`isOpen_l1BallRho`, `isOpen_physVRho`,
  `isOpen_physVqRho`), `zero_mem_l1BallRho`, star-shapedness (`smul_mem_l1BallRho`), the
  component bound `norm_le_of_mem_l1BallRho`;
* `sourceSlice_mem_restricted_rho`: `∑ |g| < q ≤ ρ`, `max 1 ρ ≤ β` give `g/β ∈ l1BallEta (q/β)`
  (the landed `sourceSlice_mem_restricted` is the case `ρ = 1`), and the image of the scaled
  inclusion on `physVqRho` (`physInclScaled_image_subset_rho`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer Balaban.Background
  Balaban.SmallField Finset Metric

section Carriers

variable {d L N₁ m₁ k K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The ball of radius `ρ` of the sources `g` in `ℓ¹`: `∑_{x,i} |g(x,i)| < ρ`. -/
def l1BallRho (d L N₁ m₁ K N : ℕ) [NeZero N₁] [NeZero L] (ρ : ℝ) :
    Set (CTorus d L N₁ m₁ K → Fin N → ℂ) :=
  {g | ∑ x, ∑ i, ‖g x i‖ < ρ}

theorem l1BallRho_one : l1BallRho d L N₁ m₁ K N 1 = l1Ball d L N₁ m₁ K N := rfl

theorem l1BallRho_mono {ρ ρ' : ℝ} (h : ρ ≤ ρ') :
    l1BallRho d L N₁ m₁ K N ρ ⊆ l1BallRho d L N₁ m₁ K N ρ' :=
  fun _ hg => lt_of_lt_of_le hg h

theorem isOpen_l1BallRho (ρ : ℝ) : IsOpen (l1BallRho d L N₁ m₁ K N ρ) :=
  isOpen_lt (by fun_prop) continuous_const

theorem zero_mem_l1BallRho {ρ : ℝ} (hρ : 0 < ρ) :
    (0 : CTorus d L N₁ m₁ K → Fin N → ℂ) ∈ l1BallRho d L N₁ m₁ K N ρ := by
  show ∑ x, ∑ i, ‖(0 : CTorus d L N₁ m₁ K → Fin N → ℂ) x i‖ < ρ
  simpa using hρ

theorem smul_mem_l1BallRho {ρ : ℝ} {g : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hg : g ∈ l1BallRho d L N₁ m₁ K N ρ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((t : ℂ) • g) ∈ l1BallRho d L N₁ m₁ K N ρ := by
  have hs : ∑ x, ∑ i, ‖((t : ℂ) • g) x i‖ = t * ∑ x, ∑ i, ‖g x i‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Real.norm_of_nonneg ht0]
  have h0 : 0 ≤ ∑ x, ∑ i, ‖g x i‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  show ∑ x, ∑ i, ‖((t : ℂ) • g) x i‖ < ρ
  rw [hs]
  have hg' : ∑ x, ∑ i, ‖g x i‖ < ρ := hg
  nlinarith

theorem norm_le_of_mem_l1BallRho {ρ : ℝ} {g : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hg : g ∈ l1BallRho d L N₁ m₁ K N ρ) (y : CTorus d L N₁ m₁ K) (i : Fin N) :
    ‖g y i‖ ≤ ρ := by
  have h1 : ‖g y i‖ ≤ ∑ i', ‖g y i'‖ :=
    Finset.single_le_sum (f := fun i' => ‖g y i'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have h2 : ∑ i', ‖g y i'‖ ≤ ∑ x, ∑ i', ‖g x i'‖ :=
    Finset.single_le_sum (f := fun x => ∑ i', ‖g x i'‖) (fun _ _ => Finset.sum_nonneg
      fun _ _ => norm_nonneg _) (Finset.mem_univ y)
  have : ∑ x, ∑ i', ‖g x i'‖ < ρ := hg
  linarith

/-- The scaled slice: `∑ |g| < q ≤ ρ` and `max 1 ρ ≤ β` give `g/β ∈ l1BallEta (q/β)`. -/
theorem sourceSlice_mem_restricted_rho {ρ β q : ℝ} (hβ : max 1 ρ ≤ β)
    {g : CTorus d L N₁ m₁ K → Fin N → ℂ} (hg : ∑ x, ∑ i, ‖g x i‖ < q) (hq : q ≤ ρ) :
    (fun y i => g y i / (β : ℂ)) ∈ l1BallEta d L N₁ m₁ K N (q / β) := by
  have hβ1 : 1 ≤ β := le_trans (le_max_left _ _) hβ
  have hβρ : ρ ≤ β := le_trans (le_max_right _ _) hβ
  have hβ0 : 0 < β := by linarith
  have hsum : ∑ x, ∑ i, ‖g x i / (β : ℂ)‖ = (∑ x, ∑ i, ‖g x i‖) / β := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hβ0.le]
  have h1 : (∑ x, ∑ i, ‖g x i‖) / β < q / β := div_lt_div_of_pos_right hg hβ0
  have h2 : q / β ≤ 1 := by
    rw [div_le_one hβ0]; linarith
  exact ⟨by rw [l1Ball, Set.mem_ofPred_eq, hsum]; exact lt_of_lt_of_le h1 h2, by rw [hsum]; exact h1.le⟩

/-- The landed `sourceSlice_mem_restricted` is the case `ρ = 1`. -/
theorem sourceSlice_mem_restricted_of_rho {β q : ℝ} (hβ : 1 ≤ β)
    {g : CTorus d L N₁ m₁ K → Fin N → ℂ} (hg : ∑ x, ∑ i, ‖g x i‖ < q) (hq : q ≤ 1) :
    (fun y i => g y i / (β : ℂ)) ∈ l1BallEta d L N₁ m₁ K N (q / β) :=
  sourceSlice_mem_restricted_rho (by simpa using hβ) hg hq

variable (S : StepSetting d L N₁ m₁ k N ϱ)

/-- The admissible parameters of the physical expansion with sources of `ℓ¹`-size `< ρ`. -/
def physSΛRho (S : StepSetting d L N₁ m₁ k N ϱ) (a₁ ν eps ρ : ℝ) :
    Set (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) :=
  XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1BallRho d L N₁ m₁ (k + 1) N ρ

/-- The admissible parameters of the chart at radius `ρ`. -/
def physVRho (S : StepSetting d L N₁ m₁ k N ϱ) (a₁ ν eps ρ : ℝ) : Set (physParam N S) :=
  physIncl N S ⁻¹' physSΛRho S a₁ ν eps ρ

/-- The parameters of `physVRho … ρ` whose source has `∑ |g| < q`. -/
def physVqRho (S : StepSetting d L N₁ m₁ k N ϱ) (a₁ ν eps ρ q : ℝ) : Set (physParam N S) :=
  {e | e ∈ physVRho S a₁ ν eps ρ ∧ ∑ x, ∑ i, ‖e.2 x i‖ < q}

/-- The constant-`h₀` fibre of the chart at radius `ρ`. -/
def physFibreRho (S : StepSetting d L N₁ m₁ k N ϱ) (a₁ ν eps ρ : ℝ) : Set (physParam N S) :=
  {e | e ∈ physVRho S a₁ ν eps ρ ∧
    ∀ y i, (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 y i = (S.h₀ i : ℂ)}

theorem physSΛRho_one (a₁ ν eps : ℝ) : physSΛRho S a₁ ν eps 1 = physSΛ S a₁ ν eps := rfl

theorem physVRho_one (a₁ ν eps : ℝ) :
    physVRho (N := N) S a₁ ν eps 1 = physV S a₁ ν eps := rfl

theorem physVqRho_one (a₁ ν eps q : ℝ) :
    physVqRho (N := N) S a₁ ν eps 1 q = physVq S a₁ ν eps q := rfl

theorem physFibreRho_one (a₁ ν eps : ℝ) :
    physFibreRho (N := N) S a₁ ν eps 1 = physFibre S a₁ ν eps := rfl

theorem physSΛRho_mono (a₁ ν eps : ℝ) {ρ ρ' : ℝ} (h : ρ ≤ ρ') :
    physSΛRho S a₁ ν eps ρ ⊆ physSΛRho S a₁ ν eps ρ' :=
  Set.prod_mono (subset_refl _) (l1BallRho_mono h)

theorem physVRho_mono (a₁ ν eps : ℝ) {ρ ρ' : ℝ} (h : ρ ≤ ρ') :
    physVRho (N := N) S a₁ ν eps ρ ⊆ physVRho S a₁ ν eps ρ' :=
  fun _ he => physSΛRho_mono S a₁ ν eps h he

theorem physVqRho_mono (a₁ ν eps q : ℝ) {ρ ρ' : ℝ} (h : ρ ≤ ρ') :
    physVqRho (N := N) S a₁ ν eps ρ q ⊆ physVqRho S a₁ ν eps ρ' q :=
  fun _ he => ⟨physVRho_mono S a₁ ν eps h he.1, he.2⟩

theorem physFibreRho_mono (a₁ ν eps : ℝ) {ρ ρ' : ℝ} (h : ρ ≤ ρ') :
    physFibreRho (N := N) S a₁ ν eps ρ ⊆ physFibreRho S a₁ ν eps ρ' :=
  fun _ he => ⟨physVRho_mono S a₁ ν eps h he.1, he.2⟩

theorem physVqRho_mono_q (a₁ ν eps ρ : ℝ) {q q' : ℝ} (h : q ≤ q') :
    physVqRho (N := N) S a₁ ν eps ρ q ⊆ physVqRho S a₁ ν eps ρ q' :=
  fun _ he => ⟨he.1, lt_of_lt_of_le he.2 h⟩

theorem physVqRho_subset (a₁ ν eps ρ q : ℝ) :
    physVqRho (N := N) S a₁ ν eps ρ q ⊆ physVRho S a₁ ν eps ρ := fun _ h => h.1

theorem physFibreRho_subset (a₁ ν eps ρ : ℝ) :
    physFibreRho (N := N) S a₁ ν eps ρ ⊆ physVRho S a₁ ν eps ρ := fun _ h => h.1

theorem physVqRho_self (a₁ ν eps ρ : ℝ) :
    physVqRho (N := N) S a₁ ν eps ρ ρ = physVRho S a₁ ν eps ρ :=
  Set.ext fun _ => ⟨fun h => h.1, fun h => ⟨h, h.2⟩⟩

theorem isOpen_physVRho (a₁ ν eps ρ : ℝ) (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) :
    IsOpen (physVRho (N := N) S a₁ ν eps ρ) :=
  (isOpen_preimage_xiCRaw (G := S.G') (N := N) (n := k + 1) (σ := 1) (ε := eps) H).prod
    (isOpen_l1BallRho ρ)

theorem isOpen_physVqRho (a₁ ν eps ρ q : ℝ) (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) :
    IsOpen (physVqRho (N := N) S a₁ ν eps ρ q) := by
  have h2 : IsOpen {e : physParam N S | ∑ x, ∑ i, ‖e.2 x i‖ < q} :=
    isOpen_lt (by fun_prop) continuous_const
  exact (isOpen_physVRho S a₁ ν eps ρ H).inter h2

/-- **The image in the slice** at radius `ρ`: for `max 1 ρ ≤ β`, `0 < ρ` and `q ≤ ρ`,
`(q, g) ↦ (q, g/β)` maps `physVqRho … ρ q` into `physSΛEta … (q/β)`. -/
theorem physInclScaled_image_subset_rho (a₁ ν eps : ℝ) {ρ β q : ℝ}
    (hβ : max 1 ρ ≤ β) (hq : q ≤ ρ) :
    physInclScaled N S ((1 / β : ℝ) : ℂ) '' physVqRho S a₁ ν eps ρ q ⊆
      physSΛEta S a₁ ν eps (q / β) := by
  rintro _ ⟨e, ⟨he, hsum⟩, rfl⟩
  refine ⟨he.1, ?_⟩
  have h := sourceSlice_mem_restricted_rho (N := N) hβ hsum hq
  have hfun : (fun y i => ((1 / β : ℝ) : ℂ) * e.2 y i) = fun y i => e.2 y i / (β : ℂ) := by
    funext y i
    push_cast
    ring
  show (fun y i => ((1 / β : ℝ) : ℂ) * e.2 y i) ∈ _
  rw [hfun]
  exact h

end Carriers

end Balaban.Fluctuation
