module

public import Balaban.LargeField.Base.BaseHistory
public import Balaban.LargeField.Base.BasePhysicalDensity
public import Balaban.LargeField.Operators.Symm
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic

/-!
# Typing data of the physical base carrier (ruling R7)

The carrier `BaseSmallFieldInput` of `BaseSmallField.lean` is specialized to `M = K = 1`.  Its
primary datum is a function of the complex source of
the physical torus `Torus d (L n_1)`, while the large-field layer indexes the source by
`GIdx S n 1 1 N`, a function on `Torus d (1 * n_1 * L ^ 1)`.  This file holds the three pieces of
typing data that the carrier needs:

* `baseZsites`, `baseSourceNorm`: the fine sites of the component `Z'` and the `ℓ¹` norm of the
  source on them (the source of the carrier is read on `Z'` only);
* `baseSiteEquiv`, `baseSourceEquiv`: the explicit reindexing of sites and of the source between
  the physical torus and `GIdx S n 1 1 N`;
* `baseRotSrc`: the action of `O(N)` on the physical source.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

section Carrier

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] [NeZero S.L] {R : ℕ → ℝ} {k0 K N : ℕ}

/-- The fine sites of the component `Z'` of `Z^pre_1`, as fine sites `Torus d (1 * n_1 * L ^ 1)` of the large-field layer. -/
def baseZsites (H : RegionHistory S n R k0 K) (Z' : H.Comp 1) :
    Set (Torus S.d (1 * n 1 * S.L ^ 1)) :=
  fineSet (S := S) (n := n) 1 1 1 (Z'.1 : Set (Torus S.d (n 1)))

theorem base_site_size_eq (S : Setting) (n : ℕ → ℕ) : S.L * n 1 = 1 * n 1 * S.L ^ 1 := by ring

/-- The sites of the physical torus `Torus d (L n_1)` as the fine sites `Torus d (1 * n_1 * L ^ 1)`
of the large-field layer. -/
def baseSiteEquiv (S : Setting) (n : ℕ → ℕ) :
    Torus S.d (S.L * n 1) ≃ Torus S.d (1 * n 1 * S.L ^ 1) :=
  Equiv.piCongrRight fun _ => (ZMod.ringEquivCongr (base_site_size_eq S n)).toEquiv

/-- The external field of the large-field layer, transported to the physical torus. -/
def baseSource (S : Setting) (n : ℕ → ℕ) (N : ℕ) (g : GIdx S n 1 1 N → ℂ) :
    Torus S.d (S.L * n 1) → Fin N → ℂ :=
  fun x i => g (baseSiteEquiv S n x, i)

/-- The reindexing `Torus d (L n_1) → Fin N → ℂ` versus `GIdx S n 1 1 N → ℂ`, as an equivalence. -/
def baseSourceEquiv (S : Setting) (n : ℕ → ℕ) (N : ℕ) :
    (GIdx S n 1 1 N → ℂ) ≃ (Torus S.d (S.L * n 1) → Fin N → ℂ) where
  toFun := baseSource S n N
  invFun h p := h ((baseSiteEquiv S n).symm p.1) p.2
  left_inv g := by
    funext p
    simp [baseSource]
  right_inv h := by
    funext x i
    simp [baseSource]

theorem baseSourceEquiv_apply (g : GIdx S n 1 1 N → ℂ) :
    baseSourceEquiv S n N g = baseSource S n N g := rfl

theorem baseSource_apply (g : GIdx S n 1 1 N → ℂ) (x : Torus S.d (S.L * n 1)) (i : Fin N) :
    baseSource S n N g x i = g (baseSiteEquiv S n x, i) := rfl

theorem baseSource_zero : baseSource S n N (0 : GIdx S n 1 1 N → ℂ) = 0 := rfl

theorem baseSource_bijective : Function.Bijective (baseSource S n N) :=
  (baseSourceEquiv S n N).bijective

/-- The reindexing preserves the `ℓ¹` norm of the source. -/
theorem sum_norm_baseSource (g : GIdx S n 1 1 N → ℂ) :
    ∑ x, ∑ i, ‖baseSource S n N g x i‖ = ∑ p : GIdx S n 1 1 N, ‖g p‖ := by
  rw [← Finset.univ_product_univ, Finset.sum_product]
  exact Fintype.sum_equiv (baseSiteEquiv S n) _ _ fun x => rfl

/-- Rotation of the physical source: `(ρ g)(x) = ρ g(x)`, transported from `rotG`. -/
noncomputable def baseRotSrc (ρ : OrthN N) (g : Torus S.d (S.L * n 1) → Fin N → ℂ) :
    Torus S.d (S.L * n 1) → Fin N → ℂ :=
  baseSourceEquiv S n N (rotG ρ ((baseSourceEquiv S n N).symm g))

theorem baseRotSrc_baseSource (ρ : OrthN N) (g : GIdx S n 1 1 N → ℂ) :
    baseRotSrc ρ (baseSource S n N g) = baseSource S n N (rotG ρ g) := by
  unfold baseRotSrc
  change baseSourceEquiv S n N (rotG ρ ((baseSourceEquiv S n N).symm (baseSourceEquiv S n N g))) = _
  rw [Equiv.symm_apply_apply]; rfl

theorem baseRotSrc_zero (ρ : OrthN N) : baseRotSrc ρ (0 : Torus S.d (S.L * n 1) → Fin N → ℂ) = 0 := by
  have := baseRotSrc_baseSource (S := S) (n := n) ρ (0 : GIdx S n 1 1 N → ℂ)
  rw [baseSource_zero] at this
  rw [this]
  funext x i
  simp [baseSource, rotG]

/-- The `ℓ¹` norm `‖g|_{Z'}‖_1` of the source of the large-field layer on the sites of the component
`Z'`. -/
noncomputable def baseSourceNorm (H : RegionHistory S n R k0 K) (Z' : H.Comp 1)
    (g : GIdx S n 1 1 N → ℂ) : ℝ :=
  open Classical in
  ∑ i : GIdx S n 1 1 N, if i.1 ∈ baseZsites H Z' then ‖g i‖ else 0

end Carrier

end Balaban.LargeField
