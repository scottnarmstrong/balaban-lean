/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.InheritedBound
public import Balaban.Spine.FinalConstField
public import Balaban.Spine.FinalSfBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The source term at the constant configuration as the inherited observable activities

A6-3 (a), assembly: `Σ_X q_j(X; g) = ⟨g, ℳ^{(j)}(h, h, g)⟩ = Floc_j` on the Def-6 torus
(`sum_inhObs_eq_Floc`): the sum over the polymers `X` of the activities `inhObs` and the sum over the
sites of the aggregated terms `ℳ^{(j)}(x) = Σ_{X ∋ x} ℳ^{(j)}(x, X)` are the same finite double sum.
-/

@[expose] public section

open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.Multiscale Balaban.Background

namespace Balaban.RootFSpine

section Sum

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

open Classical in
/-- **`Σ_X q_j(X; g) = Floc_j`**: the sum over all sets `X` of sites of the activities `inhObs` of a
scale `1 ≤ j ≤ k` at the constant configuration is the source term `Floc` of Def-6. -/
theorem sum_inhObs_eq_Floc (sf : SFData d L m₁ k N ϱ) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N))
    {N₁ : ℕ} [NeZero N₁] {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (g : Torus d (N₁ * L ^ m₁ * L ^ k) → Fin N → ℂ) :
    ∑ X : Finset (Torus d (N₁ * L ^ m₁ * L ^ k)),
      inhObs sf m₀ hv (N₁ * L ^ m₁ * L ^ k) j X g =
    Floc m₀ (sf.Tm N₁) j (Def6.constFld (hC hv)) (Def6.constFld (hC hv)) g := by
  classical
  have hcoord : ∀ (x : CTorus d L N₁ m₁ k) (i : Fin N),
      Mloc m₀ (sf.Tm N₁) j x (Def6.constFld (hC hv)) (Def6.constFld (hC hv)) g i =
        ∑ Y : Set (CTorus d L N₁ m₁ k),
          if Y ∈ polysAt m₀ j x then
            (sf.Tm N₁).M j x Y (Def6.constFld (hC hv)) (Def6.constFld (hC hv)) g i else 0 := by
    intro x i
    unfold Mloc
    rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.sum_apply]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext Y; simp
  have hL : ∀ X : Finset (Torus d (N₁ * L ^ m₁ * L ^ k)),
      inhObs sf m₀ hv (N₁ * L ^ m₁ * L ^ k) j X g =
        ∑ x : CTorus d L N₁ m₁ k, ∑ i : Fin N,
          if Def6.IsPolyDom m₀ j (X : Set (CTorus d L N₁ m₁ k)) ∧ x ∈ X then
            g x i * (sf.Tm N₁).M j x (X : Set (CTorus d L N₁ m₁ k))
              (Def6.constFld (hC hv)) (Def6.constFld (hC hv)) g i else 0 := by
    intro X
    rw [inhObs_eq_explicit]
    by_cases hP : Def6.IsPolyDom m₀ j (X : Set (CTorus d L N₁ m₁ k))
    · simp only [hj1, hjk, hP, and_self, ↓reduceIte]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x ∈ X
      · simp [hx]
      · simp [hx]
    · simp [hP]
  simp_rw [hL]
  rw [Finset.sum_comm]
  unfold Floc
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hcoord x i, Finset.mul_sum]
  refine Fintype.sum_equiv Fintype.finsetEquivSet _ _ fun X => ?_
  by_cases hP : Def6.IsPolyDom m₀ j (X : Set (CTorus d L N₁ m₁ k)) ∧ x ∈ X
  · simp [hP, polysAt, Fintype.finsetEquivSet]
  · simp [hP, polysAt, Fintype.finsetEquivSet]

open Classical in
/-- **`Σ_X q_j(X; g) = Floc_j` on a torus of side `ℓ = N₁ L^{m₁} L^k`**, the source read through the
coordinates `sfSite`. -/
theorem sum_inhObs_eq_Floc' (sf : SFData d L m₁ k N ϱ) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N))
    {N₁ ℓ : ℕ} [NeZero N₁] [NeZero ℓ] (hℓ : ℓ = N₁ * L ^ m₁ * L ^ k) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (g : Torus d ℓ → Fin N → ℂ) :
    ∑ X : Finset (Torus d ℓ), inhObs sf m₀ hv ℓ j X g =
    Floc m₀ (sf.Tm N₁) j (Def6.constFld (hC hv)) (Def6.constFld (hC hv))
      (fun x => g (sfSite ℓ x)) := by
  subst hℓ
  have : (fun x : CTorus d L N₁ m₁ k => g (sfSite (N₁ * L ^ m₁ * L ^ k) x)) = g := by
    funext x; rw [sfSite_eq_self]
  rw [this]
  exact sum_inhObs_eq_Floc sf m₀ hv hj1 hjk g

end Sum

/-- The identification of tori of equal side preserves the representatives of the coordinates. -/
theorem torusCast_val' {d a b : ℕ} (h : a = b) (y : Torus d a) (i : Fin d) :
    ((torusCast h y) i).val = (y i).val := by
  subst h; rfl

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (hv : EuclideanSpace ℝ (Fin N))

/-- The fine torus of the history is the Def-6 torus of the context. -/
theorem fine_eq_def6 : M * n K * S.L ^ K = C.N₁ * S.L ^ m₁ * S.L ^ k := by
  have h1 := histScale_eq C.geo.hM C.hnn (Nat.zero_le k) C.hkK
  simp only [Nat.sub_zero] at h1
  rw [C.hT]; exact h1.symm

/-- **The source on the Def-6 torus is the source on the fine torus read through `sfSite`.** -/
theorem sfG_eq_sfSite (g : GIdx S n M K N → ℂ) :
    sfG C.geo C.hnn C.hkK C.hT g =
      fun x i => g (sfSite (M * n K * S.L ^ K) x, i) := by
  funext x i
  have : bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT x) = sfSite (M * n K * S.L ^ K) x := by
    funext μ
    apply ZMod.val_injective
    unfold bgToFine sfToBg
    rw [torusCast_val', torusCast_val']
    unfold sfSite
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
    rw [fine_eq_def6 C]
    exact ZMod.val_lt _
  unfold sfG
  rw [this]

open Classical in
/-- **The exponent of the small-field factor at the constant configuration**: the value of
`𝒜_k + ℱ_k` (without `ℛ^{(k)}`) at `ψ_k ≡ h` on the whole torus is the vacuum term
`ℰ_k(h) - E_k |T|_k`, the source term `⟨g, h⟩` and the inherited observable activities
`Σ_j Σ_X q_j(X; g)` (the action vanishes, `actStar2_const_univ`). -/
theorem const_exponent (vc : CorrCoef S.d)
    (H : BgHyp S.d S.L k (minSep S.L C.geo.M1) C.weights (C.cs.muBg k))
    (he : ∑ i, hv i ^ 2 = 1) (hk : 1 ≤ k) (g : GIdx S n M K N → ℂ) :
    Ares2 C vc Set.univ (fun _ => hv) hv + C.Fres Set.univ (fun _ => hv) hv g =
      (EresK2 C vc Set.univ (fun _ => hv) hv -
          ((C.sf.E C.N₁ * volK M (Set.univ : Set (Torus S.d (n k))) : ℝ) : ℂ)) +
        (∑ y : Torus S.d (M * n K * S.L ^ K), ∑ i : Fin N, g (y, i) * (hv i : ℂ)) +
        ∑ j ∈ Finset.Icc 1 k, ∑ X : Finset (Torus S.d (M * n K * S.L ^ K)),
          inhObs C.sf C.m₀ hv (M * n K * S.L ^ K) j X (fun x i => g (x, i)) := by
  rw [Fres_const_univ C hv H he hk g]
  have hA : Ares2 C vc Set.univ (fun _ => hv) hv =
      EresK2 C vc Set.univ (fun _ => hv) hv -
        ((C.sf.E C.N₁ * volK M (Set.univ : Set (Torus S.d (n k))) : ℝ) : ℂ) := by
    unfold Ares2
    rw [actStar2_const_univ C hv H he hk]
    simp
  rw [hA]
  have hbij : Function.Bijective (bgToFine C.geo C.hnn C.hkK) :=
    ⟨torusCast_injective' _, torusCast_surjective' _⟩
  have hsum : (∑ x : BgT C.geo k, ∑ i : Fin N, g (bgToFine C.geo C.hnn C.hkK x, i) * (hv i : ℂ)) =
      ∑ y : Torus S.d (M * n K * S.L ^ K), ∑ i : Fin N, g (y, i) * (hv i : ℂ) :=
    Fintype.sum_equiv (Equiv.ofBijective _ hbij) _ _ fun x => rfl
  have hF : ∀ j ∈ Finset.Icc 1 k,
      Def6.Floc C.m₀ (C.sf.Tm C.N₁) j (Def6.constFld (fun i => (hv i : ℂ)))
        (Def6.constFld (hC hv)) (sfG C.geo C.hnn C.hkK C.hT g) =
      ∑ X : Finset (Torus S.d (M * n K * S.L ^ K)),
        inhObs C.sf C.m₀ hv (M * n K * S.L ^ K) j X (fun x i => g (x, i)) := by
    intro j hj
    obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 hj
    rw [sfG_eq_sfSite C g]
    exact (sum_inhObs_eq_Floc' C.sf C.m₀ hv (fine_eq_def6 C) hj1 hjk (fun x i => g (x, i))).symm
  rw [hsum, Finset.sum_congr rfl hF]
  ring

end Ctx

end Balaban.RootFSpine
