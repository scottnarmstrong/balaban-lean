/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0BoxLift
public import Balaban.LargeField.Base.KF0AllPlusGasC
public import Balaban.Polymer.MayerTransport
import Balaban.Polymer.TwoTorusE1Coef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0BlockLift`: the local terms of the all-plus gas on two tori

Let `ι = boxMap (s m) (s m₂)` be the box map of the sites of two tori of sides `s m` and `s m₂`,
`Y` a set of blocks of the first torus whose sites lie in a box that does not wrap around either
torus, and `σ` a map of blocks, injective on `Y`, with `blockOf (ι y) = σ (blockOf y)` for the sites
`y` of `Y`. Then:

* `siteSet_image_boxMap`, `haloFibre_image_boxMap`: the sites of the blocks `Z.image σ` and the
  halos over them are the images under `ι` of those over `Z`, for `Z ⊆ Y` (cardinality);
* `siteSum_lift`, `bondSum_lift`, `blockSrc_lift`, `gasTermC_lift`: the regrouped activity of `Z`
  at the source `g` and of `σ '' Z` at `g'` are equal on related configurations when `g' ∘ ι = g`
  on the sites of `Y` (`sum_sum_lift` reindexes the sums over anchors and halos);
* `integral_blockRef_lift`: integrals of functions of the blocks of `Z ⊆ Y` against the product
  block measures of the two tori correspond;
* `kf0PY_lift`: the local terms of the all-plus gas at `Y` and at `σ '' Y` agree
  (`PY_mayer_transport`).
-/

@[expose] public section

open Finset Balaban.Polymer Balaban.Green Balaban.LargeField.KF0F1 Balaban.LargeField.SphereChart

namespace Balaban.KF0Lift

section Sets

open Balaban.LargeField.KF0AllPlus

variable {d s m m2 R : ℕ} [NeZero s] [NeZero m] [NeZero m2]

omit [NeZero s] [NeZero m] [NeZero m2] in
theorem boxMap_injOn_box (hm2 : 2 * R + 1 < s * m2) {S : Finset (Torus d (s * m))}
    (hS : ∀ y ∈ S, InBox d R (s * m) y) :
    Set.InjOn (boxMap (s * m) (s * m2)) (S : Set (Torus d (s * m))) := fun a ha b hb h => by
  have := congrArg (boxMap (s * m2) (s * m)) h
  rwa [boxMap_boxMap hm2 (hS a ha), boxMap_boxMap hm2 (hS b hb)] at this

/-- The sites of the blocks `Z.image σ` are the images of the sites of the blocks `Z`. -/
theorem siteSet_image_boxMap (hm2 : 2 * R + 1 < s * m2)
    {Y : Finset (Torus d m)} (hY : ∀ y ∈ siteSet d s m Y, InBox d R (s * m) y)
    {σ : Torus d m → Torus d m2} (hσ : Set.InjOn σ (Y : Set (Torus d m)))
    (hrel : ∀ y ∈ siteSet d s m Y,
      blockOf d s m2 (boxMap (s * m) (s * m2) y) = σ (blockOf d s m y))
    {Z : Finset (Torus d m)} (hZ : Z ⊆ Y) :
    siteSet d s m2 (Z.image σ) = (siteSet d s m Z).image (boxMap (s * m) (s * m2)) := by
  have hsub : (siteSet d s m Z).image (boxMap (s * m) (s * m2)) ⊆ siteSet d s m2 (Z.image σ) := by
    intro x' hx'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
    have hxY : x ∈ siteSet d s m Y := by
      rw [mem_siteSet] at hx ⊢; exact hZ hx
    rw [mem_siteSet] at hx ⊢
    rw [hrel x hxY]
    exact Finset.mem_image_of_mem σ hx
  symm
  refine Finset.eq_of_subset_of_card_le hsub ?_
  have hinj : Set.InjOn (boxMap (s * m) (s * m2)) (siteSet d s m Z : Set (Torus d (s * m))) :=
    boxMap_injOn_box hm2 (S := siteSet d s m Z) fun y hy => hY y (by
      rw [mem_siteSet] at hy ⊢; exact hZ hy)
  rw [card_siteSet, Finset.card_image_of_injOn (fun a ha b hb h => hσ (hZ ha) (hZ hb) h),
    Finset.card_image_of_injOn hinj, card_siteSet]

/-- The site sets of the fibre over `Z.image σ` are the images of the site sets of the fibre over
`Z`. -/
theorem haloFibre_image_boxMap (hm2 : 2 * R + 1 < s * m2)
    {Y : Finset (Torus d m)} (hY : ∀ y ∈ siteSet d s m Y, InBox d R (s * m) y)
    {σ : Torus d m → Torus d m2} (hσ : Set.InjOn σ (Y : Set (Torus d m)))
    (hrel : ∀ y ∈ siteSet d s m Y,
      blockOf d s m2 (boxMap (s * m) (s * m2) y) = σ (blockOf d s m y))
    {Z : Finset (Torus d m)} (hZ : Z ⊆ Y) :
    haloFibre d s m2 (Z.image σ) =
      (haloFibre d s m Z).image (fun H => H.image (boxMap (s * m) (s * m2))) := by
  have hsZ : ∀ x ∈ siteSet d s m Z, x ∈ siteSet d s m Y := fun x hx => by
    rw [mem_siteSet] at hx ⊢; exact hZ hx
  have hSS := siteSet_image_boxMap hm2 hY hσ hrel hZ
  have himg : ∀ H : Finset (Torus d (s * m)), H ⊆ siteSet d s m Z →
      (H.image (boxMap (s * m) (s * m2))).image (blockOf d s m2) =
        (H.image (blockOf d s m)).image σ := by
    intro H hH
    rw [Finset.image_image, Finset.image_image]
    exact Finset.image_congr fun x hx => hrel x (hsZ x (hH hx))
  ext H'
  rw [Finset.mem_image]
  simp only [mem_haloFibre]
  constructor
  · intro hH'
    have hH'sub : H' ⊆ (siteSet d s m Z).image (boxMap (s * m) (s * m2)) := by
      intro x' hx'
      rw [← hSS, mem_siteSet, ← hH']
      exact Finset.mem_image_of_mem _ hx'
    set H : Finset (Torus d (s * m)) :=
      (siteSet d s m Z).filter (fun x => boxMap (s * m) (s * m2) x ∈ H') with hHdef
    have hHsub : H ⊆ siteSet d s m Z := Finset.filter_subset _ _
    have hHimg : H.image (boxMap (s * m) (s * m2)) = H' := by
      ext x'
      rw [Finset.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (Finset.mem_filter.1 hx).2
      · intro hx'
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (hH'sub hx')
        exact ⟨x, Finset.mem_filter.2 ⟨hx, hx'⟩, rfl⟩
    refine ⟨H, ?_, hHimg⟩
    have hsub : H.image (blockOf d s m) ⊆ Z := fun b hb => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hb
      exact (mem_siteSet d s m).1 (hHsub hx)
    refine TwoTorusStep.eq_of_image_eq_of_injOn hσ (hsub.trans hZ) hZ ?_
    rw [← himg H hHsub, hHimg, hH']
  · rintro ⟨H, hH, rfl⟩
    have hHsub : H ⊆ siteSet d s m Z := fun x hx => by
      rw [mem_siteSet, ← hH]; exact Finset.mem_image_of_mem _ hx
    rw [himg H hHsub, hH]

end Sets

section Vanish

open Balaban.LargeField.KF0Taylor

variable {d N n ℓ : ℕ} [NeZero ℓ] {h : EuclideanSpace ℝ (Fin N)}

theorem siteCoeff_zero_any (β ν a : ℝ) (b : Fin n → ℝ) : siteCoeff β ν a b 0 = 0 := by
  have hρ : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  have hx : (n : ℝ) * (1 / (2 * ((n : ℝ) + 1))) ^ 2 ≤ 1 / 4 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    rw [div_pow, one_pow, mul_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg (n : ℝ)]
  exact siteCoeff_zero β ν a b hρ hx

theorem bondCoeff_zero_any (β : ℝ) (n : ℕ) : bondCoeff β (bondFst n) (bondSnd n) 0 = 0 := by
  have hρ : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  have hx : (n : ℝ) * (1 / (2 * ((n : ℝ) + 1))) ^ 2 ≤ 1 / 4 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    rw [div_pow, one_pow, mul_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg (n : ℝ)]
  exact bondCoeff_zero β _ _ hρ (by rwa [card_bondFst]) (by rwa [card_bondSnd])

omit [NeZero ℓ] in
/-- The site piece vanishes unless the halo is connected and contains the anchor (no
smallness needed). -/
theorem f1SiteHalo_eq_zero [NeZero ℓ] (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (src : Torus d ℓ → Fin N → ℝ) (x : Torus d ℓ) (H : Finset (Torus d ℓ))
    (hH : ¬ (NNConnected H ∧ x ∈ H)) (ψ : Torus d ℓ → perp h) :
    f1SiteHalo e β ν src x H ψ = 0 := by
  refine kf0HaloTerm_eq_zero ν β _ _ _ (siteCoeff_zero_any _ _ _ _) (fun _ _ => Or.inl rfl) H ?_ ψ
  rintro ⟨h1, j, hj⟩
  exact hH ⟨h1, hj⟩

/-- The bond piece vanishes unless the halo is connected and contains an end of the bond. -/
theorem f1BondHalo_eq_zero (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (x : Torus d ℓ) (μ : Fin d) (H : Finset (Torus d ℓ))
    (hH : ¬ (NNConnected H ∧ (x + Pi.single μ 1 ∈ H ∨ x ∈ H))) (ψ : Torus d ℓ → perp h) :
    f1BondHalo e β ν x μ H ψ = 0 := by
  refine kf0HaloTerm_eq_zero ν β _ _ _ (bondCoeff_zero_any _ _) (bondAnchor_adj n x μ) H ?_ ψ
  rintro ⟨h1, hj⟩
  exact hH ⟨h1, bondAnchor_mem hj⟩

end Vanish

section Reindex

/-- **Reindexing a double sum over anchors and halos along an injection.** -/
theorem sum_sum_lift {α α' : Type*} [Fintype α] [Fintype α'] [DecidableEq α'] (φ : α → α')
    (S : Finset α) (S' : Finset α') (𝔽 : Finset (Finset α)) (𝔽' : Finset (Finset α'))
    (ψ : Finset α → Finset α') (F : α → Finset α → ℝ) (F' : α' → Finset α' → ℝ)
    (hS' : S' = S.image φ) (hφ : Set.InjOn φ (S : Set α)) (h𝔽' : 𝔽' = 𝔽.image ψ)
    (hψ : Set.InjOn ψ (𝔽 : Set (Finset α)))
    (hvan : ∀ x, x ∉ S → ∀ H ∈ 𝔽, F x H = 0) (hvan' : ∀ x', x' ∉ S' → ∀ H' ∈ 𝔽', F' x' H' = 0)
    (hlift : ∀ x ∈ S, ∀ H ∈ 𝔽, F' (φ x) (ψ H) = F x H) :
    ∑ x' : α', ∑ H' ∈ 𝔽', F' x' H' = ∑ x : α, ∑ H ∈ 𝔽, F x H := by
  have h1 : ∑ x' : α', ∑ H' ∈ 𝔽', F' x' H' = ∑ x' ∈ S', ∑ H' ∈ 𝔽', F' x' H' :=
    (Finset.sum_subset (Finset.subset_univ S') fun x' _ hx' =>
      Finset.sum_eq_zero fun H' hH' => hvan' x' hx' H' hH').symm
  have h2 : ∑ x : α, ∑ H ∈ 𝔽, F x H = ∑ x ∈ S, ∑ H ∈ 𝔽, F x H :=
    (Finset.sum_subset (Finset.subset_univ S) fun x _ hx =>
      Finset.sum_eq_zero fun H hH => hvan x hx H hH).symm
  rw [h1, h2, hS', Finset.sum_image hφ]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [h𝔽', Finset.sum_image hψ]
  exact Finset.sum_congr rfl fun H hH => hlift x hx H hH

end Reindex

section Nbhd

variable {d : ℕ} {R m : ℕ}

theorem valMinAbs_add_int_of_abs_le (hm : 2 * (R + 1) + 1 < m) (a : ZMod m) {z : ℤ}
    (ha : |a.valMinAbs| ≤ R) (hz : |z| ≤ 1) : (a + (z : ZMod m)).valMinAbs = a.valMinAbs + z := by
  have h1 : a + (z : ZMod m) = (((a.valMinAbs + z : ℤ)) : ZMod m) := by
    rw [Int.cast_add, ZMod.coe_valMinAbs]
  rw [h1]
  refine valMinAbs_intCast_of_abs_le (r := R + 1) hm ?_
  rw [abs_le] at ha hz ⊢
  constructor <;> omega

theorem inBox_add_int_single (hm : 2 * (R + 1) + 1 < m) {x : Torus d m} (hx : InBox d R m x)
    (μ : Fin d) {z : ℤ} (hz : |z| ≤ 1) :
    InBox d (R + 1) m (x + (((z : ℤ) : ZMod m)) • (Pi.single μ 1 : Torus d m)) := by
  intro ν
  by_cases hν : ν = μ
  · subst hν
    have h : (x + (((z : ℤ) : ZMod m)) • (Pi.single ν 1 : Torus d m)) ν = x ν + (z : ZMod m) := by
      simp
    rw [h, valMinAbs_add_int_of_abs_le hm (x ν) (hx ν) hz]
    have := hx ν
    rw [abs_le] at this hz ⊢
    constructor <;> omega
  · have h : (x + (((z : ℤ) : ZMod m)) • (Pi.single μ 1 : Torus d m)) ν = x ν := by
      simp [Pi.single_eq_of_ne hν]
    rw [h]
    exact (hx ν).trans (by omega)

theorem inBox_add_single (hm : 2 * (R + 1) + 1 < m) {x : Torus d m} (hx : InBox d R m x)
    (μ : Fin d) : InBox d (R + 1) m (x + (Pi.single μ 1 : Torus d m)) := by
  have := inBox_add_int_single hm hx μ (z := 1) (by simp)
  simpa using this

theorem inBox_sub_single (hm : 2 * (R + 1) + 1 < m) {x : Torus d m} (hx : InBox d R m x)
    (μ : Fin d) : InBox d (R + 1) m (x + -(Pi.single μ 1 : Torus d m)) := by
  have := inBox_add_int_single hm hx μ (z := -1) (by simp)
  simpa [sub_eq_add_neg] using this

end Nbhd

section Lift

open Balaban.LargeField.KF0Gas Balaban.LargeField.KF0AllPlus

variable {d N n s m m2 R₀ : ℕ} [NeZero s] [NeZero m] [NeZero m2] {h : EuclideanSpace ℝ (Fin N)}
  {Y : Finset (Torus d m)} {σ : Torus d m → Torus d m2}
  (hm : 2 * (R₀ + 1) + 1 < s * m) (hm2 : 2 * (R₀ + 1) + 1 < s * m2)
  (hY : ∀ y ∈ siteSet d s m Y, InBox d R₀ (s * m) y) (hσ : Set.InjOn σ (Y : Set (Torus d m)))
  (hrel : ∀ y ∈ siteSet d s m Y,
    blockOf d s m2 (boxMap (s * m) (s * m2) y) = σ (blockOf d s m y))

include hY in
theorem inBox_succ_of_mem {y : Torus d (s * m)} (hy : y ∈ siteSet d s m Y) :
    InBox d (R₀ + 1) (s * m) y := fun μ => (hY y hy μ).trans (by omega)

include hm hm2 hY hσ hrel in
/-- **The site pieces of `H_X` on two tori.** -/
theorem siteSum_lift (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (src : Torus d (s * m) → Fin N → ℝ) (src' : Torus d (s * m2) → Fin N → ℝ)
    (hsrc : ∀ y ∈ siteSet d s m Y, src' (boxMap (s * m) (s * m2) y) = src y)
    {Z : Finset (Torus d m)} (hZ : Z ⊆ Y) (Φ : ∀ b, BlockSpace d s m (perp h) b)
    (Φ' : ∀ b, BlockSpace d s m2 (perp h) b)
    (hΦ : ∀ y ∈ siteSet d s m Y, toSites Φ' (boxMap (s * m) (s * m2) y) = toSites Φ y) :
    ∑ x' : Torus d (s * m2), ∑ H' ∈ haloFibre d s m2 (Z.image σ),
        f1SiteHaloClip e β ν src' x' H' p (toSites Φ') =
      ∑ x : Torus d (s * m), ∑ H ∈ haloFibre d s m Z,
        f1SiteHaloClip e β ν src x H p (toSites Φ) := by
  have hR : 2 * R₀ + 1 < s * m := by omega
  have hR2 : 2 * R₀ + 1 < s * m2 := by omega
  have hsZ : ∀ x ∈ siteSet d s m Z, x ∈ siteSet d s m Y := fun x hx => by
    rw [mem_siteSet] at hx ⊢; exact hZ hx
  have hSS := siteSet_image_boxMap hR2 hY hσ hrel hZ
  have hFF := haloFibre_image_boxMap hR2 hY hσ hrel hZ
  have hfibsub : ∀ H ∈ haloFibre d s m Z, H ⊆ siteSet d s m Z := fun H hH x hx => by
    rw [mem_siteSet, ← mem_haloFibre.1 hH]; exact Finset.mem_image_of_mem _ hx
  have hinjS : Set.InjOn (boxMap (s * m) (s * m2)) (siteSet d s m Y : Set (Torus d (s * m))) :=
    boxMap_injOn_box (R := R₀ + 1) hm2 (S := siteSet d s m Y)
      fun y hy => inBox_succ_of_mem hY hy
  refine sum_sum_lift (boxMap (s * m) (s * m2)) (siteSet d s m Z) (siteSet d s m2 (Z.image σ))
    (haloFibre d s m Z) (haloFibre d s m2 (Z.image σ))
    (fun H => H.image (boxMap (s * m) (s * m2)))
    (fun x H => f1SiteHaloClip e β ν src x H p (toSites Φ))
    (fun x' H' => f1SiteHaloClip e β ν src' x' H' p (toSites Φ')) hSS
    (hinjS.mono (fun x hx => hsZ x hx)) hFF ?_ ?_ ?_ ?_
  · intro H₁ hH₁ H₂ hH₂ h12
    exact TwoTorusStep.eq_of_image_eq_of_injOn (S := siteSet d s m Y) hinjS
      (fun x hx => hsZ x (hfibsub H₁ hH₁ hx)) (fun x hx => hsZ x (hfibsub H₂ hH₂ hx)) h12
  · intro x hx H hH
    unfold f1SiteHaloClip
    refine f1SiteHalo_eq_zero e β ν src x H ?_ _
    rintro ⟨-, hxH⟩
    exact hx (hfibsub H hH hxH)
  · intro x' hx' H' hH'
    unfold f1SiteHaloClip
    refine f1SiteHalo_eq_zero e β ν src' x' H' ?_ _
    rintro ⟨-, hxH⟩
    apply hx'
    rw [mem_siteSet, ← mem_haloFibre.1 hH']
    exact Finset.mem_image_of_mem _ hxH
  · intro x hx H hH
    unfold f1SiteHaloClip
    have hxY := hsZ x hx
    refine f1SiteHalo_boxMap (R := R₀ + 1) hm hm2 e β ν src src' x
      (inBox_succ_of_mem hY hxY) (hsrc x hxY) H
      (fun y hy => inBox_succ_of_mem hY (hsZ y (hfibsub H hH hy))) _ _ ?_
    intro y hy
    simp only [clipField, hΦ y (hsZ y (hfibsub H hH hy))]

include hm hm2 hY hσ hrel in
/-- **The bond pieces of `H_X` on two tori.** -/
theorem bondSum_lift (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    {Z : Finset (Torus d m)} (hZ : Z ⊆ Y) (Φ : ∀ b, BlockSpace d s m (perp h) b)
    (Φ' : ∀ b, BlockSpace d s m2 (perp h) b)
    (hΦ : ∀ y ∈ siteSet d s m Y, toSites Φ' (boxMap (s * m) (s * m2) y) = toSites Φ y) :
    ∑ x' : Torus d (s * m2), ∑ μ : Fin d, ∑ H' ∈ haloFibre d s m2 (Z.image σ),
        f1BondHaloClip e β ν x' μ H' p (toSites Φ') =
      ∑ x : Torus d (s * m), ∑ μ : Fin d, ∑ H ∈ haloFibre d s m Z,
        f1BondHaloClip e β ν x μ H p (toSites Φ) := by
  have hR : 2 * R₀ + 1 < s * m := by omega
  have hR2 : 2 * R₀ + 1 < s * m2 := by omega
  have hsZ : ∀ x ∈ siteSet d s m Z, x ∈ siteSet d s m Y := fun x hx => by
    rw [mem_siteSet] at hx ⊢; exact hZ hx
  have hSS := siteSet_image_boxMap hR2 hY hσ hrel hZ
  have hFF := haloFibre_image_boxMap hR2 hY hσ hrel hZ
  have hfibsub : ∀ H ∈ haloFibre d s m Z, H ⊆ siteSet d s m Z := fun H hH x hx => by
    rw [mem_siteSet, ← mem_haloFibre.1 hH]; exact Finset.mem_image_of_mem _ hx
  have hbox1 : ∀ y ∈ siteSet d s m Y, InBox d (R₀ + 1) (s * m) y := fun y hy =>
    inBox_succ_of_mem hY hy
  have hinjS : Set.InjOn (boxMap (s * m) (s * m2)) (siteSet d s m Y : Set (Torus d (s * m))) :=
    boxMap_injOn_box (R := R₀ + 1) hm2 (S := siteSet d s m Y) hbox1
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Torus d (s * m))))]
  refine Finset.sum_congr rfl fun μ _ => ?_
  -- the anchors of the bond in direction `μ`
  set S : Finset (Torus d (s * m)) := Finset.univ.filter (fun x =>
    x ∈ siteSet d s m Z ∨ x + Pi.single μ 1 ∈ siteSet d s m Z) with hS
  set S' : Finset (Torus d (s * m2)) := Finset.univ.filter (fun x' =>
    x' ∈ siteSet d s m2 (Z.image σ) ∨ x' + Pi.single μ 1 ∈ siteSet d s m2 (Z.image σ)) with hS'
  have hSbox : ∀ x ∈ S, InBox d (R₀ + 1) (s * m) x ∧
      InBox d (R₀ + 1) (s * m) (x + Pi.single μ 1) := by
    intro x hx
    rcases (Finset.mem_filter.1 hx).2 with h1 | h1
    · exact ⟨hbox1 x (hsZ x h1), inBox_add_single hm (hY x (hsZ x h1)) μ⟩
    · have h2 := hY _ (hsZ _ h1)
      have h3 := inBox_sub_single hm h2 μ
      have : x + Pi.single μ 1 + -Pi.single μ 1 = x := by abel
      rw [this] at h3
      exact ⟨h3, hbox1 _ (hsZ _ h1)⟩
  have hSinj : Set.InjOn (boxMap (s * m) (s * m2)) (S : Set (Torus d (s * m))) :=
    boxMap_injOn_box (R := R₀ + 1) hm2 (S := S) fun x hx => (hSbox x hx).1
  have hSimg : S' = S.image (boxMap (s * m) (s * m2)) := by
    ext x'
    rw [Finset.mem_image]
    constructor
    · intro hx'
      rcases (Finset.mem_filter.1 hx').2 with h1 | h1
      · rw [hSS] at h1
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h1
        exact ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl hx⟩, rfl⟩
      · rw [hSS] at h1
        obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 h1
        refine ⟨y + -Pi.single μ 1, Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr (by
          have : y + -Pi.single μ 1 + Pi.single μ 1 = y := by abel
          rw [this]; exact hy)⟩, ?_⟩
        have hyb := hY y (hsZ y hy)
        have hxb : InBox d (R₀ + 1) (s * m) (y + -Pi.single μ 1) := inBox_sub_single hm hyb μ
        have hstep := (boxMap_step_iff (R := R₀ + 1) hm hm2 hxb (hbox1 y (hsZ y hy)) μ).1 (by abel)
        have hyx' : boxMap (s * m) (s * m2) y = x' + Pi.single μ 1 := hyx
        exact (add_right_cancel (hyx'.symm.trans hstep)).symm
    · rintro ⟨x, hx, rfl⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rcases (Finset.mem_filter.1 hx).2 with h1 | h1
      · left
        rw [hSS]; exact Finset.mem_image_of_mem _ h1
      · right
        rw [hSS]
        have hstep := (boxMap_step_iff (R := R₀ + 1) hm hm2 (hSbox x hx).1 (hSbox x hx).2 μ).1 rfl
        rw [← hstep]
        exact Finset.mem_image_of_mem _ h1
  refine sum_sum_lift (boxMap (s * m) (s * m2)) S S' (haloFibre d s m Z)
    (haloFibre d s m2 (Z.image σ)) (fun H => H.image (boxMap (s * m) (s * m2)))
    (fun x H => f1BondHaloClip e β ν x μ H p (toSites Φ))
    (fun x' H' => f1BondHaloClip e β ν x' μ H' p (toSites Φ')) hSimg hSinj hFF ?_ ?_ ?_ ?_
  · intro H₁ hH₁ H₂ hH₂ h12
    exact TwoTorusStep.eq_of_image_eq_of_injOn (S := siteSet d s m Y) hinjS
      (fun x hx => hsZ x (hfibsub H₁ hH₁ hx)) (fun x hx => hsZ x (hfibsub H₂ hH₂ hx)) h12
  · intro x hx H hH
    unfold f1BondHaloClip
    refine f1BondHalo_eq_zero e β ν x μ H ?_ _
    rintro ⟨-, hxH⟩
    apply hx
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hxH with h1 | h1
    · right; exact hfibsub H hH h1
    · left; exact hfibsub H hH h1
  · intro x' hx' H' hH'
    unfold f1BondHaloClip
    refine f1BondHalo_eq_zero e β ν x' μ H' ?_ _
    rintro ⟨-, hxH⟩
    apply hx'
    rw [hS', Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hb : ∀ y ∈ H', y ∈ siteSet d s m2 (Z.image σ) := fun y hy => by
      rw [mem_siteSet, ← mem_haloFibre.1 hH']; exact Finset.mem_image_of_mem _ hy
    rcases hxH with h1 | h1
    · right; exact hb _ h1
    · left; exact hb _ h1
  · intro x hx H hH
    unfold f1BondHaloClip
    refine f1BondHalo_boxMap (R := R₀ + 1) hm hm2 e β ν x μ (hSbox x hx).1 (hSbox x hx).2 H
      (fun y hy => hbox1 y (hsZ y (hfibsub H hH hy))) _ _ ?_
    intro y hy
    simp only [clipField, hΦ y (hsZ y (hfibsub H hH hy))]

include hm hm2 hY hσ hrel in
/-- **The source coefficient of `H_X` on two tori.** -/
theorem blockSrc_lift (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    {Z : Finset (Torus d m)} (hZ : Z ⊆ Y) {x : Torus d (s * m)} (hx : x ∈ siteSet d s m Z)
    (i : Fin N) (Φ : ∀ b, BlockSpace d s m (perp h) b) (Φ' : ∀ b, BlockSpace d s m2 (perp h) b)
    (hΦ : ∀ y ∈ siteSet d s m Y, toSites Φ' (boxMap (s * m) (s * m2) y) = toSites Φ y) :
    blockSrc e β ν p (boxMap (s * m) (s * m2) x) i (Z.image σ) Φ' = blockSrc e β ν p x i Z Φ := by
  have hR : 2 * R₀ + 1 < s * m := by omega
  have hR2 : 2 * R₀ + 1 < s * m2 := by omega
  have hsZ : ∀ x ∈ siteSet d s m Z, x ∈ siteSet d s m Y := fun x hx => by
    rw [mem_siteSet] at hx ⊢; exact hZ hx
  have hFF := haloFibre_image_boxMap hR2 hY hσ hrel hZ
  have hfibsub : ∀ H ∈ haloFibre d s m Z, H ⊆ siteSet d s m Z := fun H hH x hx => by
    rw [mem_siteSet, ← mem_haloFibre.1 hH]; exact Finset.mem_image_of_mem _ hx
  have hinjS : Set.InjOn (boxMap (s * m) (s * m2)) (siteSet d s m Y : Set (Torus d (s * m))) :=
    boxMap_injOn_box (R := R₀ + 1) hm2 (S := siteSet d s m Y)
      fun y hy => inBox_succ_of_mem hY hy
  unfold blockSrc
  rw [hFF, Finset.sum_image fun H₁ hH₁ H₂ hH₂ h12 =>
    TwoTorusStep.eq_of_image_eq_of_injOn (S := siteSet d s m Y) hinjS
      (fun x hx => hsZ x (hfibsub H₁ hH₁ hx)) (fun x hx => hsZ x (hfibsub H₂ hH₂ hx)) h12]
  refine Finset.sum_congr rfl fun H hH => ?_
  unfold f1SiteSrcHaloClip
  refine f1SiteSrcHalo_boxMap (R := R₀ + 1) hm hm2 e β ν x (inBox_succ_of_mem hY (hsZ x hx)) i H
    (fun y hy => inBox_succ_of_mem hY (hsZ y (hfibsub H hH hy))) _ _ ?_
  intro y hy
  simp only [clipField, hΦ y (hsZ y (hfibsub H hH hy))]

include hm hm2 hY hσ hrel in
/-- **The regrouped block activity at a complex source on two tori.** -/
theorem gasTermC_lift (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (g : Torus d (s * m) → Fin N → ℂ) (g' : Torus d (s * m2) → Fin N → ℂ)
    (hg : ∀ y ∈ siteSet d s m Y, g' (boxMap (s * m) (s * m2) y) = g y)
    {Z : NePoly (Torus d m)} (hZ : Z.1 ⊆ Y) (Φ : ∀ b, BlockSpace d s m (perp h) b)
    (Φ' : ∀ b, BlockSpace d s m2 (perp h) b)
    (hΦ : ∀ y ∈ siteSet d s m Y, toSites Φ' (boxMap (s * m) (s * m2) y) = toSites Φ y) :
    gasTermC e β ν p ⟨Z.1.image σ, Z.2.image σ⟩ g' Φ' = gasTermC e β ν p Z g Φ := by
  have hR : 2 * R₀ + 1 < s * m := by omega
  have hR2 : 2 * R₀ + 1 < s * m2 := by omega
  have hsZ : ∀ x ∈ siteSet d s m Z.1, x ∈ siteSet d s m Y := fun x hx => by
    rw [mem_siteSet] at hx ⊢; exact hZ hx
  have hSS := siteSet_image_boxMap hR2 hY hσ hrel hZ
  have hinjS : Set.InjOn (boxMap (s * m) (s * m2)) (siteSet d s m Y : Set (Torus d (s * m))) :=
    boxMap_injOn_box (R := R₀ + 1) hm2 (S := siteSet d s m Y)
      fun y hy => inBox_succ_of_mem hY hy
  unfold gasTermC
  congr 1
  · congr 1
    unfold Balaban.LargeField.KF0AllPlus.blockActivity
    rw [siteSum_lift hm hm2 hY hσ hrel e β ν p (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => rfl) hZ Φ Φ' hΦ,
      bondSum_lift hm hm2 hY hσ hrel e β ν p hZ Φ Φ' hΦ]
  · have hvan : ∀ x, x ∉ siteSet d s m Z.1 → ∀ i : Fin N,
        g x i * ((blockSrc e β ν p x i Z.1 Φ : ℝ) : ℂ) = 0 := fun x hx i => by
      rw [blockSrc_eq_zero_of_not_mem e β ν p x i Z.1 (by rwa [mem_siteSet] at hx) Φ]; simp
    have hvan' : ∀ x', x' ∉ siteSet d s m2 (Z.1.image σ) → ∀ i : Fin N,
        g' x' i * ((blockSrc e β ν p x' i (Z.1.image σ) Φ' : ℝ) : ℂ) = 0 := fun x' hx' i => by
      rw [blockSrc_eq_zero_of_not_mem e β ν p x' i _ (by rwa [mem_siteSet] at hx') Φ']; simp
    have h1 : ∑ x' : Torus d (s * m2), ∑ i : Fin N,
        g' x' i * ((blockSrc e β ν p x' i (Z.1.image σ) Φ' : ℝ) : ℂ) =
        ∑ x' ∈ siteSet d s m2 (Z.1.image σ), ∑ i : Fin N,
          g' x' i * ((blockSrc e β ν p x' i (Z.1.image σ) Φ' : ℝ) : ℂ) :=
      (Finset.sum_subset (Finset.subset_univ _) fun x' _ hx' =>
        Finset.sum_eq_zero fun i _ => hvan' x' hx' i).symm
    have h2 : ∑ x : Torus d (s * m), ∑ i : Fin N,
        g x i * ((blockSrc e β ν p x i Z.1 Φ : ℝ) : ℂ) =
        ∑ x ∈ siteSet d s m Z.1, ∑ i : Fin N,
          g x i * ((blockSrc e β ν p x i Z.1 Φ : ℝ) : ℂ) :=
      (Finset.sum_subset (Finset.subset_univ _) fun x _ hx =>
        Finset.sum_eq_zero fun i _ => hvan x hx i).symm
    rw [h1, h2, hSS, Finset.sum_image (hinjS.mono fun x hx => hsZ x hx)]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
    rw [hg x (hsZ x hx), blockSrc_lift hm hm2 hY hσ hrel e β ν p hZ hx i Φ Φ' hΦ]

end Lift

section PYLift

open Balaban.LargeField.KF0Gas Balaban.LargeField.KF0AllPlus MeasureTheory

variable {d N n s m m2 R₀ : ℕ} [NeZero s] [NeZero m] [NeZero m2] {h : EuclideanSpace ℝ (Fin N)}

/-- The block configuration of a site configuration. -/
def fromSites {W : Type*} (ψ : Torus d (s * m) → W) : ∀ b, BlockSpace d s m W b :=
  fun _ x => ψ x.1

omit [NeZero s] [NeZero m] in
theorem toSites_fromSites {W : Type*} (ψ : Torus d (s * m) → W) : toSites (fromSites ψ) = ψ := rfl

omit [NeZero s] [NeZero m] in
theorem fromSites_toSites {W : Type*} (Φ : ∀ b, BlockSpace d s m W b) :
    fromSites (toSites Φ) = Φ := by
  funext b x
  obtain ⟨y, rfl⟩ := x
  rfl

omit [NeZero s] [NeZero m] in
theorem measurable_fromSites {W : Type*} [MeasurableSpace W] :
    Measurable (fromSites (d := d) (s := s) (m := m) (W := W)) :=
  measurable_pi_iff.2 fun _ => measurable_pi_iff.2 fun x => measurable_pi_apply x.1

/-- The measurable identification of block configurations with site configurations. -/
def siteEquiv (W : Type*) [MeasurableSpace W] :
    (∀ b, BlockSpace d s m W b) ≃ᵐ (Torus d (s * m) → W) where
  toFun := toSites
  invFun := fromSites
  left_inv := fromSites_toSites
  right_inv := toSites_fromSites
  measurable_toFun := measurable_toSites
  measurable_invFun := measurable_fromSites

/-- **Integrals of local functions of the blocks on two tori** (the hypothesis `hint` of
`PY_mayer_transport`): for the product block measures of a probability measure `pc`, a function of
the blocks of `Z ⊆ Y` has the same integral as a function of the second system equal to it on
configurations related through `boxMap`. -/
theorem integral_blockRef_lift {W : Type*} [MeasurableSpace W] (pc : Measure W)
    [IsProbabilityMeasure pc] {R : ℕ} (hm2 : 2 * R + 1 < s * m2) {Y : Finset (Torus d m)}
    (hY : ∀ y ∈ siteSet d s m Y, InBox d R (s * m) y) {Z : Finset (Torus d m)} (hZ : Z ⊆ Y)
    (F : (∀ b, BlockSpace d s m W b) → ℂ) (F' : (∀ b, BlockSpace d s m2 W b) → ℂ)
    (hF : DepOn Z F)
    (hFF : ∀ Φ Φ', (∀ y ∈ siteSet d s m Y, toSites Φ' (boxMap (s * m) (s * m2) y) = toSites Φ y) →
      F' Φ' = F Φ) :
    ∫ Φ', F' Φ' ∂(Measure.pi (blockRef (d := d) (s := s) (m' := m2) pc)) =
      ∫ Φ, F Φ ∂(Measure.pi (blockRef (d := d) (s := s) (m' := m) pc)) := by
  have hmap : ∀ {m₁ : ℕ} [NeZero m₁] (G : (∀ b, BlockSpace d s m₁ W b) → ℂ),
      ∫ Φ, G Φ ∂(Measure.pi (blockRef (d := d) (s := s) (m' := m₁) pc)) =
        ∫ ψ, G (fromSites ψ) ∂(Measure.pi fun _ : Torus d (s * m₁) => pc) := by
    intro m₁ _ G
    have hmp : MeasurePreserving (siteEquiv (d := d) (s := s) (m := m₁) W)
        (Measure.pi (blockRef (d := d) (s := s) (m' := m₁) pc))
        (Measure.pi fun _ : Torus d (s * m₁) => pc) :=
      ⟨(siteEquiv W).measurable, map_toSites_pi pc⟩
    rw [← hmp.integral_comp' (g := fun ψ => G (fromSites ψ))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
    show G Φ = G (fromSites (toSites Φ))
    rw [fromSites_toSites]
  rw [hmap F', hmap F]
  have h1 : ∀ ψ' : Torus d (s * m2) → W,
      F' (fromSites ψ') = F (fromSites (fun y => ψ' (boxMap (s * m) (s * m2) y))) :=
    fun ψ' => hFF _ _ (fun y hy => rfl)
  simp_rw [h1]
  have hinj : Set.InjOn (boxMap (s * m) (s * m2)) (siteSet d s m Z : Set (Torus d (s * m))) :=
    boxMap_injOn_box hm2 (S := siteSet d s m Z) fun y hy => hY y (by
      rw [mem_siteSet] at hy ⊢; exact hZ hy)
  refine TwoTorusStep.integral_pi_comp_of_injOn pc (boxMap (s * m) (s * m2)) (siteSet d s m Z)
    hinj (f := fun ψ => F (fromSites ψ)) ?_
  intro ψ₁ ψ₂ hψ
  refine hF _ _ fun b hb => ?_
  funext x
  exact hψ x.1 (by rw [mem_siteSet, x.2]; exact hb)

end PYLift

section PYLift2

open Balaban.LargeField.KF0Gas Balaban.LargeField.KF0AllPlus MeasureTheory

variable {d N n s m m2 R₀ : ℕ} [NeZero s] [NeZero m] [NeZero m2] {h : EuclideanSpace ℝ (Fin N)}
  {Y : Finset (Torus d m)} {σ : Torus d m → Torus d m2}
  (hm : 2 * (R₀ + 1) + 1 < s * m) (hm2 : 2 * (R₀ + 1) + 1 < s * m2)
  (hY : ∀ y ∈ siteSet d s m Y, InBox d R₀ (s * m) y) (hσ : Set.InjOn σ (Y : Set (Torus d m)))
  (hrel : ∀ y ∈ siteSet d s m Y,
    blockOf d s m2 (boxMap (s * m) (s * m2) y) = σ (blockOf d s m y))

include hm hm2 hY hσ hrel in
/-- **The local terms of the all-plus gas on two tori.**  For a set `Y` of blocks whose sites lie in
a box that does not wrap around either torus, a map of blocks `σ` injective on `Y` and compatible
with `boxMap` on the sites, and sources `g`, `g'` agreeing through `boxMap`: `P'(σ '' Y)(g') = P(Y)(g)`. -/
theorem kf0PY_lift (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (pc : Measure (perp h)) [IsProbabilityMeasure pc]
    (g : Torus d (s * m) → Fin N → ℂ) (g' : Torus d (s * m2) → Fin N → ℂ)
    (hg : ∀ y ∈ siteSet d s m Y, g' (boxMap (s * m) (s * m2) y) = g y) :
    kf0PY e β ν p pc (Y.image σ) g' = kf0PY e β ν p pc Y g := by
  unfold kf0PY
  refine PY_mayer_transport (blockRef (d := d) (s := s) (m' := m) pc)
    (blockRef (d := d) (s := s) (m' := m2) pc) σ Y hσ
    (fun X => gasTermC e β ν p X g) (fun X => gasTermC e β ν p X g')
    (fun Φ Φ' => ∀ y ∈ siteSet d s m Y,
      toSites Φ' (boxMap (s * m) (s * m2) y) = toSites Φ y) ?_ ?_ ?_
  · intro Z hZ F F' hF hFF
    exact integral_blockRef_lift pc (R := R₀) (by omega) hY hZ F F' hF hFF
  · intro t
    exact depOn_gasTermC e β ν p t g
  · intro t ht Φ Φ' hR
    exact gasTermC_lift hm hm2 hY hσ hrel e β ν p g g' hg ht Φ Φ' hR

end PYLift2

end Balaban.KF0Lift
