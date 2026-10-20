/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRLift
public import Balaban.LargeField.Base.KF0FRPE
public import Balaban.Polymer.MayerTransport
import Mathlib.Tactic.Linarith

/-!
# `KF0FRLiftPY`: the local terms of route FR on two tori (route FR, (T))

`notes/phase1/KF0-FR.md` (T). For a set `Y` of blocks whose sites lie in the box `InBox R₀` and a
map of blocks `σ` compatible with `boxMap`, injective on `Y`:

* `frFX_lift`: the grouped weight of `X ⊆ Y` equals the grouped weight of `σ '' X` on configurations
  related through `boxMap` (the terms of the two block supports correspond by `frTau`);
* `frPY_lift`: the local terms of `Y` and `σ '' Y` agree (`PY_mayerGen_transport`);
* `three_le_of_polymer`, `frPY_agree`: for a polymer in the quarter box of two tori (at least three
  blocks per side), the local terms agree at the same source.
-/

@[expose] public section

open MeasureTheory Finset Balaban.Green Balaban.Polymer Balaban.LargeField.KF0Gas Balaban.KF0Lift

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N))

variable {d s m m2 : ℕ} [NeZero s] [NeZero m] [NeZero m2]

/-- The inverse of `frTau` on the image side. -/
def frTauInv (n : ℕ) {n' : ℕ} : FRTerm d n' → FRTerm d n := frTau n


omit [NeZero s] [NeZero m] [NeZero m2] in
theorem frTau_frTauInv_of {n n' : ℕ} [NeZero n] [NeZero n'] {t' : FRTerm d n'}
    (hb : boxMap n n' (boxMap n' n (frBase t')) = frBase t') :
    frTau n' (frTauInv n t') = t' := by
  rcases t' with x | ⟨x, μ⟩
  · simp only [frTauInv, frTau, frBase] at hb ⊢; rw [hb]
  · simp only [frTauInv, frTau, frBase] at hb ⊢; rw [hb]

theorem frTauInv_frTau_of {n n' : ℕ} [NeZero n] [NeZero n'] {t : FRTerm d n}
    (hb : boxMap n' n (boxMap n n' (frBase t)) = frBase t) :
    frTauInv n (frTau n' t) = t := by
  rcases t with x | ⟨x, μ⟩
  · simp only [frTauInv, frTau, frBase] at hb ⊢; rw [hb]
  · simp only [frTauInv, frTau, frBase] at hb ⊢; rw [hb]

theorem frBase_frTauInv {n n' : ℕ} [NeZero n] [NeZero n'] (t' : FRTerm d n') :
    frBase (frTauInv n t') = boxMap n' n (frBase t') := frBase_frTau t'

omit [NeZero s] [NeZero m] [NeZero m2] in
/-- Images of subsets of `Y` under a map injective on `Y` determine the subsets. -/
theorem eq_of_image_eq_of_injOn' {α β : Type*} [DecidableEq β] {σ : α → β} {Y A B : Finset α}
    (hσ : Set.InjOn σ (Y : Set α)) (hA : A ⊆ Y) (hB : B ⊆ Y) (h : A.image σ = B.image σ) :
    A = B := by
  ext b
  constructor
  · intro hb
    obtain ⟨b', hb', he⟩ := Finset.mem_image.1 (h ▸ Finset.mem_image_of_mem σ hb)
    rw [← hσ (hB hb') (hA hb) he]; exact hb'
  · intro hb
    obtain ⟨b', hb', he⟩ := Finset.mem_image.1 (h.symm ▸ Finset.mem_image_of_mem σ hb)
    rw [← hσ (hA hb') (hB hb) he]; exact hb'

section Weights

variable {R R₀ : ℕ} (hm : 2 * (R₀ + 2 * R + 2) + 1 < s * m)
  (hm2 : 2 * (R₀ + 2 * R + 2) + 1 < s * m2) {Y : Finset (Torus d m)}
  (hY : ∀ y ∈ siteSet d s m Y, InBox d R₀ (s * m) y) {σ : Torus d m → Torus d m2}
  (hσ : Set.InjOn σ (Y : Set (Torus d m)))
  (hrel : ∀ y ∈ siteSet d s m Y,
    blockOf d s m2 (boxMap (s * m) (s * m2) y) = σ (blockOf d s m y))

include hm hm2 hY hrel in
/-- The block support of the transported term. -/
theorem frBox_frTau {t : FRTerm d (s * m)} (ht : frBox R t ⊆ Y) :
    frBox R (frTau (s * m2) t) = (frBox R t).image σ := by
  have hsub : frSupp R t ⊆ siteSet d s m Y := fun y hy => by
    rw [mem_siteSet]; exact ht (blockOf_mem_frBox hy)
  have hbase : InBox d R₀ (s * m) (frBase t) := hY _ (hsub (frBase_mem_frSupp R t))
  unfold frBox
  rw [frSupp_frTau hm hm2 hbase, Finset.image_image, Finset.image_image]
  exact Finset.image_congr fun y hy => hrel y (hsub hy)

include hm hm2 hY hσ hrel in
/-- **The grouped weights on two tori.** -/
theorem frFX_lift (hh : ‖h‖ = 1) (β ν ε : ℝ) (g : Torus d (s * m) → Fin N → ℂ)
    (g' : Torus d (s * m2) → Fin N → ℂ)
    (hg : ∀ y ∈ siteSet d s m Y, g' (boxMap (s * m) (s * m2) y) = g y)
    (X : NePoly (Torus d m)) (hX : X.1 ⊆ Y) (Φ : ∀ b, BlockSpace d s m (perp h × Bool) b)
    (Φ' : ∀ b, BlockSpace d s m2 (perp h × Bool) b)
    (hR : ∀ y ∈ siteSet d s m Y, toSites Φ' (boxMap (s * m) (s * m2) y) = toSites Φ y) :
    frFX h hh β ν ε R g' ⟨X.1.image σ, X.2.image σ⟩ Φ' = frFX h hh β ν ε R g X Φ := by
  classical
  have e1 := one_add_frFX h hh β ν ε R g X Φ
  have e2 := one_add_frFX h hh β ν ε R g' ⟨X.1.image σ, X.2.image σ⟩ Φ'
  have hYbox : ∀ y ∈ siteSet d s m Y, InBox d (R₀ + 2 * R + 2) (s * m) y := fun y hy ν =>
    (hY y hy ν).trans (by omega)
  have hinjS : Set.InjOn (boxMap (s * m) (s * m2))
      ((Finset.univ.filter fun y : Torus d (s * m) => InBox d (R₀ + 2 * R + 2) (s * m) y :
        Finset (Torus d (s * m))) : Set (Torus d (s * m))) :=
    boxMap_injOn_inBox (R := R₀ + 2 * R + 2) (by omega) _ fun y hy => by
      simpa using hy
  have hXsites : siteSet d s m2 (X.1.image σ) =
      (siteSet d s m X.1).image (boxMap (s * m) (s * m2)) :=
    siteSet_image_boxMap (R := R₀) (by omega) hY hσ hrel hX
  -- the preimage of a term of `σ '' X`
  have hpre : ∀ t' : FRTerm d (s * m2), frBox R t' = X.1.image σ →
      InBox d R₀ (s * m) (frBase (frTauInv (s * m) t')) ∧
        frTau (s * m2) (frTauInv (s * m) t') = t' := by
    intro t' ht'X
    have hb' : frBase t' ∈ siteSet d s m2 (X.1.image σ) := by
      rw [mem_siteSet, ← ht'X]; exact blockOf_mem_frBox (frBase_mem_frSupp R t')
    rw [hXsites] at hb'
    obtain ⟨x₀, hx₀, hx₀e⟩ := Finset.mem_image.1 hb'
    have hx₀B : InBox d R₀ (s * m) x₀ := hY x₀ (by rw [mem_siteSet] at hx₀ ⊢; exact hX hx₀)
    have hback : boxMap (s * m2) (s * m) (frBase t') = x₀ := by
      rw [← hx₀e]; exact boxMap_boxMap (by omega) hx₀B
    refine ⟨by rw [frBase_frTauInv, hback]; exact hx₀B, frTau_frTauInv_of ?_⟩
    rw [hback, hx₀e]
  -- the terms of the two block supports correspond
  have hprod : ∏ t ∈ Finset.univ.filter (fun t => frKey R t = ⟨X.1.image σ, X.2.image σ⟩),
      frF h hh β ν ε R g' t (toSites Φ') =
      ∏ t ∈ Finset.univ.filter (fun t => frKey R t = X), frF h hh β ν ε R g t (toSites Φ) := by
    symm
    refine Finset.prod_nbij' (frTau (s * m2)) (frTauInv (s * m)) ?_ ?_ ?_ ?_ ?_
    · -- `frTau` maps the terms of `X` to the terms of `σ '' X`
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      have htX : frBox R t = X.1 := congrArg Subtype.val ht
      apply Subtype.ext
      show frBox R (frTau (s * m2) t) = X.1.image σ
      rw [frBox_frTau hm hm2 hY hrel (htX ▸ hX), htX]
    · -- the preimage of a term of `σ '' X` is a term of `X`
      intro t' ht'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht' ⊢
      have ht'X : frBox R t' = X.1.image σ := congrArg Subtype.val ht'
      obtain ⟨hbase, hτ⟩ := hpre t' ht'X
      apply Subtype.ext
      show frBox R (frTauInv (s * m) t') = X.1
      set t := frTauInv (s * m) t'
      have hsuppX : frSupp R t ⊆ siteSet d s m X.1 := by
        intro y hy
        have hy' : boxMap (s * m) (s * m2) y ∈ frSupp R t' := by
          rw [← hτ, frSupp_frTau hm hm2 hbase]; exact Finset.mem_image_of_mem _ hy
        have : boxMap (s * m) (s * m2) y ∈ siteSet d s m2 (X.1.image σ) := by
          rw [mem_siteSet, ← ht'X]; exact blockOf_mem_frBox hy'
        rw [hXsites] at this
        obtain ⟨z, hz, hzy⟩ := Finset.mem_image.1 this
        have hyB : InBox d (R₀ + 2 * R + 2) (s * m) y := inBox_of_mem_frSupp hm hbase hy
        have hzB : InBox d (R₀ + 2 * R + 2) (s * m) z :=
          hYbox z (by rw [mem_siteSet] at hz ⊢; exact hX hz)
        rw [← hinjS (by simpa using hzB) (by simpa using hyB) hzy]
        exact hz
      have hboxX : frBox R t ⊆ X.1 := by
        intro b hb
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
        exact (mem_siteSet d s m).1 (hsuppX hy)
      have := frBox_frTau hm hm2 hY hrel (hboxX.trans hX)
      rw [hτ, ht'X] at this
      exact eq_of_image_eq_of_injOn' hσ (hboxX.trans hX) hX this.symm
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      have htX : frBox R t = X.1 := congrArg Subtype.val ht
      have hbase : InBox d R₀ (s * m) (frBase t) :=
        hY _ (by rw [mem_siteSet]; exact hX (htX ▸ blockOf_mem_frBox (frBase_mem_frSupp R t)))
      exact frTauInv_frTau_of (boxMap_boxMap (by omega) hbase)
    · intro t' ht'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht'
      exact (hpre t' (congrArg Subtype.val ht')).2
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      have htX : frBox R t = X.1 := congrArg Subtype.val ht
      have hsub : frSupp R t ⊆ siteSet d s m Y := fun y hy => by
        rw [mem_siteSet]; exact hX (htX ▸ blockOf_mem_frBox hy)
      have hbase : InBox d R₀ (s * m) (frBase t) := hY _ (hsub (frBase_mem_frSupp R t))
      exact (frF_frTau h hh hm hm2 hbase (fun y hy => hR y (hsub hy))
        (by rw [hg _ (hsub (frBase_mem_frSupp R t))])).symm
  rw [hprod, ← e1] at e2
  linear_combination e2

include hm hm2 hY hσ hrel in
/-- **The local terms of route FR on two tori.** -/
theorem frPY_lift (hh : ‖h‖ = 1) {β ν ε : ℝ} (hε : 0 ≤ ε) (g : Torus d (s * m) → Fin N → ℂ)
    (g' : Torus d (s * m2) → Fin N → ℂ)
    (hg : ∀ y ∈ siteSet d s m Y, g' (boxMap (s * m) (s * m2) y) = g y) :
    frPY h hh β ν ε R g' (Y.image σ) = frPY h hh β ν ε R g Y := by
  have hprob := isProbabilityMeasure_frSiteMeasure h hε
  unfold frPY frK
  refine PY_mayerGen_transport (blockRef (d := d) (s := s) (m' := m) (frSiteMeasure h ε))
    (blockRef (d := d) (s := s) (m' := m2) (frSiteMeasure h ε)) σ Y hσ
    (frFX h hh β ν ε R g) (frFX h hh β ν ε R g')
    (fun Φ Φ' => ∀ y ∈ siteSet d s m Y,
      toSites Φ' (boxMap (s * m) (s * m2) y) = toSites Φ y) ?_
    (depOn_frFX h hh β ν ε R g) ?_
  · intro Z hZ F F' hF hFF
    exact integral_blockRef_lift (frSiteMeasure h ε) (R := R₀) (by omega) hY hZ F F' hF hFF
  · intro X hX Φ Φ' hR
    exact frFX_lift h hm hm2 hY hσ hrel hh β ν ε g g' hg X hX Φ Φ' hR

end Weights

/-- **A polymer inside the quarter box needs at least three blocks per side.** -/
theorem three_le_of_polymer {s m : ℕ} [NeZero s] [NeZero m] (hs : 2 ≤ s) (hd : 1 ≤ d)
    (A : Finset (Fin d → ℤ)) (hA : ∀ y ∈ A, ∀ μ, 4 * |y μ| < ((s * m : ℕ) : ℤ))
    (hX : IsPolymer d (s * m) s (A.image (intToTorus d (s * m)))) : 3 ≤ m := by
  have h2 := two_le_of_polymer hs hd A hA hX
  by_contra hm
  have hm2 : m = 2 := by omega
  subst hm2
  obtain ⟨⟨x, hx⟩, hsat, -⟩ := hX
  set μ₀ : Fin d := ⟨0, hd⟩ with hμ₀
  set q := (x μ₀).val / s with hq
  have hqlt : q < 2 := by
    have := ZMod.val_lt (x μ₀)
    rw [hq, Nat.div_lt_iff_lt_mul (by omega)]; linarith
  set v : ℕ := if q = 0 then s - 1 else s with hv
  have hvlt : v < s * 2 := by rw [hv]; split_ifs <;> omega
  set x' : Torus d (s * 2) := fun ν => if ν = μ₀ then ((v : ℕ) : ZMod (s * 2)) else x ν with hx'
  have hval : ((v : ℕ) : ZMod (s * 2)).val = v := ZMod.val_cast_of_lt hvlt
  have hx'mem := hsat x hx x' (fun ν => by
    by_cases hν : ν = μ₀
    · rw [hν]
      have hxv : x' μ₀ = ((v : ℕ) : ZMod (s * 2)) := by rw [hx']; simp
      rw [hxv, hval, ← hq, hv]
      split_ifs with h0
      · rw [h0, Nat.div_eq_of_lt (by omega : s - 1 < s)]
      · have : q = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hqlt) (Nat.pos_of_ne_zero h0)
        rw [this, Nat.div_self (by omega : 0 < s)]
    · simp [hx', hν])
  obtain ⟨c, hcA, hc⟩ := Finset.mem_image.1 hx'mem
  have h1 : (((c μ₀ : ℤ) : ZMod (s * 2))) = (((v : ℕ) : ZMod (s * 2))) := by
    have := congrFun hc μ₀
    simpa [hx', intToTorus_apply] using this
  have h3 : (((c μ₀ - (v : ℤ) : ℤ)) : ZMod (s * 2)) = 0 := by
    rw [Int.cast_sub, Int.cast_natCast, h1, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3
  have h4 := hA c hcA μ₀
  have e1 := le_abs_self (c μ₀)
  have e2 := neg_abs_le (c μ₀)
  have hvle : (v : ℤ) ≤ s := by rw [hv]; split_ifs <;> omega
  have h5 : |c μ₀ - (v : ℤ)| < ((s * 2 : ℕ) : ℤ) := by
    rw [abs_lt]
    generalize |c μ₀| = a at *
    push_cast at h4 ⊢
    constructor <;> omega
  have h6 := Int.eq_zero_of_abs_lt_dvd h3 h5
  have hc' : c μ₀ = v := by omega
  rw [hc'] at h4
  have : (s - 1 : ℤ) ≤ (v : ℤ) := by rw [hv]; split_ifs <;> omega
  push_cast at h4
  rw [abs_of_nonneg (by omega)] at h4
  omega

/-- **The two-torus agreement of the local terms of route FR.** -/
theorem frPY_agree (hh : ‖h‖ = 1) {β ν ε : ℝ} (hε : 0 ≤ ε) {R : ℕ} (hR : 4 * R + 3 ≤ s)
    (hs : 6 ≤ s) (hd : 1 ≤ d) (A : Finset (Fin d → ℤ))
    (hA : ∀ y ∈ A, ∀ μ, 4 * |y μ| < ((s * m : ℕ) : ℤ) ∧ 4 * |y μ| < ((s * m2 : ℕ) : ℤ))
    (hX : IsPolymer d (s * m) s (A.image (intToTorus d (s * m))))
    (g : (Fin d → ℤ) → Fin N → ℂ) :
    frPY h hh β ν ε R (fun z => g fun μ => ZMod.valMinAbs (n := s * m2) (z μ))
        ((A.image (intToTorus d (s * m2))).image (blockOf d s m2)) =
      frPY h hh β ν ε R (fun z => g fun μ => ZMod.valMinAbs (n := s * m) (z μ))
        ((A.image (intToTorus d (s * m))).image (blockOf d s m)) := by
  obtain ⟨hpoly', -, σ, -, -, -, -, hinj, hrel, himage⟩ := polymer_lift hs hd A hA hX
  have hm3 := three_le_of_polymer (by omega) hd A (fun y hy μ => (hA y hy μ).1) hX
  have hm3' := three_le_of_polymer (by omega) hd A (fun y hy μ => (hA y hy μ).2) hpoly'
  rw [← himage]
  set X : Finset (Torus d (s * m)) := A.image (intToTorus d (s * m)) with hXdef
  set R₀ : ℕ := (min (s * m) (s * m2) - 1) / 4 with hR₀
  have hsm : 3 * s ≤ s * m := by nlinarith
  have hsm2 : 3 * s ≤ s * m2 := by nlinarith
  have hmarg1 : 2 * (R₀ + 2 * R + 2) + 1 < s * m := by omega
  have hmarg2 : 2 * (R₀ + 2 * R + 2) + 1 < s * m2 := by omega
  have hc : ∀ c ∈ A, ∀ μ, |c μ| ≤ R₀ := by
    intro c hcA μ
    have h1 := (hA c hcA μ).1
    have h2 := (hA c hcA μ).2
    have e1 := le_abs_self (c μ)
    have e2 := neg_abs_le (c μ)
    generalize |c μ| = a at *
    push_cast at h1 h2
    omega
  have hsiteY : siteSet d s m (X.image (blockOf d s m)) = X := siteSet_image_blockOf hX.2.1
  have hY : ∀ y ∈ siteSet d s m (X.image (blockOf d s m)), InBox d R₀ (s * m) y := by
    rw [hsiteY]
    intro y hy
    obtain ⟨c, hcA, rfl⟩ := Finset.mem_image.1 hy
    exact inBox_intToTorus (by omega) c (hc c hcA)
  have hrel' : ∀ y ∈ siteSet d s m (X.image (blockOf d s m)),
      blockOf d s m2 (boxMap (s * m) (s * m2) y) = σ (blockOf d s m y) := by
    rw [hsiteY]; exact hrel
  have hg : ∀ y ∈ siteSet d s m (X.image (blockOf d s m)),
      (fun z : Torus d (s * m2) => g fun μ => ZMod.valMinAbs (n := s * m2) (z μ))
        (boxMap (s * m) (s * m2) y) =
      (fun z : Torus d (s * m) => g fun μ => ZMod.valMinAbs (n := s * m) (z μ)) y := by
    intro y hy
    rw [hsiteY] at hy
    obtain ⟨c, hcA, rfl⟩ := Finset.mem_image.1 hy
    have hι : boxMap (s * m) (s * m2) (intToTorus d (s * m) c) = intToTorus d (s * m2) c :=
      boxMap_intToTorus (by omega) c (hc c hcA)
    simp only [hι]
    congr 1
    funext μ
    rw [intToTorus_apply, intToTorus_apply, valMinAbs_intCast_of_abs_le (by omega) (hc c hcA μ),
      valMinAbs_intCast_of_abs_le (by omega) (hc c hcA μ)]
  exact frPY_lift h hmarg1 hmarg2 hY hinj hrel' hh hε _ _ hg

end

end Balaban.LargeField.KF0FR
