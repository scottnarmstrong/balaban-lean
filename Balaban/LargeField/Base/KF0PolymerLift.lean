/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0BlockLift
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `KF0PolymerLift`: polymers inside the quarter box on two tori

For a finite set `A ⊂ ℤ^d` inside the quarter box of two tori of sides `s m` and `s m₂` (that is,
`4 |y_μ| < min (s m, s m₂)`), the reductions `X = cast A` and `X' = cast' A` are polymers (unions of
blocks of side `s`, nearest-neighbour connected) of the two tori simultaneously
(`polymer_lift`), and the blocks correspond by a map `σ` injective on the blocks of `X` and
compatible with `boxMap` on the sites. The arithmetic of the integer model:

* `blockCoord_intCast'`, `blockOf_intToTorus`: the block of the reduction of an integer vector is
  `⌊y/s⌋ mod m`;
* `two_le_of_polymer`: a polymer inside the quarter box needs `m ≥ 2` (an all-torus polymer for
  `m = 1` would contain a site of coordinate `⌊ℓ/2⌋`);
* `block_closed_of_polymer`: `A` is closed under `ℤ^d`-blocks, `union_of_blocks_of_closed`: a
  block-closed set reduces to a union of blocks on every torus;
* `blockOf_intToTorus_eq_iff`: for `m ≥ 2` two vectors of the quarter box lie in the same torus
  block iff they lie in the same `ℤ^d`-block.

`kf0PY_agree` is the two-torus agreement of the local terms of the all-plus gas.
-/

@[expose] public section

open Finset Balaban Balaban.Polymer Balaban.Green

namespace Balaban.KF0Lift

section Cast

variable {d : ℕ}

/-- **The block of an integer representative**: `⌊y/s⌋ mod m`. -/
theorem blockCoord_intCast' {ℓ s m : ℕ} [NeZero ℓ] (hs : 0 < s) (hℓ : ℓ = s * m) (y : ℤ) :
    blockCoord s m ((y : ℤ) : ZMod ℓ) = (((y / (s : ℤ) : ℤ)) : ZMod m) := by
  have hs0 : (s : ℤ) ≠ 0 := by exact_mod_cast hs.ne'
  have hn : ((ℓ : ℕ) : ℤ) = (s : ℤ) * m := by rw [hℓ]; push_cast; rfl
  have hval : (((y : ℤ) : ZMod ℓ).val : ℤ) = y % (ℓ : ℤ) := by
    exact ZMod.val_intCast y
  set q : ℤ := y / (ℓ : ℤ) with hq
  have h1 : (((y : ℤ) : ZMod ℓ).val : ℤ) = y + (-((m : ℤ) * q)) * s := by
    rw [hval, Int.emod_def, ← hq, hn]; ring
  have h2 : ((((y : ℤ) : ZMod ℓ).val / s : ℕ) : ℤ) = y / (s : ℤ) - (m : ℤ) * q := by
    rw [Int.natCast_div, h1, Int.add_mul_ediv_right _ _ hs0]; ring
  unfold blockCoord
  have e1 : ((((y : ℤ) : ZMod ℓ).val / s : ℕ) : ZMod m) =
      ((((((y : ℤ) : ZMod ℓ).val / s : ℕ) : ℤ)) : ZMod m) := (Int.cast_natCast _).symm
  rw [e1, h2]
  push_cast
  simp only [ZMod.natCast_self, zero_mul, sub_zero]


/-- The block of the reduction of an integer vector. -/
theorem blockOf_intToTorus {s m : ℕ} [NeZero s] [NeZero m] (c : Fin d → ℤ) :
    blockOf d s m (intToTorus d (s * m) c) = fun μ => (((c μ / (s : ℤ) : ℤ)) : ZMod m) := by
  funext μ
  exact blockCoord_intCast' (Nat.pos_of_ne_zero (NeZero.ne s)) rfl (c μ)

theorem boxMap_intToTorus {ℓ ℓ' R : ℕ} (hℓ : 2 * R + 1 < ℓ) (c : Fin d → ℤ)
    (hc : ∀ μ, |c μ| ≤ R) : boxMap ℓ ℓ' (intToTorus d ℓ c) = intToTorus d ℓ' c := by
  funext μ
  show (((((c μ : ℤ) : ZMod ℓ)).valMinAbs : ℤ) : ZMod ℓ') = ((c μ : ℤ) : ZMod ℓ')
  rw [valMinAbs_intCast_of_abs_le hℓ (hc μ)]

theorem inBox_intToTorus {ℓ R : ℕ} (hℓ : 2 * R + 1 < ℓ) (c : Fin d → ℤ)
    (hc : ∀ μ, |c μ| ≤ R) : InBox d R ℓ (intToTorus d ℓ c) := fun μ => by
  show |(((c μ : ℤ) : ZMod ℓ)).valMinAbs| ≤ R
  rw [valMinAbs_intCast_of_abs_le hℓ (hc μ)]
  exact hc μ

end Cast

section Room

variable {d : ℕ}

/-- **A polymer inside the quarter box needs at least two blocks per side.** -/
theorem two_le_of_polymer {s m : ℕ} [NeZero s] [NeZero m] (hs : 2 ≤ s) (hd : 1 ≤ d)
    (A : Finset (Fin d → ℤ)) (hA : ∀ y ∈ A, ∀ μ, 4 * |y μ| < ((s * m : ℕ) : ℤ))
    (hX : IsPolymer d (s * m) s (A.image (intToTorus d (s * m)))) : 2 ≤ m := by
  by_contra hm
  have hm1 : m = 1 := by have := Nat.pos_of_ne_zero (NeZero.ne m); omega
  subst hm1
  obtain ⟨⟨x, hx⟩, hsat, -⟩ := hX
  set μ₀ : Fin d := ⟨0, hd⟩ with hμ₀
  set x' : Torus d (s * 1) := fun ν => if ν = μ₀ then (((s / 2 : ℕ) : ZMod (s * 1))) else 0 with hx'
  have hval : ∀ z : ZMod (s * 1), z.val / s = 0 := fun z => by
    have := ZMod.val_lt z
    exact Nat.div_eq_of_lt (by omega)
  have hx'mem := hsat x hx x' (fun μ => by rw [hval, hval])
  obtain ⟨c, hcA, hc⟩ := Finset.mem_image.1 hx'mem
  have h1 : (((c μ₀ : ℤ) : ZMod (s * 1))) = (((s / 2 : ℕ) : ZMod (s * 1))) := by
    have := congrFun hc μ₀
    simpa [hx', intToTorus_apply] using this
  have h2 : (((c μ₀ - ((s / 2 : ℕ) : ℤ) : ℤ)) : ZMod (s * 1)) = 0 := by
    rw [Int.cast_sub, Int.cast_natCast, h1, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
  have h3 := hA c hcA μ₀
  have e1 := le_abs_self (c μ₀)
  have e2 := neg_abs_le (c μ₀)
  have h4 : |c μ₀ - ((s / 2 : ℕ) : ℤ)| < ((s * 1 : ℕ) : ℤ) := by
    rw [abs_lt]
    generalize |c μ₀| = a at *
    push_cast at h3 ⊢
    constructor <;> omega
  have h5 := Int.eq_zero_of_abs_lt_dvd h2 h4
  generalize |c μ₀| = a at *
  push_cast at h3
  omega

end Room

section Closed

variable {d : ℕ}

theorem abs_sub_lt_of_ediv_eq {s : ℕ} (hs : 0 < s) {a b : ℤ} (h : a / (s : ℤ) = b / (s : ℤ)) :
    |a - b| < s := by
  have hs' : (0 : ℤ) < s := by exact_mod_cast hs
  have h1 := Int.mul_ediv_add_emod a s
  have h2 := Int.mul_ediv_add_emod b s
  have h3 := Int.emod_nonneg a hs'.ne'
  have h4 := Int.emod_nonneg b hs'.ne'
  have h5 := Int.emod_lt_of_pos a hs'
  have h6 := Int.emod_lt_of_pos b hs'
  rw [abs_lt]
  rw [h] at h1
  constructor <;> nlinarith

/-- **A polymer in the quarter box is block-closed in `ℤ^d`.** -/
theorem block_closed_of_polymer {s m : ℕ} [NeZero s] [NeZero m] (hs : 2 ≤ s) (hd : 1 ≤ d)
    (A : Finset (Fin d → ℤ)) (hA : ∀ y ∈ A, ∀ μ, 4 * |y μ| < ((s * m : ℕ) : ℤ))
    (hX : IsPolymer d (s * m) s (A.image (intToTorus d (s * m)))) :
    ∀ c ∈ A, ∀ z : Fin d → ℤ, (∀ μ, z μ / (s : ℤ) = c μ / (s : ℤ)) → z ∈ A := by
  have hm2 := two_le_of_polymer hs hd A hA hX
  intro c hc z hz
  obtain ⟨-, hsat, -⟩ := hX
  have hblk : blockOf d s m (intToTorus d (s * m) c) = blockOf d s m (intToTorus d (s * m) z) := by
    rw [blockOf_intToTorus, blockOf_intToTorus]
    funext μ
    rw [hz μ]
  obtain ⟨c₂, hc₂, hcz⟩ := Finset.mem_image.1 (hsat _ (Finset.mem_image_of_mem _ hc) _
    ((blockOf_eq_iff d s m _ _).1 hblk))
  have hs0 : 0 < s := by omega
  have h2s : 2 * s ≤ s * m := by nlinarith
  suffices hcz' : c₂ = z by rw [← hcz']; exact hc₂
  funext μ
  have h1 : (((c₂ μ : ℤ) : ZMod (s * m))) = (((z μ : ℤ) : ZMod (s * m))) := by
    have := congrFun hcz μ
    simpa [intToTorus_apply] using this
  have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub (c₂ μ) (z μ) (s * m)).1 h1
  have h3 := hA c hc μ
  have h4 := hA c₂ hc₂ μ
  have h5 := abs_sub_lt_of_ediv_eq hs0 (hz μ)
  have h6 : |z μ - c₂ μ| < ((s * m : ℕ) : ℤ) := by
    have e1 := abs_sub_abs_le_abs_sub (z μ) (c μ)
    have e2 := abs_sub (z μ) (c₂ μ)
    have e3 := abs_nonneg (c μ)
    have e4 := abs_nonneg (c₂ μ)
    have e5 := abs_nonneg (z μ - c μ)
    generalize |z μ - c μ| = a at *
    generalize |c μ| = b at *
    generalize |c₂ μ| = e at *
    generalize |z μ| = f at *
    generalize |z μ - c₂ μ| = g at *
    push_cast at h3 h4 h5 ⊢
    have : (2 * s : ℤ) ≤ (s : ℤ) * m := by exact_mod_cast h2s
    omega
  have := Int.eq_zero_of_abs_lt_dvd h2 h6
  omega

end Closed

section Union

variable {d : ℕ}

/-- **The block-closed set `A` reduces to a union of blocks on every torus.** -/
theorem union_of_blocks_of_closed {s m : ℕ} [NeZero s] [NeZero m] (A : Finset (Fin d → ℤ))
    (hclosed : ∀ c ∈ A, ∀ z : Fin d → ℤ, (∀ μ, z μ / (s : ℤ) = c μ / (s : ℤ)) → z ∈ A) :
    ∀ x ∈ A.image (intToTorus d (s * m)), ∀ y : Torus d (s * m),
      (∀ μ, (x μ).val / s = (y μ).val / s) → y ∈ A.image (intToTorus d (s * m)) := by
  intro x hx y hxy
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hx
  have hs0 : (s : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne s
  set w : Fin d → ℤ := fun μ => ((y μ).val : ℤ) with hw
  have hwy : intToTorus d (s * m) w = y := by
    funext μ
    simp [intToTorus_apply, hw]
  have hblk : blockOf d s m (intToTorus d (s * m) c) = blockOf d s m (intToTorus d (s * m) w) := by
    rw [hwy]; exact (blockOf_eq_iff d s m _ _).2 hxy
  rw [blockOf_intToTorus, blockOf_intToTorus] at hblk
  have hdvd : ∀ μ, ∃ q : ℤ, w μ / (s : ℤ) - c μ / (s : ℤ) = (m : ℤ) * q := fun μ => by
    have := congrFun hblk μ
    have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub (c μ / (s : ℤ)) (w μ / (s : ℤ)) m).1 this
    exact h2
  choose q hq using hdvd
  set z : Fin d → ℤ := fun μ => w μ - ((s * m : ℕ) : ℤ) * q μ with hz
  have hzdiv : ∀ μ, z μ / (s : ℤ) = c μ / (s : ℤ) := fun μ => by
    have : z μ = w μ + (-((m : ℤ) * q μ)) * (s : ℤ) := by
      simp only [hz]; push_cast; ring
    rw [this, Int.add_mul_ediv_right _ _ hs0]
    have := hq μ
    linarith
  have hzy : intToTorus d (s * m) z = y := by
    rw [← hwy]
    funext μ
    simp only [intToTorus_apply, hz]
    push_cast
    rw [show ((s : ZMod (s * m)) * (m : ZMod (s * m))) = ((s * m : ℕ) : ZMod (s * m)) by push_cast; rfl,
      ZMod.natCast_self]
    simp
  rw [← hzy]
  exact Finset.mem_image_of_mem _ (hclosed c hc z hzdiv)

end Union

section Iff

variable {d : ℕ}

theorem abs_ediv_sub_lt {s m : ℕ} [NeZero s] (hm : 2 ≤ m) {c₁ c₂ : ℤ}
    (h₁ : 4 * |c₁| < ((s * m : ℕ) : ℤ)) (h₂ : 4 * |c₂| < ((s * m : ℕ) : ℤ)) :
    |c₂ / (s : ℤ) - c₁ / (s : ℤ)| < m := by
  have hs : (0 : ℤ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hsm : (2 * s : ℤ) ≤ (s : ℤ) * m := by
    have : 2 * s ≤ s * m := by nlinarith
    exact_mod_cast this
  have a1 := Int.mul_ediv_add_emod c₁ s
  have a2 := Int.mul_ediv_add_emod c₂ s
  have b1 := Int.emod_nonneg c₁ hs.ne'
  have b2 := Int.emod_nonneg c₂ hs.ne'
  have d1 := Int.emod_lt_of_pos c₁ hs
  have d2 := Int.emod_lt_of_pos c₂ hs
  have e1 := le_abs_self c₁
  have e2 := neg_abs_le c₁
  have e3 := le_abs_self c₂
  have e4 := neg_abs_le c₂
  push_cast at h₁ h₂
  generalize |c₁| = u at *
  generalize |c₂| = v at *
  rw [abs_lt]
  constructor
  · have : (s : ℤ) * (-(m : ℤ)) < (s : ℤ) * (c₂ / (s : ℤ) - c₁ / (s : ℤ)) := by nlinarith
    exact lt_of_mul_lt_mul_left this hs.le
  · have : (s : ℤ) * (c₂ / (s : ℤ) - c₁ / (s : ℤ)) < (s : ℤ) * m := by nlinarith
    exact lt_of_mul_lt_mul_left this hs.le

/-- **Blocks of integer vectors in the quarter box.** Two vectors of the quarter box with at least
two blocks per side lie in the same block of the torus iff they lie in the same block of `ℤ^d`. -/
theorem blockOf_intToTorus_eq_iff {s m : ℕ} [NeZero s] [NeZero m] (hm : 2 ≤ m)
    {c₁ c₂ : Fin d → ℤ} (h₁ : ∀ μ, 4 * |c₁ μ| < ((s * m : ℕ) : ℤ))
    (h₂ : ∀ μ, 4 * |c₂ μ| < ((s * m : ℕ) : ℤ)) :
    blockOf d s m (intToTorus d (s * m) c₁) = blockOf d s m (intToTorus d (s * m) c₂) ↔
      ∀ μ, c₁ μ / (s : ℤ) = c₂ μ / (s : ℤ) := by
  rw [blockOf_intToTorus, blockOf_intToTorus]
  constructor
  · intro h μ
    have := congrFun h μ
    have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub (c₁ μ / (s : ℤ)) (c₂ μ / (s : ℤ)) m).1 this
    have h3 := Int.eq_zero_of_abs_lt_dvd h2 (abs_ediv_sub_lt hm (h₁ μ) (h₂ μ))
    omega
  · intro h
    funext μ
    rw [h μ]

end Iff

section PolymerLift

variable {d : ℕ}

/-- **The polymer lift.**  A polymer of one torus that is the reduction of a finite set `A ⊂ ℤ^d`
inside the quarter box of both tori is, on the other torus, again a polymer; the blocks of the two
are in bijection by a map `σ` compatible with `boxMap` on the sites. -/
theorem polymer_lift {s m m2 : ℕ} [NeZero s] [NeZero m] [NeZero m2] (hs : 6 ≤ s) (hd : 1 ≤ d)
    (A : Finset (Fin d → ℤ))
    (hA : ∀ y ∈ A, ∀ μ, 4 * |y μ| < ((s * m : ℕ) : ℤ) ∧ 4 * |y μ| < ((s * m2 : ℕ) : ℤ))
    (hX : IsPolymer d (s * m) s (A.image (intToTorus d (s * m)))) :
    IsPolymer d (s * m2) s (A.image (intToTorus d (s * m2))) ∧
    ∃ (R₀ : ℕ) (σ : Torus d m → Torus d m2),
      2 * (R₀ + 1) + 1 < s * m ∧ 2 * (R₀ + 1) + 1 < s * m2 ∧
      (∀ y ∈ A.image (intToTorus d (s * m)), InBox d R₀ (s * m) y) ∧
      (∀ c ∈ A, ∀ μ, |c μ| ≤ R₀) ∧
      Set.InjOn σ (((A.image (intToTorus d (s * m))).image (blockOf d s m) :
        Finset (Torus d m)) : Set (Torus d m)) ∧
      (∀ y ∈ A.image (intToTorus d (s * m)),
        blockOf d s m2 (boxMap (s * m) (s * m2) y) = σ (blockOf d s m y)) ∧
      ((A.image (intToTorus d (s * m))).image (blockOf d s m)).image σ =
        (A.image (intToTorus d (s * m2))).image (blockOf d s m2) := by
  have hA1 : ∀ y ∈ A, ∀ μ, 4 * |y μ| < ((s * m : ℕ) : ℤ) := fun y hy μ => (hA y hy μ).1
  have hA2 : ∀ y ∈ A, ∀ μ, 4 * |y μ| < ((s * m2 : ℕ) : ℤ) := fun y hy μ => (hA y hy μ).2
  have hs2 : 2 ≤ s := by omega
  have hm2 := two_le_of_polymer hs2 hd A hA1 hX
  have hclosed := block_closed_of_polymer hs2 hd A hA1 hX
  have hunion' := union_of_blocks_of_closed (s := s) (m := m2) A hclosed
  -- the radius
  set R₀ : ℕ := (min (s * m) (s * m2) - 1) / 4 with hR₀
  have hsm : 6 ≤ s * m := le_trans hs (Nat.le_mul_of_pos_right s (Nat.pos_of_ne_zero (NeZero.ne m)))
  have hsm2 : 6 ≤ s * m2 := le_trans hs (Nat.le_mul_of_pos_right s (Nat.pos_of_ne_zero (NeZero.ne m2)))
  have hR1 : 2 * (R₀ + 1) + 1 < s * m := by omega
  have hR2 : 2 * (R₀ + 1) + 1 < s * m2 := by omega
  have hc : ∀ c ∈ A, ∀ μ, |c μ| ≤ R₀ := by
    intro c hc μ
    have h1 := hA1 c hc μ
    have h2 := hA2 c hc μ
    have e1 := le_abs_self (c μ)
    have e2 := neg_abs_le (c μ)
    generalize |c μ| = a at *
    push_cast at h1 h2
    omega
  have hι : ∀ c ∈ A, boxMap (s * m) (s * m2) (intToTorus d (s * m) c) = intToTorus d (s * m2) c :=
    fun c hcA => boxMap_intToTorus (by omega) c (hc c hcA)
  have hbox : ∀ y ∈ A.image (intToTorus d (s * m)), InBox d R₀ (s * m) y := by
    intro y hy
    obtain ⟨c, hcA, rfl⟩ := Finset.mem_image.1 hy
    exact inBox_intToTorus (by omega) c (hc c hcA)
  have himg : (A.image (intToTorus d (s * m))).image (boxMap (s * m) (s * m2)) =
      A.image (intToTorus d (s * m2)) := by
    rw [Finset.image_image]
    exact Finset.image_congr fun c hcA => hι c hcA
  -- X' is a polymer
  have hpoly' : IsPolymer d (s * m2) s (A.image (intToTorus d (s * m2))) := by
    obtain ⟨hne, -, hconn⟩ := hX
    refine ⟨?_, hunion', ?_⟩
    · obtain ⟨x, hx⟩ := hne
      exact ⟨intToTorus d (s * m2) (Classical.choose (Finset.mem_image.1 hx)),
        Finset.mem_image_of_mem _ (Classical.choose_spec (Finset.mem_image.1 hx)).1⟩
    · intro x' hx' y' hy'
      rw [← himg] at hx' hy'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hy'
      refine Relation.ReflTransGen.lift (boxMap (s * m) (s * m2)) (fun a b hab => ?_) _ _
        (hconn x hx y hy)
      obtain ⟨ha, hb, μ, hμ⟩ := hab
      refine ⟨himg ▸ Finset.mem_image_of_mem _ ha, himg ▸ Finset.mem_image_of_mem _ hb, μ, ?_⟩
      have hR : 2 * R₀ + 1 < s * m := by omega
      have hR' : 2 * R₀ + 1 < s * m2 := by omega
      rcases hμ with hμ | hμ
      · left; exact (boxMap_step_iff hR hR' (hbox a ha) (hbox b hb) μ).1 hμ
      · right; exact (boxMap_step_iff hR hR' (hbox b hb) (hbox a ha) μ).1 hμ
  have hm2' := two_le_of_polymer hs2 hd A hA2 hpoly'
  classical
  set X : Finset (Torus d (s * m)) := A.image (intToTorus d (s * m)) with hXdef
  set σ : Torus d m → Torus d m2 := fun b =>
    if h : ∃ x ∈ X, blockOf d s m x = b then
      blockOf d s m2 (boxMap (s * m) (s * m2) h.choose) else 0 with hσ
  have hiff : ∀ x ∈ X, ∀ y ∈ X, blockOf d s m x = blockOf d s m y ↔
      blockOf d s m2 (boxMap (s * m) (s * m2) x) = blockOf d s m2 (boxMap (s * m) (s * m2) y) := by
    intro x hx y hy
    obtain ⟨c₁, hc₁, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨c₂, hc₂, rfl⟩ := Finset.mem_image.1 hy
    rw [hι c₁ hc₁, hι c₂ hc₂, blockOf_intToTorus_eq_iff hm2 (hA1 c₁ hc₁) (hA1 c₂ hc₂),
      blockOf_intToTorus_eq_iff hm2' (hA2 c₁ hc₁) (hA2 c₂ hc₂)]
  have hrel : ∀ y ∈ X, blockOf d s m2 (boxMap (s * m) (s * m2) y) = σ (blockOf d s m y) := by
    intro y hy
    have h : ∃ x ∈ X, blockOf d s m x = blockOf d s m y := ⟨y, hy, rfl⟩
    simp only [hσ, h, dite_true]
    exact ((hiff _ h.choose_spec.1 y hy).1 h.choose_spec.2).symm
  refine ⟨hpoly', R₀, σ, by omega, by omega, hbox, hc, ?_, hrel, ?_⟩
  · intro b₁ hb₁ b₂ hb₂ h12
    obtain ⟨y₁, hy₁, rfl⟩ := Finset.mem_image.1 hb₁
    obtain ⟨y₂, hy₂, rfl⟩ := Finset.mem_image.1 hb₂
    rw [← hrel y₁ hy₁, ← hrel y₂ hy₂] at h12
    exact (hiff y₁ hy₁ y₂ hy₂).2 h12
  · ext b'
    constructor
    · intro hb'
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hb'
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
      refine Finset.mem_image.2 ⟨boxMap (s * m) (s * m2) y, ?_, hrel y hy⟩
      rw [← himg]
      exact Finset.mem_image_of_mem _ hy
    · intro hb'
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hb'
      rw [← himg] at hy'
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hy'
      exact Finset.mem_image.2 ⟨blockOf d s m y, Finset.mem_image_of_mem _ hy, (hrel y hy).symm⟩

end PolymerLift

section Agree

open Balaban.LargeField.KF0AllPlus MeasureTheory Balaban.LargeField.SphereChart

variable {d N n : ℕ} {h : EuclideanSpace ℝ (Fin N)}

/-- **The local terms of the all-plus gas agree on two tori (d).**  A polymer of one torus that is
the reduction of a finite set `A ⊂ ℤ^d` in the quarter box of both tori has, on the other torus, the
same local term at the same source `g : ℤ^d → ℂ^N` (read through centred representatives). -/
theorem kf0PY_agree {s m m2 : ℕ} [NeZero s] [NeZero m] [NeZero m2] (hs : 6 ≤ s) (hd : 1 ≤ d)
    (A : Finset (Fin d → ℤ))
    (hA : ∀ y ∈ A, ∀ μ, 4 * |y μ| < ((s * m : ℕ) : ℤ) ∧ 4 * |y μ| < ((s * m2 : ℕ) : ℤ))
    (hX : IsPolymer d (s * m) s (A.image (intToTorus d (s * m))))
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (pc : Measure (perp h)) [IsProbabilityMeasure pc]
    (g : (Fin d → ℤ) → Fin N → ℂ) :
    kf0PY e β ν p pc ((A.image (intToTorus d (s * m2))).image (blockOf d s m2))
        (fun z => g fun μ => ZMod.valMinAbs (n := s * m2) (z μ)) =
      kf0PY e β ν p pc ((A.image (intToTorus d (s * m))).image (blockOf d s m))
        (fun z => g fun μ => ZMod.valMinAbs (n := s * m) (z μ)) := by
  obtain ⟨hpoly', R₀, σ, hR1, hR2, hbox, hc, hinj, hrel, himage⟩ := polymer_lift hs hd A hA hX
  rw [← himage]
  set X : Finset (Torus d (s * m)) := A.image (intToTorus d (s * m)) with hXdef
  have hsiteY : siteSet d s m (X.image (blockOf d s m)) = X := siteSet_image_blockOf hX.2.1
  have hY : ∀ y ∈ siteSet d s m (X.image (blockOf d s m)), InBox d R₀ (s * m) y := by
    rw [hsiteY]; exact hbox
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
  exact kf0PY_lift (R₀ := R₀) hR1 hR2 hY hinj hrel' e β ν p pc _ _ hg

end Agree

end Balaban.KF0Lift
