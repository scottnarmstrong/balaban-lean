/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusGenAgree
public import Balaban.LargeField.Background.TwoTorusOps
public import Balaban.LargeField.Background.TwoTorusPb
public import Balaban.LargeField.Operators.Quiet

/-!
# Blocks and cubes of integer lifts, and the cast between level tori

A block (side `P = L^j`) or a cube (side `P = L^j M`) of a torus `𝕋_ℓ`, `ℓ = P q`, is the point
`zcast q (bidx P w)` of `𝕋_q` for the integer representative `w` of a site. Two blocks (cubes) of
two tori correspond (`CCorr`) when they have this form for one `w` in the box. On the box the
correspondence is a partial bijection (`CCorr.right_unique`, `CCorr.left_unique`), it carries
`BSub` ("all sites of the block lie in a set") between two corresponding sets (`bsub_corr_iff`),
and it gives equality of finite sums and products over corresponding index sets
(`sum_of_rel`, `prod_of_rel`). The casts `torusCast` between equal torus sizes commute with
`zcast` and `liftNear`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.Multiscale

/-! ### The cast between equal torus sizes -/

section Cast

variable {d : ℕ}

theorem torusCast_zcast {m m' : ℕ} (h : m = m') (w : Fin d → ℤ) :
    torusCast h (zcast m w) = zcast m' w := by
  subst h; rfl

theorem liftNear_torusCast {m m' : ℕ} [NeZero m] [NeZero m'] (h : m = m') (c : Fin d → ℤ)
    (x : Torus d m) : liftNear c (torusCast h x) = liftNear c x := by
  subst h; rfl

theorem torusCast_injective {m m' : ℕ} (h : m = m') :
    Function.Injective (torusCast (d := d) h) := by
  subst h; exact fun _ _ e => e

theorem torusCast_surj {m m' : ℕ} (h : m = m') (y : Torus d m') :
    ∃ x : Torus d m, torusCast h x = y := by
  subst h; exact ⟨y, rfl⟩

theorem torusCast_symm_cast {m m' : ℕ} (h : m = m') (x : Torus d m) :
    torusCast h.symm (torusCast h x) = x := by
  subst h; rfl

theorem inBox_cast {m₁ m₂ m₁' m₂' : ℕ} (h₁ : m₁ = m₁') (h₂ : m₂ = m₂') {c w : Fin d → ℤ} :
    InBox m₁ m₂ c w ↔ InBox m₁' m₂' c w := by
  subst h₁; subst h₂; exact Iff.rfl

theorem inBoxK_cast {K m₁ m₂ m₁' m₂' : ℕ} (h₁ : m₁ = m₁') (h₂ : m₂ = m₂') {c w : Fin d → ℤ} :
    InBoxK K m₁ m₂ c w ↔ InBoxK K m₁' m₂' c w := by
  subst h₁; subst h₂; exact Iff.rfl

end Cast

/-! ### Corresponding points -/

section Pt

variable {d : ℕ}

theorem ptCorr_iff_exists {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂] {c : Fin d → ℤ}
    {x₁ : Torus d m₁} {x₂ : Torus d m₂} :
    PtCorr c x₁ x₂ ↔ ∃ w, InBox m₁ m₂ c w ∧ x₁ = zcast m₁ w ∧ x₂ = zcast m₂ w := by
  constructor
  · rintro ⟨h, hb⟩
    refine ⟨liftNear c x₁, hb, (zcast_liftNear x₁).symm, ?_⟩
    rw [h, zcast_liftNear]
  · rintro ⟨w, hw, rfl, rfl⟩
    refine ⟨by rw [hw.liftNear_zcast₁, hw.liftNear_zcast₂], ?_⟩
    rw [hw.liftNear_zcast₁]; exact hw

theorem ptCorr_zcast {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂] {c w : Fin d → ℤ}
    (hw : InBox m₁ m₂ c w) : PtCorr c (zcast m₁ w) (zcast m₂ w) :=
  ptCorr_iff_exists.2 ⟨w, hw, rfl, rfl⟩

end Pt

/-! ### Floor division and the blocks of a lift -/

section Block


variable {d : ℕ}

/-- The block index vector of an integer vector, for blocks of side `P`. -/
def bidx (P : ℕ) (w : Fin d → ℤ) : Fin d → ℤ := fun μ => w μ / (P : ℤ)

theorem bidx_apply (P : ℕ) (w : Fin d → ℤ) (μ : Fin d) : bidx P w μ = w μ / (P : ℤ) := rfl
theorem bidx_add_shift' {d : ℕ} {P : ℕ} (hP : 0 < P) {w s : Fin d → ℤ} :
    bidx P (w + fun μ => (P : ℤ) * s μ) = bidx P w + s := by
  have hP' : (P : ℤ) ≠ 0 := by exact_mod_cast hP.ne'
  funext μ
  simp only [bidx, Pi.add_apply]
  rw [Int.add_mul_ediv_left _ _ hP']

theorem ediv_eq_of_close {P q a b : ℤ} (hP : 0 < P) (hq : 4 ≤ q)
    (h : 4 * |a - b| < 3 * (P * q)) (hdvd : q ∣ a / P - b / P) : a / P = b / P := by
  obtain ⟨t, ht⟩ := hdvd
  have h1 := Int.emod_add_mul_ediv a P
  have h2 := Int.emod_add_mul_ediv b P
  have h3 := Int.emod_nonneg a hP.ne'
  have h4 := Int.emod_lt_of_pos a hP
  have h5 := Int.emod_nonneg b hP.ne'
  have h6 := Int.emod_lt_of_pos b hP
  have hPq : 0 ≤ P * q := by positivity
  have key : t = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have ht1 : t ≤ -1 := by omega
      have e1 : P * q * t ≤ -(P * q) := by nlinarith
      have e2 : P * (a / P - b / P) = P * q * t := by rw [ht]; ring
      have e4 : b - a > P * q - P := by nlinarith
      have e5 : 4 * (P * q - P) ≥ 3 * (P * q) := by nlinarith
      have e6 : (b - a) ≤ |a - b| := by
        have := neg_abs_le (a - b)
        linarith [abs_sub_comm a b, le_abs_self (b - a)]
      nlinarith
    · have ht1 : 1 ≤ t := by omega
      have e1 : P * q ≤ P * q * t := by nlinarith
      have e2 : P * (a / P - b / P) = P * q * t := by rw [ht]; ring
      have e4 : a - b > P * q - P := by nlinarith
      have e5 : 4 * (P * q - P) ≥ 3 * (P * q) := by nlinarith
      have e6 : (a - b) ≤ |a - b| := le_abs_self _
      nlinarith
  rw [key, mul_zero] at ht
  omega

theorem bidx_eq_of_zcast {ℓ P q : ℕ} (hP : 0 < P) (hℓ : ℓ = P * q) (hq : 4 ≤ q)
    {c w v : Fin d → ℤ} (hw : ∀ μ, 4 * |w μ - c μ| < (ℓ : ℤ))
    (hv : ∀ μ, 2 * |v μ - c μ| ≤ (ℓ : ℤ)) (h : zcast q (bidx P w) = zcast q (bidx P v)) :
    bidx P w = bidx P v := by
  funext μ
  have hd := (zcast_eq_iff q _ _).1 h μ
  refine ediv_eq_of_close (P := (P : ℤ)) (q := (q : ℤ)) (by exact_mod_cast hP)
    (by exact_mod_cast hq) ?_ hd
  have h1 := hw μ
  have h2 := hv μ
  have h3 : |w μ - v μ| ≤ |w μ - c μ| + |v μ - c μ| := by
    have := abs_sub_le (w μ) (c μ) (v μ)
    simpa [abs_sub_comm] using this
  have h4 : (ℓ : ℤ) = (P : ℤ) * q := by rw [hℓ]; push_cast; ring
  rw [h4] at h1 h2
  nlinarith

/-- A site in the block of a site with margin `P + 1` has margin `1`, and the same block index
vector. -/
theorem site_margin_of_block {ℓ P q ℓ' : ℕ} [NeZero ℓ] {cc : Fin d → ℤ} (hP : 0 < P)
    (hℓ : ℓ = P * q) (hq : 4 ≤ q) {x s : Torus d ℓ}
    (hx : InBoxK (P + 1) ℓ ℓ' cc (liftNear cc x)) (hs : blockMap P q s = blockMap P q x) :
    InBoxK 1 ℓ ℓ' cc (liftNear cc s) ∧ bidx P (liftNear cc s) = bidx P (liftNear cc x) := by
  have hx' : x = zcast ℓ (liftNear cc x) := (zcast_liftNear x).symm
  have hs' : s = zcast ℓ (liftNear cc s) := (zcast_liftNear s).symm
  rw [hx', hs', blockMap_zcast hℓ hP, blockMap_zcast hℓ hP] at hs
  have hb : bidx P (liftNear cc s) = bidx P (liftNear cc x) :=
    (bidx_eq_of_zcast hP hℓ hq (fun μ => by have := (hx μ).1; omega)
      (fun μ => liftNear_abs_le cc s μ) hs.symm).symm
  refine ⟨fun μ => ?_, hb⟩
  have h1 := abs_ediv_eq_le hP (a := liftNear cc s μ) (b := liftNear cc x μ) (congrFun hb μ)
  have h2 := hx μ
  have h3 : |liftNear cc s μ - cc μ| ≤ |liftNear cc s μ - liftNear cc x μ| +
      |liftNear cc x μ - cc μ| := by
    have := abs_sub_le (liftNear cc s μ) (liftNear cc x μ) (cc μ); exact this
  push_cast at h1 h2 ⊢
  constructor <;> nlinarith [h2.1, h2.2]

end Block

/-! ### Corresponding blocks and cubes -/

section CCorr

variable {d : ℕ}

/-- The block (cube) `y₁ ∈ 𝕋_{q₁}`, `y₂ ∈ 𝕋_{q₂}` of side `P` of the tori `𝕋_{ℓ₁}`, `𝕋_{ℓ₂}`
(`ℓ_i = P q_i`) correspond: they are the blocks of one site of the box. -/
def CCorr (c : Fin d → ℤ) (ℓ₁ ℓ₂ P q₁ q₂ : ℕ) (y₁ : Torus d q₁) (y₂ : Torus d q₂) : Prop :=
  ∃ w, InBox ℓ₁ ℓ₂ c w ∧ y₁ = zcast q₁ (bidx P w) ∧ y₂ = zcast q₂ (bidx P w)

variable {c : Fin d → ℤ} {ℓ₁ ℓ₂ P q₁ q₂ : ℕ}

theorem inBox_two_mul_le {w : Fin d → ℤ} (h : InBox ℓ₁ ℓ₂ c w) (μ : Fin d) :
    2 * |w μ - c μ| ≤ (ℓ₁ : ℤ) ∧ 2 * |w μ - c μ| ≤ (ℓ₂ : ℤ) := by
  have h1 := (inBox_two_mul_lt h μ)
  exact ⟨h1.1.le, h1.2.le⟩

theorem CCorr.right_unique (hP : 0 < P) (hℓ₁ : ℓ₁ = P * q₁) (hq₁ : 4 ≤ q₁) {y₁ : Torus d q₁}
    {y₂ y₂' : Torus d q₂} (h : CCorr c ℓ₁ ℓ₂ P q₁ q₂ y₁ y₂) (h' : CCorr c ℓ₁ ℓ₂ P q₁ q₂ y₁ y₂') :
    y₂ = y₂' := by
  obtain ⟨w, hw, rfl, rfl⟩ := h
  obtain ⟨v, hv, hwv, rfl⟩ := h'
  have := bidx_eq_of_zcast hP hℓ₁ hq₁ (fun μ => (hw μ).1) (fun μ => (inBox_two_mul_le hv μ).1) hwv
  rw [this]

theorem CCorr.left_unique (hP : 0 < P) (hℓ₂ : ℓ₂ = P * q₂) (hq₂ : 4 ≤ q₂) {y₁ y₁' : Torus d q₁}
    {y₂ : Torus d q₂} (h : CCorr c ℓ₁ ℓ₂ P q₁ q₂ y₁ y₂) (h' : CCorr c ℓ₁ ℓ₂ P q₁ q₂ y₁' y₂) :
    y₁ = y₁' := by
  obtain ⟨w, hw, rfl, rfl⟩ := h
  obtain ⟨v, hv, rfl, hwv⟩ := h'
  have := bidx_eq_of_zcast hP hℓ₂ hq₂ (fun μ => (hw μ).2) (fun μ => (inBox_two_mul_le hv μ).2) hwv
  rw [this]

theorem ccorr_symm {y₁ : Torus d q₁} {y₂ : Torus d q₂} (h : CCorr c ℓ₁ ℓ₂ P q₁ q₂ y₁ y₂) :
    CCorr c ℓ₂ ℓ₁ P q₂ q₁ y₂ y₁ := by
  obtain ⟨w, hw, h1, h2⟩ := h
  exact ⟨w, hw.symm, h2, h1⟩

/-- All sites of the block `y` of side `P` lie in `A`. -/
def BSub {ℓ q : ℕ} (P : ℕ) (y : Torus d q) (A : Set (Torus d ℓ)) : Prop :=
  ∀ x, blockMap P q x = y → x ∈ A

theorem bsub_iff_int {ℓ q : ℕ} [NeZero ℓ] {A : Set (Torus d ℓ)} (hP : 0 < P) (hℓ : ℓ = P * q)
    (hq : 4 ≤ q) {w : Fin d → ℤ} (hw : ∀ μ, 4 * |w μ - c μ| < (ℓ : ℤ)) :
    BSub P (zcast q (bidx P w)) A ↔ ∀ v, bidx P v = bidx P w → zcast ℓ v ∈ A := by
  constructor
  · intro h v hv
    apply h
    rw [blockMap_zcast hℓ hP]
    exact congrArg (zcast q) hv
  · intro h x hx
    have hx' : x = zcast ℓ (liftNear c x) := (zcast_liftNear x).symm
    rw [hx', blockMap_zcast hℓ hP] at hx
    have := bidx_eq_of_zcast hP hℓ hq hw (fun μ => by
      have := liftNear_abs_le c x μ
      exact this) hx.symm
    rw [hx']
    exact h _ this.symm

/-- Membership agrees at sites with the same representative near `c` (the third clause of
`SetCorr`; unlike `SetCorr` it is closed under complements). -/
def SetIff (c : Fin d → ℤ) {ℓ₁ ℓ₂ : ℕ} (A₁ : Set (Torus d ℓ₁)) (A₂ : Set (Torus d ℓ₂)) : Prop :=
  ∀ x₁ x₂, liftNear c x₁ = liftNear c x₂ → (x₁ ∈ A₁ ↔ x₂ ∈ A₂)

theorem SetCorr.setIff {A₁ : Set (Torus d ℓ₁)} {A₂ : Set (Torus d ℓ₂)} (h : SetCorr c A₁ A₂) :
    SetIff c A₁ A₂ := h.2.2

theorem SetCorr.symm {A₁ : Set (Torus d ℓ₁)} {A₂ : Set (Torus d ℓ₂)} (h : SetCorr c A₁ A₂) :
    SetCorr c A₂ A₁ :=
  ⟨fun x hx => (h.2.1 x hx).symm, fun x hx => (h.1 x hx).symm,
    fun x₂ x₁ hx => (h.2.2 x₁ x₂ hx.symm).symm⟩

theorem SetIff.compl {A₁ : Set (Torus d ℓ₁)} {A₂ : Set (Torus d ℓ₂)} (h : SetIff c A₁ A₂) :
    SetIff c A₁ᶜ A₂ᶜ := fun x₁ x₂ hx => by simp only [Set.mem_compl_iff]; rw [h x₁ x₂ hx]

theorem SetIff.union {A₁ B₁ : Set (Torus d ℓ₁)} {A₂ B₂ : Set (Torus d ℓ₂)}
    (h : SetIff c A₁ A₂) (h' : SetIff c B₁ B₂) : SetIff c (A₁ ∪ B₁) (A₂ ∪ B₂) :=
  fun x₁ x₂ hx => by simp only [Set.mem_union]; rw [h x₁ x₂ hx, h' x₁ x₂ hx]

theorem SetIff.inter {A₁ B₁ : Set (Torus d ℓ₁)} {A₂ B₂ : Set (Torus d ℓ₂)}
    (h : SetIff c A₁ A₂) (h' : SetIff c B₁ B₂) : SetIff c (A₁ ∩ B₁) (A₂ ∩ B₂) :=
  fun x₁ x₂ hx => by simp only [Set.mem_inter_iff]; rw [h x₁ x₂ hx, h' x₁ x₂ hx]

theorem SetIff.diff {A₁ B₁ : Set (Torus d ℓ₁)} {A₂ B₂ : Set (Torus d ℓ₂)}
    (h : SetIff c A₁ A₂) (h' : SetIff c B₁ B₂) : SetIff c (A₁ \ B₁) (A₂ \ B₂) :=
  fun x₁ x₂ hx => by simp only [Set.mem_sdiff]; rw [h x₁ x₂ hx, h' x₁ x₂ hx]

theorem SetCorr.inter_iff {A₁ B₁ : Set (Torus d ℓ₁)} {A₂ B₂ : Set (Torus d ℓ₂)}
    (hA : SetCorr c A₁ A₂) (hB : SetIff c B₁ B₂) : SetCorr c (A₁ ∩ B₁) (A₂ ∩ B₂) :=
  ⟨fun x hx => hA.1 x hx.1, fun x hx => hA.2.1 x hx.1, hA.setIff.inter hB⟩

theorem SetCorr.sdiff_iff {A₁ B₁ : Set (Torus d ℓ₁)} {A₂ B₂ : Set (Torus d ℓ₂)}
    (hA : SetCorr c A₁ A₂) (hB : SetIff c B₁ B₂) : SetCorr c (A₁ \ B₁) (A₂ \ B₂) :=
  ⟨fun x hx => hA.1 x hx.1, fun x hx => hA.2.1 x hx.1, hA.setIff.diff hB⟩

theorem bsub_corr_iff {A₁ : Set (Torus d ℓ₁)} {A₂ : Set (Torus d ℓ₂)} [NeZero ℓ₁] [NeZero ℓ₂]
    (hP : 0 < P) (hℓ₁ : ℓ₁ = P * q₁) (hℓ₂ : ℓ₂ = P * q₂) (hq₁ : 4 ≤ q₁) (hq₂ : 4 ≤ q₂)
    (hA : SetIff c A₁ A₂) {w : Fin d → ℤ} (hw : InBox ℓ₁ ℓ₂ c w) :
    BSub P (zcast q₁ (bidx P w)) A₁ ↔ BSub P (zcast q₂ (bidx P w)) A₂ := by
  rw [bsub_iff_int hP hℓ₁ hq₁ (c := c) (fun μ => (hw μ).1),
    bsub_iff_int hP hℓ₂ hq₂ (c := c) (fun μ => (hw μ).2)]
  have key : ∀ v, bidx P v = bidx P w →
      ∀ μ, 2 * |v μ - c μ| < (ℓ₁ : ℤ) ∧ 2 * |v μ - c μ| < (ℓ₂ : ℤ) := by
    intro v hv μ
    have h1 := abs_ediv_eq_le hP (a := v μ) (b := w μ) (congrFun hv μ)
    have h2 := hw μ
    have h3 : |v μ - c μ| ≤ |v μ - w μ| + |w μ - c μ| := by
      have := abs_sub_le (v μ) (w μ) (c μ)
      simpa using this
    have h4 : 4 * (P : ℤ) ≤ ℓ₁ := by rw [hℓ₁]; push_cast; nlinarith
    have h5 : 4 * (P : ℤ) ≤ ℓ₂ := by rw [hℓ₂]; push_cast; nlinarith
    constructor <;> nlinarith
  have hiff : ∀ v, bidx P v = bidx P w → (zcast ℓ₁ v ∈ A₁ ↔ zcast ℓ₂ v ∈ A₂) := by
    intro v hv
    have hvb := key v hv
    exact hA _ _ (by
      rw [liftNear_zcast (fun μ => (hvb μ).1), liftNear_zcast (fun μ => (hvb μ).2)])
  constructor
  · intro h v hv; exact (hiff v hv).1 (h v hv)
  · intro h v hv; exact (hiff v hv).2 (h v hv)

theorem exists_site_blockMap {ℓ q : ℕ} [NeZero ℓ] [NeZero q] (hP : 0 < P) (hℓ : ℓ = P * q)
    (y : Torus d q) : ∃ x : Torus d ℓ, blockMap P q x = y := by
  obtain ⟨z, rfl⟩ := exists_rep y
  refine ⟨zcast ℓ (fun μ => (P : ℤ) * z μ), ?_⟩
  rw [blockMap_zcast hℓ hP]
  congr 1
  funext μ
  have : (P : ℤ) ≠ 0 := by exact_mod_cast hP.ne'
  simp [Int.mul_ediv_cancel_left _ this]

/-- A block of a set `A` of the box has a corresponding block of `B` in the other torus. -/
theorem exists_ccorr_of_bsub {A₁ : Set (Torus d ℓ₁)} {A₂ : Set (Torus d ℓ₂)} [NeZero ℓ₁]
    [NeZero ℓ₂] [NeZero q₁] [NeZero q₂] (hP : 0 < P) (hℓ₁ : ℓ₁ = P * q₁) (hℓ₂ : ℓ₂ = P * q₂)
    (hq₁ : 4 ≤ q₁) (hq₂ : 4 ≤ q₂) (hA : SetCorr c A₁ A₂) {y₁ : Torus d q₁}
    (hy : BSub P y₁ A₁) : ∃ y₂, CCorr c ℓ₁ ℓ₂ P q₁ q₂ y₁ y₂ ∧ BSub P y₂ A₂ := by
  obtain ⟨x, hx⟩ := exists_site_blockMap hP hℓ₁ y₁
  have hxA := hy x hx
  have hb := hA.1 x hxA
  have e : y₁ = zcast q₁ (bidx P (liftNear c x)) := by
    rw [← hx]
    conv_lhs => rw [← zcast_liftNear (c := c) x]
    exact blockMap_zcast hℓ₁ hP _
  exact ⟨zcast q₂ (bidx P (liftNear c x)), ⟨liftNear c x, hb, e, rfl⟩,
    (bsub_corr_iff hP hℓ₁ hℓ₂ hq₁ hq₂ hA.setIff hb).1 (e ▸ hy)⟩

theorem exists_ccorr_of_bsub' {A₁ : Set (Torus d ℓ₁)} {A₂ : Set (Torus d ℓ₂)} [NeZero ℓ₁]
    [NeZero ℓ₂] [NeZero q₁] [NeZero q₂] (hP : 0 < P) (hℓ₁ : ℓ₁ = P * q₁) (hℓ₂ : ℓ₂ = P * q₂)
    (hq₁ : 4 ≤ q₁) (hq₂ : 4 ≤ q₂) (hA : SetCorr c A₁ A₂) {y₂ : Torus d q₂}
    (hy : BSub P y₂ A₂) : ∃ y₁, CCorr c ℓ₁ ℓ₂ P q₁ q₂ y₁ y₂ ∧ BSub P y₁ A₁ := by
  have hA' : SetCorr c A₂ A₁ := ⟨fun x hx => (hA.2.1 x hx).symm, fun x hx => (hA.1 x hx).symm, fun x₂ x₁ h => (hA.2.2 x₁ x₂ h.symm).symm⟩
  obtain ⟨y₁, h1, h2⟩ := exists_ccorr_of_bsub hP hℓ₂ hℓ₁ hq₂ hq₁ hA' hy
  exact ⟨y₁, ccorr_symm h1, h2⟩

/-- Two sets of cubes (blocks) correspond: each element has a partner, and corresponding elements
are in both sets or in neither. -/
def CSetCorr (c : Fin d → ℤ) (ℓ₁ ℓ₂ P q₁ q₂ : ℕ) (B₁ : Set (Torus d q₁)) (B₂ : Set (Torus d q₂)) :
    Prop :=
  (∀ z₁ ∈ B₁, ∃ z₂, CCorr c ℓ₁ ℓ₂ P q₁ q₂ z₁ z₂) ∧
  (∀ z₂ ∈ B₂, ∃ z₁, CCorr c ℓ₁ ℓ₂ P q₁ q₂ z₁ z₂) ∧
  ∀ z₁ z₂, CCorr c ℓ₁ ℓ₂ P q₁ q₂ z₁ z₂ → (z₁ ∈ B₁ ↔ z₂ ∈ B₂)

/-- Membership agrees at corresponding elements. -/
def CIff (c : Fin d → ℤ) (ℓ₁ ℓ₂ P q₁ q₂ : ℕ) (B₁ : Set (Torus d q₁)) (B₂ : Set (Torus d q₂)) :
    Prop :=
  ∀ z₁ z₂, CCorr c ℓ₁ ℓ₂ P q₁ q₂ z₁ z₂ → (z₁ ∈ B₁ ↔ z₂ ∈ B₂)

theorem CSetCorr.ciff {B₁ : Set (Torus d q₁)} {B₂ : Set (Torus d q₂)}
    (h : CSetCorr c ℓ₁ ℓ₂ P q₁ q₂ B₁ B₂) : CIff c ℓ₁ ℓ₂ P q₁ q₂ B₁ B₂ := h.2.2

theorem CIff.compl {B₁ : Set (Torus d q₁)} {B₂ : Set (Torus d q₂)}
    (h : CIff c ℓ₁ ℓ₂ P q₁ q₂ B₁ B₂) : CIff c ℓ₁ ℓ₂ P q₁ q₂ B₁ᶜ B₂ᶜ := fun z₁ z₂ hz => by
  simp only [Set.mem_compl_iff]; rw [h z₁ z₂ hz]

theorem CIff.inter {B₁ B₁' : Set (Torus d q₁)} {B₂ B₂' : Set (Torus d q₂)}
    (h : CIff c ℓ₁ ℓ₂ P q₁ q₂ B₁ B₂) (h' : CIff c ℓ₁ ℓ₂ P q₁ q₂ B₁' B₂') :
    CIff c ℓ₁ ℓ₂ P q₁ q₂ (B₁ ∩ B₁') (B₂ ∩ B₂') := fun z₁ z₂ hz => by
  simp only [Set.mem_inter_iff]; rw [h z₁ z₂ hz, h' z₁ z₂ hz]

/-- The set of blocks contained in a set `X` of sites, cut down by a condition that agrees at
corresponding blocks inside `X`, is a corresponding set of blocks. -/
theorem cSetCorr_bsub {X₁ : Set (Torus d ℓ₁)} {X₂ : Set (Torus d ℓ₂)} [NeZero ℓ₁] [NeZero ℓ₂]
    [NeZero q₁] [NeZero q₂] (hP : 0 < P) (hℓ₁ : ℓ₁ = P * q₁) (hℓ₂ : ℓ₂ = P * q₂)
    (hq₁ : 4 ≤ q₁) (hq₂ : 4 ≤ q₂) (hX : SetCorr c X₁ X₂) {E₁ : Set (Torus d q₁)}
    {E₂ : Set (Torus d q₂)}
    (hE : ∀ y₁ y₂, CCorr c ℓ₁ ℓ₂ P q₁ q₂ y₁ y₂ → BSub P y₁ X₁ → (y₁ ∈ E₁ ↔ y₂ ∈ E₂)) :
    CSetCorr c ℓ₁ ℓ₂ P q₁ q₂ {y | BSub P y X₁ ∧ y ∈ E₁} {y | BSub P y X₂ ∧ y ∈ E₂} := by
  refine ⟨fun z₁ hz₁ => ?_, fun z₂ hz₂ => ?_, fun z₁ z₂ hz => ?_⟩
  · obtain ⟨z₂, hz, -⟩ := exists_ccorr_of_bsub hP hℓ₁ hℓ₂ hq₁ hq₂ hX hz₁.1
    exact ⟨z₂, hz⟩
  · obtain ⟨z₁, hz, -⟩ := exists_ccorr_of_bsub' hP hℓ₁ hℓ₂ hq₁ hq₂ hX hz₂.1
    exact ⟨z₁, hz⟩
  · obtain ⟨w, hw, rfl, rfl⟩ := hz
    simp only [Set.mem_ofPred_eq]
    have hb := bsub_corr_iff hP hℓ₁ hℓ₂ hq₁ hq₂ hX.setIff hw
    rw [hb]
    exact and_congr_right fun h2 => hE _ _ ⟨w, hw, rfl, rfl⟩ (hb.2 h2)

theorem CSetCorr.symm {B₁ : Set (Torus d q₁)} {B₂ : Set (Torus d q₂)}
    (h : CSetCorr c ℓ₁ ℓ₂ P q₁ q₂ B₁ B₂) : CSetCorr c ℓ₂ ℓ₁ P q₂ q₁ B₂ B₁ :=
  ⟨fun z₂ hz => (h.2.1 z₂ hz).imp fun _ h' => ccorr_symm h',
    fun z₁ hz => (h.1 z₁ hz).imp fun _ h' => ccorr_symm h',
    fun z₂ z₁ hzz => (h.2.2 z₁ z₂ (ccorr_symm hzz)).symm⟩

theorem two_abs_ediv_le {P n a b : ℤ} (hP : 0 < P) (h : 2 * |a - b| < P * n) :
    2 * |a / P - b / P| ≤ n + 1 := by
  have h1 := Int.emod_add_mul_ediv a P
  have h2 := Int.emod_add_mul_ediv b P
  have h3 := Int.emod_nonneg a hP.ne'
  have h4 := Int.emod_lt_of_pos a hP
  have h5 := Int.emod_nonneg b hP.ne'
  have h6 := Int.emod_lt_of_pos b hP
  have e1 : P * (a / P - b / P) < (a - b) + P := by
    have : P * (a / P - b / P) = P * (a / P) - P * (b / P) := mul_sub _ _ _
    linarith
  have e2 : (a - b) - P < P * (a / P - b / P) := by
    have : P * (a / P - b / P) = P * (a / P) - P * (b / P) := mul_sub _ _ _
    linarith
  by_contra hc
  have hc' : n + 2 ≤ 2 * |a / P - b / P| := by omega
  rcases abs_cases (a / P - b / P) with ⟨h7, h8⟩ | ⟨h7, h8⟩
  · rw [h7] at hc'
    have : P * (n + 2) ≤ P * (2 * (a / P - b / P)) := mul_le_mul_of_nonneg_left hc' hP.le
    have h9 : a - b ≤ |a - b| := le_abs_self _
    nlinarith
  · rw [h7] at hc'
    have : P * (n + 2) ≤ P * (2 * (-(a / P - b / P))) := mul_le_mul_of_nonneg_left hc' hP.le
    have h9 : -(a - b) ≤ |a - b| := neg_le_abs _
    nlinarith

theorem ccorr_nbhd_imp {B₁ : Set (Torus d q₁)} {B₂ : Set (Torus d q₂)} [NeZero q₁] [NeZero q₂]
    (hℓ₁ : ℓ₁ = P * q₁) (r : ℕ) (hr₁ : 2 * r + 4 ≤ q₁) (hP : 0 < P)
    (hB : CSetCorr c ℓ₁ ℓ₂ P q₁ q₂ B₁ B₂) {y₁ : Torus d q₁} {y₂ : Torus d q₂}
    (hy : CCorr c ℓ₁ ℓ₂ P q₁ q₂ y₁ y₂) (h : y₁ ∈ nbhd r B₁) : y₂ ∈ nbhd r B₂ := by
  obtain ⟨w, hw, rfl, rfl⟩ := hy
  obtain ⟨s, hs, hmem⟩ := (mem_nbhd_zcast (bidx P w)).1 h
  obtain ⟨z₂, w', hw', hz1, hz2⟩ := hB.1 _ hmem
  have key : ∀ μ, |(bidx P w + s) μ - bidx P w' μ| < q₁ := by
    intro μ
    have h1 : 2 * |w μ - w' μ| < (P : ℤ) * q₁ := by
      have a1 := (hw μ).1
      have a2 := (hw' μ).1
      have a3 : |w μ - w' μ| ≤ |w μ - c μ| + |w' μ - c μ| := by
        have := abs_sub_le (w μ) (c μ) (w' μ)
        simpa [abs_sub_comm] using this
      have a4 : (ℓ₁ : ℤ) = (P : ℤ) * q₁ := by rw [hℓ₁]; push_cast; ring
      rw [a4] at a1 a2
      linarith
    have h2 := two_abs_ediv_le (by exact_mod_cast hP) h1
    have h3 : |(bidx P w + s) μ - bidx P w' μ| ≤ |bidx P w μ - bidx P w' μ| + |s μ| := by
      have := abs_add_le (bidx P w μ - bidx P w' μ) (s μ)
      simpa [Pi.add_apply, add_sub_right_comm] using this
    have h4 := hs μ
    simp only [bidx] at h3 h2 ⊢
    omega
  have heq := (zcast_eq_iff_of_abs_lt key).1 hz1
  have hz2' : z₂ ∈ B₂ := (hB.2.2 _ _ ⟨w', hw', hz1, hz2⟩).1 hmem
  refine (mem_nbhd_zcast (bidx P w)).2 ⟨s, hs, ?_⟩
  rw [heq, ← hz2]
  exact hz2'

theorem ccorr_nbhd_iff {B₁ : Set (Torus d q₁)} {B₂ : Set (Torus d q₂)} [NeZero q₁] [NeZero q₂]
    (hℓ₁ : ℓ₁ = P * q₁) (hℓ₂ : ℓ₂ = P * q₂) (r : ℕ) (hr₁ : 2 * r + 4 ≤ q₁)
    (hr₂ : 2 * r + 4 ≤ q₂) (hP : 0 < P) (hB : CSetCorr c ℓ₁ ℓ₂ P q₁ q₂ B₁ B₂) :
    CIff c ℓ₁ ℓ₂ P q₁ q₂ (nbhd r B₁) (nbhd r B₂) := fun _ _ hz =>
  ⟨ccorr_nbhd_imp hℓ₁ r hr₁ hP hB hz,
    ccorr_nbhd_imp hℓ₂ r hr₂ hP hB.symm (ccorr_symm hz)⟩

theorem ciff_singleton (hP : 0 < P) (hℓ₁ : ℓ₁ = P * q₁) (hℓ₂ : ℓ₂ = P * q₂) (hq₁ : 4 ≤ q₁)
    (hq₂ : 4 ≤ q₂) {y₁ : Torus d q₁} {y₂ : Torus d q₂}
    (hy : CCorr c ℓ₁ ℓ₂ P q₁ q₂ y₁ y₂) :
    CIff c ℓ₁ ℓ₂ P q₁ q₂ {y₁} {y₂} := fun z₁ z₂ hz => by
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro rfl; exact CCorr.right_unique hP hℓ₁ hq₁ hz hy
  · rintro rfl; exact CCorr.left_unique hP hℓ₂ hq₂ hz hy

theorem cSetCorr_bsub_plain {X₁ : Set (Torus d ℓ₁)} {X₂ : Set (Torus d ℓ₂)} [NeZero ℓ₁]
    [NeZero ℓ₂] [NeZero q₁] [NeZero q₂] (hP : 0 < P) (hℓ₁ : ℓ₁ = P * q₁) (hℓ₂ : ℓ₂ = P * q₂)
    (hq₁ : 4 ≤ q₁) (hq₂ : 4 ≤ q₂) (hX : SetCorr c X₁ X₂) :
    CSetCorr c ℓ₁ ℓ₂ P q₁ q₂ {y | BSub P y X₁} {y | BSub P y X₂} := by
  have := cSetCorr_bsub hP hℓ₁ hℓ₂ hq₁ hq₂ hX (E₁ := Set.univ) (E₂ := Set.univ)
    (fun _ _ _ _ => Iff.rfl)
  simpa using this

/-- **Neighbourhoods of corresponding sets of cubes, at a cube of the box with margin.** -/
theorem nbhd_iff_of_margin {q₁ q₂ r : ℕ} [NeZero q₁] [NeZero q₂] (hP : 0 < P)
    {E₁ : Set (Torus d q₁)} {E₂ : Set (Torus d q₂)}
    (hE : CIff c ℓ₁ ℓ₂ P q₁ q₂ E₁ E₂) {w : Fin d → ℤ} (hw : InBoxK (r * P) ℓ₁ ℓ₂ c w) :
    zcast q₁ (bidx P w) ∈ nbhd r E₁ ↔ zcast q₂ (bidx P w) ∈ nbhd r E₂ := by
  rw [mem_nbhd_zcast, mem_nbhd_zcast]
  refine exists_congr fun s => and_congr_right fun hs => ?_
  have hbox : InBox ℓ₁ ℓ₂ c (w + fun μ => (P : ℤ) * s μ) := by
    intro μ
    have h1 := hw μ
    have h2 : |(w + fun μ => (P : ℤ) * s μ) μ - c μ| ≤ |w μ - c μ| + P * r := by
      have e : (w + fun μ => (P : ℤ) * s μ) μ - c μ = (w μ - c μ) + P * s μ := by
        simp only [Pi.add_apply]; ring
      rw [e]
      have a1 := abs_add_le (w μ - c μ) ((P : ℤ) * s μ)
      have a2 : |(P : ℤ) * s μ| = P * |s μ| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
      have a3 : (P : ℤ) * |s μ| ≤ P * r :=
        mul_le_mul_of_nonneg_left (hs μ) (by positivity)
      linarith
    push_cast at h1
    constructor <;> nlinarith [h1.1, h1.2]
  have hcc : CCorr c ℓ₁ ℓ₂ P q₁ q₂ (zcast q₁ (bidx P w + s)) (zcast q₂ (bidx P w + s)) :=
    ⟨w + fun μ => (P : ℤ) * s μ, hbox, by rw [bidx_add_shift' hP], by rw [bidx_add_shift' hP]⟩
  exact hE _ _ hcc

/-! ### Equality of sums and products over corresponding index sets -/

theorem prod_of_rel {α β γ : Type*} [CommMonoid γ] (F : Finset α) (G : Finset β) (R : α → β → Prop)
    (f : α → γ) (g : β → γ) (h1 : ∀ a ∈ F, ∃ b ∈ G, R a b) (h2 : ∀ b ∈ G, ∃ a ∈ F, R a b)
    (hr : ∀ a b b', R a b → R a b' → b = b') (hl : ∀ a a' b, R a b → R a' b → a = a')
    (hfg : ∀ a b, a ∈ F → b ∈ G → R a b → f a = g b) : ∏ a ∈ F, f a = ∏ b ∈ G, g b := by
  classical
  refine Finset.prod_bij (fun a ha => Classical.choose (h1 a ha)) ?_ ?_ ?_ ?_
  · intro a ha
    exact (Classical.choose_spec (h1 a ha)).1
  · intro a ha a' ha' h
    have e1 := (Classical.choose_spec (h1 a ha)).2
    have e2 := (Classical.choose_spec (h1 a' ha')).2
    rw [h] at e1
    exact hl _ _ _ e1 e2
  · intro b hb
    obtain ⟨a, ha, hab⟩ := h2 b hb
    refine ⟨a, ha, ?_⟩
    exact hr a _ _ (Classical.choose_spec (h1 a ha)).2 hab
  · intro a ha
    exact hfg a _ ha (Classical.choose_spec (h1 a ha)).1 (Classical.choose_spec (h1 a ha)).2

theorem sum_of_rel {α β γ : Type*} [AddCommMonoid γ] (F : Finset α) (G : Finset β)
    (R : α → β → Prop) (f : α → γ) (g : β → γ) (h1 : ∀ a ∈ F, ∃ b ∈ G, R a b)
    (h2 : ∀ b ∈ G, ∃ a ∈ F, R a b) (hr : ∀ a b b', R a b → R a b' → b = b')
    (hl : ∀ a a' b, R a b → R a' b → a = a')
    (hfg : ∀ a b, a ∈ F → b ∈ G → R a b → f a = g b) : ∑ a ∈ F, f a = ∑ b ∈ G, g b :=
  prod_of_rel (γ := Multiplicative γ) F G R f g h1 h2 hr hl hfg

open Classical in
/-- Products over the finite sets of two corresponding sets of cubes (blocks). -/
theorem prod_cset {γ : Type*} [CommMonoid γ] [Fintype (Torus d q₁)] [Fintype (Torus d q₂)]
    (hP : 0 < P) (hℓ₁ : ℓ₁ = P * q₁) (hℓ₂ : ℓ₂ = P * q₂) (hq₁ : 4 ≤ q₁) (hq₂ : 4 ≤ q₂)
    {B₁ : Set (Torus d q₁)} {B₂ : Set (Torus d q₂)} (hB : CSetCorr c ℓ₁ ℓ₂ P q₁ q₂ B₁ B₂)
    (f : Torus d q₁ → γ) (g : Torus d q₂ → γ)
    (hfg : ∀ y₁ y₂, y₁ ∈ B₁ → y₂ ∈ B₂ → CCorr c ℓ₁ ℓ₂ P q₁ q₂ y₁ y₂ → f y₁ = g y₂) :
    ∏ y ∈ (Finset.univ.filter fun y => y ∈ B₁), f y =
      ∏ y ∈ (Finset.univ.filter fun y => y ∈ B₂), g y := by
  classical
  refine prod_of_rel _ _ (CCorr c ℓ₁ ℓ₂ P q₁ q₂) f g ?_ ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨b, hb⟩ := hB.1 a (by simpa using ha)
    exact ⟨b, by simpa using (hB.2.2 a b hb).1 (by simpa using ha), hb⟩
  · intro b hb
    obtain ⟨a, ha⟩ := hB.2.1 b (by simpa using hb)
    exact ⟨a, by simpa using (hB.2.2 a b ha).2 (by simpa using hb), ha⟩
  · intro a b b' h h'
    exact CCorr.right_unique hP hℓ₁ hq₁ h h'
  · intro a a' b h h'
    exact CCorr.left_unique hP hℓ₂ hq₂ h h'
  · intro a b ha hb h
    exact hfg a b (by simpa using ha) (by simpa using hb) h

theorem ccorr_coarsen {L q₁' q₂' : ℕ} [NeZero q₁] [NeZero q₂] (hL : 0 < L) (hq₁ : q₁ = L * q₁')
    (hq₂ : q₂ = L * q₂') {y₁ : Torus d q₁} {y₂ : Torus d q₂}
    (h : CCorr c ℓ₁ ℓ₂ P q₁ q₂ y₁ y₂) :
    CCorr c ℓ₁ ℓ₂ (P * L) q₁' q₂' (blockMap L q₁' y₁) (blockMap L q₂' y₂) := by
  obtain ⟨w, hw, rfl, rfl⟩ := h
  refine ⟨w, hw, ?_, ?_⟩
  · rw [blockMap_zcast hq₁ hL]
    congr 1; funext μ
    simp only [bidx]
    push_cast
    exact Int.ediv_ediv_of_nonneg (by positivity)
  · rw [blockMap_zcast hq₂ hL]
    congr 1; funext μ
    simp only [bidx]
    push_cast
    exact Int.ediv_ediv_of_nonneg (by positivity)

end CCorr

/-! ### Blocks and cubes of the history tori -/

section Hist

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {M K : ℕ}
  [NeZero M] [NeZero S.L]

/-- Two cubes of the tori `𝕋_{n₁ j}`, `𝕋_{n₂ j}` correspond: they contain corresponding sites. -/
def CubeCorr (c : Fin S.d → ℤ) (j : ℕ) (y₁ : Torus S.d (n₁ j)) (y₂ : Torus S.d (n₂ j)) : Prop :=
  ∃ (x₁ : Torus S.d (M * n₁ K * S.L ^ K)) (x₂ : Torus S.d (M * n₂ K * S.L ^ K)),
    PtCorr c x₁ x₂ ∧ cubeMap n₁ S.L M K j x₁ = y₁ ∧ cubeMap n₂ S.L M K j x₂ = y₂

theorem blkCorr_iff_ccorr {c : Fin S.d → ℤ} {j : ℕ} (hj : j ≤ K) {y₁ : BlockAt S n₁ M K j}
    {y₂ : BlockAt S n₂ M K j} :
    BlkCorr (n₁ := n₁) (n₂ := n₂) c j j y₁ y₂ ↔
      CCorr c (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ j) (M * n₁ K * S.L ^ (K - j))
        (M * n₂ K * S.L ^ (K - j)) y₁ y₂ := by
  constructor
  · rintro ⟨-, x₁, x₂, h1, h2, hp⟩
    obtain ⟨w, hw, rfl, rfl⟩ := ptCorr_iff_exists.1 hp
    refine ⟨w, hw, ?_, ?_⟩
    · rw [← h1]; exact jBlock_zcast hj w
    · rw [← h2]; exact jBlock_zcast hj w
  · rintro ⟨w, hw, rfl, rfl⟩
    refine ⟨rfl, zcast _ w, zcast _ w, ?_, ?_, ptCorr_zcast hw⟩
    · exact (jBlock_zcast hj w).symm.symm
    · exact (jBlock_zcast hj w).symm.symm

theorem cubeCorr_iff_ccorr {c : Fin S.d → ℤ} (hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1))
    (hnn₂ : ∀ i, i < K → n₂ i = S.L * n₂ (i + 1)) {j : ℕ} (hj : j ≤ K)
    {y₁ : Torus S.d (n₁ j)} {y₂ : Torus S.d (n₂ j)} :
    CubeCorr (M := M) (K := K) c j y₁ y₂ ↔
      CCorr c (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ j * M) (n₁ j) (n₂ j) y₁ y₂ := by
  have hP : 0 < S.L ^ j * M :=
    Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) _) (Nat.pos_of_ne_zero (NeZero.ne _))
  have e₁ := blockMap_zcast (d := S.d) (fine_eq hnn₁ hj) hP
  have e₂ := blockMap_zcast (d := S.d) (fine_eq hnn₂ hj) hP
  constructor
  · rintro ⟨x₁, x₂, hp, rfl, rfl⟩
    obtain ⟨w, hw, rfl, rfl⟩ := ptCorr_iff_exists.1 hp
    exact ⟨w, hw, e₁ w, e₂ w⟩
  · rintro ⟨w, hw, rfl, rfl⟩
    exact ⟨zcast _ w, zcast _ w, ptCorr_zcast hw, (e₁ w).symm.symm, (e₂ w).symm.symm⟩

theorem cubeMap_zcast (hnn : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1)) {j : ℕ} (hj : j ≤ K)
    (w : Fin S.d → ℤ) :
    cubeMap n₁ S.L M K j (zcast (M * n₁ K * S.L ^ K) w) = zcast (n₁ j) (bidx (S.L ^ j * M) w) :=
  blockMap_zcast (Balaban.LargeField.fine_eq hnn hj)
    (Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) _) (Nat.pos_of_ne_zero (NeZero.ne _))) w

omit [∀ k, NeZero (n₁ k)] [NeZero M] [NeZero S.L] in
theorem blockSub_iff_bsub (j : ℕ) (y : BlockAt S n₁ M K j)
    (B : Set (Torus S.d (M * n₁ K * S.L ^ K))) :
    BlockSub (S := S) (n := n₁) (M := M) (K := K) j y B ↔ BSub (S.L ^ j) y B := Iff.rfl

omit [∀ k, NeZero (n₁ k)] [NeZero M] [NeZero S.L] in
theorem cubeSub_iff_bsub (j : ℕ) (y : Torus S.d (n₁ j))
    (B : Set (Torus S.d (M * n₁ K * S.L ^ K))) :
    CubeSub (S := S) (n := n₁) M K j y B ↔ BSub (S.L ^ j * M) y B := Iff.rfl

end Hist

end Balaban.RootFSpine
