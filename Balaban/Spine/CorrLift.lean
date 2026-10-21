/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusCubeLift

/-!
# Lifted cube indices of two tori

For the cubes of side `P` of a torus `𝕋_q` (`ℓ = P q` the fine torus) whose sites lie in the box
about `cc`, the index vector of a cube is lifted to `ℤ^d` near the centre `cc / P` (`clift`).  The
lift is injective, equals `⌊w / P⌋` for the box lift `w` of every site of the cube, and the index
distance of two cubes of a set in the box is the distance of the lifts (`GBox.supDist_lt`).
Consequently a correspondence (`SetCorr`) of the fine sets of two sets of cubes of two tori is the
equality of the lifted index sets (`setCorr_iff_clift`), and the components of a set of cubes of a
torus are, under the lift, the components of the lifted set (`image_comps`).  This turns the
comparison of the combinatorics of two tori into the comparison of finite sets of `ℤ^d`.
-/

@[expose] public section

open Balaban Balaban.LargeField

namespace Balaban.RootFSpine

section Abstract

variable {d : ℕ}

/-- The integer lift of a cube index vector, near the centre `bidx P cc`. -/
def clift (P : ℕ) (cc : Fin d → ℤ) {q : ℕ} [NeZero q] (y : Torus d q) : Fin d → ℤ :=
  liftNear (bidx P cc) y

theorem zcast_clift (P : ℕ) (cc : Fin d → ℤ) {q : ℕ} [NeZero q] (y : Torus d q) :
    zcast q (clift P cc y) = y := zcast_liftNear y

theorem clift_inj (P : ℕ) (cc : Fin d → ℤ) {q : ℕ} [NeZero q] {y y' : Torus d q}
    (h : clift P cc y = clift P cc y') : y = y' := by
  rw [← zcast_clift P cc y, ← zcast_clift P cc y', h]

theorem clift_zcast (P : ℕ) (cc : Fin d → ℤ) {q : ℕ} [NeZero q] {u : Fin d → ℤ}
    (h : ∀ μ, 2 * |u μ - bidx P cc μ| < (q : ℤ)) : clift P cc (zcast q u) = u :=
  liftNear_zcast h

/-- floor-division closeness: `4|a - b| < P q` gives `2|a/P - b/P| < q` for `q ≥ 4`. -/
theorem two_abs_ediv_lt {P q : ℕ} (hP : 0 < P) (hq : 4 ≤ q) {a b : ℤ}
    (h : 4 * |a - b| < (P : ℤ) * q) : 2 * |a / (P : ℤ) - b / (P : ℤ)| < q := by
  have h1 := two_abs_ediv_le (P := (P : ℤ)) (n := ((q + 1) / 2 : ℕ)) (a := a) (b := b)
    (by exact_mod_cast hP) (by
      have : (q : ℤ) ≤ 2 * (((q + 1) / 2 : ℕ) : ℤ) := by omega
      have hP' : (0 : ℤ) < P := by exact_mod_cast hP
      nlinarith)
  have : (((q + 1) / 2 : ℕ) : ℤ) + 1 < q := by omega
  omega

theorem clift_blockMap {P q ℓ : ℕ} [NeZero ℓ] [NeZero q] (hP : 0 < P) (hℓ : ℓ = P * q)
    (hq : 4 ≤ q) (cc : Fin d → ℤ) {x : Torus d ℓ}
    (hx : ∀ μ, 4 * |liftNear cc x μ - cc μ| < (ℓ : ℤ)) :
    clift P cc (blockMap P q x) = bidx P (liftNear cc x) := by
  have hx' : x = zcast ℓ (liftNear cc x) := (zcast_liftNear x).symm
  conv_lhs => rw [hx', blockMap_zcast hℓ hP]
  refine clift_zcast P cc fun μ => ?_
  refine two_abs_ediv_lt hP hq ?_
  have h1 := hx μ
  have h2 : (ℓ : ℤ) = (P : ℤ) * q := by rw [hℓ]; push_cast; ring
  rw [h2] at h1
  exact h1

end Abstract

section Box

variable {d : ℕ} {P q ℓ m' : ℕ} [NeZero ℓ] [NeZero q] {cc : Fin d → ℤ}

/-- A set of cubes of side `P` all of whose sites have their box lift in the set `B` of lifts. -/
def GBoxB (B : (Fin d → ℤ) → Prop) (P q ℓ : ℕ) (cc : Fin d → ℤ) [NeZero ℓ]
    (A : Finset (Torus d q)) : Prop :=
  ∀ y ∈ A, ∀ x : Torus d ℓ, blockMap P q x = y → B (liftNear cc x)

/-- A set of cubes of side `P` whose sites all lie in the box. -/
abbrev GBox (P q ℓ m' : ℕ) (cc : Fin d → ℤ) [NeZero ℓ] (A : Finset (Torus d q)) : Prop :=
  GBoxB (InBox ℓ m' cc) P q ℓ cc A

/-- A set of cubes of side `P` whose sites all lie in the box with the margin `K`. -/
abbrev GBoxK (K P q ℓ m' : ℕ) (cc : Fin d → ℤ) [NeZero ℓ] (A : Finset (Torus d q)) : Prop :=
  GBoxB (InBoxK K ℓ m' cc) P q ℓ cc A

theorem GBoxK.toGBox {K P q ℓ m' : ℕ} [NeZero ℓ] {A : Finset (Torus d q)}
    (h : GBoxK K P q ℓ m' cc A) : GBox P q ℓ m' cc A := fun y hy x hx => (h y hy x hx).inBox

theorem GBoxK.mono {K K' P q ℓ m' : ℕ} [NeZero ℓ] {A : Finset (Torus d q)}
    (h : GBoxK K P q ℓ m' cc A) (hK : K' ≤ K) : GBoxK K' P q ℓ m' cc A :=
  fun y hy x hx => (h y hy x hx).mono hK

theorem bidx_mul (hP : 0 < P) (u : Fin d → ℤ) : bidx P (fun μ => (P : ℤ) * u μ) = u := by
  funext μ
  have : (P : ℤ) ≠ 0 := by exact_mod_cast hP.ne'
  simp [bidx, Int.mul_ediv_cancel_left _ this]

/-- The corner `P u` of a cube of a set in the box lies in the box. -/
theorem GBoxB.lo {B : (Fin d → ℤ) → Prop} (hB : ∀ w, B w → ∀ μ, 4 * |w μ - cc μ| < (ℓ : ℤ))
    (hP : 0 < P) (hℓ : ℓ = P * q) (hq : 4 ≤ q) {A : Finset (Torus d q)}
    (hA : GBoxB B P q ℓ cc A) {y : Torus d q} (hy : y ∈ A) :
    B (fun μ => (P : ℤ) * clift P cc y μ) := by
  set u := clift P cc y with hu
  set x := zcast ℓ (fun μ => (P : ℤ) * u μ) with hx
  have hbm : blockMap P q x = y := by
    rw [hx, blockMap_zcast hℓ hP]
    have : (fun μ => ((P : ℤ) * u μ) / (P : ℤ)) = u := bidx_mul hP u
    rw [this, hu, zcast_clift]
  have hb := hA y hy x hbm
  set w := liftNear cc x with hw
  have hcl : clift P cc y = bidx P w := by
    rw [← hbm]
    exact clift_blockMap hP hℓ hq cc (fun μ => hB _ hb μ)
  have hdvd : ∀ μ, (ℓ : ℤ) ∣ w μ - (P : ℤ) * u μ := by
    have h1 : zcast ℓ w = x := zcast_liftNear x
    exact (zcast_eq_iff ℓ w _).1 h1
  have hmod : ∀ μ, w μ = (P : ℤ) * u μ := by
    intro μ
    have hd := hdvd μ
    have e1 : u μ = w μ / (P : ℤ) := by
      have := congrFun hcl μ
      simpa [bidx] using this
    have hPpos : (0 : ℤ) < P := by exact_mod_cast hP
    have h2 := Int.emod_add_mul_ediv (w μ) (P : ℤ)
    have h3 := Int.emod_nonneg (w μ) hPpos.ne'
    have h4 := Int.emod_lt_of_pos (w μ) hPpos
    have hPℓ : (P : ℤ) ≤ ℓ := by
      rw [hℓ]; push_cast; nlinarith
    have habs : |w μ - (P : ℤ) * u μ| < ℓ := by
      rw [abs_lt]; constructor <;> nlinarith
    have := Int.eq_zero_of_abs_lt_dvd hd habs
    linarith
  have : (fun μ => (P : ℤ) * u μ) = w := funext fun μ => (hmod μ).symm
  rw [this]; exact hb

/-- The opposite corner `P u + (P - 1)` of a cube of a set in the box lies in the box. -/
theorem GBoxB.hi {B : (Fin d → ℤ) → Prop} (hB : ∀ w, B w → ∀ μ, 4 * |w μ - cc μ| < (ℓ : ℤ))
    (hP : 0 < P) (hℓ : ℓ = P * q) (hq : 4 ≤ q) {A : Finset (Torus d q)}
    (hA : GBoxB B P q ℓ cc A) {y : Torus d q} (hy : y ∈ A) :
    B (fun μ => (P : ℤ) * clift P cc y μ + ((P : ℤ) - 1)) := by
  set u := clift P cc y with hu
  set v : Fin d → ℤ := fun μ => (P : ℤ) * u μ + ((P : ℤ) - 1) with hv
  set x := zcast ℓ v with hx
  have hPpos : (0 : ℤ) < P := by exact_mod_cast hP
  have hdiv : ∀ μ, v μ / (P : ℤ) = u μ := by
    intro μ
    simp only [hv]
    rw [Int.mul_add_ediv_left _ _ hPpos.ne']
    have : ((P : ℤ) - 1) / (P : ℤ) = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
    omega
  have hbm : blockMap P q x = y := by
    rw [hx, blockMap_zcast hℓ hP]
    have : (fun μ => v μ / (P : ℤ)) = u := funext hdiv
    rw [this, hu, zcast_clift]
  have hb := hA y hy x hbm
  set w := liftNear cc x with hw
  have hcl : clift P cc y = bidx P w := by
    rw [← hbm]
    exact clift_blockMap hP hℓ hq cc (fun μ => hB _ hb μ)
  have hdvd : ∀ μ, (ℓ : ℤ) ∣ w μ - v μ := by
    have h1 : zcast ℓ w = x := zcast_liftNear x
    exact (zcast_eq_iff ℓ w _).1 h1
  have hmod : ∀ μ, w μ = v μ := by
    intro μ
    have hd := hdvd μ
    have e1 : u μ = w μ / (P : ℤ) := by
      have := congrFun hcl μ
      simpa [bidx] using this
    have h2 := Int.emod_add_mul_ediv (w μ) (P : ℤ)
    have h3 := Int.emod_nonneg (w μ) hPpos.ne'
    have h4 := Int.emod_lt_of_pos (w μ) hPpos
    have hPℓ : (P : ℤ) ≤ ℓ := by
      rw [hℓ]; push_cast; nlinarith
    have habs : |w μ - v μ| < ℓ := by
      simp only [hv]
      rw [abs_lt]; constructor <;> nlinarith
    have := Int.eq_zero_of_abs_lt_dvd hd habs
    linarith
  have : v = w := funext fun μ => (hmod μ).symm
  rw [this]; exact hb

/-- **The core of the distance bound for the lifts of two cubes of a set in the box.**  If the
corners of the cubes with lifts `u`, `u'` satisfy `2 |w - w'| + e < ℓ` then
`2 (u - u' + 1) P + e < P q + 2` (for `u' ≤ u`). -/
theorem GBoxB.pair_core {B : (Fin d → ℤ) → Prop} (hB : ∀ w, B w → ∀ μ, 4 * |w μ - cc μ| < (ℓ : ℤ))
    (hP : 0 < P) (hℓ : ℓ = P * q) (hq : 4 ≤ q) {A : Finset (Torus d q)}
    (hA : GBoxB B P q ℓ cc A) {e : ℤ}
    (hBB : ∀ w w', B w → B w' → ∀ μ, 2 * |w μ - w' μ| + e < (ℓ : ℤ)) {y y' : Torus d q}
    (hy : y ∈ A) (hy' : y' ∈ A) (μ : Fin d) (hge : clift P cc y μ - clift P cc y' μ ≥ 0) :
    2 * (clift P cc y μ - clift P cc y' μ + 1) * P + e < (P : ℤ) * q + 2 := by
  have h1 := GBoxB.hi hB hP hℓ hq hA hy
  have h2 := GBoxB.lo hB hP hℓ hq hA hy'
  have h3 := hBB _ _ h1 h2 μ
  set D := clift P cc y μ - clift P cc y' μ with hD
  have hℓz : (ℓ : ℤ) = (P : ℤ) * q := by rw [hℓ]; push_cast; ring
  have ee : ((P : ℤ) * clift P cc y μ + ((P : ℤ) - 1)) - (P : ℤ) * clift P cc y' μ =
      (P : ℤ) * D + ((P : ℤ) - 1) := by rw [hD]; ring
  rw [ee, hℓz] at h3
  have hPz : (0 : ℤ) < P := by exact_mod_cast hP
  rw [abs_of_nonneg (by nlinarith)] at h3
  nlinarith

/-- **Two cubes of a set in the box have lifted indices at distance `≤ (q - 2)/2`.** -/
theorem GBox.pair (hP : 2 ≤ P) (hℓ : ℓ = P * q) (hq : 4 ≤ q) 
    {A : Finset (Torus d q)} (hA : GBox P q ℓ m' cc A) {y y' : Torus d q} (hy : y ∈ A)
    (hy' : y' ∈ A) (μ : Fin d) : 2 * |clift P cc y μ - clift P cc y' μ| + 2 ≤ (q : ℤ) := by
  have hP0 : 0 < P := by omega
  have hPz : (2 : ℤ) ≤ P := by exact_mod_cast hP
  have hB : ∀ w, InBox ℓ m' cc w → ∀ μ, 4 * |w μ - cc μ| < (ℓ : ℤ) := fun w hw μ => (hw μ).1
  have hBB : ∀ w w', InBox ℓ m' cc w → InBox ℓ m' cc w' → ∀ μ, 2 * |w μ - w' μ| + 0 < (ℓ : ℤ) :=
    fun w w' hw hw' μ => by have := (two_abs_sub_lt hw hw' μ).1; omega
  have key : ∀ {y y' : Torus d q}, y ∈ A → y' ∈ A → clift P cc y μ - clift P cc y' μ ≥ 0 →
      2 * (clift P cc y μ - clift P cc y' μ) + 2 ≤ (q : ℤ) := by
    intro y y' hy hy' hge
    have := GBoxB.pair_core hB hP0 hℓ hq hA hBB hy hy' μ hge
    by_contra hc
    have : (q : ℤ) + 1 ≤ 2 * (clift P cc y μ - clift P cc y' μ) + 2 := by omega
    nlinarith
  rcases le_total 0 (clift P cc y μ - clift P cc y' μ) with h | h
  · rw [abs_of_nonneg h]; exact key hy hy' h
  · rw [abs_of_nonpos h]
    have := key hy' hy (by linarith)
    linarith

/-- **With a margin `P`: the lifted indices of two cubes are at distance `≤ (q - 6)/2`.** -/
theorem GBoxK.pair (hP : 2 ≤ P) (hℓ : ℓ = P * q) (hq : 4 ≤ q) 
    {A : Finset (Torus d q)} (hA : GBoxK P P q ℓ m' cc A) {y y' : Torus d q} (hy : y ∈ A)
    (hy' : y' ∈ A) (μ : Fin d) : 2 * |clift P cc y μ - clift P cc y' μ| + 6 ≤ (q : ℤ) := by
  have hP0 : 0 < P := by omega
  have hPz : (2 : ℤ) ≤ P := by exact_mod_cast hP
  have hB : ∀ w, InBoxK P ℓ m' cc w → ∀ μ, 4 * |w μ - cc μ| < (ℓ : ℤ) :=
    fun w hw μ => by have := (hw μ).1; have := abs_nonneg (w μ - cc μ); nlinarith
  have hBB : ∀ w w', InBoxK P ℓ m' cc w → InBoxK P ℓ m' cc w' → ∀ μ,
      2 * |w μ - w' μ| + 4 * P < (ℓ : ℤ) := by
    intro w w' hw hw' μ
    have h1 := (hw μ).1
    have h2 := (hw' μ).1
    have h3 : |w μ - w' μ| ≤ |w μ - cc μ| + |w' μ - cc μ| := by
      have := abs_sub_le (w μ) (cc μ) (w' μ)
      simpa [abs_sub_comm] using this
    nlinarith
  have key : ∀ {y y' : Torus d q}, y ∈ A → y' ∈ A → clift P cc y μ - clift P cc y' μ ≥ 0 →
      2 * (clift P cc y μ - clift P cc y' μ) + 6 ≤ (q : ℤ) := by
    intro y y' hy hy' hge
    have := GBoxB.pair_core hB hP0 hℓ hq hA hBB hy hy' μ hge
    by_contra hc
    have : (q : ℤ) + 1 ≤ 2 * (clift P cc y μ - clift P cc y' μ) + 6 := by omega
    nlinarith
  rcases le_total 0 (clift P cc y μ - clift P cc y' μ) with h | h
  · rw [abs_of_nonneg h]; exact key hy hy' h
  · rw [abs_of_nonpos h]
    have := key hy' hy (by linarith)
    linarith

/-- On a set of cubes in the box, the index distance is the distance of the lifts. -/
theorem GBox.supDist_lt (hP : 2 ≤ P) (hℓ : ℓ = P * q) (hq : 4 ≤ q) 
    {A : Finset (Torus d q)} (hA : GBox P q ℓ m' cc A) {y y' : Torus d q} (hy : y ∈ A)
    (hy' : y' ∈ A) {ω : ℕ} (hω : 0 < ω) :
    supDist y y' < ω ↔ ∀ μ, |clift P cc y μ - clift P cc y' μ| < ω := by
  have hnorm : ∀ μ, cycNorm q (y μ - y' μ) = (clift P cc y μ - clift P cc y' μ).natAbs := by
    intro μ
    have e : y μ - y' μ = (((clift P cc y μ - clift P cc y' μ : ℤ)) : ZMod q) := by
      conv_lhs => rw [← zcast_clift P cc y, ← zcast_clift P cc y']
      simp [zcast]
    rw [e, cycNorm_intCast_of_le]
    have := GBox.pair hP hℓ hq hA hy hy' μ
    omega
  unfold supDist
  rw [Finset.sup_lt_iff (by omega : (⊥ : ℕ) < ω)]
  constructor
  · intro h μ
    have := h μ (Finset.mem_univ _)
    rw [hnorm] at this
    have h2 : |clift P cc y μ - clift P cc y' μ| = ((clift P cc y μ - clift P cc y' μ).natAbs : ℤ) :=
      Int.abs_eq_natAbs _
    rw [h2]; exact_mod_cast this
  · intro h μ _
    rw [hnorm]
    have := h μ
    have h2 : |clift P cc y μ - clift P cc y' μ| = ((clift P cc y μ - clift P cc y' μ).natAbs : ℤ) :=
      Int.abs_eq_natAbs _
    rw [h2] at this; exact_mod_cast this

end Box

section Corr

variable {d : ℕ} {P q₁ q₂ ℓ₁ ℓ₂ : ℕ} [NeZero ℓ₁] [NeZero ℓ₂] [NeZero q₁] [NeZero q₂]

/-- The lifted cube indices of a finite set of cubes. -/
def cliftSet (P : ℕ) (cc : Fin d → ℤ) {q : ℕ} [NeZero q] (A : Finset (Torus d q)) :
    Finset (Fin d → ℤ) := A.image (clift P cc)

theorem mem_cliftSet {P : ℕ} {cc : Fin d → ℤ} {q : ℕ} [NeZero q] {A : Finset (Torus d q)}
    {u : Fin d → ℤ} : u ∈ cliftSet P cc A ↔ ∃ y ∈ A, clift P cc y = u := by
  simp [cliftSet]

theorem card_cliftSet {P : ℕ} {cc : Fin d → ℤ} {q : ℕ} [NeZero q] (A : Finset (Torus d q)) :
    (cliftSet P cc A).card = A.card :=
  Finset.card_image_of_injective _ (fun _ _ h => clift_inj P cc h)

/-- **A correspondence of fine sets of cubes is an equality of the lifted cube indices.** -/
theorem setCorr_iff_clift (hP : 2 ≤ P) (hℓ₁ : ℓ₁ = P * q₁) (hℓ₂ : ℓ₂ = P * q₂) (hq₁ : 4 ≤ q₁)
    (hq₂ : 4 ≤ q₂) {cc : Fin d → ℤ} {A₁ : Finset (Torus d q₁)} {A₂ : Finset (Torus d q₂)} :
    SetCorr cc {x : Torus d ℓ₁ | blockMap P q₁ x ∈ A₁} {x : Torus d ℓ₂ | blockMap P q₂ x ∈ A₂} ↔
      GBox P q₁ ℓ₁ ℓ₂ cc A₁ ∧ GBox P q₂ ℓ₂ ℓ₁ cc A₂ ∧ cliftSet P cc A₁ = cliftSet P cc A₂ := by
  have hP0 : 0 < P := by omega
  -- the key step: a site `x₁` of `A₁` and a site `x₂` with the same lift
  have step : ∀ (x₁ : Torus d ℓ₁) (x₂ : Torus d ℓ₂), liftNear cc x₁ = liftNear cc x₂ →
      InBox ℓ₁ ℓ₂ cc (liftNear cc x₁) →
      clift P cc (blockMap P q₁ x₁) = clift P cc (blockMap P q₂ x₂) := by
    intro x₁ x₂ hl hb
    rw [clift_blockMap hP0 hℓ₁ hq₁ cc (fun μ => (hb μ).1),
      clift_blockMap hP0 hℓ₂ hq₂ cc (fun μ => by rw [← hl]; exact (hb μ).2), hl]
  constructor
  · intro h
    have g1 : GBox P q₁ ℓ₁ ℓ₂ cc A₁ := fun y hy x hx => h.1 x (by simpa [hx] using hy)
    have g2 : GBox P q₂ ℓ₂ ℓ₁ cc A₂ := fun y hy x hx => (h.2.1 x (by simpa [hx] using hy)).symm
    refine ⟨g1, g2, ?_⟩
    ext u
    simp only [mem_cliftSet]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, hx⟩ := exists_site_blockMap hP0 hℓ₁ y
      have hxA : x ∈ {x : Torus d ℓ₁ | blockMap P q₁ x ∈ A₁} := by simpa [hx] using hy
      have hb := h.1 x hxA
      set x₂ : Torus d ℓ₂ := zcast ℓ₂ (liftNear cc x) with hx₂
      have hl : liftNear cc x = liftNear cc x₂ := by rw [hx₂, hb.liftNear_zcast₂]
      have hx2 := (h.2.2 x x₂ hl).1 hxA
      exact ⟨blockMap P q₂ x₂, hx2, by rw [← hx]; exact (step x x₂ hl hb).symm⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, hx⟩ := exists_site_blockMap hP0 hℓ₂ y
      have hxA : x ∈ {x : Torus d ℓ₂ | blockMap P q₂ x ∈ A₂} := by simpa [hx] using hy
      have hb := h.2.1 x hxA
      set x₁ : Torus d ℓ₁ := zcast ℓ₁ (liftNear cc x) with hx₁
      have hl : liftNear cc x₁ = liftNear cc x := by rw [hx₁, hb.liftNear_zcast₁]
      have hx1 := (h.2.2 x₁ x hl).2 hxA
      exact ⟨blockMap P q₁ x₁, hx1, by rw [← hx]; exact step x₁ x hl (by rw [hl]; exact hb)⟩
  · rintro ⟨g1, g2, hc⟩
    refine ⟨fun x hx => g1 _ hx x rfl, fun x hx => (g2 _ hx x rfl).symm, ?_⟩
    intro x₁ x₂ hl
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h1
      have hb := g1 _ h1 x₁ rfl
      have e := step x₁ x₂ hl hb
      have : clift P cc (blockMap P q₂ x₂) ∈ cliftSet P cc A₂ := by
        rw [← hc, ← e]; exact mem_cliftSet.2 ⟨_, h1, rfl⟩
      obtain ⟨y, hy, hye⟩ := mem_cliftSet.1 this
      rw [← clift_inj P cc hye]; exact hy
    · intro h2
      have hb := g2 _ h2 x₂ rfl
      have hb' : InBox ℓ₁ ℓ₂ cc (liftNear cc x₁) := by rw [hl]; exact hb.symm
      have e := step x₁ x₂ hl hb'
      have : clift P cc (blockMap P q₁ x₁) ∈ cliftSet P cc A₁ := by
        rw [hc, e]; exact mem_cliftSet.2 ⟨_, h2, rfl⟩
      obtain ⟨y, hy, hye⟩ := mem_cliftSet.1 this
      rw [← clift_inj P cc hye]; exact hy

end Corr

section Comps

variable {d : ℕ}

/-- Two lifted cubes are linked: both lie in the set and their index vectors are `< ω` apart. -/
def zlink (ω : ℕ) (Λ : Finset (Fin d → ℤ)) (a b : Fin d → ℤ) : Prop :=
  a ∈ Λ ∧ b ∈ Λ ∧ ∀ μ, |a μ - b μ| < ω

/-- Chains of linked lifted cubes. -/
def ZLinked (ω : ℕ) (Λ : Finset (Fin d → ℤ)) : (Fin d → ℤ) → (Fin d → ℤ) → Prop :=
  Relation.ReflTransGen (zlink ω Λ)

open Classical in
/-- The class of a lifted cube. -/
noncomputable def zclass (ω : ℕ) (Λ : Finset (Fin d → ℤ)) (a : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  Λ.filter (ZLinked ω Λ a)

open Classical in
/-- The components of a finite set of lifted cubes. -/
noncomputable def zcomps (ω : ℕ) (Λ : Finset (Fin d → ℤ)) : Finset (Finset (Fin d → ℤ)) :=
  Λ.image (zclass ω Λ)

variable {P q ℓ m' : ℕ} [NeZero ℓ] [NeZero q]

theorem linked_iff_zlinked (hP : 2 ≤ P) (hℓ : ℓ = P * q) (hq : 4 ≤ q) {cc : Fin d → ℤ}
    {A : Finset (Torus d q)} (hA : GBox P q ℓ m' cc A) {ω : ℕ} (hω : 0 < ω) {y : Torus d q}
    (hy : y ∈ A) {u : Fin d → ℤ} :
    (∃ y' ∈ A, clift P cc y' = u ∧ Linked ω (A : Set (Torus d q)) y y') ↔
      ZLinked ω (cliftSet P cc A) (clift P cc y) u := by
  constructor
  · rintro ⟨y', hy', rfl, hl⟩
    induction hl with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      refine (ih hbc.1).tail ⟨mem_cliftSet.2 ⟨b, hbc.1, rfl⟩, mem_cliftSet.2 ⟨c, hbc.2.1, rfl⟩, ?_⟩
      exact (GBox.supDist_lt hP hℓ hq hA hbc.1 hbc.2.1 hω).1 hbc.2.2
  · intro hz
    induction hz with
    | refl => exact ⟨y, hy, rfl, Linked.refl _⟩
    | @tail b c _ hbc ih =>
      obtain ⟨yb, hyb, hbe, hl⟩ := ih
      obtain ⟨yc, hyc, hce⟩ := mem_cliftSet.1 hbc.2.1
      refine ⟨yc, hyc, hce, hl.tail ⟨hyb, hyc, ?_⟩⟩
      refine (GBox.supDist_lt hP hℓ hq hA hyb hyc hω).2 ?_
      rw [hbe, hce]; exact hbc.2.2

open Classical in
theorem image_linkClass (hP : 2 ≤ P) (hℓ : ℓ = P * q) (hq : 4 ≤ q) {cc : Fin d → ℤ}
    {A : Finset (Torus d q)} (hA : GBox P q ℓ m' cc A) {ω : ℕ} (hω : 0 < ω) {y : Torus d q}
    (hy : y ∈ A) :
    (linkClass ω A y).image (clift P cc) = zclass ω (cliftSet P cc A) (clift P cc y) := by
  ext u
  simp only [Finset.mem_image, mem_linkClass, zclass, Finset.mem_filter]
  constructor
  · rintro ⟨y', ⟨hy', hl⟩, rfl⟩
    exact ⟨mem_cliftSet.2 ⟨y', hy', rfl⟩,
      (linked_iff_zlinked hP hℓ hq hA hω hy).1 ⟨y', hy', rfl, hl⟩⟩
  · rintro ⟨hu, hz⟩
    obtain ⟨y', hy', rfl, hl⟩ := (linked_iff_zlinked hP hℓ hq hA hω hy).2 hz
    exact ⟨y', ⟨hy', hl⟩, rfl⟩

open Classical in
/-- **The components of a set of cubes in the box are the components of the lifted cube indices.** -/
theorem image_comps (hP : 2 ≤ P) (hℓ : ℓ = P * q) (hq : 4 ≤ q) {cc : Fin d → ℤ}
    {A : Finset (Torus d q)} (hA : GBox P q ℓ m' cc A) {ω : ℕ} (hω : 0 < ω) :
    (comps ω A).image (Finset.image (clift P cc)) = zcomps ω (cliftSet P cc A) := by
  unfold comps zcomps
  rw [Finset.image_image]
  ext Y
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨clift P cc y, mem_cliftSet.2 ⟨y, hy, rfl⟩, by
      rw [Function.comp, image_linkClass hP hℓ hq hA hω hy]⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨y, hy, rfl⟩ := mem_cliftSet.1 hu
    exact ⟨y, hy, by rw [Function.comp, image_linkClass hP hℓ hq hA hω hy]⟩

end Comps

end Balaban.RootFSpine
