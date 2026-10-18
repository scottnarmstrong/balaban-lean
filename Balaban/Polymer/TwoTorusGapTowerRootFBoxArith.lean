/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerSitesPoly
public import Balaban.Polymer.TwoTorusGapTowerSitesCell

/-!
# Root-F's exact quarter box for the tower's cells (blocker 7), arithmetic

If `4 ∣ K`, the fine quarter box `4 |y| < D K` of the torus `ℤ/(D K)` is carried by the cell map
`y ↦ y / D` (floor division) into the cell box `|c| ≤ K / 4`: there is no extra layer of cells.
The same holds for the polymer property: for finite sets of fine sites in the exact quarter box, the
image in `ℤ/(D K)` is a polymer of blocks of side `D` iff the image in `ℤ/(D K')` is.
Also: the tower's two-torus equality `Tn ℓ g A = Tn ℓ' g A` for `A` in the cell box `Q`, and the
divisibility `4 ∣ K ℓ` from a modulus divisible by `4 D`.
-/

@[expose] public section

noncomputable section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Polymer

open scoped Classical

section Arith

variable {d D K : ℕ}

/-- The resummed term at a set in the cell box `Q` is the term of the canonical torus, so it is the
same for any two tori of the family. -/
theorem Tn_eq_of_quarterBox {ι G α : Type*} (Q : ι → α → Prop) (can : α → ι)
    (Tt : ι → G → α → ℂ) (Tn : ι → G → α → ℂ) (F : ι → α → ℂ)
    (hTn : ∀ ℓ g X, Tn ℓ g X = if Q ℓ X then Tt (can X) g X else Tt ℓ g X + F ℓ X)
    {ℓ ℓ' : ι} {g : G} {A : α} (h : Q ℓ A) (h' : Q ℓ' A) : Tn ℓ g A = Tn ℓ' g A := by
  simp [hTn, h, h']

/-- If `n = D * c` with `4 * D ∣ M` and `M ∣ n`, then `4 ∣ c`. -/
theorem four_dvd_of_dvd_modulus {n M c : ℕ} (hD : 0 < D) (hn : n = D * c) (hM : 4 * D ∣ M)
    (hdv : M ∣ n) : 4 ∣ c := by
  obtain ⟨m, rfl⟩ := hM
  obtain ⟨t, ht⟩ := hdv
  have : D * c = D * (4 * m * t) := by rw [← hn, ht]; ring
  have := Nat.eq_of_mul_eq_mul_left hD this
  exact ⟨m * t, by rw [this]; ring⟩

/-- The fine quarter box `4 |y| < D K` is carried into the cell box `4 |y / D| ≤ K` when `4 ∣ K`. -/
theorem four_abs_ediv_le (hD : 0 < D) (h4 : 4 ∣ K) {y : ℤ} (h : 4 * |y| < (D : ℤ) * K) :
    4 * |y / (D : ℤ)| ≤ K := by
  obtain ⟨m, rfl⟩ := h4
  have hDz : (0 : ℤ) < D := by exact_mod_cast hD
  have h1 := Int.mul_ediv_self_le (x := y) hDz.ne'
  have h2 := Int.lt_mul_ediv_self_add (x := y) hDz
  set c := y / (D : ℤ)
  push_cast at h ⊢
  have hy1 : y < (D : ℤ) * m := by
    have := le_abs_self y
    nlinarith
  have hy2 : -((D : ℤ) * m) < y := by
    have := neg_abs_le y
    nlinarith
  have hhi : c ≤ m := by
    by_contra hc
    replace hc := not_le.1 hc
    have : (D : ℤ) * (m + 1) ≤ (D : ℤ) * c := mul_le_mul_of_nonneg_left (by omega) hDz.le
    nlinarith
  have hlo : -(m : ℤ) ≤ c := by
    by_contra hc
    replace hc := not_le.1 hc
    have : (D : ℤ) * (c + 1) ≤ (D : ℤ) * (-(m : ℤ)) :=
      mul_le_mul_of_nonneg_left (by omega) hDz.le
    nlinarith
  have := abs_le.2 ⟨hlo, hhi⟩
  linarith

/-- The cell of a fine point of the exact quarter box has `natAbs ≤ K / 4`. -/
theorem natAbs_ediv_le_quarter (hD : 0 < D) (h4 : 4 ∣ K) {y : ℤ} (h : 4 * |y| < (D : ℤ) * K) :
    (y / (D : ℤ)).natAbs ≤ K / 4 := by
  have := four_abs_ediv_le hD h4 h
  rw [Int.abs_eq_natAbs] at this
  omega

/-- The cell index of the image of a fine point of the exact quarter box is the centred
representative of `y / D`. -/
theorem cell_valMinAbs_quarter {n : ℕ} (hn : n = D * K) (hD : 0 < D) (h4 : 4 ∣ K) {y : ℤ}
    (h : 4 * |y| < (D : ℤ) * K) :
    ((((y : ZMod n).val / D : ℕ) : ZMod K)).valMinAbs = y / (D : ℤ) := by
  have hK0 : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · subst h0
      norm_num at h
      linarith [abs_nonneg y]
    · exact h0
  have hK : 4 ≤ K := Nat.le_of_dvd hK0 h4
  exact cell_valMinAbs hn hD (r := K / 4) (by omega) (by
    rw [Int.abs_eq_natAbs]; have := natAbs_ediv_le_quarter hD h4 h; exact_mod_cast this)


/-- A finite set of fine sites in the exact quarter box whose image in `ℤ/(D K)` is a polymer of
blocks of side `D` is closed under blocks and connected, as a subset of `ℤ^d`. -/
theorem isPolymer_fwd_quarter {n : ℕ} [NeZero n] (hn : n = D * K) (hK4 : 4 ≤ K)
    (A : Finset (Fin d → ℤ)) (hA : ∀ y ∈ A, ∀ μ, 4 * |y μ| < n)
    (h : IsPolymer d n D (A.image fun y μ => ((y μ : ℤ) : ZMod n))) :
    A.Nonempty ∧ (∀ y ∈ A, ∀ y' : Fin d → ℤ, (∀ μ, y μ / (D : ℤ) = y' μ / (D : ℤ)) → y' ∈ A) ∧
      ∀ y ∈ A, ∀ y' ∈ A, Relation.ReflTransGen
        (fun a b => a ∈ A ∧ b ∈ A ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1)
        y y' := by
  classical
  have hD : 0 < D := Nat.pos_of_ne_zero (left_ne_zero_of_mul (hn ▸ NeZero.ne n))
  have hK : 0 < K := by omega
  have h4D : 4 * D ≤ n := by rw [hn]; nlinarith
  obtain ⟨hne, hsat, hconn⟩ := h
  have hbox1 : ∀ y ∈ A, ∀ μ, 2 * |y μ| + 2 < n := fun y hy μ => by
    have := hA y hy μ; omega
  have hbox2 : ∀ y ∈ A, ∀ μ, 2 * |y μ| < n := fun y hy μ => by
    have := hA y hy μ; omega
  have hinj : ∀ y ∈ A, ∀ y'' ∈ A, (fun μ => ((y μ : ℤ) : ZMod n)) =
      (fun μ => ((y'' μ : ℤ) : ZMod n)) → y = y'' := by
    intro y hy y'' hy'' he
    funext μ
    exact cast_inj (hbox2 y hy μ) (hbox2 y'' hy'' μ) (congrFun he μ)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨y, hy, -⟩ := Finset.mem_image.1 hx
    exact ⟨y, hy⟩
  · intro y hy y' hyy'
    have hx : (fun μ => ((y μ : ℤ) : ZMod n)) ∈
        A.image fun y μ => ((y μ : ℤ) : ZMod n) := Finset.mem_image_of_mem _ hy
    have := hsat _ hx (fun μ => ((y' μ : ℤ) : ZMod n)) (fun μ => by
      have e1 := val_div_cast_int hn hD hK (y μ)
      have e2 := val_div_cast_int hn hD hK (y' μ)
      rw [hyy' μ] at e1
      exact_mod_cast e1.trans e2.symm)
    obtain ⟨y'', hy'', he⟩ := Finset.mem_image.1 this
    have : y'' = y' := by
      funext μ
      refine cast_inj (hbox2 y'' hy'' μ) ?_ (congrFun he μ)
      have h1 := abs_lt_of_ediv_eq hD (hyy' μ)
      have h2 := hA y hy μ
      omega
    rwa [← this]
  · intro y0 hy0 y1 hy1
    have key : ∀ w, Relation.ReflTransGen (fun a b => a ∈ A.image (fun y μ =>
        ((y μ : ℤ) : ZMod n)) ∧ b ∈ A.image (fun y μ => ((y μ : ℤ) : ZMod n)) ∧
        ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1)
        (fun μ => ((y0 μ : ℤ) : ZMod n)) w →
        ∃ y ∈ A, (fun μ => ((y μ : ℤ) : ZMod n)) = w ∧ Relation.ReflTransGen
          (fun a b => a ∈ A ∧ b ∈ A ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨
            a = b + Pi.single μ 1) y0 y := by
      intro w hw
      induction hw with
      | refl => exact ⟨y0, hy0, rfl, Relation.ReflTransGen.refl⟩
      | tail _ hstep ih =>
        obtain ⟨y, hy, rfl, hpath⟩ := ih
        obtain ⟨-, hb, μ, hμ⟩ := hstep
        obtain ⟨y2, hy2, rfl⟩ := Finset.mem_image.1 hb
        rcases hμ with hμ | hμ
        · have e := eq_add_single_of_cast (hbox1 y hy) (hbox2 y2 hy2) hμ
          exact ⟨y2, hy2, rfl, hpath.tail ⟨hy, hy2, μ, Or.inl e⟩⟩
        · have e := eq_add_single_of_cast' (hbox1 y2 hy2) (hbox2 y hy) hμ
          exact ⟨y2, hy2, rfl, hpath.tail ⟨hy, hy2, μ, Or.inr e⟩⟩
    obtain ⟨y, hy, he, hp⟩ := key _ (hconn _ (Finset.mem_image_of_mem _ hy0) _
      (Finset.mem_image_of_mem _ hy1))
    have : y = y1 := hinj y hy y1 hy1 he
    rwa [this] at hp

/-- The image in `ℤ/n` of a finite set of fine sites in the exact quarter box is a polymer of blocks
of side `D` iff the image in `ℤ/n'` is, for any two tori `n = D K`, `n' = D K'`, `4 ≤ K, K'`,
containing the box. -/
theorem isPolymer_image_cast_iff_of_quarter {n n' K' : ℕ} [NeZero n] [NeZero n']
    (hn : n = D * K) (hn' : n' = D * K') (hK : 4 ≤ K) (hK' : 4 ≤ K')
    (A : Finset (Fin d → ℤ)) (hA : ∀ y ∈ A, ∀ μ, 4 * |y μ| < n)
    (hA' : ∀ y ∈ A, ∀ μ, 4 * |y μ| < n') :
    IsPolymer d n D (A.image fun y μ => ((y μ : ℤ) : ZMod n)) ↔
      IsPolymer d n' D (A.image fun y μ => ((y μ : ℤ) : ZMod n')) :=
  ⟨fun h => isPolymer_bwd hn' A (isPolymer_fwd_quarter hn hK A hA h),
    fun h => isPolymer_bwd hn A (isPolymer_fwd_quarter hn' hK' A hA' h)⟩

end Arith

end Balaban.Polymer.TwoTorusStep
