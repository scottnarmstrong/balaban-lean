/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalRegroupAct
public import Balaban.Polymer.TwoTorusGapTowerRootFBoxArith
public import Balaban.Spine.RootFInputs

/-!
# Two-torus agreement of the regrouped activities

A6-3 (c), the last clause. On the images of a finite set `A ⊂ ℤ^d` of the quarter box the polymers
`Y` of a torus with hull `A` are the images of the subsets `B ⊆ A` that meet every block of `A`
(`regroup_image_sum`), a condition that does not depend on the torus. Hence the two-torus agreement
of the scale-`k` terms gives that of the regrouped activity (`regroup_agree`).
-/

@[expose] public section

open Finset Balaban Balaban.Polymer.TwoTorusStep

namespace Balaban.RootFSpine

section Block

variable {D K : ℕ}

/-- The cell index of a point of the quarter box. -/
theorem cell_bounds (hD : 0 < D) {y : ℤ} (hy : 4 * |y| < (D : ℤ) * K) :
    4 * (y / (D : ℤ)) < K ∧ -(K : ℤ) - 4 < 4 * (y / (D : ℤ)) := by
  have hDz : (0 : ℤ) < D := by exact_mod_cast hD
  have h1 := Int.mul_ediv_self_le (x := y) hDz.ne'
  have h2 := Int.lt_mul_ediv_self_add (x := y) hDz
  set c := y / (D : ℤ)
  have h4y : |4 * y| < (D : ℤ) * K := by
    rw [abs_mul]; norm_num; linarith
  obtain ⟨hl, hu⟩ := abs_lt.1 h4y
  constructor
  · by_contra h
    push Not at h
    have := mul_le_mul_of_nonneg_left h hDz.le
    nlinarith
  · by_contra h
    push Not at h
    have := mul_le_mul_of_nonneg_left h hDz.le
    nlinarith

/-- For points of the quarter box, equal torus blocks are equal integer blocks. -/
theorem blockEq_int {n : ℕ} [NeZero n] (hn : n = D * K) (hD : 0 < D) (hK : 4 ≤ K) {y z : ℤ}
    (hy : 4 * |y| < n) (hz : 4 * |z| < n) :
    ((y : ZMod n).val / D = (z : ZMod n).val / D) ↔ y / (D : ℤ) = z / (D : ℤ) := by
  have hK0 : 0 < K := by omega
  have e1 := val_div_cast_int hn hD hK0 y
  have e2 := val_div_cast_int hn hD hK0 z
  constructor
  · intro h
    have h' : (y / (D : ℤ)) % (K : ℤ) = (z / (D : ℤ)) % (K : ℤ) := by
      rw [← e1, ← e2, h]
    have hdvd : (K : ℤ) ∣ y / (D : ℤ) - z / (D : ℤ) :=
      Int.ModEq.dvd h'.symm
    have hn' : (n : ℤ) = D * K := by rw [hn]; push_cast; ring
    rw [hn'] at hy hz
    obtain ⟨hy1, hy2⟩ := cell_bounds hD hy
    obtain ⟨hz1, hz2⟩ := cell_bounds hD hz
    have hK4 : (4 : ℤ) ≤ K := by exact_mod_cast hK
    have := Int.eq_zero_of_abs_lt_dvd hdvd (abs_lt.2 ⟨by linarith, by linarith⟩)
    linarith
  · intro h
    have : (((y : ZMod n).val / D : ℕ) : ℤ) = (((z : ZMod n).val / D : ℕ) : ℤ) := by
      rw [e1, e2, h]
    exact_mod_cast this

end Block

section Sum

variable {d D K n : ℕ} [NeZero n]

open Classical in
/-- **The polymers with hull `A.image` are the images of the subsets of `A` meeting every block of
`A`** (A polymer image in the quarter box). -/
theorem regroup_image_sum (hn : n = D * K) (hD : 0 < D) (hK : 4 ≤ K) (A : Finset (Fin d → ℤ))
    (hA : ∀ y ∈ A, ∀ μ, 4 * |y μ| < (n : ℤ))
    (hpoly : IsPolymer d n D (A.image fun y μ => ((y μ : ℤ) : ZMod n)))
    (F : Finset (Torus d n) → ℂ) :
    ∑ Y ∈ (Finset.univ : Finset (Finset (Torus d n))).filter
        (fun Y => hullT D Y = A.image fun y μ => ((y μ : ℤ) : ZMod n)), F Y =
      ∑ B ∈ A.powerset.filter (fun B => ∀ a ∈ A, ∃ b ∈ B, ∀ μ, a μ / (D : ℤ) = b μ / (D : ℤ)),
        F (B.image fun y μ => ((y μ : ℤ) : ZMod n)) := by
  set c : (Fin d → ℤ) → Torus d n := fun y μ => ((y μ : ℤ) : ZMod n) with hc
  have hbox2 : ∀ y ∈ A, ∀ μ, 2 * |y μ| < (n : ℤ) := fun y hy μ => by
    have := hA y hy μ; omega
  have hinj : ∀ y ∈ A, ∀ y'' ∈ A, c y = c y'' → y = y'' := by
    intro y hy y'' hy'' he
    funext μ
    exact cast_inj (hbox2 y hy μ) (hbox2 y'' hy'' μ) (congrFun he μ)
  have hblk : ∀ a ∈ A, ∀ b ∈ A, (∀ μ, (c a μ).val / D = (c b μ).val / D) ↔
      ∀ μ, a μ / (D : ℤ) = b μ / (D : ℤ) := fun a ha b hb =>
    forall_congr' fun μ => blockEq_int hn hD hK (hA a ha μ) (hA b hb μ)
  have hXcl := hpoly.2.1
  symm
  rw [← Finset.sum_image (f := F) (s := A.powerset.filter
    (fun B => ∀ a ∈ A, ∃ b ∈ B, ∀ μ, a μ / (D : ℤ) = b μ / (D : ℤ))) (g := fun B => B.image c)]
  · congr 1
    ext Y
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨B, ⟨hBA, hB⟩, rfl⟩
      ext x
      rw [mem_hullT]
      constructor
      · rintro ⟨y, hy, hxy⟩
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
        exact hXcl _ (Finset.mem_image_of_mem c (hBA hb)) x (fun μ => (hxy μ).symm)
      · intro hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨b, hb, hab⟩ := hB a ha
        exact ⟨c b, Finset.mem_image_of_mem c hb, fun μ => (hblk a ha b (hBA hb)).2 hab μ⟩
    · intro hY
      refine ⟨A.filter (fun a => c a ∈ Y), ⟨Finset.filter_subset _ _, ?_⟩, ?_⟩
      · intro a ha
        have : c a ∈ hullT D Y := hY ▸ Finset.mem_image_of_mem c ha
        obtain ⟨y, hy, hay⟩ := mem_hullT.1 this
        have hyX : y ∈ A.image c := hY ▸ subset_hullT D Y hy
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hyX
        exact ⟨b, Finset.mem_filter.2 ⟨hb, hy⟩, (hblk a ha b hb).1 hay⟩
      · ext y
        simp only [Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨a, ⟨ha, hay⟩, rfl⟩; exact hay
        · intro hy
          have hyX : y ∈ A.image c := hY ▸ subset_hullT D Y hy
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hyX
          exact ⟨a, ⟨ha, hy⟩, rfl⟩
  · intro B hB B' hB' hBB'
    have hB1 := (Finset.mem_filter.1 hB).1
    have hB1' := (Finset.mem_filter.1 hB').1
    rw [Finset.mem_powerset] at hB1 hB1'
    simp only at hBB'
    ext a
    constructor
    · intro ha
      have : c a ∈ B'.image c := hBB' ▸ Finset.mem_image_of_mem c ha
      obtain ⟨a', ha', he⟩ := Finset.mem_image.1 this
      rwa [← hinj a' (hB1' ha') a (hB1 ha) he]
    · intro ha
      have : c a ∈ B.image c := hBB' ▸ Finset.mem_image_of_mem c ha
      obtain ⟨a', ha', he⟩ := Finset.mem_image.1 this
      rwa [← hinj a' (hB1 ha') a (hB1' ha) he]

end Sum

section Agree

variable {d N : ℕ} {M L k kf : ℕ}
  {t : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ}

open Classical in
/-- **Two-torus agreement of the regrouped activity** (A6-3 (c)). The scale-`k` terms agree on the
images of finite sets of the quarter box (`hAgr`), vanish in the increment off scale-`k` polymers
(`hS`), and the admissible tori are at least four blocks of side `M L^{k+1}` wide (`h4`). -/
theorem regroup_agree (hk : k ≤ kf) (hD : 0 < M * L ^ (k + 1))
    (h4 : ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ → 4 * (M * L ^ (k + 1)) ≤ ℓ)
    (hS : ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ → ∀ Y,
      ¬ IsPolymer d ℓ (M * L ^ k) Y → ∀ g, t ℓ Y g = t ℓ Y 0)
    (hAgr : ∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], M * L ^ (kf + 1) ∣ ℓ → M * L ^ (kf + 1) ∣ ℓ' →
      ∀ (a : Fin d → ℤ) (B : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → Fin N → ℂ), a ∈ B →
        (∀ y ∈ B, ∀ μ, 4 * |y μ| < (ℓ : ℤ) ∧ 4 * |y μ| < (ℓ' : ℤ)) →
        t ℓ (B.image fun y μ => (y μ : ZMod ℓ))
            (fun z => g fun μ => ZMod.valMinAbs (n := ℓ) (z μ)) -
          t ℓ (B.image fun y μ => (y μ : ZMod ℓ)) 0 =
        t ℓ' (B.image fun y μ => (y μ : ZMod ℓ'))
            (fun z => g fun μ => ZMod.valMinAbs (n := ℓ') (z μ)) -
          t ℓ' (B.image fun y μ => (y μ : ZMod ℓ')) 0) :
    ActAgree d N L M kf (regroupFam M L k t) := by
  intro ℓ ℓ' _ _ hdv hdv' j a A g haA hbox
  by_cases hj : j = k + 1
  · subst hj
    have hdivk : M * L ^ (k + 1) ∣ M * L ^ (kf + 1) :=
      mul_dvd_mul_left M (pow_dvd_pow L (by omega))
    obtain ⟨K, hK⟩ := hdivk.trans hdv
    obtain ⟨K', hK'⟩ := hdivk.trans hdv'
    have hK4 : 4 ≤ K := by
      have h := h4 ℓ hdv
      rw [hK] at h
      exact Nat.le_of_mul_le_mul_left (by linarith) hD
    have hK4' : 4 ≤ K' := by
      have h := h4 ℓ' hdv'
      rw [hK'] at h
      exact Nat.le_of_mul_le_mul_left (by linarith) hD
    have hAl : ∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ) := fun y hy μ => (hbox y hy μ).1
    have hAl' : ∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ' : ℤ) := fun y hy μ => (hbox y hy μ).2
    have hDd : M * L ^ (k + 1) = M * L ^ k * L := by ring
    by_cases hP : IsPolymer d ℓ (M * L ^ (k + 1)) (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ))
    · have hP' : IsPolymer d ℓ' (M * L ^ (k + 1)) (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ')) :=
        (isPolymer_image_cast_iff_of_quarter hK hK' hK4 hK4' A hAl hAl').1 hP
      have key : ∀ (m : ℕ) [NeZero m] (Km : ℕ), m = M * L ^ (k + 1) * Km → 4 ≤ Km →
          (∀ y ∈ A, ∀ μ, 4 * |y μ| < (m : ℤ)) →
          IsPolymer d m (M * L ^ (k + 1)) (A.image fun y μ => ((y μ : ℤ) : ZMod m)) →
          ∀ g' : Torus d m → Fin N → ℂ,
          regroupAt M L k t m (A.image fun y μ => ((y μ : ℤ) : ZMod m)) g' -
            regroupAt M L k t m (A.image fun y μ => ((y μ : ℤ) : ZMod m)) 0 =
          ∑ B ∈ A.powerset.filter (fun B => ∀ a ∈ A, ∃ b ∈ B,
              ∀ μ, a μ / ((M * L ^ (k + 1) : ℕ) : ℤ) = b μ / ((M * L ^ (k + 1) : ℕ) : ℤ)),
            (t m (B.image fun y μ => ((y μ : ℤ) : ZMod m)) g' -
              t m (B.image fun y μ => ((y μ : ℤ) : ZMod m)) 0) := by
        intro m _ Km hm hKm hmb hPm g'
        unfold regroupAt
        rw [← Finset.sum_sub_distrib]
        have := regroup_image_sum (n := m) (D := M * L ^ (k + 1)) (K := Km) hm hD hKm A hmb hPm
          (fun Y => t m Y g' - t m Y 0)
        rw [hDd] at this ⊢
        convert this using 2
      rw [regroupFam_succ, regroupFam_succ, regroupFam_succ, regroupFam_succ,
        key ℓ K hK hK4 hAl hP _, key ℓ' K' hK' hK4' hAl' hP' _]
      refine Finset.sum_congr rfl fun B hB => ?_
      have hB' := Finset.mem_filter.1 hB
      have hBA : B ⊆ A := Finset.mem_powerset.1 hB'.1
      obtain ⟨b, hb, -⟩ := hB'.2 a haA
      exact hAgr ℓ ℓ' hdv hdv' b B g hb fun y hy μ => hbox y (hBA hy) μ
    · have hP' : ¬ IsPolymer d ℓ' (M * L ^ (k + 1)) (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ')) :=
        fun h => hP ((isPolymer_image_cast_iff_of_quarter hK hK' hK4 hK4' A hAl hAl').2 h)
      have s1 := regroup_support (M := M) (L := L) (k := k) (t := t) (ℓ := ℓ) (hS ℓ hdv)
      have s2 := regroup_support (M := M) (L := L) (k := k) (t := t) (ℓ := ℓ') (hS ℓ' hdv')
      rw [s1 (k + 1) _ (fun h => hP h.2) (fun z => g fun μ => ZMod.valMinAbs (n := ℓ) (z μ)),
        s2 (k + 1) _ (fun h => hP' h.2) (fun z => g fun μ => ZMod.valMinAbs (n := ℓ') (z μ))]
      simp
  · rw [regroupFam_ne _ _ _ _ _ _ _ _ hj, regroupFam_ne _ _ _ _ _ _ _ _ hj,
      regroupFam_ne _ _ _ _ _ _ _ _ hj, regroupFam_ne _ _ _ _ _ _ _ _ hj]

open Classical in
/-- **The regrouped activities are observable activities of top scale `k + 1`** (A6-3 (c), over
abstract scale-`k` terms): the five clauses of `ObservableActivities` for `regroupFam M L k t`. -/
theorem regroup_observableActivities {κ' κ c₉ δ B : ℝ} (hk : k ≤ kf)
    (hD : 0 < M * L ^ (k + 1))
    (h4 : ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ → 4 * (M * L ^ (k + 1)) ≤ ℓ)
    (hB0 : 0 ≤ B) (hc₉ : 0 ≤ c₉) (hκ' : 0 ≤ κ')
    (hκ : κ + (L : ℝ) ^ d * Real.log 2 ≤ κ')
    (hBc : B ≤ c₉ / 2 * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))))
    (hS : ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ → ∀ Y,
      ¬ IsPolymer d ℓ (M * L ^ k) Y → ∀ g, t ℓ Y g = t ℓ Y 0)
    (hA : ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ → ∀ Y,
      AnalyticOnNhd ℂ (t ℓ Y) {g : Torus d ℓ → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < 1})
    (hLoc : ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ → ∀ Y (g g' : Torus d ℓ → Fin N → ℂ),
      (∀ y ∈ Y, g y = g' y) → t ℓ Y g = t ℓ Y g')
    (hB : ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ → ∀ Y, IsPolymer d ℓ (M * L ^ k) Y →
      ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
      ‖t ℓ Y g - t ℓ Y 0‖ ≤ B * Real.exp (-κ' * (Y.card : ℝ) / (((M * L ^ k : ℕ) : ℝ)) ^ d))
    (hAgr : ∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], M * L ^ (kf + 1) ∣ ℓ → M * L ^ (kf + 1) ∣ ℓ' →
      ∀ (a : Fin d → ℤ) (B : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → Fin N → ℂ), a ∈ B →
        (∀ y ∈ B, ∀ μ, 4 * |y μ| < (ℓ : ℤ) ∧ 4 * |y μ| < (ℓ' : ℤ)) →
        t ℓ (B.image fun y μ => (y μ : ZMod ℓ))
            (fun z => g fun μ => ZMod.valMinAbs (n := ℓ) (z μ)) -
          t ℓ (B.image fun y μ => (y μ : ZMod ℓ)) 0 =
        t ℓ' (B.image fun y μ => (y μ : ZMod ℓ'))
            (fun z => g fun μ => ZMod.valMinAbs (n := ℓ') (z μ)) -
          t ℓ' (B.image fun y μ => (y μ : ZMod ℓ')) 0) :
    ObservableActivities d N L M κ c₉ δ (k + 1) kf (regroupFam M L k t) := by
  refine ⟨fun ℓ _ hdv => ?_, regroup_agree hk hD h4 hS hAgr⟩
  have hdivk : M * L ^ (k + 1) ∣ M * L ^ (kf + 1) :=
    mul_dvd_mul_left M (pow_dvd_pow L (by omega))
  obtain ⟨K, hK⟩ := hdivk.trans hdv
  have hℓ : ℓ = M * L ^ k * (L * K) := by rw [hK]; ring
  have hKne : K ≠ 0 := by
    rintro rfl; simp at hK; exact NeZero.ne ℓ hK
  have hLne : L ≠ 0 := by
    rintro rfl; simp at hD
  have : NeZero K := ⟨hKne⟩
  have : NeZero (L * K) := ⟨Nat.mul_ne_zero hLne hKne⟩
  have hs : 0 < M * L ^ k := by
    rcases Nat.eq_zero_or_pos (M * L ^ k) with h0 | h0
    · exfalso; rw [h0, zero_mul] at hℓ; exact NeZero.ne ℓ hℓ
    · exact h0
  exact regroup_clauses hℓ hs hB0 hc₉ hκ' hκ hBc (hS ℓ hdv) (hA ℓ hdv) (hLoc ℓ hdv) (hB ℓ hdv)

end Agree

end Balaban.RootFSpine
