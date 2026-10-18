/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusLift
public import Balaban.Background.BgFieldTwoTorusEquiv

/-!
# Generating sets of two tori that agree on a box

Two generating sets `G₁`, `G₂` on the tori `𝕋_{N₁ L^k}`, `𝕋_{N₂ L^k}` *agree on the box* about `c`
(`GenAgree`) when their layers `Ω_n` have the same integer lifts in the box `InBox` and `Ω₁` lies
in the box with margin `2` (so that `Ω₁` and its collar lie in the box). Then `Ω₁(G₁)` and `Ω₁(G₂)`
correspond (`GenAgree.equiv`), the operator `-Δ + ν + Q* a Q`, the source and the spacing
correspond, and the Def-5 backgrounds agree at corresponding sites (`GenAgree.bgFieldC_eq`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.Background

/-- The image in `𝕋_{m'}` of a point of `𝕋_m`, through the representative nearest `c`. -/
def transp {d m : ℕ} (m' : ℕ) (c : Fin d → ℤ) (x : Torus d m) : Torus d m' :=
  zcast m' (liftNear c x)

section Transp

variable {d m m' : ℕ} {c : Fin d → ℤ}

theorem transp_zcast [NeZero m] {w : Fin d → ℤ} (h : InBox m m' c w) :
    transp m' c (zcast m w) = zcast m' w := by
  unfold transp
  rw [h.liftNear_zcast₁]

end Transp

section Floor

/-- Floor quotients of two integers that are within half a period differ by less than the period
count. -/
theorem abs_ediv_sub_lt {P n w v : ℤ} (hP : 0 < P) (hn : 2 ≤ n) (h : 2 * |w - v| < P * n) :
    |w / P - v / P| < n := by
  have h1 := Int.emod_add_mul_ediv w P
  have h2 := Int.emod_add_mul_ediv v P
  have h3 := Int.emod_nonneg w hP.ne'
  have h4 := Int.emod_lt_of_pos w hP
  have h5 := Int.emod_nonneg v hP.ne'
  have h6 := Int.emod_lt_of_pos v hP
  have h' : -(P * n) < 2 * (w - v) ∧ 2 * (w - v) < P * n := by
    rcases abs_cases (w - v) with ⟨h7, _⟩ | ⟨h7, _⟩ <;> constructor <;> linarith
  rw [abs_lt]
  have hPn : 0 ≤ P * (n - 2) := mul_nonneg hP.le (by omega)
  constructor
  · by_contra hc
    push Not at hc
    have : P * (w / P - v / P) ≤ P * (-n) := mul_le_mul_of_nonneg_left hc hP.le
    nlinarith
  · by_contra hc
    push Not at hc
    have : P * n ≤ P * (w / P - v / P) := mul_le_mul_of_nonneg_left hc hP.le
    nlinarith

theorem zcast_eq_iff_of_abs_lt {d n : ℕ} {a b : Fin d → ℤ} (h : ∀ μ, |a μ - b μ| < n) :
    zcast n a = zcast n b ↔ a = b := by
  constructor
  · intro hab
    funext μ
    obtain ⟨t, ht⟩ := (zcast_eq_iff n a b).1 hab μ
    have h1 := h μ
    have hn : 0 < (n : ℤ) := lt_of_le_of_lt (abs_nonneg _) h1
    have h2 : t = 0 := by
      by_contra ht0
      have : (n : ℤ) ≤ |a μ - b μ| := by
        rw [ht, abs_mul, abs_of_pos hn]
        have := Int.one_le_abs ht0
        nlinarith
      omega
    rw [h2] at ht
    omega
  · rintro rfl; rfl

end Floor

section Shift

variable {d m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂] {c : Fin d → ℤ}

theorem transp_shift_iff {x y : Torus d m₁} (hx : InBoxK 1 m₁ m₂ c (liftNear c x))
    (hy : InBox m₁ m₂ c (liftNear c y)) (μ : Fin d) :
    transp m₂ c y = transp m₂ c x + Pi.single μ 1 ↔ y = x + Pi.single μ 1 := by
  have h1 := zcast_add_single_iff (m := m₂) (fun u u' hu hu' => hu.zcast₂_inj hu') hx hy μ
  have h2 := zcast_add_single_iff (m := m₁) (fun u u' hu hu' => hu.zcast₁_inj hu') hx hy μ
  rw [zcast_liftNear, zcast_liftNear] at h2
  exact h1.trans h2.symm

theorem transp_shift_iff' {x y : Torus d m₁} (hx : InBoxK 1 m₁ m₂ c (liftNear c x))
    (hy : InBox m₁ m₂ c (liftNear c y)) (μ : Fin d) :
    transp m₂ c y = transp m₂ c x - Pi.single μ 1 ↔ y = x - Pi.single μ 1 := by
  have h1 := zcast_sub_single_iff (m := m₂) (fun u u' hu hu' => hu.zcast₂_inj hu') hx hy μ
  have h2 := zcast_sub_single_iff (m := m₁) (fun u u' hu hu' => hu.zcast₁_inj hu') hx hy μ
  rw [zcast_liftNear, zcast_liftNear] at h2
  exact h1.trans h2.symm

end Shift

section GenAgree

variable {d L N₁ N₂ k : ℕ} [NeZero N₁] [NeZero N₂] [NeZero L] {ϱ₁ ϱ₂ : ℝ}

/-- The generating sets `G₁`, `G₂` agree on the box about `c`. -/
structure GenAgree (G₁ : GeneratingSet d L N₁ k ϱ₁) (G₂ : GeneratingSet d L N₂ k ϱ₂)
    (c : Fin d → ℤ) : Prop where
  supp₁ : ∀ x ∈ G₁.Ω 1, InBoxK 2 (N₁ * L ^ k) (N₂ * L ^ k) c (liftNear c x)
  supp₂ : ∀ x ∈ G₂.Ω 1, InBoxK 2 (N₁ * L ^ k) (N₂ * L ^ k) c (liftNear c x)
  agree : ∀ n, 1 ≤ n → n ≤ k + 1 → ∀ w, InBox (N₁ * L ^ k) (N₂ * L ^ k) c w →
    (zcast (N₁ * L ^ k) w ∈ G₁.Ω n ↔ zcast (N₂ * L ^ k) w ∈ G₂.Ω n)

variable {G₁ : GeneratingSet d L N₁ k ϱ₁} {G₂ : GeneratingSet d L N₂ k ϱ₂} {c : Fin d → ℤ}

theorem GenAgree.symm (h : GenAgree G₁ G₂ c) : GenAgree G₂ G₁ c where
  supp₁ x hx := (h.supp₂ x hx).symm
  supp₂ x hx := (h.supp₁ x hx).symm
  agree n h1 h2 w hw := (h.agree n h1 h2 w hw.symm).symm

theorem GenAgree.mem_iff (h : GenAgree G₁ G₂ c) {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ k + 1)
    {x : Torus d (N₁ * L ^ k)} (hx : InBox (N₁ * L ^ k) (N₂ * L ^ k) c (liftNear c x)) :
    x ∈ G₁.Ω n ↔ transp (N₂ * L ^ k) c x ∈ G₂.Ω n := by
  have := h.agree n h1 h2 (liftNear c x) hx
  rwa [zcast_liftNear] at this

/-- The correspondence of the regions `Ω₁`. -/
def GenAgree.equiv (h : GenAgree G₁ G₂ c) : G₁.Ω 1 ≃ G₂.Ω 1 where
  toFun x := ⟨transp (N₂ * L ^ k) c x.1,
    (h.mem_iff le_rfl (by omega) (h.supp₁ x.1 x.2).inBox).1 x.2⟩
  invFun y := ⟨transp (N₁ * L ^ k) c y.1,
    (h.symm.mem_iff le_rfl (by omega) (h.symm.supp₁ y.1 y.2).inBox).1 y.2⟩
  left_inv x := by
    apply Subtype.ext
    simp only [transp]
    rw [(h.supp₁ x.1 x.2).inBox.liftNear_zcast₂, zcast_liftNear]
  right_inv y := by
    apply Subtype.ext
    simp only [transp]
    rw [(h.symm.supp₁ y.1 y.2).inBox.liftNear_zcast₂, zcast_liftNear]

theorem GenAgree.equiv_coe (h : GenAgree G₁ G₂ c) (x : G₁.Ω 1) :
    ((h.equiv x : G₂.Ω 1) : Torus d (N₂ * L ^ k)) = zcast (N₂ * L ^ k) (liftNear c x.1) := rfl

theorem GenAgree.layer_iff (h : GenAgree G₁ G₂ c) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k)
    {x : Torus d (N₁ * L ^ k)} (hx : InBox (N₁ * L ^ k) (N₂ * L ^ k) c (liftNear c x)) :
    x ∈ G₁.layer j ↔ transp (N₂ * L ^ k) c x ∈ G₂.layer j := by
  rw [G₁.mem_layer, G₂.mem_layer, h.mem_iff h1 (by omega) hx, h.mem_iff (by omega) (by omega) hx]

theorem GenAgree.layerIndex_eq (h : GenAgree G₁ G₂ c) (x : G₁.Ω 1) :
    G₂.layerIndex ((h.equiv x : G₂.Ω 1) : Torus d (N₂ * L ^ k)) = G₁.layerIndex x.1 := by
  obtain ⟨hn1, hnk, hxl⟩ := G₁.layerIndex_spec x.2
  exact G₂.layerIndex_eq hn1 hnk ((h.layer_iff hn1 hnk (h.supp₁ x.1 x.2).inBox).1 hxl)

theorem GenAgree.spacing_eq (h : GenAgree G₁ G₂ c) (x : G₁.Ω 1) :
    G₂.spacing ((h.equiv x : G₂.Ω 1) : Torus d (N₂ * L ^ k)) = G₁.spacing x.1 := by
  unfold GeneratingSet.spacing
  rw [h.layerIndex_eq]

/-! ### Shifts and blocks of lifts -/

theorem jBlock_zcast {N : ℕ} [NeZero N] {j : ℕ} (hj : j ≤ k) (w : Fin d → ℤ) :
    jBlock d L N k j (zcast (N * L ^ k) w) =
      zcast (N * L ^ (k - j)) (fun μ => w μ / ((L ^ j : ℕ) : ℤ)) :=
  blockMap_zcast (side_eq hj) (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j) w

theorem jBlock_zcast_iff {N m' : ℕ} [NeZero N] (hN : 2 ≤ N) {j : ℕ} (hj : j ≤ k) {c w v : Fin d → ℤ}
    (hw : InBox (N * L ^ k) m' c w) (hv : InBox (N * L ^ k) m' c v) :
    jBlock d L N k j (zcast (N * L ^ k) w) = jBlock d L N k j (zcast (N * L ^ k) v) ↔
      (fun μ => w μ / ((L ^ j : ℕ) : ℤ)) = (fun μ => v μ / ((L ^ j : ℕ) : ℤ)) := by
  rw [jBlock_zcast hj, jBlock_zcast hj]
  refine zcast_eq_iff_of_abs_lt fun μ => ?_
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hP : (0 : ℤ) < ((L ^ j : ℕ) : ℤ) := by exact_mod_cast pow_pos hL j
  have hn : (2 : ℤ) ≤ ((N * L ^ (k - j) : ℕ) : ℤ) := by
    have : 2 ≤ N * L ^ (k - j) := le_trans hN (Nat.le_mul_of_pos_right _ (pow_pos hL _))
    exact_mod_cast this
  have h1 := (two_abs_sub_lt hw hv μ).1
  have h2 : ((L ^ j : ℕ) : ℤ) * ((N * L ^ (k - j) : ℕ) : ℤ) = ((N * L ^ k : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, ← side_eq hj]
  have := abs_ediv_sub_lt hP hn (by rw [h2]; exact h1)
  exact_mod_cast this

/-! ### The operator, the source and the collar -/

theorem GenAgree.eq_iff (h : GenAgree G₁ G₂ c) (x y : G₁.Ω 1) :
    ((h.equiv x : G₂.Ω 1) : Torus d (N₂ * L ^ k)) = ((h.equiv y : G₂.Ω 1) : Torus d (N₂ * L ^ k)) ↔
      x.1 = y.1 := by
  rw [Subtype.coe_inj, h.equiv.apply_eq_iff_eq]
  exact Subtype.ext_iff

theorem GenAgree.shift_iff (h : GenAgree G₁ G₂ c) (x y : G₁.Ω 1) (μ : Fin d) :
    ((h.equiv y : G₂.Ω 1) : Torus d (N₂ * L ^ k)) =
        ((h.equiv x : G₂.Ω 1) : Torus d (N₂ * L ^ k)) + Pi.single μ 1 ↔
      y.1 = x.1 + Pi.single μ 1 :=
  transp_shift_iff ((h.supp₁ x.1 x.2).mono (by omega)) (h.supp₁ y.1 y.2).inBox μ

theorem GenAgree.shift_iff' (h : GenAgree G₁ G₂ c) (x y : G₁.Ω 1) (μ : Fin d) :
    ((h.equiv y : G₂.Ω 1) : Torus d (N₂ * L ^ k)) =
        ((h.equiv x : G₂.Ω 1) : Torus d (N₂ * L ^ k)) - Pi.single μ 1 ↔
      y.1 = x.1 - Pi.single μ 1 :=
  transp_shift_iff' ((h.supp₁ x.1 x.2).mono (by omega)) (h.supp₁ y.1 y.2).inBox μ

theorem GenAgree.jBlock_iff (h : GenAgree G₁ G₂ c) (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂) {j : ℕ}
    (hj : j ≤ k) (x y : G₁.Ω 1) :
    jBlock d L N₂ k j ((h.equiv x : G₂.Ω 1) : Torus d (N₂ * L ^ k)) =
        jBlock d L N₂ k j ((h.equiv y : G₂.Ω 1) : Torus d (N₂ * L ^ k)) ↔
      jBlock d L N₁ k j x.1 = jBlock d L N₁ k j y.1 := by
  have hx := (h.supp₁ x.1 x.2).inBox
  have hy := (h.supp₁ y.1 y.2).inBox
  rw [h.equiv_coe, h.equiv_coe]
  conv_rhs => rw [← zcast_liftNear (c := c) x.1, ← zcast_liftNear (c := c) y.1]
  rw [jBlock_zcast_iff hN₂ hj hx.symm hy.symm, jBlock_zcast_iff hN₁ hj hx hy]

theorem GenAgree.fullMatrix_eq (h : GenAgree G₁ G₂ c) (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂) (a : ℕ → ℝ)
    (ν : ℝ) (x y : G₁.Ω 1) :
    fullMatrix G₂ a ν ((h.equiv x : G₂.Ω 1) : Torus d (N₂ * L ^ k))
        ((h.equiv y : G₂.Ω 1) : Torus d (N₂ * L ^ k)) = fullMatrix G₁ a ν x.1 y.1 := by
  have hlap : latticeLaplacian d (N₂ * L ^ k) ν ((h.equiv x : G₂.Ω 1) : Torus d (N₂ * L ^ k))
      ((h.equiv y : G₂.Ω 1) : Torus d (N₂ * L ^ k)) = latticeLaplacian d (N₁ * L ^ k) ν x.1 y.1 := by
    simp only [latticeLaplacian, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.sum_apply, Matrix.add_apply, Matrix.transpose_apply, shiftMatrix, smul_eq_mul,
      h.eq_iff, h.shift_iff]
  have havg : avgMatrix G₂ a ((h.equiv x : G₂.Ω 1) : Torus d (N₂ * L ^ k))
      ((h.equiv y : G₂.Ω 1) : Torus d (N₂ * L ^ k)) = avgMatrix G₁ a x.1 y.1 := by
    unfold avgMatrix
    simp only [Matrix.sum_apply, Matrix.smul_apply]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
    simp only [layerProjMatrix, blockProjMatrix, smul_eq_mul]
    have hb := h.jBlock_iff hN₁ hN₂ hj2 x y
    unfold jBlock at hb
    have hlx : x.1 ∈ G₁.layer j ↔ ((h.equiv x : G₂.Ω 1) : Torus d (N₂ * L ^ k)) ∈ G₂.layer j :=
      h.layer_iff hj1 hj2 (h.supp₁ x.1 x.2).inBox
    have hly : y.1 ∈ G₁.layer j ↔ ((h.equiv y : G₂.Ω 1) : Torus d (N₂ * L ^ k)) ∈ G₂.layer j :=
      h.layer_iff hj1 hj2 (h.supp₁ y.1 y.2).inBox
    simp only [hb, ← hlx, ← hly]
  unfold fullMatrix
  rw [Matrix.add_apply, Matrix.add_apply, hlap, havg]

theorem GenAgree.collar_imp (h : GenAgree G₁ G₂ c) {v : Fin d → ℤ}
    (hv : InBoxK 1 (N₁ * L ^ k) (N₂ * L ^ k) c v) :
    zcast (N₁ * L ^ k) v ∈ collar G₁ → zcast (N₂ * L ^ k) v ∈ collar G₂ := by
  intro hc
  obtain ⟨hnot, z, hz, hadj⟩ := (mem_collar G₁).1 hc
  have hu := h.supp₁ z hz
  have hu1 : InBoxK 1 (N₁ * L ^ k) (N₂ * L ^ k) c (liftNear c z) := hu.mono (by omega)
  have hzu : z = zcast (N₁ * L ^ k) (liftNear c z) := (zcast_liftNear z).symm
  refine (mem_collar G₂).2 ⟨?_, zcast (N₂ * L ^ k) (liftNear c z), ?_, ?_⟩
  · intro hmem
    exact hnot ((h.agree 1 le_rfl (by omega) v hv.inBox).2 hmem)
  · exact (h.agree 1 le_rfl (by omega) _ hu.inBox).1 (by rw [← hzu]; exact hz)
  · obtain ⟨μ, hμ | hμ⟩ := hadj
    · refine ⟨μ, Or.inl ?_⟩
      rw [hzu] at hμ
      have := (zcast_add_single_iff (m := N₁ * L ^ k) (fun u u' hu hu' => hu.zcast₁_inj hu') hu1
        hv.inBox μ).1 hμ
      rw [this, zcast_add_single]
    · refine ⟨μ, Or.inr ?_⟩
      rw [hzu] at hμ
      have := (zcast_add_single_iff (m := N₁ * L ^ k) (fun u u' hu hu' => hu.zcast₁_inj hu') hv
        hu.inBox μ).1 hμ
      rw [this, zcast_add_single]

theorem GenAgree.collar_iff (h : GenAgree G₁ G₂ c) {v : Fin d → ℤ}
    (hv : InBoxK 1 (N₁ * L ^ k) (N₂ * L ^ k) c v) :
    zcast (N₁ * L ^ k) v ∈ collar G₁ ↔ zcast (N₂ * L ^ k) v ∈ collar G₂ :=
  ⟨h.collar_imp hv, h.symm.collar_imp hv.symm⟩

theorem GenAgree.dataSites_iff (h : GenAgree G₁ G₂ c) {v : Fin d → ℤ}
    (hv : InBoxK 1 (N₁ * L ^ k) (N₂ * L ^ k) c v) :
    zcast (N₁ * L ^ k) v ∈ dataSites G₁ ↔ zcast (N₂ * L ^ k) v ∈ dataSites G₂ := by
  rw [mem_dataSites, mem_dataSites, h.collar_iff hv, h.agree 1 le_rfl (by omega) v hv.inBox]

/-- The data of two backgrounds agree on the box: `Ψ` on the data sites and `h̃` on `Ω₁`. -/
structure DataAgree {N : ℕ} (G₁ : GeneratingSet d L N₁ k ϱ₁) (G₂ : GeneratingSet d L N₂ k ϱ₂)
    (c : Fin d → ℤ) (D₁ : BgData G₁ N) (D₂ : BgData G₂ N) : Prop where
  psi : ∀ w, InBox (N₁ * L ^ k) (N₂ * L ^ k) c w → zcast (N₁ * L ^ k) w ∈ dataSites G₁ →
    ∀ i, D₁.Ψ (zcast (N₁ * L ^ k) w) i = D₂.Ψ (zcast (N₂ * L ^ k) w) i
  h : ∀ w, InBox (N₁ * L ^ k) (N₂ * L ^ k) c w → zcast (N₁ * L ^ k) w ∈ G₁.Ω 1 →
    ∀ i, D₁.h (zcast (N₁ * L ^ k) w) i = D₂.h (zcast (N₂ * L ^ k) w) i

variable {N : ℕ} {D₁ : BgData G₁ N} {D₂ : BgData G₂ N}

theorem GenAgree.psi_at_Ω (hA : GenAgree G₁ G₂ c) (hD : DataAgree G₁ G₂ c D₁ D₂) (x : G₁.Ω 1)
    (i : Fin N) :
    D₂.Ψ ((hA.equiv x : G₂.Ω 1) : Torus d (N₂ * L ^ k)) i = D₁.Ψ x.1 i := by
  have hx := (hA.supp₁ x.1 x.2).inBox
  have := hD.psi _ hx (by rw [zcast_liftNear]; exact (mem_dataSites G₁).2 (Or.inl x.2)) i
  rw [zcast_liftNear] at this
  rw [hA.equiv_coe]
  exact this.symm

theorem GenAgree.h_at_Ω (hA : GenAgree G₁ G₂ c) (hD : DataAgree G₁ G₂ c D₁ D₂) (x : G₁.Ω 1)
    (i : Fin N) :
    D₂.h ((hA.equiv x : G₂.Ω 1) : Torus d (N₂ * L ^ k)) i = D₁.h x.1 i := by
  have hx := (hA.supp₁ x.1 x.2).inBox
  have := hD.h _ hx (by rw [zcast_liftNear]; exact x.2) i
  rw [zcast_liftNear] at this
  rw [hA.equiv_coe]
  exact this.symm

theorem GenAgree.collar_term_eq (hA : GenAgree G₁ G₂ c) (hD : DataAgree G₁ G₂ c D₁ D₂)
    {v : Fin d → ℤ} (hv : InBoxK 1 (N₁ * L ^ k) (N₂ * L ^ k) c v) (i : Fin N) :
    (if zcast (N₂ * L ^ k) v ∈ collar G₂ then D₂.Ψ (zcast (N₂ * L ^ k) v) i else 0) =
      if zcast (N₁ * L ^ k) v ∈ collar G₁ then D₁.Ψ (zcast (N₁ * L ^ k) v) i else 0 := by
  by_cases hcol : zcast (N₁ * L ^ k) v ∈ collar G₁
  · have hcol2 := hA.collar_imp hv hcol
    simp only [hcol, hcol2, ↓reduceIte]
    exact (hD.psi v hv.inBox ((mem_dataSites G₁).2 (Or.inr hcol)) i).symm
  · have hcol2 : zcast (N₂ * L ^ k) v ∉ collar G₂ := fun h2 => hcol ((hA.collar_iff hv).2 h2)
    simp only [hcol, hcol2, ↓reduceIte]

theorem GenAgree.source_eq (hA : GenAgree G₁ G₂ c) (hD : DataAgree G₁ G₂ c D₁ D₂) (a : ℕ → ℝ)
    (ν : ℝ) (x : G₁.Ω 1) (i : Fin N) :
    source G₂ a ν D₂ (hA.equiv x, i) = source G₁ a ν D₁ (x, i) := by
  unfold source qStar boundaryTerm
  have hw := hA.supp₁ x.1 x.2
  have hlayer := hA.layerIndex_eq x
  simp only [hlayer, hA.psi_at_Ω hD, hA.h_at_Ω hD]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hx1 : x.1 = zcast (N₁ * L ^ k) (liftNear c x.1) := (zcast_liftNear x.1).symm
  have hx2 : ((hA.equiv x : G₂.Ω 1) : Torus d (N₂ * L ^ k)) =
      zcast (N₂ * L ^ k) (liftNear c x.1) := hA.equiv_coe x
  have hp : InBoxK 1 (N₁ * L ^ k) (N₂ * L ^ k) c (liftNear c x.1 + Pi.single μ 1) :=
    hw.add_single μ
  have hm : InBoxK 1 (N₁ * L ^ k) (N₂ * L ^ k) c (liftNear c x.1 - Pi.single μ 1) :=
    hw.sub_single μ
  have e1 : x.1 + Pi.single μ 1 = zcast (N₁ * L ^ k) (liftNear c x.1 + Pi.single μ 1) := by
    rw [zcast_add_single, ← hx1]
  have e2 : x.1 - Pi.single μ 1 = zcast (N₁ * L ^ k) (liftNear c x.1 - Pi.single μ 1) := by
    rw [zcast_sub_single, ← hx1]
  have e3 : ((hA.equiv x : G₂.Ω 1) : Torus d (N₂ * L ^ k)) + Pi.single μ 1 =
      zcast (N₂ * L ^ k) (liftNear c x.1 + Pi.single μ 1) := by
    rw [zcast_add_single, ← hx2]
  have e4 : ((hA.equiv x : G₂.Ω 1) : Torus d (N₂ * L ^ k)) - Pi.single μ 1 =
      zcast (N₂ * L ^ k) (liftNear c x.1 - Pi.single μ 1) := by
    rw [zcast_sub_single, ← hx2]
  simp only [e1, e2, e3, e4]
  rw [hA.collar_term_eq hD hp i, hA.collar_term_eq hD hm i]

/-- **The Def-5 background of two tori agrees on the box**: if the generating sets and the data
agree on the box, then `bgFieldC` has the same value at corresponding sites of `Ω₁`. -/
theorem GenAgree.bgFieldC_eq (hA : GenAgree G₁ G₂ c) (hD : DataAgree G₁ G₂ c D₁ D₂)
    (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂) (a : ℕ → ℝ) (ν c₀ : ℝ) (x : G₁.Ω 1) (i : Fin N) :
    bgFieldC G₂ a ν c₀ D₂ (hA.equiv x, i) = bgFieldC G₁ a ν c₀ D₁ (x, i) :=
  bgFieldC_equiv hA.equiv (fun x y => hA.fullMatrix_eq hN₁ hN₂ a ν x y)
    (fun x i => hA.source_eq hD a ν x i) (fun x => hA.spacing_eq x) x i

end GenAgree

end Balaban.RootFSpine
