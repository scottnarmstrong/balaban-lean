/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusHistGen
public import Balaban.LargeField.Background.TwoTorusBlocks
public import Balaban.LargeField.Background.TwoTorusQuietCubes

/-!
# The new part `χ^new_k` of the domain on two tori

Near a component `Zc`, the generating set of a history, the cubes of `Zc` and their neighbourhoods
correspond on two tori: `margin₁`, `margin₂` (margin of the box near `Zc`), `cube_nbhd_iff`
(neighbourhoods of `Zc` of corresponding sites), `histGen_Ω_iff_lhOmega` (the layers of the
generating set near `Zc` are `lhOmega`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.LargeField RegionHistory

section HistLh

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {k : ℕ}

omit [NeZero M] [NeZero S.L] in
/-- `lhOmega` of the localized history, in terms of cubes. -/
theorem lhOmega_iff_cubes (Hl : RegionHistory S n R k0 K) (hrem : ∀ j, Hl.rem j = ∅) {k : ℕ}
    (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
    (x : Torus S.d (M * n K * S.L ^ K)) (i : ℕ) :
    x ∈ lhOmega (locHist Hl M K (k + 1) Zc) (k + 1) (i + 1) ↔
      (cubeMap n S.L M K (k + 1) x ∉ Zc ∨ cubeMap n S.L M K (i + 1) x ∈ (Hl.step i).Omega) := by
  unfold lhOmega
  rw [locHist_Z_top Hl hrem Zc hZc]
  simp only [Nat.add_sub_cancel, Set.mem_union, Set.mem_compl_iff]
  show (cubeMap n S.L M K (i + 1) x ∈ (Hl.step i).Omega ∧
      cubeMap n S.L M K (k + 1) x ∈ (Zc : Set (Torus S.d (n (k + 1))))) ∨
    ¬ cubeMap n S.L M K (k + 1) x ∈ (Zc : Set (Torus S.d (n (k + 1)))) ↔ _
  simp only [Finset.mem_coe]
  tauto

/-- **Near `Zc`, the layers of the generating set of the history are `lhOmega`** of the
localized history. -/
theorem histGen_Ω_iff_lhOmega (Hl : RegionHistory S n R k0 K) (hrem : ∀ j, Hl.rem j = ∅)
    (hk : k + 1 ≤ K) (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < K → S.Rb ≤ R j)
    (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
    (hω : 2 * ⌊R k⌋₊ + S.L + 11 ≤ S.omega (k + 1)) {r : ℕ} (hr : r ≤ ⌊R k⌋₊ + 2)
    (x : Torus S.d (M * n K * S.L ^ K))
    (hx : cubeMap n S.L M K (k + 1) x ∈ nbhd r (Zc : Set (Torus S.d (n (k + 1))))) (i : ℕ) :
    x ∈ (Hl.histGen (M := M) (K' := K) le_rfl hrem hL hR).Ω (i + 1) ↔
      i + 1 ≤ k + 1 ∧ x ∈ lhOmega (locHist Hl M K (k + 1) Zc) (k + 1) (i + 1) := by
  have hx' : ∃ z ∈ Zc, supDist (cubeMap n S.L M K (k + 1) x) z ≤ r := by
    obtain ⟨z, hz, hd⟩ := mem_nbhd.1 hx
    exact ⟨z, Finset.mem_coe.1 hz, hd⟩
  rw [histGen_mem_near Hl hrem hk le_rfl hL hR Zc hZc hω hr x hx' i]
  exact and_congr_right fun _ => (lhOmega_iff_cubes Hl hrem Zc hZc x i).symm

end HistLh

section Ctx

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {R : ℕ → ℝ}
  {k0 K M N : ℕ} [NeZero M] [NeZero S.L] {k : ℕ} {cc : Fin S.d → ℤ}
  (Hl₁ : RegionHistory S n₁ R k0 K) (Hl₂ : RegionHistory S n₂ R k0 K)
  (hrem₁ : ∀ j, Hl₁.rem j = ∅) (hrem₂ : ∀ j, Hl₂.rem j = ∅) (hk : k + 1 ≤ K)
  (Zc₁ : Finset (Torus S.d (n₁ (k + 1)))) (Zc₂ : Finset (Torus S.d (n₂ (k + 1))))
  (hZc₁ : Zc₁ ∈ comps (S.omega (k + 1)) (Hl₁.F.Zp (k + 1)))
  (hZc₂ : Zc₂ ∈ comps (S.omega (k + 1)) (Hl₂.F.Zp (k + 1)))
  (hH : HistCorr cc (locHist Hl₁ M K (k + 1) Zc₁) (locHist Hl₂ M K (k + 1) Zc₂))
  (hV : SetCorr cc (Vsites R (locHist Hl₁ M K (k + 1) Zc₁) (k + 1))
    (Vsites R (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)))
  (h32₁ : 32 ≤ n₁ (k + 1)) (h32₂ : 32 ≤ n₂ (k + 1))

include hrem₁ hk hZc₁ hV in
/-- The margin of the box at the sites of torus `1` near `Zc₁`. -/
theorem margin₁ {r m : ℕ} (hr : r + m ≤ ⌊R k⌋₊ + 2) (hm : 4 * m ≤ n₁ (k + 1))
    (x : Torus S.d (M * n₁ K * S.L ^ K))
    (hx : cubeMap n₁ S.L M K (k + 1) x ∈ nbhd r (Zc₁ : Set (Torus S.d (n₁ (k + 1))))) :
    InBoxK (m * (S.L ^ (k + 1) * M)) (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) cc
      (liftNear cc x) := by
  have hb := zone_inBox Hl₁ hrem₁ hk Zc₁ hZc₁ hV.1 (r := r) (by omega) x hx
  have := zone_margin Hl₁ hrem₁ hk Zc₁ hZc₁ hV.1 hr hm hb (w := liftNear cc x)
    (by rw [zcast_liftNear]; exact hx)
  exact this

include hrem₂ hk hZc₂ hV in
/-- The margin of the box at the sites of torus `2` near `Zc₂`. -/
theorem margin₂ {r m : ℕ} (hr : r + m ≤ ⌊R k⌋₊ + 2) (hm : 4 * m ≤ n₂ (k + 1))
    (x : Torus S.d (M * n₂ K * S.L ^ K))
    (hx : cubeMap n₂ S.L M K (k + 1) x ∈ nbhd r (Zc₂ : Set (Torus S.d (n₂ (k + 1))))) :
    InBoxK (m * (S.L ^ (k + 1) * M)) (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) cc
      (liftNear cc x) := by
  have hV' : ∀ y ∈ Vsites R (locHist Hl₂ M K (k + 1) Zc₂) (k + 1),
      InBox (M * n₂ K * S.L ^ K) (M * n₁ K * S.L ^ K) cc (liftNear cc y) :=
    fun y hy => (hV.2.1 y hy).symm
  have hb := zone_inBox Hl₂ hrem₂ hk Zc₂ hZc₂ hV' (r := r) (by omega) x hx
  have := zone_margin Hl₂ hrem₂ hk Zc₂ hZc₂ hV' hr hm hb (w := liftNear cc x)
    (by rw [zcast_liftNear]; exact hx)
  exact this.symm

include hrem₁ hrem₂ hk hZc₁ hZc₂ hH h32₁ h32₂ in
/-- The cubes of `Zc₁`, `Zc₂` correspond. -/
theorem ciff_Zc :
    CIff cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ (k + 1) * M) (n₁ (k + 1))
      (n₂ (k + 1)) (Zc₁ : Set (Torus S.d (n₁ (k + 1)))) (Zc₂ : Set (Torus S.d (n₂ (k + 1)))) := by
  have h1 := zcubes_locHist (M := M) Hl₁ hrem₁ hk Zc₁ hZc₁
  have h2 := zcubes_locHist (M := M) Hl₂ hrem₂ hk Zc₂ hZc₂
  have hC := cSetCorr_cubeSub_plain Hl₁.F.hnn Hl₂.F.hnn hk (j := k + 1)
    (by have := h32₁; omega) (by have := h32₂; omega) (hH.Z_corr (k + 1))
  have e1 : {y | CubeSub (S := S) (n := n₁) M K (k + 1) y ((locHist Hl₁ M K (k + 1) Zc₁).Z (k + 1))} =
      (Zc₁ : Set (Torus S.d (n₁ (k + 1)))) := h1
  have e2 : {y | CubeSub (S := S) (n := n₂) M K (k + 1) y ((locHist Hl₂ M K (k + 1) Zc₂).Z (k + 1))} =
      (Zc₂ : Set (Torus S.d (n₂ (k + 1)))) := h2
  rw [e1, e2] at hC
  exact hC.ciff

include hrem₁ hrem₂ hk hZc₁ hZc₂ hH hV h32₁ h32₂ in
/-- **Corresponding sites are near corresponding components together.** -/
theorem cube_nbhd_iff {r : ℕ} (hr : r ≤ 3) (hR6 : 6 ≤ ⌊R k⌋₊) {x₁ : Torus S.d (M * n₁ K * S.L ^ K)}
    {x₂ : Torus S.d (M * n₂ K * S.L ^ K)} (hp : PtCorr cc x₁ x₂) :
    cubeMap n₁ S.L M K (k + 1) x₁ ∈ nbhd r (Zc₁ : Set (Torus S.d (n₁ (k + 1)))) ↔
      cubeMap n₂ S.L M K (k + 1) x₂ ∈ nbhd r (Zc₂ : Set (Torus S.d (n₂ (k + 1)))) := by
  obtain ⟨v, hv, rfl, rfl⟩ := ptCorr_iff_exists.1 hp
  have hP : 0 < S.L ^ (k + 1) * M :=
    Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) _) (Nat.pos_of_ne_zero (NeZero.ne _))
  have hC := ciff_Zc Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH h32₁ h32₂
  rw [cubeMap_zcast Hl₁.F.hnn hk, cubeMap_zcast Hl₂.F.hnn hk]
  constructor
  · intro h
    have hm := margin₁ Hl₁ Hl₂ hrem₁ hk Zc₁ Zc₂ hZc₁ hV (r := r) (m := r) (by omega)
      (by have := h32₁; omega) (zcast _ v) (by rw [cubeMap_zcast Hl₁.F.hnn hk]; exact h)
    rw [hv.liftNear_zcast₁] at hm
    exact (nbhd_iff_of_margin hP hC hm).1 h
  · intro h
    have hm := margin₂ Hl₁ Hl₂ hrem₂ hk Zc₁ Zc₂ hZc₂ hV (r := r) (m := r) (by omega)
      (by have := h32₂; omega) (zcast _ v) (by rw [cubeMap_zcast Hl₂.F.hnn hk]; exact h)
    rw [hv.liftNear_zcast₂] at hm
    exact (nbhd_iff_of_margin hP hC hm).2 h

include hrem₁ hrem₂ hk hZc₁ hZc₂ hH hV h32₁ h32₂ in
/-- **The layers of the generating sets of the two histories agree near the components.** -/
theorem histGen_ptCorr (hL : 2 ≤ S.L) (hR₁ : ∀ j, 1 ≤ j → j < K → S.Rb ≤ R j)
    (hR₂ : ∀ j, 1 ≤ j → j < K → S.Rb ≤ R j) (hω₁ : 2 * ⌊R k⌋₊ + S.L + 11 ≤ S.omega (k + 1))
    (hω₂ : 2 * ⌊R k⌋₊ + S.L + 11 ≤ S.omega (k + 1)) (hR6 : 6 ≤ ⌊R k⌋₊) {r : ℕ} (hr : r ≤ 3)
    {x₁ : Torus S.d (M * n₁ K * S.L ^ K)} {x₂ : Torus S.d (M * n₂ K * S.L ^ K)}
    (hp : PtCorr cc x₁ x₂)
    (hx : cubeMap n₁ S.L M K (k + 1) x₁ ∈ nbhd r (Zc₁ : Set (Torus S.d (n₁ (k + 1))))) (i : ℕ) :
    x₁ ∈ (Hl₁.histGen (M := M) (K' := K) le_rfl hrem₁ hL hR₁).Ω (i + 1) ↔
      x₂ ∈ (Hl₂.histGen (M := M) (K' := K) le_rfl hrem₂ hL hR₂).Ω (i + 1) := by
  have hx₂ := (cube_nbhd_iff Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV h32₁ h32₂ hr hR6 hp).1 hx
  rw [histGen_Ω_iff_lhOmega Hl₁ hrem₁ hk hL hR₁ Zc₁ hZc₁ hω₁ (r := r) (by omega) x₁ hx i,
    histGen_Ω_iff_lhOmega Hl₂ hrem₂ hk hL hR₂ Zc₂ hZc₂ hω₂ (r := r) (by omega) x₂ hx₂ i]
  exact and_congr_right fun _ => hH.lhOmega_iff (k + 1) (i + 1) _ _ hp.1

end Ctx



end Balaban.RootFSpine
