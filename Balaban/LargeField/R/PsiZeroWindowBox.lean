/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroWindowBlock
public import Balaban.LargeField.R.ZeroDomainC
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `Z₀` is exactly a box of `k`-blocks (Lemma III.3.2 (c))

`ZeroDomain.Zzero_in_box` gives `Z₀ ⊆ box b₀ w`.  The source says that `Z₀` *is* one box (the `k`-blocks meeting the box
`Z_{k₂}` of `π_{k₂}`-cubes, `RipeWindow.lin_box_late`).  Here:

* `Zzero_eq_box_of_lin`: if `Z_{k₂}` is the box `box a sd` of cubes (sides `≥ 1`), the blocks meeting it are exactly
  a box `box b₀ w` of blocks, with `1 ≤ w_i ≤ (sd_i M L^{k₂} + L^k - 2)/L^k + 1`;
* `Zzero_eq_box`: for a ripe window, `Z₀ = box b₀ w` with `1 ≤ w_i ≤ D₀ = 3 c₀ + 4`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M]

include H in
/-- **`Z₀` is exactly a box of blocks**, given that `Z_{k₂}` is exactly a box of cubes. -/
theorem Zzero_eq_box_of_lin {k : ℕ} (hkK : k ≤ K) (hk2 : S.kTwo k ≤ k) (Z : H.Comp k)
    {a : Torus S.d (n (S.kTwo k))} {sd : Fin S.d → ℕ}
    (hbox : (H.lin (S.kTwo k) k Z : Set (Torus S.d (n (S.kTwo k)))) = box a sd)
    (hsd : ∀ i, 1 ≤ sd i) :
    ∃ (b0 : Torus S.d (S.M * n k)) (w : Fin S.d → ℕ),
      (∀ i, 1 ≤ w i ∧ w i ≤ (sd i * (S.M * S.L ^ S.kTwo k) + S.L ^ k - 2) / S.L ^ k + 1) ∧
      H.Zzero k Z = box b0 w := by
  have hN : fineSide S n k = S.L ^ k * (S.M * n k) := by unfold fineSide; ring
  have hu : fineSide S n k = (S.M * S.L ^ S.kTwo k) * n (S.kTwo k) := H.F.fineSide_eq hk2 hkK
  have hNpos : 0 < S.L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) k
  set u := S.M * S.L ^ S.kTwo k with hu_def
  refine ⟨fun i => (((a i).val * u / S.L ^ k : ℕ) : ZMod (S.M * n k)),
    fun i => ((a i).val * u + sd i * u - 1) / S.L ^ k - (a i).val * u / S.L ^ k + 1, fun i => ⟨Nat.succ_le_succ (Nat.zero_le _), ?_⟩, ?_⟩
  · exact Nat.succ_le_succ (blockInterval_le (N := S.L ^ k) (s := sd i) (u := u) (β := (a i).val * u) hNpos)
  · ext x
    constructor
    · rintro ⟨s, rfl, hs⟩ i
      have hs' : cubeOf S n k (S.kTwo k) s ∈ box a sd := hbox ▸ hs
      obtain ⟨j, hj, hji⟩ := hs' i
      have hji' : blockCoord u (n (S.kTwo k)) (s i) = a i + (j : ZMod _) := hji
      obtain ⟨j', hj', hx⟩ := blockCoord_interval hN hu (a i) (sd i) j hj (s i) hji'
      exact ⟨j', Nat.lt_succ_of_le hj', hx⟩
    · intro hx
      have key : ∀ i, ∃ p : ZMod (fineSide S n k), (∃ j < sd i, blockCoord u (n (S.kTwo k)) p = a i + (j : ZMod _)) ∧
          blockCoord (S.L ^ k) (S.M * n k) p = x i := by
        intro i
        obtain ⟨j', hj', hxi⟩ := hx i
        obtain ⟨p, hp1, hp2⟩ := exists_site_of_block hN hu (a i) (sd i) (hsd i) j' (Nat.lt_succ_iff.mp hj')
        exact ⟨p, hp1, by rw [hp2, hxi]⟩
      choose p hp1 hp2 using key
      refine ⟨p, funext hp2, ?_⟩
      have : cubeOf S n k (S.kTwo k) p ∈ (H.lin (S.kTwo k) k Z : Set (Torus S.d (n (S.kTwo k)))) := by
        rw [hbox]
        intro i
        exact (hp1 i)
      exact this

/-- **`Z₀` is one box of `k`-blocks** (Lemma III.3.2 (c), exact form): for a ripe window, `Z₀ = box b₀ w` with
`1 ≤ w_i ≤ D₀ = 3 c₀ + 4`. -/
theorem Zzero_eq_box (G : S.Good)
    (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
    (hR0 : 2 * S.c0 + 10 ≤ S.lateR 0) {k : ℕ} (hkK : k ≤ K) {Z : H.Comp k} (W : H.RipeWindow k Z)
    (hk0 : k ≤ k0) (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) :
    ∃ (b0 : Torus S.d (S.M * n k)) (w : Fin S.d → ℕ),
      (∀ i, 1 ≤ w i ∧ w i ≤ 3 * S.c0 + 4) ∧ H.Zzero k Z = box b0 w := by
  have hS := G.ok
  have h3 := H.eight_le_L_mul_lateR k
  obtain ⟨-, hq2, hs2, -, -, hb2, -⟩ := G.lateScale_geom h18 W.core_window.1 W.point.2.1 h3
  have hk2 := hS.kTwo_le k
  obtain ⟨a, sd, hbx, hsd⟩ := W.lin_box_late G h18 hk0 hkK hT le_rfl hk2
  obtain ⟨b0, w, hw, hZ⟩ := H.Zzero_eq_box_of_lin hkK hk2 Z hbx (fun i => (hsd i).1)
  refine ⟨b0, w, fun i => ⟨(hw i).1, (hw i).2.trans ?_⟩, hZ⟩
  have hL := hS.two_le_L
  have hLpos : 0 < S.L := by omega
  have hR8 : 8 * S.M * S.lateR (S.kTwo k) < 9 * S.L ^ S.lateN2 k := by
    have h1 : (8 * (S.L * (S.M * S.lateR (S.kTwo k))) : ℝ) < 9 * S.L * (S.L : ℝ) ^ S.lateN2 k := by
      push_cast at hb2; linarith
    have h2 : 8 * (S.L * (S.M * S.lateR (S.kTwo k))) < 9 * S.L * S.L ^ S.lateN2 k := by
      exact_mod_cast h1
    have h3' : S.L * (8 * S.M * S.lateR (S.kTwo k)) < S.L * (9 * S.L ^ S.lateN2 k) := by
      calc S.L * (8 * S.M * S.lateR (S.kTwo k)) = 8 * (S.L * (S.M * S.lateR (S.kTwo k))) := by ring
        _ < 9 * S.L * S.L ^ S.lateN2 k := h2
        _ = S.L * (9 * S.L ^ S.lateN2 k) := by ring
    exact Nat.lt_of_mul_lt_mul_left h3'
  have hRk2 : 2 * S.c0 + 10 ≤ S.lateR (S.kTwo k) :=
    hR0.trans (hS.lateR_mono (Nat.zero_le _))
  have hcrit := hS.crit_le_lateR hRk2
  have hk : S.L ^ k = S.L ^ S.kTwo k * S.L ^ S.lateN2 k := by
    rw [← pow_add]; congr 1; unfold Setting.lateN2; omega
  rw [hk]
  exact side_arith (c0 := S.c0) (M := S.M) (R := S.lateR (S.kTwo k)) (sd := sd i)
    (Nat.pow_pos hLpos) (Nat.pow_pos hLpos) hR8 ((hsd i).2.trans hcrit)

end RegionHistory

end Balaban.LargeField
