/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroWindowSpec
public import Balaban.LargeField.R.PsiZeroWindowGeom
public import Balaban.LargeField.R.WindowGenGlue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `PsiZeroSpec` for the ripe window (Lemma III.3.3 with the geometry of Lemma III.3.2)

For a ripe component `Z` with its localization `𝔹_k` (`locGen`), the box `Z₀ = box b₀ w` of `k`-blocks
(`exists_window_box`), a generating set `𝔹_k(U_k)` (`bdry`) and the fine set `U^∼_k` (`Unb`):

* the blocks of `Z₀ ∪ shellOut Z₀` lie over `Ω_k(𝔹_k(U_k))` (they lie in `Z`, `Z ⊆ U_k = Ω_k(𝔹_k(U_k))`);
* the terminal blocks (`Ω_k ∩ Z` of the localization) lie off `Z₀` (Lemma III.3.2 (d));
* the blocks of `Z` lie in `U^∼_k` and the blocks of the data sites of `𝔹_k(U_k)` lie in `U^∼_k`.

`psiZeroSpec_ripe_of_input`: the source facts about `𝔹_k(U_k)` and `U^∼_k` that the history does not construct are
the three premises `hbdryZ` (`U_k ⊇ Z_k` is the top layer of `𝔹_k(U_k)`), `hZU` (`Z_k ⊆ U^∼_k`), `hdU`
(`Ω₁ ∪ C(Ω₁)` of `𝔹_k(U_k)` lies in `U^∼_k`, Lemma II.2.3 (c)); the only non-source premise is `PsiZeroInput`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

/-- The `k`-blocks meeting a fine set `U`. -/
def blocksMeeting {d L N₀ k : ℕ} (U : Set (Torus d (N₀ * L ^ k))) : Set (Torus d (N₀ * L ^ (k - k))) :=
  {y | ∃ x ∈ U, jBlock d L N₀ k k x = y}

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} [NeZero S.L] [NeZero S.M] {k : ℕ}

/-- **`PsiZeroSpec` for the ripe window, from the cited expansion estimate.**  There is a box `Z₀ = box b₀ w` of
`k`-blocks (`Z₀` of Lemma III.3.1, `1 ≤ w_i ≤ D₀ = 3 c₀ + 4`, `jBlock x ∈ box b₀ w ↔ the k-block of x lies in
Zzero`) such that, for every `PsiZeroInput` for it, the solution `ψ⁰_k` of (2.34) satisfies `PsiZeroSpec` for the
localization `𝔹_k`, `𝔹_k(U_k)` and the fine set `Z_k`, and `ψ⁰_k = ψ_k` off `Z₀`. -/
theorem psiZeroSpec_ripe_of_input (G : S.Good)
    (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
    (hR0 : 2 * S.c0 + 10 ≤ S.lateR 0) (hkK : k ≤ K) {Z : H.Comp k} (W : H.RipeWindow k Z)
    (hk0 : k ≤ k0) (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hk : 1 ≤ k)
    (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) (hL : 2 ≤ S.L) (hR' : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j)
    (hd : 2 ≤ S.d) (hn : 3 * S.c0 + 6 ≤ S.M * n k) {ϱ' : ℝ} (bdry : GeneratingSet S.d S.L (S.M * n k) k ϱ')
    (a : ℕ → ℝ) {N : ℕ} [NeZero N] (Unb : Set (Torus S.d (S.M * n k * S.L ^ k)))
    (hbdryZ : ∀ x ∈ H.locFine Z S.M k, x ∈ bdry.Ω k) (hZU : ∀ x ∈ H.locFine Z S.M k, x ∈ Unb)
    (hdU : ∀ x ∈ dataSites bdry, x ∈ Unb) (Hbg : BgHyp S.d S.L k ϱ' a 0) :
    ∃ (b0 : Torus S.d (S.M * n k * S.L ^ (k - k))) (w : Fin S.d → ℕ),
      (∀ i, 1 ≤ w i ∧ w i ≤ 3 * S.c0 + 4) ∧
      (∀ x : Torus S.d (S.M * n k * S.L ^ k), (jBlock S.d S.L (S.M * n k) k k x ∈ box b0 w ↔
        blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k Z)) ∧
      (PsiZeroInput (N := N) bdry a b0 w (blocksMeeting Unb) →
        ∃ K c11 : ℝ, 0 < K ∧ 0 < c11 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ c11 →
          ∀ ψ : BlockV S.d S.L (S.M * n k) k → EuclideanSpace ℝ (Fin N),
            BlockTube (blocksMeeting Unb \ box b0 w) δ (fun z i => ψ ⟨k, z⟩ i) →
            ∃ ψ0 : BlockV S.d S.L (S.M * n k) k → EuclideanSpace ℝ (Fin N),
              PsiZeroSpec (H.locGen Z S.M hkK hL hR') bdry (H.locFine Z S.M k) (K * δ) ψ ψ0 ∧
                ∀ z, z ∉ box b0 w → ψ0 ⟨k, z⟩ = ψ ⟨k, z⟩) := by
  have hS := G.ok
  have h3 := H.eight_le_L_mul_lateR k
  obtain ⟨b0, w, hw, hbx⟩ := H.exists_window_box G h18 hR0 hkK W hk0 hT
  refine ⟨b0, w, hw, hbx, fun inp => ?_⟩
  have hgeom : ∀ x : Torus S.d (S.M * n k * S.L ^ k),
      jBlock S.d S.L (S.M * n k) k k x ∈ box b0 w ∪ shellOut (box b0 w) → x ∈ H.locFine Z S.M k :=
    fun x hx => H.mem_locFine_of_mem_box_shell hS h3 hR hkK hk Z hbx hx
  have hsurj : ∀ y : Torus S.d (S.M * n k * S.L ^ (k - k)),
      ∃ x : Torus S.d (S.M * n k * S.L ^ k), jBlock S.d S.L (S.M * n k) k k x = y := fun y =>
    Balaban.exists_blockMap_eq (fine_eq_block S.L (S.M * n k) k)
      (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) k) y
  refine psiZeroSpec_of_input_blockTube bdry a (H.locGen Z S.M hkK hL hR') hd hk b0 w (fun i => (hw i).1)
    (fun i => (hw i).2) (by simpa using (by omega : 3 * S.c0 + 4 + 2 ≤ S.M * n k)) ?_ ?_ ?_
    (H.locFine Z S.M k) ?_ ?_ Hbg inp
  · intro y hy
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨x, hZU x (hgeom x hy), rfl⟩
  · intro x hx
    exact hbdryZ x (hgeom x hx)
  · intro x hx
    exact ⟨x, hdU x hx, rfl⟩
  · intro x hx
    exact ⟨x, hZU x hx, rfl⟩
  · intro z hz hzb
    obtain ⟨x0, hx0⟩ := hsurj z
    have hx0s : x0 ∈ BlockV.sites (⟨k, z⟩ : BlockV S.d S.L (S.M * n k) k) := hx0
    have htop := (hz.2 x0 hx0s).1
    exact H.blockMap_not_mem_Zzero_of_top hR hkK hk hL hR' Z htop ((hbx x0).1 (hx0 ▸ hzb))

/-- **`hoff` of `deltaPsi_le_pieces` for the ripe window** (P7 (2.44), `ψ⁰_k = ψ_k` off `Z₀`): the `k`-block of a site
off `Z` lies off `Z₀`, so the solution equals `ψ` there. -/
theorem psiZero_eq_off_ripe (hS : S.Ok) (h3 : 8 ≤ S.L * S.lateR k) (hR : ∀ j, R j = S.Rb * S.lam j ^ 2)
    (hkK : k ≤ K) (hk : 1 ≤ k) (Z : H.Comp k) {b0 : Torus S.d (S.M * n k * S.L ^ (k - k))}
    {w : Fin S.d → ℕ}
    (hbx : ∀ x : Torus S.d (S.M * n k * S.L ^ k), (jBlock S.d S.L (S.M * n k) k k x ∈ box b0 w ↔
        blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k Z))
    {ϱ : ℝ} (Wp : WindowPieces S.d S.L (S.M * n k) k ϱ)
    (hZ : (Wp.Z : Set (Torus S.d (S.M * n k * S.L ^ k))) = H.locFine Z S.M k)
    {N : ℕ} {ψ ψ0 : BlockV S.d S.L (S.M * n k) k → EuclideanSpace ℝ (Fin N)}
    (hoff : ∀ z, z ∉ box b0 w → ψ0 ⟨k, z⟩ = ψ ⟨k, z⟩) :
    ∀ x ∈ Wp.Unb, x ∉ Wp.Z →
      ψ0 ⟨k, jBlock S.d S.L (S.M * n k) k k x⟩ = ψ ⟨k, jBlock S.d S.L (S.M * n k) k k x⟩ := by
  intro x _ hxZ
  refine hoff _ fun hb => hxZ ?_
  have : x ∈ H.locFine Z S.M k :=
    H.mem_locFine_of_mem_box_shell hS h3 hR hkK hk Z hbx (Or.inl hb)
  exact_mod_cast hZ ▸ this

end RegionHistory

end Balaban.LargeField
