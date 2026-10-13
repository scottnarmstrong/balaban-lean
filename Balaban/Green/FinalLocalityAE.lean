/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTaggedLocal
public import Balaban.Green.FinalTaggedRow

/-!
# The locality hypothesis of Lemma AE for the last-integral families (W538)

This construction is proposed in FINALFAM; the papers print no formula (Roland question 18 pending).

Lemma AE (`Balaban.Localization.abstract_expansion`) asks for `LocalityAE P Y F` with patches
`P : ι → Set Ω`, regions `Y : Finset ι → Set Ω` and `F : (Ω → E) → (ι → ℂ) → ℂ`.  Here
`ι = MacIdx d N₀ M` (the cells), `Ω = L1Torus d N₀ × L1Torus d N₀` (pairs of sites), `E = ℂ`, a
datum `u : Ω → ℂ` is read as the matrix `U x y = u (x, y)`, and

* `P i = macBox i ×ˢ macBox i`,  `Y C = macRegion C ×ˢ macRegion C`.

Since `macBox i ⊆ macRegion C` for `i ∈ C`, the inclusion `P i ⊆ Y C` always holds for `i ∈ C`;
the hypothesis `s i = s' i` of `LocalityAE` therefore forces `s = s'` for parameters supported on
`C`, and the locality reduces to the landed equal-parameter statement
`taggedGfin_congr_of_agree_on_region`.

* `localityAE_taggedGfin`, `localityAE_taggedCfinU`: `LocalityAE` for every entry of the tagged
  family and of its Stieltjes integral.
* `isConnectedFamily_macBox`: with this `P`, `Y` every family is connected in the sense of
  `IsConnectedFamily`, so the vanishing `coef_eq_zero_of_not_connected` is vacuous here; the
  content of the locality is the congruence of coefficients in the datum on `Y C`.
* `coef_taggedGfin_congr_of_agree`, `coef_taggedCfinU_congr_of_agree`: the congruence of
  coefficients obtained from `coef_congr_of_agree`.
* `abstract_expansion_taggedGfin_final`, `abstract_expansion_taggedCfin_final`: Lemma AE applied
  to the entries of the final families (the datum is the fixed final operator, see the doc-strings).
-/

@[expose] public section

open Finset Matrix

namespace Balaban.Green

open Balaban.Localization

variable {d N₀ M : ℕ} [NeZero N₀]

/-- Locality of any matrix-dependent family that is local at equal parameters: the two-parameter
form `LocalityAE` with `P i = macBox i × macBox i`, `Y C = macRegion C × macRegion C`. -/
theorem localityAE_macBox_of_agree
    (G : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ → (MacIdx d N₀ M → ℂ) → ℂ)
    (hG : ∀ (U U' : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (C : Finset (MacIdx d N₀ M)),
      (∀ x ∈ macRegion d N₀ M C, ∀ y ∈ macRegion d N₀ M C, U x y = U' x y) →
      ∀ s ∈ supportedOn C, G U s = G U' s) :
    LocalityAE (fun i : MacIdx d N₀ M => macBox d N₀ M i ×ˢ macBox d N₀ M i)
      (fun C => macRegion d N₀ M C ×ˢ macRegion d N₀ M C)
      (fun (u : L1Torus d N₀ × L1Torus d N₀ → ℂ) s =>
        G (Matrix.of fun x y => u (x, y)) s) := by
  intro C u u' s s' hs hs' hPs hu
  have hsub : ∀ i ∈ C, macBox d N₀ M i ×ˢ macBox d N₀ M i ⊆
      macRegion d N₀ M C ×ˢ macRegion d N₀ M C := fun i hi =>
    Set.prod_mono (fun _ hx => mem_macRegion.2 ⟨i, hi, hx⟩) (fun _ hx => mem_macRegion.2 ⟨i, hi, hx⟩)
  have hss : s = s' := by
    funext i
    by_cases hi : i ∈ C
    · exact hPs i hi (hsub i hi)
    · rw [hs i hi, hs' i hi]
  subst hss
  exact hG _ _ C (fun x hx y hy => hu (x, y) ⟨hx, hy⟩) s hs

/-- **T1.**  `LocalityAE` for each entry `(x, y)` of the tagged family `taggedGfin`. -/
theorem localityAE_taggedGfin (hM : 0 < M) (hd : 0 < d) (t : ℝ) (x y : L1Torus d N₀) :
    LocalityAE (fun i : MacIdx d N₀ M => macBox d N₀ M i ×ˢ macBox d N₀ M i)
      (fun C => macRegion d N₀ M C ×ˢ macRegion d N₀ M C)
      (fun (u : L1Torus d N₀ × L1Torus d N₀ → ℂ) s =>
        taggedGfin Finset.univ (macBoxF d N₀ M) (fun z w => ((macChi d N₀ M z w : ℝ) : ℂ))
          (macTags d N₀ M) (Matrix.of fun a b => u (a, b)) t s x y) :=
  localityAE_macBox_of_agree
    (G := fun U s => taggedGfin Finset.univ (macBoxF d N₀ M)
      (fun z w => ((macChi d N₀ M z w : ℝ) : ℂ)) (macTags d N₀ M) U t s x y)
    fun _ _ _ hU _ hs => by
      rw [(taggedGfin_congr_of_agree_on_region hM hd Finset.univ hU hs).2.2]

/-- **T1.**  `LocalityAE` for each entry `(x, y)` of the Stieltjes integral `taggedCfinU`. -/
theorem localityAE_taggedCfinU (hM : 0 < M) (hd : 0 < d) (x y : L1Torus d N₀) :
    LocalityAE (fun i : MacIdx d N₀ M => macBox d N₀ M i ×ˢ macBox d N₀ M i)
      (fun C => macRegion d N₀ M C ×ˢ macRegion d N₀ M C)
      (fun (u : L1Torus d N₀ × L1Torus d N₀ → ℂ) s =>
        taggedCfinU d N₀ M (Matrix.of fun a b => u (a, b)) s x y) :=
  localityAE_macBox_of_agree
    (G := fun U s => taggedCfinU d N₀ M U s x y)
    fun _ _ _ hU _ hs => by rw [taggedCfinU_congr_of_agree_on_region hM hd hU hs]

/-- With `P i = macBox i × macBox i` and `Y C = macRegion C × macRegion C`, every family is
connected in the sense of `IsConnectedFamily`. -/
theorem isConnectedFamily_macBox (C : Finset (MacIdx d N₀ M)) :
    IsConnectedFamily (fun i : MacIdx d N₀ M => macBox d N₀ M i ×ˢ macBox d N₀ M i)
      (fun C => macRegion d N₀ M C ×ˢ macRegion d N₀ M C) C := fun i hi =>
  Set.prod_mono (fun _ hx => mem_macRegion.2 ⟨i, hi, hx⟩) (fun _ hx => mem_macRegion.2 ⟨i, hi, hx⟩)

/-- **T2.**  Vanishing of the coefficient of a non-connected family, for the entries of
`taggedGfin` (here the hypothesis is never satisfied, by `isConnectedFamily_macBox`). -/
theorem coef_taggedGfin_eq_zero_of_not_connected (hM : 0 < M) (hd : 0 < d) (t : ℝ)
    (x y : L1Torus d N₀) (u : L1Torus d N₀ × L1Torus d N₀ → ℂ) {C : Finset (MacIdx d N₀ M)}
    (hC : ¬ IsConnectedFamily (fun i : MacIdx d N₀ M => macBox d N₀ M i ×ˢ macBox d N₀ M i)
      (fun C => macRegion d N₀ M C ×ˢ macRegion d N₀ M C) C) :
    coef (fun s => taggedGfin Finset.univ (macBoxF d N₀ M)
      (fun z w => ((macChi d N₀ M z w : ℝ) : ℂ)) (macTags d N₀ M)
      (Matrix.of fun a b => u (a, b)) t s x y) C = 0 :=
  coef_eq_zero_of_not_connected (localityAE_taggedGfin hM hd t x y) u hC

/-- **T2.**  Vanishing of the coefficient of a non-connected family for `taggedCfinU`. -/
theorem coef_taggedCfinU_eq_zero_of_not_connected (hM : 0 < M) (hd : 0 < d)
    (x y : L1Torus d N₀) (u : L1Torus d N₀ × L1Torus d N₀ → ℂ) {C : Finset (MacIdx d N₀ M)}
    (hC : ¬ IsConnectedFamily (fun i : MacIdx d N₀ M => macBox d N₀ M i ×ˢ macBox d N₀ M i)
      (fun C => macRegion d N₀ M C ×ˢ macRegion d N₀ M C) C) :
    coef (fun s => taggedCfinU d N₀ M (Matrix.of fun a b => u (a, b)) s x y) C = 0 :=
  coef_eq_zero_of_not_connected (localityAE_taggedCfinU hM hd x y) u hC

/-- **T2.**  Congruence of coefficients of `taggedGfin` entries: `u = u'` on `Y C` suffices. -/
theorem coef_taggedGfin_congr_of_agree (hM : 0 < M) (hd : 0 < d) (t : ℝ) (x y : L1Torus d N₀)
    (C : Finset (MacIdx d N₀ M)) {u u' : L1Torus d N₀ × L1Torus d N₀ → ℂ}
    (huu : ∀ p ∈ macRegion d N₀ M C ×ˢ macRegion d N₀ M C, u p = u' p) :
    coef (fun s => taggedGfin Finset.univ (macBoxF d N₀ M)
      (fun z w => ((macChi d N₀ M z w : ℝ) : ℂ)) (macTags d N₀ M)
      (Matrix.of fun a b => u (a, b)) t s x y) C =
    coef (fun s => taggedGfin Finset.univ (macBoxF d N₀ M)
      (fun z w => ((macChi d N₀ M z w : ℝ) : ℂ)) (macTags d N₀ M)
      (Matrix.of fun a b => u' (a, b)) t s x y) C :=
  coef_congr_of_agree (localityAE_taggedGfin hM hd t x y) C huu

/-- **T2.**  Congruence of coefficients of `taggedCfinU` entries. -/
theorem coef_taggedCfinU_congr_of_agree (hM : 0 < M) (hd : 0 < d) (x y : L1Torus d N₀)
    (C : Finset (MacIdx d N₀ M)) {u u' : L1Torus d N₀ × L1Torus d N₀ → ℂ}
    (huu : ∀ p ∈ macRegion d N₀ M C ×ˢ macRegion d N₀ M C, u p = u' p) :
    coef (fun s => taggedCfinU d N₀ M (Matrix.of fun a b => u (a, b)) s x y) C =
    coef (fun s => taggedCfinU d N₀ M (Matrix.of fun a b => u' (a, b)) s x y) C :=
  coef_congr_of_agree (localityAE_taggedCfinU hM hd x y) C huu

/-! ### Lemma AE for the final operator

Lemma AE quantifies analyticity and the bound over all data `u`, whereas the landed analyticity
and row bounds hold for the final operator only.  We therefore apply it to the family that does
not depend on `u` (the datum is the fixed final operator); its locality is
`localityAE_macBox_of_agree` with a constant `G`.  The dependence of the coefficients on the
datum is the separate statement `coef_*_congr_of_agree` above. -/

section Final

variable {L k : ℕ} [NeZero L] {v a : ℝ}

/-- **T3.**  Lemma AE for the entries of `s ↦ G_fin(s, t)` of the final operator, `κ ≥ 1`. -/
theorem abstract_expansion_taggedGfin_final (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    (x y : L1Torus d N₀) :
    let F : (L1Torus d N₀ × L1Torus d N₀ → ℂ) → (MacIdx d N₀ M → ℂ) → ℂ := fun _ s =>
      taggedGfin Finset.univ (macBoxF d N₀ M) (fun z w => ((macChi d N₀ M z w : ℝ) : ℂ))
        (macTags d N₀ M) (finalOp d L N₀ k v a) t s x y
    (∀ u, F u (fun _ => 1) = (shiftMat (finalOp d L N₀ k v a) t)⁻¹ x y) ∧
    (∀ u, F u (fun _ => 1) = ∑ C : Finset (MacIdx d N₀ M), coef (F u) C) ∧
    (∀ u C, ‖coef (F u) C‖ ≤ (4 / 3 * taggedA0 d L κ t) / (Real.exp κ - 1) ^ C.card) ∧
    (∀ u C, ‖coef (F u) C‖ ≤ (4 / 3 * taggedA0 d L κ t) * Real.exp (-(κ - 1) * C.card)) := by
  intro F
  have hfin := taggedGfin_final (N₀ := N₀) (k := k) (L := L) hd hk hv0 hv1 ha1 ha2 hmass ht hM
    (by linarith) hMB hMκ
  have hloc : LocalityAE (fun i : MacIdx d N₀ M => macBox d N₀ M i ×ˢ macBox d N₀ M i)
      (fun C => macRegion d N₀ M C ×ˢ macRegion d N₀ M C) F :=
    localityAE_macBox_of_agree (G := fun _ s => taggedGfin Finset.univ (macBoxF d N₀ M)
      (fun z w => ((macChi d N₀ M z w : ℝ) : ℂ)) (macTags d N₀ M) (finalOp d L N₀ k v a) t s x y)
      fun _ _ _ _ _ _ => rfl
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hε := pdEps_pos (d := d) (L := L) hd
  have hcl : ∀ s ∈ Balaban.Analysis.polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ),
      ∀ p, ‖s p‖ ≤ Real.exp κ := fun s hs p => by simpa using (hs p).le
  have hana : ∀ u, AnalyticOnNhd ℂ (F u)
      (Balaban.Analysis.polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) := fun u =>
    (hfin.2.2.1 x y).mono fun s hs => hcl s hs
  have hbd : ∀ u, ∀ s ∈ Balaban.Analysis.polydisc (0 : MacIdx d N₀ M → ℂ)
      (fun _ => Real.exp κ), ‖F u s‖ ≤ 4 / 3 * taggedA0 d L κ t := fun u s hs => by
    have h := taggedGfin_row_bound (N₀ := N₀) (k := k) (L := L) hd hk hv0 hv1 ha1 ha2 hmass ht hM
      (by linarith) hMB hMκ (r := 0) le_rfl (by positivity) (hcl s hs) x
    have h1 := Finset.single_le_sum (f := fun y => Real.exp (0 * dist x y) *
        ‖taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t s x y‖)
      (fun y _ => by positivity) (Finset.mem_univ y)
    simp only [zero_mul, Real.exp_zero, one_mul] at h h1
    exact h1.trans h
  have hAE := abstract_expansion (P := fun i : MacIdx d N₀ M => macBox d N₀ M i ×ˢ macBox d N₀ M i)
    (Y := fun C => macRegion d N₀ M C ×ˢ macRegion d N₀ M C) hκ hana hbd hloc
  have h1 : ∀ u, F u (fun _ => 1) = (shiftMat (finalOp d L N₀ k v a) t)⁻¹ x y := fun u => by
    show taggedGfin Finset.univ (macBoxF d N₀ M) (fun z w => ((macChi d N₀ M z w : ℝ) : ℂ))
        (macTags d N₀ M) (finalOp d L N₀ k v a) t (fun _ => 1) x y = _
    rw [hfin.2.2.2]
  refine ⟨h1, fun u => ?_, hAE.2.2.2.1, hAE.2.2.2.2⟩
  have := hAE.1 u
  classical
  rw [Finset.filter_true_of_mem fun C _ => isConnectedFamily_macBox (d := d) (N₀ := N₀) (M := M) C]
    at this
  exact this

/-- **T3.**  Lemma AE for the entries of `s ↦ C_fin(s)` (Stieltjes square-root family of the final
operator), `κ ≥ 1`; the value at `s = 1` is the square root `sqrtMat` of the final operator. -/
theorem abstract_expansion_taggedCfin_final (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    (x y : L1Torus d N₀) :
    let F : (L1Torus d N₀ × L1Torus d N₀ → ℂ) → (MacIdx d N₀ M → ℂ) → ℂ := fun _ s =>
      taggedCfin d L N₀ k M v a s x y
    let B : ℝ := 4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)
    (∀ u, F u (fun _ => 1) = Localization.sqrtMat (finalOp d L N₀ k v a) x y) ∧
    (∀ u, F u (fun _ => 1) = ∑ C : Finset (MacIdx d N₀ M), coef (F u) C) ∧
    (∀ u C, ‖coef (F u) C‖ ≤ B / (Real.exp κ - 1) ^ C.card) ∧
    (∀ u C, ‖coef (F u) C‖ ≤ B * Real.exp (-(κ - 1) * C.card)) := by
  intro F B
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hε := pdEps_pos (d := d) (L := L) hd
  have hcl : ∀ s ∈ Balaban.Analysis.polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ),
      ∀ p, ‖s p‖ ≤ Real.exp κ := fun s hs p => by simpa using (hs p).le
  have hloc : LocalityAE (fun i : MacIdx d N₀ M => macBox d N₀ M i ×ˢ macBox d N₀ M i)
      (fun C => macRegion d N₀ M C ×ˢ macRegion d N₀ M C) F :=
    localityAE_macBox_of_agree (G := fun _ s => taggedCfin d L N₀ k M v a s x y)
      fun _ _ _ _ _ _ => rfl
  have hana : ∀ u, AnalyticOnNhd ℂ (F u)
      (Balaban.Analysis.polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) := fun u =>
    (taggedCfin_analyticOnNhd (N₀ := N₀) (k := k) (L := L) (v := v) (a := a) (M := M) hd hk hv0
      hv1 ha1 ha2 hmass hM (by linarith) hMB hMκ x y).mono fun s hs p => by simpa using hs p
  have hbd : ∀ u, ∀ s ∈ Balaban.Analysis.polydisc (0 : MacIdx d N₀ M → ℂ)
      (fun _ => Real.exp κ), ‖F u s‖ ≤ B := fun u s hs => by
    have h := taggedCfin_row_bound (N₀ := N₀) (k := k) (L := L) (v := v) (a := a) (M := M) hd hk
      hv0 hv1 ha1 ha2 hmass hM (by linarith) hMB hMκ (hcl s hs) (r := 0) le_rfl (by positivity) x
    have h1 := Finset.single_le_sum (f := fun y => Real.exp (0 * dist x y) *
        ‖taggedCfin d L N₀ k M v a s x y‖) (fun y _ => by positivity) (Finset.mem_univ y)
    simp only [zero_mul, Real.exp_zero, one_mul] at h h1
    exact h1.trans h
  have hAE := abstract_expansion (P := fun i : MacIdx d N₀ M => macBox d N₀ M i ×ˢ macBox d N₀ M i)
    (Y := fun C => macRegion d N₀ M C ×ˢ macRegion d N₀ M C) hκ hana hbd hloc
  have h1 : ∀ u, F u (fun _ => 1) = Localization.sqrtMat (finalOp d L N₀ k v a) x y := fun u => by
    show taggedCfin d L N₀ k M v a (fun _ => 1) x y = _
    rw [taggedCfin_one hd hk hv0 hv1 ha1 ha2 hmass hM (by linarith) hMB hMκ]
  refine ⟨h1, fun u => ?_, hAE.2.2.2.1, hAE.2.2.2.2⟩
  have := hAE.1 u
  classical
  rw [Finset.filter_true_of_mem fun C _ => isConnectedFamily_macBox (d := d) (N₀ := N₀) (M := M) C]
    at this
  exact this

end Final

end Balaban.Green
