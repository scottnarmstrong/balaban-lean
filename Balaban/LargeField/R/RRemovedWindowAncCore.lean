/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedWindowAnc

/-!
# The window integral: the core input and the exponent of the quiet window (W909)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4.  Lemma III.8.7 (4) and Definition II.5.11.

* `ancFin_eq_biUnion_parts`: the ancestors at scale `k₁` of `Z` are the disjoint union, over the
  ancestors `P` at scale `k₁ + 1`, of the old parts of `P` (the multi-scale ancestor bijection);
* `kappa_unroll`, `kappaPre_unroll`: along a quiet window the exponent `κ` is the sum of the step
  exponents `κ^{(j)}` of the ancestors at the scales `j + 1 ∈ (k₁, m]` plus `∑_C κ_{k₁}(C)`;
* `hκ_of_window`: the premise `hκ` of `removedKernel_kerBound_of_window`;
* `hcore_of_anc`: the premise `hcore`: the integral over the core variables of the product of the
  weights of the ancestor operators is at most `e^{-∑_C κ_{k₁}(C)}`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory ENNReal

section Anc

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {K : ℕ}
  {H : RegionHistory S n R k0 K}

theorem parts_disjoint {k : ℕ} {P P' : H.Comp (k + 1)} (hne : P ≠ P') :
    Disjoint (H.parts k P) (H.parts k P') := by
  rw [Finset.disjoint_left]
  intro c h h'
  exact hne (RegionHistory.IsSucc.unique _ ((H.mem_parts _ _ _).mp h).2
    ((H.mem_parts _ _ _).mp h').2)

/-- **The multi-scale ancestor bijection**: the ancestors at scale `k₁` of `Z` (scale `m > k₁`)
are the disjoint union, over the ancestors `P` of `Z` at scale `k₁ + 1`, of the old parts of
`P`. -/
theorem ancFin_eq_biUnion_parts {k1 m : ℕ} (h : k1 < m) (Z : H.Comp m) :
    H.ancFin k1 m Z = (H.ancFin (k1 + 1) m Z).biUnion fun P => H.parts k1 P := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [ancFin_succ le_rfl, ancFin_self]
    ext c
    simp [ancFin_self]
  | succ m hm ih =>
    rw [ancFin_succ (by omega), ancFin_succ (by omega), Finset.biUnion_biUnion]
    refine Finset.biUnion_congr rfl fun c _ => ?_
    exact ih _

theorem sum_ancFin_succ {β : Type*} [AddCommMonoid β] {a b : ℕ} (hab : a ≤ b)
    (Z' : H.Comp (b + 1)) (f : H.Comp a → β) :
    ∑ P ∈ H.ancFin a (b + 1) Z', f P = ∑ Y ∈ H.parts b Z', ∑ P ∈ H.ancFin a b Y, f P := by
  classical
  rw [ancFin_succ hab, Finset.sum_biUnion (fun c _ c' _ hne => ancFin_disjoint hne)]

/-- The sum over the ancestors at scale `k₁` is the iterated sum over the ancestors `P` at scale
`k₁ + 1` and their old parts. -/
theorem sum_anc_eq_sum_parts {β : Type*} [AddCommMonoid β] {k1 m : ℕ} (h : k1 < m)
    (Z : H.Comp m) (f : H.Comp k1 → β) :
    ∑ C ∈ H.ancFin k1 m Z, f C =
      ∑ P ∈ H.ancFin (k1 + 1) m Z, ∑ C ∈ H.parts k1 P, f C := by
  classical
  rw [ancFin_eq_biUnion_parts h Z, Finset.sum_biUnion (fun P _ P' _ hne => parts_disjoint hne)]

section Kappa

variable (B : BudgetConsts) (κK : ∀ k, H.Comp k → ℝ)

/-- One level of the unrolling of the exponent: if the exponents of the old parts of `Z'` are
given by the unrolled formula (with the step exponents `κ^{(j)}` of the ancestors at the scales
`j + 1 ∈ (k₁, m]`), so is `κ^pre_{m+1}(Z')`. -/
theorem kappaPre_step {k1 m : ℕ} (hk : k1 ≤ m) (Z' : H.Comp (m + 1))
    (hY : ∀ Y ∈ H.parts m Z', H.kappa B κK m Y =
      ∑ j ∈ Finset.Ico k1 m, ∑ P ∈ H.ancFin (j + 1) m Y,
        B.kappaStep S j (P.1 ∩ H.newCubes (j + 1)).card (H.outCubes j P).card +
      ∑ C ∈ H.ancFin k1 m Y, H.kappa B κK k1 C) :
    H.kappaPre B m (fun c => H.kappa B κK m c) Z' =
      ∑ j ∈ Finset.Ico k1 (m + 1), ∑ P ∈ H.ancFin (j + 1) (m + 1) Z',
        B.kappaStep S j (P.1 ∩ H.newCubes (j + 1)).card (H.outCubes j P).card +
      ∑ C ∈ H.ancFin k1 (m + 1) Z', H.kappa B κK k1 C := by
  classical
  unfold RegionHistory.kappaPre
  rw [Finset.sum_congr rfl hY, Finset.sum_add_distrib, Finset.sum_comm,
    Finset.sum_Ico_succ_top hk, ancFin_self, Finset.sum_singleton,
    ← sum_ancFin_succ hk Z' (fun C => H.kappa B κK k1 C)]
  have : ∀ j ∈ Finset.Ico k1 m, ∑ c ∈ H.parts m Z', ∑ P ∈ H.ancFin (j + 1) m c,
      B.kappaStep S j (P.1 ∩ H.newCubes (j + 1)).card (H.outCubes j P).card =
      ∑ P ∈ H.ancFin (j + 1) (m + 1) Z',
        B.kappaStep S j (P.1 ∩ H.newCubes (j + 1)).card (H.outCubes j P).card :=
    fun j hj => (sum_ancFin_succ (by have := Finset.mem_Ico.mp hj; omega) Z'
      (fun P => B.kappaStep S j (P.1 ∩ H.newCubes (j + 1)).card (H.outCubes j P).card)).symm
  rw [Finset.sum_congr rfl this]
  ring

/-- **The exponent along a quiet window**: if the ancestors of `Z` at the scales `(k₁, m]` are not
kept, then `κ_m(Z) = ∑_{j = k₁}^{m-1} ∑_{P ∈ Anc_{j+1}(Z)} κ^{(j)}(P) + ∑_{C ∈ Anc_{k₁}(Z)} κ_{k₁}(C)`
(Definition II.5.11). -/
theorem kappa_unroll (k1 : ℕ) : ∀ (m : ℕ), k1 ≤ m → ∀ (Z : H.Comp m),
    (∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s m Y Z → ¬ H.IsKeptEvent s Y) →
    H.kappa B κK m Z =
      ∑ j ∈ Finset.Ico k1 m, ∑ P ∈ H.ancFin (j + 1) m Z,
        B.kappaStep S j (P.1 ∩ H.newCubes (j + 1)).card (H.outCubes j P).card +
      ∑ C ∈ H.ancFin k1 m Z, H.kappa B κK k1 C := by
  intro m hk
  induction m, hk using Nat.le_induction with
  | base =>
    intro Z _
    rw [ancFin_self, Finset.Ico_self, Finset.sum_empty, Finset.sum_singleton, zero_add]
  | succ m hk ih =>
    intro Z' hq
    have hnk : ¬ H.IsKeptEvent (m + 1) Z' := hq (m + 1) (by omega) Z' (Desc.refl Z')
    have hY : ∀ Y ∈ H.parts m Z', H.kappa B κK m Y = _ := fun Y hY =>
      ih Y (fun s hs Y' h' => hq s hs Y' (Desc.trans h' (Desc.single
        ((H.mem_parts _ _ _).mp hY).1 ((H.mem_parts _ _ _).mp hY).2)))
    rw [← kappaPre_step B κK hk Z' hY]
    simp only [RegionHistory.kappa, hnk, ↓reduceIte]

/-- **The exponent `κ^pre` of the removed component**: for `Z` at scale `m + 1` whose ancestors at
the scales `(k₁, m]` are not kept, `κ^pre_{m+1}(Z) = ∑_{j = k₁}^{m} ∑_{P ∈ Anc_{j+1}(Z)} κ^{(j)}(P)
+ ∑_{C ∈ Anc_{k₁}(Z)} κ_{k₁}(C)`. -/
theorem kappaPre_unroll {k1 m : ℕ} (hk : k1 ≤ m) (Z : H.Comp (m + 1))
    (hq : ∀ s, k1 < s → s ≤ m → ∀ Y : H.Comp s, H.Desc s (m + 1) Y Z → ¬ H.IsKeptEvent s Y) :
    H.kappaPre B m (fun c => H.kappa B κK m c) Z =
      ∑ j ∈ Finset.Ico k1 (m + 1), ∑ P ∈ H.ancFin (j + 1) (m + 1) Z,
        B.kappaStep S j (P.1 ∩ H.newCubes (j + 1)).card (H.outCubes j P).card +
      ∑ C ∈ H.ancFin k1 (m + 1) Z, H.kappa B κK k1 C :=
  kappaPre_step B κK hk Z fun Y hY => kappa_unroll B κK k1 m hk Y fun s hs Y' h' =>
    hq s hs (Desc.le h') Y' (Desc.trans h' (Desc.single ((H.mem_parts _ _ _).mp hY).1
      ((H.mem_parts _ _ _).mp hY).2))

/-- **The premise `hκ`** of `removedKernel_kerBound_of_window`: in a quiet window (no new cubes,
`|𝒩_{j+1} ∩ P| = 0`) the step exponents are `-(c₁ log β_j + c₂) |Z^c_j ∩ P|_{j+1}`, so
`κ^pre = ∑_C κ_{k₁}(C) - ∑_{j,P} (c₁ log β_j + c₂) |Z^c_j ∩ P|_{j+1}`, and if the window-proportional
terms `B_w + C_k` are at most this sum (the budget `c₁ ≥ C_W`, `c₂ ≥ C'_W`), then
`κ^pre ≤ ∑_C κ_{k₁}(C) - (B_w + C_k)`. -/
theorem kappaPre_le_of_window {k1 m : ℕ} (hk : k1 ≤ m) (Z : H.Comp (m + 1))
    (hq : ∀ s, k1 < s → s ≤ m → ∀ Y : H.Comp s, H.Desc s (m + 1) Y Z → ¬ H.IsKeptEvent s Y)
    (hnew : ∀ j ∈ Finset.Ico k1 (m + 1), ∀ P ∈ H.ancFin (j + 1) (m + 1) Z,
      (P.1 ∩ H.newCubes (j + 1)).card = 0)
    {Bw Ck : ℝ}
    (hwin : Bw + Ck ≤ ∑ j ∈ Finset.Ico k1 (m + 1), ∑ P ∈ H.ancFin (j + 1) (m + 1) Z,
      (B.c1 * Real.log (B.beta j) + B.c2) *
        ((S.M : ℝ) ^ S.d / (S.L : ℝ) ^ S.d * (H.outCubes j P).card)) :
    H.kappaPre B m (fun c => H.kappa B κK m c) Z ≤
      ∑ C ∈ H.ancFin k1 (m + 1) Z, H.kappa B κK k1 C - (Bw + Ck) := by
  rw [kappaPre_unroll B κK hk Z hq]
  have : ∑ j ∈ Finset.Ico k1 (m + 1), ∑ P ∈ H.ancFin (j + 1) (m + 1) Z,
      B.kappaStep S j (P.1 ∩ H.newCubes (j + 1)).card (H.outCubes j P).card =
      -∑ j ∈ Finset.Ico k1 (m + 1), ∑ P ∈ H.ancFin (j + 1) (m + 1) Z,
        (B.c1 * Real.log (B.beta j) + B.c2) *
          ((S.M : ℝ) ^ S.d / (S.L : ℝ) ^ S.d * (H.outCubes j P).card) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [hnew j hj P hP]
    simp [BudgetConsts.kappaStep]
  rw [this]
  linarith

end Kappa

end Anc

section Core

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)

/-- **The premise `hcore` of `removedKernel_kerBound_of_window`** ((D5) at scale `k₁`, Lemma III.8.7
(4)): for a component `Z` of scale `m > k₁`, the core variables are the outputs and internal
variables of the operators `𝕋_{k₁}(C)` of the ancestors `C` of `Z` at scale `k₁` (indexed as the old
parts `C` of the ancestors `P` of `Z` at scale `k₁ + 1`, `ancFin_eq_biUnion_parts`), with the product
measure.  For every dependence `parC` of the parameters of the outputs of the ancestors on the
window variables `w` and the parameters `par`, the integral over the core variables of the product
of the weights `K_C e^{Re b_C}` is at most `e^{-∑_C κ_{k₁}(C)}`, the exponents of Definition II.5.11
(`locOp_pkgBound_kappa`). -/
theorem hcore_of_anc (hH : H.Admissible) (lab : ∀ k, H.Comp k → Fin 5)
    (hz : ∀ k, 0 < cs.z (k + 1))
    (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (B : BudgetConsts) (κK : ∀ k, H.Comp k → ℝ)
    (hκs : ∀ (k : ℕ) (Z' : H.Comp (k + 1)), κs k (H.localHistory M K (k + 1) Z') =
      B.kappaStep S k (Z'.1 ∩ H.newCubes (k + 1)).card (H.outCubes k Z').card)
    (hkept : ∀ (k : ℕ) (hk : k ≤ K) (Z : H.Comp k), IsKept H k Z →
      PkgBound (H.localHistory M K k Z) k (locOp geo cs SD KD hH lab k hk Z) (κK k Z))
    {k1 m : ℕ} (h : k1 < m) (hmK : m ≤ K) (Z : H.Comp m) {OP Wd : Type*}
    (parC : OP → Wd → ∀ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
      OutPar N R (H.localHistory M K k1 C.2.1) k1)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N))
    (par : OP) (w : Wd) :
    ∫⁻ c : (∀ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
          OutZ N R (H.localHistory M K k1 C.2.1) k1 ×
            SubCfg N (H.localHistory M K k1 C.2.1) k1
              (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A),
        ∏ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
          (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).T.absW
          (mergeOut (H.localHistory M K k1 C.2.1) k1 (c C).1 (parC par w C)) (c C).2 hv g
      ∂(Measure.pi (fun C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)) =>
        (outPartMeasure N (Vblk R (H.localHistory M K k1 C.2.1) k1)
          (ZBlk (H.localHistory M K k1 C.2.1) k1)).prod
        (subMeasure N (H.localHistory M K k1 C.2.1) k1
          (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A))) ≤
      ENNReal.ofReal (Real.exp (-∑ C ∈ H.ancFin k1 m Z, H.kappa B κK k1 C)) := by
  have h1 := core_lintegral_le (ι := Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
    (fun C => H.localHistory M K k1 C.2.1) k1
    (fun C => locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1)
    (fun C => H.kappa B κK k1 C.2.1)
    (fun C => locOp_pkgBound_kappa geo cs SD KD hH lab hz hc B κK hκs hkept k1
      (h.le.trans hmK) C.2.1) (parC par) hv g hg w
  have h2 : ∑ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)), H.kappa B κK k1 C.2.1 =
      ∑ C ∈ H.ancFin k1 m Z, H.kappa B κK k1 C := by
    rw [sum_anc_eq_sum_parts h Z, Fintype.sum_sigma,
      ← Finset.sum_coe_sort (H.ancFin (k1 + 1) m Z)]
    exact Finset.sum_congr rfl fun P _ => Finset.sum_coe_sort _ (fun C => H.kappa B κK k1 C)
  rwa [h2] at h1

end Core

end Balaban.LargeField
