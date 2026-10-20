/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfUniv
public import Balaban.LargeField.Background.CubeUnitBg

/-!
# The background of the constant block field

A6-3 (a), step (P1) (`notes/phase1/SPINE.md`, item 3): for the constant block field `ψ_k ≡ h`
with `|h| = 1` the small-field background `φ_k` of the generating set `𝔹_k(W_k)` is the constant
field `h`, and on the whole torus the real background `φ̄_k` is `h` at every site.

* `liftSingle_const`: the single-scale lift of a constant block field is the constant datum;
* `phiK_const`: `φ_k = h` on `Ω₁` (uniqueness of the small solution, `bgFieldC_constUnitBg`);
* `phiBar_const_of_mem`: `φ̄_k = h` at the data sites;
* `genW_Ω_univ`, `phiBar_const_univ`: for the cut `Y = univ`, `φ̄_k ≡ h` everywhere.
-/

@[expose] public section

open MeasureTheory Matrix Balaban Balaban.LargeField Balaban.LargeField.Def7
  Balaban.LargeField.Def7v2 Balaban.Multiscale Balaban.Background

namespace Balaban.RootFSpine

section Lift

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- Two data with the same fields are equal. -/
theorem bgData_ext {G : GeneratingSet d L N₀ k ϱ} {D D' : BgData G N} (hΨ : D.Ψ = D'.Ψ)
    (hh : D.h = D'.h) : D = D' := by
  cases D; cases D'; simp_all

/-- The single-scale lift of a constant block field is the constant datum. -/
theorem liftSingle_const (G : GeneratingSet d L N₀ k ϱ) (e : Fin N → ℝ) :
    liftSingle G (fun _ i => (e i : ℂ)) (fun i => (e i : ℂ)) = constUnitBg G e := by
  classical
  refine bgData_ext ?_ ?_ <;> rfl

end Lift

section Action

open Balaban.LargeField

variable {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- The block average of a constant field is the constant. -/
theorem bavg_const {ℓ m n : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = n * m) (hn : n ≠ 0) (c : E)
    (y : Torus d m) : bavg n m (fun _ : Torus d ℓ => c) y = c := by
  unfold bavg
  rw [Finset.sum_const, card_blockFibre hℓ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have : ((n : ℝ) ^ d)⁻¹ * ((n ^ d : ℕ) : ℝ) = 1 := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp [this]
  rw [this, one_smul]

/-- **The single-scale action vanishes at the constant configuration**: for the level
generating set `T^{(q)}_1`, a block field with `ψ_q ≡ h` and the constant background `φ ≡ h`,
for every weights, mass and set `X`. -/
theorem actionG_levelGen_const (a : ℕ → ℝ) (μ : ℝ) (h : E) (X : Finset (Site d L N₀ q))
    (ψ : (m : ℕ) → Blk d L N₀ q m → E) (hψ : ∀ y, ψ q y = h) :
    actionG (levelGen (ϱ := ϱ) q) a μ h X ψ (fun _ => h) = 0 := by
  unfold actionG
  have h1 : ∑ n ∈ Finset.Icc 1 q, ∑ y ∈ tBlocks d L N₀ q n (lam (levelGen (ϱ := ϱ) q) n ∩ X),
      a n * (L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ q n (fun _ => h) y‖ ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    obtain ⟨hn1, hnq⟩ := Finset.mem_Icc.1 hn
    rcases hnq.eq_or_lt with rfl | hlt
    · refine Finset.sum_eq_zero fun y _ => ?_
      rw [hψ y]
      unfold bavgL
      rw [bavg_const (ℓ := N₀ * L ^ n) (m := N₀ * L ^ (n - n)) (by simp [pow_zero]; ring)
        (pow_ne_zero _ (NeZero.ne L)), sub_self]
      simp
    · have : lam (levelGen (d := d) (L := L) (N₀ := N₀) (ϱ := ϱ) q) n = ∅ := by
        unfold lam
        simp only [show n ≠ 0 from by omega, ↓reduceIte]
        ext x
        simp [GeneratingSet.layer, levelGen, hnq, Nat.succ_le_of_lt hlt]
      rw [this]
      simp [tBlocks]
  have h2 : bondE X (fun _ : Site d L N₀ q => h) = 0 := by
    unfold bondE bondEdir bondTerm
    simp
  have h3 : ∑ x ∈ X, ‖(fun _ : Site d L N₀ q => h) x - h‖ ^ 2 = 0 := by simp
  rw [h1, h2, h3]
  simp

end Action

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (Y : Set (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N))

/-- The lifted data of the constant block field `ψ_k ≡ h` are the constant `h`. -/
theorem liftData_const :
    C.liftData (fun _ => hv) = fun _ i => (hv i : ℂ) := by
  funext z i
  simp [SFCtx.liftData, BlockCfg.toC, blockCfgOf]

/-- **The small-field background of the constant block field is constant** (`|h| = 1`, the
standing hypotheses of the background theory): `φ_k = h` on `Ω₁`. -/
theorem phiK_const
    (H : BgHyp S.d S.L k (minSep S.L C.geo.M1) C.weights (C.cs.muBg k))
    (he : ∑ i, hv i ^ 2 = 1) :
    C.phiK Y (fun _ => hv) hv = constUnitPhi (C.genW Y) (fun i => hv i) := by
  unfold SFCtx.phiK bgSF
  rw [liftData_const]
  have e : hC hv = fun i => (hv i : ℂ) := rfl
  rw [e, liftSingle_const]
  exact bgFieldC_constUnitBg H he

/-- **`φ̄_k = h` at the data sites** for the constant block field. -/
theorem phiBar_const_of_mem
    (H : BgHyp S.d S.L k (minSep S.L C.geo.M1) C.weights (C.cs.muBg k))
    (he : ∑ i, hv i ^ 2 = 1) {z : BgT C.geo k} (hz : z ∈ dataSites (C.genW Y)) :
    C.phiBar Y (fun _ => hv) hv z = hv := by
  ext i
  unfold SFCtx.phiBar
  rw [liftData_const, phiK_const C Y hv H he]
  have e : hC hv = fun i => (hv i : ℂ) := rfl
  rw [e, liftSingle_const]
  simp [barField_constUnitPhi _ hz]

/-- On the whole torus every site is a site of the layers `Ω_m`, `m ≤ k` of `𝔹_k(W_k)`. -/
theorem genW_Ω_univ_of_le {m : ℕ} (hmk : m ≤ k) :
    (C.genW (Set.univ : Set (Torus S.d (n k)))).Ω m = Finset.univ := by
  classical
  refine Finset.eq_univ_of_forall fun x => ?_
  unfold SFCtx.genW genSF
  rw [minimalGenSet_Ω]
  refine minLayer_antitone hmk ?_
  rw [minLayer_self]
  refine (mem_cubeInterior _).2 fun y _ => ?_
  rw [mem_cubePre]
  have : W2 R (Set.univ : Set (Torus S.d (n k))) = Set.univ := by
    unfold W2 thick
    exact Set.univ_subset_iff.1 (subset_nbhd _ _ |>.trans' (Set.univ_subset_iff.2 (by
      exact Set.univ_subset_iff.1 (subset_nbhd _ _))))
  rw [this]
  trivial

/-- On the whole torus every site is a site of the first layer of `𝔹_k(W_k)` (`k ≥ 1`). -/
theorem genW_Ω_univ (hk : 1 ≤ k) :
    (C.genW (Set.univ : Set (Torus S.d (n k)))).Ω 1 = Finset.univ :=
  genW_Ω_univ_of_le C hk

/-- **`φ̄_k ≡ h` on the whole torus** for the cut `Y = univ` (`k ≥ 1`). -/
theorem phiBar_const_univ
    (H : BgHyp S.d S.L k (minSep S.L C.geo.M1) C.weights (C.cs.muBg k))
    (he : ∑ i, hv i ^ 2 = 1) (hk : 1 ≤ k) :
    C.phiBar Set.univ (fun _ => hv) hv = fun _ => hv := by
  funext z
  refine phiBar_const_of_mem C Set.univ hv H he ?_
  refine (mem_dataSites _).2 (Or.inl ?_)
  rw [genW_Ω_univ C hk]
  exact Finset.mem_univ _

/-- **The single-scale action on the whole torus vanishes at the constant configuration**:
`A*_k(univ; h, φ̄_k) = 0` (the value function `V(h·1) = 0`, A6-3 (a)). -/
theorem actStar2_const_univ
    (H : BgHyp S.d S.L k (minSep S.L C.geo.M1) C.weights (C.cs.muBg k))
    (he : ∑ i, hv i ^ 2 = 1) (hk : 1 ≤ k) :
    actStar2 C Set.univ (fun _ => hv) hv = 0 := by
  classical
  have hb : C.bgSet (Set.univ : Set (Torus S.d (n k))) = Finset.univ := by
    ext x; simp [SFCtx.bgSet]
  unfold actStar2
  rw [hb, phiBar_const_univ C hv H he hk]
  have h1 : actionG (levelGen (ϱ := (1 : ℝ)) k) C.weights (sfActMass2 C.cs k) hv Finset.univ
      (C.psiLevelK (fun _ => hv)) (fun _ => hv) = 0 :=
    actionG_levelGen_const _ _ hv _ _ fun y => by
      simp [SFCtx.psiLevelK, singleScale]
  have h2 : starBondE (Finset.univ : Finset (BgT C.geo k)) (fun _ => hv) = 0 := by
    simp [starBondE]
  rw [h1, h2]
  simp

end Ctx

end Balaban.RootFSpine
