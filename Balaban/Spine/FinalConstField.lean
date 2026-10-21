/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfConst
public import Balaban.Background.Composition

/-!
# The composed fields of the constant configuration

A6-3 (a), step (P1e). The composition `composeField G G' a φ' Ψ'` of the constant field with the
constant datum, for generating sets whose first domain is the whole torus, is the constant field
(`composeField_const`). Hence `ψ^{(j)}_k ≡ h` at `ψ_k ≡ h` on the whole torus (`psiJ_const_univ`),
and `ℱ_k` and `ℰ_k` at the constant configuration are the Def-6 terms at the constant field.
-/

@[expose] public section

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.LargeField.Def7
  Balaban.LargeField.Def7v2 Balaban.SmallField

namespace Balaban.RootFSpine

section Compose

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-- **The composition of constant fields is constant.** -/
theorem composeField_const (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')
    (hG : ∀ x, x ∈ G.Ω 1) (hG' : ∀ x, x ∈ G'.Ω 1) (a : ℕ → ℝ) (e : Fin N → ℝ)
    (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) (hΨ' : ∀ x i, Ψ' x i = (e i : ℂ))
    (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    composeField G G' a (constUnitPhi G' e) Ψ' x i = (e i : ℂ) := by
  have hsv : (fun y => svec G' (constUnitPhi G' e) y i) = fun _ => (e i : ℂ) :=
    funext fun y => svec_constUnitPhi e (hG' y) i
  rw [composeField_of_mem a (constUnitPhi G' e) Ψ' (hG x) i, hsv,
    blockMean_const G (layerIndex_le_k G x) _ x, blockMean_const G' (layerIndex_le_k G' x) _ x,
    hΨ' x i, sub_self, mul_zero, add_zero]

end Compose

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (hv : EuclideanSpace ℝ (Fin N))

/-- **`ψ^{(j)}_k ≡ h` at the constant configuration on the whole torus** (`1 ≤ j ≤ k`). -/
theorem psiJ_const_univ
    (H : BgHyp S.d S.L k (minSep S.L C.geo.M1) C.weights (C.cs.muBg k))
    (he : ∑ i, hv i ^ 2 = 1) (hk : 1 ≤ k) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    C.psiJ Set.univ (fun _ => hv) hv j = Def6.constFld (fun i => (hv i : ℂ)) := by
  have hG : ∀ x, x ∈ (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n k) (L := S.L) (c := C.geo.c)
      (n := n k) hjk (W2 R (Set.univ : Set (Torus S.d (n k))))).Ω 1 := fun x => by
    rw [genSF_Ω_univ_of_le C hjk hj1]; exact Finset.mem_univ x
  have hG' : ∀ x, x ∈ (C.genW (Set.univ : Set (Torus S.d (n k)))).Ω 1 := fun x => by
    rw [genW_Ω_univ C hk]; exact Finset.mem_univ x
  have hphi := phiK_const C Set.univ hv H he
  have hΨ' : ∀ x i, (liftSingle (C.genW (Set.univ : Set (Torus S.d (n k)))) (C.liftData (fun _ => hv))
      (hC hv)).Ψ x i = ((hv i : ℝ) : ℂ) := fun x i => by
    have e1 : hC hv = fun i => (hv i : ℂ) := rfl
    rw [liftData_const, e1, liftSingle_const]
    exact constUnitBg_Ψ ((mem_dataSites _).2 (Or.inl (hG' x))) i
  unfold SFCtx.psiJ
  simp only [hjk, ↓reduceDIte]
  funext x i
  simp only [sfPull, Def6.constFld, psiSF]
  have := composeField_const (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n k) (L := S.L)
    (c := C.geo.c) (n := n k) hjk (W2 R (Set.univ : Set (Torus S.d (n k)))))
    (C.genW (Set.univ : Set (Torus S.d (n k)))) hG hG' C.weights (fun i => hv i) _ hΨ'
    (sfToBg C.geo C.hT x) i
  rw [← hphi] at this
  exact this

open Classical in
/-- **The source term at the constant configuration** (`Y = univ`, `ψ_k ≡ h`): `ℱ_k = ⟨g, h⟩ +
∑_{j ≤ k} ⟨g, ℳ^{(j)}(h, h)⟩`, the Def-6 source terms at the constant field. -/
theorem Fres_const_univ
    (H : BgHyp S.d S.L k (minSep S.L C.geo.M1) C.weights (C.cs.muBg k))
    (he : ∑ i, hv i ^ 2 = 1) (hk : 1 ≤ k) (g : GIdx S n M K N → ℂ) :
    C.Fres Set.univ (fun _ => hv) hv g =
      (∑ x : BgT C.geo k, ∑ i : Fin N, g (bgToFine C.geo C.hnn C.hkK x, i) * (hv i : ℂ)) +
        ∑ j ∈ Finset.Icc 1 k,
          Def6.Floc C.m₀ (C.sf.Tm C.N₁) j (Def6.constFld (fun i => (hv i : ℂ)))
            (Def6.constFld (hC hv)) (sfG C.geo C.hnn C.hkK C.hT g) := by
  rw [Fres_univ]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    rw [phiBar_const_univ C hv H he hk]
  · refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 hj
    rw [psiJ_const_univ C hv H he hk hj1 hjk]

open Classical in
/-- **The restricted energy at the constant configuration** (`Y = univ`, `ψ_k ≡ h`): the Def-6
densities at the constant field minus the correction sums. -/
theorem EresK2_const_univ (vc : CorrCoef S.d)
    (H : BgHyp S.d S.L k (minSep S.L C.geo.M1) C.weights (C.cs.muBg k))
    (he : ∑ i, hv i ^ 2 = 1) (hk : 1 ≤ k) :
    EresK2 C vc Set.univ (fun _ => hv) hv =
      ∑ j ∈ Finset.Icc 1 k,
        (Def6.Edens C.m₀ (C.sf.Tm C.N₁) j (Def6.constFld (fun i => (hv i : ℂ)))
            (Def6.constFld (hC hv)) -
          corrSum (fun y x => vc.v1 j (Def6.unlift j (x - y)))
            (fun y x => vc.v2 j (Def6.unlift j (x - y)))
            (Def6.nuIdeal S.L k (C.sf.ν k) j) ((Finset.univ : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)).filter
              (Localization.Aligned (S.L ^ j)))
            ((Finset.univ : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)).filter
              (Localization.Aligned (S.L ^ j)))
            (Def6.constFld (fun i => (hv i : ℂ))) (hC hv)) := by
  rw [EresK2_univ]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 hj
  rw [psiJ_const_univ C hv H he hk hj1 hjk]

end Ctx

end Balaban.RootFSpine
