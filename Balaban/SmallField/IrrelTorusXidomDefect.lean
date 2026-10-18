/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusBound

/-!
# Exact label identity with the tube extension discrepancy

For a non-special label, the subtraction terms of the torus irrelevant functional agree
with those of the termwise anisotropic irrelevant functional. The difference of their values
is exactly the class term at the datum minus its tube extension there.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Metric Set Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

variable {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}

open Classical in
/-- The exact discrepancy identity for a non-special label. -/
theorem irrelTorus_eq_Itw_centred_add_discrepancy (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hj1 : 1 ≤ j) (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hXne : X ≠ box (cbase (cellSide L P.m₀ m₁ j) y -
      natT fun _ => L / 2 * cellSide L P.m₀ m₁ j) (L * cellSide L P.m₀ m₁ j))
    (hSdef : S = (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
      (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    {Ψ : Fld d L N₁ m₁ k N}
    (hv : Fin N → ℂ) :
    irrelTorus P.m₀ Tm i₀ i₁ j y X Ψ (constFld hv) =
      Itw (⟨{S}, fun _ => sizeJ P.m₀ j X, fun S' c => trickFnA i₀ ν r (fun c' : Cfg d N S' =>
           Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S' c' (z - y))
             (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S' c')) c⟩ : TermFamily d N)
        i₀ i₁ ν S (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s))
        ((ν : ℂ) • hv) +
      Tm.E j y X Ψ (constFld hv) -
      trickFnA i₀ ν r (fun c' : Cfg d N S =>
        Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
          (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c'))
        (pack S (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s))
          ((ν : ℂ) • hv)) := by
  have hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S :=
    fun z hz => by rw [hSdef]; exact mem_placeSet hN hjk hy hX hz
  have hmS : ∀ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) ∈ S :=
    fun x hx => by rw [hSdef]; exact Finset.mem_image_of_mem _ hx
  have hT := tubeHypA_shiftTerm hcl hBg hν hμν hj1 hjk hy hX hyX hS hne hrad
  have hr0 := hrad.1
  have hr1 := hrad.2.1
  have hE := analyticAt_term_ref (y := y) hcl hBg hν hμν hj1 hjk hX hyX i₀ hrad
  have hνc : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  set ψ : Site d → Spin N := fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)
    with hψ
  have hψ0 : ψ 0 = Ψ y := by simp only [hψ, ibase_zero, add_zero]
  have hψeU : ∀ μ, ψ (eU μ) = Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) :=
    fun μ => by simp only [hψ, ibase_eU]
  have hψx : ∀ x, Aligned (L ^ j) x →
      ψ (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)) = Ψ x := fun x hx => by
    simp only [hψ]
    rw [add_ibase_unlift_sub hjk hy x, cbase_eq_self_of_aligned hx]
  -- the family
  set T : TermFamily d N := ⟨{S}, fun _ => sizeJ P.m₀ j X, fun S' c => trickFnA i₀ ν r
    (fun c' : Cfg d N S' =>
      Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S' c' (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S' c')) c⟩ with hTdef
  have hTterm : T.term S = trickFnA i₀ ν r (fun c' : Cfg d N S =>
      Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c')) := rfl
  -- the tensors
  have hA : ∀ x (hx : x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)),
      tensA i₀ ν S (T.term S) ⟨_, hmS x hx⟩ =
        fderiv ℂ (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1)))
          (constFld (Pi.single i₀ 1)) (blockDir L j x i₀) := fun x hx => by
    rw [hTterm]
    exact tensA_centred hT hjk hy hν hr0 hE (Finset.mem_filter.1 hx).2.1 _
  have hB : ∀ x (hx : x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X))
      x' (hx' : x' ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)),
      tensB i₀ i₁ ν S (T.term S) ⟨_, hmS x hx⟩ ⟨_, hmS x' hx'⟩ =
        D2 (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1))) (constFld (Pi.single i₀ 1))
          (blockDir L j x i₁) (blockDir L j x' i₁) := fun x hx x' hx' => by
    rw [hTterm]
    exact tensB_centred hT hjk hy hν hr0 hr1 hE i₁ (Finset.mem_filter.1 hx).2.1
      (Finset.mem_filter.1 hx').2.1 _ _
  have hsumA : ∀ G : Site d → ℂ, ∑ s : ↥S, tensA i₀ ν S (T.term S) s * G s.1 =
      ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
        fderiv ℂ (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1)))
          (constFld (Pi.single i₀ 1)) (blockDir L j x i₀) *
          G (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)) := by
    intro G
    rw [sum_placeSet hjk hy hSdef]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [hmS x hx, ↓reduceDIte]
    rw [hA x hx]
  -- `T_X`
  have hTtw : Ttw T i₀ ν S ψ ((ν : ℂ) • hv) =
      Tm.E j y X (constFld (Pi.single i₀ 1)) (constFld (Pi.single i₀ 1)) +
        (sqrtC (dot (Ψ y) (Ψ y)) - 1) *
          ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
            fderiv ℂ (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1)))
              (constFld (Pi.single i₀ 1)) (blockDir L j x i₀) +
        (dot (Ψ y) hv / sqrtC (dot (Ψ y) (Ψ y)) - 1) *
          fderiv ℂ (fun h' => Tm.E j y X (constFld (Pi.single i₀ 1)) h')
            (constFld (Pi.single i₀ 1)) (constFld (Pi.single i₀ 1)) := by
    have h1 := hsumA (fun _ => 1)
    simp only [mul_one] at h1
    simp only [Ttw, uInv, vInv, hψ0]
    rw [h1, hTterm, term_refPt_centred hT hν hr0, fderivB_centred hT hν hr0 hE, dot_smul_right]
    have e : ((ν : ℂ) * dot (Ψ y) hv / sqrtC (dot (Ψ y) (Ψ y)) - ν) *
        ((ν : ℂ)⁻¹ * fderiv ℂ (fun h' => Tm.E j y X (constFld (Pi.single i₀ 1)) h')
          (constFld (Pi.single i₀ 1)) (constFld (Pi.single i₀ 1))) =
        ((ν : ℂ) * (ν : ℂ)⁻¹) * ((dot (Ψ y) hv / sqrtC (dot (Ψ y) (Ψ y)) - 1) *
          fderiv ℂ (fun h' => Tm.E j y X (constFld (Pi.single i₀ 1)) h')
            (constFld (Pi.single i₀ 1)) (constFld (Pi.single i₀ 1))) := by ring
    rw [e, mul_inv_cancel₀ hνc, one_mul]
  -- `A_{y,X}`
  have hAx : Ax T i₀ ν ψ S = (1 / 2 : ℂ) *
      ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
        fderiv ℂ (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1)))
          (constFld (Pi.single i₀ 1)) (blockDir L j x i₀) *
          (dot (Ψ x) (Ψ x) - dot (Ψ y) (Ψ y)) := by
    have h1 := hsumA (fun s => dot (ψ s) (ψ s) - dot (ψ 0) (ψ 0))
    unfold Ax
    rw [h1]
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hψx x (Finset.mem_filter.1 hx).2.1, hψ0]
  -- `Φ_{y,X}`
  have hSx : ∀ μ μ' : Fin d, Sx T i₀ i₁ ν S μ μ' =
      ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
        ∑ x' ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
          D2 (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1))) (constFld (Pi.single i₀ 1))
            (blockDir L j x i₁) (blockDir L j x' i₁) *
          ((((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) μ : ℤ) : ℂ) -
              ((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x' - y) μ : ℤ) : ℂ)) *
            (((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) μ' : ℤ) : ℂ) -
              ((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x' - y) μ' : ℤ) : ℂ))) := by
    intro μ μ'
    unfold Sx
    rw [sum_placeSet hjk hy hSdef]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [hmS x hx, ↓reduceDIte]
    rw [sum_placeSet hjk hy hSdef]
    refine Finset.sum_congr rfl fun x' hx' => ?_
    simp only [hmS x' hx', ↓reduceDIte]
    rw [hB x hx x' hx']
    simp only [Pi.sub_apply, Int.cast_sub]
  have hPhi : Phitw T i₀ i₁ ν S ψ = -(1 / 4 : ℂ) * ∑ μ, ∑ μ',
      (dot (Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ y)
          (Ψ (y + (L ^ j) • (Pi.single μ' 1 : CTorus d L N₁ m₁ k)) - Ψ y) -
        dot (Ψ y) (Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ y) *
          dot (Ψ y) (Ψ (y + (L ^ j) • (Pi.single μ' 1 : CTorus d L N₁ m₁ k)) - Ψ y) /
          dot (Ψ y) (Ψ y)) *
      ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
        ∑ x' ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
          D2 (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1))) (constFld (Pi.single i₀ 1))
            (blockDir L j x i₁) (blockDir L j x' i₁) *
          ((((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) μ : ℤ) : ℂ) -
              ((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x' - y) μ : ℤ) : ℂ)) *
            (((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) μ' : ℤ) : ℂ) -
              ((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x' - y) μ' : ℤ) : ℂ))) := by
    unfold Phitw
    congr 1
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun μ' _ => ?_
    rw [hSx μ μ']
    congr 1
    unfold gradInv
    rw [hψeU μ, hψeU μ', hψ0]
  -- assembly
  have hcy : (constFld hv : Fld d L N₁ m₁ k N) y = hv := rfl
  unfold Itw
  rw [hTtw, hAx, hPhi, hTterm]
  simp only [irrelTorus, hXne, ↓reduceIte, add_zero, hcy, hψ]
  ring


end Balaban.SmallField.Def6v2
