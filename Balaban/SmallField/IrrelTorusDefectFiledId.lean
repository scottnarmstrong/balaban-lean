/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusBound
public import Balaban.SmallField.IrrelTorusDefectSmallSum

/-!
# The filed term of a polymer as a termwise `T + Φ`

* `TPhi_eq_Ttw_add_Phitw`: for the one-polymer family of `premisesTermAniso_centred`, the sum
  `Ttw + Phitw` at the pulled-back data is the expression `TΦ` that `irrelTorus` files at its
  centre, for any aligned centre `y` and any polymer `X ∋ y`;
* `image_unlift_Ypoly`: at the origin, the blocks of `Ypoly j X'` are placed at the shape `X'`;
* `finsum_polysAt_zero_eq_sum`: the complete finite sum at the origin is the finite sum over the
  shapes of the lifted family.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Metric Set Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

variable {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}

open Classical in
/-- **The filed term of one polymer is the termwise `T + Φ` of its pulled-back family**: for the
one-polymer family `T_{y,X}` of `premisesTermAniso_centred`, `T_X(ψ_y, b) + Φ_{y,X}(ψ_y)` is the
expression `TΦ` of `irrelTorus` at the constant field `h`, `b = ν_j h`. -/
theorem TPhi_eq_Ttw_add_Phitw (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ 1) (hj1 : 1 ≤ j) (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hSdef : S = (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
      (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    (Ψ : Fld d L N₁ m₁ k N) (hv : Fin N → ℂ) :
    Ttw (⟨{S}, fun _ => sizeJ P.m₀ j X, fun S' c => trickFnA i₀ ν r (fun c' : Cfg d N S' =>
           Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S' c' (z - y))
             (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S' c')) c⟩ : TermFamily d N)
        i₀ ν S (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s))
        ((ν : ℂ) • hv) +
      Phitw (⟨{S}, fun _ => sizeJ P.m₀ j X, fun S' c => trickFnA i₀ ν r (fun c' : Cfg d N S' =>
           Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S' c' (z - y))
             (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S' c')) c⟩ : TermFamily d N)
        i₀ i₁ ν S (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)) =
    (let e : Fld d L N₁ m₁ k N := constFld (Pi.single i₀ 1)
     let blk : Set (CTorus d L N₁ m₁ k) → Finset (CTorus d L N₁ m₁ k) := fun Z =>
       Finset.univ.filter fun x => Aligned (L ^ j) x ∧ x ∈ Z
     let u : ℂ := sqrtC (dot (Ψ y) (Ψ y))
     let dΨ : Fin d → Fin N → ℂ := fun μ =>
       Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ y
     let g : Fin d → Fin d → ℂ := fun μ μ' =>
       dot (dΨ μ) (dΨ μ') - dot (Ψ y) (dΨ μ) * dot (Ψ y) (dΨ μ') /
         dot (Ψ y) (Ψ y)
     let lift : CTorus d L N₁ m₁ k → Fin d → ℂ := fun z μ =>
       ((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) μ : ℤ) : ℂ)
     let a : Set (CTorus d L N₁ m₁ k) → CTorus d L N₁ m₁ k → ℂ := fun Z x =>
       fderiv ℂ (fun Ψ' => Tm.E j y Z Ψ' e) e (blockDir L j x i₀)
     Tm.E j y X e e + (u - 1) * ∑ x ∈ blk X, a X x
           + (dot (Ψ y) (constFld hv y) / u - 1) *
             fderiv ℂ (fun h' => Tm.E j y X e h') e e
           - (1 / 4 : ℂ) * ∑ μ, ∑ μ', g μ μ' * ∑ x ∈ blk X, ∑ x' ∈ blk X,
               D2 (fun Ψ' => Tm.E j y X Ψ' e) e (blockDir L j x i₁)
                 (blockDir L j x' i₁) *
                 ((lift x μ - lift x' μ) * (lift x μ' - lift x' μ'))) := by
  have hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S :=
    fun z hz => by rw [hSdef]; exact mem_placeSet hN hjk hy hX hz
  have hmS : ∀ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) ∈ S :=
    fun x hx => by rw [hSdef]; exact Finset.mem_image_of_mem _ hx
  have hT := tubeHypA_shiftTerm hcl hBg hν hμν hνb hj1 hjk hy hX hyX hS hne hrad
  have hr0 := hrad.1
  have hr1 := hrad.2.1
  have hE := analyticAt_term_ref (y := y) hcl hBg hν hμν hj1 hjk hX hyX i₀ hrad
  have hνc : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  set ψ : Site d → Spin N := fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)
    with hψ
  have hψ0 : ψ 0 = Ψ y := by simp only [hψ, ibase_zero, add_zero]
  have hψeU : ∀ μ, ψ (eU μ) = Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) :=
    fun μ => by simp only [hψ, ibase_eU]
  set T : TermFamily d N := ⟨{S}, fun _ => sizeJ P.m₀ j X, fun S' c => trickFnA i₀ ν r
    (fun c' : Cfg d N S' =>
      Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S' c' (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S' c')) c⟩ with hTdef
  have hTterm : T.term S = trickFnA i₀ ν r (fun c' : Cfg d N S =>
      Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c')) := rfl
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
  rw [hTtw, hPhi]
  have hcy : (constFld hv : Fld d L N₁ m₁ k N) y = hv := rfl
  simp only [hcy]
  ring


open Classical in
/-- At the origin, the placement of the blocks of `Ypoly j X'` is the shape `X'` itself. -/
theorem image_unlift_Ypoly {X' : Finset (Site d)} (hjk : j ≤ k) (hnw : NonWind L N₁ m₁ k j X') :
    (Finset.univ.filter (fun x : CTorus d L N₁ m₁ k =>
        Aligned (L ^ j) x ∧ x ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')).image
      (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - 0)) = X' := by
  ext s
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, sub_zero]
  constructor
  · rintro ⟨x, ⟨_, hx⟩, rfl⟩
    exact hx
  · intro hs
    refine ⟨ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s, ⟨aligned_ibase hjk s, ?_⟩, ?_⟩
    · show unlift j (ibase j s) ∈ X'
      rw [unlift_ibase hjk (hnw s hs)]
      exact hs
    · exact unlift_ibase hjk (hnw s hs)


open Classical in
/-- The complete finite torus sum at the origin is the finite sum over the shapes of the lifted
family. -/
theorem finsum_polysAt_zero_eq_sum (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    (f : Set (CTorus d L N₁ m₁ k) → ℂ) :
    ∑ᶠ Z ∈ polysAt P.m₀ j (0 : CTorus d L N₁ m₁ k), f Z =
      ∑ X' ∈ (liftPolys_finite (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j).toFinset,
        f (Ypoly j X') := by
  rw [finsum_polysAt_reindex hjk hN 0 f, unlift_zero]
  have hset : {X' : Finset (Site d) | (0 : Site d) ∈ X' ∧ NonWind L N₁ m₁ k j X' ∧
      IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')} =
      liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j := rfl
  rw [hset]
  exact finsum_mem_eq_finite_toFinset_sum _ _

end Balaban.SmallField.Def6v2
