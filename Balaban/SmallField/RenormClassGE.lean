/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgLiftC
public import Balaban.SmallField.RenormAnisoBridgeInf
public import Balaban.SmallField.RenormClassTube

/-!
# The cut-off term of `T∞` at an arbitrary centre on the anisotropic polydisc

The analogues of `EauxC_rot`, `EauxC_orth` and of `GE_analyticAt`, `GE_rot`, `GE_norm_le`
(`Def6AvgLiftC`) with the isotropic ball of radius `liftRadius` replaced by the anisotropic polydisc
`polyAniso` of radius `anisoRadius` (the geometric input `fp_mem_xiDomA` of `RenormAnisoBridge`
does not depend on the centre).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.SmallField Balaban.Multiscale Balaban.Background Balaban.Localization
  Metric Set Filter

variable {d L N₁ m₁ k N : ℕ} {ϱ : ℝ}

section CoreCA

variable [NeZero L] [NeZero N₁]

variable {P : Consts} {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ}

/-- **Rotation invariance of the class term at the centre `y` on the anisotropic polydisc** (from
(H.3) `rotE`), as `Eaux_rotA` at an arbitrary centre block. -/
theorem EauxC_rotA (hsf : IsSF P β ν a Tm ρd Ek)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (y : Site d) (hnw : NonWind L N₁ m₁ k j X') (hy : y ∈ X') (i₀ : Fin N)
    {δ r B : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hB : 0 ≤ B) (hrδ : 4 * N * (r * (1 + N * B)) ≤ δ)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsRot M) (hMb : ∀ i k, ‖M i k‖ ≤ B)
    {u u' : Cfg d N X'} (hu : u ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X')
    (hu' : u' ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X') (hrot : rotCfgL M X' u = u') :
    EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X' u' = EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X' u := by
  set x₀ : CTorus d L N₁ m₁ k := blockPt j y with hx₀def
  have hx₀ : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x₀ ∈ X' :=
    blockPt_mem_Ypoly hjk hnw hy
  have hNB : 0 ≤ (N : ℝ) * B := by positivity
  set ρs : ℝ := r * (1 + N * B) with hρs
  have hrs : r ≤ ρs := by rw [hρs]; nlinarith
  have hXi := xiDom_of_polyA hsf hBg hν hj1 hjk hX i₀ hδ0 hδc0 hδc1 hr0 hr1 hrs hrδ hε _
    (fun x i => (fieldOf_sub_le_poly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (j := j) hu hr0.le
      x i).trans hrs) (fun x x' h => fieldOf_block u h) hu
  have h0u : fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u' x₀ =
      M.mulVec (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u x₀) := by
    have := fieldOf_rot (j := j) (i₀ := i₀) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) M u
      (x := x₀) hx₀
    rw [← hrot, this]; rfl
  have hMe : ∀ i, ‖(M.mulVec (Pi.single i₀ 1 : Fin N → ℂ)) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤
      ρs := by
    intro i
    have h1 := fieldOf_sub_le_poly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (j := j) hu' hr0.le x₀ i
    have h2 := fun k' =>
      fieldOf_sub_le_poly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (j := j) hu hr0.le x₀ k'
    have e1 : (M.mulVec (Pi.single i₀ 1 : Fin N → ℂ)) i - (Pi.single i₀ 1 : Fin N → ℂ) i =
        (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u' x₀ i -
            (Pi.single i₀ 1 : Fin N → ℂ) i) -
          ∑ k', M i k' * (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u x₀ k' -
            (Pi.single i₀ 1 : Fin N → ℂ) k') := by
      rw [h0u]
      simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [e1]
    calc _ ≤ ‖fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u' x₀ i -
            (Pi.single i₀ 1 : Fin N → ℂ) i‖ +
          ‖∑ k', M i k' * (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u x₀ k' -
            (Pi.single i₀ 1 : Fin N → ℂ) k')‖ :=
          norm_sub_le _ _
      _ ≤ r + ∑ _k' : Fin N, B * r := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k' _ => ?_)
          rw [norm_mul]
          exact mul_le_mul (hMb i k') (h2 k') (norm_nonneg _) hB
      _ = ρs := by rw [hρs]; simp; ring
  have hXirot : XiDom (Tm.gs j (Ypoly j X')) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j
      (P.eps d L j)
      (rotField M (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u))
      (rotField M (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k (ν k) j) X' u)) := by
    rw [← hOf_rot, hrot]
    refine xiDom_of_polyA hsf hBg hν hj1 hjk hX i₀ hδ0 hδc0 hδc1 hr0 hr1 hrs hrδ hε _
      (fun x i => ?_) (fun x x' h => ?_) hu'
    · by_cases hx : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x ∈ X'
      · rw [← fieldOf_rot M u hx, hrot]
        exact (fieldOf_sub_le_poly hu' hr0.le x i).trans hrs
      · have : fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u x =
            (Pi.single i₀ 1 : Fin N → ℂ) := by
          funext i; simp [fieldOf, hx]
        have e : rotField M (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u) x =
            M.mulVec (Pi.single i₀ 1 : Fin N → ℂ) := by
          simp [rotField, this]
        rw [e]; exact hMe i
    · simp only [rotField]
      rw [fieldOf_block u h]
  have hr := hsf.rotE j hj1 hjk x₀ (Ypoly j X') hX hx₀ M hM _ _ hXi hXirot
  unfold EauxC
  rw [← hr]
  refine hsf.localE j x₀ (Ypoly j X') _ _ _ _ (fun x hx => ⟨?_, ?_⟩)
  · rw [← hrot, fieldOf_rot M u hx]
  · rw [← hrot, hOf_rot]

/-- **Rotation invariance of the class term at the centre `y` for `O(N, ℂ)` on the anisotropic
polydisc**, through one real reflection of a coordinate `p ≠ i₀`. -/
theorem EauxC_orthA (hsf : IsSF P β ν a Tm ρd Ek)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (y : Site d) (hnw : NonWind L N₁ m₁ k j X') (hy : y ∈ X') {i₀ p : Fin N} (hp : p ≠ i₀)
    {δ r B : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hB : 1 ≤ B) (hrδ : 4 * N * (r * (1 + N * B)) ≤ δ)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsOrth M) (hMb : ∀ i k, ‖M i k‖ ≤ B)
    {u u' : Cfg d N X'} (hu : u ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X')
    (hu' : u' ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X') (hrot : rotCfgL M X' u = u') :
    EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X' u' = EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X' u := by
  have hB0 : 0 ≤ B := by linarith
  rcases det_isOrth hM with hd | hd
  · exact EauxC_rotA hsf hBg hν hj1 hjk hX y hnw hy i₀ hδ0 hδc0 hδc1 hr0 hr1 hB0 hrδ hε
      ⟨hM, Or.inr hd⟩ hMb hu hu' hrot
  · set Pm := reflP N p with hPm
    have hPpoly : rotCfgL Pm X' u ∈ polyAniso i₀ (nuIdeal L k (ν k) j) r X' :=
      rotCfgL_reflP_mem_polyAniso hp hu
    have h1 := EauxC_rotA hsf hBg hν hj1 hjk hX y hnw hy i₀ hδ0 hδc0 hδc1 hr0 hr1 hB0 hrδ hε
      (isRot_reflP p) (fun i k => (reflP_norm_le p i k).trans hB) hu hPpoly rfl
    have hMP : IsRot (M * Pm) := by
      refine ⟨?_, Or.inr ?_⟩
      · rw [Matrix.transpose_mul, hPm, reflP_transpose, Matrix.mul_assoc,
          ← Matrix.mul_assoc M.transpose, hM, Matrix.one_mul, reflP_mul_self]
      · rw [Matrix.det_mul, hd, hPm, reflP_det]; norm_num
    have hMPb : ∀ i k, ‖(M * Pm) i k‖ ≤ B := by
      intro i k
      rw [hPm]
      unfold reflP
      rw [Matrix.mul_diagonal]
      by_cases h : k = p
      · simp [h]; exact hMb i p
      · simp [h]; exact hMb i k
    have h2 := EauxC_rotA hsf hBg hν hj1 hjk hX y hnw hy i₀ hδ0 hδc0 hδc1 hr0 hr1 hB0 hrδ hε
      hMP hMPb hPpoly hu' (by
        have hPP : Pm * Pm = 1 := by rw [hPm]; exact reflP_mul_self p
        rw [← rotCfgL_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]; exact hrot)
    rw [h2, h1]

end CoreCA

section GEA

variable [NeZero L] {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

section Facts

variable (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N}
include hF hn

/-- The domain inclusion at the data of a point of the anisotropic polydisc, on the torus `n`. -/
theorem GE_xiDomA {X' : Finset (Site d)} {n : ℕ}
    (hgood : GoodAt L m₁ k P.m₀ j X' n) {c : Cfg d N X'}
    (hc : c ∈ polyAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X') :
    haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
    XiDom ((Tm (torusSeq L P.m₀ n)).gs j (Ypoly j X')) (aIdeal L k (a k))
      (bgMass L k (β k) (ν k)) j (P.eps d L j) (fieldOf j i₀ X' c)
      (hOf (nuIdeal L k (ν k) j) X' c) := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  obtain ⟨hr0, hr1, δ, hδ0, hδc0, hδc1, hε, hrδ⟩ := hF.anisoRadiusOK hn.hsmall i₀
  have hN : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
  exact fp_mem_xiDomA (hF.torus _) (bgHyp_of_class hF.admissible hF.coeff hn.hd hn.hL hn.hϱ)
    hF.coeff.nu_pos hn.hj1 hn.hjk hgood.2 i₀ hδ0 hδc0 hδc1 hr0 hr1 (by nlinarith) hε hc

/-- On the anisotropic polydisc around the reference point the data of a configuration extend into
the analyticity domain on every torus on which the polymer is good, so the cut-off is inactive. -/
theorem GE_suppA {X' : Finset (Site d)} (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    {y : Site d} (hy : y ∈ X') {c : Cfg d N X'}
    (hc : c ∈ polyAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X') :
    Supp P β ν a Tm j ⟨X', y, fieldInfOf L j i₀ X' c, hInfOf (nuIdeal L k (ν k) j) X' c⟩ := by
  refine ⟨hX, hy, ?_⟩
  show ∀ᶠ n in atTop, _
  filter_upwards [hX] with n hn'
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  refine ⟨fieldOf j i₀ X' c, hOf (nuIdeal L k (ν k) j) X' c, fun x _ => ?_,
    GE_xiDomA hF hn hn' hc⟩
  rw [pullFld_fieldInfOf, pullFld_hInfOf]
  exact ⟨rfl, rfl⟩

theorem GE_of_polyA {X' : Finset (Site d)} (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    {y : Site d} (hy : y ∈ X') {c : Cfg d N X'}
    (hc : c ∈ polyAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X') :
    GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' c =
      Einf P.m₀ Tm j y X' (fieldInfOf L j i₀ X' c) (hInfOf (nuIdeal L k (ν k) j) X' c) := by
  unfold GE FB
  rw [ite_eq_left (GE_suppA hF hn hX hy hc)]

theorem GE_eq_EauxCA {X' : Finset (Site d)}
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    {y : Site d} (hy : y ∈ X') {c : Cfg d N X'}
    (hc : c ∈ polyAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X') {n : ℕ}
    (hgood : GoodAt L m₁ k P.m₀ j X' n) :
    GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' c =
      EauxC (Tm (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k (ν k) j) y X' c := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  rw [GE_of_polyA hF hn hX hy hc,
    Einf_eq_torus hF.torusIndep hn.hj1 hn.hjk hy hX _ _ (torusSeq L P.m₀ n) hgood.1 hgood.2,
    pullFld_fieldInfOf, pullFld_hInfOf]
  rfl

theorem GE_analyticAtA {X' : Finset (Site d)}
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    {y : Site d} (hy : y ∈ X') {u₀ : Cfg d N X'}
    (hu : u₀ ∈ polyAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X') :
    AnalyticAt ℂ (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X') u₀ := by
  obtain ⟨n, hgood⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have hXi := GE_xiDomA hF hn hgood hu
  have hE := (hF.torus (torusSeq L P.m₀ n)).analyticE j hn.hj1 hn.hjk (blockPt j y) (Ypoly j X')
    hgood.2 (blockPt_mem_Ypoly hn.hjk hgood.1 hy)
    (fieldOf j i₀ X' u₀, hOf (nuIdeal L k (ν k) j) X' u₀) hXi
  have han : AnalyticAt ℂ (EauxC (Tm (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k (ν k) j) y X') u₀ :=
    AnalyticAt.comp (g := fun p : Fld d L (torusSeq L P.m₀ n) m₁ k N ×
        Fld d L (torusSeq L P.m₀ n) m₁ k N =>
      (Tm (torusSeq L P.m₀ n)).E j (blockPt j y) (Ypoly j X') p.1 p.2)
    (f := fun c : Cfg d N X' => ((fieldOf (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k)
      j i₀ X' c, hOf (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k)
      (nuIdeal L k (ν k) j) X' c) : Fld d L (torusSeq L P.m₀ n) m₁ k N ×
        Fld d L (torusSeq L P.m₀ n) m₁ k N)) (x := u₀) hE
    (analyticAt_fp j i₀ (nuIdeal L k (ν k) j) X' u₀)
  refine han.congr ?_
  filter_upwards [isOpen_polyAniso.mem_nhds hu] with c hc
  exact (GE_eq_EauxCA hF hn hX hy hc hgood).symm

theorem GE_rotA (hne : i₁ ≠ i₀) {X' : Finset (Site d)}
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    {y : Site d} (hy : y ∈ X') {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsOrth M)
    (hMb : ∀ i k, ‖M i k‖ ≤ rotB N) {u u' : Cfg d N X'}
    (hu : u ∈ polyAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X')
    (hu' : u' ∈ polyAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X')
    (hrot : rotCfgL M X' u = u') :
    GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' u' =
      GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' u := by
  obtain ⟨n, hgood⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  rw [GE_eq_EauxCA hF hn hX hy hu' hgood, GE_eq_EauxCA hF hn hX hy hu hgood]
  obtain ⟨hr0, hr1, δ, hδ0, hδc0, hδc1, hε, hrδ⟩ := hF.anisoRadiusOK hn.hsmall i₀
  exact EauxC_orthA (hF.torus _) (bgHyp_of_class hF.admissible hF.coeff hn.hd hn.hL hn.hϱ)
    hF.coeff.nu_pos hn.hj1 hn.hjk hgood.2 y hgood.1 hy hne hδ0 hδc0 hδc1 hr0 hr1
    (one_le_rotB i₀) hrδ hε hM hMb hu hu' hrot

theorem GE_norm_leA {X' : Finset (Site d)} (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    {y : Site d} (hy : y ∈ X') {c : Cfg d N X'}
    (hc : c ∈ polyAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X') :
    ‖GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' c‖ ≤
      P.E₀ * Real.exp (-P.κ * dInf L m₁ k P.m₀ j X') := by
  obtain ⟨n₀, hgood₀⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  refine bound_dInf hgood₀ (norm_nonneg _) hF.admissible.κ_pos.le fun n hgood => ?_
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  rw [GE_eq_EauxCA hF hn hX hy hc hgood]
  exact (hF.torus _).boundE j hn.hj1 hn.hjk (blockPt j y) (Ypoly j X') hgood.2
    (blockPt_mem_Ypoly hn.hjk hgood.1 hy) _ _ (GE_xiDomA hF hn hgood hc)

end Facts

end GEA

end Balaban.SmallField.Def6
