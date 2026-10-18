/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLabelsPlus
public import Balaban.Fluctuation.LocalClassDensityLevelCast

/-!
# The labels of the new level on the local charts: reduction to a local family
(`StepTowerLocalChart`)

P3 pp. 78–79 ((4.44)–(4.47)): the term of the localization domain `Y` is the term of the step
recomputed with the generating set `𝔹_{k+1}(Y)` (the function (4.32) is unchanged when `𝔹_{k+1}` is
replaced by a generating set agreeing with it on `Y₁`, with the parameters `s = 0` off `Y₁`); it is
therefore analytic on `Ξ^c_{k+1}(𝔹_{k+1}(Y); 1, ε′)` (4.46), bounded there by (4.47), and it depends
only on the fields restricted to `Y` (p. 78).  In the class of the formalization the generating set
of the label polymer `Y` is `castG hc (localB (k + 1) … (Yp Y) hsep)` (W1057), and the polymer of the
label `T′` (a set of cubes of index one) is `Y⁺(T′) = sitesOf (piHull m₀ (thickSet 𝔹 (sitesOf T′)))`
(W1075, W1076).

`newLabels_castInputs_of_localFamily` states what the recomputed terms must provide and derives
from it the label inputs `hTlblock`, `hTlan`, `hTlloc`, `hTlbd`, `hTlrot` and `hDz` of
`localClass_newLevel_of_expansion_cast`, in their exact forms, for the labels
`Tl T′ y Y p = f (blockIndex y) T′ p` if `Y = Y⁺(T′)`, `0` otherwise, and the bounds
`EbE T′ y Y = b (blockIndex y) T′` if `Y = Y⁺(T′)`, `0` otherwise (the form of
`newLabels_hsum_of_chain_bound_thick`, which gives `hsum`).  The family `f z T′` is a function of
the pair of fields with:

* (A1) analyticity on the chart `Ξ^c_{k+1}(𝔹(Y⁺(T′)); 1, ε_{k+1})` of the local generating set;
* (A2) the bound `b z T′` of the coefficient of the step there;
* (A3) dependence only on the fields on `Y⁺(T′)` among the pairs of the chart of radius
  `K_loc ε_{k+1}`, `K_loc = (2 K₁ + 2) C₁` (the chart in which the class completes its terms);
* (A4) invariance under the real rotations on the chart of radius `ε_{k+1}`;
* (A5) equality with the coefficient `e z (π (clipRaw 𝔹 q), 0) T′` of the step at the pairs `q` of
  the step chart `Ξ^c_{k+1}(𝔹_{k+1}; 1, ε_{k+1})` (the replacement identity of P3 p. 79).

This is a conditional statement: no family with (A1)–(A5) is constructed here.  The chain's
coefficient family `e` is defined only on the parameters `physV` of the step chart, and (A1) cannot
be obtained from it by extending a datum of the local chart to the step chart (a configuration
winding around a hole of `Y⁺(T′)` has no extension with small gradients, `N = 2`); the family has to
be the coefficient of the step recomputed on `𝔹(Y⁺(T′))` (notes, `WIDEGEN.md`, W1081).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec
  Balaban.LargeField Matrix

section LocalFamily

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp) (C : StepClass d L N₁ m₁ k N ϱ)

open Classical in
/-- **The label inputs of the new level from a family recomputed on the local generating sets.**
For a coefficient family `e` of the step with the clauses of the class chain used by the sum
identity (rooted polymer support of index one, value `E0locJ C z` at every datum of the step chart
of radius `eps`), the class radius `ε_{k+1} = P.eps d L (k + 1) ≤ eps`, and a family `f` with
(A1)–(A5) of the module docstring on the local generating sets
`castG hc (localB (k + 1) … (Yp Y⁺(T′)) hsep)`, the labels `Tl` and bounds `EbE` fixed by `hTl`,
`hEbE` satisfy the inputs `hTlblock`, `hTlan`, `hTlloc`, `hTlbd`, `hTlrot` and `hDz` of
`localClass_newLevel_of_expansion_cast` (`𝒯E = Finset.univ`, weights `S.a`, mass `S.ν`, density
`densE0 C`). -/
theorem newLabels_castInputs_of_localFamily {P : Consts} (hN : L ^ P.m₀ ∣ N₁) (hL : 3 ≤ L)
    (h3 : 3 ≤ L ^ (P.m₀ + m₁))
    (hG : S.G' = levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
    (hε : P.eps d L (k + 1) ≤ eps)
    {N₁' m₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    (hsep : ϱ ≤ minSep L (L ^ m₁'))
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁' m₁' (k + 1)))
    -- the coefficient family of the step chain
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (hπ : ∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩)
    (e : RootIdx d L N₁ m₁ (k + 1) → physParam N S →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℂ)
    (hsupp : ∀ z θ T, e z θ T ≠ 0 →
      rootCube (m₀ := 1) z ∈ T ∧ IsPolyDom 1 (k + 1) (sitesOf T))
    (hval : ∀ z (D : BgData S.G' N), XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      Jr.E0locJ C z (rawOf D) =
        ∑ T, e z ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), 0) T)
    (b : RootIdx d L N₁ m₁ (k + 1) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℝ)
    -- the family recomputed on the local generating sets
    (f : RootIdx d L N₁ m₁ (k + 1) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hfan : ∀ z T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
      AnalyticOnNhd ℂ (f z T)
        {p | (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
          (castG hc (localB (k + 1) (le_refl (k + 1))
            (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2})
    (hfbd : ∀ z T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
      ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1))
          (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2 →
      ‖f z T p‖ ≤ b z T)
    (hfloc : ∀ z T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom S.a S.ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
        FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1))
          (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2 →
      (xiFieldDom S.a S.ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
        FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1))
          (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p'.1 p'.2 →
      (∀ x ∈ sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))), p.1 x = p'.1 x ∧ p.2 x = p'.2 x) →
      f z T p = f z T p')
    (hfrot : ∀ z T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
      ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1))
          (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2 →
      f z T (rotField (cmat Q) p.1, rotField (cmat Q) p.2) = f z T p)
    (hfval : ∀ z T (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      XiDom S.G' S.a S.ν (k + 1) (P.eps d L (k + 1)) q.1 q.2 →
      f z T q = e z (π (clipRaw S.G' q), 0) T)
    -- the labels and their bounds
    (Tl : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTl : ∀ T y Y p, Tl T y Y p =
      if sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))) = Y then f (blockIndex y) T p else 0)
    (EbE : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) → ℝ)
    (hEbE : ∀ T y Y, EbE T y Y =
      if sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))) = Y then b (blockIndex y) T else 0) :
    -- `hTlblock`
    (∀ τ ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := k + 1) 1 (k + 1) Set.univ))), ∀ z z' Y p,
      blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) z =
        blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) z' →
      Tl τ z Y p = Tl τ z' Y p) ∧
    -- `hTlan`
    (∀ τ ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := k + 1) 1 (k + 1) Set.univ))), ∀ z Y, IsPolyDom P.m₀ (k + 1) Y →
      AnalyticOnNhd ℂ (Tl τ z Y)
        {p | (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
          (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p.1 p.2}) ∧
    -- `hTlloc`
    (∀ τ ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := k + 1) 1 (k + 1) Set.univ))), ∀ z Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom S.a S.ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
        FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p.1 p.2 →
      (xiFieldDom S.a S.ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
        FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p'.1 p'.2 →
      (∀ x ∈ Y, p.1 x = p'.1 x ∧ p.2 x = p'.2 x) → Tl τ z Y p = Tl τ z Y p') ∧
    -- `hTlbd`
    (∀ τ ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := k + 1) 1 (k + 1) Set.univ))), ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → z ∈ Y →
      ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p.1 p.2 →
      ‖Tl τ z Y p‖ ≤ EbE τ z Y) ∧
    -- `hTlrot`
    (∀ τ ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := k + 1) 1 (k + 1) Set.univ))), ∀ z Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p.1 p.2 →
      Tl τ z Y (rotField (cmat Q) p.1, rotField (cmat Q) p.2) = Tl τ z Y p) ∧
    -- `hDz`
    (∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1))) q.1 q.2 →
      ∑ᶠ Y ∈ polysAt P.m₀ (k + 1) y,
        ∑ τ ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (K := k + 1) 1 (k + 1) Set.univ))), Tl τ y Y q = Jr.densE0 C y q) := by
  -- the labels as functions of the field pair, on `Y = Y⁺(T′)` and off it
  have hon : ∀ T y, Tl T y (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) =
      f (blockIndex y) T := fun T y => by
    funext p; rw [hTl]; simp
  have hoff : ∀ T y Y, sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))) ≠ Y →
      Tl T y Y = fun _ => 0 := fun T y Y hY => by
    funext p; rw [hTl]; simp only [hY, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T _ z z' Y p hzz
    have hb : blockIndex z = blockIndex z' :=
      rootSite_injective (by rw [rootSite_blockIndex, rootSite_blockIndex, hzz])
    rw [hTl, hTl, hb]
  · intro T _ z Y hY
    by_cases hTY : sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))) = Y
    · subst hTY
      rw [hon]
      exact hfan _ T hY
    · rw [hoff T z Y hTY]
      exact fun _ _ => analyticAt_const
  · intro T _ z Y hY p p' hp hp' hpp
    by_cases hTY : sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))) = Y
    · subst hTY
      rw [hon]
      exact hfloc _ T hY p p' hp hp' hpp
    · rw [hoff T z Y hTY]
  · intro T _ z Y hY _ p hp
    rw [hEbE]
    by_cases hTY : sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))) = Y
    · subst hTY
      rw [hon, ite_eq_left rfl]
      exact hfbd _ T hY p hp
    · rw [hoff T z Y hTY, ite_eq_right hTY, norm_zero]
  · intro T _ z Y hY Q hQ p hp
    by_cases hTY : sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))) = Y
    · subst hTY
      rw [hon]
      exact hfrot _ T hY Q hQ p hp
    · rw [hoff T z Y hTY]
  · intro y q hq
    have hq' : XiDom S.G' S.a S.ν (k + 1) (P.eps d L (k + 1)) q.1 q.2 := by
      rw [hG]; exact hq
    -- on the step chart the labels are those of the step chain
    have hstep : ∀ T Y, Tl T y Y q =
        if sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))) = Y then
          e (blockIndex y) (π (clipRaw S.G' q), 0) T else 0 := by
      intro T Y
      rw [hTl]
      split_ifs with hTY
      · exact hfval _ T q hq'
      · rfl
    have hsum := newLabels_sum_eq_densE0_hull Jr C
      (fun T => sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))
      (fun y _ hr hp => rootHullThick_mem S.hG' hN hL h3 y hr hp) π hπ e hsupp hval
      (fun T y Y q => if sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))) = Y then
          e (blockIndex y) (π (clipRaw S.G' q), 0) T else 0)
      (fun _ _ _ _ => rfl) hε y q hq'
    rw [← hsum]
    exact finsum_congr fun Y => finsum_congr fun _ =>
      Finset.sum_congr rfl fun T _ => hstep T Y

end LocalFamily

end Balaban.Inhabited
