/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLabels
public import Balaban.Inhabited.StepTowerHullPlus

/-!
# The labels of the new level on the enlarged polymer `Y⁺` (`StepTowerNewLabelsPlus`)

The labels of `StepTowerNewLabels.lean` live on the `π′`-hull `Y(T′)` of the cube set `T′`.  The
local charts need the hull of the thickened read set,
`Y⁺(T′) = sitesOf (piHull m₀ (thickSet 𝔹 (sitesOf T′)))`.

* `isPolyDom_piHull_thick`: `Y⁺(T′)` is a polymer of index `m₀` when `sitesOf T′` is a polymer
  (any index) and `𝔹` is a level generating set (every thickened site lies in an aligned `π′` box
  meeting `sitesOf T′`);
* `rootHullThick_mem`: it contains the block of the root;
* `newLabels_stepChart_of_rootFamily_thick`: the statement of `newLabels_stepChart_of_rootFamily`
  with `Y⁺` in place of `Y` (instance of `newLabels_stepChart_of_rootFamily_hull`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

section Thick

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ} {ϱ : ℝ}

/-- **The hull of the thickened set of a polymer is a polymer of index `m₀`.** -/
theorem isPolyDom_piHull_thick {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (hG : IsLevel G K)
    (hN : L ^ m₀ ∣ N₁) (hL : 3 ≤ L) (h3 : 3 ≤ L ^ (m₀ + m₁)) {m₀' j : ℕ}
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ)}
    (hp : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀' j (sitesOf T)) :
    IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K
      (sitesOf (piHull m₀ (thickSet G (sitesOf T)))) := by
  have hsub : sitesOf T ⊆ thickSet G (sitesOf T) := fun _ hx => Or.inl hx
  have hnear := thickSet_near_sitesOf hG hN h3 T
  refine isPolyDom_sitesOf_piHull_of_reach hN (hp.1.mono hsub) fun s hs s' hs' => ?_
  have hX := subset_sitesOf_piHull hN (thickSet G (sitesOf T))
  have hsymm : ∀ a b : CTorus d L N₁ m₁ K,
      (a ∈ sitesOf (piHull m₀ (thickSet G (sitesOf T))) ∧
        b ∈ sitesOf (piHull m₀ (thickSet G (sitesOf T))) ∧ Nbr a b) →
      (b ∈ sitesOf (piHull m₀ (thickSet G (sitesOf T))) ∧
        a ∈ sitesOf (piHull m₀ (thickSet G (sitesOf T))) ∧ Nbr b a) :=
    fun a b h => ⟨h.2.1, h.1, h.2.2.symm⟩
  have hto : ∀ s ∈ thickSet G (sitesOf T), ∃ x ∈ sitesOf T, Relation.ReflTransGen
      (fun a b => a ∈ sitesOf (piHull m₀ (thickSet G (sitesOf T))) ∧
        b ∈ sitesOf (piHull m₀ (thickSet G (sitesOf T))) ∧ Nbr a b) s x := by
    intro s hs
    obtain ⟨x, hx, hnr⟩ := hnear s hs
    obtain ⟨b, hba, hxb, hsb⟩ := exists_box_of_cellNear hN hL hnr
    have hb : b ∈ piBases m₀ (thickSet G (sitesOf T)) :=
      ⟨hba, ⟨s, hsb, hs⟩⟩
    exact ⟨x, hx, (rtg_symm hsymm (reach_piBases_box hN hb hsb)).trans
      (reach_piBases_box hN hb hxb)⟩
  obtain ⟨x, hx, hsx⟩ := hto s hs
  obtain ⟨x', hx', hsx'⟩ := hto s' hs'
  refine (hsx.trans ?_).trans (rtg_symm hsymm hsx')
  exact Relation.ReflTransGen.mono (fun _ _ h => ⟨hX (hsub h.1), hX (hsub h.2.1), h.2.2⟩) _ _
    (hp.2.2 x hx x' hx')

/-- **The hull of the thickened rooted polymer of index one is a polymer of index `m₀` containing
the block of the root.** -/
theorem rootHullThick_mem {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (hG : IsLevel G K)
    (hN : L ^ m₀ ∣ N₁) (hL : 3 ≤ L) (h3 : 3 ≤ L ^ (m₀ + m₁)) (y : CTorus d L N₁ m₁ K)
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ)}
    (hT : rootCube (m₀ := 1) (blockIndex y) ∈ T)
    (hp : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) 1 K (sitesOf T)) :
    IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K
        (sitesOf (piHull m₀ (thickSet G (sitesOf T)))) ∧
      y ∈ sitesOf (piHull m₀ (thickSet G (sitesOf T))) := by
  have hpoly := isPolyDom_piHull_thick hG hN hL h3 hp
  refine ⟨hpoly, (mem_iff_blockBase_mem_of_isPolyDom hN hpoly y).2 ?_⟩
  rw [← rootSite_blockIndex]
  exact subset_sitesOf_piHull hN _ (Or.inl (mem_sitesOf.2 ⟨_, hT, rootSite_mem_box_rootCube _⟩))

end Thick

section Labels

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp) (C : StepClass d L N₁ m₁ k N ϱ)

/-- **The step-chart labels attached to the enlarged polymer `Y⁺(T′)`.**  The statement of
`newLabels_stepChart_of_rootFamily` with `Y⁺(T′) = sitesOf (piHull m₀ (thickSet 𝔹 (sitesOf T′)))`
in place of `Y(T′)`: block dependence, support on a polymer of index `m₀` containing the centre,
analyticity and the per-label bound on the step chart, and the regrouped identity
`Σ_{Y ∋ y} Σ_{T′} Tl = densE0 C y q`. -/
theorem newLabels_stepChart_of_rootFamily_thick {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hL : 3 ≤ L)
    (h3 : 3 ≤ L ^ (m₀ + m₁)) (hG : IsLevel S.G' (k + 1))
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (hπ : ∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩)
    (e : RootIdx d L N₁ m₁ (k + 1) → physParam N S →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℂ)
    (b : RootIdx d L N₁ m₁ (k + 1) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℝ)
    (hean : ∀ z T, AnalyticOnNhd ℂ (fun θ => e z θ T) (physV S S.a₁ S.ν eps))
    (hbd : ∀ z T, ∀ θ ∈ physV S S.a₁ S.ν eps, ‖e z θ T‖ ≤ b z T)
    (hsupp : ∀ z θ T, e z θ T ≠ 0 →
      rootCube (m₀ := 1) z ∈ T ∧ IsPolyDom 1 (k + 1) (sitesOf T))
    (hval : ∀ z (D : BgData S.G' N), XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      Jr.E0locJ C z (rawOf D) =
        ∑ T, e z ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), 0) T)
    (Tl : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTl : ∀ T y Y q, Tl T y Y q =
      if sitesOf (piHull m₀ (thickSet S.G' (sitesOf T))) = Y then e (blockIndex y) (π (clipRaw S.G' q), 0) T
      else 0)
    (EbE : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) → ℝ)
    (hEbE : ∀ T y Y, EbE T y Y =
      if sitesOf (piHull m₀ (thickSet S.G' (sitesOf T))) = Y then b (blockIndex y) T else 0) :
    (∀ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := k + 1) 1 (k + 1) Set.univ))), ∀ y y' Y q,
      blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) y =
        blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) y' →
      Tl T y Y q = Tl T y' Y q) ∧
    (∀ T y Y q, Tl T y Y q ≠ 0 → IsPolyDom m₀ (k + 1) Y ∧ y ∈ Y) ∧
    (∀ ε, ε ≤ eps → ∀ T y Y,
      AnalyticOnNhd ℂ (Tl T y Y) {q | XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2}) ∧
    (∀ ε, ε ≤ eps → ∀ T y Y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 → ‖Tl T y Y q‖ ≤ EbE T y Y) ∧
    (∀ ε, ε ≤ eps → ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
      ∑ᶠ Y ∈ polysAt m₀ (k + 1) y, ∑ T ∈ Finset.univ, Tl T y Y q = Jr.densE0 C y q) :=
  newLabels_stepChart_of_rootFamily_hull Jr C
    (fun T => sitesOf (piHull m₀ (thickSet S.G' (sitesOf T))))
    (fun y _ hr hp => rootHullThick_mem hG hN hL h3 y hr hp) π hπ e b hean hbd hsupp hval Tl hTl
    EbE hEbE

end Labels

end Balaban.Inhabited
