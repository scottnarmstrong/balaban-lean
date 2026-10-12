module

public import Balaban.LargeField.Budget.CanonicalBook
public import Balaban.LargeField.Budget.Labelled

/-!
# Kept positions are a function of the localized history; labelled summability without `hpos`

`RegionHistory.keptPos H k Z` is the set of positions `(j, c)` (a scale `j` and a component `c`
of `Z^pre_j`) of the kept ripe events (`IsKeptEvent`) in the lineage of `Z`, `Z` included.  By
`Budget/CanonicalBook.lean` the book of a component is a function of its localized history; here
we deduce that so is `keptPos` (`keptPos_eq_of_localHistory_eq`), which discharges the hypothesis
`hpos` of `sum_inv_logC_labelled`: `sum_inv_logC_labelled_canonical` states the labelled
summability for families whose positions are the kept positions of an actual history.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  (H : RegionHistory S n R k0)

open Classical in
/-- The positions of the kept ripe events in the lineage of a component (itself included):
`keptPos (k+1) Z' = ⋃_{parts} keptPos k ∪ {(k+1, Z') if Z' is a kept ripe event}`. -/
noncomputable def keptPos : ∀ k, H.Comp k → Finset (KeptPos S n)
  | 0, _ => ∅
  | k + 1, Z' =>
      (H.parts k Z').biUnion (fun c => keptPos k c) ∪
        (if H.IsKeptEvent (k + 1) Z' then {⟨k + 1, Z'.1⟩} else ∅)

theorem keptPos_succ (k : ℕ) (Z' : H.Comp (k + 1)) :
    H.keptPos (k + 1) Z' =
      (H.parts k Z').biUnion (fun c => H.keptPos k c) ∪
        (open Classical in if H.IsKeptEvent (k + 1) Z' then {⟨k + 1, Z'.1⟩} else ∅) := rfl

open Classical in
/-- `keptPos` as a function of the cube set (empty off the components). -/
noncomputable def keptPosO (k : ℕ) (Y : Finset (Torus S.d (n k))) : Finset (KeptPos S n) :=
  if h : Y ∈ comps (S.omega k) (H.Zp k) then H.keptPos k ⟨Y, h⟩ else ∅

theorem keptPosO_comp (k : ℕ) (c : H.Comp k) : H.keptPosO k c.1 = H.keptPos k c := by
  classical
  simp [keptPosO, c.2]

theorem biUnion_parts_eq (k : ℕ) (Z' : H.Comp (k + 1))
    (g : Finset (Torus S.d (n k)) → Finset (KeptPos S n)) :
    (H.parts k Z').biUnion (fun c => g c.1) = (comps (S.omega k) (H.oldCubes k Z')).biUnion g := by
  classical
  rw [← H.parts_image_eq_comps k Z']
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, hp⟩
    exact ⟨c.1, ⟨c, hc, rfl⟩, hp⟩
  · rintro ⟨Y, ⟨c, hc, rfl⟩, hp⟩
    exact ⟨c, hc, hp⟩

variable {H}

variable {M K : ℕ} [NeZero M]

/-- **The kept positions are a function of the localized history.** -/
theorem keptPos_eq_of_localHistory_eq :
    ∀ (k : ℕ), k ≤ K → ∀ (H1 H2 : RegionHistory S n R k0) (Z1 : H1.Comp k) (Z2 : H2.Comp k),
      localHistory H1 M K k Z1 = localHistory H2 M K k Z2 →
      H1.keptPos k Z1 = H2.keptPos k Z2 := by
  classical
  intro k
  induction k with
  | zero => intro _ H1 _ Z1; exact (H1.F.isEmpty_comp_zero.false Z1).elim
  | succ k ih =>
    intro hkK H1 H2 Z1 Z2 h
    obtain ⟨hZ, hold, -, hfam⟩ := record_forward hkK Z1 Z2 h
    obtain ⟨-, -, hbk⟩ := spine_bk_eq_of_localHistory_eq (k + 1) hkK H1 H2 Z1 Z2 h
    have hmem1 := fun Y (hY : Y ∈ comps (S.omega k) (H1.oldCubes k Z1)) =>
      mem_Zp_of_old H1 k Z1 hY
    have hmem2 := fun Y (hY : Y ∈ comps (S.omega k) (H1.oldCubes k Z1)) =>
      mem_Zp_of_old H2 k Z2 (hold ▸ hY)
    have hO : ∀ Y ∈ comps (S.omega k) (H1.oldCubes k Z1), H1.keptPosO k Y = H2.keptPosO k Y := by
      intro Y hY
      have e1 := H1.keptPosO_comp k ⟨Y, hmem1 Y hY⟩
      have e2 := H2.keptPosO_comp k ⟨Y, hmem2 Y hY⟩
      simp only at e1 e2
      rw [e1, e2]
      exact ih (by omega) H1 H2 _ _ (hfam Y (hmem1 Y hY) (hmem2 Y hY) hY)
    have hkept : H1.IsKeptEvent (k + 1) Z1 ↔ H2.IsKeptEvent (k + 1) Z2 := by
      unfold IsKeptEvent
      rw [hbk]
    rw [keptPos_succ, keptPos_succ]
    have hu : (H1.parts k Z1).biUnion (fun c => H1.keptPos k c) =
        (H2.parts k Z2).biUnion (fun c => H2.keptPos k c) := by
      have a1 := H1.biUnion_parts_eq k Z1 (H1.keptPosO k)
      have a2 := H2.biUnion_parts_eq k Z2 (H2.keptPosO k)
      simp only [keptPosO_comp] at a1 a2
      rw [a1, a2, hold]
      exact Finset.biUnion_congr rfl fun Y hY => hO Y (by rw [hold]; exact hY)
    have hB : (if H1.IsKeptEvent (k + 1) Z1 then ({⟨k + 1, Z1.1⟩} : Finset (KeptPos S n)) else ∅) =
        (if H2.IsKeptEvent (k + 1) Z2 then ({⟨k + 1, Z2.1⟩} : Finset (KeptPos S n)) else ∅) := by
      by_cases hk : H1.IsKeptEvent (k + 1) Z1
      · have hk2 := hkept.mp hk
        simp only [hk, hk2, ↓reduceIte, hZ]
      · have hk2 : ¬ H2.IsKeptEvent (k + 1) Z2 := fun h2 => hk (hkept.mpr h2)
        simp only [hk, hk2, ↓reduceIte]
    rw [hu, hB]

/-- Ripeness (and the kept event) of a component is a function of its localized history. -/
theorem isKeptEvent_iff_of_localHistory_eq {k : ℕ} (hkK : k ≤ K) {H1 H2 : RegionHistory S n R k0}
    (Z1 : H1.Comp k) (Z2 : H2.Comp k)
    (h : localHistory H1 M K k Z1 = localHistory H2 M K k Z2) :
    H1.IsKeptEvent k Z1 ↔ H2.IsKeptEvent k Z2 := by
  obtain ⟨-, -, hbk⟩ := spine_bk_eq_of_localHistory_eq k hkK H1 H2 Z1 Z2 h
  unfold IsKeptEvent
  rw [hbk]

end RegionHistory

section Labelled

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  {Lab : Type*} [Nonempty Lab]

open RegionHistory in
/-- **Lemma II.5.15 with kept labels, without `hpos`**: for `L^d ≥ 8`, `k ≤ K`,
`∑_ϰ C_dec(ϰ)^{-1} ≤ 1` (S3), and a finite family `𝒜` of labelled localized histories `(a, T)` of
the component `Y`, where `a` is the localized history of `Y` in some region history `H` and `T`
carries one label for each kept ripe event in the lineage of `Y` in `H` (positions `keptPos`),
`∑_{(a,T) ∈ 𝒜} C_k(a)^{-1} ∏_{(p,ϰ) ∈ T} C_dec(ϰ)^{-1} ≤ 1`. -/
theorem sum_inv_logC_labelled_canonical (hLd : 8 ≤ S.L ^ S.d) {k : ℕ} (hkK : k ≤ K)
    (Y : Finset (Torus S.d (n k))) (cdec : Lab → ℝ)
    (hlab : ∀ F : Finset Lab, ∑ ϰ ∈ F, Real.exp (-cdec ϰ) ≤ 1)
    (𝒜 : Finset (LocalHistory S n M K × Finset (KeptPos S n × Lab)))
    (hhist : ∀ x ∈ 𝒜, ∃ (H : RegionHistory S n R k0) (hY : Y ∈ comps (S.omega k) (H.Zp k)),
      x.1 = localHistory H M K k ⟨Y, hY⟩ ∧ x.2.image Prod.fst = H.keptPos k ⟨Y, hY⟩)
    (hfun : ∀ x ∈ 𝒜, ∀ p ϰ ϰ', (p, ϰ) ∈ x.2 → (p, ϰ') ∈ x.2 → ϰ = ϰ') :
    ∑ x ∈ 𝒜, Real.exp (-(x.1.logC k + ∑ t ∈ x.2, cdec t.2)) ≤ 1 := by
  refine sum_inv_logC_labelled (R := R) (k0 := k0) hLd hkK Y cdec hlab 𝒜 ?_ hfun ?_
  · intro x hx
    obtain ⟨H, hY, h1, -⟩ := hhist x hx
    exact ⟨H, hY, h1⟩
  · intro x hx x' hx' hxx
    obtain ⟨H, hY, h1, h2⟩ := hhist x hx
    obtain ⟨H', hY', h1', h2'⟩ := hhist x' hx'
    rw [h2, h2']
    refine keptPos_eq_of_localHistory_eq (M := M) (K := K) k hkK H H' ⟨Y, hY⟩ ⟨Y, hY'⟩ ?_
    rw [← h1, ← h1', hxx]

end Labelled

end Balaban.LargeField
