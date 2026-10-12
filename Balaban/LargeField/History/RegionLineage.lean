module

public import Balaban.LargeField.History.FlowBook

/-!
# Ancestors, lineages and the overwritten regions (Part I, Definition I.4.2, Lemma I.4.3)

For a region history, `AncRel j t Y Z` says that the component `Y` of `Z^pre_j` is an ancestor
of the component `Z` of `Z^pre_{j+t}`: the chain of successors of `Y` ends in `Z` and does not meet
a removed component at the scales `j, …, j+t-1`.  `lineage j t Z` is the union of the ancestors
of `Z` at scale `j`, `Zov j t` the region at scale `j` after the overwrites of the scales
`< j+t`: the cubes `y ∈ Z^pre_j` whose coarsening at every scale `j+s`, `s < t`, lies in `Z_{j+s}`.

* `lineage_eq_inter` (Lemma I.4.3 (c)): `Lin_j(Z) = Z_j ∩ Z` (the cubes of `Zov j t` that
  coarsen into `Z`);
* `lineage_disjoint` and `iUnion_lineage` (Lemma I.4.3 (d));
* `Zov_mono` and `blockMap_Z_subset_Zpre` (Lemma I.4.3 (b), regions grow).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K)

/-- The coarsening of a cube of `𝕋_j` to `𝕋_{j+t}`. -/
def cm : (t j : ℕ) → Torus S.d (n j) → Torus S.d (n (j + t))
  | 0, _, x => x
  | t + 1, j, x => blockMap S.L (n (j + t + 1)) (cm t j x)

/-- `Y` is an ancestor of `Z`: the successor chain of `Y` ends in `Z` and avoids the removed
components at the scales `j, …, j+t-1`. -/
inductive AncRel : (j t : ℕ) → H.Comp j → H.Comp (j + t) → Prop
  | refl (j : ℕ) (Y : H.Comp j) : AncRel j 0 Y Y
  | step (j t : ℕ) (Y : H.Comp j) (Y' : H.Comp (j + t)) (Y'' : H.Comp (j + t + 1)) :
      AncRel j t Y Y' → (h : Y'.1 ∉ H.rem (j + t)) → H.IsSucc (j + t) Y' Y'' → AncRel j (t + 1) Y Y''

/-- The lineage `Lin_j(Z)`: the union of the ancestors of `Z` at scale `j`. -/
def lineage (j t : ℕ) (Z : H.Comp (j + t)) : Set (Torus S.d (n j)) :=
  {y | ∃ Y : H.Comp j, H.AncRel j t Y Z ∧ y ∈ Y.1}

/-- The region at scale `j` after the overwrites of the scales `j, …, j+t-1`. -/
def Zov (j t : ℕ) : Set (Torus S.d (n j)) :=
  {y | y ∈ H.F.Zpre j ∧ ∀ s, s < t → cm (S := S) (n := n) s j y ∈ (H.step (j + s)).Z}

theorem Zov_zero (j : ℕ) : H.Zov j 0 = H.F.Zpre j := by
  ext y; simp [Zov]

theorem Zov_mono {j t : ℕ} : H.Zov j (t + 1) ⊆ H.Zov j t :=
  fun _ hy => ⟨hy.1, fun s hs => hy.2 s (by omega)⟩

theorem Zov_subset_Zpre (j t : ℕ) : H.Zov j t ⊆ H.F.Zpre j := fun _ hy => hy.1

theorem Z_subset_Zpre (k : ℕ) : (H.step k).Z ⊆ H.F.Zpre k := by
  rw [H.Z_eq k]; exact Set.sdiff_subset

/-- Regions grow (Lemma I.4.3 (b)): `Z_j^↑ ⊆ Z^pre_{j+1}`. -/
theorem blockMap_Z_subset_Zpre (j : ℕ) {x : Torus S.d (n j)} (hx : x ∈ (H.step j).Z) :
    blockMap S.L (n (j + 1)) x ∈ H.F.Zpre (j + 1) :=
  (H.step j).Z0_subset_Zpre (S.omega (j + 1)) (critOpt S k0 (j + 1))
    ((H.step j).Uprime_subset_Z0 ((H.step j).blockMap_Z_subset_Uprime hx))

/-- A cube of the region `Z_k = Z^pre_k ∖ ⋃ Rem_k` lies in a non-removed component. -/
theorem mem_Z_iff {k : ℕ} {x : Torus S.d (n k)} {Y : H.Comp k} (hx : x ∈ Y.1) :
    x ∈ (H.step k).Z ↔ Y.1 ∉ H.rem k := by
  rw [H.Z_eq k]
  simp only [Set.mem_sdiff, Set.mem_iUnion, Finset.mem_coe, exists_prop]
  constructor
  · rintro ⟨-, h⟩ hY
    exact h ⟨Y.1, hY, hx⟩
  · intro hY
    refine ⟨mem_finOf.mp (comp_subset Y.2 hx), ?_⟩
    rintro ⟨Y', hY', hxY'⟩
    have hY'c := H.rem_sub k hY'
    exact hY (comp_eq_of_mem Y.2 hY'c hx hxY' ▸ hY')

/-- **Lemma I.4.3 (c)**: the lineage is `Z_j ∩ Z`: `Lin_j(Z) = {y ∈ Zov j t : cm y ∈ Z}`. -/
theorem lineage_eq_inter (j t : ℕ) (Z : H.Comp (j + t)) (hjt : j + t ≤ K) :
    H.lineage j t Z = {y | y ∈ H.Zov j t ∧ cm (S := S) (n := n) t j y ∈ Z.1} := by
  induction t with
  | zero =>
    ext y
    constructor
    · rintro ⟨Y, hY, hy⟩
      cases hY
      exact ⟨⟨mem_finOf.mp (comp_subset (Subtype.prop _) hy), fun s hs => by omega⟩, hy⟩
    · rintro ⟨-, hy⟩
      exact ⟨Z, AncRel.refl j Z, hy⟩
  | succ t ih =>
    ext y
    constructor
    · rintro ⟨Y, hY, hy⟩
      cases hY with
      | step _ _ Y' _ hY' hrem hsucc =>
        have hyY' : y ∈ H.lineage j t Y' := ⟨Y, hY', hy⟩
        rw [ih Y' (by omega)] at hyY'
        obtain ⟨hZov, hcm⟩ := hyY'
        have hZ : cm (S := S) (n := n) t j y ∈ (H.step (j + t)).Z := (H.mem_Z_iff hcm).mpr hrem
        refine ⟨⟨hZov.1, fun s hs => ?_⟩, ?_⟩
        · by_cases hst : s = t
          · subst hst; exact hZ
          · exact hZov.2 s (by omega)
        · show blockMap S.L (n (j + t + 1)) (cm (S := S) (n := n) t j y) ∈ _
          exact hsucc ⟨_, hcm, rfl⟩
    · rintro ⟨hZov, hy⟩
      have hZt : cm (S := S) (n := n) t j y ∈ (H.step (j + t)).Z := hZov.2 t (by omega)
      have hZpre := H.Z_subset_Zpre (j + t) hZt
      obtain ⟨Y', hY', hyY'⟩ := mem_comp_self (ω := S.omega (j + t)) (mem_finOf.mpr hZpre)
      have hrem : Y' ∉ H.rem (j + t) := (H.mem_Z_iff (Y := ⟨Y', hY'⟩) hyY').mp hZt
      have hjt' : j + t < K := by omega
      have hx : blockMap S.L (n (j + t + 1)) (cm (S := S) (n := n) t j y) ∈
          (H.succ hjt' ⟨Y', hY'⟩ hrem).1 :=
        H.succ_spec hjt' hrem ⟨_, hyY', rfl⟩
      have hsucc : H.IsSucc (j + t) ⟨Y', hY'⟩ Z :=
        (H.succ_eq_iff hjt' hrem).mp
          (Subtype.ext (comp_eq_of_mem (H.succ hjt' ⟨Y', hY'⟩ hrem).2 Z.2 hx hy))
      have hmem : y ∈ H.lineage j t ⟨Y', hY'⟩ := by
        rw [ih ⟨Y', hY'⟩ (by omega)]
        exact ⟨⟨hZov.1, fun s hs => hZov.2 s (by omega)⟩, hyY'⟩
      obtain ⟨Y0, hY0, hy0⟩ := hmem
      exact ⟨Y0, AncRel.step j t Y0 ⟨Y', hY'⟩ Z hY0 hrem hsucc, hy0⟩

/-- **Lemma I.4.3 (d)**: lineages of distinct components are disjoint. -/
theorem lineage_disjoint (j t : ℕ) (hjt : j + t ≤ K) {Z Z' : H.Comp (j + t)} (hne : Z ≠ Z') :
    Disjoint (H.lineage j t Z) (H.lineage j t Z') := by
  rw [Set.disjoint_left]
  intro y hy hy'
  rw [H.lineage_eq_inter j t _ hjt] at hy
  rw [H.lineage_eq_inter j t _ hjt] at hy'
  exact hne (Subtype.ext (comp_eq_of_mem Z.2 Z'.2 hy.2 hy'.2))

/-- **Lemma I.4.3 (d)**: `Z_j` is the union of the lineages of the components of `Z^pre_{j+t}`
(for `t ≥ 1`; for the cubes of `Zov j t` whose coarsening lies in `Z^pre_{j+t}`). -/
theorem iUnion_lineage (j t : ℕ) (hjt : j + t ≤ K) :
    (⋃ Z : H.Comp (j + t), H.lineage j t Z) =
      {y | y ∈ H.Zov j t ∧ cm (S := S) (n := n) t j y ∈ H.F.Zpre (j + t)} := by
  ext y
  simp only [Set.mem_iUnion, H.lineage_eq_inter j t _ hjt, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨Z, hy, hz⟩
    exact ⟨hy, mem_finOf.mp (comp_subset Z.2 hz)⟩
  · rintro ⟨hy, hz⟩
    obtain ⟨Z, hZ, hyZ⟩ := mem_comp_self (ω := S.omega (j + t)) (mem_finOf.mpr hz)
    exact ⟨⟨Z, hZ⟩, hy, hyZ⟩

/-- For `t ≥ 1` the condition `cm y ∈ Z^pre_{j+t}` is automatic on `Zov j t`. -/
theorem Zov_coarsen_mem {j t : ℕ} (ht : 1 ≤ t) {y : Torus S.d (n j)} (hy : y ∈ H.Zov j t) :
    cm (S := S) (n := n) t j y ∈ H.F.Zpre (j + t) := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  exact H.blockMap_Z_subset_Zpre (j + t') (hy.2 t' (by omega))

end RegionHistory

end Balaban.LargeField
