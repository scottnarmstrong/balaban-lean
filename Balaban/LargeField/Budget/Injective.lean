module

public import Balaban.LargeField.Budget.Fine

/-!
# The localized history of a component is determined by its first-level data (Lemma II.5.15)

A localized history of a component `Z'` of `Z^pre_{k+1}` is determined by

* the set `S = Z_k ∩ Z'` of `π_k`-cubes,
* the new cubes `(P, Q, R, S)_{k+1} ∩ Z'` (the four region families),
* the localized histories of the components `Y` of `S` (the old parts).

`localHistory_succ_eq` is this injectivity statement.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

section Comps

variable {d n ω : ℕ} [NeZero n]

theorem linkClass_eq_of_comp_subset {X S D : Finset (Torus d n)} (hD : D ∈ comps ω X)
    (hDS : D ⊆ S) (hSX : S ⊆ X) {x : Torus d n} (hx : x ∈ D) : linkClass ω S x = D := by
  ext y
  rw [mem_linkClass]
  constructor
  · rintro ⟨hy, hl⟩
    exact ((mem_comp_iff hD hx).mpr ⟨hSX hy, hl.mono (by exact_mod_cast hSX)⟩)
  · intro hy
    exact ⟨hDS hy, (comp_linked_self_of_comp hD hx hy).mono (by exact_mod_cast hDS)⟩

/-- The components of a union of components of `X` are these components. -/
theorem comps_biUnion_of_subset {X : Finset (Torus d n)} {T : Finset (Finset (Torus d n))}
    (hT : T ⊆ comps ω X) : comps ω (T.biUnion id) = T := by
  have hsub : T.biUnion id ⊆ X := by
    intro x hx
    obtain ⟨D, hD, hxD⟩ := Finset.mem_biUnion.mp hx
    exact comp_subset (hT hD) hxD
  have hDS : ∀ D ∈ T, D ⊆ T.biUnion id := fun D hD x hx => Finset.mem_biUnion.mpr ⟨D, hD, hx⟩
  ext C
  constructor
  · intro hC
    obtain ⟨x, hx, rfl⟩ := mem_comps_iff.mp hC
    obtain ⟨D, hD, hxD⟩ := Finset.mem_biUnion.mp hx
    rw [linkClass_eq_of_comp_subset (hT hD) (hDS D hD) hsub hxD]
    exact hD
  · intro hD
    obtain ⟨x, hx⟩ := comp_nonempty (hT hD)
    refine mem_comps_iff.mpr ⟨x, Finset.mem_biUnion.mpr ⟨C, hD, hx⟩, ?_⟩
    rw [linkClass_eq_of_comp_subset (hT hD) (hDS C hD) hsub hx]

end Comps

theorem RegionStep.eq_of_fields {d L n0 n1 : ℕ} {Rprev Rk : ℝ} {a b : RegionStep d L n0 n1 Rprev Rk}
    (hZ : a.Z = b.Z) (hP : a.P = b.P) (hQ : a.Q = b.Q) (hR : a.R = b.R) (hS : a.S = b.S) :
    a = b := by
  cases a; cases b
  simp only at hZ hP hQ hR hS
  subst hZ hP hQ hR hS
  rfl

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

/-- The old parts of `Z'` are the components of the set `Z_k ∩ Z'` of `π_k`-cubes. -/
theorem parts_image_eq_comps (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k < K)
    (Z' : H.Comp (k + 1)) :
    (H.parts k Z').image Subtype.val = comps (S.omega k) (H.oldCubes k Z') := by
  classical
  have hT : (H.parts k Z').image Subtype.val ⊆ comps (S.omega k) (H.Zp k) := by
    intro Y hY
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hY
    exact c.2
  have e : H.oldCubes k Z' = ((H.parts k Z').image Subtype.val).biUnion id := by
    rw [H.oldCubes_eq hk, Finset.image_biUnion]
    rfl
  rw [e, comps_biUnion_of_subset hT]

/-- The cubes of `Z_k` over `Z'` form the lineage of `Z'` at scale `k`. -/
theorem lin_succ_self (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k < K) (Z' : H.Comp (k + 1)) :
    H.lin k (k + 1) Z' = H.oldCubes k Z' := by
  rw [lin, ancFin_succ le_rfl, Finset.biUnion_biUnion, H.oldCubes_eq hk]
  refine Finset.biUnion_congr rfl fun c _ => ?_
  have := H.lin_self k c
  simpa [lin] using this

/-- The lineage of `Z'` at a scale `j ≤ k` is the union of the lineages of its old parts. -/
theorem lin_succ_decomp (H : RegionHistory S n R k0 K) {j : ℕ} (k : ℕ) (hjk : j ≤ k)
    (Z' : H.Comp (k + 1)) :
    H.lin j (k + 1) Z' = (H.parts k Z').biUnion fun c => H.lin j k c := by
  rw [lin, ancFin_succ hjk, Finset.biUnion_biUnion]
  rfl

open Classical in
/-- The lineage at scale `j` of a component of `Z^pre_k`, indexed by the finset of cubes
(`∅` if it is not a component). -/
noncomputable def linO (H : RegionHistory S n R k0 K) (j k : ℕ) (Y : Finset (Torus S.d (n k))) :
    Finset (Torus S.d (n j)) :=
  if h : Y ∈ comps (S.omega k) (H.Zp k) then H.lin j k ⟨Y, h⟩ else ∅

theorem linO_comp (H : RegionHistory S n R k0 K) (j k : ℕ) (c : H.Comp k) :
    H.linO j k c.1 = H.lin j k c := by
  classical
  simp [linO, c.2]

theorem lin_succ_decomp' (H : RegionHistory S n R k0 K) {j : ℕ} (k : ℕ) (hjk : j ≤ k)
    (hk : k < K) (Z' : H.Comp (k + 1)) :
    H.lin j (k + 1) Z' = (comps (S.omega k) (H.oldCubes k Z')).biUnion fun Y => H.linO j k Y := by
  classical
  rw [← H.parts_image_eq_comps hk Z', Finset.image_biUnion, H.lin_succ_decomp k hjk]
  exact Finset.biUnion_congr rfl fun c _ => (H.linO_comp j k c).symm

/-! ### Equality of localized histories -/

theorem tailZ_congr {H1 H2 : RegionHistory S n R k0 K} {k : ℕ} (Z1 : H1.Comp k) (Z2 : H2.Comp k)
    (hZ : Z1.1 = Z2.1) (hkK : k ≤ K) {j : ℕ} (hj : k ≤ j) :
    H1.tailZ k Z1 j = H2.tailZ k Z2 j := by
  induction j, hj using Nat.le_induction with
  | base =>
    rw [tailZ_eq_lin Z1 le_rfl hkK, tailZ_eq_lin Z2 le_rfl hkK, lin_self, lin_self, hZ]
  | succ j hj ih =>
    have hn : ¬ (j + 1 ≤ k ∧ j + 1 ≤ K) := by omega
    simp only [tailZ, hn, ite_false, ih]

/-- The localized history only depends on the component and on the steps of the lineage
localization. -/
theorem localHistory_congr {H1 H2 : RegionHistory S n R k0 K} {M K k : ℕ} [NeZero M]
    (Z1 : H1.Comp k) (Z2 : H2.Comp k) (hZ : Z1.1 = Z2.1)
    (hst : ∀ j, (H1.locRH k Z1).step j = (H2.locRH k Z2).step j) :
    localHistory H1 M K k Z1 = localHistory H2 M K k Z2 := by
  unfold localHistory
  simp only [hst, hZ]

theorem inter_biUnion_congr {α β : Type*} [DecidableEq β] {I : Finset α} {X1 X2 : Set β}
    {f1 f2 : α → Finset β} (e : ∀ Y ∈ I, X1 ∩ (f1 Y : Set β) = X2 ∩ (f2 Y : Set β)) :
    X1 ∩ ((I.biUnion f1 : Finset β) : Set β) = X2 ∩ ((I.biUnion f2 : Finset β) : Set β) := by
  ext x
  simp only [Set.mem_inter_iff, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, exists_prop]
  constructor
  · rintro ⟨hx, Y, hY, hxY⟩
    have := (Set.ext_iff.mp (e Y hY) x).mp ⟨hx, hxY⟩
    exact ⟨this.1, Y, hY, this.2⟩
  · rintro ⟨hx, Y, hY, hxY⟩
    have := (Set.ext_iff.mp (e Y hY) x).mpr ⟨hx, hxY⟩
    exact ⟨this.1, Y, hY, this.2⟩

variable {M K : ℕ} [NeZero M]

/-- **Injectivity of the first-level data (Lemma II.5.15)**: the localized history of a component
`Z'` of `Z^pre_{k+1}` is determined by the cubes of `Z_k` over `Z'`, the new cubes
`P, Q, R, S` of the step into scale `k+1` in `Z'`, and the localized histories of the components
of `Z_k ∩ Z'`. -/
theorem localHistory_succ_eq {H1 H2 : RegionHistory S n R k0 K} {k : ℕ} (hkK : k + 1 ≤ K)
    (Z1 : H1.Comp (k + 1)) (Z2 : H2.Comp (k + 1)) (hZ : Z1.1 = Z2.1)
    (hS : H1.oldCubes k Z1 = H2.oldCubes k Z2)
    (hP : (H1.step k).P ∩ (Z1.1 : Set _) = (H2.step k).P ∩ (Z2.1 : Set _))
    (hQ : (H1.step k).Q ∩ (Z1.1 : Set _) = (H2.step k).Q ∩ (Z2.1 : Set _))
    (hR : (H1.step k).R ∩ (Z1.1 : Set _) = (H2.step k).R ∩ (Z2.1 : Set _))
    (hS' : (H1.step k).S ∩ (Z1.1 : Set _) = (H2.step k).S ∩ (Z2.1 : Set _))
    (hfam : ∀ Y (h1 : Y ∈ comps (S.omega k) (H1.Zp k)) (h2 : Y ∈ comps (S.omega k) (H2.Zp k)),
      Y ∈ comps (S.omega k) (H1.oldCubes k Z1) →
        localHistory H1 M K k ⟨Y, h1⟩ = localHistory H2 M K k ⟨Y, h2⟩) :
    localHistory H1 M K (k + 1) Z1 = localHistory H2 M K (k + 1) Z2 := by
  classical
  have hkK' : k ≤ K := by omega
  have hnn1 := H1.F.hnn
  have hnn2 := H2.F.hnn
  have := H1.neZero_L
  -- membership of the index set in both component sets
  have hmem1 : ∀ Y, Y ∈ comps (S.omega k) (H1.oldCubes k Z1) → Y ∈ comps (S.omega k) (H1.Zp k) := by
    intro Y hY
    rw [← H1.parts_image_eq_comps (by omega) Z1] at hY
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hY
    exact c.2
  have hmem2 : ∀ Y, Y ∈ comps (S.omega k) (H1.oldCubes k Z1) → Y ∈ comps (S.omega k) (H2.Zp k) := by
    intro Y hY
    rw [hS, ← H2.parts_image_eq_comps (by omega) Z2] at hY
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hY
    exact c.2
  have hfam' : ∀ Y (hY : Y ∈ comps (S.omega k) (H1.oldCubes k Z1)),
      localHistory H1 M K k ⟨Y, hmem1 Y hY⟩ = localHistory H2 M K k ⟨Y, hmem2 Y hY⟩ :=
    fun Y hY => hfam Y (hmem1 Y hY) (hmem2 Y hY) hY
  -- lineages of the old parts agree
  have hlin : ∀ j, j ≤ k → ∀ Y (hY : Y ∈ comps (S.omega k) (H1.oldCubes k Z1)),
      H1.linO j k Y = H2.linO j k Y := by
    intro j hj Y hY
    have h := congrArg (fun a => a.Z j) (hfam' Y hY)
    rw [localHistory_Z _ hkK' hj, localHistory_Z _ hkK' hj] at h
    have h' := fineSet_injective (S := S) (n := n) (M := M) (K := K) hnn1 (hj.trans hkK') h
    have h'' : H1.lin j k ⟨Y, hmem1 Y hY⟩ = H2.lin j k ⟨Y, hmem2 Y hY⟩ := by
      exact_mod_cast h'
    have e1 := H1.linO_comp j k ⟨Y, hmem1 Y hY⟩
    have e2 := H2.linO_comp j k ⟨Y, hmem2 Y hY⟩
    simp only at e1 e2
    rw [e1, e2, h'']
  have hZlin : ∀ j, j ≤ k → H1.lin j (k + 1) Z1 = H2.lin j (k + 1) Z2 := by
    intro j hj
    rw [H1.lin_succ_decomp' k hj (by omega), H2.lin_succ_decomp' k hj (by omega), hS]
    refine Finset.biUnion_congr rfl fun Y hY => ?_
    rw [← hS] at hY
    exact hlin j hj Y hY
  -- new cubes of the old parts agree
  have hnew : ∀ j, j < k → ∀ Y (hY : Y ∈ comps (S.omega k) (H1.oldCubes k Z1)),
      (H1.step j).P ∩ (H1.linO (j + 1) k Y : Set _) = (H2.step j).P ∩ (H2.linO (j + 1) k Y : Set _) ∧
      (H1.step j).Q ∩ (H1.linO (j + 1) k Y : Set _) = (H2.step j).Q ∩ (H2.linO (j + 1) k Y : Set _) ∧
      (H1.step j).R ∩ (H1.linO (j + 1) k Y : Set _) = (H2.step j).R ∩ (H2.linO (j + 1) k Y : Set _) ∧
      (H1.step j).S ∩ (H1.linO (j + 1) k Y : Set _) = (H2.step j).S ∩ (H2.linO (j + 1) k Y : Set _) := by
    intro j hj Y hY
    have hf := hfam' Y hY
    obtain ⟨a1, a2, a3, a4⟩ := localHistory_new (H := H1) (M := M) (K := K) ⟨Y, hmem1 Y hY⟩ hkK' hj
    obtain ⟨b1, b2, b3, b4⟩ := localHistory_new (H := H2) (M := M) (K := K) ⟨Y, hmem2 Y hY⟩ hkK' hj
    have e1 := H1.linO_comp (j + 1) k ⟨Y, hmem1 Y hY⟩
    have e2 := H2.linO_comp (j + 1) k ⟨Y, hmem2 Y hY⟩
    simp only at e1 e2
    rw [e1, e2]
    have h1 := congrArg (fun a => a.P j) hf
    have h2 := congrArg (fun a => a.Q j) hf
    have h3 := congrArg (fun a => a.R j) hf
    have h4 := congrArg (fun a => a.Sset j) hf
    rw [a1, b1] at h1
    rw [a2, b2] at h2
    rw [a3, b3] at h3
    rw [a4, b4] at h4
    have hj1 : j + 1 ≤ K := by omega
    exact ⟨fineSet_injective (S := S) (n := n) (M := M) (K := K) hnn1 hj1 h1,
      fineSet_injective (S := S) (n := n) (M := M) (K := K) hnn1 hj1 h2,
      fineSet_injective (S := S) (n := n) (M := M) (K := K) hnn1 hj1 h3,
      fineSet_injective (S := S) (n := n) (M := M) (K := K) hnn1 hj1 h4⟩
  -- the tail regions agree
  have hZf : ∀ j, H1.tailZ (k + 1) Z1 j = H2.tailZ (k + 1) Z2 j := by
    intro j
    by_cases hj : j ≤ k + 1
    · rw [tailZ_eq_lin Z1 hj (by omega), tailZ_eq_lin Z2 hj (by omega)]
      by_cases hjk : j ≤ k
      · rw [hZlin j hjk]
      · have : j = k + 1 := by omega
        subst this
        rw [lin_self, lin_self, hZ]
    · exact tailZ_congr Z1 Z2 hZ hkK (by omega)
  -- the steps agree
  have hst : ∀ j, (H1.locRH (k + 1) Z1).step j = (H2.locRH (k + 1) Z2).step j := by
    intro j
    by_cases hj : j < k + 1
    · have hZj : ((H1.locRH (k + 1) Z1).step j).Z = ((H2.locRH (k + 1) Z2).step j).Z := by
        show (H1.locStep (k + 1) Z1 j).Z = (H2.locStep (k + 1) Z2 j).Z
        rw [locStep_Z, locStep_Z, hZf]
      obtain ⟨p1, q1, r1, s1⟩ := locRH_new Z1 hj (by omega)
      obtain ⟨p2, q2, r2, s2⟩ := locRH_new Z2 hj (by omega)
      by_cases hjk : j < k
      · have hjl : ∀ (X1 X2 : Set (Torus S.d (n (j + 1)))),
            (∀ Y ∈ comps (S.omega k) (H1.oldCubes k Z1),
              X1 ∩ (H1.linO (j + 1) k Y : Set _) = X2 ∩ (H2.linO (j + 1) k Y : Set _)) →
            X1 ∩ (H1.lin (j + 1) (k + 1) Z1 : Set _) = X2 ∩ (H2.lin (j + 1) (k + 1) Z2 : Set _) := by
          intro X1 X2 e
          rw [H1.lin_succ_decomp' k (by omega) (by omega), H2.lin_succ_decomp' k (by omega) (by omega), ← hS]
          exact inter_biUnion_congr e
        refine RegionStep.eq_of_fields hZj ?_ ?_ ?_ ?_
        · rw [p1, p2]
          exact hjl _ _ fun Y hY => (hnew j hjk Y hY).1
        · rw [q1, q2]
          exact hjl _ _ fun Y hY => (hnew j hjk Y hY).2.1
        · rw [r1, r2]
          exact hjl _ _ fun Y hY => (hnew j hjk Y hY).2.2.1
        · rw [s1, s2]
          exact hjl _ _ fun Y hY => (hnew j hjk Y hY).2.2.2
      · have hjk' : j = k := by omega
        subst hjk'
        refine RegionStep.eq_of_fields hZj ?_ ?_ ?_ ?_
        · rw [p1, p2, lin_self, lin_self]; exact hP
        · rw [q1, q2, lin_self, lin_self]; exact hQ
        · rw [r1, r2, lin_self, lin_self]; exact hR
        · rw [s1, s2, lin_self, lin_self]; exact hS'
    · have e1 : (H1.locRH (k + 1) Z1).step j = emptyStep S n R j (H1.tailZ (k + 1) Z1 j) := by
        show H1.locStep (k + 1) Z1 j = _
        unfold locStep; exact ite_eq_right_of_eq_false _ _ (eq_false (fun h => hj h.1))
      have e2 : (H2.locRH (k + 1) Z2).step j = emptyStep S n R j (H2.tailZ (k + 1) Z2 j) := by
        show H2.locStep (k + 1) Z2 j = _
        unfold locStep; exact ite_eq_right_of_eq_false _ _ (eq_false (fun h => hj h.1))
      rw [e1, e2, hZf j]
  exact localHistory_congr Z1 Z2 hZ hst

end RegionHistory

end Balaban.LargeField
