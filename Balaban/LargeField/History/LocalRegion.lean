module

public import Balaban.LargeField.History.LocalUnion
public import Balaban.LargeField.History.RegionGrow

/-!
# The localized history is again a region history (Part I, Definition I.4.4, Lemma I.3.9)

Let `Z` be a component of `Z^pre_k`.  The *lineage localization* `locRH H k Z` is the region history
(on the same tori, with the same parameters) whose step `j → j + 1`, `j < k`, is the local step
`(H.step j).restrict Lin_{j+1}(Z)` of Lemma I.3.9: the cubes of `Z_j` whose coarsening lies in the
lineage `Lin_{j+1}(Z)` of `Z` at scale `j + 1`, and the new large-field cubes lying in the lineage.
It has no removals, and for `j ≥ k` it continues with steps without new cubes.

* `locRH_Zpre`: its regions are the lineages: `Z^pre_j(loc) = Lin_j(Z)` for `j ≤ k` (Lemma I.3.9
  (c) at every step); in particular `Z^pre_k(loc) = Z` and `Z` is its only component;
* `locRH_Z`: `Z_j(loc) = Lin_j(Z)` for `j ≤ k`;
* `locRH_derived`: for `j < k` the complements `Ω'ᶜ, Ωᶜ, Ω''ᶜ, Z^{(0)}` of the local step are the
  global ones intersected with `Lin_{j+1}(Z)` (Lemma I.3.9 (b));
* `localHistory`: the localized history 𝔥_k(Z) of Definition I.4.4 as fine sets: the records of
  `locRH H k Z` (the lineage of `Z`), so records of removed components never occur;
* `localHistory_subset_raw`: its records are contained in those of `rawLocalHistory`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  {H : RegionHistory S n R k0}

theorem Desc.first {a b : ℕ} {Y : H.Comp a} {Z : H.Comp b} (h : H.Desc a b Y Z) (hab : a < b) :
    ∃ hrem : Y.1 ∉ H.rem a, H.Desc (a + 1) b (H.succ a Y hrem) Z := by
  induction h with
  | refl => omega
  | step b' W' Y' Y'' hd hrem hs ih =>
    rcases Nat.eq_or_lt_of_le hd.le with heq | hlt
    · subst heq
      have : Y' = W' := (desc_self_unique' hd)
      subst this
      exact ⟨hrem, hs ▸ Desc.refl _⟩
    · obtain ⟨hr, hd'⟩ := ih hlt
      exact ⟨hr, Desc.step b' _ Y' Y'' hd' hrem hs⟩
where
  desc_self_unique' {b : ℕ} {Y Z : H.Comp b} (h : H.Desc b b Y Z) : Z = Y := by
    cases h with
    | refl => rfl
    | step b' _ _ _ hd _ _ => have := hd.le; omega

variable (H)

/-- A step without new cubes, from the region `Z'`. -/
def emptyStep (S : Setting) (n : ℕ → ℕ) (R : ℕ → ℝ) (j : ℕ) (Z' : Set (Torus S.d (n j))) :
    RegionStep S.d S.L (n j) (n (j + 1)) (R (j - 1)) (R j) where
  Z := Z'
  P := ∅
  Q := ∅
  R := ∅
  S := ∅
  P_sub := Set.empty_subset _
  Q_sub := Set.empty_subset _
  R_sub := Set.empty_subset _
  S_sub := Set.empty_subset _

/-- The regions `Z^pre_j` of the lineage localization: the lineages `Lin_j(Z)` for `j ≤ k`
(`∅` for `j = 0`), and then the regions of the steps without new cubes. -/
noncomputable def tailZ (k : ℕ) (Z : H.Comp k) : ∀ j, Set (Torus S.d (n j))
  | 0 => ∅
  | j + 1 =>
    if j + 1 ≤ k then ((H.lin (j + 1) k Z : Finset (Torus S.d (n (j + 1)))) : Set _)
    else (emptyStep S n R j (tailZ k Z j)).Zpre (S.omega (j + 1)) (critOpt S k0 (j + 1))

/-- The steps of the lineage localization. -/
noncomputable def locStep (k : ℕ) (Z : H.Comp k) (j : ℕ) :
    RegionStep S.d S.L (n j) (n (j + 1)) (R (j - 1)) (R j) :=
  if j < k then (H.step j).restrict ((H.lin (j + 1) k Z : Finset (Torus S.d (n (j + 1)))) : Set _)
  else emptyStep S n R j (H.tailZ k Z j)

/-- The steps of the lineage localization, as `FlowSteps`. -/
noncomputable def locF (k : ℕ) (Z : H.Comp k) : FlowSteps S n R k0 :=
  { H.F with step := H.locStep k Z }

variable {H}

theorem lin_linkClosed (a b : ℕ) (Z : H.Comp b) :
    LinkClosed (S.omega a) (H.F.Zpre a) ((H.lin a b Z : Finset (Torus S.d (n a))) : Set _) := by
  intro x hx y hy hxy
  obtain ⟨Y, hd, hxY⟩ := mem_lin.mp (Finset.mem_coe.mp hx)
  have hyY : y ∈ Y.1 := mem_comp_of_close Y.2 hxY (mem_finOf.mpr hy) hxy
  exact Finset.mem_coe.mpr (mem_lin.mpr ⟨Y, hd, hyY⟩)

theorem lin_sub_Zpre (a b : ℕ) (Z : H.Comp b) :
    ((H.lin a b Z : Finset (Torus S.d (n a))) : Set _) ⊆ H.F.Zpre a := by
  intro x hx
  obtain ⟨Y, -, hxY⟩ := mem_lin.mp (Finset.mem_coe.mp hx)
  exact mem_finOf.mp (comp_subset Y.2 hxY)

theorem lin_self (k : ℕ) (Z : H.Comp k) : H.lin k k Z = Z.1 := by
  unfold lin; rw [ancFin_self, Finset.singleton_biUnion]

theorem lin_zero (b : ℕ) (Z : H.Comp b) : H.lin 0 b Z = ∅ := by
  ext x
  simp only [mem_lin, Finset.notMem_empty, iff_false]
  rintro ⟨Y, -, -⟩
  exact (H.F.isEmpty_comp_zero.false Y)

theorem tailZ_eq_lin {k : ℕ} (Z : H.Comp k) {j : ℕ} (hj : j ≤ k) :
    H.tailZ k Z j = ((H.lin j k Z : Finset (Torus S.d (n j))) : Set _) := by
  cases j with
  | zero => rw [lin_zero]; simp [tailZ]
  | succ j => simp [tailZ, hj]

theorem locStep_Z (k : ℕ) (Z : H.Comp k) (j : ℕ) : (H.locStep k Z j).Z = H.tailZ k Z j := by
  unfold locStep
  by_cases hj : j < k
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hj), tailZ_eq_lin Z hj.le]
    ext z
    show (z ∈ (H.step j).Z ∧ blockMap S.L (n (j + 1)) z ∈
      ((H.lin (j + 1) k Z : Finset (Torus S.d (n (j + 1)))) : Set _)) ↔ _
    constructor
    · rintro ⟨hz, hzl⟩
      obtain ⟨Y1, hd1, hzY1⟩ := mem_lin.mp (Finset.mem_coe.mp hzl)
      have hzp : z ∈ H.F.Zpre j := H.Z_subset_Zpre j hz
      obtain ⟨Y, hY, hzY⟩ := mem_comp_self (ω := S.omega j) (mem_finOf.mpr hzp)
      have hrem : Y ∉ H.rem j := (H.mem_Z_iff (Y := ⟨Y, hY⟩) hzY).mp hz
      have hs := H.succ_spec j (c := ⟨Y, hY⟩) hrem ⟨z, hzY, rfl⟩
      have heq : Y1 = H.succ j ⟨Y, hY⟩ hrem :=
        Subtype.ext (comp_eq_of_mem Y1.2 (H.succ j ⟨Y, hY⟩ hrem).2 hzY1 hs)
      subst heq
      exact Finset.mem_coe.mpr (mem_lin.mpr ⟨⟨Y, hY⟩, (Desc.single hrem rfl).trans hd1, hzY⟩)
    · intro hz
      obtain ⟨Y, hd, hzY⟩ := mem_lin.mp (Finset.mem_coe.mp hz)
      obtain ⟨hrem, hd'⟩ := Desc.first hd hj
      refine ⟨(H.mem_Z_iff hzY).mpr hrem, ?_⟩
      have hs := H.succ_spec j hrem ⟨z, hzY, rfl⟩
      exact Finset.mem_coe.mpr (mem_lin.mpr ⟨H.succ j Y hrem, hd', hs⟩)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hj)]; rfl

theorem locF_Zpre (k : ℕ) (Z : H.Comp k) : ∀ j, (H.locF k Z).Zpre j = H.tailZ k Z j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    show (H.locStep k Z j).Zpre (S.omega (j + 1)) (critOpt S k0 (j + 1)) = _
    by_cases hj : j < k
    · have hg := H.stepGeom j
      have e : H.locStep k Z j = (H.step j).restrict
          ((H.lin (j + 1) k Z : Finset (Torus S.d (n (j + 1)))) : Set _) := by
        unfold locStep; exact ite_eq_left_of_eq_true _ _ (eq_true hj)
      rw [e, tailZ_eq_lin Z (show j + 1 ≤ k by omega)]
      exact (H.step j).restrict_Zpre_closed (critOpt S k0 (j + 1)) hg.hn hg.rad
        (lin_linkClosed (j + 1) k Z) hg.hω2 (lin_sub_Zpre (j + 1) k Z)
    · have e : H.locStep k Z j = emptyStep S n R j (H.tailZ k Z j) := by
        unfold locStep; exact ite_eq_right_of_eq_false _ _ (eq_false hj)
      rw [e]
      have : ¬ j + 1 ≤ k := by omega
      simp [tailZ, this]

/-- **The localized history is a region history (Lemma I.3.9 at every step)**: the lineage
localization of the component `Z` of `Z^pre_k`. -/
noncomputable def locRH (k : ℕ) (Z : H.Comp k) : RegionHistory S n R k0 where
  F := H.locF k Z
  rem := fun _ => ∅
  rem_sub := fun _ => Finset.empty_subset _
  rem_empty := fun _ _ => rfl
  Z_eq := fun j => by
    show (H.locStep k Z j).Z = (H.locF k Z).Zpre j \ ⋃ c ∈ (∅ : Finset (Finset (Torus S.d (n j)))),
      (c : Set (Torus S.d (n j)))
    simp [locStep_Z, locF_Zpre]

theorem locRH_rem (k : ℕ) (Z : H.Comp k) (j : ℕ) : (H.locRH k Z).rem j = ∅ := rfl

theorem locRH_step {k : ℕ} (Z : H.Comp k) {j : ℕ} (hj : j < k) :
    (H.locRH k Z).step j = (H.step j).restrict
      ((H.lin (j + 1) k Z : Finset (Torus S.d (n (j + 1)))) : Set _) := by
  show H.locStep k Z j = _
  unfold locStep; exact ite_eq_left_of_eq_true _ _ (eq_true hj)

/-- `Z^pre_j(loc) = Lin_j(Z)` for `j ≤ k`: Lemma I.3.9 (c) at every step. -/
theorem locRH_Zpre {k : ℕ} (Z : H.Comp k) {j : ℕ} (hj : j ≤ k) :
    (H.locRH k Z).F.Zpre j = ((H.lin j k Z : Finset (Torus S.d (n j))) : Set _) := by
  rw [show (H.locRH k Z).F.Zpre j = (H.locF k Z).Zpre j from rfl, locF_Zpre, tailZ_eq_lin Z hj]

/-- `Z_j(loc) = Lin_j(Z)` for `j ≤ k`. -/
theorem locRH_Z {k : ℕ} (Z : H.Comp k) {j : ℕ} (hj : j ≤ k) :
    ((H.locRH k Z).step j).Z = ((H.lin j k Z : Finset (Torus S.d (n j))) : Set _) := by
  show (H.locStep k Z j).Z = _
  rw [locStep_Z, tailZ_eq_lin Z hj]

/-- The pre-`R` region of the localized history at scale `k` is `Z`. -/
theorem locRH_Zp {k : ℕ} (Z : H.Comp k) : (H.locRH k Z).F.Zp k = Z.1 := by
  show finOf ((H.locRH k Z).F.Zpre k) = _
  rw [locRH_Zpre Z le_rfl, lin_self, finOf_coe]

/-- `Z` is the only component of the pre-`R` region of the localized history at scale `k`. -/
theorem locRH_comps {k : ℕ} (Z : H.Comp k) :
    comps (S.omega k) ((H.locRH k Z).F.Zp k) = {Z.1} := by
  rw [locRH_Zp]
  ext Y
  rw [Finset.mem_singleton]
  constructor
  · intro hY
    ext y
    constructor
    · intro hyY
      exact comp_subset hY hyY
    · intro hyZ
      obtain ⟨x, hx⟩ := comp_nonempty hY
      have hxZ : x ∈ Z.1 := comp_subset hY hx
      have hl : Linked (S.omega k) (Z.1 : Set (Torus S.d (n k))) x y :=
        comp_linked_self_of_comp Z.2 hxZ hyZ
      exact (mem_comp_iff hY hx).mpr ⟨hyZ, hl⟩
  · rintro rfl
    exact comp_mem_comps_self Z.2

/-- The new cubes of the local step are the global ones in the lineage. -/
theorem locRH_new {k : ℕ} (Z : H.Comp k) {j : ℕ} (hj : j < k) :
    ((H.locRH k Z).step j).P = (H.step j).P ∩ ((H.lin (j + 1) k Z : Finset _) : Set _) ∧
    ((H.locRH k Z).step j).Q = (H.step j).Q ∩ ((H.lin (j + 1) k Z : Finset _) : Set _) ∧
    ((H.locRH k Z).step j).R = (H.step j).R ∩ ((H.lin (j + 1) k Z : Finset _) : Set _) ∧
    ((H.locRH k Z).step j).S = (H.step j).S ∩ ((H.lin (j + 1) k Z : Finset _) : Set _) := by
  rw [locRH_step Z hj]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Lemma I.3.9 (b)** along the lineage: for `j < k` the complements `Ω'ᶜ, Ωᶜ, Ω''ᶜ, Z^{(0)}` of
the local step are the global ones intersected with `Lin_{j+1}(Z)`. -/
theorem locRH_derived {k : ℕ} (Z : H.Comp k) {j : ℕ} (hj : j < k) :
    (H.step j).OmegaPrimeᶜ ∩ ((H.lin (j + 1) k Z : Finset _) : Set _) =
      ((H.locRH k Z).step j).OmegaPrimeᶜ ∧
    (H.step j).Omegaᶜ ∩ ((H.lin (j + 1) k Z : Finset _) : Set _) =
      ((H.locRH k Z).step j).Omegaᶜ ∧
    (H.step j).OmegaDDᶜ ∩ ((H.lin (j + 1) k Z : Finset _) : Set _) =
      ((H.locRH k Z).step j).OmegaDDᶜ ∧
    (H.step j).Z0 ∩ ((H.lin (j + 1) k Z : Finset _) : Set _) = ((H.locRH k Z).step j).Z0 := by
  have hg := H.stepGeom j
  rw [locRH_step Z hj]
  have hcl : LinkClosed (S.omega (j + 1)) ((H.step j).Zpre (S.omega (j + 1)) (critOpt S k0 (j + 1)))
      ((H.lin (j + 1) k Z : Finset _) : Set _) := lin_linkClosed (j + 1) k Z
  exact ⟨(H.step j).OmegaPrime_compl_inter_closed _ hg.hn hg.rad hcl,
    (H.step j).Omega_compl_inter_closed _ hg.hn hg.rad hcl,
    (H.step j).OmegaDD_compl_inter_closed _ hg.hn hg.rad hcl,
    (H.step j).Z0_inter_closed _ hg.hn hg.rad hcl⟩

/-- Cubes of the lineage coarsen into `Z`. -/
theorem cubeMap_mem_of_desc [NeZero S.L] (hnn : ∀ i, n i = S.L * n (i + 1)) {M K a b : ℕ}
    [NeZero M] (hbK : b ≤ K) {Y : H.Comp a} {Z : H.Comp b} (h : H.Desc a b Y Z)
    {x : Torus S.d (M * n K * S.L ^ K)} (hx : cubeMap n S.L M K a x ∈ Y.1) :
    cubeMap n S.L M K b x ∈ Z.1 := by
  induction h with
  | refl => exact hx
  | step b' W' Y' Y'' hd hrem hs ih =>
    have h1 := ih (by omega) hx
    have h2 : blockMap S.L (n (b' + 1)) (cubeMap n S.L M K b' x) ∈ Y''.1 := by
      rw [← hs]; exact H.succ_spec b' hrem ⟨_, h1, rfl⟩
    rwa [cubeMap_succ hnn (by omega) x] at h2

variable (H) in
/-- The localized history `𝔥_k(Z)` of a component `Z` of `Z^pre_k` (Definition I.4.4), as fine
sets: the records of the lineage localization `locRH H k Z`, intersected with the fine set of `Z`. -/
noncomputable def localHistory (M K k : ℕ) (Z : H.Comp k) : LocalHistory S n M K where
  Z j := fineSet (S := S) (n := n) M K j ((H.locRH k Z).step j).Z ∩ fineSet M K k Z.1
  P j := fineSet M K (j + 1) ((H.locRH k Z).step j).P ∩ fineSet M K k Z.1
  Q j := fineSet M K (j + 1) ((H.locRH k Z).step j).Q ∩ fineSet M K k Z.1
  R j := fineSet M K (j + 1) ((H.locRH k Z).step j).R ∩ fineSet M K k Z.1
  Sset j := fineSet M K (j + 1) ((H.locRH k Z).step j).S ∩ fineSet M K k Z.1
  OmegaPrime j := fineSet M K (j + 1) ((H.locRH k Z).step j).OmegaPrime ∩ fineSet M K k Z.1
  Omega j := fineSet M K (j + 1) ((H.locRH k Z).step j).Omega ∩ fineSet M K k Z.1
  OmegaDD j := fineSet M K (j + 1) ((H.locRH k Z).step j).OmegaDD ∩ fineSet M K k Z.1

/-- The records of the localized history are contained in the raw records (the new cubes and the
regions `Z_j`, `j < k`). -/
theorem localHistory_subset_raw {k : ℕ} (Z : H.Comp k) {M K : ℕ} [NeZero M] (hkK : k ≤ K) {j : ℕ}
    (hj : j < k) :
    (localHistory H M K k Z).Z j ⊆
        (rawLocalHistory H M K k Z).Z j ∧
    (localHistory H M K k Z).P j ⊆
        (rawLocalHistory H M K k Z).P j ∧
    (localHistory H M K k Z).Q j ⊆
        (rawLocalHistory H M K k Z).Q j ∧
    (localHistory H M K k Z).R j ⊆
        (rawLocalHistory H M K k Z).R j ∧
    (localHistory H M K k Z).Sset j ⊆
        (rawLocalHistory H M K k Z).Sset j := by
  have := H.neZero_L
  have hin : ∀ {a : ℕ} (ha : a ≤ k) (x : Torus S.d (M * n K * S.L ^ K)),
      cubeMap n S.L M K a x ∈ ((H.lin a k Z : Finset (Torus S.d (n a))) : Set _) →
      x ∈ fineSet (S := S) (n := n) M K k (Z.1 : Set (Torus S.d (n k))) := by
    intro a ha x hx
    obtain ⟨Y, hd, hxY⟩ := mem_lin.mp (Finset.mem_coe.mp hx)
    exact cubeMap_mem_of_desc H.F.hnn hkK hd hxY
  obtain ⟨hP, hQ, hR, hS⟩ := locRH_new Z hj
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : cubeMap n S.L M K j x ∈ ((H.locRH k Z).step j).Z := hx.1
    rw [locRH_Z Z hj.le] at hx'
    refine ⟨?_, hin hj.le x hx'⟩
    obtain ⟨Y, hd, hxY⟩ := mem_lin.mp (Finset.mem_coe.mp hx')
    obtain ⟨hrem, -⟩ := Desc.first hd hj
    exact (H.mem_Z_iff hxY).mpr hrem
  · intro x hx
    have hx' : cubeMap n S.L M K (j + 1) x ∈ ((H.locRH k Z).step j).P := hx.1
    rw [hP] at hx'
    exact ⟨hx'.1, hin (by omega) x hx'.2⟩
  · intro x hx
    have hx' : cubeMap n S.L M K (j + 1) x ∈ ((H.locRH k Z).step j).Q := hx.1
    rw [hQ] at hx'
    exact ⟨hx'.1, hin (by omega) x hx'.2⟩
  · intro x hx
    have hx' : cubeMap n S.L M K (j + 1) x ∈ ((H.locRH k Z).step j).R := hx.1
    rw [hR] at hx'
    exact ⟨hx'.1, hin (by omega) x hx'.2⟩
  · intro x hx
    have hx' : cubeMap n S.L M K (j + 1) x ∈ ((H.locRH k Z).step j).S := hx.1
    rw [hS] at hx'
    exact ⟨hx'.1, hin (by omega) x hx'.2⟩

end RegionHistory

end Balaban.LargeField
