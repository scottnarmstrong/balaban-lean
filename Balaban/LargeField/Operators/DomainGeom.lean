module

public import Balaban.LargeField.Operators.Ancestors
public import Balaban.LargeField.Operators.Setup
public import Balaban.LargeField.Operators.AncVars
public import Balaban.LargeField.Region.Inclusions

/-!
# Lineage geometry for the domain identity (Part II, proof of Lemma II.5.13)

For a component `Z'` of `Z^pre_{k+1}` and an old part `Y ∈ Anc_k(Z')` the localized histories
`a_Y = 𝔞|_Y` and `a' = 𝔞` of `Y` and `Z'` agree on the fine set of `Y`:

* `blockMap_nbhd_lin`: the margin — a cube of `𝕋_i` within `1` of the lineage `Lin_i(Z)` lies over
  `Lin_{i+1}(Z)` (Lemma I.3.5 (i) for the localized steps);
* `mem_lin_iff_of_mem_part`: on the fine set of `Y` the lineages of `Y` and `Z'` agree;
* `locOmega_iff`: at a cube of the lineage the localized `Ω_{j+1}` is the global one, and
  outside the lineage every localized `Ω_{j+1}` contains the cube.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  {H : RegionHistory S n R k0}

section Geom

variable [NeZero S.L]

/-- **Margin (Lemma I.3.5 (i) for the lineage localization).** A cube of `𝕋_i` within `1` of the
lineage `Lin_i(Z)` of a component `Z` of `Z^pre_b` lies over the lineage `Lin_{i+1}(Z)`
(`i + 1 ≤ b`). -/
theorem blockMap_nbhd_lin {b : ℕ} (Z : H.Comp b) {i : ℕ} (hi : i + 1 ≤ b)
    {e : Torus S.d (n i)} (he : e ∈ nbhd 1 ((H.lin i b Z : Finset (Torus S.d (n i))) : Set _)) :
    blockMap S.L (n (i + 1)) e ∈ ((H.lin (i + 1) b Z : Finset (Torus S.d (n (i + 1)))) : Set _) := by
  set st := (H.locRH b Z).step i with hst
  have hZ : st.Z = ((H.lin i b Z : Finset (Torus S.d (n i))) : Set _) := locRH_Z Z (by omega)
  have hn := H.F.hnn i
  have hL : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne _)
  have he' : e ∈ nbhd 1 st.U := by
    refine nbhd_mono le_rfl ?_ he
    rw [← hZ]
    exact subset_nbhd _ _
  have hm : (1 + S.L - 1) / S.L ≤ ⌊R i⌋₊ + 4 := by
    rw [show 1 + S.L - 1 = S.L by omega, Nat.div_self hL]
    omega
  have h1 := st.blockMap_nbhd_U_subset hn hm he'
  have h2 := st.Z0_subset_Zpre (S.omega (i + 1)) (critOpt S k0 (i + 1))
    (st.OmegaPrime_compl_subset_Z0 h1)
  have h3 : (H.locRH b Z).F.Zpre (i + 1) = st.Zpre (S.omega (i + 1)) (critOpt S k0 (i + 1)) := rfl
  rw [← h3, locRH_Zpre Z hi] at h2
  exact h2

/-- **Margin, general radius.**  A cube of `𝕋_i` within `m` of the lineage `Lin_i(Z)` with
`⌈m/L⌉ ≤ ⌊R_i⌋ + 4` lies over the lineage `Lin_{i+1}(Z)` (`i + 1 ≤ b`). -/
theorem blockMap_nbhd_lin_of_le {b : ℕ} (Z : H.Comp b) {i : ℕ} (hi : i + 1 ≤ b) {m : ℕ}
    (hm : (m + S.L - 1) / S.L ≤ ⌊R i⌋₊ + 4)
    {e : Torus S.d (n i)} (he : e ∈ nbhd m ((H.lin i b Z : Finset (Torus S.d (n i))) : Set _)) :
    blockMap S.L (n (i + 1)) e ∈ ((H.lin (i + 1) b Z : Finset (Torus S.d (n (i + 1)))) : Set _) := by
  set st := (H.locRH b Z).step i with hst
  have hZ : st.Z = ((H.lin i b Z : Finset (Torus S.d (n i))) : Set _) := locRH_Z Z (by omega)
  have hn := H.F.hnn i
  have he' : e ∈ nbhd m st.U := by
    refine nbhd_mono le_rfl ?_ he
    rw [← hZ]
    exact subset_nbhd _ _
  have h1 := st.blockMap_nbhd_U_subset hn hm he'
  have h2 := st.Z0_subset_Zpre (S.omega (i + 1)) (critOpt S k0 (i + 1))
    (st.OmegaPrime_compl_subset_Z0 h1)
  have h3 : (H.locRH b Z).F.Zpre (i + 1) = st.Zpre (S.omega (i + 1)) (critOpt S k0 (i + 1)) := rfl
  rw [← h3, locRH_Zpre Z hi] at h2
  exact h2

/-- Beyond the lineage: a cube `c` of `𝕋_{k+1}` within `2` of the coarsening of a cube of the
lineage `Lin_k(Z')` lies in `Z'` and is not over `Ω_{k+1}` of the localized step. -/
theorem fibre_far {M K : ℕ} [NeZero M] {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    {z0 : Torus S.d (n k)} (hz0 : z0 ∈ ((H.lin k (k + 1) Z' : Finset (Torus S.d (n k))) : Set _))
    {c : Torus S.d (n (k + 1))} (hd : supDist (blockMap S.L (n (k + 1)) z0) c ≤ 2) :
    c ∈ (Z'.1 : Set (Torus S.d (n (k + 1)))) ∧ c ∉ ((H.locRH (k + 1) Z').step k).Omega := by
  have hnn := H.F.hnn
  have hL : 2 ≤ S.L := H.F.ok.two_le_L
  obtain ⟨w, hw⟩ := exists_site_of_cube (M := M) (K := K) (S := S) (n := n) hnn hK c
  set y' := cubeMap n S.L M K k w with hy'
  have hby : blockMap S.L (n (k + 1)) y' = c := by
    rw [hy', cubeMap_succ hnn (by omega) w, hw]
  have hdist : supDist y' z0 ≤ 3 * S.L - 1 := by
    have h1 := supDist_le_blockMap (L := S.L) (m := n (k + 1)) (hnn k) y' z0
    rw [hby] at h1
    have h2 : supDist c (blockMap S.L (n (k + 1)) z0) ≤ 2 := by rw [supDist_comm]; exact hd
    have h3 : S.L * supDist c (blockMap S.L (n (k + 1)) z0) ≤ S.L * 2 := Nat.mul_le_mul_left _ h2
    omega
  constructor
  · have hm : (3 * S.L - 1 + S.L - 1) / S.L ≤ ⌊R k⌋₊ + 4 := by
      have : (3 * S.L - 1 + S.L - 1) / S.L ≤ 3 := by
        rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
        omega
      omega
    have h := blockMap_nbhd_lin_of_le Z' (show k + 1 ≤ k + 1 by omega) hm
      (e := y') (mem_nbhd.mpr ⟨z0, hz0, hdist⟩)
    rw [hby, lin_self] at h
    exact h
  · intro hO
    have hzZ : z0 ∈ ((H.locRH (k + 1) Z').step k).Z := by
      rw [locRH_Z Z' (by omega)]; exact hz0
    have := ((H.locRH (k + 1) Z').step k).fine_far (by omega) (hnn k) (by rw [hby]; exact hO) hzZ
    have h4 : S.L * 4 ≤ S.L * (⌊R k⌋₊ + 4) := Nat.mul_le_mul_left _ (by omega)
    omega

variable {M K : ℕ} [NeZero M]

/-- Splitting of a descent chain at an intermediate scale. -/
theorem Desc.split {a c b : ℕ} {Y : H.Comp a} {Z : H.Comp b} (hac : a ≤ c) (hcb : c ≤ b)
    (h : H.Desc a b Y Z) : ∃ W : H.Comp c, H.Desc a c Y W ∧ H.Desc c b W Z := by
  induction h with
  | refl =>
    obtain rfl : c = a := le_antisymm hcb hac
    exact ⟨_, Desc.refl _, Desc.refl _⟩
  | step b' Y' Y'' Y3 hd hrem hs ih =>
    rcases Nat.eq_or_lt_of_le hcb with heq | hlt
    · subst heq
      exact ⟨Y3, Desc.step b' Y' Y'' Y3 hd hrem hs, Desc.refl _⟩
    · obtain ⟨W, h1, h2⟩ := ih (by omega)
      exact ⟨W, h1, Desc.step b' W Y'' Y3 h2 hrem hs⟩

/-- A site over the lineage `Lin_a(Z)` lies over `Z` at scale `b`. -/
theorem cubeMap_mem_of_lin {a b : ℕ} (hbK : b ≤ K) {Z : H.Comp b}
    {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : cubeMap n S.L M K a x ∈ ((H.lin a b Z : Finset (Torus S.d (n a))) : Set _)) :
    cubeMap n S.L M K b x ∈ Z.1 := by
  obtain ⟨Y, hd, hxY⟩ := mem_lin.mp (Finset.mem_coe.mp hx)
  exact cubeMap_mem_of_desc H.F.hnn hbK hd hxY

/-- The lineage is compatible with coarsening: a site over `Lin_a(Z)` is, at every scale
`a ≤ c ≤ b`, over `Lin_c(Z)`. -/
theorem cubeMap_lin_coarsen {a c b : ℕ} (hac : a ≤ c) (hcb : c ≤ b) (hbK : b ≤ K) {Z : H.Comp b}
    {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : cubeMap n S.L M K a x ∈ ((H.lin a b Z : Finset (Torus S.d (n a))) : Set _)) :
    cubeMap n S.L M K c x ∈ ((H.lin c b Z : Finset (Torus S.d (n c))) : Set _) := by
  obtain ⟨Y, hd, hxY⟩ := mem_lin.mp (Finset.mem_coe.mp hx)
  obtain ⟨W, h1, h2⟩ := Desc.split hac hcb hd
  exact Finset.mem_coe.mpr (mem_lin.mpr ⟨W, h2, cubeMap_mem_of_desc H.F.hnn (hcb.trans hbK) h1 hxY⟩)

/-- On the fine set of an old part `Y` of `Z'` the lineages of `Y` and `Z'` agree (`i ≤ k`). -/
theorem mem_lin_part_iff {k : ℕ} (hK : k + 1 ≤ K) {Y : H.Comp k} {Z' : H.Comp (k + 1)}
    (hY : Y ∈ H.parts k Z') {i : ℕ} (hi : i ≤ k) {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : cubeMap n S.L M K k x ∈ Y.1) :
    cubeMap n S.L M K i x ∈ ((H.lin i (k + 1) Z' : Finset (Torus S.d (n i))) : Set _) ↔
      cubeMap n S.L M K i x ∈ ((H.lin i k Y : Finset (Torus S.d (n i))) : Set _) := by
  constructor
  · intro h
    obtain ⟨Y'', hd, hxY⟩ := mem_lin.mp (Finset.mem_coe.mp h)
    obtain ⟨c, hc, hdc⟩ := (desc_succ_iff hi).mp hd
    have hxc : cubeMap n S.L M K k x ∈ c.1 := cubeMap_mem_of_desc H.F.hnn (by omega) hdc hxY
    have hcY : c = Y := Subtype.ext (comp_eq_of_mem c.2 Y.2 hxc hx)
    subst hcY
    exact Finset.mem_coe.mpr (mem_lin.mpr ⟨Y'', hdc, hxY⟩)
  · intro h
    exact lin_mono hY h

/-- At a cube of `𝕋_{j+1}` the localized `Ω_{j+1}` is the global one inside the lineage, and
contains the cube outside it (`j < b`). -/
theorem mem_locOmega_iff' {b : ℕ} (Z : H.Comp b) {j : ℕ} (hj : j < b) (e : Torus S.d (n (j + 1))) :
    e ∈ ((H.locRH b Z).step j).Omega ↔
      e ∈ (H.step j).Omega ∨ e ∉ ((H.lin (j + 1) b Z : Finset (Torus S.d (n (j + 1)))) : Set _) := by
  by_cases hy : e ∈ ((H.lin (j + 1) b Z : Finset (Torus S.d (n (j + 1)))) : Set _)
  · simp only [hy, not_true_eq_false, or_false]
    exact (mem_locOmega_iff Z hj hy).1
  · simp only [hy, not_false_eq_true, or_true, iff_true]
    by_contra h
    obtain ⟨-, h2, -, -⟩ := locRH_derived Z hj
    have : e ∈ ((H.locRH b Z).step j).Omegaᶜ := h
    rw [← h2] at this
    exact hy this.2

/-- The same for `Ω''_{j+1}`. -/
theorem mem_locOmegaDD_iff' {b : ℕ} (Z : H.Comp b) {j : ℕ} (hj : j < b)
    (e : Torus S.d (n (j + 1))) :
    e ∈ ((H.locRH b Z).step j).OmegaDD ↔
      e ∈ (H.step j).OmegaDD ∨
        e ∉ ((H.lin (j + 1) b Z : Finset (Torus S.d (n (j + 1)))) : Set _) := by
  by_cases hy : e ∈ ((H.lin (j + 1) b Z : Finset (Torus S.d (n (j + 1)))) : Set _)
  · simp only [hy, not_true_eq_false, or_false]
    exact (mem_locOmega_iff Z hj hy).2
  · simp only [hy, not_false_eq_true, or_true, iff_true]
    by_contra h
    exact hy (mem_lin_of_not_mem_locOmegaDD Z hj h)

section Agree

variable {k : ℕ} (hK : k + 1 ≤ K) {Y : H.Comp k} {Z' : H.Comp (k + 1)} (hY : Y ∈ H.parts k Z')

include hK hY in
/-- The fine set of an old part lies in that of the component. -/
theorem part_fine_sub {x : Torus S.d (M * n K * S.L ^ K)} (hx : cubeMap n S.L M K k x ∈ Y.1) :
    cubeMap n S.L M K (k + 1) x ∈ Z'.1 := by
  obtain ⟨hrem, hs⟩ := (H.mem_parts k Y Z').mp hY
  exact cubeMap_mem_of_desc H.F.hnn hK (Desc.single hrem hs) hx

include hK hY in
theorem agree_Z {j : ℕ} (hj : j ≤ k) {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : cubeMap n S.L M K k x ∈ Y.1) :
    x ∈ (H.localHistory M K k Y).Z j ↔ x ∈ (H.localHistory M K (k + 1) Z').Z j := by
  have h1 : x ∈ (H.localHistory M K k Y).Z j ↔ cubeMap n S.L M K j x ∈
      ((H.lin j k Y : Finset (Torus S.d (n j))) : Set _) := by
    show (cubeMap n S.L M K j x ∈ ((H.locRH k Y).step j).Z ∧ cubeMap n S.L M K k x ∈ Y.1) ↔ _
    rw [locRH_Z Y hj]
    simp [hx]
  have h2 : x ∈ (H.localHistory M K (k + 1) Z').Z j ↔ cubeMap n S.L M K j x ∈
      ((H.lin j (k + 1) Z' : Finset (Torus S.d (n j))) : Set _) := by
    show (cubeMap n S.L M K j x ∈ ((H.locRH (k + 1) Z').step j).Z ∧
      cubeMap n S.L M K (k + 1) x ∈ Z'.1) ↔ _
    rw [locRH_Z Z' (by omega)]
    simp [part_fine_sub hK hY hx]
  rw [h1, h2, mem_lin_part_iff hK hY hj hx]

include hK hY in
theorem agree_Omega {j : ℕ} (hj : j < k) {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : cubeMap n S.L M K k x ∈ Y.1) :
    x ∈ (H.localHistory M K k Y).Omega j ↔ x ∈ (H.localHistory M K (k + 1) Z').Omega j := by
  show (cubeMap n S.L M K (j + 1) x ∈ ((H.locRH k Y).step j).Omega ∧ cubeMap n S.L M K k x ∈ Y.1) ↔
    (cubeMap n S.L M K (j + 1) x ∈ ((H.locRH (k + 1) Z').step j).Omega ∧
      cubeMap n S.L M K (k + 1) x ∈ Z'.1)
  rw [mem_locOmega_iff' Y hj, mem_locOmega_iff' Z' (by omega), mem_lin_part_iff hK hY (show j + 1 ≤ k by omega) hx]
  simp [hx, part_fine_sub hK hY hx]

include hK hY in
theorem agree_OmegaDD {j : ℕ} (hj : j < k) {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : cubeMap n S.L M K k x ∈ Y.1) :
    x ∈ (H.localHistory M K k Y).OmegaDD j ↔ x ∈ (H.localHistory M K (k + 1) Z').OmegaDD j := by
  show (cubeMap n S.L M K (j + 1) x ∈ ((H.locRH k Y).step j).OmegaDD ∧
      cubeMap n S.L M K k x ∈ Y.1) ↔
    (cubeMap n S.L M K (j + 1) x ∈ ((H.locRH (k + 1) Z').step j).OmegaDD ∧
      cubeMap n S.L M K (k + 1) x ∈ Z'.1)
  rw [mem_locOmegaDD_iff' Y hj, mem_locOmegaDD_iff' Z' (by omega),
    mem_lin_part_iff hK hY (show j + 1 ≤ k by omega) hx]
  simp [hx, part_fine_sub hK hY hx]

include hK hY in
/-- `Ω_i` of the localized region histories of `Y` and `Z'` agree on the fine set of `Y`
(`1 ≤ i ≤ k`). -/
theorem agree_lhOmega {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k) {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : cubeMap n S.L M K k x ∈ Y.1) :
    x ∈ lhOmega (H.localHistory M K k Y) k i ↔
      x ∈ lhOmega (H.localHistory M K (k + 1) Z') (k + 1) i := by
  have hY1 : x ∈ (H.localHistory M K k Y).Z k :=
    (mem_localHistory_Z_top (M := M) (K := K) Y x).mpr hx
  have hZ1 : x ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) :=
    (mem_localHistory_Z_top (M := M) (K := K) Z' x).mpr (part_fine_sub hK hY hx)
  unfold lhOmega
  simp only [Set.mem_union, Set.mem_compl_iff, hY1, hZ1, not_true_eq_false, or_false]
  exact agree_Omega hK hY (by omega) hx

end Agree

/-- The variable sets of a localized history lie in the fine set of its component. -/
theorem varSet_sub_fineSet {k : ℕ} (Z : H.Comp k) (j : ℕ) (κ : VarKind) :
    varSet (H.localHistory M K k Z) j κ ⊆
      fineSet (S := S) (n := n) M K k (Z.1 : Set (Torus S.d (n k))) := by
  intro x hx
  cases κ with
  | large => exact hx.1.2
  | fluct => exact hx.1.2

/-- A block of the fine set of two components lies in both, so they agree. -/
theorem comp_eq_of_block_sub {k j : ℕ} (hjk : j ≤ k) (hkK : k ≤ K) {Y Y' : H.Comp k}
    {z : BlockAt S n M K j} (h : BlockSub (S := S) (n := n) (M := M) (K := K) j z
      (fineSet (S := S) (n := n) M K k (Y.1 : Set (Torus S.d (n k)))))
    (h' : BlockSub (S := S) (n := n) (M := M) (K := K) j z
      (fineSet (S := S) (n := n) M K k (Y'.1 : Set (Torus S.d (n k))))) : Y = Y' := by
  obtain ⟨x0, hx0⟩ := exists_site_in_block (S := S) (n := n) (M := M) (K := K) (hjk.trans hkK) z
  exact Subtype.ext (comp_eq_of_mem Y.2 Y'.2 (h x0 hx0) (h' x0 hx0))

/-- Inversion of a descent at its own scale. -/
theorem Desc.self_eq {b : ℕ} {Y Z : H.Comp b} (h : H.Desc b b Y Z) : Y = Z := by
  cases h with
  | refl => rfl
  | step b' _ _ _ hd _ _ => have := hd.le; omega

/-- A cube of the lineage of `Z'` at scale `k` is a cube of an old part. -/
theorem exists_part_of_mem_lin {k : ℕ} {Z' : H.Comp (k + 1)} {e : Torus S.d (n k)}
    (he : e ∈ ((H.lin k (k + 1) Z' : Finset (Torus S.d (n k))) : Set _)) :
    ∃ Y : H.Comp k, Y ∈ H.parts k Z' ∧ e ∈ Y.1 := by
  obtain ⟨c, hd, hec⟩ := mem_lin.mp (Finset.mem_coe.mp he)
  obtain ⟨c', hc', hdc⟩ := (desc_succ_iff le_rfl).mp hd
  have := Desc.self_eq hdc
  subst this
  exact ⟨c, hc', hec⟩

/-- A site of the record `Z_i` of the localized history of `Z'` lies over its lineage. -/
theorem cubeMap_mem_lin_of_mem_Z {b i : ℕ} (hi : i ≤ b) {Z : H.Comp b}
    {x : Torus S.d (M * n K * S.L ^ K)} (hx : x ∈ (H.localHistory M K b Z).Z i) :
    cubeMap n S.L M K i x ∈ ((H.lin i b Z : Finset (Torus S.d (n i))) : Set _) := by
  have h : cubeMap n S.L M K i x ∈ ((H.locRH b Z).step i).Z := hx.1
  rwa [locRH_Z Z hi] at h

section Near

variable {k : ℕ} {Y : H.Comp k} {Z' : H.Comp (k + 1)}

/-- The cube `e ∈ 𝕋_k` is within `1` of the old part `Y`. -/
def NearPart (Y : H.Comp k) (e : Torus S.d (n k)) : Prop := ∃ z ∈ Y.1, supDist e z ≤ 1

theorem NearPart.of_mem {e : Torus S.d (n k)} (he : e ∈ Y.1) : NearPart Y e :=
  ⟨e, he, by simp [supDist_self]⟩

theorem part_sub_lin (hY : Y ∈ H.parts k Z') :
    (Y.1 : Set (Torus S.d (n k))) ⊆ ((H.lin k (k + 1) Z' : Finset (Torus S.d (n k))) : Set _) := by
  intro z hz
  obtain ⟨hrem, hs⟩ := (H.mem_parts k Y Z').mp hY
  exact Finset.mem_coe.mpr (mem_lin.mpr ⟨Y, Desc.single hrem hs, hz⟩)

/-- A cube within `1` of an old part lies over `Z'`. -/
theorem near_blockMap_mem (hY : Y ∈ H.parts k Z') {e : Torus S.d (n k)} (he : NearPart Y e) :
    blockMap S.L (n (k + 1)) e ∈ (Z'.1 : Set (Torus S.d (n (k + 1)))) := by
  obtain ⟨z, hz, hd⟩ := he
  have h := blockMap_nbhd_lin Z' (le_refl (k + 1)) (e := e)
    (mem_nbhd.mpr ⟨z, part_sub_lin hY hz, hd⟩)
  rwa [lin_self] at h

/-- A cube within `1` of an old part `Y` is in `Y` or outside the lineage of `Z'`. -/
theorem near_cases (hY : Y ∈ H.parts k Z') {e : Torus S.d (n k)} (he : NearPart Y e) :
    e ∈ Y.1 ∨ e ∉ ((H.lin k (k + 1) Z' : Finset (Torus S.d (n k))) : Set _) := by
  by_cases hmem : e ∈ ((H.lin k (k + 1) Z' : Finset (Torus S.d (n k))) : Set _)
  · left
    obtain ⟨z, hz, hd⟩ := he
    obtain ⟨c, hd', hec⟩ := mem_lin.mp (Finset.mem_coe.mp hmem)
    have hzX : z ∈ H.Zp k := comp_subset Y.2 hz
    have hL : 2 ≤ S.L := H.F.ok.two_le_L
    have hω : 2 ≤ S.omega k := hL.trans (H.stepGeom k).hLωk
    have hzc : z ∈ c.1 := mem_comp_of_close c.2 hec hzX (by omega)
    have hcY : c = Y := Subtype.ext (comp_eq_of_mem c.2 Y.2 hzc hz)
    subst hcY
    exact hec
  · right; exact hmem

end Near

end Geom

end RegionHistory

end Balaban.LargeField
