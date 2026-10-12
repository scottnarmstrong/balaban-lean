module

public import Balaban.LargeField.Region.Step
import Mathlib.Tactic.Linarith

/-!
# Inclusions of the region calculus (Part I, Lemma I.3.5)

Lemma I.3.5 (a)-(i) for one step of Definition I.3.1. The statements (a)-(d) are proved for the
set functions of `Balaban.LargeField.Region`; (e)-(i) for a `RegionStep`.

Version note. (f) is stated in the index distance of `𝕋_k` (cubes of `𝕋_{k+1}` over `Ω`): the
fine-set statement of the document is this index statement with the factors `M L^k`
(Lemma I.2.2). In (i), the "in particular" needs `1 ≤ ⌊R_k⌋` (since `⌈9/L⌉ = 5` for `L = 2`);
the document assumes this tacitly (in the flow `R_k ≥ R_base`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace Region

variable {d n0 n1 : ℕ} [NeZero n1]

/-! ### (a) -/

theorem nbhd_subset_compl_OmegaPrime (L ρ : ℕ) (U' : Set (Torus d n1)) :
    nbhd (ρ + 4) U' ⊆ (OmegaPrime L ρ U')ᶜ := by
  intro x hx hxO
  have h : x ∈ nbhd (ρ + 1) (nbhd 3 U') := by
    rw [nbhd_nbhd]; convert hx using 2; omega
  exact opening_disjoint_nbhd (L := L) (m := ρ + 2) (by omega) _ x hxO (by simpa using h)

theorem compl_OmegaPrime_subset (L ρ : ℕ) (hL : 0 < L) (U' : Set (Torus d n1)) :
    (OmegaPrime L ρ U')ᶜ ⊆ nbhd (ρ + L + 3) U' := by
  have h := opening_compl_subset (L := L) (m := ρ + 2) hL (by omega) (nbhd 3 U')
  rw [nbhd_nbhd] at h
  intro x hx
  have := h hx
  convert this using 2
  omega

/-! ### (b), (c): constrained openings -/

theorem openingIn_one_subset (L : ℕ) (F Ω : Set (Torus d n1)) : openingIn L 1 F Ω ⊆ Ω := by
  intro x hx
  exact (openingIn_subset (L := L) (m := 1) le_rfl F Ω hx).1

theorem openingIn_one_disjoint (L : ℕ) (F Ω : Set (Torus d n1)) :
    Disjoint (openingIn L 1 F Ω) F := by
  rw [Set.disjoint_left]
  intro x hx hxF
  have := (openingIn_subset (L := L) (m := 1) le_rfl F Ω hx).2
  simp only [Nat.sub_self, nbhd_zero] at this
  exact this hxF

theorem openingIn_one_diff_subset (L : ℕ) (hL : 0 < L) (F Ω : Set (Torus d n1))
    (hΩ : IsLBlockUnion L Ω) : Ω \ openingIn L 1 F Ω ⊆ nbhd (L - 1) F := by
  have h := openingIn_diff_subset (L := L) (m := 1) hL le_rfl F Ω hΩ
  intro x hx
  have := h hx
  convert this using 2
  omega

theorem Omega_subset (L : ℕ) (P Ω' : Set (Torus d n1)) : Omega L P Ω' ⊆ Ω' :=
  openingIn_one_subset L _ _

theorem Omega_disjoint (L : ℕ) (P Ω' : Set (Torus d n1)) : Disjoint (Omega L P Ω') (nbhd 3 P) :=
  openingIn_one_disjoint L _ _

theorem diff_Omega_subset (L : ℕ) (hL : 0 < L) (P Ω' : Set (Torus d n1)) (hΩ : IsLBlockUnion L Ω') :
    Ω' \ Omega L P Ω' ⊆ nbhd (L + 2) P := by
  have h := openingIn_one_diff_subset L hL (nbhd 3 P) Ω' hΩ
  rw [nbhd_nbhd] at h
  intro x hx
  have := h hx
  convert this using 2
  omega

theorem OmegaDD_subset (L : ℕ) (F Ω : Set (Torus d n1)) : OmegaDD L F Ω ⊆ Ω :=
  openingIn_one_subset L _ _

theorem OmegaDD_disjoint (L : ℕ) (F Ω : Set (Torus d n1)) : Disjoint (OmegaDD L F Ω) F :=
  openingIn_one_disjoint L _ _

theorem diff_OmegaDD_subset (L ρ : ℕ) (hL : 0 < L) (Q R Ω : Set (Torus d n1))
    (hΩ : IsLBlockUnion L Ω) :
    Ω \ OmegaDD L (FDD ρ Q R) Ω ⊆ nbhd (ρ + L + 1) Q ∪ nbhd (2 * ρ + L + 3) R := by
  have h := openingIn_one_diff_subset L hL (FDD ρ Q R) Ω hΩ
  unfold FDD at h
  rw [nbhd_union, nbhd_nbhd, nbhd_nbhd] at h
  intro x hx
  rcases h hx with h1 | h1
  · left; convert h1 using 2; omega
  · right; convert h1 using 2; omega

theorem isLBlockUnion_OmegaPrime (L ρ : ℕ) (U' : Set (Torus d n1)) :
    IsLBlockUnion L (OmegaPrime L ρ U') := opening_isLBlockUnion _ _ _

theorem isLBlockUnion_Omega (L : ℕ) (P Ω' : Set (Torus d n1)) : IsLBlockUnion L (Omega L P Ω') :=
  openingIn_isLBlockUnion _ _ _ _

theorem isLBlockUnion_OmegaDD (L : ℕ) (F Ω : Set (Torus d n1)) :
    IsLBlockUnion L (OmegaDD L F Ω) := openingIn_isLBlockUnion _ _ _ _

/-! ### (d) -/

theorem nbhd_subset_Z0 (L ρ2 : ℕ) (F : Set (Torus d n1)) : nbhd (ρ2 + 2) F ⊆ Z0 L ρ2 F := by
  intro x hx hxO
  exact opening_disjoint_nbhd (L := L) (m := ρ2 + 3) (by omega) F x hxO (by simpa using hx)

theorem Z0_subset_nbhd (L ρ2 : ℕ) (hL : 0 < L) (F : Set (Torus d n1)) :
    Z0 L ρ2 F ⊆ nbhd (ρ2 + L + 1) F := by
  have h := opening_compl_subset (L := L) (m := ρ2 + 3) hL (by omega) F
  intro x hx
  have := h hx
  convert this using 2
  omega

theorem subset_Z0 (L ρ2 : ℕ) (F : Set (Torus d n1)) : F ⊆ Z0 L ρ2 F :=
  (subset_nbhd _ F).trans (nbhd_subset_Z0 L ρ2 F)

/-- Points of the opening are far from `F`. -/
theorem le_supDist_of_mem_opening {L m : ℕ} {F : Set (Torus d n1)} {x : Torus d n1}
    (hx : x ∈ opening L m F) {f : Torus d n1} (hf : f ∈ F) : m ≤ supDist x f := by
  obtain ⟨c, hxc, hc⟩ := hx
  exact le_setDist_iff.mp hc x hxc f hf

end Region

namespace RegionStep

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rprev Rk : ℝ}
  (st : RegionStep d L n0 n1 Rprev Rk)

/-- **Lemma I.3.5 (a)**. -/
theorem nbhd_Uprime_subset (st : RegionStep d L n0 n1 Rprev Rk) :
    nbhd (⌊Rk⌋₊ + 4) st.Uprime ⊆ st.OmegaPrimeᶜ :=
  Region.nbhd_subset_compl_OmegaPrime _ _ _

/-- **Lemma I.3.5 (a)**. -/
theorem OmegaPrime_compl_subset (hL : 0 < L) :
    st.OmegaPrimeᶜ ⊆ nbhd (⌊Rk⌋₊ + L + 3) st.Uprime :=
  Region.compl_OmegaPrime_subset _ _ hL _

/-- **Lemma I.3.5 (b)**. -/
theorem Omega_subset_OmegaPrime : st.Omega ⊆ st.OmegaPrime := Region.Omega_subset _ _ _

/-- **Lemma I.3.5 (b)**. -/
theorem Omega_disjoint_nbhd_P : Disjoint st.Omega (nbhd 3 st.P) := Region.Omega_disjoint _ _ _

/-- **Lemma I.3.5 (b)**. -/
theorem OmegaPrime_diff_Omega_subset (hL : 0 < L) :
    st.OmegaPrime \ st.Omega ⊆ nbhd (L + 2) st.P :=
  Region.diff_Omega_subset _ hL _ _ (Region.isLBlockUnion_OmegaPrime _ _ _)

/-- **Lemma I.3.5 (c)**. -/
theorem OmegaDD_subset_Omega : st.OmegaDD ⊆ st.Omega := Region.OmegaDD_subset _ _ _

/-- **Lemma I.3.5 (c)**. -/
theorem OmegaDD_disjoint_FDD : Disjoint st.OmegaDD st.FDD := Region.OmegaDD_disjoint _ _ _

/-- **Lemma I.3.5 (c)**. -/
theorem Omega_diff_OmegaDD_subset (hL : 0 < L) :
    st.Omega \ st.OmegaDD ⊆ nbhd (⌊Rk⌋₊ + L + 1) st.Q ∪ nbhd (2 * ⌊Rk⌋₊ + L + 3) st.R :=
  Region.diff_OmegaDD_subset _ _ hL _ _ _ (Region.isLBlockUnion_Omega _ _ _)

/-- **Lemma I.3.5 (d)**. -/
theorem nbhd_FZ_subset_Z0 : nbhd (⌊2 * Rk⌋₊ + 2) st.FZ ⊆ st.Z0 := Region.nbhd_subset_Z0 _ _ _

/-- **Lemma I.3.5 (d)**. -/
theorem Z0_subset_nbhd_FZ (hL : 0 < L) : st.Z0 ⊆ nbhd (⌊2 * Rk⌋₊ + L + 1) st.FZ :=
  Region.Z0_subset_nbhd _ _ hL _

/-- **Lemma I.3.5 (e)**: `U' ⊆ Ω'ᶜ`. -/
theorem Uprime_subset_compl : st.Uprime ⊆ st.OmegaPrimeᶜ :=
  (subset_nbhd (⌊Rk⌋₊ + 4) _).trans st.nbhd_Uprime_subset

/-- **Lemma I.3.5 (e)**: `Ω'ᶜ ⊆ Ωᶜ`. -/
theorem OmegaPrime_compl_subset_Omega_compl : st.OmegaPrimeᶜ ⊆ st.Omegaᶜ :=
  Set.compl_subset_compl.mpr st.Omega_subset_OmegaPrime

/-- **Lemma I.3.5 (e)**: `Ωᶜ ⊆ Ω''ᶜ`. -/
theorem Omega_compl_subset_OmegaDD_compl : st.Omegaᶜ ⊆ st.OmegaDDᶜ :=
  Set.compl_subset_compl.mpr st.OmegaDD_subset_Omega

/-- **Lemma I.3.5 (e)**: `Ω''ᶜ ⊆ F^Z`. -/
theorem OmegaDD_compl_subset_FZ : st.OmegaDDᶜ ⊆ st.FZ :=
  (subset_nbhd 4 _).trans Set.subset_union_left

/-- **Lemma I.3.5 (e)**: `F^Z ⊆ Z^{(0)}`. -/
theorem FZ_subset_Z0 : st.FZ ⊆ st.Z0 := Region.subset_Z0 _ _ _

/-- **Lemma I.3.5 (e)**: `Z^{(0)} ⊆ Z^pre`. -/
theorem Z0_subset_Zpre (ω : ℕ) (crit : Option ℕ) : st.Z0 ⊆ st.Zpre ω crit :=
  Region.subset_Zpre ω crit _

/-- **Lemma I.3.5 (e)**: `U' ⊆ Z^{(0)}` (and the whole chain). -/
theorem Uprime_subset_Z0 : st.Uprime ⊆ st.Z0 :=
  st.Uprime_subset_compl.trans <| st.OmegaPrime_compl_subset_Omega_compl.trans <|
    st.Omega_compl_subset_OmegaDD_compl.trans <| st.OmegaDD_compl_subset_FZ.trans st.FZ_subset_Z0

/-- **Lemma I.3.5 (e)**: `Ω''ᶜ ⊆ Z^{(0)}`. -/
theorem OmegaDD_compl_subset_Z0 : st.OmegaDDᶜ ⊆ st.Z0 :=
  st.OmegaDD_compl_subset_FZ.trans st.FZ_subset_Z0

/-- **Lemma I.3.5 (e)**: `Ωᶜ ⊆ Z^{(0)}`. -/
theorem Omega_compl_subset_Z0 : st.Omegaᶜ ⊆ st.Z0 :=
  st.Omega_compl_subset_OmegaDD_compl.trans st.OmegaDD_compl_subset_Z0

/-- **Lemma I.3.5 (e)**: `Ω'ᶜ ⊆ Z^{(0)}`. -/
theorem OmegaPrime_compl_subset_Z0 : st.OmegaPrimeᶜ ⊆ st.Z0 :=
  st.OmegaPrime_compl_subset_Omega_compl.trans st.Omega_compl_subset_Z0

/-- **Lemma I.3.5 (e)**: `P ⊆ Ω' \ Ω`. -/
theorem P_subset_compl_Omega : st.P ⊆ st.Omegaᶜ := fun _ hp hpO =>
  (Set.disjoint_left.mp st.Omega_disjoint_nbhd_P) hpO (subset_nbhd 3 _ hp)

/-- **Lemma I.3.5 (e)**: `Q ∪ R ⊆ Ω''ᶜ`, first `Q`. -/
theorem Q_subset_compl_OmegaDD : st.Q ⊆ st.OmegaDDᶜ := fun _ hq hqO =>
  (Set.disjoint_left.mp st.OmegaDD_disjoint_FDD) hqO
    (Or.inl (subset_nbhd _ _ hq))

/-- **Lemma I.3.5 (e)**: `R ⊆ Ω''ᶜ`. -/
theorem R_subset_compl_OmegaDD : st.R ⊆ st.OmegaDDᶜ := fun _ hq hqO =>
  (Set.disjoint_left.mp st.OmegaDD_disjoint_FDD) hqO
    (Or.inr (subset_nbhd _ _ hq))

/-- **Lemma I.3.5 (e)**: `S ⊆ F^Z`. -/
theorem S_subset_FZ : st.S ⊆ st.FZ :=
  (subset_nbhd 1 _).trans Set.subset_union_right

/-- **Lemma I.3.5 (e)**: `𝒩 ⊆ Z^{(0)}`. -/
theorem newCubes_subset_Z0 : st.newCubes ⊆ st.Z0 := by
  intro x hx
  rcases hx with ((hx | hx) | hx) | hx
  · exact st.Omega_compl_subset_Z0 (st.P_subset_compl_Omega hx)
  · exact st.OmegaDD_compl_subset_Z0 (st.Q_subset_compl_OmegaDD hx)
  · exact st.OmegaDD_compl_subset_Z0 (st.R_subset_compl_OmegaDD hx)
  · exact st.FZ_subset_Z0 (st.S_subset_FZ hx)

/-- **Lemma I.3.5 (f)**: `Ω ⊇ Ω'' ⊇ (Z^pre)ᶜ`. -/
theorem Zpre_compl_subset_OmegaDD (ω : ℕ) (crit : Option ℕ) : (st.Zpre ω crit)ᶜ ⊆ st.OmegaDD := by
  intro x hx
  by_contra hxO
  exact hx (st.Z0_subset_Zpre ω crit (st.OmegaDD_compl_subset_Z0 hxO))

/-- **Lemma I.3.5 (f)**: `Ω ⊇ Ω''`. -/
theorem OmegaDD_subset_Omega' : st.OmegaDD ⊆ st.Omega := st.OmegaDD_subset_Omega

/-- **Lemma I.3.5 (f)** (index form). A cube of `𝕋_k` over a cube of `Ω_{k+1}` is at index distance
`≥ L(⌊R_k⌋+4) + ⌊R_{k-1}⌋ + 2` from `Z_k`. (With Lemma I.2.2 this is the fine-set bound
`dist_∞(Z_k, Ω_{k+1}) ≥ ([R_k]+4)LM + ([R_{k-1}]+1)M`, in scale-`k` units.) -/
theorem fine_far (hL : 0 < L) (hn : n0 = L * n1) {y : Torus d n0}
    (hy : blockMap L n1 y ∈ st.Omega) {z : Torus d n0} (hz : z ∈ st.Z) :
    L * (⌊Rk⌋₊ + 4) + ⌊Rprev⌋₊ + 2 ≤ supDist y z := by
  by_contra hlt
  push Not at hlt
  have hlt' : supDist z y ≤ (⌊Rprev⌋₊ + 1) + L * (⌊Rk⌋₊ + 4) := by
    rw [supDist_comm]; omega
  obtain ⟨y', h1, h2⟩ := exists_split hlt'
  have hy'U : blockMap L n1 y' ∈ st.Uprime :=
    ⟨y', mem_nbhd.mpr ⟨z, hz, by rw [supDist_comm]; exact h1⟩, rfl⟩
  have hd := supDist_blockMap_le hn y' y
  have hdiv : (L * (⌊Rk⌋₊ + 4) + L - 1) / L = ⌊Rk⌋₊ + 4 := by
    have : L * (⌊Rk⌋₊ + 4) + L - 1 = (L - 1) + L * (⌊Rk⌋₊ + 4) := by omega
    rw [this, Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt (by omega)]
    omega
  have hd2 : supDist (blockMap L n1 y') (blockMap L n1 y) ≤ ⌊Rk⌋₊ + 4 := by
    refine hd.trans ?_
    rw [← hdiv]
    exact Nat.div_le_div_right (by omega)
  have hmem : blockMap L n1 y ∈ nbhd (⌊Rk⌋₊ + 4) st.Uprime :=
    mem_nbhd.mpr ⟨blockMap L n1 y', hy'U, by rw [supDist_comm]; exact hd2⟩
  exact st.nbhd_Uprime_subset hmem (st.Omega_subset_OmegaPrime hy)

/-- **Lemma I.3.5 (f)**: as fine sets `Z_kᶜ ⊇ Ω_{k+1}`: a cube over `Ω_{k+1}` is not in `Z_k`. -/
theorem not_mem_Z_of_mem_Omega (hL : 0 < L) (hn : n0 = L * n1) {y : Torus d n0}
    (hy : blockMap L n1 y ∈ st.Omega) : y ∉ st.Z := fun hz => by
  have := st.fine_far hL hn hy hz
  rw [supDist_self] at this
  omega

/-- **Lemma I.3.5 (g)** (P6 (2.6)): `(((Z^pre)ᶜ)^{≈2})^∼ ∩ ((Ω''ᶜ)^{∼3} ∪ S) = ∅`
(`≈` at scale `k+1` adds `⌊R_k⌋ + 1`). Needs `R_k ≥ 0`. -/
theorem thick2_Zpre_compl_disjoint (hRk : 0 ≤ Rk) (ω : ℕ) (crit : Option ℕ) :
    Disjoint (nbhd 1 (thick2 ⌊Rk⌋₊ (st.Zpre ω crit)ᶜ)) (nbhd 3 st.OmegaDDᶜ ∪ st.S) := by
  rw [Set.disjoint_left]
  intro v hv hvT
  rw [thick2_eq, nbhd_nbhd] at hv
  obtain ⟨x, hx, hxv⟩ := mem_nbhd.mp hv
  have hxO : x ∈ opening L (⌊2 * Rk⌋₊ + 3) st.FZ := by
    by_contra hxn
    exact hx (st.Z0_subset_Zpre ω crit hxn)
  have hfloor : 2 * ⌊Rk⌋₊ ≤ ⌊2 * Rk⌋₊ := by
    apply Nat.le_floor
    push_cast
    have := Nat.floor_le hRk
    linarith
  have hfar : ⌊2 * Rk⌋₊ + 3 + 1 ≤ supDist x v := by
    refine far_of_nbhd (by omega) fun w hw => Region.le_supDist_of_mem_opening hxO ?_
    rcases hvT with hvT | hvT
    · left
      have : w ∈ nbhd 1 (nbhd 3 st.OmegaDDᶜ) := mem_nbhd.mpr ⟨v, hvT, by rw [supDist_comm]; exact hw⟩
      rwa [nbhd_nbhd] at this
    · right
      exact mem_nbhd.mpr ⟨v, hvT, by rw [supDist_comm]; exact hw⟩
  rw [supDist_comm] at hxv
  omega

/-- **Lemma I.3.5 (h)**: if `P = Q = R = ∅` (and `S = ∅`, which is not needed here) then
`Ω' = Ω = Ω''` (P7 p. 498). -/
theorem eq_of_new_empty (hP : st.P = ∅) (hQ : st.Q = ∅) (hR : st.R = ∅) : st.OmegaPrime = st.Omega ∧ st.Omega = st.OmegaDD := by
  have h1 : st.Omega = st.OmegaPrime := by
    show openingIn L 1 (nbhd 3 st.P) st.OmegaPrime = st.OmegaPrime
    rw [hP, nbhd_empty]
    exact openingIn_empty _ (Region.isLBlockUnion_OmegaPrime _ _ _)
  have h2 : st.OmegaDD = st.Omega := by
    show openingIn L 1 st.FDD st.Omega = st.Omega
    have : st.FDD = ∅ := by
      show Region.FDD ⌊Rk⌋₊ st.Q st.R = ∅
      rw [hQ, hR]; simp [Region.FDD, nbhd_empty]
    rw [this]
    exact openingIn_empty _ (Region.isLBlockUnion_Omega _ _ _)
  exact ⟨h1.symm, h2.symm⟩

/-- **Lemma I.3.5 (i)** (P7 p. 503): for `⌈m/L⌉ ≤ ⌊R_k⌋ + 4`, a cube of `𝕋_k` within `m` of `U_k`
lies over `Ω'ᶜ` (hence over `Ωᶜ`). -/
theorem blockMap_nbhd_U_subset (hn : n0 = L * n1) {m : ℕ} (hm : (m + L - 1) / L ≤ ⌊Rk⌋₊ + 4)
    {y : Torus d n0} (hy : y ∈ nbhd m st.U) : blockMap L n1 y ∈ st.OmegaPrimeᶜ := by
  have h := blockMap_nbhd_subset hn (m := n1) m st.U ⟨y, hy, rfl⟩
  exact st.nbhd_Uprime_subset (nbhd_mono hm subset_rfl h)

/-- **Lemma I.3.5 (i)**: the ring `U_kᶜ ∩ U_k^{∼m}` avoids `Z_k`. -/
theorem ring_subset_compl_Z {y : Torus d n0} (hy : y ∈ (st.U)ᶜ) : y ∉ st.Z := fun hz =>
  hy (subset_nbhd _ _ hz)

/-- **Lemma I.3.5 (i)**, "in particular": for `L ≥ 2` and `1 ≤ ⌊R_k⌋`, a cube of the ring
`U_kᶜ ∩ U_k^{∼9}` avoids `Z_k` and lies over `Ωᶜ`. -/
theorem ring_nine (hL : 2 ≤ L) (hn : n0 = L * n1) (hρ : 1 ≤ ⌊Rk⌋₊) {y : Torus d n0}
    (hy : y ∈ (st.U)ᶜ ∩ nbhd 9 st.U) :
    y ∉ st.Z ∧ blockMap L n1 y ∈ st.Omegaᶜ := by
  refine ⟨st.ring_subset_compl_Z hy.1, ?_⟩
  have hm : (9 + L - 1) / L ≤ ⌊Rk⌋₊ + 4 := by
    have : (9 + L - 1) / L ≤ 5 := by
      rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
      omega
    omega
  exact st.OmegaPrime_compl_subset_Omega_compl (st.blockMap_nbhd_U_subset hn hm hy.2)

end RegionStep

end Balaban.LargeField
