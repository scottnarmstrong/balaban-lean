/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.GSIsoOfOmega
import Mathlib.Tactic.Linarith

/-!
# Local generating sets on two tori: the exact transport of the operators

Two generating sets `G`, `H` of the step tori `CTorus d L N₁ m₁ K` and `CTorus d L N₁' m₁ K` are
carried onto each other by the box map `bm` when all their domains lie in the centred box of
radius `ρ` and the domains `Ω_n` correspond on the box of radius `ρ + 1` (`OmegaIso`; the local
generating sets of corresponding polymers, `localB_omega_boxMap_all`).  Then `bm` is a bijection
`Ω₁(G) ≃ Ω₁(H)` (`OmegaIso.e`), and every matrix on `Ω₁` built from the operator of the set is
the reindexing of the corresponding matrix of the other set.  Unlike the whole-lattice comparison
of `TwoTorusCubeOps` (which compares the operators of `levelGS` on a box only), the comparison is
exact: no estimate, no block argument for the inverses (`Matrix.inv_submatrix_equiv`).

* `cutFullMatrix_corr`: the entries of `-Δ_cut + ν + Q* a Q` at corresponding sites of the box,
  for any two generating sets whose layers correspond there (generic form of
  `cutFullMatrix_boxMap`);
* `OmegaIso.e`, `OmegaIso.layerIndex_eq`, `OmegaIso.spacing_eq`, `OmegaIso.collar_iff`;
* `OmegaIso.cutOperator_submatrix`, `OmegaIso.dirichletOperator_submatrix`: the cut operators of
  corresponding cuts and potentials are reindexings of each other;
* `OmegaIso.cubeCut_iff`: the cube cuts of sets corresponding on the box;
* `OmegaIso.intBox_iff`: the interaction box of a centre of the box and of its image;
* `OmegaIso.cD_submatrix`, `OmegaIso.cubeH_submatrix`, `OmegaIso.cubeG_submatrix`: the cube
  operators of a centre of the box and of its image (the cube resolvent through
  `Matrix.inv_submatrix_equiv`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Polymer
  Balaban.Polymer.TwoTorusStep Matrix

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱ' : ℝ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ K) ((N₁ * L ^ m₁) * L ^ K)

/-! ### The full matrix of two generating sets at corresponding sites -/

/-- **The full cut matrix at corresponding sites** (generic form of `cutFullMatrix_boxMap`): the
entries at two sites of the box of radius `ρ` of `-Δ + ν + Q* a Q` with a cut removed correspond,
if the two cuts correspond at the bonds based in the box of radius `ρ + 1` and the layers of the
two generating sets correspond at the two sites.  Margin: `2 ρ + 3 L^K + 5` below both sides. -/
theorem cutFullMatrix_corr {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {H : GeneratingSet d L (N₁' * L ^ m₁) K ϱ'} (a : ℕ → ℝ) (ν : ℝ) {ρ : ℕ}
    (hn : 2 * ρ + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {cut : Finset (CTorus d L N₁ m₁ K × Fin d)} {cut' : Finset (CTorus d L N₁' m₁ K × Fin d)}
    (hcut : ∀ z, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) z → ∀ μ : Fin d,
      ((z, μ) ∈ cut ↔ (bm z, μ) ∈ cut'))
    {x y : CTorus d L N₁ m₁ K} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y)
    (hlx : ∀ n, 1 ≤ n → n ≤ K → (bm x ∈ H.layer n ↔ x ∈ G.layer n))
    (hly : ∀ n, 1 ≤ n → n ≤ K → (bm y ∈ H.layer n ↔ y ∈ G.layer n)) :
    cutFullMatrix H a ν cut' (bm x) (bm y) = cutFullMatrix G a ν cut x y := by
  unfold cutFullMatrix cutLaplacian
  simp only [Matrix.add_apply, Matrix.sub_apply]
  rw [latticeLaplacian_apply, latticeLaplacian_apply, sum_bondMatrix_apply, sum_bondMatrix_apply,
    avgMatrix_corr a hn hn' hx hy hlx hly]
  have e0 : bm x = bm y ↔ x = y :=
    ⟨boxMap_inj (hm' := (by omega : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ K)) hx hy,
      fun h => by rw [h]⟩
  have e1 : ∀ μ : Fin d, (bm y = bm x + Pi.single μ 1) ↔ (y = x + Pi.single μ 1) := fun μ =>
    (step_boxMap_iff (r := ρ) (by omega) (by omega) hx hy μ).symm
  have e2 : ∀ μ : Fin d, (bm x = bm y + Pi.single μ 1) ↔ (x = y + Pi.single μ 1) := fun μ =>
    (step_boxMap_iff (r := ρ) (by omega) (by omega) hy hx μ).symm
  have e3 : ∀ μ : Fin d, bm (x - Pi.single μ 1) = bm x - Pi.single μ 1 := fun μ =>
    boxMap_sub_single (ρ := ρ) (by omega) (by omega) hx μ
  have e4 : ∀ μ : Fin d, ((bm x - Pi.single μ 1, μ) ∈ cut') ↔ ((x - Pi.single μ 1, μ) ∈ cut) := by
    intro μ
    rw [← e3 μ]
    exact (hcut _ (inBox_sub_single (by omega) hx μ) μ).symm
  have e5 : ∀ μ : Fin d, ((bm x, μ) ∈ cut') ↔ ((x, μ) ∈ cut) := fun μ =>
    (hcut x (inBox_mono (Nat.le_succ ρ) hx) μ).symm
  have e6 : ∀ μ : Fin d, ((bm y, μ) ∈ cut') ↔ ((y, μ) ∈ cut) := fun μ =>
    (hcut y (inBox_mono (Nat.le_succ ρ) hy) μ).symm
  simp only [e0, e1, e2, e4, e5, e6]

/-! ### Two generating sets carried onto each other by the box map -/

/-- **Two generating sets of two tori carried onto each other by the box map**: the domains lie
in the centred box of radius `ρ` of each torus, the domains `Ω_n` correspond on the box of radius
`ρ + 1`, and both sides exceed `2 ρ + 16 L^(K + m₁ + 2) + 16` (the room for the interaction
boxes of the cubes of the sets). -/
structure OmegaIso (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (H : GeneratingSet d L (N₁' * L ^ m₁) K ϱ') (ρ : ℕ) : Prop where
  boxG : ∀ x ∈ G.Ω 1, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x
  boxH : ∀ x ∈ H.Ω 1, InBox d ρ ((N₁' * L ^ m₁) * L ^ K) x
  corr : ∀ x, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) x → ∀ n, 1 ≤ n → n ≤ K →
    (bm x ∈ H.Ω n ↔ x ∈ G.Ω n)
  room : 2 * ρ + 16 * L ^ (K + m₁ + 2) + 16 < (N₁ * L ^ m₁) * L ^ K
  room' : 2 * ρ + 16 * L ^ (K + m₁ + 2) + 16 < (N₁' * L ^ m₁) * L ^ K
  hK : 1 ≤ K

/-- The powers of `L` below the room of an `OmegaIso`. -/
theorem pow_le_room {j : ℕ} (hj : j ≤ K) :
    1 ≤ L ^ j ∧ L ^ K ≤ L ^ (K + m₁ + 2) ∧ L ^ (j + m₁) ≤ L ^ (K + m₁ + 2) ∧
      L ^ (j + 2) ≤ L ^ (K + m₁ + 2) ∧ L * L ^ (j + m₁) ≤ L ^ (K + m₁ + 2) ∧
      1 ≤ L ^ (j + m₁) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  refine ⟨Nat.one_le_pow _ _ hL, Nat.pow_le_pow_right hL (by omega),
    Nat.pow_le_pow_right hL (by omega), Nat.pow_le_pow_right hL (by omega), ?_,
    Nat.one_le_pow _ _ hL⟩
  rw [← pow_succ']
  exact Nat.pow_le_pow_right hL (by omega)

namespace OmegaIso

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {H : GeneratingSet d L (N₁' * L ^ m₁) K ϱ'}
  {ρ : ℕ}

theorem mem_iff (hI : OmegaIso G H ρ) {x : CTorus d L N₁ m₁ K}
    (hx : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) x) : bm x ∈ H.Ω 1 ↔ x ∈ G.Ω 1 :=
  hI.corr x hx 1 le_rfl hI.hK

theorem layer_iff (hI : OmegaIso G H ρ) {x : CTorus d L N₁ m₁ K}
    (hx : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) x) {n : ℕ} (h1 : 1 ≤ n) (hn : n ≤ K) :
    bm x ∈ H.layer n ↔ x ∈ G.layer n :=
  layer_corr_of_omega (fun m hm hmK => hI.corr x hx m hm hmK) h1 hn

theorem inBox_succ (hI : OmegaIso G H ρ) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.Ω 1) :
    InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) x :=
  inBox_mono (Nat.le_succ ρ) (hI.boxG x hx)

theorem mapsTo (hI : OmegaIso G H ρ) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.Ω 1) :
    bm x ∈ H.Ω 1 :=
  (hI.mem_iff (hI.inBox_succ hx)).2 hx

theorem two_lt (hI : OmegaIso G H ρ) :
    2 * (ρ + 1) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K ∧
      2 * (ρ + 1) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K := by
  obtain ⟨-, h2, -⟩ := pow_le_room (L := L) (m₁ := m₁) (le_refl K)
  have := hI.room; have := hI.room'
  constructor <;> omega

/-- **The bijection `Ω₁(G) ≃ Ω₁(H)` of an `OmegaIso`**: the box map. -/
def e (hI : OmegaIso G H ρ) : G.Ω 1 ≃ H.Ω 1 :=
  Equiv.ofBijective (fun x => ⟨bm (x : CTorus d L N₁ m₁ K), hI.mapsTo x.2⟩)
    ⟨fun x y hxy => Subtype.ext (boxMap_inj
        (hm' := (by have := hI.two_lt.2; omega : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ K))
        (hI.boxG x x.2) (hI.boxG y y.2) (congrArg Subtype.val hxy)),
      fun x' => by
        have hb := hI.boxH x' x'.2
        have hlt : 2 * ρ + 1 < (N₁ * L ^ m₁) * L ^ K := by have := hI.two_lt.1; omega
        have hxb : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (bm' (x' : CTorus d L N₁' m₁ K)) :=
          inBox_boxMap hlt hb
        have hback : bm (bm' (x' : CTorus d L N₁' m₁ K)) = x' := boxMap_boxMap hlt hb
        have hmem : bm' (x' : CTorus d L N₁' m₁ K) ∈ G.Ω 1 := by
          refine (hI.mem_iff (inBox_mono (Nat.le_succ ρ) hxb)).1 ?_
          rw [hback]; exact x'.2
        exact ⟨⟨_, hmem⟩, Subtype.ext hback⟩⟩

@[simp] theorem coe_e (hI : OmegaIso G H ρ) (x : G.Ω 1) :
    ((hI.e x : H.Ω 1) : CTorus d L N₁' m₁ K) = bm (x : CTorus d L N₁ m₁ K) := rfl

theorem coe_e_symm (hI : OmegaIso G H ρ) (x' : H.Ω 1) :
    bm ((hI.e.symm x' : G.Ω 1) : CTorus d L N₁ m₁ K) = (x' : CTorus d L N₁' m₁ K) := by
  rw [← coe_e hI, Equiv.apply_symm_apply]

/-- The layer index at corresponding sites of `Ω₁`. -/
theorem layerIndex_eq (hI : OmegaIso G H ρ) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.Ω 1) :
    H.layerIndex (bm x) = G.layerIndex x := by
  obtain ⟨h1, h2, h3⟩ := G.layerIndex_spec hx
  exact H.layerIndex_eq h1 h2 ((hI.layer_iff (hI.inBox_succ hx) h1 h2).2 h3)

/-- The spacing at corresponding sites of `Ω₁`. -/
theorem spacing_eq (hI : OmegaIso G H ρ) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.Ω 1) :
    H.spacing (bm x) = G.spacing x := by
  unfold GeneratingSet.spacing
  rw [hI.layerIndex_eq hx]

/-- The collar at corresponding sites of the box of radius `ρ + 1`. -/
theorem collar_iff (hI : OmegaIso G H ρ) {x : CTorus d L N₁ m₁ K}
    (hx : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) x) : bm x ∈ collar H ↔ x ∈ collar G :=
  collar_corr_of_omega (by have := hI.two_lt.1; omega) (by have := hI.two_lt.2; omega) hI.boxG
    hI.boxH (fun z hz => hI.mem_iff hz) hx

/-! ### The operators -/

/-- **The cut operators are reindexings of each other**, for cuts corresponding at the bonds
based in the box of radius `ρ + 1` and potentials corresponding under `e`. -/
theorem cutOperator_submatrix (hI : OmegaIso G H ρ) (a : ℕ → ℝ) (ν : ℝ)
    {cut : Finset (CTorus d L N₁ m₁ K × Fin d)} {cut' : Finset (CTorus d L N₁' m₁ K × Fin d)}
    (hcut : ∀ z, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) z → ∀ μ : Fin d,
      ((z, μ) ∈ cut ↔ (bm z, μ) ∈ cut'))
    {α : G.Ω 1 → ℂ} {α' : H.Ω 1 → ℂ} (hα : ∀ x, α' (hI.e x) = α x) :
    (cutOperator G a ν cut α).submatrix hI.e.symm hI.e.symm = cutOperator H a ν cut' α' := by
  ext x' y'
  obtain ⟨x, rfl⟩ := hI.e.surjective x'
  obtain ⟨y, rfl⟩ := hI.e.surjective y'
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  have ⟨h1, h2⟩ := hI.two_lt
  have hxb := hI.boxG x x.2
  have hyb := hI.boxG y y.2
  unfold cutOperator Green.restrictOp
  simp only [Matrix.add_apply, Matrix.submatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  rw [coe_e, coe_e, cutFullMatrix_corr a ν (ρ := ρ) (by omega) (by omega) hcut hxb hyb
    (fun n h1 h2 => hI.layer_iff (hI.inBox_succ x.2) h1 h2)
    (fun n h1 h2 => hI.layer_iff (hI.inBox_succ y.2) h1 h2)]
  congr 1
  simp only [EmbeddingLike.apply_eq_iff_eq, hα]

/-- **The Dirichlet operators are reindexings of each other**, for potentials corresponding under
`e`. -/
theorem dirichletOperator_submatrix (hI : OmegaIso G H ρ) (a : ℕ → ℝ) (ν : ℝ)
    {α : G.Ω 1 → ℂ} {α' : H.Ω 1 → ℂ} (hα : ∀ x, α' (hI.e x) = α x) :
    (dirichletOperator G a ν α).submatrix hI.e.symm hI.e.symm = dirichletOperator H a ν α' := by
  rw [← cutOperator_empty, ← cutOperator_empty]
  exact hI.cutOperator_submatrix a ν (fun z _ μ => by simp) hα

/-- **The cube cuts of two sets corresponding on the box of radius `ρ + 2`** correspond at the
bonds based in the box of radius `ρ + 1`. -/
theorem cubeCut_iff (hI : OmegaIso G H ρ) {Λ : Finset (CTorus d L N₁ m₁ K)}
    {Λ' : Finset (CTorus d L N₁' m₁ K)}
    (hΛ : ∀ w, InBox d (ρ + 2) ((N₁ * L ^ m₁) * L ^ K) w → (w ∈ Λ ↔ bm w ∈ Λ'))
    {z : CTorus d L N₁ m₁ K} (hz : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) z) (μ : Fin d) :
    (z, μ) ∈ cubeCut G Λ ↔ (bm z, μ) ∈ cubeCut H Λ' := by
  have ⟨h1, h2⟩ := hI.two_lt
  have hz2 := inBox_add_single (ρ := ρ + 1) (by omega) hz μ
  have ha : bm (z + Pi.single μ 1) = bm z + Pi.single μ 1 :=
    boxMap_add_single (ρ := ρ + 1) (by omega) (by omega) hz μ
  have hz2' : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) (z + Pi.single μ 1) ∨
      ¬ (z + Pi.single μ 1 ∈ G.Ω 1 ∨ bm (z + Pi.single μ 1) ∈ H.Ω 1) := by
    by_cases hm : z + Pi.single μ 1 ∈ G.Ω 1
    · exact Or.inl (hI.inBox_succ hm)
    · by_cases hm' : bm (z + Pi.single μ 1) ∈ H.Ω 1
      · left
        have hb := hI.boxH _ hm'
        have := valMinAbs_boxMap (m' := (N₁' * L ^ m₁) * L ^ K) (by omega : 2 * (ρ + 2) + 1 < _)
          hz2
        exact fun ν => by rw [← this ν]; exact (hb ν).trans (by omega)
      · exact Or.inr (by tauto)
  have hzG : z ∈ G.Ω 1 ↔ bm z ∈ H.Ω 1 := (hI.mem_iff hz).symm
  have hzeG : z + Pi.single μ 1 ∈ G.Ω 1 ↔ bm z + Pi.single μ 1 ∈ H.Ω 1 := by
    rw [← ha]
    rcases hz2' with h | h
    · exact (hI.mem_iff h).symm
    · tauto
  rw [mem_cubeCut, mem_cubeCut, hΛ z (inBox_mono (Nat.le_succ _) hz),
    hΛ _ hz2, ha, hzG, hzeG]

/-! ### The cube operators -/

/-- **The interaction box of a centre of the box and of its image** agree at the sites of the box
of radius `ρ + 2`. -/
theorem intBox_iff (hI : OmegaIso G H ρ) {j : ℕ} (hj : j ≤ K) {y0 : CTorus d L N₁ m₁ K}
    (hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0) {w : CTorus d L N₁ m₁ K}
    (hw : InBox d (ρ + 2) ((N₁ * L ^ m₁) * L ^ K) w) :
    w ∈ intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K) ↔
      bm w ∈ intBox ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) := by
  obtain ⟨-, -, h3, -, -, -⟩ := pow_le_room (L := L) (m₁ := m₁) hj
  have := hI.room; have := hI.room'
  exact mem_intBox_boxMap_iff_of_le (R' := ρ + 2 + 3 * L ^ (j + m₁)) hy0 (by omega) (by omega)
    (by omega) (inBox_mono (by omega) hw)

/-- The cube multiplier `c_z` of a centre of the box and of its image. -/
theorem cD_submatrix (hI : OmegaIso G H ρ) {j : ℕ} (hj : j ≤ K) {y0 : CTorus d L N₁ m₁ K}
    (hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0) :
    (cD G ((j, y0) : ℕ × CTorus d L N₁ m₁ K)).submatrix hI.e.symm hI.e.symm =
      cD H ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) := by
  unfold cD
  rw [Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x'
  obtain ⟨x, rfl⟩ := hI.e.surjective x'
  simp only [Function.comp_apply, Equiv.symm_apply_apply, coe_e]
  exact if_congr (hI.intBox_iff hj hy0 (inBox_mono (by omega) (hI.boxG x x.2))) rfl rfl

/-- **The cube operators `H_z(A)` of a centre of the box and of its image** are reindexings of
each other, for potentials corresponding under `e`. -/
theorem cubeH_submatrix (hI : OmegaIso G H ρ) (a : ℕ → ℝ) (ν : ℝ) {j : ℕ} (hj : j ≤ K)
    {y0 : CTorus d L N₁ m₁ K} (hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0)
    {α : G.Ω 1 → ℂ} {α' : H.Ω 1 → ℂ} (hα : ∀ x, α' (hI.e x) = α x) :
    (cubeH G a ν α ((j, y0) : ℕ × CTorus d L N₁ m₁ K)).submatrix hI.e.symm hI.e.symm =
      cubeH H a ν α' ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) := by
  unfold cubeH
  exact hI.cutOperator_submatrix a ν (fun z hz μ => hI.cubeCut_iff
    (fun w hw => hI.intBox_iff hj hy0 hw) hz μ) hα

/-- **The cube resolvents `G^{(z)}(A) c_z` of a centre of the box and of its image** are
reindexings of each other, for potentials corresponding under `e` (no invertibility is needed:
`Matrix.inv_submatrix_equiv`). -/
theorem cubeG_submatrix (hI : OmegaIso G H ρ) (a : ℕ → ℝ) (ν : ℝ) {j : ℕ} (hj : j ≤ K)
    {y0 : CTorus d L N₁ m₁ K} (hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0)
    {α : G.Ω 1 → ℂ} {α' : H.Ω 1 → ℂ} (hα : ∀ x, α' (hI.e x) = α x) :
    (cubeG G a ν α ((j, y0) : ℕ × CTorus d L N₁ m₁ K)).submatrix hI.e.symm hI.e.symm =
      cubeG H a ν α' ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) := by
  unfold cubeG
  rw [← Matrix.submatrix_mul_equiv _ _ _ hI.e.symm, ← Matrix.inv_submatrix_equiv,
    hI.cubeH_submatrix a ν hj hy0 hα, hI.cD_submatrix hj hy0]

end OmegaIso

end Balaban.Polymer.LocalIso
