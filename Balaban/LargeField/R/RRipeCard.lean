module

public import Balaban.LargeField.R.ChainCount
public import Balaban.LargeField.R.RipeBox
public import Balaban.LargeField.History.FlowBook
public import Balaban.LargeField.Def7FineSize
import Mathlib.Tactic.Linarith

/-!
# Removed components are small boxes (cardinality and diameter)

The large-field operation `R^{(k)}` removes the *ripe* components of `Z^pre_k`
(Definition I.4.1, `RegionHistory.Admissible`).  A ripe component has the geometric window of
Part III, Lemma III.1.2 (`RegionHistory.ripe_window`), and its `Z_k` is one box of side at most
`crit_k = 2ρ_k + 10` scale-`k` cubes in every direction (`RipeWindow.lin_eq_box`).  This file
states the consequences for a *removed* component `c ∈ Rem_k`, in the form the cover-extension
estimate of `notes/phase1/VMOD-37.md` §2 (OPEN-R-FINE-EXTRA) will consume:

* `removed_ripe`: a removed component is ripe, `1 ≤ k ≤ k₀`;
* `removed_ripeWindow`: it has the window `RipeWindow`;
* `removed_eq_box`, `removed_card_le`: it is a box with sides in `[1, crit_k]`, so it has at most
  `crit_k ^ d` cubes;
* `removed_supDist_lt`: any two of its cubes are at torus sup-distance `< crit_k` (scale-`k`
  cube units);
* `removed_sep`: two distinct components of `Z^pre_k` are at sup-distance `≥ ω_k`;
* `coverIdx`, `card_coverIdx_le`, `removed_coverIdx_card_le`: the number of block positions
  (aligned groups of `L` cubes per direction, the `π'_k`-boxes in cube-index units) meeting a
  box of side `s` is at most `∏ (s_i + L - 1)`, hence at most `(crit_k + 2L)^d`.

NOT proved here: the cover-extension estimate (2) of VMOD-37 itself, the charge inequality (3),
and everything analytic about `R`.  This file is pure finite geometry.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K}

/-- A removed component is ripe (this is the admissibility `H.Admissible`), and the scale `k`
satisfies `1 ≤ k ≤ k₀` because `Rem_k = ∅` otherwise. -/
theorem removed_ripe (hadm : H.Admissible) {k : ℕ} {c : H.Comp k} (hc : c.1 ∈ H.rem k) :
    S.Ripe k (H.bk k c) ∧ 1 ≤ k ∧ k ≤ k0 := by
  refine ⟨hadm k c hc, ?_, ?_⟩
  · by_contra h
    have : k = 0 := by omega
    rw [H.rem_empty k (Or.inl this)] at hc
    exact Finset.notMem_empty _ hc
  · by_contra h
    rw [H.rem_empty k (Or.inr (by omega))] at hc
    exact Finset.notMem_empty _ hc

/-- A removed component has the geometric window of Lemma III.1.2. -/
theorem removed_ripeWindow (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hadm : H.Admissible) {k : ℕ}
    (hkK : k ≤ K) {c : H.Comp k} (hc : c.1 ∈ H.rem k) : H.RipeWindow k c := by
  obtain ⟨hr, -, hk0⟩ := removed_ripe hadm hc
  exact ripe_window G hT hk0 hkK hr

/-- **A removed component is one box** of sides in `[1, crit_k]`, `crit_k = 2ρ_k + 10`. -/
theorem removed_eq_box (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hadm : H.Admissible) {k : ℕ}
    (hkK : k ≤ K) {c : H.Comp k} (hc : c.1 ∈ H.rem k) :
    ∃ (a : Torus S.d (n k)) (sd : Fin S.d → ℕ),
      (c.1 : Set (Torus S.d (n k))) = box a sd ∧ ∀ i, 1 ≤ sd i ∧ sd i ≤ S.crit k := by
  obtain ⟨-, hk1, hk0⟩ := removed_ripe hadm hc
  have W := removed_ripeWindow G hT hadm hkK hc
  obtain ⟨-, hcov, -⟩ := W.unique_box k c W.point.2.2.le (Desc.refl c)
  exact comp_eq_box_of_covered hk1 hk0 (hT k hk1 hk0) c hcov

/-- **Cardinality**: a removed component has at most `crit_k ^ d = (2ρ_k + 10)^d` cubes
(`Set.ncard` form). -/
theorem removed_ncard_le (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hadm : H.Admissible) {k : ℕ}
    (hkK : k ≤ K) {c : H.Comp k} (hc : c.1 ∈ H.rem k) :
    (c.1 : Set (Torus S.d (n k))).ncard ≤ (2 * S.rho k + 10) ^ S.d := by
  obtain ⟨a, sd, hbox, hsd⟩ := removed_eq_box G hT hadm hkK hc
  rw [hbox]
  refine (ncard_box_le a sd).trans ?_
  calc ∏ i, sd i ≤ ∏ _i : Fin S.d, S.crit k := by
        apply Finset.prod_le_prod
        intro i _; exact (hsd i).2
    _ = (2 * S.rho k + 10) ^ S.d := by simp [Setting.crit]

/-- **Cardinality** (`Finset.card` form). -/
theorem removed_card_le (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hadm : H.Admissible) {k : ℕ}
    (hkK : k ≤ K) {c : H.Comp k} (hc : c.1 ∈ H.rem k) :
    c.1.card ≤ (2 * S.rho k + 10) ^ S.d := by
  have := removed_ncard_le G hT hadm hkK hc
  rwa [Set.ncard_coe_finset] at this

end RegionHistory

/-- Two points of a box of sides `≤ m` are at torus sup-distance `< m` (`0 < m`). -/
theorem supDist_lt_of_mem_box {d n : ℕ} [NeZero n] {a x y : Torus d n} {sd : Fin d → ℕ} {m : ℕ}
    (hm : 0 < m) (hsd : ∀ i, sd i ≤ m) (hx : x ∈ box a sd) (hy : y ∈ box a sd) :
    supDist x y < m := by
  have : supDist x y ≤ m - 1 := by
    rw [supDist_le_iff]
    intro i
    obtain ⟨j, hj, hxj⟩ := hx i
    obtain ⟨j', hj', hyj⟩ := hy i
    rw [cycNorm_le_iff]
    refine ⟨(j : ℤ) - j', ?_, ?_⟩
    · have h1 := hsd i
      rw [abs_le]
      constructor <;> omega
    · rw [hxj, hyj]; push_cast; ring
  omega

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K}

/-- **Diameter**: any two cubes of a removed component are at torus sup-distance `< crit_k`,
in units of scale-`k` cubes (`supDist` on `Torus d (n k)`). -/
theorem removed_supDist_lt (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hadm : H.Admissible) {k : ℕ}
    (hkK : k ≤ K) {c : H.Comp k} (hc : c.1 ∈ H.rem k) {x y : Torus S.d (n k)}
    (hx : x ∈ c.1) (hy : y ∈ c.1) : supDist x y < 2 * S.rho k + 10 := by
  obtain ⟨a, sd, hbox, hsd⟩ := removed_eq_box G hT hadm hkK hc
  have hx' : x ∈ box a sd := hbox ▸ (Finset.mem_coe.mpr hx)
  have hy' : y ∈ box a sd := hbox ▸ (Finset.mem_coe.mpr hy)
  exact supDist_lt_of_mem_box (m := 2 * S.rho k + 10) (by omega) (fun i => (hsd i).2) hx' hy'

/-- **Separation**: two distinct components of `Z^pre_k` are at torus sup-distance `≥ ω_k`
(Lemma I.2.12 (a)); in particular so are two distinct removed components. -/
theorem comp_sep {k : ℕ} {c c' : H.Comp k} (hne : c ≠ c') {x y : Torus S.d (n k)}
    (hx : x ∈ c.1) (hy : y ∈ c'.1) : S.omega k ≤ supDist x y :=
  comps_sep c.2 c'.2 (fun h => hne (Subtype.ext h)) hx hy

end RegionHistory

/-! ### Cover boxes meeting a box of cubes

The `π'_k`-cover boxes of `Def7FineSize.lean` are the aligned fine boxes `box b (L · a)` with
`a = L^{k+m₀+m₁} = L^k M` (`Fluctuation.ModAdmissible`).  In units of scale-`k` cubes, an aligned
base `b = a q` is the cube `q`, and `box b (L a)` is the block of the `L` cubes `q, …, q + L - 1`
per direction (a block may start at any cube).  `coverIdx L Y` is the set of block positions `q`
whose block meets the set `Y` of cubes. -/

/-- The block positions `q` whose block of `L` cubes per direction meets `Y`. -/
def coverIdx {d n : ℕ} (L : ℕ) (Y : Set (Torus d n)) : Set (Torus d n) :=
  {q | ∃ t : Fin d → ℕ, (∀ μ, t μ < L) ∧ q + Balaban.Localization.natT t ∈ Y}

/-- The block positions meeting a box of side `s` lie in a box of side `s + L - 1`. -/
theorem coverIdx_box_subset {d n : ℕ} [NeZero n] (L : ℕ) (a : Torus d n) (s : Fin d → ℕ) :
    coverIdx L (box a s) ⊆
      box (a - Balaban.Localization.natT (fun _ => L - 1)) (fun i => s i + (L - 1)) := by
  rintro q ⟨t, ht, hq⟩ i
  obtain ⟨j, hj, hji⟩ := hq i
  refine ⟨j + (L - 1) - t i, ?_, ?_⟩
  · have := ht i; beta_reduce; omega
  · have h1 : t i ≤ j + (L - 1) := by have := ht i; omega
    have h2 : q i = a i + (j : ZMod n) - (t i : ZMod n) := by
      have : q i + (t i : ZMod n) = a i + (j : ZMod n) := by simpa using hji
      rw [← this]; ring
    rw [h2]
    push_cast [Nat.cast_sub h1]
    simp only [Pi.sub_apply, Balaban.Localization.natT_apply]
    ring

/-- The number of block positions meeting a box of side `s` is at most `∏ (s_i + L - 1)`. -/
theorem ncard_coverIdx_box_le {d n : ℕ} [NeZero n] (L : ℕ) (a : Torus d n) (s : Fin d → ℕ) :
    (coverIdx L (box a s)).ncard ≤ ∏ i, (s i + (L - 1)) :=
  (Set.ncard_le_ncard (coverIdx_box_subset L a s) (Set.toFinite _)).trans
    (ncard_box_le _ _)

/-- One coordinate of the block map of a fine box: if `a ∣ b.val` then the cube index of `b + w`
is the cube index of `b` plus `w / a`. -/
theorem blockIdx_add {N a nk : ℕ} [NeZero N] (hN : N = a * nk) (b : ZMod N) (w : ℕ)
    (hb : b.val % a = 0) :
    (((b + (w : ZMod N)).val / a : ℕ) : ZMod nk) =
      ((b.val / a : ℕ) : ZMod nk) + ((w / a : ℕ) : ZMod nk) := by
  have hdvd : a ∣ b.val := Nat.dvd_of_mod_eq_zero hb
  subst hN
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod, Nat.mod_mul_right_div_self,
    ZMod.natCast_mod, Nat.add_div_of_dvd_right hdvd]
  push_cast; rfl

section Fine

open Balaban.Localization Def7

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K m₀ m₁ : ℕ} [NeZero S.L]
  (F : FineSizeFrame S n M K m₀ m₁)

/-- Unit conversion: the side of the fine torus is `a · n_k`, `a = L^{k+m₀+m₁}` the fine cell side
of scale `k`, i.e. the fine torus is `n_k` cells of `a` sites per direction. -/
theorem fine_side_eq (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K) :
    (F.N₁ * S.L ^ m₁) * S.L ^ K = cellSide S.L m₀ m₁ k * n k := by
  have hM : NeZero M := ⟨by rw [F.hM]; exact (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _).ne'⟩
  have h1 := fine_eq (L := S.L) (M := M) (nn := n) hnn hkK
  have h2 : cellSide S.L m₀ m₁ k = S.L ^ k * M := by
    unfold cellSide; rw [F.hM, ← pow_add]; congr 1; ring
  rw [F.side, h1, h2]

/-- The scale-`k` cube index of a fine site (the block map of the fine torus onto `𝕋_k`). -/
noncomputable def cubeIdx (k : ℕ) (b : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K) : Torus S.d (n k) :=
  cubeMap n S.L M K k (castT F.side b)

theorem cubeIdx_apply (k : ℕ) (b : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K) (μ : Fin S.d) :
    cubeIdx F k b μ = (((b μ).val / (S.L ^ k * M) : ℕ) : ZMod (n k)) := by
  unfold cubeIdx cubeMap
  simp only [blockMap_apply, blockCoord]
  rw [castT_val]

theorem d7Pull_iff (k : ℕ) (Y : Set (Torus S.d (n k))) (x : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K) :
    x ∈ d7Pull F k Y ↔ cubeIdx F k x ∈ Y := Iff.rfl

/-- The cube index is injective on aligned fine sites. -/
theorem cubeIdx_injOn (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K)
    {b b' : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K}
    (hb : Aligned (cellSide S.L m₀ m₁ k) b) (hb' : Aligned (cellSide S.L m₀ m₁ k) b')
    (h : cubeIdx F k b = cubeIdx F k b') : b = b' := by
  have hside := fine_side_eq F hnn hkK
  have hcs : cellSide S.L m₀ m₁ k = S.L ^ k * M := by
    unfold cellSide; rw [F.hM, ← pow_add]; congr 1; ring
  have hpos : 0 < cellSide S.L m₀ m₁ k := cellSide_pos m₀ m₁ k
  funext μ
  have hμ := congrFun h μ
  rw [cubeIdx_apply, cubeIdx_apply, ← hcs] at hμ
  have hlt : ∀ x : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K,
      (x μ).val / cellSide S.L m₀ m₁ k < n k := by
    intro x
    rw [Nat.div_lt_iff_lt_mul hpos]
    have h1 := lt_of_lt_of_eq (ZMod.val_lt (x μ)) hside
    exact lt_of_lt_of_eq h1 (Nat.mul_comm _ _)
  have h2 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hμ
  rw [Nat.mod_eq_of_lt (hlt b), Nat.mod_eq_of_lt (hlt b')] at h2
  apply ZMod.val_injective
  rw [← Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (hb μ)),
    ← Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (hb' μ)), h2]

/-- A fine box `box b (L a)` with aligned base `b` meeting the fine lift of a set `Y` of cubes
has its block position `cubeIdx b` in `coverIdx L Y`. -/
theorem cubeIdx_mem_coverIdx (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K)
    {b : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K}
    (hb : Aligned (cellSide S.L m₀ m₁ k) b) (Y : Set (Torus S.d (n k)))
    (hne : (Balaban.Localization.box b (S.L * cellSide S.L m₀ m₁ k) ∩ d7Pull F k Y).Nonempty) :
    cubeIdx F k b ∈ coverIdx S.L Y := by
  have hside := fine_side_eq F hnn hkK
  have hcs : cellSide S.L m₀ m₁ k = S.L ^ k * M := by
    unfold cellSide; rw [F.hM, ← pow_add]; congr 1; ring
  have hpos : 0 < cellSide S.L m₀ m₁ k := cellSide_pos m₀ m₁ k
  obtain ⟨x, ⟨w, hw, rfl⟩, hxY⟩ := hne
  refine ⟨fun μ => w μ / cellSide S.L m₀ m₁ k, fun μ => ?_, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul hpos]; exact hw μ
  · have : cubeIdx F k (b + natT w) = cubeIdx F k b + natT (fun μ => w μ / cellSide S.L m₀ m₁ k) := by
      funext μ
      simp only [Pi.add_apply, cubeIdx_apply, natT_apply]
      rw [← hcs]
      exact blockIdx_add (by rw [hside]) (b μ) (w μ) (hb μ)
    rw [← this]; exact hxY

/-- The `π'_k`-cover boxes of `Def7FineSize.lean` (the aligned fine boxes `box b (L · a)`,
`a = L^{k+m₀+m₁}`, of `Fluctuation.ModAdmissible`), identified by their bases `b`, that meet the
fine lift `d7Pull F k Y` of a set `Y` of scale-`k` cubes. -/
def coverBoxes (k : ℕ) (Y : Set (Torus S.d (n k))) :
    Set (Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K) :=
  {b | Aligned (cellSide S.L m₀ m₁ k) b ∧
    (Balaban.Localization.box b (S.L * cellSide S.L m₀ m₁ k) ∩ d7Pull F k Y).Nonempty}

/-- **Cover boxes meeting a set of cubes (fine units)**: the `π'_k`-cover boxes meeting the fine
lift of a set `Y` of scale-`k` cubes are at most as many as the block positions `coverIdx L Y`. -/
theorem coverBoxes_ncard_le (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K)
    (Y : Set (Torus S.d (n k))) :
    (coverBoxes F k Y).ncard ≤ (coverIdx S.L Y).ncard := by
  refine Set.ncard_le_ncard_of_injOn (cubeIdx F k) (fun b hb => ?_) (fun b hb b' hb' h => ?_)
    (Set.toFinite _)
  · exact cubeIdx_mem_coverIdx F hnn hkK hb.1 Y hb.2
  · exact cubeIdx_injOn F hnn hkK hb.1 hb'.1 h

end Fine

namespace RegionHistory

open Balaban.Localization Def7

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} [NeZero S.L] {M m₀ m₁ : ℕ}

/-- **Fine units**: the number of `π'_k`-cover boxes meeting the fine lift of a removed component
is at most `(crit_k + 2L)^d` (so `C_{d,L} = 1`).  The tower condition `n_i = L n_{i+1}` is
`StepGeom.hn` of the history. -/
theorem removed_coverBoxes_ncard_le (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hadm : H.Admissible)
    (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ} (hkK : k ≤ K) {c : H.Comp k}
    (hc : c.1 ∈ H.rem k) :
    (coverBoxes F k (c.1 : Set (Torus S.d (n k)))).ncard ≤ (S.crit k + 2 * S.L) ^ S.d := by
  have hnn : ∀ i, i < K → n i = S.L * n (i + 1) := fun i hi => (H.stepGeom hi).hn
  obtain ⟨a, sd, hbox, hsd⟩ := removed_eq_box G hT hadm hkK hc
  refine (coverBoxes_ncard_le F hnn hkK _).trans ?_
  rw [hbox]
  refine (ncard_coverIdx_box_le S.L a sd).trans ?_
  calc ∏ i, (sd i + (S.L - 1)) ≤ ∏ _i : Fin S.d, (S.crit k + 2 * S.L) := by
        apply Finset.prod_le_prod
        intro i _
        have := (hsd i).2
        omega
    _ = (S.crit k + 2 * S.L) ^ S.d := by simp

/-- **Sum over removed components** (T5): for a finite set `C` of removed components of scale `k`
(for instance those whose fine lift meets a label `X`), the total number of cover boxes meeting
them is at most `|C| (crit_k + 2L)^d`. -/
theorem removed_coverBoxes_sum_le (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hadm : H.Admissible)
    (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ} (hkK : k ≤ K) (C : Finset (H.Comp k))
    (hC : ∀ c ∈ C, c.1 ∈ H.rem k) :
    ∑ c ∈ C, (coverBoxes F k (c.1 : Set (Torus S.d (n k)))).ncard ≤
      C.card * (S.crit k + 2 * S.L) ^ S.d := by
  calc ∑ c ∈ C, (coverBoxes F k (c.1 : Set (Torus S.d (n k)))).ncard
      ≤ ∑ _c ∈ C, (S.crit k + 2 * S.L) ^ S.d :=
        Finset.sum_le_sum fun c hc => removed_coverBoxes_ncard_le G hT hadm F hkK (hC c hc)
    _ = C.card * (S.crit k + 2 * S.L) ^ S.d := by simp

/-- Distinct components of `Z^pre_k` are disjoint sets of cubes. -/
theorem comp_disjoint {k : ℕ} {c c' : H.Comp k} (hne : c ≠ c') :
    Disjoint c.1 c'.1 := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  have h := comp_sep hne hx hx'
  rw [supDist_self] at h
  have : 2 ≤ S.omega k := by unfold Setting.omega; split_ifs <;> omega
  omega

/-- The fine lifts of distinct components of `Z^pre_k` are disjoint. -/
theorem comp_lift_disjoint (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ} {c c' : H.Comp k}
    (hne : c ≠ c') :
    Disjoint (d7Pull F k (c.1 : Set (Torus S.d (n k)))) (d7Pull F k (c'.1 : Set (Torus S.d (n k)))) := by
  rw [Set.disjoint_iff_inter_eq_empty, ← d7Pull_inter,
    Set.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_coe.mpr (comp_disjoint hne)), d7Pull_empty]

end RegionHistory

end Balaban.LargeField
