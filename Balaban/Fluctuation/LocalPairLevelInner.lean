/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairReplacement
public import Balaban.Fluctuation.PhysicalReadsFNu
public import Balaban.SmallField.LocalGeneratorCovariance

/-!
# The inner-cube hypotheses of the replacement at the local generator

The component hypotheses `hin` of `Dec2.Gs_rows_cross`, `Dec2.decFixed_rows_cross`,
`Dec2.decBg_component_cross` and `eTermFun_replacement_cross` ask, for every cube inside the
component with a non-zero factor, that it is a cube of the second cover inside the component, with
the same factor `s_z = ∏_{P ∈ 𝒬(z)} s_P`, the same layers on the stencil of its interaction cube
and the same partition function.  For the cover of the ambient level set `𝔹_{k+1}`
(`IsLevel 𝔹_{k+1} (k + 1)`) against the cover of `𝔹_{k+1}(Y) = localB (k + 1) … Y` these follow
from the IndexMatch lemmas of `LocalPairIndexMatch.lean` when the relevant cubes have their
`𝒞_{k+1}`-cubes in `Y` (they lie in the top layer `Ω_{k+1}(𝔹_{k+1}(Y))`) and the two parameter
vectors agree on those cubes.

* `layer_iff_of_level_of_top`: a level set `𝔹_n` and a generating set `𝔹'` without layer `n + 1`
  have the same layers at the sites of `Ω_n(𝔹')` (the stencil hypothesis for the fluctuation pair
  `(𝔹_k, 𝔹_k(Y))`);
* `level_localB_inner_cross`: the hypothesis `hin` for the covers of `𝔹_{k+1}` and `𝔹_{k+1}(Y)`
  with operator generating sets `H` (whole level) and `H'`;
* `level_localB_iff_of_cover`, `level_localB_chi_eq_of_cover`, `level_localB_qset_eq_of_cover`:
  the IndexMatch statements with the depth condition on the cubes of the two covers only;
  `fineCubeIdx_top_eq_of_sameCell`, `level_localB_hat_of_box`: the hat-box condition from the
  thickened cube in the top layer; `localB_hatBox_top_of_active`, `localB_hat_of_active`: for an
  active local cube (parameters cut off the top layer) its thickened cube is in the top layer;
* `level_localB_active_cross`: with parameters `s'` of `𝔹_{k+1}(Y)` vanishing at the cubes off the
  top layer (the transport `τ` of P3: the lower-layer cubes of `𝔹_{k+1}(Y)` are cut), every cube of
  the cover of `𝔹_{k+1}(Y)` with a non-zero factor is a cube of the cover of `𝔹_{k+1}` with the same
  factor; `level_localB_inner_cross'` (the hypothesis `hin'`), `level_localB_dich_cross`,
  `level_localB_row_cross` (the dichotomy and row hypotheses of the second pair from those of the
  first) are its consequences.  The interaction cube of a top cube is assumed to lie in `Ω₁(H')`
  (`htop`; for `H' = 𝔹_{k+1}(Y)` this is the `5 L` thickening of P3 (4.5), not proved here).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Balaban.LargeField Balaban.SmallField.GsSpec Balaban.Polymer.TwoTorusStep

section Level

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'}

/-- **Layers of a level set and of a set without the layer `n + 1`.**  If every site lies in the
layer `n` of `G` (`IsLevel G n`) and `G'` has no layer above `n`, then at a site of `Ω_n(G')` the
layers `1 ≤ m ≤ K` of `G` and `G'` agree (both: the layer `n` only). -/
theorem layer_iff_of_level_of_top {n : ℕ} (hG : IsLevel G n) (htop : G'.Ω (n + 1) = ∅)
    {x : Torus d (N₀ * L ^ K)} (hx : x ∈ G'.Ω n) {m : ℕ} (hm : 1 ≤ m) (hmK : m ≤ K) :
    x ∈ G.layer m ↔ x ∈ G'.layer m := by
  obtain ⟨hn1, hnK⟩ := hG.bounds
  have hxn : x ∈ G.layer n := hG.mem_layer x
  have hx' : x ∈ G'.layer n := G'.mem_layer.2 ⟨hx, by rw [htop]; exact Finset.notMem_empty _⟩
  constructor
  · intro h
    by_cases hmn : m = n
    · subst hmn; exact hx'
    · exact absurd h (G.layer_disjoint hn1 hnK hm hmK (Ne.symm hmn) hxn)
  · intro h
    by_cases hmn : m = n
    · subst hmn; exact hxn
    · by_cases hlt : m < n
      · exact absurd h (fun h' => (G'.mem_layer.1 h').2
          (G'.Ω_antitone (by omega) (by omega) (by omega) hx))
      · have hgt : n + 1 ≤ m := by omega
        have := (G'.mem_layer.1 h).1
        have h2 : x ∈ G'.Ω (n + 1) := G'.Ω_antitone (by omega) hgt (by omega) this
        rw [htop] at h2
        exact absurd h2 (Finset.notMem_empty _)

end Level

section LevelInner

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱl ϱH ϱH' : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}

/-- **IndexMatch for the cubes of the two covers**: a pair `q'` is a cube of the cover of the
ambient level set exactly when it is a cube of the cover of `𝔹_{k+1}(Y)`, if its base lies in the
top layer `Ω_{k+1}(𝔹_{k+1}(Y))` whenever it is a cube of one of the two covers.

The core of `level_localB_iff_of_cover`, for an arbitrary generating set `Gl` in place of `𝔹_{k+1}(Y)`. -/
theorem level_iff_of_cover (hG' : IsLevel Gp (k + 1))
    {q' : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (h : (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx Gl) →
      q'.2 ∈ Gl.Ω (k + 1)) :
    q' ∈ cubeIdx Gp ↔ q' ∈ cubeIdx Gl := by
  by_cases hc : q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx Gl
  · exact level_mem_cubeIdx_iff_of_mem_top hG' (h hc)
  · exact iff_of_false (fun h' => hc (Or.inl h')) (fun h' => hc (Or.inr h'))

/-- **IndexMatch for the cubes of the two covers**: a pair `q'` is a cube of the cover of the
ambient level set exactly when it is a cube of the cover of `𝔹_{k+1}(Y)`, if its base lies in the
top layer `Ω_{k+1}(𝔹_{k+1}(Y))` whenever it is a cube of one of the two covers. -/
theorem level_localB_iff_of_cover (hG' : IsLevel Gp (k + 1)) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    {q' : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (h : (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx (localB (k + 1) hk Y hsep)) →
      q'.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1)) :
    q' ∈ cubeIdx Gp ↔ q' ∈ cubeIdx (localB (k + 1) hk Y hsep) := level_iff_of_cover hG' h

/-- **The partition functions of the two covers agree at `x`** if the cubes of either cover whose
bump does not vanish at `x` have their bases in the top layer (`chi_congr_of_active`, with
`level_localB_iff_of_cover` for the cubes of the two covers).

The core of `level_localB_chi_eq_of_cover`, for an arbitrary generating set `Gl` in place of `𝔹_{k+1}(Y)`. -/
theorem level_chi_eq_of_cover (hG' : IsLevel Gp (k + 1))
    {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1),
      (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx Gl) →
        cubeBump m₁ q'.1 q'.2 x ≠ 0 → q'.2 ∈ Gl.Ω (k + 1))
    (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    chi Gp q x = chi Gl q x :=
  chi_congr_of_active (fun q' hq' => level_iff_of_cover hG' fun hc => hx q' hc hq') q

/-- **The partition functions of the two covers agree at `x`** if the cubes of either cover whose
bump does not vanish at `x` have their bases in the top layer (`chi_congr_of_active`, with
`level_localB_iff_of_cover` for the cubes of the two covers). -/
theorem level_localB_chi_eq_of_cover (hG' : IsLevel Gp (k + 1)) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1),
      (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx (localB (k + 1) hk Y hsep)) →
        cubeBump m₁ q'.1 q'.2 x ≠ 0 → q'.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1))
    (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    chi Gp q x = chi (localB (k + 1) hk Y hsep) q x := level_chi_eq_of_cover hG' hx q

/-- **The footprints of the two covers agree at `q`** if the cubes of either cover meeting the
thickened cube `□̂_z` have their bases in the top layer (`qset_coverOf_congr`, with
`level_localB_iff_of_cover` for the cubes of the two covers).

The core of `level_localB_qset_eq_of_cover`, for an arbitrary generating set `Gl` in place of `𝔹_{k+1}(Y)`. -/
theorem level_qset_eq_of_cover (hG' : IsLevel Gp (k + 1))
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1),
      (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx Gl) →
        (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧ InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
          q'.2 ∈ Gl.Ω (k + 1)) :
    (coverOf Gp).Qset q = (coverOf Gl).Qset q :=
  qset_coverOf_congr fun q' hq' => level_iff_of_cover hG' fun hc => hq q' hc hq'

/-- **The footprints of the two covers agree at `q`** if the cubes of either cover meeting the
thickened cube `□̂_z` have their bases in the top layer (`qset_coverOf_congr`, with
`level_localB_iff_of_cover` for the cubes of the two covers). -/
theorem level_localB_qset_eq_of_cover (hG' : IsLevel Gp (k + 1)) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1),
      (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx (localB (k + 1) hk Y hsep)) →
        (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧ InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
          q'.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1)) :
    (coverOf Gp).Qset q = (coverOf (localB (k + 1) hk Y hsep)).Qset q := level_qset_eq_of_cover hG' hq
/-- Two sites in the same cell of side `M₁ L^j`, `j ≤ k + 1`, have the same `𝒞_{k+1}`-cube. -/
theorem fineCubeIdx_top_eq_of_sameCell {j : ℕ} (hj : j ≤ k + 1) {y z : CTorus d L N₁ m₁ (k + 1)}
    (h : SameCell (L ^ (j + m₁)) y z) :
    fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
        (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
        (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) := by
  funext ν
  rw [fineCubeIdx_torusCast_coord, fineCubeIdx_torusCast_coord]
  unfold blockCoord
  have e : L ^ (k + 1) * L ^ m₁ = L ^ (j + m₁) * L ^ (k + 1 - j) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h ν]

/-- **The top layer of the literal local generator is a union of cells of side `M₁ L^{k+1}`**: two
sites in one cell of side `L^{k+1+m₁}` are in the top layer together. -/
theorem localB_top_union (hk : k + 1 ≤ k + 1) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hsep : ϱl ≤ minSep L (L ^ m₁)) (x y : CTorus d L N₁ m₁ (k + 1))
    (hxy : SameCell (L ^ (k + 1 + m₁)) x y) :
    x ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) ↔ y ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) := by
  have h := fineCubeIdx_top_eq_of_sameCell (le_refl (k + 1)) hxy
  rw [mem_localB_Ω_top, mem_localB_Ω_top]
  exact ⟨fun hx w hw => hx w (hw.trans h.symm), fun hy w hw => hy w (hw.trans h)⟩

/-- **The hat-box condition from the hat box.**  If every site of the thickened cube `□̂_z` lies in
the top layer `Ω_{k+1}(𝔹_{k+1}(Y))`, every cube of either cover meeting `□̂_z` has its base there
(a cube of a cover has level at most `k + 1`, and its cell lies in a `𝒞_{k+1}`-cube).

The core of `level_localB_hat_of_box`, for an arbitrary generating set `Gl` in place of `𝔹_{k+1}(Y)`. -/
theorem level_hat_of_box (hU : ∀ x y : CTorus d L N₁ m₁ (k + 1), SameCell (L ^ (k + 1 + m₁)) x y →
      (x ∈ Gl.Ω (k + 1) ↔ y ∈ Gl.Ω (k + 1)))  {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hbox : ∀ y, InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y →
      y ∈ Gl.Ω (k + 1)) :
    ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1),
      (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx Gl) →
        (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧ InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
          q'.2 ∈ Gl.Ω (k + 1) := by
  rintro q' hc ⟨y, hyc, hyb⟩
  have hj : q'.1 ≤ k + 1 := by
    rcases hc with h | h
    · exact ((mem_cubeIdx _).1 h).1.2
    · exact ((mem_cubeIdx _).1 h).1.2
  exact (hU y q'.2 (hyc.mono (pow_dvd_pow L (by omega)))).1 (hbox y hyb)

/-- **The hat-box condition from the hat box.**  If every site of the thickened cube `□̂_z` lies in
the top layer `Ω_{k+1}(𝔹_{k+1}(Y))`, every cube of either cover meeting `□̂_z` has its base there
(a cube of a cover has level at most `k + 1`, and its cell lies in a `𝒞_{k+1}`-cube). -/
theorem level_localB_hat_of_box (hk : k + 1 ≤ k + 1) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hsep : ϱl ≤ minSep L (L ^ m₁)) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hbox : ∀ y, InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y →
      y ∈ (localB (k + 1) hk Y hsep).Ω (k + 1)) :
    ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1),
      (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx (localB (k + 1) hk Y hsep)) →
        (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧ InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
          q'.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) := level_hat_of_box (localB_top_union hk Y hsep) hbox

/-- **The inner-cube hypothesis `hin` at the local generator.**  Let `𝔹_{k+1}` be a level set and
`𝔹_{k+1}(Y) = localB (k + 1) … Y`, with operator generating sets `H` (with `Ω₁(H)` the whole torus)
and `H'`.  Suppose every cube of the cover of `𝔹_{k+1}` inside `T` (read on `H`) with a non-zero
factor has: the same layers of `H`, `H'` on the stencil of its interaction cube; its base, the bases
of the cubes whose bump does not vanish on its interaction cube and the bases of the cubes meeting
its thickened cube `□̂_z` in the top layer `Ω_{k+1}(𝔹_{k+1}(Y))` (their `𝒞_{k+1}`-cubes lie in `Y`).
If the two parameter vectors agree at the cubes with base in `Ω_{k+1}(𝔹_{k+1}(Y))`, then the cube is
a cube of the cover of `𝔹_{k+1}(Y)` inside `T` (read on `H'`), with the same factor, the same layers
on the stencil and the same partition function.

The core of `level_localB_inner_cross`, for an arbitrary generating set `Gl` in place of `𝔹_{k+1}(Y)`. -/
theorem level_inner_cross (hG' : IsLevel Gp (k + 1))
    {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH}
    {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH'} (hH : ∀ x, x ∈ H.Ω 1)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : Dec2.DecParams (coverOf Gp)}
    {s' : Dec2.DecParams (coverOf Gl)}
    (hdeep : ∀ q ∈ Dec2.innerCentres (coverOf Gp) H T,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 →
        (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
          (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
            ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
        q.2 ∈ Gl.Ω (k + 1) ∧
        (∀ x ∈ intBox q, ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1),
          (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx Gl) → cubeBump m₁ q'.1 q'.2 x ≠ 0 →
          q'.2 ∈ Gl.Ω (k + 1)) ∧
        (∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1), (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx Gl) →
          (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
          InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
            q'.2 ∈ Gl.Ω (k + 1)))
    (hs : ∀ P : ℕ × CTorus d L N₁ m₁ (k + 1), P.2 ∈ Gl.Ω (k + 1) →
      Dec2.extS (coverOf Gl) s' P = Dec2.extS (coverOf Gp) s P) :
    ∀ q ∈ Dec2.innerCentres (coverOf Gp) H T,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 →
        q ∈ Dec2.innerCentres (coverOf Gl) H' T ∧
        (coverOf Gl).sProd
            (Dec2.extS (coverOf Gl) s') q =
          (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ∧
        (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
          (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
            ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
        (∀ x ∈ intBox q, (coverOf Gp).chi q x = (coverOf Gl).chi q x) := by
  classical
  intro q hq hne
  obtain ⟨hnb, hbase, hact, hhat⟩ := hdeep q hq hne
  obtain ⟨hqc, hqT⟩ := Finset.mem_filter.1 hq
  have hqT' : ∀ x ∈ intBox q, x ∈ T := fun x hx => hqT ⟨x, hH x⟩ hx
  have hqc' : q ∈ (coverOf Gl).cubeIdx :=
    (level_mem_cubeIdx_iff_of_mem_top hG' hbase).1 hqc
  have hQ : (coverOf Gp).Qset q = (coverOf Gl).Qset q :=
    level_qset_eq_of_cover hG' hhat
  refine ⟨Finset.mem_filter.2 ⟨hqc', fun x hx => hqT' x hx⟩, ?_, hnb, fun x hx => ?_⟩
  · unfold DecCover.sProd
    rw [← hQ]
    refine Finset.prod_congr rfl fun P hP => hs P (hhat P (Or.inl ((DecCover.mem_Qset _).1 hP).1) ?_)
    exact ((DecCover.mem_Qset _).1 hP).2
  · exact level_chi_eq_of_cover hG' (hact x hx) q


/-- **The inner-cube hypothesis `hin` at the local generator.**  Let `𝔹_{k+1}` be a level set and
`𝔹_{k+1}(Y) = localB (k + 1) … Y`, with operator generating sets `H` (with `Ω₁(H)` the whole torus)
and `H'`.  Suppose every cube of the cover of `𝔹_{k+1}` inside `T` (read on `H`) with a non-zero
factor has: the same layers of `H`, `H'` on the stencil of its interaction cube; its base, the bases
of the cubes whose bump does not vanish on its interaction cube and the bases of the cubes meeting
its thickened cube `□̂_z` in the top layer `Ω_{k+1}(𝔹_{k+1}(Y))` (their `𝒞_{k+1}`-cubes lie in `Y`).
If the two parameter vectors agree at the cubes with base in `Ω_{k+1}(𝔹_{k+1}(Y))`, then the cube is
a cube of the cover of `𝔹_{k+1}(Y)` inside `T` (read on `H'`), with the same factor, the same layers
on the stencil and the same partition function. -/
theorem level_localB_inner_cross (hG' : IsLevel Gp (k + 1)) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH}
    {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH'} (hH : ∀ x, x ∈ H.Ω 1)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : Dec2.DecParams (coverOf Gp)}
    {s' : Dec2.DecParams (coverOf (localB (k + 1) hk Y hsep))}
    (hdeep : ∀ q ∈ Dec2.innerCentres (coverOf Gp) H T,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 →
        (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
          (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
            ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
        q.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) ∧
        (∀ x ∈ intBox q, ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1),
          (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx (localB (k + 1) hk Y hsep)) → cubeBump m₁ q'.1 q'.2 x ≠ 0 →
          q'.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1)) ∧
        (∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1), (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx (localB (k + 1) hk Y hsep)) →
          (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
          InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
            q'.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1)))
    (hs : ∀ P : ℕ × CTorus d L N₁ m₁ (k + 1), P.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) →
      Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = Dec2.extS (coverOf Gp) s P) :
    ∀ q ∈ Dec2.innerCentres (coverOf Gp) H T,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 →
        q ∈ Dec2.innerCentres (coverOf (localB (k + 1) hk Y hsep)) H' T ∧
        (coverOf (localB (k + 1) hk Y hsep)).sProd
            (Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s') q =
          (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ∧
        (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
          (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
            ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
        (∀ x ∈ intBox q, (coverOf Gp).chi q x = (coverOf (localB (k + 1) hk Y hsep)).chi q x) := level_inner_cross hG' hH hdeep hs

/-- **The interaction cube of a top cube of `𝔹_{k+1}(Y)` lies in `Ω_k(𝔹_{k+1}(Y))`** (`k ≥ 1`): its
sites are within sup-distance `3 M₁ L^{k+1}` of the base, and `𝔹_{k+1}(Y)` is sup-separated
(`localB_supSep`, the `5 L` thickening of P3 (4.5)).

The core of `localB_intBox_top_subset`, for an arbitrary generating set `Gl` in place of `𝔹_{k+1}(Y)`. -/
theorem top_intBox_subset (hSS : SupSep Gl m₁) (hk1 : 1 ≤ k)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ (coverOf Gl).cubeIdx)
    (hq2 : q.2 ∈ Gl.Ω (k + 1)) {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∈ intBox q) : x ∈ Gl.Ω k := by
  obtain ⟨⟨hq1, hqK⟩, hql, -⟩ := (mem_cubeIdx _).1 hq
  have hqk : q.1 = k + 1 := (mem_layer_iff_of_mem_top hq2 hq1 hqK).1 hql
  have hB : (0 : ℝ) ≤ 5 / 2 * (L : ℝ) ^ (q.1 + m₁) := by positivity
  have hd := supDist_le_of_inBox hB ((mem_intBox).1 hx)
  have hd' : (supDist q.2 x : ℝ) ≤ 4 * (L : ℝ) ^ (k + 1 + m₁) := by
    rw [LargeField.supDist_comm]
    have e : (L : ℝ) ^ (q.1 + m₁) = (L : ℝ) ^ (k + 1 + m₁) := by rw [hqk]
    have : (0 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := by positivity
    linarith
  have := mem_pred_cube_sup (hSS) (by omega) le_rfl hq2 hd'
  simpa using this


/-- **The interaction cube of a top cube of `𝔹_{k+1}(Y)` lies in `Ω_k(𝔹_{k+1}(Y))`** (`k ≥ 1`): its
sites are within sup-distance `3 M₁ L^{k+1}` of the base, and `𝔹_{k+1}(Y)` is sup-separated
(`localB_supSep`, the `5 L` thickening of P3 (4.5)). -/
theorem localB_intBox_top_subset (hk1 : 1 ≤ k) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx)
    (hq2 : q.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1)) {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∈ intBox q) : x ∈ (localB (k + 1) hk Y hsep).Ω k := top_intBox_subset (localB_supSep hk Y hsep) hk1 hq hq2 hx

/-- **The active cubes of the local cover.**  Let `k ≥ 1`, let `Ω_k(𝔹_{k+1}(Y)) ⊆ Ω₁(H')`, let the
parameters `s'` of `𝔹_{k+1}(Y)` vanish at the cubes whose base is not in the top layer
`Ω_{k+1}(𝔹_{k+1}(Y))` and agree with `s` at the cubes whose base is, and let the cubes meeting the
thickened cube of an active cube of the local cover have their bases in the top layer.  Then every
cube of the local cover with a non-zero factor is a cube of the cover of `𝔹_{k+1}` with the same
factor, and its interaction cube lies in `Ω₁(H')`.

The core of `level_localB_active_cross`, for an arbitrary generating set `Gl` in place of `𝔹_{k+1}(Y)`. -/
theorem level_active_cross (hSS : SupSep Gl m₁) (hG' : IsLevel Gp (k + 1)) (hk1 : 1 ≤ k)
    {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH'}
    (hH' : ∀ x ∈ Gl.Ω k, x ∈ H'.Ω 1)
    {s : Dec2.DecParams (coverOf Gp)}
    {s' : Dec2.DecParams (coverOf Gl)}
    (hs'0 : ∀ P ∈ (coverOf Gl).cubeIdx,
      P.2 ∉ Gl.Ω (k + 1) →
        Dec2.extS (coverOf Gl) s' P = 0)
    (hhat : ∀ q ∈ (coverOf Gl).cubeIdx,
      (coverOf Gl).sProd
          (Dec2.extS (coverOf Gl) s') q ≠ 0 →
        ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1), (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx Gl) →
          (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
          InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
            q'.2 ∈ Gl.Ω (k + 1))
    (hs : ∀ P : ℕ × CTorus d L N₁ m₁ (k + 1), P.2 ∈ Gl.Ω (k + 1) →
      Dec2.extS (coverOf Gl) s' P = Dec2.extS (coverOf Gp) s P)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ (coverOf Gl).cubeIdx)
    (hne : (coverOf Gl).sProd
      (Dec2.extS (coverOf Gl) s') q ≠ 0) :
    q ∈ (coverOf Gp).cubeIdx ∧
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q =
        (coverOf Gl).sProd
          (Dec2.extS (coverOf Gl) s') q ∧
      ∀ x ∈ intBox q, x ∈ H'.Ω 1 := by
  classical
  have hq0 : Dec2.extS (coverOf Gl) s' q ≠ 0 := fun h =>
    hne (Finset.prod_eq_zero (self_mem_Qset hq) h)
  have hdeep : q.2 ∈ Gl.Ω (k + 1) := by
    by_contra h
    exact hq0 (hs'0 q hq h)
  have hhq := hhat q hq hne
  have hqc : q ∈ (coverOf Gp).cubeIdx :=
    (level_mem_cubeIdx_iff_of_mem_top hG' hdeep).2 hq
  have hQ : (coverOf Gp).Qset q = (coverOf Gl).Qset q :=
    level_qset_eq_of_cover hG' hhq
  refine ⟨hqc, ?_, fun x hx => hH' x (top_intBox_subset hSS hk1 hq hdeep hx)⟩
  unfold DecCover.sProd
  rw [hQ]
  exact Finset.prod_congr rfl fun P hP =>
    (hs P (hhq P (Or.inr ((DecCover.mem_Qset _).1 hP).1) ((DecCover.mem_Qset _).1 hP).2)).symm


/-- **The active cubes of the local cover.**  Let `k ≥ 1`, let `Ω_k(𝔹_{k+1}(Y)) ⊆ Ω₁(H')`, let the
parameters `s'` of `𝔹_{k+1}(Y)` vanish at the cubes whose base is not in the top layer
`Ω_{k+1}(𝔹_{k+1}(Y))` and agree with `s` at the cubes whose base is, and let the cubes meeting the
thickened cube of an active cube of the local cover have their bases in the top layer.  Then every
cube of the local cover with a non-zero factor is a cube of the cover of `𝔹_{k+1}` with the same
factor, and its interaction cube lies in `Ω₁(H')`. -/
theorem level_localB_active_cross (hG' : IsLevel Gp (k + 1)) (hk1 : 1 ≤ k) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH'}
    (hH' : ∀ x ∈ (localB (k + 1) hk Y hsep).Ω k, x ∈ H'.Ω 1)
    {s : Dec2.DecParams (coverOf Gp)}
    {s' : Dec2.DecParams (coverOf (localB (k + 1) hk Y hsep))}
    (hs'0 : ∀ P ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      P.2 ∉ (localB (k + 1) hk Y hsep).Ω (k + 1) →
        Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = 0)
    (hhat : ∀ q ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      (coverOf (localB (k + 1) hk Y hsep)).sProd
          (Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s') q ≠ 0 →
        ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1), (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx (localB (k + 1) hk Y hsep)) →
          (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
          InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
            q'.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1))
    (hs : ∀ P : ℕ × CTorus d L N₁ m₁ (k + 1), P.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) →
      Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = Dec2.extS (coverOf Gp) s P)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx)
    (hne : (coverOf (localB (k + 1) hk Y hsep)).sProd
      (Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s') q ≠ 0) :
    q ∈ (coverOf Gp).cubeIdx ∧
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q =
        (coverOf (localB (k + 1) hk Y hsep)).sProd
          (Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s') q ∧
      ∀ x ∈ intBox q, x ∈ H'.Ω 1 := level_active_cross (localB_supSep hk Y hsep) hG' hk1 hH' hs'0 hhat hs hq hne

/-- **The hypothesis `hin'` at the local generator** (under the hypotheses of
`level_localB_active_cross`).

The core of `level_localB_inner_cross'`, for an arbitrary generating set `Gl` in place of `𝔹_{k+1}(Y)`. -/
theorem level_inner_cross' (hSS : SupSep Gl m₁) (hG' : IsLevel Gp (k + 1)) (hk1 : 1 ≤ k)
    {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH}
    {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH'}
    (hH' : ∀ x ∈ Gl.Ω k, x ∈ H'.Ω 1)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : Dec2.DecParams (coverOf Gp)}
    {s' : Dec2.DecParams (coverOf Gl)}
    (hs'0 : ∀ P ∈ (coverOf Gl).cubeIdx,
      P.2 ∉ Gl.Ω (k + 1) →
        Dec2.extS (coverOf Gl) s' P = 0)
    (hhat : ∀ q ∈ (coverOf Gl).cubeIdx,
      (coverOf Gl).sProd
          (Dec2.extS (coverOf Gl) s') q ≠ 0 →
        ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1), (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx Gl) →
          (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
          InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
            q'.2 ∈ Gl.Ω (k + 1))
    (hs : ∀ P : ℕ × CTorus d L N₁ m₁ (k + 1), P.2 ∈ Gl.Ω (k + 1) →
      Dec2.extS (coverOf Gl) s' P = Dec2.extS (coverOf Gp) s P) :
    ∀ q ∈ Dec2.innerCentres (coverOf Gl) H' T,
      (coverOf Gl).sProd
          (Dec2.extS (coverOf Gl) s') q ≠ 0 →
        q ∈ Dec2.innerCentres (coverOf Gp) H T ∧
          (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 := by
  classical
  intro q hq hne
  obtain ⟨hqc', hqT⟩ := Finset.mem_filter.1 hq
  obtain ⟨hqc, heq, hbox⟩ :=
    level_active_cross hSS hG' hk1 hH' hs'0 hhat hs hqc' hne
  refine ⟨Finset.mem_filter.2 ⟨hqc, fun x hx => hqT ⟨x, hbox x hx⟩ hx⟩, ?_⟩
  rw [heq]; exact hne


/-- **The hypothesis `hin'` at the local generator** (under the hypotheses of
`level_localB_active_cross`). -/
theorem level_localB_inner_cross' (hG' : IsLevel Gp (k + 1)) (hk1 : 1 ≤ k) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH}
    {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH'}
    (hH' : ∀ x ∈ (localB (k + 1) hk Y hsep).Ω k, x ∈ H'.Ω 1)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : Dec2.DecParams (coverOf Gp)}
    {s' : Dec2.DecParams (coverOf (localB (k + 1) hk Y hsep))}
    (hs'0 : ∀ P ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      P.2 ∉ (localB (k + 1) hk Y hsep).Ω (k + 1) →
        Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = 0)
    (hhat : ∀ q ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      (coverOf (localB (k + 1) hk Y hsep)).sProd
          (Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s') q ≠ 0 →
        ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1), (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx (localB (k + 1) hk Y hsep)) →
          (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
          InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
            q'.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1))
    (hs : ∀ P : ℕ × CTorus d L N₁ m₁ (k + 1), P.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) →
      Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = Dec2.extS (coverOf Gp) s P) :
    ∀ q ∈ Dec2.innerCentres (coverOf (localB (k + 1) hk Y hsep)) H' T,
      (coverOf (localB (k + 1) hk Y hsep)).sProd
          (Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s') q ≠ 0 →
        q ∈ Dec2.innerCentres (coverOf Gp) H T ∧
          (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 := level_inner_cross' (localB_supSep hk Y hsep) hG' hk1 hH' hs'0 hhat hs

/-- **The dichotomy of the local pair** from that of the ambient pair (under the hypotheses of
`level_localB_active_cross`; `Ω₁(H)` the whole torus).

The core of `level_localB_dich_cross`, for an arbitrary generating set `Gl` in place of `𝔹_{k+1}(Y)`. -/
theorem level_dich_cross (hSS : SupSep Gl m₁) (hG' : IsLevel Gp (k + 1)) (hk1 : 1 ≤ k)
    {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH}
    {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH'} (hH : ∀ x, x ∈ H.Ω 1)
    (hH' : ∀ x ∈ Gl.Ω k, x ∈ H'.Ω 1)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : Dec2.DecParams (coverOf Gp)}
    {s' : Dec2.DecParams (coverOf Gl)}
    (hs'0 : ∀ P ∈ (coverOf Gl).cubeIdx,
      P.2 ∉ Gl.Ω (k + 1) →
        Dec2.extS (coverOf Gl) s' P = 0)
    (hhat : ∀ q ∈ (coverOf Gl).cubeIdx,
      (coverOf Gl).sProd
          (Dec2.extS (coverOf Gl) s') q ≠ 0 →
        ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1), (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx Gl) →
          (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
          InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
            q'.2 ∈ Gl.Ω (k + 1))
    (hs : ∀ P : ℕ × CTorus d L N₁ m₁ (k + 1), P.2 ∈ Gl.Ω (k + 1) →
      Dec2.extS (coverOf Gl) s' P = Dec2.extS (coverOf Gp) s P)
    (hdich : ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 →
      SubI H (intBox q) T ∨ DisjI H (intBox q) T) :
    ∀ q ∈ (coverOf Gl).cubeIdx,
      (coverOf Gl).sProd
          (Dec2.extS (coverOf Gl) s') q ≠ 0 →
        SubI H' (intBox q) T ∨ DisjI H' (intBox q) T := by
  intro q hq hne
  obtain ⟨hqc, heq, -⟩ := level_active_cross hSS hG' hk1 hH' hs'0 hhat hs hq hne
  rcases hdich q hqc (by rw [heq]; exact hne) with h | h
  · exact Or.inl fun x hx => h ⟨x, hH x⟩ hx
  · exact Or.inr fun x hx => h ⟨x, hH x⟩ hx


/-- **The dichotomy of the local pair** from that of the ambient pair (under the hypotheses of
`level_localB_active_cross`; `Ω₁(H)` the whole torus). -/
theorem level_localB_dich_cross (hG' : IsLevel Gp (k + 1)) (hk1 : 1 ≤ k) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH}
    {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH'} (hH : ∀ x, x ∈ H.Ω 1)
    (hH' : ∀ x ∈ (localB (k + 1) hk Y hsep).Ω k, x ∈ H'.Ω 1)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : Dec2.DecParams (coverOf Gp)}
    {s' : Dec2.DecParams (coverOf (localB (k + 1) hk Y hsep))}
    (hs'0 : ∀ P ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      P.2 ∉ (localB (k + 1) hk Y hsep).Ω (k + 1) →
        Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = 0)
    (hhat : ∀ q ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      (coverOf (localB (k + 1) hk Y hsep)).sProd
          (Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s') q ≠ 0 →
        ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1), (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx (localB (k + 1) hk Y hsep)) →
          (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
          InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
            q'.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1))
    (hs : ∀ P : ℕ × CTorus d L N₁ m₁ (k + 1), P.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) →
      Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = Dec2.extS (coverOf Gp) s P)
    (hdich : ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 →
      SubI H (intBox q) T ∨ DisjI H (intBox q) T) :
    ∀ q ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      (coverOf (localB (k + 1) hk Y hsep)).sProd
          (Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s') q ≠ 0 →
        SubI H' (intBox q) T ∨ DisjI H' (intBox q) T := level_dich_cross (localB_supSep hk Y hsep) hG' hk1 hH hH' hs'0 hhat hs hdich

/-- **The row hypothesis of the local pair** from that of the ambient pair (under the hypotheses of
`level_localB_active_cross`).

The core of `level_localB_row_cross`, for an arbitrary generating set `Gl` in place of `𝔹_{k+1}(Y)`. -/
theorem level_row_cross (hSS : SupSep Gl m₁) (hG' : IsLevel Gp (k + 1)) (hk1 : 1 ≤ k)
    {Yc T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : Dec2.DecParams (coverOf Gp)}
    {s' : Dec2.DecParams (coverOf Gl)}
    (hs'0 : ∀ P ∈ (coverOf Gl).cubeIdx,
      P.2 ∉ Gl.Ω (k + 1) →
        Dec2.extS (coverOf Gl) s' P = 0)
    (hhat : ∀ q ∈ (coverOf Gl).cubeIdx,
      (coverOf Gl).sProd
          (Dec2.extS (coverOf Gl) s') q ≠ 0 →
        ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1), (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx Gl) →
          (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
          InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
            q'.2 ∈ Gl.Ω (k + 1))
    (hs : ∀ P : ℕ × CTorus d L N₁ m₁ (k + 1), P.2 ∈ Gl.Ω (k + 1) →
      Dec2.extS (coverOf Gl) s' P = Dec2.extS (coverOf Gp) s P)
    (hrow : ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 →
      ∀ x ∈ Yc, x ∈ intBox q → x ∈ T) :
    ∀ q ∈ (coverOf Gl).cubeIdx,
      (coverOf Gl).sProd
          (Dec2.extS (coverOf Gl) s') q ≠ 0 →
        ∀ x ∈ Yc, x ∈ intBox q → x ∈ T := by
  intro q hq hne
  obtain ⟨hqc, heq, -⟩ := level_active_cross hSS (H' := Gl) hG' hk1
    (fun x hx => Gl.Ω_antitone le_rfl hk1 (by omega) hx) hs'0 hhat hs hq hne
  exact hrow q hqc (by rw [heq]; exact hne)

/-- **The row hypothesis of the local pair** from that of the ambient pair (under the hypotheses of
`level_localB_active_cross`). -/
theorem level_localB_row_cross (hG' : IsLevel Gp (k + 1)) (hk1 : 1 ≤ k) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    {Yc T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : Dec2.DecParams (coverOf Gp)}
    {s' : Dec2.DecParams (coverOf (localB (k + 1) hk Y hsep))}
    (hs'0 : ∀ P ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      P.2 ∉ (localB (k + 1) hk Y hsep).Ω (k + 1) →
        Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = 0)
    (hhat : ∀ q ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      (coverOf (localB (k + 1) hk Y hsep)).sProd
          (Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s') q ≠ 0 →
        ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1), (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx (localB (k + 1) hk Y hsep)) →
          (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
          InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
            q'.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1))
    (hs : ∀ P : ℕ × CTorus d L N₁ m₁ (k + 1), P.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) →
      Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = Dec2.extS (coverOf Gp) s P)
    (hrow : ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 →
      ∀ x ∈ Yc, x ∈ intBox q → x ∈ T) :
    ∀ q ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      (coverOf (localB (k + 1) hk Y hsep)).sProd
          (Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s') q ≠ 0 →
        ∀ x ∈ Yc, x ∈ intBox q → x ∈ T := level_row_cross (localB_supSep hk Y hsep) hG' hk1 hs'0 hhat hs hrow

/-- **The thickened cube of an active local cube lies in the top layer.**  Let `k ≥ 1`,
`m₁ ≥ 2`, `4 L² ≤ M₁ = L^{m₁}`, and let the parameters `s'` of `𝔹_{k+1}(Y)` vanish at the cubes
of its cover whose base is not in the top layer.  If the factor `s'_z` of a cube `z` of the cover
of `𝔹_{k+1}(Y)` does not vanish, every site of `□̂_z` lies in `Ω_{k+1}(𝔹_{k+1}(Y))`: the base of `z`
is in the top layer (`z ∈ 𝒬(z)`), so `□̂_z` lies in `Ω_k` (sup-separation, `hatRad ≤ 4 M₁ L^{k+1}`
up to half a cube), and a site of `□̂_z` in the layer `k` would put its own cube of layer `k`, whose
parameter vanishes, into `𝒬(z)`.

The core of `localB_hatBox_top_of_active`, for an arbitrary generating set `Gl` in place of `𝔹_{k+1}(Y)`. -/
theorem hatBox_top_of_active (hSS : SupSep Gl m₁) (hA : CubeAligned Gl m₁) (hk1 : 1 ≤ k)
    (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {s' : Dec2.DecParams (coverOf Gl)}
    (hs'0 : ∀ P ∈ (coverOf Gl).cubeIdx,
      P.2 ∉ Gl.Ω (k + 1) →
        Dec2.extS (coverOf Gl) s' P = 0)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ (coverOf Gl).cubeIdx)
    (hne : (coverOf Gl).sProd
      (Dec2.extS (coverOf Gl) s') q ≠ 0)
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) :
    y ∈ Gl.Ω (k + 1) := by
  classical
  have hq0 : Dec2.extS (coverOf Gl) s' q ≠ 0 := fun h =>
    hne (Finset.prod_eq_zero (self_mem_Qset hq) h)
  have hdeep : q.2 ∈ Gl.Ω (k + 1) := by
    by_contra h
    exact hq0 (hs'0 q hq h)
  obtain ⟨⟨hq1, hqK⟩, hql, -⟩ := (mem_cubeIdx _).1 hq
  have hqk : q.1 = k + 1 := (mem_layer_iff_of_mem_top hdeep hq1 hqK).1 hql
  -- the site lies in `Ω_k`
  have hR : (0 : ℝ) ≤ hatRad L m₁ q.1 := by unfold hatRad; positivity
  have hd := supDist_le_of_inBox hR hy
  have hMr : (4 : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ m₁ := by exact_mod_cast hM
  have hd' : (supDist q.2 y : ℝ) ≤ 4 * (L : ℝ) ^ (k + 1 + m₁) := by
    rw [LargeField.supDist_comm]
    have e1 : (L : ℝ) ^ (q.1 + m₁) = (L : ℝ) ^ (k + 1) * (L : ℝ) ^ m₁ := by rw [hqk, pow_add]
    have e2 : (L : ℝ) ^ (k + 1 + m₁) = (L : ℝ) ^ (k + 1) * (L : ℝ) ^ m₁ := by rw [pow_add]
    have e3 : (L : ℝ) ^ q.1 = (L : ℝ) ^ (k + 1) := by rw [hqk]
    unfold hatRad at hd
    rw [e1, e3] at hd
    rw [e2]
    have hp : (0 : ℝ) ≤ (L : ℝ) ^ (k + 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hMr hp]
  have hyk : y ∈ Gl.Ω k := by
    simpa using mem_pred_cube_sup (hSS) (by omega) le_rfl hdeep hd'
  by_contra hyt
  -- its own cube of layer `k` meets `□̂_z` and has a vanishing parameter
  have hyl : y ∈ Gl.layer k :=
    Gl.mem_layer.2 ⟨hyk, hyt⟩
  have hA := hA
  have hQ : ((k, ownBase (k + m₁) y) : ℕ × CTorus d L N₁ m₁ (k + 1)) ∈
      (coverOf Gl).cubeIdx := own_mem_cubeIdx hA hk1 (by omega) hyl
  have hsc : SameCell (L ^ (k + m₁)) y (ownBase (k + m₁) y) := ownBase_sameCell y
  have hQt : ownBase (k + m₁) y ∉ Gl.Ω (k + 1) := by
    intro h
    have hsc' : SameCell (L ^ (k + 1 + m₁)) y (ownBase (k + m₁) y) :=
      hsc.mono (pow_dvd_pow L (by omega))
    exact hyt ((hA.union (k + 1) (by omega) le_rfl _ _ hsc').2 h)
  have hQq : ((k, ownBase (k + m₁) y) : ℕ × CTorus d L N₁ m₁ (k + 1)) ∈
      (coverOf Gl).Qset q :=
    (DecCover.mem_Qset _).2 ⟨hQ, y, hsc, hy⟩
  exact hne (Finset.prod_eq_zero hQq (hs'0 _ hQ hQt))


/-- **The thickened cube of an active local cube lies in the top layer.**  Let `k ≥ 1`,
`m₁ ≥ 2`, `4 L² ≤ M₁ = L^{m₁}`, and let the parameters `s'` of `𝔹_{k+1}(Y)` vanish at the cubes
of its cover whose base is not in the top layer.  If the factor `s'_z` of a cube `z` of the cover
of `𝔹_{k+1}(Y)` does not vanish, every site of `□̂_z` lies in `Ω_{k+1}(𝔹_{k+1}(Y))`: the base of `z`
is in the top layer (`z ∈ 𝒬(z)`), so `□̂_z` lies in `Ω_k` (sup-separation, `hatRad ≤ 4 M₁ L^{k+1}`
up to half a cube), and a site of `□̂_z` in the layer `k` would put its own cube of layer `k`, whose
parameter vanishes, into `𝒬(z)`. -/
theorem localB_hatBox_top_of_active (hk1 : 1 ≤ k) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁)) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {s' : Dec2.DecParams (coverOf (localB (k + 1) hk Y hsep))}
    (hs'0 : ∀ P ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      P.2 ∉ (localB (k + 1) hk Y hsep).Ω (k + 1) →
        Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = 0)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx)
    (hne : (coverOf (localB (k + 1) hk Y hsep)).sProd
      (Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s') q ≠ 0)
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) :
    y ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) := hatBox_top_of_active (localB_supSep hk Y hsep) (localB_cubeAligned hk Y hsep hm₁) hk1 hM hs'0 hq hne hy

/-- **The hat-box hypothesis of `level_localB_active_cross` holds** for parameters vanishing off the
top layer (`localB_hatBox_top_of_active`, `level_localB_hat_of_box`).

The core of `localB_hat_of_active`, for an arbitrary generating set `Gl` in place of `𝔹_{k+1}(Y)`. -/
theorem hat_of_active (hSS : SupSep Gl m₁) (hA : CubeAligned Gl m₁) (hk1 : 1 ≤ k)
    (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {s' : Dec2.DecParams (coverOf Gl)}
    (hs'0 : ∀ P ∈ (coverOf Gl).cubeIdx,
      P.2 ∉ Gl.Ω (k + 1) →
        Dec2.extS (coverOf Gl) s' P = 0) :
    ∀ q ∈ (coverOf Gl).cubeIdx,
      (coverOf Gl).sProd
          (Dec2.extS (coverOf Gl) s') q ≠ 0 →
        ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1),
          (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx Gl) →
          (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧ InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
            q'.2 ∈ Gl.Ω (k + 1) :=
  fun _ hq hne => level_hat_of_box (Gp := Gp)
    (fun x y h => hA.union (k + 1) (by omega) le_rfl x y h) fun _ hy =>
    hatBox_top_of_active hSS hA hk1 hM hs'0 hq hne hy

/-- **The hat-box hypothesis of `level_localB_active_cross` holds** for parameters vanishing off the
top layer (`localB_hatBox_top_of_active`, `level_localB_hat_of_box`). -/
theorem localB_hat_of_active (hk1 : 1 ≤ k) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁)) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {s' : Dec2.DecParams (coverOf (localB (k + 1) hk Y hsep))}
    (hs'0 : ∀ P ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      P.2 ∉ (localB (k + 1) hk Y hsep).Ω (k + 1) →
        Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = 0) :
    ∀ q ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      (coverOf (localB (k + 1) hk Y hsep)).sProd
          (Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s') q ≠ 0 →
        ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1),
          (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx (localB (k + 1) hk Y hsep)) →
          (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧ InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
            q'.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) := hat_of_active (localB_supSep hk Y hsep) (localB_cubeAligned hk Y hsep hm₁) hk1 hM hs'0
end LevelInner

end Balaban.Localization
