/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairReplacement
public import Balaban.Fluctuation.PhysicalReadsFNu

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
        (∀ x ∈ intBox q, ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1), cubeBump m₁ q'.1 q'.2 x ≠ 0 →
          q'.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1)) ∧
        (∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1), (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
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
        (∀ x ∈ intBox q, (coverOf Gp).chi q x = (coverOf (localB (k + 1) hk Y hsep)).chi q x) := by
  classical
  intro q hq hne
  obtain ⟨hnb, hbase, hact, hhat⟩ := hdeep q hq hne
  obtain ⟨hqc, hqT⟩ := Finset.mem_filter.1 hq
  have hqT' : ∀ x ∈ intBox q, x ∈ T := fun x hx => hqT ⟨x, hH x⟩ hx
  have hqc' : q ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx :=
    (level_localB_mem_cubeIdx_iff hG' hk Y hsep ((mem_localB_Ω_top q.2).1 hbase)).1 hqc
  have hQ : (coverOf Gp).Qset q = (coverOf (localB (k + 1) hk Y hsep)).Qset q :=
    level_localB_qset_eq hG' hk Y hsep fun q' hq' => (mem_localB_Ω_top q'.2).1 (hhat q' hq')
  refine ⟨Finset.mem_filter.2 ⟨hqc', fun x hx => hqT' x hx⟩, ?_, hnb, fun x hx => ?_⟩
  · unfold DecCover.sProd
    rw [← hQ]
    refine Finset.prod_congr rfl fun P hP => hs P (hhat P ?_)
    exact ((DecCover.mem_Qset _).1 hP).2
  · exact level_localB_chi_eq hG' hk Y hsep
      (fun q' hq' => (mem_localB_Ω_top q'.2).1 (hact x hx q' hq')) q

/-- **The active cubes of the local cover.**  If the parameters `s'` of `𝔹_{k+1}(Y)` vanish at the
cubes whose base is not in the top layer `Ω_{k+1}(𝔹_{k+1}(Y))` and agree with `s` at the cubes whose
base is, and for each cube of the local cover with base in the top layer its interaction cube lies
in `Ω₁(H')` and the cubes meeting its thickened cube have their bases in the top layer, then every
cube of the local cover with a non-zero factor is a cube of the cover of `𝔹_{k+1}` with the same
factor, and its interaction cube lies in `Ω₁(H')`. -/
theorem level_localB_active_cross (hG' : IsLevel Gp (k + 1)) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH'}
    {s : Dec2.DecParams (coverOf Gp)}
    {s' : Dec2.DecParams (coverOf (localB (k + 1) hk Y hsep))}
    (hs'0 : ∀ P ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      P.2 ∉ (localB (k + 1) hk Y hsep).Ω (k + 1) →
        Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = 0)
    (htop : ∀ q ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      q.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) →
        (∀ x ∈ intBox q, x ∈ H'.Ω 1) ∧
        (∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1), (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
          InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
            q'.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1)))
    (hs : ∀ P : ℕ × CTorus d L N₁ m₁ (k + 1), P.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) →
      Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = Dec2.extS (coverOf Gp) s P)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx)
    (hne : (coverOf (localB (k + 1) hk Y hsep)).sProd
      (Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s') q ≠ 0) :
    q ∈ (coverOf Gp).cubeIdx ∧
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q =
        (coverOf (localB (k + 1) hk Y hsep)).sProd
          (Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s') q ∧
      ∀ x ∈ intBox q, x ∈ H'.Ω 1 := by
  classical
  have hq0 : Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' q ≠ 0 := fun h =>
    hne (Finset.prod_eq_zero (self_mem_Qset hq) h)
  have hdeep : q.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) := by
    by_contra h
    exact hq0 (hs'0 q hq h)
  obtain ⟨hbox, hhat⟩ := htop q hq hdeep
  have hqc : q ∈ (coverOf Gp).cubeIdx :=
    (level_localB_mem_cubeIdx_iff hG' hk Y hsep ((mem_localB_Ω_top q.2).1 hdeep)).2 hq
  have hQ : (coverOf Gp).Qset q = (coverOf (localB (k + 1) hk Y hsep)).Qset q :=
    level_localB_qset_eq hG' hk Y hsep fun q' hq' => (mem_localB_Ω_top q'.2).1 (hhat q' hq')
  refine ⟨hqc, ?_, hbox⟩
  unfold DecCover.sProd
  rw [hQ]
  exact Finset.prod_congr rfl fun P hP => (hs P (hhat P ((DecCover.mem_Qset _).1 hP).2)).symm

/-- **The hypothesis `hin'` at the local generator** (under the hypotheses of
`level_localB_active_cross`). -/
theorem level_localB_inner_cross' (hG' : IsLevel Gp (k + 1)) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH}
    {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH'}
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : Dec2.DecParams (coverOf Gp)}
    {s' : Dec2.DecParams (coverOf (localB (k + 1) hk Y hsep))}
    (hs'0 : ∀ P ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      P.2 ∉ (localB (k + 1) hk Y hsep).Ω (k + 1) →
        Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = 0)
    (htop : ∀ q ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      q.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) →
        (∀ x ∈ intBox q, x ∈ H'.Ω 1) ∧
        (∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1), (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
          InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
            q'.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1)))
    (hs : ∀ P : ℕ × CTorus d L N₁ m₁ (k + 1), P.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) →
      Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = Dec2.extS (coverOf Gp) s P) :
    ∀ q ∈ Dec2.innerCentres (coverOf (localB (k + 1) hk Y hsep)) H' T,
      (coverOf (localB (k + 1) hk Y hsep)).sProd
          (Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s') q ≠ 0 →
        q ∈ Dec2.innerCentres (coverOf Gp) H T ∧
          (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 := by
  classical
  intro q hq hne
  obtain ⟨hqc', hqT⟩ := Finset.mem_filter.1 hq
  obtain ⟨hqc, heq, hbox⟩ := level_localB_active_cross hG' hk Y hsep hs'0 htop hs hqc' hne
  refine ⟨Finset.mem_filter.2 ⟨hqc, fun x hx => hqT ⟨x, hbox x hx⟩ hx⟩, ?_⟩
  rw [heq]; exact hne

/-- **The dichotomy of the local pair** from that of the ambient pair (under the hypotheses of
`level_localB_active_cross`; `Ω₁(H)` the whole torus). -/
theorem level_localB_dich_cross (hG' : IsLevel Gp (k + 1)) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH}
    {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH'} (hH : ∀ x, x ∈ H.Ω 1)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : Dec2.DecParams (coverOf Gp)}
    {s' : Dec2.DecParams (coverOf (localB (k + 1) hk Y hsep))}
    (hs'0 : ∀ P ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      P.2 ∉ (localB (k + 1) hk Y hsep).Ω (k + 1) →
        Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = 0)
    (htop : ∀ q ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      q.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) →
        (∀ x ∈ intBox q, x ∈ H'.Ω 1) ∧
        (∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1), (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
          InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
            q'.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1)))
    (hs : ∀ P : ℕ × CTorus d L N₁ m₁ (k + 1), P.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) →
      Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = Dec2.extS (coverOf Gp) s P)
    (hdich : ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 →
      SubI H (intBox q) T ∨ DisjI H (intBox q) T) :
    ∀ q ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      (coverOf (localB (k + 1) hk Y hsep)).sProd
          (Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s') q ≠ 0 →
        SubI H' (intBox q) T ∨ DisjI H' (intBox q) T := by
  intro q hq hne
  obtain ⟨hqc, heq, -⟩ := level_localB_active_cross hG' hk Y hsep hs'0 htop hs hq hne
  rcases hdich q hqc (by rw [heq]; exact hne) with h | h
  · exact Or.inl fun x hx => h ⟨x, hH x⟩ hx
  · exact Or.inr fun x hx => h ⟨x, hH x⟩ hx

/-- **The row hypothesis of the local pair** from that of the ambient pair (under the hypotheses of
`level_localB_active_cross`). -/
theorem level_localB_row_cross (hG' : IsLevel Gp (k + 1)) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH'}
    {Yc T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : Dec2.DecParams (coverOf Gp)}
    {s' : Dec2.DecParams (coverOf (localB (k + 1) hk Y hsep))}
    (hs'0 : ∀ P ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      P.2 ∉ (localB (k + 1) hk Y hsep).Ω (k + 1) →
        Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = 0)
    (htop : ∀ q ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      q.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) →
        (∀ x ∈ intBox q, x ∈ H'.Ω 1) ∧
        (∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1), (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
          InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
            q'.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1)))
    (hs : ∀ P : ℕ × CTorus d L N₁ m₁ (k + 1), P.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) →
      Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s' P = Dec2.extS (coverOf Gp) s P)
    (hrow : ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 →
      ∀ x ∈ Yc, x ∈ intBox q → x ∈ T) :
    ∀ q ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      (coverOf (localB (k + 1) hk Y hsep)).sProd
          (Dec2.extS (coverOf (localB (k + 1) hk Y hsep)) s') q ≠ 0 →
        ∀ x ∈ Yc, x ∈ intBox q → x ∈ T := by
  intro q hq hne
  obtain ⟨hqc, heq, -⟩ := level_localB_active_cross (H' := H') hG' hk Y hsep hs'0 htop hs hq hne
  exact hrow q hqc (by rw [heq]; exact hne)

end LevelInner

end Balaban.Localization
