/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairCubeOps

/-!
# CrossGs: the decoupled Green's operators of two pairs on one torus

The third input of the replacement of P3 pp. 78-79: the decoupled Green's operator
`G_s(A) = G*_s(A) (1 - 𝒦_s(A))⁻¹` of a pair `(C, H)` (cover, operator generating set) and that of a
second pair `(C', H')` on the same torus agree on a set `T` of sites such that, for both pairs,
every interaction cube with a non-zero factor `s_z` lies inside `T` or avoids it, the cubes inside
`T` with a non-zero factor are the same for both pairs, with the same factors, and near each of them
the layers of `H` and `H'` and the partition functions of `C` and `C'` agree.  This is the block
argument of `Gs_local` (one pair) across the two index spaces `H.Ω 1`, `H'.Ω 1`: `G*_s` and `𝒦_s`
do not couple `T` to its complement, their `T × T` blocks are sums over the common inner cubes of
the entries compared in `LocalPairCubeOps.lean`, and the `T`-rows of `X (1 - 𝒦)⁻¹ f` are
determined by those blocks (`resolvent_rows_transport`).

* `sum_inner_cross`: two sums over the inner cubes with non-zero factors;
* `Dec2.Gstar_apply_cross`, `Dec2.Kcal_apply_cross`: the entries of `G*_s`, `𝒦_s` on `T × T`;
* `Dec2.Gs_rows_cross`: the rows of `G_s(A) f` on `T`;
* `Dec2.Gs_rows_cross_of_subset`: on a set `Y ⊇ T` all of whose sites meet the active cubes only
  inside `T` (both rows vanish on `Y \ T`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix Balaban.Polymer.TwoTorusStep

/-- **Two sums over inner cubes.**  If every index of `I` with a non-zero coefficient is an index of
`I'` with the same coefficient and the same term, and every index of `I'` with a non-zero
coefficient is an index of `I` with a non-zero coefficient, then the two sums of the products
agree. -/
theorem sum_inner_cross {ι : Type*} [DecidableEq ι] {I I' : Finset ι} {c c' F F' : ι → ℂ}
    (hin : ∀ q ∈ I, c q ≠ 0 → q ∈ I' ∧ c' q = c q ∧ F' q = F q)
    (hin' : ∀ q ∈ I', c' q ≠ 0 → q ∈ I ∧ c q ≠ 0) :
    ∑ q ∈ I', c' q * F' q = ∑ q ∈ I, c q * F q := by
  classical
  have e1 : ∑ q ∈ I, c q * F q = ∑ q ∈ I.filter (fun q => c q ≠ 0), c q * F q := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h : c q = 0
    · simp [h]
    · simp [h]
  have e2 : ∑ q ∈ I', c' q * F' q = ∑ q ∈ I'.filter (fun q => c' q ≠ 0), c' q * F' q := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h : c' q = 0
    · simp [h]
    · simp [h]
  have hset : I'.filter (fun q => c' q ≠ 0) = I.filter (fun q => c q ≠ 0) := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hq, hc⟩
      exact hin' q hq hc
    · rintro ⟨hq, hc⟩
      obtain ⟨hq', hcc, -⟩ := hin q hq hc
      exact ⟨hq', by rw [hcc]; exact hc⟩
  rw [e1, e2, hset]
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨hq, hc⟩ := Finset.mem_filter.1 hq
  obtain ⟨-, hcc, hFF⟩ := hin q hq hc
  rw [hcc, hFF]

namespace Dec2

section Pair

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {C C' : DecCover d L N₁ m₁ K}
variable {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {H' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
variable {a : ℕ → ℝ} {ν Kc Cx Kc' Cx' : ℝ}

/-- **CrossGs, the entries of `G*_s`.**  Let every interaction cube with a non-zero factor lie
inside `T` or avoid it, for both pairs; let every cube inside `T` with a non-zero factor for
`(C, H)` be a cube inside `T` for `(C', H')` with the same factor, near which (on the stencil of its
interaction cube) the layers of `H`, `H'` agree and on whose interaction cube the partition
functions of `C`, `C'` agree, and conversely every cube inside `T` with a non-zero factor for
`(C', H')` be one for `(C, H)`; let the admissible potentials agree on `T`.  Then the entries of
`G*_s` at a site of `T` (of both `Ω₁`) and any site of both `Ω₁` agree. -/
theorem Gstar_apply_cross (S : CoverBase C H a ν Kc Cx) (S' : CoverBase C' H' a ν Kc' Cx')
    {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ} (hαA : AdmPot H α) (hαB : AdmPot H' α')
    {T : Finset (CTorus d L N₁ m₁ K)} {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    (hdich' : ∀ q ∈ C'.cubeIdx, C'.sProd s' q ≠ 0 →
      SubI H' (intBox q) T ∨ DisjI H' (intBox q) T)
    (hin : ∀ q ∈ innerCentres C H T, C.sProd s q ≠ 0 →
      q ∈ innerCentres C' H' T ∧ C'.sProd s' q = C.sProd s q ∧
      (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ K,
        (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
          ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
      (∀ x ∈ intBox q, C.chi q x = C'.chi q x))
    (hin' : ∀ q ∈ innerCentres C' H' T, C'.sProd s' q ≠ 0 →
      q ∈ innerCentres C H T ∧ C.sProd s q ≠ 0)
    (hα : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      α ⟨x, hx⟩ = α' ⟨x, hx'⟩)
    {x z : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1) (hz : z ∈ H.Ω 1)
    (hz' : z ∈ H'.Ω 1) (hxT : x ∈ T) :
    Gstar C' H' a ν α' s' ⟨x, hx'⟩ ⟨z, hz'⟩ = Gstar C H a ν α s ⟨x, hx⟩ ⟨z, hz⟩ := by
  classical
  rw [Gstar2_apply_of_mem S hαA hdich (x := ⟨x, hx⟩) hxT,
    Gstar2_apply_of_mem S' hαB hdich' (x := ⟨x, hx'⟩) hxT]
  refine sum_inner_cross (fun q hq hc => ?_) hin'
  obtain ⟨hq', hcc, hnb, hchi⟩ := hin q hq hc
  refine ⟨hq', hcc, ?_⟩
  have hqT : SubI H (intBox q) T := (Finset.mem_filter.1 hq).2
  exact chiD_cubeG_apply_cross S S' hαA hαB (Finset.mem_filter.1 hq).1
    (Finset.mem_filter.1 hq').1 hnb hchi
    (fun w hw hw' hwq => hα w hw hw' (hqT ⟨w, hw⟩ hwq)) hx hx' hz hz'

/-- **CrossGs, the entries of `𝒦_s`**, under the hypotheses of `Gstar_apply_cross`. -/
theorem Kcal_apply_cross (S : CoverBase C H a ν Kc Cx) (S' : CoverBase C' H' a ν Kc' Cx')
    {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ} (hαA : AdmPot H α) (hαB : AdmPot H' α')
    {T : Finset (CTorus d L N₁ m₁ K)} {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    (hdich' : ∀ q ∈ C'.cubeIdx, C'.sProd s' q ≠ 0 →
      SubI H' (intBox q) T ∨ DisjI H' (intBox q) T)
    (hin : ∀ q ∈ innerCentres C H T, C.sProd s q ≠ 0 →
      q ∈ innerCentres C' H' T ∧ C'.sProd s' q = C.sProd s q ∧
      (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ K,
        (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
          ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
      (∀ x ∈ intBox q, C.chi q x = C'.chi q x))
    (hin' : ∀ q ∈ innerCentres C' H' T, C'.sProd s' q ≠ 0 →
      q ∈ innerCentres C H T ∧ C.sProd s q ≠ 0)
    (hα : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      α ⟨x, hx⟩ = α' ⟨x, hx'⟩)
    {x z : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1) (hz : z ∈ H.Ω 1)
    (hz' : z ∈ H'.Ω 1) (hxT : x ∈ T) :
    Kcal C' H' a ν α' s' ⟨x, hx'⟩ ⟨z, hz'⟩ = Kcal C H a ν α s ⟨x, hx⟩ ⟨z, hz⟩ := by
  classical
  rw [Kcal2_apply_of_mem (α := α) S hdich (x := ⟨x, hx⟩) hxT,
    Kcal2_apply_of_mem (α := α') S' hdich' (x := ⟨x, hx'⟩) hxT]
  refine sum_inner_cross (fun q hq hc => ?_) hin'
  obtain ⟨hq', hcc, hnb, hchi⟩ := hin q hq hc
  refine ⟨hq', hcc, ?_⟩
  have hqT : SubI H (intBox q) T := (Finset.mem_filter.1 hq).2
  exact Kz_cubeG_apply_cross S S' hαA hαB (Finset.mem_filter.1 hq).1
    (Finset.mem_filter.1 hq').1 hnb hchi
    (fun w hw hw' hwq => hα w hw hw' (hqT ⟨w, hw⟩ hwq)) hx hx' hz hz'

/-- **CrossGs: the rows of `G_s(A) f` on `T`.**  Under the hypotheses of `Gstar_apply_cross`, if
moreover `T` lies in `Ω₁(H)` exactly where it lies in `Ω₁(H')`, `1 - 𝒦_s` is invertible for both
pairs and the sources agree on `T`, then `(G_s(A) f)(y) = (G'_{s'}(A') f')(y)` at every site `y` of
`T` (of both `Ω₁`). -/
theorem Gs_rows_cross (S : CoverBase C H a ν Kc Cx) (S' : CoverBase C' H' a ν Kc' Cx')
    {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ} (hαA : AdmPot H α) (hαB : AdmPot H' α')
    {T : Finset (CTorus d L N₁ m₁ K)} (hTΩ : ∀ x ∈ T, (x ∈ H.Ω 1 ↔ x ∈ H'.Ω 1))
    {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hU : IsUnit (1 - Kcal C H a ν α s)) (hU' : IsUnit (1 - Kcal C' H' a ν α' s'))
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    (hdich' : ∀ q ∈ C'.cubeIdx, C'.sProd s' q ≠ 0 →
      SubI H' (intBox q) T ∨ DisjI H' (intBox q) T)
    (hin : ∀ q ∈ innerCentres C H T, C.sProd s q ≠ 0 →
      q ∈ innerCentres C' H' T ∧ C'.sProd s' q = C.sProd s q ∧
      (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ K,
        (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
          ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
      (∀ x ∈ intBox q, C.chi q x = C'.chi q x))
    (hin' : ∀ q ∈ innerCentres C' H' T, C'.sProd s' q ≠ 0 →
      q ∈ innerCentres C H T ∧ C.sProd s q ≠ 0)
    (hα : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      α ⟨x, hx⟩ = α' ⟨x, hx'⟩)
    {f : H.Ω 1 → ℂ} {f' : H'.Ω 1 → ℂ}
    (hf : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      f ⟨x, hx⟩ = f' ⟨x, hx'⟩)
    {y : CTorus d L N₁ m₁ K} (hy : y ∈ H.Ω 1) (hy' : y ∈ H'.Ω 1) (hyT : y ∈ T) :
    (Gs C H a ν α s *ᵥ f) ⟨y, hy⟩ = (Gs C' H' a ν α' s' *ᵥ f') ⟨y, hy'⟩ := by
  classical
  obtain ⟨ι, hι⟩ : ∃ ι : H.Ω 1 → H'.Ω 1, ∀ w : H.Ω 1, ι w =
      if h : (w : CTorus d L N₁ m₁ K) ∈ H'.Ω 1 then ⟨w, h⟩ else ⟨y, hy'⟩ := ⟨_, fun _ => rfl⟩
  have hιv : ∀ (w : H.Ω 1) (hw : (w : CTorus d L N₁ m₁ K) ∈ T),
      ι w = ⟨w, (hTΩ w hw).1 w.2⟩ := by
    intro w hw
    rw [hι, dite_eq_left ((hTΩ w hw).1 w.2)]
  have e₁ : ι ⟨y, hy⟩ = ⟨y, hy'⟩ := hιv ⟨y, hy⟩ hyT
  rw [← e₁]
  symm
  unfold Gs
  refine resolvent_rows_transport (fun w : H.Ω 1 => (w : CTorus d L N₁ m₁ K) ∈ T)
    (fun w : H'.Ω 1 => (w : CTorus d L N₁ m₁ K) ∈ T) ι
    (fun w₁ w₂ h₁ h₂ h => ?_) (fun w hw => ?_) (fun w' hw' => ?_) _ _ _ _
    (fun x z hx hz => Gstar2_apply_eq_zero_of_mem S hαA hdich hx hz)
    (fun x z hx hz => Kcal2_apply_eq_zero_of_mem S hdich hx hz)
    (fun x z hx hz => Gstar2_apply_eq_zero_of_mem S' hαB hdich' hx hz)
    (fun x z hx hz => Kcal2_apply_eq_zero_of_mem S' hdich' hx hz)
    (fun x z hx hz => Kcal2_apply_eq_zero_of_not_mem S' hdich' hx hz)
    (fun x z hx hz => ?_) (fun x z hx hz => ?_) hU hU' (fun z hz => ?_) hyT
  · have := congrArg Subtype.val ((hιv w₁ h₁).symm.trans (h.trans (hιv w₂ h₂)))
    exact Subtype.ext this
  · show ((ι w : H'.Ω 1) : CTorus d L N₁ m₁ K) ∈ T
    rw [hιv w hw]; exact hw
  · exact ⟨⟨w', (hTΩ w' hw').2 w'.2⟩, hw', (hιv _ hw').trans rfl⟩
  · rw [hιv x hx, hιv z hz]
    exact Gstar_apply_cross S S' hαA hαB hdich hdich' hin hin' hα x.2 _ z.2 _ hx
  · rw [hιv x hx, hιv z hz]
    exact Kcal_apply_cross S S' hαA hαB hdich hdich' hin hin' hα x.2 _ z.2 _ hx
  · rw [hιv z hz]
    exact (hf z z.2 _ hz).symm

/-- **CrossGs on a set `Y ⊇ T`.**  Under the hypotheses of `Gs_rows_cross`, if moreover every
interaction cube with a non-zero factor meets `Y` only inside `T` (for both pairs), then
`(G_s(A) f)(y) = (G'_{s'}(A') f')(y)` at every site `y` of `Y` (of both `Ω₁`): on `Y \ T` both
rows vanish. -/
theorem Gs_rows_cross_of_subset (S : CoverBase C H a ν Kc Cx)
    (S' : CoverBase C' H' a ν Kc' Cx') {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ} (hαA : AdmPot H α)
    (hαB : AdmPot H' α') {Y T : Finset (CTorus d L N₁ m₁ K)}
    (hTΩ : ∀ x ∈ T, (x ∈ H.Ω 1 ↔ x ∈ H'.Ω 1)) {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hU : IsUnit (1 - Kcal C H a ν α s)) (hU' : IsUnit (1 - Kcal C' H' a ν α' s'))
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    (hdich' : ∀ q ∈ C'.cubeIdx, C'.sProd s' q ≠ 0 →
      SubI H' (intBox q) T ∨ DisjI H' (intBox q) T)
    (hrow : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hrow' : ∀ q ∈ C'.cubeIdx, C'.sProd s' q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hin : ∀ q ∈ innerCentres C H T, C.sProd s q ≠ 0 →
      q ∈ innerCentres C' H' T ∧ C'.sProd s' q = C.sProd s q ∧
      (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ K,
        (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
          ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
      (∀ x ∈ intBox q, C.chi q x = C'.chi q x))
    (hin' : ∀ q ∈ innerCentres C' H' T, C'.sProd s' q ≠ 0 →
      q ∈ innerCentres C H T ∧ C.sProd s q ≠ 0)
    (hα : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      α ⟨x, hx⟩ = α' ⟨x, hx'⟩)
    {f : H.Ω 1 → ℂ} {f' : H'.Ω 1 → ℂ}
    (hf : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      f ⟨x, hx⟩ = f' ⟨x, hx'⟩)
    {y : CTorus d L N₁ m₁ K} (hy : y ∈ H.Ω 1) (hy' : y ∈ H'.Ω 1) (hyY : y ∈ Y) :
    (Gs C H a ν α s *ᵥ f) ⟨y, hy⟩ = (Gs C' H' a ν α' s' *ᵥ f') ⟨y, hy'⟩ := by
  by_cases hyT : y ∈ T
  · exact Gs_rows_cross S S' hαA hαB hTΩ hU hU' hdich hdich' hin hin' hα hf hy hy' hyT
  · rw [Gs2_apply_eq_zero_of_not_mem S hαA hrow f (y := ⟨y, hy⟩) hyY hyT,
      Gs2_apply_eq_zero_of_not_mem S' hαB hrow' f' (y := ⟨y, hy'⟩) hyY hyT]

end Pair

end Dec2

end Balaban.Localization
