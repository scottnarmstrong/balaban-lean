module

public import Balaban.LargeField.Geometry.Components
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Disjoint neighbourhoods; local and global sets near a component (Part I, §I.2.7)

* `nbhd_disjoint_of_comps` (Lemma I.2.13): for distinct components `Y ≠ Y'` of the width `ω`,
  `ω ≤ d(u, u') + 2k` for `u ∈ Y^{∼k}`, `u' ∈ Y'^{∼k}`;
  `nbhd_thick_disjoint` is its flow form (I.4) (width `ω = 2[R̂_{k-1}] + L + 11`, thick
  neighbourhoods `Y^≈`), which uses the hypothesis `λ_{k-1} ≥ 0` (audit P1-02) through
  `floor_run_le_floor_hat` (the relation (I.3) `R_{k-1} ≤ R̂_{k-1}`).
* `local_eq_global_nbhd`, `local_eq_global_compl` (Lemma I.2.14 (a), (b)) and the flow form
  `flow_local_eq_global`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban

variable {d n : ℕ} [NeZero n] {ω : ℕ} {X : Finset (Torus d n)}

/-- **Lemma I.2.13**: `d(Y^{∼k}, Y'^{∼k}) ≥ ω - 2k` for distinct components. -/
theorem nbhd_disjoint_of_comps {Y Y' : Finset (Torus d n)} (hY : Y ∈ comps ω X)
    (hY' : Y' ∈ comps ω X) (hne : Y ≠ Y') (k : ℕ) :
    ∀ u ∈ nbhd k (Y : Set (Torus d n)), ∀ u' ∈ nbhd k (Y' : Set (Torus d n)),
      ω ≤ supDist u u' + 2 * k := by
  intro u hu u' hu'
  obtain ⟨y, hy, hyu⟩ := mem_nbhd.mp hu
  obtain ⟨y', hy', hyu'⟩ := mem_nbhd.mp hu'
  have h := comps_sep hY hY' hne hy hy'
  have h1 := supDist_triangle y u y'
  have h2 := supDist_triangle u u' y'
  rw [supDist_comm y u] at h1
  omega

/-- The relation (I.3) in floor form: if `λ ≥ 0` and `λ ≤ λ̂` then `[R_base λ²] ≤ [R_base λ̂²]`,
that is, `[R_{k-1}] ≤ [R̂_{k-1}]`. (For `λ < 0` this fails; audit P1-02.) -/
theorem floor_run_le_floor_hat {Rbase lam lamHat : ℝ} (hR : 0 ≤ Rbase) (hlam : 0 ≤ lam)
    (hle : lam ≤ lamHat) : ⌊Rbase * lam ^ 2⌋₊ ≤ ⌊Rbase * lamHat ^ 2⌋₊ :=
  Nat.floor_le_floor (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlam hle 2) hR)

/-- **Lemma I.2.13, flow form (I.4)**: for the width `ω = 2 r̂ + L + 11` and `r ≤ r̂` (where
`r = [R_{k-1}]`, `r̂ = [R̂_{k-1}]`), the sets `U = Y^≈ = Y^{∼(r+1)}` of distinct components satisfy
`L + 9 ≤ d(u, u') + 2 m` for `u ∈ U^{∼m}`, `u' ∈ U'^{∼m}`. -/
theorem nbhd_thick_disjoint {Y Y' : Finset (Torus d n)} (hY : Y ∈ comps ω X)
    (hY' : Y' ∈ comps ω X) (hne : Y ≠ Y') {L r rhat : ℕ} (hr : r ≤ rhat)
    (hω : ω = 2 * rhat + L + 11) (m : ℕ) :
    ∀ u ∈ nbhd m (thick r (Y : Set (Torus d n))), ∀ u' ∈ nbhd m (thick r (Y' : Set (Torus d n))),
      L + 9 ≤ supDist u u' + 2 * m := by
  intro u hu u' hu'
  unfold thick at hu hu'
  rw [nbhd_nbhd] at hu hu'
  have := nbhd_disjoint_of_comps hY hY' hne (r + 1 + m) u hu u' hu'
  omega

/-- The consequence (I.4): `U^{∼m} ∩ U'^{∼m} = ∅` as soon as `2 m ≤ L + 8` (e.g. `m = 1`,
`m = 4`, and `m = 6` if `L ≥ 4`). -/
theorem nbhd_thick_disjoint_empty {Y Y' : Finset (Torus d n)} (hY : Y ∈ comps ω X)
    (hY' : Y' ∈ comps ω X) (hne : Y ≠ Y') {L r rhat : ℕ} (hr : r ≤ rhat)
    (hω : ω = 2 * rhat + L + 11) {m : ℕ} (hm : 2 * m ≤ L + 8) :
    Disjoint (nbhd m (thick r (Y : Set (Torus d n)))) (nbhd m (thick r (Y' : Set (Torus d n)))) := by
  rw [Set.disjoint_left]
  intro u hu hu'
  have := nbhd_thick_disjoint hY hY' hne hr hω m u hu u hu'
  rw [supDist_self] at this
  omega

section Local

variable {Y : Finset (Torus d n)}

private theorem mem_of_close {x y : Torus d n} (hY : Y ∈ comps ω X) (hy : y ∈ Y) (hxX : x ∈ X)
    (h : supDist y x < ω) : x ∈ Y :=
  (mem_comp_iff hY hy).mpr ⟨hxX, Linked.single (comp_subset hY hy) hxX h⟩

/-- **Lemma I.2.14 (a)**: for `n ≤ t`, `2 t < ω`:
`X^{∼n} ∩ Y^{∼t} = Y^{∼n} ∩ Y^{∼t}`. -/
theorem local_eq_global_nbhd (hY : Y ∈ comps ω X) {t : ℕ} (ht : 2 * t < ω) {k : ℕ} (hk : k ≤ t) :
    nbhd k (X : Set (Torus d n)) ∩ nbhd t (Y : Set (Torus d n)) =
      nbhd k (Y : Set (Torus d n)) ∩ nbhd t (Y : Set (Torus d n)) := by
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    refine ⟨?_, hx2⟩
    obtain ⟨x', hx'X, hxx'⟩ := mem_nbhd.mp hx1
    obtain ⟨y, hy, hxy⟩ := mem_nbhd.mp hx2
    have h1 := supDist_triangle y x x'
    rw [supDist_comm y x] at h1
    have hx'Y : x' ∈ Y := mem_of_close hY hy (by exact_mod_cast hx'X) (by omega)
    exact mem_nbhd.mpr ⟨x', hx'Y, hxx'⟩
  · rintro ⟨hx1, hx2⟩
    exact ⟨nbhd_mono le_rfl (by exact_mod_cast comp_subset hY) hx1, hx2⟩

/-- **Lemma I.2.14 (b)**: for `2 t < ω`, `ω ≥ 2`:
`(X^c)^{∼k} ∩ Y^{∼t} = (Y^c)^{∼k} ∩ Y^{∼t}`. -/
theorem local_eq_global_compl (hY : Y ∈ comps ω X) {t : ℕ} (ht : 2 * t < ω) (hω : 2 ≤ ω) (k : ℕ) :
    nbhd k (X : Set (Torus d n))ᶜ ∩ nbhd t (Y : Set (Torus d n)) =
      nbhd k (Y : Set (Torus d n))ᶜ ∩ nbhd t (Y : Set (Torus d n)) := by
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    refine ⟨nbhd_mono le_rfl ?_ hx1, hx2⟩
    intro z hz hzY
    exact hz (by exact_mod_cast comp_subset hY (by exact_mod_cast hzY))
  · rintro ⟨hx1, hx2⟩
    refine ⟨?_, hx2⟩
    obtain ⟨y0, hy0, hxy0⟩ := mem_nbhd.mp hx2
    by_cases hxY : x ∈ (Y : Set (Torus d n))
    · -- minimal distance to `Yᶜ`
      obtain ⟨z0, hz0, hxz0⟩ := mem_nbhd.mp hx1
      obtain ⟨y, hyc, hmin⟩ := Set.exists_min_image (Y : Set (Torus d n))ᶜ (supDist x)
        (Set.toFinite _) ⟨z0, hz0⟩
      set δ := supDist x y with hδ
      have hδn : δ ≤ k := (hmin z0 hz0).trans hxz0
      obtain ⟨g, hg0, hgδ, hg⟩ := exists_geodesic x y
      have hδpos : 1 ≤ δ := by
        by_contra h0
        have : δ = 0 := by omega
        have := supDist_eq_zero.mp this
        exact hyc (this ▸ hxY)
      obtain ⟨hgd, -⟩ := hg (δ - 1) (by omega)
      obtain ⟨-, hstep⟩ := hg (δ - 1) (by omega)
      have hz : g (δ - 1) ∈ (Y : Set (Torus d n)) := by
        by_contra hzn
        have := hmin _ hzn
        omega
      have hstep' := hstep (by omega)
      rw [show δ - 1 + 1 = δ by omega, hgδ] at hstep'
      have hyX : y ∉ (X : Set (Torus d n)) := by
        intro hyX
        exact hyc (mem_of_close hY (by exact_mod_cast hz) (by exact_mod_cast hyX) (by omega))
      exact mem_nbhd.mpr ⟨y, hyX, hδn⟩
    · have hxX : x ∉ (X : Set (Torus d n)) := by
        intro hxX
        exact hxY (mem_of_close hY (by exact_mod_cast hy0) (by exact_mod_cast hxX)
          (by rw [supDist_comm]; omega))
      exact mem_nbhd.mpr ⟨x, hxX, by simp [supDist_self]⟩

/-- **Lemma I.2.14, flow form**: with `a = [R_{k₁-1}] + 1 = r + 1`, `U = X^≈ = X^{∼a}`,
`W = (X^c)^{≈2} = (X^c)^{∼2a}`, the local sets `U^Y = Y^{∼a}`, `W^Y = (Y^c)^{∼2a}`; for
`2 (a + m) < ω` (e.g. `r ≤ r̂`, `ω = 2 r̂ + L + 11`, `2 m ≤ L + 8`) on `(U^Y)^{∼m}` the global sets
`U^{∼j}` (`j ≤ m`) and `W` agree with the local ones. -/
theorem flow_local_eq_global (hY : Y ∈ comps ω X) {r m : ℕ} (hω : 2 ≤ ω) (hm : 2 * (r + 1 + m) < ω) :
    (∀ j ≤ m, nbhd j (thick r (X : Set (Torus d n))) ∩ nbhd m (thick r (Y : Set (Torus d n))) =
      nbhd j (thick r (Y : Set (Torus d n))) ∩ nbhd m (thick r (Y : Set (Torus d n)))) ∧
    thick2 r (X : Set (Torus d n))ᶜ ∩ nbhd m (thick r (Y : Set (Torus d n))) =
      thick2 r (Y : Set (Torus d n))ᶜ ∩ nbhd m (thick r (Y : Set (Torus d n))) := by
  constructor
  · intro j hj
    unfold thick
    simp only [nbhd_nbhd]
    exact local_eq_global_nbhd hY hm (by omega)
  · rw [thick2_eq, thick2_eq]
    unfold thick
    simp only [nbhd_nbhd]
    exact local_eq_global_compl hY hm hω _

/-- The flow hypotheses of `flow_local_eq_global`: `r ≤ r̂`, `ω = 2 r̂ + L + 11`, `2 m ≤ L + 8`. -/
theorem flow_local_eq_global' (hY : Y ∈ comps ω X) {L r rhat m : ℕ} (hr : r ≤ rhat)
    (hω : ω = 2 * rhat + L + 11) (hm : 2 * m ≤ L + 8) :
    (∀ j ≤ m, nbhd j (thick r (X : Set (Torus d n))) ∩ nbhd m (thick r (Y : Set (Torus d n))) =
      nbhd j (thick r (Y : Set (Torus d n))) ∩ nbhd m (thick r (Y : Set (Torus d n)))) ∧
    thick2 r (X : Set (Torus d n))ᶜ ∩ nbhd m (thick r (Y : Set (Torus d n))) =
      thick2 r (Y : Set (Torus d n))ᶜ ∩ nbhd m (thick r (Y : Set (Torus d n))) :=
  flow_local_eq_global hY (by omega) (by omega)

end Local

end Balaban.LargeField
