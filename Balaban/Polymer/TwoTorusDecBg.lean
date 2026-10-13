/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGreenRows
public import Balaban.Polymer.TwoTorusData
public import Balaban.Localization.RowsBg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The decoupled background field on two tori

For the whole-lattice generating set `levelGS j` of two step tori `CTorus d L N₁ m₁ K` and
`CTorus d L N₁' m₁ K`, identified on a centred box by `boxMap`, this file compares the decoupled
background systems `IsDecBg` on a component `Y` of the cut and its block set `B = S_Y`, for raw data
that agree under the box map on the read set `RowsDep B`.

* `approxField_levelGS_boxMap`, `residual_levelGS_boxMap`: the approximate field `φ₀` and the
  residual `f₀` at corresponding sites agree when the data agree on `approxDep`, `resDep`.
* `Nexp_transport`: the entrywise map `𝒩` at corresponding sites, under a bijection of the row
  supports of the operators.
* `decBg_rows_transport` (D1): for candidate multipliers corresponding on `B`, the rows of the
  background map `𝒩(δφ(α))` correspond on `B` and the corrections `δφ(α)` correspond on `Y`.  The
  rows of the cut Green operator are the landed `decBg_green_rows_transport`; the image of the block
  set (`hB'`) and the agreement of the cut factors on the inner cubes (`hagree`) are hypotheses.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background Matrix

section Generic

/-- **Picard iterations on two carriers.**  Let `S` and `S'` be maps of `ι → ℂ` and `ι' → ℂ`
whose iterates from `0` stay in the ball of radius `ρ` and converge to `ξ`, `ξ'` at rate `1/2`.
If one step of `S` at a site of `T` and one step of `S'` at its image under `e` agree whenever the
two arguments correspond on `T`, then `ξ` and `ξ'` correspond on `T`. -/
theorem fixed_agree_of_step_transport {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {S : (ι → ℂ) → (ι → ℂ)} {S' : (ι' → ℂ) → (ι' → ℂ)} {T : ι → Prop} (e : ι → ι') {ρ : ℝ}
    {ξ : ι → ℂ} {ξ' : ι' → ℂ}
    (hstep : ∀ (u : ι → ℂ) (v : ι' → ℂ), (∀ i, ‖u i‖ ≤ ρ) → (∀ i, ‖v i‖ ≤ ρ) →
      (∀ i, T i → u i = v (e i)) → ∀ i, T i → S u i = S' v (e i))
    (hit : ∀ n : ℕ, S^[n] 0 ∈ Metric.closedBall (0 : ι → ℂ) ρ ∧
      ‖S^[n] 0 - ξ‖ ≤ (1 / 2 : ℝ) ^ n * ρ)
    (hit' : ∀ n : ℕ, S'^[n] 0 ∈ Metric.closedBall (0 : ι' → ℂ) ρ ∧
      ‖S'^[n] 0 - ξ'‖ ≤ (1 / 2 : ℝ) ^ n * ρ) (hρ : 0 ≤ ρ) :
    ∀ i, T i → ξ i = ξ' (e i) := by
  have hagree : ∀ n : ℕ, ∀ i, T i → (S^[n] 0) i = (S'^[n] 0) (e i) := by
    intro n
    induction n with
    | zero => intro i _; simp
    | succ n ih =>
      intro i hi
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      refine hstep _ _ (fun j => ?_) (fun j => ?_) ih i hi
      · exact (norm_le_pi_norm _ j).trans (mem_closedBall_zero_iff.1 (hit n).1)
      · exact (norm_le_pi_norm _ j).trans (mem_closedBall_zero_iff.1 (hit' n).1)
  intro i hi
  by_contra hne
  have hpos : 0 < ‖ξ i - ξ' (e i)‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (by positivity : 0 < ‖ξ i - ξ' (e i)‖ / (2 * (ρ + 1))) (by norm_num : (1 / 2 : ℝ) < 1)
  have h1 : ‖ξ i - (S^[n] 0) i‖ ≤ (1 / 2 : ℝ) ^ n * ρ := by
    have e1 : ξ i - (S^[n] 0) i = (ξ - S^[n] 0) i := rfl
    rw [e1]
    exact (norm_le_pi_norm _ i).trans (by rw [norm_sub_rev]; exact (hit n).2)
  have h2 : ‖(S'^[n] 0) (e i) - ξ' (e i)‖ ≤ (1 / 2 : ℝ) ^ n * ρ :=
    (norm_le_pi_norm (S'^[n] 0 - ξ') (e i)).trans (hit' n).2
  have h3 : ξ i - ξ' (e i) = (ξ i - (S^[n] 0) i) + ((S'^[n] 0) (e i) - ξ' (e i)) := by
    rw [hagree n i hi]; ring
  have h4 : ‖ξ i - ξ' (e i)‖ ≤ 2 * ((1 / 2 : ℝ) ^ n * ρ) := by
    rw [h3]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := by linarith
  have h5 : (1 / 2 : ℝ) ^ n * (2 * (ρ + 1)) < ‖ξ i - ξ' (e i)‖ :=
    (lt_div_iff₀ (by positivity : 0 < 2 * (ρ + 1))).1 hn
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]

variable {A B : Type*} [Fintype A] [Fintype B]

/-- **A row sum, transported.**  If the row of `H` at `x` vanishes off `S`, the row of `H'` at
`x'` off `S'`, `ι` is a bijection of `S` onto `S'` carrying the entries, and `g'` corresponds to `g`
at the sites of `S` where the row of `H` does not vanish, then the row sums agree. -/
theorem row_sum_transport (S : A → Prop) (S' : B → Prop) [DecidablePred S] [DecidablePred S']
    (ι : A → B) (hinj : ∀ a b, S a → S b → ι a = ι b → a = b) (hmap : ∀ a, S a → S' (ι a))
    (hsurj : ∀ b, S' b → ∃ a, S a ∧ ι a = b) (H : Matrix A A ℂ) (H' : Matrix B B ℂ) {x : A} {x' : B}
    (h0 : ∀ a, ¬ S a → H x a = 0) (h0' : ∀ b, ¬ S' b → H' x' b = 0)
    (hH : ∀ a, S a → H' x' (ι a) = H x a) {g : A → ℂ} {g' : B → ℂ}
    (hg : ∀ a, S a → H x a ≠ 0 → g' (ι a) = g a) :
    ∑ b, H' x' b * g' b = ∑ a, H x a * g a := by
  have h := mulVec_apply_transport S S' ι hinj hmap hsurj H H' g g' (x := x) (x' := x')
    (fun a ha => by rw [h0 a ha, zero_mul]) (fun b hb => by rw [h0' b hb, zero_mul])
    (fun a ha => by
      by_cases h : H x a = 0
      · rw [hH a ha, h, zero_mul, zero_mul]
      · rw [hH a ha, hg a ha h])
  simpa [Matrix.mulVec, dotProduct] using h

end Generic

section NexpTransport

variable {d L N₀ N₀' k N : ℕ} [NeZero N₀] [NeZero N₀'] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀' k ϱ'}

/-- **The entrywise map `𝒩` at a site, transported.**  The value of `𝒩` at `x` only reads the
data at `x` and at the sites where the row of `H` at `x` does not vanish; if these correspond
under a bijection `ι` of the row supports carrying the entries of the rows, the values agree. -/
theorem Nexp_transport (ιU : Bool) {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {φ' : Torus d (N₀' * L ^ k) → Fin N → ℂ} {Fs dφ : G.Ω 1 × Fin N → ℂ}
    {Fs' dφ' : G'.Ω 1 × Fin N → ℂ} {H : Matrix (G.Ω 1) (G.Ω 1) ℂ}
    {H' : Matrix (G'.Ω 1) (G'.Ω 1) ℂ} {x : G.Ω 1} {x' : G'.Ω 1}
    (S : G.Ω 1 → Prop) (S' : G'.Ω 1 → Prop) [DecidablePred S] [DecidablePred S']
    (ι : G.Ω 1 → G'.Ω 1) (hinj : ∀ a b, S a → S b → ι a = ι b → a = b)
    (hmap : ∀ a, S a → S' (ι a)) (hsurj : ∀ b, S' b → ∃ a, S a ∧ ι a = b)
    (h0 : ∀ y, ¬ S y → H x y = 0) (h0' : ∀ y, ¬ S' y → H' x' y = 0)
    (hH : ∀ y, S y → H' x' (ι y) = H x y)
    (hφx : ∀ i, φ' x' i = φ x i) (hFx : ∀ i, Fs' (x', i) = Fs (x, i))
    (hdx : ∀ i, dφ' (x', i) = dφ (x, i))
    (hy : ∀ y, S y → H x y ≠ 0 →
      (∀ i, φ' (ι y) i = φ y i) ∧ (∀ i, dφ' (ι y, i) = dφ (y, i))) :
    Nexp ιU φ' Fs' dφ' H' x' = Nexp ιU φ Fs dφ H x := by
  have hrow := fun (g : G.Ω 1 → ℂ) (g' : G'.Ω 1 → ℂ)
      (hg : ∀ a, S a → H x a ≠ 0 → g' (ι a) = g a) =>
    row_sum_transport S S' ι hinj hmap hsurj H H' h0 h0' hH hg
  unfold Nexp
  have t1 : ∑ i, (φ' x' i + dφ' (x', i)) * Fs' (x', i) = ∑ i, (φ x i + dφ (x, i)) * Fs (x, i) :=
    Finset.sum_congr rfl fun i _ => by rw [hφx i, hdx i, hFx i]
  have t2 : ∑ y, ∑ i, H' x' y * (φ' x' i - φ' y i) * dφ' (y, i) =
      ∑ y, ∑ i, H x y * (φ x i - φ y i) * dφ (y, i) := by
    have e1 : ∀ (G₀ : GeneratingSet d L N₀ k ϱ) (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
        (H₀ : Matrix (G₀.Ω 1) (G₀.Ω 1) ℂ) (x₀ : G₀.Ω 1) (dφ₀ : G₀.Ω 1 × Fin N → ℂ),
        ∑ y, ∑ i, H₀ x₀ y * (φ₀ x₀ i - φ₀ y i) * dφ₀ (y, i) =
          ∑ y, H₀ x₀ y * ∑ i, (φ₀ x₀ i - φ₀ y i) * dφ₀ (y, i) := fun _ _ _ _ _ =>
      Finset.sum_congr rfl fun _ _ => by rw [Finset.mul_sum]; simp only [mul_assoc]
    have e2 : ∑ y, ∑ i, H' x' y * (φ' x' i - φ' y i) * dφ' (y, i) =
        ∑ y, H' x' y * ∑ i, (φ' x' i - φ' y i) * dφ' (y, i) :=
      Finset.sum_congr rfl fun _ _ => by rw [Finset.mul_sum]; simp only [mul_assoc]
    rw [e1, e2]
    refine hrow _ _ fun a ha hne => Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨h1, h2⟩ := hy a ha hne
    rw [hφx i, h1 i, h2 i]
  have t3 : ∑ y, H' x' y * ∑ i, dφ' (y, i) * dφ' (y, i) =
      ∑ y, H x y * ∑ i, dφ (y, i) * dφ (y, i) := by
    refine hrow _ _ fun a ha hne => Finset.sum_congr rfl fun i _ => ?_
    rw [(hy a ha hne).2 i]
  have t4 : ∑ i, dφ' (x', i) * ∑ y, H' x' y * dφ' (y, i) =
      ∑ i, dφ (x, i) * ∑ y, H x y * dφ (y, i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hdx i, hrow (fun y => dφ (y, i)) (fun y => dφ' (y, i)) fun a ha hne => (hy a ha hne).2 i]
  have t5 : ∑ y, H' x' y * (∑ i, φ' y i * φ' y i - 1) =
      ∑ y, H x y * (∑ i, φ y i * φ y i - 1) := by
    refine hrow _ _ fun a ha hne => ?_
    simp only [(hy a ha hne).1]
  rw [t1, t2, t3, t4, t5]

end NexpTransport


section GenericDep

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)

/-- The denominator of the weights is the sum over the active blocks. -/
theorem denom_eq_sum_active (x : Torus d (N₀ * L ^ k)) :
    denom G x = ∑ q ∈ active G x, bump q.1 q.2 x := by
  unfold denom
  symm
  refine Finset.sum_subset (Finset.filter_subset _ _) fun q hq hqa => ?_
  exact bump_eq_zero_of_not_active G hq hqa

/-- The interpolation is the sum over the active blocks. -/
theorem interp_eq_sum_active (Φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) :
    interp G Φ x = ∑ q ∈ active G x, ((bump q.1 q.2 x / denom G x : ℝ) : ℂ) • Φ q.2 := by
  unfold interp
  symm
  refine Finset.sum_subset (Finset.filter_subset _ _) fun q hq hqa => ?_
  have := weight_eq_zero G hq hqa
  unfold weight at this
  rw [this]; simp

theorem mem_resSites_of_mem_blk {x y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.blk (G.layerIndex x) x) : y ∈ resSites G x := by
  unfold resSites
  exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hy))

theorem add_single_mem_resSites (x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    x + Pi.single μ 1 ∈ resSites G x := by
  unfold resSites
  exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.2 ⟨μ, Finset.mem_univ _, rfl⟩)))

theorem sub_single_mem_resSites (x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    x - Pi.single μ 1 ∈ resSites G x := by
  unfold resSites
  exact Finset.mem_insert_of_mem (Finset.mem_union_right _
    (Finset.mem_image.2 ⟨μ, Finset.mem_univ _, rfl⟩))

end GenericDep

section LevelData

variable {d L N₁ N₁' m₁ K N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {j : ℕ}
variable (hj1 : 1 ≤ j) (hj : j ≤ K)

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "ιb" x:max => Subtype.mk (bm (x : CTorus d L N₁ m₁ K))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := K) (ϱ := ϱ) hj1 hj _)

include hj1 in
/-- The local solutions at a site and at its image correspond when the data do. -/
theorem locSol_levelGS_boxMap (a : ℕ → ℝ) (ν : ℝ) {Ψ h : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {Ψ' h' : CTorus d L N₁' m₁ K → Fin N → ℂ} {y : CTorus d L N₁ m₁ K}
    (hΨ : Ψ y = Ψ' (bm y)) (hh : h y = h' (bm y)) :
    locSol GB a ν Ψ' h' (bm y) = locSol GA a ν Ψ h y := by
  unfold locSol blockMass
  rw [ite_eq_left (levelGS_mem_Ω_one hj1 hj _), ite_eq_left (levelGS_mem_Ω_one hj1 hj _),
    layerIndex_levelGS hj1 hj, layerIndex_levelGS hj1 hj, hΨ, hh]

include hj1 in
/-- **The interpolation on two tori.**  For a site of the box of radius `ρ`, the interpolations of
two fields agreeing at the base points of the active blocks correspond.  Margin:
`2 ρ + 5 L^K < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem interp_levelGS_boxMap {ρ : ℕ} (hn : 2 * ρ + 5 * L ^ K < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 5 * L ^ K < (N₁' * L ^ m₁) * L ^ K)
    {Φ : CTorus d L N₁ m₁ K → Fin N → ℂ} {Φ' : CTorus d L N₁' m₁ K → Fin N → ℂ}
    {x : CTorus d L N₁ m₁ K} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hΦ : ∀ q ∈ active GA x, Φ' (bm q.2) = Φ q.2) :
    interp GB Φ' (bm x) = interp GA Φ x := by
  obtain ⟨hK1, hjK⟩ := pow_facts (L := L) hj
  have hact := active_levelGS_image (ϱ := ϱ) (m₁ := m₁) (N₁ := N₁) (N₁' := N₁') hj1 hj hn hn' hx
  have hbase : ∀ q ∈ active GA x, q.1 = j ∧
      InBox d (ρ + 2 * L ^ K) ((N₁ * L ^ m₁) * L ^ K) q.2 := by
    intro q hq
    obtain ⟨hqb, hne⟩ := (mem_active _).1 hq
    have hq1 : q.1 = j := ((mem_blockIdx_levelGS hj q).1 hqb).1
    refine ⟨hq1, ?_⟩
    rw [hq1] at hne
    exact inBox_mono (by omega) (inBox_of_bump_ne_zero j (N₀ := N₁ * L ^ m₁) (k := K) _ _ hx
      (by omega) hne)
  have hinj : Set.InjOn (Prod.map id bm) (active GA x : Set (ℕ × CTorus d L N₁ m₁ K)) := by
    intro q1 hq1 q2 hq2 h
    obtain ⟨e1, b1⟩ := hbase q1 hq1
    obtain ⟨e2, b2⟩ := hbase q2 hq2
    have h2 : bm q1.2 = bm q2.2 := congrArg Prod.snd h
    exact Prod.ext (by rw [e1, e2])
      (boxMap_inj (hm' := (by omega : 2 * (ρ + 2 * L ^ K) + 1 < (N₁' * L ^ m₁) * L ^ K)) b1 b2 h2)
  have hbump : ∀ q ∈ active GA x, bump q.1 (bm q.2) (bm x) = bump q.1 q.2 x := by
    intro q hq
    obtain ⟨e1, b1⟩ := hbase q hq
    rw [e1]
    exact bump_boxMap (N₀ := N₁ * L ^ m₁) (N₀' := N₁' * L ^ m₁) (k := K) j x q.2 hx b1
      (by omega) (by omega) (by omega) (by omega)
  have hden : denom GB (bm x) = denom GA x := by
    rw [denom_eq_sum_active, denom_eq_sum_active, hact, Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun q hq => hbump q hq
  rw [interp_eq_sum_active, interp_eq_sum_active, hden, hact, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun q hq => ?_
  simp only [Prod.map_fst, Prod.map_snd, id]
  rw [hbump q hq, hΦ q hq]

include hj1 in
/-- **The approximate field on two tori.**  For a site `x` of the box of radius `ρ`, if the data
`(Ψ, h)` and `(Ψ', h')` correspond on `approxDep x`, then `φ₀'(bm x) = φ₀(x)`.  Margin:
`2 ρ + 5 L^K < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem approxField_levelGS_boxMap {ρ : ℕ} (a : ℕ → ℝ) (ν : ℝ)
    (hn : 2 * ρ + 5 * L ^ K < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 5 * L ^ K < (N₁' * L ^ m₁) * L ^ K)
    {Ψ h : CTorus d L N₁ m₁ K → Fin N → ℂ} {Ψ' h' : CTorus d L N₁' m₁ K → Fin N → ℂ}
    {x : CTorus d L N₁ m₁ K} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hag : ∀ z ∈ approxDep GA x, Ψ z = Ψ' (bm z) ∧ h z = h' (bm z)) :
    approxField GB a ν Ψ' h' (bm x) = approxField GA a ν Ψ h x := by
  have hloc : ∀ z ∈ approxDep GA x, locSol GB a ν Ψ' h' (bm z) = locSol GA a ν Ψ h z :=
    fun z hz => locSol_levelGS_boxMap hj1 hj a ν (hag z hz).1 (hag z hz).2
  unfold approxField
  rw [ite_eq_left (levelGS_mem_Ω_one hj1 hj _), ite_eq_left (levelGS_mem_Ω_one hj1 hj _),
    layerIndex_levelGS hj1 hj, layerIndex_levelGS hj1 hj]
  split_ifs
  · exact hloc x (mem_approxDep_self x)
  · congr 1
    refine interp_levelGS_boxMap hj1 hj hn hn' hx fun q hq => hloc q.2 ?_
    unfold approxDep
    exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨q, hq, rfl⟩)

include hj1 in
/-- The residual sites of a site of the box of radius `ρ` lie in the box of radius `ρ + L^K`. -/
theorem inBox_of_mem_resSites_levelGS {ρ : ℕ} (hn : 2 * ρ + 3 * L ^ K < (N₁ * L ^ m₁) * L ^ K)
    {x : CTorus d L N₁ m₁ K} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    {y : CTorus d L N₁ m₁ K} (hy : y ∈ resSites GA x) :
    InBox d (ρ + L ^ K) ((N₁ * L ^ m₁) * L ^ K) y := by
  obtain ⟨hK1, hjK⟩ := pow_facts (L := L) hj
  unfold resSites at hy
  rw [layerIndex_levelGS hj1 hj] at hy
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and] at hy
  rcases hy with rfl | (hy | ⟨μ, rfl⟩) | ⟨μ, rfl⟩
  · exact inBox_mono (by omega) hx
  · exact inBox_mono (by omega) (inBox_of_mem_cell (a := L ^ j) (by omega) hx
      (by simpa [GeneratingSet.mem_blk, jBlock_eq_iff_mem_box hj] using hy))
  · exact inBox_mono (by omega) (inBox_add_single (by omega) hx μ)
  · exact inBox_mono (by omega) (inBox_sub_single (by omega) hx μ)

include hj1 in
theorem not_mem_collar_levelGS (y : CTorus d L N₁ m₁ K) : y ∉ collar GA :=
  fun h => ((mem_collar _).1 h).1 (levelGS_mem_Ω_one hj1 hj y)

include hj1 in
/-- **The residual on two tori.**  For a site `x` of the box of radius `ρ`, if the data correspond
on `resDep x`, the residuals of the approximate fields at `x` and at its image agree.  Margin:
`2 ρ + 7 L^K < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem residual_levelGS_boxMap {ρ : ℕ} (a : ℕ → ℝ) (ν : ℝ)
    (hn : 2 * ρ + 7 * L ^ K < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 7 * L ^ K < (N₁' * L ^ m₁) * L ^ K)
    {D : BgData GA N} {D' : BgData GB N} {x : (GA).Ω 1}
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K))
    (hag : ∀ z ∈ resDep GA (x : CTorus d L N₁ m₁ K), D.Ψ z = D'.Ψ (bm z) ∧ D.h z = D'.h (bm z))
    (i : Fin N) :
    residual GB a ν D' (approxField GB a ν D'.Ψ D'.h) (ιb x, i) =
      residual GA a ν D (approxField GA a ν D.Ψ D.h) (x, i) := by
  obtain ⟨hK1, hjK⟩ := pow_facts (L := L) hj
  have hφ : ∀ y ∈ resSites GA (x : CTorus d L N₁ m₁ K),
      approxField GB a ν D'.Ψ D'.h (bm y) = approxField GA a ν D.Ψ D.h y := fun y hy =>
    approxField_levelGS_boxMap hj1 hj (ρ := ρ + L ^ K) a ν (by omega) (by omega)
      (inBox_of_mem_resSites_levelGS hj1 hj (by omega) hx hy)
      fun z hz => hag z (approxDep_subset_resDep hy hz)
  have hxd : (x : CTorus d L N₁ m₁ K) ∈ resDep GA (x : CTorus d L N₁ m₁ K) :=
    approxDep_subset_resDep (mem_resSites_self _) (mem_approxDep_self _)
  have hc := not_mem_collar_levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) hj1 hj
  have hc' := not_mem_collar_levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (ϱ := ϱ) hj1 hj
  -- the block of `x` and of its image
  have hbox : ∀ z ∈ box (cbase (L ^ j) (x : CTorus d L N₁ m₁ K)) (L ^ j),
      InBox d (ρ + L ^ K) ((N₁ * L ^ m₁) * L ^ K) z := fun z hz =>
    inBox_mono (by omega) (inBox_of_mem_cell (a := L ^ j) (by omega) hx hz)
  have hblkS := blk_image (r := ρ + L ^ K) (j := j) (GA) (GB) hj (by omega)
    (x : CTorus d L N₁ m₁ K) hbox
  have hblk : (GB).blk j (bm (x : CTorus d L N₁ m₁ K)) =
      ((GA).blk j (x : CTorus d L N₁ m₁ K)).image bm := by
    apply Finset.coe_injective
    rw [Finset.coe_image]
    exact hblkS.symm
  have hblkbox : ∀ z ∈ (GA).blk j (x : CTorus d L N₁ m₁ K),
      InBox d (ρ + L ^ K) ((N₁ * L ^ m₁) * L ^ K) z := fun z hz => hbox z (by
    simpa [GeneratingSet.mem_blk, jBlock_eq_iff_mem_box hj] using hz)
  have hsum : ∑ y ∈ (GB).blk j (bm (x : CTorus d L N₁ m₁ K)),
      approxField GB a ν D'.Ψ D'.h y i =
      ∑ y ∈ (GA).blk j (x : CTorus d L N₁ m₁ K), approxField GA a ν D.Ψ D.h y i := by
    rw [hblk, Finset.sum_image fun y1 hy1 y2 hy2 h => boxMap_inj
      (hm' := (by omega : 2 * (ρ + L ^ K) + 1 < (N₁' * L ^ m₁) * L ^ K))
      (hblkbox y1 hy1) (hblkbox y2 hy2) h]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [hφ y (mem_resSites_of_mem_blk _ (by rwa [layerIndex_levelGS hj1 hj]))]
  have hp : ∀ μ : Fin d, bm ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) =
      bm (x : CTorus d L N₁ m₁ K) + Pi.single μ 1 := fun μ =>
    boxMap_add_single (ρ := ρ) (by omega) (by omega) hx μ
  have hm : ∀ μ : Fin d, bm ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) =
      bm (x : CTorus d L N₁ m₁ K) - Pi.single μ 1 := fun μ =>
    boxMap_sub_single (ρ := ρ) (by omega) (by omega) hx μ
  have hφp : ∀ μ : Fin d, approxField GB a ν D'.Ψ D'.h (bm (x : CTorus d L N₁ m₁ K) +
      Pi.single μ 1) = approxField GA a ν D.Ψ D.h ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) :=
    fun μ => by rw [← hp μ]; exact hφ _ (add_single_mem_resSites _ _ μ)
  have hφm : ∀ μ : Fin d, approxField GB a ν D'.Ψ D'.h (bm (x : CTorus d L N₁ m₁ K) -
      Pi.single μ 1) = approxField GA a ν D.Ψ D.h ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) :=
    fun μ => by rw [← hm μ]; exact hφ _ (sub_single_mem_resSites _ _ μ)
  have hφx := hφ _ (mem_resSites_self _)
  rw [residual_apply, residual_apply]
  simp only [hc, hc', ↓reduceIte, add_zero, Finset.sum_const_zero]
  show _ = _
  rw [layerIndex_levelGS hj1 hj, layerIndex_levelGS hj1 hj]
  change _ * (D'.Ψ (bm (x : CTorus d L N₁ m₁ K)) i - _ * ∑ y ∈ (GB).blk j
      (bm (x : CTorus d L N₁ m₁ K)), approxField GB a ν D'.Ψ D'.h y i) +
      _ * (D'.h (bm (x : CTorus d L N₁ m₁ K)) i -
        approxField GB a ν D'.Ψ D'.h (bm (x : CTorus d L N₁ m₁ K)) i) +
      ∑ μ : Fin d, (approxField GB a ν D'.Ψ D'.h (bm (x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i +
        approxField GB a ν D'.Ψ D'.h (bm (x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i -
        2 * approxField GB a ν D'.Ψ D'.h (bm (x : CTorus d L N₁ m₁ K)) i) = _
  rw [hsum, hφx]
  simp only [hφp, hφm, ← (hag _ hxd).1, ← (hag _ hxd).2]

end LevelData


section Rows

variable {d L N₁ N₁' m₁ K N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {j : ℕ}
variable (hj1 : 1 ≤ j) (hj : j ≤ K)

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "ιb" x:max => Subtype.mk (bm (x : CTorus d L N₁ m₁ K))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := K) (ϱ := ϱ) hj1 hj _)

include hj1 in
/-- **D1 (BG-2, `decBg_rows_transport`): the rows of the background equation on two tori.**
Let `Y` be a union of nearest-neighbour components of the cut on the first torus, `B = S_Y` its
block set, and `Y' = bm '' Y`, `B' = bm '' B` the corresponding sets on the second torus (the
image of `B` is the block set of `Y'`: hypothesis `hB'`), all in the box of radius `R`.  Let the
cut factors vanish on the parameter cubes outside `𝒞` (resp. `𝒞'`) and agree on the interaction
cubes inside `B` (`hagree`), and let the raw data agree under the box map on the read set
`RowsDep B` (the sites read by the residual at the sites of `B` and by the approximate field at
the sites read by the rows of `H_D(0)` at `B`).  For candidate multipliers `α`, `α'` with
`|α|₂, |α'|₂ ≤ γ₁/8` corresponding on `B`:

* the rows at `x ∈ B` of `𝒩(δφ(α))` (the left side of `DecFixed` in `IsDecBg.fixed`) correspond;
* the corrections `δφ(α) = G_s(α)(f₀ - α φ₀)` (the correction of `IsDecBg.field`) correspond at
  every site of `Y`.

Margin: `4 R + 12 L^(j+m₁) + 7 L^K + 5 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem decBg_rows_transport {cstar BG : ℝ} (hF : FamSpec d L cstar BG) {a : ℕ → ℝ} {ν : ℝ}
    (SA : DGSetting GA a ν) (SB : DGSetting GB a ν) (hconn : HatConn GA) (hconn' : HatConn GB)
    {κ : ℝ} (hκ : 0 ≤ κ) (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s : DecParams GA} {s' : DecParams GB} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ K)} {X₁' Y' : Finset (CTorus d L N₁' m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (GA).Ω 1) Y)
    (hYc : IsNnComp ((Vset X₁' 𝒞').filter fun x => x ∈ (GB).Ω 1) Y')
    (hs0 : ∀ P ∈ parCubes GA X₁, P ∉ 𝒞 → extS GA s P = 0)
    (hs0' : ∀ P ∈ parCubes GB X₁', P ∉ 𝒞' → extS GB s' P = 0)
    (hY' : Y.image bm = Y') (hB' : (SY GA X₁ 𝒞 Y).image bm = SY GB X₁' 𝒞' Y')
    (hagree : ∀ q ∈ innerCentres GA (SY GA X₁ 𝒞 Y),
      sProd GB (extS GB s') (Prod.map id bm q) = sProd GA (extS GA s) q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + m₁) + 7 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + m₁) + 7 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {D : BgData GA N} {D' : BgData GB N}
    (hD : RawBoxAgree {z | RowsDep GA a ν (SY GA X₁ 𝒞 Y) z} (rawOf D) (rawOf D'))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
    (hsm : Small GA α (gamma1 d / 8)) (hsm' : Small GB α' (gamma1 d / 8))
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY GA X₁ 𝒞 Y → α x = α' (ιb x)) :
    (∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY GA X₁ 𝒞 Y →
      Nmap GA (dirichletOperator GA a ν 0) true (approxField GA a ν D.Ψ D.h)
          (residual GA a ν D (approxField GA a ν D.Ψ D.h))
          (dphi GA (decG GA a ν s) 0 (approxField GA a ν D.Ψ D.h)
            (residual GA a ν D (approxField GA a ν D.Ψ D.h)) α) x =
        Nmap GB (dirichletOperator GB a ν 0) true (approxField GB a ν D'.Ψ D'.h)
          (residual GB a ν D' (approxField GB a ν D'.Ψ D'.h))
          (dphi GB (decG GB a ν s') 0 (approxField GB a ν D'.Ψ D'.h)
            (residual GB a ν D' (approxField GB a ν D'.Ψ D'.h)) α') (ιb x)) ∧
    (∀ y : (GA).Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      dphi GA (decG GA a ν s) 0 (approxField GA a ν D.Ψ D.h)
          (residual GA a ν D (approxField GA a ν D.Ψ D.h)) α (y, i) =
        dphi GB (decG GB a ν s') 0 (approxField GB a ν D'.Ψ D'.h)
          (residual GB a ν D' (approxField GB a ν D'.Ψ D'.h)) α' (ιb y, i)) := by
  classical
  have hd0 : 0 < d := by have := SA.hd; omega
  obtain ⟨hK1, hjK⟩ := pow_facts (L := L) hj
  have hBY : SY GA X₁ 𝒞 Y ⊆ Y := SY_subset_levelGS hj1 hj
  have hBR : ∀ x ∈ SY GA X₁ 𝒞 Y, InBox d R ((N₁ * L ^ m₁) * L ^ K) x := fun x hx => hYR x (hBY hx)
  obtain ⟨-, hunit⟩ := hF.2.2 GA SA hκ hM hs N
  obtain ⟨-, hunit'⟩ := hF.2.2 GB SB hκ hM hs' N
  have hA : AdmPot GA (0 + α) := admPot_of_small hd0 (by rw [zero_add]; exact hsm)
  have hA' : AdmPot GB (0 + α') := admPot_of_small hd0 (by rw [zero_add]; exact hsm')
  have hag : ∀ z, RowsDep GA a ν (SY GA X₁ 𝒞 Y) z → D.Ψ z = D'.Ψ (bm z) ∧ D.h z = D'.h (bm z) :=
    fun z hz => hD z hz
  -- the approximate field at the sites of `B` and at the sites read by the rows
  have hφB : ∀ y : (GA).Ω 1, (y : CTorus d L N₁ m₁ K) ∈ SY GA X₁ 𝒞 Y →
      approxField GB a ν D'.Ψ D'.h (bm (y : CTorus d L N₁ m₁ K)) =
        approxField GA a ν D.Ψ D.h (y : CTorus d L N₁ m₁ K) := fun y hy =>
    approxField_levelGS_boxMap hj1 hj (ρ := R) a ν (by omega) (by omega) (hBR _ hy)
      fun z hz => hag z (Or.inl ⟨y, hy, approxDep_subset_resDep (mem_resSites_self _) hz⟩)
  have hφrow : ∀ y : (GA).Ω 1, RowSite GA a ν (0 : (GA).Ω 1 → ℂ) (SY GA X₁ 𝒞 Y) y →
      approxField GB a ν D'.Ψ D'.h (bm (y : CTorus d L N₁ m₁ K)) =
        approxField GA a ν D.Ψ D.h (y : CTorus d L N₁ m₁ K) := fun y hy =>
    approxField_levelGS_boxMap hj1 hj (ρ := R) a ν (by omega) (by omega)
      (hYR _ (rowSite_subset SA hy)) fun z hz => hag z (Or.inr ⟨y, hy, hz⟩)
  -- the residual at the sites of `B`
  have hfB : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY GA X₁ 𝒞 Y → ∀ i : Fin N,
      residual GB a ν D' (approxField GB a ν D'.Ψ D'.h) (ιb x, i) =
        residual GA a ν D (approxField GA a ν D.Ψ D.h) (x, i) := fun x hx i =>
    residual_levelGS_boxMap hj1 hj (ρ := R) a ν (by omega) (by omega) (hBR _ hx)
      (fun z hz => hag z (Or.inl ⟨x, hx, hz⟩)) i
  -- the correction on `Y`
  have hdphi : ∀ y : (GA).Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      dphi GA (decG GA a ν s) 0 (approxField GA a ν D.Ψ D.h)
          (residual GA a ν D (approxField GA a ν D.Ψ D.h)) α (y, i) =
        dphi GB (decG GB a ν s') 0 (approxField GB a ν D'.Ψ D'.h)
          (residual GB a ν D' (approxField GB a ν D'.Ψ D'.h)) α' (ιb y, i) := by
    intro y hy i
    unfold dphi decG
    rw [liftOp_mulVec, liftOp_mulVec]
    refine decBg_green_rows_transport hj1 hj SA SB hY' hB' hBY hYR (by omega) (by omega) hA hA'
      (fun x hx => by simp only [Pi.add_apply, Pi.zero_apply, zero_add]; exact hα x hx)
      (hunit hA) (hunit' hA') (dich_SY_of_comp SA hconn hY hs0)
      (dich_SY_of_comp SB hconn' hYc hs0') (row_SY_levelGS hj1 hj SA hconn hY hs0)
      (row_SY_levelGS hj1 hj SB hconn' hYc hs0') hagree (fun x hx => ?_) y hy
    simp only [Fsrc]
    rw [← hfB x hx i, ← hα x hx]
    congr 2
    exact congrFun (hφB x hx).symm i
  refine ⟨fun x hx => ?_, hdphi⟩
  have hxR := hBR _ hx
  have hres := resSites_levelGS_image (ϱ := ϱ) (m₁ := m₁) (N₁ := N₁) (N₁' := N₁') (ρ := R) hj1 hj
    (by omega) (by omega) hxR
  have hrb : ∀ y ∈ resSites GA (x : CTorus d L N₁ m₁ K),
      InBox d (R + L ^ K) ((N₁ * L ^ m₁) * L ^ K) y := fun y hy =>
    inBox_of_mem_resSites_levelGS hj1 hj (by omega) hxR hy
  rw [Nmap_explicit, Nmap_explicit]
  symm
  refine Nexp_transport true (fun y : (GA).Ω 1 => (y : CTorus d L N₁ m₁ K) ∈
      resSites GA (x : CTorus d L N₁ m₁ K))
    (fun y : (GB).Ω 1 => (y : CTorus d L N₁' m₁ K) ∈ resSites GB (bm (x : CTorus d L N₁ m₁ K)))
    (fun y => ιb y) (fun y1 y2 h1 h2 h => ?_) (fun y hy => ?_) (fun y' hy' => ?_)
    (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_) (fun i => congrFun (hφB x hx) i)
    (fun i => hfB x hx i) (fun i => (hdphi x (hBY hx) i).symm) (fun y hy hne => ?_)
  · exact Subtype.ext (boxMap_inj (hm' := (by omega : 2 * (R + L ^ K) + 1 < (N₁' * L ^ m₁) * L ^ K))
      (hrb _ h1) (hrb _ h2) (congrArg Subtype.val h))
  · show bm (y : CTorus d L N₁ m₁ K) ∈ resSites GB (bm (x : CTorus d L N₁ m₁ K))
    have : bm (y : CTorus d L N₁ m₁ K) ∈ (↑(resSites GB (bm (x : CTorus d L N₁ m₁ K))) :
        Set (CTorus d L N₁' m₁ K)) := by
      rw [hres]; exact Set.mem_image_of_mem _ hy
    exact this
  · have : (y' : CTorus d L N₁' m₁ K) ∈ (↑(resSites GB (bm (x : CTorus d L N₁ m₁ K))) :
        Set (CTorus d L N₁' m₁ K)) := hy'
    rw [hres] at this
    obtain ⟨y0, hy0, hyy⟩ := this
    exact ⟨⟨y0, levelGS_mem_Ω_one hj1 hj y0⟩, hy0, Subtype.ext hyy⟩
  · by_contra hne
    exact hy (mem_resSites_of_entry_ne_zero (x := x) (y := y) hne)
  · by_contra hne
    exact hy (mem_resSites_of_entry_ne_zero (G := GB) (x := ιb x) (y := y) hne)
  · exact dirichletOperator_boxMap (ρ := R + L ^ K) hj1 hj a ν (by omega) (by omega)
      (fun _ _ => rfl) x y (inBox_mono (by omega) hxR) (hrb _ hy)
  · have hrow : RowSite GA a ν (0 : (GA).Ω 1 → ℂ) (SY GA X₁ 𝒞 Y) y := Or.inr ⟨x, hx, hne⟩
    exact ⟨fun i => congrFun (hφrow y hrow) i,
      fun i => (hdphi y (rowSite_subset SA hrow) i).symm⟩

end Rows

end Balaban.Polymer.TwoTorusStep
