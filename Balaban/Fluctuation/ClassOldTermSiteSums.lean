/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6InfSum
public import Balaban.Fluctuation.InteractionFPart
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Per-site sums of the label bounds of a class member

The general activity constructor takes, for the old energy terms and the old observable terms of a
class member, a bound `ρE` (resp. `ρM`) on the sums over the labels rooted at a site (resp. at a
site and a component) of `Eb(τ) exp(-κ₀ d^cov_j(X))`.

* `sum_polyDom_through_le`: for fixed `j` and a site `x`, the sum of `exp(-κ₀ d^cov_j(X))` over
  the polymers `X ∈ 𝒟_j` containing `x` is at most `K₀` (from the entropy bound (G2)).
* `sum_labels_filter_le`: the sum over a finite set of labels `τ` rooted at `x`, with the polymer
  of `τ` containing `x`, of `w(j_τ) exp(-κ₀ d^cov)` is at most `∑_{j=1}^k w(j) K₀`.
* `classE_siteSum_le`, `classM_siteSum_le`: the two hypotheses of the constructor for the label
  sets of a class, with the factor `k` (constant prefactor) or uniformly in `k`
  (geometrically decaying prefactors).
* `l1_lt_one_of_mem_l1Ball`: the unit `ℓ¹` ball of sources lies in `{ℓ¹ < 1}`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.SmallField Balaban.SmallField.Def6
  Finset

variable {d L N₁ m₁ K k : ℕ} [NeZero L] [NeZero N₁]

open Classical in
/-- **The polymers through a site.**  For `j ≤ k`, `L ^ m₀ ∣ N₁`, `κ₀ ≥ a_ent + 1` and a site `x`,
`∑_{X ∈ 𝒟_j, x ∈ X} exp(-κ₀ d^cov_j(X)) ≤ K₀`. -/
theorem sum_polyDom_through_le {m₀ j : ℕ} (hjk : j ≤ K) (hN : L ^ m₀ ∣ N₁) {κ₀ : ℝ}
    (hκ : aEnt d L + 1 ≤ κ₀) (x : CTorus d L N₁ m₁ K) :
    ∑ X ∈ Finset.univ.filter (fun X : Set (CTorus d L N₁ m₁ K) =>
        IsPolyDom m₀ j X ∧ x ∈ X), Real.exp (-κ₀ * treeLenCovOne m₀ j X) ≤ K0 d L κ₀ := by
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hΩ : IsPiUnion (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ :=
    fun z _ => ⟨cbase (cellSide L m₀ m₁ j) z, aligned_cbase z, mem_box_cbase ha0 z,
      Set.subset_univ _⟩
  have hG2 := G2_X (m₀ := m₀) (j := j) hN hjk hΩ (t0 := cbase (cellSide L m₀ m₁ j) x)
    (aligned_cbase _) (Set.subset_univ _) hκ
  calc _ = ∑ X ∈ Finset.univ.filter (fun X : Set (CTorus d L N₁ m₁ K) =>
          IsPolyDom m₀ j X ∧ x ∈ X), Real.exp (-κ₀ * dcovMod m₀ j Set.univ X) :=
        Finset.sum_congr rfl fun X _ => by rw [dcovMod_of_subset (Set.subset_univ X)]
    _ ≤ _ := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun _ _ _ => (Real.exp_pos _).le)) hG2
        intro X hX
        obtain ⟨hX1, hx⟩ := (Finset.mem_filter.1 hX).2
        have hDj := isDj_of_isPolyDom hX1
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨hDj, fun z hz => absurd (Set.mem_univ z) hz⟩, cell_subset_of_mem hjk hN hDj hx⟩

open Classical in
/-- **Label sums rooted at a site.**  Let `𝒯` be a finite set of labels with `j_τ`, `X_τ`, and
`P τ` the condition that `τ` is rooted at `x`.  If every such label has `1 ≤ j_τ ≤ k`,
`X_τ ∈ 𝒟_{j_τ}` and `x ∈ X_τ`, and `τ` is determined by `(j_τ, X_τ)` among them, then
`∑_{τ} w(j_τ) exp(-κ₀ d^cov_{j_τ}(X_τ)) ≤ ∑_{j=1}^k w(j) K₀`. -/
theorem sum_labels_filter_le {ι : Type*} (𝒯 : Finset ι) (P : ι → Prop) [DecidablePred P] (jj : ι → ℕ)
    (XX : ι → Set (CTorus d L N₁ m₁ K)) {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) {κ₀ : ℝ}
    (hκ : aEnt d L + 1 ≤ κ₀) (x : CTorus d L N₁ m₁ K) (hkK : k ≤ K) (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hmem : ∀ τ ∈ 𝒯, P τ → (1 ≤ jj τ ∧ jj τ ≤ k) ∧ IsPolyDom m₀ (jj τ) (XX τ) ∧ x ∈ XX τ)
    (hinj : ∀ τ ∈ 𝒯, P τ → ∀ τ' ∈ 𝒯, P τ' → jj τ = jj τ' → XX τ = XX τ' → τ = τ') :
    ∑ τ ∈ 𝒯.filter P, w (jj τ) * Real.exp (-κ₀ * treeLenCovOne m₀ (jj τ) (XX τ)) ≤
      ∑ j ∈ Finset.Icc 1 k, w j * K0 d L κ₀ := by
  have hI : Set.InjOn (fun τ => (jj τ, XX τ)) (↑(𝒯.filter P) : Set ι) := by
    intro a ha b hb h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
    exact hinj a ha.1 ha.2 b hb.1 hb.2 (congrArg Prod.fst h) (congrArg Prod.snd h)
  calc _ = ∑ p ∈ (𝒯.filter P).image (fun τ => (jj τ, XX τ)),
          w p.1 * Real.exp (-κ₀ * treeLenCovOne m₀ p.1 p.2) :=
        (Finset.sum_image (f := fun p : ℕ × Set (CTorus d L N₁ m₁ K) =>
          w p.1 * Real.exp (-κ₀ * treeLenCovOne m₀ p.1 p.2)) hI).symm
    _ ≤ ∑ p ∈ ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (Set (CTorus d L N₁ m₁ K)))).filter
          (fun p => IsPolyDom m₀ p.1 p.2 ∧ x ∈ p.2),
          w p.1 * Real.exp (-κ₀ * treeLenCovOne m₀ p.1 p.2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun p _ _ => mul_nonneg (hw _) (Real.exp_pos _).le)
        intro p hp
        obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hp
        obtain ⟨hτ1, hτ2⟩ := Finset.mem_filter.1 hτ
        obtain ⟨hj, hX, hx⟩ := hmem τ hτ1 hτ2
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ,
          and_true]
        exact ⟨hj, hX, hx⟩
    _ = ∑ j ∈ Finset.Icc 1 k, ∑ X ∈ Finset.univ.filter (fun X : Set (CTorus d L N₁ m₁ K) =>
          IsPolyDom m₀ j X ∧ x ∈ X), w j * Real.exp (-κ₀ * treeLenCovOne m₀ j X) := by
        rw [Finset.sum_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_filter]
    _ ≤ _ := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          (sum_polyDom_through_le ((Finset.mem_Icc.1 hj).2.trans hkK) hN hκ x) (hw j)

open Classical in
/-- **The per-site sum of the old energy label bounds** (the hypothesis `hρE` of the constructor,
with `rE τ = y` for `τ = (j, y, X)`).  If `Eb τ ≤ w(j_τ)` then the sum over the labels rooted at
`x` of `Eb τ exp(-κ₀ d^cov_{j}(X))` is at most `∑_{j=1}^k w(j) K₀`. -/
theorem classE_siteSum_le {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) {κ₀ : ℝ} (hκ : aEnt d L + 1 ≤ κ₀)
    (hkK : k ≤ K)
    (𝒯E : Finset (ℕ × CTorus d L N₁ m₁ K × Set (CTorus d L N₁ m₁ K)))
    (h𝒯 : ∀ τ ∈ 𝒯E, (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2)
    (EbE : ℕ × CTorus d L N₁ m₁ K × Set (CTorus d L N₁ m₁ K) → ℝ) (w : ℕ → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hEb : ∀ τ ∈ 𝒯E, EbE τ ≤ w τ.1) (x : CTorus d L N₁ m₁ K) :
    ∑ τ ∈ 𝒯E.filter (fun τ => τ.2.1 = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ τ.1 τ.2.2) ≤
      ∑ j ∈ Finset.Icc 1 k, w j * K0 d L κ₀ := by
  refine le_trans (Finset.sum_le_sum fun τ hτ => mul_le_mul_of_nonneg_right
    (hEb τ (Finset.mem_filter.1 hτ).1) (Real.exp_pos _).le) ?_
  refine sum_labels_filter_le 𝒯E (fun τ => τ.2.1 = x) (fun τ => τ.1) (fun τ => τ.2.2) hN hκ x
    hkK w hw (fun τ hτ hP => ?_) (fun τ _ hP τ' _ hP' h1 h2 => ?_)
  · obtain ⟨h1, h2, h3⟩ := h𝒯 τ hτ
    exact ⟨h1, h2, hP ▸ h3⟩
  · exact Prod.ext h1 (Prod.ext (hP.trans hP'.symm) h2)

open Classical in
/-- **The per-site sum of the old observable label bounds** (the hypothesis `hρM` of the
constructor, with `(ys τ, is τ) = (y, i)` for `τ = (j, y, i, X)`). -/
theorem classM_siteSum_le {N : ℕ} {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) {κ₀ : ℝ} (hκ : aEnt d L + 1 ≤ κ₀)
    (hkK : k ≤ K)
    (𝒯M : Finset (ℕ × CTorus d L N₁ m₁ K × Fin N × Set (CTorus d L N₁ m₁ K)))
    (h𝒯 : ∀ τ ∈ 𝒯M, (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom m₀ τ.1 τ.2.2.2 ∧ τ.2.1 ∈ τ.2.2.2)
    (EbM : ℕ × CTorus d L N₁ m₁ K × Fin N × Set (CTorus d L N₁ m₁ K) → ℝ) (w : ℕ → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hEb : ∀ τ ∈ 𝒯M, EbM τ ≤ w τ.1) (p : CTorus d L N₁ m₁ K × Fin N) :
    ∑ τ ∈ 𝒯M.filter (fun τ => (τ.2.1, τ.2.2.1) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ τ.1 τ.2.2.2) ≤
      ∑ j ∈ Finset.Icc 1 k, w j * K0 d L κ₀ := by
  refine le_trans (Finset.sum_le_sum fun τ hτ => mul_le_mul_of_nonneg_right
    (hEb τ (Finset.mem_filter.1 hτ).1) (Real.exp_pos _).le) ?_
  refine sum_labels_filter_le 𝒯M (fun τ => (τ.2.1, τ.2.2.1) = p) (fun τ => τ.1)
    (fun τ => τ.2.2.2) hN hκ p.1 hkK w hw (fun τ hτ hP => ?_) (fun τ _ hP τ' _ hP' h1 h2 => ?_)
  · obtain ⟨h1, h2, h3⟩ := h𝒯 τ hτ
    exact ⟨h1, h2, (congrArg Prod.fst hP) ▸ h3⟩
  · have := hP.trans hP'.symm
    have e1 : τ.2.1 = τ'.2.1 := (Prod.mk.inj this).1
    have e2 : τ.2.2.1 = τ'.2.2.1 := (Prod.mk.inj this).2
    exact Prod.ext h1 (Prod.ext e1 (Prod.ext e2 h2))

/-- **Energy, constant prefactor.**  With `Eb τ ≤ c` (for the class, `c = β⁻¹ E₀`), the per-site
bound is `k · c · K₀`; it grows linearly in `k`. -/
theorem classE_siteSum_le_const {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) {κ₀ : ℝ}
    (hκ : aEnt d L + 1 ≤ κ₀) (hkK : k ≤ K)
    (𝒯E : Finset (ℕ × CTorus d L N₁ m₁ K × Set (CTorus d L N₁ m₁ K)))
    (h𝒯 : ∀ τ ∈ 𝒯E, (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2)
    (EbE : ℕ × CTorus d L N₁ m₁ K × Set (CTorus d L N₁ m₁ K) → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hEb : ∀ τ ∈ 𝒯E, EbE τ ≤ c) (x : CTorus d L N₁ m₁ K) :
    ∑ τ ∈ 𝒯E.filter (fun τ => τ.2.1 = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ τ.1 τ.2.2) ≤ (k : ℝ) * (c * K0 d L κ₀) := by
  classical
  refine le_trans (classE_siteSum_le hN hκ hkK 𝒯E h𝒯 EbE (fun _ => c) (fun _ => hc)
    hEb x) ?_
  simp

/-- **The geometric series bound** `∑_{j=1}^k q^j ≤ (1 - q)⁻¹` for `0 ≤ q < 1`. -/
theorem sum_Icc_pow_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) (k : ℕ) :
    ∑ j ∈ Finset.Icc 1 k, q ^ j ≤ (1 - q)⁻¹ := by
  have hs := hasSum_geometric_of_lt_one h0 h1
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.range (k + 1)) ?_
    (fun _ _ _ => pow_nonneg h0 _)) ?_
  · intro j hj
    simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
    omega
  · exact sum_le_hasSum _ (fun i _ => pow_nonneg h0 i) hs

/-- **Observable, geometrically decaying prefactor, uniform in `k`.**  With
`Eb τ ≤ c₉ ((L^{j})⁻¹)^e` (the class prefactor, `e = (d-2)/2 + γ - α₁`), `e > 0` and `L ≥ 2`,
the per-site bound is `c₉ K₀ (1 - (L⁻¹)^e)⁻¹`, independent of `k`. -/
theorem classM_siteSum_le_geom {N : ℕ} {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) {κ₀ : ℝ}
    (hκ : aEnt d L + 1 ≤ κ₀) (hkK : k ≤ K) (hL : 2 ≤ L)
    (𝒯M : Finset (ℕ × CTorus d L N₁ m₁ K × Fin N × Set (CTorus d L N₁ m₁ K)))
    (h𝒯 : ∀ τ ∈ 𝒯M, (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom m₀ τ.1 τ.2.2.2 ∧ τ.2.1 ∈ τ.2.2.2)
    (EbM : ℕ × CTorus d L N₁ m₁ K × Fin N × Set (CTorus d L N₁ m₁ K) → ℝ) {c₉ e : ℝ}
    (hc₉ : 0 ≤ c₉) (he : 0 < e)
    (hEb : ∀ τ ∈ 𝒯M, EbM τ ≤ c₉ * (((L : ℝ) ^ τ.1)⁻¹) ^ e)
    (p : CTorus d L N₁ m₁ K × Fin N) :
    ∑ τ ∈ 𝒯M.filter (fun τ => (τ.2.1, τ.2.2.1) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ τ.1 τ.2.2.2) ≤
      c₉ * K0 d L κ₀ * (1 - ((L : ℝ)⁻¹) ^ e)⁻¹ := by
  classical
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hLi : (L : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < L))
  set q : ℝ := ((L : ℝ)⁻¹) ^ e with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg (inv_nonneg.2 hL0.le) _
  have hq1 : q < 1 := Real.rpow_lt_one (inv_nonneg.2 hL0.le) hLi he
  have hpow : ∀ j : ℕ, (((L : ℝ) ^ j)⁻¹) ^ e = q ^ j := by
    intro j
    rw [hq, ← inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.2 hL0.le),
      mul_comm, Real.rpow_mul (inv_nonneg.2 hL0.le), Real.rpow_natCast]
  have hw : ∀ j : ℕ, 0 ≤ c₉ * q ^ j := fun j => mul_nonneg hc₉ (pow_nonneg hq0 j)
  refine le_trans (classM_siteSum_le (N := N) hN hκ hkK 𝒯M h𝒯 EbM (fun j => c₉ * q ^ j) hw
    (fun τ hτ => by simpa only [hpow] using hEb τ hτ) p) ?_
  calc ∑ j ∈ Finset.Icc 1 k, c₉ * q ^ j * K0 d L κ₀
      = c₉ * K0 d L κ₀ * ∑ j ∈ Finset.Icc 1 k, q ^ j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (sum_Icc_pow_le hq0 hq1 k) ?_
        have h1 : 0 ≤ 1 - Real.exp (-1) :=
          sub_nonneg.2 (Real.exp_le_one_iff.2 (by norm_num))
        have : 0 ≤ K0 d L κ₀ := div_nonneg (Real.exp_pos _).le h1
        positivity

/-- **The unit `ℓ¹` ball of sources lies in `{ℓ¹ < 1}`.** -/
theorem l1_lt_one_of_mem_l1Ball {N : ℕ} {g : Fld d L N₁ m₁ K N}
    (hg : g ∈ l1Ball d L N₁ m₁ K N) : Def6.l1 g < 1 := by
  refine lt_of_le_of_lt ?_ hg
  unfold Def6.l1
  refine Finset.sum_le_sum fun x _ => ?_
  unfold vn
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun i _ => norm_nonneg _, ?_⟩
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)

end Balaban.Fluctuation
