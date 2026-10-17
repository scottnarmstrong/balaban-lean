/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldTermSiteSums
public import Balaban.Fluctuation.Prop33Parts
public import Balaban.Localization.BlockCount
public import Balaban.Localization.I5Glue
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The per-domain sum of the label bounds, uniformly in `k` (`LocalClassDensityFamilyGenCount`)

For the labels `τ = (j, y, X)` of a class (`1 ≤ j ≤ k`, `X ∈ 𝒟_j` of index `m₀`, `y ∈ X` aligned to
`L^j`) with per-label bounds `B_τ`, the numerical condition `hnumH` of the activity family asks for
a bound of the per-domain sum `∑_{τ : Y ∈ polyDom τ} 2 B_τ e^{-κ₀ d(X_τ)}`.  With the raw bound of
the old terms (one `E₀` for every `(j, y)`) the sum grows like `L^{(k+1)d}` (W945
`classActivity_domainSum_ge`).  With bounds that decay in `k - j`,
`B_τ ≤ C_I E₀ s_{jk}^{d + α₃}`, `s_{jk} = L^{-(k-j)}`, for `k - j ≥ n₁`, and `B_τ ≤ K_L E₀` for the
last `n₁` levels, the sum is bounded uniformly in `k`.

* `card_aligned_in_cellUnion`: a union `Y` of cells of side `L^{k+1+m_c+m₁}` contains at most
  `#cells(Y) · (L^{k+1+m_c+m₁-j})^d` points aligned to `L^j`;
* `scale_identity`, `geom_levels`: the arithmetic of `s_{jk}^{d+α₃} (L^{k-j})^d = (L^{-α₃})^{k-j}`
  and of the geometric sum over the levels;
* `classActivity_domainSum_le_uniform`: for a family of labels whose centres lie in `Y` whenever the
  label is counted, the sum is at most
  `#cells(Y) · L^{(1+m_c+m₁)d} · E₀ · 2K₀(κ₀) (C_I (1 - L^{-α₃})⁻¹ + n₁ K_L L^{(n₁-1)d})`
  (`K₀(κ₀)` of (G2) is the entropy of the polymers through a site, `sum_polyDom_through_le`), with
  no dependence on `k`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Finset

/-- **The scale identity**: `(L^{-m})^{d+α} (L^m)^d = (L^{-α})^m`. -/
theorem scale_identity (L : ℕ) (hL : 2 ≤ L) (d m : ℕ) {α : ℝ} :
    (((L : ℝ)⁻¹ ^ m) ^ ((d : ℝ) + α)) * (((L : ℝ) ^ m) ^ d) = (((L : ℝ) ^ (-α)) ^ m) := by
  have hL0 : (0 : ℝ) < L := by positivity
  have hx : (0 : ℝ) < (L : ℝ) ^ m := by positivity
  rw [inv_pow, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le, ← Real.rpow_natCast ((L : ℝ) ^ m) d,
    ← Real.rpow_add hx]
  rw [← Real.rpow_natCast (L : ℝ) m, ← Real.rpow_mul hL0.le,
    ← Real.rpow_natCast ((L : ℝ) ^ (-α)) m, ← Real.rpow_mul hL0.le]
  congr 1
  ring

/-- **The geometric sum over the levels**: for `0 ≤ q < 1`, `∑_{j ≤ k} q^{k-j} ≤ (1 - q)⁻¹`. -/
theorem geom_levels (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ∑ j ∈ (Icc 1 k).filter P, q ^ (k - j) ≤ (1 - q)⁻¹ := by
  have h1 : ∑ j ∈ (Icc 1 k).filter P, q ^ (k - j) ≤ ∑ j ∈ Icc 1 k, q ^ (k - j) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => pow_nonneg hq0 _)
  have h2 : ∑ j ∈ Icc 1 k, q ^ (k - j) = ∑ m ∈ range k, q ^ m := by
    refine Finset.sum_bij (fun j _ => k - j) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_Icc] at hj
      rw [Finset.mem_range]; omega
    · intro a ha b hb h
      rw [Finset.mem_Icc] at ha hb
      omega
    · intro m hm
      rw [Finset.mem_range] at hm
      exact ⟨k - m, by rw [Finset.mem_Icc]; omega, by omega⟩
    · intro j _; rfl
  have h3 : (∑ m ∈ range k, q ^ m) * (1 - q) = 1 - q ^ k := geom_sum_mul_neg q k
  have hq : 0 < 1 - q := by linarith
  have h4 : ∑ m ∈ range k, q ^ m ≤ (1 - q)⁻¹ := by
    rw [← one_div, le_div_iff₀ hq]
    linarith [pow_nonneg hq0 k]
  linarith

section Counting

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

open Classical in
/-- **Aligned points in a union of cells.**  If every site `y` of `Y` has its cell
`box (cbase a y) a`, `a = L^{K+m_c+m₁}`, inside `Y`, then the number of points of `Y` aligned to
`L^j` (`j ≤ K + m₁`) is at most `#cells(Y) · (L^{K+m_c+m₁-j})^d`. -/
theorem card_aligned_in_cellUnion {j mc : ℕ} (hj : j ≤ K + m₁)
    {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : ∀ y ∈ Y, box (cbase (cellSide L mc m₁ K) y) (cellSide L mc m₁ K) ⊆ Y) :
    (Finset.univ.filter fun b : CTorus d L N₁ m₁ K => Aligned (L ^ j) b ∧ b ∈ Y).card ≤
      cellCount (cellSide L mc m₁ K) Y * (L ^ (K + mc + m₁ - j)) ^ d := by
  have hLpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hjdvd : L ^ j ∣ (N₁ * L ^ m₁) * L ^ K := by
    have h1 : L ^ j ∣ L ^ m₁ * L ^ K := by
      rw [← pow_add]; exact pow_dvd_pow L (by omega)
    rw [mul_assoc]
    exact Dvd.dvd.mul_left h1 N₁
  have hadiv : cellSide L mc m₁ K = L ^ (K + mc + m₁ - j) * L ^ j := by
    unfold cellSide
    rw [← pow_add]
    congr 1
    omega
  have hsub : (Finset.univ.filter fun b : CTorus d L N₁ m₁ K => Aligned (L ^ j) b ∧ b ∈ Y) ⊆
      (Finset.univ.filter fun c : CTorus d L N₁ m₁ K =>
        Aligned (cellSide L mc m₁ K) c ∧ box c (cellSide L mc m₁ K) ⊆ Y).biUnion
        (fun c => Finset.univ.filter fun b : CTorus d L N₁ m₁ K =>
          Aligned (L ^ j) b ∧ b ∈ box c (L ^ (K + mc + m₁ - j) * L ^ j)) := by
    intro b hb
    obtain ⟨hal, hbY⟩ := (Finset.mem_filter.1 hb).2
    rw [Finset.mem_biUnion]
    refine ⟨cbase (cellSide L mc m₁ K) b, Finset.mem_filter.2
      ⟨Finset.mem_univ _, aligned_cbase b, hY b hbY⟩, Finset.mem_filter.2
      ⟨Finset.mem_univ _, hal, ?_⟩⟩
    rw [← hadiv]
    exact mem_box_cbase (cellSide_pos (L := L) mc m₁ K) b
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ c ∈ (Finset.univ.filter fun c : CTorus d L N₁ m₁ K =>
        Aligned (cellSide L mc m₁ K) c ∧ box c (cellSide L mc m₁ K) ⊆ Y),
        (L ^ (K + mc + m₁ - j)) ^ d := by
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun c hc => ?_)
        exact card_aligned_in_box_mul hjdvd (pow_pos hLpos j) _
          (aligned_of_dvd (Dvd.intro_left _ hadiv.symm) (Finset.mem_filter.1 hc).2.1)
    _ = _ := by
        unfold cellCount
        rw [Finset.sum_const, smul_eq_mul]



open Classical in
/-- **The per-domain sum of the label bounds is uniform in `k`.**  Let `τ ∈ ι` be a finite family
of labels `(j_τ, y_τ, X_τ)` (`1 ≤ j_τ ≤ k`, `X_τ ∈ 𝒟_{j_τ}` of index `m₀`, `y_τ ∈ X_τ` aligned to
`L^{j_τ}`, different labels being different triples), `Q` a predicate on labels (in the
application `Y ∈ polyDom τ`) such that the centre of every label with `Q` lies in `Y`, and `Y` a
union of cells of side `L^{k+1+m_c+m₁}`.  If the bounds `B_τ` of the labels satisfy
`B_τ ≤ C_I E₀ s_{jk}^{d+α₃}` (`s_{jk} = L^{-(k-j)}`) for `k - j ≥ n₁` and `B_τ ≤ K_L E₀` for the
last `n₁` levels, then
`∑_{τ : Q τ} 2 B_τ e^{-κ₀ d(X_τ)} ≤ #cells(Y) · L^{(1+m_c+m₁)d} · E₀ ·
2K₀(κ₀) (C_I (1 - L^{-α₃})⁻¹ + n₁ K_L L^{(n₁-1)d})`
for `κ₀ ≥ a_ent + 1`: the right side does not depend on `k`. -/
theorem classActivity_domainSum_le_uniform {ι : Type*} [Fintype ι] {k m₀ mc : ℕ} {m₁ : ℕ}
    (hN : L ^ m₀ ∣ N₁) {κ₀ : ℝ} (hκ : aEnt d L + 1 ≤ κ₀) (hL : 2 ≤ L)
    (jL : ι → ℕ) (yL : ι → CTorus d L N₁ m₁ (k + 1)) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj : ∀ τ, 1 ≤ jL τ ∧ jL τ ≤ k) (hXp : ∀ τ, IsPolyDom m₀ (jL τ) (XL τ))
    (hy : ∀ τ, yL τ ∈ XL τ) (hal : ∀ τ, Aligned (L ^ jL τ) (yL τ))
    (hinj : ∀ τ τ', jL τ = jL τ' → yL τ = yL τ' → XL τ = XL τ' → τ = τ')
    (Q : ι → Prop) [DecidablePred Q] {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hQ : ∀ τ, Q τ → yL τ ∈ Y)
    (hY : ∀ y ∈ Y, box (cbase (cellSide L mc m₁ (k + 1)) y) (cellSide L mc m₁ (k + 1)) ⊆ Y)
    (Eb : ι → ℝ) {CI KL E₀ α₃ : ℝ} (n₁ : ℕ) (hCI : 0 ≤ CI) (hKL : 0 ≤ KL)
    (hE₀ : 0 ≤ E₀) (hα : 0 < α₃)
    (hEbI : ∀ τ, jL τ + n₁ ≤ k →
      Eb τ ≤ CI * E₀ * (((L : ℝ)⁻¹ ^ (k - jL τ)) ^ ((d : ℝ) + α₃)))
    (hEbL : ∀ τ, k < jL τ + n₁ → Eb τ ≤ KL * E₀) :
    ∑ τ ∈ Finset.univ.filter Q, 2 * Eb τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ)) ≤
      (cellCount (cellSide L mc m₁ (k + 1)) Y : ℝ) * (((L : ℝ) ^ (1 + mc + m₁)) ^ d) * E₀ *
        (2 * K0 d L κ₀ * (CI * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
          n₁ * KL * (((L : ℝ) ^ (n₁ - 1)) ^ d))) := by
  have hL0 : (0 : ℝ) < L := by positivity
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have hK0 : 0 < K0 d L κ₀ := by
    unfold K0
    have : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
    have : 0 < 1 - Real.exp (-1) := by linarith
    positivity
  set q : ℝ := (L : ℝ) ^ (-α₃) with hqdef
  have hq0 : 0 ≤ q := (Real.rpow_pos_of_pos hL0 _).le
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith)
  -- the level weights
  set w : ℕ → ℝ := fun j => if j + n₁ ≤ k then CI * E₀ * (((L : ℝ)⁻¹ ^ (k - j)) ^ ((d : ℝ) + α₃))
    else KL * E₀ with hwdef
  have hw0 : ∀ j, 0 ≤ w j := fun j => by
    simp only [hwdef]
    split_ifs
    · have : 0 ≤ ((L : ℝ)⁻¹ ^ (k - j)) ^ ((d : ℝ) + α₃) :=
        Real.rpow_nonneg (pow_nonneg (inv_nonneg.2 hL0.le) _) _
      positivity
    · positivity
  have hEbw : ∀ τ, Eb τ ≤ w (jL τ) := fun τ => by
    simp only [hwdef]
    split_ifs with h
    · exact hEbI τ h
    · exact hEbL τ (by omega)
  set A : ℕ → Finset (CTorus d L N₁ m₁ (k + 1)) := fun j =>
    Finset.univ.filter fun b => Aligned (L ^ j) b ∧ b ∈ Y with hAdef
  set S := Finset.univ.filter Q with hS
  have hS1 : ∀ τ ∈ S, Q τ := fun τ hτ => (Finset.mem_filter.1 hτ).2
  have step1 : ∑ τ ∈ S, 2 * Eb τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ)) ≤
      ∑ τ ∈ S, 2 * w (jL τ) * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ)) :=
    Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_right
      (by have := hEbw τ; linarith) (Real.exp_pos _).le
  -- one level and one centre
  have hent : ∀ j ∈ Finset.Icc 1 k, ∀ y : CTorus d L N₁ m₁ (k + 1),
      ∑ τ ∈ Finset.univ.filter (fun τ => yL τ = y ∧ jL τ = j),
        Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ)) ≤ K0 d L κ₀ := by
    intro j hj y
    have hinjOn : Set.InjOn XL ↑(Finset.univ.filter (fun τ => yL τ = y ∧ jL τ = j)) := by
      intro a ha b hb h
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      exact hinj a b (ha.2.trans hb.2.symm) (ha.1.trans hb.1.symm) h
    calc _ = ∑ X ∈ (Finset.univ.filter (fun τ => yL τ = y ∧ jL τ = j)).image XL,
          Real.exp (-κ₀ * treeLenCovOne m₀ j X) := by
          rw [Finset.sum_image hinjOn]
          exact Finset.sum_congr rfl fun τ hτ => by
            rw [(Finset.mem_filter.1 hτ).2.2]
      _ ≤ ∑ X ∈ Finset.univ.filter (fun X : Set (CTorus d L N₁ m₁ (k + 1)) =>
            IsPolyDom m₀ j X ∧ y ∈ X), Real.exp (-κ₀ * treeLenCovOne m₀ j X) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => (Real.exp_pos _).le)
          intro X hX
          obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hX
          obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hτ).2
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
          · exact h2 ▸ hXp τ
          · exact h1 ▸ hy τ
      _ ≤ K0 d L κ₀ := sum_polyDom_through_le (Nat.le_succ k |>.trans' (Finset.mem_Icc.1 hj).2)
          hN hκ y
  have hfib : ∀ j ∈ Finset.Icc 1 k,
      ∑ τ ∈ S.filter (fun τ => jL τ = j),
        2 * w (jL τ) * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ)) ≤
        (A j).card * (2 * w j * K0 d L κ₀) := by
    intro j hj
    have hmaps : ∀ τ ∈ S.filter (fun τ => jL τ = j), yL τ ∈ A j := by
      intro τ hτ
      obtain ⟨hτS, hτj⟩ := Finset.mem_filter.1 hτ
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hτj ▸ hal τ, hQ τ (hS1 τ hτS)⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc _ ≤ ∑ y ∈ A j, 2 * w j * K0 d L κ₀ := by
          refine Finset.sum_le_sum fun y _ => ?_
          have hsub : ((S.filter (fun τ => jL τ = j)).filter (fun τ => yL τ = y)) ⊆
              Finset.univ.filter (fun τ => yL τ = y ∧ jL τ = j) := by
            intro τ hτ
            obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hτ
            obtain ⟨h3, h4⟩ := Finset.mem_filter.1 h1
            exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2, h4⟩
          calc _ = ∑ τ ∈ (S.filter (fun τ => jL τ = j)).filter (fun τ => yL τ = y),
                2 * w j * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ)) :=
                Finset.sum_congr rfl fun τ hτ => by
                  rw [(Finset.mem_filter.1 (Finset.mem_filter.1 hτ).1).2]
            _ = 2 * w j * ∑ τ ∈ (S.filter (fun τ => jL τ = j)).filter (fun τ => yL τ = y),
                Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ)) := by rw [Finset.mul_sum]
            _ ≤ 2 * w j * ∑ τ ∈ Finset.univ.filter (fun τ => yL τ = y ∧ jL τ = j),
                Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ)) :=
                mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub
                  (fun _ _ _ => (Real.exp_pos _).le)) (by have := hw0 j; positivity)
            _ ≤ 2 * w j * K0 d L κ₀ :=
                mul_le_mul_of_nonneg_left (hent j hj y) (by have := hw0 j; positivity)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hmapsj : ∀ τ ∈ S, jL τ ∈ Finset.Icc 1 k := fun τ _ => Finset.mem_Icc.2 (hj τ)
  -- the count of the centres of a level
  have hcard : ∀ j ∈ Finset.Icc 1 k, ((A j).card : ℝ) ≤
      (cellCount (cellSide L mc m₁ (k + 1)) Y : ℝ) * (((L : ℝ) ^ (1 + mc + m₁)) ^ d) *
        (((L : ℝ) ^ (k - j)) ^ d) := by
    intro j hj
    have hj' := Finset.mem_Icc.1 hj
    have h := card_aligned_in_cellUnion (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
      (j := j) (mc := mc) (by omega) hY
    have hexp : L ^ (k + 1 + mc + m₁ - j) = L ^ (k - j) * L ^ (1 + mc + m₁) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hexp, mul_pow] at h
    have h' : ((A j).card : ℝ) ≤ (cellCount (cellSide L mc m₁ (k + 1)) Y : ℝ) *
        ((((L : ℝ) ^ (k - j)) ^ d) * (((L : ℝ) ^ (1 + mc + m₁)) ^ d)) := by exact_mod_cast h
    calc _ ≤ _ := h'
      _ = _ := by ring
  -- the sum over the levels
  have hlev : ∑ j ∈ Finset.Icc 1 k, w j * (((L : ℝ) ^ (k - j)) ^ d) ≤
      E₀ * (CI * (1 - q)⁻¹ + n₁ * KL * (((L : ℝ) ^ (n₁ - 1)) ^ d)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 k) (fun j => j + n₁ ≤ k)]
    have hT1 : ∑ j ∈ (Finset.Icc 1 k).filter (fun j => j + n₁ ≤ k),
        w j * (((L : ℝ) ^ (k - j)) ^ d) ≤ E₀ * (CI * (1 - q)⁻¹) := by
      have : ∀ j ∈ (Finset.Icc 1 k).filter (fun j => j + n₁ ≤ k),
          w j * (((L : ℝ) ^ (k - j)) ^ d) = CI * E₀ * q ^ (k - j) := by
        intro j hj
        have hj2 := (Finset.mem_filter.1 hj).2
        simp only [hwdef, ite_eq_left hj2]
        rw [mul_assoc, scale_identity L hL d (k - j)]
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
      calc _ ≤ CI * E₀ * (1 - q)⁻¹ :=
            mul_le_mul_of_nonneg_left (geom_levels q hq0 hq1 k (fun j => j + n₁ ≤ k))
              (by positivity)
        _ = _ := by ring
    have hT2 : ∑ j ∈ (Finset.Icc 1 k).filter (fun j => ¬ j + n₁ ≤ k),
        w j * (((L : ℝ) ^ (k - j)) ^ d) ≤ E₀ * (n₁ * KL * (((L : ℝ) ^ (n₁ - 1)) ^ d)) := by
      have hb : ∀ j ∈ (Finset.Icc 1 k).filter (fun j => ¬ j + n₁ ≤ k),
          w j * (((L : ℝ) ^ (k - j)) ^ d) ≤ KL * E₀ * (((L : ℝ) ^ (n₁ - 1)) ^ d) := by
        intro j hj
        have hj2 := (Finset.mem_filter.1 hj).2
        simp only [hwdef, ite_eq_right hj2]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact pow_le_pow_left₀ (by positivity)
          (pow_le_pow_right₀ hL1.le (by omega)) d
      have hcardT : ((Finset.Icc 1 k).filter (fun j => ¬ j + n₁ ≤ k)).card ≤ n₁ := by
        calc _ ≤ (Finset.Ioc (k - n₁) k).card := by
              refine Finset.card_le_card fun j hj => ?_
              have := Finset.mem_filter.1 hj
              have := Finset.mem_Icc.1 this.1
              rw [Finset.mem_Ioc]; omega
          _ ≤ n₁ := by rw [Nat.card_Ioc]; omega
      calc _ ≤ ∑ j ∈ (Finset.Icc 1 k).filter (fun j => ¬ j + n₁ ≤ k),
            KL * E₀ * (((L : ℝ) ^ (n₁ - 1)) ^ d) := Finset.sum_le_sum hb
        _ = (((Finset.Icc 1 k).filter (fun j => ¬ j + n₁ ≤ k)).card : ℝ) *
            (KL * E₀ * (((L : ℝ) ^ (n₁ - 1)) ^ d)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ n₁ * (KL * E₀ * (((L : ℝ) ^ (n₁ - 1)) ^ d)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcardT) (by positivity)
        _ = _ := by ring
    calc _ ≤ _ := add_le_add hT1 hT2
      _ = _ := by ring
  -- assembly
  have hfs := Finset.sum_fiberwise_of_maps_to (s := S) (f := fun τ => 2 * w (jL τ) *
    Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ))) hmapsj
  have hfinal : ∑ j ∈ Finset.Icc 1 k, ((A j).card : ℝ) * (2 * w j * K0 d L κ₀) ≤
      (cellCount (cellSide L mc m₁ (k + 1)) Y : ℝ) * (((L : ℝ) ^ (1 + mc + m₁)) ^ d) *
        (2 * K0 d L κ₀) * ∑ j ∈ Finset.Icc 1 k, w j * (((L : ℝ) ^ (k - j)) ^ d) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    calc ((A j).card : ℝ) * (2 * w j * K0 d L κ₀) ≤
        ((cellCount (cellSide L mc m₁ (k + 1)) Y : ℝ) * (((L : ℝ) ^ (1 + mc + m₁)) ^ d) *
          (((L : ℝ) ^ (k - j)) ^ d)) * (2 * w j * K0 d L κ₀) :=
          mul_le_mul_of_nonneg_right (hcard j hj) (by have := hw0 j; positivity)
      _ = _ := by ring
  refine le_of_le_of_eq (step1.trans (hfs.symm.le.trans (le_trans
    (Finset.sum_le_sum fun j hj => hfib j hj)
    (hfinal.trans (mul_le_mul_of_nonneg_left hlev (by positivity)))))) (by ring)

open Classical in
/-- **The centre of a label lies in every domain of its expansion**: `y ∈ X ⊆ X₁ ⊆ Y` for
`Y ∈ polyDom` (`CovSetup.X_sub`, `subset_Ysites`). -/
theorem centre_mem_of_mem_polyDom {k m₀ j : ℕ} {ϱ : ℝ}
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} (hcov : CovSetup Gp m₀ j X 𝒦X)
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : y ∈ X)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : Y ∈ polyDom Gp X₁f m₀ j 𝒦X) : y ∈ Y := by
  unfold polyDom polymerDomains at hY
  obtain ⟨C, -, rfl⟩ := Finset.mem_image.1 hY
  exact subset_Ysites _ _ (hcov.X_sub hy)

open Classical in
/-- **The per-domain sum of the label bounds in the form of the condition `hnumH`.**  For labels
`τ` with the cover data `(X₁f τ, 𝒦X τ)` of their expansion, a domain `Y` which is a union of cells
of side `L^{k+1+m_c+m₁}`, and bounds `B_τ` as in `classActivity_domainSum_le_uniform`,
`∑_{τ : Y ∈ polyDom τ} 2 B_τ e^{-κ₀ d(X_τ) - 2κ_dec d^cov_{m₀}(Y)}` is at most
`#cells(Y) · L^{(1+m_c+m₁)d} · E₀ · 2K₀(κ₀) (C_I (1 - L^{-α₃})⁻¹ + n₁ K_L L^{(n₁-1)d}) ·
e^{-2κ_dec d^cov_{m₀}(Y)}`. -/
theorem classActivity_domainSum_polyDom_le_uniform {ι : Type*} [Fintype ι] {k m₀ mc : ℕ}
    {ϱ : ℝ} (Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (hN : L ^ m₀ ∣ N₁) {κ₀ κdec : ℝ} (hκ : aEnt d L + 1 ≤ κ₀) (hL : 2 ≤ L)
    (jL : ι → ℕ) (yL : ι → CTorus d L N₁ m₁ (k + 1)) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj : ∀ τ, 1 ≤ jL τ ∧ jL τ ≤ k) (hXp : ∀ τ, IsPolyDom m₀ (jL τ) (XL τ))
    (hy : ∀ τ, yL τ ∈ XL τ) (hal : ∀ τ, Aligned (L ^ jL τ) (yL τ))
    (hinj : ∀ τ τ', jL τ = jL τ' → yL τ = yL τ' → XL τ = XL τ' → τ = τ')
    (hcov : ∀ τ, CovSetup Gp m₀ (jL τ) (XL τ) (𝒦X τ))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY : ∀ y ∈ Y, box (cbase (cellSide L mc m₁ (k + 1)) y) (cellSide L mc m₁ (k + 1)) ⊆ Y)
    (Eb : ι → ℝ) {CI KL E₀ α₃ : ℝ} (n₁ : ℕ) (hCI : 0 ≤ CI) (hKL : 0 ≤ KL)
    (hE₀ : 0 ≤ E₀) (hα : 0 < α₃)
    (hEbI : ∀ τ, jL τ + n₁ ≤ k →
      Eb τ ≤ CI * E₀ * (((L : ℝ)⁻¹ ^ (k - jL τ)) ^ ((d : ℝ) + α₃)))
    (hEbL : ∀ τ, k < jL τ + n₁ → Eb τ ≤ KL * E₀) :
    ∑ τ, (if Y ∈ polyDom Gp (X₁f τ) m₀ (jL τ) (𝒦X τ) then
        2 * Eb τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ) -
          2 * κdec * treeLenCov Gp m₀ Y) else 0) ≤
      (cellCount (cellSide L mc m₁ (k + 1)) Y : ℝ) * (((L : ℝ) ^ (1 + mc + m₁)) ^ d) * E₀ *
        (2 * K0 d L κ₀ * (CI * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
          n₁ * KL * (((L : ℝ) ^ (n₁ - 1)) ^ d))) * Real.exp (-(2 * κdec * treeLenCov Gp m₀ Y)) := by
  have h := classActivity_domainSum_le_uniform hN hκ hL jL yL XL hj hXp hy hal hinj
    (fun τ => Y ∈ polyDom Gp (X₁f τ) m₀ (jL τ) (𝒦X τ)) (Y := Y)
    (fun τ hτ => centre_mem_of_mem_polyDom (hcov τ) (hy τ) hτ) hY Eb n₁ hCI hKL hE₀ hα hEbI hEbL
  have he : ∀ τ, (if Y ∈ polyDom Gp (X₁f τ) m₀ (jL τ) (𝒦X τ) then
        2 * Eb τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ) -
          2 * κdec * treeLenCov Gp m₀ Y) else 0) =
      (if Y ∈ polyDom Gp (X₁f τ) m₀ (jL τ) (𝒦X τ) then
        2 * Eb τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ)) else 0) *
        Real.exp (-(2 * κdec * treeLenCov Gp m₀ Y)) := fun τ => by
    split_ifs
    · rw [sub_eq_add_neg, Real.exp_add]; ring
    · simp
  rw [Finset.sum_congr rfl fun τ _ => he τ, ← Finset.sum_mul, ← Finset.sum_filter]
  exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

end Counting

end Balaban.Fluctuation
