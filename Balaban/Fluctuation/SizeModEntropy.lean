/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModStruct
public import Balaban.Fluctuation.SizeModSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# (G2): entropy (FLUCTUATION.md Lemma 1.2)

For a `π_j`-cube `□ ⊆ Ω` and `κ₀ ≥ a_ent + 1`:
`∑_{X ⊇ □, X ∈ 𝒟_j(mod Ω^c)} e^{-κ₀ d^cov_j(X mod Ω^c)} ≤ K₀` (`G2_X`) and
`∑_{S ⊇ □} e^{-κ₀ d_Ω(S)} ≤ K₀` (`G2_S`; sets `S` of `π_j`-cubes of `Ω`, the terms with
`d_Ω(S) = ∞` being `0`).  The constants `aEnt d L`, `K0 d L` are explicit and depend only on
`(d, L)`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

/-- The base `Q = B (2C)^{2Δ}` of the entropy bound, `B = (2L-1)^d`, `Δ = 3^d`,
`C = Δ² 2^{B (1 + Δ)}`. -/
noncomputable def entQ (d L : ℕ) : ℝ :=
  ((2 * (L - 1) + 1) ^ d : ℕ) *
    (2 * (((3 ^ d) ^ 2 : ℕ) : ℝ) * 2 ^ (((2 * (L - 1) + 1) ^ d * (1 + 3 ^ d) : ℕ))) ^ (2 * 3 ^ d)

/-- **`a_ent(d, L)`** of (G2). -/
noncomputable def aEnt (d L : ℕ) : ℝ := Real.log (entQ d L)

/-- **`K₀(d, L, κ₀)`** of (G2) (it does not depend on `κ₀ ≥ a_ent + 1`). -/
noncomputable def K0 (d L : ℕ) (_κ₀ : ℝ) : ℝ := Real.exp (aEnt d L) / (1 - Real.exp (-1))

theorem one_le_entQ (d L : ℕ) [NeZero L] : 1 ≤ entQ d L := by
  unfold entQ
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h1 : (1 : ℝ) ≤ (((2 * (L - 1) + 1) ^ d : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_pow _ _ (by omega)
  have h2 : (1 : ℝ) ≤ 2 * (((3 ^ d) ^ 2 : ℕ) : ℝ) * 2 ^ (((2 * (L - 1) + 1) ^ d * (1 + 3 ^ d) : ℕ)) := by
    have a1 : (1 : ℝ) ≤ (((3 ^ d) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by norm_num))
    have a2 : (1 : ℝ) ≤ 2 ^ (((2 * (L - 1) + 1) ^ d * (1 + 3 ^ d) : ℕ)) := one_le_pow₀ (by norm_num)
    nlinarith
  exact one_le_mul_of_one_le_of_one_le h1 (one_le_pow₀ h2)

theorem aEnt_nonneg (d L : ℕ) [NeZero L] : 0 ≤ aEnt d L := Real.log_nonneg (one_le_entQ d L)

/-- The counting bound: `|famT| ≤ exp (a_ent (ℓ + 1))` for `m = 3^d (ℓ + 2)` cells. -/
theorem card_famT_le_exp {d n : ℕ} [NeZero n] (L : ℕ) [NeZero L] (a : ℕ) (ℓ : ℕ)
    (t0 : Torus d n) :
    ((famT L a (3 ^ d * (ℓ + 2)) t0).card : ℝ) ≤ Real.exp (aEnt d L * (ℓ + 1)) := by
  set B : ℕ := (2 * (L - 1) + 1) ^ d with hB
  set Δ : ℕ := 3 ^ d with hΔ
  set m : ℕ := Δ * (ℓ + 2) with hm
  have hB1 : 1 ≤ B := Nat.one_le_pow _ _ (by omega)
  have hΔ1 : 1 ≤ Δ := Nat.one_le_pow _ _ (by norm_num)
  have h0 := card_famT_le (d := d) L a m t0
  have h0R : ((famT L a m t0).card : ℝ) ≤
      (B : ℝ) * ((m : ℝ) * (Δ : ℝ) ^ (2 * m)) * 2 ^ (m * B * (1 + Δ)) := by
    have h0' : (famT L a m t0).card ≤ B * (m * Δ ^ (2 * m)) * 2 ^ (m * B * (1 + Δ)) := h0
    exact_mod_cast h0'
  set C : ℝ := 2 * ((Δ ^ 2 : ℕ) : ℝ) * 2 ^ (B * (1 + Δ)) with hC
  have hC1 : 1 ≤ C := by
    have a1 : (1 : ℝ) ≤ ((Δ ^ 2 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow _ _ hΔ1
    have a2 : (1 : ℝ) ≤ 2 ^ (B * (1 + Δ)) := one_le_pow₀ (by norm_num)
    rw [hC]; nlinarith
  have e1 : (Δ : ℝ) ^ (2 * m) * 2 ^ (m * B * (1 + Δ)) = (C / 2) ^ m := by
    rw [hC]
    push_cast
    rw [show (2 * ((Δ : ℝ) ^ 2) * 2 ^ (B * (1 + Δ))) / 2 = (Δ : ℝ) ^ 2 * 2 ^ (B * (1 + Δ)) by ring,
      mul_pow, ← pow_mul, ← pow_mul]
    congr 2; ring
  have hmle : (m : ℝ) ≤ 2 ^ m := by exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
  have h1 : ((famT L a m t0).card : ℝ) ≤ (B : ℝ) * C ^ m := by
    calc _ ≤ _ := h0R
      _ = (B : ℝ) * ((m : ℝ) * ((Δ : ℝ) ^ (2 * m) * 2 ^ (m * B * (1 + Δ)))) := by ring
      _ = (B : ℝ) * ((m : ℝ) * (C / 2) ^ m) := by rw [e1]
      _ ≤ (B : ℝ) * (2 ^ m * (C / 2) ^ m) := by
          gcongr
      _ = (B : ℝ) * C ^ m := by rw [← mul_pow]; congr 2; ring
  have hmle2 : m ≤ 2 * Δ * (ℓ + 1) := by rw [hm]; nlinarith
  have h2 : C ^ m ≤ (C ^ (2 * Δ)) ^ (ℓ + 1) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hC1 (by nlinarith)
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have h3 : (B : ℝ) ≤ (B : ℝ) ^ (ℓ + 1) := by
    calc (B : ℝ) = (B : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hBR (by omega)
  have hQ : entQ d L = (B : ℝ) * C ^ (2 * Δ) := by
    unfold entQ; rfl
  have hQpos : 0 < entQ d L := lt_of_lt_of_le one_pos (one_le_entQ d L)
  have hexp : Real.exp (aEnt d L * (ℓ + 1)) = entQ d L ^ (ℓ + 1) := by
    unfold aEnt
    rw [mul_comm, show ((ℓ : ℝ) + 1) = ((ℓ + 1 : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul,
      Real.exp_log hQpos]
  rw [hexp, hQ, mul_pow]
  calc _ ≤ (B : ℝ) * C ^ m := h1
    _ ≤ (B : ℝ) ^ (ℓ + 1) * (C ^ (2 * Δ)) ^ (ℓ + 1) :=
        mul_le_mul h3 h2 (by positivity) (by positivity)

section G2

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

/-- An admissible pair of cost `< ℓ + 1` gives a connected set of at most `3^d (ℓ + 2)` cells near
`t0`: the cells met by the structure. -/
theorem image_mem_Acand (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {Z Ω 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (h : ModAdmissible m₀ j Ω Z 𝒦 W E) {t0 : CTorus d L N₁ m₁ K}
    (ht0 : Aligned (cellSide L m₀ m₁ j) t0) (ht0Z : t0 ∈ Z ∩ Ω) {ℓ : ℕ}
    (hcost : bondCost (scaleW L m₀ m₁ j) E < ℓ + 1) :
    W.image (cbase (cellSide L m₀ m₁ j)) ∈ Acand L (cellSide L m₀ m₁ j) (3 ^ d * (ℓ + 2)) t0 := by
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  obtain ⟨c, hcA, hcn⟩ := exists_near_of_mem hN hj h ht0 ht0Z
  have hcard := card_image_cbase_le hN hj h.2.2.1
  have hlt : ((W.image (cbase (cellSide L m₀ m₁ j))).card : ℝ) < ((3 ^ d * (ℓ + 2) : ℕ) : ℝ) := by
    push_cast
    have h3 : (0 : ℝ) < 3 ^ d := by positivity
    nlinarith
  refine mem_Acand hcA hcn (by exact_mod_cast hlt.le) (connected_image_cbase hdvd ha0 h.2.2.1)

theorem mem_famT_of_admissible (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {Z Ω 𝒦 : Set (CTorus d L N₁ m₁ K)} {W : Finset (CTorus d L N₁ m₁ K)}
    {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (h : ModAdmissible m₀ j Ω Z 𝒦 W E) {t0 : CTorus d L N₁ m₁ K}
    (ht0 : Aligned (cellSide L m₀ m₁ j) t0) (ht0Z : t0 ∈ Z ∩ Ω) {ℓ : ℕ}
    (hcost : bondCost (scaleW L m₀ m₁ j) E < ℓ + 1) {T U : Finset (CTorus d L N₁ m₁ K)}
    (hT : ∀ t ∈ T, Aligned (cellSide L m₀ m₁ j) t ∧ t ∈ Z ∩ Ω)
    (hU : ∀ u ∈ U, ∃ t ∈ T, Near 1 (cellSide L m₀ m₁ j) t u) :
    (T, U) ∈ famT L (cellSide L m₀ m₁ j) (3 ^ d * (ℓ + 2)) t0 := by
  classical
  have hT' : ∀ t ∈ T, t ∈ nbF (L - 1) (cellSide L m₀ m₁ j)
      (W.image (cbase (cellSide L m₀ m₁ j))) := by
    intro t ht
    obtain ⟨c, hcA, hcn⟩ := exists_near_of_mem hN hj h (hT t ht).1 (hT t ht).2
    exact mem_nbF.2 ⟨c, hcA, hcn⟩
  refine Finset.mem_biUnion.2 ⟨W.image (cbase (cellSide L m₀ m₁ j)),
    image_mem_Acand hN hj h ht0 ht0Z hcost, Finset.mem_product.2 ⟨Finset.mem_powerset.2 hT', ?_⟩⟩
  refine Finset.mem_powerset.2 fun u hu => ?_
  obtain ⟨t, htT, hn⟩ := hU u hu
  exact mem_nbF.2 ⟨t, hT' t htT, hn⟩

open Classical in
/-- **(G2), polymers.**  For a `π_j`-cube `□ ⊆ Ω` and `κ₀ ≥ a_ent + 1`:
`∑_{X ⊇ □, X ∈ 𝒟_j(mod Ω^c)} e^{-κ₀ d^cov_j(X mod Ω^c)} ≤ K₀`. -/
theorem G2_X (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {Ω : Set (CTorus d L N₁ m₁ K)}
    (hΩ : IsPiUnion m₀ j Ω) {t0 : CTorus d L N₁ m₁ K} (ht0 : Aligned (cellSide L m₀ m₁ j) t0)
    (ht0Ω : box t0 (cellSide L m₀ m₁ j) ⊆ Ω) {κ₀ : ℝ} (hκ : aEnt d L + 1 ≤ κ₀) :
    ∑ X ∈ Finset.univ.filter (fun X : Set (CTorus d L N₁ m₁ K) =>
        DjMod m₀ j Ω X ∧ box t0 (cellSide L m₀ m₁ j) ⊆ X),
      Real.exp (-κ₀ * dcovMod m₀ j Ω X) ≤ K0 d L κ₀ := by
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  refine sum_exp_le _ _ (fun X _ => dcovMod_nonneg _ _) (aEnt_nonneg d L) hκ (fun ℓ => ?_)
  refine le_trans ?_ (card_famT_le_exp L (cellSide L m₀ m₁ j) ℓ t0)
  have hsub : (Finset.univ.filter (fun X : Set (CTorus d L N₁ m₁ K) =>
        DjMod m₀ j Ω X ∧ box t0 (cellSide L m₀ m₁ j) ⊆ X)).filter
        (fun X => dcovMod m₀ j Ω X < ℓ + 1) ⊆
      (famT L (cellSide L m₀ m₁ j) (3 ^ d * (ℓ + 2)) t0).image
        (fun p => reconSet m₀ j Ω p.1 p.2) := by
    intro X hX
    obtain ⟨hX1, hlt⟩ := Finset.mem_filter.1 hX
    obtain ⟨hXD, hbox⟩ := (Finset.mem_filter.1 hX1).2
    obtain ⟨𝒦, W, E, hE, hc⟩ :=
      exists_admissible_eq_dcovMod (exists_admissible_of_IsDj (Ω := Ω) hXD.1)
    have ht0X : t0 ∈ X ∩ Ω := ⟨hbox (mem_box_self t0 ha0), ht0Ω (mem_box_self t0 ha0)⟩
    refine Finset.mem_image.2 ⟨(cellsIn m₀ j (X ∩ Ω), Uset m₀ j Ω X), ?_,
      (X_eq_recon hN hj hΩ hXD hbox ht0Ω).symm⟩
    refine mem_famT_of_admissible hN hj hE ht0 ht0X (by rw [hc]; exact hlt) ?_ ?_
    · intro t ht
      obtain ⟨hal, hsub⟩ := mem_cellsIn.1 ht
      exact ⟨hal, hsub (mem_box_self t ha0)⟩
    · intro u hu
      exact (Finset.mem_filter.1 hu).2.2.2
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  exact_mod_cast this

omit [NeZero N₁] [NeZero L] in
theorem exists_admissible_of_ne_top {Ω X : Set (CTorus d L N₁ m₁ K)}
    (h : dcovModE m₀ j Ω X ≠ ⊤) : ∃ 𝒦 W E, ModAdmissible m₀ j Ω X 𝒦 W E := by
  by_contra hh
  exact h (le_antisymm le_top (le_iInf fun 𝒦 => le_iInf fun W => le_iInf fun E =>
    le_iInf fun h => absurd ⟨𝒦, W, E, h⟩ hh))

open Classical in
/-- **(G2), supports.**  For a `π_j`-cube `□ ⊆ Ω` and `κ₀ ≥ a_ent + 1`, summing over the sets
`S ⊆ Ω` of `π_j`-cubes containing `□` with `d_Ω(S) < ∞`:
`∑_{S ⊇ □} e^{-κ₀ d_Ω(S)} ≤ K₀`. -/
theorem G2_S (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {Ω : Set (CTorus d L N₁ m₁ K)}
    {t0 : CTorus d L N₁ m₁ K} (ht0 : Aligned (cellSide L m₀ m₁ j) t0)
    {κ₀ : ℝ} (hκ : aEnt d L + 1 ≤ κ₀) :
    ∑ S ∈ Finset.univ.filter (fun S : Set (CTorus d L N₁ m₁ K) =>
        IsPiUnion m₀ j S ∧ S ⊆ Ω ∧ box t0 (cellSide L m₀ m₁ j) ⊆ S ∧ dOmega m₀ j Ω S ≠ ⊤),
      Real.exp (-κ₀ * (dOmega m₀ j Ω S).toReal) ≤ K0 d L κ₀ := by
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  refine sum_exp_le _ _ (fun S _ => ENNReal.toReal_nonneg) (aEnt_nonneg d L) hκ (fun ℓ => ?_)
  refine le_trans ?_ (card_famT_le_exp L (cellSide L m₀ m₁ j) ℓ t0)
  have hsub : (Finset.univ.filter (fun S : Set (CTorus d L N₁ m₁ K) =>
        IsPiUnion m₀ j S ∧ S ⊆ Ω ∧ box t0 (cellSide L m₀ m₁ j) ⊆ S ∧ dOmega m₀ j Ω S ≠ ⊤)).filter
        (fun S => (dOmega m₀ j Ω S).toReal < ℓ + 1) ⊆
      (famT L (cellSide L m₀ m₁ j) (3 ^ d * (ℓ + 2)) t0).image
        (fun p => reconSet m₀ j Ω p.1 p.2) := by
    intro S hS
    obtain ⟨hS1, hlt⟩ := Finset.mem_filter.1 hS
    obtain ⟨hSU, hSΩ, hbox, hfin⟩ := (Finset.mem_filter.1 hS1).2
    have hdE : dOmega m₀ j Ω S = dcovModE m₀ j Ω (Yhat Ω S) := by
      unfold dOmega at hfin ⊢
      by_cases hcon : SiteConnected (Yhat Ω S)
      · simp [hcon]
      · simp [hcon] at hfin
    rw [hdE] at hfin hlt
    obtain ⟨𝒦, W, E, hE, he⟩ := exists_admissible_eq_dcovModE (exists_admissible_of_ne_top hfin)
    have hcost : bondCost (scaleW L m₀ m₁ j) E < ℓ + 1 := by
      have : (ENNReal.ofReal (bondCost (scaleW L m₀ m₁ j) E)).toReal = bondCost (scaleW L m₀ m₁ j) E :=
        ENNReal.toReal_ofReal (bondCost_scaleW_nonneg E)
      rw [he] at this
      rw [← this]; exact hlt
    have ht0S : t0 ∈ S := hbox (mem_box_self t0 ha0)
    have ht0Z : t0 ∈ Yhat Ω S ∩ Ω := ⟨subset_Yhat Ω S ht0S, hSΩ ht0S⟩
    refine Finset.mem_image.2 ⟨(cellsIn m₀ j S, ∅), ?_, (S_eq_recon hN hj hSU Ω).symm⟩
    refine mem_famT_of_admissible hN hj hE ht0 ht0Z hcost ?_ (by simp)
    intro t ht
    obtain ⟨hal, hsub⟩ := mem_cellsIn.1 ht
    have htS : t ∈ S := hsub (mem_box_self t ha0)
    exact ⟨hal, subset_Yhat Ω S htS, hSΩ htS⟩
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  exact_mod_cast this

end G2

end Balaban.Fluctuation
