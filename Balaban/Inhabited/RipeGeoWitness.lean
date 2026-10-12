/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RadiiHist
public import Balaban.Inhabited.RadiiSetting
public import Balaban.LargeField.R.WindowOfHistory
public import Balaban.Inhabited.WindowCollarWitness

/-!
# The actual window of a ripe component, instantiated

The genuine-radii family (`RadiiSet`, `RadiiHist`): `d = L = 3`, `M = 14 M₁`, `R_base = 32`,
`R_j = R_base λ_j²`, so `Geo` holds with `c = 14` (`RadiiSet.wGeo`; LF-RECONSTRUCTION §I.1.3: the
order of constants `M = c M₁`, `c ≥ 14`, `R_j ≥ R_base`).  The history `RadiiHist.histT` has a ripe
component `Z` at scale `T = t^*`.  Here the window of Definition III.2.1 (`windowOfHistory`) is formed
for it and the landed geometric theorems of Lemma III.1.2 are applied to it.
-/

@[expose] public section

namespace Balaban.Inhabited.RipeGeo

open Balaban Balaban.LargeField Balaban.Inhabited Balaban.Multiscale Balaban.Background

/-- The setting. -/
noncomputable abbrev S0 : Setting := RadiiSet.wS

instance : NeZero S0.M := ⟨by
  show 14 * RadiiSet.M1 ≠ 0
  have := RadiiSet.M1_pos; omega⟩

/-- The scale of the ripe component. -/
noncomputable abbrev T : ℕ := RadiiHist.Tstar S0

/-- A side factor with `4 ρ_j + 21 ≤ n_j` (ripeness) and `4 ν_max(j) (crit_j + ω_j) + 4 ≤ n_j`
(the premise `hT` of the collar bound), `1 ≤ j ≤ T`. -/
noncomputable def N1 : ℕ :=
  RadiiHist.bigN S0 + ∑ j ∈ Finset.range (T + 1), (4 * S0.numax j * (S0.crit j + S0.omega j) + 4)

instance : NeZero N1 := ⟨by have := (inferInstance : NeZero (RadiiHist.bigN S0)).out; unfold N1; omega⟩

/-- The side lengths `n_k = N₁ L^{T-k}`. -/
noncomputable abbrev n0 : ℕ → ℕ := RadiiHist.side S0 N1 T

/-- The history with `K = k₀ = T`. -/
noncomputable abbrev H0 : RegionHistory S0 n0 RadiiSet.wR T T :=
  RadiiHist.histT RadiiSet.wS_ok le_rfl le_rfl RadiiSet.wRH N1

theorem N1_le_side (k : ℕ) : N1 ≤ n0 k := by
  unfold n0 RadiiHist.side
  exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne _)))

theorem hT0 : ∀ j, 1 ≤ j → j ≤ T →
    4 * S0.numax j * (S0.crit j + S0.omega j) + 4 ≤ n0 j := by
  intro j _ hj
  have hk' : j ∈ Finset.range (T + 1) := Finset.mem_range.mpr (by omega)
  have h1 := Finset.single_le_sum (f := fun j => 4 * S0.numax j * (S0.crit j + S0.omega j) + 4)
    (fun _ _ => Nat.zero_le _) hk'
  have := N1_le_side j
  unfold N1 at this
  omega

theorem hT0' : ∀ j, 1 ≤ j → j ≤ T → 4 * S0.rho j + 21 ≤ n0 j := by
  intro j _ hj
  have hk' : j ∈ Finset.range (T + 1) := Finset.mem_range.mpr (by omega)
  have h1 := Finset.single_le_sum (f := fun j => 4 * S0.rho j + 21)
    (fun _ _ => Nat.zero_le _) hk'
  have h3 : RadiiHist.bigN S0 = 1 + ∑ j ∈ Finset.range (T + 1), (4 * S0.rho j + 21) := rfl
  have := N1_le_side j
  unfold N1 at this
  omega

theorem exists_ripe0 : ∃ c : H0.Comp T, S0.Ripe T (H0.bk T c) := by
  obtain ⟨c, -, h⟩ := RadiiHist.exists_ripe RadiiSet.wS_ok (le_refl _) (le_refl _) RadiiSet.wRH N1
  exact ⟨c, h⟩

/-- The ripe component. -/
noncomputable def Z0 : H0.Comp T := exists_ripe0.choose

theorem hrip0 : S0.Ripe T (H0.bk T Z0) := exists_ripe0.choose_spec

theorem hW0 : H0.RipeWindow T Z0 :=
  RegionHistory.ripe_window RadiiSet.wS_good hT0' le_rfl le_rfl hrip0

/-- The datum `Geo` of the witness: `M = 14 M₁`, `R_j = 32 λ_j² ≥ R_base`. -/
noncomputable def g0 : Geo S0 n0 RadiiSet.wR S0.M := RadiiSet.wGeo n0

theorem hkK0 : T ≤ T := le_rfl

/-- **A ripe window together with a `Geo`** (with `3 ≤ L`). -/
theorem exists_ripeWindow_geo :
    ∃ (S : Setting) (n : ℕ → ℕ) (_ : ∀ k, NeZero (n k)) (R : ℕ → ℝ) (k0 K : ℕ)
      (H : RegionHistory S n R k0 K) (k : ℕ) (Z : H.Comp k),
      S.Good ∧ 3 ≤ S.L ∧ H.RipeWindow k Z ∧ Nonempty (Geo S n R S.M) :=
  ⟨S0, n0, inferInstance, RadiiSet.wR, T, T, H0, T, Z0, RadiiSet.wS_good, le_refl _, hW0,
    ⟨g0⟩⟩

/-- The window of the ripe component. -/
noncomputable abbrev W0 := H0.windowOfHistory Z0 g0 hkK0 hW0

/-- `Hyp` for the window of the witness (Lemma III.1.2, Definition III.2.1). -/
theorem W0_hyp : W0.Hyp := H0.windowOfHistory_hyp hkK0 hW0

/-- The generating set of the window. -/
noncomputable abbrev G0 := W0.windowGenSet W0_hyp

theorem W0_hZ : W0.Zk1 ⊆ W0.Z := H0.windowOfHistory_hZ (g := g0) hkK0 hW0

theorem W0_hOmK1 : ∀ x, x ∉ W0.Zk1 → x ∈ W0.full.Ω 1 :=
  H0.windowOfHistory_hOmK1 (g := g0) hkK0 hW0

theorem W0_hOmK : ∀ x, x ∉ W0.Z → x ∈ W0.full.Ω T :=
  H0.windowOfHistory_hOmK (g := g0) hkK0 hW0 (RadiiHist.one_le_Tstar S0)

theorem W0_hZk1top : ∀ x ∈ W0.Zk1, x ∉ W0.full.Ω (S0.k1 T + 1) :=
  H0.windowOfHistory_hZk1top (g := g0) hkK0 hW0

theorem W0_hsupp : ∀ x ∈ W0.bdry.Ω 1, x ∈ W0.Unb :=
  H0.windowOfHistory_hsupp (g := g0) hkK0 hW0

theorem W0_hbdry : ∀ m, 1 ≤ m → m ≤ T → W0.bdry.Ω m ∩ (W0.Unb \ W0.Z) ⊆ W0.full.Ω m :=
  H0.windowOfHistory_hbdry (g := g0) hkK0 hW0

theorem W0_hmargin : ∀ x ∈ G0.Ω 1, ∀ c, Adj x c → c ∈ W0.Zk1 → c ∈ W0.full.Ω (S0.k1 T) :=
  H0.windowOfHistory_hmargin (g := g0) hkK0 hW0

theorem W0_hcore : ∀ m, 1 ≤ m → m ≤ T → W0.core.Ω m ∩ W0.Zk1 ⊆ W0.full.Ω m :=
  H0.windowOfHistory_hcore (g := g0) hkK0 hW0

theorem W0_hexitLayer :
    ∀ x, x ∉ W0.Zk1 → ∀ c, Adj x c → c ∈ W0.Zk1 → x ∈ W0.full.layer (S0.k1 T) :=
  H0.windowOfHistory_hexitLayer (g := g0) hkK0 hW0

/-! ### The premises of the collar bound at the witness -/

theorem Z_sub_bdry_top : ∀ x ∈ W0.Z, x ∈ W0.bdry.Ω T := by
  intro x hx
  rw [H0.windowOfHistory_Z (g := g0) hkK0 hW0, RegionHistory.mem_locFineFin,
    RegionHistory.mem_locFine_k hkK0] at hx
  refine RegionHistory.windowBdry_top_mem (g := g0) ?_
  unfold RegionHistory.bdryU thick
  exact subset_nbhd _ _ hx

/-- `hprec`: the window generating set precedes the boundary piece (every layer of the glued set is
inside the same layer of `𝔹_k(U_k)`, since `Z_{k₁} ⊆ Z ⊆ Ω_k(𝔹_k(U_k))`). -/
theorem W0_precedes : Precedes G0 W0.bdry := by
  intro i hi1 hik x hx
  rw [WindowPieces.windowGenSet_Ω] at hx
  have hZ : x ∈ W0.Z → x ∈ W0.bdry.Ω i := fun h =>
    W0.bdry.Ω_antitone hi1 hik (by omega) (Z_sub_bdry_top x h)
  rcases Finset.mem_union.1 hx with h | h
  · rcases Finset.mem_union.1 h with h | h
    · exact hZ (W0_hZ (Finset.mem_inter.1 h).2)
    · exact hZ (Finset.mem_sdiff.1 (Finset.mem_inter.1 h).2).1
  · exact (Finset.mem_inter.1 h).1

theorem M1_real_pos : (1 : ℝ) ≤ RadiiSet.M1 := by exact_mod_cast RadiiSet.M1_pos

/-- `winSep` of the witness is at least `R₀(3,3)`: `min (L M R_base, 5 L M₁) = 15 M₁ ≥ R₀(3,3)`. -/
theorem bgR0_le_winSep : Balaban.Background.bgR0 3 3 ≤ RegionHistory.winSep g0 := by
  unfold RegionHistory.winSep
  refine le_min ?_ ?_
  · have := RadiiSet.bgR0_le_minSep
    show _ ≤ ((3 : ℕ) : ℝ) * ((14 * RadiiSet.M1 : ℕ) : ℝ) * 32
    push_cast at this ⊢; nlinarith [M1_real_pos]
  · have := RadiiSet.bgR0_le_minSep
    unfold minSep
    show _ ≤ 5 * ((3 : ℕ) : ℝ) * ((RadiiSet.M1 : ℕ) : ℝ)
    push_cast at this ⊢; linarith

theorem compWeight_mem (r : ℕ) (hr : 1 ≤ r) :
    Balaban.Background.compWeight 3 1 r ∈ Set.Icc (1 / 2 : ℝ) 2 := by
  unfold Balaban.Background.compWeight
  have h9 : (9 : ℝ) ≤ (((3 : ℕ) : ℝ) ^ r) ^ 2 := by
    have : (3 : ℝ) ≤ ((3 : ℕ) : ℝ) ^ r := by
      have := pow_le_pow_right₀ (show (1 : ℝ) ≤ ((3 : ℕ) : ℝ) by norm_num) hr
      simpa using this
    nlinarith
  have hpos : 0 < (((3 : ℕ) : ℝ) ^ r) ^ 2 := by linarith
  have hinv : ((((3 : ℕ) : ℝ) ^ r) ^ 2)⁻¹ ≤ 1 / 9 := by
    rw [inv_le_comm₀ hpos (by norm_num)]; simpa using h9
  have hinv0 : 0 < ((((3 : ℕ) : ℝ) ^ r) ^ 2)⁻¹ := inv_pos.2 hpos
  have hD : 0 < 1 - ((((3 : ℕ) : ℝ) ^ r) ^ 2)⁻¹ := by linarith
  have hnum : (1 - ((((3 : ℕ) : ℝ) ^ 2)⁻¹)) = 8 / 9 := by norm_num
  rw [hnum]
  constructor
  · rw [le_div_iff₀ hD]; nlinarith
  · rw [div_le_iff₀ hD]; nlinarith

/-- `BgHyp` of the witness at the separation `winSep` and mass `0` (any scale). -/
theorem bgHyp_W0 (k : ℕ) :
    Balaban.Background.BgHyp 3 3 k (RegionHistory.winSep g0) (Balaban.Background.compWeight 3 1) 0 where
  hd := le_rfl
  hL := le_rfl
  hϱ := bgR0_le_winSep
  weights := fun j h1 _ => compWeight_mem j h1
  mass := le_rfl
  massLe := by simp

/-- **The collar bound (2.3) at the actual window of the ripe component of the genuine-radii
witness**: all premises (`hG`, `hrip`, `hq1`, `hT`, `hϱ`, `hprec`, `hBg`) are discharged.  The
conclusion is vacuous unless the inner collar is nonempty. -/
theorem collar_bound_W0 {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S0.d S0.L ε (S0.k1 T) T δ)
    (hδ' : IsAdmDelta S0.d S0.L ε (S0.k1 T - 1) (S0.k1 T) δ) (hδpos : ∀ j, 0 < δ j)
    {N : ℕ} (hN : 0 < N) (h : Fin N → ℝ) :
    ∃ K6 : ℝ, 0 < K6 ∧ ∀ c ∈ collarIn W0 W0_hyp,
      vn (deltaPsiColl W0 W0_hyp (H0.windowOfHistory_parentRefines Z0 g0 hkK0 hW0) W0_precedes
          (compWeight S0.L 1) (fun _ => EuclideanSpace.single (⟨0, hN⟩ : Fin N) (1 : ℝ))
          (fun _ => EuclideanSpace.single (⟨0, hN⟩ : Fin N) (1 : ℝ)) h c) <
        (3 * S0.d * S0.L + 2) * S0.hatW ε T * δ (S0.k1 T) :=
  H0.inner_collar_data_change_lt_actual_of_const RadiiSet.wS_good hkK0 hW0 g0 le_rfl hrip0
    (by rw [← hW0.core_k1]; exact hW0.k1_pos hkK0) hT0
    (by
      show (2 * 3 * 3 : ℝ) ≤ ((3 : ℕ) : ℝ) * ((14 * RadiiSet.M1 : ℕ) : ℝ) * 32
      push_cast; nlinarith [M1_real_pos])
    hδ hδ' hδpos W0_precedes (bgHyp_W0 T) hN h

end Balaban.Inhabited.RipeGeo
