module

public import Balaban.LargeField.R.DeltaPsiCollarChiDom
public import Balaban.LargeField.R.DeltaPsiDef
public import Balaban.LargeField.Characteristic.RealDomain
public import Balaban.Inhabited.RipeHistory
public import Balaban.Inhabited.JointL4Setting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Non-vacuity of the collar chain for the actual window

* **B1.** `Geo S n R M` requires `M = c M₁` with `c ≥ 14` and `R_j ≥ R_base`.  `geo_of_radii` builds it
  (`M₁ = 1`, `c = M`) whenever `14 ≤ M`, `R_base ≤ R_j` and `R` is nondecreasing; conversely
  `not_nonempty_geo_of_lt` (`M < 14`) and `not_nonempty_geo_of_zero_radii` (`R ≡ 0`, `R_base > 0`)
  show that no `Geo` exists in the landed ripe-window witnesses (`M = 2` for `JointWitness.setting`,
  `M = 4` for `JointL4.setting`; both with `R ≡ 0`): `no_geo_joint_witness`, `no_geo_jointL4_witness`.
* **B3.** For *any* ripe window with a `Geo`, the reference-field premises of the collar chain
  (`hdom`, `hspec`, `hwin`, `hθ1`, `hθc`, `hΛ21`) have a joint instance:
  `inner_collar_data_change_lt_actual_of_const` (constant unit field, small `K6`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section Geo

/-- **B1 (construction).**  A `Geo` exists as soon as `14 ≤ M`, `R_base ≤ R_j` and `⌊R_{j-1}⌋ ≤ ⌊R_j⌋`
(`M₁ = 1`, `c = M`). -/
theorem nonempty_geo_of (S : Setting) (n : ℕ → ℕ) (R : ℕ → ℝ) (M : ℕ) (hM : 14 ≤ M)
    (hRlow : ∀ j, S.Rb ≤ R j) (hRmono : ∀ j, ⌊R (j - 1)⌋₊ ≤ ⌊R j⌋₊) : Nonempty (Geo S n R M) :=
  haveI : NeZero M := ⟨by omega⟩
  ⟨{ M1 := 1, c := M, neM1 := ⟨one_ne_zero⟩, nec := inferInstance, hM := (mul_one M).symm, hc := hM,
     hRlow := hRlow, hRmono := hRmono }⟩

/-- **B1 (obstruction, `M`).**  `Geo S n R M` forces `14 ≤ M`. -/
theorem not_nonempty_geo_of_lt (S : Setting) (n : ℕ → ℕ) (R : ℕ → ℝ) (M : ℕ) (hM : M < 14) :
    ¬ Nonempty (Geo S n R M) := by
  rintro ⟨g⟩
  have h1 : 1 ≤ g.M1 := Nat.pos_of_ne_zero (NeZero.ne _)
  have := g.hc
  have := g.hM
  nlinarith

/-- **B1 (obstruction, radii).**  `Geo S n R M` forces `R_base ≤ R_j`, so it does not exist for the
radii `R ≡ 0` of the landed witnesses (as `R_base > 0`). -/
theorem not_nonempty_geo_of_zero_radii (S : Setting) (n : ℕ → ℕ) (M : ℕ) (hRb : 0 < S.Rb) :
    ¬ Nonempty (Geo S n JointWitness.radii M) := by
  rintro ⟨g⟩
  have := g.hRlow 0
  simp [JointWitness.radii] at this
  linarith

end Geo

section Witness

open JointWitness

/-- No `Geo` exists for the ripe-window witness `ripeWindow_nonempty` (`M = 2 < 14`, `R ≡ 0`), whatever
the side lengths and radii: the parameter that must change is `M` (to a multiple `M = c M₁`,
`c ≥ 14`) and the radii (`R_j ≥ R_base`). -/
theorem no_geo_joint_witness (n : ℕ → ℕ) (R : ℕ → ℝ) :
    ¬ Nonempty (Geo (setting jointBeta) n R (setting jointBeta).M) :=
  not_nonempty_geo_of_lt _ _ _ _ (by show (2 : ℕ) < 14; norm_num)

/-- The same for the `L = 4` setting (`M = 4`). -/
theorem no_geo_jointL4_witness (n : ℕ → ℕ) (R : ℕ → ℝ) (β : ℝ) :
    ¬ Nonempty (Geo (Inhabited.JointL4.setting β) n R (Inhabited.JointL4.setting β).M) :=
  not_nonempty_geo_of_lt _ _ _ _ (by show (4 : ℕ) < 14; norm_num)

end Witness

section AdmDelta

open Finset

/-- **`IsAdmDelta` is inhabited**: the geometric sequence `δ_i = (3/4)^i` is admissible (Lemma III.4.4)
for `L ≥ 2`, `d ≥ 3`, `ε ≥ 0` and all `k₁, k`. -/
theorem isAdmDelta_geom (d L : ℕ) (hd : 3 ≤ d) (hL : 2 ≤ L) {ε : ℝ} (hε : 0 ≤ ε) (k1 k : ℕ) :
    IsAdmDelta d L ε k1 k (fun i => (3 / 4 : ℝ) ^ i) where
  pos i _ _ := by positivity
  anti i _ _ := by
    rw [pow_succ]; have : (0 : ℝ) < (3 / 4) ^ i := by positivity
    nlinarith
  growth i j _ hij _ := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hij
    have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hbase : (4 / 3 : ℝ) ≤ (L : ℝ) ^ (((d : ℝ) - 2) / 2) := by
      have h1 : (L : ℝ) ^ ((1 : ℝ) / 2) ≤ (L : ℝ) ^ (((d : ℝ) - 2) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      refine le_trans ?_ h1
      rw [← Real.sqrt_eq_rpow]
      exact Real.le_sqrt_of_sq_le (by nlinarith)
    have hx : (L : ℝ) ^ (((d : ℝ) - 2) / 2 * (((i + m : ℕ) : ℝ) - i)) =
        ((L : ℝ) ^ (((d : ℝ) - 2) / 2)) ^ m := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      congr 1; push_cast; ring
    rw [hx]
    have h4 : (4 / 3 : ℝ) ^ m ≤ ((L : ℝ) ^ (((d : ℝ) - 2) / 2)) ^ m :=
      pow_le_pow_left₀ (by norm_num) hbase m
    have he : 1 ≤ Real.exp ε := Real.one_le_exp hε
    have h5 : (4 / 3 : ℝ) ^ m * (3 / 4) ^ m = 1 := by rw [← mul_pow]; norm_num
    have hp : (0 : ℝ) < (3 / 4) ^ i := by positivity
    have hq : (0 : ℝ) < (3 / 4) ^ m := by positivity
    calc (3 / 4 : ℝ) ^ i = 1 * (3 / 4) ^ i := (one_mul _).symm
      _ ≤ (Real.exp ε * ((L : ℝ) ^ (((d : ℝ) - 2) / 2)) ^ m * (3 / 4) ^ m) * (3 / 4) ^ i := by
        apply mul_le_mul_of_nonneg_right _ hp.le
        calc (1 : ℝ) = (4 / 3 : ℝ) ^ m * (3 / 4) ^ m := h5.symm
          _ ≤ ((L : ℝ) ^ (((d : ℝ) - 2) / 2)) ^ m * (3 / 4) ^ m := mul_le_mul_of_nonneg_right h4 hq.le
          _ ≤ _ := by
            have : 0 ≤ ((L : ℝ) ^ (((d : ℝ) - 2) / 2)) ^ m * (3 / 4) ^ m := by positivity
            nlinarith
      _ = _ := by rw [pow_add]; ring
  tail i _ hik := by
    have key : ∀ k, i ≤ k → ∑ n ∈ Icc i k, (3 / 4 : ℝ) ^ n = 4 * ((3 / 4) ^ i - (3 / 4) ^ (k + 1)) := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => simp; ring
      | succ k hk ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih]; ring
    rw [key k hik]
    have : (0 : ℝ) ≤ (3 / 4) ^ (k + 1) := by positivity
    linarith

end AdmDelta

section Const

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-- The constant unit field satisfies `PsiZeroSpec` for itself as `ψ` and `ψ⁰` (any `θ > 0`). -/
theorem psiZeroSpec_const (Gk : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')
    (Zf : Set (Torus d (N₀ * L ^ k))) {θ : ℝ} (hθ : 0 < θ) (hN : 0 < N) :
    PsiZeroSpec Gk G' Zf θ
      (fun _ => EuclideanSpace.single (⟨0, hN⟩ : Fin N) (1 : ℝ))
      (fun _ => EuclideanSpace.single (⟨0, hN⟩ : Fin N) (1 : ℝ)) := by
  refine ⟨Set.univ, fun _ _ => trivial, fun _ _ => trivial, ⟨?_, ?_⟩, fun _ _ => rfl⟩
  · intro y _ y' _ _; simpa using hθ
  · intro y _; simpa using hθ

/-- The constant unit field satisfies `WinBond` for positive `c δ_i`. -/
theorem winBond_const (G : GeneratingSet d L N₀ k ϱ) (Zc Zf : Set (Torus d (N₀ * L ^ k)))
    (k1 : ℕ) {c : ℝ} {δ : ℕ → ℝ} (hc : 0 < c) (hδ : ∀ i, 0 < δ i) (hN : 0 < N) :
    WinBond G Zc Zf k1 c δ (fun _ => EuclideanSpace.single (⟨0, hN⟩ : Fin N) (1 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro i u v _ _ _; simpa using mul_pos hc (hδ i)
  · intro i u v _ _ _; simpa using mul_pos hc (hδ i)

/-- Three smallness conditions `K a_i ≤ b_i` hold for a small positive `K`. -/
theorem exists_small_K (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) :
    ∃ K : ℝ, 0 < K ∧ K * a1 ≤ b1 ∧ K * a2 ≤ b2 ∧ K * a3 ≤ b3 := by
  have key : ∀ a b : ℝ, 0 ≤ a → 0 < b → ∀ K, K ≤ b / (a + 1) → 0 ≤ K → K * a ≤ b := by
    intro a b ha hb K hK hK0
    have h1 : K * (a + 1) ≤ b := by
      have := mul_le_mul_of_nonneg_right hK (by linarith : (0 : ℝ) ≤ a + 1)
      rwa [div_mul_cancel₀ _ (by linarith : a + 1 ≠ 0)] at this
    nlinarith
  refine ⟨min (b1 / (a1 + 1)) (min (b2 / (a2 + 1)) (b3 / (a3 + 1))), ?_, ?_, ?_, ?_⟩
  · refine lt_min (by positivity) (lt_min (by positivity) (by positivity))
  · exact key a1 b1 ha1 hb1 _ (min_le_left _ _) (by positivity)
  · exact key a2 b2 ha2 hb2 _ ((min_le_right _ _).trans (min_le_left _ _)) (by positivity)
  · exact key a3 b3 ha3 hb3 _ ((min_le_right _ _).trans (min_le_right _ _)) (by positivity)

end Const

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} {k : ℕ} {Z : H.Comp k} [NeZero S.L] [NeZero S.M]

/-- **B3.  The collar-datum bound (2.3) at the constant reference field, for any ripe window with a
`Geo`** (COLLAR-FIX (2.3); LF-RECONSTRUCTION III.4.6): for the constant unit field `ψ = ψ⁰ = e₀` (which
lies in the support of the retained characteristic functions, `chiDomProp_const`, and satisfies
`PsiZeroSpec` and `WinBond`), there is a `K6 > 0` such that every `c ∈ C_in` satisfies
`|D^ph.Ψ(c) - D⁰.Ψ(c)| < (3dL + 2) Ŵ_k δ_{k₁}`.  The reference-field premises
`hdom hspec hwin hθ1 hθc hΛ21 hΛ21'` are discharged; what remains is the source setting, the
admissible tolerance sequence, and the typing of the background (`hprec`, `hBg`). -/
theorem inner_collar_data_change_lt_actual_of_const
    (hG : S.Good) (hkK : k ≤ K) (hW : H.RipeWindow k Z) (g : Geo S n R S.M)
    (hk0 : k ≤ k0) (hrip : S.Ripe k (H.bk k Z)) (hq1 : 1 ≤ (H.bk k Z).q)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.numax j * (S.crit j + S.omega j) + 4 ≤ n j)
    (hϱ : (2 * S.d * S.L : ℝ) ≤ (S.L : ℝ) * S.M * S.Rb)
    {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k) k δ)
    (hδ' : IsAdmDelta S.d S.L ε (S.k1 k - 1) (S.k1 k) δ) (hδpos : ∀ j, 0 < δ j)
    {a₁ : ℝ}
    (hprec : Precedes ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW))
      (windowOfHistory H Z g hkK hW).bdry)
    (hBg : BgHyp S.d S.L k (winSep g) (compWeight S.L a₁) 0)
    {N : ℕ} (hN : 0 < N) (h : Fin N → ℝ) :
    ∃ K6 : ℝ, 0 < K6 ∧ ∀ c ∈ collarIn (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW),
      vn (deltaPsiColl (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)
          (windowOfHistory_parentRefines H Z g hkK hW) hprec (compWeight S.L a₁)
          (fun _ => EuclideanSpace.single (⟨0, hN⟩ : Fin N) (1 : ℝ))
          (fun _ => EuclideanSpace.single (⟨0, hN⟩ : Fin N) (1 : ℝ)) h c) <
        (3 * S.d * S.L + 2) * S.hatW ε k * δ (S.k1 k) := by
  have hS := H.F.ok
  have hd : 0 < S.d := by have := hS.three_le_d; omega
  have hδk := hδpos k
  have hC1 := bgC1_pos_of (d := S.d) (L := S.L) (N := N) hd
  have hK1 := bgK1_pos S.d S.L N
  have hcrit : (0 : ℝ) < S.crit k := by
    have : 0 < S.crit k := by unfold Setting.crit; omega
    exact_mod_cast this
  have hLpos : (0 : ℝ) < S.L := hS.hatW_pos_L
  have hMpos : (0 : ℝ) < S.M := by exact_mod_cast hS.one_le_M
  have hWpos : 0 < S.hatW ε k := by
    have hexp := Real.exp_pos ε
    have hdR : (0 : ℝ) < S.d := by exact_mod_cast hd
    have hX : 0 < 8 * (S.d : ℝ) * S.L * Real.exp ε * ((S.L : ℝ) * S.M * (S.crit k : ℝ)) ^ S.d := by
      positivity
    exact lt_of_lt_of_le hX (hS.hatW_ge ε k)
  obtain ⟨K6, hK6, h1, h2, h3⟩ := exists_small_K (3 * δ k) (9 * δ k)
    (3 * S.d * (S.M * S.crit k) + 18 * bgK1 S.d S.L N) 1 (bgC1 S.d S.L N) (S.hatW ε k)
    (by positivity) (by positivity) (by positivity) one_pos hC1 hWpos
  refine ⟨K6, hK6, fun c hc => ?_⟩
  have hθ0 : 0 < 3 * K6 * δ k := by positivity
  exact inner_collar_data_change_lt_actual_of_chiDom (g := g) (Zc := Set.univ) hG hkK hW hk0 hrip hq1 hT hϱ hδ hprec hBg
    (fun _ => EuclideanSpace.single (⟨0, hN⟩ : Fin N) (1 : ℝ)) h
    (fun _ _ => EuclideanSpace.single (⟨0, hN⟩ : Fin N) (1 : ℝ)) (fun _ _ => (0 : EuclideanSpace ℝ (Fin N)))
    (chiDomProp_const hd hN _ k _ Set.univ δ (fun _ => 1) 1 hδpos (fun _ => one_pos) one_pos)
    hδ' hK6 (by linarith) (by linarith) (psiZeroSpec_const _ _ _ hθ0 hN)
    (winBond_const _ _ _ _ (by positivity) hδpos hN) (by nlinarith) hc

end RegionHistory

end Balaban.LargeField
