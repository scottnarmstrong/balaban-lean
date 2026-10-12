module

public import Balaban.LargeField.R.DeltaPsiCollarActual
public import Balaban.LargeField.R.DeltaPsiCollarInner
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The inner-collar data change (2.3) at the actual window, without `hcoreTop`

* `inner_collar_data_change_lt_of_shell`: the Lemma-CH / final-comparison half of COLLAR-FIX (2.3)
  for a window whose parent spin at the collar site is already within `Ŵ_k δ_{k₁}` of a window block
  (the shell bound (2.2)); the proof is that of `inner_collar_data_change_lt_of_coreTop`, whose only use of
  `hcoreTop` was inside `inner_collar_shell_bound`;
* `inner_collar_data_change_lt_actual`, `inner_collar_data_change_bound_actual`: (2.3) for
  `windowOfHistory H Z g hkK hW`, constants `3dL + 2` (strict) and `3dL + 3`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} {k : ℕ} {Z : H.Comp k} [NeZero S.L] [NeZero S.M]

/-- **The Lemma-CH / final-comparison step, abstract in the site** (LFR III.4.6; the common part of the
interior bound at a core site and of (2.3) at a collar site).  For a site `c ∈ Z_{k₁}` with a block `P`
whose spin is within `Ŵ_k δ_{k₁}` of a window block (`hshell`), a value
`Dv = ψ(P) - C` where `C` is within `2 K₁ · 3θ` of the block value `ψ⁰_k(b_k(c))` (`hcmp`: the
comparison (2.43) of `psiZeroWin_sub_le`, or of `psiZeroWin_collar_sub_le` at a collar site), one has
`|Dv| < (3dL + 2) Ŵ_k δ_{k₁}`. -/
theorem data_change_lt_of_shell_site
    (hG : S.Good) (hkK : k ≤ K) (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j)
    (hk0 : k ≤ k0) (hrip : S.Ripe k (H.bk k Z)) (hq1 : 1 ≤ (H.bk k Z).q)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.numax j * (S.crit j + S.omega j) + 4 ≤ n j)
    (hϱ : (2 * S.d * S.L : ℝ) ≤ (S.L : ℝ) * S.M * S.Rb)
    {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k) k δ)
    {N : ℕ} (ψ ψ0 : BlockV S.d S.L (S.M * n k) k → EuclideanSpace ℝ (Fin N))
    {K6 : ℝ} (hK6 : 0 < K6) (hθ1 : 3 * K6 * δ k ≤ 1)
    {ϱb : ℝ} (Gb : GeneratingSet S.d S.L (S.M * n k) k ϱb)
    (hspec : PsiZeroSpec (H.locGen Z S.M hkK hL hR) Gb (H.locFine Z S.M k) (3 * K6 * δ k) ψ ψ0)
    (hwin : WinBond (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (H.locFine Z S.M k)
      (S.k1 k) (3 * S.d * S.L) δ ψ)
    (hΛ21 : 3 * S.d * K6 * (S.M * S.crit k) + 2 * (bgK1 S.d S.L N * (3 * (3 * K6))) ≤ S.hatW ε k)
    {c : Torus S.d (S.M * n k * S.L ^ k)} (hcZ1 : c ∈ H.locFine Z S.M (S.k1 k))
    (P : BlockV S.d S.L (S.M * n k) k) (Dv C : Fin N → ℂ)
    (hdel : Dv = (fun i => ((ψ P i : ℝ) : ℂ)) - C)
    (hcmp : vn (C - fun i => ((ψ0 ⟨k, jBlock S.d S.L (S.M * n k) k k c⟩ i : ℝ) : ℂ)) ≤
      2 * (bgK1 S.d S.L N * (3 * (3 * K6 * δ k))))
    (hshell : ∃ s ∈ (H.locGen Z S.M hkK hL hR).layer (S.k1 k), s ∉ H.locFine Z S.M (S.k1 k) ∧
      dist (ψ P) (ψ (blockOf S.d S.L (S.M * n k) k (S.k1 k) s)) ≤ S.hatW ε k * δ (S.k1 k)) :
    vn Dv < (3 * S.d * S.L + 2) * S.hatW ε k * δ (S.k1 k) := by
  classical
  have hS := H.F.ok
  have hW : H.RipeWindow k Z :=
    ripe_window hG (fun j hj1 hj0 => (hT_forms hS (hT j hj1 hj0)).1) hk0 hkK hrip
  have hqk1 : S.k1 k = (H.bk k Z).q := hW.core_k1
  have hk1 : 1 ≤ S.k1 k := by rw [hqk1]; exact hq1
  have hkq : S.k1 k < k := by
    rw [hqk1]
    have := hW.core_window.1
    have : 1 ≤ S.nq (H.bk k Z).q := by unfold Setting.nq; omega
    omega
  have hd1 : 1 ≤ S.d := by have := hS.three_le_d; omega
  have hcZ : c ∈ H.locFine Z S.M k := locFine_mono hkK hkq.le le_rfl hcZ1
  have hnn := hnn_k H hkK
  have hblk : ∀ x x' : Torus S.d (S.M * n k * S.L ^ k),
      jBlock S.d S.L (S.M * n k) k (S.k1 k) x = jBlock S.d S.L (S.M * n k) k (S.k1 k) x' →
        (x ∈ H.locFine Z S.M (S.k1 k) ↔ x' ∈ H.locFine Z S.M (S.k1 k)) := by
    intro x x' h
    have h1 := cubeMap_eq_of_jBlock_eq (S := S) (n := n) (M := S.M) (k := k) hnn
      (m := S.k1 k) (j := S.k1 k) le_rfl hkq.le h
    show cubeMap n S.L S.M k (S.k1 k) x ∈ ((H.locRH k Z).step (S.k1 k)).Z ↔
      cubeMap n S.L S.M k (S.k1 k) x' ∈ ((H.locRH k Z).step (S.k1 k)).Z
    rw [h1]
  have hΩ : ∀ x ∈ H.locFine Z S.M (S.k1 k), x ∉ (H.locGen Z S.M hkK hL hR).Ω (S.k1 k + 1) :=
    fun x hx => locFine_not_mem_Omega (hkK := hkK) (hL := hL) (hR := hR) hkq hx
  have hT2 : ∀ j, 1 ≤ j → j ≤ k0 → 2 * S.crit j + 5 ≤ n j :=
    fun j hj1 hj0 => (hT_forms hS (hT j hj1 hj0)).2
  have hZfar : ∀ z ∈ H.locFine Z S.M (S.k1 k), ∀ y ∈ (H.locGen Z S.M hkK hL hR).Ω (S.k1 k + 1),
      (2 * S.d * (S.L : ℝ) ^ (S.k1 k + 1) : ℝ) <
        Green.torusDist S.d (S.M * n k * S.L ^ k) z y := fun z hz y hy =>
    locFine_far (hkK := hkK) (hL := hL) (hR := hR) hϱ hk1 hkq hz hy
  have hδpos : ∀ i, S.k1 k ≤ i → i < k → 0 < δ i := fun i h1 h2 => hδ.pos i h1 h2.le
  have hc3 : (0 : ℝ) < 3 * S.d * S.L := by
    have : (1 : ℝ) ≤ S.d := by exact_mod_cast hd1
    have : (2 : ℝ) ≤ S.L := by exact_mod_cast hL
    positivity
  have hδk1 := hδ.pos (S.k1 k) le_rfl hkq.le
  obtain ⟨s, hsl', hsZ', hcore⟩ := hshell
  have hyw : IsWindowBlock (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (S.k1 k)
      (blockOf S.d S.L (S.M * n k) k (S.k1 k) s) :=
    isWindowBlock_blockOf (H.locGen Z S.M hkK hL hR) hblk hΩ hk1 le_rfl hkq hsl' hsZ'
  obtain ⟨len, xs, hx0, hwinb, hterm, hadj, hinj, hdist⟩ :=
    lemmaCH_of_ripe hG hkK hL hR hk0 hrip hT hδ hc3 ψ
      (fun u v hu hv huv => winBond_intra hwin u v hu hv huv)
      (fun u v hu hv huv => winBond_cross hϱ hd1 hL (H.locGen Z S.M hkK hL hR) hk1 hZfar hc3
        hδpos hwin u v hu hv huv) hkq hyw rfl
  obtain ⟨Ut, hZUt, -, hreg, hagree⟩ := hspec
  generalize hyk : xs len = yk at hterm hdist
  obtain ⟨ik, β⟩ := yk
  obtain ⟨hik, hall⟩ := hterm
  simp only at hik
  subst hik
  obtain ⟨s', hs'⟩ := exists_site_of_block (d := S.d) (L := S.L) (N₀ := S.M * n ik) (k := ik)
    (j := ik) le_rfl β
  have hsZ'' : s' ∈ H.locFine Z S.M ik := (hall s' hs').2
  have hψk : ψ0 ⟨ik, β⟩ = ψ ⟨ik, β⟩ := hagree _ ⟨rfl, hall⟩
  have hθ0 : 0 < 3 * K6 * δ ik := by
    have := hδ.pos ik (by omega) le_rfl
    positivity
  obtain ⟨m', hm', hr⟩ := zblocks_reach (H := H) (Z := Z) hkK (by omega) hk0 hW
    (by have := hT2 ik (by omega) hk0; omega) ⟨s', hsZ'', hs'⟩ ⟨c, hcZ, rfl⟩
  have hPU : {γ | ∃ x ∈ H.locFine Z S.M ik, jBlock S.d S.L (S.M * n ik) ik ik x = γ} ⊆ Ut := by
    rintro γ ⟨x', hx', rfl⟩
    exact hZUt x' hx'
  have hD2 := psi0_dist_le hPU hθ0 hreg hr
  have hmR' : (m' : ℝ) ≤ S.d * (S.M * S.crit ik) := by exact_mod_cast hm'
  have t1 := vn_triangle (fun i => ((ψ P i : ℝ) : ℂ)) (fun i => ((ψ ⟨ik, β⟩ i : ℝ) : ℂ)) C
  have t2 := vn_triangle (fun i => ((ψ ⟨ik, β⟩ i : ℝ) : ℂ))
    (fun i => ((ψ0 ⟨ik, jBlock S.d S.L (S.M * n ik) ik ik c⟩ i : ℝ) : ℂ)) C
  have e1 : vn ((fun i => ((ψ P i : ℝ) : ℂ)) - fun i => ((ψ ⟨ik, β⟩ i : ℝ) : ℂ)) =
      dist (ψ P) (ψ ⟨ik, β⟩) := vn_cast_sub _ _
  have e2 : vn ((fun i => ((ψ ⟨ik, β⟩ i : ℝ) : ℂ)) -
      fun i => ((ψ0 ⟨ik, jBlock S.d S.L (S.M * n ik) ik ik c⟩ i : ℝ) : ℂ)) =
      dist (ψ0 ⟨ik, β⟩) (ψ0 ⟨ik, jBlock S.d S.L (S.M * n ik) ik ik c⟩) := by
    rw [← hψk]; exact vn_cast_sub _ _
  have e3 := vn_sub_comm (fun i => ((ψ0 ⟨ik, jBlock S.d S.L (S.M * n ik) ik ik c⟩ i : ℝ) : ℂ)) C
  have hD3' := hcmp
  rw [hdel]
  have hδk := hδ.pos ik (by omega) le_rfl
  have hδj := hδ.pos (S.k1 ik) le_rfl hkq.le
  have hδkj : δ ik ≤ δ (S.k1 ik) := hδ.le_of_le le_rfl hkq.le
  have hWpos : 0 < S.hatW ε ik := by
    by_contra hneg
    push Not at hneg
    have h0 := lt_of_le_of_lt dist_nonneg hdist
    have : S.hatW ε ik * (3 * S.d * S.L) * δ (S.k1 ik) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hneg hc3.le) hδj.le
    linarith
  have hK1 := bgK1_pos S.d S.L N
  have hθm : (m' : ℝ) * (3 * K6 * δ ik) ≤ S.d * (S.M * S.crit ik) * (3 * K6 * δ ik) :=
    mul_le_mul_of_nonneg_right hmR' hθ0.le
  have hΛ' : (3 * S.d * K6 * (S.M * S.crit ik) + 2 * (bgK1 S.d S.L N * (3 * (3 * K6)))) * δ ik ≤
      S.hatW ε ik * δ ik := mul_le_mul_of_nonneg_right hΛ21 hδk.le
  have hWδ : S.hatW ε ik * δ ik ≤ S.hatW ε ik * δ (S.k1 ik) := mul_le_mul_of_nonneg_left hδkj hWpos.le
  have hT0 : 0 < S.hatW ε ik * δ (S.k1 ik) := mul_pos hWpos hδj
  have eW : S.hatW ε ik * (3 * S.d * S.L) * δ (S.k1 ik) = 3 * S.d * S.L * (S.hatW ε ik * δ (S.k1 ik)) := by ring
  have hBK : 0 ≤ bgK1 S.d S.L N * (3 * (3 * K6 * δ ik)) := by positivity
  have t0 := dist_triangle (ψ P) (ψ (blockOf S.d S.L (S.M * n ik) ik (S.k1 ik) s)) (ψ ⟨ik, β⟩)
  nlinarith [hdist, hD2, hD3', hθm, hΛ', hWδ, hT0, e1, e2, e3, t1, t2, eW, hcore, t0, hBK]

/-- **(2.3) from the shell bound**: for `c ∈ C_in` of a window `W` with the history objects
(`hfull`, `hZk1`), if the parent spin of `c` is within `Ŵ_k δ_{k₁}` of a window block `s`
(`hshell`, (2.2)), then `|D^ph.Ψ(c) - D⁰.Ψ(c)| < (3dL + 2) Ŵ_k δ_{k₁}` (Lemma CH, then P7 (2.43) at a
collar site).  Auxiliary form: the main theorem `inner_collar_data_change_lt_actual` discharges `hshell`. -/
theorem inner_collar_data_change_lt_of_shell
    (hG : S.Good) (hkK : k ≤ K) (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j)
    (hk0 : k ≤ k0) (hrip : S.Ripe k (H.bk k Z)) (hq1 : 1 ≤ (H.bk k Z).q)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.numax j * (S.crit j + S.omega j) + 4 ≤ n j)
    (hϱ : (2 * S.d * S.L : ℝ) ≤ (S.L : ℝ) * S.M * S.Rb)
    {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k) k δ)
    {ϱW : ℝ} (W : WindowPieces S.d S.L (S.M * n k) k ϱW) (hWh : W.Hyp)
    (hfull : ∀ j, W.full.Ω j = (H.locGen Z S.M hkK hL hR).Ω j)
    (hZk1 : (W.Zk1 : Set (Torus S.d (S.M * n k * S.L ^ k))) = H.locFine Z S.M (S.k1 k))
    {a₁ : ℝ} (href : ParentRefines (W.windowGenSet hWh) W.full)
    (hprec : Precedes (W.windowGenSet hWh) W.bdry)
    (hBg : BgHyp S.d S.L k ϱW (compWeight S.L a₁) 0)
    {N : ℕ} (ψ ψ0 : BlockV S.d S.L (S.M * n k) k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    {K6 : ℝ} (hK6 : 0 < K6) (hθ1 : 3 * K6 * δ k ≤ 1)
    (hθc : 3 * (3 * K6 * δ k) ≤ bgC1 S.d S.L N)
    (hspec : PsiZeroSpec (H.locGen Z S.M hkK hL hR) W.bdry (H.locFine Z S.M k) (3 * K6 * δ k) ψ ψ0)
    (hwin : WinBond (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (H.locFine Z S.M k)
      (S.k1 k) (3 * S.d * S.L) δ ψ)
    (hΛ21 : 3 * S.d * K6 * (S.M * S.crit k) + 2 * (bgK1 S.d S.L N * (3 * (3 * K6))) ≤ S.hatW ε k)
    {c : Torus S.d (S.M * n k * S.L ^ k)} (hc : c ∈ collarIn W hWh)
    (hshell : ∃ s ∈ W.full.layer (S.k1 k), s ∉ W.Zk1 ∧
      dist (ψ (parentBlock W.full c)) (ψ (blockOf S.d S.L (S.M * n k) k (S.k1 k) s)) ≤
        S.hatW ε k * δ (S.k1 k)) :
    vn (deltaPsiColl W hWh href hprec (compWeight S.L a₁) ψ ψ0 h c) <
      (3 * S.d * S.L + 2) * S.hatW ε k * δ (S.k1 k) := by
  classical
  have hS := H.F.ok
  have hW : H.RipeWindow k Z :=
    ripe_window hG (fun j hj1 hj0 => (hT_forms hS (hT j hj1 hj0)).1) hk0 hkK hrip
  have hqk1 : S.k1 k = (H.bk k Z).q := hW.core_k1
  have hkq : S.k1 k < k := by
    rw [hqk1]
    have := hW.core_window.1
    have : 1 ≤ S.nq (H.bk k Z).q := by unfold Setting.nq; omega
    omega
  obtain ⟨hcol, hcZ1'⟩ := (mem_collarIn W hWh).1 hc
  have hcZ1 : c ∈ H.locFine Z S.M (S.k1 k) := by rw [← hZk1]; exact hcZ1'
  have hθ0 : 0 < 3 * K6 * δ k := by
    have := hδ.pos k (by omega) le_rfl
    positivity
  obtain ⟨Ut, hZUt, hdUt, hreg, hagree⟩ := id hspec
  have hD3 := psiZeroWin_collar_sub_le hprec hBg ψ0 h hθ0 hθ1 hθc hdUt hreg hcol
  have hK1 := bgK1_pos S.d S.L N
  obtain ⟨s, hsl, hsZ, hsh⟩ := hshell
  refine data_change_lt_of_shell_site hG hkK hS.two_le_L hR hk0 hrip hq1 hT hϱ hδ ψ ψ0 hK6 hθ1
    W.bdry ?_ hwin hΛ21 hcZ1 (parentBlock W.full c)
    (deltaPsiColl W hWh href hprec (compWeight S.L a₁) ψ ψ0 h c)
    (psiZeroWin (W.windowGenSet hWh) W.bdry (compWeight S.L a₁) ψ0 h c) ?_ ?_ ⟨s, ?_, ?_, hsh⟩
  · exact ⟨Ut, hZUt, hdUt, hreg, hagree⟩
  · funext i
    rw [deltaPsiColl_of_mem W hWh href hprec _ ψ ψ0 h ((mem_dataSites _).2 (Or.inr hcol)) i]
    have := inheritedField_eq_parentBlock W ψ c i
    unfold inheritedField at this
    rw [this]
    rfl
  · refine hD3.trans ?_
    nlinarith [mul_pos hK1 hθ0]
  · have h1 := (GeneratingSet.mem_layer _).1 hsl
    exact (GeneratingSet.mem_layer _).2 ⟨by rw [← hfull]; exact h1.1, by rw [← hfull]; exact h1.2⟩
  · exact fun hh => hsZ (by rw [← Finset.mem_coe, hZk1]; exact hh)

/-- **COLLAR-FIX (2.3) for the actual window, strict form, without `hcoreTop`**:
for `c ∈ C_in` of `windowOfHistory H Z g hkK hW`,
`|D^ph.Ψ(c) - D⁰.Ψ(c)| < (3dL + 2) Ŵ_k δ_{k₁}`.

Proof: the shell bound (2.2) `inner_collar_shell_bound_actual` (path of `regSetT` to a window block, with the
collar block prepended; any core layer), Lemma CH, then P7 (2.43) at a collar site
(`psiZeroWin_collar_sub_le`), as in `inner_collar_data_change_lt_of_coreTop`.

Remaining hypotheses, with their sources:
* `hG, hk0, hrip, hq1, hT, hϱ, hδ`: the source setting (goodness, ripeness of `Z`, the large-torus condition
  (H-T), `L M R_base ≥ 2dL`, the admissible tolerance sequence of Lemma III.4.5); `hW`, `g`: typing data of the
  window (`hW` is `ripe_window`);
* `hprec`: `𝔹_k(U_k)` follows the window generating set (typing of `windowData`);
* `hBg`: the background hypothesis `BgHyp` of P3 at the separation `winSep g` of the pieces;
* `ψ ψ0 h K6 hK6 hθ1 hθc hspec hwin`: the data and the properties (2.42)-(2.43), (1.24) of the reference
  field of LFR III.4.6 (`PsiZeroSpec`, `WinBond`, smallness of `θ = 3 K₆ δ_k`);
* `hΛ21`: (Λ21) of LFR §I.1.3; `hΛ21'`: (Λ21′) `(m_W + 1) C_reg ≤ Ŵ_k`, `m_W = d (2⌊R_{k₁-1}⌋ + 3) M`;
* `hCreg`: `0 ≤ C_reg`; `hband`: the bond bound of `regSetT` against `regSetTExt` with constant `C_reg δ_{k₁}`
  (Definition II.5.6, `bond_le_Creg_of_chiDomProp` with Lemma III.4.5; its transfer from the history torus to
  the window torus is the torus-cast bridge, not formalized). -/
theorem inner_collar_data_change_lt_actual
    (hG : S.Good) (hkK : k ≤ K) (hW : H.RipeWindow k Z) (g : Geo S n R S.M)
    (hk0 : k ≤ k0) (hrip : S.Ripe k (H.bk k Z)) (hq1 : 1 ≤ (H.bk k Z).q)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.numax j * (S.crit j + S.omega j) + 4 ≤ n j)
    (hϱ : (2 * S.d * S.L : ℝ) ≤ (S.L : ℝ) * S.M * S.Rb)
    {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k) k δ)
    {a₁ : ℝ}
    (hprec : Precedes ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW))
      (windowOfHistory H Z g hkK hW).bdry)
    (hBg : BgHyp S.d S.L k (winSep g) (compWeight S.L a₁) 0)
    {N : ℕ} (ψ ψ0 : BlockV S.d S.L (S.M * n k) k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    {K6 : ℝ} (hK6 : 0 < K6) (hθ1 : 3 * K6 * δ k ≤ 1)
    (hθc : 3 * (3 * K6 * δ k) ≤ bgC1 S.d S.L N)
    (hspec : PsiZeroSpec (H.locGen Z S.M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j))
      (windowOfHistory H Z g hkK hW).bdry (H.locFine Z S.M k) (3 * K6 * δ k) ψ ψ0)
    (hwin : WinBond (H.locGen Z S.M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j))
      (H.locFine Z S.M (S.k1 k)) (H.locFine Z S.M k) (S.k1 k) (3 * S.d * S.L) δ ψ)
    (hΛ21 : 3 * S.d * K6 * (S.M * S.crit k) + 2 * (bgK1 S.d S.L N * (3 * (3 * K6))) ≤ S.hatW ε k)
    {Creg : ℝ} (hCreg : 0 ≤ Creg)
    (hband : ∀ y ∈ regSetT H Z S.M (S.k1 k), ∀ y' ∈ regSetTExt H Z S.M (S.k1 k), AdjT y y' →
      dist (ψ ⟨S.k1 k, y⟩) (ψ ⟨S.k1 k, y'⟩) ≤ Creg * δ (S.k1 k))
    (hΛ21' : (((S.d * ((2 * ⌊R (S.k1 k - 1)⌋₊ + 3) * S.M) : ℕ) : ℝ) + 1) * Creg ≤ S.hatW ε k)
    {c : Torus S.d (S.M * n k * S.L ^ k)}
    (hc : c ∈ collarIn (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)) :
    vn (deltaPsiColl (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)
        (windowOfHistory_parentRefines H Z g hkK hW) hprec (compWeight S.L a₁) ψ ψ0 h c) <
      (3 * S.d * S.L + 2) * S.hatW ε k * δ (S.k1 k) := by
  have hS := H.F.ok
  have hqk1 : S.k1 k = (H.bk k Z).q := hW.core_k1
  have hkq : S.k1 k < k := by
    rw [hqk1]
    have := hW.core_window.1
    have : 1 ≤ S.nq (H.bk k Z).q := by unfold Setting.nq; omega
    omega
  have hδk1 := hδ.pos (S.k1 k) le_rfl hkq.le
  have hC0 : 0 ≤ Creg * δ (S.k1 k) := mul_nonneg hCreg hδk1.le
  obtain ⟨s, hsl, hsZ, hsh⟩ := inner_collar_shell_bound_actual (g := g) hkK hW ψ hC0 hband hc
  refine inner_collar_data_change_lt_of_shell hG hkK hS.two_le_L (fun j _ _ => g.hRlow j) hk0 hrip hq1 hT
    hϱ hδ (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)
    (fun j => windowOfHistory_full_Ω (g := g) hkK hW j) ?_ (windowOfHistory_parentRefines H Z g hkK hW) hprec
    hBg ψ ψ0 h hK6 hθ1 hθc hspec hwin hΛ21 hc ⟨s, hsl, hsZ, hsh.trans ?_⟩
  · ext x
    rw [Finset.mem_coe, windowOfHistory_Zk1, mem_locFineFin]
  · calc _ = (((S.d * ((2 * ⌊R (S.k1 k - 1)⌋₊ + 3) * S.M) : ℕ) : ℝ) + 1) * Creg * δ (S.k1 k) := by ring
      _ ≤ S.hatW ε k * δ (S.k1 k) := mul_le_mul_of_nonneg_right hΛ21' hδk1.le

/-- A site of `Z_{k₁} ∩ Ω₁(𝔹_{k₁}(W))` (any layer of the core piece) lies in the layer exactly `k₁` of
the parent `𝔹_k`: its `π_{k₁}`-cube is within `2⌊R_{k₁-1}⌋ + 3` of a cube off `Z_{k₁}` (Lemma II.2.3 (c) for
the minimal set of `W = (Z_{k₁}ᶜ)^{≈2}`), hence in `Ω_{k₁}` (Lemma I.3.5 (g), `mem_regOmega_of_near`), and
`Z_{k₁} ∩ Ω_{k₁+1} = ∅` (Lemma III.1.2 (f)). -/
theorem windowOfHistory_core_mem_full_layer (hkK : k ≤ K) (hW : H.RipeWindow k Z) (g : Geo S n R S.M)
    {x : Torus S.d (S.M * n k * S.L ^ k)}
    (hxZ : x ∈ (windowOfHistory H Z g hkK hW).Zk1)
    (hx1 : x ∈ (windowOfHistory H Z g hkK hW).core.Ω 1) :
    x ∈ (windowOfHistory H Z g hkK hW).full.layer (S.k1 k) := by
  classical
  have hq1 : 1 ≤ S.k1 k := hW.k1_pos hkK
  have hqk : S.k1 k ≤ k := k1_le hW
  have hnn : ∀ i, i < k → n i = S.L * n (i + 1) := fun i hi => H.F.hnn i (lt_of_lt_of_le hi hkK)
  have hR0 : ∀ i, 0 ≤ R i := fun i =>
    le_trans (by have := H.F.ok.two_le_Rb; linarith) (g.hRlow i)
  have hc0 : cubeMap n S.L S.M k (S.k1 k) x ∈ nbhd 1 (coreW H Z (S.k1 k)) :=
    cubeMap_nbhd_of_mem_cast (g := g) H.F.ok.two_le_L hnn hqk (A := coreW H Z (S.k1 k))
      (min_le_right _ _) hx1
  obtain ⟨w, hw, h1⟩ := mem_nbhd.1 hc0
  have hw' := hw
  simp only [coreW, thick2, thick, nbhd_nbhd] at hw'
  obtain ⟨e, he, h2⟩ := mem_nbhd.1 hw'
  have hce : supDist (cubeMap n S.L S.M k (S.k1 k) x) e ≤ 2 * ⌊R (S.k1 k - 1)⌋₊ + 3 :=
    (supDist_triangle _ w e).trans (by omega)
  have hcube : cubeMap n S.L S.M k (S.k1 k) x ∈ regOmega H Z (S.k1 k) :=
    mem_regOmega_of_near H Z hR0 hq1 he (by omega)
  have hΩ : x ∈ (H.locGen Z S.M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j)).Ω (S.k1 k) := by
    generalize S.k1 k = q at hq1 hqk hcube
    obtain ⟨i, rfl⟩ : ∃ i, q = i + 1 := ⟨q - 1, by omega⟩
    exact (mem_locGen_succ (hkK := hkK) (hL := H.F.ok.two_le_L) (hR := fun j _ _ => g.hRlow j)
      (Z := Z) (M := S.M) (by omega)).2 hcube
  exact (GeneratingSet.mem_layer _).2 ⟨by rw [windowOfHistory_full_Ω]; exact hΩ,
    windowOfHistory_hZk1top (g := g) hkK hW x hxZ⟩

/-- **The interior bound on the core piece, without `hcoreTop`** (LF-RECONSTRUCTION III.4.6 (2.48′) on
`Ω₁(G) ∩ Z_{k₁}`, any layer of the core): for `x ∈ Ω₁(G) ∩ Z_{k₁}`,
`|D^ph.Ψ(x) - D⁰.Ψ(x)| < (3dL + 2) Ŵ_k δ_{k₁}`.  Three steps: the parent spin `ψ(b_{k₁}(x))` (the parent
layer of `x` is `k₁`, `windowOfHistory_core_mem_full_layer`) is within `(m_W + 1) C_reg δ_{k₁} ≤ Ŵ_k δ_{k₁}`
of a window block (`windowOfHistory_regPath_in`, any core layer), Lemma CH to a terminal block, and the
landed interior comparison `psiZeroWin_sub_le` (valid at every site of `Ω₁(G)`, no top-layer
requirement; constant `2 K₁ · 3θ`).  Hypotheses as in `inner_collar_data_change_lt_actual`, with `0 < a₁`
for `psiZeroWin_sub_le`. -/
theorem deltaPsiColl_interior_lt_actual
    (hG : S.Good) (hkK : k ≤ K) (hW : H.RipeWindow k Z) (g : Geo S n R S.M)
    (hk0 : k ≤ k0) (hrip : S.Ripe k (H.bk k Z)) (hq1 : 1 ≤ (H.bk k Z).q)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.numax j * (S.crit j + S.omega j) + 4 ≤ n j)
    (hϱ : (2 * S.d * S.L : ℝ) ≤ (S.L : ℝ) * S.M * S.Rb)
    {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k) k δ)
    {a₁ : ℝ} (ha₁ : 0 < a₁)
    (hprec : Precedes ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW))
      (windowOfHistory H Z g hkK hW).bdry)
    (hBg : BgHyp S.d S.L k (winSep g) (compWeight S.L a₁) 0)
    {N : ℕ} (ψ ψ0 : BlockV S.d S.L (S.M * n k) k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    {K6 : ℝ} (hK6 : 0 < K6) (hθ1 : 3 * K6 * δ k ≤ 1)
    (hθc : 3 * (3 * K6 * δ k) ≤ bgC1 S.d S.L N)
    (hspec : PsiZeroSpec (H.locGen Z S.M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j))
      (windowOfHistory H Z g hkK hW).bdry (H.locFine Z S.M k) (3 * K6 * δ k) ψ ψ0)
    (hwin : WinBond (H.locGen Z S.M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j))
      (H.locFine Z S.M (S.k1 k)) (H.locFine Z S.M k) (S.k1 k) (3 * S.d * S.L) δ ψ)
    (hΛ21 : 3 * S.d * K6 * (S.M * S.crit k) + 2 * (bgK1 S.d S.L N * (3 * (3 * K6))) ≤ S.hatW ε k)
    {Creg : ℝ} (hCreg : 0 ≤ Creg)
    (hband : ∀ y ∈ regSetT H Z S.M (S.k1 k), ∀ y' ∈ regSetTExt H Z S.M (S.k1 k), AdjT y y' →
      dist (ψ ⟨S.k1 k, y⟩) (ψ ⟨S.k1 k, y'⟩) ≤ Creg * δ (S.k1 k))
    (hΛ21' : (((S.d * ((2 * ⌊R (S.k1 k - 1)⌋₊ + 3) * S.M) : ℕ) : ℝ) + 1) * Creg ≤ S.hatW ε k)
    {x : Torus S.d (S.M * n k * S.L ^ k)}
    (hx : x ∈ ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).Ω 1)
    (hxZ : x ∈ (windowOfHistory H Z g hkK hW).Zk1) :
    vn (deltaPsiColl (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)
        (windowOfHistory_parentRefines H Z g hkK hW) hprec (compWeight S.L a₁) ψ ψ0 h x) <
      (3 * S.d * S.L + 2) * S.hatW ε k * δ (S.k1 k) := by
  have hS := H.F.ok
  have hk1 : 1 ≤ S.k1 k := hW.k1_pos hkK
  have hqk1 : S.k1 k = (H.bk k Z).q := hW.core_k1
  have hkq : S.k1 k < k := by
    rw [hqk1]
    have := hW.core_window.1
    have : 1 ≤ S.nq (H.bk k Z).q := by unfold Setting.nq; omega
    omega
  have hδk1 := hδ.pos (S.k1 k) le_rfl hkq.le
  have hC0 : 0 ≤ Creg * δ (S.k1 k) := mul_nonneg hCreg hδk1.le
  have hxcore : x ∈ (windowOfHistory H Z g hkK hW).core.Ω 1 := by
    have := hx
    rw [WindowPieces.windowGenSet_Ω] at this
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at this
    rcases this with (⟨h1, _⟩ | ⟨_, h2, h3⟩) | ⟨_, _, h3⟩
    · exact h1
    · exact absurd hxZ h3
    · exact absurd (windowOfHistory_hZ (g := g) hkK hW hxZ) h3
  have hxl := windowOfHistory_core_mem_full_layer hkK hW g hxZ hxcore
  have hxF1 : x ∈ (windowOfHistory H Z g hkK hW).full.Ω 1 :=
    (windowOfHistory H Z g hkK hW).full.layer_subset hk1 hkq.le hxl
  have hli := (windowOfHistory H Z g hkK hW).full.layerIndex_eq hk1 hkq.le hxl
  have hxZ1 : x ∈ H.locFine Z S.M (S.k1 k) := by
    have := hxZ
    rwa [windowOfHistory_Zk1, mem_locFineFin] at this
  obtain ⟨m, hm, u, hu0, huT, huA, hum, s, hs, hsZ, hsu⟩ :=
    windowOfHistory_regPath_in (g := g) hkK hW hxZ hxcore
  have h2 := regPath_dist_le ψ hband huT huA hum
  have hθ0 : 0 < 3 * K6 * δ k := by
    have := hδ.pos k (by omega) le_rfl
    positivity
  obtain ⟨Ut, hZUt, hdUt, hreg, hagree⟩ := id hspec
  have hD3 := psiZeroWin_sub_le hS.two_le_L ha₁ hprec hBg ψ0 h hθ0 hθ1 hθc hdUt hreg hx
  have e0 : blockOf S.d S.L (S.M * n k) k (S.k1 k) x =
      ⟨S.k1 k, jBlock S.d S.L (S.M * n k) k (S.k1 k) x⟩ := rfl
  have e2 : blockOf S.d S.L (S.M * n k) k (S.k1 k) s = ⟨S.k1 k, u m⟩ := by
    simp only [blockOf]; rw [hsu]
  refine data_change_lt_of_shell_site hG hkK hS.two_le_L (fun j _ _ => g.hRlow j) hk0 hrip hq1 hT hϱ hδ
    ψ ψ0 hK6 hθ1 (windowOfHistory H Z g hkK hW).bdry ?_ hwin hΛ21 hxZ1
    (blockOf S.d S.L (S.M * n k) k (S.k1 k) x)
    (deltaPsiColl (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)
      (windowOfHistory_parentRefines H Z g hkK hW) hprec (compWeight S.L a₁) ψ ψ0 h x)
    (psiZeroWin ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW))
      (windowOfHistory H Z g hkK hW).bdry (compWeight S.L a₁) ψ0 h x) ?_ hD3
    ⟨s, hs, fun hh => hsZ (by rw [windowOfHistory_Zk1, mem_locFineFin]; exact hh), ?_⟩
  · exact ⟨Ut, hZUt, hdUt, hreg, hagree⟩
  · funext i
    rw [deltaPsiColl_of_mem _ _ _ _ _ ψ ψ0 h ((Balaban.Background.mem_dataSites _).2 (Or.inl hx)) i,
      psiTilde_of_mem _ ψ hxF1, hli]
    rfl
  · rw [e0, e2]
    rw [hu0] at h2
    have hm' : (m : ℝ) ≤ (S.d * ((2 * ⌊R (S.k1 k - 1)⌋₊ + 3) * S.M) : ℕ) := by exact_mod_cast hm
    calc _ ≤ (m : ℝ) * (Creg * δ (S.k1 k)) := h2
      _ ≤ ((((S.d * ((2 * ⌊R (S.k1 k - 1)⌋₊ + 3) * S.M) : ℕ) : ℝ) + 1) * Creg) * δ (S.k1 k) := by
          nlinarith
      _ ≤ S.hatW ε k * δ (S.k1 k) := mul_le_mul_of_nonneg_right hΛ21' hδk1.le

end RegionHistory

end Balaban.LargeField
