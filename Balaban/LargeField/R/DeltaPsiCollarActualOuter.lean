module

public import Balaban.LargeField.R.DeltaPsiCoreFinal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The outer-piece bounds of Lemma III.4.6 for pieces of any separation

`deltaPsi_layer_lt_outer` and `deltaPsi_top_outer` (`DeltaPsi.lean`) are stated for window pieces of
separation exactly `L M R_base` with `W.full = 𝔹_k`.  The actual window `windowOfHistory` has the
separation `winSep g = min (L M R_base) (minSep L M₁)` and `full = 𝔹_k.relax`, so the equality `hfull` is
not available.  The statements and proofs below are those of `DeltaPsi.lean`, with `W` of arbitrary
separation `ϱW` and `hfull` replaced by the equality of the sets `Ω_j` (all the proof uses of `hfull`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} {k : ℕ} {Z : H.Comp k} [NeZero S.L] [NeZero S.M]

/-- **`deltaPsi_layer_lt_outer` for pieces of any separation** (Lemma III.4.6 (2.48′), layers `k₁ ≤ j < k`
on `𝔹_k ∩ Z^c_{k₁} ∩ Z`). -/
theorem deltaPsi_layer_lt_outer_gen
    (hG : S.Good) (hkK : k ≤ K) (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j)
    (hk0 : k ≤ k0) (hrip : S.Ripe k (H.bk k Z)) (hq1 : 1 ≤ (H.bk k Z).q)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.numax j * (S.crit j + S.omega j) + 4 ≤ n j)
    (hϱ : (2 * S.d * S.L : ℝ) ≤ (S.L : ℝ) * S.M * S.Rb)
    {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k) k δ)
    {ϱW : ℝ} (W : WindowPieces S.d S.L (S.M * n k) k ϱW) (hWh : W.Hyp)
    (hfull : ∀ j, W.full.Ω j = (H.locGen Z S.M hkK hL hR).Ω j)
    (hZ : (W.Z : Set (Torus S.d (S.M * n k * S.L ^ k))) = H.locFine Z S.M k)
    (hZk1 : (W.Zk1 : Set (Torus S.d (S.M * n k * S.L ^ k))) = H.locFine Z S.M (S.k1 k))
    {a₁ : ℝ} (ha₁ : 0 < a₁) (hprec : Precedes (W.windowGenSet hWh) W.bdry)
    (hBg : BgHyp S.d S.L k ϱW (compWeight S.L a₁) 0)
    {N : ℕ} (ψ ψ0 : BlockV S.d S.L (S.M * n k) k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    {K6 : ℝ} (hK6 : 0 < K6) (hθ1 : 3 * K6 * δ k ≤ 1)
    (hθc : 3 * (3 * K6 * δ k) ≤ bgC1 S.d S.L N)
    (hspec : PsiZeroSpec (H.locGen Z S.M hkK hL hR) W.bdry (H.locFine Z S.M k) (3 * K6 * δ k) ψ ψ0)
    (hwin : WinBond (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (H.locFine Z S.M k)
      (S.k1 k) (3 * S.d * S.L) δ ψ)
    (hΛ21 : 3 * S.d * K6 * (S.M * S.crit k) + 2 * (bgK1 S.d S.L N * (3 * (3 * K6))) ≤ S.hatW ε k)
    {x : Torus S.d (S.M * n k * S.L ^ k)} (hx : x ∈ (W.windowGenSet hWh).Ω 1)
    (hxZ : x ∈ H.locFine Z S.M k) (hxc : x ∉ H.locFine Z S.M (S.k1 k))
    {j : ℕ} (hk1j : S.k1 k ≤ j) (hjk : j < k) (hxl : x ∈ (W.windowGenSet hWh).layer j) :
    vn (deltaPsi (W.windowGenSet hWh) W.bdry (compWeight S.L a₁) ψ ψ0 h x) <
      (3 * S.d * S.L + 2) * S.hatW ε k * δ j := by
  classical
  have hS := H.F.ok
  have hxZ' : x ∈ W.Z := by rw [← Finset.mem_coe, hZ]; exact hxZ
  have hxc' : x ∉ W.Zk1 := by rw [← Finset.mem_coe, hZk1]; exact hxc
  have hxG : x ∈ (H.locGen Z S.M hkK hL hR).layer j := by
    have h1 := (GeneratingSet.mem_layer _).1 ((windowGen_mem_layer_iff W hWh hxZ' hxc' j).1 hxl)
    exact (GeneratingSet.mem_layer _).2 ⟨by rw [← hfull]; exact h1.1, by rw [← hfull]; exact h1.2⟩
  -- the geometry of the window
  have hW : H.RipeWindow k Z :=
    ripe_window hG (fun j hj1 hj0 => (hT_forms hS (hT j hj1 hj0)).1) hk0 hkK hrip
  have hqk1 : S.k1 k = (H.bk k Z).q := hW.core_k1
  have hk1 : 1 ≤ S.k1 k := by rw [hqk1]; exact hq1
  have hkq : S.k1 k < k := by
    rw [hqk1]
    have := hW.core_window.1
    have : 1 ≤ S.nq (H.bk k Z).q := by unfold Setting.nq; omega
    omega
  have hnn := hnn_k H hkK
  have hblk : ∀ x x' : Torus S.d (S.M * n k * S.L ^ k),
      jBlock S.d S.L (S.M * n k) k (S.k1 k) x = jBlock S.d S.L (S.M * n k) k (S.k1 k) x' →
        (x ∈ H.locFine Z S.M (S.k1 k) ↔ x' ∈ H.locFine Z S.M (S.k1 k)) := by
    intro x x' h
    have h1 := cubeMap_eq_of_jBlock_eq (S := S) (n := n) (M := S.M) (K := k) (j := S.k1 k)
      (k := S.k1 k) le_rfl hkq.le hnn h
    show cubeMap n S.L S.M k (S.k1 k) x ∈ ((H.locRH k Z).step (S.k1 k)).Z ↔
      cubeMap n S.L S.M k (S.k1 k) x' ∈ ((H.locRH k Z).step (S.k1 k)).Z
    rw [h1]
  have hΩ : ∀ x ∈ H.locFine Z S.M (S.k1 k), x ∉ (H.locGen Z S.M hkK hL hR).Ω (S.k1 k + 1) :=
    fun x hx => locFine_not_mem_Omega (hkK := hkK) (hL := hL) (hR := hR) hkq hx
  have hd1 : 1 ≤ S.d := by have := hS.three_le_d; omega
  have hT2 : ∀ j, 1 ≤ j → j ≤ k0 → 2 * S.crit j + 5 ≤ n j :=
    fun j hj1 hj0 => (hT_forms hS (hT j hj1 hj0)).2
  have hZfar : ∀ z ∈ H.locFine Z S.M (S.k1 k), ∀ y ∈ (H.locGen Z S.M hkK hL hR).Ω (S.k1 k + 1),
      (2 * S.d * (S.L : ℝ) ^ (S.k1 k + 1) : ℝ) <
        Green.torusDist S.d (S.M * n k * S.L ^ k) z y := fun z hz y hy =>
    locFine_far (hkK := hkK) (hL := hL) (hR := hR) hϱ hk1 hkq hz hy
  have hδpos : ∀ i, S.k1 k ≤ i → i < k → 0 < δ i := fun i h1 h2 => hδ.pos i h1 h2.le
  have hc : (0 : ℝ) < 3 * S.d * S.L := by
    have : (1 : ℝ) ≤ S.d := by exact_mod_cast hd1
    have : (2 : ℝ) ≤ S.L := by exact_mod_cast hL
    positivity
  -- the window block of `x` and the chain
  have hy : IsWindowBlock (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (S.k1 k)
      (blockOf S.d S.L (S.M * n k) k j x) :=
    isWindowBlock_blockOf (H.locGen Z S.M hkK hL hR) hblk hΩ hk1 hk1j hjk hxG hxc
  obtain ⟨len, xs, hx0, hwinb, hterm, hadj, hinj, hdist⟩ :=
    lemmaCH_of_ripe hG hkK hL hR hk0 hrip hT hδ hc ψ
      (fun u v hu hv huv => winBond_intra hwin u v hu hv huv)
      (fun u v hu hv huv => winBond_cross hϱ hd1 hL (H.locGen Z S.M hkK hL hR) hk1 hZfar hc
        hδpos hwin u v hu hv huv) hjk hy rfl
  -- the terminal block
  obtain ⟨Ut, hZUt, hdUt, hreg, hagree⟩ := hspec
  have hj1 : 1 ≤ j := le_trans hk1 hk1j
  have hlay : (W.windowGenSet hWh).layerIndex x = j :=
    GeneratingSet.layerIndex_eq _ hj1 hjk.le hxl
  have hxδ : psiTilde (W.windowGenSet hWh) ψ x = fun i => ψ (blockOf S.d S.L (S.M * n k) k j x) i := by
    funext i; rw [psiTilde_of_mem _ ψ hx, hlay]
  generalize hyk : xs len = yk at hterm hdist
  obtain ⟨ik, β⟩ := yk
  obtain ⟨hik, hall⟩ := hterm
  simp only at hik
  subst hik
  obtain ⟨s, hs⟩ := exists_site_of_block (d := S.d) (L := S.L) (N₀ := S.M * n ik) (k := ik)
    (j := ik) le_rfl β
  have hsZ : s ∈ H.locFine Z S.M ik := (hall s hs).2
  have hψk : ψ0 ⟨ik, β⟩ = ψ ⟨ik, β⟩ := hagree _ ⟨rfl, hall⟩
  -- the path in `Z`
  have hθ0 : 0 < 3 * K6 * δ ik := by
    have := hδ.pos ik (by omega) le_rfl
    positivity
  obtain ⟨m, hm, hr⟩ := zblocks_reach (H := H) (Z := Z) hkK (by omega) hk0 hW
    (by have := hT2 ik (by omega) hk0; omega) ⟨s, hsZ, hs⟩ ⟨x, hxZ, rfl⟩
  have hPU : {γ | ∃ x ∈ H.locFine Z S.M ik, jBlock S.d S.L (S.M * n ik) ik ik x = γ} ⊆ Ut := by
    rintro γ ⟨x', hx', rfl⟩
    exact hZUt x' hx'
  have hD2 := psi0_dist_le hPU hθ0 hreg hr
  have hmR : (m : ℝ) ≤ S.d * (S.M * S.crit ik) := by exact_mod_cast hm
  -- (2.43)
  have hD3 := psiZeroWin_sub_le hL ha₁ hprec hBg ψ0 h hθ0 hθ1 hθc hdUt hreg hx
  -- assembling
  set y := blockOf S.d S.L (S.M * n ik) ik j x with hydef
  set C := psiZeroWin (W.windowGenSet hWh) W.bdry (compWeight S.L a₁) ψ0 h x with hC
  have hdel : deltaPsi (W.windowGenSet hWh) W.bdry (compWeight S.L a₁) ψ ψ0 h x =
      (fun i => ((ψ y i : ℝ) : ℂ)) - C := by
    funext i
    rw [deltaPsi_of_mem _ _ _ _ _ _ hx i, congrFun hxδ i]
    rfl
  have t1 := vn_triangle (fun i => ((ψ y i : ℝ) : ℂ)) (fun i => ((ψ ⟨ik, β⟩ i : ℝ) : ℂ)) C
  have t2 := vn_triangle (fun i => ((ψ ⟨ik, β⟩ i : ℝ) : ℂ))
    (fun i => ((ψ0 ⟨ik, jBlock S.d S.L (S.M * n ik) ik ik x⟩ i : ℝ) : ℂ)) C
  have e1 : vn ((fun i => ((ψ y i : ℝ) : ℂ)) - fun i => ((ψ ⟨ik, β⟩ i : ℝ) : ℂ)) =
      dist (ψ y) (ψ ⟨ik, β⟩) := vn_cast_sub _ _
  have e2 : vn ((fun i => ((ψ ⟨ik, β⟩ i : ℝ) : ℂ)) -
      fun i => ((ψ0 ⟨ik, jBlock S.d S.L (S.M * n ik) ik ik x⟩ i : ℝ) : ℂ)) =
      dist (ψ0 ⟨ik, β⟩) (ψ0 ⟨ik, jBlock S.d S.L (S.M * n ik) ik ik x⟩) := by
    rw [← hψk]; exact vn_cast_sub _ _
  have e3 := vn_sub_comm (fun i => ((ψ0 ⟨ik, jBlock S.d S.L (S.M * n ik) ik ik x⟩ i : ℝ) : ℂ)) C
  have hD3' : vn (C - fun i => ((ψ0 ⟨ik, jBlock S.d S.L (S.M * n ik) ik ik x⟩ i : ℝ) : ℂ)) ≤
      2 * (bgK1 S.d S.L N * (3 * (3 * K6 * δ ik))) := hD3
  rw [hdel]
  have hδk := hδ.pos ik (by omega) le_rfl
  have hδj := hδ.pos j hk1j hjk.le
  have hδkj : δ ik ≤ δ j := hδ.le_of_le hk1j hjk.le
  have hWpos : 0 < S.hatW ε ik := by
    by_contra hneg
    push Not at hneg
    have h0 := lt_of_le_of_lt dist_nonneg hdist
    have : S.hatW ε ik * (3 * S.d * S.L) * δ j ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hneg hc.le) hδj.le
    linarith
  have hθm : (m : ℝ) * (3 * K6 * δ ik) ≤ S.d * (S.M * S.crit ik) * (3 * K6 * δ ik) :=
    mul_le_mul_of_nonneg_right hmR hθ0.le
  have hΛ' : (3 * S.d * K6 * (S.M * S.crit ik) + 2 * (bgK1 S.d S.L N * (3 * (3 * K6)))) * δ ik ≤
      S.hatW ε ik * δ ik := mul_le_mul_of_nonneg_right hΛ21 hδk.le
  have hWδ : S.hatW ε ik * δ ik ≤ S.hatW ε ik * δ j := mul_le_mul_of_nonneg_left hδkj hWpos.le
  have hT0 : 0 < S.hatW ε ik * δ j := mul_pos hWpos hδj
  have eW : S.hatW ε ik * (3 * S.d * S.L) * δ j = 3 * S.d * S.L * (S.hatW ε ik * δ j) := by ring
  nlinarith [hdist, hD2, hD3', hθm, hΛ', hWδ, hT0, e1, e2, e3, t1, t2, eW]


/-- **`deltaPsi_top_outer` for pieces of any separation** (`δψ = 0` on `Ω_k` of `𝔹_k ∩ Z^c_{k₁} ∩ Z`). -/
theorem deltaPsi_top_outer_gen
    (hkK : k ≤ K) (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j)
    {ϱW : ℝ} (W : WindowPieces S.d S.L (S.M * n k) k ϱW) (hWh : W.Hyp)
    (hfull : ∀ j, W.full.Ω j = (H.locGen Z S.M hkK hL hR).Ω j)
    (hZ : (W.Z : Set (Torus S.d (S.M * n k * S.L ^ k))) = H.locFine Z S.M k)
    (hZk1 : (W.Zk1 : Set (Torus S.d (S.M * n k * S.L ^ k))) = H.locFine Z S.M (S.k1 k))
    {a₁ : ℝ} (ha₁ : 0 < a₁) (hprec : Precedes (W.windowGenSet hWh) W.bdry)
    {N : ℕ} (ψ ψ0 : BlockV S.d S.L (S.M * n k) k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    {θ : ℝ} (hspec : PsiZeroSpec (H.locGen Z S.M hkK hL hR) W.bdry (H.locFine Z S.M k) θ ψ ψ0)
    {x : Torus S.d (S.M * n k * S.L ^ k)} (hx : x ∈ (W.windowGenSet hWh).Ω 1)
    (hxZ : x ∈ H.locFine Z S.M k) (hxc : x ∉ H.locFine Z S.M (S.k1 k))
    (hxk : x ∈ (H.locGen Z S.M hkK hL hR).Ω k) :
    deltaPsi (W.windowGenSet hWh) W.bdry (compWeight S.L a₁) ψ ψ0 h x = 0 := by
  classical
  have hxZ' : x ∈ W.Z := by rw [← Finset.mem_coe, hZ]; exact hxZ
  have hxc' : x ∉ W.Zk1 := by rw [← Finset.mem_coe, hZk1]; exact hxc
  have hk1 : 1 ≤ k := one_le_of_mem_Ω1 hx
  have hxl : x ∈ (W.windowGenSet hWh).layer k := by
    rw [windowGen_mem_layer_iff W hWh hxZ' hxc', GeneratingSet.mem_layer]
    exact ⟨by rw [hfull]; exact hxk, by simp [GeneratingSet.top]⟩
  have hlay : (W.windowGenSet hWh).layerIndex x = k := GeneratingSet.layerIndex_eq _ hk1 le_rfl hxl
  have hlay' : W.bdry.layerIndex x = k := by
    have h1 := hprec.layerIndex_le hx
    have h2 := (W.bdry.layerIndex_spec (hprec.mem_Ω1 hx)).2.1
    omega
  have hnn := hnn_k H hkK
  have hZf : ∀ x x' : Torus S.d (S.M * n k * S.L ^ k),
      jBlock S.d S.L (S.M * n k) k k x = jBlock S.d S.L (S.M * n k) k k x' →
        (x ∈ H.locFine Z S.M k ↔ x' ∈ H.locFine Z S.M k) := by
    intro x x' h
    have h1 := cubeMap_eq_of_jBlock_eq (S := S) (n := n) (M := S.M) (K := k) (j := k)
      (k := k) le_rfl le_rfl hnn h
    show cubeMap n S.L S.M k k x ∈ ((H.locRH k Z).step k).Z ↔
      cubeMap n S.L S.M k k x' ∈ ((H.locRH k Z).step k).Z
    rw [h1]
  obtain ⟨Ut, -, -, -, hagree⟩ := hspec
  have hterm := isTerminalBlock_blockOf (H.locGen Z S.M hkK hL hR) hk1 hZf
    (show x ∈ (H.locGen Z S.M hkK hL hR).Ω k from hxk) hxZ
  have hψ := hagree _ hterm
  have hxd : x ∈ dataSites W.bdry := (mem_dataSites W.bdry).2 (Or.inl (hprec.mem_Ω1 hx))
  funext i
  rw [deltaPsi_of_mem _ _ _ _ _ _ hx i]
  have hz : psiZeroWin (W.windowGenSet hWh) W.bdry (compWeight S.L a₁) ψ0 h x i =
      ((ψ0 ⟨k, jBlock S.d S.L (S.M * n k) k k x⟩ i : ℝ) : ℂ) := by
    unfold psiZeroWin
    rw [composeField_eq_data_top _ _ hx (compWeight_pos hL ha₁ hk1).ne' hlay hlay' i]
    unfold psiZeroData
    rw [liftSingle_Ψ W.bdry _ _ hxd]
  rw [hz]
  have : psiTilde (W.windowGenSet hWh) ψ x i = ψ0 ⟨k, jBlock S.d S.L (S.M * n k) k k x⟩ i := by
    rw [psiTilde_of_mem _ ψ hx, hlay]
    rw [← hψ]
    rfl
  rw [this]
  simp

end RegionHistory

end Balaban.LargeField
