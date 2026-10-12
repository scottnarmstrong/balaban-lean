module

public import Balaban.LargeField.R.DeltaPsiComp
public import Balaban.LargeField.R.DeltaPsiEdge
public import Balaban.LargeField.R.DeltaPsiZ
public import Balaban.LargeField.R.WindowGenGlue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma III.4.6: the window field `δψ` (P7 Lemma 2.3, (2.48′))

For a ripe component `Z` of scale `k` with window `𝔹_{k₁,k}`, on the sites of the window generating set in
`Z ∖ Z_{k₁}` (the region `𝔹_k ∩ Z^c_{k₁} ∩ Z` of Definition III.2.1):

* `δψ = 0` on `Ω_k` (`deltaPsi_top`);
* `|δψ| < C_{23} Ŵ_k δ_j` on `Λ_j`, `k₁ ≤ j ≤ k - 1`, `C_{23} = 3dL + 2` (`deltaPsi_layer_lt`).

Proof of the second bound: the chain of Lemma CH from the window block of `x` to a terminal block
`y_k` (`lemmaCH_of_ripe`, edge costs from `WinBond`: `winBond_intra`, `winBond_cross`) gives
`|ψ_j(y) - ψ_k(y_k)| < 3dL Ŵ_k δ_j`; `ψ⁰_k(y_k) = ψ_k(y_k)` and `ψ⁰_k ∈ Ψ̃(U^∼_k; 3 K₆ δ_k)` along a
monotone path in the box `Z` (`zblocks_reach`, at most `d M crit_k` bonds) give
`|ψ_k(y_k) - ψ⁰_k(z(x))| ≤ 3 d K₆ M crit_k δ_k`; and (2.43) (`psiZeroWin_sub_le`) gives
`|ψ⁰_k(z(x)) - ψ⁰_{k₁,k}(x)| ≤ 2 K₁ · 3 · 3K₆ δ_k`.  The last two are `≤ Ŵ_k δ_k ≤ Ŵ_k δ_j` by the
hypothesis (Λ21).

*Not covered*: the sites of the core `Z_{k₁}` (`j = k₁`, `x ∈ 𝔹_{k₁}(W) ∩ Z_{k₁}`), which need the
regularity of `ψ_{k₁}` from the step `k₁ - 1 → k₁` (Definition II.5.6).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section Aux

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-- The Euclidean norm of the difference of two real vectors. -/
theorem vn_cast_sub (u w : EuclideanSpace ℝ (Fin N)) :
    vn (fun i => ((u i : ℝ) : ℂ) - ((w i : ℝ) : ℂ)) = dist u w := by
  have h := vn_ofReal (N := N) (fun i => u i - w i)
  have e : (fun i => (((u i - w i : ℝ)) : ℂ)) = fun i => ((u i : ℝ) : ℂ) - ((w i : ℝ) : ℂ) := by
    funext i; push_cast; ring
  rw [e] at h
  rw [h, EuclideanSpace.dist_eq, rn_toLp_eq]
  rw [EuclideanSpace.norm_eq]
  simp [Real.dist_eq, sq_abs]

/-- The composed field at a site of the top layer of both generating sets is the datum. -/
theorem composeField_eq_data_top {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}
    {a : ℕ → ℝ} (φ' : G'.Ω 1 × Fin N → ℂ) (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hak : a k ≠ 0) (hG : G.layerIndex x = k)
    (hG' : G'.layerIndex x = k) (i : Fin N) :
    composeField G G' a φ' Ψ' x i = Ψ' x i := by
  rw [composeField_of_mem a φ' Ψ' hx i, hG, hG']
  have hL : ((L : ℝ) ^ k) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hcoef : a k / a k * (((L : ℝ) ^ k) ^ 2 / ((L : ℝ) ^ k) ^ 2) = 1 := by
    rw [div_self hak, div_self hL, one_mul]
  have hblk : G.blk k x = G'.blk k x := by
    ext y; rw [GeneratingSet.mem_blk, GeneratingSet.mem_blk]
  have hmean : blockMean G k (fun y => svec G' φ' y i) x = blockMean G' k (fun y => svec G' φ' y i) x := by
    unfold blockMean; rw [hblk]
  rw [hcoef, hmean]
  simp

theorem IsAdmDelta.le_of_le {ε : ℝ} {k1 k : ℕ} {δ : ℕ → ℝ} (h : IsAdmDelta d L ε k1 k δ) {j : ℕ}
    (hk1 : k1 ≤ j) (hjk : j ≤ k) : δ k ≤ δ j := by
  have key : ∀ t, j + t ≤ k → δ (j + t) ≤ δ j := by
    intro t
    induction t with
    | zero => intro _; exact le_rfl
    | succ t ih =>
      intro ht
      have h1 := h.anti (j + t) (by omega) (by omega)
      have h2 := ih (by omega)
      have : j + (t + 1) = j + t + 1 := by ring
      rw [this]
      linarith
  have := key (k - j) (by omega)
  rwa [show j + (k - j) = k by omega] at this

end Aux

section Window

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- On `Z ∖ Z_{k₁}` the layers of the window generating set are those of `𝔹_k` (the pieces' regions
are disjoint). -/
theorem windowGen_mem_iff (W : WindowPieces d L N₀ k ϱ) (h : W.Hyp)
    {x : Torus d (N₀ * L ^ k)} (hxZ : x ∈ W.Z) (hxc : x ∉ W.Zk1) (m : ℕ) :
    x ∈ (W.windowGenSet h).Ω m ↔ x ∈ W.full.Ω m := by
  rw [W.windowGenSet_Ω h m]
  simp [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, hxc, hxZ]

theorem windowGen_mem_layer_iff (W : WindowPieces d L N₀ k ϱ) (h : W.Hyp)
    {x : Torus d (N₀ * L ^ k)} (hxZ : x ∈ W.Z) (hxc : x ∉ W.Zk1) (m : ℕ) :
    x ∈ (W.windowGenSet h).layer m ↔ x ∈ W.full.layer m := by
  rw [GeneratingSet.mem_layer, GeneratingSet.mem_layer, windowGen_mem_iff W h hxZ hxc,
    windowGen_mem_iff W h hxZ hxc]

end Window

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} {k : ℕ} {Z : H.Comp k} [NeZero S.L] [NeZero S.M]

/-- **Lemma III.4.6 (2.48′), layers `k₁ ≤ j < k`** on the region `𝔹_k ∩ Z^c_{k₁} ∩ Z` of the window. -/
theorem deltaPsi_layer_lt
    (hG : S.Good) (hkK : k ≤ K) (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j)
    (hk0 : k ≤ k0) (hrip : S.Ripe k (H.bk k Z)) (hq1 : 1 ≤ (H.bk k Z).q)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.numax j * (S.crit j + S.omega j) + 4 ≤ n j)
    (hϱ : (2 * S.d * S.L : ℝ) ≤ (S.L : ℝ) * S.M * S.Rb)
    {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k) k δ)
    (W : WindowPieces S.d S.L (S.M * n k) k ((S.L : ℝ) * S.M * S.Rb)) (hWh : W.Hyp)
    (hfull : W.full = H.locGen Z S.M hkK hL hR)
    (hZ : (W.Z : Set (Torus S.d (S.M * n k * S.L ^ k))) = H.locFine Z S.M k)
    (hZk1 : (W.Zk1 : Set (Torus S.d (S.M * n k * S.L ^ k))) = H.locFine Z S.M (S.k1 k))
    {a₁ : ℝ} (ha₁ : 0 < a₁) (hprec : Precedes (W.windowGenSet hWh) W.bdry)
    (hBg : BgHyp S.d S.L k ((S.L : ℝ) * S.M * S.Rb) (compWeight S.L a₁) 0)
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
    rw [← hfull]; exact (windowGen_mem_layer_iff W hWh hxZ' hxc' j).1 hxl
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

/-- **Lemma III.4.6 (2.48′), `δψ = 0` on `Ω_k`**, on the region `𝔹_k ∩ Z^c_{k₁} ∩ Z` of the window. -/
theorem deltaPsi_top
    (hkK : k ≤ K) (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j)
    (W : WindowPieces S.d S.L (S.M * n k) k ((S.L : ℝ) * S.M * S.Rb)) (hWh : W.Hyp)
    (hfull : W.full = H.locGen Z S.M hkK hL hR)
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
    rw [windowGen_mem_layer_iff W hWh hxZ' hxc', hfull, GeneratingSet.mem_layer]
    exact ⟨hxk, by simp [GeneratingSet.top]⟩
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

/-- **Lemma III.4.6 ((2.48′); P7 Lemma 2.3)** on the region `𝔹_k ∩ Z^c_{k₁} ∩ Z` of the window
generating set `𝔹_{k₁,k}`: `δψ = 0` on `Ω_k` and `|δψ| < C_{23} Ŵ_k δ_j` on `Λ_j`, `k₁ ≤ j ≤ k - 1`,
`C_{23} = 3dL + 2`.  Hypotheses: the ripe window `Z` with (H-T), the window pieces of Definition III.2.1
(`W.full = 𝔹_k`, `W.Z`, `W.Zk1` the fine sets of `Z`, `Z_{k₁}`), `𝔹_{k₁,k} ≺ 𝔹_k(U_k)` and the Green's
function setting of `𝔹_k(U_k)` (BG (6.2) is defined for such pairs), the admissible sequence `δ`
(Lemma III.4.5), the block field `ψ⁰_k` of Lemma III.3.3 with `θ = 3 K₆ δ_k` small (`PsiZeroSpec`, (Λ22)),
the window domain (`WinBond`, (1.24)), and the constant condition (Λ21) in the normalisation of this
file: `3 d K₆ M crit_k + 2 K₁ · 3 · 3K₆ ≤ Ŵ_k`, `K₁ = bgK1`. -/
theorem deltaPsi_le
    (hG : S.Good) (hkK : k ≤ K) (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j)
    (hk0 : k ≤ k0) (hrip : S.Ripe k (H.bk k Z)) (hq1 : 1 ≤ (H.bk k Z).q)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.numax j * (S.crit j + S.omega j) + 4 ≤ n j)
    (hϱ : (2 * S.d * S.L : ℝ) ≤ (S.L : ℝ) * S.M * S.Rb)
    {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k) k δ)
    (W : WindowPieces S.d S.L (S.M * n k) k ((S.L : ℝ) * S.M * S.Rb)) (hWh : W.Hyp)
    (hfull : W.full = H.locGen Z S.M hkK hL hR)
    (hZ : (W.Z : Set (Torus S.d (S.M * n k * S.L ^ k))) = H.locFine Z S.M k)
    (hZk1 : (W.Zk1 : Set (Torus S.d (S.M * n k * S.L ^ k))) = H.locFine Z S.M (S.k1 k))
    {a₁ : ℝ} (ha₁ : 0 < a₁) (hprec : Precedes (W.windowGenSet hWh) W.bdry)
    (hBg : BgHyp S.d S.L k ((S.L : ℝ) * S.M * S.Rb) (compWeight S.L a₁) 0)
    {N : ℕ} (ψ ψ0 : BlockV S.d S.L (S.M * n k) k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    {K6 : ℝ} (hK6 : 0 < K6) (hθ1 : 3 * K6 * δ k ≤ 1)
    (hθc : 3 * (3 * K6 * δ k) ≤ bgC1 S.d S.L N)
    (hspec : PsiZeroSpec (H.locGen Z S.M hkK hL hR) W.bdry (H.locFine Z S.M k) (3 * K6 * δ k) ψ ψ0)
    (hwin : WinBond (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (H.locFine Z S.M k)
      (S.k1 k) (3 * S.d * S.L) δ ψ)
    (hΛ21 : 3 * S.d * K6 * (S.M * S.crit k) + 2 * (bgK1 S.d S.L N * (3 * (3 * K6))) ≤ S.hatW ε k)
    {x : Torus S.d (S.M * n k * S.L ^ k)} (hx : x ∈ (W.windowGenSet hWh).Ω 1)
    (hxZ : x ∈ H.locFine Z S.M k) (hxc : x ∉ H.locFine Z S.M (S.k1 k)) :
    (x ∈ (H.locGen Z S.M hkK hL hR).Ω k →
      deltaPsi (W.windowGenSet hWh) W.bdry (compWeight S.L a₁) ψ ψ0 h x = 0) ∧
    ∀ j, S.k1 k ≤ j → j < k → x ∈ (W.windowGenSet hWh).layer j →
      vn (deltaPsi (W.windowGenSet hWh) W.bdry (compWeight S.L a₁) ψ ψ0 h x) <
        (3 * S.d * S.L + 2) * S.hatW ε k * δ j :=
  ⟨fun hxk => deltaPsi_top hkK hL hR W hWh hfull hZ hZk1 ha₁ hprec ψ ψ0 h hspec hx hxZ hxc hxk,
    fun _ hk1j hjk hxl => deltaPsi_layer_lt hG hkK hL hR hk0 hrip hq1 hT hϱ hδ W hWh hfull hZ hZk1
      ha₁ hprec hBg ψ ψ0 h hK6 hθ1 hθc hspec hwin hΛ21 hx hxZ hxc hk1j hjk hxl⟩

end RegionHistory

end Balaban.LargeField
