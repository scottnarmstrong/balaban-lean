module

public import Balaban.LargeField.R.DeltaPsi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma III.4.6, the core piece: `δψ` on `𝔹_{k₁}(W) ∩ Z_{k₁}` (P7 Lemma 2.3, (2.48′))

For `x ∈ 𝔹_{k₁}(W) ∩ Z_{k₁}` (the first piece of the window generating set) the proof of LFR Lemma III.4.6
reads: `x` lies in the top layer `Ω_{k₁}` of the core, so `ψ̃(x) = ψ_{k₁}(y)` for the `k₁`-block `y ∋ x`;
`ψ_{k₁}` is regular on the support of the small-field functions of the step `k₁ - 1 → k₁`
(`ψ_{k₁} ∈ Ψ̃(T; 3δ_{k₁})`, the form of P7 p. 501, `PsiTildeSet`), and `W` reaches at most `m_W` blocks
into `Z_{k₁}` (`≤ 2[R_{k₁-1}] + 3` cubes of `M` blocks each), so a path of at most `m_W` blocks inside
`T` leads from `y` to a window block, which costs `3 m_W δ_{k₁} ≤ Ŵ_k δ_{k₁}`; the rest is the chain of
Lemma CH from the window block, the box `Z`, and (2.43), exactly as for the outer region.

The regularity of `ψ_{k₁}` (`hTreg`) and the reach of the window (`hreach`, `3 m_W ≤ Ŵ_k`) are source
premises; they are stated for the abstract set `T` of `k₁`-blocks on which the step `k₁ - 1 → k₁` makes
`ψ_{k₁}` regular.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section Walk

/-- Along a walk of `m` steps each costing at most `B` the endpoints are at distance `≤ m B`. -/
theorem dist_walk_le {α E : Type*} [PseudoMetricSpace E] (f : α → E) (u : ℕ → α) {B : ℝ} :
    ∀ {m : ℕ}, (∀ i < m, dist (f (u i)) (f (u (i + 1))) ≤ B) →
      dist (f (u 0)) (f (u m)) ≤ m * B
  | 0, _ => by simp
  | m + 1, h => by
    have ih := dist_walk_le f u (m := m) (fun i hi => h i (by omega))
    have h1 := dist_triangle (f (u 0)) (f (u m)) (f (u (m + 1)))
    have h2 := h m (by omega)
    push_cast
    linarith

end Walk

section Window

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- On `Z_{k₁}` (`⊆ Z`) the layers of the window generating set are those of the core. -/
theorem windowGen_mem_core_iff (W : WindowPieces d L N₀ k ϱ) (h : W.Hyp)
    {x : Torus d (N₀ * L ^ k)} (hxZ1 : x ∈ W.Zk1) (hxZ : x ∈ W.Z) (m : ℕ) :
    x ∈ (W.windowGenSet h).Ω m ↔ x ∈ W.core.Ω m := by
  rw [W.windowGenSet_Ω h m]
  simp [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, hxZ1, hxZ]

theorem windowGen_mem_core_layer_iff (W : WindowPieces d L N₀ k ϱ) (h : W.Hyp)
    {x : Torus d (N₀ * L ^ k)} (hxZ1 : x ∈ W.Zk1) (hxZ : x ∈ W.Z) (m : ℕ) :
    x ∈ (W.windowGenSet h).layer m ↔ x ∈ W.core.layer m := by
  rw [GeneratingSet.mem_layer, GeneratingSet.mem_layer, windowGen_mem_core_iff W h hxZ1 hxZ,
    windowGen_mem_core_iff W h hxZ1 hxZ]

end Window

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} {k : ℕ} {Z : H.Comp k} [NeZero S.L] [NeZero S.M]

/-- **Lemma III.4.6 (2.48′), the core piece**: for `x ∈ 𝔹_{k₁}(W) ∩ Z_{k₁}` in the top layer `k₁` of the
core, `|δψ(x)| < C₂₃ Ŵ_k δ_{k₁}`, `C₂₃ = 3dL + 2`.  Premises beyond those of `deltaPsi_le_outer`: the
regularity of `ψ_{k₁}` on the set `T` of `k₁`-blocks (`hTreg`, `ψ_{k₁} ∈ Ψ̃(T; 3δ_{k₁})`), and the reach of
`W` into `Z_{k₁}` (`hreach`: from a core site of `Z_{k₁}` a path of at most `m_W` adjacent `k₁`-blocks
of `T` leads to a `k₁`-block containing a site of `Λ_{k₁} ∖ Z_{k₁}`; `3 m_W ≤ Ŵ_k`). -/
theorem deltaPsi_core_lt
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
    (T : Set (Torus S.d (S.M * n k * S.L ^ (k - S.k1 k))))
    (hTreg : PsiTildeSet T (fun u => ψ ⟨S.k1 k, u⟩) (3 * δ (S.k1 k)))
    (mW : ℕ) (hmW : 3 * (mW : ℝ) ≤ S.hatW ε k)
    (hreach : ∀ x : Torus S.d (S.M * n k * S.L ^ k), x ∈ W.core.layer (S.k1 k) →
      x ∈ H.locFine Z S.M (S.k1 k) → ∃ m ≤ mW,
        ∃ u : ℕ → Torus S.d (S.M * n k * S.L ^ (k - S.k1 k)),
          u 0 = jBlock S.d S.L (S.M * n k) k (S.k1 k) x ∧ (∀ i ≤ m, u i ∈ T) ∧
          (∀ i < m, AdjT (u i) (u (i + 1))) ∧
          ∃ s ∈ (H.locGen Z S.M hkK hL hR).layer (S.k1 k), s ∉ H.locFine Z S.M (S.k1 k) ∧
            jBlock S.d S.L (S.M * n k) k (S.k1 k) s = u m)
    {x : Torus S.d (S.M * n k * S.L ^ k)} (hx : x ∈ (W.windowGenSet hWh).Ω 1)
    (hxZ1 : x ∈ H.locFine Z S.M (S.k1 k)) (hxl : x ∈ W.core.layer (S.k1 k)) :
    vn (deltaPsi (W.windowGenSet hWh) W.bdry (compWeight S.L a₁) ψ ψ0 h x) <
      (3 * S.d * S.L + 2) * S.hatW ε k * δ (S.k1 k) := by
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
  have hxZ : x ∈ H.locFine Z S.M k :=
    locFine_mono hkK hkq.le le_rfl hxZ1
  have hxZ1' : x ∈ W.Zk1 := by rw [← Finset.mem_coe, hZk1]; exact hxZ1
  have hxZ' : x ∈ W.Z := by rw [← Finset.mem_coe, hZ]; exact hxZ
  have hlayW : x ∈ (W.windowGenSet hWh).layer (S.k1 k) :=
    (windowGen_mem_core_layer_iff W hWh hxZ1' hxZ' _).2 hxl
  have hlay : (W.windowGenSet hWh).layerIndex x = S.k1 k :=
    GeneratingSet.layerIndex_eq _ hk1 hkq.le hlayW
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
  have hδk1 := hδ.pos (S.k1 k) le_rfl hkq.le
  -- the path of blocks inside `T` to a window block
  obtain ⟨m, hmle, u, hu0, huT, huadj, s, hsl, hsZ, hsu⟩ := hreach x hxl hxZ1
  have hyw : IsWindowBlock (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (S.k1 k)
      (blockOf S.d S.L (S.M * n k) k (S.k1 k) s) :=
    isWindowBlock_blockOf (H.locGen Z S.M hkK hL hR) hblk hΩ hk1 le_rfl hkq hsl hsZ
  have hywu : blockOf S.d S.L (S.M * n k) k (S.k1 k) s = ⟨S.k1 k, u m⟩ := by
    simp only [blockOf]; rw [hsu]
  rw [hywu] at hyw
  have hbond : ∀ i < m, dist ((fun v => ψ ⟨S.k1 k, v⟩) (u i)) ((fun v => ψ ⟨S.k1 k, v⟩) (u (i + 1))) ≤
      3 * δ (S.k1 k) := fun i hi => by
    rw [dist_eq_norm]
    exact (hTreg.1 (u i) (huT i hi.le) (u (i + 1)) (huT (i + 1) hi) (huadj i hi)).le
  have hwalk := dist_walk_le (fun v => ψ ⟨S.k1 k, v⟩) u hbond
  simp only [hu0] at hwalk
  have hmR : (m : ℝ) ≤ mW := by exact_mod_cast hmle
  have hcore : dist (ψ (blockOf S.d S.L (S.M * n k) k (S.k1 k) x)) (ψ ⟨S.k1 k, u m⟩) ≤
      S.hatW ε k * δ (S.k1 k) := by
    have e : blockOf S.d S.L (S.M * n k) k (S.k1 k) x = ⟨S.k1 k, jBlock S.d S.L (S.M * n k) k (S.k1 k) x⟩ :=
      rfl
    rw [e]
    refine hwalk.trans ?_
    nlinarith
  obtain ⟨len, xs, hx0, hwinb, hterm, hadj, hinj, hdist⟩ :=
    lemmaCH_of_ripe hG hkK hL hR hk0 hrip hT hδ hc ψ
      (fun u v hu hv huv => winBond_intra hwin u v hu hv huv)
      (fun u v hu hv huv => winBond_cross hϱ hd1 hL (H.locGen Z S.M hkK hL hR) hk1 hZfar hc
        hδpos hwin u v hu hv huv) hkq hyw rfl
  -- the terminal block
  obtain ⟨Ut, hZUt, hdUt, hreg, hagree⟩ := hspec
  have hxδ : psiTilde (W.windowGenSet hWh) ψ x = fun i => ψ (blockOf S.d S.L (S.M * n k) k (S.k1 k) x) i := by
    funext i; rw [psiTilde_of_mem _ ψ hx, hlay]
  generalize hyk : xs len = yk at hterm hdist
  obtain ⟨ik, β⟩ := yk
  obtain ⟨hik, hall⟩ := hterm
  simp only at hik
  subst hik
  obtain ⟨s', hs'⟩ := exists_site_of_block (d := S.d) (L := S.L) (N₀ := S.M * n ik) (k := ik)
    (j := ik) le_rfl β
  have hsZ' : s' ∈ H.locFine Z S.M ik := (hall s' hs').2
  have hψk : ψ0 ⟨ik, β⟩ = ψ ⟨ik, β⟩ := hagree _ ⟨rfl, hall⟩
  have hθ0 : 0 < 3 * K6 * δ ik := by
    have := hδ.pos ik (by omega) le_rfl
    positivity
  obtain ⟨m', hm', hr⟩ := zblocks_reach (H := H) (Z := Z) hkK (by omega) hk0 hW
    (by have := hT2 ik (by omega) hk0; omega) ⟨s', hsZ', hs'⟩ ⟨x, hxZ, rfl⟩
  have hPU : {γ | ∃ x ∈ H.locFine Z S.M ik, jBlock S.d S.L (S.M * n ik) ik ik x = γ} ⊆ Ut := by
    rintro γ ⟨x', hx', rfl⟩
    exact hZUt x' hx'
  have hD2 := psi0_dist_le hPU hθ0 hreg hr
  have hmR' : (m' : ℝ) ≤ S.d * (S.M * S.crit ik) := by exact_mod_cast hm'
  -- (2.43)
  have hD3 := psiZeroWin_sub_le hL ha₁ hprec hBg ψ0 h hθ0 hθ1 hθc hdUt hreg hx
  set y := blockOf S.d S.L (S.M * n ik) ik (S.k1 ik) x with hydef
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
  have hδj := hδ.pos (S.k1 ik) le_rfl hkq.le
  have hδkj : δ ik ≤ δ (S.k1 ik) := hδ.le_of_le le_rfl hkq.le
  have hWpos : 0 < S.hatW ε ik := by
    by_contra hneg
    push Not at hneg
    have h0 := lt_of_le_of_lt dist_nonneg hdist
    have : S.hatW ε ik * (3 * S.d * S.L) * δ (S.k1 ik) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hneg hc.le) hδj.le
    linarith
  have hθm : (m' : ℝ) * (3 * K6 * δ ik) ≤ S.d * (S.M * S.crit ik) * (3 * K6 * δ ik) :=
    mul_le_mul_of_nonneg_right hmR' hθ0.le
  have hΛ' : (3 * S.d * K6 * (S.M * S.crit ik) + 2 * (bgK1 S.d S.L N * (3 * (3 * K6)))) * δ ik ≤
      S.hatW ε ik * δ ik := mul_le_mul_of_nonneg_right hΛ21 hδk.le
  have hWδ : S.hatW ε ik * δ ik ≤ S.hatW ε ik * δ (S.k1 ik) := mul_le_mul_of_nonneg_left hδkj hWpos.le
  have hT0 : 0 < S.hatW ε ik * δ (S.k1 ik) := mul_pos hWpos hδj
  have eW : S.hatW ε ik * (3 * S.d * S.L) * δ (S.k1 ik) = 3 * S.d * S.L * (S.hatW ε ik * δ (S.k1 ik)) := by ring
  have t0 := dist_triangle (ψ y) (ψ ⟨S.k1 ik, u m⟩) (ψ ⟨ik, β⟩)
  nlinarith [hdist, hD2, hD3', hθm, hΛ', hWδ, hT0, e1, e2, e3, t1, t2, eW, hcore, t0]

end RegionHistory

end Balaban.LargeField
