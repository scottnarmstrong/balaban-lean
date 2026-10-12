module

public import Balaban.LargeField.R.DeltaPsiCore
public import Balaban.LargeField.R.DeltaPhi
public import Balaban.LargeField.R.DeltaPsiBdryLayer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma III.4.6 (2.48′) on all of `Ω₁(𝔹_{k₁,k})`

The three pieces of the window generating set `𝔹_{k₁,k} = (𝔹_{k₁}(W) ∩ Z_{k₁}) ∪ (𝔹_k ∩ Z^c_{k₁} ∩ Z) ∪
(𝔹_k(U_k) ∩ Z^c ∩ U^∼_k)`:

* outer piece: `deltaPsi_le_outer` (`DeltaPsi.lean`);
* core piece: `deltaPsi_core_lt` (`DeltaPsiCore.lean`);
* boundary piece (`deltaPsi_bdry_eq_zero`): a site of `U^∼_k ∖ Z` lies in the single top layer of
  `𝔹_k(U_k)`, and `ψ⁰_k = ψ_k` off `Z` (P7 (2.44)), so `δψ = 0`.

`deltaPsi_le_pieces'` is (2.48′) on `Ω₁(𝔹_{k₁,k})` minus the lower boundary layers: `|δψ| ≤ C₂₃ Ŵ_k δ_{max(k₁, min(n,k))}` for `x` of layer `n`.
`dataChangeBound_of_collar` assembles `DataChangeBound` from it and the collar inequality.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section Bdry

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- Off `Z` (so off `Z_{k₁} ⊆ Z`) the layers of the window generating set are those of `𝔹_k(U_k)`. -/
theorem windowGen_mem_bdry_layer_iff (W : WindowPieces d L N₀ k ϱ) (h : W.Hyp)
    {x : Torus d (N₀ * L ^ k)} (hxU : x ∈ W.Unb) (hxZ : x ∉ W.Z) (hxZ1 : x ∉ W.Zk1) (m : ℕ) :
    x ∈ (W.windowGenSet h).layer m ↔ x ∈ W.bdry.layer m := by
  have key : ∀ m, x ∈ (W.windowGenSet h).Ω m ↔ x ∈ W.bdry.Ω m := by
    intro m
    rw [W.windowGenSet_Ω h m]
    simp [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, hxZ1, hxZ, hxU]
  rw [GeneratingSet.mem_layer, GeneratingSet.mem_layer, key, key]

/-- **Lemma III.4.6, boundary piece**: `δψ = 0` on `𝔹_k(U_k) ∩ Z^c ∩ U^∼_k` (the sites of `Ω₁` of the window
generating set off `Z`).  Premises: such a site lies in the top layer `k` of `𝔹_k(U_k)` (`hbl`) and
`ψ⁰_k = ψ_k` on its `k`-block (P7 (2.44), `ψ⁰_k = ψ_k` off `Z₀`; `hoff`). -/
theorem deltaPsi_bdry_eq_zero (W : WindowPieces d L N₀ k ϱ) (hWh : W.Hyp) {a₁ : ℝ} (ha₁ : 0 < a₁)
    (hL : 2 ≤ L) (hprec : Precedes (W.windowGenSet hWh) W.bdry)
    (ψ ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ (W.windowGenSet hWh).Ω 1) (hxU : x ∈ W.Unb)
    (hxZ : x ∉ W.Z) (hxZ1 : x ∉ W.Zk1) (hbl : x ∈ W.bdry.layer k)
    (hoff : ψ0 ⟨k, jBlock d L N₀ k k x⟩ = ψ ⟨k, jBlock d L N₀ k k x⟩) :
    deltaPsi (W.windowGenSet hWh) W.bdry (compWeight L a₁) ψ ψ0 h x = 0 := by
  classical
  have hk1 : 1 ≤ k := one_le_of_mem_Ω1 hx
  have hxl : x ∈ (W.windowGenSet hWh).layer k := (windowGen_mem_bdry_layer_iff W hWh hxU hxZ hxZ1 k).2 hbl
  have hlay : (W.windowGenSet hWh).layerIndex x = k := GeneratingSet.layerIndex_eq _ hk1 le_rfl hxl
  have hlay' : W.bdry.layerIndex x = k := GeneratingSet.layerIndex_eq _ hk1 le_rfl hbl
  have hxd : x ∈ dataSites W.bdry := (mem_dataSites W.bdry).2 (Or.inl (hprec.mem_Ω1 hx))
  funext i
  rw [deltaPsi_of_mem _ _ _ _ _ _ hx i]
  have hz : psiZeroWin (W.windowGenSet hWh) W.bdry (compWeight L a₁) ψ0 h x i =
      ((ψ0 ⟨k, jBlock d L N₀ k k x⟩ i : ℝ) : ℂ) := by
    unfold psiZeroWin
    rw [composeField_eq_data_top _ _ hx (compWeight_pos hL ha₁ hk1).ne' hlay hlay' i]
    unfold psiZeroData
    rw [liftSingle_Ψ W.bdry _ _ hxd]
  rw [hz]
  have : psiTilde (W.windowGenSet hWh) ψ x i = ψ0 ⟨k, jBlock d L N₀ k k x⟩ i := by
    rw [psiTilde_of_mem _ ψ hx, hlay, hoff]
    rfl
  rw [this]
  simp

end Bdry

section Assemble

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-- **`DataChangeBound` from (2.48′) on `Ω₁` and the collar inequality**: if `|δψ| ≤ C δ_{max(k₁,min(n,k))}`
on the sites of layer `n` of `Ω₁(G)` (`deltaPsi_le_pieces`), and the collar inequality holds with `τ₁ = C δ_{k₁}`, then
the data-change hypothesis of `deltaPhi_le_of_dataChange` holds. -/
theorem dataChangeBound_of_le (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')
    (a : ℕ → ℝ) (ψ ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ) (C : ℝ) (k1 : ℕ)
    {δ : ℕ → ℝ}
    (hΩ : ∀ x ∈ G.Ω 1, vn (deltaPsi G G' a ψ ψ0 h x) ≤ C * δ (max k1 (min (G.layerIndex x) k)))
    (hcol : ∀ x ∈ collar G, vn (fun i => ((psiTilde G ψ x i : ℝ) : ℂ) - psiZeroWin G G' a ψ0 h x i) ≤
      C * δ (max k1 (min 1 k))) :
    DataChangeBound G G' a ψ ψ0 h (fun n => C * δ (max k1 (min n k))) :=
  ⟨hΩ, hcol⟩

end Assemble

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} {k : ℕ} {Z : H.Comp k} [NeZero S.L] [NeZero S.M]

theorem hatW_nonneg (ε : ℝ) (k : ℕ) : 0 ≤ S.hatW ε k := by
  unfold Setting.hatW
  positivity

/-- **Lemma III.4.6 ((2.48′); P7 Lemma 2.3) on all of `Ω₁(𝔹_{k₁,k})`.**  For `x ∈ Ω₁` of layer `n` of the
window generating set, `|δψ(x)| ≤ C₂₃ Ŵ_k δ_{max(k₁, min(n,k))}`, `C₂₃ = 3dL + 2` (so `δψ = 0`-type
bounds on `Ω_k` and `< C₂₃ Ŵ_k δ_j` on `Λ_j`, `k₁ ≤ j < k`, and `≤ C₂₃ Ŵ_k δ_{k₁}` on the core).

Premises beyond `deltaPsi_le_outer` are those of the core piece (`deltaPsi_core_lt`: `hTreg`, `hmW`,
`hreach`, and `hcoreTop`: the core sites of `Z_{k₁}` lie in the top layer `k₁` of `𝔹_{k₁}(W)`) and of the
boundary piece (`hoff`).

*Domain restriction (replaces the old premise `hbl`).*  The old theorem `deltaPsi_le_pieces` assumed that every
boundary-piece site of `Ω₁` lies in the top layer `k` of `𝔹_k(U_k)`.  That is false for the actual window when
`k ≥ 2` and `U_k ≠` torus (`not_bdry_top_of_data`): the cubes of `Ω_{k-1} ∖ Ω_k` next to `U_k` lie in
`U^∼_k ∖ Z`.  Here the conclusion is therefore asserted for the sites `x` with `hxb` (a boundary-piece site, if
`x` is one, is in the top layer of `𝔹_k(U_k)`), i.e. on the core, outer and top-boundary sites.  The bound on the
lower layers of `𝔹_k(U_k) ∩ Z^c ∩ U^∼_k` is not covered (see `DeltaPsiBdryLayer`).

*Naming*: this is stated for an abstract `WindowPieces`, with `hreach`, `hcoreTop` and `hoff` as
premises. The name `deltaPsi_le` stays reserved for the version on the actual ripe window, with the reach,
top-layer and off-`Z` facts derived from the history and `psiZero`. -/
theorem deltaPsi_le_pieces'
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
    (hcoreTop : ∀ x ∈ W.Zk1, x ∈ W.core.Ω 1 → x ∈ W.core.layer (S.k1 k))
    (hoff : ∀ x ∈ W.Unb, x ∉ W.Z →
      ψ0 ⟨k, jBlock S.d S.L (S.M * n k) k k x⟩ = ψ ⟨k, jBlock S.d S.L (S.M * n k) k k x⟩)
    {x : Torus S.d (S.M * n k * S.L ^ k)} (hx : x ∈ (W.windowGenSet hWh).Ω 1)
    (hxb : x ∈ W.Unb → x ∉ W.Z → x ∈ W.bdry.Ω 1 → x ∈ W.bdry.layer k) :
    vn (deltaPsi (W.windowGenSet hWh) W.bdry (compWeight S.L a₁) ψ ψ0 h x) ≤
      (3 * S.d * S.L + 2) * S.hatW ε k *
        δ (max (S.k1 k) (min ((W.windowGenSet hWh).layerIndex x) k)) := by
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
  have hC0 : (0 : ℝ) ≤ (3 * S.d * S.L + 2) * S.hatW ε k := by
    have := hatW_nonneg (S := S) ε k
    positivity
  have hδpos : ∀ i, S.k1 k ≤ i → i ≤ k → 0 < δ i := fun i h1 h2 => hδ.pos i h1 h2
  have hxmem := hx
  rw [W.windowGenSet_Ω hWh 1] at hxmem
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hxmem
  obtain ⟨hj01, hj0k, hxj0⟩ := (W.windowGenSet hWh).layerIndex_spec hx
  set j := (W.windowGenSet hWh).layerIndex x with hjdef
  rcases hxmem with (⟨hxc1, hxZ1⟩ | ⟨hxf, hxZ, hxnZ1⟩) | ⟨hxbd, hxU, hxnZ⟩
  · -- the core piece
    have hxZ1' : x ∈ H.locFine Z S.M (S.k1 k) := by rw [← hZk1]; exact hxZ1
    have hxl := hcoreTop x hxZ1 hxc1
    have hxZ : x ∈ W.Z := by
      rw [← Finset.mem_coe, hZ]; exact locFine_mono hkK hkq.le le_rfl hxZ1'
    have hlayW : x ∈ (W.windowGenSet hWh).layer (S.k1 k) :=
      (windowGen_mem_core_layer_iff W hWh hxZ1 hxZ _).2 hxl
    have hjk1 : j = S.k1 k := GeneratingSet.layerIndex_eq _ hk1 hkq.le hlayW
    have hcl : max (S.k1 k) (min j k) = S.k1 k := by omega
    rw [hcl]
    exact (deltaPsi_core_lt hG hkK hL hR hk0 hrip hq1 hT hϱ hδ W hWh hfull hZ hZk1 ha₁ hprec hBg ψ ψ0 h
      hK6 hθ1 hθc hspec hwin hΛ21 T hTreg mW hmW hreach hx hxZ1' hxl).le
  · -- the outer piece
    have hxZ' : x ∈ H.locFine Z S.M k := by rw [← hZ]; exact hxZ
    have hxc' : x ∉ H.locFine Z S.M (S.k1 k) := by rw [← hZk1]; exact hxnZ1
    have hxlf : x ∈ (H.locGen Z S.M hkK hL hR).layer j := by
      rw [← hfull]; exact (windowGen_mem_layer_iff W hWh hxZ hxnZ1 j).1 hxj0
    have hxΩk1 : x ∈ (H.locGen Z S.M hkK hL hR).Ω (S.k1 k) := by
      by_contra hnot
      exact hxc' (compl_Omega_subset (hkK := hkK) (hL := hL) (hR := hR) hk1 hkq.le hnot)
    have hk1j : S.k1 k ≤ j := by
      by_contra hlt
      push Not at hlt
      have h1 := (GeneratingSet.mem_layer _).1 hxlf
      exact h1.2 (((H.locGen Z S.M hkK hL hR).Ω_antitone (by omega) (by omega) (by omega)) hxΩk1)
    have hcl : max (S.k1 k) (min j k) = j := by omega
    rw [hcl]
    obtain ⟨hA, hB⟩ := deltaPsi_le_outer hG hkK hL hR hk0 hrip hq1 hT hϱ hδ W hWh hfull hZ hZk1 ha₁ hprec
      hBg ψ ψ0 h hK6 hθ1 hθc hspec hwin hΛ21 hx hxZ' hxc'
    rcases Nat.lt_or_ge j k with hjk | hjk
    · exact (hB j hk1j hjk hxj0).le
    · have hjk' : j = k := le_antisymm hj0k hjk
      have hxΩ : x ∈ (H.locGen Z S.M hkK hL hR).Ω k := by
        have := ((GeneratingSet.mem_layer _).1 hxlf).1
        rwa [hjk'] at this
      rw [hA hxΩ, vn_zero]
      exact mul_nonneg hC0 (hδpos j hk1j hj0k).le
  · -- the boundary piece
    have hxZ1b : x ∉ W.Zk1 := fun hh => hxnZ (by
      rw [← Finset.mem_coe, hZ]
      have : x ∈ H.locFine Z S.M (S.k1 k) := by rw [← hZk1]; exact hh
      exact locFine_mono hkK hkq.le le_rfl this)
    have hbl' := hxb hxU hxnZ hxbd
    have hlayW : x ∈ (W.windowGenSet hWh).layer k :=
      (windowGen_mem_bdry_layer_iff W hWh hxU hxnZ hxZ1b k).2 hbl'
    have hjk : j = k := GeneratingSet.layerIndex_eq _ (by omega) le_rfl hlayW
    have hcl : max (S.k1 k) (min j k) = k := by omega
    rw [hcl, deltaPsi_bdry_eq_zero W hWh ha₁ hL hprec ψ ψ0 h hx hxU hxnZ hxZ1b hbl' (hoff x hxU hxnZ),
      vn_zero]
    exact mul_nonneg hC0 (hδpos k hkq.le le_rfl).le

end RegionHistory

end Balaban.LargeField
