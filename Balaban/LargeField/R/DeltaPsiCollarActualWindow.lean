module

public import Balaban.LargeField.R.DeltaPsiCollarActualInner
public import Balaban.LargeField.R.DeltaPsiCollarActualOuter
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `DataChangeBound'` for the actual window (COLLAR-FIX §3; LF-RECONSTRUCTION III.4.6)

`dataChangeBound'_windowOfHistory_of_bdryTop`: `|δψ′| ≤ τ(n_G(x))` on `Ω₁(G)` and `≤ τ(1)` on the whole collar
of `G = windowGenSet (windowOfHistory H Z g hkK hW)`, `τ(n) = C_* Ŵ_k δ_{max(k₁, min(n,k))}`, `C_* = 3dL + 3`,
without `hcoreTop`.  Pieces: the core piece `deltaPsiColl_interior_lt_actual` (any core layer), the outer piece
`Z ∖ Z_{k₁}` by `deltaPsi_layer_lt_outer_gen`/`deltaPsi_top_outer_gen`, the boundary piece
`deltaPsi_bdry_eq_zero` (top layer, `hxb`), the exact outer collar identity (2.1) and the inner collar (2.3).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} {k : ℕ} {Z : H.Comp k} [NeZero S.L] [NeZero S.M]

/-- A site of `Z_{k₁} ∩ Ω₁(G)` has window layer index at most `k₁` (the core piece has no layer
above `k₁`). -/
theorem windowOfHistory_layerIndex_le_k1 (hkK : k ≤ K) (hW : H.RipeWindow k Z) (g : Geo S n R S.M)
    {x : Torus S.d (S.M * n k * S.L ^ k)} (hxZ : x ∈ (windowOfHistory H Z g hkK hW).Zk1)
    (hx : x ∈ ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).Ω 1) :
    ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).layerIndex x ≤
      S.k1 k := by
  obtain ⟨hj1, hjk, hl⟩ := ((windowOfHistory H Z g hkK hW).windowGenSet
    (windowOfHistory_hyp hkK hW)).layerIndex_spec hx
  by_contra hlt
  push Not at hlt
  have hmem := ((GeneratingSet.mem_layer _).1 hl).1
  have h1 := ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).Ω_antitone
    (i := S.k1 k + 1) (j := _) (by omega) (by omega) (by omega) hmem
  rw [WindowPieces.windowGenSet_Ω] at h1
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at h1
  rcases h1 with (⟨h2, _⟩ | ⟨_, h2, h3⟩) | ⟨_, _, h3⟩
  · exact windowCore_not_mem_succ (g := g) _ (k1_le hW) x h2
  · exact absurd hxZ h3
  · exact absurd (windowOfHistory_hZ (g := g) hkK hW hxZ) h3

/-- **`DataChangeBound′` for the actual window, without `hcoreTop`** (COLLAR-FIX §3, (2.1), (2.3);
LF-RECONSTRUCTION III.4.6 (2.48′)): `|δψ′| ≤ τ(n_G(x))` on `Ω₁(G)` and `≤ τ(1)` on the collar, where
`τ(m) = (3dL + 3) Ŵ_k δ_{max(k₁, min(m,k))}`.  The `bdryTop` in the name is the restriction `hxb` (a boundary
piece site of `Ω₁(G)` lies in the top layer `k` of `𝔹_k(U_k)`), as in `deltaPsi_le_pieces'`: the lower layers
of `𝔹_k(U_k) ∩ Z^c ∩ U^∼_k` are not covered.

Hypotheses and sources.
* `hG hk0 hrip hq1 hT hϱ hδ hW g`: the source setting (goodness, ripe `Z` of scale `k ≤ k₀`, (H-T), `L M R_base ≥
  2dL`, the admissible sequence of Lemma III.4.5); `hW` and `g` are the typing data of `windowOfHistory`;
* `ha₁ hprec hBg`: the weight `a₁ > 0`, `𝔹_{k₁,k} ≺ 𝔹_k(U_k)` (typing of `windowData`), the background hypothesis
  of P3 at the separation `winSep g`;
* `ψ ψ0 h K6 hK6 hθ1 hθc hspec hwin`: the data and (2.42)-(2.43), (1.24) of the reference field of III.4.6;
* `hΛ21`, `hΛ21'`: (Λ21), (Λ21′) of LFR §I.1.3 (conditions on constants);
* `hCreg hband`: `0 ≤ C_reg` and the bond bound of `regSetT` against `regSetTExt` (Definition II.5.6;
  `bond_le_Creg_of_chiDomProp` on the history torus, the transfer to the window torus is the torus-cast bridge);
* `hoff`: `ψ⁰_k = ψ_k` off `Z` (P7 (2.44)); `hxb`: top layer of the boundary-piece sites of `Ω₁(G)`. -/
theorem dataChangeBound'_windowOfHistory_of_bdryTop
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
    (hband : ∀ y ∈ regSetT H Z S.M (S.k1 k), ∀ y' ∈ regSetTExt H Z S.M (S.k1 k),
      (∃ x ∈ (windowOfHistory H Z g hkK hW).full.layer (S.k1 k),
        jBlock S.d S.L (S.M * n k) k (S.k1 k) x = y) →
      (∃ x ∈ (windowOfHistory H Z g hkK hW).full.layer (S.k1 k),
        jBlock S.d S.L (S.M * n k) k (S.k1 k) x = y') → AdjT y y' →
      dist (ψ ⟨S.k1 k, y⟩) (ψ ⟨S.k1 k, y'⟩) ≤ Creg * δ (S.k1 k))
    (hΛ21' : (((S.d * ((2 * ⌊R (S.k1 k - 1)⌋₊ + 3) * S.M) : ℕ) : ℝ) + 1) * Creg ≤ S.hatW ε k)
    (hoff : ∀ x ∈ dataSites (windowOfHistory H Z g hkK hW).bdry,
      x ∉ (windowOfHistory H Z g hkK hW).Z →
      ψ0 ⟨k, jBlock S.d S.L (S.M * n k) k k x⟩ = ψ ⟨k, jBlock S.d S.L (S.M * n k) k k x⟩)
    (hxb : ∀ x ∈ ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).Ω 1,
      x ∈ (windowOfHistory H Z g hkK hW).Unb → x ∉ (windowOfHistory H Z g hkK hW).Z →
      x ∈ (windowOfHistory H Z g hkK hW).bdry.Ω 1 → x ∈ (windowOfHistory H Z g hkK hW).bdry.layer k) :
    DataChangeBound' (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)
      (windowOfHistory_parentRefines H Z g hkK hW) hprec (compWeight S.L a₁) ψ ψ0 h
      (fun m => (3 * S.d * S.L + 3) * S.hatW ε k * δ (max (S.k1 k) (min m k))) := by
  classical
  have hS := H.F.ok
  have hL := hS.two_le_L
  have hqk1 : S.k1 k = (H.bk k Z).q := hW.core_k1
  have hk1 : 1 ≤ S.k1 k := by rw [hqk1]; exact hq1
  have hkq : S.k1 k < k := by
    rw [hqk1]
    have := hW.core_window.1
    have : 1 ≤ S.nq (H.bk k Z).q := by unfold Setting.nq; omega
    omega
  have hW0 := hatW_nonneg (S := S) ε k
  have hfullΩ : ∀ j, (windowOfHistory H Z g hkK hW).full.Ω j =
      (H.locGen Z S.M hkK hL (fun j _ _ => g.hRlow j)).Ω j := fun j => windowOfHistory_full_Ω hkK hW j
  have hZ : ((windowOfHistory H Z g hkK hW).Z : Set (Torus S.d (S.M * n k * S.L ^ k))) =
      H.locFine Z S.M k := by
    ext x; rw [Finset.mem_coe, windowOfHistory_Z, mem_locFineFin]
  have hZk1 : ((windowOfHistory H Z g hkK hW).Zk1 : Set (Torus S.d (S.M * n k * S.L ^ k))) =
      H.locFine Z S.M (S.k1 k) := by
    ext x; rw [Finset.mem_coe, windowOfHistory_Zk1, mem_locFineFin]
  have hdpos : ∀ m, 0 ≤ δ (max (S.k1 k) (min m k)) := fun m =>
    (hδ.pos _ (le_max_left _ _) (max_le hkq.le (min_le_right _ _))).le
  refine dataChangeBound'_of_pieces _ _ _ _ _ ψ ψ0 h ?_ (by omega)
    (windowOfHistory_hOmK1 (g := g) hkK hW) (windowOfHistory_hsupp (g := g) hkK hW)
    (windowOfHistory_hOmK (g := g) hkK hW (by omega)) hoff ?_ ?_
  · exact mul_nonneg (mul_nonneg (by positivity) hW0) (hdpos 1)
  · intro x hx
    have hxmem := hx
    rw [WindowPieces.windowGenSet_Ω] at hxmem
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hxmem
    obtain ⟨hj01, hj0k, hxj0⟩ := ((windowOfHistory H Z g hkK hW).windowGenSet
      (windowOfHistory_hyp hkK hW)).layerIndex_spec hx
    set j := ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).layerIndex x
      with hjdef
    have hC0 : (0 : ℝ) ≤ (3 * S.d * S.L + 2) * S.hatW ε k := by positivity
    rcases hxmem with (⟨hxc1, hxZ1⟩ | ⟨hxf, hxZ, hxnZ1⟩) | ⟨hxbd, hxU, hxnZ⟩
    · -- the core piece
      have hlt := deltaPsiColl_interior_lt_actual hG hkK hW g hk0 hrip hq1 hT hϱ hδ ha₁ hprec hBg ψ ψ0 h
        hK6 hθ1 hθc hspec hwin hΛ21 hCreg hband hΛ21' hx hxZ1
      have hjle := windowOfHistory_layerIndex_le_k1 hkK hW g hxZ1 hx
      have hcl : max (S.k1 k) (min j k) = S.k1 k := by omega
      show _ ≤ (3 * S.d * S.L + 3) * S.hatW ε k * δ (max (S.k1 k) (min j k))
      rw [hcl]
      have h0 : 0 ≤ S.hatW ε k * δ (S.k1 k) := mul_nonneg hW0 (hδ.pos _ le_rfl hkq.le).le
      nlinarith
    · -- the outer piece
      have hxZ' : x ∈ H.locFine Z S.M k := by rw [← hZ]; exact hxZ
      have hxc' : x ∉ H.locFine Z S.M (S.k1 k) := by rw [← hZk1]; exact hxnZ1
      have hxlf : x ∈ (H.locGen Z S.M hkK hL (fun j _ _ => g.hRlow j)).layer j := by
        have h1 := (GeneratingSet.mem_layer _).1
          ((windowGen_mem_layer_iff _ (windowOfHistory_hyp hkK hW) hxZ hxnZ1 j).1 hxj0)
        exact (GeneratingSet.mem_layer _).2 ⟨by rw [← hfullΩ]; exact h1.1, by rw [← hfullΩ]; exact h1.2⟩
      have hxΩk1 : x ∈ (H.locGen Z S.M hkK hL (fun j _ _ => g.hRlow j)).Ω (S.k1 k) := by
        by_contra hnot
        exact hxc' (compl_Omega_subset (hkK := hkK) (hL := hL) (hR := fun j _ _ => g.hRlow j)
          hk1 hkq.le hnot)
      have hk1j : S.k1 k ≤ j := by
        by_contra hlt
        push Not at hlt
        have h1 := (GeneratingSet.mem_layer _).1 hxlf
        exact h1.2 (((H.locGen Z S.M hkK hL (fun j _ _ => g.hRlow j)).Ω_antitone (by omega) (by omega)
          (by omega)) hxΩk1)
      have hcl : max (S.k1 k) (min j k) = j := by omega
      have e : deltaPsiColl (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)
            (windowOfHistory_parentRefines H Z g hkK hW) hprec (compWeight S.L a₁) ψ ψ0 h x =
          deltaPsi ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW))
            (windowOfHistory H Z g hkK hW).bdry (compWeight S.L a₁) ψ ψ0 h x :=
        funext fun i => deltaPsiColl_eq_deltaPsi_outer _ _ _ _ _ _ _ _ hx hxZ hxnZ1 i
      rw [e]
      show _ ≤ (3 * S.d * S.L + 3) * S.hatW ε k * δ (max (S.k1 k) (min j k))
      rw [hcl]
      have hδj : 0 ≤ δ j := (hδ.pos j hk1j hj0k).le
      have h0 : 0 ≤ S.hatW ε k * δ j := mul_nonneg hW0 hδj
      rcases Nat.lt_or_ge j k with hjk | hjk
      · have := deltaPsi_layer_lt_outer_gen hG hkK hL (fun j _ _ => g.hRlow j) hk0 hrip hq1 hT hϱ hδ
          (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW) hfullΩ hZ hZk1 ha₁ hprec hBg ψ ψ0 h
          hK6 hθ1 hθc hspec hwin hΛ21 hx hxZ' hxc' hk1j hjk hxj0
        nlinarith
      · have hjk' : j = k := le_antisymm hj0k hjk
        have hxΩ : x ∈ (H.locGen Z S.M hkK hL (fun j _ _ => g.hRlow j)).Ω k := by
          have := ((GeneratingSet.mem_layer _).1 hxlf).1
          rwa [hjk'] at this
        rw [deltaPsi_top_outer_gen hkK hL (fun j _ _ => g.hRlow j) (windowOfHistory H Z g hkK hW)
          (windowOfHistory_hyp hkK hW) hfullΩ hZ hZk1 ha₁ hprec ψ ψ0 h hspec hx hxZ' hxc' hxΩ, vn_zero]
        nlinarith
    · -- the boundary piece
      have hxZ1b : x ∉ (windowOfHistory H Z g hkK hW).Zk1 := fun hh =>
        hxnZ (windowOfHistory_hZ (g := g) hkK hW hh)
      have hbl := hxb x hx hxU hxnZ hxbd
      have hlayW : x ∈ ((windowOfHistory H Z g hkK hW).windowGenSet
          (windowOfHistory_hyp hkK hW)).layer k :=
        (windowGen_mem_bdry_layer_iff _ (windowOfHistory_hyp hkK hW) hxU hxnZ hxZ1b k).2 hbl
      have hjk : j = k := GeneratingSet.layerIndex_eq _ (by omega) le_rfl hlayW
      have hlay : (windowOfHistory H Z g hkK hW).full.layerIndex x = j := by
        rw [hjk]
        exact (windowOfHistory H Z g hkK hW).full.layerIndex_eq (by omega) le_rfl
          ((GeneratingSet.mem_layer _).2 ⟨windowOfHistory_hOmK (g := g) hkK hW (by omega) x hxnZ,
            by simp [(windowOfHistory H Z g hkK hW).full.top]⟩)
      have e : deltaPsiColl (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)
            (windowOfHistory_parentRefines H Z g hkK hW) hprec (compWeight S.L a₁) ψ ψ0 h x =
          deltaPsi ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW))
            (windowOfHistory H Z g hkK hW).bdry (compWeight S.L a₁) ψ ψ0 h x :=
        funext fun i => deltaPsiColl_eq_deltaPsi _ _ _ _ _ _ _ _ hx hlay i
      have hxd : x ∈ dataSites (windowOfHistory H Z g hkK hW).bdry :=
        (mem_dataSites _).2 (Or.inl (hprec.mem_Ω1 hx))
      rw [e, deltaPsi_bdry_eq_zero _ _ ha₁ hL hprec ψ ψ0 h hx hxU hxnZ hxZ1b hbl (hoff x hxd hxnZ), vn_zero]
      exact mul_nonneg (mul_nonneg (by positivity) hW0) (hdpos j)
  · intro c hc
    have hmax : max (S.k1 k) (min 1 k) = S.k1 k := by omega
    show _ ≤ (3 * S.d * S.L + 3) * S.hatW ε k * δ (max (S.k1 k) (min 1 k))
    rw [hmax]
    exact inner_collar_data_change_bound_actual hG hkK hW g hk0 hrip hq1 hT hϱ hδ hprec hBg ψ ψ0 h hK6 hθ1
      hθc hspec hwin hΛ21 hCreg hband hΛ21' hc

end RegionHistory

end Balaban.LargeField
