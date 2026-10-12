module

public import Balaban.LargeField.R.DeltaPsiCollarInner

/-!
# `DataChangeBound'` for the window (COLLAR-FIX §3)

`dataChangeBound'_window_of_coreTop`: `|δψ′| ≤ τ(n_G(x))` on `Ω₁(G)` and `≤ τ(1)` on the whole collar `C_G`, with
`τ(n) = C_* Ŵ_k δ_{max(k₁, min(n,k))}`, `C_* = 3dL + 3`.  Pieces: the landed interior bound
`deltaPsi_le_pieces'` on `Ω₁(G)` (the parent and window layers agree there: top core layer `k₁` by `hcore`
and `hZk1top`, `Z ∖ Z_{k₁}` by `layerIndex_window_eq_full`, the top-layer boundary piece by `hxb`), the exact outer
identity (2.1), and the inner-collar bound (2.3) (`inner_collar_data_change_bound_of_coreTop`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} {k : ℕ} {Z : H.Comp k} [NeZero S.L] [NeZero S.M]

/-- **`DataChangeBound′` for the window** (COLLAR-FIX §3, (2.1), (2.3), P7 (2.48′)). Conditional on `hcoreTop` (every core site of the window lies in the top layer `k₁`), which COLLAR-FIX §2 does not derive for the actual core; no instance with a nonempty inner collar is landed, so non-vacuity of the premise set is open. It is restricted to top-layer boundary sites through `hxb`, as in `deltaPsi_le_pieces'`. -/
theorem dataChangeBound'_window_of_coreTop
    (hG : S.Good) (hkK : k ≤ K) (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j)
    (hk0 : k ≤ k0) (hrip : S.Ripe k (H.bk k Z)) (hq1 : 1 ≤ (H.bk k Z).q)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.numax j * (S.crit j + S.omega j) + 4 ≤ n j)
    (hϱ : (2 * S.d * S.L : ℝ) ≤ (S.L : ℝ) * S.M * S.Rb)
    {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k) k δ)
    (W : WindowPieces S.d S.L (S.M * n k) k ((S.L : ℝ) * S.M * S.Rb)) (hWh : W.Hyp)
    (hfull : W.full = H.locGen Z S.M hkK hL hR)
    (hZ : (W.Z : Set (Torus S.d (S.M * n k * S.L ^ k))) = H.locFine Z S.M k)
    (hZk1 : (W.Zk1 : Set (Torus S.d (S.M * n k * S.L ^ k))) = H.locFine Z S.M (S.k1 k))
    {a₁ : ℝ} (ha₁ : 0 < a₁) (href : ParentRefines (W.windowGenSet hWh) W.full)
    (hprec : Precedes (W.windowGenSet hWh) W.bdry)
    (hBg : BgHyp S.d S.L k ((S.L : ℝ) * S.M * S.Rb) (compWeight S.L a₁) 0)
    {N : ℕ} (ψ ψ0 : BlockV S.d S.L (S.M * n k) k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    {K6 : ℝ} (hK6 : 0 < K6) (hθ1 : 3 * K6 * δ k ≤ 1)
    (hθc : 3 * (3 * K6 * δ k) ≤ bgC1 S.d S.L N)
    (hspec : PsiZeroSpec (H.locGen Z S.M hkK hL hR) W.bdry (H.locFine Z S.M k) (3 * K6 * δ k) ψ ψ0)
    (hwin : WinBond (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (H.locFine Z S.M k)
      (S.k1 k) (3 * S.d * S.L) δ ψ)
    (hΛ21 : 3 * S.d * K6 * (S.M * S.crit k) + 2 * (bgK1 S.d S.L N * (3 * (3 * K6))) ≤ S.hatW ε k)
    (T : Set (Torus S.d (S.M * n k * S.L ^ (k - S.k1 k)))) (mW : ℕ) {Creg : ℝ} (hCreg : 0 ≤ Creg)
    (hTband : ∀ y ∈ T, ∀ y' ∈ T, AdjT y y' → ‖ψ ⟨S.k1 k, y⟩ - ψ ⟨S.k1 k, y'⟩‖ ≤ Creg * δ (S.k1 k))
    (hΛ21' : ((mW : ℝ) + 1) * Creg ≤ S.hatW ε k)
    (hcoreTop : ∀ x ∈ W.Zk1, x ∈ W.core.Ω 1 → x ∈ W.core.layer (S.k1 k))
    (hreach : ∀ x ∈ W.core.layer (S.k1 k), x ∈ W.Zk1 → ∃ m ≤ mW,
      TPathToWindow W.full W.Zk1 (S.k1 k) T (jBlock S.d S.L (S.M * n k) k (S.k1 k) x) m)
    (hexitLayer : ∀ x ∈ (W.windowGenSet hWh).Ω 1, x ∉ W.Zk1 → ∀ c, Adj x c → c ∈ W.Zk1 →
      x ∈ W.full.layer (S.k1 k))
    (hcT : ∀ c ∈ collarIn W hWh, jBlock S.d S.L (S.M * n k) k (S.k1 k) c ∈ T)
    (hwT : ∀ x ∈ (W.windowGenSet hWh).Ω 1, x ∉ W.Zk1 → x ∈ W.full.layer (S.k1 k) →
      jBlock S.d S.L (S.M * n k) k (S.k1 k) x ∈ T)
    (hmargin : ∀ x ∈ (W.windowGenSet hWh).Ω 1, ∀ c, Adj x c → c ∈ W.Zk1 → c ∈ W.full.Ω (S.k1 k))
    (hZk1top : ∀ x ∈ W.Zk1, x ∉ W.full.Ω (S.k1 k + 1))
    (hTreg : PsiTildeSet T (fun u => ψ ⟨S.k1 k, u⟩) (3 * δ (S.k1 k)))
    (hmW : 3 * (mW : ℝ) ≤ S.hatW ε k)
    (hcore : ∀ n, 1 ≤ n → n ≤ k → W.core.Ω n ∩ W.Zk1 ⊆ W.full.Ω n)
    (hOmK1 : ∀ x, x ∉ W.Zk1 → x ∈ W.full.Ω 1) (hsupp : ∀ x ∈ W.bdry.Ω 1, x ∈ W.Unb)
    (hOmK : ∀ x, x ∉ W.Z → x ∈ W.full.Ω k)
    (hoff : ∀ x, (x ∈ W.Unb ∨ x ∈ dataSites W.bdry) → x ∉ W.Z →
      ψ0 ⟨k, jBlock S.d S.L (S.M * n k) k k x⟩ = ψ ⟨k, jBlock S.d S.L (S.M * n k) k k x⟩)
    (hxb : ∀ x ∈ (W.windowGenSet hWh).Ω 1, x ∈ W.Unb → x ∉ W.Z → x ∈ W.bdry.Ω 1 → x ∈ W.bdry.layer k)
    :
    DataChangeBound' W hWh href hprec (compWeight S.L a₁) ψ ψ0 h
      (fun m => (3 * S.d * S.L + 3) * S.hatW ε k * δ (max (S.k1 k) (min m k))) := by
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
  have hZsub : W.Zk1 ⊆ W.Z := fun x hx => by
    rw [← Finset.mem_coe, hZ]
    have : x ∈ H.locFine Z S.M (S.k1 k) := by rw [← hZk1]; exact hx
    exact locFine_mono hkK hkq.le le_rfl this
  have hW0 := hatW_nonneg (S := S) ε k
  have hreach' : ∀ x : Torus S.d (S.M * n k * S.L ^ k), x ∈ W.core.layer (S.k1 k) →
      x ∈ H.locFine Z S.M (S.k1 k) → ∃ m ≤ mW,
        ∃ u : ℕ → Torus S.d (S.M * n k * S.L ^ (k - S.k1 k)),
          u 0 = jBlock S.d S.L (S.M * n k) k (S.k1 k) x ∧ (∀ i ≤ m, u i ∈ T) ∧
          (∀ i < m, AdjT (u i) (u (i + 1))) ∧
          ∃ s ∈ (H.locGen Z S.M hkK hL hR).layer (S.k1 k), s ∉ H.locFine Z S.M (S.k1 k) ∧
            jBlock S.d S.L (S.M * n k) k (S.k1 k) s = u m := by
    intro x hxl hxZ1
    obtain ⟨m, hm, u, hu0, huT, huA, s, hs, hsZ, hsu⟩ :=
      hreach x hxl (by rw [← Finset.mem_coe, hZk1]; exact hxZ1)
    refine ⟨m, hm, u, hu0, huT, huA, s, by rw [← hfull]; exact hs, fun hh => hsZ ?_, hsu⟩
    rw [← Finset.mem_coe, hZk1]; exact hh
  have hoffU : ∀ x ∈ W.Unb, x ∉ W.Z →
      ψ0 ⟨k, jBlock S.d S.L (S.M * n k) k k x⟩ = ψ ⟨k, jBlock S.d S.L (S.M * n k) k k x⟩ :=
    fun x hx hxZ => hoff x (Or.inl hx) hxZ
  refine dataChangeBound'_of_pieces W hWh href hprec (compWeight S.L a₁) ψ ψ0 h ?_ (by omega) hOmK1 hsupp hOmK
    (fun x hx hxZ => hoff x (Or.inr hx) hxZ) ?_ ?_
  · exact mul_nonneg (mul_nonneg (by positivity) hW0)
      (hδ.pos _ (le_max_left _ _) (max_le hkq.le (min_le_right _ _))).le
  · intro x hx
    -- the parent and window layers agree
    have hxmem := hx
    rw [W.windowGenSet_Ω hWh 1] at hxmem
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hxmem
    obtain ⟨hj01, hj0k, hxj0⟩ := (W.windowGenSet hWh).layerIndex_spec hx
    have hlay : W.full.layerIndex x = (W.windowGenSet hWh).layerIndex x := by
      rcases hxmem with (⟨hxc1, hxZ1⟩ | ⟨hxf, hxZ, hxnZ1⟩) | ⟨hxbd, hxU, hxnZ⟩
      · have hxl := hcoreTop x hxZ1 hxc1
        have hlayW : x ∈ (W.windowGenSet hWh).layer (S.k1 k) :=
          (windowGen_mem_core_layer_iff W hWh hxZ1 (hZsub hxZ1) _).2 hxl
        rw [GeneratingSet.layerIndex_eq _ hk1 hkq.le hlayW]
        have hfl : x ∈ W.full.layer (S.k1 k) :=
          (GeneratingSet.mem_layer _).2 ⟨hcore _ hk1 hkq.le
            (Finset.mem_inter.2 ⟨((GeneratingSet.mem_layer _).1 hxl).1, hxZ1⟩), hZk1top x hxZ1⟩
        exact W.full.layerIndex_eq hk1 hkq.le hfl
      · exact layerIndex_window_eq_full W hWh hxZ hxnZ1 hx
      · have hZ1 : x ∉ W.Zk1 := fun hh => hxnZ (hZsub hh)
        have hbl := hxb x hx hxU hxnZ hxbd
        have hlayW : x ∈ (W.windowGenSet hWh).layer k :=
          (windowGen_mem_bdry_layer_iff W hWh hxU hxnZ hZ1 k).2 hbl
        rw [GeneratingSet.layerIndex_eq _ (by omega) le_rfl hlayW]
        exact W.full.layerIndex_eq (by omega) le_rfl
          ((GeneratingSet.mem_layer _).2 ⟨hOmK x hxnZ, by simp [W.full.top]⟩)
    have e : deltaPsiColl W hWh href hprec (compWeight S.L a₁) ψ ψ0 h x =
        deltaPsi (W.windowGenSet hWh) W.bdry (compWeight S.L a₁) ψ ψ0 h x :=
      funext fun i => deltaPsiColl_eq_deltaPsi W hWh href hprec _ ψ ψ0 h hx hlay i
    rw [e]
    refine (deltaPsi_le_pieces' hG hkK hL hR hk0 hrip hq1 hT hϱ hδ W hWh hfull hZ hZk1 ha₁ hprec hBg ψ ψ0 h
      hK6 hθ1 hθc hspec hwin hΛ21 T hTreg mW hmW hreach' hcoreTop hoffU hx (hxb x hx)) |>.trans ?_
    have hj : S.k1 k ≤ max (S.k1 k) (min ((W.windowGenSet hWh).layerIndex x) k) := le_max_left _ _
    have hjk : max (S.k1 k) (min ((W.windowGenSet hWh).layerIndex x) k) ≤ k :=
      max_le hkq.le (min_le_right _ _)
    have hd := (hδ.pos _ hj hjk).le
    have h0 : 0 ≤ S.hatW ε k * δ (max (S.k1 k) (min ((W.windowGenSet hWh).layerIndex x) k)) :=
      mul_nonneg hW0 hd
    nlinarith
  · intro c hc
    have hmax : max (S.k1 k) (min 1 k) = S.k1 k := by omega
    rw [hmax]
    exact inner_collar_data_change_bound_of_coreTop hG hkK hL hR hk0 hrip hq1 hT hϱ hδ W hWh hfull hZ hZk1 href
      hprec hBg ψ ψ0 h hK6 hθ1 hθc hspec hwin hΛ21 T mW hCreg hTband hΛ21' hcoreTop hreach hexitLayer
      hcT hwT hmargin hZk1top hc

end RegionHistory

end Balaban.LargeField
