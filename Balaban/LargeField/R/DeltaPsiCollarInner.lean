module

public import Balaban.LargeField.R.DeltaPsiCollarBound
public import Balaban.LargeField.R.DeltaPsiCoreFinal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The inner-collar data change (COLLAR-FIX (2.3))

For `c ∈ C_in = C_G ∩ Z_{k₁}` the physical datum reads `ψ_{k₁}(b_{k₁}(c))` (COLLAR-FIX (1.2)), the reference
reads the composed field `ψ⁰_{k₁,k}(c) = φ̄_k⁰(c)` (COLLAR-FIX (1.3)).  The path of
`inner_collar_shell_bound` ((2.2)) leads from `b_{k₁}(c)` to a window block, Lemma CH (LFR III.4.4) from
there to a terminal block, and the final comparison of LFR III.4.6 (P7 (2.43) at a collar site, here
`psiZeroWin_collar_sub_le`) to the reference value at `c`.

* `psiZeroWin_collar_sub_le`: (2.43) at a site of the collar `C_G`;
* `inner_collar_data_change_lt_of_coreTop`: `|D^ph.Ψ(c) - D⁰.Ψ(c)| < (3dL + 2) Ŵ_k δ_{k₁}`;
* `inner_collar_data_change_bound_of_coreTop`: COLLAR-FIX (2.3) with `C_∂ = 3dL + 3`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section Comp

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

/-- **(2.43) at a collar site**: for `c ∈ C_G` the reference field `ψ⁰_{k₁,k}(c) = φ̄_k⁰(c)` is within
`K₁ · 3θ` of the block value `ψ̃⁰_k` (`ψ̃⁰_k ∈ Ψ̃(T; θ)`).  At a site of `Ω₁(G)` the landed
`psiZeroWin_sub_le` has `2 K₁ · 3θ`; on the collar the composed field is the bar field of the
background itself (`composeField_of_collar`), so only the closeness `|φ - Ψ| ≤ K₁ · 3θ` of the background
to its data is used. -/
theorem psiZeroWin_collar_sub_le {a₁ : ℝ} (hprec : Precedes G G')
    (H : BgHyp d L k ϱ' (compWeight L a₁) 0) (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N))
    (h : Fin N → ℝ) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (h3 : 3 * θ ≤ bgC1 d L N)
    {T : Set (Torus d (N₀ * L ^ (k - k)))} (hT : ∀ x ∈ dataSites G', jBlock d L N₀ k k x ∈ T)
    (hψ : PsiTildeSet T (fun z => ψ0 ⟨k, z⟩) θ) {c : Torus d (N₀ * L ^ k)} (hc : c ∈ collar G) :
    vn (fun i => psiZeroWin G G' (compWeight L a₁) ψ0 h c i - ((ψ0 ⟨k, jBlock d L N₀ k k c⟩ i : ℝ) : ℂ))
      ≤ bgK1 d L N * (3 * θ) := by
  classical
  have hD : InDomainR G' 0 (3 * θ) (psiZeroData G' ψ0 h) :=
    inDomainR_liftSingle G' (fun z i => ψ0 ⟨k, z⟩ i) h T hθ0 hθ1 hT hψ
  obtain ⟨φ, α, -, hb, -, hunit, hmin, huniq⟩ := bg_real H (by positivity) h3 hD
  have hbg : bgField G' (compWeight L a₁) 0 (psiZeroData G' ψ0 h) = φ := bgField_eq hmin huniq
  have hFB : FieldBounds G' (bgK1 d L N * (3 * θ)) (psiZeroData G' ψ0 h).Ψ φ :=
    fieldBounds_of_bgBounds (fun x _ i => rfl) hb (dot_eq_one_of_unit hunit)
  have hK := bgK1_pos d L N
  -- `c` is a data site of `G'`
  obtain ⟨hcG, x, hx, hadj⟩ := (mem_collar _).1 hc
  have hcd : c ∈ dataSites G' := by
    by_cases hc1 : c ∈ G'.Ω 1
    · exact (mem_dataSites G').2 (Or.inl hc1)
    · exact (mem_dataSites G').2 (Or.inr ((mem_collar _).2 ⟨hc1, x, hprec.mem_Ω1 hx, hadj⟩))
  have h2 : (psiZeroData G' ψ0 h).Ψ c = fun i => ((ψ0 ⟨k, jBlock d L N₀ k k c⟩ i : ℝ) : ℂ) := by
    funext i
    unfold psiZeroData
    rw [liftSingle_Ψ G' _ _ hcd]
  have e : (fun i => psiZeroWin G G' (compWeight L a₁) ψ0 h c i -
        ((ψ0 ⟨k, jBlock d L N₀ k k c⟩ i : ℝ) : ℂ)) =
      fun i => barField G' (psiZeroData G' ψ0 h).Ψ φ c i - (psiZeroData G' ψ0 h).Ψ c i := by
    funext i
    have h1 : psiZeroWin G G' (compWeight L a₁) ψ0 h c i =
        barField G' (psiZeroData G' ψ0 h).Ψ φ c i := by
      unfold psiZeroWin
      rw [hbg]
      exact composeField_of_collar _ _ _ hc i
    rw [h1, congrFun h2 i]
  rw [e]
  by_cases hc1 : c ∈ G'.Ω 1
  · have := hFB.close ⟨c, hc1⟩
    convert this using 2
    funext i
    simp [barField, hc1]
  · have : (fun i => barField G' (psiZeroData G' ψ0 h).Ψ φ c i - (psiZeroData G' ψ0 h).Ψ c i) = 0 := by
      funext i
      simp [barField, hc1]
    rw [this, vn_zero]
    positivity

end Comp

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} {k : ℕ} {Z : H.Comp k} [NeZero S.L] [NeZero S.M]

/-- **COLLAR-FIX (2.3), strict form**: for `c ∈ C_in = C_G ∩ Z_{k₁}`,
`|D^ph.Ψ(c) - D⁰.Ψ(c)| < (3dL + 2) Ŵ_k δ_{k₁}`.

The proof is that of `deltaPsi_core_lt` (LFR III.4.6) with the starting point `ψ_{k₁}(b_{k₁}(c))`
instead of `ψ̃(x)` of a core site: (2.2) (`inner_collar_shell_bound`) leads to a window block at cost
`(m_W + 1) C_reg δ_{k₁} ≤ Ŵ_k δ_{k₁}`; Lemma CH (LFR III.4.4) costs `3dL Ŵ_k δ_{k₁}`; the terminal block
is connected to the reference value by P7 (2.43) at a collar site (`psiZeroWin_collar_sub_le`), bounded as
in `deltaPsi_core_lt` by `Ŵ_k δ_k ≤ Ŵ_k δ_{k₁}` using (Λ21).  What changed with respect to
`deltaPsi_core_lt`: the starting step is the shell bound for the parent spin of a collar site, and the
last comparison is the collar-site version (constant `K₁·3θ`, not `2K₁·3θ`).

Premises: the geometry of `inner_collar_shell_bound` (`hZ`, `hcoreTop`, `hreach`, `hexitLayer`, `hcT`,
`hwT`, `hmargin`, `hZk1top`), the band regularity `hT` with constant `C_reg` and the strengthened (Λ21)
`hΛ21'`: `(m_W + 1) C_reg ≤ Ŵ_k` (a condition on the constants of LFR §I.1.3), together with the
premises of `deltaPsi_core_lt` that concern the chain and the final comparison. Conditional on `hcoreTop` (every core site of the window lies in the top layer `k₁`), which COLLAR-FIX §2 does not derive for the actual core; no instance with a nonempty inner collar is landed, so non-vacuity of the premise set is open. -/
theorem inner_collar_data_change_lt_of_coreTop
    (hG : S.Good) (hkK : k ≤ K) (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j)
    (hk0 : k ≤ k0) (hrip : S.Ripe k (H.bk k Z)) (hq1 : 1 ≤ (H.bk k Z).q)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.numax j * (S.crit j + S.omega j) + 4 ≤ n j)
    (hϱ : (2 * S.d * S.L : ℝ) ≤ (S.L : ℝ) * S.M * S.Rb)
    {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k) k δ)
    (W : WindowPieces S.d S.L (S.M * n k) k ((S.L : ℝ) * S.M * S.Rb)) (hWh : W.Hyp)
    (hfull : W.full = H.locGen Z S.M hkK hL hR)
    (hZ : (W.Z : Set (Torus S.d (S.M * n k * S.L ^ k))) = H.locFine Z S.M k)
    (hZk1 : (W.Zk1 : Set (Torus S.d (S.M * n k * S.L ^ k))) = H.locFine Z S.M (S.k1 k))
    {a₁ : ℝ} (href : ParentRefines (W.windowGenSet hWh) W.full)
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
    {c : Torus S.d (S.M * n k * S.L ^ k)} (hc : c ∈ collarIn W hWh) :
    vn (deltaPsiColl W hWh href hprec (compWeight S.L a₁) ψ ψ0 h c) <
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
  have hd1 : 1 ≤ S.d := by have := hS.three_le_d; omega
  obtain ⟨hcol, hcZ1'⟩ := (mem_collarIn W hWh).1 hc
  have hcZ1 : c ∈ H.locFine Z S.M (S.k1 k) := by rw [← hZk1]; exact hcZ1'
  have hcZ : c ∈ H.locFine Z S.M k := locFine_mono hkK hkq.le le_rfl hcZ1
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
  -- (2.2): from the parent spin of `c` to a window block
  have hC0 : 0 ≤ Creg * δ (S.k1 k) := mul_nonneg hCreg hδk1.le
  obtain ⟨s, hsl, hsZ, hshell⟩ := inner_collar_shell_bound W hWh hk1 hkq.le T mW (fun x hx => by
      rw [← Finset.mem_coe, hZ]
      have : x ∈ H.locFine Z S.M (S.k1 k) := by rw [← hZk1]; exact hx
      exact locFine_mono hkK hkq.le le_rfl this)
    hcoreTop hreach hexitLayer hcT hwT hmargin hZk1top ψ hC0 hTband hc
  have hsl' : s ∈ (H.locGen Z S.M hkK hL hR).layer (S.k1 k) := by rw [← hfull]; exact hsl
  have hsZ' : s ∉ H.locFine Z S.M (S.k1 k) := fun hh => hsZ (by rw [← Finset.mem_coe, hZk1]; exact hh)
  have hyw : IsWindowBlock (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (S.k1 k)
      (blockOf S.d S.L (S.M * n k) k (S.k1 k) s) :=
    isWindowBlock_blockOf (H.locGen Z S.M hkK hL hR) hblk hΩ hk1 le_rfl hkq hsl' hsZ'
  have hcore : dist (ψ (parentBlock W.full c)) (ψ (blockOf S.d S.L (S.M * n k) k (S.k1 k) s)) ≤
      S.hatW ε k * δ (S.k1 k) := by
    refine hshell.trans ?_
    calc ((mW : ℝ) + 1) * (Creg * δ (S.k1 k)) = (((mW : ℝ) + 1) * Creg) * δ (S.k1 k) := by ring
      _ ≤ S.hatW ε k * δ (S.k1 k) := mul_le_mul_of_nonneg_right hΛ21' hδk1.le
  obtain ⟨len, xs, hx0, hwinb, hterm, hadj, hinj, hdist⟩ :=
    lemmaCH_of_ripe hG hkK hL hR hk0 hrip hT hδ hc3 ψ
      (fun u v hu hv huv => winBond_intra hwin u v hu hv huv)
      (fun u v hu hv huv => winBond_cross hϱ hd1 hL (H.locGen Z S.M hkK hL hR) hk1 hZfar hc3
        hδpos hwin u v hu hv huv) hkq hyw rfl
  obtain ⟨Ut, hZUt, hdUt, hreg, hagree⟩ := hspec
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
  -- (2.43) at the collar site
  have hD3 := psiZeroWin_collar_sub_le hprec hBg ψ0 h hθ0 hθ1 hθc hdUt hreg hcol
  set P := parentBlock W.full c with hPdef
  set C := psiZeroWin (W.windowGenSet hWh) W.bdry (compWeight S.L a₁) ψ0 h c with hC
  have hdel : deltaPsiColl W hWh href hprec (compWeight S.L a₁) ψ ψ0 h c =
      (fun i => ((ψ P i : ℝ) : ℂ)) - C := by
    funext i
    rw [deltaPsiColl_of_mem W hWh href hprec _ ψ ψ0 h ((mem_dataSites _).2 (Or.inr hcol)) i]
    have := inheritedField_eq_parentBlock W ψ c i
    unfold inheritedField at this
    rw [this]
    rfl
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
  have hD3' : vn (C - fun i => ((ψ0 ⟨ik, jBlock S.d S.L (S.M * n ik) ik ik c⟩ i : ℝ) : ℂ)) ≤
      bgK1 S.d S.L N * (3 * (3 * K6 * δ ik)) := hD3
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

/-- **COLLAR-FIX (2.3)**: `|D^ph.Ψ(c) - D⁰.Ψ(c)| ≤ C_∂ Ŵ_k δ_{k₁}`, `C_∂ = 3dL + 3`, for `c ∈ C_in`.  The
constant obtained from the landed pieces is `3dL + 2` (`inner_collar_data_change_lt_of_coreTop`); the extra unit of
the note is not needed.  Premises as in `inner_collar_data_change_lt_of_coreTop`. Conditional on `hcoreTop` (every core site of the window lies in the top layer `k₁`), which COLLAR-FIX §2 does not derive for the actual core; no instance with a nonempty inner collar is landed, so non-vacuity of the premise set is open. -/
theorem inner_collar_data_change_bound_of_coreTop
    (hG : S.Good) (hkK : k ≤ K) (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j)
    (hk0 : k ≤ k0) (hrip : S.Ripe k (H.bk k Z)) (hq1 : 1 ≤ (H.bk k Z).q)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.numax j * (S.crit j + S.omega j) + 4 ≤ n j)
    (hϱ : (2 * S.d * S.L : ℝ) ≤ (S.L : ℝ) * S.M * S.Rb)
    {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k) k δ)
    (W : WindowPieces S.d S.L (S.M * n k) k ((S.L : ℝ) * S.M * S.Rb)) (hWh : W.Hyp)
    (hfull : W.full = H.locGen Z S.M hkK hL hR)
    (hZ : (W.Z : Set (Torus S.d (S.M * n k * S.L ^ k))) = H.locFine Z S.M k)
    (hZk1 : (W.Zk1 : Set (Torus S.d (S.M * n k * S.L ^ k))) = H.locFine Z S.M (S.k1 k))
    {a₁ : ℝ} (href : ParentRefines (W.windowGenSet hWh) W.full)
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
    {c : Torus S.d (S.M * n k * S.L ^ k)} (hc : c ∈ collarIn W hWh) :
    vn (deltaPsiColl W hWh href hprec (compWeight S.L a₁) ψ ψ0 h c) ≤
      (3 * S.d * S.L + 3) * S.hatW ε k * δ (S.k1 k) := by
  have hlt := inner_collar_data_change_lt_of_coreTop hG hkK hL hR hk0 hrip hq1 hT hϱ hδ W hWh hfull hZ hZk1 href
    hprec hBg ψ ψ0 h hK6 hθ1 hθc hspec hwin hΛ21 T mW hCreg hTband hΛ21' hcoreTop hreach hexitLayer hcT
    hwT hmargin hZk1top hc
  have hS := H.F.ok
  have hW : H.RipeWindow k Z :=
    ripe_window hG (fun j hj1 hj0 => (hT_forms hS (hT j hj1 hj0)).1) hk0 hkK hrip
  have hqk1 : S.k1 k = (H.bk k Z).q := hW.core_k1
  have hkq : S.k1 k < k := by
    rw [hqk1]
    have := hW.core_window.1
    have : 1 ≤ S.nq (H.bk k Z).q := by unfold Setting.nq; omega
    omega
  have h0 : 0 ≤ S.hatW ε k * δ (S.k1 k) :=
    mul_nonneg (hatW_nonneg ε k) (hδ.pos (S.k1 k) le_rfl hkq.le).le
  nlinarith

end RegionHistory

end Balaban.LargeField
