module

public import Balaban.LargeField.R.DeltaPsiCollarActualWindow
public import Balaban.LargeField.R.WindowRegSetBridge
public import Balaban.LargeField.R.DeltaPsiCollarLambda21
import Mathlib.Tactic.Positivity

/-!
# The collar chain for the actual window with `hband` discharged (COLLAR-FIX (2.1)-(2.3))

W205's collar-datum bounds (`DeltaPsiCollarActual*`) have one analytic premise `hband`: the bond bound
`dist (ψ_{k₁} y) (ψ_{k₁} y') ≤ C_reg δ_{k₁}` for `y ∈ regSetT`, `y' ∈ regSetTExt` adjacent layer blocks of
`𝔹_k` (LF-RECONSTRUCTION Definition II.5.6, Lemma III.4.5).  W204's `windowOfHistory_hTband_of_chiDom`
proves it when the multiscale field lies in the support of the retained characteristic functions.

* A1: `isLayerBlock_iff` (the unfolded layer condition of W205 is `IsLayerBlock`) and
  `hband_of_chiDom` (the field `ψ` of the collar files is `windowFieldOfMulti` of a `MultiField`);
* A2: `*_of_chiDom` versions of the four main theorems.  The premises `hCreg` and `hband` are gone; in
  their place stand `ChiDomProp` (the support hypothesis) and `IsAdmDelta (k₁-1) k₁` (Lemma III.4.5).
  `C_reg = 3 d L e^ε L^((d-2)/2)`.  The constant condition (Λ21′) `(m_W+1) C_reg ≤ Ŵ_k` is itself a
  theorem of the landed constants (`Setting.Ok.lambda21'_of_radiusHyp`), so it is no longer a premise.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} {k : ℕ} {Z : H.Comp k} [NeZero S.L] [NeZero S.M]

/-- **A1.** W205's unfolded layer condition is `IsLayerBlock`. -/
theorem isLayerBlock_iff (hkK : k ≤ K) (hW : H.RipeWindow k Z) (g : Geo S n R S.M)
    (b : BlockAt S n S.M k (S.k1 k)) :
    (∃ x ∈ (windowOfHistory H Z g hkK hW).full.layer (S.k1 k),
        jBlock S.d S.L (S.M * n k) k (S.k1 k) x = b) ↔
      IsLayerBlock (windowOfHistory H Z g hkK hW).full (S.k1 k) b := Iff.rfl

/-- **A1.** The bond premise of W205's collar files for `ψ = windowFieldOfMulti ψm`, from the support
hypothesis `ChiDomProp` (`windowOfHistory_hTband_of_chiDom`), with
`C_reg = 3 d L e^ε L^((d-2)/2)`. -/
theorem hband_of_chiDom (g : Geo S n R S.M) (hkK : k ≤ K) (hW : H.RipeWindow k Z) {N : ℕ}
    (Zc : Set (Torus S.d (S.M * n k * S.L ^ k))) (δ p0 : ℕ → ℝ) (Cpsi : ℝ)
    (ψm ψ' : MultiField S n S.M k N)
    (hdom : ChiDomProp (H.localHistory S.M k k Z) k (windowOfHistory H Z g hkK hW).full Zc δ p0 Cpsi ψm ψ')
    {ε : ℝ} (hδ' : IsAdmDelta S.d S.L ε (S.k1 k - 1) (S.k1 k) δ) :
    ∀ y ∈ regSetT H Z S.M (S.k1 k), ∀ y' ∈ regSetTExt H Z S.M (S.k1 k),
      (∃ x ∈ (windowOfHistory H Z g hkK hW).full.layer (S.k1 k),
        jBlock S.d S.L (S.M * n k) k (S.k1 k) x = y) →
      (∃ x ∈ (windowOfHistory H Z g hkK hW).full.layer (S.k1 k),
        jBlock S.d S.L (S.M * n k) k (S.k1 k) x = y') → AdjT y y' →
      dist (windowFieldOfMulti ψm ⟨S.k1 k, y⟩) (windowFieldOfMulti ψm ⟨S.k1 k, y'⟩) ≤
        (3 * S.d * S.L * Real.exp ε * (S.L : ℝ) ^ (((S.d : ℝ) - 2) / 2)) * δ (S.k1 k) := by
  intro y hy y' hy' hly hly' hadj
  rw [dist_eq_norm]
  exact windowOfHistory_hTband_of_chiDom H Z hkK hW Zc δ p0 Cpsi ψm ψ' hdom hδ' hy hy' hly hly' hadj

/-- `inner_collar_data_change_lt_actual`: the premise `hband` replaced by `ChiDomProp` (LFR Definition II.5.6, Lemma III.4.5). -/
theorem inner_collar_data_change_lt_actual_of_chiDom
    (hG : S.Good) (hkK : k ≤ K) (hW : H.RipeWindow k Z) (g : Geo S n R S.M)
    (hk0 : k ≤ k0) (hrip : S.Ripe k (H.bk k Z)) (hq1 : 1 ≤ (H.bk k Z).q)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.numax j * (S.crit j + S.omega j) + 4 ≤ n j)
    (hϱ : (2 * S.d * S.L : ℝ) ≤ (S.L : ℝ) * S.M * S.Rb)
    {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k) k δ)
    {a₁ : ℝ}
    (hprec : Precedes ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW))
      (windowOfHistory H Z g hkK hW).bdry)
    (hBg : BgHyp S.d S.L k (winSep g) (compWeight S.L a₁) 0)
    {N : ℕ} (ψ0 : BlockV S.d S.L (S.M * n k) k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    {Zc : Set (Torus S.d (S.M * n k * S.L ^ k))} {p0 : ℕ → ℝ} {Cpsi : ℝ}
    (ψm ψ' : MultiField S n S.M k N)
    (hdom : ChiDomProp (H.localHistory S.M k k Z) k (windowOfHistory H Z g hkK hW).full Zc δ p0 Cpsi ψm ψ')
    (hδ' : IsAdmDelta S.d S.L ε (S.k1 k - 1) (S.k1 k) δ)
    {K6 : ℝ} (hK6 : 0 < K6) (hθ1 : 3 * K6 * δ k ≤ 1)
    (hθc : 3 * (3 * K6 * δ k) ≤ bgC1 S.d S.L N)
    (hspec : PsiZeroSpec (H.locGen Z S.M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j))
      (windowOfHistory H Z g hkK hW).bdry (H.locFine Z S.M k) (3 * K6 * δ k) (windowFieldOfMulti ψm) ψ0)
    (hwin : WinBond (H.locGen Z S.M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j))
      (H.locFine Z S.M (S.k1 k)) (H.locFine Z S.M k) (S.k1 k) (3 * S.d * S.L) δ (windowFieldOfMulti ψm))
    (hΛ21 : 3 * S.d * K6 * (S.M * S.crit k) + 2 * (bgK1 S.d S.L N * (3 * (3 * K6))) ≤ S.hatW ε k)
    {c : Torus S.d (S.M * n k * S.L ^ k)}
    (hc : c ∈ collarIn (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)) :
    vn (deltaPsiColl (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)
        (windowOfHistory_parentRefines H Z g hkK hW) hprec (compWeight S.L a₁) (windowFieldOfMulti ψm) ψ0 h c) <
      (3 * S.d * S.L + 2) * S.hatW ε k * δ (S.k1 k) := by
  have hband := hband_of_chiDom g hkK hW Zc δ p0 Cpsi ψm ψ' hdom hδ'
  exact inner_collar_data_change_lt_actual hG hkK hW g hk0 hrip hq1 hT hϱ hδ hprec hBg (windowFieldOfMulti ψm) ψ0 h hK6 hθ1 hθc hspec hwin hΛ21
    (by positivity) hband (H.F.ok.lambda21'_of_radiusHyp H.F.RH ε k) hc

/-- `deltaPsiColl_interior_lt_actual`: the premise `hband` replaced by `ChiDomProp` (LFR Definition II.5.6, Lemma III.4.5). -/
theorem deltaPsiColl_interior_lt_actual_of_chiDom
    (hG : S.Good) (hkK : k ≤ K) (hW : H.RipeWindow k Z) (g : Geo S n R S.M)
    (hk0 : k ≤ k0) (hrip : S.Ripe k (H.bk k Z)) (hq1 : 1 ≤ (H.bk k Z).q)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.numax j * (S.crit j + S.omega j) + 4 ≤ n j)
    (hϱ : (2 * S.d * S.L : ℝ) ≤ (S.L : ℝ) * S.M * S.Rb)
    {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k) k δ)
    {a₁ : ℝ} (ha₁ : 0 < a₁)
    (hprec : Precedes ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW))
      (windowOfHistory H Z g hkK hW).bdry)
    (hBg : BgHyp S.d S.L k (winSep g) (compWeight S.L a₁) 0)
    {N : ℕ} (ψ0 : BlockV S.d S.L (S.M * n k) k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    {Zc : Set (Torus S.d (S.M * n k * S.L ^ k))} {p0 : ℕ → ℝ} {Cpsi : ℝ}
    (ψm ψ' : MultiField S n S.M k N)
    (hdom : ChiDomProp (H.localHistory S.M k k Z) k (windowOfHistory H Z g hkK hW).full Zc δ p0 Cpsi ψm ψ')
    (hδ' : IsAdmDelta S.d S.L ε (S.k1 k - 1) (S.k1 k) δ)
    {K6 : ℝ} (hK6 : 0 < K6) (hθ1 : 3 * K6 * δ k ≤ 1)
    (hθc : 3 * (3 * K6 * δ k) ≤ bgC1 S.d S.L N)
    (hspec : PsiZeroSpec (H.locGen Z S.M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j))
      (windowOfHistory H Z g hkK hW).bdry (H.locFine Z S.M k) (3 * K6 * δ k) (windowFieldOfMulti ψm) ψ0)
    (hwin : WinBond (H.locGen Z S.M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j))
      (H.locFine Z S.M (S.k1 k)) (H.locFine Z S.M k) (S.k1 k) (3 * S.d * S.L) δ (windowFieldOfMulti ψm))
    (hΛ21 : 3 * S.d * K6 * (S.M * S.crit k) + 2 * (bgK1 S.d S.L N * (3 * (3 * K6))) ≤ S.hatW ε k)
    {x : Torus S.d (S.M * n k * S.L ^ k)}
    (hx : x ∈ ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).Ω 1)
    (hxZ : x ∈ (windowOfHistory H Z g hkK hW).Zk1) :
    vn (deltaPsiColl (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)
        (windowOfHistory_parentRefines H Z g hkK hW) hprec (compWeight S.L a₁) (windowFieldOfMulti ψm) ψ0 h x) <
      (3 * S.d * S.L + 2) * S.hatW ε k * δ (S.k1 k) := by
  have hband := hband_of_chiDom g hkK hW Zc δ p0 Cpsi ψm ψ' hdom hδ'
  exact deltaPsiColl_interior_lt_actual hG hkK hW g hk0 hrip hq1 hT hϱ hδ ha₁ hprec hBg (windowFieldOfMulti ψm) ψ0 h hK6 hθ1 hθc hspec hwin hΛ21
    (by positivity) hband (H.F.ok.lambda21'_of_radiusHyp H.F.RH ε k) hx hxZ

/-- `inner_collar_data_change_bound_actual`: the premise `hband` replaced by `ChiDomProp` (LFR Definition II.5.6, Lemma III.4.5). -/
theorem inner_collar_data_change_bound_actual_of_chiDom
    (hG : S.Good) (hkK : k ≤ K) (hW : H.RipeWindow k Z) (g : Geo S n R S.M)
    (hk0 : k ≤ k0) (hrip : S.Ripe k (H.bk k Z)) (hq1 : 1 ≤ (H.bk k Z).q)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.numax j * (S.crit j + S.omega j) + 4 ≤ n j)
    (hϱ : (2 * S.d * S.L : ℝ) ≤ (S.L : ℝ) * S.M * S.Rb)
    {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k) k δ)
    {a₁ : ℝ}
    (hprec : Precedes ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW))
      (windowOfHistory H Z g hkK hW).bdry)
    (hBg : BgHyp S.d S.L k (winSep g) (compWeight S.L a₁) 0)
    {N : ℕ} (ψ0 : BlockV S.d S.L (S.M * n k) k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    {Zc : Set (Torus S.d (S.M * n k * S.L ^ k))} {p0 : ℕ → ℝ} {Cpsi : ℝ}
    (ψm ψ' : MultiField S n S.M k N)
    (hdom : ChiDomProp (H.localHistory S.M k k Z) k (windowOfHistory H Z g hkK hW).full Zc δ p0 Cpsi ψm ψ')
    (hδ' : IsAdmDelta S.d S.L ε (S.k1 k - 1) (S.k1 k) δ)
    {K6 : ℝ} (hK6 : 0 < K6) (hθ1 : 3 * K6 * δ k ≤ 1)
    (hθc : 3 * (3 * K6 * δ k) ≤ bgC1 S.d S.L N)
    (hspec : PsiZeroSpec (H.locGen Z S.M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j))
      (windowOfHistory H Z g hkK hW).bdry (H.locFine Z S.M k) (3 * K6 * δ k) (windowFieldOfMulti ψm) ψ0)
    (hwin : WinBond (H.locGen Z S.M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j))
      (H.locFine Z S.M (S.k1 k)) (H.locFine Z S.M k) (S.k1 k) (3 * S.d * S.L) δ (windowFieldOfMulti ψm))
    (hΛ21 : 3 * S.d * K6 * (S.M * S.crit k) + 2 * (bgK1 S.d S.L N * (3 * (3 * K6))) ≤ S.hatW ε k)
    {c : Torus S.d (S.M * n k * S.L ^ k)}
    (hc : c ∈ collarIn (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)) :
    vn (deltaPsiColl (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)
        (windowOfHistory_parentRefines H Z g hkK hW) hprec (compWeight S.L a₁) (windowFieldOfMulti ψm) ψ0 h c) ≤
      (3 * S.d * S.L + 3) * S.hatW ε k * δ (S.k1 k) := by
  have hband := hband_of_chiDom g hkK hW Zc δ p0 Cpsi ψm ψ' hdom hδ'
  exact inner_collar_data_change_bound_actual hG hkK hW g hk0 hrip hq1 hT hϱ hδ hprec hBg (windowFieldOfMulti ψm) ψ0 h hK6 hθ1 hθc hspec hwin hΛ21
    (by positivity) hband (H.F.ok.lambda21'_of_radiusHyp H.F.RH ε k) hc

/-- `dataChangeBound'_windowOfHistory_of_bdryTop`: the premise `hband` replaced by `ChiDomProp` (LFR Definition II.5.6, Lemma III.4.5). -/
theorem dataChangeBound'_windowOfHistory_of_bdryTop_of_chiDom
    (hG : S.Good) (hkK : k ≤ K) (hW : H.RipeWindow k Z) (g : Geo S n R S.M)
    (hk0 : k ≤ k0) (hrip : S.Ripe k (H.bk k Z)) (hq1 : 1 ≤ (H.bk k Z).q)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.numax j * (S.crit j + S.omega j) + 4 ≤ n j)
    (hϱ : (2 * S.d * S.L : ℝ) ≤ (S.L : ℝ) * S.M * S.Rb)
    {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k) k δ)
    {a₁ : ℝ} (ha₁ : 0 < a₁)
    (hprec : Precedes ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW))
      (windowOfHistory H Z g hkK hW).bdry)
    (hBg : BgHyp S.d S.L k (winSep g) (compWeight S.L a₁) 0)
    {N : ℕ} (ψ0 : BlockV S.d S.L (S.M * n k) k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    {Zc : Set (Torus S.d (S.M * n k * S.L ^ k))} {p0 : ℕ → ℝ} {Cpsi : ℝ}
    (ψm ψ' : MultiField S n S.M k N)
    (hdom : ChiDomProp (H.localHistory S.M k k Z) k (windowOfHistory H Z g hkK hW).full Zc δ p0 Cpsi ψm ψ')
    (hδ' : IsAdmDelta S.d S.L ε (S.k1 k - 1) (S.k1 k) δ)
    {K6 : ℝ} (hK6 : 0 < K6) (hθ1 : 3 * K6 * δ k ≤ 1)
    (hθc : 3 * (3 * K6 * δ k) ≤ bgC1 S.d S.L N)
    (hspec : PsiZeroSpec (H.locGen Z S.M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j))
      (windowOfHistory H Z g hkK hW).bdry (H.locFine Z S.M k) (3 * K6 * δ k) (windowFieldOfMulti ψm) ψ0)
    (hwin : WinBond (H.locGen Z S.M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j))
      (H.locFine Z S.M (S.k1 k)) (H.locFine Z S.M k) (S.k1 k) (3 * S.d * S.L) δ (windowFieldOfMulti ψm))
    (hΛ21 : 3 * S.d * K6 * (S.M * S.crit k) + 2 * (bgK1 S.d S.L N * (3 * (3 * K6))) ≤ S.hatW ε k)
    (hoff : ∀ x ∈ dataSites (windowOfHistory H Z g hkK hW).bdry,
      x ∉ (windowOfHistory H Z g hkK hW).Z →
      ψ0 ⟨k, jBlock S.d S.L (S.M * n k) k k x⟩ = (windowFieldOfMulti ψm) ⟨k, jBlock S.d S.L (S.M * n k) k k x⟩)
    (hxb : ∀ x ∈ ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).Ω 1,
      x ∈ (windowOfHistory H Z g hkK hW).Unb → x ∉ (windowOfHistory H Z g hkK hW).Z →
      x ∈ (windowOfHistory H Z g hkK hW).bdry.Ω 1 → x ∈ (windowOfHistory H Z g hkK hW).bdry.layer k) :
    DataChangeBound' (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)
      (windowOfHistory_parentRefines H Z g hkK hW) hprec (compWeight S.L a₁) (windowFieldOfMulti ψm) ψ0 h
      (fun m => (3 * S.d * S.L + 3) * S.hatW ε k * δ (max (S.k1 k) (min m k))) := by
  have hband := hband_of_chiDom g hkK hW Zc δ p0 Cpsi ψm ψ' hdom hδ'
  exact dataChangeBound'_windowOfHistory_of_bdryTop hG hkK hW g hk0 hrip hq1 hT hϱ hδ ha₁ hprec hBg (windowFieldOfMulti ψm) ψ0 h hK6 hθ1 hθc hspec hwin hΛ21
    (by positivity) hband (H.F.ok.lambda21'_of_radiusHyp H.F.RH ε k) hoff hxb


end RegionHistory

end Balaban.LargeField
