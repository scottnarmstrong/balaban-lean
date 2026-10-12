module

public import Balaban.LargeField.R.DeltaPhiResp
public import Balaban.LargeField.R.DeltaPsi
public import Balaban.LargeField.R.ChainSeq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
*Naming*: `deltaPhi_le_of_dataChange` and `layerBounds_window_of_dataChange` are conditional on
`DataChangeBound` (the full (2.48′)); the names `deltaPhi_le`, `layerBounds_window` are reserved for the
final unconditional (2.49′).

# Lemma III.4.7: the response `δφ_{k₁,k}` to the window data change (P7 Lemma 2.4, (2.49′))

`δφ_{k₁,k} := φ_k(𝔹_{k₁,k}; ψ̃) - φ_k(𝔹_{k₁,k}; ψ⁰_{k₁,k})` (`deltaPhi`) and its multiplier
`δα_{k₁,k}` (`deltaAlpha`) are the differences of the Def-5 backgrounds of the window generating set for
the data `ψ̃` (`psiTildeData`) and `ψ⁰_{k₁,k}` (`windowData`).  `deltaPhi_le_of_dataChange` is the layered bound
(2.49′) from the layered bound (2.48′) on the data change, by P3 Proposition 2.1 in its layered form
(`layered_response`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.Fluctuation

section Profile

variable {d L k1 k : ℕ} [NeZero L]

/-- The layer profile `τ_n = C δ_{clamp(n)}` of an admissible sequence (`clamp` to `[k₁, k]`) is a
`LayerProfile` with `A₀ = e^ε`, `R = L^{(d-2)/2}`. -/
theorem layerProfile_of_adm {ε : ℝ} {δ : ℕ → ℝ} (h : IsAdmDelta d L ε k1 k δ) (hd : 2 ≤ d)
    (hk1k : k1 ≤ k) {C : ℝ} (hC : 0 < C) :
    LayerProfile k (fun n => C * δ (max k1 (min n k))) (Real.exp ε)
      ((L : ℝ) ^ (((d : ℝ) - 2) / 2)) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  refine ⟨fun n hn1 hnk => ?_, fun n hn1 hnk => ?_, fun i j hi hij hj => ?_⟩
  · exact mul_pos hC (h.pos _ (le_max_left _ _) (max_le hk1k (min_le_right _ _)))
  · have e1 : max k1 (min (n + 1) k) = n + 1 ∨ max k1 (min (n + 1) k) = k1 := by omega
    rcases le_or_gt (n + 1) k1 with h1 | h1
    · have : max k1 (min (n + 1) k) = max k1 (min n k) := by omega
      simp only [this, le_refl]
    · have e2 : max k1 (min (n + 1) k) = n + 1 := by omega
      have e3 : max k1 (min n k) = n := by omega
      simp only [e2, e3]
      exact mul_le_mul_of_nonneg_left (h.anti n (by omega) (by omega)) hC.le
  · set ci := max k1 (min i k) with hci
    set cj := max k1 (min j k) with hcj
    have hcicj : ci ≤ cj := by omega
    have hdiff : cj - ci ≤ j - i := by omega
    have hg := h.growth ci cj (le_max_left _ _) hcicj (max_le hk1k (min_le_right _ _))
    have hρ : 0 ≤ ((d : ℝ) - 2) / 2 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have hpow : (L : ℝ) ^ (((d : ℝ) - 2) / 2 * ((cj : ℝ) - ci)) ≤
        ((L : ℝ) ^ (((d : ℝ) - 2) / 2)) ^ (j - i) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
      apply mul_le_mul_of_nonneg_left _ hρ
      have : ((cj - ci : ℕ) : ℝ) ≤ ((j - i : ℕ) : ℝ) := by exact_mod_cast hdiff
      rw [Nat.cast_sub hcicj] at this
      exact this
    have hcjpos := h.pos cj (by omega) (max_le hk1k (min_le_right _ _))
    calc C * δ ci ≤ C * (Real.exp ε * (L : ℝ) ^ (((d : ℝ) - 2) / 2 * ((cj : ℝ) - ci)) * δ cj) :=
          mul_le_mul_of_nonneg_left hg hC.le
      _ ≤ C * (Real.exp ε * ((L : ℝ) ^ (((d : ℝ) - 2) / 2)) ^ (j - i) * δ cj) := by
          gcongr
      _ = Real.exp ε * ((L : ℝ) ^ (((d : ℝ) - 2) / 2)) ^ (j - i) * (C * δ cj) := by ring

end Profile

section Data

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

theorem psiTilde_layerConst (G : GeneratingSet d L N₀ k ϱ)
    (ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) :
    IsLayerConstant G (fun x i => ((psiTilde G ψ x i : ℝ) : ℂ)) := by
  intro n hn1 hnk x hx x' hx'
  have hxΩ : x ∈ G.Ω 1 := G.layer_subset hn1 hnk hx
  have hb := GeneratingSet.mem_blk.1 hx'
  have hx'l : x' ∈ G.layer n := (G.mem_layer_iff hn1 hnk hb).2 hx
  have hx'Ω : x' ∈ G.Ω 1 := G.layer_subset hn1 hnk hx'l
  funext i
  simp only [psiTilde_of_mem G ψ hxΩ, psiTilde_of_mem G ψ hx'Ω, G.layerIndex_eq hn1 hnk hx,
    G.layerIndex_eq hn1 hnk hx'l]
  have : blockOf d L N₀ k n x' = blockOf d L N₀ k n x := by
    simp only [blockOf]; rw [hb]
  rw [this]

/-- The Def-5 data of the window generating set from the multiscale field `ψ̃` (and the external
field `h`). -/
noncomputable def psiTildeData (G : GeneratingSet d L N₀ k ϱ)
    (ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ) : BgData G N :=
  BgData.clip G (fun x i => ((psiTilde G ψ x i : ℝ) : ℂ)) (fun _ i => ((h i : ℝ) : ℂ))
    (psiTilde_layerConst G ψ) (fun _ _ _ _ _ _ _ => rfl)

/-- The Def-5 data of the window generating set from the composed field `ψ⁰_{k₁,k}` (BG (6.2)). -/
noncomputable def windowData (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')
    (hprec : Precedes G G') (a : ℕ → ℝ) (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N))
    (h : Fin N → ℝ) : BgData G N :=
  BgData.clip G (fun x i => psiZeroWin G G' a ψ0 h x i) (fun _ i => ((h i : ℝ) : ℂ))
    (composeField_layerConst hprec a _ (psiZeroData G' ψ0 h).Ψ_layerConst)
    (fun _ _ _ _ _ _ _ => rfl)

/-- **`δφ_{k₁,k}`** (P7 (2.46)–(2.49)): `φ_k(𝔹_{k₁,k}; ψ̃) - φ_k(𝔹_{k₁,k}; ψ⁰_{k₁,k})`, the difference of
the massless Def-5 backgrounds of the window generating set. -/
noncomputable def deltaPhi (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')
    (hprec : Precedes G G') (a : ℕ → ℝ) (ψ ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N))
    (h : Fin N → ℝ) : G.Ω 1 × Fin N → ℂ :=
  bgField G a 0 (psiTildeData G ψ h) - bgField G a 0 (windowData G G' hprec a ψ0 h)

/-- **`δα_{k₁,k}`**: the difference of the multipliers of the two backgrounds. -/
noncomputable def deltaAlpha (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')
    (hprec : Precedes G G') (a : ℕ → ℝ) (ψ ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N))
    (h : Fin N → ℝ) : G.Ω 1 → ℂ :=
  bgMult G a 0 (psiTildeData G ψ h) - bgMult G a 0 (windowData G G' hprec a ψ0 h)

/-- **The data-change bound (2.48′) on the whole data set `Ω₁ ∪ C`** (the hypothesis of P3 Proposition
2.1): `|δψ| ≤ τ_{n(x)}` on `Ω₁` and `≤ τ₁` on the collar `C(Ω₁)`, where on the collar `δψ` is
`ψ̃ - ψ⁰_{k₁,k}` read at the fine scale. -/
def DataChangeBound (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')
    (a : ℕ → ℝ) (ψ ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    (τ : ℕ → ℝ) : Prop :=
  (∀ x ∈ G.Ω 1, vn (deltaPsi G G' a ψ ψ0 h x) ≤ τ (G.layerIndex x)) ∧
  ∀ x ∈ collar G, vn (fun i => ((psiTilde G ψ x i : ℝ) : ℂ) - psiZeroWin G G' a ψ0 h x i) ≤ τ 1

/-- `DataChangeBound` is inhabited (single-scale generating sets, the zero field, `τ ≥ 0`). -/
theorem dataChangeBound_nonempty (hk : 1 ≤ k) {a : ℕ → ℝ} (ha : a k ≠ 0) {τ : ℕ → ℝ}
    (hτ : ∀ n, 0 ≤ τ n) (h : Fin N → ℝ) :
    ∃ ψ ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N),
      DataChangeBound (singleGen d L N₀ k ϱ) (singleGen d L N₀ k ϱ') a ψ ψ0 h τ := by
  classical
  refine ⟨fun _ => 0, fun _ => 0, ?_, ?_⟩
  · intro x hx
    have hlay : (singleGen d L N₀ k ϱ).layerIndex x = k := by
      refine GeneratingSet.layerIndex_eq _ hk le_rfl ?_
      rw [GeneratingSet.mem_layer, singleGen_Ω le_rfl, singleGen_Ω_succ]
      simp
    have hlay' : (singleGen d L N₀ k ϱ').layerIndex x = k := by
      refine GeneratingSet.layerIndex_eq _ hk le_rfl ?_
      rw [GeneratingSet.mem_layer, singleGen_Ω le_rfl, singleGen_Ω_succ]
      simp
    have hz : ∀ i, psiZeroWin (singleGen d L N₀ k ϱ) (singleGen d L N₀ k ϱ') a
        (fun _ => (0 : EuclideanSpace ℝ (Fin N))) h x i = 0 := by
      intro i
      unfold psiZeroWin
      rw [composeField_eq_data_top _ _ hx ha hlay hlay' i]
      have hxd : x ∈ dataSites (singleGen d L N₀ k ϱ') :=
        (mem_dataSites _).2 (Or.inl (by rw [singleGen_Ω hk]; exact Finset.mem_univ x))
      unfold psiZeroData
      rw [liftSingle_Ψ _ _ _ hxd]
      simp
    have hd0 : deltaPsi (singleGen d L N₀ k ϱ) (singleGen d L N₀ k ϱ') a (fun _ => 0)
        (fun _ => 0) h x = 0 := by
      funext i
      rw [deltaPsi_of_mem _ _ _ _ _ _ hx i, hz i, psiTilde_of_mem _ _ hx i]
      simp
    rw [hd0, vn_zero]
    exact hτ _
  · intro x hx
    obtain ⟨hx1, -⟩ := (mem_collar _).1 hx
    exact absurd (by rw [singleGen_Ω (by omega)]; exact Finset.mem_univ x) hx1

end Data

section Main

open Balaban.Fluctuation in
/-- **Lemma III.4.7 ((2.49′); P7 Lemma 2.4)**, for the window generating set `G = 𝔹_{k₁,k}`, `G' = 𝔹_k(U_k)`
(`𝔹_{k₁,k} ≺ 𝔹_k(U_k)`), the weights of BG (6.1), and `C = C₂₃ Ŵ_k`.

There are `K_w, δ_w > 0` (depending on `d, L, N` only; P3 Proposition 2.1) such that, if the data of the
window (`ψ̃` and `ψ⁰_{k₁,k}`) lie in the real domain `𝒟_ℝ` with the Green's function setting
(`BgHyp`, `hsep`: `ϱ` large), the data change satisfies the layered bound `|δψ| ≤ C δ_j` on `Λ_j`
(`DataChangeBound`, (2.48′), with the clamp of the layer to `[k₁, k]`) and `C δ_{k₁} ≤ δ_w` (smallness, (Λ22)), then
for `y ∈ Ω₁` of layer `j` the quantities `|δφ|`, `ℓ|∂δφ|`, `ℓ²|Δδφ|`, `ℓ²|δα|` at `y` are at most
`K_w C_F e^ε L^{(d-2)/2} · C δ_j` (`LayerBounds`).  Since `L^{(d-2)/2} = L^{-2} L^{(d+2)/2}` this is
(2.49′) with `C₂₄ = K_w C_F e^ε C₂₃ / L²` (the decay factor `e^{-γ_w d(y, (Ω_k^c)^∼)}` is `1` for
`y ∈ Λ_j`, `j < k`, since then `y ∈ Ω_k^c`). -/
theorem deltaPhi_le_of_dataChange (N : ℕ) {d L : ℕ} [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₀ k : ℕ} [NeZero N₀] {ϱ ϱ' : ℝ} (G : GeneratingSet d L N₀ k ϱ)
        (G' : GeneratingSet d L N₀ k ϱ') (hprec : Precedes G G') {a : ℕ → ℝ},
        BgHyp d L k ϱ a 0 → 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1) →
        ∀ (ψ ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ) {ε : ℝ}, 0 ≤ ε →
        ∀ {k1 : ℕ}, 1 ≤ k1 → k1 ≤ k → ∀ {δ : ℕ → ℝ}, IsAdmDelta d L ε k1 k δ →
        ∀ {C : ℝ}, 0 < C → ∀ {δ₁ δ₂ : ℝ}, 0 < δ₁ → δ₁ ≤ bgC1 d L N →
        InDomainR G 0 δ₁ (psiTildeData G ψ h) → 0 < δ₂ → δ₂ ≤ bgC1 d L N →
        InDomainR G 0 δ₂ (windowData G G' hprec a ψ0 h) →
        bgK1 d L N * δ₂ ≤ deltaStar d L N → bgK1 d L N * δ₂ ≤ δw →
        DataChangeBound G G' a ψ ψ0 h (fun n => C * δ (max k1 (min n k))) →
        C * δ k1 ≤ deltaStar d L N → C * δ k1 ≤ δw →
        LayerBounds G (fun n => C * δ (max k1 (min n k)))
          (Kw * (cF d L * (Real.exp ε * (L : ℝ) ^ (((d : ℝ) - 2) / 2))))
          (deltaPhi G G' hprec a ψ ψ0 h) (deltaAlpha G G' hprec a ψ ψ0 h) := by
  classical
  obtain ⟨Kw, δw, hKw0, hδw0, hW⟩ := weightedProp51S_exists N hd hL
  refine ⟨Kw, δw, hKw0, hδw0, ?_⟩
  intro N₀ k _ ϱ ϱ' G G' hprec a H hsep ψ ψ0 h ε hε k1 hk1 hk1k δ hδ C hC δ₁ δ₂ hδ₁0 hδ₁ hD₁ hδ₂0
    hδ₂ hD₂ hK hKw' hdc hτs hτw
  have hk : 1 ≤ k := le_trans hk1 hk1k
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hρ : 0 ≤ ((d : ℝ) - 2) / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast (by omega : 2 ≤ d)
    linarith
  have hprof := layerProfile_of_adm hδ (by omega) hk1k hC
  have hA₀ : 1 ≤ Real.exp ε := Real.one_le_exp hε
  have hR : 1 ≤ (L : ℝ) ^ (((d : ℝ) - 2) / 2) := Real.one_le_rpow hL1 hρ
  have hRγ : (L : ℝ) ^ (((d : ℝ) - 2) / 2) ≤ Real.exp (gammaW d * (ϱ - 1)) := by
    rw [Real.rpow_def_of_pos hLpos]
    refine Real.exp_le_exp.2 ?_
    have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
    have hd0 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have e : gammaW d * (ϱ - 1) = 2 * (agmonRate d / 16 * (ϱ - 1)) := by unfold gammaW; ring
    rw [e]
    nlinarith
  have hτ1 : (fun n => C * δ (max k1 (min n k))) 1 = C * δ k1 := by
    simp only
    have : max k1 (min 1 k) = k1 := by omega
    rw [this]
  have hΩ : ∀ x ∈ G.Ω 1, vn (fun i => (psiTildeData G ψ h).Ψ x i - (windowData G G' hprec a ψ0 h).Ψ x i) ≤
      (fun n => C * δ (max k1 (min n k))) (G.layerIndex x) := by
    intro x hx
    have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    have e : (fun i => (psiTildeData G ψ h).Ψ x i - (windowData G G' hprec a ψ0 h).Ψ x i) =
        deltaPsi G G' a ψ ψ0 h x := by
      funext i
      rw [deltaPsi_of_mem _ _ _ _ _ _ hx i]
      simp [psiTildeData, windowData, BgData.clip, hxd]
    rw [e]; exact hdc.1 x hx
  have hcol : ∀ x ∈ collar G, vn (fun i => (psiTildeData G ψ h).Ψ x i -
      (windowData G G' hprec a ψ0 h).Ψ x i) ≤ (fun n => C * δ (max k1 (min n k))) 1 := by
    intro x hx
    have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inr hx)
    have e : (fun i => (psiTildeData G ψ h).Ψ x i - (windowData G G' hprec a ψ0 h).Ψ x i) =
        fun i => ((psiTilde G ψ x i : ℝ) : ℂ) - psiZeroWin G G' a ψ0 h x i := by
      funext i
      simp [psiTildeData, windowData, BgData.clip, hxd]
    rw [e]; exact hdc.2 x hx
  have hh : ∀ x i, (psiTildeData G ψ h).h x i = (windowData G G' hprec a ψ0 h).h x i := by
    intro x i
    simp [psiTildeData, windowData, BgData.clip]
  have hτs' : (fun n => C * δ (max k1 (min n k))) 1 ≤ deltaStar d L N := by rw [hτ1]; exact hτs
  have hτw' : (fun n => C * δ (max k1 (min n k))) 1 ≤ δw := by rw [hτ1]; exact hτw
  exact layered_response hW (N₁ := N₀) (m₁ := 0) (by simp) H hsep hδ₂0 hδ₂ hD₂ hδ₁0 hδ₁ hD₁ hK hKw'
    hh hk hprof hA₀ hR hRγ hΩ hcol hτs' hτw'

end Main

section Window

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- `L^{(d-2)/2} = L^{(d+2)/2} / L²`. -/
theorem rpow_half_sub (hL : 0 < (L : ℝ)) :
    (L : ℝ) ^ (((d : ℝ) - 2) / 2) = (L : ℝ) ^ (((d : ℝ) + 2) / 2) / (L : ℝ) ^ 2 := by
  rw [eq_div_iff (by positivity), ← Real.rpow_natCast, ← Real.rpow_add hL]
  congr 1
  push_cast; ring

/-- **(2.49′) in the shape of the source**: for `y ∈ Λ_j`, `k₁ ≤ j ≤ k - 1`, with `C = C₂₃ Ŵ_k` the
bounds of `deltaPhi_le_of_dataChange` read
`|δφ|, ℓ|∂δφ|, ℓ²|Δδφ|, ℓ²|δα| ≤ C₂₄ L^{(d+2)/2} Ŵ_k δ_j`, `C₂₄ = K_w C_F e^ε C₂₃ / L²`
(`ℓ = L^j` is the spacing at `y`). -/
theorem layerBounds_window_of_dataChange {G : GeneratingSet d L N₀ k ϱ} {Kw ε Wh : ℝ} {k1 : ℕ} {δ : ℕ → ℝ}
    {δφ : G.Ω 1 × Fin N → ℂ} {δα : G.Ω 1 → ℂ}
    (hb : LayerBounds G (fun n => ((3 * d * L + 2) * Wh) * δ (max k1 (min n k)))
      (Kw * (cF d L * (Real.exp ε * (L : ℝ) ^ (((d : ℝ) - 2) / 2)))) δφ δα)
    (hk1 : 1 ≤ k1) {y : G.Ω 1} {j : ℕ} (hy : (y : Torus d (N₀ * L ^ k)) ∈ G.layer j)
    (hk1j : k1 ≤ j) (hjk : j ≤ k) :
    (∀ i, ‖δφ (y, i)‖ ≤ Kw * cF d L * Real.exp ε * (3 * d * L + 2) / (L : ℝ) ^ 2 *
      (L : ℝ) ^ (((d : ℝ) + 2) / 2) * Wh * δ j) ∧
    (∀ μ i, G.spacing (y : Torus d (N₀ * L ^ k)) *
      ‖svec G δφ ((y : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i -
        svec G δφ (y : Torus d (N₀ * L ^ k)) i‖ ≤ Kw * cF d L * Real.exp ε * (3 * d * L + 2) /
          (L : ℝ) ^ 2 * (L : ℝ) ^ (((d : ℝ) + 2) / 2) * Wh * δ j) ∧
    (∀ i, G.spacing (y : Torus d (N₀ * L ^ k)) ^ 2 * ‖∑ μ : Fin d,
      (2 * svec G δφ (y : Torus d (N₀ * L ^ k)) i -
        svec G δφ ((y : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i -
        svec G δφ ((y : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i)‖ ≤
          Kw * cF d L * Real.exp ε * (3 * d * L + 2) / (L : ℝ) ^ 2 *
            (L : ℝ) ^ (((d : ℝ) + 2) / 2) * Wh * δ j) ∧
    G.spacing (y : Torus d (N₀ * L ^ k)) ^ 2 * ‖δα y‖ ≤ Kw * cF d L * Real.exp ε *
      (3 * d * L + 2) / (L : ℝ) ^ 2 * (L : ℝ) ^ (((d : ℝ) + 2) / 2) * Wh * δ j := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hj1 : 1 ≤ j := le_trans hk1 hk1j
  have hlay : G.layerIndex (y : Torus d (N₀ * L ^ k)) = j := G.layerIndex_eq hj1 hjk hy
  have hcl : max k1 (min j k) = j := by omega
  have hB : Kw * (cF d L * (Real.exp ε * (L : ℝ) ^ (((d : ℝ) - 2) / 2))) *
      (((3 * d * L + 2) * Wh) * δ j) = Kw * cF d L * Real.exp ε * (3 * d * L + 2) / (L : ℝ) ^ 2 *
        (L : ℝ) ^ (((d : ℝ) + 2) / 2) * Wh * δ j := by
    rw [rpow_half_sub hLpos]
    field_simp
  refine ⟨fun i => ?_, fun μ i => ?_, fun i => ?_, ?_⟩
  · have := hb.val y i
    simp only [hlay, hcl] at this
    rwa [hB] at this
  · have := hb.fwd y y.2 μ i
    simp only [hlay, hcl] at this
    rwa [hB] at this
  · have := hb.lap y y.2 i
    simp only [hlay, hcl] at this
    rwa [hB] at this
  · have := hb.alpha y
    simp only [hlay, hcl] at this
    rwa [hB] at this

end Window

end Balaban.LargeField
