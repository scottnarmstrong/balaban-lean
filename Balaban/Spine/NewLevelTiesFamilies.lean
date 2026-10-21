/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.NewLevelTies
public import Balaban.Inhabited.NewLevelLabelData
public import Balaban.Inhabited.StepTowerChainDomNbhd

/-!
# The new level on the local generating sets from the ties (row (iii) of A4-1b)

`StepTowerG.newLevel_localFamilies_birth_of` at the base tower, the radius constant and the flow
constant of the ties of the new level (`NewLevelTies`), with the premises that are definitions or
lemmas of the class under ruling R13 discharged:

* the chosen families and optimal structures of the labels (`exists_labelData`, the polymers
  `XL τ = labelPoly m₀ τ`);
* the cube exponent `s = hatScale L m₁ ϱ` of the local sets with `s < m₀`, the margin of the local
  sets inside the cells, the separation `ϱ ≤ minSep (L^{m₁+s})` (`exists_rhoSepG_le_minSep`) and the
  specification `HatSpec` of the class generating sets (`SFTermClausesStrong.hat`): `ClassHatCond`;
* the unit fields near the constant field lie in the birth-mass domain (`exists_birthXiDom_ball` at
  the standing hypotheses of the birth masses, `birthMass_bgHyp_of_flow`);
* the flow conditions at the rate `q = L^{-2γ}` and the flow constant `c₈` of the ties, the radius of
  the mass response, and the smallness of `ε_j` at every level (from that of `ε_1`).

`NewLevelTies.newLevel_localFamilies`: the remaining premises are the class (its strong clauses on
the birth-mass domain, its weights, the flow of its masses with the step mass `ν = ν_k L^{-2k}` small)
and the bound of its irrelevant terms on their term domain with its decay in the level (the open
input A4-1b (ii)).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Background
  Balaban.Localization Balaban.Fluctuation Balaban.Inhabited Balaban.Inhabited.LevelStep
  Balaban.SmallField.GsSpec Balaban.Multiscale Balaban.Polymer

open Classical in
/-- **The clauses (A1)–(A5) of the new level at every root, from the ties** (row (iii) of A4-1b,
route R-LOC; blocker 6).  For the ties of the new level at `(L, P₀, m₁, ϱ)` and the constants
`C_I, K_L, α₃, n₁` of the bound of the irrelevant parts there are a base tower `T₀` of the class
chain (block exponent `m₁`), a label rate `κ_dec` and `β₀` such that at every scale `k`, for
`β ≥ β₀`, every class `C` with the constants `P₀` (strong clauses on the birth-mass domain) whose
weights are those of the step and whose masses follow the flow at the rate and flow constant of the
ties, with the bound of its irrelevant terms on their term domain with its decay in the level, the
chain gives a coefficient family `e z` of every root with its rooted support and its value
`E0locJ C z`, and on the cast local sets `𝔹_{k+1}(Ŷ⁺(T′))` local families with (A1)–(A5). -/
theorem NewLevelTies.newLevel_localFamilies {d L N : ℕ} [NeZero L] [NeZero N] {P₀ : Consts}
    {m₁ : ℕ} {ϱ : ℝ} (H : NewLevelTies d N L P₀ m₁ ϱ) (hγ0 : 0 < P₀.γ) (hγ1 : P₀.γ < 1 / 2)
    (hα₀ : 0 < P₀.α₀) (hc₈ : 0 ≤ P₀.c₈) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    (CI KL α₃ : ℝ) (n₁ : ℕ) (hCI : 0 ≤ CI) (hKL : 0 ≤ KL) (hα₃ : 0 < α₃) :
    ∃ (κmin : ℝ) (T₀ : StepTowerG d L N κmin) (κdec β₀ : ℝ),
      CollarBase d L N P₀.m₀ ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - P₀.γ))) T₀ κdec ∧ T₀.m₁ = m₁ ∧
      3 ≤ β₀ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k), ∃ Tk : StepTowerG d L N κmin,
      Tk.t = 17 / 16 * P₀.eps d L (k + 1) ∧ Tk.m₁ = m₁ ∧
    ∀ (N₁ : ℕ) [NeZero N₁] (_ : L ^ P₀.m₀ ∣ N₁), 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
    ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
    ∀ (S : StepSetting d L N₁ Tk.m₁ k N ϱ) (_ : S = hatStepKG Tk.hN k Tk.m₁ ϱ hk ν β p₁ Tk.δ),
    ∃ Jr : S.JointRep Tk.t (2 * p₁),
    ∀ (C : StepClass d L N₁ Tk.m₁ k N ϱ) (Rg : Regime L) (a : ℕ → ℝ)
      (_ : P₀.m₀ = C.m₀) (_ : SFTermClausesStrong P₀ (birthXiDom P₀ Rg a N₁) C.Tm)
      (_ : 0 ≤ P₀.E₀)
      -- the weights and the flow of the masses of the class
      (_ : aIdeal L (k + 1) (a (k + 1)) = compWeight L S.a₁)
      {ξ : ℕ → Fin 3 → ℂ} {ν₀ : ℝ}
      (_ : ∀ n, ‖ξ n‖ ≤ P₀.c₈ / 4 * Flow.rate (L : ℝ) P₀.γ ^ (n + 1))
      (_ : ∀ n, n ≤ k → ((Rg.ν n : ℝ) : ℂ) = Flow.nuSeq (L : ℝ) ξ (ν₀ : ℂ) n)
      (_ : ν = physMass L k (Rg.ν k))
      (_ : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (1 + 2 * (Real.exp (3 * (P₀.c₈ / 4 *
        (Flow.rate (L : ℝ) P₀.γ ^ 2 / (1 - Flow.rate (L : ℝ) P₀.γ)))) - 1)) ≤ 1)
      -- the bounds of the irrelevant parts in `d(X)` on their term domain with their decay in the
      -- level (P1 (3.128), the open input A4-1b (ii))
      (Bl : ℕ → CTorus d L N₁ Tk.m₁ (k + 1) → Set (CTorus d L N₁ Tk.m₁ (k + 1)) → ℝ)
      (_ : ∀ j y X, 0 ≤ Bl j y X)
      (_ : ∀ (i₀ i₁ : Fin N) (j : ℕ) (y : CTorus d L N₁ Tk.m₁ (k + 1))
        (X : Set (CTorus d L N₁ Tk.m₁ (k + 1))), 1 ≤ j → j ≤ k → IsPolyDom C.m₀ j X → y ∈ X →
        ∀ Ψ h : Fld d L N₁ Tk.m₁ (k + 1) N, (birthXiDom P₀ Rg a N₁).dom j (C.Tm.gs j X) Ψ h →
        dot (Ψ y) (Ψ y) ∈ Complex.slitPlane →
        ‖irrelTorus C.m₀ C.Tm i₀ i₁ j y X Ψ h‖ ≤
          Bl j y X * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ j X))
      (_ : ∀ j y X, j + n₁ ≤ k →
        Bl j y X ≤ CI * P₀.E₀ * ((((L : ℝ)⁻¹ ^ (k - j)) ^ ((d : ℝ) + α₃))))
      (_ : ∀ j y X, k < j + n₁ → Bl j y X ≤ KL * P₀.E₀),
    ∃ e : RootIdx d L N₁ Tk.m₁ (k + 1) → physParam N S →
        Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁) (K := k + 1) 1 (k + 1) Set.univ) →
          ℂ,
      (∀ z θ T', e z θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')) ∧
      (∀ z (D : BgData S.G' N), XiCData S.G' S.a S.ν (k + 1) 1 Tk.t D →
        Jr.E0locJ C z (rawOf D) = ∑ T', e z ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
          (0 : CTorus d L N₁ Tk.m₁ (k + 1) → Fin N → ℂ)) T') ∧
      ∀ {N₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ (Tk.m₁ + hatScale L Tk.m₁ ϱ) = N₁ * L ^ Tk.m₁)
        (hsep : ϱ ≤ Balaban.LargeField.minSep L (L ^ (Tk.m₁ + hatScale L Tk.m₁ ϱ)))
        (π : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N →L[ℂ] rawSub N S.G'),
        (∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩) →
      ∃ (f : RootIdx d L N₁ Tk.m₁ (k + 1) → Finset (CubeB (d := d) (L := L) (N₁ := N₁)
          (m₁ := Tk.m₁) (K := k + 1) 1 (k + 1) Set.univ) →
            Fld d L N₁ Tk.m₁ (k + 1) N × Fld d L N₁ Tk.m₁ (k + 1) N → ℂ)
        (b : RootIdx d L N₁ Tk.m₁ (k + 1) → Finset (CubeB (d := d) (L := L) (N₁ := N₁)
          (m₁ := Tk.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℝ),
        ∀ z, NewLevelLocalFamily S P₀ hc hsep
          (fun Y => {x' : CTorus d L N₁' (Tk.m₁ + hatScale L Tk.m₁ ϱ) (k + 1) |
            (torusCast x' : CTorus d L N₁ Tk.m₁ (k + 1)) ∈ hatSet P₀.m₀ (k + 1) Y}) π (e z) (f z)
          (b z) := by
  obtain ⟨κmin, T₀, κdec, hT, hQ16, hNLN, hTm, hlam⟩ := H.tower
  have hd : 3 ≤ d := T₀.hd
  have hL : 3 ≤ L := T₀.hL
  have hK2 : 0 < xiK2 d L N := by
    have := cK2_pos d L N
    unfold xiK2; positivity
  obtain ⟨β₀, hβ₀, HB⟩ := T₀.newLevel_localFamilies_birth_of P₀.m₀ hA p hγ0 hγ1 hT rfl rfl rfl
    H.large_L hQ16 hNLN P₀ rfl hα₀ H.eps_quad CI KL α₃ n₁ hCI hKL hα₃
  refine ⟨κmin, T₀, κdec, β₀, hT, hTm, hβ₀, fun k hk => ?_⟩
  -- the room `λ = 17/16` of the step radii
  have hr16 : xiK2 d L N * ((3 / 2 : ℝ) * (1 / (24 * xiK2 d L N))) = 1 / 16 := by
    field_simp; ring
  obtain ⟨Tk, hTt, hTm', -, -, -, -, -, -, -, -, -, hTm0, -, -, -, -, Hk⟩ :=
    HB (1 / (24 * xiK2 d L N)) (17 / 16) (by positivity) (by rw [hr16]; norm_num) hr16.le hlam k hk
  have hTm1 : Tk.m₁ = m₁ := hTm'.trans hTm
  refine ⟨Tk, hTt, hTm1, ?_⟩
  intro N₁ _ hN₁ h5 ν hν0 hν β hβ p₁ hp0 hp₁ S hS
  have hTk0 : Tk.m₀ = 1 := hTm0.trans hT.m₀_eq
  have hϱ : ϱ = rhoSepG d L Tk.m₁ := by rw [hTm1]; exact H.sep
  have hN₁' : L ^ Tk.m₀ ∣ N₁ := by
    rw [hTk0]
    exact (pow_dvd_pow L (by have := H.m₀_ge; omega)).trans hN₁
  obtain ⟨Jr, HJ⟩ := Hk N₁ hN₁' h5 ν hν0 hν β hβ p₁ hp0 hp₁ hϱ S hS
  refine ⟨Jr, ?_⟩
  intro C Rg a hm hcl hE₀ hAw ξ ν₀ hξ hνflow hνS hmass Bl hBl hB hEbI hEbL
  -- the component of the constant field of the unit witness (any one serves)
  let i₀ : Fin N := ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩
  have hSa : S.a₁ = 1 := by subst hS; rfl
  have hSν : S.ν = ν := by subst hS; rfl
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have h3d : (3 : ℝ) ≤ d := by exact_mod_cast hd
  -- the class radii
  have hpos : ∀ j, 0 < P₀.eps d L j := fun j => by
    have := epsTail_pos j
    unfold Consts.eps epsSeq
    positivity
  have hanti : Antitone (P₀.eps d L) :=
    classEpsG_antitone (d := d) (L := L) hα₀.le (by unfold Consts.alpha; linarith)
  -- the flow
  have hqf0 : 0 < Flow.rate (L : ℝ) P₀.γ := Flow.rate_pos (by linarith) _
  have hqf1 : Flow.rate (L : ℝ) P₀.γ < 1 := Flow.rate_lt_one hL1 hγ0
  have hτ : Real.exp (3 * (P₀.c₈ / 4 * (Flow.rate (L : ℝ) P₀.γ ^ 2 /
      (1 - Flow.rate (L : ℝ) P₀.γ)))) - 1 ≤ 1 / 2 := by
    have := H.tau_small; linarith
  obtain ⟨rm, hτr, hrm, hKε1, hζε1⟩ := H.rm
  have hrm0 : 0 ≤ rm := by
    have hx : 0 ≤ 3 * (P₀.c₈ / 4 * (Flow.rate (L : ℝ) P₀.γ ^ 2 /
        (1 - Flow.rate (L : ℝ) P₀.γ))) :=
      mul_nonneg (by norm_num) (mul_nonneg (div_nonneg hc₈ (by norm_num))
        (div_nonneg (sq_nonneg _) (by linarith)))
    have := Real.add_one_le_exp (3 * (P₀.c₈ / 4 * (Flow.rate (L : ℝ) P₀.γ ^ 2 /
      (1 - Flow.rate (L : ℝ) P₀.γ))))
    linarith
  -- the standing hypotheses at the step mass and at the birth masses
  have HBs : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν := by
    rw [hSa, hSν]
    exact bgHyp_lvG hd hL (hϱ ▸ bgR0_le_rhoSepG Tk.m₁ hd hL) hν0.le hν
  have H' := birthMass_bgHyp_of_flow HBs hqf0.le hqf1 hc₈ H.c8_rate hξ hτ hνflow (hSν.trans hνS)
    (by rw [hSν]; exact hmass)
  -- the unit fields near the constant field lie in the birth-mass domain
  have hdom : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ Tk.m₁) (k + 1) ϱ,
      (∀ i, j < i → G.Ω i = ∅) →
      ∀ Ψ : Fld d L N₁ Tk.m₁ (k + 1) N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
      (∀ x x', jBlock d L (N₁ * L ^ Tk.m₁) (k + 1) j x = jBlock d L (N₁ * L ^ Tk.m₁) (k + 1) j x' →
        Ψ x = Ψ x') →
      (birthXiDom P₀ Rg a N₁).dom j G Ψ (constFld (Pi.single i₀ 1)) := fun j hj1 hjk =>
    exists_birthXiDom_ball P₀ Rg a i₀ (hjk.trans (Nat.le_succ k))
      (by rw [hAw]; exact H' j hj1 hjk) (hpos j)
  -- the label data
  have hNC : L ^ C.m₀ ∣ N₁ := hm ▸ hN₁
  obtain ⟨𝒦X, h𝒦, hopt⟩ := exists_labelData (k := k) (m₀ := C.m₀) hNC rfl
  -- the cube exponent of the local sets (ruling R13)
  have hhs : hatScale L Tk.m₁ ϱ = hatScale L m₁ ϱ := by rw [hTm1]
  have hslt : hatScale L Tk.m₁ ϱ < C.m₀ := by rw [hhs, ← hm]; exact H.hat_lt
  have hmarg : (((5 * L + 13) * L ^ hatScale L Tk.m₁ ϱ + L / 2 * L ^ C.m₀ : ℕ) : ℝ) +
      (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) * L ≤ (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (C.m₀ + 1) := by
    rw [hhs, ← hm]; exact H.hat_margin
  have hidx : (((5 * L + 13) * L ^ hatScale L Tk.m₁ ϱ : ℕ) : ℝ) +
      (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) * (L : ℝ) ≤ (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (C.m₀ + 1) := by
    have h : (((5 * L + 13) * L ^ hatScale L Tk.m₁ ϱ : ℕ) : ℝ) ≤
        (((5 * L + 13) * L ^ hatScale L Tk.m₁ ϱ + L / 2 * L ^ C.m₀ : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right _ _
    linarith
  have hmin : rhoSepG d L Tk.m₁ ≤ LargeField.minSep L (L ^ (Tk.m₁ + hatScale L Tk.m₁ ϱ)) := by
    obtain ⟨s₀, hs₀⟩ := exists_rhoSepG_le_minSep hd hL
    rw [hϱ]; exact minSep_hatScale (hs₀ Tk.m₁)
  have hHat : ClassHatCond C (hatScale L Tk.m₁ ϱ) (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) := by
    refine ⟨hmarg, rfl, hslt, fun j hj1 hjk X hX => ?_⟩
    rw [← hm] at hX ⊢
    exact hcl.hat j hj1 (hjk.trans (Nat.le_succ k)) X hX
  -- the smallness of `ε_j` at every level, from that of `ε_1`
  have hX1 := one_le_xiC1 d
  have hK1 := bgK1_pos d L N
  have hsmε : ∀ j, 1 ≤ j → j ≤ k → (4 * d + 6) * ((2 * d + 1) * P₀.eps d L j) ≤ 1 :=
    fun j hj1 _ => le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hanti hj1)
      (by positivity)) (by positivity)) H.eps_small
  have hc1ε : ∀ j, 1 ≤ j → j ≤ k → 4 * (xiC1 d * P₀.eps d L j) ≤ bgC1 d L N :=
    fun j hj1 _ => le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hanti hj1)
      (by linarith)) (by norm_num)) H.eps_c1
  have hKε : ∀ j, 1 ≤ j → j ≤ k →
      bgK1 d L N * (xiC1 d * P₀.eps d L j) + 3 * rm ≤ deltaStar d L N := fun j hj1 _ => by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hanti hj1)
      (by linarith : (0 : ℝ) ≤ xiC1 d)) hK1.le
    linarith
  have hζε : ∀ j, 1 ≤ j → j ≤ k → 8 * P₀.eps d L j * rm ≤ deltaStar d L N := fun j hj1 _ => by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hanti hj1)
      (by norm_num : (0 : ℝ) ≤ 8)) hrm0
    linarith
  exact HJ C _ rfl Rg a hm hcl hE₀ i₀ hdom (fun τ => labelPoly C.m₀ τ.1) 𝒦X (fun _ => rfl) h𝒦
    hopt hNC (hm ▸ H.m₀_ge) hslt.le hidx hmin hm.symm hHat hAw hqf0.le hqf1 hc₈ H.c8_rate hξ
    hνflow hνS hτ hτr hrm hmass H.tau_K hsmε hc1ε hKε hζε Bl hBl hB hEbI hEbL

end Balaban.RootFSpine
