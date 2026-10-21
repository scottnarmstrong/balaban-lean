/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityIrrelSupport
public import Balaban.Fluctuation.LocalClassDensityIrrelStepRoom
public import Balaban.Fluctuation.NewLevelOldTermsBgSetting
public import Balaban.SmallField.Def6v2Birth

/-!
# The composed data of a local pair in the domain of an inherited class term (ruling R13)

The checks of ruling R13 (a) (the class generating set of a level-`j` polymer `X` is the cast
local set `𝔹_j(X)`, and the chain composes the data of the old term `(j, y, X)` on it).

* **The sites read by the irrelevant part** (`stPlus_mem_dataSites`): for a polymer `X` of `𝒟_j`,
  a site `y ∈ X` aligned to `L^j` and any generating set `G` with `X ⊆ Ω₁(G)` (in particular the
  class set `Tm.gs j X`, `GsSpecCore.subset`), the sites `y + L^j e_μ` read by
  `irrelTorus … j y X` (`irrelTorus_congr`) are data sites of `G`: each is a neighbour of the last
  site `y + (L^j - 1) e_μ ∈ X` of the `j`-block of `y` (`blockEnd_mem_of_isPolyDom`), so it lies in
  `Ω₁(G)` or in its one-site collar.  No margin beyond the collar is needed.
* **The room at `Gb`** (`d2raw_d1Triple_mem_xiDom_of_top`): the composed data of the realizable
  triples of a local pair `(Gb, H⁻_b)` whose top layer contains the data sites of `Gk` lie in
  `Ξ^c_j(Gj; 1, ε)` with the weights and the mass of the step, for
  `ε ≥ ε' + K₂ δ₃ + K₂ δ_fl` (`d2raw_d1Triple_mem_xiDom` with `bgSetting_of_top`,
  `flSetting_of_top_gen`).
* **The slit plane** (`dot_mem_slitPlane_of_xiDom`): at every data site of `G` a point of
  `Ξ^c_j(G; 1, ε)` has `Ψ(y)·Ψ(y)` of positive real part.
* **The weights and the mass** (`aIdeal_eq_compWeight`, `aIdeal_compWeight`, `physMass_nuIdeal`):
  the class weights `aIdeal L K a_K` are the composition weights `compWeight L (aIdeal L K a_K 1)`,
  under the free flow `a_K = compWeight L a_ker K` they are `compWeight L a_ker` (so they match the
  step's `compWeight L S.a₁` iff `S.a₁ = a_ker`); the class mass `physMass L j ν_j` of level `j` is
  `physMass L K ν_K` along the ideal flow `ν_j = ν_K L^{-2(K-j)}` only.
* **The inclusion** (`d2raw_mem_birthXiDom_of_top`): with these matchings and the room
  `ε' + K₂ δ₃ + K₂ δ_fl ≤ ε_j`, the composed data of the local pair lie in the class term domain
  `(birthXiDom P Rg a).dom j Gj ∩ {Ψ(y)·Ψ(y) ∈ slitPlane}` (`irrelTorus_analyticOnNhd`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset

section Sites

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {m₀ j : ℕ}

/-- **The last site of the `j`-block of a site of a polymer lies in the polymer**: for `X` of
`𝒟_j` and `y ∈ X` aligned to `L^j`, `y + (L^j - 1) e_μ ∈ X`. -/
theorem blockEnd_mem_of_isPolyDom (hN : L ^ m₀ ∣ N₁) (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom m₀ j X) {y : CTorus d L N₁ m₁ k} (hy : y ∈ X)
    (hal : Aligned (L ^ j) y) (μ : Fin d) :
    y + natT (Pi.single μ (L ^ j - 1)) ∈ X := by
  set s := cellSide L m₀ m₁ j with hs
  have hs0 : 0 < s := cellSide_pos m₀ m₁ j
  have hjs : L ^ j ∣ s := pow_dvd_pow L (by omega)
  have hc : Aligned s (cbase s y) := aligned_cbase y
  set r : Fin d → ℕ := fun ν => (y ν).val % s with hr
  have hyr : y = cbase s y + natT r := by rw [cbase_eq_sub]; abel
  have hrs : ∀ ν, r ν < s := fun ν => Nat.mod_lt _ hs0
  have hrμ : r μ + (L ^ j - 1) < s := by
    have h1 : L ^ j ∣ r μ := by
      refine Nat.dvd_of_mod_eq_zero ?_
      show (y μ).val % s % L ^ j = 0
      rw [Nat.mod_mod_of_dvd _ hjs]
      exact hal μ
    obtain ⟨q, hq⟩ := h1
    obtain ⟨t, ht⟩ := hjs
    have hLj : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
    have hqt : q < t := by
      have := hrs μ
      rw [hq, ht] at this
      exact Nat.lt_of_mul_lt_mul_left this
    have h2 : L ^ j * (q + 1) ≤ L ^ j * t := Nat.mul_le_mul_left _ hqt
    have h3 : L ^ j * (q + 1) = L ^ j * q + L ^ j := by ring
    rw [hq]
    omega
  have hz : y + natT (Pi.single μ (L ^ j - 1)) ∈ box (cbase s y) s := by
    refine ⟨r + Pi.single μ (L ^ j - 1), fun ν => ?_, ?_⟩
    · by_cases h : ν = μ
      · subst h
        simpa using hrμ
      · simpa [Pi.single_apply, h] using hrs ν
    · rw [natT_add]
      conv_lhs => rw [hyr]
      abel
  have hyb : y ∈ box (cbase s y) s := ⟨r, hrs, hyr⟩
  exact (mem_iff_cell_base hN hjk hX hc hz).2 ((mem_iff_cell_base hN hjk hX hc hyb).1 hy)

/-- **The sites `y + L^j e_μ` read by the irrelevant part are data sites** of every generating set
whose first domain contains the polymer `X` (the one-site collar suffices). -/
theorem stPlus_mem_dataSites (hN : L ^ m₀ ∣ N₁) (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom m₀ j X) {y : CTorus d L N₁ m₁ k} (hy : y ∈ X)
    (hal : Aligned (L ^ j) y) {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ}
    (hXG : X ⊆ ↑(G.Ω 1)) (μ : Fin d) :
    y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k) ∈ dataSites G := by
  classical
  have hz := blockEnd_mem_of_isPolyDom hN hjk hX hy hal μ
  have hLj : 1 ≤ L ^ j := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hsingle : (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k) =
      natT (Pi.single μ (L ^ j) : Fin d → ℕ) := by
    funext ν
    by_cases h : ν = μ
    · subst h; simp [natT]
    · simp [natT, h]
  have hone : (natT (Pi.single μ 1 : Fin d → ℕ) : CTorus d L N₁ m₁ k) = Pi.single μ 1 := by
    funext ν
    by_cases h : ν = μ
    · subst h; simp [natT]
    · simp [natT, h]
  have hst : y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k) =
      (y + natT (Pi.single μ (L ^ j - 1))) + Pi.single μ 1 := by
    rw [hsingle, ← hone, add_assoc, ← natT_add, ← Pi.single_add, Nat.sub_add_cancel hLj]
  have hadj : Adj (y + natT (Pi.single μ (L ^ j - 1)))
      ((y + natT (Pi.single μ (L ^ j - 1))) + Pi.single μ 1) := ⟨μ, Or.inl rfl⟩
  rw [hst, mem_dataSites]
  by_cases h : (y + natT (Pi.single μ (L ^ j - 1))) + Pi.single μ 1 ∈ G.Ω 1
  · exact Or.inl h
  · exact Or.inr (mem_collar_of_adj G (hXG hz) h hadj)

end Sites

section Room

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm ϱb ϱd : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱd}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
  {Kc Cx c₂ Kc' Cx' c₂' BG₂ δ₁ δfl : ℝ}

/-- **The room of the composed data of a local pair** (`d2raw_d1Triple_mem_xiDom` on `Gb`): for an
old term with the step's settings whose generating set `Gk` has its data sites in the top layer of
`Gb`, the composed data of the realizable triples of `(Gb, H⁻_b)` lie in `Ξ^c_j(Gj; 1, ε)` with
the weights `compWeight L a₁` and the mass `ν` of the step, for `ε ≥ ε' + K₂ δ₃ + K₂ δ_fl`. -/
theorem d2raw_d1Triple_mem_xiDom_of_top
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) (hG' : IsLevel Gp (k + 1))
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc' Cx' c₂' BG₂ δ₁ δfl X₁f) (hG : IsLevel Hm k)
    (hk1 : 1 ≤ k) (HBb : BgHyp d L (k + 1) ϱb (compWeight L a₁) ν)
    (hrb : r₀ * (L : ℝ) ^ m₁ ≤ ϱb - 1) (hC : FlCore N Gb Gd a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hdk : Gd.Ω k = Gb.Ω k) (hdtop : Gd.Ω (k + 1) = ∅)
    (htop : ∀ x ∈ dataSites Gk, x ∈ Gb.Ω (k + 1))
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {t : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) × (Gd.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (ht : t ∈ FlRealLC Gb Gd a₁ ν BG κ eps X₁f BG₂ δ₁) {ε : ℝ}
    (hε : eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl ≤ ε) :
    XiDom Gj (compWeight L a₁) ν j ε
      (D2raw Gk Gj (compWeight L a₁) Fk
        (d1Triple Gb Gk Gd (compWeight L a₁) t.1.1 t.2.1 t.2.2)).1
      (D2raw Gk Gj (compWeight L a₁) Fk
        (d1Triple Gb Gk Gd (compWeight L a₁) t.1.1 t.2.1 t.2.2)).2 :=
  d2raw_d1Triple_mem_xiDom (bgSetting_of_top hB hG' hC.Sp HBb hrb htop)
    (flSetting_of_top_gen hF hG hk1 hC hdk hdtop htop) hFk ht hε

end Room

section Slit

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **The square of the field at a data site has positive real part** on `Ξ^c_j(G; 1, ε)`: the
field is `Ψ_r + Ψ'` with `| |Ψ_r|² - 1 | < δ` and `‖(Ψ_r + Ψ')² - Ψ_r²‖ < δ`, `δ ≤ c₀ ≤ 1/16`
(`InPsiTildeC` (R2), (C2b)); in particular `Ψ(y)·Ψ(y) ∈ slitPlane`. -/
theorem dot_mem_slitPlane_of_xiDom {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ}
    {ν ε : ℝ} {j : ℕ} {Ψ h : Fld d L N₁ m₁ K N} (hX : XiDom G a ν j ε Ψ h)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ dataSites G) :
    dot (Ψ x) (Ψ x) ∈ Complex.slitPlane := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hΨ, -, hXi⟩ := hX
  obtain ⟨-, -, -, Dc, -, hC, hU, -⟩ := hXi
  obtain ⟨δ, ε', -, hδε, hεc, -, -, hDC⟩ := hU
  obtain ⟨Ψr, _, Ψ', _, hP, hD1, -⟩ := hDC
  have hval : ∀ i, Ψ x i = (Ψr x i : ℂ) + Ψ' x i := fun i => by
    rw [hΨ x i, ← hC.1 x hx i, hD1 x hx i]
  have hdot : dot (Ψ x) (Ψ x) =
      ∑ i, ((Ψr x i : ℂ) + Ψ' x i) * ((Ψr x i : ℂ) + Ψ' x i) := by
    unfold dot
    exact Finset.sum_congr rfl fun i _ => by rw [hval i]
  have hreal : (∑ i, (Ψr x i : ℂ) * (Ψr x i : ℂ)) = ((∑ i, Ψr x i ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun i _ => (sq _).symm
  have he := hP.c2b x hx
  rw [hreal] at he
  have hr2 := hP.r2 x hx
  have hδ : δ ≤ 1 / 16 := hδε.trans (hεc.trans (bgC0_le d L N))
  rw [hdot]
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  set w := ∑ i, ((Ψr x i : ℂ) + Ψ' x i) * ((Ψr x i : ℂ) + Ψ' x i) with hw
  have hre : -δ < (w - ((∑ i, Ψr x i ^ 2 : ℝ) : ℂ)).re := by
    have h1 := (abs_le.1 (Complex.abs_re_le_norm (w - ((∑ i, Ψr x i ^ 2 : ℝ) : ℂ)))).1
    linarith
  have hsplit : w.re = (∑ i, Ψr x i ^ 2) + (w - ((∑ i, Ψr x i ^ 2 : ℝ) : ℂ)).re := by
    rw [Complex.sub_re, Complex.ofReal_re]
    ring
  have hA : 1 - δ < ∑ i, Ψr x i ^ 2 := by
    have := (abs_lt.1 hr2).1
    linarith
  rw [hsplit]
  linarith

end Slit

section Weights

variable {L : ℕ}

/-- **The class weights are composition weights**:
`aIdeal L K a_K = compWeight L (aIdeal L K a_K 1)` (`a_n = a_K (1 - L^{-2K})/(1 - L^{-2n})` and
`compWeight L a₁ n = a₁ (1 - L^{-2})/(1 - L^{-2n})`). -/
theorem aIdeal_eq_compWeight (hL : 2 ≤ L) (K : ℕ) (aK : ℝ) :
    aIdeal L K aK = compWeight L (aIdeal L K aK 1) := by
  funext n
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hu : (1 : ℝ) - ((L : ℝ) ^ 2)⁻¹ ≠ 0 := by
    have : ((L : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hL1 (by norm_num))
    linarith
  unfold aIdeal compWeight
  simp only [inv_pow, pow_one]
  rw [div_mul_cancel₀ _ hu]

/-- **Under the free flow the class weights are those of the kernel coefficient**:
`aIdeal L K (compWeight L a K) = compWeight L a` for `K ≥ 1`.  Hence they equal the step's weights
`compWeight L S.a₁` iff `S.a₁ = a` (`compWeight L · 1 = ·`). -/
theorem aIdeal_compWeight (hL : 2 ≤ L) {K : ℕ} (hK : 1 ≤ K) (a : ℝ) :
    aIdeal L K (compWeight L a K) = compWeight L a := by
  funext n
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hD : (1 : ℝ) - (((L : ℝ) ^ K) ^ 2)⁻¹ ≠ 0 := by
    have : (((L : ℝ) ^ K) ^ 2)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ (one_lt_pow₀ (one_lt_pow₀ hL1 (by omega)) (by norm_num))
    linarith
  unfold aIdeal compWeight
  simp only [inv_pow]
  rw [div_mul_cancel₀ _ hD]

/-- **The class mass of level `j` along the ideal flow** `ν_j = ν_K L^{-2(K-j)}` is the mass of
level `K`: `physMass L j (nuIdeal L K ν_K j) = physMass L K ν_K` (`j ≤ K`). -/
theorem physMass_nuIdeal {K j : ℕ} (hjK : j ≤ K) (νK : ℝ) :
    physMass L j (nuIdeal L K νK j) = physMass L K νK := by
  unfold physMass nuIdeal
  rw [mul_assoc, ← mul_pow, ← mul_inv, ← pow_add, Nat.sub_add_cancel hjK]

end Weights

section Inclusion

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm ϱb ϱd : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱd}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
  {Kc Cx c₂ Kc' Cx' c₂' BG₂ δ₁ δfl : ℝ}

/-- **The composed data of a local pair lie in the class term domain under R13 (a)**: when the
term is composed on the class generating set `Gj` of its polymer, the class weights and the class
mass of level `j` are the step's (`hA`, `hμ`) and the class radius pays the room
(`ε' + K₂ δ₃ + K₂ δ_fl ≤ ε_j`), the composed data of the realizable triples of `(Gb, H⁻_b)` lie in
`(birthXiDom P Rg a).dom j Gj`, and `Ψ(y)·Ψ(y) ∈ slitPlane` at every data site `y` of `Gj`: the
domain of `irrelTorus … j y X` (`irrelTorus_analyticOnNhd`). -/
theorem d2raw_mem_birthXiDom_of_top (P : Consts) (Rg : Regime L) (a : ℕ → ℝ)
    (hA : aIdeal L (k + 1) (a (k + 1)) = compWeight L a₁) (hμ : physMass L j (Rg.ν j) = ν)
    (hroom : eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl ≤ P.eps d L j)
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) (hG' : IsLevel Gp (k + 1))
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc' Cx' c₂' BG₂ δ₁ δfl X₁f) (hG : IsLevel Hm k)
    (hk1 : 1 ≤ k) (HBb : BgHyp d L (k + 1) ϱb (compWeight L a₁) ν)
    (hrb : r₀ * (L : ℝ) ^ m₁ ≤ ϱb - 1) (hC : FlCore N Gb Gd a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hdk : Gd.Ω k = Gb.Ω k) (hdtop : Gd.Ω (k + 1) = ∅)
    (htop : ∀ x ∈ dataSites Gk, x ∈ Gb.Ω (k + 1))
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {t : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) × (Gd.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (ht : t ∈ FlRealLC Gb Gd a₁ ν BG κ eps X₁f BG₂ δ₁) {y : CTorus d L N₁ m₁ (k + 1)}
    (hy : y ∈ dataSites Gj) :
    (birthXiDom P Rg a N₁ : FieldDom d L N₁ m₁ (k + 1) N ϱ₂).dom j Gj
        (D2raw Gk Gj (compWeight L a₁) Fk
          (d1Triple Gb Gk Gd (compWeight L a₁) t.1.1 t.2.1 t.2.2)).1
        (D2raw Gk Gj (compWeight L a₁) Fk
          (d1Triple Gb Gk Gd (compWeight L a₁) t.1.1 t.2.1 t.2.2)).2 ∧
      dot ((D2raw Gk Gj (compWeight L a₁) Fk
          (d1Triple Gb Gk Gd (compWeight L a₁) t.1.1 t.2.1 t.2.2)).1 y)
        ((D2raw Gk Gj (compWeight L a₁) Fk
          (d1Triple Gb Gk Gd (compWeight L a₁) t.1.1 t.2.1 t.2.2)).1 y) ∈ Complex.slitPlane := by
  have h := d2raw_d1Triple_mem_xiDom_of_top hB hG' hF hG hk1 HBb hrb hC hdk hdtop htop hFk ht
    hroom
  refine ⟨?_, dot_mem_slitPlane_of_xiDom h hy⟩
  rw [birthXiDom_dom_iff, hA, hμ]
  exact h

end Inclusion

end Balaban.Fluctuation
