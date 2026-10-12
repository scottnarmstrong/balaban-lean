/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.I5WitnessData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `i5_background` on data with non-empty data sites: the instance

* `i5_background_data_of`: the conclusion of `Balaban.Localization.i5_background` for the data of
  `BgSettingData` (`Gp = GpD`, `Gk = GkD` with `dataSites GkD ≠ ∅`, `Gj = G0D`), `X = XD`,
  `𝒦_X = KM` (a chosen family of `X` that attains `d^cov_1(X)`, so `hopt` holds), `X₁ = X1 GpD 0 1 KM`
  a proper subset of the torus, the constant old term `Edata`, `κ = 100000`, `κ_dec = 24`, `κ₀ = 7`;
  `exists_data_premises`: its numerical premises are satisfiable.
* `one_lt_card_polymerDomains`: the set `polymerDomains` of the expansion has more than one element
  (it contains `X₁` and `X₁ ∪ D(P)` for a level-`2` cube `P` adjacent to `X₁`), so the sum over
  domains in the conclusion is not a single term `Ev X₁`.
* `xiCRaw_G0D`, `eq_of_mem_xiCRaw_G0D`: for `Gj = G0D` (no data sites) the domain `Ξ^c_j(𝔹_j)` consists
  of the zero datum only, so every `𝓔` is constant on it; an old term that reads the data needs a `Gj`
  with data sites.

**What the instance tests.**  The hypotheses `CovSetup`, `HatConn`, `hopt` (with `d^cov_1(X) ≥ 294`, so
the decay factors are not `1`), `BgSetting` with `dataSites Gk ≠ ∅` and a proper `X₁` are all satisfied
together.  **What it does not test.**  The old term is constant; it reads no datum, so the
locality statement (agreement on `thickSet Y` implies equality of `Ev Y`) is tested only for terms
that do not depend on the datum, and `Ev Y` may be taken `0` for `Y ≠ X₁`.  The hypothesis `hopt` is
met by choosing `𝒦_X` to be a minimizing family (`KM`), not the family `KX` of `BgSettingData`.
-/

@[expose] public section

namespace Balaban.Inhabited
namespace I5WitnessData

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.I5Inhabited Balaban.Inhabited.BgSettingData


/-! ### The old term and the instance of `i5_background` -/

section Instance

variable {m₁ : ℕ}

/-- **The old term (constant).**  `𝓔 ≡ exp (-(κ_dec - 1) d^cov_1(X))`, i.e. `E_b = 1` and the bound of
`i5_background` attained with equality. -/
noncomputable def Edata (m₁ : ℕ) (κdec : ℝ) : RawData 3 3 (240 * 3 ^ m₁) 2 2 → ℂ :=
  fun _ => ((Real.exp (-(κdec - 1) * treeLenCovOne 0 1 (XD m₁)) : ℝ) : ℂ)

theorem Edata_analytic (κdec : ℝ) (S : Set (RawData 3 3 (240 * 3 ^ m₁) 2 2)) :
    AnalyticOnNhd ℂ (Edata m₁ κdec) S := analyticOnNhd_const

theorem Edata_bound (κdec : ℝ) (r : RawData 3 3 (240 * 3 ^ m₁) 2 2) :
    ‖Edata m₁ κdec r‖ ≤ 1 * Real.exp (-(κdec - 1) * treeLenCovOne 0 1 (XD m₁)) := by
  unfold Edata
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]

/-- The numerical inequalities of `i5_background` at `κ = 100000`, `κ_dec = 24`, `κ₀ = 7`. -/
theorem num_ineqs :
    (0 : ℝ) ≤ 7 ∧ 3 * (7 : ℝ) + 3 ≤ 24 ∧
    4 * ((3 : ℕ) : ℝ) * ((((2 * 3 + 1) ^ 3 : ℕ)) : ℝ) * 24 ≤ 100000 ∧
    1 ≤ ((100000 : ℝ) / 2 - 1) / 2 ∧
    Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ 0) ^ 3 : ℕ) : ℝ)) ≤ ((100000 : ℝ) / 2 - 1) / 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have h343 : Real.log (343 : ℝ) ≤ 343 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  norm_num at h343 ⊢
  linarith

/-- **`i5_background` on the data with non-empty data sites.**  `Gp = GpD` (whole lattice, level
`2`), `Gk = GkD` (`Ω₁` one `1`-block), `Gj = G0D` (empty), `X₀ = dataSites GkD`, `X = XD`,
`𝒦_X = KM` (a chosen family of `X` attaining `d^cov_1(X)`), `X₁ = X1 GpD 0 1 KM` (a proper subset of
the torus), `𝓔 = Edata` (constant), `κ = 100000`, `κ_dec = 24`, `κ₀ = 7`.  The conclusion is
that of `i5_background`. -/
theorem i5_background_data_of (h4 : 4 ≤ m₁) {c BG eps δ₃ : ℝ} (hS : DecSpecs 3 3 c BG)
    (hm : c * Real.exp ((N0 3 3 : ℝ) * 100000) ≤ (3 : ℝ) ^ m₁)
    (hnum : ChainNum 3 3 2 m₁ BG 100000 324 eps δ₃) :
    ∃ Ev : Set (T m₁) → RawData 3 3 (240 * 3 ^ m₁) 2 2 → ℂ,
      (∀ D : BgData (GpD m₁ (rhoSep m₁)) 2,
        XiCData (GpD m₁ (rhoSep m₁)) (compWeight 3 1) 0 2 1 eps D →
        Edata m₁ 24 (rawOf (composeData (bgSetting_dataM h4 hS hm hnum).hq (compWeight 3 1)
          (bgFieldC (GkD m₁ (rhoSep m₁)) (compWeight 3 1) 0 (bgC0 3 3 2)
            (composeData (bgSetting_dataM h4 hS hm hnum).hP (compWeight 3 1)
              (bgFieldC (GpD m₁ (rhoSep m₁)) (compWeight 3 1) 0 (bgC0 3 3 2) D) D))
          (composeData (bgSetting_dataM h4 hS hm hnum).hP (compWeight 3 1)
            (bgFieldC (GpD m₁ (rhoSep m₁)) (compWeight 3 1) 0 (bgC0 3 3 2) D) D))) =
        ∑ Y ∈ polymerDomains
          (fun i : ParIdx (GpD m₁ (rhoSep m₁)) (↑(X1fM m₁ (rhoSep m₁)) : Set (T m₁)) => i.1.1)
          (GpD m₁ (rhoSep m₁)) 0 (X1 (GpD m₁ (rhoSep m₁)) 0 1 (KM m₁)), Ev Y (rawOf D)) ∧
      (∀ Y, ∀ u ∈ XiCRaw (GpD m₁ (rhoSep m₁)) (compWeight 3 1) 0 2 1 eps,
        ∀ u' ∈ XiCRaw (GpD m₁ (rhoSep m₁)) (compWeight 3 1) 0 2 1 eps,
        agreeOn (thickSet (GpD m₁ (rhoSep m₁)) Y) u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw (GpD m₁ (rhoSep m₁)) (compWeight 3 1) 0 2 1 eps,
        ‖Ev Y u‖ ≤ 1 * Real.exp (-7 * treeLenCovOne 0 1 (XD m₁) -
          2 * 24 * treeLenCov (GpD m₁ (rhoSep m₁)) 0 Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw (GpD m₁ (rhoSep m₁)) (compWeight 3 1) 0 2 1 eps)) := by
  obtain ⟨h0, h3, hk, h1, hlog⟩ := num_ineqs
  exact i5_background (bgSetting_dataM h4 hS hm hnum) (covSetup_KM m₁ _) (coe_X1fM m₁ _)
    hatConn_GpD (hopt_data m₁) (κdec := 24) (κ₀ := 7) (Eb := 1) h0 h3 hk h1 hlog zero_le_one
    (Edata_analytic 24 _) (fun r _ => Edata_bound 24 r)

/-- The premises of `i5_background_data_of` are satisfiable (the same constants as
`bgSetting_data`). -/
theorem exists_data_premises :
    ∃ (m₁ : ℕ) (c BG eps δ₃ : ℝ), 4 ≤ m₁ ∧ DecSpecs 3 3 c BG ∧
      c * Real.exp ((N0 3 3 : ℝ) * 100000) ≤ (3 : ℝ) ^ m₁ ∧
      ChainNum 3 3 2 m₁ BG 100000 324 eps δ₃ := by
  obtain ⟨c, BG, hS⟩ := decSpecs_exists (d := 3) (L := 3) (by norm_num) (by norm_num)
  have hBG : 0 ≤ BG := hS.fam.2.1
  obtain ⟨m₁, h4, hm⟩ := exists_m₁ (c * Real.exp ((N0 3 3 : ℝ) * 100000))
  obtain ⟨eps, δ₃, hnum⟩ := chainNum_exists 3 3 2 m₁ (by norm_num) hBG 100000 324
  exact ⟨m₁, c, BG, eps, δ₃, h4, hS, hm, hnum⟩

end Instance

/-! ### The polymer domains: more than one -/

section Domains

variable {m₁ : ℕ}

/-- First exit from a set along a chain. -/
theorem exists_exit {α : Type*} {R : α → α → Prop} {S : Set α} {x y : α}
    (h : Relation.ReflTransGen R x y) (hx : x ∈ S) (hy : y ∉ S) : ∃ u ∈ S, ∃ v ∉ S, R u v := by
  have key : y ∈ S ∨ ∃ u ∈ S, ∃ v ∉ S, R u v := by
    clear hy
    induction h with
    | refl => exact Or.inl hx
    | @tail b c _ hbc ih =>
      rcases ih with hb | hex
      · by_cases hc : c ∈ S
        · exact Or.inl hc
        · exact Or.inr ⟨b, hb, c, hc, hbc⟩
      · exact Or.inr hex
  rcases key with h' | h'
  · exact absurd h' hy
  · exact h'

theorem sameCell_cbase {n d a : ℕ} [NeZero n] (ha : 0 < a) (y : Torus d n) :
    SameCell a y (cbase a y) := by
  intro μ
  have hlt : a * ((y μ).val / a) < n := by
    calc a * ((y μ).val / a) ≤ (y μ).val := Nat.mul_div_le _ _
      _ < n := ZMod.val_lt _
  have : ((cbase a y) μ).val = a * ((y μ).val / a) := by
    simp only [cbase]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  rw [this, Nat.mul_div_cancel_left _ ha]

/-- **There is more than one polymer domain.**  `polymerDomains` contains `X₁` itself (the empty
family) and `X₁ ∪ D(P)` for the `π¹`-cube `P` of level `2` containing a site just outside `X₁`. -/
theorem one_lt_card_polymerDomains (h4 : 4 ≤ m₁) :
    1 < (polymerDomains
      (fun i : ParIdx (GpD m₁ (rhoSep m₁)) (↑(X1fM m₁ (rhoSep m₁)) : Set (T m₁)) => i.1.1)
      (GpD m₁ (rhoSep m₁)) 0 (X1 (GpD m₁ (rhoSep m₁)) 0 1 (KM m₁))).card := by
  classical
  set ρ := rhoSep m₁ with hρ
  set G := GpD m₁ ρ with hG
  have hcov := covSetup_KM m₁ ρ
  -- a crossing edge
  have h0 : (0 : T m₁) ∈ X1 G 0 1 (KM m₁) := hcov.X_sub (zero_mem_XD m₁)
  have ha := antipode_not_mem_X1M (m₁ := m₁) (ρ := ρ)
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_exit
    (siteConnected_univ (d := 3) (L := 3) (N₁ := 240) (m₁ := m₁) (K := 2) 0 (Set.mem_univ _)
      _ (Set.mem_univ _)) h0 ha
  -- the cube containing y
  set q : ℕ × T m₁ := (2, cbase (cellSide 3 0 m₁ 2) y) with hq
  have hcs : cellSide 3 0 m₁ 2 = 3 ^ (2 + m₁) := by unfold cellSide; ring_nf
  have hqc : q ∈ cubeIdx G := by
    refine (mem_cubeIdx G).2 ⟨⟨by norm_num, le_rfl⟩, ?_, ?_⟩
    · show cbase (cellSide 3 0 m₁ 2) y ∈ G.layer 2
      rw [hG, GpD_layer_two]; exact Finset.mem_univ _
    · intro μ
      have := aligned_cbase (a := cellSide 3 0 m₁ 2) y μ
      rwa [hcs] at this
  have hyP : y ∈ Pset m₁ q := by
    show SameCell (3 ^ (2 + m₁)) y (cbase (cellSide 3 0 m₁ 2) y)
    rw [← hcs]
    exact sameCell_cbase (cellSide_pos 0 m₁ 2) y
  have hdisj : Disjoint (Pset m₁ q) (↑(X1fM m₁ ρ) : Set (T m₁)) := by
    rw [coe_X1fM]
    by_contra hnd
    exact hy (Pset_subset_of_not_disjoint hcov.polySetup hqc hnd hyP)
  set i : ParIdx G (↑(X1fM m₁ ρ) : Set (T m₁)) := ⟨⟨q, hqc⟩, hdisj⟩ with hi
  -- the family {i} is connected
  have hconn : IsConnectedFamily (fun i : ParIdx G (↑(X1fM m₁ ρ) : Set (T m₁)) => Pset m₁ i.1.1)
      (compY (fun i : ParIdx G (↑(X1fM m₁ ρ) : Set (T m₁)) => i.1.1) (X1 G 0 1 (KM m₁)))
      ({i} : Finset _) := by
    intro j hj z hz
    rw [Finset.mem_singleton] at hj
    subst hj
    have hxy' : latGraph 3 (240 * 3 ^ m₁ * 3 ^ 2) |>.Adj x y := ⟨fun h => hy (h ▸ hx), hxy.2.2⟩
    have hcp := cubeP_connIn (dgSetting_GpD h4) hqc
    have hyc : y ∈ cubeP q := mem_cubeP.2 hyP
    have hzc : z ∈ cubeP q := mem_cubeP.2 hz
    have hpath := hcp y hyc z hzc
    unfold compY
    refine ⟨x, hx, ?_⟩
    have hV : ∀ w ∈ cubeP q, w ∈ patchUnion (X1 G 0 1 (KM m₁))
        (fun i : ParIdx G (↑(X1fM m₁ ρ) : Set (T m₁)) => Pset m₁ i.1.1) {i} :=
      fun w hw => Or.inr (Set.mem_iUnion₂.2 ⟨i, Finset.mem_singleton_self _, mem_cubeP.1 hw⟩)
    have hxV : x ∈ patchUnion (X1 G 0 1 (KM m₁))
        (fun i : ParIdx G (↑(X1fM m₁ ρ) : Set (T m₁)) => Pset m₁ i.1.1) {i} := Or.inl hx
    have step1 : Relation.ReflTransGen (fun a b => (latGraph 3 (240 * 3 ^ m₁ * 3 ^ 2)).Adj a b ∧
        a ∈ patchUnion (X1 G 0 1 (KM m₁))
          (fun i : ParIdx G (↑(X1fM m₁ ρ) : Set (T m₁)) => Pset m₁ i.1.1) {i} ∧
        b ∈ patchUnion (X1 G 0 1 (KM m₁))
          (fun i : ParIdx G (↑(X1fM m₁ ρ) : Set (T m₁)) => Pset m₁ i.1.1) {i}) x y :=
      Relation.ReflTransGen.single ⟨hxy', hxV, hV y hyc⟩
    refine step1.trans ?_
    clear step1
    have claim : ∀ w, Relation.ReflTransGen (stepIn (cubeP q)) y w →
        Relation.ReflTransGen (fun a b => (latGraph 3 (240 * 3 ^ m₁ * 3 ^ 2)).Adj a b ∧
        a ∈ patchUnion (X1 G 0 1 (KM m₁))
          (fun i : ParIdx G (↑(X1fM m₁ ρ) : Set (T m₁)) => Pset m₁ i.1.1) {i} ∧
        b ∈ patchUnion (X1 G 0 1 (KM m₁))
          (fun i : ParIdx G (↑(X1fM m₁ ρ) : Set (T m₁)) => Pset m₁ i.1.1) {i}) y w := by
      intro w hp
      induction hp with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c _ hbc ih =>
        refine ih.trans ?_
        by_cases hbc' : b = c
        · subst hbc'; exact Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.single ⟨⟨hbc', hbc.2.2⟩, hV b hbc.1, hV c hbc.2.1⟩
    exact claim z hpath
  -- the two domains
  have hD := exists_Dcubes hcov.hU hcov.hN hqc
  obtain ⟨b, hb⟩ := hD
  have hyD : y ∈ Ysites G 0 (fun i : ParIdx G (↑(X1fM m₁ ρ) : Set (T m₁)) => i.1.1)
      (X1 G 0 1 (KM m₁)) ({i} : Finset _) :=
    Or.inr (Set.mem_iUnion₂.2 ⟨i, Finset.mem_singleton_self _,
      cellOf_subset_Dsites hb (Pset_subset_cellOf 0 q hyP)⟩)
  unfold polymerDomains
  refine Finset.one_lt_card.2 ⟨X1 G 0 1 (KM m₁), ?_,
    Ysites G 0 (fun i : ParIdx G (↑(X1fM m₁ ρ) : Set (T m₁)) => i.1.1) (X1 G 0 1 (KM m₁))
      ({i} : Finset _), ?_, fun h => hy (h ▸ hyD)⟩
  · refine Finset.mem_image.2 ⟨∅, ?_, ?_⟩
    · simp [IsConnectedFamily]
    · simp [Ysites]
  · exact Finset.mem_image.2 ⟨{i}, by simpa using hconn, rfl⟩

end Domains

/-! ### The old term cannot read the data when `Gj` is empty -/

section Gj

variable {m₁ : ℕ} {ρ : ℝ}

theorem G0D_dataSites : dataSites (G0D m₁ ρ) = ∅ := by
  ext x
  simp [mem_dataSites, G0D_Ω _ le_rfl, G0D_collar]

/-- **Every raw datum of `Ξ^c_j(𝔹_j)` for the empty set `Gj = G0D` is zero** (`Ψ` vanishes off the data
sites and `h̃` off `Ω₁`, both empty).  So any `𝓔` on this domain is constant: a `𝓔` that reads the data
needs a `Gj` with data sites. -/
theorem xiCRaw_G0D {N : ℕ} {a : ℕ → ℝ} {ν σ ε : ℝ} {n : ℕ} {r : RawData 3 3 (240 * 3 ^ m₁) 2 N}
    (hr : r ∈ XiCRaw (G0D m₁ ρ) a ν n σ ε) : r = (0, 0) := by
  obtain ⟨D, -, rfl⟩ := hr
  refine Prod.ext (funext fun x => D.Ψ_zero x ?_) (funext fun x => D.h_zero x ?_)
  · rw [G0D_dataSites]; simp
  · rw [G0D_Ω 1 le_rfl]; simp

theorem eq_of_mem_xiCRaw_G0D {N : ℕ} {a : ℕ → ℝ} {ν σ ε : ℝ} {n : ℕ}
    {r r' : RawData 3 3 (240 * 3 ^ m₁) 2 N} (E : RawData 3 3 (240 * 3 ^ m₁) 2 N → ℂ)
    (hr : r ∈ XiCRaw (G0D m₁ ρ) a ν n σ ε) (hr' : r' ∈ XiCRaw (G0D m₁ ρ) a ν n σ ε) :
    E r = E r' := by
  rw [xiCRaw_G0D hr, xiCRaw_G0D hr']

end Gj

end I5WitnessData
end Balaban.Inhabited
