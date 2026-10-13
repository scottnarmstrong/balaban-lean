/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusDecSol
public import Balaban.Polymer.TwoTorusXGreen
public import Balaban.Localization.RowsCov

/-!
# The decoupled covariance on two tori, and the fluctuation from the raw data

* `decSol_value_twoTorus_of_decBg` (D0): the values of the decoupled fluctuation solution on two
  tori correspond on a component when its data are `flEdat` of the values of the decoupled
  background pair (the maps `F₁`, `F₁'` with the defining property of Theorem I-4b at level
  `j + 1`): the only hypotheses on the data are the agreement of the raw data on `RowsDep (S_Y)`
  and of the fluctuations `ψ, ψ'` on `S_Y^F` (the source `f₁` of `flEdat` is `0`).  The chain is
  `decBg_value_twoTorus`'s proof (`i4b_exists_unique`, `hF₁`) → `decSol_data_of_decBg` →
  `decSol_value_twoTorus`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background Matrix

/-! ### D0: the fluctuation values from the raw data -/

section FromRaw

variable {d L N₁ N₁' m₁ K N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱp : ℝ} {j : ℕ}
variable (hj1 : 1 ≤ j) (hj : j ≤ K) (hjp : j + 1 ≤ K)

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "PA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱp)
  (j + 1) hjp
local notation "PB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱp)
  (j + 1) hjp
local notation "CA" => coverOf (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
  (ϱ := ϱp) (j + 1) hjp)
local notation "CB" => coverOf (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K)
  (ϱ := ϱp) (j + 1) hjp)
local notation "ιb" x:max => Subtype.mk (bm (x : CTorus d L N₁ m₁ K))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := K) (ϱ := ϱ) hj1 hj _)

include hj1 in
/-- **D0: the decoupled fluctuation on two tori, from the raw data.**  Let `F₁`, `F₁'` be maps
with the defining property of the decoupled background pair of Theorem I-4b for the generating set
`levelGS (j + 1)` of each torus (as in `decBg_value_twoTorus`), and `Sol`, `Sol'` maps with the
defining property of the analytic solution of Theorem I-4a for the pair
`(coverOf (levelGS (j + 1)), levelGS j)` (as in `decSol_value_twoTorus`).  Let the data of the
fluctuation problem be `flEdat` of the background values: `e = (barField D.Ψ φ, flAlpha α, ψ, 0)`
with `(φ, α) = F₁ (s, rawOf D)` (and likewise on the second torus).  Under the geometric
hypotheses of the two comparisons on a common component `Y`, if the raw data agree on
`RowsDep (S_Y)` and the fluctuations agree on `S_Y^F`, then the fluctuation multipliers agree on
`S_Y^F` and the fluctuation fields on `Y`.  The base potential and the base field of the
fluctuation data are compared by `decSol_data_of_decBg`; the source `f₁ = 0` needs no
hypothesis. -/
theorem decSol_value_twoTorus_of_decBg {c BG : ℝ} (hS : DecSpecs d L c BG) {a : ℕ → ℝ} {ν : ℝ}
    (SPA : DGSetting PA a ν) (SPB : DGSetting PB a ν) (hconn : HatConn PA)
    (hconn' : HatConn PB) (HBg : BgHyp d L K ϱp a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : DecParams PA × RawData d L (N₁ * L ^ m₁) K N → ((PA).Ω 1 × Fin N → ℂ) × ((PA).Ω 1 → ℂ)}
    {F₁' : DecParams PB × RawData d L (N₁' * L ^ m₁) K N →
      ((PB).Ω 1 × Fin N → ℂ) × ((PB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams PA) (D : BgData PA N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC PA (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (PA).Ω 1 × Fin N → ℂ)
        (α : (PA).Ω 1 → ℂ), IsDecBg PA a ν (rho4 d L N BG κ) s D φ α → F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams PB) (D : BgData PB N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC PB (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (PB).Ω 1 × Fin N → ℂ)
        (α : (PB).Ω 1 → ℂ), IsDecBg PB a ν (rho4 d L N BG κ) s D φ α → F₁' (s, rawOf D) = (φ, α))
    {s : DecParams PA} {s' : DecParams PB} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D : BgData PA N} {D' : BgData PB N}
    (hDd : InUnionDomainC PA (bgC0 d L N) (c7 d L N BG κ) ν D)
    (hDd' : InUnionDomainC PB (bgC0 d L N) (c7 d L N BG κ) ν D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ K)} {X₁' Y' : Finset (CTorus d L N₁' m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (PA).Ω 1) Y)
    (hYc : IsNnComp ((Vset X₁' 𝒞').filter fun x => x ∈ (PB).Ω 1) Y')
    (hs0 : ∀ P ∈ parCubes PA X₁, P ∉ 𝒞 → extS PA s P = 0)
    (hs0' : ∀ P ∈ parCubes PB X₁', P ∉ 𝒞' → extS PB s' P = 0)
    (hY' : Y.image bm = Y') (hB' : (SY PA X₁ 𝒞 Y).image bm = SY PB X₁' 𝒞' Y')
    (hagree : ∀ q ∈ innerCentres PA (SY PA X₁ 𝒞 Y),
      sProd PB (extS PB s') (Prod.map id bm q) = sProd PA (extS PA s) q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + 1 + m₁) + 7 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + 1 + m₁) + 7 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    (hD : RawBoxAgree {z | RowsDep PA a ν (SY PA X₁ 𝒞 Y) z} (rawOf D) (rawOf D'))
    {Kc Cx cstar BG₂ : ℝ} (hF : Dec2.FamSpec d L Kc Cx cstar BG₂)
    (SA : Dec2.CoverBase CA HA a ν Kc Cx) (SB : Dec2.CoverBase CB HB a ν Kc Cx) {κ₂ : ℝ}
    (hκ₂ : 0 ≤ κ₂) (hM₂ : cstar * Real.exp (N0 d L * κ₂) ≤ (L : ℝ) ^ m₁) (ιU : Bool)
    {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ₂) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ₂) (gamma1 d / 8))
    {Sol : Dec2.DecParams CA × Edat HA N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams CB × Edat HB N → ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams CA × Edat HA N, (∀ P, ‖p.1 P‖ < Real.exp κ₂) →
      StrictDataM HA N ιU δ₀ δ₁ p.2 →
        (Sol p).1 = dphi HA (Dec2.decG CA HA a ν p.1) p.2.2.1 p.2.1
          (pertSource HA a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed CA HA a ν p.1 ιU p.2.2.1 p.2.1
          (pertSource HA a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small HA (Sol p).2 (c6' d L N (famConst d L BG₂ κ₂) (gamma1 d / 8)) ∧
        Small HA (Sol p).2 (cK2' d L N (famConst d L BG₂ κ₂) * δ₁) ∧
        SupBounds HA (Sol p).1 (cK2' d L N (famConst d L BG₂ κ₂) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small HA δα' (c6' d L N (famConst d L BG₂ κ₂) (gamma1 d / 8)) →
          Dec2.DecFixed CA HA a ν p.1 ιU p.2.2.1 p.2.1
            (pertSource HA a p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams CB × Edat HB N, (∀ P, ‖p.1 P‖ < Real.exp κ₂) →
      StrictDataM HB N ιU δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi HB (Dec2.decG CB HB a ν p.1) p.2.2.1 p.2.1
          (pertSource HB a p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed CB HB a ν p.1 ιU p.2.2.1 p.2.1
          (pertSource HB a p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small HB (Sol' p).2 (c6' d L N (famConst d L BG₂ κ₂) (gamma1 d / 8)) ∧
        Small HB (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ₂) * δ₁) ∧
        SupBounds HB (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ₂) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small HB δα' (c6' d L N (famConst d L BG₂ κ₂) (gamma1 d / 8)) →
          Dec2.DecFixed CB HB a ν p.1 ιU p.2.2.1 p.2.1
            (pertSource HB a p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {σ : Dec2.DecParams CA} {σ' : Dec2.DecParams CB} (hσ : ∀ P, ‖σ P‖ < Real.exp κ₂)
    (hσ' : ∀ P, ‖σ' P‖ < Real.exp κ₂)
    {ψ : CTorus d L N₁ m₁ K → Fin N → ℂ} {ψ' : CTorus d L N₁' m₁ K → Fin N → ℂ}
    (he : StrictDataM HA N ιU δ₀ δ₁ (flEdat PA HA (F₁ (s, rawOf D)) D.Ψ ψ))
    (he' : StrictDataM HB N ιU δ₀ δ₁ (flEdat PB HB (F₁' (s', rawOf D')) D'.Ψ ψ'))
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)} {A' : Finset (ℕ × CTorus d L N₁' m₁ K)}
    (hYF : Dec2.IsIncUnion CA HA a ν X₁ 𝒞 Y A) (hYFc : Dec2.IsIncUnion CB HB a ν X₁' 𝒞' Y' A')
    (hσ0 : ∀ P ∈ (CA).parCubes X₁, P ∉ 𝒞 → Dec2.extS CA σ P = 0)
    (hσ0' : ∀ P ∈ (CB).parCubes X₁', P ∉ 𝒞' → Dec2.extS CB σ' P = 0)
    (hBF' : (Dec2.SYF CA HA a ν X₁ 𝒞 Y).image bm = Dec2.SYF CB HB a ν X₁' 𝒞' Y')
    (hagreeF : ∀ q ∈ Dec2.innerCentres CA HA (Dec2.SYF CA HA a ν X₁ 𝒞 Y),
      (CB).sProd (Dec2.extS CB σ') (Prod.map id bm q) = (CA).sProd (Dec2.extS CA σ) q)
    (hΨB : ∀ x ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y, ψ x = ψ' (bm x)) :
    (∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      (Sol' (σ', flEdat PB HB (F₁' (s', rawOf D')) D'.Ψ ψ')).2 (ιb x) =
        (Sol (σ, flEdat PA HA (F₁ (s, rawOf D)) D.Ψ ψ)).2 x) ∧
    (∀ y : (HA).Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      (Sol' (σ', flEdat PB HB (F₁' (s', rawOf D')) D'.Ψ ψ')).1 (ιb y, i) =
        (Sol (σ, flEdat PA HA (F₁ (s, rawOf D)) D.Ψ ψ)).1 (y, i)) := by
  obtain ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hDC⟩ := id hDd
  obtain ⟨δ', ε', hδ0', hδε', hε', hδ', hνε', hDC'⟩ := id hDd'
  obtain ⟨φ, α, hsol, -⟩ := i4b_exists_unique hS SPA HBg hκ hM (fun P => (hs P).le) hδ0 hδε hε
    hδ hνε hDC
  obtain ⟨φ', α', hsol', -⟩ := i4b_exists_unique hS SPB HBg hκ hM (fun P => (hs' P).le) hδ0' hδε'
    hε' hδ' hνε' hDC'
  have e1 := hF₁ s D hs hDd φ α hsol
  have e2 := hF₁' s' D' hs' hDd' φ' α' hsol'
  rw [e1] at he ⊢
  rw [e2] at he' ⊢
  obtain ⟨hαB, hφR⟩ := decSol_data_of_decBg hj1 hj hjp hS SPA SPB hconn hconn' HBg hκ hM
    (fun P => (hs P).le) (fun P => (hs' P).le) hδ0 hδε hε hδ hνε hδ0' hδε' hε' hδ' hνε' hDC hDC'
    hY hYc hs0 hs0' hY' hB' hagree hYR hn hn' hD hsol hsol'
  exact decSol_value_twoTorus hj1 hj hjp hF SA SB hκ₂ hM₂ ιU h0 h1 hδ₀ hδ₁ hSol hSol' hσ hσ' he
    he' hYF hYFc hσ0 hσ0' hY' hBF' hagreeF hYR hn hn' hαB hφR hΨB (fun _ _ _ => rfl)

end FromRaw

/-! ### Abstract transport lemmas -/

section AbstractInv

variable {A B : Type*} [Fintype A] [Fintype B]

/-- **A sum, transported.**  If `F` vanishes off `S`, `F'` off `S'`, and `F' ∘ ι = F` on `S`
(`ι` a bijection of `S` onto `S'`), the sums agree. -/
theorem sum_transport (S : A → Prop) (S' : B → Prop) [DecidablePred S] [DecidablePred S']
    (ι : A → B) (hinj : ∀ a b, S a → S b → ι a = ι b → a = b) (hmap : ∀ a, S a → S' (ι a))
    (hsurj : ∀ b, S' b → ∃ a, S a ∧ ι a = b) (F : A → ℂ) (F' : B → ℂ)
    (h0 : ∀ a, ¬ S a → F a = 0) (h0' : ∀ b, ¬ S' b → F' b = 0)
    (he : ∀ a, S a → F' (ι a) = F a) : ∑ b, F' b = ∑ a, F a := by
  have h1 : ∑ a, F a = ∑ a, if S a then F' (ι a) else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : S a
    · rw [ite_eq_left ha, he a ha]
    · rw [ite_eq_right ha, h0 a ha]
  have h2 : ∑ b, F' b = ∑ b, if S' b then F' b else 0 := by
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : S' b
    · rw [ite_eq_left hb]
    · rw [ite_eq_right hb, h0' b hb]
  rw [h1, h2, sum_ite_transport S S' ι hinj hmap hsurj F']

/-- A square matrix that does not couple the rows of `S` to the columns off `S` and is invertible
has an invertible `S`-block: a vector supported in `S` whose image vanishes on `S` is `0`. -/
theorem eq_zero_of_triangular [DecidableEq B] (S' : B → Prop) [DecidablePred S'] (M' : Matrix B B ℂ)
    (hM0' : ∀ x z, S' x → ¬ S' z → M' x z = 0) (hU' : IsUnit M') {v : B → ℂ}
    (hv0 : ∀ b, ¬ S' b → v b = 0) (hMv : ∀ b, S' b → (M' *ᵥ v) b = 0) : v = 0 := by
  have hdet' := (Matrix.isUnit_iff_isUnit_det _).1 hU'
  set Ms : Matrix {b // S' b} {b // S' b} ℂ := M'.submatrix Subtype.val Subtype.val with hMs
  set Ws : Matrix {b // S' b} {b // S' b} ℂ := (M'⁻¹).submatrix Subtype.val Subtype.val with hWs
  have hsub : ∀ (b : {b // S' b}) (F : B → ℂ), (∀ d, ¬ S' d → F d = 0) →
      ∑ d : {b // S' b}, F d = ∑ d, F d := by
    intro b F hF
    rw [← Fintype.sum_subtype_add_sum_subtype S' F]
    have : ∑ d : {x // ¬ S' x}, F d = 0 := Finset.sum_eq_zero fun d _ => hF d d.2
    rw [this, add_zero]
  have hMW : Ms * Ws = 1 := by
    ext b c
    rw [Matrix.mul_apply]
    simp only [hMs, hWs, Matrix.submatrix_apply]
    rw [hsub b (fun d => M' b d * M'⁻¹ d c) (fun d hd => by rw [hM0' b d b.2 hd, zero_mul])]
    have := congrFun (congrFun (Matrix.mul_nonsing_inv M' hdet') b) c
    rw [Matrix.mul_apply] at this
    rw [this]
    by_cases h : b = c
    · subst h; simp
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (fun h' => h (Subtype.ext h'))]
  have hWM : Ws * Ms = 1 := mul_eq_one_comm.1 hMW
  have hMs0 : Ms *ᵥ (fun b => v b) = 0 := by
    funext b
    simp only [Matrix.mulVec, dotProduct, hMs, Matrix.submatrix_apply, Pi.zero_apply]
    rw [hsub b (fun d => M' b d * v d) (fun d hd => by rw [hv0 d hd, mul_zero])]
    exact hMv b b.2
  have hvs : (fun b : {b // S' b} => v b) = 0 := by
    rw [← Matrix.one_mulVec (fun b : {b // S' b} => v b), ← hWM, ← Matrix.mulVec_mulVec, hMs0,
      Matrix.mulVec_zero]
  funext b
  by_cases hb : S' b
  · exact congrFun hvs ⟨b, hb⟩
  · exact hv0 b hb

/-- **Rows of `M⁻¹ f` on a block, transported.**  Let `ι` be a bijection of `S ⊆ A` onto `S' ⊆ B`.
If `M`, `M'` are invertible, their rows in `S`, `S'` read only columns in `S`, `S'`, their entries
on `S × S` correspond, and the sources correspond on `S`, then the rows on `S` of `M⁻¹ f` and
`M'⁻¹ f'` correspond.  (The rows off `S` may read `S`: only the `S`-blocks are compared.) -/
theorem inv_mulVec_transport_of_triangular [DecidableEq A] [DecidableEq B] (S : A → Prop)
    (S' : B → Prop) [DecidablePred S] [DecidablePred S'] (ι : A → B)
    (hinj : ∀ a b, S a → S b → ι a = ι b → a = b) (hmap : ∀ a, S a → S' (ι a))
    (hsurj : ∀ b, S' b → ∃ a, S a ∧ ι a = b) (M : Matrix A A ℂ) (M' : Matrix B B ℂ)
    (hM0 : ∀ x z, S x → ¬ S z → M x z = 0) (hM0' : ∀ x z, S' x → ¬ S' z → M' x z = 0)
    (hM : ∀ x z, S x → S z → M' (ι x) (ι z) = M x z) (hU : IsUnit M) (hU' : IsUnit M')
    {f : A → ℂ} {f' : B → ℂ} (hf : ∀ z, S z → f' (ι z) = f z) {y : A} (hy : S y) :
    (M'⁻¹ *ᵥ f') (ι y) = (M⁻¹ *ᵥ f) y := by
  obtain ⟨g, hg⟩ : ∃ g : A → ℂ, g = M⁻¹ *ᵥ f := ⟨_, rfl⟩
  obtain ⟨g', hg'⟩ : ∃ g' : B → ℂ, g' = M'⁻¹ *ᵥ f' := ⟨_, rfl⟩
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hdet' := (Matrix.isUnit_iff_isUnit_det _).1 hU'
  have hMg : M *ᵥ g = f := by
    rw [hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hMg' : M' *ᵥ g' = f' := by
    rw [hg', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet', Matrix.one_mulVec]
  obtain ⟨κ, hκ⟩ : ∃ κ : B → A, ∀ a, S a → κ (ι a) = a := by
    refine ⟨fun b => if h : ∃ a, S a ∧ ι a = b then h.choose else y, fun a ha => ?_⟩
    have h : ∃ a', S a' ∧ ι a' = ι a := ⟨a, ha, rfl⟩
    dsimp only
    rw [dite_eq_left h]
    exact hinj _ _ h.choose_spec.1 ha h.choose_spec.2
  obtain ⟨v, hv⟩ : ∃ v : B → ℂ, v = fun b => if S' b then g (κ b) - g' b else 0 := ⟨_, rfl⟩
  have hvι : ∀ a, S a → v (ι a) = g a - g' (ι a) := fun a ha => by
    rw [hv]; dsimp only; rw [ite_eq_left (hmap a ha), hκ a ha]
  have hv0 : ∀ b, ¬ S' b → v b = 0 := fun b hb => by
    rw [hv]; dsimp only; rw [ite_eq_right hb]
  have hMv : ∀ b, S' b → (M' *ᵥ v) b = 0 := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := hsurj b hb
    have e1 : (M' *ᵥ v) (ι x) = (M *ᵥ (g - fun a => g' (ι a))) x := by
      refine mulVec_apply_transport S S' ι hinj hmap hsurj M M' _ _ (fun a ha => ?_)
        (fun b hb => ?_) (fun a ha => ?_)
      · rw [hM0 x a hx ha, zero_mul]
      · rw [hv0 b hb, mul_zero]
      · rw [hM x a hx ha, hvι a ha]; rfl
    have e2 : (M' *ᵥ g') (ι x) = (M *ᵥ fun a => g' (ι a)) x := by
      refine mulVec_apply_transport S S' ι hinj hmap hsurj M M' _ _ (fun a ha => ?_)
        (fun b hb => ?_) (fun a ha => ?_)
      · rw [hM0 x a hx ha, zero_mul]
      · rw [hM0' (ι x) b (hmap x hx) hb, zero_mul]
      · rw [hM x a hx ha]
    rw [e1, Matrix.mulVec_sub, Pi.sub_apply, ← e2, hMg, hMg', hf x hx, sub_self]
  have hvz := eq_zero_of_triangular S' M' hM0' hU' hv0 hMv
  have hgg : g' (ι y) = g y := by
    have := hvι y hy
    rw [hvz, Pi.zero_apply] at this
    exact (sub_eq_zero.1 this.symm).symm
  rw [← hg, ← hg', hgg]

end AbstractInv

/-! ### The constraint operators on one torus: the block structure of `M_{x,s}` -/

section MBlock

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl

/-- **`M_{x,s}` does not couple `S_Y` to its complement.**  For the top level, a union `Y` of
components of the cut and factors vanishing off `𝒞` on the parameter cubes, the entries of
`M_{x,s} = φ₀² - K_x(φ₀) Ĝ_{k,x,s} φ₀` from a row in `S_Y` to a column outside `S_Y` vanish: the
rows of `K_x(φ₀)` at `S_Y` read only `Y` (`row_in_Y`), `Ĝ_{k,x,s}` vanishes on `Y \ S_Y`, and its
rows on `S_Y` read only `S_Y`. -/
theorem decM_apply_eq_zero_of_mem_SY {a : ℕ → ℝ} {aT x₀ ν : ℝ} (S : XSetting (GA) a aT ν)
    (hx₀ : 0 ≤ x₀) (hconn : HatConn (GA)) {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (GA).Ω 1) Y)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} (hs0 : ∀ P ∈ parCubes (GA) X₁, P ∉ 𝒞 → s P = 0)
    {α : (GA).Ω 1 → ℂ} (hα : AdmPot (GA) α) (hU : IsUnit (1 - Kcalx (GA) a aT x₀ ν α s))
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) {z w : (GA).Ω 1}
    (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y)
    (hw : (w : CTorus d L N₁ m₁ (k + 1)) ∉ SY (GA) X₁ 𝒞 Y) :
    decM (GA) a aT x₀ ν α s φ z w = 0 := by
  have hj1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hdich := dich_SY_of_comp S.dg hconn hY hs0
  have hrow := row_SY_levelGS hj1 le_rfl S.dg hconn hY hs0
  have e : decM (GA) a aT x₀ ν α s φ z w =
      (decM (GA) a aT x₀ ν α s φ *ᵥ Pi.single w 1) z := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hzw : z ≠ w := fun h => hw (by rw [← h]; exact hz)
  have hv : ∀ b : (GA).Ω 1, (b : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y →
      (Pi.single w 1 : (GA).Ω 1 → ℂ) b = 0 := fun b hb =>
    Pi.single_eq_of_ne (fun h : b = w => hw (by rw [← h]; exact hb)) _
  rw [e, decM_mulVec_eq, Pi.sub_apply, fieldMul_transpose_mulVec, commK_mulVec]
  have t1 : ∑ i, restrictField (GA) φ z i *
      (fieldMul (restrictField (GA) φ) *ᵥ (Pi.single w 1 : (GA).Ω 1 → ℂ)) (z, i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [fieldMul_mulVec, Pi.single_eq_of_ne hzw, mul_zero, mul_zero]
  have t2 : ∀ y : (GA).Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i,
      (liftOp N (Gsx (GA) a aT x₀ ν α s) *ᵥ (fieldMul (restrictField (GA) φ) *ᵥ
        (Pi.single w 1 : (GA).Ω 1 → ℂ))) (y, i) = 0 := by
    intro y hyY i
    rw [liftOp_mulVec]
    by_cases hyT : (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y
    · have key : ∀ f : (GA).Ω 1 → ℂ, (∀ b : (GA).Ω 1,
          (b : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y → f b = 0) →
          (Gsx (GA) a aT x₀ ν α s *ᵥ f) y = 0 := by
        intro f hf
        simp only [Matrix.mulVec, dotProduct]
        refine Finset.sum_eq_zero fun b _ => ?_
        by_cases hb : (b : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y
        · rw [hf b hb, mul_zero]
        · rw [Gsx_apply_eq_zero_of_mem S hx₀ hα hU hdich hyT hb, zero_mul]
      exact key _ fun b hb => by rw [fieldMul_mulVec, hv b hb, mul_zero]
    · exact Gsx_apply_eq_zero_of_not_mem S hx₀ hα hrow _ hyY hyT
  have t3 : ∑ y, ∑ i, xDirichletOperator (GA) a aT x₀ ν α z y *
      (restrictField (GA) φ z i - restrictField (GA) φ y i) *
      (liftOp N (Gsx (GA) a aT x₀ ν α s) *ᵥ (fieldMul (restrictField (GA) φ) *ᵥ
        (Pi.single w 1 : (GA).Ω 1 → ℂ))) (y, i) = 0 := by
    refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun i _ => ?_
    by_cases h0 : xDirichletOperator (GA) a aT x₀ ν α z y = 0
    · rw [h0, zero_mul, zero_mul]
    · rw [t2 y (row_in_Y S hz h0) i, mul_zero]
  rw [t1, t3, sub_zero]

end MBlock

/-! ### The constraint operators and `Z_{x,s}` on two tori -/

section ZRows

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "ιb" x:max => Subtype.mk (bm (x : CTorus d L N₁ m₁ (k + 1)))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) (ϱ := ϱ)
    (Nat.le_add_left 1 k) le_rfl _)

/-- `boxMap` is a bijection of a set `T` of sites of the box of radius `R` onto its image, as a map
of the sites `Ω₁` of the top levels. -/
theorem boxMap_bij_top {T : Finset (CTorus d L N₁ m₁ (k + 1))}
    {T' : Finset (CTorus d L N₁' m₁ (k + 1))} (hT' : T.image bm = T') {R : ℕ}
    (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1)) :
    (∀ a b : (GA).Ω 1, (a : CTorus d L N₁ m₁ (k + 1)) ∈ T → (b : CTorus d L N₁ m₁ (k + 1)) ∈ T →
      (ιb a : (GB).Ω 1) = ιb b → a = b) ∧
    (∀ a : (GA).Ω 1, (a : CTorus d L N₁ m₁ (k + 1)) ∈ T →
      ((ιb a : (GB).Ω 1) : CTorus d L N₁' m₁ (k + 1)) ∈ T') ∧
    (∀ b : (GB).Ω 1, (b : CTorus d L N₁' m₁ (k + 1)) ∈ T' →
      ∃ a : (GA).Ω 1, (a : CTorus d L N₁ m₁ (k + 1)) ∈ T ∧ (ιb a : (GB).Ω 1) = b) := by
  refine ⟨fun a b ha hb h => Subtype.ext (boxMap_inj (hm' := hm') (hTR _ ha) (hTR _ hb)
    (congrArg Subtype.val h)), fun a ha => ?_, fun b hb => ?_⟩
  · show bm (a : CTorus d L N₁ m₁ (k + 1)) ∈ T'
    rw [← hT']; exact Finset.mem_image_of_mem _ ha
  · rw [← hT', Finset.mem_image] at hb
    obtain ⟨x2, hx2T, hx2⟩ := hb
    exact ⟨⟨x2, levelGS_mem_Ω_one (Nat.le_add_left 1 k) le_rfl x2⟩, hx2T, Subtype.ext hx2⟩

variable {a : ℕ → ℝ} {aT x₀ ν : ℝ}
  {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
  {X₁' Y' : Finset (CTorus d L N₁' m₁ (k + 1))} {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ (k + 1))}
  {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ}
  {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} {R : ℕ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}

variable (SA : XSetting (GA) a aT ν) (SB : XSetting (GB) a aT ν) (hx₀ : 0 ≤ x₀)
  (hconn : HatConn (GA)) (hconn' : HatConn (GB))
  (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (GA).Ω 1) Y)
  (hYc : IsNnComp ((Vset X₁' 𝒞').filter fun x => x ∈ (GB).Ω 1) Y')
  (hs0 : ∀ P ∈ parCubes (GA) X₁, P ∉ 𝒞 → s P = 0)
  (hs0' : ∀ P ∈ parCubes (GB) X₁', P ∉ 𝒞' → s' P = 0)
  (hY' : Y.image bm = Y') (hB' : (SY (GA) X₁ 𝒞 Y).image bm = SY (GB) X₁' 𝒞' Y')
  (hagree : ∀ q ∈ innerCentres (GA) (SY (GA) X₁ 𝒞 Y),
    sProd (GB) s' (Prod.map id bm q) = sProd (GA) s q)
  (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
  (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
  (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
  (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
  (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y → α' (ιb x) = α x)
  (hU : IsUnit (1 - Kcalx (GA) a aT x₀ ν α s)) (hU' : IsUnit (1 - Kcalx (GB) a aT x₀ ν α' s'))
include SA SB hx₀ hconn hconn' hY hYc hs0 hs0' hY' hB' hagree hYR hn hn' hαA hαB hα hU hU'

/-- **The rows of `Ĝ_{k,x,s} w` on a component, on two tori**: for `w` corresponding on `S_Y`, the
outputs correspond on `Y` (`xGreen_rows_transport` with `T = S_Y`, the dichotomy and the rows
outside `S_Y` from the cut, `dich_SY_of_comp`, `row_SY_levelGS`). -/
theorem Gsx_lift_rows_SY {w : (GA).Ω 1 × Fin N → ℂ} {w' : (GB).Ω 1 × Fin N → ℂ}
    (hw : ∀ y : (GA).Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y → ∀ i,
      w' (ιb y, i) = w (y, i))
    (y : (GA).Ω 1) (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y) (i : Fin N) :
    (liftOp N (Gsx (GB) a aT x₀ ν α' s') *ᵥ w') (ιb y, i) =
      (liftOp N (Gsx (GA) a aT x₀ ν α s) *ᵥ w) (y, i) := by
  have hj1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  rw [liftOp_mulVec, liftOp_mulVec]
  exact xGreen_rows_transport SA SB hx₀ hY' hB' (SY_subset_levelGS hj1 le_rfl) hYR hn hn' hαA hαB
    hα hU hU' (dich_SY_of_comp SA.dg hconn hY hs0) (dich_SY_of_comp SB.dg hconn' hYc hs0')
    (row_SY_levelGS hj1 le_rfl SA.dg hconn hY hs0) (row_SY_levelGS hj1 le_rfl SB.dg hconn' hYc hs0')
    hagree (f := fun b => w (b, i)) (f' := fun b => w' (b, i)) (fun x hx => hw x hx i) y hy

omit hconn hconn' hY hYc hs0 hs0' hagree hαA hαB hU hU' in
/-- **The rows of `K_x(φ₀) u` at `S_Y`, on two tori.**  The row of the commutator at a site of
`S_Y` reads `u` and `φ₀` at the sites `y` with `H_{k,x}(A) z y ≠ 0`, which lie in `Y`
(`row_in_Y`) and in `R(S_Y)` (`rowsCov_R`). -/
theorem commKx_rows_transport
    (hφR : ∀ u ∈ rowsCov_R (GA) a aT ν α X₁ 𝒞 Y, φ' (bm u) = φ u)
    {u : (GA).Ω 1 × Fin N → ℂ} {u' : (GB).Ω 1 × Fin N → ℂ}
    (hu : ∀ y : (GA).Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i, u' (ιb y, i) = u (y, i))
    {z : (GA).Ω 1} (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y) :
    (commK (xDirichletOperator (GB) a aT x₀ ν α') (restrictField (GB) φ') *ᵥ u') (ιb z) =
      (commK (xDirichletOperator (GA) a aT x₀ ν α) (restrictField (GA) φ) *ᵥ u) z := by
  have hj1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hSYY := SY_subset_levelGS (ϱ := ϱ) (X₁ := X₁) (𝒞 := 𝒞) (Y := Y) hj1 le_rfl
  obtain ⟨hinj, hmap, hsurj⟩ := boxMap_bij_top (ϱ := ϱ) hY' hYR
    (by omega : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
  have hz' : ((ιb z : (GB).Ω 1) : CTorus d L N₁' m₁ (k + 1)) ∈ SY (GB) X₁' 𝒞' Y' := by
    rw [← hB']; exact Finset.mem_image_of_mem _ hz
  rw [commK_mulVec, commK_mulVec]
  refine sum_transport (fun y : (GA).Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y)
    (fun y : (GB).Ω 1 => (y : CTorus d L N₁' m₁ (k + 1)) ∈ Y') (fun y => ιb y) hinj hmap hsurj
    _ _ (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_)
  · refine Finset.sum_eq_zero fun i _ => ?_
    have h0 : xDirichletOperator (GA) a aT x₀ ν α z y = 0 := by
      by_contra h0
      exact hy (row_in_Y SA hz h0)
    rw [h0, zero_mul, zero_mul]
  · refine Finset.sum_eq_zero fun i _ => ?_
    have h0 : xDirichletOperator (GB) a aT x₀ ν α' (ιb z) y = 0 := by
      by_contra h0
      exact hy (row_in_Y SB hz' h0)
    rw [h0, zero_mul, zero_mul]
  · have hzR := hYR _ (hSYY hz)
    have hyR := hYR _ hy
    rw [xDirichletOperator_boxMap_row (ρ := R) a aT x₀ ν (by omega) (by omega) z y (hα z hz) hzR
      hyR]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h0 : xDirichletOperator (GA) a aT x₀ ν α z y = 0
    · rw [h0, zero_mul, zero_mul, zero_mul, zero_mul]
    · have e1 : φ' (bm (z : CTorus d L N₁ m₁ (k + 1))) = φ z := hφR _ (Or.inl hz)
      have e2 : φ' (bm (y : CTorus d L N₁ m₁ (k + 1))) = φ y :=
        hφR _ (Or.inr ⟨z, y, hz, rfl, x₀, hx₀, h0⟩)
      simp only [restrictField]
      rw [e1, e2, hu y hy i]

/-- **The rows of `N_{x,s} w` at `S_Y`, on two tori**, for `w` corresponding on `S_Y` and the
field corresponding on `R(S_Y)`. -/
theorem decN_rows_transport
    (hφR : ∀ u ∈ rowsCov_R (GA) a aT ν α X₁ 𝒞 Y, φ' (bm u) = φ u)
    {w : (GA).Ω 1 × Fin N → ℂ} {w' : (GB).Ω 1 × Fin N → ℂ}
    (hw : ∀ y : (GA).Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y → ∀ i,
      w' (ιb y, i) = w (y, i))
    {z : (GA).Ω 1} (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y) :
    (decN (GB) a aT x₀ ν α' s' φ' *ᵥ w') (ιb z) = (decN (GA) a aT x₀ ν α s φ *ᵥ w) z := by
  rw [decN_mulVec_eq, decN_mulVec_eq, Pi.sub_apply, Pi.sub_apply, fieldMul_transpose_mulVec,
    fieldMul_transpose_mulVec]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : φ' (bm (z : CTorus d L N₁ m₁ (k + 1))) = φ z := hφR _ (Or.inl hz)
    simp only [restrictField]
    rw [e1, hw z hz i]
  · exact commKx_rows_transport SA SB hx₀ hY' hB' hYR hn hn' hα hφR
      (fun y hy i => Gsx_lift_rows_SY SA SB hx₀ hconn hconn' hY hYc hs0 hs0'
        hY' hB' hagree hYR hn hn' hαA hαB hα hU hU' hw y hy i) hz

/-- **The rows of `M_{x,s} v` at `S_Y`, on two tori**, for `v` corresponding on `S_Y`:
`M_{x,s} v = N_{x,s} (φ₀ v)`. -/
theorem decM_rows_transport
    (hφR : ∀ u ∈ rowsCov_R (GA) a aT ν α X₁ 𝒞 Y, φ' (bm u) = φ u)
    {v : (GA).Ω 1 → ℂ} {v' : (GB).Ω 1 → ℂ}
    (hv : ∀ y : (GA).Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y → v' (ιb y) = v y)
    {z : (GA).Ω 1} (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y) :
    (decM (GB) a aT x₀ ν α' s' φ' *ᵥ v') (ιb z) = (decM (GA) a aT x₀ ν α s φ *ᵥ v) z := by
  have e : ∀ {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (β : G.Ω 1 → ℂ)
      (ψ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (σ : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
      (u : G.Ω 1 → ℂ), decM G a aT x₀ ν β σ ψ *ᵥ u =
        decN G a aT x₀ ν β σ ψ *ᵥ (fieldMul (restrictField G ψ) *ᵥ u) := by
    intro G β ψ σ u
    rw [decM_mulVec_eq, decN_mulVec_eq]
  have e' : ∀ {G : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ} (β : G.Ω 1 → ℂ)
      (ψ : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) (σ : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ)
      (u : G.Ω 1 → ℂ), decM G a aT x₀ ν β σ ψ *ᵥ u =
        decN G a aT x₀ ν β σ ψ *ᵥ (fieldMul (restrictField G ψ) *ᵥ u) := by
    intro G β ψ σ u
    rw [decM_mulVec_eq, decN_mulVec_eq]
  rw [e, e']
  refine decN_rows_transport SA SB hx₀ hconn hconn' hY hYc hs0 hs0' hY' hB' hagree hYR hn hn'
    hαA hαB hα hU hU' hφR (fun y hy i => ?_) hz
  rw [fieldMul_mulVec, fieldMul_mulVec, hv y hy]
  have e1 : φ' (bm (y : CTorus d L N₁ m₁ (k + 1))) = φ y := hφR _ (Or.inl hy)
  simp only [restrictField]
  rw [e1]

/-- **The rows of `M_{x,s}⁻¹ f` on `S_Y`, on two tori.**  `M_{x,s}` does not couple `S_Y` to its
complement (`decM_apply_eq_zero_of_mem_SY`), its entries on `S_Y × S_Y` correspond
(`decM_rows_transport`), so the `S_Y`-blocks of the inverses correspond
(`inv_mulVec_transport_of_triangular`). -/
theorem decM_inv_rows_transport
    (hφR : ∀ u ∈ rowsCov_R (GA) a aT ν α X₁ 𝒞 Y, φ' (bm u) = φ u)
    (hM : IsUnit (decM (GA) a aT x₀ ν α s φ)) (hM' : IsUnit (decM (GB) a aT x₀ ν α' s' φ'))
    {f : (GA).Ω 1 → ℂ} {f' : (GB).Ω 1 → ℂ}
    (hf : ∀ y : (GA).Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y → f' (ιb y) = f y)
    {z : (GA).Ω 1} (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y) :
    ((decM (GB) a aT x₀ ν α' s' φ')⁻¹ *ᵥ f') (ιb z) =
      ((decM (GA) a aT x₀ ν α s φ)⁻¹ *ᵥ f) z := by
  have hj1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hSYY := SY_subset_levelGS (ϱ := ϱ) (X₁ := X₁) (𝒞 := 𝒞) (Y := Y) hj1 le_rfl
  obtain ⟨hinj, hmap, hsurj⟩ := boxMap_bij_top (ϱ := ϱ) hB' (fun x hx => hYR x (hSYY hx))
    (by omega : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
  refine inv_mulVec_transport_of_triangular
    (fun y : (GA).Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y)
    (fun y : (GB).Ω 1 => (y : CTorus d L N₁' m₁ (k + 1)) ∈ SY (GB) X₁' 𝒞' Y') (fun y => ιb y)
    hinj hmap hsurj _ _
    (fun x z hx hz => decM_apply_eq_zero_of_mem_SY SA hx₀ hconn hY hs0 hαA hU φ hx hz)
    (fun x z hx hz => decM_apply_eq_zero_of_mem_SY SB hx₀ hconn' hYc hs0' hαB hU' φ' hx hz)
    (fun x w hx hw => ?_) hM hM' hf hz
  have h1 : decM (GB) a aT x₀ ν α' s' φ' (ιb x) (ιb w) =
      (decM (GB) a aT x₀ ν α' s' φ' *ᵥ Pi.single (ιb w) 1) (ιb x) := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have h2 : decM (GA) a aT x₀ ν α s φ x w = (decM (GA) a aT x₀ ν α s φ *ᵥ Pi.single w 1) x := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  refine h1.trans (Eq.trans ?_ h2.symm)
  refine decM_rows_transport SA SB hx₀ hconn hconn' hY hYc hs0 hs0' hY' hB' hagree hYR hn hn'
    hαA hαB hα hU hU' hφR (fun y hy => ?_) hx
  by_cases hyw : y = w
  · subst hyw; simp
  · rw [Pi.single_eq_of_ne hyw, Pi.single_eq_of_ne (fun h => hyw (hinj y w hy hw h))]

/-- **The rows of `Z_{x,s} w = Ĝ_{k,x,s} w - Π_{x,s} w` on a component, on two tori.**  For `w`
corresponding on `S_Y`, the multipliers on `S_Y` and the fields on `R(S_Y)`, the outputs correspond
at every site of `Y`. -/
theorem decZ_rows_transport
    (hφR : ∀ u ∈ rowsCov_R (GA) a aT ν α X₁ 𝒞 Y, φ' (bm u) = φ u)
    (hM : IsUnit (decM (GA) a aT x₀ ν α s φ)) (hM' : IsUnit (decM (GB) a aT x₀ ν α' s' φ'))
    {w : (GA).Ω 1 × Fin N → ℂ} {w' : (GB).Ω 1 × Fin N → ℂ}
    (hw : ∀ y : (GA).Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y → ∀ i,
      w' (ιb y, i) = w (y, i))
    (y : (GA).Ω 1) (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y) (i : Fin N) :
    (decZ (GB) a aT x₀ ν α' s' φ' *ᵥ w') (ιb y, i) = (decZ (GA) a aT x₀ ν α s φ *ᵥ w) (y, i) := by
  have hZ : ∀ {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (aa : G.Ω 1 → ℂ)
      (ss : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (pp : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
      (ww : G.Ω 1 × Fin N → ℂ),
      decZ G a aT x₀ ν aa ss pp *ᵥ ww = liftOp N (Gsx G a aT x₀ ν aa ss) *ᵥ ww -
        liftOp N (Gsx G a aT x₀ ν aa ss) *ᵥ (fieldMul (restrictField G pp) *ᵥ
          ((decM G a aT x₀ ν aa ss pp)⁻¹ *ᵥ (decN G a aT x₀ ν aa ss pp *ᵥ ww))) := by
    intro G aa ss pp ww
    unfold decZ decPi
    rw [Matrix.sub_mulVec]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hZ' : ∀ {G : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ} (aa : G.Ω 1 → ℂ)
      (ss : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ) (pp : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ)
      (ww : G.Ω 1 × Fin N → ℂ),
      decZ G a aT x₀ ν aa ss pp *ᵥ ww = liftOp N (Gsx G a aT x₀ ν aa ss) *ᵥ ww -
        liftOp N (Gsx G a aT x₀ ν aa ss) *ᵥ (fieldMul (restrictField G pp) *ᵥ
          ((decM G a aT x₀ ν aa ss pp)⁻¹ *ᵥ (decN G a aT x₀ ν aa ss pp *ᵥ ww))) := by
    intro G aa ss pp ww
    unfold decZ decPi
    rw [Matrix.sub_mulVec]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hv : ∀ z : (GA).Ω 1, (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y →
      ((decM (GB) a aT x₀ ν α' s' φ')⁻¹ *ᵥ (decN (GB) a aT x₀ ν α' s' φ' *ᵥ w')) (ιb z) =
        ((decM (GA) a aT x₀ ν α s φ)⁻¹ *ᵥ (decN (GA) a aT x₀ ν α s φ *ᵥ w)) z :=
    fun z hz => decM_inv_rows_transport SA SB hx₀ hconn hconn' hY hYc hs0 hs0' hY' hB' hagree hYR
      hn hn' hαA hαB hα hU hU' hφR hM hM' (fun x hx => decN_rows_transport SA SB hx₀ hconn hconn'
        hY hYc hs0 hs0' hY' hB' hagree hYR hn hn' hαA hαB hα hU hU' hφR hw hx) hz
  rw [hZ, hZ', Pi.sub_apply, Pi.sub_apply,
    Gsx_lift_rows_SY SA SB hx₀ hconn hconn' hY hYc hs0 hs0' hY' hB' hagree hYR hn hn' hαA hαB hα
      hU hU' hw y hy i,
    Gsx_lift_rows_SY SA SB hx₀ hconn hconn' hY hYc hs0 hs0' hY' hB' hagree hYR hn hn' hαA hαB hα
      hU hU' (fun z hz j => ?_) y hy i]
  rw [fieldMul_mulVec, fieldMul_mulVec, hv z hz]
  have e1 : φ' (bm (z : CTorus d L N₁ m₁ (k + 1))) = φ z := hφR _ (Or.inl hz)
  simp only [restrictField]
  rw [e1]

end ZRows

/-! ### The unit lattice of the top level on two tori -/

section Unit

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

omit [NeZero N₁'] in
/-- Every point of the unit lattice is a unit point of the top level `levelGS (k + 1)`. -/
theorem mem_unitPts_levelTop (b : UnitTorus d L N₁ m₁ k) :
    b ∈ unitPts (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) le_rfl) := by
  obtain ⟨z, hz⟩ := exists_blockMap_eq (d := d) (unitBlock_side (N₁ := N₁) (L := L) (m₁ := m₁)
    (k := k)) (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) k) b
  refine (mem_unitPts _).2 ⟨z, ?_, hz⟩
  rw [layer_levelGS le_rfl]
  simp

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "ιb" x:max => Subtype.mk (bm (x : CTorus d L N₁ m₁ (k + 1)))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) (ϱ := ϱ)
    (Nat.le_add_left 1 k) le_rfl _)
set_option hygiene false in
local notation "ιu" b:max => Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _)

/-- **The unit block of a site of the box, on two tori**: `unitBlock (bm x) = bU (unitBlock x)`,
`bU` the box map of the unit lattices.  Margin: `2 ρ + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)`. -/
theorem unitBlock_boxMap {ρ : ℕ}
    (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    unitBlock (bm x) = bU (unitBlock x) := by
  have hp : 0 < L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) k
  have hrc : ρ < L ^ k * (ρ / L ^ k + 1) := Nat.lt_mul_div_succ ρ hp
  have hc : 2 * (ρ / L ^ k + 1) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1 - k) := by
    have hk : k + 1 - k = 1 := by omega
    rw [hk, pow_one]
    have h1 : ρ / L ^ k * L ^ k ≤ ρ := Nat.div_mul_le_self ρ (L ^ k)
    have h2 : L ^ k ≤ L ^ (k + 1) :=
      Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_succ k)
    have h3 : (N₁ * L ^ m₁) * L ^ (k + 1) = (N₁ * L ^ m₁ * L) * L ^ k := by ring
    have h4 : (2 * (ρ / L ^ k + 1) + 1) * L ^ k < (N₁ * L ^ m₁ * L) * L ^ k := by
      have e : (2 * (ρ / L ^ k + 1) + 1) * L ^ k = 2 * (ρ / L ^ k * L ^ k) + 3 * L ^ k := by ring
      rw [e, ← h3]; omega
    exact Nat.lt_of_mul_lt_mul_right h4
  exact jBlock_boxMap (N₀ := N₁ * L ^ m₁) (N₀' := N₁' * L ^ m₁) (k := k + 1) (j := k)
    (Nat.le_succ k) hrc hc x hx

omit [NeZero N₁'] in
/-- A site in the `m`-block of a site of the box of radius `ρ` lies in the box of radius
`ρ + L^m`. -/
theorem inBox_of_jBlock_eq {m ρ : ℕ} (hm : m ≤ k + 1)
    (hn : 2 * (ρ + L ^ m) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1)) {x y : CTorus d L N₁ m₁ (k + 1)}
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (h : jBlock d L (N₁ * L ^ m₁) (k + 1) m y = jBlock d L (N₁ * L ^ m₁) (k + 1) m x) :
    InBox d (ρ + L ^ m) ((N₁ * L ^ m₁) * L ^ (k + 1)) y :=
  inBox_of_mem_cell hn hx ((jBlock_eq_iff_mem_box hm y x).1 h)

omit [NeZero N₁'] in
/-- A unit point whose `(k+1)`-block is that of a site `x₀` of the box of radius `ρ` has a fine
site in that block, in the box of radius `ρ + L^(k+1)`. -/
theorem unit_anchor {ρ : ℕ} (hn : 2 * (ρ + L ^ (k + 1)) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    {x0 : CTorus d L N₁ m₁ (k + 1)} (hx0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x0)
    (b : unitPts (GA))
    (hb : unitBlock1 (b : UnitTorus d L N₁ m₁ k) = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x0) :
    ∃ y : CTorus d L N₁ m₁ (k + 1), unitBlock y = (b : UnitTorus d L N₁ m₁ k) ∧
      jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x0 ∧
      InBox d (ρ + L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) y := by
  obtain ⟨y, -, hy⟩ := (mem_unitPts _).1 b.2
  have h1 : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y =
      jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x0 := by
    rw [← unitBlock1_unitBlock, hy, hb]
  exact ⟨y, hy, h1, inBox_of_jBlock_eq le_rfl hn hx0 h1⟩

/-- The image of a unit point with a fine site `y` of the box: `ιu b = unitBlock (bm y)`. -/
theorem coe_ιu {ρ : ℕ} (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (b : unitPts (GA)) {y : CTorus d L N₁ m₁ (k + 1)}
    (hy : unitBlock y = (b : UnitTorus d L N₁ m₁ k))
    (hyR : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) y) :
    (((ιu b) : unitPts (GB)) : UnitTorus d L N₁' m₁ k) = unitBlock (bm y) := by
  show bU (b : UnitTorus d L N₁ m₁ k) = _
  rw [← hy, unitBlock_boxMap hn hyR]

/-- **The rows of `A_{k,x} g` on two tori** (`A = covA … (liftOp N P)`, `P` the projection onto
the constants of the `L`-blocks of the unit lattice): at a unit point `b₀` whose `(k+1)`-block is
that of a site `x₀` of the box, the rows correspond if the inputs correspond on the unit points of
that block.  Margin: `2 ρ + 5 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` (and for `N₁'`). -/
theorem covA_unit_rows_transport (c bb x₀ : ℝ) {ρ : ℕ}
    (hn : 2 * ρ + 5 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 5 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {x0 : CTorus d L N₁ m₁ (k + 1)} (hx0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x0)
    {b0 : unitPts (GA)}
    (hb0 : unitBlock1 (b0 : UnitTorus d L N₁ m₁ k) = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x0)
    {g : unitPts (GA) × Fin N → ℂ} {g' : unitPts (GB) × Fin N → ℂ}
    (hg : ∀ b3 : unitPts (GA), unitBlock1 (b3 : UnitTorus d L N₁ m₁ k) =
      unitBlock1 (b0 : UnitTorus d L N₁ m₁ k) → ∀ j, g' (ιu b3, j) = g (b3, j)) (i : Fin N) :
    (covA c bb x₀ (liftOp N (unitP (GB))) *ᵥ g') (ιu b0, i) =
      (covA c bb x₀ (liftOp N (unitP (GA))) *ᵥ g) (b0, i) := by
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hR1 : 2 * (ρ + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hR1' : 2 * (ρ + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1) := by
    omega
  have hx0' : InBox d ρ ((N₁' * L ^ m₁) * L ^ (k + 1)) (bm x0) := inBox_boxMap (by omega) hx0
  have hx0R := inBox_mono (Nat.le_add_right ρ (L ^ (k + 1))) hx0
  -- the fine sites of the unit points of the block
  have hrep := fun (b3 : unitPts (GA)) (h3 : unitBlock1 (b3 : UnitTorus d L N₁ m₁ k) =
      unitBlock1 (b0 : UnitTorus d L N₁ m₁ k)) =>
    unit_anchor (ϱ := ϱ) (by omega) hx0 b3 (h3.trans hb0)
  obtain ⟨y0, hy0, hy0x, hy0R⟩ := hrep b0 rfl
  have hιu0 := coe_ιu (N₁' := N₁') hR1 b0 hy0 hy0R
  have hblk0 : unitBlock1 (((ιu b0) : unitPts (GB)) : UnitTorus d L N₁' m₁ k) =
      jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bm x0) := by
    rw [hιu0, unitBlock1_unitBlock]
    exact (jBlock_boxMap_iff (m₁ := m₁) (j := k + 1) le_rfl hR1 hR1' hy0R hx0R).1 hy0x
  rw [covA_mulVec_eq, covA_mulVec_eq]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hg b0 rfl i, liftOp_mulVec, liftOp_mulVec]
  congr 1
  congr 1
  refine mulVec_apply_transport
    (fun b3 : unitPts (GA) => unitBlock1 (b3 : UnitTorus d L N₁ m₁ k) =
      unitBlock1 (b0 : UnitTorus d L N₁ m₁ k))
    (fun b3 : unitPts (GB) => unitBlock1 (b3 : UnitTorus d L N₁' m₁ k) =
      unitBlock1 (((ιu b0) : unitPts (GB)) : UnitTorus d L N₁' m₁ k))
    (fun b3 => ιu b3) (fun b3 b4 h3 h4 h => ?_) (fun b3 h3 => ?_) (fun b3' h3' => ?_) _ _ _ _
    (fun b3 h3 => ?_) (fun b3' h3' => ?_) (fun b3 h3 => ?_)
  · obtain ⟨y3, hy3, -, hy3R⟩ := hrep b3 h3
    obtain ⟨y4, hy4, -, hy4R⟩ := hrep b4 h4
    have e := congrArg Subtype.val h
    rw [coe_ιu (N₁' := N₁') hR1 b3 hy3 hy3R, coe_ιu (N₁' := N₁') hR1 b4 hy4 hy4R] at e
    have e2 := (jBlock_boxMap_iff (m₁ := m₁) (j := k) (Nat.le_succ k) hR1 hR1' hy3R hy4R).2 e
    exact Subtype.ext (hy3.symm.trans (e2.trans hy4))
  · obtain ⟨y3, hy3, hy3x, hy3R⟩ := hrep b3 h3
    show unitBlock1 (((ιu b3) : unitPts (GB)) : UnitTorus d L N₁' m₁ k) = _
    rw [coe_ιu (N₁' := N₁') hR1 b3 hy3 hy3R, unitBlock1_unitBlock, hblk0]
    exact (jBlock_boxMap_iff (m₁ := m₁) (j := k + 1) le_rfl hR1 hR1' hy3R hx0R).1 hy3x
  · obtain ⟨y3', hy3', hy3x', hy3R'⟩ := unit_anchor (ϱ := ϱ) (by omega) hx0' b3' (h3'.trans hblk0)
    have hback : bm (bm' y3') = y3' := boxMap_boxMap (by omega) hy3R'
    have hy3R : InBox d (ρ + L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) (bm' y3') :=
      inBox_boxMap (by omega) hy3R'
    have hx3 : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (bm' y3') =
        jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x0 := by
      refine (jBlock_boxMap_iff (m₁ := m₁) (j := k + 1) le_rfl hR1 hR1' hy3R hx0R).2 ?_
      rw [hback]; exact hy3x'
    refine ⟨⟨unitBlock (bm' y3'), mem_unitPts_levelTop _⟩, ?_, ?_⟩
    · show unitBlock1 (unitBlock (bm' y3')) = _
      rw [unitBlock1_unitBlock, hx3, ← hb0]
    · refine Subtype.ext ?_
      rw [coe_ιu (N₁' := N₁') hR1 ⟨unitBlock (bm' y3'), mem_unitPts_levelTop _⟩ rfl hy3R, hback]
      exact hy3'
  · simp only [unitP]
    rw [ite_eq_right (fun h => h3 h.symm), zero_mul]
  · simp only [unitP]
    rw [ite_eq_right (fun h => h3' h.symm), zero_mul]
  · have hm : unitBlock1 (((ιu b3) : unitPts (GB)) : UnitTorus d L N₁' m₁ k) =
        unitBlock1 (((ιu b0) : unitPts (GB)) : UnitTorus d L N₁' m₁ k) := by
      obtain ⟨y3, hy3, hy3x, hy3R⟩ := hrep b3 h3
      rw [coe_ιu (N₁' := N₁') hR1 b3 hy3 hy3R, unitBlock1_unitBlock, hblk0]
      exact (jBlock_boxMap_iff (m₁ := m₁) (j := k + 1) le_rfl hR1 hR1' hy3R hx0R).1 hy3x
    simp only [unitP]
    rw [ite_eq_left hm.symm, ite_eq_left h3.symm, hg b3 h3 i]

/-- **The rows of `Q g` on two tori** (`Q` the block average onto the unit lattice): at a unit
point `b₃` whose `(k+1)`-block is that of a site `x₀` of the box, the rows correspond if the inputs
correspond on the fine sites of `b₃`.  Margin: `2 ρ + 5 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` (and for
`N₁'`). -/
theorem unitQ_rows_transport {ρ : ℕ}
    (hn : 2 * ρ + 5 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 5 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {x0 : CTorus d L N₁ m₁ (k + 1)} (hx0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x0)
    {b3 : unitPts (GA)}
    (hb3 : unitBlock1 (b3 : UnitTorus d L N₁ m₁ k) = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x0)
    {u : (GA).Ω 1 × Fin N → ℂ} {u' : (GB).Ω 1 × Fin N → ℂ}
    (hu : ∀ y : (GA).Ω 1, unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = (b3 : UnitTorus d L N₁ m₁ k) →
      ∀ j, u' (ιb y, j) = u (y, j)) (j : Fin N) :
    (liftRect N (unitQ (GB)) *ᵥ u') (ιu b3, j) = (liftRect N (unitQ (GA)) *ᵥ u) (b3, j) := by
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hR1 : 2 * (ρ + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hR1' : 2 * (ρ + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1) := by
    omega
  have hx0' : InBox d ρ ((N₁' * L ^ m₁) * L ^ (k + 1)) (bm x0) := inBox_boxMap (by omega) hx0
  have hx0R := inBox_mono (Nat.le_add_right ρ (L ^ (k + 1))) hx0
  obtain ⟨y3, hy3, hy3x, hy3R⟩ := unit_anchor (ϱ := ϱ) (by omega) hx0 b3 hb3
  have hιu3 := coe_ιu (N₁' := N₁') hR1 b3 hy3 hy3R
  -- the fine sites of `b₃` lie in the box of radius `ρ + L^(k+1)`
  have hfib : ∀ y : CTorus d L N₁ m₁ (k + 1), unitBlock y = (b3 : UnitTorus d L N₁ m₁ k) →
      InBox d (ρ + L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) y := by
    intro y hy
    refine inBox_of_jBlock_eq le_rfl (by omega) hx0 ?_
    rw [← unitBlock1_unitBlock, hy, hb3]
  rw [liftRect_mulVec, liftRect_mulVec]
  simp only [Matrix.mulVec, dotProduct]
  refine sum_transport
    (fun y : (GA).Ω 1 => unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = (b3 : UnitTorus d L N₁ m₁ k))
    (fun y : (GB).Ω 1 => unitBlock (y : CTorus d L N₁' m₁ (k + 1)) =
      (((ιu b3) : unitPts (GB)) : UnitTorus d L N₁' m₁ k))
    (fun y => ιb y) (fun y1 y2 h1 h2 h => ?_) (fun y hy => ?_) (fun y' hy' => ?_) _ _
    (fun y hy => ?_) (fun y' hy' => ?_) (fun y hy => ?_)
  · exact Subtype.ext (boxMap_inj (hm' := (by omega : 2 * (ρ + L ^ (k + 1)) + 1 <
      (N₁' * L ^ m₁) * L ^ (k + 1))) (hfib _ h1) (hfib _ h2) (congrArg Subtype.val h))
  · show unitBlock (bm (y : CTorus d L N₁ m₁ (k + 1))) = _
    rw [hιu3]
    exact (jBlock_boxMap_iff (m₁ := m₁) (j := k) (Nat.le_succ k) hR1 hR1' (hfib _ hy) hy3R).1
      (hy.trans hy3.symm)
  · have hy'' : unitBlock (y' : CTorus d L N₁' m₁ (k + 1)) = unitBlock (bm y3) := hy'.trans hιu3
    have hblk : jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (y' : CTorus d L N₁' m₁ (k + 1)) =
        jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bm x0) := by
      rw [← unitBlock1_unitBlock, hy'', unitBlock1_unitBlock]
      exact (jBlock_boxMap_iff (m₁ := m₁) (j := k + 1) le_rfl hR1 hR1' hy3R hx0R).1 hy3x
    have hyR' := inBox_of_jBlock_eq (N₁ := N₁') le_rfl (by omega) hx0' hblk
    have hback : bm (bm' (y' : CTorus d L N₁' m₁ (k + 1))) = y' := boxMap_boxMap (by omega) hyR'
    have hyR : InBox d (ρ + L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
        (bm' (y' : CTorus d L N₁' m₁ (k + 1))) := inBox_boxMap (by omega) hyR'
    refine ⟨⟨bm' (y' : CTorus d L N₁' m₁ (k + 1)), levelGS_mem_Ω_one (Nat.le_add_left 1 k)
      le_rfl _⟩, ?_, Subtype.ext hback⟩
    show unitBlock (bm' (y' : CTorus d L N₁' m₁ (k + 1))) = _
    have e : unitBlock (bm (bm' (y' : CTorus d L N₁' m₁ (k + 1)))) = unitBlock (bm y3) := by
      rw [hback]; exact hy''
    exact ((jBlock_boxMap_iff (m₁ := m₁) (j := k) (Nat.le_succ k) hR1 hR1' hyR hy3R).2 e).trans hy3
  · simp only [unitQ]
    rw [ite_eq_right hy, zero_mul]
  · simp only [unitQ]
    rw [ite_eq_right hy', zero_mul]
  · have hm : unitBlock (bm (y : CTorus d L N₁ m₁ (k + 1))) =
        (((ιu b3) : unitPts (GB)) : UnitTorus d L N₁' m₁ k) := by
      rw [hιu3]
      exact (jBlock_boxMap_iff (m₁ := m₁) (j := k) (Nat.le_succ k) hR1 hR1' (hfib _ hy) hy3R).1
        (hy.trans hy3.symm)
    simp only [unitQ]
    rw [ite_eq_left hm, ite_eq_left hy, hu y hy j]

omit [NeZero N₁'] in
/-- `Q* v` at a site of the top level reads `v` at the unit point of the site only. -/
theorem unitQT_apply (v : unitPts (GA) × Fin N → ℂ) (y : (GA).Ω 1) (j : Fin N) :
    ((liftRect N (unitQ (GA)))ᵀ *ᵥ v) (y, j) =
      ((Real.sqrt ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹) : ℝ) : ℂ) *
        v (⟨unitBlock (y : CTorus d L N₁ m₁ (k + 1)), mem_unitPts_levelTop _⟩, j) := by
  rw [liftRect_transpose, liftRect_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [Finset.sum_eq_single (⟨unitBlock (y : CTorus d L N₁ m₁ (k + 1)), mem_unitPts_levelTop _⟩ :
    unitPts (GA))]
  · simp [unitQ]
  · intro b _ hb
    have : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ≠ (b : UnitTorus d L N₁ m₁ k) :=
      fun h => hb (Subtype.ext h.symm)
    simp [unitQ, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The rows of `Q* v` on two tori**: at a site `y` of the box, `Q* v` reads `v` at the unit
point of `y`. -/
theorem unitQT_rows_transport {ρ : ℕ}
    (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    {v : unitPts (GA) × Fin N → ℂ} {v' : unitPts (GB) × Fin N → ℂ} (y : (GA).Ω 1)
    (hyR : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) (y : CTorus d L N₁ m₁ (k + 1)))
    (hv : ∀ j, v' (ιu (⟨unitBlock (y : CTorus d L N₁ m₁ (k + 1)), mem_unitPts_levelTop _⟩ :
      unitPts (GA)), j) = v (⟨unitBlock (y : CTorus d L N₁ m₁ (k + 1)), mem_unitPts_levelTop _⟩, j))
    (j : Fin N) :
    ((liftRect N (unitQ (GB)))ᵀ *ᵥ v') (ιb y, j) = ((liftRect N (unitQ (GA)))ᵀ *ᵥ v) (y, j) := by
  rw [unitQT_apply, unitQT_apply, ← hv j]
  congr 3
  exact Subtype.ext (unitBlock_boxMap hn hyR)

end Unit

/-! ### D1: the decoupled covariance on two tori -/

section CovRows

open MeasureTheory Set

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "ιb" x:max => Subtype.mk (bm (x : CTorus d L N₁ m₁ (k + 1)))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) (ϱ := ϱ)
    (Nat.le_add_left 1 k) le_rfl _)
set_option hygiene false in
local notation "ιu" b:max => Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _)

/-- **D1: the decoupled covariance `C_x(s)` on two tori, at the unit points of a component.**  Let
`Y` be a union of components of the cut of the top level `levelGS (k + 1)` of the first torus and
`Y' = bm '' Y` its image, with `S_Y` going to `S_{Y'}` (`hB'`), the parameters vanishing on the
parameter cubes off `𝒞` (`hs0`, `hs0'`) and their cube products agreeing on the inner cubes of
`S_Y` (`hagree`), `Y` in the box of radius `R`.  If the multipliers correspond on `S_Y`, the fields
on `R(S_Y)` (`rowsCov_R`), and the inputs on the unit points whose `(k+1)`-block lies in `Y` or
meets `S_Y`, then `C_x(α, φ, s) h` and `C_x(α', φ', s') h'` correspond at every unit point whose
`(k+1)`-block lies in `Y`.  Margin: `4 R + 12 L^(k+1+m₁) + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` (and for
`N₁'`). -/
theorem decCov_rows_transport {a : ℕ → ℝ} {aT x₀ ν δ κ : ℝ}
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    {X₁' Y' : Finset (CTorus d L N₁' m₁ (k + 1))} {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ (k + 1))}
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (GA).Ω 1) Y)
    (hYc : IsNnComp ((Vset X₁' 𝒞').filter fun x => x ∈ (GB).Ω 1) Y')
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hs0 : ∀ P ∈ parCubes (GA) X₁, P ∉ 𝒞 → s P = 0)
    (hs0' : ∀ P ∈ parCubes (GB) X₁', P ∉ 𝒞' → s' P = 0)
    (hY' : Y.image bm = Y') (hB' : (SY (GA) X₁ 𝒞 Y).image bm = SY (GB) X₁' 𝒞' Y')
    (hagree : ∀ q ∈ innerCentres (GA) (SY (GA) X₁ 𝒞 Y),
      sProd (GB) s' (Prod.map id bm q) = sProd (GA) s q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y → α' (ιb x) = α x)
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hφR : ∀ u ∈ rowsCov_R (GA) a aT ν α X₁ 𝒞 Y, φ' (bm u) = φ u)
    (D : XData (GA) a aT ν x₀ α κ s) (D' : XData (GB) a aT ν x₀ α' κ s')
    (hφ : IsConstraintField (GA) δ φ) (hφ' : IsConstraintField (GB) δ φ') (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (h : unitPts (GA) × Fin N → ℂ) (h' : unitPts (GB) × Fin N → ℂ)
    (hh : ∀ b' : unitPts (GA), (UnitOut (GA) Y b' ∨ UnitIn (GA) X₁ 𝒞 Y b') → ∀ i,
      h' (ιu b', i) = h (b', i)) :
    ∀ b : unitPts (GA), UnitOut (GA) Y b → ∀ i : Fin N,
      (decCov (GB) a aT x₀ ν α' s' φ' (unitQ (GB)) (unitP (GB)) *ᵥ h') (ιu b, i) =
        (decCov (GA) a aT x₀ ν α s φ (unitQ (GA)) (unitP (GA)) *ᵥ h) (b, i) := by
  classical
  intro b hb i
  have SA := D.st
  have SB := D'.st
  have hx₀ := D.x0
  have hαA := D.pot
  have hαB := D'.pot
  have hU := D.isUnit_one_sub
  have hU' := D'.isUnit_one_sub
  have hM := decM_isUnit D hφ hδ hsm
  have hM' := decM_isUnit D' hφ' hδ hsm
  have hj1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hKm : L ^ (k + 1) ≤ L ^ (k + 1 + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_add_right _ _)
  have hnu : 2 * R + 5 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hnu' : 2 * R + 5 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hSYY := SY_subset_levelGS (ϱ := ϱ) (X₁ := X₁) (𝒞 := 𝒞) (Y := Y) hj1 le_rfl
  have hout : ∀ b3 : unitPts (GA), UnitOut (GA) Y b3 → ∃ x0 : CTorus d L N₁ m₁ (k + 1),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x0 ∧
        unitBlock1 (b3 : UnitTorus d L N₁ m₁ k) = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x0 := by
    intro b3 hb3
    obtain ⟨y, -, hy⟩ := (mem_unitPts _).1 b3.2
    have hyY : y ∈ Y := hb3 ⟨y, levelGS_mem_Ω_one hj1 le_rfl y⟩ (by rw [hy])
    exact ⟨y, hYR y hyY, by rw [← hy, unitBlock1_unitBlock]⟩
  have hbo : ∀ b3 : unitPts (GA), unitBlock1 (b3 : UnitTorus d L N₁ m₁ k) =
      unitBlock1 (b : UnitTorus d L N₁ m₁ k) → UnitOut (GA) Y b3 :=
    fun b3 h3 y hy => hb y (hy.trans h3)
  rw [decCov_mulVec_eq, decCov_mulVec_eq, Pi.add_apply, Pi.add_apply, Pi.smul_apply,
    Pi.smul_apply]
  obtain ⟨xb, hxbR, hxb⟩ := hout b hb
  have t0 := covA_unit_rows_transport (N := N) (a k) (aT / (L : ℝ) ^ 2) x₀ hnu hnu' hxbR hxb
    (g := h) (g' := h') (fun b3 h3 j => hh b3 (Or.inl (hbo b3 h3)) j) i
  have z1 : ∀ b2 : unitPts (GA), UnitIn (GA) X₁ 𝒞 Y b2 → ∀ j,
      (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP (GB))) *ᵥ h') (ιu b2, j) =
        (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP (GA))) *ᵥ h) (b2, j) := by
    rintro b2 ⟨y, hy, hyb⟩ j
    exact covA_unit_rows_transport (a k) (aT / (L : ℝ) ^ 2) x₀ hnu hnu' (hYR _ (hSYY hy))
      (hyb.symm.trans (unitBlock1_unitBlock _))
      (fun b3 h3 j' => hh b3 (Or.inr ⟨y, hy, hyb.trans h3.symm⟩) j') j
  have z2 : ∀ y : (GA).Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y → ∀ j,
      ((liftRect N (unitQ (GB)))ᵀ *ᵥ
        (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP (GB))) *ᵥ h')) (ιb y, j) =
      ((liftRect N (unitQ (GA)))ᵀ *ᵥ
        (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP (GA))) *ᵥ h)) (y, j) := by
    intro y hy j
    exact unitQT_rows_transport (ρ := R) (by omega) y (hYR _ (hSYY hy))
      (fun j' => z1 _ ⟨y, hy, rfl⟩ j') j
  have z3 := decZ_rows_transport SA SB hx₀ hconn hconn' hY hYc hs0 hs0' hY' hB' hagree hYR hn hn'
    hαA hαB hα hU hU' hφR hM hM' z2
  have z4 : ∀ b3 : unitPts (GA), UnitOut (GA) Y b3 → ∀ j,
      (liftRect N (unitQ (GB)) *ᵥ (decZ (GB) a aT x₀ ν α' s' φ' *ᵥ
        ((liftRect N (unitQ (GB)))ᵀ *ᵥ
          (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP (GB))) *ᵥ h')))) (ιu b3, j) =
      (liftRect N (unitQ (GA)) *ᵥ (decZ (GA) a aT x₀ ν α s φ *ᵥ
        ((liftRect N (unitQ (GA)))ᵀ *ᵥ
          (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP (GA))) *ᵥ h)))) (b3, j) := by
    intro b3 hb3 j
    obtain ⟨x3, hx3R, hx3⟩ := hout b3 hb3
    exact unitQ_rows_transport hnu hnu' hx3R hx3
      (fun y hy j' => z3 y (hb3 y (by rw [hy])) j') j
  have t1 := covA_unit_rows_transport (N := N) (a k) (aT / (L : ℝ) ^ 2) x₀ hnu hnu' hxbR hxb
    (fun b3 h3 j => z4 b3 (hbo b3 h3) j) i
  rw [t0, t1]

/-- At a unit point whose `(k+1)`-block avoids the core of `s`, `C_x(s) h = A_{k,x} h`: the
`Z`-term vanishes on the whole block (one torus). -/
theorem decCov_apply_of_free {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ}
    {aT x₀ ν : ℝ} {α : G.Ω 1 → ℂ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (b : unitPts G)
    (hb : ∀ y : G.Ω 1, unitBlock1 (unitBlock (y : CTorus d L N₁ m₁ (k + 1))) =
      unitBlock1 (b : UnitTorus d L N₁ m₁ k) → (y : CTorus d L N₁ m₁ (k + 1)) ∉ Core G s)
    (h : unitPts G × Fin N → ℂ) (i : Fin N) :
    (decCov G a aT x₀ ν α s φ (unitQ G) (unitP G) *ᵥ h) (b, i) =
      (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h) (b, i) := by
  classical
  rw [decCov_mulVec_eq, Pi.add_apply, Pi.smul_apply]
  have hbo : ∀ b3 : unitPts G, unitP G b b3 ≠ 0 → unitBlock1 (b : UnitTorus d L N₁ m₁ k) =
      unitBlock1 (b3 : UnitTorus d L N₁ m₁ k) := fun b3 hP => unitP_ne_zero_imp hP
  have hW : ∀ b3 : unitPts G, unitBlock1 (b : UnitTorus d L N₁ m₁ k) =
      unitBlock1 (b3 : UnitTorus d L N₁ m₁ k) → ∀ j,
      (liftRect N (unitQ G) *ᵥ (decZ G a aT x₀ ν α s φ *ᵥ ((liftRect N (unitQ G))ᵀ *ᵥ
        (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h)))) (b3, j) = 0 := by
    intro b3 hb3 j
    have e0 : (liftRect N (unitQ G) *ᵥ (0 : G.Ω 1 × Fin N → ℂ)) (b3, j) = 0 := by simp
    rw [← e0]
    refine mulVec_apply_congr _ _ _ _ ?_
    rintro ⟨y, j'⟩ hq
    obtain ⟨hj, hQ⟩ := liftRect_ne_zero_imp _ hq
    simp only at hj hQ
    subst hj
    exact decZ_apply_eq_zero _ (hb y (by rw [unitQ_ne_zero_imp hQ]; exact hb3.symm)) _
  have e1 := covA_apply_congr (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G))
    (liftRect N (unitQ G) *ᵥ (decZ G a aT x₀ ν α s φ *ᵥ ((liftRect N (unitQ G))ᵀ *ᵥ
      (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h)))) 0 (b, i)
    (by rw [hW b rfl i]; rfl) (by
      rintro ⟨b3, j⟩ hq
      obtain ⟨hj, hP⟩ := liftOp_ne_zero_imp _ hq
      simp only at hj hP
      subst hj
      rw [hW b3 (hbo b3 hP) _]; rfl)
  rw [e1]
  simp

/-- **D1, free branch.**  At a unit point `b` whose `(k+1)`-block avoids the core of `s` on the
first torus, and whose image avoids the core of `s'` on the second torus, `C_x(s) h` and
`C_x(s') h'` correspond as soon as the inputs correspond on the unit points of the block (no
agreement of the backgrounds is needed).  `x_b` is a site of the box of radius `R` in the block of
`b`.  Margin: `2 R + 5 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` (and for `N₁'`). -/
theorem decCov_rows_transport_free {a : ℕ → ℝ} {aT x₀ ν : ℝ} {α : (GA).Ω 1 → ℂ}
    {α' : (GB).Ω 1 → ℂ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ} {R : ℕ}
    (hnu : 2 * R + 5 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnu' : 2 * R + 5 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {b : unitPts (GA)} {xb : CTorus d L N₁ m₁ (k + 1)}
    (hxbR : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) xb)
    (hxb : unitBlock1 (b : UnitTorus d L N₁ m₁ k) = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) xb)
    (hfree : FreeBlk (GA) s s b) (hfree' : FreeBlk (GB) s' s' (ιu b))
    (h : unitPts (GA) × Fin N → ℂ) (h' : unitPts (GB) × Fin N → ℂ)
    (hh : ∀ b3 : unitPts (GA), unitBlock1 (b3 : UnitTorus d L N₁ m₁ k) =
      unitBlock1 (b : UnitTorus d L N₁ m₁ k) → ∀ i, h' (ιu b3, i) = h (b3, i)) (i : Fin N) :
    (decCov (GB) a aT x₀ ν α' s' φ' (unitQ (GB)) (unitP (GB)) *ᵥ h') (ιu b, i) =
      (decCov (GA) a aT x₀ ν α s φ (unitQ (GA)) (unitP (GA)) *ᵥ h) (b, i) := by
  rw [decCov_apply_of_free _ (fun y hy => (hfree' y hy).1),
    decCov_apply_of_free _ (fun y hy => (hfree y hy).1)]
  exact covA_unit_rows_transport _ _ _ hnu hnu' hxbR hxb hh i

/-! ### D2: the square root `C^{1/2}(s)` on two tori -/

/-- **D2: the decoupled square root on two tori** (two-torus form of `I4c_local_sqrt2_rows`).
Under the hypotheses of `decCov_rows_transport` for every `x ≥ 0` (the data `XData` at every
`x`), the rows of `C^{1/2}(s) h = π⁻¹ ∫₀^∞ x^{-1/2} C_x(s) h dx` correspond at every unit point
whose `(k+1)`-block lies in `Y`: the integrands correspond for every `x > 0`
(`decCov_rows_transport`), and the landed improper-integral formula (`intMat_mulVec_apply`, with
the landed integrability `integrable_decSqrtInt`) is the same on the two tori. -/
theorem decCovSqrt_rows_transport {a : ℕ → ℝ} {aT ν δ κ : ℝ}
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    {X₁' Y' : Finset (CTorus d L N₁' m₁ (k + 1))} {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ (k + 1))}
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (GA).Ω 1) Y)
    (hYc : IsNnComp ((Vset X₁' 𝒞').filter fun x => x ∈ (GB).Ω 1) Y')
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hs0 : ∀ P ∈ parCubes (GA) X₁, P ∉ 𝒞 → s P = 0)
    (hs0' : ∀ P ∈ parCubes (GB) X₁', P ∉ 𝒞' → s' P = 0)
    (hY' : Y.image bm = Y') (hB' : (SY (GA) X₁ 𝒞 Y).image bm = SY (GB) X₁' 𝒞' Y')
    (hagree : ∀ q ∈ innerCentres (GA) (SY (GA) X₁ 𝒞 Y),
      sProd (GB) s' (Prod.map id bm q) = sProd (GA) s q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y → α' (ιb x) = α x)
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hφR : ∀ u ∈ rowsCov_R (GA) a aT ν α X₁ 𝒞 Y, φ' (bm u) = φ u)
    (hfam : ∀ x, 0 ≤ x → XData (GA) a aT ν x α κ s)
    (hfam' : ∀ x, 0 ≤ x → XData (GB) a aT ν x α' κ s')
    (hφ : IsConstraintField (GA) δ φ) (hφ' : IsConstraintField (GB) δ φ') (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (h : unitPts (GA) × Fin N → ℂ) (h' : unitPts (GB) × Fin N → ℂ)
    (hh : ∀ b' : unitPts (GA), (UnitOut (GA) Y b' ∨ UnitIn (GA) X₁ 𝒞 Y b') → ∀ i,
      h' (ιu b', i) = h (b', i))
    {b : unitPts (GA)} (hb : UnitOut (GA) Y b) (i : Fin N) :
    (decCovSqrt (GB) a aT ν α' s' φ' (unitQ (GB)) (unitP (GB)) *ᵥ h') (ιu b, i) =
      (decCovSqrt (GA) a aT ν α s φ (unitQ (GA)) (unitP (GA)) *ᵥ h) (b, i) := by
  classical
  have Hs := (standing_pair hfam hφ hδ hsm).1
  have Hs' := (standing_pair hfam' hφ' hδ hsm).1
  have e1 := intMat_mulVec_apply (integrable_decSqrtInt Hs) h (b, i)
  have e2 := intMat_mulVec_apply (integrable_decSqrtInt Hs') h' (ιu b, i)
  have e3 : ∫ x in Ioi (0 : ℝ),
      (decSqrtInt (GB) a aT ν α' s' φ' (unitQ (GB)) (unitP (GB)) x *ᵥ h') (ιu b, i) =
      ∫ x in Ioi (0 : ℝ), (decSqrtInt (GA) a aT ν α s φ (unitQ (GA)) (unitP (GA)) x *ᵥ h) (b, i) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 ≤ x := (mem_Ioi.mp hx).le
    simp only [decSqrtInt, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
    rw [decCov_rows_transport hconn hconn' hY hYc hs0 hs0' hY' hB' hagree hYR hn hn' hα hφR
      (hfam x hx0) (hfam' x hx0) hφ hφ' hδ hsm h h' hh b hb i]
  simp only [decCovSqrt, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  rw [e1, e2, e3]

/-- **D2 under `CompleteBlocks`** (two-torus form of `I4c_local_sqrt_rows`): when every site of `Y`
has its whole `(k+1)`-block in `Y`, the inputs need only correspond on the unit points whose
`(k+1)`-block lies in `Y` (`unitOut_of_unitIn_or`). -/
theorem decCovSqrt_rows_transport_of_complete {a : ℕ → ℝ} {aT ν δ κ : ℝ}
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    {X₁' Y' : Finset (CTorus d L N₁' m₁ (k + 1))} {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ (k + 1))}
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (GA).Ω 1) Y)
    (hYc : IsNnComp ((Vset X₁' 𝒞').filter fun x => x ∈ (GB).Ω 1) Y')
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hs0 : ∀ P ∈ parCubes (GA) X₁, P ∉ 𝒞 → s P = 0)
    (hs0' : ∀ P ∈ parCubes (GB) X₁', P ∉ 𝒞' → s' P = 0)
    (hY' : Y.image bm = Y') (hB' : (SY (GA) X₁ 𝒞 Y).image bm = SY (GB) X₁' 𝒞' Y')
    (hagree : ∀ q ∈ innerCentres (GA) (SY (GA) X₁ 𝒞 Y),
      sProd (GB) s' (Prod.map id bm q) = sProd (GA) s q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y → α' (ιb x) = α x)
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hφR : ∀ u ∈ rowsCov_R (GA) a aT ν α X₁ 𝒞 Y, φ' (bm u) = φ u)
    (hfam : ∀ x, 0 ≤ x → XData (GA) a aT ν x α κ s)
    (hfam' : ∀ x, 0 ≤ x → XData (GB) a aT ν x α' κ s')
    (hφ : IsConstraintField (GA) δ φ) (hφ' : IsConstraintField (GB) δ φ') (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hcomp : CompleteBlocks (GA) Y)
    (h : unitPts (GA) × Fin N → ℂ) (h' : unitPts (GB) × Fin N → ℂ)
    (hh : ∀ b' : unitPts (GA), UnitOut (GA) Y b' → ∀ i, h' (ιu b', i) = h (b', i))
    {b : unitPts (GA)} (hb : UnitOut (GA) Y b) (i : Fin N) :
    (decCovSqrt (GB) a aT ν α' s' φ' (unitQ (GB)) (unitP (GB)) *ᵥ h') (ιu b, i) =
      (decCovSqrt (GA) a aT ν α s φ (unitQ (GA)) (unitP (GA)) *ᵥ h) (b, i) :=
  decCovSqrt_rows_transport hconn hconn' hY hYc hs0 hs0' hY' hB' hagree hYR hn hn' hα hφR hfam
    hfam' hφ hφ' hδ hsm h h' (fun b' hb' i' => hh b' (unitOut_of_unitIn_or hcomp hb') i') hb i

/-- **D2 with the free branch** (two-torus form of `I4c_local_sqrt3_rows`).  The output unit point
`b` either has its `(k+1)`-block in `Y` (then `decCovSqrt_rows_transport_of_complete` applies), or
its block avoids the core of `s` and the block of its image avoids the core of `s'` (`FreeBlk` on
each torus), with a site `x_b` of the block in the box of radius `R`; then only the inputs on the
unit points of the block are compared, and no agreement of the backgrounds is used. -/
theorem decCovSqrt_rows_transport3 {a : ℕ → ℝ} {aT ν δ κ : ℝ}
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    {X₁' Y' : Finset (CTorus d L N₁' m₁ (k + 1))} {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ (k + 1))}
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (GA).Ω 1) Y)
    (hYc : IsNnComp ((Vset X₁' 𝒞').filter fun x => x ∈ (GB).Ω 1) Y')
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hs0 : ∀ P ∈ parCubes (GA) X₁, P ∉ 𝒞 → s P = 0)
    (hs0' : ∀ P ∈ parCubes (GB) X₁', P ∉ 𝒞' → s' P = 0)
    (hY' : Y.image bm = Y') (hB' : (SY (GA) X₁ 𝒞 Y).image bm = SY (GB) X₁' 𝒞' Y')
    (hagree : ∀ q ∈ innerCentres (GA) (SY (GA) X₁ 𝒞 Y),
      sProd (GB) s' (Prod.map id bm q) = sProd (GA) s q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y → α' (ιb x) = α x)
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hφR : ∀ u ∈ rowsCov_R (GA) a aT ν α X₁ 𝒞 Y, φ' (bm u) = φ u)
    (hfam : ∀ x, 0 ≤ x → XData (GA) a aT ν x α κ s)
    (hfam' : ∀ x, 0 ≤ x → XData (GB) a aT ν x α' κ s')
    (hφ : IsConstraintField (GA) δ φ) (hφ' : IsConstraintField (GB) δ φ') (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hcomp : CompleteBlocks (GA) Y)
    (h : unitPts (GA) × Fin N → ℂ) (h' : unitPts (GB) × Fin N → ℂ) {b : unitPts (GA)}
    (hb : UnitOut (GA) Y b ∨ (FreeBlk (GA) s s b ∧ FreeBlk (GB) s' s' (ιu b) ∧
      ∃ xb : CTorus d L N₁ m₁ (k + 1), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) xb ∧
        unitBlock1 (b : UnitTorus d L N₁ m₁ k) = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) xb))
    (hh : ∀ b' : unitPts (GA), (UnitOut (GA) Y b' ∨
      unitBlock1 (b : UnitTorus d L N₁ m₁ k) = unitBlock1 (b' : UnitTorus d L N₁ m₁ k)) → ∀ i,
      h' (ιu b', i) = h (b', i))
    (i : Fin N) :
    (decCovSqrt (GB) a aT ν α' s' φ' (unitQ (GB)) (unitP (GB)) *ᵥ h') (ιu b, i) =
      (decCovSqrt (GA) a aT ν α s φ (unitQ (GA)) (unitP (GA)) *ᵥ h) (b, i) := by
  rcases hb with hb | ⟨hfree, hfree', xb, hxbR, hxb⟩
  · exact decCovSqrt_rows_transport_of_complete hconn hconn' hY hYc hs0 hs0' hY' hB' hagree hYR
      hn hn' hα hφR hfam hfam' hφ hφ' hδ hsm hcomp h h' (fun b' hb' => hh b' (Or.inl hb')) hb i
  · classical
    have hKm : L ^ (k + 1) ≤ L ^ (k + 1 + m₁) :=
      Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_add_right _ _)
    have Hs := (standing_pair hfam hφ hδ hsm).1
    have Hs' := (standing_pair hfam' hφ' hδ hsm).1
    have e1 := intMat_mulVec_apply (integrable_decSqrtInt Hs) h (b, i)
    have e2 := intMat_mulVec_apply (integrable_decSqrtInt Hs') h' (ιu b, i)
    have e3 : ∫ x in Ioi (0 : ℝ),
        (decSqrtInt (GB) a aT ν α' s' φ' (unitQ (GB)) (unitP (GB)) x *ᵥ h') (ιu b, i) =
        ∫ x in Ioi (0 : ℝ),
          (decSqrtInt (GA) a aT ν α s φ (unitQ (GA)) (unitP (GA)) x *ᵥ h) (b, i) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      simp only [decSqrtInt, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
      rw [decCov_rows_transport_free (R := R) (by omega) (by omega) hxbR hxb hfree hfree' h h'
        (fun b3 h3 j => hh b3 (Or.inr h3.symm) j) i]
    simp only [decCovSqrt, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
    rw [e1, e2, e3]

/-! ### D1 and D2 with the geometric inputs discharged -/

/-- **D1 with the geometric inputs discharged.**  `decCov_rows_transport` for the image sets
`X₁' = bm '' X₁`, `𝒞' = Prod.map id bm '' 𝒞`, `Y' = bm '' Y` of sets in the box of radius `R`: the
image of the block set is `SY_image` and the agreement of the cube products on the inner cubes of
`S_Y` is `hagree_boxMap` (both at the level `k + 1`), from parameters corresponding at the cubes of
the box of radius `R₁ = R + (3 L^(k+1+m₁) + 3 L^(k+3)) + L^(k+1+m₁)` (`hsP`).  Margins:
`4 R + 12 L^(k+1+m₁) + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` and
`2 R₁ + 5 L · cellSide L 0 m₁ (k+1) < N₁ L^m₁ L^(k+1)` (and for `N₁'`). -/
theorem decCov_rows_transport_of_box {a : ℕ → ℝ} {aT x₀ ν δ κ : ℝ}
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (GA).Ω 1) Y)
    (hYc : IsNnComp ((Vset (X₁.image bm) (𝒞.image (Prod.map id bm))).filter
      fun x => x ∈ (GB).Ω 1) (Y.image bm))
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hs0 : ∀ P ∈ parCubes (GA) X₁, P ∉ 𝒞 → s P = 0)
    (hs0' : ∀ P ∈ parCubes (GB) (X₁.image bm), P ∉ 𝒞.image (Prod.map id bm) → s' P = 0)
    {R : ℕ} (hXR : ∀ x ∈ X₁, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hCR : ∀ P ∈ 𝒞, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) P.2)
    (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hsP : ∀ P ∈ cubeIdx (GA),
      InBox d (R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁))
        ((N₁ * L ^ m₁) * L ^ (k + 1)) P.2 → s' (Prod.map id bm P) = s P)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y → α' (ιb x) = α x)
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hφR : ∀ u ∈ rowsCov_R (GA) a aT ν α X₁ 𝒞 Y, φ' (bm u) = φ u)
    (D : XData (GA) a aT ν x₀ α κ s) (D' : XData (GB) a aT ν x₀ α' κ s')
    (hφ : IsConstraintField (GA) δ φ) (hφ' : IsConstraintField (GB) δ φ') (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (h : unitPts (GA) × Fin N → ℂ) (h' : unitPts (GB) × Fin N → ℂ)
    (hh : ∀ b' : unitPts (GA), (UnitOut (GA) Y b' ∨ UnitIn (GA) X₁ 𝒞 Y b') → ∀ i,
      h' (ιu b', i) = h (b', i)) :
    ∀ b : unitPts (GA), UnitOut (GA) Y b → ∀ i : Fin N,
      (decCov (GB) a aT x₀ ν α' s' φ' (unitQ (GB)) (unitP (GB)) *ᵥ h') (ιu b, i) =
        (decCov (GA) a aT x₀ ν α s φ (unitQ (GA)) (unitP (GA)) *ᵥ h) (b, i) :=
  decCov_rows_transport hconn hconn' hY hYc hs0 hs0' rfl
    (SY_image (Nat.le_add_left 1 k) le_rfl hnS hnS' hXR hCR hYR)
    (hagree_boxMap (Nat.le_add_left 1 k) le_rfl hnS hnS'
      (SY_subset_levelGS (Nat.le_add_left 1 k) le_rfl) hYR hsP) hYR hn hn' hα hφR D D' hφ hφ' hδ
    hsm h h' hh

/-- **D2 with the geometric inputs discharged** (`decCovSqrt_rows_transport` for the image sets,
as in `decCov_rows_transport_of_box`). -/
theorem decCovSqrt_rows_transport_of_box {a : ℕ → ℝ} {aT ν δ κ : ℝ}
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (GA).Ω 1) Y)
    (hYc : IsNnComp ((Vset (X₁.image bm) (𝒞.image (Prod.map id bm))).filter
      fun x => x ∈ (GB).Ω 1) (Y.image bm))
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hs0 : ∀ P ∈ parCubes (GA) X₁, P ∉ 𝒞 → s P = 0)
    (hs0' : ∀ P ∈ parCubes (GB) (X₁.image bm), P ∉ 𝒞.image (Prod.map id bm) → s' P = 0)
    {R : ℕ} (hXR : ∀ x ∈ X₁, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hCR : ∀ P ∈ 𝒞, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) P.2)
    (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hsP : ∀ P ∈ cubeIdx (GA),
      InBox d (R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁))
        ((N₁ * L ^ m₁) * L ^ (k + 1)) P.2 → s' (Prod.map id bm P) = s P)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y → α' (ιb x) = α x)
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hφR : ∀ u ∈ rowsCov_R (GA) a aT ν α X₁ 𝒞 Y, φ' (bm u) = φ u)
    (hfam : ∀ x, 0 ≤ x → XData (GA) a aT ν x α κ s)
    (hfam' : ∀ x, 0 ≤ x → XData (GB) a aT ν x α' κ s')
    (hφ : IsConstraintField (GA) δ φ) (hφ' : IsConstraintField (GB) δ φ') (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (h : unitPts (GA) × Fin N → ℂ) (h' : unitPts (GB) × Fin N → ℂ)
    (hh : ∀ b' : unitPts (GA), (UnitOut (GA) Y b' ∨ UnitIn (GA) X₁ 𝒞 Y b') → ∀ i,
      h' (ιu b', i) = h (b', i))
    {b : unitPts (GA)} (hb : UnitOut (GA) Y b) (i : Fin N) :
    (decCovSqrt (GB) a aT ν α' s' φ' (unitQ (GB)) (unitP (GB)) *ᵥ h') (ιu b, i) =
      (decCovSqrt (GA) a aT ν α s φ (unitQ (GA)) (unitP (GA)) *ᵥ h) (b, i) :=
  decCovSqrt_rows_transport hconn hconn' hY hYc hs0 hs0' rfl
    (SY_image (Nat.le_add_left 1 k) le_rfl hnS hnS' hXR hCR hYR)
    (hagree_boxMap (Nat.le_add_left 1 k) le_rfl hnS hnS'
      (SY_subset_levelGS (Nat.le_add_left 1 k) le_rfl) hYR hsP) hYR hn hn' hα hφR hfam hfam' hφ hφ'
    hδ hsm h h' hh hb i

end CovRows

end Balaban.Polymer.TwoTorusStep
