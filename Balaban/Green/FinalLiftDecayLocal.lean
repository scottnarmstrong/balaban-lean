/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLiftDecayTerm
public import Balaban.Green.FinalLiftDecayTube
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The variation of a term from the variation of the datum on a union of blocks (blocker 5)

Let `C`, `C'` be two data of the whole-level set `𝔹_j` (`Ξ^c_K(𝔹_j; 1, ε)`), with the same `h`, such that
`Ψ_{C'} - Ψ_C` is bounded by `M` on a union `B ⊇ X` of `L^j`-blocks.  Cutting the difference off outside
`B` gives a layer-constant direction `δΨ`; by locality of the term the value at `C'` is the value at
`C + δΨ`.  The complex line `C + t δΨ`, `|t| < ρ`, stays in the local chart (`xiDom_localB_tube`) as long
as `ρ N M ≤ δ₃`; the Cauchy estimate gives
`‖ℰ(C') - ℰ(C)‖ ≤ 2 E₀ e^{-κ d_j(X)} N M / δ₃` (`norm_E_sub_le_of_local_diff`).
-/

@[expose] public section

namespace Balaban.Green

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.Localization Balaban.LargeField
  Balaban.Fluctuation

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁]

/-- The only layer of the whole-level set `𝔹_j` is `j`. -/
theorem levelGS_layer_eq {j : ℕ} (hj : j ≤ K) {ϱ : ℝ} {n : ℕ} {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).layer n) :
    n = j := by
  rw [GeneratingSet.mem_layer] at hx
  simp only [levelGS] at hx
  by_cases h1 : n ≤ j
  · by_cases h2 : n + 1 ≤ j
    · simp [h1, h2] at hx
    · omega
  · simp [h1] at hx

/-- A function that is constant on the `L^j`-blocks and vanishes outside a union `B` of `L^j`-blocks
is layer-constant for the whole-level set `𝔹_j`. -/
theorem isLayerConstant_levelGS_cut {j : ℕ} (hj : j ≤ K) {ϱ : ℝ} {f : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hf : IsLayerConstant
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) f)
    {B : Set (CTorus d L N₁ m₁ K)}
    (hB : ∀ x x' : CTorus d L N₁ m₁ K, jBlock d L (N₁ * L ^ m₁) K j x = jBlock d L (N₁ * L ^ m₁) K j x' →
      (x ∈ B ↔ x' ∈ B)) (t : ℂ) :
    IsLayerConstant (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
      (fun x i => t * (open Classical in if x ∈ B then f x i else 0)) := by
  classical
  intro n hn1 hnk x hx x' hx'
  have hn := levelGS_layer_eq hj hx
  subst hn
  have h1 := hf n hn1 hnk x hx x' hx'
  have h2 : x' ∈ B ↔ x ∈ B := hB x' x (GeneratingSet.mem_blk.1 hx')
  funext i
  by_cases hxB : x ∈ B
  · have : x' ∈ B := h2.2 hxB
    simp [hxB, this, congrFun h1 i]
  · have : x' ∉ B := fun h => hxB (h2.1 h)
    simp [hxB, this]

/-- **The variation of a term from the variation of the datum on a union of blocks.**  See the module
docstring; `m = N M` bounds the norm of the cut-off direction and `δ₃` is the room of the tube. -/
theorem norm_E_sub_le_of_local_diff {ϱ : ℝ} {P : Consts} {A : ℕ → ℝ} {μ : ℝ} {εseq : ℕ → ℝ}
    {Tm : Terms d L N₁ m₁ K N ϱ}
    (hT : SFTermClauses P (xiFieldDom A μ εseq : FieldDom d L N₁ m₁ K N ϱ) Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K) {y : CTorus d L N₁ m₁ K} {X : Set (CTorus d L N₁ m₁ K)}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X) {hsep : ϱ ≤ minSep L (L ^ m₁)}
    (hgs : Tm.gs j X = localB j hj X hsep) (H : BgHyp d L K ϱ A μ) {ε δ₃ : ℝ}
    (hδ₃0 : 0 < δ₃) (hδ₃1 : δ₃ ≤ 1)
    (hsmall0 : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1)
    (hδ₂ : xiC1 d * ε + 5 * δ₃ ≤ bgC1 d L N) (hstar : δ₃ ≤ deltaStar d L N)
    (hK1s : bgK1 d L N * (xiC1 d * ε) ≤ deltaStar d L N)
    (hsm : bgK1 d L N * (xiC1 d * ε) + cK2 d L N * δ₃ < bgC0 d L N)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * (ε + xiK2 d L N * δ₃)) ≤ 1)
    (hc0 : xiC1 d * (ε + xiK2 d L N * δ₃) ≤ bgC0 d L N)
    (hc1 : xiC1 d * (ε + xiK2 d L N * δ₃) ≤ bgC1 d L N)
    (hεb : (2 * bgK1 d L N + 2) * (xiC1 d * (ε + xiK2 d L N * δ₃)) ≤ εseq j)
    {C C' : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) N}
    (hC : XiCData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
      A μ K 1 ε C)
    (hd : XiDom (localB j hj X hsep) A μ j (εseq j) C.Ψ C.h)
    (hd' : XiDom (localB j hj X hsep) A μ j (εseq j) C'.Ψ C'.h)
    (hh : ∀ x i, C'.h x i = C.h x i) {B : Set (CTorus d L N₁ m₁ K)}
    (hB : ∀ x x' : CTorus d L N₁ m₁ K, jBlock d L (N₁ * L ^ m₁) K j x =
      jBlock d L (N₁ * L ^ m₁) K j x' → (x ∈ B ↔ x' ∈ B)) (hXB : X ⊆ B) {M : ℝ}
    (hNM : 0 < (N : ℝ) * M) (hBM : ∀ x ∈ B, ∀ i, ‖C'.Ψ x i - C.Ψ x i‖ ≤ M) :
    ‖Tm.E j y X C'.Ψ C'.h - Tm.E j y X C.Ψ C.h‖ ≤
      2 * (P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X)) * ((N * M) / δ₃) := by
  classical
  set Bd := P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X) with hBd
  have hBd0 : 0 ≤ Bd := by
    have := hT.boundE j hj1 hj y X hX hy C.Ψ C.h (by rw [hgs]; exact hd)
    exact (norm_nonneg _).trans this
  by_cases hlt : (N : ℝ) * M < δ₃
  · set m := (N : ℝ) * M with hm
    set ρ := δ₃ / m with hρdef
    have hρ : 1 < ρ := (one_lt_div hNM).2 hlt
    set u : Fld d L N₁ m₁ K N := fun x i => if x ∈ B then C'.Ψ x i - C.Ψ x i else 0 with hu
    have hlc : IsLayerConstant (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ)
        j hj) (fun x i => C'.Ψ x i - C.Ψ x i) := by
      intro n hn1 hnk x hx x' hx'
      funext i
      simp [congrFun (C'.Ψ_layerConst n hn1 hnk x hx x' hx') i,
        congrFun (C.Ψ_layerConst n hn1 hnk x hx x' hx') i]
    have hcut : ∀ t : ℂ, IsLayerConstant (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := K) (ϱ := ϱ) j hj) (fun x i => t * u x i) := fun t =>
      isLayerConstant_levelGS_cut hj hlc hB t
    have hvu : ∀ x, vn (u x) ≤ m := by
      intro x
      by_cases hxB : x ∈ B
      · have : u x = fun i => C'.Ψ x i - C.Ψ x i := by funext i; simp [hu, hxB]
        rw [this]
        exact vn_le_card_mul (by nlinarith [hNM, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]) (hBM x hxB)
      · have : u x = 0 := by funext i; simp [hu, hxB]
        rw [this]
        have : vn (0 : Fin N → ℂ) = 0 := by simp [vn]
        rw [this]; exact hNM.le
    have hkey := norm_E_sub_le_of_line hT hj1 hj hX hy (Ψ := C.Ψ) (h := C.h) (Ψ' := C'.Ψ)
      (h' := C'.h) (u := u) (uh := 0) hρ (fun x hx => ⟨by funext i; simp [hu, hXB hx], by funext i; simpa using hh x i⟩)
      (fun t ht => by
        rw [hgs]
        have hm0 : 0 ≤ m := hNM.le
        have hvt : ∀ x ∈ dataSites (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
            (ϱ := ϱ) j hj), vn (fun i => t * u x i) ≤ δ₃ := by
          intro x _
          have e : (fun i => t * u x i) = t • u x := rfl
          rw [e, vn_smul]
          have h1 : ‖t‖ ≤ ρ := ht.le
          calc ‖t‖ * vn (u x) ≤ ρ * m :=
                mul_le_mul h1 (hvu x) (by simp [vn_nonneg]) (by positivity)
            _ = δ₃ := by rw [hρdef]; field_simp
        have := xiDom_localB_tube (X := X) (hsep := hsep) hj1 hj (a := A) (ν := μ) (εb := εseq j) H hδ₃0.le
          hδ₃1 hsmall0 hδ₂ hstar hK1s hsm hsmall hc0 hc1 hεb hC (hcut t) hvt
          (Ψ := C.Ψ + t • u) (h := C.h + t • 0) (fun x hx i => by
            have hxd : x ∈ dataSites (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
                (ϱ := ϱ) j hj) := (mem_dataSites _).2 (Or.inl (by simp [levelGS, hj1]))
            rw [perturbData_Ψ hxd]
            simp) (fun x _ i => by simp)
        exact this)
    refine hkey.trans (le_of_eq ?_)
    rw [hρdef, hBd]; field_simp
  · push Not at hlt
    have h1 := hT.boundE j hj1 hj y X hX hy C.Ψ C.h (by rw [hgs]; exact hd)
    have h2 := hT.boundE j hj1 hj y X hX hy C'.Ψ C'.h (by rw [hgs]; exact hd')
    calc ‖Tm.E j y X C'.Ψ C'.h - Tm.E j y X C.Ψ C.h‖ ≤ Bd + Bd :=
          (norm_sub_le _ _).trans (add_le_add h2 h1)
      _ = 2 * Bd * 1 := by ring
      _ ≤ 2 * Bd * ((N * M) / δ₃) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [le_div_iff₀ hδ₃0]; linarith

end Balaban.Green
