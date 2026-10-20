/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.NewLevelTermsBgAnalytic
public import Balaban.Fluctuation.MarkedVRawY
public import Balaban.Fluctuation.PhysicalReadsE
public import Balaban.Fluctuation.ClassOldLocalGk
public import Balaban.Localization.DecLogZero

/-!
# The marked terms recomputed on a background generating set: locality

P3 Lemma 4.2 at a background generating set `Gb`, (AE2): the sharp locality of the marked terms
`evDecBg` of the step's expansion recomputed on `Gb` with the canonical transport (ruling R8;
P3 pp. 78-79, (4.44)-(4.47)), for the labels `Y` with the margin `LabelMargin Gb Y` (every site
within sup-distance `2 L^{k+1+m₁}` of `Y` in the top layer `Ω_{k+1}(Gb)`).  The proof is the
row-local theory of the step (`fan_value_eq_of_component`) at the generating set `Gb`: the
connectedness of the thickened cubes and the footprint inclusions are asked only at the centres and
sites near the component, where `Gb` is in its top layer.

* `top_of_adm`, `hatConnAdm_of_top`, `hatBox_subset_Omega_of_top`: the admissible centres of a
  component inside the top layer are top centres; their thickened cubes are connected and lie in
  `Ω₁(Gb)`;
* `supDist_le_of_coordNear`, `layer_near_of_labelMargin`: the sites near a label with margin lie in
  the top layer;
* `markedHatPsiFBg_liftZ_mem_flBallLC_core`, `markedHatPsiFBg_liftZ_rows`: the marked local hat
  field of `Gb` lies in the fluctuation ball and agrees on a component from raw data on the
  component and hat variables on its unit blocks;
* `fanBg_canon_eq_of_family`: the functional of a term at two data agreeing on the component of a
  connected family whose sites have the margin;
* `evDecBg_canon_local_of`: the terms `evDecBg … Y (Θ, res ψ̂)` at two data with `AgHatDir Y`
  agree, for every label `Y` with the margin (the hypothesis `hloc` of the field lemmas of the
  marks at `Gg = Gb`, for a functional `Φ` with the agreement property of the row theorems).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.Polymer Balaban.LargeField Finset Matrix

section Geom

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱb : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb} {a : ℕ → ℝ} {ν : ℝ}

/-- The top region of a generating set is its top layer. -/
theorem mem_layer_top {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ Gb.Ω (k + 1)) :
    x ∈ Gb.layer (k + 1) :=
  Gb.mem_layer.2 ⟨hx, by simp [Gb.top]⟩

/-- A centre whose base lies in the top region is a centre of the top layer. -/
theorem top_of_base_mem {z : ℕ × CTorus d L N₁ m₁ (k + 1)} (hz : z ∈ cubeIdx Gb)
    (h : z.2 ∈ Gb.Ω (k + 1)) : z.1 = k + 1 := by
  obtain ⟨⟨h1, hK⟩, hl, -⟩ := (mem_cubeIdx Gb).1 hz
  by_contra hne
  exact Gb.layer_disjoint h1 hK (by omega) le_rfl hne hl (mem_layer_top h)

/-- **The admissible centres of a component in the top layer are top centres**: if `X₁` lies in the
top region of `Gb` and the marked cubes are cubes of the top layer, a centre `z` of `Gb` whose
parameter cubes lie in `𝒞` has layer `k + 1` (`z ∈ 𝒬(z)`: either `z` is a parameter cube, hence
marked, or its cube lies in `X₁`). -/
theorem top_of_adm {X₁ : Finset (CTorus d L N₁ m₁ (k + 1))}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} (hX₁ : ∀ x ∈ X₁, x ∈ Gb.Ω (k + 1))
    (h𝒞 : ∀ P ∈ 𝒞, P.1 = k + 1) {z : ℕ × CTorus d L N₁ m₁ (k + 1)} (hz : z ∈ cubeIdx Gb)
    (hP : ∀ P ∈ Qset Gb z, P ∈ parCubes Gb X₁ → P ∈ 𝒞) : z.1 = k + 1 := by
  classical
  by_cases hzP : z ∈ parCubes Gb X₁
  · exact h𝒞 z (hP z (self_mem_Qset_zeroCuts hz) hzP)
  · have hsub : cubeP z ⊆ X₁ := by
      by_contra hc
      exact hzP (Finset.mem_filter.2 ⟨hz, hc⟩)
    exact top_of_base_mem hz (hX₁ _ (hsub (mem_cubeP.2 (SameCell.refl _ _))))

/-- **Connectedness of the thickened cubes at the admissible centres of a component in the top
layer** (`HatConnAdm`): they are top centres, of layer `k + 1 ≥ 2` (`connIn_hatI_of_two_le`). -/
theorem hatConnAdm_of_top (S : DGSetting Gb a ν) (hk : 1 ≤ k)
    {X₁ : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hX₁ : ∀ x ∈ X₁, x ∈ Gb.Ω (k + 1)) (h𝒞 : ∀ P ∈ 𝒞, P.1 = k + 1) : HatConnAdm Gb X₁ 𝒞 :=
  fun z hz hP => connIn_hatI_of_two_le S hz (by rw [top_of_adm hX₁ h𝒞 hz hP]; omega)

/-- The thickened cubes of the centres of `Z_Y` of a component in the top layer lie in `Ω₁(Gb)`. -/
theorem hatBox_subset_Omega_of_top (S : DGSetting Gb a ν) (hk : 1 ≤ k)
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hX₁ : ∀ x ∈ X₁, x ∈ Gb.Ω (k + 1)) (h𝒞 : ∀ P ∈ 𝒞, P.1 = k + 1) :
    ∀ z ∈ ZY Gb X₁ 𝒞 Y, ∀ v ∈ hatBox z, v ∈ Gb.Ω 1 := by
  classical
  intro z hzZ v hv
  obtain ⟨hz, hP, -⟩ := Finset.mem_filter.1 hzZ
  exact hatBox_subset_Omega S hz (by rw [top_of_adm hX₁ h𝒞 hz hP]; omega) hv

/-- A lift distance `≤ r` in every coordinate bounds the sup distance by `r`. -/
theorem supDist_le_of_coordNear {x y : CTorus d L N₁ m₁ (k + 1)} {r : ℕ}
    (h : ∀ μ, CoordNear (N₁ * L ^ m₁ * L ^ (k + 1)) (r : ℝ) (y μ) (x μ)) : supDist x y ≤ r := by
  refine supDist_le_iff.2 fun μ => ?_
  have h1 := natAbs_cycRep_le_of_coordNear (h μ)
  have h2 : cycNorm _ (y μ - x μ) ≤ (Green.cycRep (y μ - x μ)).natAbs :=
    cycNorm_le_natAbs_cycRep _
  rw [cycNorm_sub_comm]
  have h3 : ((cycNorm _ (y μ - x μ) : ℕ) : ℝ) ≤ r :=
    (Nat.cast_le.2 h2).trans h1
  exact_mod_cast h3

/-- **The sites near a label with margin lie in the top layer**: for `Y ⊆ Yl` with
`LabelMargin Gb Yl`, every site within lift distance `3 L^{k+1}` of a site of `Y` lies in layer
`k + 1` of `Gb` (`3 L^{k+1} ≤ 2 L^{k+1+m₁}`). -/
theorem layer_near_of_labelMargin (S : DGSetting Gb a ν) {Yl : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYl : LabelMargin Gb Yl) {Y : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : ∀ x ∈ Y, x ∈ Yl) :
    ∀ x ∈ Y, ∀ y : CTorus d L N₁ m₁ (k + 1),
      (∀ μ, CoordNear (N₁ * L ^ m₁ * L ^ (k + 1)) (3 * (L : ℝ) ^ (k + 1)) (y μ) (x μ)) →
      y ∈ Gb.layer (k + 1) := by
  intro x hx y hy
  refine mem_layer_top (hYl x (hY x hx) y ?_)
  have hr : ((3 * L ^ (k + 1) : ℕ) : ℝ) = 3 * (L : ℝ) ^ (k + 1) := by push_cast; ring
  have h1 := supDist_le_of_coordNear (r := 3 * L ^ (k + 1)) (fun μ => by rw [hr]; exact hy μ)
  refine h1.trans ?_
  have hM : 4 * L ^ 2 ≤ L ^ m₁ := S.hM
  have hL : 1 ≤ L ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have h4 : 4 ≤ L ^ m₁ := le_trans (by omega) hM
  have e : L ^ (k + 1 + m₁) = L ^ (k + 1) * L ^ m₁ := pow_add _ _ _
  rw [e]
  calc 3 * L ^ (k + 1) ≤ 2 * (L ^ (k + 1) * 4) := by omega
    _ ≤ 2 * (L ^ (k + 1) * L ^ m₁) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h4)

/-- A cube of the level set `Gp` based in the top region of `Gb` is a centre of `Gb`. -/
theorem mem_cubeIdx_of_top (hG' : IsLevel Gp (k + 1)) {P : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hP : P ∈ cubeIdx Gp) (h2 : P.2 ∈ Gb.Ω (k + 1)) : P ∈ cubeIdx Gb := by
  have h1 : P.1 = k + 1 := level_eq_of_mem_cubeIdx hG' hP
  obtain ⟨-, -, hb⟩ := (mem_cubeIdx Gp).1 hP
  refine (mem_cubeIdx Gb).2 ⟨⟨by omega, by omega⟩, ?_, hb⟩
  rw [h1]
  exact mem_layer_top h2

/-- A centre of `Gb` of the top layer is a cube of the level set `Gp`. -/
theorem mem_cubeIdx_of_isLevel (hG' : IsLevel Gp (k + 1)) {P : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hP : P ∈ cubeIdx Gb) (h1 : P.1 = k + 1) : P ∈ cubeIdx Gp := by
  obtain ⟨hr, -, hb⟩ := (mem_cubeIdx Gb).1 hP
  refine (mem_cubeIdx Gp).2 ⟨hr, ?_, hb⟩
  rw [h1]
  exact hG'.mem_layer _

end Geom

section Params

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱb : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}

/-- **The transported parameters off the parameter cubes of `Gb`**: when `X₁` lies in the top region
of `Gb`, the transported parameters equal `1` on the cubes of `Gb` inside `X₁` (`extS` form). -/
theorem extS_canon_par_one (hG' : IsLevel Gp (k + 1)) {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hX₁top : ∀ x ∈ X₁f, x ∈ Gb.Ω (k + 1))
    (w : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) :
    ∀ P ∈ cubeIdx Gb, P ∉ parCubes Gb X₁f →
      extS Gb ((BgTransport.canon Gp Gb N).par
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w)) P = 1 := by
  intro P hP hPn
  unfold extS
  rw [dite_eq_left hP]
  exact tauExt_eq_one (Gl := Gb) hG' (fun x hx => hx) hX₁top w P hP hPn

/-- **The transported parameters vanish on the parameter cubes of `Gb` outside `𝒞`** when the
step's parameters vanish on the parameter cubes of `Gp` outside `𝒞`: a cube of `Gb` below the top
layer carries `0`; a top cube is a cube of `Gp` with the step's parameter. -/
theorem extS_canon_par_zero (hG' : IsLevel Gp (k + 1)) {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    {w : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ}
    (hs0 : ∀ P ∈ parCubes Gp X₁f, P ∉ 𝒞 →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w) P = 0) :
    ∀ P ∈ parCubes Gb X₁f, P ∉ 𝒞 →
      extS Gb ((BgTransport.canon Gp Gb N).par
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w)) P = 0 := by
  classical
  intro P hP hP𝒞
  obtain ⟨hPc, hPn⟩ := Finset.mem_filter.1 hP
  unfold extS
  rw [dite_eq_left hPc]
  show (if P.2 ∈ Gb.Ω (k + 1) then Dec2.extS (coverOf Gp)
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w) P else 0) = 0
  split_ifs with htop
  · have hPp : P ∈ cubeIdx Gp := mem_cubeIdx_of_isLevel hG' hPc (top_of_base_mem hPc htop)
    have h := hs0 P (Finset.mem_filter.2 ⟨hPp, hPn⟩) hP𝒞
    unfold extS at h
    rw [dite_eq_left hPp] at h
    unfold Dec2.extS
    rw [dite_eq_left (show P ∈ (coverOf Gp).cubeIdx from hPp)]
    exact h
  · rfl

end Params

section Hat

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱb ϱm : ℝ}
variable {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The marked local hat field of `Gb` lies in the local fluctuation ball** (from the standing
hypotheses `FlCore` of the pair `(Gb, H⁻)`, `H⁻` without layer `k + 1`): the coordinates of
`cc C^{1/2}(s) ψ̂` are bounded by `‖cc‖ K c_ψ` (`hatSqrtF_coord_le`) and the marks by
`‖u‖ + ‖t‖` (`localLiftMul_mem_flBallLC_of_coord`). -/
theorem markedHatPsiFBg_liftZ_mem_flBallLC_core
    (hC : FlCore N Gb Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) (hHm : Hm.Ω (k + 1) = ∅)
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gb) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ), IsDecBg Gb (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s : DecParams Gb} (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData Gb N}
    (hD : XiCData Gb (compWeight L a₁) ν (k + 1) 1 eps D) {ψh : unitPts Gb × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (Z : Finset (unitPts Gb)) {u t : ℂ}
    (hδ : (‖u‖ + ‖t‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁) :
    markedHatPsiFBg Gb a₁ ν (liftZ Gb) cc F₁ Z u t s (rawOf D) ψh ∈ FlBallLC Hm δ₁ := by
  have hmb : ∀ b : unitPts Gb, ‖u + (if b ∈ Z then t else 0)‖ ≤ ‖u‖ + ‖t‖ := by
    intro b
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  rw [markedHatPsiFBg_liftZ_eq (Gb := Gb) a₁ ν cc F₁ Z u t s (rawOf D) ψh]
  exact localLiftMul_mem_flBallLC_of_coord hHm hC.δ₁_pos
    (hatSqrtF_coord_le hC hk cc hcψ hMX hmar hα hsm hF₁ hs hD hψh)
    (fun b => u + if b ∈ Z then t else 0) hmb hδ

/-- **The marked local hat field of `Gb` on a component** (`MARK-ROWS` with the extension by zero, at
any generating set): from the hypotheses of `hatSqrtF_rows_of_bgAgree_adm` with the background
agreement supplied by `bgAgree_of_agree_on_component_adm` (raw data on `Y`), and the hat variables
agreeing on the unit blocks inside `Y`, the marked local hat fields agree at every site of `Y`. -/
theorem markedHatPsiFBg_liftZ_rows (hC : FlCore N Gb Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (cc : ℂ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gb) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ), IsDecBg Gb (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s s' : DecParams Gb} (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D D' : BgData Gb N} (hD : XiCData Gb (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gb (compWeight L a₁) ν (k + 1) 1 eps D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hconn : HatConnAdm Gb X₁ 𝒞)
    (hfoot : (∀ x ∈ SY Gb X₁ 𝒞 Y, resDep Gb x ⊆ Y) ∧
      (∀ x ∈ SY Gb X₁ 𝒞 Y, ∀ u ∈ resSites Gb x, approxDep Gb u ⊆ Y))
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gb.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx Gb, P ∉ parCubes Gb X₁ → extS Gb s P = 1 ∧ extS Gb s' P = 1)
    (hs0 : ∀ P ∈ parCubes Gb X₁, P ∉ 𝒞 → extS Gb s P = 0 ∧ extS Gb s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI Gb (cubeP P) Y → extS Gb s P = extS Gb s' P)
    (hcomp : CompleteBlocks Gb Y)
    (hdata : ∀ z ∈ Y, D.Ψ z = D'.Ψ z ∧ (z ∈ Gb.Ω 1 → D.h z = D'.h z))
    (ψh ψh' : unitPts Gb × Fin N → ℂ)
    (hh : ∀ b' : unitPts Gb, UnitOut Gb Y b' → ∀ i, ψh (b', i) = ψh' (b', i))
    (Z : Finset (unitPts Gb)) (u t : ℂ) :
    ∀ y ∈ Y,
      markedHatPsiFBg Gb a₁ ν (liftZ Gb) cc F₁ Z u t s (rawOf D) ψh y =
        markedHatPsiFBg Gb a₁ ν (liftZ Gb) cc F₁ Z u t s' (rawOf D') ψh' y := by
  classical
  intro y hy
  rw [markedHatPsiFBg_liftZ_eq (Gb := Gb) a₁ ν cc F₁ Z u t s (rawOf D) ψh,
    markedHatPsiFBg_liftZ_eq (Gb := Gb) a₁ ν cc F₁ Z u t s' (rawOf D') ψh']
  funext i
  by_cases hb : unitBlock y ∈ unitPts Gb
  · simp only [hb, dite_true]
    have hyΩ : y ∈ Gb.Ω 1 := (Finset.mem_filter.1 (hY.1 hy)).2
    have hout : UnitOut Gb Y ⟨unitBlock y, hb⟩ := fun y' hy' => hcomp ⟨y, hyΩ⟩ y' hy hy'
    have h := hatSqrtF_rows_of_bgAgree_adm hC hk hMX hmar hα hsm hF₁ hs hs' hD hD' hconn hY hs1
      hs0 hag hcomp (bgAgree_of_agree_on_component_adm hC hs hs' hD hD' hconn hfoot hY hs1 hs0 hag
        hdata) ψh ψh' hout hh i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h]
  · simp only [hb, dite_false]

end Hat

section Local

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱb ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The functional of a term recomputed on `Gb` at two data agreeing on the component of a
connected family** (P3 Lemma 4.2 at `Gb`, (AE2), one family).  Let `(F₁, Sol)` be a decoupling pair
of `(Gb, H⁻)` with its defining properties, `H⁻` without layer `k + 1` and covering the top region
of `Gb` (`hHmtop`), and let `Φ` have the agreement property of the row theorems at `Gb` (`hΦ`).
For a connected family `C` of the step's expansion with sites `Ysites C = Yl` and the margin
`LabelMargin Gb Yl`, two data `(Θ, ψ̂), (Θ', ψ̂')` of the chart of `Gb` with `AgHatDir Yl`, and the
parameters in `supN C (e^κ)`, the functional of the term with the canonical transport takes equal
values.  Proof: `fan_value_eq_of_component` at `Gb`, the geometry of the component in the top layer
of `Gb` supplying the localized hypotheses. -/
theorem fanBg_canon_eq_of_family (hC : FlCore N Gb Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG' : IsLevel Gp (k + 1)) (hHm : Hm.Ω (k + 1) = ∅)
    (hHmtop : ∀ y ∈ Gb.Ω (k + 1), y ∈ Hm.Ω 1)
    (hrow : RowInHat (coverOf Gb) Hm (compWeight L a₁) ν)
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gb) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ), IsDecBg Gb (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gb) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (Φ : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (hΦ : ∀ {φ φ' : Gb.Ω 1 × Fin N → ℂ} {α α' : Gb.Ω 1 → ℂ} {δφ δφ' : Hm.Ω 1 × Fin N → ℂ}
      {D D' : BgData Gb N} {ψ ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
      {Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))},
      (∀ x : Gb.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY Gb X₁f 𝒞 Y → α x = α' x) →
      (∀ y : Gb.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i,
        φ (y, i) - approxField Gb (compWeight L a₁) ν D.Ψ D.h y i =
          φ' (y, i) - approxField Gb (compWeight L a₁) ν D'.Ψ D'.h y i) →
      (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i, δφ (y, i) = δφ' (y, i)) →
      (∀ y ∈ Y, ψ y = ψ' y) →
      (∀ z ∈ Y, D.Ψ z = D'.Ψ z ∧ (z ∈ Gb.Ω 1 → D.h z = D'.h z)) →
      (∀ x ∈ X₁f, x ∈ Y) →
      Φ (φ, α) δφ (rawOf D, ψ) = Φ (φ', α') δφ' (rawOf D', ψ'))
    (Zb : Finset (unitPts Gb)) {um tm : ℂ}
    (hW : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    {Yl : Set (CTorus d L N₁ m₁ (k + 1))} (hYl : LabelMargin Gb Yl)
    {C : Finset (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))}
    (hCm : C ∈ connFams (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
      (X1 Gp m₀ j 𝒦X) Yl)
    {u u' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
      {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
    (hu' : u' ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
      {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
    (hAg : AgHatDir hG' Yl u u')
    {w : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ} (hw : w ∈ supN C (Real.exp κ)) :
    FFmarkedBg Gp X₁f Gb a₁ ν (BgTransport.canon Gp Gb N) cc F₁ Sol Φ Zb um tm
        (u.1, (BgTransport.canon Gp Gb N).res u.2) w =
      FFmarkedBg Gp X₁f Gb a₁ ν (BgTransport.canon Gp Gb N) cc F₁ Sol Φ Zb um tm
        (u'.1, (BgTransport.canon Gp Gb N).res u'.2) w := by
  classical
  obtain ⟨Θ, ψh⟩ := u
  obtain ⟨Θ', ψh₂⟩ := u'
  obtain ⟨⟨D, hD, rfl⟩, hψh⟩ := hu
  obtain ⟨⟨D', hD', rfl⟩, hψh₂⟩ := hu'
  obtain ⟨hAgΘ, hAgψ⟩ := hAg
  obtain ⟨hCc, hCY⟩ := (mem_connFams _).1 hCm
  set cmap : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℕ × CTorus d L N₁ m₁ (k + 1) :=
    fun i => i.1.1 with hcc
  have hcc_mem : ∀ i, cmap i ∈ cubeIdx Gp := fun i => i.1.2
  have e2 : compY cmap (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = compY cmap (X1 Gp m₀ j 𝒦X) :=
    congrArg (fun S => compY cmap S) hX₁
  -- the component and its place in the top layer of `Gb`
  set Yc : Set (CTorus d L N₁ m₁ (k + 1)) := compY cmap (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C
    with hYc
  set Y : Finset (CTorus d L N₁ m₁ (k + 1)) := Finset.univ.filter (· ∈ Yc) with hY
  set 𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1)) := C.image cmap with h𝒞
  have hmemY : ∀ x, x ∈ Y ↔ x ∈ Yc := fun x => by simp [hY]
  have hYcYl : Yc ⊆ Yl := by
    rw [← hCY, hYc, e2]
    exact compY_subset_Ysites hcov.hU hcov.hN hcc_mem _ C
  have hYYl : ∀ x ∈ Y, x ∈ Yl := fun x hx => hYcYl ((hmemY x).1 hx)
  have hYtop : ∀ y ∈ Y, y ∈ Gb.Ω (k + 1) := fun y hy => hYl.subset y (hYYl y hy)
  have hXY : ∀ x ∈ X₁f, x ∈ Y := fun x hx => (hmemY x).2 (subset_compY
    (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C (Finset.mem_coe.2 hx))
  have hX₁top : ∀ x ∈ X₁f, x ∈ Gb.Ω (k + 1) := fun x hx => hYtop x (hXY x hx)
  have h𝒞top : ∀ P ∈ 𝒞, P.1 = k + 1 := by
    intro P hP
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hP
    exact level_eq_of_mem_cubeIdx hG' (hcc_mem i)
  have h𝒞Gb : ∀ P ∈ 𝒞, P ∈ cubeIdx Gb := by
    intro P hP
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP
    have hsub : Pset m₁ (cmap i) ⊆ Yc := by
      have := hCc i hi
      rw [← e2] at this
      exact this
    exact mem_cubeIdx_of_top hG' (hcc_mem i)
      (hYtop _ ((hmemY _).2 (hsub (self_mem_Pset (cmap i)))))
  -- the parameters
  have hw0 : ∀ i ∉ C, w i = 0 := fun i hi => hw.1 i hi
  obtain ⟨hYnnP, -, hs0P, -⟩ := compY_geometry hcov hX₁ C w w hw0 hw0 (fun _ _ _ => rfl) Y hmemY
  set σ : DecParams Gb := (BgTransport.canon Gp Gb N).par
    (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w) with hσ
  have hwp : w ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
      (fun _ => Real.exp κ) := fun i => by simpa using hw.2 i
  have hσκ : ∀ P, ‖σ P‖ < Real.exp κ :=
    tauExt_norm_lt (Gl := Gb) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) hC.hκ w hwp
  have hσ1 : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ cubeIdx Gb),
      P ∉ parCubes Gb X₁f → σ ⟨P, hP⟩ = 1 :=
    tauExt_eq_one (Gl := Gb) hG' (fun x hx => hx) hX₁top w
  have hs1E : ∀ P ∈ cubeIdx Gb, P ∉ parCubes Gb X₁f → extS Gb σ P = 1 ∧ extS Gb σ P = 1 :=
    fun P hP hPn => ⟨extS_canon_par_one hG' hX₁top w P hP hPn,
      extS_canon_par_one hG' hX₁top w P hP hPn⟩
  have hs0E : ∀ P ∈ parCubes Gb X₁f, P ∉ 𝒞 → extS Gb σ P = 0 ∧ extS Gb σ P = 0 :=
    fun P hP hP𝒞 => ⟨extS_canon_par_zero hG' (fun P hP hP𝒞 => (hs0P P hP hP𝒞).1) P hP hP𝒞,
      extS_canon_par_zero hG' (fun P hP hP𝒞 => (hs0P P hP hP𝒞).1) P hP hP𝒞⟩
  have hagE : ∀ P ∈ 𝒞, SubI Gb (cubeP P) Y → extS Gb σ P = extS Gb σ P := fun _ _ _ => rfl
  have hYnn : IsNnComp ((Vset X₁f 𝒞).filter fun x => x ∈ Gb.Ω 1) Y := by
    refine ⟨fun x hx => Finset.mem_filter.2 ⟨(Finset.mem_filter.1 (hYnnP.1 hx)).1,
      Gb.Ω_antitone le_rfl (by omega) (by omega) (hYtop x hx)⟩, fun x hx y hy hadj => ?_⟩
    refine hYnnP.2 x hx y (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hy).1, ?_⟩) hadj
    rw [hG'.Ω_one]; exact Finset.mem_univ _
  -- the localized hypotheses of the row theorems at `Gb`
  have hconn : HatConnAdm Gb X₁f 𝒞 := hatConnAdm_of_top hC.Sp hk hX₁top h𝒞top
  have hhat := hatBox_subset_Omega_of_top hC.Sp hk (Y := Y) hX₁top h𝒞top
  have hlay := layer_near_of_labelMargin hC.Sp hYl hYYl
  have hfoot := footprint_subset_component_of (G := Gb) (n := k + 1) (by omega) le_rfl X₁f 𝒞 Y
    hhat hlay
  have hSYF : ∀ x ∈ Dec2.SYF (coverOf Gb) Hm (compWeight L a₁) ν X₁f 𝒞 Y, x ∈ SY Gb X₁f 𝒞 Y :=
    fun x hx => SYF_subset_SY_adm (Dec2.coverLocal_self hC.Sp) (fun y hy => hC.hPmp.mem_Ω1 hy)
      hconn hYnn hx
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hfootF : ∀ u ∈ Dec2.SYF (coverOf Gb) Hm (compWeight L a₁) ν X₁f 𝒞 Y,
      ∀ w ∈ resSites Hm u, approxDep Gb w ⊆ Y := by
    intro u hu w hw'
    refine approxDep_subset_component_of_near (n := k + 1) (by omega) le_rfl hhat hlay (hSYF u hu)
      fun μ => ?_
    exact (resSites_coord_bound_of (layerIndex_le_top Hm u) rfl hw' μ).mono
      (pow_le_pow_right₀ hL1 (layerIndex_le_top Hm u))
  have hcolY : ∀ y ∈ collar Hm, (∃ x : Hm.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈
      Dec2.SYF (coverOf Gb) Hm (compWeight L a₁) ν X₁f 𝒞 Y ∧
        Adj (x : CTorus d L N₁ m₁ (k + 1)) y) → y ∈ Y := by
    rintro y hy ⟨x, hx, hadj⟩
    exfalso
    have hxY := mem_of_mem_SY hhat (hSYF _ hx)
    have hyTop : y ∈ Gb.Ω (k + 1) := hYl x (hYYl _ hxY) y
      ((Adj.supDist_le_one hadj).trans
        (Nat.mul_pos (by norm_num) (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)))
    exact ((mem_collar Hm).1 hy).1 (hHmtop y hyTop)
  -- the data and the hat variables
  have hdataY : ∀ z ∈ Y, D.Ψ z = D'.Ψ z ∧ (z ∈ Gb.Ω 1 → D.h z = D'.h z) := fun z hz => by
    have := hAgΘ z (Or.inl (hYYl z hz))
    exact ⟨this.1, fun _ => this.2⟩
  have hX1cell : IsCellUnion (L ^ (k + 1 + m₁)) (X1 Gp m₀ j 𝒦X) :=
    (X1_isCellUnion (G := Gp) (j := j) (𝒦X := 𝒦X) hcov.hN).mono_dvd (pow_dvd_pow L (by omega))
  have hYcell : IsCellUnion (L ^ (k + 1)) (Y : Set (CTorus d L N₁ m₁ (k + 1))) := by
    have h := compY_isCellUnion (c := cmap) hX1cell (C := C)
      (fun i _ => level_eq_of_mem_cubeIdx hG' (hcc_mem i))
    rw [← e2] at h
    have hYeq : (Y : Set (CTorus d L N₁ m₁ (k + 1))) = Yc := by
      ext x; simp [hY]
    rw [hYeq]
    exact h.mono_dvd (pow_dvd_pow L (by omega))
  have hcomp : CompleteBlocks Gb Y := completeBlocks_of_cellUnion hYcell
  have hh : ∀ b : unitPts Gb, UnitOut Gb Y b → ∀ i,
      resZ (N := N) Gp Gb ψh (b, i) = resZ (N := N) Gp Gb ψh₂ (b, i) := by
    intro b hb i
    obtain ⟨x, hxl, hxb⟩ := (mem_unitPts Gb).1 b.2
    have hxΩ : x ∈ Gb.Ω 1 := Gb.layer_subset (by omega) le_rfl hxl
    have hxY : x ∈ Y := hb ⟨x, hxΩ⟩ (by simp only [hxb])
    have key : ∀ p : unitPts Gp, p.1 = unitBlock x → ψh (p, i) = ψh₂ (p, i) := by
      intro p hp
      have hpx : p = unitPt hG' x := Subtype.ext hp
      rw [hpx]
      exact hAgψ x (hYYl x hxY) i
    rw [resZ_apply, resZ_apply]
    simp only [dite_eq_left (mem_unitPts_of_isLevel hG' b.1)]
    exact key _ hxb.symm
  have hψY := markedHatPsiFBg_liftZ_rows hC hk cc hMX hdm hα hsm hF₁ hσκ hσκ hD hD' hconn hfoot
    hYnn hs1E hs0E hagE hcomp hdataY _ _ hh Zb um tm
  have hψ := (markedHatPsiFBg_liftZ_mem_flBallLC_core hC hk hHm cc hcψ hMX hdm hα hsm hF₁ hσκ hD
    (ψh := resZ (N := N) Gp Gb ψh) (fun q => by
      rw [resZ_apply]; split_ifs
      · exact hψh _
      · rw [norm_zero]; exact hcψ) Zb hW).1
  have hψ' := (markedHatPsiFBg_liftZ_mem_flBallLC_core hC hk hHm cc hcψ hMX hdm hα hsm hF₁ hσκ hD'
    (ψh := resZ (N := N) Gp Gb ψh₂) (fun q => by
      rw [resZ_apply]; split_ifs
      · exact hψh₂ _
      · rw [norm_zero]; exact hcψ) Zb hW).1
  -- the term
  have hcl : clipRawL Gb (rawOf D) = rawOf D := clipRaw_of_mem_rawSub Gb (rawOf_mem_rawSub D)
  have hcl' : clipRawL Gb (rawOf D') = rawOf D' := clipRaw_of_mem_rawSub Gb (rawOf_mem_rawSub D')
  have e1 := FFmarkedBg_canon_apply X₁f Gb a₁ ν cc F₁ Sol Φ Zb um tm (rawOf D, ψh) w
  have e2 := FFmarkedBg_canon_apply X₁f Gb a₁ ν cc F₁ Sol Φ Zb um tm (rawOf D', ψh₂) w
  dsimp only at e1 e2 ⊢
  rw [hcl] at e1
  rw [hcl'] at e2
  rw [e1, e2]
  exact fan_value_eq_of_component hC hrow hF₁ hSol Φ hΦ hσκ hσκ hσ1 hσ1 hD hD' hψ hψ' hconn hfoot
    hfootF hYnn hs1E hs0E hagE h𝒞Gb hdataY hψY hcolY hXY

/-- **(AE2) of Lemma 4.2 at a background generating set: the sharp locality of the recomputed
terms** (P3 pp. 78-79, (4.44)-(4.47)).  Under the hypotheses of `fanBg_canon_eq_of_family`, for every
label `Y` with the margin `LabelMargin Gb Y`, the terms `evDecBg … Y (Θ, res ψ̂)` of the canonical
transport take equal values at two data of the chart of `Gb` with `AgHatDir Y` (raw data agreeing
on `thickSet Y`, hat variables at the unit points of `Y`).  This is the hypothesis `hloc` of the
field lemmas of the marks at `Gg = Gb` (`deriv_evDecBg_hatOf_fields_gen`, `decMarkGBg_dep_gen`)
for a functional with the agreement property of the row theorems. -/
theorem evDecBg_canon_local_of (hC : FlCore N Gb Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG' : IsLevel Gp (k + 1)) (hHm : Hm.Ω (k + 1) = ∅)
    (hHmtop : ∀ y ∈ Gb.Ω (k + 1), y ∈ Hm.Ω 1)
    (hrow : RowInHat (coverOf Gb) Hm (compWeight L a₁) ν)
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gb) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ), IsDecBg Gb (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gb) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (Φ : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (hΦ : ∀ {φ φ' : Gb.Ω 1 × Fin N → ℂ} {α α' : Gb.Ω 1 → ℂ} {δφ δφ' : Hm.Ω 1 × Fin N → ℂ}
      {D D' : BgData Gb N} {ψ ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
      {Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))},
      (∀ x : Gb.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY Gb X₁f 𝒞 Y → α x = α' x) →
      (∀ y : Gb.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i,
        φ (y, i) - approxField Gb (compWeight L a₁) ν D.Ψ D.h y i =
          φ' (y, i) - approxField Gb (compWeight L a₁) ν D'.Ψ D'.h y i) →
      (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i, δφ (y, i) = δφ' (y, i)) →
      (∀ y ∈ Y, ψ y = ψ' y) →
      (∀ z ∈ Y, D.Ψ z = D'.Ψ z ∧ (z ∈ Gb.Ω 1 → D.h z = D'.h z)) →
      (∀ x ∈ X₁f, x ∈ Y) →
      Φ (φ, α) δφ (rawOf D, ψ) = Φ (φ', α') δφ' (rawOf D', ψ'))
    (Zb : Finset (unitPts Gb)) :
    ∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Y, LabelMargin Gb Y → ∀ u ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir hG' Y u u' →
        evDecBg Gp X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon Gp Gb N) cc F₁ Sol Φ Zb um tm Y
            (u.1, (BgTransport.canon Gp Gb N).res u.2) =
          evDecBg Gp X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon Gp Gb N) cc F₁ Sol Φ Zb um tm Y
            (u'.1, (BgTransport.canon Gp Gb N).res u'.2) := by
  intro um tm hW Y hYm u hu u' hu' hAg
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  unfold evDecBg evTerm
  refine Finset.sum_congr rfl fun C hC' => ?_
  exact coef_congr_near hE1 fun w hw => fanBg_canon_eq_of_family hC hk hG' hHm hHmtop hrow cc hcψ
    hMX hdm hα hsm hcov hX₁ hF₁ hSol Φ hΦ Zb hW hYm hC' hu hu' hAg hw

end Local

end Balaban.Localization
