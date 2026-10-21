/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.NewLevelDetBgClauses
public import Balaban.Fluctuation.ResDepTop
public import Balaban.Fluctuation.NewLevelTermsBgLocal

/-!
# Locality and covariance of the determinant part at the parameters of a local generating set

Route R-LOC, L5, the determinant half of the clauses (A3), (A4) of
`newLabels_castInputs_of_localFamily`: the determinant part `newLevelDetBg Gb … Zb θ T` of the
coefficient recomputed on a generating set `Gb`, at two parameters of the chart of `Gb`

* is the same when the raw data agree on `thickSet Gp (sitesOf T)` of the level set `Gp`, for a
  polymer `T` with the label margin in `Gb` (`newLevelDetBg_local_of_margin`: near the sites of `T`
  the residual reads of `Gb` are those of `Gp`, `resDep_eq_of_top`);
* is the same when the raw data of one are the rotation of those of the other
  (`newLevelDetBg_rot_param`, from `newLevelDetBg_rot`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.SmallField Finset Matrix

section Local

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱb ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The residual reads of `Gb` at a site with the label margin lie in the thickened set of the
level set**: for a site `x` of a set `Y` with `LabelMargin Gb Y`, `resDep Gb x = resDep Gp x`, whose
sites lie in `thickSet Gp Y`. -/
theorem resDep_mem_thickSet_of_labelMargin (Sd : DGSetting Gb (compWeight L a₁) ν)
    (hGp : IsLevel Gp (k + 1)) {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : LabelMargin Gb Y)
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ Y) {w : CTorus d L N₁ m₁ (k + 1)}
    (hw : w ∈ resDep Gb x) : w ∈ thickSet Gp Y := by
  have hlay := layer_near_of_labelMargin Sd hY (Y := {x}) (fun y hy => by
    rw [Finset.mem_singleton.1 hy]; exact hx) x (Finset.mem_singleton_self x)
  rw [resDep_eq_of_top hGp (Nat.le_add_left 1 k) hlay] at hw
  exact Or.inr ⟨x, hx, (hGp x).1, hw⟩

/-- **Locality of the determinant part at the parameters of `Gb`** (P3 p. 79 for the determinant;
the determinant half of (A3)): for a polymer `T` with the label margin in `Gb` and two parameters
of the chart `Ξ^c_{k+1}(Gb; 1, ε)` whose raw data agree on `thickSet Gp (sitesOf T)`, the
determinant parts are equal. -/
theorem newLevelDetBg_local_of_margin (hC : FlCore N Gb Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) {δc : ℝ} (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2) (hGp : IsLevel Gp (k + 1))
    (hN : L ^ 1 ∣ N₁) (Zb : Finset (unitPts Gb))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTm : LabelMargin Gb (sitesOf T)) {θ θ' : physParamBg N Gb}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps)
    (hag : agreeOn (thickSet Gp (sitesOf T)) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
      (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) :
    newLevelDetBg Gb (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Zb θ T =
      newLevelDetBg Gb (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Zb θ' T := by
  obtain ⟨D, hD, hθD⟩ := hθ
  obtain ⟨D₂, hD₂, hθD₂⟩ := hθ'
  rw [newLevelDetBg_of_eq Gb _ _ _ _ Zb hθD T, newLevelDetBg_of_eq Gb _ _ _ _ Zb hθD₂ T,
    ← newLevelDetBg_rawOf Gb _ _ _ _ Zb D θ.2 T, ← newLevelDetBg_rawOf Gb _ _ _ _ Zb D₂ θ'.2 T]
  refine newLevelDetBg_eq_of_agree hC hk hδc hcap hsm hmar hα hD hD₂ hN Zb θ.2 θ'.2 T
    fun x hx w hw => ?_
  have hwt := resDep_mem_thickSet_of_labelMargin hC.Sp hGp hTm hx hw
  obtain ⟨h1, h2⟩ := hag w hwt
  rw [hθD, hθD₂] at h1 h2
  exact ⟨h1, fun _ => h2⟩

/-- **Covariance of the determinant part at the parameters of `Gb`** (the determinant half of
(A4)): at a parameter of the chart of `Gb` and a parameter whose raw data are their rotation by
`R` (`Rᵀ R = 1`), the determinant parts are equal (any sources). -/
theorem newLevelDetBg_rot_param (hC : FlCore N Gb Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) {δc : ℝ} (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (Zb : Finset (unitPts Gb))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    {θ θ' : physParamBg N Gb}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps)
    (hrot : (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) =
      rotRaw R (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) :
    newLevelDetBg Gb (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Zb θ' T =
      newLevelDetBg Gb (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Zb θ T := by
  obtain ⟨D, hD, hθD⟩ := hθ
  have hθ'D : (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf (D.rot R) := by
    rw [hrot, hθD, rawOf_rot]
  rw [newLevelDetBg_of_eq Gb _ _ _ _ Zb hθ'D T, newLevelDetBg_of_eq Gb _ _ _ _ Zb hθD T,
    ← newLevelDetBg_rawOf Gb _ _ _ _ Zb (D.rot R) θ'.2 T,
    ← newLevelDetBg_rawOf Gb _ _ _ _ Zb D θ.2 T]
  exact newLevelDetBg_rot hC hk hδc hcap hsm hmar hα hD hR Zb θ.2 θ'.2 T

end Local

end Balaban.Fluctuation
