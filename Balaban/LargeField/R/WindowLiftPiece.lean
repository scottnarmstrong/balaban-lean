/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowLiftDatum

/-!
# The datum of a piece is the lift of the window configuration

P7 p. 501 (2.14) with P6 p. 7 (2.16).  For a piece `(j, c)` of the window of a ripe component
`Z`, the datum `locData` at the output `ancOut c P (ρ x)` and the new variables `ρ x` restricted to
`c`, read at a data site of the local generating set, is the field `ψ` of the window configuration
`(o, x)` at the blocks of the site: `ψ_{j+1}` on the `(j+1)`-block of a site over `Ω` of the step
`j`, `ψ_j` on its `j`-block otherwise.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory Balaban.Background

section Piece

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {N : ℕ}

/-- The `(j+1)`-block of a data site of the piece `c` lies in the output set `V_c`. -/
theorem block_mem_Vblk_of_dataSite (g : Geo S n R M) {m' j : ℕ} (hmK : m' + 1 ≤ K) (hj : j ≤ m')
    (c : H.Comp (j + 1)) (hK : j + 1 ≤ K) {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hy : torusCast (piece_torus_eq g H.F.hnn hmK hj) y ∈
      dataSites (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK)) :
    torusCast (blk_eq_top H.F.hnn hmK (Nat.succ_le_succ hj))
        (jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (j + 1) y) ∈
      Vblk R (H.localHistory M K (j + 1) c) (j + 1) := by
  obtain ⟨v, hv, hd⟩ := cube_near_piece g hmK hj c hK hy
  have hx0 : jBlock S.d S.L (M * n K) K (j + 1) (torusCast (fine_eq_top H.F.hnn hmK).symm y) =
      torusCast (blk_eq_top H.F.hnn hmK (Nat.succ_le_succ hj))
        (jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (j + 1) y) :=
    jBlock_torusCast (Nat.succ_le_succ hj) hK (fine_eq_top H.F.hnn hmK).symm _ y
  show blockCube S n M K (j + 1) _ ∈ Vcubes R (H.localHistory M K (j + 1) c) (j + 1)
  rw [← hx0, blockCube_castSite H.F.hnn hmK hK y]
  unfold Vcubes
  simp only [Nat.add_sub_cancel]
  obtain ⟨w, hw1, hw2⟩ := exists_split (x := cubeMap n S.L M (m' + 1) (j + 1) y) (z := v)
    (a := 1) (b := ⌊R j⌋₊ + 1) (by omega)
  exact mem_nbhd.mpr ⟨w, mem_nbhd.mpr ⟨v, Zcubes_loc_top hK c hv, hw2⟩, hw1⟩

section Lift

variable (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
/-- **The top piece reads the window configuration.**  The datum of the piece `(m', Z)` at the output
`o` and the new variables of `x` is the lift of `ψ` at the data sites of its local generating set,
`ψ_{m'+1} = o`, `ψ_{m'}` = the variables of `x`. -/
theorem hlift_top {m' : ℕ} (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)} (hnk : ¬ IsKept H (m' + 1) Z)
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (hv : EuclideanSpace ℝ (Fin N))
    (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hψ1 : ∀ b, ψ ⟨m' + 1, b⟩ = outField N o (torusCast (blk_eq_top H.F.hnn hm le_rfl) b))
    (hψ0 : ∀ i (hi : i ≤ m') b, ψ ⟨i, b⟩ =
      subVarField N x i (torusCast (blk_eq_top H.F.hnn hm (hi.trans (Nat.le_succ _))) b))
    {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hy : torusCast (piece_torus_eq geo H.F.hnn hm (le_refl m')) y ∈
      dataSites (locGen geo (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hm Z) hm)) :
    (locData geo (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hm Z) hm o
        (newRestrict (H.localHistory M K (m' + 1) Z)
          (newVars_sub_locOp_A geo cs SD KD hm hnk) x) hv).Ψ
        (torusCast (piece_torus_eq geo H.F.hnn hm (le_refl m')) y) =
      fun q => ((ψ (blockOf S.d S.L (M * n (m' + 1)) (m' + 1)
        (if torusCast (piece_torus_eq geo H.F.hnn hm (le_refl m')) y ∈
            fineK1 geo.M1 geo.c (n (m' + 1)) S.L m' ((H.locRH (m' + 1) Z).step m').Omega
          then m' + 1 else m') y) q : ℝ) : ℂ) := by
  classical
  refine (locData_Ψ_window geo hm (le_refl m') Z hm o _ hv hy).trans ?_
  funext q
  by_cases h : torusCast (piece_torus_eq geo H.F.hnn hm (le_refl m')) y ∈
      fineK1 geo.M1 geo.c (n (m' + 1)) S.L m' ((H.locRH (m' + 1) Z).step m').Omega
  · simp only [h, ↓reduceIte]
    unfold blockOf
    rw [hψ1]
    rfl
  · simp only [h, ↓reduceIte]
    unfold blockOf
    rw [hψ0 m' le_rfl]
    exact congrArg (fun v : EuclideanSpace ℝ (Fin N) => ((v.ofLp q : ℝ) : ℂ))
      (subVarField_new (newVars_sub_locOp_A geo cs SD KD hm hnk) x _)

open Classical in
/-- **A lower piece reads the window configuration.**  For a piece `(j, c)` of the window, `c` an old
part of the component `P` of `Z^pre_{j+2}`, with `k₁ ≤ j < m'`, the datum at the output
`ancOut c P (ρ x)` and the new variables of `ρ x` restricted to `c` is the lift of `ψ` at the data
sites of its local generating set (`ρ x` the restriction of the configuration `x` of `Z`). -/
theorem hlift_lower {m' j k1 : ℕ} (hm : m' + 1 ≤ K) (hj : j < m') (hk1j : k1 ≤ j)
    {Z : H.Comp (m' + 1)} {P : H.Comp (j + 1 + 1)} {c : H.Comp (j + 1)} (hcP : c ∈ H.parts (j + 1) P)
    (hdP : H.Desc (j + 1 + 1) (m' + 1) P Z) (hdc : H.Desc (j + 1) (m' + 1) c Z)
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (ρPx : SubCfg N (H.localHistory M K (j + 1 + 1) P) (j + 1 + 1)
      (locOp geo cs SD KD hH lab (j + 1 + 1) (hdP.le.trans hm) P).A)
    (ρcx : SubCfg N (H.localHistory M K (j + 1) c) (j + 1)
      (locOp geo cs SD KD hH lab (j + 1) (hdc.le.trans hm) c).A)
    (hρP : ∀ p : ↥(locOp geo cs SD KD hH lab (j + 1 + 1) (hdP.le.trans hm) P).A, ρPx p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hdP
        (fun t ht Y' h' => hq t (by omega) Y' h') p.1 p.2⟩)
    (hρc : ∀ p : ↥(locOp geo cs SD KD hH lab (j + 1) (hdc.le.trans hm) c).A, ρcx p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hdc
        (fun t ht Y' h' => hq t (by omega) Y' h') p.1 p.2⟩)
    (hv : EuclideanSpace ℝ (Fin N))
    (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hψ0 : ∀ i (hi : i ≤ m') b, ψ ⟨i, b⟩ =
      subVarField N x i (torusCast (blk_eq_top H.F.hnn hm (hi.trans (Nat.le_succ _))) b))
    {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hy : torusCast (piece_torus_eq geo H.F.hnn hm hj.le) y ∈
      dataSites (locGen geo (H.locRH (j + 1) c) j c.1 (locComp_mem H (hdc.le.trans hm) c)
        (hdc.le.trans hm))) :
    (locData geo (H.locRH (j + 1) c) j c.1 (locComp_mem H (hdc.le.trans hm) c) (hdc.le.trans hm)
        (ancOut (N := N) (R := R) c P ρPx)
        (newRestrict (H.localHistory M K (j + 1) c)
          (newVars_sub_locOp_A geo cs SD KD (hdc.le.trans hm) (hq (j + 1) (by omega) c hdc)) ρcx)
        hv).Ψ (torusCast (piece_torus_eq geo H.F.hnn hm hj.le) y) =
      fun q => ((ψ (blockOf S.d S.L (M * n (m' + 1)) (m' + 1)
        (if torusCast (piece_torus_eq geo H.F.hnn hm hj.le) y ∈
            fineK1 geo.M1 geo.c (n (j + 1)) S.L j ((H.locRH (j + 1) c).step j).Omega
          then j + 1 else j) y) q : ℝ) : ℂ) := by
  classical
  have hK : j + 1 ≤ K := hdc.le.trans hm
  refine (locData_Ψ_window geo hm hj.le c hK _ _ hv hy).trans ?_
  funext q
  have hx0 : ∀ i, i ≤ m' + 1 → ∀ hi : i ≤ m' + 1,
      jBlock S.d S.L (M * n K) K i (torusCast (fine_eq_top H.F.hnn hm).symm y) =
        torusCast (blk_eq_top H.F.hnn hm hi)
          (jBlock S.d S.L (M * n (m' + 1)) (m' + 1) i y) :=
    fun i _ hi => jBlock_torusCast hi (hi.trans hm) (fine_eq_top H.F.hnn hm).symm _ y
  by_cases h : torusCast (piece_torus_eq geo H.F.hnn hm hj.le) y ∈
      fineK1 geo.M1 geo.c (n (j + 1)) S.L j ((H.locRH (j + 1) c).step j).Omega
  · simp only [h, ↓reduceIte]
    unfold blockOf
    rw [hψ0 (j + 1) hj]
    refine congrArg (fun v : EuclideanSpace ℝ (Fin N) => ((v.ofLp q : ℝ) : ℂ)) ?_
    have hV : torusCast (blk_eq_top H.F.hnn hm (Nat.succ_le_succ hj.le))
        (jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (j + 1) y) ∈
        Vblk R (locHist (H.locRH (j + 1) c) M K (j + 1) c.1) (j + 1) :=
      block_mem_Vblk_of_dataSite geo hm hj.le c hK hy
    unfold outField ancOut
    simp only [hV, ↓reduceDIte]
    refine subVarField_desc_eq geo cs SD KD hm hdP (fun t ht Y' h' => hq t (by omega) Y' h')
      (hq (j + 1 + 1) (by omega) P hdP) ρPx x hρP _ (x0 := torusCast (fine_eq_top H.F.hnn hm).symm y)
      (hx0 (j + 1) (by omega) (by omega)) ?_
    rw [cubeMap_castSite H.F.hnn hm]
    exact hcase_parent geo hm hj hcP hdP hK hy
  · simp only [h, ↓reduceIte]
    unfold blockOf
    rw [hψ0 j hj.le]
    refine congrArg (fun v : EuclideanSpace ℝ (Fin N) => ((v.ofLp q : ℝ) : ℂ)) ?_
    refine (subVarField_new (newVars_sub_locOp_A geo cs SD KD hK (hq (j + 1) (by omega) c hdc))
      ρcx _).trans ?_
    refine subVarField_desc_eq geo cs SD KD hm hdc (fun t ht Y' h' => hq t (by omega) Y' h')
      (hq (j + 1) (by omega) c hdc) ρcx x hρc _ (x0 := torusCast (fine_eq_top H.F.hnn hm).symm y)
      (hx0 j (by omega) (by omega)) ?_
    rw [cubeMap_castSite H.F.hnn hm]
    exact hcase_piece geo hm hj.le c hdc hK hy

open Classical in
/-- `hlift_top` for data `(ou0, xu0)` given through their defining equations. -/
theorem hlift_top_of_eq {m' : ℕ} (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)} (hnk : ¬ IsKept H (m' + 1) Z)
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (hv : EuclideanSpace ℝ (Fin N))
    (ou0 : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (xu0 : NewCfg N (H.localHistory M K (m' + 1) Z) m')
    (hou : ou0 = o)
    (hxu : xu0 = newRestrict (H.localHistory M K (m' + 1) Z)
      (newVars_sub_locOp_A geo cs SD KD hm hnk) x)
    (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hψ1 : ∀ b, ψ ⟨m' + 1, b⟩ = outField N o (torusCast (blk_eq_top H.F.hnn hm le_rfl) b))
    (hψ0 : ∀ i (hi : i ≤ m') b, ψ ⟨i, b⟩ =
      subVarField N x i (torusCast (blk_eq_top H.F.hnn hm (hi.trans (Nat.le_succ _))) b))
    {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hy : torusCast (piece_torus_eq geo H.F.hnn hm (le_refl m')) y ∈
      dataSites (locGen geo (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hm Z) hm)) :
    (locData geo (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hm Z) hm ou0 xu0 hv).Ψ
        (torusCast (piece_torus_eq geo H.F.hnn hm (le_refl m')) y) =
      fun q => ((ψ (blockOf S.d S.L (M * n (m' + 1)) (m' + 1)
        (if torusCast (piece_torus_eq geo H.F.hnn hm (le_refl m')) y ∈
            fineK1 geo.M1 geo.c (n (m' + 1)) S.L m' ((H.locRH (m' + 1) Z).step m').Omega
          then m' + 1 else m') y) q : ℝ) : ℂ) := by
  subst hou hxu
  exact hlift_top geo cs SD KD hm hnk ou0 x hv ψ hψ1 hψ0 hy

open Classical in
/-- `hlift_lower` for data `(ou0, xu0)` given through their defining equations. -/
theorem hlift_lower_of_eq {m' j k1 : ℕ} (hm : m' + 1 ≤ K) (hj : j < m') (hk1j : k1 ≤ j)
    {Z : H.Comp (m' + 1)} {P : H.Comp (j + 1 + 1)} {c : H.Comp (j + 1)} (hcP : c ∈ H.parts (j + 1) P)
    (hdP : H.Desc (j + 1 + 1) (m' + 1) P Z) (hdc : H.Desc (j + 1) (m' + 1) c Z)
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (ρPx : SubCfg N (H.localHistory M K (j + 1 + 1) P) (j + 1 + 1)
      (locOp geo cs SD KD hH lab (j + 1 + 1) (hdP.le.trans hm) P).A)
    (ρcx : SubCfg N (H.localHistory M K (j + 1) c) (j + 1)
      (locOp geo cs SD KD hH lab (j + 1) (hdc.le.trans hm) c).A)
    (hρP : ∀ p : ↥(locOp geo cs SD KD hH lab (j + 1 + 1) (hdP.le.trans hm) P).A, ρPx p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hdP
        (fun t ht Y' h' => hq t (by omega) Y' h') p.1 p.2⟩)
    (hρc : ∀ p : ↥(locOp geo cs SD KD hH lab (j + 1) (hdc.le.trans hm) c).A, ρcx p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hdc
        (fun t ht Y' h' => hq t (by omega) Y' h') p.1 p.2⟩)
    (hv : EuclideanSpace ℝ (Fin N))
    (ou0 : OutT N R (H.localHistory M K (j + 1) c) (j + 1))
    (xu0 : NewCfg N (H.localHistory M K (j + 1) c) j)
    (hou : ou0 = ancOut (N := N) (R := R) c P ρPx)
    (hxu : xu0 = newRestrict (H.localHistory M K (j + 1) c)
      (newVars_sub_locOp_A geo cs SD KD (hdc.le.trans hm) (hq (j + 1) (by omega) c hdc)) ρcx)
    (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hψ0 : ∀ i (hi : i ≤ m') b, ψ ⟨i, b⟩ =
      subVarField N x i (torusCast (blk_eq_top H.F.hnn hm (hi.trans (Nat.le_succ _))) b))
    {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hy : torusCast (piece_torus_eq geo H.F.hnn hm hj.le) y ∈
      dataSites (locGen geo (H.locRH (j + 1) c) j c.1 (locComp_mem H (hdc.le.trans hm) c)
        (hdc.le.trans hm))) :
    (locData geo (H.locRH (j + 1) c) j c.1 (locComp_mem H (hdc.le.trans hm) c) (hdc.le.trans hm)
        ou0 xu0 hv).Ψ (torusCast (piece_torus_eq geo H.F.hnn hm hj.le) y) =
      fun q => ((ψ (blockOf S.d S.L (M * n (m' + 1)) (m' + 1)
        (if torusCast (piece_torus_eq geo H.F.hnn hm hj.le) y ∈
            fineK1 geo.M1 geo.c (n (j + 1)) S.L j ((H.locRH (j + 1) c).step j).Omega
          then j + 1 else j) y) q : ℝ) : ℂ) := by
  subst hou hxu
  exact hlift_lower geo cs SD KD hm hj hk1j hcP hdP hdc hq x ρPx ρcx hρP hρc hv ψ hψ0 hy

end Lift

end Piece

end Balaban.LargeField
