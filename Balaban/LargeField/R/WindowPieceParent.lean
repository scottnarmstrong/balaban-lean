/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowPieceNone

/-!
# The real domain of the datum of an ancestor piece (blocker 4)

An ancestor piece `C` of the window (a component of `Z^pre_{k+1}`, `k = i + 1`, retained in the
lineage) has a successor `P` of scale `k + 2` with `C ∈ parts_{k+1}(P)`.  Its output `o` on `V_C` is the
field `ψ_{k+1}` of the variables of `P` (`ancOut`).  The data sites of the local family of `C` that are
not over `C` lie over cubes of the shell of `C` (within `⌊R_k⌋ + 2` cubes); by the separation of the
components these cubes are outside `Z^pre_{k+1}`.

* `shell_parent_geometry`: the cubes of scale `k + 2` within one cube of such a cube lie in `P` and
  outside `Ω_{k+2}` (Lemma I.3.5 (i));
* `parent_shell_conditions`: hence the hypotheses of the second family of `ChiDomProp` of `P` at scale
  `k + 1` hold at such a cube (it lies in `P`, outside `Z_{k+1}`, far from `Ω_{k+2}`), and the cube is a
  cube of `Ω_{k+1}` of the localized history of `P`, so the multiscale field of `P` at scale `k + 1`
  reads the variables there;
* `parent_outside_sphere`, `parent_outside_pair`: (R2) and (R1) at the data sites of `C` outside `C`,
  from the second family of `P`;
* `piece_inDomainR_of_parent`: the datum of `C` lies in the real domain `Ψ̃(G; ν, η)` from
  `ChiDomAt` of `C` and of `P`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField.Def7 RegionHistory

section PieceParent

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N i : ℕ} (H : RegionHistory S n R k0 K) (g : Geo S n R M)
  (C : H.Comp (i + 1 + 1)) (P : H.Comp (i + 1 + 1 + 1)) (hCP : C ∈ H.parts (i + 1 + 1) P)
  (hjK : i + 1 + 1 + 1 ≤ K)

omit [NeZero M] in
include g hjK hCP in
/-- The cubes over the shell of `C` (outside `C`, within `⌊R_{k}⌋ + 2`) lie over `U_{k+1}^{∼1}`, hence
in `P` together with their one-cube neighbours, away from `Ω_{k+2}`. -/
theorem shell_parent_geometry
    {w : Torus S.d (n (i + 1 + 1))} (hw : w ∈ nbhd (⌊R (i + 1)⌋₊ + 2) C.1) :
    ∀ c, supDist (blockMap S.L (n (i + 1 + 1 + 1)) w) c ≤ 1 →
      c ∈ P.1 ∧ c ∉ (H.step (i + 1 + 1)).Omega := by
  intro c hc
  have hret : C.1 ∉ H.rem (i + 1 + 1) := ((H.mem_parts (i + 1 + 1) C P).mp hCP).1
  set st := H.step (i + 1 + 1) with hst
  have hL : 0 < S.L := NeZero.pos S.L
  have hn : n (i + 1 + 1) = S.L * n (i + 1 + 1 + 1) := H.F.hnn (i + 1 + 1) (by omega)
  obtain ⟨v, hv, hd⟩ := mem_nbhd.1 hw
  have hCZ : ∀ z, z ∈ C.1 → z ∈ st.Z := fun z hz => (H.mem_Z_iff hz).2 hret
  have hwU : w ∈ nbhd 1 st.U := by
    show w ∈ nbhd 1 (nbhd (⌊R (i + 1)⌋₊ + 1) st.Z)
    rw [nbhd_nbhd]
    exact mem_nbhd.2 ⟨v, hCZ v hv, by omega⟩
  have hq1 := blockMap_nbhd_subset hn (m := n (i + 1 + 1 + 1)) 1 st.U ⟨w, hwU, rfl⟩
  have hdiv : (1 + S.L - 1) / S.L = 1 := by
    rw [show 1 + S.L - 1 = S.L by omega, Nat.div_self hL]
  rw [hdiv] at hq1
  obtain ⟨u', hu', hqu⟩ := mem_nbhd.1 hq1
  have hcU : c ∈ nbhd (⌊R (i + 1 + 1)⌋₊ + 4) st.Uprime :=
    mem_nbhd.2 ⟨u', hu', (supDist_triangle c (blockMap S.L (n (i + 1 + 1 + 1)) w) u').trans
      (by rw [supDist_comm c]; omega)⟩
  have hcO : c ∉ st.Omega := fun hO => st.nbhd_Uprime_subset hcU
    (st.Omega_subset_OmegaPrime hO)
  refine ⟨?_, hcO⟩
  have hcZ : c ∈ H.F.Zp (i + 1 + 1 + 1) :=
    mem_finOf.2 (Omega_compl_subset_Zpre' (i + 1 + 1) st _ _ hcO)
  have hv'P : blockMap S.L (n (i + 1 + 1 + 1)) v ∈ P.1 :=
    ((H.mem_parts (i + 1 + 1) C P).mp hCP).2 ⟨v, hv, rfl⟩
  have h1 := supDist_blockMap_le (L := S.L) (m := n (i + 1 + 1 + 1)) hn w v
  have h2 : (supDist w v + S.L - 1) / S.L ≤ ⌊R (i + 1)⌋₊ + 2 := by
    refine Nat.div_le_of_le_mul ?_
    have e : S.L * (⌊R (i + 1)⌋₊ + 2) = S.L * ⌊R (i + 1)⌋₊ + 2 * S.L := by ring
    have e2 : ⌊R (i + 1)⌋₊ ≤ S.L * ⌊R (i + 1)⌋₊ := Nat.le_mul_of_pos_left _ hL
    omega
  have hom : 2 * ⌊R (i + 1 + 1)⌋₊ + S.L + 11 ≤ S.omega (i + 1 + 1 + 1) :=
    (H.stepGeom (show i + 1 + 1 < K by omega)).rad.omega_rho
  have hmono := g.hRmono (i + 1 + 1)
  simp only [Nat.add_sub_cancel] at hmono
  refine mem_comp_of_close P.2 hv'P hcZ ?_
  have h3 := supDist_triangle (blockMap S.L (n (i + 1 + 1 + 1)) v) (blockMap S.L (n (i + 1 + 1 + 1)) w) c
  have h4 := supDist_comm (blockMap S.L (n (i + 1 + 1 + 1)) v) (blockMap S.L (n (i + 1 + 1 + 1)) w)
  omega

omit [NeZero M] [NeZero S.L] in
include hjK in
/-- A cube of `Ω_{k+1}` of the lineage-localized history of `P` (`k + 1 = i + 2`) is a cube of the
global `Ω_{k+1}`: the complement of the local `Ω` is contained in that of the global history. -/
theorem mem_locOmega_of_mem_Omega {w : Torus S.d (n (i + 1 + 1))}
    (hw : w ∈ (H.step (i + 1)).Omega) : w ∈ ((H.locRH (i + 1 + 1 + 1) P).step (i + 1)).Omega := by
  by_contra hc
  have h1 := ((H.locRH_derived P (show i + 1 < i + 1 + 1 + 1 by omega)
    (show i + 1 < K by omega)).2.1)
  have hc' : w ∈ ((H.locRH (i + 1 + 1 + 1) P).step (i + 1)).Omegaᶜ := hc
  rw [← h1] at hc'
  exact hc'.1 hw

include g hCP hjK in
/-- **The hypotheses of the second family of `ChiDomProp` of `P` at scale `k + 1 = i + 2` hold at a cube
`w` of the shell of `C`**: `w` is a cube of `P`, it misses `Z_{k+1}`, it is far from `Ω_{k+2}`, and it is a
cube of the localized `Ω_{k+1}` of `P`. -/
theorem parent_shell_conditions {w : Torus S.d (n (i + 1 + 1))}
    (hw : w ∈ nbhd (⌊R (i + 1)⌋₊ + 2) C.1) (hwC : w ∉ C.1) :
    CubeSub (S := S) (n := n) M K (i + 1 + 1) w
        (fineSet (S := S) (n := n) M K (i + 1 + 1 + 1) (P.1 : Set (Torus S.d (n (i + 1 + 1 + 1))))) ∧
      (∀ z, cubeMap n S.L M K (i + 1 + 1) z = w →
        z ∉ (H.localHistory M K (i + 1 + 1 + 1) P).Z (i + 1 + 1)) ∧
      (∀ z, cubeMap n S.L M K (i + 1 + 1) z = w →
        cubeMap n S.L M K (i + 1 + 1 + 1) z ∉
          lhOmegaSim (H.localHistory M K (i + 1 + 1 + 1) P) (i + 1 + 1 + 1) (i + 1 + 1 + 1)) ∧
      w ∈ ((H.locRH (i + 1 + 1 + 1) P).step (i + 1)).Omega := by
  have hjC : i + 1 + 1 ≤ K := by omega
  have hgeo := shell_parent_geometry H g C P hCP hjK hw
  have hwZp : w ∉ H.F.Zp (i + 1 + 1) := fun hZ => hwC (mem_comp_of_near_comp H C hjC hZ hw)
  have hsucc : ∀ z, cubeMap n S.L M K (i + 1 + 1) z = w →
      cubeMap n S.L M K (i + 1 + 1 + 1) z = blockMap S.L (n (i + 1 + 1 + 1)) w := by
    intro z hz
    rw [← cubeMap_succ H.F.hnn hjK z, hz]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    show cubeMap n S.L M K (i + 1 + 1 + 1) z ∈ P.1
    rw [hsucc z hz]
    exact (hgeo _ (by simp [supDist_self])).1
  · intro z hz hzZ
    have h1 : cubeMap n S.L M K (i + 1 + 1) z ∈ ((H.locRH (i + 1 + 1 + 1) P).step (i + 1 + 1)).Z := hzZ.1
    rw [locRH_Z P (Nat.le_succ _) hjC] at h1
    rw [hz] at h1
    exact hwZp (mem_finOf.2 (lin_sub_Zpre (i + 1 + 1) (i + 1 + 1 + 1) P h1))
  · intro z hz hmem
    unfold lhOmegaSim lhOmegaNb at hmem
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at hmem
    rw [hsucc z hz] at hmem
    obtain ⟨v, hv, hd⟩ := mem_nbhd.1 hmem
    obtain ⟨hvP, hvO⟩ := hgeo v hd
    obtain ⟨x0, hx0⟩ := cubeMap_surjective (S := S) (n := n) (M := M) (K := K) H.F.hnn hjK v
    rcases hv x0 hx0 with hl | hr
    · apply hvO
      have h2 : cubeMap n S.L M K (i + 1 + 1 + 1) x0 ∈ ((H.locRH (i + 1 + 1 + 1) P).step (i + 1 + 1)).Omega :=
        hl.1
      rw [hx0] at h2
      exact (omega_loc_iff H P hjK hvP).1 h2
    · exact hr (cubeSub_Z_of_mem_comp (M := M) H P hjK hvP x0 hx0)
  · exact mem_locOmega_of_mem_Omega H P hjK (mem_omega_of_not_mem_Zp H hwZp)

section PieceParentOut

variable (hjC : i + 1 + 1 ≤ K)

omit [NeZero M] in
include hjC in
/-- A data site of the local family of `C` whose cube is not in `C` lies over `Ω_{k+1}` of the
localized history of `C`. -/
theorem dataSite_outside_omega {s : BgT g (i + 1 + 1)}
    (hq : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ C.1) :
    blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∈
      ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega :=
  mem_omega_of_not_mem_Zp (H.locRH (i + 1 + 1) C) (by rw [locRH_Zp hjC C]; exact hq)

include hjC in
/-- The datum of `C` at a data site outside `C` is the output field at the top block of the site. -/
theorem dataSite_outside_value (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (x : NewCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1)) (hv : EuclideanSpace ℝ (Fin N))
    {s : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjC C) hjC))
    (hq : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ C.1) (l : Fin N) :
    ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjC C) hjC o x hv).Ψ s l).re =
      outField N o (jBlock S.d S.L (M * n K) K (i + 1 + 1) (bgToFine g H.F.hnn hjC s)) l := by
  rw [locData_Ψ_of_omega (H.locRH (i + 1 + 1) C) C.1 (locComp_mem H hjC C) hjC g o x hv hs
    (dataSite_outside_omega H g C hjC hq)]
  simp only [Complex.ofReal_re]
  have hb1 : blkToBlock g H.F.hnn hjC
      (jBlock S.d S.L (g.M1 * (g.c * n (i + 1 + 1))) (i + 1 + 1) (i + 1 + 1) s) =
      jBlock S.d S.L (M * n K) K (i + 1 + 1) (bgToFine g H.F.hnn hjC s) :=
    (jBlock_bgToFine_gen g H.F.hnn hjC le_rfl s).symm
  rw [hb1]
  rfl

/-- The cube of the data site `s` of `C` as a cube of the shell of `C`. -/
theorem dataSite_cube_eq {s : BgT g (i + 1 + 1)} :
    cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjC s) =
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s :=
  cubeMap_bgToFine_gen g H.F.hnn hjC _ s

include hjC hjK hCP in
/-- The conditions of the second family of `P` at the `π_{k+1}`-cube of a data site of `C` outside `C`
(`cubeMap` form). -/
theorem parent_outside_conditions {s : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjC C) hjC))
    (hq : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ C.1) :
    cubeMap n S.L M K (i + 1 + 1 + 1) (bgToFine g H.F.hnn hjC s) ∈ P.1 ∧
      (∀ z, cubeMap n S.L M K (i + 1 + 1) z = cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjC s) →
        z ∉ (H.localHistory M K (i + 1 + 1 + 1) P).Z (i + 1 + 1)) ∧
      (∀ z, cubeMap n S.L M K (i + 1 + 1) z = cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjC s) →
        cubeMap n S.L M K (i + 1 + 1 + 1) z ∉
          lhOmegaSim (H.localHistory M K (i + 1 + 1 + 1) P) (i + 1 + 1 + 1) (i + 1 + 1 + 1)) := by
  have hw := dataSite_cube_mem_nbhd_comp H g C hjC hs
  rw [← dataSite_cube_eq H g hjC] at hw hq
  obtain ⟨hA, hB, hD, -⟩ := parent_shell_conditions H g C P hCP hjK hw hq
  exact ⟨hA (bgToFine g H.F.hnn hjC s) rfl, hB, hD⟩

include hjC hjK hCP in
/-- **(R2) at a data site of `C` outside `C`, from the second family of `ChiDomProp` of the
successor `P`**: if the output of `C` is the field `ψ` of `P` at the top blocks of the data sites
outside `C`, the sphere bound holds there with the radius of the second family. -/
theorem parent_outside_sphere {η : ℝ} (ψP : MultiField S n M K N)
    (hF2 : PieceSecondFamily H P ψP η)
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (x : NewCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1)) (hv : EuclideanSpace ℝ (Fin N))
    (hoP : ∀ t ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjC C) hjC),
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) t ∉ C.1 →
      outField N o (jBlock S.d S.L (M * n K) K (i + 1 + 1) (bgToFine g H.F.hnn hjC t)) =
        ψP (i + 1 + 1) (jBlock S.d S.L (M * n K) K (i + 1 + 1) (bgToFine g H.F.hnn hjC t)))
    {s : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjC C) hjC))
    (hq : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ C.1) :
    |∑ l, ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjC C) hjC o x hv).Ψ s l).re ^ 2 - 1| < η := by
  obtain ⟨hP, hB, hD⟩ := parent_outside_conditions H g C P hCP hjK hjC hs hq
  have key := psi_block_sphere_far H P hjK ψP hF2 hP hB hD
  rw [← hoP s hs hq] at key
  simp_rw [dataSite_outside_value H g C hjC o x hv hs hq]
  rw [parent_sum_sq_eq_norm_sq]
  exact key

include hjC hjK hCP in
/-- **(R1) at an interface pair of data sites of `C` outside `C`, from the second family of
`ChiDomProp` of the successor `P`.** -/
theorem parent_outside_pair {η : ℝ} (ψP : MultiField S n M K N)
    (hF2 : PieceSecondFamily H P ψP η)
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (x : NewCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1)) (hv : EuclideanSpace ℝ (Fin N))
    (hoP : ∀ t ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjC C) hjC),
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) t ∉ C.1 →
      outField N o (jBlock S.d S.L (M * n K) K (i + 1 + 1) (bgToFine g H.F.hnn hjC t)) =
        ψP (i + 1 + 1) (jBlock S.d S.L (M * n K) K (i + 1 + 1) (bgToFine g H.F.hnn hjC t)))
    {s s' : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjC C) hjC))
    (hs' : s' ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjC C) hjC))
    (hp : IsInterfacePair (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjC C) hjC) s s')
    (hq : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ C.1)
    (hq' : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s' ∉ C.1) :
    rn (fun l => ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjC C) hjC o x hv).Ψ s l).re -
      ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjC C) hjC o x hv).Ψ s' l).re) < η := by
  obtain ⟨hP, hB, hD⟩ := parent_outside_conditions H g C P hCP hjK hjC hs hq
  have key := psi_block_pair_far H P hjK ψP hF2 hP hB hD (blockAdj_of_interfacePair H g hjC hp).2
  have e : (fun l => ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjC C) hjC o x hv).Ψ s l).re -
      ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjC C) hjC o x hv).Ψ s' l).re) =
      fun l => (ψP (i + 1 + 1) (jBlock S.d S.L (M * n K) K (i + 1 + 1) (bgToFine g H.F.hnn hjC s)) -
        ψP (i + 1 + 1) (jBlock S.d S.L (M * n K) K (i + 1 + 1) (bgToFine g H.F.hnn hjC s'))) l := by
    funext l
    rw [dataSite_outside_value H g C hjC o x hv hs hq l, dataSite_outside_value H g C hjC o x hv hs' hq' l,
      hoP s hs hq, hoP s' hs' hq']
    rfl
  rw [e, rn_fun_eq_norm]
  exact key

include hjC hjK hCP in
/-- The `π_{k+1}`-cube of a data site of `C` outside `C` is a cube of the localized `Ω_{k+1}` of `P`. -/
theorem parent_outside_omega {s : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjC C) hjC))
    (hq : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ C.1) :
    cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjC s) ∈
      ((H.locRH (i + 1 + 1 + 1) P).step (i + 1)).Omega := by
  have hw := dataSite_cube_mem_nbhd_comp H g C hjC hs
  rw [← dataSite_cube_eq H g hjC] at hw hq
  exact (parent_shell_conditions H g C P hCP hjK hw hq).2.2.2

include hjK in
/-- The multiscale field of `P` at the scale `k + 1` reads the variables of `P` at a block over a cube of
the localized `Ω_{k+1}`. -/
theorem parent_field_value {AP : Set (InternalVars (H.localHistory M K (i + 1 + 1 + 1) P) (i + 1 + 1 + 1))}
    (oP : OutT N R (H.localHistory M K (i + 1 + 1 + 1) P) (i + 1 + 1 + 1))
    (xP : SubCfg N (H.localHistory M K (i + 1 + 1 + 1) P) (i + 1 + 1 + 1) AP)
    {b : BlockAt S n M K (i + 1 + 1)}
    (hb : blockCube S n M K (i + 1 + 1) b ∈ ((H.locRH (i + 1 + 1 + 1) P).step (i + 1)).Omega) :
    subMultiscaleField N (H.localHistory M K (i + 1 + 1 + 1) P) (i + 1 + 1 + 1)
      (Vblk R (H.localHistory M K (i + 1 + 1 + 1) P) (i + 1 + 1 + 1)) xP oP (i + 1 + 1) b =
      subVarField N xP (i + 1 + 1) b := by
  have hmask := blockSub_lhOmega_of_cube (M := M) H P hjK (y := b) hb
  unfold subMultiscaleField
  simp only [Nat.lt_succ_self, ↓reduceIte, hmask, or_true]

variable (cs : OpConsts)

include hjC hjK hCP in
/-- **The real domain of the datum of an ancestor piece.**  `C` is a piece with the successor `P` in the
lineage, `ChiDomAt` holds for `C` at `(o, xw)` and for `P` at `(oP, xP)`, and the output `o` of `C` is the
field `ψ_{k+1}` of the variables of `P` on `V_C`.  Then the datum of `C` at `(o, newRestrict xw)` is in
the real domain `Ψ̃(G; ν, η)` for
`η = max (max (3dLδ_{k}) (3δ_{k})) (max (3dLδ_{k-1}) (3δ_{k+1}))`, `k = i + 1`: the inside of `C` by the
families of `ChiDomAt` of `C`, the outside of `C` by the second family of `ChiDomAt` of `P` at scale
`k + 1`. -/
theorem piece_inDomainR_of_parent {ν : ℝ}
    {A : Set (InternalVars (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))}
    (hnew : newVars (H.localHistory M K (i + 1 + 1) C) (i + 1) ⊆ A)
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (xw : SubCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) A)
    (hχd : ChiDomAt g cs H (i + 1 + 1) C o xw) (hv : EuclideanSpace ℝ (Fin N))
    {AP : Set (InternalVars (H.localHistory M K (i + 1 + 1 + 1) P) (i + 1 + 1 + 1))}
    (oP : OutT N R (H.localHistory M K (i + 1 + 1 + 1) P) (i + 1 + 1 + 1))
    (xP : SubCfg N (H.localHistory M K (i + 1 + 1 + 1) P) (i + 1 + 1 + 1) AP)
    (hχP : ChiDomAt g cs H (i + 1 + 1 + 1) P oP xP)
    (hou : ∀ b ∈ Vblk R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1),
      outField N o b = subVarField N xP (i + 1 + 1) b)
    (hν : 0 ≤ ν) (hunit : ‖hv‖ = 1)
    (hη : 0 < max (max (3 * S.d * S.L * cs.delta (i + 1)) (3 * cs.delta (i + 1)))
      (max (3 * S.d * S.L * cs.delta i) (3 * cs.delta (i + 1 + 1))))
    (hmass : 2 * ν * ((S.L : ℝ) ^ (i + 1 + 1)) ^ 2 <
      (max (max (3 * S.d * S.L * cs.delta (i + 1)) (3 * cs.delta (i + 1)))
        (max (3 * S.d * S.L * cs.delta i) (3 * cs.delta (i + 1 + 1)))) ^ 2) :
    InDomainR (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjC C) hjC) ν
      (max (max (3 * S.d * S.L * cs.delta (i + 1)) (3 * cs.delta (i + 1)))
        (max (3 * S.d * S.L * cs.delta i) (3 * cs.delta (i + 1 + 1))))
      (locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjC C) hjC o
        (newRestrict (H.localHistory M K (i + 1 + 1) C) hnew xw) hv) := by
  obtain ⟨hF1, hF2, hFZ⟩ := families_of_chiDomAt H g cs C hχd
  have hF2P := (families_of_chiDomAt H g cs P hχP).2.1
  have hoP : ∀ t ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjC C) hjC),
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) t ∉ C.1 →
      outField N o (jBlock S.d S.L (M * n K) K (i + 1 + 1) (bgToFine g H.F.hnn hjC t)) =
        subMultiscaleField N (H.localHistory M K (i + 1 + 1 + 1) P) (i + 1 + 1 + 1)
          (Vblk R (H.localHistory M K (i + 1 + 1 + 1) P) (i + 1 + 1 + 1)) xP oP (i + 1 + 1)
          (jBlock S.d S.L (M * n K) K (i + 1 + 1) (bgToFine g H.F.hnn hjC t)) := by
    intro t ht hq
    rw [parent_field_value H P hjK oP xP]
    · exact hou _ (dataSite_block_mem_Vblk H g C hjC ht)
    · rw [blockCube, cubeMap_eq_comp H.F.hnn hjC]
      exact parent_outside_omega H g C P hCP hjK hjC ht hq
  refine piece_inDomainR H g C hjC
    (subMultiscaleField N (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1)
      (Vblk R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1)) xw o)
    o (newRestrict (H.localHistory M K (i + 1 + 1) C) hnew xw) hv hν hunit hη hmass
    (subMultiscaleField N (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1)
      (Vblk R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1)) xw o)
    (pieceField_top_eq H C o xw hnew) (pieceField_k_eq H C o xw hnew) hF1 hF2 hFZ
    (fun t _ _ => pieceField_k_eq H C o xw hnew _) ?_ ?_
  · intro t ht hq
    exact parent_outside_sphere H g C P hCP hjK hjC _ hF2P o _ hv hoP ht hq
  · intro t t' ht ht' hp hq hq' _ _
    exact parent_outside_pair H g C P hCP hjK hjC _ hF2P o _ hv hoP ht ht' hp hq hq'

end PieceParentOut

end PieceParent

end Balaban.LargeField
