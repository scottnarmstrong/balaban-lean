module

public import Balaban.LargeField.Operators.QuietIndep

/-!
# Confinement of the new′ variables of a quiet step to shells (Part II, Lemma II.5.14)

In a quiet step there are no fluctuation variables (`Ω = Ω''` on `Z'`, `quiet_omega_eq`), so the
new′ variables are the outputs `ψ_{k+1}` on `Ω_{k+1} ∩ Z'` (`shell_newOut`) and the variables
`ψ_k` on `Z^c_k ∩ Ω^c_{k+1} ∩ Z'` (`shell_newPrime`).  By `χ^new_k(Z')` (the first and second
families of (1.24)) each such variable lies in the shell `{||u|² - 1| < 3 d L δ_k}`; this uses the
layers of the generating set of the history (`mem_histGen`) and `Ω_k^c ⊆ Z_k`
(`RegionSeq.OmegaAt_compl_subset_Z`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory ENNReal

section Shell

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0} {k : ℕ}

theorem quiet_new_empty (Z' : H.Comp (k + 1)) (hq : IsQuiet (H.locRH (k + 1) Z') k Z'.1) :
    ((H.locRH (k + 1) Z').step k).P = ∅ ∧ ((H.locRH (k + 1) Z').step k).Q = ∅ ∧
      ((H.locRH (k + 1) Z').step k).R = ∅ := by
  have hsub : ∀ x ∈ ((H.locRH (k + 1) Z').step k).newCubes, False := by
    intro x hx
    have h0 := ((H.locRH (k + 1) Z').step k).newCubes_subset_Z0 hx
    have h1 := ((H.locRH (k + 1) Z').step k).Z0_subset_Zpre (S.omega (k + 1))
      (critOpt S k0 (k + 1)) h0
    have h2 : x ∈ ((H.locRH (k + 1) Z').F.Zp (k + 1) : Finset _) := mem_finOf.mpr h1
    rw [locRH_Zp] at h2
    have h3 : x ∈ (Z'.1 ∩ (H.locRH (k + 1) Z').newCubes (k + 1)) :=
      Finset.mem_inter.mpr ⟨h2, mem_finOf.mpr hx⟩
    rw [hq] at h3
    exact Finset.notMem_empty _ h3
  refine ⟨?_, ?_, ?_⟩ <;> ext x <;> simp only [Set.mem_empty_iff_false, iff_false] <;> intro hx
  · exact hsub x (Or.inl (Or.inl (Or.inl hx)))
  · exact hsub x (Or.inl (Or.inl (Or.inr hx)))
  · exact hsub x (Or.inl (Or.inr hx))

theorem quiet_omega_eq (Z' : H.Comp (k + 1)) (hq : IsQuiet (H.locRH (k + 1) Z') k Z'.1) :
    (H.localHistory M K (k + 1) Z').Omega k = (H.localHistory M K (k + 1) Z').OmegaDD k := by
  obtain ⟨hP, hQ, hR⟩ := quiet_new_empty Z' hq
  have h := ((H.locRH (k + 1) Z').step k).eq_of_new_empty hP hQ hR
  show fineSet (S := S) (n := n) M K (k + 1) ((H.locRH (k + 1) Z').step k).Omega ∩ _ =
    fineSet (S := S) (n := n) M K (k + 1) ((H.locRH (k + 1) Z').step k).OmegaDD ∩ _
  rw [h.2]

theorem quiet_newPrime_large (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (hq : IsQuiet (H.locRH (k + 1) Z') k Z'.1)
    (p : InternalVars (H.localHistory M K (k + 1) Z') (k + 1))
    (hp : p ∈ newPrimeVars (H.localHistory M K (k + 1) Z') k) :
    p.1.2.1 = VarKind.large := by
  obtain ⟨⟨⟨j, hj⟩, κ, y⟩, hb⟩ := p
  have hjk : j = k := hp.1
  subst hjk
  cases κ with
  | large => rfl
  | fluct =>
    exfalso
    obtain ⟨x0, hx0⟩ := exists_site_in_block (S := S) (n := n) (M := M) (by omega) y
    have := hb x0 hx0
    simp only [varSet] at this
    rw [quiet_omega_eq Z' hq] at this
    exact this.2 this.1

variable (geo : Geo S n R M) (cs : OpConsts)

theorem shell_newOut (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) (hchi : ChiNewAt geo cs H k Z' o x)
    (y : BlockAt S n M K (k + 1)) (hy : newOutP (H.localHistory M K (k + 1) Z') k y) :
    |‖outField N o y‖ ^ 2 - 1| < 3 * S.d * S.L * cs.delta k := by
  have hnn := H.F.hnn
  obtain ⟨hcZ, hcO⟩ := (newOutP_iff hK Z' y).mp hy
  set c := blockCube S n M K (k + 1) y with hc
  have hcub : CubeSub (S := S) (n := n) M K (k + 1) c ((H.localHistory M K (k + 1) Z').Z (k + 1)) := by
    intro x' hx'
    refine ⟨?_, ?_⟩
    · show cubeMap n S.L M K (k + 1) x' ∈ ((H.locRH (k + 1) Z').step (k + 1)).Z
      rw [locRH_Z Z' le_rfl, lin_self, hx']; exact hcZ
    · show cubeMap n S.L M K (k + 1) x' ∈ (Z'.1 : Set (Torus S.d (n (k + 1))))
      rw [hx']; exact hcZ
  have hom : c ∈ omegaSim (H.localHistory M K (k + 1) Z') (k + 1) (k + 1) := by
    unfold omegaSim omegaNb
    have hne : ¬ (k + 1 = k + 1 + 1) := by omega
    simp only [hne, ↓reduceIte]
    refine subset_nbhd 1 _ ?_
    intro x' hx'
    refine ⟨?_, ?_⟩
    · show cubeMap n S.L M K (k + 1) x' ∈ ((H.locRH (k + 1) Z').step k).Omega
      rw [hx']; exact hcO
    · show cubeMap n S.L M K (k + 1) x' ∈ (Z'.1 : Set (Torus S.d (n (k + 1))))
      rw [hx']; exact hcZ
  have h1 := hchi.1 c hcub hom
  obtain ⟨x0, hx0⟩ := exists_site_in_block (S := S) (n := n) (M := M) hK y
  have hx0c : cubeMap n S.L M K (k + 1) x0 = c := (blockCube_eq_cubeMap hnn hK hx0).symm
  have hmem : (⟨k + 1, y⟩ : BlockPt S n M K) ∈ genBlocksIn
      ((H.locRH (k + 1) Z').histGen (M := M) (locRH_rem (k + 1) Z') H.F.ok.two_le_L K
        (fun j _ _ => geo.hRlow j)) (k + 1) (nbhd 1 {c}) := by
    refine ⟨Nat.succ_pos k, hK, x0, ?_, hx0, by rw [hx0c]; exact subset_nbhd 1 _ rfl⟩
    rw [GeneratingSet.mem_layer]
    refine ⟨?_, ?_⟩
    · rw [(H.locRH (k + 1) Z').mem_histGen]
      exact ⟨hK, by rw [hx0c]; exact hcO⟩
    · rw [(H.locRH (k + 1) Z').mem_histGen]
      rintro ⟨hK2, hO2⟩
      have hO2' : blockMap S.L (n (k + 1 + 1)) (cubeMap n S.L M K (k + 1) x0) ∈
          ((H.locRH (k + 1) Z').step (k + 1)).Omega := by
        rw [cubeMap_succ hnn (by omega)]; exact hO2
      have hz : cubeMap n S.L M K (k + 1) x0 ∈ ((H.locRH (k + 1) Z').step (k + 1)).Z := by
        rw [locRH_Z Z' le_rfl, lin_self, hx0c]; exact hcZ
      exact ((H.locRH (k + 1) Z').step (k + 1)).not_mem_Z_of_mem_Omega
        (Nat.pos_of_ne_zero (NeZero.ne _)) (hnn (k + 1)) hO2' hz
  have h2 := h1.2 _ hmem
  have hψ : subMultiscaleField N (H.localHistory M K (k + 1) Z') (k + 1)
      (Vblk R (H.localHistory M K (k + 1) Z') (k + 1)) x o (k + 1) y = outField N o y := by
    unfold subMultiscaleField
    simp only [lt_irrefl, ↓reduceIte, ↓reduceDIte]
    have hb : BlockSub (S := S) (n := n) (M := M) (K := K) (k + 1) y
        ((H.localHistory M K (k + 1) Z').Omega k) := hy.2
    simp [hb]
  simpa [hψ] using h2

theorem shell_newPrime (hK : k + 1 ≤ K) (hk1 : 1 ≤ k) (hδ : 0 ≤ cs.delta k) (hdL : 1 ≤ S.d * S.L)
    (Z' : H.Comp (k + 1)) (hq : IsQuiet (H.locRH (k + 1) Z') k Z'.1)
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) (hchi : ChiNewAt geo cs H k Z' o x)
    (p : InternalVars (H.localHistory M K (k + 1) Z') (k + 1))
    (hp : p ∈ newPrimeVars (H.localHistory M K (k + 1) Z') k) :
    |‖VarVal.toEuc (x ⟨p, newPrimeVars_sub _ _ hp⟩)‖ ^ 2 - 1| < 3 * S.d * S.L * cs.delta k := by
  have hlarge := quiet_newPrime_large hK Z' hq p hp
  obtain ⟨⟨⟨j, hj⟩, κ, y⟩, hb⟩ := p
  have hjk : j = k := hp.1
  subst hjk
  subst hlarge
  have hcompl : BlockSub (S := S) (n := n) (M := M) (K := K) j y
      ((H.localHistory M K (j + 1) Z').Z j)ᶜ := by
    rcases hp.2 with h | h
    · exact VarKind.noConfusion h
    · exact h
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hnn := H.F.hnn
  have hkK : m + 1 ≤ K := by omega
  have hmK : m ≤ K := by omega
  obtain ⟨x0, hx0⟩ := exists_site_in_block (S := S) (n := n) (M := M) hkK y
  have hb0 := hb x0 hx0
  have hbZ : x0 ∈ (H.localHistory M K (m + 1 + 1) Z').Z (m + 1 + 1) := hb0.1
  have hbO : x0 ∉ (H.localHistory M K (m + 1 + 1) Z').Omega (m + 1) := hb0.2
  have hcube : cubeMap n S.L M K (m + 1) x0 = blockCube S n M K (m + 1) y :=
    (blockCube_eq_cubeMap hnn hkK hx0).symm
  have hcube' : cubeMap n S.L M K (m + 1 + 1) x0 =
      blockMap S.L (n (m + 1 + 1)) (blockCube S n M K (m + 1) y) := by
    rw [← cubeMap_succ hnn hkK x0, hcube]
  have h'Z : blockMap S.L (n (m + 1 + 1)) (blockCube S n M K (m + 1) y) ∈
      (Z'.1 : Set (Torus S.d (n (m + 1 + 1)))) := by
    have : cubeMap n S.L M K (m + 1 + 1) x0 ∈ (Z'.1 : Set (Torus S.d (n (m + 1 + 1)))) := hbZ.2
    rwa [hcube'] at this
  have h'O : blockMap S.L (n (m + 1 + 1)) (blockCube S n M K (m + 1) y) ∉
      ((H.locRH (m + 1 + 1) Z').step (m + 1)).Omega := by
    intro hh
    apply hbO
    refine ⟨?_, ?_⟩
    · show cubeMap n S.L M K (m + 1 + 1) x0 ∈ ((H.locRH (m + 1 + 1) Z').step (m + 1)).Omega
      rwa [hcube']
    · show cubeMap n S.L M K (m + 1 + 1) x0 ∈ (Z'.1 : Set (Torus S.d (n (m + 1 + 1))))
      rwa [hcube']
  have hnotZ : blockCube S n M K (m + 1) y ∉ ((H.locRH (m + 1 + 1) Z').step (m + 1)).Z := by
    intro hh
    exact hcompl x0 hx0 ⟨by
      show cubeMap n S.L M K (m + 1) x0 ∈ ((H.locRH (m + 1 + 1) Z').step (m + 1)).Z
      rwa [hcube], by
      show cubeMap n S.L M K (m + 1 + 1) x0 ∈ (Z'.1 : Set (Torus S.d (n (m + 1 + 1))))
      rwa [hcube']⟩
  have hΩk : blockCube S n M K (m + 1) y ∈ ((H.locRH (m + 1 + 1) Z').step m).Omega := by
    by_contra hh
    exact hnotZ (((H.locRH (m + 1 + 1) Z').toSeq (locRH_rem (m + 1 + 1) Z')).OmegaAt_compl_subset_Z
      m hh)
  have hbl : BlockSub (S := S) (n := n) (M := M) (K := K) (m + 1) y
      ((H.localHistory M K (m + 1 + 1) Z').Omega m) := fun x' hx' => by
    have e1 : cubeMap n S.L M K (m + 1) x' = blockCube S n M K (m + 1) y :=
      (blockCube_eq_cubeMap hnn hkK hx').symm
    refine ⟨?_, ?_⟩
    · show cubeMap n S.L M K (m + 1) x' ∈ ((H.locRH (m + 1 + 1) Z').step m).Omega
      rw [e1]; exact hΩk
    · show cubeMap n S.L M K (m + 1 + 1) x' ∈ (Z'.1 : Set (Torus S.d (n (m + 1 + 1))))
      rw [← cubeMap_succ hnn hkK x', e1]; exact h'Z
  have hψ : subMultiscaleField N (H.localHistory M K (m + 1 + 1) Z') (m + 1 + 1)
      (Vblk R (H.localHistory M K (m + 1 + 1) Z') (m + 1 + 1)) x o (m + 1) y =
      VarVal.toEuc (x ⟨⟨⟨⟨m + 1, hj⟩, VarKind.large, y⟩, hb⟩, newPrimeVars_sub _ _ hp⟩) := by
    classical
    unfold subMultiscaleField
    have hbl' : m + 1 = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) (m + 1) y
        ((H.localHistory M K (m + 1 + 1) Z').Omega (m + 1 - 1)) := Or.inr hbl
    simp only [Nat.lt_succ_self, hbl', ↓reduceIte]
    unfold subVarField
    have hex : ∃ hj' : m + 1 < m + 1 + 1, ∃ hb' : BlockSub (S := S) (n := n) (M := M) (K := K)
        (m + 1) y (varSet (H.localHistory M K (m + 1 + 1) Z') (m + 1) .large),
        mkVar (H.localHistory M K (m + 1 + 1) Z') (m + 1 + 1) (m + 1) .large y hj' hb' ∈
          newVars (H.localHistory M K (m + 1 + 1) Z') (m + 1) := ⟨hj, hb, rfl⟩
    simp only [hex, ↓reduceDIte]
    rfl
  have hCube : CubeSub (S := S) (n := n) M K (m + 1 + 1)
      (blockMap S.L (n (m + 1 + 1)) (blockCube S n M K (m + 1) y))
      ((H.localHistory M K (m + 1 + 1) Z').Z (m + 1 + 1)) := by
    intro x' hx'
    refine ⟨?_, ?_⟩
    · show cubeMap n S.L M K (m + 1 + 1) x' ∈ ((H.locRH (m + 1 + 1) Z').step (m + 1 + 1)).Z
      rw [locRH_Z Z' le_rfl, lin_self, hx']; exact h'Z
    · show cubeMap n S.L M K (m + 1 + 1) x' ∈ (Z'.1 : Set (Torus S.d (n (m + 1 + 1))))
      rw [hx']; exact h'Z
  have hdL' : (1 : ℝ) ≤ S.d * S.L := by exact_mod_cast hdL
  by_cases hom : blockMap S.L (n (m + 1 + 1)) (blockCube S n M K (m + 1) y) ∈
      omegaSim (H.localHistory M K (m + 1 + 1) Z') (m + 1 + 1) (m + 1 + 1)
  · -- first family
    have h1 := hchi.1 _ hCube hom
    have hmem : (⟨m + 1, y⟩ : BlockPt S n M K) ∈ genBlocksIn
        ((H.locRH (m + 1 + 1) Z').histGen (M := M) (locRH_rem (m + 1 + 1) Z')
          H.F.ok.two_le_L K (fun j _ _ => geo.hRlow j)) (m + 1 + 1)
        (nbhd 1 {blockMap S.L (n (m + 1 + 1)) (blockCube S n M K (m + 1) y)}) := by
      refine ⟨Nat.succ_pos m, hkK, x0, ?_, hx0, ?_⟩
      · rw [GeneratingSet.mem_layer]
        refine ⟨?_, ?_⟩
        · rw [(H.locRH (m + 1 + 1) Z').mem_histGen]
          exact ⟨hkK, by rw [hcube]; exact hΩk⟩
        · rw [(H.locRH (m + 1 + 1) Z').mem_histGen]
          rintro ⟨-, hO2⟩
          exact h'O (by rw [← hcube']; exact hO2)
      · rw [hcube']; exact subset_nbhd 1 _ rfl
    have h2 := h1.2 _ hmem
    simp only [hψ] at h2
    exact h2
  · -- second family
    have h2 := hchi.2.1 (m + 1) (Or.inl rfl) (blockCube S n M K (m + 1) y) ?_ ?_ ?_
    · have h3 := h2.2 _ ⟨y, rfl, x0, hx0, by rw [hcube]; exact subset_nbhd 1 _ rfl⟩
      simp only [hψ] at h3
      refine h3.trans_le ?_
      nlinarith
    · intro x' hx'
      show cubeMap n S.L M K (m + 1 + 1) x' ∈ (Z'.1 : Set (Torus S.d (n (m + 1 + 1))))
      rw [← cubeMap_succ hnn hkK x', hx']; exact h'Z
    · intro x' hx' hx''
      exact hnotZ (hx' ▸ hx''.1)
    · intro x' hx'
      rw [← cubeMap_succ hnn hkK x', hx']; exact hom

end Shell

end Balaban.LargeField
