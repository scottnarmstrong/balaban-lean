module

public import Balaban.LargeField.Budget.LogC
public import Balaban.LargeField.Budget.KeySum

/-!
# The summability (1.27) (Part II, Lemma II.5.15)

For `L^d ≥ 8`, every scale `k ≤ K` and every set `Y` of `π_k`-cubes,
`∑_{a ∈ 𝔥_k(Y)} C_k(a)^{-1} ≤ 1`, where `𝔥_k(Y)` (`histSet`) is the set of all localized
histories `localHistory H M K k Y` of components `Y` of region histories `H`, and
`C_k(a) = exp (a.logC k)` (Definition II.5.11, `LocalHistory.logC`).

Proof (as in the document): induction on `k`.  The map
`a ↦ (Z_k ∩ Z', (P, Q, R, S)_{k+1} ∩ Z', (localized histories of the components of Z_k ∩ Z'))`
is injective (`localHistory_succ_eq`), the weights multiply (`logC_succ`), the localized histories of
the old parts are summed by the induction hypothesis, and the four new-cube families range over
subsets of the `π_{k+1}`-cubes of `Z'` outside the cubes of `Z_k` (they avoid `U'_k ⊇ Z_k^↑`);
the remaining sum is `KeySum.sum_powerset_le_one`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

section KeyCubes

variable (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)]

open Classical in
/-- The `π_k`-cubes over a set `Y'` of `π_{k+1}`-cubes. -/
noncomputable def overCubes (k : ℕ) (Y' : Finset (Torus S.d (n (k + 1)))) :
    Finset (Torus S.d (n k)) :=
  Finset.univ.filter fun x => blockMap S.L (n (k + 1)) x ∈ Y'

open Classical in
/-- The cubes of `Y'` whose `π_k`-children avoid the set `Sx` of `π_k`-cubes. -/
noncomputable def freeCubes (k : ℕ) (Y' : Finset (Torus S.d (n (k + 1))))
    (Sx : Finset (Torus S.d (n k))) : Finset (Torus S.d (n (k + 1))) :=
  Y'.filter fun y => ∀ x ∈ Sx, blockMap S.L (n (k + 1)) x ≠ y

open Classical in
/-- The cubes of `Y'` lying in a set `X` of `π_{k+1}`-cubes. -/
noncomputable def newOf {k : ℕ} (X : Set (Torus S.d (n (k + 1)))) (Y' : Finset (Torus S.d (n (k + 1)))) :
    Finset (Torus S.d (n (k + 1))) :=
  Y'.filter fun y => y ∈ X

variable {S n}

theorem mem_newOf {k : ℕ} {X : Set (Torus S.d (n (k + 1)))} {Y' : Finset (Torus S.d (n (k + 1)))}
    {y : Torus S.d (n (k + 1))} : y ∈ newOf S n X Y' ↔ y ∈ Y' ∧ y ∈ X := by
  classical
  simp [newOf]

theorem card_overCubes {k : ℕ} (hnn : n k = S.L * n (k + 1)) (Y' : Finset (Torus S.d (n (k + 1)))) :
    (overCubes S n k Y').card = S.L ^ S.d * Y'.card :=
  card_preimage_blockMap hnn Y'

theorem free_bound {k : ℕ} (hnn : n k = S.L * n (k + 1)) (Y' : Finset (Torus S.d (n (k + 1))))
    {Sx : Finset (Torus S.d (n k))} (hSx : Sx ⊆ overCubes S n k Y') :
    S.L ^ S.d * (freeCubes S n k Y' Sx).card + Sx.card ≤ (overCubes S n k Y').card := by
  classical
  have h1 := card_preimage_blockMap (d := S.d) hnn (freeCubes S n k Y' Sx)
  have hsub : (Finset.univ.filter fun x : Torus S.d (n k) =>
      blockMap S.L (n (k + 1)) x ∈ freeCubes S n k Y' Sx) ⊆ overCubes S n k Y' \ Sx := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [freeCubes, Finset.mem_filter] at hx
    refine Finset.mem_sdiff.mpr ⟨?_, fun hxS => hx.2 x hxS rfl⟩
    simp only [overCubes, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hx.1
  have h2 := Finset.card_le_card hsub
  rw [h1, Finset.card_sdiff_of_subset hSx] at h2
  have := Finset.card_le_card hSx
  omega

end KeyCubes

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  (H : RegionHistory S n R k0)

open Classical in
/-- The cubes of `Z_k` over a set `Y'` of `π_{k+1}`-cubes. -/
noncomputable def oldOf (k : ℕ) (Y' : Finset (Torus S.d (n (k + 1)))) :
    Finset (Torus S.d (n k)) :=
  Finset.univ.filter fun x => x ∈ (H.step k).Z ∧ blockMap S.L (n (k + 1)) x ∈ Y'

theorem oldCubes_eq_oldOf (k : ℕ) (Z' : H.Comp (k + 1)) : H.oldCubes k Z' = H.oldOf k Z'.1 := rfl

theorem oldOf_subset (k : ℕ) (Y' : Finset (Torus S.d (n (k + 1)))) :
    H.oldOf k Y' ⊆ overCubes S n k Y' := by
  classical
  intro x hx
  simp only [oldOf, overCubes, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact hx.2

/-- A new cube of the step into scale `k+1` has no child in `Z_k`. -/
theorem newCube_free (k : ℕ) (Y' : Finset (Torus S.d (n (k + 1))))
    {X : Set (Torus S.d (n (k + 1)))} (hX : X ⊆ (H.step k).newCubes) :
    newOf S n X Y' ⊆ freeCubes S n k Y' (H.oldOf k Y') := by
  classical
  intro y hy
  rw [mem_newOf] at hy
  simp only [freeCubes, Finset.mem_filter]
  refine ⟨hy.1, fun x hx hxy => ?_⟩
  simp only [oldOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  have hU : blockMap S.L (n (k + 1)) x ∈ (H.step k).Uprime := (H.step k).blockMap_Z_subset_Uprime hx.1
  rw [hxy] at hU
  exact Set.disjoint_left.mp (H.step k).newCubes_disjoint_Uprime (hX hy.2) hU

end RegionHistory

section KeySpace

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- The first-level data of a localized history: the cubes of `Z_k` over `Z'` and the four
families `(P, Q, R, S)_{k+1} ∩ Z'`. -/
abbrev Key (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (k : ℕ) : Type :=
  Σ _ : Finset (Torus S.d (n k)),
    Finset (Torus S.d (n (k + 1))) × Finset (Torus S.d (n (k + 1))) ×
      Finset (Torus S.d (n (k + 1))) × Finset (Torus S.d (n (k + 1)))

/-- The possible first-level data over `Z'`: `S₀` a set of `π_k`-cubes over `Z'`, and the four new-cube
families subsets of the `π_{k+1}`-cubes of `Z'` with no child in `S₀`. -/
noncomputable def keySpace (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (k : ℕ)
    (Y' : Finset (Torus S.d (n (k + 1)))) : Finset (Key S n k) :=
  (overCubes S n k Y').powerset.sigma fun S0 =>
    (freeCubes S n k Y' S0).powerset ×ˢ ((freeCubes S n k Y' S0).powerset ×ˢ
      ((freeCubes S n k Y' S0).powerset ×ˢ (freeCubes S n k Y' S0).powerset))

/-- The numerical sum over the first-level data: `∑ e^{-n₁ - (5/4) n₂} 2^{4 n₂ / L^d} ≤ 1`. -/
theorem sum_keySpace_le_one {k : ℕ} (hnn : n k = S.L * n (k + 1)) (hLd : 8 ≤ S.L ^ S.d)
    (Y' : Finset (Torus S.d (n (k + 1)))) :
    ∑ κ ∈ keySpace S n k Y',
      Real.exp (-((5 * ((S.L : ℝ) ^ S.d * Y'.card) - κ.1.card) / 4)) ≤ 1 := by
  classical
  unfold keySpace
  rw [Finset.sum_sigma]
  have hF : ((overCubes S n k Y').card : ℝ) = (S.L : ℝ) ^ S.d * Y'.card := by
    rw [card_overCubes hnn]; push_cast; rfl
  have h := sum_powerset_le_one (overCubes S n k Y') (u := (S.L : ℝ) ^ S.d)
    (by exact_mod_cast hLd) (fun S0 => (freeCubes S n k Y' S0).card) (by
      intro S0 hS0
      have hS0' := Finset.mem_powerset.mp hS0
      have := free_bound hnn Y' hS0'
      have h' : (((S.L ^ S.d * (freeCubes S n k Y' S0).card + S0.card : ℕ)) : ℝ) ≤
          ((overCubes S n k Y').card : ℝ) := by exact_mod_cast this
      push_cast at h'
      linarith)
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun S0 _ => ?_
  simp only [Finset.sum_const, Finset.card_product, Finset.card_powerset, nsmul_eq_mul]
  rw [hF]
  push_cast
  ring_nf

end KeySpace

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  (H : RegionHistory S n R k0) {M K : ℕ} [NeZero M]

instance : Inhabited (LocalHistory S n M K) :=
  ⟨⟨fun _ => ∅, fun _ => ∅, fun _ => ∅, fun _ => ∅, fun _ => ∅, fun _ => ∅, fun _ => ∅,
    fun _ => ∅⟩⟩

open Classical in
/-- The localized history of the component `Y` of `Z^pre_k` (the empty record if `Y` is not a
component). -/
noncomputable def subHist (M K k : ℕ) [NeZero M] (Y : Finset (Torus S.d (n k))) :
    LocalHistory S n M K :=
  if h : Y ∈ comps (S.omega k) (H.Zp k) then localHistory H M K k ⟨Y, h⟩ else default

theorem subHist_of_mem {k : ℕ} {Y : Finset (Torus S.d (n k))}
    (h : Y ∈ comps (S.omega k) (H.Zp k)) : H.subHist M K k Y = localHistory H M K k ⟨Y, h⟩ := by
  classical
  simp [subHist, h]

/-- `logC_succ`, summed over the components of `Z_k ∩ Z'`. -/
theorem logC_succ_comps {k : ℕ} (hkK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) :
    (localHistory H M K (k + 1) Z').logC (k + 1) =
      ∑ Y ∈ comps (S.omega k) (H.oldCubes k Z'), (H.subHist M K k Y).logC k +
        (5 * ((S.L : ℝ) ^ S.d * Z'.1.card) - (H.oldCubes k Z').card) / 4 := by
  rw [H.logC_succ hkK Z', ← H.parts_image_eq_comps k Z', Finset.sum_image
    (fun _ _ _ _ h => Subtype.val_injective h)]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [H.subHist_of_mem c.2]

end RegionHistory

/-- The set `𝔥_k(Y)` of localized histories of the component `Y` of `Z^pre_k`, over all region
histories (on the given tori, with the given radii) in which `Y` is a component. -/
def histSet (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (R : ℕ → ℝ) (k0 M K k : ℕ) [NeZero M]
    (Y : Finset (Torus S.d (n k))) : Set (RegionHistory.LocalHistory S n M K) :=
  {a | ∃ (H : RegionHistory S n R k0) (hY : Y ∈ comps (S.omega k) (H.Zp k)),
    a = RegionHistory.localHistory H M K k ⟨Y, hY⟩}

theorem inter_eq_of_newOf_eq {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {k : ℕ}
    {X X' : Set (Torus S.d (n (k + 1)))} {Y' : Finset (Torus S.d (n (k + 1)))}
    (h : newOf S n X Y' = newOf S n X' Y') : X ∩ (Y' : Set _) = X' ∩ (Y' : Set _) := by
  ext x
  have := Finset.ext_iff.mp h x
  rw [mem_newOf, mem_newOf] at this
  simp only [Set.mem_inter_iff, Finset.mem_coe]
  constructor
  · rintro ⟨hx, hy⟩; exact ⟨(this.mp ⟨hy, hx⟩).2, hy⟩
  · rintro ⟨hx, hy⟩; exact ⟨(this.mpr ⟨hy, hx⟩).2, hy⟩

section Main

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]

open RegionHistory in
/-- **Lemma II.5.15 (the summability (1.27) for localized histories)**, for `L^d ≥ 8`: for every
scale `k ≤ K`, every set `Y` of `π_k`-cubes and every finite set `A` of localized histories of
the component `Y` (of region histories `H`, with the four new-cube families `P, Q, R, S` at every
scale), `∑_{a ∈ A} C_k(a)^{-1} ≤ 1`, where `C_k(a) = exp (a.logC k)`
(Definition II.5.11).  In particular, over the whole set `𝔥_k(Y)` (`histSet`). -/
theorem sum_inv_logC_le_one (hLd : 8 ≤ S.L ^ S.d) :
    ∀ (k : ℕ), k ≤ K → ∀ (Y : Finset (Torus S.d (n k))) (A : Finset (LocalHistory S n M K)),
      (∀ a ∈ A, a ∈ histSet S n R k0 M K k Y) → ∑ a ∈ A, Real.exp (-(a.logC k)) ≤ 1 := by
  classical
  intro k
  induction k with
  | zero =>
    intro _ Y A hA
    have : A = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro a ha
      obtain ⟨H, hY, -⟩ := hA a ha
      obtain ⟨x, hx⟩ := comp_nonempty hY
      have := comp_subset hY hx
      have h0 : H.Zp 0 = ∅ := H.F.Zp_zero
      rw [h0] at this
      simp at this
    simp [this]
  | succ k ih =>
    intro hkK Y' A hA
    by_cases hAe : A = ∅
    · simp [hAe]
    obtain ⟨a0, ha0⟩ := Finset.nonempty_iff_ne_empty.mpr hAe
    obtain ⟨H0, -, -⟩ := hA a0 ha0
    have : Nonempty (RegionHistory S n R k0) := ⟨H0⟩
    have hex : ∀ a ∈ A, ∃ (H : RegionHistory S n R k0)
        (hY : Y' ∈ comps (S.omega (k + 1)) (H.Zp (k + 1))),
        a = localHistory H M K (k + 1) ⟨Y', hY⟩ := hA
    choose! wit hmem heq using hex
    have hnn : n k = S.L * n (k + 1) := H0.F.hnn k
    -- the first-level data of a localized history
    let key : LocalHistory S n M K → Key S n k := fun a =>
      ⟨(wit a).oldOf k Y', (newOf S n ((wit a).step k).P Y', newOf S n ((wit a).step k).Q Y',
        newOf S n ((wit a).step k).R Y', newOf S n ((wit a).step k).S Y')⟩
    have hKS : ∀ a ∈ A, key a ∈ keySpace S n k Y' := by
      intro a _
      simp only [keySpace, key, Finset.mem_sigma, Finset.mem_powerset, Finset.mem_product]
      exact ⟨(wit a).oldOf_subset k Y',
        (wit a).newCube_free k Y' (fun y hy => Or.inl (Or.inl (Or.inl hy))),
        (wit a).newCube_free k Y' (fun y hy => Or.inl (Or.inl (Or.inr hy))),
        (wit a).newCube_free k Y' (fun y hy => Or.inl (Or.inr hy)),
        (wit a).newCube_free k Y' (fun y hy => Or.inr hy)⟩
    have hfib : ∀ κ ∈ keySpace S n k Y',
        ∑ a ∈ A.filter (fun a => key a = κ), Real.exp (-(a.logC (k + 1))) ≤
          Real.exp (-((5 * ((S.L : ℝ) ^ S.d * Y'.card) - κ.1.card) / 4)) := by
      intro κ _
      set Φ := A.filter (fun a => key a = κ) with hΦ
      set I := comps (S.omega k) κ.1 with hI
      set t0 : ℝ := (5 * ((S.L : ℝ) ^ S.d * Y'.card) - κ.1.card) / 4 with ht0
      have hΦA : ∀ a ∈ Φ, a ∈ A ∧ key a = κ := fun a ha => Finset.mem_filter.mp ha
      -- the weights multiply
      have hwt : ∀ a ∈ Φ, Real.exp (-(a.logC (k + 1))) =
          Real.exp (-t0) * ∏ Y ∈ I, Real.exp (-(((wit a).subHist M K k Y).logC k)) := by
        intro a ha
        obtain ⟨haA, hak⟩ := hΦA a ha
        have hold : (wit a).oldCubes k ⟨Y', hmem a haA⟩ = κ.1 := by
          have := congrArg Sigma.fst hak
          exact this
        have h1 : a.logC (k + 1) = ∑ Y ∈ I, (((wit a).subHist M K k Y).logC k) + t0 := by
          conv_lhs => rw [heq a haA]
          rw [(wit a).logC_succ_comps hkK ⟨Y', hmem a haA⟩, hold]
        rw [h1, show -(∑ Y ∈ I, (((wit a).subHist M K k Y).logC k) + t0) =
          ∑ Y ∈ I, -(((wit a).subHist M K k Y).logC k) + -t0 by
            rw [Finset.sum_neg_distrib]; ring, Real.exp_add, Real.exp_sum, mul_comm]
      -- the sub-histories of the old parts
      have hIsub : ∀ a ∈ Φ, ∀ Y ∈ I, Y ∈ comps (S.omega k) ((wit a).Zp k) := by
        intro a ha Y hY
        obtain ⟨haA, hak⟩ := hΦA a ha
        have hold : (wit a).oldCubes k ⟨Y', hmem a haA⟩ = κ.1 := congrArg Sigma.fst hak
        rw [hI, ← hold, ← (wit a).parts_image_eq_comps k ⟨Y', hmem a haA⟩] at hY
        obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hY
        exact c.2
      let Ψ : LocalHistory S n M K → ∀ Y ∈ I, LocalHistory S n M K :=
        fun a Y _ => (wit a).subHist M K k Y
      let B : Finset (Torus S.d (n k)) → Finset (LocalHistory S n M K) :=
        fun Y => Φ.image fun a => (wit a).subHist M K k Y
      have hBsum : ∀ Y ∈ I, ∑ b ∈ B Y, Real.exp (-(b.logC k)) ≤ 1 := by
        intro Y hY
        refine ih (by omega) Y (B Y) ?_
        intro b hb
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        have hY' := hIsub a ha Y hY
        exact ⟨wit a, hY', (wit a).subHist_of_mem hY'⟩
      have hΨinj : Set.InjOn Ψ Φ := by
        intro a ha a' ha' hΨ
        obtain ⟨haA, hak⟩ := hΦA a ha
        obtain ⟨haA', hak'⟩ := hΦA a' ha'
        have hkk : key a = key a' := hak.trans hak'.symm
        have hS0 := congrArg Sigma.fst hkk
        obtain ⟨hP, hQ, hR, hS'⟩ : newOf S n ((wit a).step k).P Y' = newOf S n ((wit a').step k).P Y' ∧
            newOf S n ((wit a).step k).Q Y' = newOf S n ((wit a').step k).Q Y' ∧
            newOf S n ((wit a).step k).R Y' = newOf S n ((wit a').step k).R Y' ∧
            newOf S n ((wit a).step k).S Y' = newOf S n ((wit a').step k).S Y' := by
          have h2 := (Sigma.mk.inj_iff.mp hkk).2
          simp only [heq_eq_eq, Prod.mk.injEq] at h2
          exact h2
        have hold : (wit a).oldCubes k ⟨Y', hmem a haA⟩ = (wit a').oldCubes k ⟨Y', hmem a' haA'⟩ :=
          hS0
        have hmain := localHistory_succ_eq hkK ⟨Y', hmem a haA⟩ ⟨Y', hmem a' haA'⟩ rfl hold
          (inter_eq_of_newOf_eq hP) (inter_eq_of_newOf_eq hQ) (inter_eq_of_newOf_eq hR)
          (inter_eq_of_newOf_eq hS') (by
            intro Y h1 h2 hY
            have hYI : Y ∈ I := by
              rw [hI, ← hak]
              exact hY
            have := congrFun (congrFun hΨ Y) hYI
            simp only [Ψ] at this
            rw [(wit a).subHist_of_mem h1, (wit a').subHist_of_mem h2] at this
            exact this)
        rw [heq a haA, heq a' haA']
        exact hmain
      have hsub : Φ.image Ψ ⊆ I.pi B := by
        intro p hp
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
        exact Finset.mem_pi.mpr fun Y _ => Finset.mem_image.mpr ⟨a, ha, rfl⟩
      calc ∑ a ∈ Φ, Real.exp (-(a.logC (k + 1)))
          = Real.exp (-t0) * ∑ a ∈ Φ, ∏ Y ∈ I.attach, Real.exp (-((Ψ a Y.1 Y.2).logC k)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a ha => ?_
            rw [hwt a ha, Finset.prod_attach I
              (fun Y => Real.exp (-(((wit a).subHist M K k Y).logC k)))]
        _ = Real.exp (-t0) * ∑ p ∈ Φ.image Ψ, ∏ Y ∈ I.attach, Real.exp (-((p Y.1 Y.2).logC k)) := by
            rw [Finset.sum_image hΨinj]
        _ ≤ Real.exp (-t0) * ∑ p ∈ I.pi B, ∏ Y ∈ I.attach, Real.exp (-((p Y.1 Y.2).logC k)) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun _ _ _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le))
              (Real.exp_pos _).le
        _ = Real.exp (-t0) * ∏ Y ∈ I, ∑ b ∈ B Y, Real.exp (-(b.logC k)) := by
            rw [Finset.prod_sum]
        _ ≤ Real.exp (-t0) * 1 :=
            mul_le_mul_of_nonneg_left (Finset.prod_le_one₀
              (fun _ _ => Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) hBsum)
              (Real.exp_pos _).le
        _ = Real.exp (-t0) := mul_one _
    calc ∑ a ∈ A, Real.exp (-(a.logC (k + 1)))
        = ∑ κ ∈ keySpace S n k Y', ∑ a ∈ A.filter (fun a => key a = κ),
            Real.exp (-(a.logC (k + 1))) := (Finset.sum_fiberwise_of_maps_to hKS _).symm
      _ ≤ ∑ κ ∈ keySpace S n k Y',
            Real.exp (-((5 * ((S.L : ℝ) ^ S.d * Y'.card) - κ.1.card) / 4)) :=
          Finset.sum_le_sum hfib
      _ ≤ 1 := sum_keySpace_le_one hnn hLd Y'

end Main

end Balaban.LargeField
