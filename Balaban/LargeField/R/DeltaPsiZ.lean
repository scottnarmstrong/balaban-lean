module

public import Balaban.LargeField.R.ChainCH
public import Balaban.LargeField.R.DeltaPsiPath
public import Balaban.LargeField.R.DeltaPsiDef
public import Balaban.LargeField.R.FineBox
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The component `Z` is one box of `k`-blocks (Part III, Lemma III.1.2 (d), used in Lemma III.4.6)

For a ripe component `Z` of scale `k` covered by one box of side `≤ crit_k` (`RipeWindow.unique_box`),
the set of cubes of `Z` is exactly a box of side `≤ crit_k` (`ancestor_box_crit`), hence the set of
`k`-blocks over `Z` is a box of `M s_i` blocks in direction `i`, and any two of its blocks are joined
inside `Z` by at most `d M crit_k` nearest-neighbour steps (`zblocks_reach`): the monotone path of the
source ("a monotone path inside the box `Z`", P7 p. 509).  `psi0_dist_le` bounds a field in `Ψ̃(U; θ)`
along such a path.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Multiscale

section Bound

variable {d m : ℕ} [NeZero m] {N : ℕ}

/-- A block field in `Ψ̃(U; θ)` changes by at most `n θ` along an `n`-step path inside `U`. -/
theorem psi0_dist_le {U P : Set (Torus d m)} (hP : P ⊆ U)
    {f : Torus d m → EuclideanSpace ℝ (Fin N)} {θ : ℝ} (hθ : 0 < θ) (hf : PsiTildeSet U f θ)
    {β β' : Torus d m} {n : ℕ} (hr : ReachIn torusAdj P β β' n) : dist (f β) (f β') ≤ n * θ := by
  refine reach_dist_le f (fun x hx y hy hadj => ?_) hr
  by_cases he : x = y
  · subst he; simp [hθ.le]
  · rw [dist_eq_norm]
    exact (hf.1 x (hP hx) y (hP hy) ⟨he, hadj⟩).le

end Bound

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} {k : ℕ} {Z : H.Comp k} [NeZero S.L] [NeZero S.M]

/-- `ancestor_box` with the side bound `s_i ≤ crit_q` (Lemma III.1.2 (d): `Z` is one box of side
`≤ crit_k`). -/
theorem ancestor_box_crit {q : ℕ} (hq1 : 1 ≤ q) (hq0 : q ≤ k0) {Y : H.Comp q}
    (hcov : CoveredBy S n q Y.1 1) (hn : 2 * S.crit q < n q) :
    ∃ (a : Torus S.d (n q)) (s : Fin S.d → ℕ), ((Y.1 : Finset (Torus S.d (n q))) : Set (Torus S.d (n q))) = box a s ∧
      ∀ i, 1 ≤ s i ∧ 2 * s i < n q ∧ s i ≤ S.crit q := by
  classical
  obtain ⟨B, hB, hs, hsub⟩ := hcov
  obtain ⟨y0, hy0⟩ := comp_nonempty Y.2
  have hy0' := hsub (show y0 ∈ ((Y.1 : Finset (Torus S.d (n q))) : Set _) from hy0)
  simp only [Set.mem_iUnion, exists_prop] at hy0'
  obtain ⟨b0, hb0, -⟩ := hy0'
  have hBsingle : ∀ b ∈ B, b = b0 := by
    intro b hb
    have : B.card ≤ 1 := hB
    exact Finset.card_le_one.mp this b hb b0 hb0
  have hYb : ∀ x ∈ ((Y.1 : Finset (Torus S.d (n q))) : Set _), x ∈ box b0.1 b0.2 := by
    intro x hx
    have := hsub hx
    simp only [Set.mem_iUnion, exists_prop] at this
    obtain ⟨b, hb, hxb⟩ := this
    rwa [hBsingle b hb] at hxb
  have hsmall : IsSmall ((Y.1 : Finset (Torus S.d (n q))) : Set (Torus S.d (n q))) := by
    intro i
    refine ⟨b0.1 i, b0.2 i, ?_, fun x hx => ?_⟩
    · have := hs b0 hb0 i; omega
    · obtain ⟨j, hj, hxj⟩ := hYb x hx i
      exact ⟨j, hj, hxj⟩
  have hside : side ((Y.1 : Finset (Torus S.d (n q))) : Set (Torus S.d (n q))) ≤ S.crit q := by
    unfold side
    refine Finset.sup_le fun i _ => ?_
    refine (ncard_hullCoord_le (a := b0.1 i) (s := b0.2 i) (by have := hs b0 hb0 i; omega)
      (fun x hx => ?_)).trans (hs b0 hb0 i)
    obtain ⟨j, hj, hxj⟩ := hYb x hx i
    exact ⟨j, hj, hxj⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hY : Y.1 ∈ comps (S.omega (q' + 1)) (finOf (hullClosure (S.omega (q' + 1)) (S.crit (q' + 1))
      (H.step q').Z0)) := by
    have h := Y.2
    have hcrit : critOpt S k0 (q' + 1) = some (S.crit (q' + 1)) := by
      simp [critOpt, hq0]
    change Y.1 ∈ comps (S.omega (q' + 1)) (finOf ((H.step q').Zpre (S.omega (q' + 1))
      (critOpt S k0 (q' + 1)))) at h
    rw [hcrit] at h
    exact h
  have hω : 2 ≤ S.omega (q' + 1) := by have := L_add_eleven_le_omega S (q' + 1); omega
  have hbox := hullClosure_box hω _ hY hsmall hside
  obtain ⟨a, s, hh, hs', hsd⟩ := hull_eq_box (X := ((Y.1 : Finset (Torus S.d (n (q' + 1)))) : Set _))
    ⟨y0, hy0⟩ hsmall
  refine ⟨a, s, hbox.trans hh, fun i => ⟨(hs' i).1, (hs' i).2, ?_⟩⟩
  have h1 : s i ≤ Finset.univ.sup s := Finset.le_sup (f := s) (Finset.mem_univ i)
  rw [← hsd] at h1
  exact h1.trans hside


/-- **`Z` is one box of `k`-blocks** (Lemma III.1.2 (d)): any two `k`-blocks over `Z` are joined by at
most `d M crit_k` nearest-neighbour steps through `k`-blocks over `Z`. -/
theorem zblocks_reach (hkK : k ≤ K) (hk1 : 1 ≤ k) (hk0 : k ≤ k0) (hW : H.RipeWindow k Z)
    (hn : 2 * S.crit k < n k) {β β' : Torus S.d (S.M * n k * S.L ^ (k - k))}
    (hβ : ∃ x ∈ H.locFine Z S.M k, jBlock S.d S.L (S.M * n k) k k x = β)
    (hβ' : ∃ x ∈ H.locFine Z S.M k, jBlock S.d S.L (S.M * n k) k k x = β') :
    ∃ m ≤ S.d * (S.M * S.crit k), ReachIn torusAdj
      {γ | ∃ x ∈ H.locFine Z S.M k, jBlock S.d S.L (S.M * n k) k k x = γ} β β' m := by
  classical
  have hcov : CoveredBy S n k Z.1 1 :=
    (hW.unique_box k Z (by have := hW.point.2.1; omega) (Desc.refl Z)).2.1
  obtain ⟨a, s, hbox, hs⟩ := ancestor_box_crit (H := H) hk1 hk0 hcov hn
  have hℓ : S.M * n k * S.L ^ (k - k) = S.M * n k := by simp
  set a' : Torus S.d (S.M * n k * S.L ^ (k - k)) :=
    fun c => (((S.M * (a c).val : ℕ)) : ZMod (S.M * n k * S.L ^ (k - k))) with ha'
  set s' : Fin S.d → ℕ := fun c => S.M * s c with hs'
  have hiff := fun γ : Torus S.d (S.M * n k * S.L ^ (k - k)) =>
    blockMap_mem_box_iff (d := S.d) (ℓ := S.M * n k * S.L ^ (k - k)) (N := S.M) (m := n k) hℓ a
      (s := s) γ
  have hset : {γ | ∃ x ∈ H.locFine Z S.M k, jBlock S.d S.L (S.M * n k) k k x = γ} = box a' s' := by
    ext γ
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : cubeMap n S.L S.M k k x ∈ Z.1 := (mem_locFine_k hkK).mp hx
      have h2 := cubeMap_eq_comp (hnn_k H hkK) le_rfl x
      have h3 : blockMap S.M (n k) (jBlock S.d S.L (S.M * n k) k k x) ∈ box a s := by
        rw [h2, ← hbox]; exact_mod_cast h1
      exact (hiff _).1 h3
    · intro hγ
      obtain ⟨x, hx⟩ := exists_site_of_block (d := S.d) (L := S.L) (N₀ := S.M * n k) (k := k)
        (j := k) le_rfl γ
      refine ⟨x, ?_, hx⟩
      rw [mem_locFine_k hkK]
      have h3 : blockMap S.M (n k) γ ∈ box a s := (hiff γ).2 hγ
      have h2 := cubeMap_eq_comp (hnn_k H hkK) le_rfl x
      rw [hx] at h2
      rw [← h2]
      rw [← hbox] at h3
      exact_mod_cast h3
  have hs'm : ∀ c, s' c ≤ S.M * n k * S.L ^ (k - k) := by
    intro c
    rw [hℓ]
    have := (hs c).2.1
    exact Nat.mul_le_mul_left _ (by omega)
  have hβb : β ∈ box a' s' := hset ▸ hβ
  have hβ'b : β' ∈ box a' s' := hset ▸ hβ'
  obtain ⟨m, hm, hr⟩ := box_reach hs'm hβb hβ'b
  refine ⟨m, hm.trans ?_, hset ▸ hr⟩
  calc ∑ c, (s' c - 1) ≤ ∑ _c : Fin S.d, (S.M * S.crit k) := by
        refine Finset.sum_le_sum fun c _ => ?_
        have := (hs c).2.2
        simp only [hs']
        have : S.M * s c ≤ S.M * S.crit k := Nat.mul_le_mul_left _ this
        omega
    _ = S.d * (S.M * S.crit k) := by simp

end RegionHistory

end Balaban.LargeField
