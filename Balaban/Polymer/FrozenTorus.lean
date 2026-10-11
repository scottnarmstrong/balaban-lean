module

public import Balaban.Polymer.Bridge

/-!
# The polymer expansion in the frozen language

`pe_blockTorus_frozen` restates `pe_blockTorus` for the frozen geometry: polymers are the
`X : Finset (Torus d (s * m))` with `Balaban.IsPolymer d (s * m) s X`, their size is the number of
blocks `X.card / s ^ d`, and the local terms are indexed by the polymers.  The local term of `X`
is `frozenPY K X`, the local term `P(Y)` of the block-torus expansion for the set `Y` of blocks of
`X`.  Locality of `frozenPY` is `frozenPY_congr`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

variable (d s m : ℕ) [NeZero s] [NeZero m]

/-- The activities of the block-torus expansion obtained from activities on site sets. -/
def blockActivity (K : Finset (Balaban.Torus d (s * m)) → ℂ) :
    BlockPolymer (blockGraph d m) → ℂ := fun Z => K (siteSet d s m Z.1)

/-- The local term of a polymer `X` of the torus `Torus d (s * m)`: the local term of its set of
blocks. -/
def frozenPY (K : Finset (Balaban.Torus d (s * m)) → ℂ) (X : Finset (Balaban.Torus d (s * m))) : ℂ :=
  PY (overlap (blockGraph d m)) (fun Z => Z.1) (blockActivity d s m K) (X.image (blockOf d s m))

variable {d s m}

/-- Locality of the local term in the frozen language. -/
theorem frozenPY_congr {K K' : Finset (Balaban.Torus d (s * m)) → ℂ}
    {X : Finset (Balaban.Torus d (s * m))} (hX : Balaban.IsPolymer d (s * m) s X)
    (h : ∀ X', Balaban.IsPolymer d (s * m) s X' → X' ⊆ X → K X' = K' X') :
    frozenPY d s m K X = frozenPY d s m K' X := by
  unfold frozenPY
  refine PY_congr _ _ _ (fun Z hZ => ?_)
  unfold blockActivity
  refine h _ ((isPolymer_siteSet_iff _).mpr Z.2) ?_
  intro x hx
  rw [mem_siteSet] at hx
  have := hZ hx
  rw [Finset.mem_image] at this
  obtain ⟨x', hx', hxx⟩ := this
  exact hX.2.1 x' hx' x ((blockOf_eq_iff d s m x' x).mp hxx)

/-- The polymer expansion on the torus `Torus d (s * m)` for the frozen polymers (unions of blocks
of side `s`, nearest-neighbour connected), with decay in the number of blocks `|X| / s ^ d`. -/
theorem pe_blockTorus_frozen {ε κ κ' α : ℝ} (hε : 0 ≤ ε) (hκ' : 0 ≤ κ')
    (hq : ((2 * d : ℕ) : ℝ) ^ 2 * Real.exp (-(κ - κ' - α)) < 1)
    (hcond : ε * Real.exp (-(κ - κ' - α)) /
      (1 - ((2 * d : ℕ) : ℝ) ^ 2 * Real.exp (-(κ - κ' - α))) ≤ α)
    (K : Finset (Balaban.Torus d (s * m)) → ℂ)
    (hK : ∀ X, Balaban.IsPolymer d (s * m) s X →
      ‖K X‖ ≤ ε * Real.exp (-κ * ((X.card : ℝ) / (s : ℝ) ^ d))) :
    Xi (overlap (blockGraph d m)) (blockActivity d s m K) =
        Complex.exp (logSeries (overlap (blockGraph d m)) (blockActivity d s m K)) ∧
    logSeries (overlap (blockGraph d m)) (blockActivity d s m K) =
      ∑ X ∈ (Finset.univ : Finset (Finset (Balaban.Torus d (s * m)))).filter
        (Balaban.IsPolymer d (s * m) s), frozenPY d s m K X ∧
    (∀ x : Balaban.Torus d (s * m),
      ∑ X ∈ (Finset.univ : Finset (Finset (Balaban.Torus d (s * m)))).filter
          (fun X => Balaban.IsPolymer d (s * m) s X ∧ x ∈ X),
        ‖frozenPY d s m K X‖ * Real.exp (κ' * ((X.card : ℝ) / (s : ℝ) ^ d)) ≤ α) ∧
    ‖logSeries (overlap (blockGraph d m)) (blockActivity d s m K)‖ ≤ (m : ℝ) ^ d * α := by
  have hK' : ∀ Z : BlockPolymer (blockGraph d m),
      ‖blockActivity d s m K Z‖ ≤ ε * Real.exp (-κ * Z.1.card) := fun Z => by
    have hp : Balaban.IsPolymer d (s * m) s (siteSet d s m Z.1) :=
      (isPolymer_siteSet_iff _).mpr Z.2
    refine (hK _ hp).trans (le_of_eq ?_)
    rw [card_div_eq _ hp.2.1, image_siteSet]
  have main := pe_blockTorus d m hε hκ' hq hcond (blockActivity d s m K) hK'
  obtain ⟨h1, h2, h3, h4⟩ := main
  refine ⟨h1, ?_, ?_, ?_⟩
  · -- the sum over all `Y` reduces to the sum over polymers
    rw [h2]
    have hz : ∀ Y ∈ (Finset.univ : Finset (Finset (Balaban.Torus d m))),
        Y ∉ (Finset.univ : Finset (Finset (Balaban.Torus d m))).filter
          (IsAnimal (blockGraph d m)) →
        PY (overlap (blockGraph d m)) (fun Z => Z.1) (blockActivity d s m K) Y = 0 := by
      intro Y _ hY
      exact PY_eq_zero_of_not_isAnimal _ Y (by simpa using hY)
    rw [← Finset.sum_subset (Finset.filter_subset _ _) hz]
    refine Finset.sum_nbij' (fun Y => siteSet d s m Y) (fun X => X.image (blockOf d s m))
      ?_ ?_ ?_ ?_ ?_
    · intro Y hY
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY ⊢
      exact (isPolymer_siteSet_iff Y).mpr hY
    · intro X hX
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX ⊢
      exact isAnimal_image_blockOf hX
    · intro Y _
      exact image_siteSet Y
    · intro X hX
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
      exact siteSet_image_blockOf hX.2.1
    · intro Y _
      unfold frozenPY
      rw [image_siteSet]
  · intro x
    have hb := h3 (blockOf d s m x)
    refine le_trans ?_ hb
    have hinj : Set.InjOn (fun X : Finset (Balaban.Torus d (s * m)) => X.image (blockOf d s m))
        ↑((Finset.univ : Finset (Finset (Balaban.Torus d (s * m)))).filter
          (fun X => Balaban.IsPolymer d (s * m) s X ∧ x ∈ X)) := by
      intro X hX X' hX' h
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hX hX'
      rw [← siteSet_image_blockOf hX.1.2.1, ← siteSet_image_blockOf hX'.1.2.1]
      exact congrArg _ h
    have hsum := Finset.sum_image (f := fun Y : Finset (Balaban.Torus d m) =>
        ‖PY (overlap (blockGraph d m)) (fun Z => Z.1) (blockActivity d s m K) Y‖ *
          Real.exp (κ' * (Y.card : ℝ))) hinj
    calc _ = ∑ X ∈ (Finset.univ : Finset (Finset (Balaban.Torus d (s * m)))).filter
          (fun X => Balaban.IsPolymer d (s * m) s X ∧ x ∈ X),
          ‖PY (overlap (blockGraph d m)) (fun Z => Z.1) (blockActivity d s m K)
            (X.image (blockOf d s m))‖ *
          Real.exp (κ' * ((X.image (blockOf d s m)).card : ℝ)) := by
          refine Finset.sum_congr rfl (fun X hX => ?_)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
          rw [card_div_eq _ hX.1.2.1]
          rfl
      _ = _ := hsum.symm
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro Y hY
          rw [Finset.mem_image] at hY
          obtain ⟨X, hX, rfl⟩ := hY
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX ⊢
          exact Finset.mem_image_of_mem _ hX.2
  · refine h4.trans (le_of_eq ?_)
    simp [ZMod.card]

end Balaban.Polymer
