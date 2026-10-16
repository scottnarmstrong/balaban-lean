module

public import Balaban.Polymer.TwoTorusResumLimit
public import Balaban.Polymer.TwoTorusResumInstance

/-!
# The limit resummation for a growing family of block tori (W849, blocker 7)

The family of Root-F tori has sides `ℓ = q M L^{k_f+1}`; the torus has `K = q` cells of the
last scale per side.  Tori are ordered by the number of cells per side, and a sequence `tor n` has
`K (tor n)` non-decreasing and tending to infinity.  For the supports `P ℓ` (polymers of the block
torus `Torus d (K ℓ)` in centred coordinates), the quarter box `Q ℓ` and the margin `τ ℓ`, the
order, cofinality, eventual-box and margin hypotheses of `resum_lastScale_limit` are proved, and
the space of the functions analytic on an open set is closed under bounded uniform limits.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset Filter Topology

namespace Balaban.Polymer

section Family

variable {d : ℕ} {ι : Type*}

/-- Monotonicity of the order `K ℓ ≤ K ℓ'` along the sequence. -/
theorem rootF_hmono (K : ι → ℕ) (tor : ℕ → ι) (hKm : ∀ m n, m ≤ n → K (tor m) ≤ K (tor n)) :
    ∀ m n, m ≤ n → (fun ℓ ℓ' => K ℓ ≤ K ℓ') (tor m) (tor n) := hKm

/-- Every torus is below `tor n` for large `n`. -/
theorem rootF_hcof (K : ι → ℕ) (tor : ℕ → ι)
    (hKt : Tendsto (fun n => K (tor n)) atTop atTop) :
    ∀ ℓ, ∀ᶠ n in atTop, (fun ℓ ℓ' => K ℓ ≤ K ℓ') ℓ (tor n) :=
  fun ℓ => hKt.eventually_ge_atTop (K ℓ)

/-- **The eventual box (W849).**  A support in the quarter box of a torus, read in centred
coordinates, is a polymer of the quarter box of every larger torus of the sequence. -/
theorem rootF_hev (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)] (hK : ∀ ℓ, 2 ≤ K ℓ) (tor : ℕ → ι)
    (hKt : Tendsto (fun n => K (tor n)) atTop atTop)
    (P : ι → Finset (Finset (Fin d → ℤ))) (Q : ι → Finset (Fin d → ℤ) → Prop)
    (hP : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
      X = Y.image (fun b μ => (b μ).valMinAbs))
    (hQ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4) :
    ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ∀ᶠ n in atTop, X ∈ P (tor n) ∧ Q (tor n) X := by
  intro ℓ X hX hQX
  filter_upwards [hKt.eventually_ge_atTop (K ℓ)] with n hn
  refine ⟨?_, (hQ _ _).2 fun x hx μ => ((hQ _ _).1 hQX x hx μ).trans (Nat.div_le_div_right hn)⟩
  obtain ⟨Y, hY, rfl⟩ := (hP ℓ _).1 hX
  have hbox : ∀ b ∈ Y, ∀ μ, (b μ).valMinAbs.natAbs ≤ K ℓ / 4 := fun b hb μ =>
    (hQ ℓ _).1 hQX _ (Finset.mem_image_of_mem _ hb) μ
  obtain ⟨Y', hY', h⟩ := quarterBox_polymer_larger (hK ℓ) hn hY hbox
  exact (hP _ _).2 ⟨Y', hY', h.symm⟩

/-- **The margin tends to infinity (W849).** -/
theorem rootF_hτ (K : ι → ℕ) (tor : ℕ → ι)
    (hKt : Tendsto (fun n => K (tor n)) atTop atTop)
    (τ : ι → Finset (Fin d → ℤ) → ℕ)
    (hτ : ∀ ℓ X, τ ℓ X = K ℓ / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs))
    (X : Finset (Fin d → ℤ)) :
    Tendsto (fun n => τ (tor n) X) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hKt.eventually_ge_atTop
    (4 * (b + X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs))))
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  rw [hτ]
  omega

/-- **Analytic functions on an open set are closed under bounded uniform limits (W849).**  The
hypothesis `hWlim` of `resum_lastScale_limit` for `W` the space of the functions analytic on an
open set `D`. -/
theorem hWlim_analytic {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] (D : Set G)
    (hD : IsOpen D) (W : Submodule ℂ (G → ℂ)) (hW : ∀ f, f ∈ W ↔ AnalyticOnNhd ℂ f D) :
    ∀ (f : ℕ → G → ℂ) (F : G → ℂ) (M : ℝ), (∀ᶠ n in atTop, f n ∈ W) →
      (∀ᶠ n in atTop, ∀ g ∈ D, ‖f n g‖ ≤ M) → TendstoUniformlyOn f F atTop D → F ∈ W :=
  fun f F M hf hM hu => analytic_closed_under_uniform_limit D hD W hW f F M hf hM hu

end Family

end Balaban.Polymer
