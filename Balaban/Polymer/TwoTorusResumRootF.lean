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

section Assembly

variable {d : ℕ} {ι : Type*}

/-- **The pairwise closeness in the form of the limit (W849).**  The closeness of two block tori
of the form delivered by `finalCoef_close_quarterBox` (smaller torus first, with its margin, bound
`Pc (C₀ e^{-c₀ Mr (2τ - 7)} + ε) / (e^{κ₁} - 1)^{|X|}`) gives the bound
`a e^{-lam τ} e^{-κ' |X|}`, `a = Pc (C₀ e^{7 c₀ Mr} + ε₁)`, of `lastScale_limit`. -/
theorem rootF_hcoef_limit {G : Type*} (K : ι → ℕ) (P : ι → Finset (Finset (Fin d → ℤ)))
    (Q : ι → Finset (Fin d → ℤ) → Prop) (sz : Finset (Fin d → ℤ) → ℕ)
    (τ : ι → Finset (Fin d → ℤ) → ℕ) (D : Set G) (T : ι → G → Finset (Fin d → ℤ) → ℂ)
    {κ' κ₁ lam Pc C₀ c₀ Mr ε₁ : ℝ} {t₀ : ℕ} (ε : ι → G → Finset (Fin d → ℤ) → ℝ)
    (hPc : 0 ≤ Pc) (hC : 0 ≤ C₀) (hκ₁ : 0 < κ₁) (hκ'₁ : κ' ≤ Real.log (Real.exp κ₁ - 1))
    (hlamc : lam ≤ 2 * c₀ * Mr)
    (hcoef : ∀ ℓ ℓ' X, X ∈ P ℓ → Q ℓ X → X ∈ P ℓ' → K ℓ ≤ K ℓ' → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      ‖T ℓ g X - T ℓ' g X‖ ≤
        Pc * (C₀ * Real.exp (-c₀ * (Mr * (2 * (τ ℓ X : ℝ) - 7))) + ε ℓ g X) /
          (Real.exp κ₁ - 1) ^ sz X)
    (hε0 : ∀ ℓ g X, 0 ≤ ε ℓ g X)
    (hε : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      ε ℓ g X ≤ ε₁ * Real.exp (-lam * (τ ℓ X : ℝ))) :
    ∀ ℓ ℓ', (fun ℓ ℓ' => K ℓ ≤ K ℓ') ℓ ℓ' → ∀ X, X ∈ P ℓ → Q ℓ X → X ∈ P ℓ' → Q ℓ' X →
      t₀ ≤ τ ℓ X → ∀ g ∈ D, ‖T ℓ' g X - T ℓ g X‖ ≤
        (Pc * (C₀ * Real.exp (7 * c₀ * Mr) + ε₁)) * Real.exp (-lam * (τ ℓ X : ℝ)) *
          Real.exp (-κ' * (sz X : ℝ)) := by
  intro ℓ ℓ' hle X hX hQX hX' _ ht g hg
  rw [norm_sub_rev]
  exact (hcoef ℓ ℓ' X hX hQX hX' hle ht g hg).trans
    (quarterBox_rate hPc hC hκ₁ hκ'₁ hlamc (hε0 ℓ g X) (hε ℓ X hX hQX ht g hg))

end Assembly

section Assembled

variable {d : ℕ} {ι : Type*}

/-- **The limit resummation for a growing family of block tori (W849, blocker 7).**
`resum_lastScale_limit` for the supports `P ℓ` of the block torus `Torus d (K ℓ)` (centred
coordinates), the quarter box `Q ℓ`, `sz X = |X|`, the margin `τ`, the chain map `Φ` of
`lastScale_chain`, the order `K ℓ ≤ K ℓ'`, and a sequence of tori `tor n` with `K (tor n)`
non-decreasing and unbounded.  The new terms equal the limit `V g X = lim_n T (tor n) g X` on the
quarter box of every torus.  The physical inputs are the hypotheses on `T`: support, locality,
analyticity (`han`, with `W` the functions analytic on the open set `D`), the bound `hbd`, and the
closeness `hcoef` of two tori (the form of `finalCoef_close_quarterBox`: smaller torus first, its
margin) together with the decay `hε` of the closeness `ε` of the operators on the support. -/
theorem resum_lastScale_torus_limit {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)] (hd : 0 < d)
    (hK : ∀ ℓ, 2 ≤ K ℓ) (P : ι → Finset (Finset (Fin d → ℤ)))
    (Q : ι → Finset (Fin d → ℤ) → Prop) (sz : Finset (Fin d → ℤ) → ℕ)
    (τ : ι → Finset (Fin d → ℤ) → ℕ) (tor : ℕ → ι) (D : Set G) (hD : IsOpen D)
    (W : Submodule ℂ (G → ℂ)) (hW : ∀ f, f ∈ W ↔ AnalyticOnNhd ℂ f D)
    (R : Finset (Fin d → ℤ) → Prop)
    (Ag : Finset (Fin d → ℤ) → G → G → Prop) (T : ι → G → Finset (Fin d → ℤ) → ℂ)
    {B κ κ' κ₁ lam Pc C₀ c₀ Mr ε₁ : ℝ} {t₀ : ℕ} (ε : ι → G → Finset (Fin d → ℤ) → ℝ)
    (hKm : ∀ m n, m ≤ n → K (tor m) ≤ K (tor n))
    (hKt : Tendsto (fun n => K (tor n)) atTop atTop)
    (hP : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
      X = Y.image (fun b μ => (b μ).valMinAbs))
    (hQ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
    (hsz : ∀ X, sz X = X.card)
    (hτ : ∀ ℓ X, τ ℓ X = K ℓ / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs))
    (hR : ∀ ℓ X, X ∈ P ℓ → R X)
    (hAg : ∀ X Z, X ⊆ Z → ∀ g g', Ag Z g g' → Ag X g g')
    (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hκ' : κ + Real.log 2 ≤ κ') (hlam : κ' ≤ lam) (hPc : 0 ≤ Pc) (hC : 0 ≤ C₀) (hε₁ : 0 ≤ ε₁)
    (hκ₁ : 0 < κ₁) (hκ'₁ : κ' ≤ Real.log (Real.exp κ₁ - 1)) (hlamc : lam ≤ 2 * c₀ * Mr)
    (hsupp : ∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, T ℓ g X = 0)
    (hloc : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → T ℓ g X = T ℓ g' X)
    (han : ∀ ℓ X, X ∈ P ℓ → (fun g => T ℓ g X) ∈ W)
    (hbd : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖T ℓ g X‖ ≤ B * Real.exp (-κ' * (sz X : ℝ)))
    (hcoef : ∀ ℓ ℓ' X, X ∈ P ℓ → Q ℓ X → X ∈ P ℓ' → K ℓ ≤ K ℓ' → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      ‖T ℓ g X - T ℓ' g X‖ ≤
        Pc * (C₀ * Real.exp (-c₀ * (Mr * (2 * (τ ℓ X : ℝ) - 7))) + ε ℓ g X) /
          (Real.exp κ₁ - 1) ^ sz X)
    (hε0 : ∀ ℓ g X, 0 ≤ ε ℓ g X)
    (hε : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      ε ℓ g X ≤ ε₁ * Real.exp (-lam * (τ ℓ X : ℝ))) :
    ∃ Φ : ι → Finset (Fin d → ℤ) → Finset (Fin d → ℤ),
    ∃ V : G → Finset (Fin d → ℤ) → ℂ,
      (∀ g X, V g X = limUnder atTop (fun n => T (tor n) g X)) ∧
      ∃ Tn : ι → G → Finset (Fin d → ℤ) → ℂ,
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ⊆ Φ ℓ X) ∧
      (∀ ℓ g X, Tn ℓ g X = if Q ℓ X then V g X else
        T ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - V g X₀)) ∧
      (∀ ℓ g, ∑ X ∈ P ℓ, Tn ℓ g X = ∑ X ∈ P ℓ, T ℓ g X) ∧
      (∀ ℓ ℓ' g X, Q ℓ X → Q ℓ' X → Tn ℓ g X = Tn ℓ' g X) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖Tn ℓ g X‖ ≤
        (B + (Pc * (C₀ * Real.exp (7 * c₀ * Mr) + ε₁)) * Real.exp κ' +
          2 * B * Real.exp (κ' * (t₀ : ℝ))) * Real.exp (-κ * (sz X : ℝ))) ∧
      (∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, Tn ℓ g X = 0) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → Tn ℓ g X = Tn ℓ g' X) ∧
      (∀ ℓ X, X ∈ P ℓ → (fun g => Tn ℓ g X) ∈ W) := by
  obtain ⟨Φ, hsub, hΦP, hΦsz, hfib, hRΦ, hAgΦ⟩ :=
    lastScale_chain K hd hK P Q sz τ R Ag hP hQ hsz hτ hR hAg
  have hlim := rootF_hcoef_limit K P Q sz τ D T ε hPc hC hκ₁ hκ'₁ hlamc hcoef hε0 hε
  obtain ⟨V, hV, Tn, h⟩ := resum_lastScale_limit P Q sz τ Φ D W R Ag T tor
    (fun ℓ ℓ' => K ℓ ≤ K ℓ') hB (by positivity) hκ hκ' hlam hΦP hΦsz
    (fun ℓ Z => by convert hfib ℓ Z) hRΦ hAgΦ hsupp hloc han hbd (rootF_hmono K tor hKm)
    (rootF_hcof K tor hKt) (rootF_hev K hK tor hKt P Q hP hQ) (fun ℓ X _ _ => rootF_hτ K tor hKt τ hτ X)
    hlim (hWlim_analytic D hD W hW)
  refine ⟨Φ, V, hV, Tn, hsub, ?_⟩
  convert h

end Assembled

section RootFSides

/-- **Root-F's tori as block tori (W849).**  The admissible sides of Root-F are the multiples
`ℓ = q s` of `s = M L^{k_f+1}`; the torus has `K = ℓ / s = q` cells of the last scale per side.
For sides `side ℓ` that are multiples of `s` with `2 s ≤ side ℓ`, the number of cells
`K ℓ = side ℓ / s` is at least `2` (hence nonzero), satisfies `K ℓ * s = side ℓ`, and for a
sequence of tori whose sides are non-decreasing and unbounded, `K (tor n)` is non-decreasing and
tends to infinity: the hypotheses `hK`, `hKm`, `hKt` of `resum_lastScale_torus_limit`. -/
theorem rootF_cells {ι : Type*} {s : ℕ} (hs : 0 < s) (side : ι → ℕ) (tor : ℕ → ι)
    (hdvd : ∀ ℓ, s ∣ side ℓ) (hbig : ∀ ℓ, 2 * s ≤ side ℓ)
    (hsm : ∀ m n, m ≤ n → side (tor m) ≤ side (tor n))
    (hst : Tendsto (fun n => side (tor n)) atTop atTop) :
    (∀ ℓ, 2 ≤ side ℓ / s) ∧ (∀ ℓ, side ℓ / s * s = side ℓ) ∧
      (∀ m n, m ≤ n → side (tor m) / s ≤ side (tor n) / s) ∧
      Tendsto (fun n => side (tor n) / s) atTop atTop := by
  refine ⟨fun ℓ => ?_, fun ℓ => Nat.div_mul_cancel (hdvd ℓ), fun m n h =>
    Nat.div_le_div_right (hsm m n h), ?_⟩
  · rw [Nat.le_div_iff_mul_le hs]
    exact hbig ℓ
  · rw [tendsto_atTop_atTop] at hst ⊢
    intro b
    obtain ⟨N, hN⟩ := hst (b * s)
    exact ⟨N, fun n hn => (Nat.le_div_iff_mul_le hs).2 (hN n hn)⟩

end RootFSides

end Balaban.Polymer
