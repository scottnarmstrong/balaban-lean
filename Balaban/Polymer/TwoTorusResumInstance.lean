module

public import Balaban.Polymer.TwoTorusResum
public import Balaban.Polymer.BoxTransport
public import Balaban.Green.FinalTermBound

/-!
# The chain, fibre and order hypotheses of the last-scale resummation (W846, blocker 7)

Instance of `resum_lastScale_of_quarterBox` (W845) for the block tori `Torus d (K ℓ)`.  The cells
of different tori are identified through their centred coordinates `(b μ).valMinAbs : ℤ`; a
support is a finite set of cells `Fin d → ℤ`.  The quarter box of `ℓ` is the set of cells with
every centred coordinate of absolute value at most `K ℓ / 4`; the margin of a support `X` is
`K ℓ / 4` minus the largest absolute coordinate of `X`.  For each support the chain of the
margin's length of `exists_edgeChain_map` (W843) is chosen; the map `Φ ℓ` so obtained is a
function of the support alone, with `X ⊆ Φ ℓ X`, hence its fibres have at most `2 ^ |Z|`
elements and the rate condition is the one of the abstract resummation, `κ + log 2 ≤ κ'`,
with no further loss.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

section Chain

variable {d : ℕ}

theorem valMinAbs_cells_injective {K : ℕ} [NeZero K] :
    Function.Injective (fun (b : Balaban.Torus d K) (μ : Fin d) => (b μ).valMinAbs) := by
  intro b b' h
  funext μ
  have h1 := congrFun h μ
  simp only at h1
  rw [← ZMod.coe_valMinAbs (b μ), ← ZMod.coe_valMinAbs (b' μ), h1]

theorem preimage_image_cells {K : ℕ} [NeZero K] (Y : Finset (Balaban.Torus d K)) :
    (Finset.univ : Finset (Balaban.Torus d K)).filter
      (fun b => (fun μ => (b μ).valMinAbs) ∈ Y.image (fun b μ => (b μ).valMinAbs)) = Y := by
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨b', hb', h⟩
    rw [valMinAbs_cells_injective h] at hb'
    exact hb'
  · intro hb
    exact ⟨b, hb, rfl⟩

theorem natAbs_valMinAbs_le_iff {K : ℕ} [NeZero K] (a : ZMod K) (r : ℕ) :
    a.valMinAbs.natAbs ≤ r ↔ a.val ≤ r ∨ K - r ≤ a.val := by
  have h := ZMod.val_lt a
  rw [ZMod.valMinAbs_natAbs_eq_min]
  omega

theorem lt_natAbs_valMinAbs_iff {K : ℕ} [NeZero K] (a : ZMod K) (r : ℕ) :
    r < a.valMinAbs.natAbs ↔ r < a.val ∧ a.val < K - r := by
  have h := ZMod.val_lt a
  rw [ZMod.valMinAbs_natAbs_eq_min]
  omega

/-- **The chain map of one torus, with the margin as length (W846).**  For `K ≥ 2` and `d > 0`
there is a map `Φ₀` on sets of cells such that for every polymer `Y` of cells of centred
coordinates at most `K / 4`, `Φ₀ Y` is a polymer containing `Y`, with at most
`K / 4 - rad Y + 1` more cells, and with a cell of centred coordinate larger than `K / 4`;
here `rad Y` is the largest absolute centred coordinate of `Y`. -/
theorem chain_torus {K : ℕ} [NeZero K] (hd : 0 < d) (hK : 2 ≤ K) :
    ∃ Φ₀ : Finset (Balaban.Torus d K) → Finset (Balaban.Torus d K),
      ∀ Y : Finset (Balaban.Torus d K), IsAnimal (blockGraph d K) Y →
        (∀ b ∈ Y, ∀ μ, (b μ).valMinAbs.natAbs ≤ K / 4) →
        Y ⊆ Φ₀ Y ∧ IsAnimal (blockGraph d K) (Φ₀ Y) ∧
          (Φ₀ Y).card ≤ Y.card +
            (K / 4 - Y.sup (fun b => Finset.univ.sup fun μ => (b μ).valMinAbs.natAbs) + 1) ∧
          ∃ b ∈ Φ₀ Y, ∃ μ : Fin d, K / 4 < (b μ).valMinAbs.natAbs := by
  have hK' : 2 * (K / 4) + 2 ≤ K := by omega
  choose Ψ hΨ1 _ using fun t : ℕ => exists_edgeChain_map (d := d) (K := K) (r := K / 4) (t := t) hK'
  refine ⟨fun Y => Ψ (K / 4 - Y.sup (fun b => Finset.univ.sup fun μ =>
    (b μ).valMinAbs.natAbs)) Y, fun Y hY hbox => ?_⟩
  set rad := Y.sup (fun b => Finset.univ.sup fun μ => (b μ).valMinAbs.natAbs) with hrad
  have hne : Y.Nonempty := ((isAnimal_iff _ _).1 hY).1
  obtain ⟨b0, hb0, hb0e⟩ := Finset.exists_mem_eq_sup Y hne
    (fun b => Finset.univ.sup fun μ => (b μ).valMinAbs.natAbs)
  obtain ⟨μ₀, -, hμ₀⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
    ⟨⟨0, hd⟩, Finset.mem_univ _⟩ (fun μ => (b0 μ).valMinAbs.natAbs)
  have hm : (b0 μ₀).valMinAbs.natAbs = rad := by rw [hrad, hb0e, hμ₀]
  have hmr : rad ≤ K / 4 := by
    rw [← hm]; exact hbox b0 hb0 μ₀
  have hboxv : ∀ b ∈ Y, ∀ μ, (b μ).val ≤ K / 4 ∨ K - K / 4 ≤ (b μ).val := fun b hb μ =>
    (natAbs_valMinAbs_le_iff _ _).1 (hbox b hb μ)
  have hnear : ∃ b0 ∈ Y, ∃ μ₀ : Fin d, (((b0 μ₀).val ≤ K / 4 ∧ K / 4 ≤ (b0 μ₀).val +
        (K / 4 - rad)) ∨ (K - K / 4 ≤ (b0 μ₀).val ∧ K / 4 ≤ K - (b0 μ₀).val + (K / 4 - rad))) := by
    refine ⟨b0, hb0, μ₀, ?_⟩
    have h1 := ZMod.val_lt (b0 μ₀)
    rw [ZMod.valMinAbs_natAbs_eq_min] at hm
    omega
  obtain ⟨h1, h2, h3, b, hb, μ, h4, h5⟩ := hΨ1 (K / 4 - rad) Y hY hboxv hnear
  refine ⟨h1, h2, by omega, b, hb, μ, ?_⟩
  exact (lt_natAbs_valMinAbs_iff _ _).2 ⟨h4, h5⟩

/-- **The chain, fibre and support hypotheses of the last-scale resummation (W846, blocker 7).**
For the supports `P ℓ` = polymers of the torus `Torus d (K ℓ)` read in centred coordinates
(`hP`), the quarter box `Q ℓ` (`hQ`: every centred coordinate at most `K ℓ / 4` in absolute
value), size `sz X = |X|` and margin `τ ℓ X = K ℓ / 4 - (largest absolute coordinate of X)`, there
is one map `Φ ℓ` with `X ⊆ Φ ℓ X` on the polymers of the quarter box, satisfying the hypotheses
`hΦP`, `hΦsz`, `hfib`, `hRΦ`, `hAgΦ` of `resum_lastScale`.  The support predicate `R` is
implied by being a polymer (`hR`) and the agreement `Ag` decreases with the set (`hAg`). -/
theorem lastScale_chain {ι G : Type*} (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)] (hd : 0 < d)
    (hK : ∀ ℓ, 2 ≤ K ℓ) (P : ι → Finset (Finset (Fin d → ℤ)))
    (Q : ι → Finset (Fin d → ℤ) → Prop) (sz : Finset (Fin d → ℤ) → ℕ)
    (τ : ι → Finset (Fin d → ℤ) → ℕ) (R : Finset (Fin d → ℤ) → Prop)
    (Ag : Finset (Fin d → ℤ) → G → G → Prop)
    (hP : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
      X = Y.image (fun b μ => (b μ).valMinAbs))
    (hQ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
    (hsz : ∀ X, sz X = X.card)
    (hτ : ∀ ℓ X, τ ℓ X = K ℓ / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs))
    (hR : ∀ ℓ X, X ∈ P ℓ → R X)
    (hAg : ∀ X Z, X ⊆ Z → ∀ g g', Ag Z g g' → Ag X g g') :
    ∃ Φ : ι → Finset (Fin d → ℤ) → Finset (Fin d → ℤ),
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ⊆ Φ ℓ X) ∧
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → Φ ℓ X ∈ P ℓ ∧ ¬ Q ℓ (Φ ℓ X)) ∧
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → sz (Φ ℓ X) ≤ sz X + τ ℓ X + 1) ∧
      (∀ ℓ Z, (((P ℓ).filter (Q ℓ)).filter (fun X => Φ ℓ X = Z)).card ≤ 2 ^ sz Z) ∧
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → R X → R (Φ ℓ X)) ∧
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → ∀ g g', Ag (Φ ℓ X) g g' → Ag X g g') := by
  choose Φ₀ hΦ₀ using fun ℓ => chain_torus (d := d) (K := K ℓ) hd (hK ℓ)
  let Φ : ι → Finset (Fin d → ℤ) → Finset (Fin d → ℤ) := fun ℓ X =>
    (Φ₀ ℓ ((Finset.univ : Finset (Balaban.Torus d (K ℓ))).filter
      (fun b => (fun μ => (b μ).valMinAbs) ∈ X))).image (fun b μ => (b μ).valMinAbs)
  -- the data of a support in the quarter box
  have key : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ∃ Y : Finset (Balaban.Torus d (K ℓ)),
      Y ⊆ Φ₀ ℓ Y ∧ IsAnimal (blockGraph d (K ℓ)) (Φ₀ ℓ Y) ∧
      (Φ₀ ℓ Y).card ≤ Y.card + (K ℓ / 4 -
        Y.sup (fun b => Finset.univ.sup fun μ => (b μ).valMinAbs.natAbs) + 1) ∧
      (∃ b ∈ Φ₀ ℓ Y, ∃ μ : Fin d, K ℓ / 4 < (b μ).valMinAbs.natAbs) ∧
      X = Y.image (fun b μ => (b μ).valMinAbs) ∧ Φ ℓ X = (Φ₀ ℓ Y).image (fun b μ => (b μ).valMinAbs) ∧
      Y.card = X.card ∧ τ ℓ X = K ℓ / 4 -
        Y.sup (fun b => Finset.univ.sup fun μ => (b μ).valMinAbs.natAbs) := by
    intro ℓ X hX hQX
    obtain ⟨Y, hY, rfl⟩ := (hP ℓ _).1 hX
    have hbox : ∀ b ∈ Y, ∀ μ, (b μ).valMinAbs.natAbs ≤ K ℓ / 4 := fun b hb μ =>
      (hQ ℓ _).1 hQX _ (Finset.mem_image_of_mem _ hb) μ
    obtain ⟨h1, h2, h3, h4⟩ := hΦ₀ ℓ Y hY hbox
    refine ⟨Y, h1, h2, h3, h4, rfl, ?_, ?_, ?_⟩
    · show (Φ₀ ℓ _).image _ = _
      rw [preimage_image_cells]
    · exact (Finset.card_image_of_injective _ valMinAbs_cells_injective).symm
    · rw [hτ, Finset.sup_image]
      rfl
  have hsub : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ⊆ Φ ℓ X := by
    intro ℓ X hX hQX
    obtain ⟨Y, h1, -, -, -, rfl, hΦ, -⟩ := key ℓ X hX hQX
    rw [hΦ]
    exact Finset.image_subset_image h1
  have hΦP : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → Φ ℓ X ∈ P ℓ ∧ ¬ Q ℓ (Φ ℓ X) := by
    intro ℓ X hX hQX
    obtain ⟨Y, -, h2, -, ⟨b, hb, μ, hbμ⟩, -, hΦ, -⟩ := key ℓ X hX hQX
    rw [hΦ]
    refine ⟨(hP ℓ _).2 ⟨_, h2, rfl⟩, fun hq => ?_⟩
    have := (hQ ℓ _).1 hq _ (Finset.mem_image_of_mem _ hb) μ
    omega
  refine ⟨Φ, hsub, hΦP, ?_, ?_, ?_, ?_⟩
  · intro ℓ X hX hQX
    obtain ⟨Y, -, -, h3, -, -, hΦ, hc, hτX⟩ := key ℓ X hX hQX
    rw [hsz, hsz, hτX, hΦ, Finset.card_image_of_injective _ valMinAbs_cells_injective, ← hc]
    exact h3
  · intro ℓ Z
    have hsubZ : ((P ℓ).filter (Q ℓ)).filter (fun X => Φ ℓ X = Z) ⊆ Z.powerset := by
      intro X hX
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hX
      obtain ⟨hP', hQ'⟩ := Finset.mem_filter.1 h1
      rw [Finset.mem_powerset, ← h2]
      exact hsub ℓ X hP' hQ'
    rw [hsz]
    exact (Finset.card_le_card hsubZ).trans (by rw [Finset.card_powerset])
  · intro ℓ X hX hQX _
    exact hR ℓ _ (hΦP ℓ X hX hQX).1
  · intro ℓ X hX hQX g g' hg
    exact hAg X _ (hsub ℓ X hX hQX) g g' hg

theorem inBox_iff_natAbs {K r : ℕ} (c : Balaban.Torus d K) :
    InBox d r K c ↔ ∀ μ, (c μ).valMinAbs.natAbs ≤ r := by
  unfold InBox
  refine forall_congr' fun μ => ?_
  rw [Int.abs_eq_natAbs]
  exact_mod_cast Iff.rfl

/-- **A polymer of the quarter box of `K` is a polymer of every larger torus (W846).**  The set
of centred coordinates of a polymer of `Torus d K` inside the box of radius `K / 4` is also the
set of centred coordinates of a polymer of `Torus d K'`, `K ≤ K'`, `2 ≤ K`. -/
theorem quarterBox_polymer_larger {K K' : ℕ} [NeZero K] [NeZero K'] (hK : 2 ≤ K)
    (hKK' : K ≤ K') {Y : Finset (Balaban.Torus d K)} (hY : IsAnimal (blockGraph d K) Y)
    (hbox : ∀ b ∈ Y, ∀ μ, (b μ).valMinAbs.natAbs ≤ K / 4) :
    ∃ Y' : Finset (Balaban.Torus d K'), IsAnimal (blockGraph d K') Y' ∧
      Y'.image (fun b μ => (b μ).valMinAbs) = Y.image (fun b μ => (b μ).valMinAbs) := by
  have hm : 2 * (K / 4) + 1 < K := by omega
  have hm' : 2 * (K / 4) + 1 < K' := by omega
  have hin : ∀ c ∈ Y, InBox d (K / 4) K c := fun c hc => (inBox_iff_natAbs c).2 (hbox c hc)
  refine ⟨Y.image (boxMap K K'), isAnimal_image_boxMap hm hm' hin hY, ?_⟩
  rw [Finset.image_image]
  refine Finset.image_congr fun c hc => ?_
  funext μ
  exact valMinAbs_boxMap hm' (hin c hc) μ

/-- **The resummation of the last-scale terms on the block tori (W846, blocker 7).**  The
theorem `resum_lastScale_of_quarterBox` (W845) for the supports `P ℓ` of the torus `ℓ`
(polymers of `Torus d (K ℓ)` in centred coordinates), the quarter box `Q ℓ`, `sz X = |X|` and the
margin `τ ℓ X = K ℓ / 4 - (largest absolute coordinate of X)`, with the chain map `Φ` constructed
(`lastScale_chain`) and the canonical torus `can X` required to be at least as large as every `ℓ`
for which `X` lies in the quarter box (`hcanK`; then `X ∈ P (can X)` is a theorem).  The
closeness `hcoef` is the bound of `finalCoef_close_quarterBox` in its own order: the smaller torus
`ℓ` first (`K ℓ ≤ K ℓ'`), with the margin of the smaller torus.  The rate condition is
`κ + log 2 ≤ κ'` as in `resum_lastScale`: the fibres of `Φ ℓ` have at most `2 ^ |Z|` elements
because `Φ ℓ X` depends on `X` only and contains `X`, so the variable length of the chains costs
nothing. -/
theorem resum_lastScale_torus {ι G : Type*} (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)] (hd : 0 < d)
    (hK : ∀ ℓ, 2 ≤ K ℓ) (P : ι → Finset (Finset (Fin d → ℤ)))
    (Q : ι → Finset (Fin d → ℤ) → Prop) (sz : Finset (Fin d → ℤ) → ℕ)
    (τ : ι → Finset (Fin d → ℤ) → ℕ) (can : Finset (Fin d → ℤ) → ι) (D : Set G)
    (W : Submodule ℂ (G → ℂ)) (R : Finset (Fin d → ℤ) → Prop)
    (Ag : Finset (Fin d → ℤ) → G → G → Prop) (T : ι → G → Finset (Fin d → ℤ) → ℂ)
    {B κ κ' κ₁ lam Pc C₀ c₀ Mr ε₁ : ℝ} {t₀ : ℕ} (ε : ι → G → Finset (Fin d → ℤ) → ℝ)
    (hP : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
      X = Y.image (fun b μ => (b μ).valMinAbs))
    (hQ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
    (hsz : ∀ X, sz X = X.card)
    (hτ : ∀ ℓ X, τ ℓ X = K ℓ / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs))
    (hR : ∀ ℓ X, X ∈ P ℓ → R X)
    (hAg : ∀ X Z, X ⊆ Z → ∀ g g', Ag Z g g' → Ag X g g')
    (hcanK : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → K ℓ ≤ K (can X))
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
    ∃ Tn : ι → G → Finset (Fin d → ℤ) → ℂ,
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ⊆ Φ ℓ X) ∧
      (∀ ℓ g X, Tn ℓ g X = if Q ℓ X then T (can X) g X else
        T ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - T (can X₀) g X₀)) ∧
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
  have hcanP : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ∈ P (can X) := by
    intro ℓ X hX hQX
    obtain ⟨Y, hY, rfl⟩ := (hP ℓ _).1 hX
    have hbox : ∀ b ∈ Y, ∀ μ, (b μ).valMinAbs.natAbs ≤ K ℓ / 4 := fun b hb μ =>
      (hQ ℓ _).1 hQX _ (Finset.mem_image_of_mem _ hb) μ
    obtain ⟨Y', hY', h⟩ := quarterBox_polymer_larger (hK ℓ) (hcanK ℓ _ hX hQX) hY hbox
    exact (hP _ _).2 ⟨Y', hY', h.symm⟩
  obtain ⟨Tn, h⟩ := resum_lastScale_of_quarterBox P Q sz τ Φ can D W R Ag T ε hB hκ hκ' hlam hPc hC
    hε₁ hκ₁ hκ'₁ hlamc hcanP hΦP hΦsz (fun ℓ Z => by convert hfib ℓ Z) hRΦ hAgΦ hsupp hloc han hbd
    (fun ℓ X hX hQX ht g hg => hcoef ℓ (can X) X hX hQX (hcanP ℓ X hX hQX)
      (hcanK ℓ X hX hQX) ht g hg) hε0 hε
  refine ⟨Φ, Tn, hsub, ?_⟩
  convert h

end Chain

section Rate

/-- **The rates of the crude bound and of the closeness (W846).**  If `0 ≤ κ'` and
`2 e^{κ'} + 2 ≤ e^{κ₁}` then `3 < e^{κ₁}`, `0 < κ₁`, and `κ'` is at most both
`log ((e^{κ₁} - 1) / 2)` (the rate of `detRatioCoef_decay`) and `log (e^{κ₁} - 1)` (the rate
of `quarterBox_rate`). -/
theorem rate_of_kappa_large {κ' κ₁ : ℝ} (hκ' : 0 ≤ κ') (h : 2 * Real.exp κ' + 2 ≤ Real.exp κ₁) :
    3 < Real.exp κ₁ ∧ 0 < κ₁ ∧ κ' ≤ Real.log ((Real.exp κ₁ - 1) / 2) ∧
      κ' ≤ Real.log (Real.exp κ₁ - 1) := by
  have h1 : 1 ≤ Real.exp κ' := Real.one_le_exp hκ'
  have h3 : 3 < Real.exp κ₁ := by linarith
  have hκ₁ : 0 < κ₁ := by
    by_contra hc
    have := Real.exp_le_one_iff.2 (not_lt.1 hc)
    linarith
  have h4 : Real.exp κ' ≤ (Real.exp κ₁ - 1) / 2 := by linarith
  have h5 : κ' ≤ Real.log ((Real.exp κ₁ - 1) / 2) := by
    rw [← Real.log_exp κ']
    exact Real.log_le_log (Real.exp_pos _) h4
  refine ⟨h3, hκ₁, h5, h5.trans (Real.log_le_log (by linarith) (by linarith))⟩

/-- Such a `κ₁` exists. -/
theorem exists_kappa_large (κ' : ℝ) : ∃ κ₁ : ℝ, 2 * Real.exp κ' + 2 ≤ Real.exp κ₁ :=
  ⟨Real.log (2 * Real.exp κ' + 2), by
    rw [Real.exp_log (by positivity)]⟩

/-- **The crude bound with the rate `κ'` (W846).**  A coefficient with `n` cells and
`‖c‖ ≤ 2 n D / (e^{κ₁} - 1)^n` (the form delivered by the determinant-ratio estimate) satisfies
`‖c‖ ≤ 2 D e^{-κ' n}` for `0 ≤ κ'` and `2 e^{κ'} + 2 ≤ e^{κ₁}`. -/
theorem detRatioCoef_decay_rate {κ' κ₁ D c : ℝ} {n : ℕ} (hκ' : 0 ≤ κ') (hD : 0 ≤ D)
    (h : 2 * Real.exp κ' + 2 ≤ Real.exp κ₁)
    (hc : ‖c‖ ≤ 2 * n * D / (Real.exp κ₁ - 1) ^ n) :
    ‖c‖ ≤ 2 * D * Real.exp (-κ' * n) := by
  obtain ⟨h3, -, h5, -⟩ := rate_of_kappa_large hκ' h
  refine (Balaban.Green.detRatioCoef_decay h3 hD hc).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith

end Rate

end Balaban.Polymer
