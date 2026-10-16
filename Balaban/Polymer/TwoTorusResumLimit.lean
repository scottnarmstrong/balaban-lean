module

public import Balaban.Polymer.TwoTorusResum
public import Balaban.Analysis.AnalyticLimit

/-!
# The last-scale terms as a limit over growing tori (W847, blocker 7)

The canonical value of the resummation `resum_lastScale_target` is the infinite-volume limit of the
terms `T (tor n) g X` along a sequence of tori `tor n`.  Given the closeness of two tori (the
smaller first, with the margin of the smaller), the sequence is Cauchy for every `g ∈ D`, its limit
`V g X` is within the closeness bound of every torus of the family, inherits the bound, the
support and the locality, and is a uniform limit on `D`, hence lies in any space `W` of functions
that is closed under bounded uniform limits on `D` (for instance the functions analytic on an open
set `D`, `analytic_closed_under_uniform_limit`).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset Filter Topology

namespace Balaban.Polymer

/-- **The limit over growing tori (W847).**  `tor : ℕ → ι` is a sequence of tori, `Le` an order on
tori with `Le (tor m) (tor n)` for `m ≤ n` and every torus below `tor n` for large `n`.  Every
support in the box of some torus lies in the box of all large `tor n` with margin tending to
infinity, and the terms of two tori are close with the margin of the smaller.  Then
`V g X := lim_n T (tor n) g X` exists on `D`, and satisfies the closeness to every torus of the
family, the bound, the support, the locality and the uniform convergence on `D`. -/
theorem lastScale_limit {ι G S : Type*} (P : ι → Finset S) (Q : ι → S → Prop) (sz : S → ℕ)
    (τ : ι → S → ℕ) (D : Set G) (R : S → Prop) (Ag : S → G → G → Prop) (T : ι → G → S → ℂ)
    (tor : ℕ → ι) (Le : ι → ι → Prop) {B a κ' lam : ℝ} {t₀ : ℕ} (hlam : 0 < lam)
    (hmono : ∀ m n, m ≤ n → Le (tor m) (tor n)) (hcof : ∀ ℓ, ∀ᶠ n in atTop, Le ℓ (tor n))
    (hev : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ∀ᶠ n in atTop, X ∈ P (tor n) ∧ Q (tor n) X)
    (hτ : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → Tendsto (fun n => τ (tor n) X) atTop atTop)
    (hsupp : ∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, T ℓ g X = 0)
    (hloc : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → T ℓ g X = T ℓ g' X)
    (hbd : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖T ℓ g X‖ ≤ B * Real.exp (-κ' * (sz X : ℝ)))
    (hcoef : ∀ ℓ ℓ', Le ℓ ℓ' → ∀ X, X ∈ P ℓ → Q ℓ X → X ∈ P ℓ' → Q ℓ' X → t₀ ≤ τ ℓ X →
      ∀ g ∈ D, ‖T ℓ' g X - T ℓ g X‖ ≤
        a * Real.exp (-lam * (τ ℓ X : ℝ)) * Real.exp (-κ' * (sz X : ℝ))) :
    ∃ V : G → S → ℂ, (∀ g X, V g X = limUnder atTop (fun n => T (tor n) g X)) ∧
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → ∀ g ∈ D, Tendsto (fun n => T (tor n) g X) atTop (𝓝 (V g X))) ∧
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
        ‖T ℓ g X - V g X‖ ≤
          a * Real.exp (-lam * (τ ℓ X : ℝ)) * Real.exp (-κ' * (sz X : ℝ))) ∧
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → ∀ g ∈ D, ‖V g X‖ ≤ B * Real.exp (-κ' * (sz X : ℝ))) ∧
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → TendstoUniformlyOn (fun n g => T (tor n) g X)
        (fun g => V g X) atTop D) ∧
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ R X → ∀ g, V g X = 0) ∧
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → ∀ g g', Ag X g g' → V g X = V g' X) := by
  set V : G → S → ℂ := fun g X => limUnder atTop (fun n => T (tor n) g X) with hV
  -- the rate sequence
  have hu : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → Tendsto (fun m => a * Real.exp (-lam * (τ (tor m) X : ℝ)) *
      Real.exp (-κ' * (sz X : ℝ))) atTop (𝓝 0) := by
    intro ℓ X hX hQ
    have h1 : Tendsto (fun m => -lam * (τ (tor m) X : ℝ)) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (by linarith)
        (tendsto_natCast_atTop_atTop.comp (hτ ℓ X hX hQ))
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul a
    have h3 := h2.mul_const (Real.exp (-κ' * (sz X : ℝ)))
    simpa using h3
  -- the sequence is Cauchy
  have hconv : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ∀ g ∈ D,
      Tendsto (fun n => T (tor n) g X) atTop (𝓝 (V g X)) := by
    intro ℓ X hX hQ g hg
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((hev ℓ X hX hQ).and
      ((hτ ℓ X hX hQ).eventually_ge_atTop t₀))
    have hcs : CauchySeq (fun n => T (tor n) g X) := by
      refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
      obtain ⟨m, hm1, hm2⟩ := ((hu ℓ X hX hQ).eventually (gt_mem_nhds hε)).and
        (eventually_ge_atTop N) |>.exists
      refine ⟨m, fun n hn => ?_⟩
      have h1 := hN m hm2
      have h2 := hN n (hm2.trans hn)
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (hcoef (tor m) (tor n) (hmono m n hn) X h1.1.1 h1.1.2 h2.1.1 h2.1.2
        h1.2 g hg) hm1
    obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcs
    have hVv : V g X = v := hv.limUnder_eq
    rw [hVv]
    exact hv
  have hclose : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      ‖T ℓ g X - V g X‖ ≤ a * Real.exp (-lam * (τ ℓ X : ℝ)) * Real.exp (-κ' * (sz X : ℝ)) := by
    intro ℓ X hX hQ ht g hg
    obtain ⟨ℓ0, hℓ0P, hℓ0Q⟩ : ∃ ℓ0, X ∈ P ℓ0 ∧ Q ℓ0 X := ⟨ℓ, hX, hQ⟩
    have hl := hconv ℓ X hX hQ g hg
    have h1 : Tendsto (fun n => ‖T (tor n) g X - T ℓ g X‖) atTop (𝓝 ‖V g X - T ℓ g X‖) :=
      (hl.sub_const _).norm
    have h2 : ‖V g X - T ℓ g X‖ ≤
        a * Real.exp (-lam * (τ ℓ X : ℝ)) * Real.exp (-κ' * (sz X : ℝ)) := by
      refine le_of_tendsto h1 ?_
      filter_upwards [hev ℓ X hX hQ, hcof ℓ] with n hn hle
      exact hcoef ℓ (tor n) hle X hX hQ hn.1 hn.2 ht g hg
    rwa [norm_sub_rev] at h2
  refine ⟨V, fun _ _ => rfl, hconv, hclose, ?_, ?_, ?_, ?_⟩
  · intro ℓ X hX hQ g hg
    refine le_of_tendsto (hconv ℓ X hX hQ g hg).norm ?_
    filter_upwards [hev ℓ X hX hQ] with n hn using hbd (tor n) X hn.1 g hg
  · intro ℓ X hX hQ
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((hev ℓ X hX hQ).and
      ((hτ ℓ X hX hQ).eventually_ge_atTop t₀))
    filter_upwards [(hu ℓ X hX hQ).eventually (gt_mem_nhds hε), eventually_ge_atTop N]
      with n hn1 hn2 g hg
    have h1 := hN n hn2
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt (hclose (tor n) X h1.1.1 h1.1.2 h1.2 g hg) hn1
  · intro ℓ X hX hQ hR g
    have : Tendsto (fun n => T (tor n) g X) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev ℓ X hX hQ] with n hn
      exact (hsupp (tor n) X hn.1 hR g).symm
    exact this.limUnder_eq
  · intro ℓ X hX hQ g g' hag
    have h : (fun n => T (tor n) g X) =ᶠ[atTop] (fun n => T (tor n) g' X) := by
      filter_upwards [hev ℓ X hX hQ] with n hn using hloc (tor n) X hn.1 g g' hag
    show limUnder atTop (fun n => T (tor n) g X) = limUnder atTop (fun n => T (tor n) g' X)
    unfold limUnder
    rw [Filter.map_congr h]

/-- **Bounded uniform limits of analytic functions (W847).**  If `D` is open and `W` is the space
of the functions analytic on `D`, then `W` is closed under limits that are eventually bounded on
`D` and uniform on `D`. -/
theorem analytic_closed_under_uniform_limit {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (D : Set G) (hD : IsOpen D) (W : Submodule ℂ (G → ℂ))
    (hW : ∀ f, f ∈ W ↔ AnalyticOnNhd ℂ f D) (f : ℕ → G → ℂ) (F : G → ℂ) (M : ℝ)
    (hf : ∀ᶠ n in atTop, f n ∈ W) (hM : ∀ᶠ n in atTop, ∀ g ∈ D, ‖f n g‖ ≤ M)
    (hu : TendstoUniformlyOn f F atTop D) : F ∈ W := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hf.and hM)
  rw [hW]
  refine Balaban.Analysis.analyticOnNhd_of_tendstoUniformlyOn (f := fun k => f (k + N)) hD
    (fun k => (hW _).1 (hN (k + N) (by omega)).1) (M := M)
    (fun k => (hN (k + N) (by omega)).2) ?_
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  exact (tendsto_add_atTop_nat N).eventually (hu ε hε)

/-- **The resummation with the limit as the value on the quarter box (W847).**  The assembly of
`lastScale_limit` and `resum_lastScale_target`: for the unbounded family of tori, the new terms
`Tn` equal the limit `V g X = lim_n T (tor n) g X` on the quarter box of every torus; they have
the same sum as `T`, and the bound, support, locality and membership in `W` of
`resum_lastScale`.  The space `W` is closed under bounded uniform limits on `D`
(`analytic_closed_under_uniform_limit` for the functions analytic on an open `D`). -/
theorem resum_lastScale_limit {ι G S : Type*} (P : ι → Finset S) (Q : ι → S → Prop) (sz : S → ℕ)
    (τ : ι → S → ℕ) (Φ : ι → S → S) (D : Set G) (W : Submodule ℂ (G → ℂ)) (R : S → Prop)
    (Ag : S → G → G → Prop) (T : ι → G → S → ℂ) (tor : ℕ → ι) (Le : ι → ι → Prop)
    {B a κ κ' lam : ℝ} {t₀ : ℕ} (hB : 0 ≤ B) (ha : 0 ≤ a) (hκ : 0 ≤ κ)
    (hκ' : κ + Real.log 2 ≤ κ') (hlam : κ' ≤ lam)
    (hΦP : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → Φ ℓ X ∈ P ℓ ∧ ¬ Q ℓ (Φ ℓ X))
    (hΦsz : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → sz (Φ ℓ X) ≤ sz X + τ ℓ X + 1)
    (hfib : ∀ ℓ Z, (((P ℓ).filter (Q ℓ)).filter (fun X => Φ ℓ X = Z)).card ≤ 2 ^ sz Z)
    (hRΦ : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → R X → R (Φ ℓ X))
    (hAgΦ : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ∀ g g', Ag (Φ ℓ X) g g' → Ag X g g')
    (hsupp : ∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, T ℓ g X = 0)
    (hloc : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → T ℓ g X = T ℓ g' X)
    (han : ∀ ℓ X, X ∈ P ℓ → (fun g => T ℓ g X) ∈ W)
    (hbd : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖T ℓ g X‖ ≤ B * Real.exp (-κ' * (sz X : ℝ)))
    (hmono : ∀ m n, m ≤ n → Le (tor m) (tor n)) (hcof : ∀ ℓ, ∀ᶠ n in atTop, Le ℓ (tor n))
    (hev : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ∀ᶠ n in atTop, X ∈ P (tor n) ∧ Q (tor n) X)
    (hτ : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → Tendsto (fun n => τ (tor n) X) atTop atTop)
    (hcoef : ∀ ℓ ℓ', Le ℓ ℓ' → ∀ X, X ∈ P ℓ → Q ℓ X → X ∈ P ℓ' → Q ℓ' X → t₀ ≤ τ ℓ X →
      ∀ g ∈ D, ‖T ℓ' g X - T ℓ g X‖ ≤
        a * Real.exp (-lam * (τ ℓ X : ℝ)) * Real.exp (-κ' * (sz X : ℝ)))
    (hWlim : ∀ (f : ℕ → G → ℂ) (F : G → ℂ) (M : ℝ), (∀ᶠ n in atTop, f n ∈ W) →
      (∀ᶠ n in atTop, ∀ g ∈ D, ‖f n g‖ ≤ M) → TendstoUniformlyOn f F atTop D → F ∈ W) :
    ∃ V : G → S → ℂ, (∀ g X, V g X = limUnder atTop (fun n => T (tor n) g X)) ∧
      ∃ Tn : ι → G → S → ℂ,
      (∀ ℓ g X, Tn ℓ g X = if Q ℓ X then V g X else
        T ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - V g X₀)) ∧
      (∀ ℓ g, ∑ X ∈ P ℓ, Tn ℓ g X = ∑ X ∈ P ℓ, T ℓ g X) ∧
      (∀ ℓ ℓ' g X, Q ℓ X → Q ℓ' X → Tn ℓ g X = Tn ℓ' g X) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖Tn ℓ g X‖ ≤
        (B + a * Real.exp κ' + 2 * B * Real.exp (κ' * (t₀ : ℝ))) *
          Real.exp (-κ * (sz X : ℝ))) ∧
      (∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, Tn ℓ g X = 0) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → Tn ℓ g X = Tn ℓ g' X) ∧
      (∀ ℓ X, X ∈ P ℓ → (fun g => Tn ℓ g X) ∈ W) := by
  have hlam0 : 0 < lam := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  obtain ⟨V, hVdef, hconv, hclose, hVbd, hunif, hVsupp, hVloc⟩ :=
    lastScale_limit P Q sz τ D R Ag T tor Le hlam0 hmono hcof hev hτ hsupp hloc hbd hcoef
  refine ⟨V, hVdef, ?_⟩
  refine resum_lastScale_target P Q sz τ Φ D W R Ag T V hB ha hκ hκ' hlam hΦP hΦsz hfib hRΦ hAgΦ
    hsupp hVsupp hVloc ?_ hVbd hloc han hbd hclose
  intro ℓ X hX hQ
  refine hWlim (fun n g => T (tor n) g X) (fun g => V g X) (B * Real.exp (-κ' * (sz X : ℝ))) ?_ ?_
    (hunif ℓ X hX hQ)
  · filter_upwards [hev ℓ X hX hQ] with n hn using han (tor n) X hn.1
  · filter_upwards [hev ℓ X hX hQ] with n hn g hg using hbd (tor n) X hn.1 g hg

end Balaban.Polymer
