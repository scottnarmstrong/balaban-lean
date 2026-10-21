/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LastScaleCells
public import Balaban.Spine.LastIntegral

/-!
# The exact two-torus agreement of the last-scale activities (A6-3 (d), blocker 7)

The agreement step of the small-field last integral: from per-torus activities `aT` of the scale
`k + 1` (the clauses of Root-F's observable form on each admissible torus, `LastScaleTorusClauses`)
and the uniform closeness of their increments on two tori on the quarter-box polymers
(`LastScaleTwoTorusClose`), activities `p` with the exact two-torus agreement and the same sums
(`observableActivitiesAt_of_twoTorusClose`). Design: TORUSLAST2 §3 and SPINE-AUDIT-2 (d) (P6 p. 3,
P4 (H.4)): the activities of the polymers of the quarter box are one object valid for all tori, the
limit of `aT` over growing tori (Cauchy by the closeness, `lastScale_limit`); on each torus the
finite-size defect `aT - lim` of such a polymer is moved onto the polymer obtained by joining it to
the outside of the quarter box by a chain of cells (`lastScale_chain`), which never lies in a quarter
box; the bound of the moved defect is `e^{-λ τ}` in the margin `τ` against the chain cost
`e^{-κ' (τ + 1)}`, and the fibres of the chain map have at most `2^{|X|}` elements.

Steps: `cellTerm_close` (the closeness of the cell terms from that of `aT`), `cellResum_exists` (the
resummed cell terms, `resum_lastScale_limit` on the tori `TwoCell`), `resumAct` (the activities
read back on the fine sites: the term of the polymer `sitesT Y` is the resummed term of its cells `Y`;
on the tori with one block per side the increment of `aT`), its clauses (`resumAct_supp`,
`resumAct_analytic`, `resumAct_local`, `resumAct_bound`, `resumAct_agree`, `resumAct_sum`).
-/

@[expose] public section

open Finset Filter Topology Balaban Balaban.Polymer Balaban.Polymer.TwoTorusStep

namespace Balaban.RootFSpine.LastScale

variable {d N : ℕ}

section Core

variable {s s' : ℕ} {aT : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ}

/-- **The closeness of the cell terms of two tori** (the hypothesis `hcoef` of the resummation):
from the closeness of the increments of `aT` on the images of the integer sets `A` whose cells form
a polymer of the cell box of the smaller torus. -/
theorem cellTerm_close {κ' a lam : ℝ} {t₀ : ℕ}
    (hL : ∀ (ℓ : ℕ) [NeZero ℓ], s' ∣ ℓ → ∀ X (g g' : Torus d ℓ → Fin N → ℂ),
      (∀ y ∈ X, g y = g' y) → aT ℓ X g = aT ℓ X g')
    (hC : ∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], s' ∣ ℓ → s' ∣ ℓ' → ℓ ≤ ℓ' →
      ∀ A : Finset (Fin d → ℤ), IsPolymer d ℓ s (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ)) →
      (∀ y ∈ A, ∀ μ, (y μ / (s : ℤ)).natAbs ≤ ℓ / s / 4) → t₀ ≤ cellMargin s (ℓ / s) A →
      ∀ g : (Fin d → ℤ) → Fin N → ℂ, ∑ y ∈ A, ∑ i, ‖g y i‖ < 1 →
      ‖(aT ℓ' (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ')) (fun z => g fun μ => (z μ).valMinAbs) -
          aT ℓ' (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ')) 0) -
        (aT ℓ (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ)) (fun z => g fun μ => (z μ).valMinAbs) -
          aT ℓ (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ)) 0)‖ ≤
        a * Real.exp (-lam * (cellMargin s (ℓ / s) A : ℝ)) *
          Real.exp (-κ' * ((A.card : ℝ) / (s : ℝ) ^ d)))
    (i i' : TwoCell s s') (hle : i.1 / s ≤ i'.1 / s) {X : Finset (Fin d → ℤ)}
    (hX : X ∈ cellPolys d (i.1 / s)) (hQ : ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ i.1 / s / 4)
    (hX' : X ∈ cellPolys d (i'.1 / s)) (hQ' : ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ i'.1 / s / 4)
    (ht : t₀ ≤ i.1 / s / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs))
    {G : (Fin d → ℤ) → Fin N → ℂ} (hG : G ∈ zBall d N) :
    ‖cellTerm s s' aT i' G X - cellTerm s s' aT i G X‖ ≤
      a * Real.exp (-lam * ((i.1 / s / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs) :
        ℕ) : ℝ)) * Real.exp (-κ' * (X.card : ℝ)) := by
  have hs0 := i.2.2.1
  set A := (sitesT s (i.1 / s) i.1 X).image (liftZ s (i.1 / s)) with hAdef
  have hAi : ∀ y, y ∈ A ↔ (fun μ => y μ / (s : ℤ)) ∈ X :=
    mem_image_liftZ_sitesT i.eq hs0 hX
  have hm := cellMargin_of_mem_iff i.eq hs0 hX hAi
  have hcard : ((A.card : ℝ) / (s : ℝ) ^ d) = X.card := by
    rw [card_of_mem_iff i.eq hs0 hX hAi]
    have : (0 : ℝ) < (s : ℝ) ^ d := by positivity
    push_cast
    field_simp
  have hℓ : i.1 ≤ i'.1 := by
    rw [i.eq, i'.eq]; exact Nat.mul_le_mul_left _ hle
  have hc := hC i.1 i'.1 i.2.1 i'.2.1 hℓ A (by
      rw [image_cast_of_mem_iff i.eq hs0 hX hAi]
      exact (isPolymer_iff_sitesT i.eq hs0 _).2 ⟨X, hX, rfl⟩)
    (fun y hy μ => hQ _ ((hAi y).1 hy) μ) (by rw [hm]; exact ht) G (hG A)
  rw [incr_eq_cellTerm hL i hX hQ hAi G, incr_eq_cellTerm hL i' hX' hQ' hAi G, hm,
    hcard] at hc
  exact hc

open scoped Classical in
/-- **The resummed cell terms** (A6-3 (d)): the limit resummation `resum_lastScale_limit` applied
to the cell terms `cellTerm` of the tori with at least two cells per side, with the chain map of
`lastScale_chain` and the sequence of tori `s' (n + 2)`. The resummed terms `Tn` vanish at the zero
source, are analytic (`anW`) and local, satisfy the bound with rate `κ`, agree on the cell boxes of
two tori, and have the sums of the cell terms. -/
theorem cellResum_exists (hd : 0 < d) (hss' : s ∣ s') (hs' : 0 < s') (hs0 : 0 < s)
    {κ κ' B a lam : ℝ} {t₀ : ℕ} (hB : 0 ≤ B) (ha : 0 ≤ a) (hκ : 0 ≤ κ)
    (hκ' : κ + Real.log 2 ≤ κ') (hlam : κ' ≤ lam)
    (hA : ∀ (ℓ : ℕ) [NeZero ℓ], s' ∣ ℓ → ∀ X, AnalyticOnNhd ℂ (aT ℓ X) (torusBall d N ℓ))
    (hL : ∀ (ℓ : ℕ) [NeZero ℓ], s' ∣ ℓ → ∀ X (g g' : Torus d ℓ → Fin N → ℂ),
      (∀ y ∈ X, g y = g' y) → aT ℓ X g = aT ℓ X g')
    (hBd : ∀ (ℓ : ℕ) [NeZero ℓ], s' ∣ ℓ → ∀ X, ∀ g ∈ torusBall d N ℓ,
      ‖aT ℓ X g - aT ℓ X 0‖ ≤ B * Real.exp (-κ' * ((X.card : ℝ) / (s : ℝ) ^ d)))
    (hC : ∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], s' ∣ ℓ → s' ∣ ℓ' → ℓ ≤ ℓ' →
      ∀ A : Finset (Fin d → ℤ), IsPolymer d ℓ s (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ)) →
      (∀ y ∈ A, ∀ μ, (y μ / (s : ℤ)).natAbs ≤ ℓ / s / 4) → t₀ ≤ cellMargin s (ℓ / s) A →
      ∀ g : (Fin d → ℤ) → Fin N → ℂ, ∑ y ∈ A, ∑ i, ‖g y i‖ < 1 →
      ‖(aT ℓ' (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ')) (fun z => g fun μ => (z μ).valMinAbs) -
          aT ℓ' (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ')) 0) -
        (aT ℓ (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ)) (fun z => g fun μ => (z μ).valMinAbs) -
          aT ℓ (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ)) 0)‖ ≤
        a * Real.exp (-lam * (cellMargin s (ℓ / s) A : ℝ)) *
          Real.exp (-κ' * ((A.card : ℝ) / (s : ℝ) ^ d))) :
    ∃ Tn : TwoCell s s' → ((Fin d → ℤ) → Fin N → ℂ) → Finset (Fin d → ℤ) → ℂ,
      (∀ i Y, Tn i 0 Y = 0) ∧
      (∀ i Y, Y ∈ cellPolys d (i.1 / s) → (fun G => Tn i G Y) ∈ anW d N s) ∧
      (∀ i Y, Y ∈ cellPolys d (i.1 / s) → ∀ G G',
        (∀ y : Fin d → ℤ, (fun μ => y μ / (s : ℤ)) ∈ Y → G y = G' y) → Tn i G Y = Tn i G' Y) ∧
      (∀ i Y, Y ∈ cellPolys d (i.1 / s) → ∀ G ∈ zBall d N,
        ‖Tn i G Y‖ ≤ (B + a * Real.exp κ' + 2 * B * Real.exp (κ' * (t₀ : ℝ))) *
          Real.exp (-κ * (Y.card : ℝ))) ∧
      (∀ i i' G Y, (∀ x ∈ Y, ∀ μ, (x μ).natAbs ≤ i.1 / s / 4) →
        (∀ x ∈ Y, ∀ μ, (x μ).natAbs ≤ i'.1 / s / 4) → Tn i G Y = Tn i' G Y) ∧
      (∀ i G, ∑ Y ∈ cellPolys d (i.1 / s), Tn i G Y =
        ∑ Y ∈ cellPolys d (i.1 / s), cellTerm s s' aT i G Y) := by
  let Kf : TwoCell s s' → ℕ := fun i => i.1 / s
  have hKf : ∀ i : TwoCell s s', NeZero (Kf i) := fun i => TwoCell.neZeroK i
  let P : TwoCell s s' → Finset (Finset (Fin d → ℤ)) := fun i => cellPolys d (i.1 / s)
  let Q : TwoCell s s' → Finset (Fin d → ℤ) → Prop :=
    fun i X => ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ Kf i / 4
  let τ : TwoCell s s' → Finset (Fin d → ℤ) → ℕ :=
    fun i X => Kf i / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs)
  let Ag : Finset (Fin d → ℤ) → ((Fin d → ℤ) → Fin N → ℂ) → ((Fin d → ℤ) → Fin N → ℂ) → Prop :=
    fun X G G' => ∀ y : Fin d → ℤ, (fun μ => y μ / (s : ℤ)) ∈ X → G y = G' y
  have hP : ∀ i X, X ∈ P i ↔ ∃ Y, IsAnimal (blockGraph d (Kf i)) Y ∧
      X = Y.image (fun b μ => (b μ).valMinAbs) := fun i X => mem_cellPolys
  have hAg : ∀ X Z, X ⊆ Z → ∀ G G', Ag Z G G' → Ag X G G' :=
    fun X Z h G G' hZ y hy => hZ y (h hy)
  obtain ⟨Φ, -, hΦP, hΦsz, hfib, hRΦ, hAgΦ⟩ := lastScale_chain Kf hd (fun i => TwoCell.two_le i)
    P Q Finset.card τ (fun _ => True) Ag hP (fun _ _ => Iff.rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => trivial) hAg
  -- a sequence of tori with unbounded number of cells
  obtain ⟨r, hr⟩ := hss'
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0, mul_zero] at hr; omega
    · exact h0
  let tor : ℕ → TwoCell s s' := fun n => ⟨s' * (n + 2), dvd_mul_right _ _, hs0,
    ⟨r * (n + 2), by rw [hr]; ring⟩, by rw [hr]; nlinarith⟩
  have hKtor : ∀ n, Kf (tor n) = r * (n + 2) := by
    intro n
    show s' * (n + 2) / s = r * (n + 2)
    rw [hr, mul_assoc, Nat.mul_div_cancel_left _ hs0]
  have hKm : ∀ m n, m ≤ n → Kf (tor m) ≤ Kf (tor n) := by
    intro m n hmn
    rw [hKtor, hKtor]
    exact Nat.mul_le_mul_left _ (by omega)
  have hKt : Tendsto (fun n => Kf (tor n)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun n hn => ?_⟩
    rw [hKtor]
    nlinarith
  have hev := rootF_hev Kf (fun i => TwoCell.two_le i) tor hKt P Q hP (fun _ _ => Iff.rfl)
  have hτt : ∀ i X, X ∈ P i → Q i X → Tendsto (fun n => τ (tor n) X) atTop atTop :=
    fun i X _ _ => rootF_hτ Kf tor hKt τ (fun _ _ => rfl) X
  let T := cellTerm (d := d) (N := N) s s' aT
  obtain ⟨V, hV, Tn, hTn, hsum, hagr, hbd, -, hloc, hW⟩ := resum_lastScale_limit P Q Finset.card
    τ Φ (zBall d N) (anW d N s) (fun _ => True) Ag T tor (fun i i' => Kf i ≤ Kf i') hB ha hκ hκ'
    hlam hΦP hΦsz (fun i Z => by convert hfib i Z) hRΦ hAgΦ (fun _ _ _ h => absurd trivial h)
    (fun i X _ G G' h => cellTerm_local hL i X G G' h) (fun i X _ => cellTerm_mem_anW hA i X)
    (fun i X hX G hG => cellTerm_bound hBd i hX hG) hKm (rootF_hcof Kf tor hKt) hev hτt
    (fun i i' hle X hX hQ hX' hQ' ht G hG => cellTerm_close hL hC i i' hle hX hQ hX' hQ' ht hG)
    (fun f F Mb hf hM hu => anW_closed f F Mb hf hM hu)
  have hV0 : ∀ Y, V 0 Y = 0 := by
    intro Y
    rw [hV]
    have : (fun n => T (tor n) 0 Y) = fun _ => (0 : ℂ) := funext fun n => cellTerm_zero _ _
    rw [this]
    exact tendsto_const_nhds.limUnder_eq
  refine ⟨Tn, fun i Y => ?_, hW, hloc, hbd, fun i i' G Y hQ hQ' => hagr i i' G Y hQ hQ',
    hsum⟩
  rw [hTn]
  split_ifs
  · exact hV0 Y
  · simp [T, cellTerm_zero, hV0]

/-- The activities built from resummed cell terms `Tn`: on a torus of `TwoCell` the term of the
fine polymer `sitesT Y` is `Tn` of its cells `Y` at the extended source, and zero on the other sets;
on the other admissible tori it is the increment of `aT`. -/
noncomputable def resumAct (s s' : ℕ)
    (aT : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ)
    (Tn : TwoCell s s' → ((Fin d → ℤ) → Fin N → ℂ) → Finset (Fin d → ℤ) → ℂ)
    (ℓ : ℕ) (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ) : ℂ :=
  if h : s' ∣ ℓ ∧ 0 < s ∧ s ∣ ℓ ∧ 2 * s ≤ ℓ then
    haveI : NeZero ℓ := ⟨(TwoCell.pos ⟨ℓ, h⟩).ne'⟩
    haveI : NeZero (ℓ / s) := TwoCell.neZeroK ⟨ℓ, h⟩
    ∑ Y ∈ (cellPolys d (ℓ / s)).filter (fun Y => sitesT s (ℓ / s) ℓ Y = X),
      Tn ⟨ℓ, h⟩ (extZ s (ℓ / s) ℓ g) Y
  else aT ℓ X g - aT ℓ X 0

variable {Tn : TwoCell s s' → ((Fin d → ℤ) → Fin N → ℂ) → Finset (Fin d → ℤ) → ℂ}

theorem resumAct_pos (i : TwoCell s s') (X : Finset (Torus d i.1)) (g : Torus d i.1 → Fin N → ℂ) :
    resumAct s s' aT Tn i.1 X g =
      ∑ Y ∈ (cellPolys d (i.1 / s)).filter (fun Y => sitesT s (i.1 / s) i.1 Y = X),
        Tn i (extZ s (i.1 / s) i.1 g) Y := by
  unfold resumAct
  split_ifs with h
  · rfl
  · exact absurd i.2 h

theorem resumAct_neg {ℓ : ℕ} (h : ¬ (s' ∣ ℓ ∧ 0 < s ∧ s ∣ ℓ ∧ 2 * s ≤ ℓ))
    (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ) :
    resumAct s s' aT Tn ℓ X g = aT ℓ X g - aT ℓ X 0 := by
  unfold resumAct
  split_ifs
  rfl

theorem filter_sitesT_eq_singleton (i : TwoCell s s') {Y : Finset (Fin d → ℤ)}
    (hY : Y ∈ cellPolys d (i.1 / s)) :
    (cellPolys d (i.1 / s)).filter
      (fun Y' => sitesT s (i.1 / s) i.1 Y' = sitesT s (i.1 / s) i.1 Y) = {Y} := by
  ext Y'
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hY', h⟩; exact sitesT_injOn i.eq i.2.2.1 hY' hY h
  · rintro rfl; exact ⟨hY, rfl⟩

theorem resumAct_zero (hTn0 : ∀ i Y, Tn i 0 Y = 0) (ℓ : ℕ) (X : Finset (Torus d ℓ)) :
    resumAct s s' aT Tn ℓ X 0 = 0 := by
  by_cases h : s' ∣ ℓ ∧ 0 < s ∧ s ∣ ℓ ∧ 2 * s ≤ ℓ
  · refine (resumAct_pos ⟨ℓ, h⟩ X 0).trans (Finset.sum_eq_zero fun Y _ => ?_)
    rw [extZ_zero]
    exact hTn0 _ Y
  · rw [resumAct_neg h, sub_self]

theorem resumAct_supp
    (hS : ∀ (ℓ : ℕ) [NeZero ℓ], s' ∣ ℓ → ∀ X, ¬ IsPolymer d ℓ s X → ∀ g, aT ℓ X g = aT ℓ X 0)
    (ℓ : ℕ) [NeZero ℓ] (hdv : s' ∣ ℓ) (X : Finset (Torus d ℓ)) (hX : ¬ IsPolymer d ℓ s X)
    (g : Torus d ℓ → Fin N → ℂ) : resumAct s s' aT Tn ℓ X g = 0 := by
  by_cases h : s' ∣ ℓ ∧ 0 < s ∧ s ∣ ℓ ∧ 2 * s ≤ ℓ
  · have key : ∀ (i : TwoCell s s') (X : Finset (Torus d i.1)), ¬ IsPolymer d i.1 s X →
        ∀ g : Torus d i.1 → Fin N → ℂ, resumAct s s' aT Tn i.1 X g = 0 := by
      intro i X hX g
      rw [resumAct_pos, Finset.filter_false_of_mem, Finset.sum_empty]
      intro Y hY hYX
      exact hX (hYX ▸ (isPolymer_iff_sitesT i.eq i.2.2.1 _).2 ⟨Y, hY, rfl⟩)
    exact key ⟨ℓ, h⟩ X hX g
  · rw [resumAct_neg h, hS ℓ hdv X hX g, sub_self]

theorem resumAct_analytic
    (hA : ∀ (ℓ : ℕ) [NeZero ℓ], s' ∣ ℓ → ∀ X, AnalyticOnNhd ℂ (aT ℓ X) (torusBall d N ℓ))
    (hW : ∀ i Y, Y ∈ cellPolys d (i.1 / s) → (fun G => Tn i G Y) ∈ anW d N s)
    (ℓ : ℕ) [NeZero ℓ] (hdv : s' ∣ ℓ) (X : Finset (Torus d ℓ)) :
    AnalyticOnNhd ℂ (resumAct s s' aT Tn ℓ X) (torusBall d N ℓ) := by
  by_cases h : s' ∣ ℓ ∧ 0 < s ∧ s ∣ ℓ ∧ 2 * s ≤ ℓ
  · have key : ∀ (i : TwoCell s s') (X : Finset (Torus d i.1)),
        AnalyticOnNhd ℂ (resumAct s s' aT Tn i.1 X) (torusBall d N i.1) := by
      intro i X
      have : resumAct s s' aT Tn i.1 X = fun g =>
          ∑ Y ∈ (cellPolys d (i.1 / s)).filter (fun Y => sitesT s (i.1 / s) i.1 Y = X),
            Tn i (extZ s (i.1 / s) i.1 g) Y := funext (resumAct_pos i X)
      rw [this]
      have h := Finset.analyticOnNhd_sum (𝕜 := ℂ)
        (f := fun Y g => Tn i (extZ s (i.1 / s) i.1 g) Y)
        ((cellPolys d (i.1 / s)).filter (fun Y => sitesT s (i.1 / s) i.1 Y = X)) fun Y hY =>
        mem_anW.1 (hW i Y (Finset.mem_filter.1 hY).1) i.1
      convert h using 1
      funext g
      rw [Finset.sum_apply]
    exact key ⟨ℓ, h⟩ X
  · have : resumAct s s' aT Tn ℓ X = fun g => aT ℓ X g - aT ℓ X 0 := funext (resumAct_neg h X)
    rw [this]
    exact (hA ℓ hdv X).sub analyticOnNhd_const

theorem resumAct_local
    (hL : ∀ (ℓ : ℕ) [NeZero ℓ], s' ∣ ℓ → ∀ X (g g' : Torus d ℓ → Fin N → ℂ),
      (∀ y ∈ X, g y = g' y) → aT ℓ X g = aT ℓ X g')
    (hloc : ∀ i Y, Y ∈ cellPolys d (i.1 / s) → ∀ G G',
      (∀ y : Fin d → ℤ, (fun μ => y μ / (s : ℤ)) ∈ Y → G y = G' y) → Tn i G Y = Tn i G' Y)
    (ℓ : ℕ) [NeZero ℓ] (hdv : s' ∣ ℓ) (X : Finset (Torus d ℓ)) (g g' : Torus d ℓ → Fin N → ℂ)
    (hgg : ∀ y ∈ X, g y = g' y) : resumAct s s' aT Tn ℓ X g = resumAct s s' aT Tn ℓ X g' := by
  by_cases h : s' ∣ ℓ ∧ 0 < s ∧ s ∣ ℓ ∧ 2 * s ≤ ℓ
  · have key : ∀ (i : TwoCell s s') (X : Finset (Torus d i.1))
        (g g' : Torus d i.1 → Fin N → ℂ), (∀ y ∈ X, g y = g' y) →
        resumAct s s' aT Tn i.1 X g = resumAct s s' aT Tn i.1 X g' := by
      intro i X g g' hgg
      rw [resumAct_pos, resumAct_pos]
      refine Finset.sum_congr rfl fun Y hY => ?_
      obtain ⟨hYP, hYX⟩ := Finset.mem_filter.1 hY
      refine hloc i Y hYP _ _ fun y hy => ?_
      unfold extZ
      split_ifs with hl
      · apply hgg
        rw [← hYX, mem_sitesT]
        convert hy using 1
        funext μ
        rw [← liftZ_ediv i.2.2.1 _ μ, hl]
      · rfl
    exact key ⟨ℓ, h⟩ X g g' hgg
  · rw [resumAct_neg h, resumAct_neg h, hL ℓ hdv X g g' hgg]

theorem resumAct_bound {κ κ' B Bn : ℝ} (hBn : 0 ≤ Bn) (hBB : B ≤ Bn) (hκκ : κ ≤ κ')
    (hBd : ∀ (ℓ : ℕ) [NeZero ℓ], s' ∣ ℓ → ∀ X, ∀ g ∈ torusBall d N ℓ,
      ‖aT ℓ X g - aT ℓ X 0‖ ≤ B * Real.exp (-κ' * ((X.card : ℝ) / (s : ℝ) ^ d)))
    (hbd : ∀ i Y, Y ∈ cellPolys d (i.1 / s) → ∀ G ∈ zBall d N,
      ‖Tn i G Y‖ ≤ Bn * Real.exp (-κ * (Y.card : ℝ)))
    (ℓ : ℕ) [NeZero ℓ] (hdv : s' ∣ ℓ) (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ)
    (hg : g ∈ torusBall d N ℓ) :
    ‖resumAct s s' aT Tn ℓ X g‖ ≤ Bn * Real.exp (-κ * ((X.card : ℝ) / (s : ℝ) ^ d)) := by
  by_cases h : s' ∣ ℓ ∧ 0 < s ∧ s ∣ ℓ ∧ 2 * s ≤ ℓ
  · have key : ∀ (i : TwoCell s s') (X : Finset (Torus d i.1)) (g : Torus d i.1 → Fin N → ℂ),
        g ∈ torusBall d N i.1 →
        ‖resumAct s s' aT Tn i.1 X g‖ ≤ Bn * Real.exp (-κ * ((X.card : ℝ) / (s : ℝ) ^ d)) := by
      intro i X g hg
      by_cases hex : ∃ Y ∈ cellPolys d (i.1 / s), sitesT s (i.1 / s) i.1 Y = X
      · obtain ⟨Y, hY, rfl⟩ := hex
        rw [resumAct_pos, filter_sitesT_eq_singleton i hY, Finset.sum_singleton,
          card_sitesT_div i.eq i.2.2.1 hY]
        exact hbd i Y hY _ (extZ_mem_zBall hg)
      · rw [resumAct_pos, Finset.filter_false_of_mem (fun Y hY h => hex ⟨Y, hY, h⟩),
          Finset.sum_empty, norm_zero]
        positivity
    exact key ⟨ℓ, h⟩ X g hg
  · rw [resumAct_neg h]
    refine (hBd ℓ hdv X g hg).trans ?_
    have hx : 0 ≤ (X.card : ℝ) / (s : ℝ) ^ d := by positivity
    refine mul_le_mul hBB (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hBn
    nlinarith

theorem resumAct_sum
    (hS : ∀ (ℓ : ℕ) [NeZero ℓ], s' ∣ ℓ → ∀ X, ¬ IsPolymer d ℓ s X → ∀ g, aT ℓ X g = aT ℓ X 0)
    (hsum : ∀ i G, ∑ Y ∈ cellPolys d (i.1 / s), Tn i G Y =
      ∑ Y ∈ cellPolys d (i.1 / s), cellTerm s s' aT i G Y)
    (ℓ : ℕ) [NeZero ℓ] (g : Torus d ℓ → Fin N → ℂ) :
    ∑ X, resumAct s s' aT Tn ℓ X g = ∑ X, (aT ℓ X g - aT ℓ X 0) := by
  classical
  by_cases h : s' ∣ ℓ ∧ 0 < s ∧ s ∣ ℓ ∧ 2 * s ≤ ℓ
  · have key : ∀ (i : TwoCell s s') (g : Torus d i.1 → Fin N → ℂ),
        ∑ X, resumAct s s' aT Tn i.1 X g = ∑ X, (aT i.1 X g - aT i.1 X 0) := by
      intro i g
      rw [Finset.sum_congr rfl fun X _ => resumAct_pos i X g,
        Finset.sum_fiberwise (cellPolys d (i.1 / s)) (sitesT s (i.1 / s) i.1)
          (fun Y => Tn i (extZ s (i.1 / s) i.1 g) Y), hsum i]
      simp only [cellTerm_extZ]
      rw [← Finset.sum_image (f := fun X => aT i.1 X g - aT i.1 X 0)
        (sitesT_injOn i.eq i.2.2.1)]
      refine Finset.sum_subset (Finset.subset_univ _) fun X _ hX => ?_
      have hnp : ¬ IsPolymer d i.1 s X := fun hp => hX (by
        obtain ⟨Y, hY, rfl⟩ := (isPolymer_iff_sitesT i.eq i.2.2.1 X).1 hp
        exact Finset.mem_image_of_mem _ hY)
      rw [hS i.1 i.2.1 X hnp g, sub_self]
    exact key ⟨ℓ, h⟩ g
  · exact Finset.sum_congr rfl fun X _ => resumAct_neg h X g

theorem resumAct_agree (hd : 0 < d) (hss' : s ∣ s') (hs4 : 4 ≤ s)
    (hS : ∀ (ℓ : ℕ) [NeZero ℓ], s' ∣ ℓ → ∀ X, ¬ IsPolymer d ℓ s X → ∀ g, aT ℓ X g = aT ℓ X 0)
    (hloc : ∀ i Y, Y ∈ cellPolys d (i.1 / s) → ∀ G G',
      (∀ y : Fin d → ℤ, (fun μ => y μ / (s : ℤ)) ∈ Y → G y = G' y) → Tn i G Y = Tn i G' Y)
    (hagr : ∀ i i' G Y, (∀ x ∈ Y, ∀ μ, (x μ).natAbs ≤ i.1 / s / 4) →
      (∀ x ∈ Y, ∀ μ, (x μ).natAbs ≤ i'.1 / s / 4) → Tn i G Y = Tn i' G Y)
    (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (hdv : s' ∣ ℓ) (hdv' : s' ∣ ℓ')
    (A : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → Fin N → ℂ)
    (hbox : ∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ) ∧ 4 * |y μ| < (ℓ' : ℤ)) :
    resumAct s s' aT Tn ℓ (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ))
        (fun z => g fun μ => (z μ).valMinAbs) =
      resumAct s s' aT Tn ℓ' (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ'))
        (fun z => g fun μ => (z μ).valMinAbs) := by
  have hs0 : 0 < s := by omega
  have hAℓ : ∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ) := fun y hy μ => (hbox y hy μ).1
  have hAℓ' : ∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ' : ℤ) := fun y hy μ => (hbox y hy μ).2
  have hsℓ : s ∣ ℓ := hss'.trans hdv
  have hsℓ' : s ∣ ℓ' := hss'.trans hdv'
  by_cases hP : IsPolymer d ℓ s (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ))
  · obtain ⟨hK4, hK4', hP', hcl⟩ := isPolymer_transfer_quarter hd hs4 hsℓ hsℓ' hAℓ hAℓ' hP
    have key : ∀ j : TwoCell s s', (∀ y ∈ A, ∀ μ, 4 * |y μ| < (j.1 : ℤ)) →
        IsPolymer d j.1 s (A.image fun y μ => ((y μ : ℤ) : ZMod j.1)) →
        resumAct s s' aT Tn j.1 (A.image fun y μ => ((y μ : ℤ) : ZMod j.1))
            (fun z => g fun μ => (z μ).valMinAbs) = Tn j g (A.image fun y μ => y μ / (s : ℤ)) ∧
          ∀ x ∈ A.image (fun y μ => y μ / (s : ℤ)), ∀ μ, (x μ).natAbs ≤ j.1 / s / 4 := by
      intro j hAj hPj
      obtain ⟨hXP, hXQ, hmem⟩ := quarter_cells hs4 j.eq j.two_le hAj hcl hPj
      have himg := image_cast_of_mem_iff j.eq hs0 hXP hmem
      refine ⟨?_, hXQ⟩
      rw [resumAct_pos, himg, filter_sitesT_eq_singleton j hXP, Finset.sum_singleton]
      refine hloc j _ hXP _ _ fun y hy => ?_
      have hK2 := j.two_le
      have hyq : ∀ μ, (y μ / (s : ℤ)).natAbs ≤ j.1 / s / 4 := fun μ => hXQ _ hy μ
      have hl : liftZ s (j.1 / s) (fun μ => ((y μ : ℤ) : ZMod j.1)) = y :=
        liftZ_cast j.eq hs0 (by omega) y fun μ =>
          valMinAbs_intCast_of_abs_le (r := j.1 / s / 4) (by omega)
            (by rw [Int.abs_eq_natAbs]; exact_mod_cast hyq μ)
      unfold extZ
      simp only [hl, ↓reduceIte]
      refine congrArg g (funext fun μ => ?_)
      have h2 := two_abs_lt_of_cell hs0 hK2 (hyq μ)
      have hℓ : ((j.1 : ℕ) : ℤ) = (s : ℤ) * ((j.1 / s : ℕ) : ℤ) := by
        conv_lhs => rw [j.eq]
        push_cast; ring
      exact valMinAbs_cast_of_two_abs_lt (by rw [hℓ]; exact h2)
    have hj : s' ∣ ℓ ∧ 0 < s ∧ s ∣ ℓ ∧ 2 * s ≤ ℓ := ⟨hdv, hs0, hsℓ, by
      have := Nat.mul_div_cancel' hsℓ; nlinarith⟩
    have hj' : s' ∣ ℓ' ∧ 0 < s ∧ s ∣ ℓ' ∧ 2 * s ≤ ℓ' := ⟨hdv', hs0, hsℓ', by
      have := Nat.mul_div_cancel' hsℓ'; nlinarith⟩
    obtain ⟨e1, q1⟩ := key ⟨ℓ, hj⟩ hAℓ hP
    obtain ⟨e2, q2⟩ := key ⟨ℓ', hj'⟩ hAℓ' hP'
    exact e1.trans ((hagr _ _ g _ q1 q2).trans e2.symm)
  · have hP' : ¬ IsPolymer d ℓ' s (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ')) := fun hP' =>
      hP (isPolymer_transfer_quarter hd hs4 hsℓ' hsℓ hAℓ' hAℓ hP').2.2.1
    rw [resumAct_supp hS ℓ hdv _ hP, resumAct_supp hS ℓ' hdv' _ hP']

end Core

section RootF

/-- **Per-torus last-scale activities** (A6-3 (d), input (i) of the agreement step: the clauses of
`ObservableActivitiesAt` on each admissible torus, without the agreement, at a rate `κ'` and an
amplitude `B`). On every torus `𝕋_ℓ` with `M L^{kf+1} ∣ ℓ` the family `aT ℓ X g` (scale `k + 1`) has
increments vanishing off the polymers of block side `M L^{k+1}`, is analytic on the unit `ℓ¹` ball,
depends on `g|_X` only, and its increments are bounded there by `B e^{-κ' |X| / (M L^{k+1})^d}`. -/
def LastScaleTorusClauses (d N L M kf k : ℕ) (κ' B : ℝ)
    (aT : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) : Prop :=
  ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ →
    (∀ X, ¬ IsPolymer d ℓ (M * L ^ (k + 1)) X → ∀ g, aT ℓ X g = aT ℓ X 0) ∧
    (∀ X, AnalyticOnNhd ℂ (aT ℓ X) {g | ∑ y, ∑ i, ‖g y i‖ < 1}) ∧
    (∀ X (g g' : Torus d ℓ → Fin N → ℂ), (∀ y ∈ X, g y = g' y) → aT ℓ X g = aT ℓ X g') ∧
    (∀ X (g : Torus d ℓ → Fin N → ℂ), ∑ y, ∑ i, ‖g y i‖ < 1 →
      ‖aT ℓ X g - aT ℓ X 0‖ ≤
        B * Real.exp (-κ' * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d))

/-- **The uniform two-torus closeness of the last-scale activities** (A6-3 (d), the second input of
the agreement step). For two admissible tori `ℓ ≤ ℓ'` and a finite set `A ⊂ ℤ^d` whose image in
`𝕋_ℓ` is a polymer of block side `s = M L^{k+1}` with all its cells in the cell box
`|⌊y_μ/s⌋| ≤ (ℓ/s)/4` of the smaller torus, at margin `τ = cellMargin ≥ t₀` cells from the edge of
that box: the increments of `aT` at the images of `A` on the two tori, at a source `g` on `ℤ^d`
read through the centred coordinates, differ by at most `a e^{-λ τ} e^{-κ' |A|/s^d}` when
`∑_{y ∈ A} |g(y)| < 1`. -/
def LastScaleTwoTorusClose (d N L M kf k : ℕ) (κ' a lam : ℝ) (t₀ : ℕ)
    (aT : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) : Prop :=
  ∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], M * L ^ (kf + 1) ∣ ℓ → M * L ^ (kf + 1) ∣ ℓ' → ℓ ≤ ℓ' →
    ∀ A : Finset (Fin d → ℤ),
      IsPolymer d ℓ (M * L ^ (k + 1)) (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ)) →
      (∀ y ∈ A, ∀ μ, (y μ / ((M * L ^ (k + 1) : ℕ) : ℤ)).natAbs ≤ ℓ / (M * L ^ (k + 1)) / 4) →
      t₀ ≤ cellMargin (M * L ^ (k + 1)) (ℓ / (M * L ^ (k + 1))) A →
      ∀ g : (Fin d → ℤ) → Fin N → ℂ, ∑ y ∈ A, ∑ i, ‖g y i‖ < 1 →
      ‖(aT ℓ' (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ')) (fun z => g fun μ => (z μ).valMinAbs) -
          aT ℓ' (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ')) 0) -
        (aT ℓ (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ)) (fun z => g fun μ => (z μ).valMinAbs) -
          aT ℓ (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ)) 0)‖ ≤
        a * Real.exp (-lam * (cellMargin (M * L ^ (k + 1)) (ℓ / (M * L ^ (k + 1))) A : ℝ)) *
          Real.exp (-κ' * (A.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d)

/-- Rule 10: the zero family satisfies the per-torus clauses. -/
theorem lastScaleTorusClauses_zero {d N L M kf k : ℕ} {κ' B : ℝ} (hB : 0 ≤ B) :
    LastScaleTorusClauses d N L M kf k κ' B fun _ _ _ => 0 :=
  fun _ _ _ => ⟨fun _ _ _ => rfl, fun _ => analyticOnNhd_const, fun _ _ _ _ => rfl,
    fun _ _ _ => by rw [sub_self, norm_zero]; positivity⟩

/-- Rule 10: the zero family satisfies the two-torus closeness. -/
theorem lastScaleTwoTorusClose_zero {d N L M kf k : ℕ} {κ' a lam : ℝ} {t₀ : ℕ} (ha : 0 ≤ a) :
    LastScaleTwoTorusClose d N L M kf k κ' a lam t₀ fun _ _ _ => 0 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ => by simp only [sub_self, norm_zero]; positivity

/-- **The two-torus agreement of the last-scale activities** (A6-3 (d), blocker 7; P6 p. 3,
SPINE-AUDIT-2 (d), TORUSLAST2 §3). Given per-torus activities `aT` of the scale `k + 1` with the
clauses of Root-F's observable form at the rate `κ'` and amplitude `B`
(`LastScaleTorusClauses`), and the uniform closeness of their increments on two tori on the
quarter-box polymers, decaying like `e^{-λ τ}` in the margin `τ` (`LastScaleTwoTorusClose`), there
are activities `p` of the scale `k + 1` in Root-F's form (`ObservableActivitiesAt`, the exact
two-torus agreement `ActAgree` included) with the same sums of increments on every admissible torus.

The activities of a polymer of the quarter box are the limit of `aT` over growing tori (Cauchy by the
closeness); on each torus the difference is moved to the polymer obtained by a chain of cells from
the polymer to outside the quarter box (`resum_lastScale_limit`, `lastScale_chain`). The conditions:
`κ + log 2 ≤ κ'` (the fibres of the chain map have at most `2^{|X|}` elements), `κ' ≤ λ` (the
closeness decays at least as fast as the activities: with the final operators' closeness, rate
`2 c₀ M` per cell, this is `M ≥ κ'/(2 c₀)`, `c₀ = c₀(d, L)`), and the amplitude
`B + a e^{κ'} + 2 B e^{κ' t₀} ≤ (c₉/2) L^{-(k+1)((d-2)/2+δ)}`. -/
theorem observableActivitiesAt_of_twoTorusClose {d N L M kf k : ℕ} (hd : 0 < d) (hk : k ≤ kf)
    (hs4 : 4 ≤ M * L ^ (k + 1)) {κ c₉ δ κ' B a lam : ℝ} {t₀ : ℕ} (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hκ : 0 ≤ κ) (hκ' : κ + Real.log 2 ≤ κ') (hlam : κ' ≤ lam)
    (hamp : B + a * Real.exp κ' + 2 * B * Real.exp (κ' * (t₀ : ℝ)) ≤
      c₉ / 2 * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))))
    (aT : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ)
    (hT : LastScaleTorusClauses d N L M kf k κ' B aT)
    (hC : LastScaleTwoTorusClose d N L M kf k κ' a lam t₀ aT) :
    ∃ p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ,
      ObservableActivitiesAt d N L M κ c₉ δ (k + 1) kf p ∧
      ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ → ∀ g : Torus d ℓ → Fin N → ℂ,
        ∑ X, p ℓ (k + 1) X g = ∑ X, (aT ℓ X g - aT ℓ X 0) := by
  set s := M * L ^ (k + 1) with hsdef
  set s' := M * L ^ (kf + 1) with hs'def
  have hs0 : 0 < s := by omega
  have hM0 : M ≠ 0 := by rintro rfl; simp [hsdef] at hs0
  have hL0 : L ≠ 0 := by rintro rfl; simp [hsdef] at hs0
  have hss' : s ∣ s' := mul_dvd_mul_left M (pow_dvd_pow L (by omega))
  have hs' : 0 < s' := by positivity
  have hsR : ((s : ℕ) : ℝ) = (M : ℝ) * (L : ℝ) ^ (k + 1) := by rw [hsdef]; push_cast; ring
  have hexp : ∀ (κ'' : ℝ) (n : ℕ), -κ'' * ((n : ℝ) / ((s : ℕ) : ℝ) ^ d) =
      -κ'' * (n : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d := by
    intro κ'' n; rw [hsR]; ring
  have hS : ∀ (ℓ : ℕ) [NeZero ℓ], s' ∣ ℓ → ∀ X, ¬ IsPolymer d ℓ s X → ∀ g, aT ℓ X g = aT ℓ X 0 :=
    fun ℓ _ hdv => (hT ℓ hdv).1
  have hA : ∀ (ℓ : ℕ) [NeZero ℓ], s' ∣ ℓ → ∀ X, AnalyticOnNhd ℂ (aT ℓ X) (torusBall d N ℓ) :=
    fun ℓ _ hdv => (hT ℓ hdv).2.1
  have hL : ∀ (ℓ : ℕ) [NeZero ℓ], s' ∣ ℓ → ∀ X (g g' : Torus d ℓ → Fin N → ℂ),
      (∀ y ∈ X, g y = g' y) → aT ℓ X g = aT ℓ X g' := fun ℓ _ hdv => (hT ℓ hdv).2.2.1
  have hBd : ∀ (ℓ : ℕ) [NeZero ℓ], s' ∣ ℓ → ∀ X, ∀ g ∈ torusBall d N ℓ,
      ‖aT ℓ X g - aT ℓ X 0‖ ≤ B * Real.exp (-κ' * ((X.card : ℝ) / (s : ℝ) ^ d)) := by
    intro ℓ _ hdv X g hg
    rw [hexp]
    exact (hT ℓ hdv).2.2.2 X g hg
  have hC' : ∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], s' ∣ ℓ → s' ∣ ℓ' → ℓ ≤ ℓ' →
      ∀ A : Finset (Fin d → ℤ), IsPolymer d ℓ s (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ)) →
      (∀ y ∈ A, ∀ μ, (y μ / (s : ℤ)).natAbs ≤ ℓ / s / 4) → t₀ ≤ cellMargin s (ℓ / s) A →
      ∀ g : (Fin d → ℤ) → Fin N → ℂ, ∑ y ∈ A, ∑ i, ‖g y i‖ < 1 →
      ‖(aT ℓ' (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ')) (fun z => g fun μ => (z μ).valMinAbs) -
          aT ℓ' (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ')) 0) -
        (aT ℓ (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ)) (fun z => g fun μ => (z μ).valMinAbs) -
          aT ℓ (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ)) 0)‖ ≤
        a * Real.exp (-lam * (cellMargin s (ℓ / s) A : ℝ)) *
          Real.exp (-κ' * ((A.card : ℝ) / (s : ℝ) ^ d)) := by
    intro ℓ ℓ' _ _ hdv hdv' hle A hP hcell ht g hg
    rw [hexp]
    exact hC ℓ ℓ' hdv hdv' hle A hP hcell ht g hg
  obtain ⟨Tn, h0, hW, hloc, hbd, hagr, hsum⟩ :=
    cellResum_exists (aT := aT) hd hss' hs' hs0 hB ha hκ hκ' hlam hA hL hBd hC'
  set Bn := B + a * Real.exp κ' + 2 * B * Real.exp (κ' * (t₀ : ℝ)) with hBndef
  have hBn : 0 ≤ Bn := by positivity
  have hBB : B ≤ Bn := by
    have : 0 ≤ a * Real.exp κ' := by positivity
    have : 0 ≤ 2 * B * Real.exp (κ' * (t₀ : ℝ)) := by positivity
    linarith
  have hκκ : κ ≤ κ' := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hLpos : (0 : ℝ) < (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hc₉ : 0 ≤ c₉ := by
    have := hBn.trans hamp
    by_contra hneg
    push Not at hneg
    have : c₉ / 2 * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hLpos
    linarith
  let p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ :=
    fun ℓ _ X g => resumAct s s' aT Tn ℓ X g
  have hagree : ActAgree d N L M kf p := by
    intro ℓ ℓ' _ _ hdv hdv' j y A g _ hbox
    simp only [p]
    rw [resumAct_zero h0, resumAct_zero h0, sub_zero, sub_zero]
    exact resumAct_agree hd hss' hs4 hS hloc hagr ℓ ℓ' hdv hdv' A g hbox
  refine ⟨p, ⟨fun ℓ _ hdv => ⟨?_, ?_, ?_, ?_⟩, hagree.actAt (k + 1)⟩, fun ℓ _ hdv g => ?_⟩
  · intro j X hX g
    simp only [RootFSpine.actAt]
    split_ifs with hj
    · subst hj
      have hnp : ¬ IsPolymer d ℓ s X := fun h => hX ⟨by simp, h⟩
      simp only [p]
      rw [resumAct_supp hS ℓ hdv X hnp g, resumAct_zero h0]
    · rfl
  · exact ActAnalyticAt.actAt (k + 1) fun j X => resumAct_analytic hA hW ℓ hdv X
  · exact ActLocalAt.actAt (k + 1) fun j X g g' h => resumAct_local hL hloc ℓ hdv X g g' h
  · intro j hj X g hg
    simp only [RootFSpine.actAt]
    split_ifs with hjk
    · subst hjk
      simp only [p]
      rw [resumAct_zero h0, sub_zero]
      refine (resumAct_bound hBn hBB hκκ hBd hbd ℓ hdv X g hg).trans ?_
      rw [hexp]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      exact hamp
    · rw [sub_self, norm_zero]
      have : (0 : ℝ) < (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) :=
        Real.rpow_pos_of_pos (by positivity) _
      positivity
  · exact resumAct_sum hS hsum ℓ g

end RootF

end Balaban.RootFSpine.LastScale

