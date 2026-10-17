module

public import Balaban.LargeField.Base.BaseFirstRecordCount

/-!
# The local first-record quotient and its six-bit code

A local record is the image of a base record under restriction of its four cube sets to
one component. Taking the image identifies global records that differ only outside the
component. Two spare binary fields make this four-field code a six-field code.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban

open Classical in
/-- Equality of four local bit fields is exactly equality of the four record sets on `X`. -/
theorem baseFirstRecord_localBits_eq_iff
    {d L n1 : ℕ} [NeZero n1] {Rk : ℝ}
    (X : Finset (Torus d n1)) (br br' : BaseRecord d L n1 Rk) :
    (fun (j : Fin 4) (x : X) =>
      if j = 0 then decide (x.1 ∈ br.P)
      else if j = 1 then decide (x.1 ∈ br.Q)
      else if j = 2 then decide (x.1 ∈ br.R)
      else decide (x.1 ∈ br.S)) =
    (fun (j : Fin 4) (x : X) =>
      if j = 0 then decide (x.1 ∈ br'.P)
      else if j = 1 then decide (x.1 ∈ br'.Q)
      else if j = 2 then decide (x.1 ∈ br'.R)
      else decide (x.1 ∈ br'.S)) ↔
      ∀ x : X, (x.1 ∈ br.P ↔ x.1 ∈ br'.P) ∧
        (x.1 ∈ br.Q ↔ x.1 ∈ br'.Q) ∧
        (x.1 ∈ br.R ↔ x.1 ∈ br'.R) ∧
        (x.1 ∈ br.S ↔ x.1 ∈ br'.S) := by
  classical
  constructor
  · intro heq x
    have hp : decide (x.1 ∈ br.P) = decide (x.1 ∈ br'.P) := by
      simpa using congrFun (congrFun heq (0 : Fin 4)) x
    have hq : decide (x.1 ∈ br.Q) = decide (x.1 ∈ br'.Q) := by
      simpa using congrFun (congrFun heq (1 : Fin 4)) x
    have hr : decide (x.1 ∈ br.R) = decide (x.1 ∈ br'.R) := by
      simpa using congrFun (congrFun heq (2 : Fin 4)) x
    have hs : decide (x.1 ∈ br.S) = decide (x.1 ∈ br'.S) := by
      simpa using congrFun (congrFun heq (3 : Fin 4)) x
    exact ⟨decide_eq_decide.mp hp, decide_eq_decide.mp hq,
      decide_eq_decide.mp hr, decide_eq_decide.mp hs⟩
  · intro h
    funext j x
    obtain ⟨hp, hq, hr, hs⟩ := h x
    fin_cases j
    · simp [hp]
    · simp [hq]
    · simp [hr]
    · simp [hs]

open Classical in
/-- The image of global admissible base records under restriction to `X` has total
six-bit coding cost at most one. Global records with the same four restricted sets occur
only once in this image. -/
theorem baseFirstRecord_localRestriction_weighted_count
    {d L n1 : ℕ} [NeZero n1] {Rk : ℝ}
    (X : Finset (Torus d n1)) (records : Finset (BaseRecord d L n1 Rk))
    (hd : 3 ≤ d) (hL : 2 ≤ L) :
    let localRecords : Finset (Fin 4 → X → Bool) :=
      records.image fun br => fun j x =>
        if j = 0 then decide (x.1 ∈ br.P)
        else if j = 1 then decide (x.1 ∈ br.Q)
        else if j = 2 then decide (x.1 ∈ br.R)
        else decide (x.1 ∈ br.S)
    ∑ _r ∈ localRecords, Real.exp (-(5 / 4 : ℝ) * (L : ℝ) ^ d * X.card) ≤ 1 := by
  classical
  dsimp only
  let localRecords : Finset (Fin 4 → X → Bool) :=
    records.image fun br => fun j x =>
      if j = 0 then decide (x.1 ∈ br.P)
      else if j = 1 then decide (x.1 ∈ br.Q)
      else if j = 2 then decide (x.1 ∈ br.R)
      else decide (x.1 ∈ br.S)
  let code : localRecords → Fin 6 → X → Bool := fun r j x =>
    if hj : j.val < 4 then r.1 ⟨j.val, hj⟩ x else false
  have hcode : Function.Injective code := by
    intro r r' heq
    apply Subtype.ext
    funext j x
    let i : Fin 6 := ⟨j.val, lt_trans j.isLt (by norm_num)⟩
    have hi := congrFun (congrFun heq i) x
    simpa [code, i, j.isLt] using hi
  exact baseFirstRecord_weighted_count_of_injectiveCoding X localRecords code hcode
    d L hd hL

end Balaban.LargeField
