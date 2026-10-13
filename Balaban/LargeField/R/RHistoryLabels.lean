module

public import Balaban.LargeField.Def7
public import Balaban.LargeField.Def7Hist
public import Balaban.LargeField.R.Outcome

/-!
# The labelled histories of the operation `R` (VMOD-37, package 5 `RHistoryLabels`)

Before `R^{(k)}` the class record `IsRepPre2` has `complete : IsComplete k k 𝔄`; after `R^{(k)}`
the record `IsRep2` has `complete : IsComplete k (k+1) 𝔄'` and `pin : D4Pin (k+1)`.  This file
is the finite combinatorics relating the two, on the landed `LabHist`:

* `agree_succ_iff`: `Agree k (k+1)` is `Agree k k` together with equality of `Rem_k` and of the
  kept-label record at scale `k`;
* `LabHist.outcomeAt`, `AdmOutcome`: the scale-`k` outcome of each component (a kept label
  `ϰ ∈ Fin 5`, or removed), read off from `rem k` and `keptLab k`; it is determined by the
  `(k,k+1)`-record and, together with the `(k,k)`-record, determines it
  (`agree_succ_iff_outcome`);
* `fibreEquiv`: the fibre of `(k,k+1)`-classes over a `(k,k)`-class is in bijection with the
  realized outcome assignments;
* `isComplete_succ_of_enum`, `exists_enum`: the new complete index set and the projection;
* `realized_of_relabel`: every relabelling of the kept components is realized;
* `d4Pin_succ_iff`: `D4Pin (k+1)` is `D4Pin k` together with the pin at scale `k`.

NOT proved here: the physical statement `OPEN-R-PRESERVES-ISREP2` (construction of the post
family and density, the identity `ρ⁺ = R ρ⁻`, operator bounds, budget, D1/D7 fields).
-/

@[expose] public section

namespace Balaban.LargeField.Def7

open Balaban Balaban.LargeField RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

/-! ### T1 -/

/-- `Agree k (k+1)` compares, beyond `Agree k k`, exactly the removed set `Rem_k` and the
kept-label record at scale `k`. -/
theorem agree_succ_iff (k : ℕ) (A B : LabHist S n R k0 K) :
    A.Agree k (k + 1) B ↔ A.Agree k k B ∧ A.H.rem k = B.H.rem k ∧ A.keptLab k = B.keptLab k := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun j hj => h2 j (by omega)⟩, h2 k (by omega)⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
    · exact h2 j h
    · exact ⟨h3, h4⟩

/-! ### T2: the outcome assignment -/

open Classical in
/-- **The scale-`k` outcome of a history**: at a set of cubes `c`, `some rem` if `c ∈ Rem_k`,
`some (kept ϰ)` if `c` is a kept component with label `ϰ`, and `none` otherwise. -/
noncomputable def LabHist.outcomeAt (A : LabHist S n R k0 K) (k : ℕ)
    (c : Finset (Torus S.d (n k))) : Option Outcome :=
  if c ∈ A.H.rem k then some Outcome.rem else (A.keptLab k c).map Outcome.kept

theorem LabHist.keptLab_of_mem_rem (A : LabHist S n R k0 K) {k : ℕ}
    {c : Finset (Torus S.d (n k))} (h : c ∈ A.H.rem k) : A.keptLab k c = none := by
  classical
  unfold LabHist.keptLab
  split_ifs with h1 h2
  · exact absurd h h2.2
  · rfl
  · rfl

theorem LabHist.mem_rem_iff_outcomeAt (A : LabHist S n R k0 K) (k : ℕ)
    (c : Finset (Torus S.d (n k))) : c ∈ A.H.rem k ↔ A.outcomeAt k c = some Outcome.rem := by
  classical
  unfold LabHist.outcomeAt
  by_cases h : c ∈ A.H.rem k
  · simp [h]
  · simp only [h, ite_false, false_iff]
    cases A.keptLab k c <;> simp

/-- The outcome assignment at scale `k` is the pair (`Rem_k`, kept labels at scale `k`). -/
theorem outcomeAt_eq_iff (A B : LabHist S n R k0 K) (k : ℕ) :
    A.outcomeAt k = B.outcomeAt k ↔ A.H.rem k = B.H.rem k ∧ A.keptLab k = B.keptLab k := by
  classical
  constructor
  · intro h
    have hr : A.H.rem k = B.H.rem k := by
      ext c
      rw [A.mem_rem_iff_outcomeAt, B.mem_rem_iff_outcomeAt, h]
    refine ⟨hr, funext fun c => ?_⟩
    by_cases hc : c ∈ A.H.rem k
    · rw [A.keptLab_of_mem_rem hc, B.keptLab_of_mem_rem (hr ▸ hc)]
    · have hc' : c ∉ B.H.rem k := hr ▸ hc
      have := congrFun h c
      simp only [LabHist.outcomeAt, hc, hc', ite_false] at this
      exact Option.map_injective (fun a b hab => by cases hab; rfl) this
  · rintro ⟨h1, h2⟩
    funext c
    simp only [LabHist.outcomeAt, h1, h2]

/-- **T1 in terms of outcomes**: two histories agree at `(k,k+1)` iff they agree at `(k,k)` and
have the same scale-`k` outcome assignment. -/
theorem agree_succ_iff_outcome (k : ℕ) (A B : LabHist S n R k0 K) :
    A.Agree k (k + 1) B ↔ A.Agree k k B ∧ A.outcomeAt k = B.outcomeAt k := by
  rw [agree_succ_iff, outcomeAt_eq_iff]

/-- The outcome assignment is determined by the `(k,k+1)`-record. -/
theorem outcomeAt_eq_of_agree {k : ℕ} {A B : LabHist S n R k0 K} (h : A.Agree k (k + 1) B) :
    A.outcomeAt k = B.outcomeAt k :=
  ((agree_succ_iff_outcome k A B).mp h).2

/-- **Admissible outcome assignments** (for a history `A`): an outcome is assigned exactly to the
ripe components of `Z^pre_k` at the scales `1 ≤ k ≤ k₀` in which `R` acts (`IsKept`); at every
other set of cubes, and at every scale outside `[1,k₀]`, the value is `none`. -/
def AdmOutcome (A : LabHist S n R k0 K) (k : ℕ)
    (f : Finset (Torus S.d (n k)) → Option Outcome) : Prop :=
  ∀ c, (f c).isSome ↔ ∃ h : c ∈ comps (S.omega k) (A.H.Zp k), IsKept A.H k ⟨c, h⟩

/-- The outcome assignment of a history is admissible: removed components are ripe
(`Admissible`), and every other ripe component is kept with a label. -/
theorem outcomeAt_adm (A : LabHist S n R k0 K) (k : ℕ) : AdmOutcome A k (A.outcomeAt k) := by
  classical
  intro c
  by_cases hr : c ∈ A.H.rem k
  · have hc : c ∈ comps (S.omega k) (A.H.Zp k) := A.H.rem_sub k hr
    have hk : IsKept A.H k ⟨c, hc⟩ := by
      have hrip := A.adm k ⟨c, hc⟩ hr
      refine ⟨?_, ?_, hrip⟩
      · by_contra h0
        have : k = 0 := by omega
        simp [A.H.rem_empty k (Or.inl this)] at hr
      · by_contra h0
        simp [A.H.rem_empty k (Or.inr (by omega))] at hr
    simp [LabHist.outcomeAt, hr, hc, hk]
  · simp only [LabHist.outcomeAt, hr, ite_false, Option.isSome_map]
    unfold LabHist.keptLab
    by_cases hc : c ∈ comps (S.omega k) (A.H.Zp k)
    · simp only [hc, hr, not_false_eq_true, and_true]
      by_cases hk : IsKept A.H k ⟨c, hc⟩ <;> simp [hk]
    · simp [hc]

/-! ### T3: the fibre and the enumeration -/

/-- The scale-`k` outcome assignments realized by histories with the `(k,k)`-record of `A`. -/
def Realized (k : ℕ) (A : LabHist S n R k0 K) :
    Set (Finset (Torus S.d (n k)) → Option Outcome) :=
  {f | ∃ B : LabHist S n R k0 K, B.Agree k k A ∧ B.outcomeAt k = f}

/-- A realized assignment is admissible for a history realizing it. -/
theorem realized_adm {k : ℕ} {A : LabHist S n R k0 K} {f} (hf : f ∈ Realized k A) :
    ∃ B : LabHist S n R k0 K, B.Agree k k A ∧ AdmOutcome B k f := by
  obtain ⟨B, hB, rfl⟩ := hf
  exact ⟨B, hB, outcomeAt_adm B k⟩

/-- The `(k,k+1)`-classes of histories lying over the `(k,k)`-class of `A`. -/
def fibreSetoid (k : ℕ) (A : LabHist S n R k0 K) :
    Setoid {B : LabHist S n R k0 K // B.Agree k k A} :=
  Setoid.comap Subtype.val (agreeSetoid S n R k0 K k (k + 1))

/-- **The fibre of the forgetful map** `(k,k+1)`-records `→` `(k,k)`-records over the class of
`A` is in bijection with the realized outcome assignments. -/
noncomputable def fibreEquiv (k : ℕ) (A : LabHist S n R k0 K) :
    Quotient (fibreSetoid k A) ≃ Realized k A :=
  Equiv.ofBijective
    (Quotient.lift (fun B => (⟨B.1.outcomeAt k, B.1, B.2, rfl⟩ : Realized k A))
      (fun B B' h => Subtype.ext (outcomeAt_eq_of_agree h)))
    ⟨by
      rintro ⟨B⟩ ⟨B'⟩ h
      have h' : B.1.outcomeAt k = B'.1.outcomeAt k := congrArg Subtype.val h
      exact Quotient.sound ((agree_succ_iff_outcome k B.1 B'.1).mpr
        ⟨LabHist.agree_trans B.2 (LabHist.agree_symm B'.2), h'⟩),
     by
      rintro ⟨f, B, hB, rfl⟩
      exact ⟨⟦⟨B, hB⟩⟧, rfl⟩⟩

/-- Realized assignments depend only on the `(k,k)`-class. -/
theorem realized_congr {k : ℕ} {A A' : LabHist S n R k0 K} (h : A.Agree k k A') :
    Realized k A = Realized k A' := by
  ext f
  exact ⟨fun ⟨B, hB, hf⟩ => ⟨B, LabHist.agree_trans hB h, hf⟩,
    fun ⟨B, hB, hf⟩ => ⟨B, LabHist.agree_trans hB (LabHist.agree_symm h), hf⟩⟩

/-- **Transport of completeness (enumeration)**: if `𝔄` is complete at `(k,k)` and `𝔄'` contains
exactly one history for every pair (element `A ∈ 𝔄`, realized assignment `f`), then `𝔄'` is
complete at `(k,k+1)`. -/
theorem isComplete_succ_of_enum {k : ℕ} {𝔄 𝔄' : Finset (LabHist S n R k0 K)}
    (h𝔄 : IsComplete k k 𝔄)
    (h𝔄' : ∀ A ∈ 𝔄, ∀ f ∈ Realized k A,
      ∃! B, B ∈ 𝔄' ∧ B.Agree k k A ∧ B.outcomeAt k = f) :
    IsComplete k (k + 1) 𝔄' := by
  intro C
  obtain ⟨A, ⟨hA, hCA⟩, -⟩ := h𝔄 C
  obtain ⟨B, ⟨hB, hBA, hBf⟩, huniq⟩ :=
    h𝔄' A hA (C.outcomeAt k) ⟨C, hCA, rfl⟩
  refine ⟨B, ⟨hB, (agree_succ_iff_outcome k C B).mpr
    ⟨LabHist.agree_trans hCA (LabHist.agree_symm hBA), hBf.symm⟩⟩, ?_⟩
  rintro B' ⟨hB', hCB'⟩
  obtain ⟨h1, h2⟩ := (agree_succ_iff_outcome k C B').mp hCB'
  exact huniq B' ⟨hB', LabHist.agree_trans (LabHist.agree_symm h1) hCA, h2.symm.trans rfl⟩

open Classical in
/-- The projection onto a complete `(k,k)`-set: the representative in `𝔄` agreeing with `B`
at `(k,k)` (and `B` itself if there is none). -/
noncomputable def projTo (k : ℕ) (𝔄 : Finset (LabHist S n R k0 K)) (B : LabHist S n R k0 K) :
    LabHist S n R k0 K :=
  if h : ∃ A ∈ 𝔄, B.Agree k k A then h.choose else B

theorem projTo_eq {k : ℕ} {𝔄 : Finset (LabHist S n R k0 K)} (h𝔄 : IsComplete k k 𝔄)
    {B A : LabHist S n R k0 K} (hA : A ∈ 𝔄) (hBA : B.Agree k k A) : projTo k 𝔄 B = A := by
  classical
  have h : ∃ A ∈ 𝔄, B.Agree k k A := ⟨A, hA, hBA⟩
  unfold projTo
  simp only [h, ↓reduceDIte]
  exact (h𝔄 B).unique ⟨h.choose_spec.1, h.choose_spec.2⟩ ⟨hA, hBA⟩

/-- **Existence of the structured complete set with projection**: for `𝔄` complete at `(k,k)`
there are a finite `𝔄'` complete at `(k,k+1)` and a projection `π : 𝔄' → 𝔄` (`π B` is the
representative in `𝔄` agreeing with `B` at `(k,k)`), surjective, whose fibre over each `A ∈ 𝔄`
is in bijection (by `B ↦ outcomeAt B k`) with the realized assignments `Realized k A`. -/
theorem exists_enum {k : ℕ} {𝔄 : Finset (LabHist S n R k0 K)} (h𝔄 : IsComplete k k 𝔄) :
    ∃ 𝔄' : Finset (LabHist S n R k0 K),
      IsComplete k (k + 1) 𝔄' ∧
      (∀ B ∈ 𝔄', projTo k 𝔄 B ∈ 𝔄 ∧ B.Agree k k (projTo k 𝔄 B)) ∧
      (∀ A ∈ 𝔄, ∃ B ∈ 𝔄', projTo k 𝔄 B = A) ∧
      (∀ A ∈ 𝔄, Set.BijOn (fun B => B.outcomeAt k) {B | B ∈ 𝔄' ∧ projTo k 𝔄 B = A}
        (Realized k A)) := by
  classical
  obtain ⟨𝔄', h'⟩ := exists_isComplete (S := S) (n := n) (R := R) (k0 := k0) (K := K) k (k + 1)
  refine ⟨𝔄', h', fun B _ => ?_, fun A hA => ?_, fun A hA => ?_⟩
  · obtain ⟨A, ⟨hA, hBA⟩, -⟩ := h𝔄 B
    rw [projTo_eq h𝔄 hA hBA]
    exact ⟨hA, hBA⟩
  · obtain ⟨B, ⟨hB, hAB⟩, -⟩ := h' A
    exact ⟨B, hB, projTo_eq h𝔄 hA
      (LabHist.agree_symm ((agree_succ_iff k A B).mp hAB).1)⟩
  · refine ⟨fun B hB => ?_, fun B hB B' hB' h => ?_, fun f hf => ?_⟩
    · obtain ⟨hB, hπ⟩ := hB
      obtain ⟨A₀, ⟨hA₀, hBA₀⟩, -⟩ := h𝔄 B
      rw [projTo_eq h𝔄 hA₀ hBA₀] at hπ
      exact ⟨B, hπ ▸ hBA₀, rfl⟩
    · obtain ⟨hB, hπ⟩ := hB
      obtain ⟨hB', hπ'⟩ := hB'
      obtain ⟨A₀, ⟨hA₀, hBA₀⟩, -⟩ := h𝔄 B
      obtain ⟨A₁, ⟨hA₁, hBA₁⟩, -⟩ := h𝔄 B'
      rw [projTo_eq h𝔄 hA₀ hBA₀] at hπ
      rw [projTo_eq h𝔄 hA₁ hBA₁] at hπ'
      subst hπ; subst hπ'
      exact (h' B).unique ⟨hB, LabHist.agree_refl _ _ B⟩
        ⟨hB', (agree_succ_iff_outcome k B B').mpr
          ⟨LabHist.agree_trans hBA₀ (LabHist.agree_symm hBA₁), h⟩⟩
    · obtain ⟨C, hCA, rfl⟩ := hf
      obtain ⟨B, ⟨hB, hCB⟩, -⟩ := h' C
      obtain ⟨h1, h2⟩ := (agree_succ_iff_outcome k C B).mp hCB
      exact ⟨B, ⟨hB, projTo_eq h𝔄 hA (LabHist.agree_trans (LabHist.agree_symm h1) hCA)⟩,
        h2.symm⟩

/-! ### T4: realizability and the cardinality bound -/

/-- Relabel an outcome with the kept label `g`: kept outcomes get the new label, `rem` stays. -/
def Outcome.relabel (g : Fin 5) : Outcome → Outcome
  | Outcome.kept _ => Outcome.kept g
  | Outcome.rem => Outcome.rem

/-- The history with the labels of scale `k` replaced by `g` (same region history). -/
def LabHist.relabel (A : LabHist S n R k0 K) (k : ℕ) (g : Finset (Torus S.d (n k)) → Fin 5) :
    LabHist S n R k0 K where
  H := A.H
  adm := A.adm
  lab := fun j c => if h : j = k then g (h ▸ c) else A.lab j c

theorem LabHist.keptLab_relabel_ne (A : LabHist S n R k0 K) (k : ℕ)
    (g : Finset (Torus S.d (n k)) → Fin 5) {j : ℕ} (hj : j ≠ k)
    (c : Finset (Torus S.d (n j))) : (A.relabel k g).keptLab j c = A.keptLab j c := by
  classical
  unfold LabHist.keptLab
  change (if h : c ∈ comps (S.omega j) (A.H.Zp j) then
      if IsKept A.H j ⟨c, h⟩ ∧ c ∉ A.H.rem j then some ((A.relabel k g).lab j c) else none
    else none) = _
  split_ifs <;> simp_all [LabHist.relabel]

theorem LabHist.keptLab_relabel (A : LabHist S n R k0 K) (k : ℕ)
    (g : Finset (Torus S.d (n k)) → Fin 5) (c : Finset (Torus S.d (n k))) :
    (A.relabel k g).keptLab k c = (A.keptLab k c).map (fun _ => g c) := by
  classical
  unfold LabHist.keptLab
  change (if h : c ∈ comps (S.omega k) (A.H.Zp k) then
      if IsKept A.H k ⟨c, h⟩ ∧ c ∉ A.H.rem k then some ((A.relabel k g).lab k c) else none
    else none) = _
  split_ifs <;> simp_all [LabHist.relabel]

theorem LabHist.relabel_agree (A : LabHist S n R k0 K) (k : ℕ)
    (g : Finset (Torus S.d (n k)) → Fin 5) : (A.relabel k g).Agree k k A :=
  ⟨fun j _ => ⟨rfl, rfl, rfl, rfl⟩, fun j hj =>
    ⟨rfl, funext fun c => A.keptLab_relabel_ne k g (by omega) c⟩⟩

theorem LabHist.relabel_outcomeAt (A : LabHist S n R k0 K) (k : ℕ)
    (g : Finset (Torus S.d (n k)) → Fin 5) (c : Finset (Torus S.d (n k))) :
    (A.relabel k g).outcomeAt k c = (A.outcomeAt k c).map (Outcome.relabel (g c)) := by
  classical
  by_cases hr : c ∈ A.H.rem k
  · simp [LabHist.outcomeAt, LabHist.relabel, hr, Outcome.relabel]
  · simp only [LabHist.outcomeAt, hr, ite_false]
    show (if c ∈ A.H.rem k then _ else _) = _
    rw [A.keptLab_relabel k g c]
    simp only [hr, ite_false]
    cases A.keptLab k c <;> simp [Outcome.relabel]

/-- **Realizability of every relabelling**: for every choice `g` of labels, the assignment of `A`
with the kept labels replaced by `g` is realized by a history with the `(k,k)`-record of `A`.
(With `g` constant this is "all kept components get the same label".  Changing the *removed* set
is not covered, see the module report: it changes `Z_k` and the later steps.) -/
theorem realized_of_relabel (A : LabHist S n R k0 K) (k : ℕ)
    (g : Finset (Torus S.d (n k)) → Fin 5) :
    (fun c => (A.outcomeAt k c).map (Outcome.relabel (g c))) ∈ Realized k A :=
  ⟨A.relabel k g, A.relabel_agree k g, funext (A.relabel_outcomeAt k g)⟩

theorem Outcome.card : Fintype.card Outcome = 6 :=
  (Fintype.ofEquiv_card _).trans (by simp)

/-- **Cardinality bound on a fibre, fixed set of outcome-carrying components**: the realized
assignments whose set of components carrying an outcome is exactly the finite set `s` number at
most `6 ^ s.card` (one of the six outcomes per component). -/
theorem ncard_realized_support_le (k : ℕ) (A : LabHist S n R k0 K)
    (s : Finset (Finset (Torus S.d (n k)))) :
    {f ∈ Realized k A | ∀ c, (f c).isSome ↔ c ∈ s}.ncard ≤ 6 ^ s.card := by
  classical
  have hfin : (Set.univ : Set (s → Outcome)).Finite := Set.toFinite _
  have hcard : (Set.univ : Set (s → Outcome)).ncard = 6 ^ s.card := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Outcome.card,
      Fintype.card_coe]
  rw [← hcard]
  refine Set.ncard_le_ncard_of_injOn (fun f c => (f c.1).getD Outcome.rem) (fun _ _ => trivial)
    ?_ hfin
  rintro f ⟨-, hf⟩ g ⟨-, hg⟩ h
  funext c
  by_cases hc : c ∈ s
  · have h1 := congrFun h ⟨c, hc⟩
    have hf' := (hf c).2 hc
    have hg' := (hg c).2 hc
    simp only at h1
    cases hfc : f c <;> cases hgc : g c <;> simp_all
  · have hf' : f c = none := by simpa [hc] using hf c
    have hg' : g c = none := by simpa [hc] using hg c
    rw [hf', hg']

/-- The regions `Z^pre_j`, `j ≤ k`, are functions of the `(k,k)`-record. -/
theorem zpre_eq_of_agree {k : ℕ} {A B : LabHist S n R k0 K} (h : A.Agree k k B) :
    ∀ j, j ≤ k → A.H.F.Zpre j = B.H.F.Zpre j := by
  intro j
  induction j with
  | zero => intro _; simp [FlowSteps.Zpre]
  | succ j ih =>
    intro hj
    have hj' : j < k := hj
    have hZ : (A.H.step j).Z = (B.H.step j).Z := by
      rw [A.H.Z_eq, B.H.Z_eq, ih hj'.le, (h.2 j hj').1]
    obtain ⟨hP, hQ, hR, hS⟩ := h.1 j hj'
    unfold FlowSteps.Zpre
    have key : ∀ (st st' : RegionStep S.d S.L (n j) (n (j + 1)) (R (j - 1)) (R j)),
        st.Z = st'.Z → st.P = st'.P → st.Q = st'.Q → st.R = st'.R → st.S = st'.S →
        ∀ (ω : ℕ) (c : Option ℕ), st.Zpre ω c = st'.Zpre ω c := by
      intro st st'
      obtain ⟨Z, P, Q, R', S', -, -, -, -⟩ := st
      obtain ⟨Z', P', Q', R'', S'', -, -, -, -⟩ := st'
      intro h1 h2 h3 h4 h5 ω c
      simp only at h1 h2 h3 h4 h5
      subst h1 h2 h3 h4 h5
      rfl
    exact key _ _ hZ hP hQ hR hS _ _

/-- The components of `Z^pre_k` are the same for the histories of one `(k,k)`-class. -/
theorem comps_zp_eq_of_agree {k : ℕ} {A B : LabHist S n R k0 K} (h : A.Agree k k B) :
    comps (S.omega k) (A.H.Zp k) = comps (S.omega k) (B.H.Zp k) := by
  have := zpre_eq_of_agree h k le_rfl
  show comps (S.omega k) (finOf (A.H.F.Zpre k)) = comps (S.omega k) (finOf (B.H.F.Zpre k))
  rw [this]

/-- A realized assignment is supported on the components of `Z^pre_k`, which depend only on
the `(k,k)`-record. -/
theorem realized_support_subset {k : ℕ} {A : LabHist S n R k0 K} {f}
    (hf : f ∈ Realized k A) (c) (hc : (f c).isSome) : c ∈ comps (S.omega k) (A.H.Zp k) := by
  obtain ⟨B, hB, rfl⟩ := hf
  have := ((outcomeAt_adm B k) c).1 hc
  obtain ⟨h, -⟩ := this
  have e := comps_zp_eq_of_agree hB
  exact Eq.mp (congrArg (c ∈ ·) e) h

/-! ### T5: the top pin -/

section Pin

variable {M N : ℕ} [NeZero M] [NeZero S.L] {geo : Geo S n R M} {cs : OpConsts}
  {P : BudgetConsts} {k : ℕ}

/-- **Transport of the pin**: `D4Pin (k+1)` is `D4Pin k` together with the pin
`κ_k(Z, 𝔸 ∩ Z) = κ^pre_k(Z, 𝔸 ∩ Z)` at the kept components of scale `k` of every history in
`𝔄` (the new scale-`k` kept label exponent; `1 ≤ k`). -/
theorem d4Pin_succ_iff {k0' : ℕ} (rep : Rep S n R k0 K M N geo cs P k0') (j : ℕ) :
    D4Pin (j + 1) rep ↔ D4Pin j rep ∧
      (1 ≤ j → ∀ A ∈ rep.hist, ∀ Z : A.H.Comp j, IsKept A.H j Z → Z.1 ∉ A.H.rem j →
        rep.κK j (A.H.localHistory M K j Z) = rep.kappaPreH A j Z) := by
  constructor
  · intro h
    exact ⟨fun A hA i hi hij => h A hA i hi (by omega),
      fun hj A hA Z hK hr => h A hA j hj (by omega) Z hK hr⟩
  · rintro ⟨h1, h2⟩ A hA i hi hij Z hK hr
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | rfl
    · exact h1 A hA i hi h Z hK hr
    · exact h2 hi A hA Z hK hr

end Pin

end Balaban.LargeField.Def7
