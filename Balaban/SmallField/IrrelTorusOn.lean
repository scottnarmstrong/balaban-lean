/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2
public import Balaban.SmallField.RenormTermwiseAnalytic
public import Balaban.Polymer.BoxTransport

/-!
# The irrelevant part of a term on the torus, renormalizing a selected family of polymers

P1 Proposition 3.10 and (3.126)–(3.127), pp. 152–153.  The label functional `irrelTorus`
subtracts from the term `ℰ(y, X)` of every label its relevant local part `T_X + Φ_{y,X}` and files
the sum of these parts over the polymers through `y` at the cell `□(y)`.  Here the polymers whose
relevant part is subtracted (and filed) are those of a selection `sm y X`:

`ℰ^{sm}_{irrel}(y, X) = ℰ(y, X) - 1_{sm y X} (T_X + Φ_{y,X}) - A_{y,X}
  + 1_{X = □(y)} Σ_{Z ∋ y, sm y Z} (T_Z + Φ_{y,Z})`.

* `relPartTorus`: the relevant local part `T_Z + Φ_{y,Z}` of the term of a polymer `Z` at the centre
  `y`, a function of `Ψ(y)`, `h(y)` and the stencil `Ψ(y + L^j e_μ)` only;
* `aTermTorus`: the term `A_{y,X} = ½ Σ_{x ∈ X} a_X(x) (Ψ(x)·Ψ(x) - Ψ(y)·Ψ(y))`;
* `irrelTorusOn sm`: the label functional of the selection `sm`; `irrelTorus` is the selection of
  all polymers (`irrelTorus_eq_irrelTorusOn`), and `relBox m₀` selects the polymers in the box of
  half-side `r_k = ⌊L^{m₀+m₁+k}/8⌋` (fine sites) around `y`, which do not wind around any torus
  with `L^{m₀} ∣ N₁`;
* `irrelTorusOn_congr`, `irrelTorusOn_analyticOnNhd`, `irrelTorusOn_rot`: the locality, analyticity
  and `O(N)` invariance of the label functional (FLUCTUATION.md Lemma 3.2 (ii)), for every
  selection.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **The relevant local part `T_Z + Φ_{y,Z}` of the term of a polymer `Z` at the centre `y`**
(P1 (3.104), (3.126); FLUCTUATION.md §3.2): with the reference field `e = e_{i₀}`, the aligned
sites `x ∈ Z`, `a_Z(x) = ∂ℰ(y,Z)/∂ψ_{i₀}(x)` at `e`, `u = √(Ψ(y)·Ψ(y))`,
`∂_μΨ = Ψ(y + L^j e_μ) - Ψ(y)` and the centred integer positions of the blocks,
`T_Z = ℰ(y,Z)(e) + (u - 1) Σ_x a_Z(x) + (Ψ(y)·h(y)/u - 1) ∂_h ℰ(y,Z)(e)·e` and
`Φ_{y,Z} = -¼ Σ_{μν} [∂_μΨ·∂_νΨ - (Ψ(y)·∂_μΨ)(Ψ(y)·∂_νΨ)/(Ψ(y)·Ψ(y))] S_Z^{μν}`. -/
noncomputable def relPartTorus (Tm : Terms d L N₁ m₁ k N ϱ) (i₀ i₁ : Fin N) (j : ℕ)
    (y : CTorus d L N₁ m₁ k) (Ψ h : Fld d L N₁ m₁ k N) (Z : Set (CTorus d L N₁ m₁ k)) : ℂ :=
  let e : Fld d L N₁ m₁ k N := constFld (Pi.single i₀ 1)
  let blk : Set (CTorus d L N₁ m₁ k) → Finset (CTorus d L N₁ m₁ k) := fun Z =>
    Finset.univ.filter fun x => Aligned (L ^ j) x ∧ x ∈ Z
  let u : ℂ := sqrtC (dot (Ψ y) (Ψ y))
  let dΨ : Fin d → Fin N → ℂ := fun μ =>
    Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ y
  let g : Fin d → Fin d → ℂ := fun μ μ' =>
    dot (dΨ μ) (dΨ μ') - dot (Ψ y) (dΨ μ) * dot (Ψ y) (dΨ μ') / dot (Ψ y) (Ψ y)
  let lift : CTorus d L N₁ m₁ k → Fin d → ℂ := fun z μ =>
    ((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) μ : ℤ) : ℂ)
  let a : Set (CTorus d L N₁ m₁ k) → CTorus d L N₁ m₁ k → ℂ := fun Z x =>
    fderiv ℂ (fun Ψ' => Tm.E j y Z Ψ' e) e (blockDir L j x i₀)
  Tm.E j y Z e e + (u - 1) * ∑ x ∈ blk Z, a Z x
    + (dot (Ψ y) (h y) / u - 1) * fderiv ℂ (fun h' => Tm.E j y Z e h') e e
    - (1 / 4 : ℂ) * ∑ μ, ∑ μ', g μ μ' * ∑ x ∈ blk Z, ∑ x' ∈ blk Z,
        D2 (fun Ψ' => Tm.E j y Z Ψ' e) e (blockDir L j x i₁) (blockDir L j x' i₁) *
          ((lift x μ - lift x' μ) * (lift x μ' - lift x' μ'))

open Classical in
/-- **The term `A_{y,X}`** (P1 (3.109), FLUCTUATION.md §3.2):
`A_{y,X} = ½ Σ_{x ∈ X aligned} a_X(x) (Ψ(x)·Ψ(x) - Ψ(y)·Ψ(y))`, `a_X(x) = ∂ℰ(y,X)/∂ψ_{i₀}(x)` at the
reference field `e_{i₀}`. -/
noncomputable def aTermTorus (Tm : Terms d L N₁ m₁ k N ϱ) (i₀ : Fin N) (j : ℕ)
    (y : CTorus d L N₁ m₁ k) (Ψ : Fld d L N₁ m₁ k N) (X : Set (CTorus d L N₁ m₁ k)) : ℂ :=
  (1 / 2 : ℂ) * ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
    fderiv ℂ (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1))) (constFld (Pi.single i₀ 1))
      (blockDir L j x i₀) * (dot (Ψ x) (Ψ x) - dot (Ψ y) (Ψ y))

open Classical in
/-- **The irrelevant part of the term of a label `(j, y, X)` for a selection `sm` of the renormalized
polymers** (P1 Proposition 3.10, (3.126)–(3.127)):
`ℰ^{sm}_{irrel}(y, X) = ℰ(y,X) - 1_{sm y X} (T_X + Φ_{y,X}) - A_{y,X}
  + 1_{X = □(y)} Σ_{Z ∈ 𝒟_j, Z ∋ y, sm y Z} (T_Z + Φ_{y,Z})`,
`□(y)` the `π'_j`-cube whose central `π_j`-cube is the cell of `y`.  The sum over the labels at a
centre is the sum of the terms minus `Σ_X A_{y,X}` for every selection (`finsum_irrelTorusOn_eq`). -/
noncomputable def irrelTorusOn (sm : CTorus d L N₁ m₁ k → Set (CTorus d L N₁ m₁ k) → Prop)
    (m₀ : ℕ) (Tm : Terms d L N₁ m₁ k N ϱ) (i₀ i₁ : Fin N) (j : ℕ) (y : CTorus d L N₁ m₁ k)
    (X : Set (CTorus d L N₁ m₁ k)) (Ψ h : Fld d L N₁ m₁ k N) : ℂ :=
  Tm.E j y X Ψ h - (if sm y X then relPartTorus Tm i₀ i₁ j y Ψ h X else 0)
    - aTermTorus Tm i₀ j y Ψ X
    + if X = box (cbase (cellSide L m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L m₀ m₁ j)
        (L * cellSide L m₀ m₁ j) then
      ∑ᶠ Z ∈ polysAt m₀ j y, (if sm y Z then relPartTorus Tm i₀ i₁ j y Ψ h Z else 0) else 0

/-- **The polymers renormalized at the centre `y` in finite volume**: `X` lies in the box of
half-side `r_k = ⌊L^{m₀+m₁+k}/8⌋` (in fine sites) around `y`.  `r_k` is an eighth of the side of the
smallest torus with `L^{m₀} ∣ N₁`, so such a polymer does not wind around any of these tori. -/
def relBox (m₀ : ℕ) (y : CTorus d L N₁ m₁ k) (X : Set (CTorus d L N₁ m₁ k)) : Prop :=
  ∀ z ∈ X, Balaban.Polymer.InBox d (L ^ (m₀ + m₁ + k) / 8) ((N₁ * L ^ m₁) * L ^ k) (z - y)

/-- **The label functional renormalizing the polymers of the box around the centre**
(`relBox`): large polymers keep their relevant parts, which are small by their size. -/
noncomputable abbrev irrelTorusB (m₀ : ℕ) (Tm : Terms d L N₁ m₁ k N ϱ) (i₀ i₁ : Fin N) (j : ℕ)
    (y : CTorus d L N₁ m₁ k) (X : Set (CTorus d L N₁ m₁ k)) (Ψ h : Fld d L N₁ m₁ k N) : ℂ :=
  irrelTorusOn (relBox m₀) m₀ Tm i₀ i₁ j y X Ψ h

section API

variable {P : Consts} {Dom : FieldDom d L N₁ m₁ k N ϱ} {Tm : Terms d L N₁ m₁ k N ϱ}

/-- The relevant local part depends on the fields only through `Ψ(y)`, `h(y)` and the stencil
`Ψ(y + L^j e_μ)`. -/
theorem relPartTorus_congr (Tm : Terms d L N₁ m₁ k N ϱ) (i₀ i₁ : Fin N) (j : ℕ)
    {y : CTorus d L N₁ m₁ k} {Ψ Ψ' h h' : Fld d L N₁ m₁ k N} (e1 : Ψ y = Ψ' y) (e2 : h y = h' y)
    (e3 : ∀ μ : Fin d, Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) =
      Ψ' (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)))
    (Z : Set (CTorus d L N₁ m₁ k)) :
    relPartTorus Tm i₀ i₁ j y Ψ h Z = relPartTorus Tm i₀ i₁ j y Ψ' h' Z := by
  simp only [relPartTorus, e1, e2, e3]

/-- The term `A_{y,X}` depends on `Ψ` only on `X ∪ {y}`. -/
theorem aTermTorus_congr (Tm : Terms d L N₁ m₁ k N ϱ) (i₀ : Fin N) (j : ℕ)
    {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {Ψ Ψ' : Fld d L N₁ m₁ k N}
    (e1 : Ψ y = Ψ' y) (hΨ : ∀ x ∈ X, Ψ x = Ψ' x) :
    aTermTorus Tm i₀ j y Ψ X = aTermTorus Tm i₀ j y Ψ' X := by
  classical
  unfold aTermTorus
  congr 1
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [hΨ x (Finset.mem_filter.1 hx).2.2, e1]

open Classical in
/-- **Locality of the label functional** (FLUCTUATION (3.0), Lemma 3.2 (ii)), for every selection:
for `y ∈ X`, `ℰ^{sm}_{irrel}(y, X; Ψ, h)` depends on `Ψ` only on `X^⋆ = X ∪ st₊(y)`,
`st₊(y) = {y + L^j e_μ}`, and on `h` only on `X`. -/
theorem irrelTorusOn_congr (hcl : SFTermClauses P Dom Tm)
    (sm : CTorus d L N₁ m₁ k → Set (CTorus d L N₁ m₁ k) → Prop) (m₀ : ℕ) (i₀ i₁ : Fin N) (j : ℕ)
    {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} (hy : y ∈ X)
    {Ψ Ψ' h h' : Fld d L N₁ m₁ k N}
    (hΨ : ∀ x ∈ X ∪ Set.range (fun μ : Fin d => y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)),
      Ψ x = Ψ' x)
    (hh : ∀ x ∈ X, h x = h' x) :
    irrelTorusOn sm m₀ Tm i₀ i₁ j y X Ψ h = irrelTorusOn sm m₀ Tm i₀ i₁ j y X Ψ' h' := by
  have e1 : Ψ y = Ψ' y := hΨ y (Or.inl hy)
  have e2 : h y = h' y := hh y hy
  have e3 : ∀ μ : Fin d, Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) =
      Ψ' (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) :=
    fun μ => hΨ _ (Or.inr ⟨μ, rfl⟩)
  have e4 : Tm.E j y X Ψ h = Tm.E j y X Ψ' h' :=
    hcl.localE j y X Ψ Ψ' h h' fun x hx => ⟨hΨ x (Or.inl hx), hh x hx⟩
  have hR := relPartTorus_congr Tm i₀ i₁ j e1 e2 e3
  unfold irrelTorusOn
  rw [e4, hR, aTermTorus_congr Tm i₀ j e1 fun x hx => hΨ x (Or.inl hx)]
  simp only [hR]

/-- The evaluation `p ↦ p.1 x i` of the first field of a pair is analytic. -/
theorem analyticAt_fld_fst_apply (x : CTorus d L N₁ m₁ k) (i : Fin N)
    (p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N) :
    AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => p.1 x i) p :=
  (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : CTorus d L N₁ m₁ k => Fin N → ℂ) x)).comp
    (ContinuousLinearMap.fst ℂ _ _)).analyticAt p

/-- The evaluation `p ↦ p.2 x i` of the second field of a pair is analytic. -/
theorem analyticAt_fld_snd_apply (x : CTorus d L N₁ m₁ k) (i : Fin N)
    (p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N) :
    AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => p.2 x i) p :=
  (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : CTorus d L N₁ m₁ k => Fin N → ℂ) x)).comp
    (ContinuousLinearMap.snd ℂ _ _)).analyticAt p

theorem analyticAt_dot_of {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → Fin N → ℂ} {p : E} (hf : ∀ i, AnalyticAt ℂ (fun q => f q i) p)
    (hg : ∀ i, AnalyticAt ℂ (fun q => g q i) p) :
    AnalyticAt ℂ (fun q => dot (f q) (g q)) p := by
  unfold dot
  exact Finset.analyticAt_fun_sum _ fun i _ => (hf i).mul (hg i)

/-- **The relevant local part is analytic in the fields** where `Ψ(y)·Ψ(y) ∉ (-∞, 0]` (the
tensors are taken at the fixed reference field). -/
theorem analyticAt_relPartTorus (Tm : Terms d L N₁ m₁ k N ϱ) (i₀ i₁ : Fin N) (j : ℕ)
    (y : CTorus d L N₁ m₁ k) (Z : Set (CTorus d L N₁ m₁ k))
    {p₀ : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N}
    (hp₀ : dot (p₀.1 y) (p₀.1 y) ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
      relPartTorus Tm i₀ i₁ j y p.1 p.2 Z) p₀ := by
  have hev := fun x i => analyticAt_fld_fst_apply (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
    (N := N) x i p₀
  have hevh := fun x i => analyticAt_fld_snd_apply (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
    (k := k) (N := N) x i p₀
  have hdot : ∀ x x', AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
      dot (p.1 x) (p.1 x')) p₀ := fun x x' => analyticAt_dot_of (hev x) (hev x')
  have h0 : dot (p₀.1 y) (p₀.1 y) ≠ 0 := Complex.slitPlane_ne_zero hp₀
  have hu : AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
      sqrtC (dot (p.1 y) (p.1 y))) p₀ := (hdot y y).cpow analyticAt_const hp₀
  have hu0 : sqrtC (dot (p₀.1 y) (p₀.1 y)) ≠ 0 := sqrtC_ne_zero h0
  have hdiff : ∀ μ : Fin d, ∀ i, AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
      (p.1 (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - p.1 y) i) p₀ :=
    fun μ i => (hev _ i).sub (hev y i)
  have hg : ∀ μ μ' : Fin d, AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
      dot (p.1 (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - p.1 y)
          (p.1 (y + (L ^ j) • (Pi.single μ' 1 : CTorus d L N₁ m₁ k)) - p.1 y) -
        dot (p.1 y) (p.1 (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - p.1 y) *
          dot (p.1 y) (p.1 (y + (L ^ j) • (Pi.single μ' 1 : CTorus d L N₁ m₁ k)) - p.1 y) /
          dot (p.1 y) (p.1 y)) p₀ := fun μ μ' =>
    (analyticAt_dot_of (hdiff μ) (hdiff μ')).sub
      (((analyticAt_dot_of (hev y) (hdiff μ)).mul (analyticAt_dot_of (hev y) (hdiff μ'))).div
        (hdot y y) h0)
  have hv : AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
      dot (p.1 y) (p.2 y) / sqrtC (dot (p.1 y) (p.1 y))) p₀ :=
    (analyticAt_dot_of (hev y) (hevh y)).div hu hu0
  simp only [relPartTorus]
  exact ((analyticAt_const.add ((hu.sub analyticAt_const).mul analyticAt_const)).add
    ((hv.sub analyticAt_const).mul analyticAt_const)).sub
    (analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun μ _ =>
      Finset.analyticAt_fun_sum _ fun μ' _ => (hg μ μ').mul analyticAt_const))

/-- The term `A_{y,X}` is analytic in the fields (a polynomial in `Ψ`). -/
theorem analyticAt_aTermTorus (Tm : Terms d L N₁ m₁ k N ϱ) (i₀ : Fin N) (j : ℕ)
    (y : CTorus d L N₁ m₁ k) (X : Set (CTorus d L N₁ m₁ k))
    (p₀ : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N) :
    AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
      aTermTorus Tm i₀ j y p.1 X) p₀ := by
  have hev := fun x i => analyticAt_fld_fst_apply (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
    (N := N) x i p₀
  have hdot : ∀ x x', AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
      dot (p.1 x) (p.1 x')) p₀ := fun x x' => analyticAt_dot_of (hev x) (hev x')
  unfold aTermTorus
  exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun x _ =>
    analyticAt_const.mul ((hdot x x).sub (hdot y y)))

open Classical in
/-- **Analyticity of the label functional** (FLUCTUATION.md Lemma 3.2 (ii)), for every selection:
for a polymer `X ∈ 𝒟_j` containing `y`, `(Ψ, h) ↦ ℰ^{sm}_{irrel}(y, X; Ψ, h)` is analytic on the
domain of the term `ℰ(y, X)` intersected with `{Ψ(y)·Ψ(y) ∉ (-∞, 0]}`. -/
theorem irrelTorusOn_analyticOnNhd (hcl : SFTermClauses P Dom Tm)
    (sm : CTorus d L N₁ m₁ k → Set (CTorus d L N₁ m₁ k) → Prop) (m₀ : ℕ) (i₀ i₁ : Fin N)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X) :
    AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
        irrelTorusOn sm m₀ Tm i₀ i₁ j y X p.1 p.2)
      {p | Dom.dom j (Tm.gs j X) p.1 p.2 ∧ dot (p.1 y) (p.1 y) ∈ Complex.slitPlane} := by
  intro p₀ hp₀
  have hE : AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Tm.E j y X p.1 p.2)
      p₀ := hcl.analyticE j hj1 hjk y X hX hy p₀ hp₀.1
  have hR := fun Z => analyticAt_relPartTorus Tm i₀ i₁ j y Z hp₀.2
  unfold irrelTorusOn
  refine ((hE.sub ?_).sub (analyticAt_aTermTorus Tm i₀ j y X p₀)).add ?_
  · split_ifs
    · exact hR X
    · exact analyticAt_const
  · split_ifs
    · have hfin := (Set.toFinite (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j y))
      simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
      refine Finset.analyticAt_fun_sum _ fun Z _ => ?_
      split_ifs
      · exact hR Z
      · exact analyticAt_const
    · exact analyticAt_const

/-- The relevant local part is invariant under the real orthogonal matrices. -/
theorem relPartTorus_rot (Tm : Terms d L N₁ m₁ k N ϱ) (i₀ i₁ : Fin N) (j : ℕ)
    (y : CTorus d L N₁ m₁ k) {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRot R)
    (Ψ h : Fld d L N₁ m₁ k N) (Z : Set (CTorus d L N₁ m₁ k)) :
    relPartTorus Tm i₀ i₁ j y (rotField R Ψ) (rotField R h) Z =
      relPartTorus Tm i₀ i₁ j y Ψ h Z := by
  have hd : ∀ v w : Spin N, dot (R.mulVec v) (R.mulVec w) = dot v w := dot_mulVec_rot hR.1
  simp only [relPartTorus, rotField, ← Matrix.mulVec_sub, hd]

/-- The term `A_{y,X}` is invariant under the real orthogonal matrices. -/
theorem aTermTorus_rot (Tm : Terms d L N₁ m₁ k N ϱ) (i₀ : Fin N) (j : ℕ)
    (y : CTorus d L N₁ m₁ k) {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRot R)
    (Ψ : Fld d L N₁ m₁ k N) (X : Set (CTorus d L N₁ m₁ k)) :
    aTermTorus Tm i₀ j y (rotField R Ψ) X = aTermTorus Tm i₀ j y Ψ X := by
  have hd : ∀ v w : Spin N, dot (R.mulVec v) (R.mulVec w) = dot v w := dot_mulVec_rot hR.1
  simp only [aTermTorus, rotField, hd]

open Classical in
/-- **`O(N)` invariance of the label functional** (FLUCTUATION.md Lemma 3.2 (ii); P1 (H.4)), for
every selection: for a real orthogonal `R` and data `(Ψ, h)`, `(RΨ, Rh)` in the domain of the term of
`X ∈ 𝒟_j`, `ℰ^{sm}_{irrel}(y, X; RΨ, Rh) = ℰ^{sm}_{irrel}(y, X; Ψ, h)`. -/
theorem irrelTorusOn_rot (hcl : SFTermClauses P Dom Tm)
    (sm : CTorus d L N₁ m₁ k → Set (CTorus d L N₁ m₁ k) → Prop) (m₀ : ℕ) (i₀ i₁ : Fin N) {j : ℕ}
    (hj1 : 1 ≤ j) (hjk : j ≤ k) {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X) {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRot R)
    {Ψ h : Fld d L N₁ m₁ k N} (h1 : Dom.dom j (Tm.gs j X) Ψ h)
    (h2 : Dom.dom j (Tm.gs j X) (rotField R Ψ) (rotField R h)) :
    irrelTorusOn sm m₀ Tm i₀ i₁ j y X (rotField R Ψ) (rotField R h) =
      irrelTorusOn sm m₀ Tm i₀ i₁ j y X Ψ h := by
  have hE := hcl.rotE j hj1 hjk y X hX hy R hR Ψ h h1 h2
  unfold irrelTorusOn
  rw [hE, aTermTorus_rot Tm i₀ j y hR Ψ X]
  simp only [relPartTorus_rot Tm i₀ i₁ j y hR Ψ h]

end API

end Balaban.SmallField.Def6v2
