/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusOn

/-!
# The irrelevant part of a term of the effective action on the torus (P1 Proposition 3.10)

P1 Proposition 3.10 and (3.127), pp. 152–153: on the torus,
`ℰ^{(j)}(ψ, v_j h) = Σ_{y ∈ T^{(j)}} Σ_{X ∈ 𝒟_j, X ∋ y} ℰ^{(j)}_{irrel}(y, X; ψ, v_j h)`, the
labels `(j, y, X)` of the inductive hypotheses with new functionals: the irrelevant part of each
term (P1 (3.104); FLUCTUATION.md §3.2, `I(y,X) = ℰ(y,X) - T_X - A_{y,X} - Φ_{y,X}`, landed in
`ℤ^d` form as `Itw`), plus, at the cube `□(y)` of the cover whose central large cube contains `y`,
the relevant local parts `T_{X'} + Φ_{y,X'}` resummed over the polymers `X' ∋ y` (P1 p. 152:
for each `y` the cube `□` of the cover `π_j` containing `y` in its central large cube is taken,
and the local expression of `y` is assigned to the term of `(y, □)`).

* `irrelTorus`: the label functional `ℰ^{(j)}_{irrel}(y, X; Ψ, h)` on the fine torus, built from the
  relevant local part `relPartTorus` and the term `aTermTorus` (`IrrelTorusOn.lean`);
* `irrelTorus_eq_irrelTorusOn`: it is the functional `irrelTorusOn` of the selection `relBox` of
  the polymers in the box of half-side `r_k` around the centre (ruling R15); the properties below are
  the instances of those of `irrelTorusOn`;
* `irrelTorus_congr`: it depends on `(Ψ, h)` only through `Ψ` on `X^⋆ = X ∪ st₊(y)` and `h` on
  `X` (`y ∈ X`), `st₊(y) = {y + L^j e_μ}` (FLUCTUATION (3.0), Lemma 3.2 (ii));
* `irrelTorus_analyticOnNhd`: it is analytic on the domain of the term where
  `Ψ(y)·Ψ(y) ∉ (-∞, 0]` (Lemma 3.2 (ii));
* `irrelTorus_rot`: it is invariant under the real orthogonal matrices (Lemma 3.2 (ii)).
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **The irrelevant part `ℰ^{(j)}_{irrel}(y, X; Ψ, h)` of the term of a label `(j, y, X)` on the
torus** (P1 Proposition 3.10, Corollary 3.11, (3.104), (3.126)–(3.127), pp. 146–153; FLUCTUATION.md
§3.2, Lemma 3.2; the landed `ℤ^d` form `Itw` of `RenormTermwiseDefs`).  With the reference point
`P₀ = (e_{i₀}, ν_j e_{i₀})` in the variables `(ψ, b = ν_j h)`, i.e. the constant fields
`Ψ = h = e_{i₀}`, the `j`-blocks `x ∈ X` (the `L^j`-aligned sites of `X`) and the tensors of the
single term `ℰ(y, X)` at `P₀`:
`a_X(x) = ∂ℰ(y,X)/∂ψ_{i₀}(x)`, `B_X(x,x') = ∂²ℰ(y,X)/∂ψ_{i₁}(x)∂ψ_{i₁}(x')`,
`S_X^{μν} = Σ_{x,x'} B_X(x,x') (x-x')_μ (x-x')_ν`, the blocks placed in `ℤ^d` relative to the
centre `y` (`x ↦ unlift (x - y)`, the centred form of the term pulled back at `y`),
`ℰ_{irrel}(y,X) = ℰ(y,X) - 1_{X ∈ B(y)} (T_X + Φ_{y,X}) - A_{y,X}
  + 1_{X = □(y)} Σ_{X' ∋ y, X' ⊆ B(y)} (T_{X'} + Φ_{y,X'})`
(ruling R15: the relevant parts are subtracted from, and filed at the cell for, the polymers inside
the box `B(y)` of half-side `r_k = ⌊L^{m₀+m₁+k}/8⌋` around `y` only, `relBox`; the large polymers
keep their relevant parts, small by their size), where
* `T_X = f_X(P₀) + ∂_u f_X(P₀) (u - 1) + ∂_v f_X(P₀) (v - ν_j)`, `u = √(Ψ(y)·Ψ(y))`,
  `v = Ψ(y)·b(y)/u`, `∂_u f_X(P₀) = Σ_x a_X(x)`, `∂_v f_X(P₀) = ∂_b ℰ(y,X)(P₀)·e_{i₀}`; with
  `b = ν_j h` the last term is `(Ψ(y)·h(y)/u - 1) ∂_h ℰ(y,X)(P₀)·e_{i₀}`;
* `A_{y,X} = ½ Σ_{x ∈ X} a_X(x) (Ψ(x)·Ψ(x) - Ψ(y)·Ψ(y))`;
* `Φ_{y,X} = -¼ Σ_{μν} S_X^{μν} [∂_μΨ·∂_νΨ - (Ψ(y)·∂_μΨ)(Ψ(y)·∂_νΨ)/(Ψ(y)·Ψ(y))]`,
  `∂_μΨ = Ψ(y + L^j e_μ) - Ψ(y)`;
* `□(y)` is the `π'_j`-cube (side `L M ℓ_j = L · cellSide`, a polymer of `𝒟_j`) whose central
  `π_j`-cube (offset `⌊L/2⌋` cells in every direction) is the cell of `y` (P1 p. 152).
The relevant local parts `T_{X'} + Φ_{y,X'}` vanish after the resummation over `X'` in infinite
volume (`Ttw_tsum_zero`, `Phitw_tsum_zero`); `Σ_y Σ_X A_{y,X} = 0` on the torus by the Euclidean
covariance of the density (P1 (3.112)–(3.113)).  It is the functional `irrelTorusOn (relBox m₀)`
(`IrrelTorusOn.lean`), the same on two tori at the cell (`irrelTorus_cell_boxAgree`). -/
noncomputable def irrelTorus (m₀ : ℕ) (Tm : Terms d L N₁ m₁ k N ϱ) (i₀ i₁ : Fin N) (j : ℕ)
    (y : CTorus d L N₁ m₁ k) (X : Set (CTorus d L N₁ m₁ k)) (Ψ h : Fld d L N₁ m₁ k N) : ℂ :=
  irrelTorusOn (relBox m₀) m₀ Tm i₀ i₁ j y X Ψ h

open Classical in
/-- **`irrelTorus` is the label functional of the selection `relBox`** (ruling R15). -/
theorem irrelTorus_eq_irrelTorusOn (m₀ : ℕ) (Tm : Terms d L N₁ m₁ k N ϱ) (i₀ i₁ : Fin N) (j : ℕ)
    (y : CTorus d L N₁ m₁ k) (X : Set (CTorus d L N₁ m₁ k)) (Ψ h : Fld d L N₁ m₁ k N) :
    irrelTorus m₀ Tm i₀ i₁ j y X Ψ h = irrelTorusOn (relBox m₀) m₀ Tm i₀ i₁ j y X Ψ h :=
  rfl

section API

variable {P : Consts} {Dom : FieldDom d L N₁ m₁ k N ϱ} {Tm : Terms d L N₁ m₁ k N ϱ}

open Classical in
/-- **Locality of the label functional** (FLUCTUATION (3.0), Lemma 3.2 (ii)): for `y ∈ X`,
`ℰ_{irrel}(y, X; Ψ, h)` depends on `Ψ` only on `X^⋆ = X ∪ st₊(y)`, `st₊(y) = {y + L^j e_μ}`, and
on `h` only on `X`. -/
theorem irrelTorus_congr (hcl : SFTermClauses P Dom Tm) (m₀ : ℕ) (i₀ i₁ : Fin N) (j : ℕ)
    {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} (hy : y ∈ X)
    {Ψ Ψ' h h' : Fld d L N₁ m₁ k N}
    (hΨ : ∀ x ∈ X ∪ Set.range (fun μ : Fin d => y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)),
      Ψ x = Ψ' x)
    (hh : ∀ x ∈ X, h x = h' x) :
    irrelTorus m₀ Tm i₀ i₁ j y X Ψ h = irrelTorus m₀ Tm i₀ i₁ j y X Ψ' h' := by
  rw [irrelTorus_eq_irrelTorusOn, irrelTorus_eq_irrelTorusOn]
  exact irrelTorusOn_congr hcl _ m₀ i₀ i₁ j hy hΨ hh

open Classical in
/-- **Analyticity of the label functional** (FLUCTUATION.md Lemma 3.2 (ii)): for a polymer
`X ∈ 𝒟_j` containing `y`, `(Ψ, h) ↦ ℰ_{irrel}(y, X; Ψ, h)` is analytic on the domain of the term
`ℰ(y, X)` intersected with `{Ψ(y)·Ψ(y) ∉ (-∞, 0]}` (where the principal root `u` is analytic and
nonzero). -/
theorem irrelTorus_analyticOnNhd (hcl : SFTermClauses P Dom Tm) (m₀ : ℕ) (i₀ i₁ : Fin N)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X) :
    AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
        irrelTorus m₀ Tm i₀ i₁ j y X p.1 p.2)
      {p | Dom.dom j (Tm.gs j X) p.1 p.2 ∧ dot (p.1 y) (p.1 y) ∈ Complex.slitPlane} := by
  simp only [irrelTorus_eq_irrelTorusOn]
  exact irrelTorusOn_analyticOnNhd hcl _ m₀ i₀ i₁ hj1 hjk hX hy

/-- **`O(N)` invariance of the label functional** (FLUCTUATION.md Lemma 3.2 (ii); P1 (H.4)): for
a real orthogonal `R` and data `(Ψ, h)`, `(RΨ, Rh)` in the domain of the term of `X ∈ 𝒟_j`,
`ℰ_{irrel}(y, X; RΨ, Rh) = ℰ_{irrel}(y, X; Ψ, h)` (the tensors are taken at the fixed reference
field; the subtracted local parts depend on the data through the invariant products only). -/
theorem irrelTorus_rot (hcl : SFTermClauses P Dom Tm) (m₀ : ℕ) (i₀ i₁ : Fin N) {j : ℕ}
    (hj1 : 1 ≤ j) (hjk : j ≤ k) {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X) {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRot R)
    {Ψ h : Fld d L N₁ m₁ k N} (h1 : Dom.dom j (Tm.gs j X) Ψ h)
    (h2 : Dom.dom j (Tm.gs j X) (rotField R Ψ) (rotField R h)) :
    irrelTorus m₀ Tm i₀ i₁ j y X (rotField R Ψ) (rotField R h) =
      irrelTorus m₀ Tm i₀ i₁ j y X Ψ h := by
  rw [irrelTorus_eq_irrelTorusOn, irrelTorus_eq_irrelTorusOn]
  exact irrelTorusOn_rot hcl _ m₀ i₀ i₁ hj1 hjk hX hy hR h1 h2

end API

end Balaban.SmallField.Def6v2
