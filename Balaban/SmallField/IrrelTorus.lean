/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2
public import Balaban.SmallField.RenormTermwiseAnalytic

/-!
# The irrelevant part of a term of the effective action on the torus (P1 Proposition 3.10)

P1 Proposition 3.10 and (3.127), pp. 152–153: on the torus,
`ℰ^{(j)}(ψ, v_j h) = Σ_{y ∈ T^{(j)}} Σ_{X ∈ 𝒟_j, X ∋ y} ℰ^{(j)}_{irrel}(y, X; ψ, v_j h)`, the
labels `(j, y, X)` of the inductive hypotheses with new functionals: the irrelevant part of each
term (P1 (3.104); FLUCTUATION.md §3.2, `I(y,X) = ℰ(y,X) - T_X - A_{y,X} - Φ_{y,X}`, landed in
`ℤ^d` form as `Itw`), plus, at the cube `□(y)` of the cover whose central large cube contains `y`,
the relevant local parts `T_{X'} + Φ_{y,X'}` resummed over the polymers `X' ∋ y` (P1 p. 152:
"for each `y` we take the cube `□` from the cover `π_j` which contains the point `y` in the
central large cube of `□`, and we assign the local expression to `ℰ_{irrel}(y, □)`").

* `irrelTorus`: the label functional `ℰ^{(j)}_{irrel}(y, X; Ψ, h)` on the fine torus;
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
`ℰ_{irrel}(y,X) = ℰ(y,X) - T_X - Φ_{y,X} - A_{y,X} + 1_{X = □(y)} Σ_{X' ∋ y} (T_{X'} + Φ_{y,X'})`,
where
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
covariance of the density (P1 (3.112)–(3.113)). -/
noncomputable def irrelTorus (m₀ : ℕ) (Tm : Terms d L N₁ m₁ k N ϱ) (i₀ i₁ : Fin N) (j : ℕ)
    (y : CTorus d L N₁ m₁ k) (X : Set (CTorus d L N₁ m₁ k)) (Ψ h : Fld d L N₁ m₁ k N) : ℂ :=
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
  let TΦ : Set (CTorus d L N₁ m₁ k) → ℂ := fun Z =>
    Tm.E j y Z e e + (u - 1) * ∑ x ∈ blk Z, a Z x
      + (dot (Ψ y) (h y) / u - 1) * fderiv ℂ (fun h' => Tm.E j y Z e h') e e
      - (1 / 4 : ℂ) * ∑ μ, ∑ μ', g μ μ' * ∑ x ∈ blk Z, ∑ x' ∈ blk Z,
          D2 (fun Ψ' => Tm.E j y Z Ψ' e) e (blockDir L j x i₁) (blockDir L j x' i₁) *
            ((lift x μ - lift x' μ) * (lift x μ' - lift x' μ'))
  Tm.E j y X Ψ h - TΦ X
    - (1 / 2 : ℂ) * ∑ x ∈ blk X, a X x * (dot (Ψ x) (Ψ x) - dot (Ψ y) (Ψ y))
    + if X = box (cbase (cellSide L m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L m₀ m₁ j)
        (L * cellSide L m₀ m₁ j) then ∑ᶠ Z ∈ polysAt m₀ j y, TΦ Z else 0

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
  have e1 : Ψ y = Ψ' y := hΨ y (Or.inl hy)
  have e2 : h y = h' y := hh y hy
  have e3 : ∀ μ : Fin d, Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) =
      Ψ' (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) :=
    fun μ => hΨ _ (Or.inr ⟨μ, rfl⟩)
  have e4 : Tm.E j y X Ψ h = Tm.E j y X Ψ' h' :=
    hcl.localE j y X Ψ Ψ' h h' fun x hx => ⟨hΨ x (Or.inl hx), hh x hx⟩
  simp only [irrelTorus, e1, e2, e3, e4]
  congr 3
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [hΨ x (Or.inl (Finset.mem_filter.1 hx).2.2)]

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
  intro p₀ hp₀
  have hE : AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Tm.E j y X p.1 p.2)
      p₀ := hcl.analyticE j hj1 hjk y X hX hy p₀ hp₀.1
  have hev := fun x i => analyticAt_fld_fst_apply (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
    (N := N) x i p₀
  have hevh := fun x i => analyticAt_fld_snd_apply (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
    (k := k) (N := N) x i p₀
  have hdot : ∀ x x', AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
      dot (p.1 x) (p.1 x')) p₀ := fun x x' => analyticAt_dot_of (hev x) (hev x')
  have h0 : dot (p₀.1 y) (p₀.1 y) ≠ 0 := Complex.slitPlane_ne_zero hp₀.2
  have hu : AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
      sqrtC (dot (p.1 y) (p.1 y))) p₀ := (hdot y y).cpow analyticAt_const hp₀.2
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
  simp only [irrelTorus]
  refine ((hE.sub ?_).sub ?_).add ?_
  · exact ((analyticAt_const.add ((hu.sub analyticAt_const).mul analyticAt_const)).add
      ((hv.sub analyticAt_const).mul analyticAt_const)).sub
      (analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun μ _ =>
        Finset.analyticAt_fun_sum _ fun μ' _ => (hg μ μ').mul analyticAt_const))
  · exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun x _ =>
      analyticAt_const.mul ((hdot x x).sub (hdot y y)))
  · split_ifs
    · have hfin := (Set.toFinite (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j y))
      simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
      exact Finset.analyticAt_fun_sum _ fun Z _ =>
        ((analyticAt_const.add ((hu.sub analyticAt_const).mul analyticAt_const)).add
          ((hv.sub analyticAt_const).mul analyticAt_const)).sub
          (analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun μ _ =>
            Finset.analyticAt_fun_sum _ fun μ' _ => (hg μ μ').mul analyticAt_const))
    · exact analyticAt_const

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
  have hd : ∀ v w : Spin N, dot (R.mulVec v) (R.mulVec w) = dot v w := dot_mulVec_rot hR.1
  have hE := hcl.rotE j hj1 hjk y X hX hy R hR Ψ h h1 h2
  simp only [irrelTorus]
  rw [hE]
  simp only [rotField, ← Matrix.mulVec_sub, hd]

end API

end Balaban.SmallField.Def6v2
