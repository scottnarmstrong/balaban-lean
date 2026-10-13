module

public import Balaban.LargeField.Def7SmallField
public import Balaban.Background.ExistenceSetup
public import Balaban.SmallField.Def6Terms
public import Balaban.SmallField.Xi
public import Balaban.SmallField.Def6ContInhabited

/-!
# Whole-level generating sets and the regional composed field

This file proves that the regional composed field at which the large-field step evaluates
inherited terms lies outside the analyticity domain of the whole-level generating set whenever the
local generating set is a proper subset.  It does not prove that no scheme with whole-level
generating sets can work (a scheme with an additional extension or local-rebuilding theorem is not
excluded), and it makes no choice between the options; that choice is with the author.

Contents.
* `no_zero_on_dataSites_of_inUnionDomainC`: no datum of the complex union domain has a zero spin
  vector at a data site (`|q - 1| < δ` and `|q| < δ` for `q = ∑ᵢ Ψ(x,i)²` force `1 < 2δ ≤ 1/8`).
* `not_xiDom_of_zero_spin`, `not_xiDom_levelGS_of_zero_spin`: a field with a zero spin vector at a
  data site of `G` is outside `XiDom G`; for `levelGS j`, `j ≥ 1`, every site is a data site.
* `regional_psiJ_not_globalXiDom`: the regional field `C.psiJ Y ψk hv j` vanishes at every site
  whose image in the level-`k` torus is outside `dataSites (genSF j (W2 R Y))`, hence is outside
  `XiDom (levelGS j)` (for every `a`, `ν`, `ε`) at the pair `(C.psiJ …, constFld (hC hv))`
  at which `EresJ`, `MresJ` evaluate the inherited terms.
* `xiDom_levelGS_nonempty`: the global domain itself is not empty; `no_site_of_dataSites_eq_univ`:
  if the local generator covers every site the statement has no site to apply to.

Non-vacuity.  No landed context has a proper local generator: `SFCtx` inhabitants live on the torus
with one cube per side (`nonempty_sfCtx`) or with `2 ⌊R_0⌋ + 4` cubes per side (`ctxMulti`), where
`W2 R Y` (a `2 ⌊R_0⌋`-fold thickening) is the whole torus, so every site is a data site.  An
instance of the site hypothesis of `regional_psiJ_not_globalXiDom` needs a torus with at least
`4 ⌊R_{k-1}⌋ + 4` cubes per side (so that a cube lies at distance `≥ 2 ⌊R_{k-1}⌋ + 2` from `Y`,
beyond `W2 R Y` and the one-cube collar).

As a clause-level consequence: in `SFTermClauses`, `analyticE`/`boundE` for `Tm.gs j X = levelGS j`
are statements on `XiDom (levelGS j)`; the regional argument is outside that set, so those clauses
cannot be applied at the argument where `EresJ`/`MresJ` evaluate the term.  The terms are still
evaluated there (they are total functions).
-/

@[expose] public section

namespace Balaban.LargeField.GlobalGenRegional

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Finset

section ZeroExclusion

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **No zero spin vector on the data sites of the complex union domain.**  If the datum `Dc`
lies in `InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν`, then at no data site is every component of
`Dc.Ψ` zero: with `q = ∑ᵢ Ψ(x,i)²` the real clause gives `|q - 1| < δ`, the complex clause gives
`|q| < δ`, whence `1 < 2δ ≤ 2 bgC1 ≤ 2 bgC0 ≤ 1/8`. -/
theorem no_zero_on_dataSites_of_inUnionDomainC (hd : 0 < d)
    (G : GeneratingSet d L N₀ k ϱ) {ν : ℝ} {Dc : BgData G N}
    (hD : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν Dc)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ dataSites G) :
    ¬ ∀ i, Dc.Ψ x i = 0 := by
  intro hz
  obtain ⟨δ, ε, hδ, -, -, hδ1, -, Ψ, h, Ψ', h', hP, hΨ, -⟩ := hD
  have r2 := hP.toInPsiTilde.r2 x hx
  have c2b := hP.c2b x hx
  have hq : ∀ i, (Ψ x i : ℂ) + Ψ' x i = 0 := fun i => by rw [← hΨ x hx i]; exact hz i
  have e1 : ∑ i, ((Ψ x i : ℂ) + Ψ' x i) * ((Ψ x i : ℂ) + Ψ' x i) = 0 := by simp [hq]
  have e2 : ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ) = ((∑ i, Ψ x i ^ 2 : ℝ) : ℂ) := by
    push_cast; simp [sq]
  rw [e1, e2, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs] at c2b
  have h1 : (1 : ℝ) ≤ |∑ i, Ψ x i ^ 2 - 1| + |∑ i, Ψ x i ^ 2| := by
    have := abs_sub (∑ i, Ψ x i ^ 2) (∑ i, Ψ x i ^ 2 - 1)
    have h3 : ∑ i, Ψ x i ^ 2 - (∑ i, Ψ x i ^ 2 - 1) = 1 := by ring
    rw [h3] at this
    simp at this; linarith
  have := bgC1_le_bgC0 d L N hd
  have := bgC0_le (d := d) (L := L) (N := N)
  linarith

end ZeroExclusion

section GlobalChart

open Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **Global-chart exclusion.**  A field `Ψ` with a zero spin vector at a data site of `G` is not
in `XiDom G a ν j ε` (for any kernel sequence, mass, level and radius): `XiDom` contains a complex
datum in the union domain realizing the field on `dataSites G`. -/
theorem not_xiDom_of_zero_spin (hd : 0 < d) (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ)
    (a : ℕ → ℝ) (ν : ℝ) (j : ℕ) (ε : ℝ) (Ψ h : Fld d L N₁ m₁ k N)
    {x : Localization.CTorus d L N₁ m₁ k} (hx : x ∈ dataSites G) (hz : ∀ i, Ψ x i = 0) :
    ¬ XiDom G a ν j ε Ψ h := by
  rintro ⟨Ψ₀, h₀, Ψ'', h'', hΨ, -, -, -, Dr, Dc, -, hR, hU, -⟩
  refine no_zero_on_dataSites_of_inUnionDomainC hd G hU hx fun i => ?_
  rw [hR.1 x hx i, ← hΨ x i]
  exact hz i

/-- Every site is a data site of the whole-level generating set of level `j ≥ 1`. -/
theorem mem_dataSites_levelGS {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (x : Localization.CTorus d L N₁ m₁ k) :
    x ∈ dataSites (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk) := by
  rw [mem_dataSites]
  left
  simp [levelGS, hj1]

/-- **A field with a zero spin vector at any site is outside `XiDom (levelGS j)`** (`j ≥ 1`). -/
theorem not_xiDom_levelGS_of_zero_spin (hd : 0 < d) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (a : ℕ → ℝ) (ν : ℝ) (ε : ℝ) (Ψ h : Fld d L N₁ m₁ k N) {x : Localization.CTorus d L N₁ m₁ k}
    (hz : ∀ i, Ψ x i = 0) :
    ¬ XiDom (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk) a ν j ε Ψ h :=
  not_xiDom_of_zero_spin hd _ a ν j ε Ψ h (mem_dataSites_levelGS hj1 hjk x) hz

end GlobalChart

section Regional

open Balaban.SmallField Balaban.SmallField.Def6 Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (Y : Set (Torus S.d (n k))) (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
  (hv : EuclideanSpace ℝ (Fin N))

/-- The regional composed field `C.psiJ Y ψk hv j` vanishes at every site of the Def-6 torus whose
image in the level-`k` torus (by `sfToBg`, the transport used by `sfPull`) is outside the data
sites of the local generating set `genSF j (W2 R Y)`. -/
theorem psiJ_eq_zero_of_not_mem {j : ℕ} (hjk : j ≤ k) {x : Localization.CTorus S.d S.L C.N₁ m₁ k}
    (hx : sfToBg C.geo C.hT x ∉ dataSites
      (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n k) (L := S.L) (c := C.geo.c) (n := n k)
        hjk (W2 R Y))) (i : Fin N) :
    C.psiJ Y ψk hv j x i = 0 := by
  unfold SFCtx.psiJ
  simp only [hjk, ↓reduceDIte]
  exact composeField_of_not_mem _ _ _ hx i

/-- **The regional argument is outside the whole-level analyticity domain.**  Let `1 ≤ j ≤ k` and
let `x` be a site of the Def-6 torus whose image under `sfToBg` is not a data site of the local
generating set `genSF j (W2 R Y)`.  Then for all `ψk`, `hv` (and every kernel sequence `a`, mass `ν`
and radius `ε`) the pair `(C.psiJ Y ψk hv j, constFld (hC hv))`, at which `EresJ`/`MresJ` evaluate
the inherited terms, is not in `XiDom (levelGS j) a ν j ε`. -/
theorem regional_psiJ_not_globalXiDom (hd : 0 < S.d) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {x : Localization.CTorus S.d S.L C.N₁ m₁ k}
    (hx : sfToBg C.geo C.hT x ∉ dataSites
      (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n k) (L := S.L) (c := C.geo.c) (n := n k)
        hjk (W2 R Y)))
    (a : ℕ → ℝ) (ν ε : ℝ) :
    ¬ XiDom (levelGS (d := S.d) (L := S.L) (N₁ := C.N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk)
      a ν j ε (C.psiJ Y ψk hv j) (constFld (hC hv)) :=
  not_xiDom_levelGS_of_zero_spin hd hj1 hjk a ν ε _ _
    (psiJ_eq_zero_of_not_mem C Y ψk hv hjk hx)

end Regional

section Remarks

open Balaban.SmallField.Def6

/-- **The global domain is not empty (the statement above concerns one regional argument).**  In
the landed witness setting (`d = L = 3`, `N = 2`, the witness kernel sequence and mass), the
constant unit field `e₀` with `h = e₀` lies in `XiDom (levelGS j)` for every `j ≤ k` and every
`ε > 0`. -/
theorem xiDom_levelGS_nonempty {m₁ k N₁ : ℕ} [NeZero N₁] {ϱ : ℝ} {α₀ : ℝ} (hα : 0 < α₀)
    (hϱ : bgR0 3 3 ≤ ϱ) {j : ℕ} (hjk : j ≤ k) (ε : ℝ) (hε : 0 < ε) :
    XiDom (levelGS j hjk : GeneratingSet 3 3 (N₁ * 3 ^ m₁) k ϱ) (aIdeal 3 k (witnessa k))
      (Balaban.SmallField.Def6.bgMass 3 k (witnessβ k) (witnessν k k)) j ε
      (fun _ => (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ))
      (fun _ => (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ)) := by
  obtain ⟨ρ, hρ, h⟩ := xiDom_ball_witness (m₁ := m₁) (N₁ := N₁) (ϱ := ϱ) hα hϱ hjk ε hε
  exact h _ _ (fun x i => by simpa using hρ.le) (fun x i => by simpa using hρ.le)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)

/-- **If the local generating set covers all sites there is no site `x` to apply the theorem to.** -/
theorem no_site_of_dataSites_eq_univ {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    {G : GeneratingSet d L N₀ k ϱ} (h : dataSites G = Finset.univ) (x : Torus d (N₀ * L ^ k)) :
    ¬ x ∉ dataSites G := fun hx => hx (h ▸ Finset.mem_univ x)

end Remarks

end Balaban.LargeField.GlobalGenRegional
