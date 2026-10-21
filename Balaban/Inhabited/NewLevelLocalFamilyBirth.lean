/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelConstants
public import Balaban.Inhabited.StepTowerRotChainBirth
public import Balaban.Inhabited.StepTowerLocalChart

/-!
# The clauses (A1)–(A5) of the new level along the class chain (route R-LOC, L5; blocker 6)

The class chain on its formula path (`…_formula_birth_of`, the chart premise replaced by the inclusion
of the composed data in the class domain at the birth masses, rulings R2, R6, R13) composed with the
clauses (A1)–(A5) of the new level at a step of a tower (`StepTowerG.newLevel_localFamily_of_class`),
with the conditions on constants of L5 discharged (`NewLevelConstants`):

* `NewLevelLocalFamily`: the clauses (A1)–(A5) of a family on the local generating sets, bundled
  (the premises `hfan`, `hfbd`, `hfloc`, `hfrot`, `hfval` of `newLabels_castInputs_of_localFamily`
  at one root); `newLevelLocalFamily_zero` (inhabited);
* `StepTowerG.newLevel_localFamily_birth_of`: at a base tower `T₀` of the chain with `K₂ Q ≤ 1/16`
  and `NewLevelNumerics` (both provided by `exists_newLevelConstants`), for `L^{-α} ≤ 1/16`: for every
  class constant `P₀` with `α₀` small there is `β₀` such that, at every scale and for every class in
  the regime of ruling R13 with the flow constant small, the family `e` of the chain has a local
  family `f` with (A1)–(A5) on the cast local sets `𝔹_{k+1}(Ŷ⁺(T′))`.  The premises are the class
  (its clauses on the birth-mass domain, its generating sets, its weights, its flow), the bound of its
  irrelevant terms on their term domain with its decay in the level (the open input A4-1b (ii)), the
  analyticity of the old densities along the path (a premise of the chain), and the conditions on
  constants `L^{-α} ≤ 1/16`, `(N + 1) K₂ ε₁ ≤ 1/8`, `2 K_m τ₁ ≤ 1/9` (`L` large, `α₀` and the flow
  constant small: ties of the prefix); the radii of the marks, `hca`, `hsmO`, the (DL-gap) and the
  numerics of the new level are no longer premises;
* `StepTowerG.newLevel_localFamilies_birth_of` (row (iii) of A4-1b): the same for the families of
  all roots at once — the premises `hsupp`, `hval`, `hfan`, `hfbd`, `hfloc`, `hfrot`, `hfval` of
  `newLabels_castInputs_of_localFamily` (the provider of the label inputs of
  `localClass_newLevel_of_expansion_cast`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis

section Clauses

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The clauses (A1)–(A5) of the new level on the local generating sets** (P3 (4.44)–(4.47); route
R-LOC).  For the coefficient family `e` of the step `S` at one root, a family `f` of the pair of
fields and bounds `b` on the local sets `castG hc (localB (k + 1) … (Yp Y⁺(T′)) hsep)`,
`Y⁺(T′) = sitesOf (piHull m₀ (thickSet 𝔹 (sitesOf T′)))`: (A1) analyticity on the chart
`Ξ^c_{k+1}(·; 1, ε_{k+1})` of the local set, (A2) the bound `b T′` there, (A3) dependence only on the
fields on `Y⁺(T′)` on the chart of radius `K_loc ε_{k+1}`, `K_loc = (2 K₁ + 2) C₁`, (A4) invariance
under the real rotations, (A5) equality with the coefficient `e (π (clipRaw 𝔹 q), 0) T′` of the step
at the pairs `q` of the step chart.  These are the premises `hfan`, `hfbd`, `hfloc`, `hfrot`, `hfval`
of `newLabels_castInputs_of_localFamily` at one root. -/
def NewLevelLocalFamily (S : StepSetting d L N₁ m₁ k N ϱ) (P : Consts) {N₁' m₁' : ℕ} [NeZero N₁']
    (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hsep : ϱ ≤ LargeField.minSep L (L ^ m₁'))
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁' m₁' (k + 1)))
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ) → ℂ)
    (f : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
      Set.univ) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (b : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
      Set.univ) → ℝ) : Prop :=
  (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
    AnalyticOnNhd ℂ (f T)
      {p | (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1))
          (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2}) ∧
  (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
    ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
    (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
      (castG hc (localB (k + 1) (le_refl (k + 1))
        (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2 →
    ‖f T p‖ ≤ b T) ∧
  (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
    ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
    (xiFieldDom S.a S.ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
      FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
      (castG hc (localB (k + 1) (le_refl (k + 1))
        (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2 →
    (xiFieldDom S.a S.ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
      FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
      (castG hc (localB (k + 1) (le_refl (k + 1))
        (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p'.1 p'.2 →
    (∀ x ∈ sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))), p.1 x = p'.1 x ∧ p.2 x = p'.2 x) →
    f T p = f T p') ∧
  (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
    ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
    ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
    (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
      (castG hc (localB (k + 1) (le_refl (k + 1))
        (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2 →
    f T (rotField (cmat Q) p.1, rotField (cmat Q) p.2) = f T p) ∧
  (∀ T (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
    XiDom S.G' S.a S.ν (k + 1) (P.eps d L (k + 1)) q.1 q.2 →
    f T q = e (π (clipRaw S.G' q), 0) T)

/-- **`NewLevelLocalFamily` is inhabited** (rule 10): the zero family of the zero coefficient with
the zero bounds. -/
theorem newLevelLocalFamily_zero (S : StepSetting d L N₁ m₁ k N ϱ) (P : Consts) {N₁' m₁' : ℕ}
    [NeZero N₁'] (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hsep : ϱ ≤ LargeField.minSep L (L ^ m₁'))
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁' m₁' (k + 1)))
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G') :
    NewLevelLocalFamily S P hc hsep Yp π (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) :=
  ⟨fun _ _ => analyticOnNhd_const, fun _ _ _ _ => by simp, fun _ _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩

end Clauses

open Classical in
/-- **The clauses (A1)–(A5) of the new level along the class chain, with the conditions on constants
discharged** (route R-LOC, L5; rulings R2, R3, R6, R13; blocker 6).  At a base tower `T₀` of the
class chain (`CollarBase` at `q = L^{-α}`, `α = (d-2)/2 - γ`) with the closeness ratio
`K₂ Q ≤ 1/16` and the numerics of the new level (the tower of `exists_newLevelConstants`), for
`L^{-α} ≤ 1/16`: for every class constant `P₀` with `(N + 1) K₂ ε₁ ≤ 1/8` and every set of constants
`C_I, K_L, α₃, n₁` of the bound of the irrelevant parts there is `β₀` such that the statement of
`StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_ren_rot_formula_birth_of`
holds for the classes with constants `P₀` (with `λ ≤ 17/16` and, in place of the (DL-gap), the
smallness `2 K_m τ₁ ≤ 1/9` of the flow constant; the smallness of the class constants against the
marked radius is no longer a premise), and the family `e` of the chain has, on the cast local sets
`𝔹_{k+1}(Ŷ⁺(T′))`, a local family `f` with bounds `b` and (A1)–(A5) (`NewLevelLocalFamily`). -/
theorem StepTowerG.newLevel_localFamily_birth_of
    {d L N : ℕ} [NeZero L] (m₀ : ℕ) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1 / 2) {κmin : ℝ} (T₀ : StepTowerG d L N κmin) {κdec : ℝ}
    (hT : CollarBase d L N m₀ ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ))) T₀ κdec) {Q F η : ℝ}
    (hQdef : Q = (N : ℝ) * composedCloseBound d L N T₀.m₁ T₀.BG T₀.κ (xiC1 d)
      (4 * (d : ℝ) * (L : ℝ) ^ 3 + L))
    (hFdef : F = (N : ℝ) * (5 * cK2' d L N (famConst d L T₀.BG₂ T₀.κ) + 1))
    (hηdef : η = (1 - (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ))) / (4 * xiK2 d L N * F))
    (hLq : (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) ≤ 1 / 16) (hQ16 : xiK2 d L N * Q ≤ 1 / 16)
    (hNLN : Nonempty (NewLevelNumerics d L N T₀.m₁ T₀.c T₀.BG T₀.κ T₀.t T₀.c₂ T₀.BG₂ T₀.δc
      (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) ((2 * bgK1 d L N + 2) * xiC1 d * T₀.t))) :
    ∀ P₀ : Consts, P₀.γ = γ → 0 < P₀.α₀ →
    -- the radius constant `α₀` small (the (DL-gap))
    ((N : ℝ) + 1) * cK2 d L N * P₀.eps d L 1 ≤ 1 / 8 →
    -- the constants of the bound of the irrelevant parts (A4-1b (ii))
    ∀ (CI KL α₃ : ℝ) (n₁ : ℕ), 0 ≤ CI → 0 ≤ KL → 0 < α₃ →
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
    ∀ r₀ lam : ℝ, 0 < r₀ → lam = 1 + xiK2 d L N * ((3 / 2 : ℝ) * r₀) →
    xiK2 d L N * ((3 / 2 : ℝ) * r₀) ≤ 1 / 16 → lam * P₀.eps d L 1 ≤ T₀.t →
    ∀ (k : ℕ) (hk : 1 ≤ k), ∃ Tk : StepTowerG d L N κmin, Tk.t = lam * P₀.eps d L (k + 1) ∧
      Tk.m₁ = T₀.m₁ ∧ Tk.c = T₀.c ∧ Tk.BG = T₀.BG ∧ Tk.κ = T₀.κ ∧ Tk.c₂ = T₀.c₂ ∧
      Tk.BG₂ = T₀.BG₂ ∧ Tk.δc = T₀.δc ∧ Tk.δ = T₀.δ ∧ Tk.δ' = T₀.δ' ∧ Tk.κ0 = T₀.κ0 ∧ Tk.m₀ = T₀.m₀ ∧
      ChainNum d L N Tk.m₁ Tk.BG Tk.κ (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) Tk.t (Q * Tk.t) ∧
      FlNum d L N Tk.BG Tk.BG₂ Tk.κ Tk.t (Q * Tk.t) (min Tk.t (η * (lam * P₀.eps d L k)))
        (F * min Tk.t (η * (lam * P₀.eps d L k))) ∧
      -- the cover: the radius premise of `newLabels_castInputs` at `eps = Tk.t`
      P₀.eps d L (k + 1) ≤ Tk.t ∧
      -- the room of the inherited labels at every level `j ≤ k`
      (∀ j ≤ k, Tk.t + xiK2 d L N * (Q * Tk.t) +
        xiK2 d L N * (F * min Tk.t (η * (lam * P₀.eps d L k))) ≤ P₀.eps d L j) ∧
    ∀ (N₁ : ℕ) [NeZero N₁] (_ : L ^ Tk.m₀ ∣ N₁), 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
    ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
    ∀ {ϱ : ℝ} (_ : ϱ = rhoSepG d L Tk.m₁) (S : StepSetting d L N₁ Tk.m₁ k N ϱ)
      (_ : S = hatStepKG Tk.hN k Tk.m₁ ϱ hk ν β p₁ Tk.δ),
    ∃ Jr : S.JointRep Tk.t (2 * p₁),
    ∀ (C : StepClass d L N₁ Tk.m₁ k N ϱ) (z : RootIdx d L N₁ Tk.m₁ (k + 1))
      (𝒯E : Finset (ℕ × CTorus d L N₁ Tk.m₁ (k + 1) × Set (CTorus d L N₁ Tk.m₁ (k + 1))))
      (_ : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ Tk.m₁ (k + 1) ×
          Set (CTorus d L N₁ Tk.m₁ (k + 1))))).filter
        (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
      (Rg : Regime L) (a : ℕ → ℝ)
      (_ : P₀.m₀ = C.m₀) (_ : SFTermClauses P₀ (birthXiDom P₀ Rg a N₁) C.Tm)
      (_ : 0 ≤ P₀.E₀) (i₀ : Fin N)
      (_ : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ Tk.m₁) (k + 1)
          ϱ, (∀ i, j < i → G.Ω i = ∅) →
        ∀ Ψ : Fld d L N₁ Tk.m₁ (k + 1) N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
        (∀ x x', jBlock d L (N₁ * L ^ Tk.m₁) (k + 1) j x = jBlock d L (N₁ * L ^ Tk.m₁) (k + 1) j x' →
          Ψ x = Ψ x') →
        (birthXiDom P₀ Rg a N₁).dom j G Ψ (constFld (Pi.single i₀ 1)))
      (XL 𝒦X : {τ // τ ∈ 𝒯E} → Set (CTorus d L N₁ Tk.m₁ (k + 1)))
      (_ : ∀ τ : {τ // τ ∈ 𝒯E}, XL τ = τ.1.2.2 ∪ box (cbase (cellSide L C.m₀ Tk.m₁ τ.1.1) τ.1.2.1 -
        natT fun _ => L / 2 * cellSide L C.m₀ Tk.m₁ τ.1.1) (L * cellSide L C.m₀ Tk.m₁ τ.1.1))
      (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ChosenOne C.m₀ τ.1.1 (XL τ) (𝒦X τ))
      (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∃ (W₀ : Finset (CTorus d L N₁ Tk.m₁ (k + 1)))
        (E₀ : Finset (CTorus d L N₁ Tk.m₁ (k + 1) × CTorus d L N₁ Tk.m₁ (k + 1))),
        ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
          bondCost (scaleW L C.m₀ Tk.m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 (XL τ))
      (_ : L ^ C.m₀ ∣ N₁) (_ : d ≤ C.m₀) {s : ℕ} (_ : s ≤ C.m₀)
      (_ : (((5 * L + 13) * L ^ s : ℕ) : ℝ) + (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) * (L : ℝ) ≤ (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (C.m₀ + 1))
      (_ : rhoSepG d L Tk.m₁ ≤ Balaban.LargeField.minSep L (L ^ (Tk.m₁ + s))) (_ : C.m₀ = m₀)
      -- the regime of ruling R13, and the composed data of the labels in the class domain at the
      -- birth masses (the weights, the flow of the masses, the (DL-gap) and the smallness of `ε_j`)
      (_ : ClassHatCond C s (4 * (d : ℝ) * (L : ℝ) ^ 3 + L))
      (_ : aIdeal L (k + 1) (a (k + 1)) = compWeight L S.a₁)
      {ξ : ℕ → Fin 3 → ℂ} {q c₈ ν₀ : ℝ} (_ : 0 ≤ q) (_ : q < 1) (_ : 0 ≤ c₈)
      (_ : c₈ * q ≤ 1 - q) (_ : ∀ n, ‖ξ n‖ ≤ c₈ / 4 * q ^ (n + 1))
      (_ : ∀ n, n ≤ k → ((Rg.ν n : ℝ) : ℂ) = Flow.nuSeq (L : ℝ) ξ (ν₀ : ℂ) n)
      (_ : ν = physMass L k (Rg.ν k))
      {rm : ℝ} (_ : (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1) ≤ 1 / 2) (_ : 2 * (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1) < rm) (_ : rm ≤ 1 / 16)
      (_ : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (1 + 2 * (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1)) ≤ 1)
      -- the flow constant small (the (DL-gap))
      (_ : (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) *
        (2 * (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1)) ≤ 1 / 9)
      (_ : ∀ j, 1 ≤ j → j ≤ k → (4 * d + 6) * ((2 * d + 1) * P₀.eps d L j) ≤ 1)
      (_ : ∀ j, 1 ≤ j → j ≤ k → 4 * (xiC1 d * P₀.eps d L j) ≤ bgC1 d L N)
      (_ : ∀ j, 1 ≤ j → j ≤ k → bgK1 d L N * (xiC1 d * P₀.eps d L j) + 3 * rm ≤ deltaStar d L N)
      (_ : ∀ j, 1 ≤ j → j ≤ k → 8 * P₀.eps d L j * rm ≤ deltaStar d L N),
    ∃ (Gk : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ Tk.m₁) (k + 1) ϱ)
      (Gj : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ Tk.m₁) (k + 1) ϱ)
      (X₀ X₁f : {τ // τ ∈ 𝒯E} → Finset (CTorus d L N₁ Tk.m₁ (k + 1))),
      (∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ Tk.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ)) ∧
      (∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν Tk.c Tk.BG Tk.κ (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) Tk.t (Q * Tk.t) (X₀ τ) (X₁f τ) τ.1.1) ∧
      (∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ Tk.m₁ k ϱ) S.a₁ S.ν Tk.κ Tk.BG Tk.t (Q * Tk.t)
        (levelKc d L) (Cchi d L) Tk.c₂ Tk.BG₂ (min Tk.t (η * (lam * P₀.eps d L k))) (F * min Tk.t (η * (lam * P₀.eps d L k))) (X₁f τ)) ∧
      (∀ τ : {τ // τ ∈ 𝒯E}, Gj τ = C.Tm.gs τ.1.1 τ.1.2.2) ∧
      ∀
      -- the bounds of the irrelevant parts in `d(X)` on their term domain with their decay in the
      -- level (P1 (3.128), the open input A4-1b (ii))
      (Bl : ℕ → CTorus d L N₁ Tk.m₁ (k + 1) → Set (CTorus d L N₁ Tk.m₁ (k + 1)) → ℝ)
      (_ : ∀ j y X, 0 ≤ Bl j y X)
      (_ : ∀ (i₀ i₁ : Fin N) (j : ℕ) (y : CTorus d L N₁ Tk.m₁ (k + 1))
        (X : Set (CTorus d L N₁ Tk.m₁ (k + 1))), 1 ≤ j → j ≤ k → IsPolyDom C.m₀ j X → y ∈ X →
        ∀ Ψ h : Fld d L N₁ Tk.m₁ (k + 1) N, (birthXiDom P₀ Rg a N₁).dom j (C.Tm.gs j X) Ψ h →
        dot (Ψ y) (Ψ y) ∈ Complex.slitPlane →
        ‖irrelTorus C.m₀ C.Tm i₀ i₁ j y X Ψ h‖ ≤
          Bl j y X * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ j X))
      (_ : ∀ j y X, j + n₁ ≤ k →
        Bl j y X ≤ CI * P₀.E₀ * ((((L : ℝ)⁻¹ ^ (k - j)) ^ ((d : ℝ) + α₃))))
      (_ : ∀ j y X, k < j + n₁ → Bl j y X ≤ KL * P₀.E₀),
    -- the old densities are analytic along the path
    (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 Tk.t D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun q : Fld d L N₁ Tk.m₁ (k + 1) N × Fld d L N₁ Tk.m₁ (k + 1) N =>
          Edens C.m₀ C.Tm j q.1 q.2)
        (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
    ∃ e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁)
        (K := k + 1) 1 (k + 1) Set.univ) → ℂ, ∃ B : ℝ,
      (∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁) (K := k + 1) 1 (k + 1)
          Set.univ),
        AnalyticOnNhd ℂ (fun θ => e θ T') (physV S S.a₁ S.ν Tk.t) ∧
        (∀ θ ∈ physV S S.a₁ S.ν Tk.t, ∀ θ' ∈ physV S S.a₁ S.ν Tk.t,
          physRestrict (N := N) (thickSet S.G' (Yhat Set.univ (sitesOf T')))
              (physIncl N S θ) =
            physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf T'))) (physIncl N S θ') →
          e θ T' = e θ' T') ∧
        (∀ θ ∈ physV S S.a₁ S.ν Tk.t, ‖e θ T'‖ ≤
          (L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L Tk.κ /
              (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp Tk.κ))) *
              Real.exp (-((Tk.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) *
                dExt T') +
            B * Real.exp (-Tk.κ' * dExt T')) ∧
        (∀ θ, e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T'))) ∧
      (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 Tk.t D →
        Jr.E0locJ C z (rawOf D) = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
          (0 : CTorus d L N₁ Tk.m₁ (k + 1) → Fin N → ℂ)) T' ∧
        (S.withDatumH D).E0locH C z = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
          rawSub N S.G'), (0 : CTorus d L N₁ Tk.m₁ (k + 1) → Fin N → ℂ)) T') ∧
      (∀ ε : ℝ, ε ≤ Tk.t → ∀ q : Fld d L N₁ Tk.m₁ (k + 1) N × Fld d L N₁ Tk.m₁ (k + 1) N,
        XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
        Jr.densE0 C (rootSite z) q = ∑ T',
          (if h : clipRaw S.G' q ∈ rawSub N S.G' then
            e ((⟨clipRaw S.G' q, h⟩ : rawSub N S.G'), 0) T' else 0)) ∧
      -- the per-label spin covariance of the family
      (∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
        ∀ θ ∈ physV S S.a₁ S.ν Tk.t, ∀ θ' ∈ physV S S.a₁ S.ν Tk.t,
        (θ'.1 : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N) =
          rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N) →
        ∀ T', e θ' T' = e θ T') ∧ NewLevelFormula S C z Jr
        ⟨Tk.κ, Tk.BG, Tk.BG₂, p₁, Tk.κ0, Tk.κ, Tk.BG, Tk.BG₂, min Tk.t (η * (lam * P₀.eps d L k)), p₁, C.m₀,
          Tk.c, 4 * (d : ℝ) * (L : ℝ) ^ 3 + L, Q * Tk.t, levelKc d L, Cchi d L, Tk.c₂,
          F * min Tk.t (η * (lam * P₀.eps d L k))⟩ e ∧
      -- the clauses (A1)–(A5) of the new level on the local sets `𝔹_{k+1}(Ŷ⁺(T′))`
      ∀ {N₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ (Tk.m₁ + s) = N₁ * L ^ Tk.m₁)
        (hsep : ϱ ≤ Balaban.LargeField.minSep L (L ^ (Tk.m₁ + s)))
        (π : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N →L[ℂ] rawSub N S.G'),
        (∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩) →
      ∃ (f : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁) (K := k + 1) 1 (k + 1)
          Set.univ) → Fld d L N₁ Tk.m₁ (k + 1) N × Fld d L N₁ Tk.m₁ (k + 1) N → ℂ)
        (b : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁) (K := k + 1) 1 (k + 1)
          Set.univ) → ℝ),
        NewLevelLocalFamily S P₀ hc hsep
          (fun Y => {x' : CTorus d L N₁' (Tk.m₁ + s) (k + 1) |
            (torusCast x' : CTorus d L N₁ Tk.m₁ (k + 1)) ∈ hatSet P₀.m₀ (k + 1) Y}) π e f b := by
  classical
  have hd : 3 ≤ d := T₀.hd
  have hL : 3 ≤ L := T₀.hL
  have hN2 : 2 ≤ N := T₀.hN
  have : NeZero N := ⟨by omega⟩
  have hd0 : 0 < d := by omega
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have h3d : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hq0 : 0 < (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) := Real.rpow_pos_of_pos hLpos _
  have hq1 : (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < L)) (by linarith)
  obtain ⟨hQ, hF, hη⟩ := T₀.collar_consts_pos hq1 hQdef hFdef hηdef
  have hK : 0 < xiK2 d L N := by
    have := cK2_pos d L N
    unfold xiK2; positivity
  have hKFη : xiK2 d L N * F * η = (1 - (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ))) / 4 := by
    rw [hηdef]; field_simp
  obtain ⟨hNLN0⟩ := hNLN
  obtain ⟨hC0⟩ := T₀.core
  have hBG : 0 ≤ T₀.BG := hC0.hS.fam.2.1
  have hBG₂ : 0 ≤ T₀.BG₂ := hC0.hS2.fam.2.1
  have Hφ :=
    StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_ren_rot_formula_birth_of
      m₀ hA p hγ0 hγ1 T₀ hT hQdef hFdef hηdef
  intro P₀ hγ hα₀ hquad CI KL α₃ n₁ hCI hKL hα₃
  have hαP : P₀.alpha d = ((d : ℝ) - 2) / 2 - γ := by unfold Consts.alpha; rw [hγ]
  have hpos : ∀ j, 0 < P₀.eps d L j := fun j => by
    have := epsTail_pos j
    unfold Consts.eps epsSeq
    positivity
  have hanti : Antitone (P₀.eps d L) :=
    classEpsG_antitone (d := d) (L := L) hα₀.le (by rw [hαP]; linarith)
  obtain ⟨β₁, hβ₁, H⟩ := Hφ P₀ hγ hα₀
  -- the cap of Theorem 3.4 and the constant of the class at the base tower
  set cap : ℝ := 1 / (8 * (2 * (K0 d L T₀.κ0 + 1) + (K0 d L T₀.κ0 + rootUnionK d L 1 T₀.m₁ T₀.κ0) +
      rootUnionK d L 1 T₀.m₁ T₀.κ0) ^ 3 * c1 d L *
      Real.exp (((2 * T₀.κdec - 1) - 2 * T₀.κ0) * cG d L + c1 d L + T₀.κ' * cG d L)) with hcapdef
  have hcap : 0 < cap := by
    have := K0_pos d L T₀.κ0
    have := rootUnionK_nonneg (d := d) (L := L) (m₁ := T₀.m₁) 1 T₀.κ0
    have := one_le_c1 d L
    rw [hcapdef]; positivity
  set KO : ℝ := ((2 ^ L ^ d : ℕ) : ℝ) * (c1 d L * ((((L : ℝ) ^ (1 + m₀ + T₀.m₁)) ^ d) * P₀.E₀ *
      (2 * K0 d L T₀.κ0 * (CI * Real.exp ((κdec - 1) * cG d L) * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
        n₁ * (KL * Real.exp ((κdec - 1) * cG d L)) * ((((L : ℝ) ^ (n₁ - 1)) ^ d))))) *
      Real.exp ((2 * T₀.κdec - 1) * (2 * (d : ℝ) * (L : ℝ) ^ m₀ *
        ((((L ^ (m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L))) with hKOdef
  obtain ⟨β₂, -, Hβ⟩ := newLevel_beta_of (N := N) hd hL hA.le p hγ0 hγ1 T₀.m₁ (κ := T₀.κ)
    (BG := T₀.BG) (BG₂ := T₀.BG₂) T₀.fam_nonneg T₀.rho_nonneg hα₀ (lt_min one_pos hη) hcap
    (le_max_right KO 0)
  refine ⟨max β₁ β₂, hβ₁.trans (le_max_left _ _), fun r₀ lam hr hlam hr16 hε1 k hk => ?_⟩
  have hlam1 : 1 ≤ lam := by
    have := mul_pos hK (by positivity : (0 : ℝ) < 3 / 2 * r₀)
    rw [hlam]; linarith only [this]
  have hlam17 : lam ≤ 17 / 16 := by rw [hlam]; linarith only [hr16]
  have hrr : xiK2 d L N * ((3 / 2 : ℝ) * r₀) * (3 + (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ))) ≤
      1 - (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) := by
    have h0 : 0 ≤ xiK2 d L N * ((3 / 2 : ℝ) * r₀) := by positivity
    nlinarith only [h0, hr16, hLq, hq0]
  obtain ⟨Tk, hTt, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ', hTk0, hTm0, hC, hFl, hcov,
    hroom, Hk⟩ := H r₀ lam hr hlam hrr hε1 k hk
  refine ⟨Tk, hTt, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ', hTk0, hTm0, hC, hFl, hcov,
    hroom, ?_⟩
  intro N₁ _ hN₁ h5 ν hν0 hν β hβ p₁ hp0 hp₁ ϱ hϱ S hS
  obtain ⟨Jr, Hφ'⟩ := Hk N₁ hN₁ h5 ν hν0 hν β ((le_max_left _ _).trans hβ) p₁ hp0 hp₁ hϱ S hS
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 Rg a hm hcl hE₀ i₀ hdom XL 𝒦X hXL h𝒦 hopt hNC hm7 s hs hidx hmin hCm hHat
    hAw ξ q c₈ ν₀ hq0' hq1' hc₈ hc₈q hξ hνflow hνS rm hτ hτr hrm hmass hτK hsmε hc1ε hKε hζε
  -- the (DL-gap)
  have hgap := classEpsG_gap (d := d) (L := L) hα₀.le k
  rw [hαP] at hgap
  have hρ := dlGap_factor_le hq0.le hLq (mul_nonneg hK.le hQ) hQ16 hlam17
  have hDL := newLevel_dlGap (N := N) hanti hpos hk hgap hK.le hQ hF.le hη.le
    (zero_le_one.trans hlam1) hTt hKFη hρ (cK2_pos d L N).le hquad hτK
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, hGj, HG⟩ := @Hφ' C z 𝒯E h𝒯 P₀ Rg a hm hcl hE₀ i₀ i₀ hdom
    XL 𝒦X hXL h𝒦 hopt hNC hm7 s hs hidx hmin hCm hHat hAw ξ q c₈ ν₀ hq0' hq1' hc₈ hc₈q hξ hνflow
    hνS rm hτ hτr hrm hmass hDL hsmε hc1ε hKε hζε
  refine ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, hGj, ?_⟩
  intro Bl hBl hB hEbI hEbL hE
  -- the step
  have hSa : S.a₁ = 1 := by subst hS; rfl
  have hSβ : S.β = β := by subst hS; rfl
  have hSb : S.betaU = β * (L : ℝ) ^ (k * (d - 2)) := by
    subst hS; exact hatStepKG_betaU Tk.hN (by omega) k Tk.m₁ ϱ hk ν β p₁ Tk.δ
  have hκdecT : Tk.κdec = T₀.κdec := by rw [Tk.κdec_eq, T₀.κdec_eq, hTk0]
  have hκ'T : Tk.κ' = T₀.κ' := by rw [Tk.κ'_eq, T₀.κ'_eq, hκdecT, hTk0]
  have hβ3 : (3 : ℝ) ≤ β := (hβ₁.trans (le_max_left _ _)).trans hβ
  have hβ0 : 0 < β := lt_of_lt_of_le (by norm_num) hβ3
  -- the step radius and the fluctuation radius
  have htlow : P₀.α₀ * (L : ℝ) ^ (-((((d : ℝ) - 2) / 2 - γ) * ((k : ℝ) + 1))) ≤ Tk.t := by
    have h := classEpsG_lower (d := d) (L := L) hα₀.le (k + 1)
    rw [hαP] at h
    push_cast at h
    rw [hTt]
    exact h.trans (le_mul_of_one_le_left (hpos _).le hlam1)
  have hδ₁ : min 1 η * Tk.t ≤ min Tk.t (η * (lam * P₀.eps d L k)) := by
    have ht0 := Tk.t_pos
    refine le_min (mul_le_of_le_one_left ht0.le (min_le_left _ _)) ?_
    have hle : Tk.t ≤ lam * P₀.eps d L k := by
      rw [hTt]; exact mul_le_mul_of_nonneg_left (hanti (Nat.le_succ k)) (zero_le_one.trans hlam1)
    calc min 1 η * Tk.t ≤ η * Tk.t := mul_le_mul_of_nonneg_right (min_le_right _ _) ht0.le
      _ ≤ η * (lam * P₀.eps d L k) := mul_le_mul_of_nonneg_left hle hη.le
  have hδ0 : 0 < min Tk.t (η * (lam * P₀.eps d L k)) :=
    lt_of_lt_of_le (mul_pos (lt_min one_pos hη) Tk.t_pos) hδ₁
  obtain ⟨⟨cψ, r, R₁, R, U, hcψ, hρ₀c, hRu, hR₁, hr, hrays, hR, hRR, hUR, hU, hsmZ⟩, hmr, hca,
    hsmO⟩ := Hβ β ((le_max_right _ _).trans hβ) k hk Tk.t (min Tk.t (η * (lam * P₀.eps d L k))) p₁
      htlow hδ₁ hp0 hp₁
  -- the smallness of the class constants against the marked radius
  have hεnum : corrU / ((min Tk.t (η * (lam * P₀.eps d L k))) / (2 * markedRad d L N k S.a₁ Tk.κ p₁
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
      (((2 ^ L ^ d : ℕ) : ℝ) * (c1 d L * ((((L : ℝ) ^ (1 + C.m₀ + Tk.m₁)) ^ d) * P₀.E₀ *
      (2 * K0 d L Tk.κ0 * (CI * Real.exp ((κdec - 1) * cG d L) * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
        n₁ * (KL * Real.exp ((κdec - 1) * cG d L)) * ((((L : ℝ) ^ (n₁ - 1)) ^ d))))) *
      Real.exp ((2 * Tk.κdec - 1) * (2 * (d : ℝ) * (L : ℝ) ^ C.m₀ *
        ((((L ^ (C.m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L)))) ≤
      1 / (8 * (2 * (K0 d L Tk.κ0 + 1) + (K0 d L Tk.κ0 + rootUnionK d L 1 Tk.m₁ Tk.κ0) +
        rootUnionK d L 1 Tk.m₁ Tk.κ0) ^ 3 * c1 d L *
        Real.exp (((2 * Tk.κdec - 1) - 2 * Tk.κ0) * cG d L + c1 d L + Tk.κ' * cG d L)) := by
    rw [hSa, hSb, hTκ, hCm, hTm, hTk0, hκdecT, hκ'T]
    refine le_trans ?_ hsmO
    refine mul_le_mul_of_nonneg_left (le_max_left KO 0) ?_
    exact div_nonneg corrU_pos.le (div_nonneg hδ0.le (mul_pos two_pos hmr).le)
  obtain ⟨e, B, h1, h2, h3, h4, hnl⟩ := HG (fun τ => Bl τ.1.1 τ.1.2.1 τ.1.2.2)
    (fun τ => hBl _ _ _)
    (fun τ Ψ h hΨ hdot => by
      obtain ⟨hj1, hjk, -, hX, hy⟩ := classLabel_mem h𝒯 τ
      exact hB i₀ i₀ _ _ _ hj1 hjk hX hy Ψ h hΨ hdot)
    n₁ hCI hKL hα₃ (fun τ hτ => hEbI _ _ _ hτ) (fun τ hτ => hEbL _ _ _ hτ) hE hεnum
  refine ⟨e, B, h1, h2, h3, h4, hnl, ?_⟩
  intro N₁' _ hc hsep π hπ
  -- the numerics of the new level at the step radius `Tk.t`
  have hTkle : Tk.t ≤ T₀.t := by
    rw [hTt]
    exact (mul_le_mul_of_nonneg_left (hanti (by omega : 1 ≤ k + 1))
      (zero_le_one.trans hlam1)).trans hε1
  have hNk : Nonempty (NewLevelNumerics d L N Tk.m₁ Tk.c Tk.BG Tk.κ Tk.t Tk.c₂ Tk.BG₂ Tk.δc
      (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) ((2 * bgK1 d L N + 2) * xiC1 d * Tk.t)) := by
    have hT0 := T₀.t_pos
    have hl0 : 0 < Tk.t / T₀.t := div_pos Tk.t_pos hT0
    have hl1 : Tk.t / T₀.t ≤ 1 := (div_le_one hT0).2 hTkle
    have h := hNLN0.nonempty_scale hd0 hBG hBG₂ hl0 hl1
    have e1 : Tk.t / T₀.t * T₀.t = Tk.t := div_mul_cancel₀ _ hT0.ne'
    have e2 : Tk.t / T₀.t * ((2 * bgK1 d L N + 2) * xiC1 d * T₀.t) =
        (2 * bgK1 d L N + 2) * xiC1 d * Tk.t := by
      field_simp
    rw [e1, e2] at h
    rw [hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc]
    exact h
  obtain ⟨hNLNk⟩ := hNk
  obtain ⟨f, b, hf⟩ := Tk.newLevel_localFamily_of_class (hTm0.trans hT.m₀_eq) hk hN₁ h5 hν0 hν hβ0
    hp0 hϱ S hS Jr C z hδ0 (min_le_left _ _) (mul_nonneg hQ Tk.t_pos.le)
    (mul_nonneg hF.le hδ0.le) hm7 (by rw [hTκ]; exact hT.rate)
    (by rw [hκdecT, hCm]; exact hT.rate') e (fun θ T' => (h1 T').2.2.2 θ) hHat hnl hm Rg a hcl hAw
    hq0' hq1' hc₈ hc₈q hξ hνflow hνS hτ hτr hrm hmass hDL hsmε hc1ε hKε hζε Bl hBl hB n₁ hCI hKL
    hα₃ hE₀ hEbI hEbL hcov hNLNk hcψ hρ₀c (by rw [hSa, hSb, hTκ]; exact hRu) hR₁ hr hrays hR
    (by rw [hSa, hSb, hTκ]; exact hRR) hUR hU
    (by rw [hSβ, hSa, hTm, hTB₂, hTκ, hTB, hTk0, hκdecT, hκ'T]; exact hsmZ)
    (by rw [hSa, hSb, hTκ]; exact hmr) (by rw [hSa, hSb, hTκ]; exact hca) hεnum hc hsep π hπ
  exact ⟨f, b, hf⟩

open Classical in
/-- **The clauses (A1)–(A5) of the new level at every root along the class chain** (row (iii) of
A4-1b, route R-LOC; the provider of the label inputs of the new level).  At a base tower `T₀` of the
class chain with `K₂ Q ≤ 1/16` and the numerics of the new level (the tower of
`exists_newLevelConstants`), for `L^{-α} ≤ 1/16`: for every class constant `P₀` with
`(N + 1) K₂ ε₁ ≤ 1/8` and every set of constants of the bound of the irrelevant parts there is `β₀`
such that at every scale `k`, for every class `C` in the regime of ruling R13 with the flow constant
small and with the bound of its irrelevant terms on their term domain (A4-1b (ii)), the chain gives
a coefficient family `e z` of every root `z` with its rooted support and its value `E0locJ C z` on
the step chart, and, on the cast local sets `𝔹_{k+1}(Ŷ⁺(T′))`, local families `f z` with bounds
`b z` and (A1)–(A5) (`NewLevelLocalFamily`).  These are the premises `hsupp`, `hval`, `hfan`,
`hfbd`, `hfloc`, `hfrot`, `hfval` of `newLabels_castInputs_of_localFamily` (with `hG` from the step,
`S.G' = 𝔹_{k+1}`, and `hε` the cover `ε_{k+1} ≤ T_k.t`), which gives the label inputs of
`localClass_newLevel_of_expansion_cast`. -/
theorem StepTowerG.newLevel_localFamilies_birth_of
    {d L N : ℕ} [NeZero L] (m₀ : ℕ) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1 / 2) {κmin : ℝ} (T₀ : StepTowerG d L N κmin) {κdec : ℝ}
    (hT : CollarBase d L N m₀ ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ))) T₀ κdec) {Q F η : ℝ}
    (hQdef : Q = (N : ℝ) * composedCloseBound d L N T₀.m₁ T₀.BG T₀.κ (xiC1 d)
      (4 * (d : ℝ) * (L : ℝ) ^ 3 + L))
    (hFdef : F = (N : ℝ) * (5 * cK2' d L N (famConst d L T₀.BG₂ T₀.κ) + 1))
    (hηdef : η = (1 - (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ))) / (4 * xiK2 d L N * F))
    (hLq : (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) ≤ 1 / 16) (hQ16 : xiK2 d L N * Q ≤ 1 / 16)
    (hNLN : Nonempty (NewLevelNumerics d L N T₀.m₁ T₀.c T₀.BG T₀.κ T₀.t T₀.c₂ T₀.BG₂ T₀.δc
      (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) ((2 * bgK1 d L N + 2) * xiC1 d * T₀.t))) :
    ∀ P₀ : Consts, P₀.γ = γ → 0 < P₀.α₀ →
    -- the radius constant `α₀` small (the (DL-gap))
    ((N : ℝ) + 1) * cK2 d L N * P₀.eps d L 1 ≤ 1 / 8 →
    -- the constants of the bound of the irrelevant parts (A4-1b (ii))
    ∀ (CI KL α₃ : ℝ) (n₁ : ℕ), 0 ≤ CI → 0 ≤ KL → 0 < α₃ →
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
    ∀ r₀ lam : ℝ, 0 < r₀ → lam = 1 + xiK2 d L N * ((3 / 2 : ℝ) * r₀) →
    xiK2 d L N * ((3 / 2 : ℝ) * r₀) ≤ 1 / 16 → lam * P₀.eps d L 1 ≤ T₀.t →
    ∀ (k : ℕ) (hk : 1 ≤ k), ∃ Tk : StepTowerG d L N κmin, Tk.t = lam * P₀.eps d L (k + 1) ∧
      Tk.m₁ = T₀.m₁ ∧ Tk.c = T₀.c ∧ Tk.BG = T₀.BG ∧ Tk.κ = T₀.κ ∧ Tk.c₂ = T₀.c₂ ∧
      Tk.BG₂ = T₀.BG₂ ∧ Tk.δc = T₀.δc ∧ Tk.δ = T₀.δ ∧ Tk.δ' = T₀.δ' ∧ Tk.κ0 = T₀.κ0 ∧ Tk.m₀ = T₀.m₀ ∧
      ChainNum d L N Tk.m₁ Tk.BG Tk.κ (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) Tk.t (Q * Tk.t) ∧
      FlNum d L N Tk.BG Tk.BG₂ Tk.κ Tk.t (Q * Tk.t) (min Tk.t (η * (lam * P₀.eps d L k)))
        (F * min Tk.t (η * (lam * P₀.eps d L k))) ∧
      -- the cover: the radius premise of `newLabels_castInputs` at `eps = Tk.t`
      P₀.eps d L (k + 1) ≤ Tk.t ∧
      -- the room of the inherited labels at every level `j ≤ k`
      (∀ j ≤ k, Tk.t + xiK2 d L N * (Q * Tk.t) +
        xiK2 d L N * (F * min Tk.t (η * (lam * P₀.eps d L k))) ≤ P₀.eps d L j) ∧
    ∀ (N₁ : ℕ) [NeZero N₁] (_ : L ^ Tk.m₀ ∣ N₁), 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
    ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
    ∀ {ϱ : ℝ} (_ : ϱ = rhoSepG d L Tk.m₁) (S : StepSetting d L N₁ Tk.m₁ k N ϱ)
      (_ : S = hatStepKG Tk.hN k Tk.m₁ ϱ hk ν β p₁ Tk.δ),
    ∃ Jr : S.JointRep Tk.t (2 * p₁),
    ∀ (C : StepClass d L N₁ Tk.m₁ k N ϱ)
      (𝒯E : Finset (ℕ × CTorus d L N₁ Tk.m₁ (k + 1) × Set (CTorus d L N₁ Tk.m₁ (k + 1))))
      (_ : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ Tk.m₁ (k + 1) ×
          Set (CTorus d L N₁ Tk.m₁ (k + 1))))).filter
        (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
      (Rg : Regime L) (a : ℕ → ℝ)
      (_ : P₀.m₀ = C.m₀) (_ : SFTermClauses P₀ (birthXiDom P₀ Rg a N₁) C.Tm)
      (_ : 0 ≤ P₀.E₀) (i₀ : Fin N)
      (_ : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ Tk.m₁) (k + 1)
          ϱ, (∀ i, j < i → G.Ω i = ∅) →
        ∀ Ψ : Fld d L N₁ Tk.m₁ (k + 1) N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
        (∀ x x', jBlock d L (N₁ * L ^ Tk.m₁) (k + 1) j x = jBlock d L (N₁ * L ^ Tk.m₁) (k + 1) j x' →
          Ψ x = Ψ x') →
        (birthXiDom P₀ Rg a N₁).dom j G Ψ (constFld (Pi.single i₀ 1)))
      (XL 𝒦X : {τ // τ ∈ 𝒯E} → Set (CTorus d L N₁ Tk.m₁ (k + 1)))
      (_ : ∀ τ : {τ // τ ∈ 𝒯E}, XL τ = τ.1.2.2 ∪ box (cbase (cellSide L C.m₀ Tk.m₁ τ.1.1) τ.1.2.1 -
        natT fun _ => L / 2 * cellSide L C.m₀ Tk.m₁ τ.1.1) (L * cellSide L C.m₀ Tk.m₁ τ.1.1))
      (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ChosenOne C.m₀ τ.1.1 (XL τ) (𝒦X τ))
      (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∃ (W₀ : Finset (CTorus d L N₁ Tk.m₁ (k + 1)))
        (E₀ : Finset (CTorus d L N₁ Tk.m₁ (k + 1) × CTorus d L N₁ Tk.m₁ (k + 1))),
        ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
          bondCost (scaleW L C.m₀ Tk.m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 (XL τ))
      (_ : L ^ C.m₀ ∣ N₁) (_ : d ≤ C.m₀) {s : ℕ} (_ : s ≤ C.m₀)
      (_ : (((5 * L + 13) * L ^ s : ℕ) : ℝ) + (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) * (L : ℝ) ≤ (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (C.m₀ + 1))
      (_ : rhoSepG d L Tk.m₁ ≤ Balaban.LargeField.minSep L (L ^ (Tk.m₁ + s))) (_ : C.m₀ = m₀)
      -- the regime of ruling R13, and the composed data of the labels in the class domain at the
      -- birth masses (the weights, the flow of the masses, the (DL-gap) and the smallness of `ε_j`)
      (_ : ClassHatCond C s (4 * (d : ℝ) * (L : ℝ) ^ 3 + L))
      (_ : aIdeal L (k + 1) (a (k + 1)) = compWeight L S.a₁)
      {ξ : ℕ → Fin 3 → ℂ} {q c₈ ν₀ : ℝ} (_ : 0 ≤ q) (_ : q < 1) (_ : 0 ≤ c₈)
      (_ : c₈ * q ≤ 1 - q) (_ : ∀ n, ‖ξ n‖ ≤ c₈ / 4 * q ^ (n + 1))
      (_ : ∀ n, n ≤ k → ((Rg.ν n : ℝ) : ℂ) = Flow.nuSeq (L : ℝ) ξ (ν₀ : ℂ) n)
      (_ : ν = physMass L k (Rg.ν k))
      {rm : ℝ} (_ : (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1) ≤ 1 / 2) (_ : 2 * (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1) < rm) (_ : rm ≤ 1 / 16)
      (_ : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (1 + 2 * (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1)) ≤ 1)
      -- the flow constant small (the (DL-gap))
      (_ : (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) *
        (2 * (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1)) ≤ 1 / 9)
      (_ : ∀ j, 1 ≤ j → j ≤ k → (4 * d + 6) * ((2 * d + 1) * P₀.eps d L j) ≤ 1)
      (_ : ∀ j, 1 ≤ j → j ≤ k → 4 * (xiC1 d * P₀.eps d L j) ≤ bgC1 d L N)
      (_ : ∀ j, 1 ≤ j → j ≤ k → bgK1 d L N * (xiC1 d * P₀.eps d L j) + 3 * rm ≤ deltaStar d L N)
      (_ : ∀ j, 1 ≤ j → j ≤ k → 8 * P₀.eps d L j * rm ≤ deltaStar d L N)
      -- the bounds of the irrelevant parts in `d(X)` on their term domain with their decay in the
      -- level (P1 (3.128), the open input A4-1b (ii))
      (Bl : ℕ → CTorus d L N₁ Tk.m₁ (k + 1) → Set (CTorus d L N₁ Tk.m₁ (k + 1)) → ℝ)
      (_ : ∀ j y X, 0 ≤ Bl j y X)
      (_ : ∀ (i₀ i₁ : Fin N) (j : ℕ) (y : CTorus d L N₁ Tk.m₁ (k + 1))
        (X : Set (CTorus d L N₁ Tk.m₁ (k + 1))), 1 ≤ j → j ≤ k → IsPolyDom C.m₀ j X → y ∈ X →
        ∀ Ψ h : Fld d L N₁ Tk.m₁ (k + 1) N, (birthXiDom P₀ Rg a N₁).dom j (C.Tm.gs j X) Ψ h →
        dot (Ψ y) (Ψ y) ∈ Complex.slitPlane →
        ‖irrelTorus C.m₀ C.Tm i₀ i₁ j y X Ψ h‖ ≤
          Bl j y X * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ j X))
      (_ : ∀ j y X, j + n₁ ≤ k →
        Bl j y X ≤ CI * P₀.E₀ * ((((L : ℝ)⁻¹ ^ (k - j)) ^ ((d : ℝ) + α₃))))
      (_ : ∀ j y X, k < j + n₁ → Bl j y X ≤ KL * P₀.E₀),
    -- the old densities are analytic along the path
    (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 Tk.t D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun q : Fld d L N₁ Tk.m₁ (k + 1) N × Fld d L N₁ Tk.m₁ (k + 1) N =>
          Edens C.m₀ C.Tm j q.1 q.2)
        (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
    ∃ e : RootIdx d L N₁ Tk.m₁ (k + 1) → physParam N S →
        Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁) (K := k + 1) 1 (k + 1) Set.univ) →
          ℂ,
      -- the rooted polymer support and the value of the family of every root (the premises
      -- `hsupp`, `hval` of `newLabels_castInputs_of_localFamily`)
      (∀ z θ T', e z θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')) ∧
      (∀ z (D : BgData S.G' N), XiCData S.G' S.a S.ν (k + 1) 1 Tk.t D →
        Jr.E0locJ C z (rawOf D) = ∑ T', e z ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
          (0 : CTorus d L N₁ Tk.m₁ (k + 1) → Fin N → ℂ)) T') ∧
      -- the clauses (A1)–(A5) of every root on the local sets `𝔹_{k+1}(Ŷ⁺(T′))`
      ∀ {N₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ (Tk.m₁ + s) = N₁ * L ^ Tk.m₁)
        (hsep : ϱ ≤ Balaban.LargeField.minSep L (L ^ (Tk.m₁ + s)))
        (π : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N →L[ℂ] rawSub N S.G'),
        (∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩) →
      ∃ (f : RootIdx d L N₁ Tk.m₁ (k + 1) → Finset (CubeB (d := d) (L := L) (N₁ := N₁)
          (m₁ := Tk.m₁) (K := k + 1) 1 (k + 1) Set.univ) →
            Fld d L N₁ Tk.m₁ (k + 1) N × Fld d L N₁ Tk.m₁ (k + 1) N → ℂ)
        (b : RootIdx d L N₁ Tk.m₁ (k + 1) → Finset (CubeB (d := d) (L := L) (N₁ := N₁)
          (m₁ := Tk.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℝ),
        ∀ z, NewLevelLocalFamily S P₀ hc hsep
          (fun Y => {x' : CTorus d L N₁' (Tk.m₁ + s) (k + 1) |
            (torusCast x' : CTorus d L N₁ Tk.m₁ (k + 1)) ∈ hatSet P₀.m₀ (k + 1) Y}) π (e z) (f z)
          (b z) := by
  intro P₀ hγ hα₀ hquad CI KL α₃ n₁ hCI hKL hα₃
  obtain ⟨β₀, hβ₀, H⟩ := T₀.newLevel_localFamily_birth_of m₀ hA p hγ0 hγ1 hT hQdef hFdef hηdef
    hLq hQ16 hNLN P₀ hγ hα₀ hquad CI KL α₃ n₁ hCI hKL hα₃
  refine ⟨β₀, hβ₀, fun r₀ lam hr hlam hr16 hε1 k hk => ?_⟩
  obtain ⟨Tk, hTt, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ', hTk0, hTm0, hC, hFl, hcov,
    hroom, Hk⟩ := H r₀ lam hr hlam hr16 hε1 k hk
  refine ⟨Tk, hTt, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ', hTk0, hTm0, hC, hFl, hcov,
    hroom, ?_⟩
  intro N₁ _ hN₁ h5 ν hν0 hν β hβ p₁ hp0 hp₁ ϱ hϱ S hS
  obtain ⟨Jr, HJ⟩ := Hk N₁ hN₁ h5 ν hν0 hν β hβ p₁ hp0 hp₁ hϱ S hS
  refine ⟨Jr, ?_⟩
  intro C 𝒯E h𝒯 Rg a hm hcl hE₀ i₀ hdom XL 𝒦X hXL h𝒦 hopt hNC hm7 s hs hidx hmin hCm hHat
    hAw ξ q c₈ ν₀ hq0 hq1 hc₈ hc₈q hξ hνflow hνS rm hτ hτr hrm hmass hτK hsmε hc1ε hKε hζε
    Bl hBl hB hEbI hEbL hE
  -- the family of every root
  have Hz : ∀ z : RootIdx d L N₁ Tk.m₁ (k + 1), ∃ e : physParam N S →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℂ,
      (∀ θ T', e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')) ∧
      (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 Tk.t D →
        Jr.E0locJ C z (rawOf D) = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
          (0 : CTorus d L N₁ Tk.m₁ (k + 1) → Fin N → ℂ)) T') ∧
      ∀ {N₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ (Tk.m₁ + s) = N₁ * L ^ Tk.m₁)
        (hsep : ϱ ≤ Balaban.LargeField.minSep L (L ^ (Tk.m₁ + s)))
        (π : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N →L[ℂ] rawSub N S.G'),
        (∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩) →
      ∃ (f : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁) (K := k + 1) 1 (k + 1)
          Set.univ) → Fld d L N₁ Tk.m₁ (k + 1) N × Fld d L N₁ Tk.m₁ (k + 1) N → ℂ)
        (b : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁) (K := k + 1) 1 (k + 1)
          Set.univ) → ℝ),
        NewLevelLocalFamily S P₀ hc hsep
          (fun Y => {x' : CTorus d L N₁' (Tk.m₁ + s) (k + 1) |
            (torusCast x' : CTorus d L N₁ Tk.m₁ (k + 1)) ∈ hatSet P₀.m₀ (k + 1) Y}) π e f b := by
    intro z
    obtain ⟨-, -, -, -, -, -, -, -, HG⟩ := @HJ C z 𝒯E h𝒯 Rg a hm hcl hE₀ i₀ hdom XL 𝒦X hXL h𝒦
      hopt hNC hm7 s hs hidx hmin hCm hHat hAw ξ q c₈ ν₀ hq0 hq1 hc₈ hc₈q hξ hνflow hνS rm hτ hτr
      hrm hmass hτK hsmε hc1ε hKε hζε
    obtain ⟨e, _B, h1, h2, -, -, -, hloc⟩ := HG Bl hBl hB hEbI hEbL hE
    exact ⟨e, fun θ T' => (h1 T').2.2.2 θ, fun D hD => (h2 D hD).1, hloc⟩
  choose e he using Hz
  refine ⟨e, fun z => (he z).1, fun z => (he z).2.1, ?_⟩
  intro N₁' _ hc hsep π hπ
  choose f b hf using fun z => (he z).2.2 hc hsep π hπ
  exact ⟨f, b, hf⟩

end Balaban.Inhabited
