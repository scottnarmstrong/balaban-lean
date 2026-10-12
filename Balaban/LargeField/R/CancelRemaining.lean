/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CancelBound
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Lemma III.6.4: the remaining terms (LF-RECONSTRUCTION §III.6.3, (2.59)′, (2.60)′; P7 (2.59)-(2.60))

The field estimates behind Lemma III.6.4, with the one cited input stated once:

* `Lemma262` (P7 Lemma 2.2 = Lemma III.6.2, (2.41), cited): pointwise bounds on `∂φ̄⁰`, on the mass term
  `|ν||φ⁰ - h|²` and on the multiplier `α⁰` of `φ⁰_k`; `lemma262_nonempty` is its inhabitedness
  (for every datum there are constants for which it holds);
* `norm_actionRegion0_le` ((a), P7 (2.59)): `|A*_{0,k}(Z_{k₁}; φ⁰)| ≤ ½ B_∂² d #Z_{k₁} + ½ #Z_{k₁} B_m`;
* `norm_alphaTerm_le`, `norm_massSelf_le` ((b), P7 (2.60)): `½ β_k |⟨δφ, (α⁰ + ν) δφ⟩|` for a pointwise
  bound on `δφ` (the layered bound (2.49′), `deltaPhi_le_of_dataChange`);
* `norm_starPair_le` and the `ν`-term ((c));
* `remaining_terms`: (a), (b), (c) with the strict bound `< ¼` from the numerical conditions.

The numerical conditions (`hΛa`, `hΛb`, `hΛb'`, `hΛc`, `hΛν`) are the strengthened (Λ25)(a)-(c) for the
constants of the pointwise bounds; their derivation from the parameter chain (III.1.1), (III.1.2) (c),
`ν_max` and (Λ25) is not formalized here.  The "Consequently" part of Lemma III.6.4
(`β_k{···} ≥ γ₀·(LF-1 bracket) - 1`) needs LF-1 (a) for the pair `(δψ, δφ)` and is not formalized.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace Balaban.LargeField.ActionConv

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Finset

section Pairs

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}

theorem sum_starWeight (D : Region G) :
    ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d, D.starWeight x μ = d * D.sites.card := by
  unfold Region.starWeight
  rw [Finset.sum_comm]
  have h1 : ∀ μ : Fin d, ∑ x : Torus d (N₀ * L ^ k),
      (((if x ∈ D.sites then (1 : ℝ) else 0) + (if x + Pi.single μ 1 ∈ D.sites then 1 else 0)) / 2) =
      D.sites.card := by
    intro μ
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    have e1 : ∑ x : Torus d (N₀ * L ^ k), (if x ∈ D.sites then (1 : ℝ) else 0) = D.sites.card := by
      simp
    have e2 : ∑ x : Torus d (N₀ * L ^ k), (if x + Pi.single μ 1 ∈ D.sites then (1 : ℝ) else 0) =
        D.sites.card := by
      rw [← e1]
      exact Fintype.sum_equiv (Equiv.addRight (Pi.single μ 1 : Torus d (N₀ * L ^ k)))
        (fun x => if x + Pi.single μ 1 ∈ D.sites then (1 : ℝ) else 0)
        (fun x => if x ∈ D.sites then (1 : ℝ) else 0) (fun x => rfl)
    rw [e1, e2]; ring
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem starWeight_nonneg (D : Region G) (x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    0 ≤ D.starWeight x μ := by
  unfold Region.starWeight
  have : (0 : ℝ) ≤ (if x ∈ D.sites then 1 else 0) := by split_ifs <;> norm_num
  have : (0 : ℝ) ≤ (if x + Pi.single μ 1 ∈ D.sites then 1 else 0) := by split_ifs <;> norm_num
  positivity

/-- `‖⟨f, f⟩_{D*}‖ ≤ B² d #D` if every bond meeting `D` has `|∂f| ≤ B`. -/
theorem norm_bondPair_le (D : Region G) (f : Torus d (N₀ * L ^ k) → Fin N → ℂ) {B : ℝ}
    (hB : ∀ x μ, D.starWeight x μ ≠ 0 →
      vn (fun i => f (x + Pi.single μ 1) i - f x i) ≤ B) :
    ‖D.bondPair f f‖ ≤ B ^ 2 * (d * D.sites.card) := by
  unfold Region.bondPair
  rw [← sum_starWeight D, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (starWeight_nonneg D x μ)]
  by_cases hw : D.starWeight x μ = 0
  · simp [hw]
  · have := norm_dotC_le (fun i => f (x + Pi.single μ 1) i - f x i)
      (fun i => f (x + Pi.single μ 1) i - f x i)
    have hb := hB x μ hw
    have hn := vn_nonneg (fun i => f (x + Pi.single μ 1) i - f x i)
    calc D.starWeight x μ * ‖∑ i, (f (x + Pi.single μ 1) i - f x i) *
          (f (x + Pi.single μ 1) i - f x i)‖
        ≤ D.starWeight x μ * (B ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (starWeight_nonneg D x μ)
          refine this.trans ?_
          nlinarith
      _ = B ^ 2 * D.starWeight x μ := by ring

/-- `‖⟨p, q⟩_D‖ ≤ #D · P Q` for pointwise bounds `|p| ≤ P`, `|q| ≤ Q` on `D`. -/
theorem norm_massPair_le (D : Region G) (p q : Torus d (N₀ * L ^ k) → Fin N → ℂ) {P Q : ℝ}
    (hp : ∀ x ∈ D.sites, vn (p x) ≤ P) (hq : ∀ x ∈ D.sites, vn (q x) ≤ Q) :
    ‖D.massPair p q‖ ≤ D.sites.card * (P * Q) := by
  unfold Region.massPair
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x ∈ D.sites, ‖∑ i, p x i * q x i‖ ≤ ∑ x ∈ D.sites, P * Q := by
        refine Finset.sum_le_sum fun x hx => (norm_dotC_le (p x) (q x)).trans ?_
        exact mul_le_mul (hp x hx) (hq x hx) (vn_nonneg _) ((vn_nonneg _).trans (hp x hx))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- `‖⟨p, γ q⟩_D‖ ≤ #D · B_γ P Q`. -/
theorem norm_sitePair_le (D : Region G) (γ : G.Ω 1 → ℂ) (p q : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    {Bγ P Q : ℝ} (hγ : ∀ x ∈ D.sites, ‖zeroExt (G.Ω 1) γ x‖ ≤ Bγ)
    (hp : ∀ x ∈ D.sites, vn (p x) ≤ P) (hq : ∀ x ∈ D.sites, vn (q x) ≤ Q) :
    ‖D.sitePair γ p q‖ ≤ D.sites.card * (Bγ * (P * Q)) := by
  unfold Region.sitePair
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x ∈ D.sites, ‖zeroExt (G.Ω 1) γ x * ∑ i, p x i * q x i‖
      ≤ ∑ x ∈ D.sites, Bγ * (P * Q) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [norm_mul]
        have h1 := (norm_dotC_le (p x) (q x)).trans
          (mul_le_mul (hp x hx) (hq x hx) (vn_nonneg _) ((vn_nonneg _).trans (hp x hx)))
        have h2 : 0 ≤ Bγ := (norm_nonneg _).trans (hγ x hx)
        exact mul_le_mul (hγ x hx) h1 (norm_nonneg _) h2
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end Pairs

section Remaining

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

/-- **Lemma III.6.2 (P7 Lemma 2.2, (2.41); cited)** for the single-scale background `φ⁰_k`, in fine units, on
a set `S` of sites: the gradient `|∂φ̄⁰| ≤ B_∂` of the bonds meeting `S`, the mass term
`|ν||φ⁰ - h|² ≤ B_m` (the (R3)-type bound), and the multiplier `|α⁰| ≤ B_α`.  The constants are those of
(2.41) (`3K₁K₆δ_k` in scale-`k` units, `6K₁K₆ε_k` for the extension) converted to fine units; they are
parameters of the structure.  This is the one input of Lemma III.6.4 that is not proved here. -/
structure Lemma262 (G' : GeneratingSet d L N₀ k ϱ') (a : ℕ → ℝ)
    (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ) (ν : ℝ)
    (S : Finset (Torus d (N₀ * L ^ k))) (Bgrad Bmass Balpha : ℝ) : Prop where
  grad : ∀ (x : Torus d (N₀ * L ^ k)) (μ : Fin d), (x ∈ S ∨ x + Pi.single μ 1 ∈ S) →
    vn (fun i => barField G' (psiZeroData G' ψ0 h).Ψ (phiZero G' a ψ0 h) (x + Pi.single μ 1) i -
      barField G' (psiZeroData G' ψ0 h).Ψ (phiZero G' a ψ0 h) x i) ≤ Bgrad
  mass : ∀ x ∈ S, |ν| * vn (fun i => svec G' (phiZero G' a ψ0 h) x i -
    (psiZeroData G' ψ0 h).h x i) ^ 2 ≤ Bmass
  alpha : ∀ x ∈ S, ‖zeroExt (G'.Ω 1) (alphaZero G' a ψ0 h) x‖ ≤ Balpha
  grad_nonneg : 0 ≤ Bgrad
  mass_nonneg : 0 ≤ Bmass
  alpha_nonneg : 0 ≤ Balpha

/-- `Lemma262` is inhabited: for all data there are constants (finite suprema over the torus) for which
the bounds hold. -/
theorem le_sum_univ {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (x : ι) :
    f x ≤ ∑ y, f y :=
  Finset.single_le_sum (fun i _ => hf i) (Finset.mem_univ x)

theorem lemma262_nonempty (G' : GeneratingSet d L N₀ k ϱ') (a : ℕ → ℝ)
    (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ) (ν : ℝ)
    (S : Finset (Torus d (N₀ * L ^ k))) :
    ∃ Bgrad Bmass Balpha : ℝ, Lemma262 G' a ψ0 h ν S Bgrad Bmass Balpha := by
  classical
  set g : Torus d (N₀ * L ^ k) → Fin d → ℝ := fun x μ => vn (fun i =>
      barField G' (psiZeroData G' ψ0 h).Ψ (phiZero G' a ψ0 h) (x + Pi.single μ 1) i -
      barField G' (psiZeroData G' ψ0 h).Ψ (phiZero G' a ψ0 h) x i) with hg
  set m : Torus d (N₀ * L ^ k) → ℝ := fun x => |ν| * vn (fun i =>
      svec G' (phiZero G' a ψ0 h) x i - (psiZeroData G' ψ0 h).h x i) ^ 2 with hm
  set al : Torus d (N₀ * L ^ k) → ℝ := fun x =>
      ‖zeroExt (G'.Ω 1) (alphaZero G' a ψ0 h) x‖ with hal
  have hg0 : ∀ x μ, 0 ≤ g x μ := fun x μ => vn_nonneg _
  have hm0 : ∀ x, 0 ≤ m x := fun x => by simp only [hm]; positivity
  have hal0 : ∀ x, 0 ≤ al x := fun x => norm_nonneg _
  refine ⟨∑ x, ∑ μ, g x μ, ∑ x, m x, ∑ x, al x, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x μ _
    exact (le_sum_univ (g x) (hg0 x) μ).trans
      (le_sum_univ (fun x => ∑ μ, g x μ) (fun x => Finset.sum_nonneg fun μ _ => hg0 x μ) x)
  · intro x _
    exact le_sum_univ m hm0 x
  · intro x _
    exact le_sum_univ al hal0 x
  · exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun μ _ => hg0 x μ
  · exact Finset.sum_nonneg fun x _ => hm0 x
  · exact Finset.sum_nonneg fun x _ => hal0 x


theorem region_starWeight_ne_zero (D : Region G') {x : Torus d (N₀ * L ^ k)} {μ : Fin d}
    (h : D.starWeight x μ ≠ 0) : x ∈ D.sites ∨ x + Pi.single μ 1 ∈ D.sites := by
  by_contra hcon
  push Not at hcon
  apply h
  unfold Region.starWeight
  simp [hcon.1, hcon.2]

/-- **Lemma III.6.4 (a), field estimate** (P7 (2.59)): from (2.41) for the extension,
`|A*_{0,k}(Z_{k₁}; φ⁰)| ≤ ½ B_∂² d #Z_{k₁} + ½ #Z_{k₁} B_m`. -/
theorem norm_actionRegion0_le (a : ℕ → ℝ) (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N))
    (h : Fin N → ℝ) (Zk1 : Region G') {ν Bgrad Bmass Balpha : ℝ}
    (hL : Lemma262 G' a ψ0 h ν Zk1.sites Bgrad Bmass Balpha) :
    ‖actionRegion0 Zk1 ν (psiZeroData G' ψ0 h) (phiZero G' a ψ0 h)‖ ≤
      1 / 2 * (Bgrad ^ 2 * (d * Zk1.sites.card)) + 1 / 2 * (Zk1.sites.card * Bmass) := by
  unfold actionRegion0
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    have := norm_bondPair_le Zk1
      (barField G' (psiZeroData G' ψ0 h).Ψ (phiZero G' a ψ0 h)) (B := Bgrad)
      (fun x μ hw => hL.grad x μ (region_starWeight_ne_zero Zk1 hw))
    have e : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [e]
    linarith
  · rw [norm_mul]
    have hn : ‖(ν : ℂ) / 2‖ = |ν| / 2 := by
      rw [norm_div]; simp
    rw [hn]
    unfold Region.massPair
    have h1 : ‖∑ x ∈ Zk1.sites, ∑ i, (svec G' (phiZero G' a ψ0 h) x i -
        (psiZeroData G' ψ0 h).h x i) * (svec G' (phiZero G' a ψ0 h) x i -
        (psiZeroData G' ψ0 h).h x i)‖ ≤ ∑ x ∈ Zk1.sites, vn (fun i => svec G' (phiZero G' a ψ0 h) x i -
        (psiZeroData G' ψ0 h).h x i) ^ 2 := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
      have := norm_dotC_le (fun i => svec G' (phiZero G' a ψ0 h) x i - (psiZeroData G' ψ0 h).h x i)
        (fun i => svec G' (phiZero G' a ψ0 h) x i - (psiZeroData G' ψ0 h).h x i)
      unfold dotC at this
      nlinarith
    have h2 : |ν| * ∑ x ∈ Zk1.sites, vn (fun i => svec G' (phiZero G' a ψ0 h) x i -
        (psiZeroData G' ψ0 h).h x i) ^ 2 ≤ Zk1.sites.card * Bmass := by
      rw [Finset.mul_sum]
      calc _ ≤ ∑ x ∈ Zk1.sites, Bmass := Finset.sum_le_sum fun x hx => hL.mass x hx
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    calc |ν| / 2 * ‖∑ x ∈ Zk1.sites, ∑ i, (svec G' (phiZero G' a ψ0 h) x i -
        (psiZeroData G' ψ0 h).h x i) * (svec G' (phiZero G' a ψ0 h) x i -
        (psiZeroData G' ψ0 h).h x i)‖ ≤ |ν| / 2 * ∑ x ∈ Zk1.sites, vn (fun i => svec G' (phiZero G' a ψ0 h) x i -
        (psiZeroData G' ψ0 h).h x i) ^ 2 := by gcongr
      _ ≤ 1 / 2 * (Zk1.sites.card * Bmass) := by linarith

theorem zeroExt_restrictα (hprec : Precedes G G') (α' : G'.Ω 1 → ℂ) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) :
    zeroExt (G.Ω 1) (hprec.restrictα α') x = zeroExt (G'.Ω 1) α' x := by
  have hx' : x ∈ G'.Ω 1 := hprec.mem_Ω1 hx
  simp [zeroExt, hx, hx', Precedes.restrictα, Precedes.incl]

/-- **Lemma III.6.4 (b), field estimate** (P7 (2.60)): `½ β_k |⟨δφ, γ δφ⟩_{X_win}| ≤ ½ β_k #X_win B_γ B_δ²`
for `|γ| ≤ B_γ`, `|δφ| ≤ B_δ` on `X_win`. -/
theorem norm_alphaTerm_le (D : Region G) {β0 Bγ Bδ : ℝ} (hβ0 : 0 ≤ β0) (γ : G.Ω 1 → ℂ)
    (w : Torus d (N₀ * L ^ k) → Fin N → ℂ) (hγ : ∀ x ∈ D.sites, ‖zeroExt (G.Ω 1) γ x‖ ≤ Bγ)
    (hw : ∀ x ∈ D.sites, vn (w x) ≤ Bδ) :
    ‖(1 / 2 : ℂ) * (β0 : ℂ) * D.sitePair γ w w‖ ≤ 1 / 2 * β0 * (D.sites.card * (Bγ * (Bδ * Bδ))) := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ0]
  have e : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [e]
  have := norm_sitePair_le D γ w w hγ hw hw
  have h0 : 0 ≤ 1 / 2 * β0 := by positivity
  calc 1 / 2 * β0 * ‖D.sitePair γ w w‖ ≤ 1 / 2 * β0 * (D.sites.card * (Bγ * (Bδ * Bδ))) := by gcongr
    _ = _ := by ring

/-- The `ν`-part of the complex form of (b): `‖ν ⟨δφ, δφ⟩_X‖ ≤ |ν| #X B_δ²`. -/
theorem norm_massSelf_le (D : Region G) (ν : ℝ) (w : Torus d (N₀ * L ^ k) → Fin N → ℂ) {Bδ : ℝ}
    (hw : ∀ x ∈ D.sites, vn (w x) ≤ Bδ) :
    ‖(ν : ℂ) * D.massPair w w‖ ≤ |ν| * (D.sites.card * (Bδ * Bδ)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  exact norm_massPair_le D w w hw hw

/-- **Lemma III.6.4 (c), the surface term**: `|S_st| ≤ #st(X) B_w B_∂`. -/
theorem norm_starPair_le (D : Region G) (w f : Torus d (N₀ * L ^ k) → Fin N → ℂ) {Bw Bder : ℝ}
    (hw : ∀ b ∈ D.crossing, vn (fun i => (w b.1 i + w (b.1 + Pi.single b.2 1) i) / 2) ≤ Bw)
    (hf : ∀ b ∈ D.crossing, vn (fun i => D.outwardDeriv f b i) ≤ Bder) :
    ‖D.starPair w f‖ ≤ D.crossing.card * (Bw * Bder) := by
  unfold Region.starPair
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b ∈ D.crossing, ‖∑ i, ((w b.1 i + w (b.1 + Pi.single b.2 1) i) / 2) *
        D.outwardDeriv f b i‖ ≤ ∑ b ∈ D.crossing, Bw * Bder := by
        refine Finset.sum_le_sum fun b hb => (norm_dotC_le (fun i => (w b.1 i +
          w (b.1 + Pi.single b.2 1) i) / 2) (fun i => D.outwardDeriv f b i)).trans ?_
        exact mul_le_mul (hw b hb) (hf b hb) (vn_nonneg _) ((vn_nonneg _).trans (hw b hb))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]


variable {β0 : ℝ} (hprec : Precedes G G') (a : ℕ → ℝ) (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N))
  (h : Fin N → ℝ)

/-- **Lemma III.6.4 ((2.59)′, (2.60)′, surface and `ν`-terms)**, conditional on Lemma III.6.2 (2.41)
(`Lemma262`, cited) and on the layered bound (2.49′) for `δφ_{k₁,k} = φ_{k₁,k} - φ⁰_k` (the pointwise
bound `hδ`; landed as `deltaPhi_le_of_dataChange`).  With `X = X_win`, `Z_{k₁}` the core:

* (a) `|β_k A*_{0,k}(Z_{k₁}; φ⁰_k)| < ¼`;
* (b) `½ β_k |⟨δφ, α⁰ δφ⟩_{X_win}| < ¼`, and with `α⁰ + ν` in place of `α⁰` (complex domain);
* (c) `β_k |S_st| < ¼` and `β_k |ν⟨δφ, φ⁰ - h⟩_{X_win}| < ¼`;

each from the corresponding numerical condition (the form of the strengthened (Λ25)(a)-(c) for the
constants of the pointwise bounds): `hΛa`, `hΛb`, `hΛb'`, `hΛc`, `hΛν`.  The verification of these
conditions from the parameter chain (III.1.1), (III.1.2) (c), `ν_max` is the content of (Λ25) and is not
part of this theorem. -/
theorem remaining_terms (hβ0 : 0 ≤ β0) {ν : ℝ} (Du : BgData G N) {φu : G.Ω 1 × Fin N → ℂ}
    (D : Region G) (Zk1 : Region G')
    {Bgrad Bmass Balpha Bgrad' Bmass' Balpha' Bδ Bφ Bw Bder : ℝ}
    (hZ : Lemma262 G' a ψ0 h ν Zk1.sites Bgrad Bmass Balpha)
    (hD : Lemma262 G' a ψ0 h ν D.sites Bgrad' Bmass' Balpha')
    (hδ : ∀ x ∈ D.sites, vn (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h)) x) ≤ Bδ)
    (hφ : ∀ x ∈ D.sites, vn (fun i => svec G (hprec.restrictφ (phiZero G' a ψ0 h)) x i -
      (windowData G G' hprec a ψ0 h).h x i) ≤ Bφ)
    (hw : ∀ b ∈ D.crossing, vn (fun i =>
      (wExt (windowData G G' hprec a ψ0 h) Du (hprec.restrictφ (phiZero G' a ψ0 h)) φu b.1 i +
        wExt (windowData G G' hprec a ψ0 h) Du (hprec.restrictφ (phiZero G' a ψ0 h)) φu
          (b.1 + Pi.single b.2 1) i) / 2) ≤ Bw)
    (hder : ∀ b ∈ D.crossing, vn (fun i => D.outwardDeriv (barField G
      (windowData G G' hprec a ψ0 h).Ψ (hprec.restrictφ (phiZero G' a ψ0 h))) b i) ≤ Bder)
    (hΛa : β0 * (1 / 2 * (Bgrad ^ 2 * (d * Zk1.sites.card)) + 1 / 2 * (Zk1.sites.card * Bmass)) < 1 / 4)
    (hΛb : 1 / 2 * β0 * (D.sites.card * (Balpha' * (Bδ * Bδ))) < 1 / 4)
    (hΛb' : 1 / 2 * β0 * (D.sites.card * ((Balpha' + |ν|) * (Bδ * Bδ))) < 1 / 4)
    (hΛc : β0 * (D.crossing.card * (Bw * Bder)) < 1 / 4)
    (hΛν : β0 * (|ν| * (D.sites.card * (Bδ * Bφ))) < 1 / 4) :
    ‖(β0 : ℂ) * actionRegion0 Zk1 ν (psiZeroData G' ψ0 h) (phiZero G' a ψ0 h)‖ < 1 / 4 ∧
      ‖(1 / 2 : ℂ) * (β0 : ℂ) * D.sitePair (hprec.restrictα (alphaZero G' a ψ0 h))
        (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h)))
        (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h)))‖ < 1 / 4 ∧
      ‖(1 / 2 : ℂ) * (β0 : ℂ) * (D.sitePair (hprec.restrictα (alphaZero G' a ψ0 h))
        (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h)))
        (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h))) +
        (ν : ℂ) * D.massPair (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h)))
          (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h))))‖ < 1 / 4 ∧
      ‖(β0 : ℂ) * stTerm D (windowData G G' hprec a ψ0 h) Du
        (hprec.restrictφ (phiZero G' a ψ0 h)) φu‖ < 1 / 4 ∧
      ‖(β0 : ℂ) * nuTerm D ν (windowData G G' hprec a ψ0 h) (hprec.restrictφ (phiZero G' a ψ0 h))
        φu‖ < 1 / 4 := by
  have hβn : ‖(β0 : ℂ)‖ = β0 := by rw [Complex.norm_real, Real.norm_of_nonneg hβ0]
  have hαD : ∀ x ∈ D.sites, ‖zeroExt (G.Ω 1) (hprec.restrictα (alphaZero G' a ψ0 h)) x‖ ≤ Balpha' :=
    fun x hx => by
      rw [zeroExt_restrictα hprec _ (D.sub_Ω hx)]
      exact hD.alpha x hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [norm_mul, hβn]
    calc β0 * ‖actionRegion0 Zk1 ν (psiZeroData G' ψ0 h) (phiZero G' a ψ0 h)‖
        ≤ β0 * (1 / 2 * (Bgrad ^ 2 * (d * Zk1.sites.card)) + 1 / 2 * (Zk1.sites.card * Bmass)) := by
          gcongr; exact norm_actionRegion0_le a ψ0 h Zk1 hZ
      _ < 1 / 4 := hΛa
  · exact (norm_alphaTerm_le D hβ0 _ _ hαD hδ).trans_lt hΛb
  · have h1 := norm_alphaTerm_le D hβ0 (hprec.restrictα (alphaZero G' a ψ0 h)) _ hαD hδ
    have h2 := norm_massSelf_le D ν (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h))) hδ
    have e : (1 / 2 : ℂ) * (β0 : ℂ) * (D.sitePair (hprec.restrictα (alphaZero G' a ψ0 h))
        (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h)))
        (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h))) +
        (ν : ℂ) * D.massPair (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h)))
          (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h)))) =
        (1 / 2 : ℂ) * (β0 : ℂ) * D.sitePair (hprec.restrictα (alphaZero G' a ψ0 h))
          (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h)))
          (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h))) +
        (1 / 2 : ℂ) * (β0 : ℂ) * ((ν : ℂ) * D.massPair (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h)))
          (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h)))) := by ring
    rw [e]
    refine (norm_add_le _ _).trans_lt (lt_of_le_of_lt ?_ hΛb')
    have h3 : ‖(1 / 2 : ℂ) * (β0 : ℂ) * ((ν : ℂ) * D.massPair
        (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h)))
        (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h))))‖ ≤
        1 / 2 * β0 * (|ν| * (D.sites.card * (Bδ * Bδ))) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ0]
      have e2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
      rw [e2]
      have h0 : 0 ≤ 1 / 2 * β0 := by positivity
      gcongr
    nlinarith
  · rw [norm_mul, hβn]
    calc β0 * ‖stTerm D (windowData G G' hprec a ψ0 h) Du
          (hprec.restrictφ (phiZero G' a ψ0 h)) φu‖ ≤ β0 * (D.crossing.card * (Bw * Bder)) := by
          gcongr; exact norm_starPair_le D _ _ hw hder
      _ < 1 / 4 := hΛc
  · rw [norm_mul, hβn]
    have := norm_mul (ν : ℂ) (D.massPair (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h)))
      (fun x i => svec G (hprec.restrictφ (phiZero G' a ψ0 h)) x i -
        (windowData G G' hprec a ψ0 h).h x i))
    unfold nuTerm
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    calc β0 * (|ν| * ‖D.massPair (svec G (φu - hprec.restrictφ (phiZero G' a ψ0 h)))
        (fun x i => svec G (hprec.restrictφ (phiZero G' a ψ0 h)) x i -
          (windowData G G' hprec a ψ0 h).h x i)‖) ≤ β0 * (|ν| * (D.sites.card * (Bδ * Bφ))) := by
          gcongr; exact norm_massPair_le D _ _ hδ hφ
      _ < 1 / 4 := hΛν

end Remaining

end Balaban.LargeField.ActionConv
