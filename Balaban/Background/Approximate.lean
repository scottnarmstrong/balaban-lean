/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.ApproxReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lemma 5.3: the hard-spin approximate solution (LEMMA53-astra.md, §4)

Assembly.  For data `(Ψ + Ψ', h + h')` in the complex domain `Ψ̃^c(δ, ε)` and the corresponding real
data `(Ψ, h)`, `Balaban.Background.lemma53` states, with an absolute constant `lemma53Const d L`
depending only on `(d, L)` and for `δ ≤ approxDelta d L`:

* `φ₀ ⬝ φ₀ = 1` and `|φ₀ - Ψ| ≤ C δ` on `Ω₁ ∪ C`;
* `IsSmoothField G (C δ) φ₀`;
* `ℓ(x)² |f₀(x)| ≤ C δ` on `Ω₁` for the residual `f₀ = S(Ψ, h̃) - H_D(0) φ₀` (`α₀ = 0`);
* the same for the real data, whose field and residual are real;
* `|φ₀^c - φ₀^r| ≤ ε + C δ` on `Ω₁ ∪ C`;
* for the real data, `√ν |φ₀ - h| ≤ C δ / ℓ(x)` on `Ω₁`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Assembly

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν δ ε : ℝ}

/-- Real data are complex data with zero perturbation. -/
def DataWit.ofReal (hδ : 0 < δ) (hε : 0 < ε) {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ}
    {h₀ : Fin N → ℝ} (hP : InPsiTilde G ν δ Ψ h₀) (D : BgData G N)
    (hΨ : ∀ x ∈ dataSites G, ∀ i, D.Ψ x i = (Ψ x i : ℂ))
    (hh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (h₀ i : ℂ)) : DataWit G ν δ ε D where
  Ψ := Ψ
  h₀ := h₀
  Ψ' := fun _ _ => 0
  h' := fun _ _ => 0
  P :=
    { toInPsiTilde := hP
      eps_pos := hε
      layerConst' := fun n hn1 hnk x hx x' hx' => rfl
      hLayerConst' := fun n hn1 hnk x hx x' hx' => rfl
      c1 := fun x x' _ => by
        have : vn ((fun _ => (0 : ℂ)) - (fun _ => (0 : ℂ)) : Fin N → ℂ) = 0 := by
          rw [sub_self]; exact vn_zero
        rw [this]; exact hδ
      c2a := fun x _ => by
        have : vn (fun _ => (0 : ℂ) : Fin N → ℂ) = 0 := vn_zero
        rw [this]; linarith
      c2b := fun x _ => by simpa using hδ
      c3a := fun x _ => by
        have : vn (fun _ => (0 : ℂ) : Fin N → ℂ) = 0 := vn_zero
        rw [this, mul_zero]; positivity
      c3b := fun x _ => by simpa using (by positivity : 0 < δ ^ 2) }
  hΨ := fun x hx i => by simpa using hΨ x hx i
  hh := fun x hx i => by simpa using hh x hx i


variable {D : BgData G N}

/-- **(A4)**: the approximate field is within `(B₇ + 500) δ` of the data. -/
theorem phi0_data_close (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D)
    (hs : cA2 d L * δ ≤ 1 / 100) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ dataSites G) :
    cNorm (approxField G a ν D.Ψ D.h x - D.Ψ x) ≤ (cB7 d L + 500) * δ := by
  obtain ⟨-, c1⟩ := phi0_close_locSol S W hs hx
  obtain ⟨-, c2, -, -⟩ := locSol_facts S W hx
  have e : approxField G a ν D.Ψ D.h x - D.Ψ x =
      (approxField G a ν D.Ψ D.h x - locSol G a ν D.Ψ D.h x) +
        (locSol G a ν D.Ψ D.h x - D.Ψ x) := by
    funext i; simp [Pi.sub_apply, Pi.add_apply]
  rw [e]
  have := cNorm_add_le (approxField G a ν D.Ψ D.h x - locSol G a ν D.Ψ D.h x)
    (locSol G a ν D.Ψ D.h x - D.Ψ x)
  linarith

/-- **(A6)**: comparison of the fields of the complex and of the real data. -/
theorem phi0_compare (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D)
    (Dr : BgData G N) (hΨr : ∀ x ∈ dataSites G, ∀ i, Dr.Ψ x i = (W.Ψ x i : ℂ))
    (hhr : ∀ x ∈ G.Ω 1, ∀ i, Dr.h x i = (W.h₀ i : ℂ))
    (hs : cA2 d L * δ ≤ 1 / 100) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ dataSites G) :
    cNorm (approxField G a ν D.Ψ D.h x - approxField G a ν Dr.Ψ Dr.h x) ≤
      ε + (2 * (cB7 d L + 500) + 1) * δ := by
  have Wr := DataWit.ofReal S.hδ0 (S.hδ0.trans_le S.hδε) W.P.toInPsiTilde Dr hΨr hhr
  have c1 := phi0_data_close S W hs hx
  have c2 := phi0_data_close S Wr hs hx
  have c3 : cNorm (D.Ψ x - Dr.Ψ x) ≤ ε + δ := by
    have e : D.Ψ x - Dr.Ψ x = W.Ψ' x := by
      funext i; simp [Pi.sub_apply, W.hΨ x hx i, hΨr x hx i]
    rw [e]; exact (W.P.c2a x hx).le
  have e : approxField G a ν D.Ψ D.h x - approxField G a ν Dr.Ψ Dr.h x =
      (approxField G a ν D.Ψ D.h x - D.Ψ x) + (D.Ψ x - Dr.Ψ x) +
        (Dr.Ψ x - approxField G a ν Dr.Ψ Dr.h x) := by
    funext i; simp [Pi.sub_apply, Pi.add_apply]
  rw [e]
  have t1 := cNorm_add_le (approxField G a ν D.Ψ D.h x - D.Ψ x) (D.Ψ x - Dr.Ψ x)
  have t2 := cNorm_add_le (approxField G a ν D.Ψ D.h x - D.Ψ x + (D.Ψ x - Dr.Ψ x))
    (Dr.Ψ x - approxField G a ν Dr.Ψ Dr.h x)
  have e2 : cNorm (Dr.Ψ x - approxField G a ν Dr.Ψ Dr.h x) =
      cNorm (approxField G a ν Dr.Ψ Dr.h x - Dr.Ψ x) := vn_sub_comm _ _
  linarith

/-- The mass term for real data: `√ν |φ₀ - h| ≤ (B₇ + 503) δ / ℓ(x)`. -/
theorem phi0_mass_real (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D)
    (Dr : BgData G N) (hΨr : ∀ x ∈ dataSites G, ∀ i, Dr.Ψ x i = (W.Ψ x i : ℂ))
    (hhr : ∀ x ∈ G.Ω 1, ∀ i, Dr.h x i = (W.h₀ i : ℂ))
    (hs : cA2 d L * δ ≤ 1 / 100) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    Real.sqrt ν * cNorm (approxField G a ν Dr.Ψ Dr.h x - cplx W.h₀) ≤
      (cB7 d L + 503) * δ / G.spacing x := by
  have Wr := DataWit.ofReal S.hδ0 (S.hδ0.trans_le S.hδε) W.P.toInPsiTilde Dr hΨr hhr
  have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
  obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hx
  obtain ⟨hB0, hB1⟩ := blockMass_le S hx
  have hL3 := S.hL
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hℓ : (0 : ℝ) < G.spacing x := by unfold GeneratingSet.spacing; positivity
  have hBk : blockMass G ν x ≤ ν * ((L : ℝ) ^ k) ^ 2 := by
    have hL' : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    have := pow_le_pow_right₀ hL' hnk
    have h2 : ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ ((L : ℝ) ^ k) ^ 2 := by
      nlinarith [pow_nonneg hL0.le (G.layerIndex x)]
    exact mul_le_mul_of_nonneg_left h2 S.hν0
  obtain ⟨-, c2, -, -⟩ := locSol_facts S Wr hxd
  have hcplx : Dr.Ψ x = cplx (W.Ψ x) := funext fun i => by simp [cplx, hΨr x hxd i]
  have hmass := real_mass_bound (ψ := W.Ψ x) (h := W.h₀) (δ := δ) (B := blockMass G ν x)
    S.hδ0.le (by linarith [S.hδε, S.hε]) hB0 hB1 (W.P.r2 x hxd) (W.P.r3 x hxd)
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hBk (abs_nonneg _)) W.P.r4)
    (φ := locSol G a ν Dr.Ψ Dr.h x) (by rw [hcplx] at c2; exact c2)
  obtain ⟨-, c1⟩ := phi0_close_locSol S Wr hs hxd
  have hsB : Real.sqrt (blockMass G ν x) = Real.sqrt ν * G.spacing x := by
    unfold blockMass GeneratingSet.spacing
    rw [Real.sqrt_mul S.hν0, Real.sqrt_sq (by positivity)]
  have hsB1 : Real.sqrt (blockMass G ν x) ≤ 1 := by
    calc Real.sqrt (blockMass G ν x) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hB1
      _ = 1 := Real.sqrt_one
  have e : approxField G a ν Dr.Ψ Dr.h x - cplx W.h₀ =
      (approxField G a ν Dr.Ψ Dr.h x - locSol G a ν Dr.Ψ Dr.h x) +
        (locSol G a ν Dr.Ψ Dr.h x - cplx W.h₀) := by
    funext i; simp [Pi.sub_apply, Pi.add_apply]
  rw [e]
  have t := cNorm_add_le (approxField G a ν Dr.Ψ Dr.h x - locSol G a ν Dr.Ψ Dr.h x)
    (locSol G a ν Dr.Ψ Dr.h x - cplx W.h₀)
  have hs0 : 0 ≤ Real.sqrt ν := Real.sqrt_nonneg _
  have h1 : Real.sqrt ν * cNorm (approxField G a ν Dr.Ψ Dr.h x - locSol G a ν Dr.Ψ Dr.h x) ≤
      cB7 d L * δ / G.spacing x := by
    rw [le_div_iff₀ hℓ]
    have : Real.sqrt ν * G.spacing x ≤ 1 := by rw [← hsB]; exact hsB1
    calc Real.sqrt ν * cNorm (approxField G a ν Dr.Ψ Dr.h x - locSol G a ν Dr.Ψ Dr.h x) *
          G.spacing x = (Real.sqrt ν * G.spacing x) *
          cNorm (approxField G a ν Dr.Ψ Dr.h x - locSol G a ν Dr.Ψ Dr.h x) := by ring
      _ ≤ 1 * (cB7 d L * δ) := mul_le_mul this c1 (cNorm_nonneg _) zero_le_one
      _ = cB7 d L * δ := one_mul _
  have h2 : Real.sqrt ν * cNorm (locSol G a ν Dr.Ψ Dr.h x - cplx W.h₀) ≤
      503 * δ / G.spacing x := by
    rw [le_div_iff₀ hℓ]
    rw [hsB] at hmass
    calc Real.sqrt ν * cNorm (locSol G a ν Dr.Ψ Dr.h x - cplx W.h₀) * G.spacing x =
        Real.sqrt ν * G.spacing x * cNorm (locSol G a ν Dr.Ψ Dr.h x - cplx W.h₀) := by ring
      _ ≤ 503 * δ := hmass
  have := mul_le_mul_of_nonneg_left t hs0
  have e3 : (cB7 d L + 503) * δ / G.spacing x =
      cB7 d L * δ / G.spacing x + 503 * δ / G.spacing x := by ring
  rw [e3]
  nlinarith


theorem isSmoothField_mono {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {δ₁ δ₂ : ℝ}
    (h : IsSmoothField G δ₁ φ) (h12 : δ₁ ≤ δ₂) : IsSmoothField G δ₂ φ := by
  have hp : ∀ x, 0 < G.spacing x := fun x => by
    unfold GeneratingSet.spacing; have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  refine ⟨fun x hx μ => ?_, fun x hx => ?_⟩
  · obtain ⟨h1, h2⟩ := h.grad x hx μ
    exact ⟨h1.trans (div_le_div_of_nonneg_right h12 (hp x).le),
      h2.trans (div_le_div_of_nonneg_right h12 (hp x).le)⟩
  · exact (h.lap x hx).trans (div_le_div_of_nonneg_right h12 (by have := hp x; positivity))

/-- The constant of Lemma 5.3, a function of `(d, L)` only. -/
noncomputable def lemma53Const (d L : ℕ) : ℝ :=
  max (max (max (cSm d L) (cB7 d L + 500)) (max (cRes d L) (cB7 d L + 503)))
    (2 * (cB7 d L + 500) + 1)

/-- The smallness threshold `δ**` of Lemma 5.3, a function of `(d, L)` only. -/
noncomputable def approxDelta (d L : ℕ) : ℝ := min (1 / 1024) (1 / (100 * cA2 d L))

theorem approxDelta_pos (d L : ℕ) : 0 < approxDelta d L := by
  unfold approxDelta
  have := cA1_pos d L
  have : 0 < cA2 d L := by unfold cA2; linarith
  exact lt_min (by norm_num) (by positivity)

theorem approxDelta_le (d L : ℕ) {δ : ℝ} (hδ : δ ≤ approxDelta d L) :
    δ ≤ 1 / 1024 ∧ cA2 d L * δ ≤ 1 / 100 := by
  have hA : 0 < cA2 d L := by have := cA1_pos d L; unfold cA2; linarith
  refine ⟨hδ.trans (min_le_left _ _), ?_⟩
  have h2 : δ ≤ 1 / (100 * cA2 d L) := hδ.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at h2
  nlinarith

theorem cB7_le_const (d L : ℕ) : cB7 d L + 500 ≤ lemma53Const d L := by
  unfold lemma53Const
  exact le_max_of_le_left (le_max_of_le_left (le_max_right _ _))

/-- **Lemma 5.3 (the hard-spin approximate solution).**  Let `D` be complex data in `Ψ̃^c(δ, ε)`
(decomposition `W`) and `Dr` the corresponding real data `(Ψ, h)`; `φ₀ = approxField`.  For
`δ ≤ approxDelta d L` and `C = lemma53Const d L` (depending only on `(d, L)`; in particular not on
`k, N₀, ϱ, N, a, ν` or the generating set): -/
theorem lemma53 (S : ApproxSetting d L k ϱ a ν δ ε) (hδ : δ ≤ approxDelta d L)
    (D Dr : BgData G N) (W : DataWit G ν δ ε D)
    (hΨr : ∀ x ∈ dataSites G, ∀ i, Dr.Ψ x i = (W.Ψ x i : ℂ))
    (hhr : ∀ x ∈ G.Ω 1, ∀ i, Dr.h x i = (W.h₀ i : ℂ)) :
    -- the constraint and the closeness to the data, for the complex data
    (∀ x ∈ dataSites G, approxField G a ν D.Ψ D.h x ⬝ᵥ approxField G a ν D.Ψ D.h x = 1 ∧
      vn (approxField G a ν D.Ψ D.h x - D.Ψ x) ≤ lemma53Const d L * δ) ∧
    -- smoothness
    IsSmoothField G (lemma53Const d L * δ) (approxField G a ν D.Ψ D.h) ∧
    -- the residual `f₀ = S(Ψ, h̃) - H_D(0) φ₀`
    (∀ x : G.Ω 1, G.spacing x.1 ^ 2 *
      vn (fun i => residual G a ν D (approxField G a ν D.Ψ D.h) (x, i)) ≤
        lemma53Const d L * δ) ∧
    -- the same for the real data
    (∀ x ∈ dataSites G, approxField G a ν Dr.Ψ Dr.h x ⬝ᵥ approxField G a ν Dr.Ψ Dr.h x = 1 ∧
      vn (approxField G a ν Dr.Ψ Dr.h x - Dr.Ψ x) ≤ lemma53Const d L * δ) ∧
    IsSmoothField G (lemma53Const d L * δ) (approxField G a ν Dr.Ψ Dr.h) ∧
    (∀ x : G.Ω 1, G.spacing x.1 ^ 2 *
      vn (fun i => residual G a ν Dr (approxField G a ν Dr.Ψ Dr.h) (x, i)) ≤
        lemma53Const d L * δ) ∧
    -- complex versus real
    (∀ x ∈ dataSites G, vn (approxField G a ν D.Ψ D.h x - approxField G a ν Dr.Ψ Dr.h x) ≤
      ε + lemma53Const d L * δ) ∧
    -- real data give real fields and residuals
    (∀ x ∈ dataSites G, ∀ i, (approxField G a ν Dr.Ψ Dr.h x i).im = 0) ∧
    (∀ (x : G.Ω 1) (i : Fin N),
      (residual G a ν Dr (approxField G a ν Dr.Ψ Dr.h) (x, i)).im = 0) ∧
    -- the mass term
    (∀ x ∈ G.Ω 1, Real.sqrt ν * vn (approxField G a ν Dr.Ψ Dr.h x - cplx W.h₀) ≤
      lemma53Const d L * δ / G.spacing x) := by
  obtain ⟨hδ1, hs⟩ := approxDelta_le d L hδ
  have hC0 : (0 : ℝ) ≤ lemma53Const d L := by
    have := cB7_pos d L
    exact (by positivity : (0 : ℝ) ≤ cB7 d L + 500).trans (cB7_le_const d L)
  have Wr := DataWit.ofReal S.hδ0 (S.hδ0.trans_le S.hδε) W.P.toInPsiTilde Dr hΨr hhr
  have hmax1 : cSm d L ≤ lemma53Const d L := by
    unfold lemma53Const
    exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_refl _)))
  have hmax3 : cRes d L ≤ lemma53Const d L := by
    unfold lemma53Const
    exact le_max_of_le_left (le_max_of_le_right (le_max_left _ _))
  have hmax4 : cB7 d L + 503 ≤ lemma53Const d L := by
    unfold lemma53Const
    exact le_max_of_le_left (le_max_of_le_right (le_max_right _ _))
  have hmax5 : 2 * (cB7 d L + 500) + 1 ≤ lemma53Const d L := by
    unfold lemma53Const; exact le_max_right _ _
  have hmaxd := cB7_le_const d L
  have gen : ∀ (D' : BgData G N) (W' : DataWit G ν δ ε D'),
      (∀ x ∈ dataSites G, approxField G a ν D'.Ψ D'.h x ⬝ᵥ approxField G a ν D'.Ψ D'.h x = 1 ∧
        vn (approxField G a ν D'.Ψ D'.h x - D'.Ψ x) ≤ lemma53Const d L * δ) ∧
      IsSmoothField G (lemma53Const d L * δ) (approxField G a ν D'.Ψ D'.h) ∧
      (∀ x : G.Ω 1, G.spacing x.1 ^ 2 *
        vn (fun i => residual G a ν D' (approxField G a ν D'.Ψ D'.h) (x, i)) ≤
          lemma53Const d L * δ) := by
    intro D' W'
    refine ⟨fun x hx => ⟨(phi0_close_locSol S W' hs hx).1, ?_⟩, ?_, fun x => ?_⟩
    · exact (phi0_data_close S W' hs hx).trans (mul_le_mul_of_nonneg_right hmaxd S.hδ0.le)
    · exact isSmoothField_mono (phi0_isSmoothField S W' hs (by linarith)) 
        (mul_le_mul_of_nonneg_right hmax1 S.hδ0.le)
    · exact (residual_bound S W' hs (by linarith) x).trans
        (mul_le_mul_of_nonneg_right hmax3 S.hδ0.le)
  obtain ⟨g1, g2, g3⟩ := gen D W
  obtain ⟨r1, r2, r3⟩ := gen Dr Wr
  refine ⟨g1, g2, g3, r1, r2, r3, fun x hx => ?_, ?_, ?_, ?_⟩
  · refine (phi0_compare S W Dr hΨr hhr hs hx).trans ?_
    have := mul_le_mul_of_nonneg_right hmax5 S.hδ0.le
    linarith
  · have hrΨ : ∀ y ∈ dataSites G, IsRealVec (Dr.Ψ y) := fun y hy => by
      have : Dr.Ψ y = cplx (W.Ψ y) := funext fun i => by simp [cplx, hΨr y hy i]
      rw [this]; exact isRealVec_cplx _
    have hrh : ∀ y ∈ G.Ω 1, IsRealVec (Dr.h y) := fun y hy => by
      have : Dr.h y = cplx W.h₀ := funext fun i => by simp [cplx, hhr y hy i]
      rw [this]; exact isRealVec_cplx _
    exact fun x hx i => isRealVec_approxField hrΨ hrh hx i
  · have hrΨ : ∀ y ∈ dataSites G, IsRealVec (Dr.Ψ y) := fun y hy => by
      have : Dr.Ψ y = cplx (W.Ψ y) := funext fun i => by simp [cplx, hΨr y hy i]
      rw [this]; exact isRealVec_cplx _
    have hrh : ∀ y ∈ G.Ω 1, IsRealVec (Dr.h y) := fun y hy => by
      have : Dr.h y = cplx W.h₀ := funext fun i => by simp [cplx, hhr y hy i]
      rw [this]; exact isRealVec_cplx _
    exact fun x i => residual_real Dr _ (fun y hy => isRealVec_approxField hrΨ hrh hy) hrΨ hrh x i
  · intro x hx
    have hℓ : (0 : ℝ) < G.spacing x := by
      unfold GeneratingSet.spacing
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    refine (phi0_mass_real S W Dr hΨr hhr hs hx).trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hmax4 S.hδ0.le) hℓ.le

end Assembly

end Balaban.Background
