module

public import Balaban.LargeField.Characteristic.Reg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The real domain `𝒟_ℝ` as a condition on real fields, and `𝒟_ℝ ⊂ 𝒟`

* `bgC1_pos_of`: the radius `c₁` of Theorem 5.2 is positive;
* `InPsiTilde.mono`, `InPsiTilde.congr`: the conditions (R1)-(R4) are monotone in `δ` and read
  the field only on the data sites;
* `inUnionDomainR_iff`: for real data with `h̃ ≡ h` on a nonempty `Ω₁`, `D ∈ 𝒟_ℝ(G)` iff
  `(Re Ψ, h) ∈ Ψ̃(G; c₁)` (the union over `δ ≤ c₁` is attained at `δ = c₁`);
* `inUnionDomainC_of_R`: under `BgHyp`, `𝒟_ℝ(G) ⊂ 𝒟(G)` (take `Ψ' = 0 = h'`, `δ = ε`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

set_option linter.unusedSectionVars false

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem bgC1_pos_of (hd : 0 < d) : 0 < bgC1 d L N := by
  have h1 := approxDelta_pos d L
  have h2 := deltaStar_pos (d := d) (L := L) (N := N) hd
  have h3 := lemma53Const_pos d L
  have h4 := bgC0_pos d L N hd
  have h5 := bgK1_pos d L N
  unfold bgC1
  refine lt_min (lt_min h1 ?_) (lt_min ?_ ?_) <;> positivity

section Psi

variable {G : GeneratingSet d L N₀ q ϱ} {μ δ δ' : ℝ} {Ψ Ψ' : Torus d (N₀ * L ^ q) → Fin N → ℝ}
  {h : Fin N → ℝ}

theorem _root_.Balaban.Background.InPsiTilde.mono (hP : InPsiTilde G μ δ Ψ h) (hδ0 : 0 ≤ δ) (hδ : δ ≤ δ') :
    InPsiTilde G μ δ' Ψ h where
  layerConst := hP.layerConst
  r1 := fun x x' hx => (hP.r1 x x' hx).trans_le hδ
  r2 := fun x hx => (hP.r2 x hx).trans_le hδ
  r3 := fun x hx => (hP.r3 x hx).trans_le (by nlinarith)
  r4 := (hP.r4).trans_le (by nlinarith)

theorem _root_.Balaban.Background.InPsiTilde.congr (hP : InPsiTilde G μ δ Ψ h)
    (hΨ : ∀ x ∈ dataSites G, Ψ' x = Ψ x) : InPsiTilde G μ δ Ψ' h where
  layerConst := by
    intro n hn1 hnk x hx x' hx'
    have hx1 : x ∈ G.Ω 1 := G.layer_subset hn1 hnk hx
    have hx'l : x' ∈ G.layer n := (G.mem_layer_iff hn1 hnk (G.mem_blk.1 hx')).2 hx
    have hx'1 : x' ∈ G.Ω 1 := G.layer_subset hn1 hnk hx'l
    rw [hΨ x ((mem_dataSites G).2 (Or.inl hx1)), hΨ x' ((mem_dataSites G).2 (Or.inl hx'1))]
    exact hP.layerConst n hn1 hnk x hx x' hx'
  r1 := fun x x' hx => by
    rw [hΨ x hx.1, hΨ x' hx.2.1]; exact hP.r1 x x' hx
  r2 := fun x hx => by rw [hΨ x hx]; exact hP.r2 x hx
  r3 := fun x hx => by rw [hΨ x hx]; exact hP.r3 x hx
  r4 := hP.r4

end Psi

section Union

variable {G : GeneratingSet d L N₀ q ϱ} {μ c₁ : ℝ} {D : BgData G N}

/-- For real data with `h̃ ≡ h` on a nonempty `Ω₁`, `D ∈ 𝒟_ℝ(G)` iff `(Re Ψ, h) ∈ Ψ̃(G; c₁)`. -/
theorem inUnionDomainR_iff (hc : 0 < c₁) {h : Fin N → ℝ} (hne : (G.Ω 1).Nonempty)
    (hΨ : ∀ x i, (D.Ψ x i).im = 0) (hh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (h i : ℂ)) :
    InUnionDomainR G c₁ μ D ↔ InPsiTilde G μ c₁ (fun x i => (D.Ψ x i).re) h := by
  constructor
  · rintro ⟨δ, hδ0, hδc, Ψ', h', hP, hΨ', hh'⟩
    obtain ⟨x₀, hx₀⟩ := hne
    have hhh : h' = h := by
      funext i
      have := (hh' x₀ hx₀ i).symm.trans (hh x₀ hx₀ i)
      exact_mod_cast this
    subst hhh
    refine (hP.congr (Ψ := Ψ') (Ψ' := fun x i => (D.Ψ x i).re) fun x hx => ?_).mono hδ0.le hδc
    funext i
    have := hΨ' x hx i
    rw [this]; simp
  · intro hP
    refine ⟨c₁, hc, le_rfl, fun x i => (D.Ψ x i).re, h, hP, fun x _ i => ?_, hh⟩
    exact (Complex.ext (by simp) (by simp [hΨ x i])).symm

/-- On an empty `Ω₁` the domain `𝒟_ℝ(G)` does not depend on the data. -/
theorem inUnionDomainR_of_empty (hne : G.Ω 1 = ∅) (D' : BgData G N) :
    InUnionDomainR G c₁ μ D ↔ InUnionDomainR G c₁ μ D' := by
  have hds : dataSites G = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    rcases (mem_dataSites G).1 hx with h | h
    · simp [hne] at h
    · obtain ⟨-, x', hx', -⟩ := (mem_collar G).1 h
      simp [hne] at hx'
  have key : ∀ E : BgData G N, InUnionDomainR G c₁ μ E ↔ ∃ δ : ℝ, 0 < δ ∧ δ ≤ c₁ ∧
      ∃ (Ψ : Torus d (N₀ * L ^ q) → Fin N → ℝ) (h : Fin N → ℝ), InPsiTilde G μ δ Ψ h := by
    intro E
    constructor
    · rintro ⟨δ, h0, hc, Ψ, h, hP, -, -⟩
      exact ⟨δ, h0, hc, Ψ, h, hP⟩
    · rintro ⟨δ, h0, hc, Ψ, h, hP⟩
      refine ⟨δ, h0, hc, Ψ, h, hP, fun x hx => ?_, fun x hx => ?_⟩
      · simp [hds] at hx
      · simp [hne] at hx
  rw [key D, key D']

/-- **`𝒟_ℝ(G) ⊂ 𝒟(G)`** under the standing hypotheses (`ν L^{2q} ≤ 1`, `d ≥ 3`): real data of
the real domain lie in the open complex union domain (take `Ψ' = 0 = h'`, `δ = ε`). -/
theorem inUnionDomainC_of_R {a : ℕ → ℝ} (H : BgHyp d L q ϱ a μ)
    (hD : InUnionDomainR G (bgC1 d L N) μ D) :
    InUnionDomainC G (bgC0 d L N) (bgC1 d L N) μ D := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨δ, hδ0, hδc, Ψ, h, hP, hΨ, hh⟩ := hD
  refine ⟨δ, δ, hδ0, le_rfl, hδc.trans (bgC1_le_bgC0 d L N hd0), hδc, ?_, ?_⟩
  · have := H.massLe
    nlinarith [sq_nonneg δ]
  · refine ⟨Ψ, h, 0, 0, ⟨hP, hδ0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro n hn1 hnk x hx x' hx'; rfl
    · intro n hn1 hnk x hx x' hx'; rfl
    · intro x x' hx; simp [vn, hδ0]
    · intro x hx; simp [vn, hδ0]
    · intro x hx; simp [hδ0]
    · intro x hx
      simp only [vn, Pi.zero_apply]
      have : 0 < δ ^ 2 / δ := by positivity
      simpa using this
    · intro x hx; simp [hδ0]
    · intro x hx i
      simp [hΨ x hx i]
    · intro x hx i
      simp [hh x hx i]
