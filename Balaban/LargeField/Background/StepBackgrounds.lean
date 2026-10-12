module

public import Balaban.LargeField.Background.Factorization
public import Balaban.LargeField.Background.Lift
public import Balaban.LargeField.Background.StepGenSetsFlow
import Mathlib.Tactic.Linarith

/-!
# The backgrounds used by Def-7 (Part II, Definition II.2.7)

All backgrounds are instances of Def-5 (`bgFieldC c₀ G a μ D`, the unique small solution of (EL)
with `|α|₂ < c₀`, `c₀` the constant of BG Theorem 5.2) on the generating sets of Definition II.2.4
with the lifted data of Definition II.2.1:

* `bgCube` (i): `φ_k(□; ψ_k) = bg(G_k(□); lift_k ψ_k)`;
* `bgCubeMixed` (ii): `φ'_{k+1}(□'; ψ_k, θ) = bg(G_{k+1}(□'); lift_{k,k+1}(ψ_k, θ))`;
* `bgSF` and `psiSF` (iii): `φ_k = bg(𝔹_k(W_k); lift_k ψ_k)` and
  `ψ_k^{(j)} = composeField (𝔹_j(W_k), 𝔹_k(W_k), a; φ_k, lift_k ψ_k)`;
* `bgLocPiece`, `bgLocUnion` (iv): `φ^loc_{k+1}`, on each piece
  `bg(G^{Z'}_{k+1}; lift_{k,k+1}(ψ_k, ψ_{k+1}))`; `bgLocUnion_eq_piece` is Lemma II.2.6.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

set_option linter.unusedSectionVars false

/-! ### Extensionality of the data -/

theorem BgData.ext' {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    {G : GeneratingSet d L N₀ k ϱ} {D D' : BgData G N} (h1 : D.Ψ = D'.Ψ) (h2 : D.h = D'.h) :
    D = D' := by
  cases D; cases D'; simp_all

section PieceData

variable {ι : Type*} {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {Gs : ι → GeneratingSet d L N₀ k ϱ'} (hD : PieceDecomp G Gs)

include hD

theorem PieceDecomp.dataSites_subset (i : ι) : dataSites (Gs i) ⊆ dataSites G := by
  intro x hx
  rcases (mem_dataSites _).1 hx with h | h
  · exact (mem_dataSites _).2 (Or.inl (hD.mem_of_mem h))
  · obtain ⟨hx1, x'', hx'', hadj⟩ := (mem_collar _).1 h
    exact (mem_dataSites _).2 (Or.inr ((hD.mem_collar_iff hx'' hadj).2 h))

theorem PieceDecomp.restrict_eq (i : ι) (D : BgData G N) (D' : BgData (Gs i) N)
    (hΨ : ∀ x ∈ dataSites (Gs i), D'.Ψ x = D.Ψ x) (hh : ∀ x ∈ (Gs i).Ω 1, D'.h x = D.h x) :
    hD.restrict i D = D' := by
  refine BgData.ext' (funext fun x => ?_) (funext fun x => ?_)
  · by_cases hx : x ∈ dataSites (Gs i)
    · rw [hD.restrict_Ψ i D hx, hΨ x hx]
    · rw [(hD.restrict i D).Ψ_zero x hx, D'.Ψ_zero x hx]
  · by_cases hx : x ∈ (Gs i).Ω 1
    · rw [hD.restrict_h i D hx, hh x hx]
    · rw [(hD.restrict i D).h_zero x hx, D'.h_zero x hx]

end PieceData

/-! ### (i)-(iii): cubes and the small-field backgrounds -/

section Cubes

variable {d M1 N₁ L q N c n : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] (a : ℕ → ℝ) (μ c₀ : ℝ)

/-- **Definition II.2.7 (i)**: `φ_k(□; ψ_k) = bg(G_k(□); lift_k ψ_k)` (`q = k`), the background
of the cube `□ = a0 ∈ 𝕋_k` (mass `μ = μ_k`, weights `a`). -/
noncomputable def bgCube (a0 : Torus d n) (ψ : Torus d (M1 * N₁ * L ^ (q - q)) → Fin N → ℂ)
    (h : Fin N → ℂ) :
    (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n a0).Ω 1 × Fin N → ℂ :=
  bgFieldC (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n a0) a μ c₀
    (liftSingle (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n a0) ψ h)

/-- **Definition II.2.7 (ii)**: `φ'_{k+1}(□'; ψ_k, θ) = bg(G_{k+1}(□'); lift_{k,k+1}(ψ_k, θ))`,
the background of the cube `□' = a0 ∈ 𝕋_{k+1}` (here `q = k + 1`; `Om` is the fine set
`Ω_{k+1}`). -/
noncomputable def bgCubeMixed {k : ℕ} (hm : N₁ * L ^ (k + 1 - (k + 1)) = c * n) (a0 : Torus d n)
    (Om : Finset (Torus d (M1 * N₁ * L ^ (k + 1))))
    (hOm : IsBlockUnion L (M1 * N₁) (k + 1) (k + 1) Om)
    (ψ : Torus d (M1 * N₁ * L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ : Torus d (M1 * N₁ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h : Fin N → ℂ) :
    (genCubeMixed hm a0 Om hOm).Ω 1 × Fin N → ℂ :=
  bgFieldC (genCubeMixed hm a0 Om hOm) a μ c₀
    (liftMixed (genCubeMixed hm a0 Om hOm) hOm (genCubeMixed_top_subset hm a0 Om hOm) ψ ϑ h)

/-- **Definition II.2.7 (iii)**: the small-field background `φ_k = bg(𝔹_k(W_k); lift_k ψ_k)`,
`W` a set of `π_q`-cubes. -/
noncomputable def bgSF (W : Set (Torus d n)) (ψ : Torus d (M1 * N₁ * L ^ (q - q)) → Fin N → ℂ)
    (h : Fin N → ℂ) :
    (genSF (M1 := M1) (N₁ := N₁) (L := L) (c := c) (n := n) (le_refl q) W).Ω 1 × Fin N → ℂ :=
  bgFieldC (genSF (M1 := M1) (N₁ := N₁) (L := L) (c := c) (n := n) (le_refl q) W) a μ c₀
    (liftSingle (genSF (M1 := M1) (N₁ := N₁) (L := L) (c := c) (n := n) (le_refl q) W) ψ h)

/-- **Definition II.2.7 (iii)**: `ψ_k^{(j)} = composeField(𝔹_j(W_k), 𝔹_k(W_k), a; φ_k, lift_k ψ_k)`
for `j ≤ k` (P5 (1.4); BG (6.2)). -/
noncomputable def psiSF {j : ℕ} (hj : j ≤ q) (W : Set (Torus d n))
    (ψ : Torus d (M1 * N₁ * L ^ (q - q)) → Fin N → ℂ) (h : Fin N → ℂ) :
    Torus d (M1 * N₁ * L ^ q) → Fin N → ℂ :=
  composeField (genSF (M1 := M1) (N₁ := N₁) (L := L) (c := c) (n := n) hj W)
    (genSF (M1 := M1) (N₁ := N₁) (L := L) (c := c) (n := n) (le_refl q) W) a
    (bgSF a μ c₀ W ψ h)
    (liftSingle (genSF (M1 := M1) (N₁ := N₁) (L := L) (c := c) (n := n) (le_refl q) W) ψ h).Ψ

end Cubes

/-! ### (iv): the local backgrounds of the components -/

section Flow

variable {d M1 c n1 L k n0 N : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]
  {Rprev Rk : ℝ} {ω : ℕ} {Zp : Set (Torus d n1)} (st : RegionStep d L n0 n1 Rprev Rk)
  (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L) (hρ : 3 * L ≤ ⌊Rprev⌋₊)
  (hω : 2 * ⌊Rk⌋₊ + L + 11 ≤ ω) (hZ : st.Omegaᶜ ⊆ Zp) (a : ℕ → ℝ) (μ c₀ : ℝ)

variable (M1 c n1 L k) in
/-- **Definition II.2.4 (v)**: `𝔹^loc_{k+1}(∂Ω_{k+1}) = ⋃_{Z'} G^{Z'}_{k+1}` (layerwise union over
the components of `Zp = Z^pre_{k+1}`). -/
noncomputable def genBoundaryUnion (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hω : 2 * ⌊Rk⌋₊ + L + 11 ≤ ω) (hZ : st.Omegaᶜ ⊆ Zp) :
    GeneratingSet d L (M1 * (c * n1)) (k + 1) (minSep L M1) :=
  unionGenSet (fun Z : (comps ω (finOf Zp) : Finset (Finset (Torus d n1))) =>
    genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ Z.2)

/-- **Lemma II.2.5 (b)**: the union is the union of separated pieces (`PieceDecomp`). -/
theorem genBoundaryUnion_decomp :
    PieceDecomp (genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ)
      (fun Z : (comps ω (finOf Zp) : Finset (Finset (Torus d n1))) =>
        genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ Z.2) :=
  unionGenSet_decomp _ (Nat.succ_pos k) fun Z Z' hne _ hu _ hw =>
    genBoundaryLocal_far st hc hn hL hρ hω hZ Z.2 Z'.2 (fun h => hne (Subtype.ext h)) hu hw

theorem genBoundaryLocal_top_subset {Z' : Finset (Torus d n1)} (hZ' : Z' ∈ comps ω (finOf Zp)) :
    (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ').Ω (k + 1) ⊆
      fineK1 M1 c n1 L k st.Omega :=
  boundaryGenSet_top_subset _ _ _ _

theorem genBoundaryUnion_top_subset :
    (genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ).Ω (k + 1) ⊆
      fineK1 M1 c n1 L k st.Omega := by
  unfold genBoundaryUnion
  rw [unionGenSet_Ω]
  exact Finset.biUnion_subset.2 fun Z _ => genBoundaryLocal_top_subset st hc hn hL hρ hω hZ Z.2

/-- **Definition II.2.7 (iv)**, one piece: `bg(G^{Z'}_{k+1}; lift_{k,k+1}(ψ_k, ψ_{k+1}))`
(`Ω = Ω_{k+1}`, mass `μ = μ_{k+1}`). -/
noncomputable def bgLocPiece {Z' : Finset (Torus d n1)} (hZ' : Z' ∈ comps ω (finOf Zp))
    (ψ : Torus d (M1 * (c * n1) * L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ : Torus d (M1 * (c * n1) * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h : Fin N → ℂ) :
    (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ').Ω 1 × Fin N → ℂ :=
  bgFieldC (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ') a μ c₀
    (liftMixed (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ')
      ((isCubeUnion_fineK1 st.Omega).isBlockUnion (le_refl _))
      (genBoundaryLocal_top_subset st hc hn hL hρ hω hZ hZ') ψ ϑ h)

/-- **Definition II.2.7 (iv)**: `φ^loc_{k+1}` as the background of the union `𝔹^loc`. -/
noncomputable def bgLocUnion
    (ψ : Torus d (M1 * (c * n1) * L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ : Torus d (M1 * (c * n1) * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h : Fin N → ℂ) :
    (genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ).Ω 1 × Fin N → ℂ :=
  bgFieldC (genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ) a μ c₀
    (liftMixed (genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ)
      ((isCubeUnion_fineK1 st.Omega).isBlockUnion (le_refl _))
      (genBoundaryUnion_top_subset st hc hn hL hρ hω hZ) ψ ϑ h)

/-- **Lemma II.2.6 for the backgrounds of Def-7**: where the `∃!` branch defining `bgLocUnion`
applies, it is, on each piece, the background of the piece. -/
theorem bgLocUnion_eq_piece
    (ψ : Torus d (M1 * (c * n1) * L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ : Torus d (M1 * (c * n1) * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h : Fin N → ℂ)
    (H : ∃! s : ((genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ).Ω 1 × Fin N → ℂ) ×
        ((genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ).Ω 1 → ℂ), IsSmallSolution (genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ) a μ c₀
      (liftMixed (genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ)
        ((isCubeUnion_fineK1 st.Omega).isBlockUnion (le_refl _))
        (genBoundaryUnion_top_subset st hc hn hL hρ hω hZ) ψ ϑ h) s.1 s.2)
    (Z : (comps ω (finOf Zp) : Finset (Finset (Torus d n1))))
    (x : (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ Z.2).Ω 1) (l : Fin N) :
    bgLocUnion st hc hn hL hρ hω hZ a μ c₀ ψ ϑ h
        ((genBoundaryUnion_decomp st hc hn hL hρ hω hZ).incl Z x, l) =
      bgLocPiece st hc hn hL hρ hω hZ a μ c₀ Z.2 ψ ϑ h (x, l) := by
  have hD := genBoundaryUnion_decomp (M1 := M1) (c := c) (n1 := n1) (L := L) (k := k) st hc hn hL
    hρ hω hZ
  have hres := hD.restrict_eq Z
    (liftMixed (genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ)
      ((isCubeUnion_fineK1 st.Omega).isBlockUnion (le_refl _))
      (genBoundaryUnion_top_subset st hc hn hL hρ hω hZ) ψ ϑ h)
    (liftMixed (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ Z.2)
      ((isCubeUnion_fineK1 st.Omega).isBlockUnion (le_refl _))
      (genBoundaryLocal_top_subset st hc hn hL hρ hω hZ Z.2) ψ ϑ h)
    (fun y hy => by
      rw [liftMixed_Ψ _ _ _ _ _ _ hy, liftMixed_Ψ _ _ _ _ _ _ (hD.dataSites_subset Z hy)])
    (fun y hy => by
      rw [liftMixed_h _ _ _ _ _ _ hy, liftMixed_h _ _ _ _ _ _ (hD.mem_of_mem hy)])
  unfold bgLocUnion bgLocPiece
  rw [bgFieldC_local_eq hD a μ c₀ _ H Z x l, hres]

end Flow

end Balaban.LargeField
