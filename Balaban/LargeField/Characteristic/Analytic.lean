module

public import Balaban.LargeField.Characteristic.OperatorDomain
public import Balaban.LargeField.Region.Generating
import Mathlib.Tactic.Linarith

/-!
# The analyticity spaces (Part II, Definition II.3.5; P5 (1.36)-(1.37))

Characteristic functions are indicator functions of real configurations and are never continued;
what is continued analytically is the integrand on the *domains* below, which are sets of complex
fields (the integration variables continued to complex values).

* `DeltaC` is `Δ^c_j(□; 1, ε)` (a): complex fields `ψ_j` whose lift lies in `𝒟(G_j(□))` and whose
  complex small solution satisfies the inequalities of Definition II.3.1 with `ε` (`RegC`);
* `DeltaPrimeC` is `Δ'^c_j(□; (¾, 5/4), ε_{j-1})` (b): the complexification of item 3 of
  Definition II.3.2 (`RegMixedIneq` on `𝒟(G_{k+1}(□'))`);
* `H7Domain` is the product of (1.36), (1.37) and the polydisc `‖g‖_{ℓ¹} < 1` (d).

The generating set `G_j(□)` is a level-`j` object (`genCube` with `q = j`, cubes of `𝕋_j`
indexed by `Torus d (n j)`, torus `Torus d (M1 * (c * n j) * L ^ j)`); the fields of the history
live on the blocks of the history torus of level `K`, and are transported to the level-`j` torus
by `histCast` (the two are the same set of blocks: `n j * L ^ j = n K * L ^ K`, `M = c * M1`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory

set_option linter.unusedSectionVars false

/-! ### Transport between the level-`q` torus and the history torus -/

/-- Transport along an equality of torus sizes. -/
def torusCast {d m m' : ℕ} (h : m = m') (y : Torus d m) : Torus d m' := h ▸ y

section Cast

variable {n : ℕ → ℕ} {L M1 c M K : ℕ}

theorem histScale_eq (hM : M = c * M1) (hnn : ∀ i, i < K → n i = L * n (i + 1)) {i q : ℕ} (hiq : i ≤ q)
    (hqK : q ≤ K) : M1 * (c * n q) * L ^ (q - i) = M * n K * L ^ (K - i) := by
  rw [nn_eq_pow' hnn hqK, hM]
  have : L ^ (K - i) = L ^ (K - q) * L ^ (q - i) := by rw [← pow_add]; congr 1; omega
  rw [this]; ring

end Cast

/-! ### `Δ^c_j(□; 1, ε)` and `Δ'^c_j(□; (¾, 5/4), ε_{j-1})` -/

section DeltaC

variable {d M1 N₁ L N : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

section Single

variable {q : ℕ} (a : ℕ → ℝ) (μ ε : ℝ) (h : Fin N → ℂ) (c n : ℕ)

/-- **Definition II.3.5 (a)**: `Δ^c_q(□; 1, ε)`, the complex fields `ψ_q` (only their values on
the blocks of `□^{∼3}` matter, by the stencil lemma) whose lift `D^c` lies in the open complex
domain `𝒟(G_q(□))` and for which the complex small solution `bg(G_q(□); D^c)` satisfies the
inequalities of Definition II.3.1 with `ε` in place of `δ`. -/
def DeltaC (y0 : Torus d n) : Set (Torus d (M1 * N₁ * L ^ (q - q)) → Fin N → ℂ) :=
  {ψ | RegC (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) a μ
    (liftSingle (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) ψ h) ε
    (cubeNbhd M1 N₁ L q c n 1 y0) (cubeNbhd M1 N₁ L q c n 1 y0)}

end Single

section Mixed

variable {k : ℕ} (a : ℕ → ℝ) (μ ε νk : ℝ) (h : Fin N → ℂ) {c n : ℕ}
  (hm : N₁ * L ^ (k + 1 - (k + 1)) = c * n) (y0 : Torus d n)
  (Om : Finset (Torus d (M1 * N₁ * L ^ (k + 1))))
  (hOm : IsBlockUnion L (M1 * N₁) (k + 1) (k + 1) Om)

/-- The complex mixed lift `lift_{k,k+1}(ψ_k, θ)` on `G_{k+1}(□')`. -/
noncomputable def mixedDataC (ψ : Torus d (M1 * N₁ * L ^ (k + 1 - k)) → Fin N → ℂ)
    (θ : Torus d (M1 * N₁ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) :
    BgData (genCubeMixed hm y0 Om hOm) N :=
  liftMixed (genCubeMixed hm y0 Om hOm) hOm (genCubeMixed_top_subset hm y0 Om hOm) ψ θ h

/-- **Definition II.3.5 (b)**: `Δ'^c_{k+1}(□'; (¾, 5/4), ε)`, the complexification of item 3 of
Definition II.3.2 at the step `k → k + 1`: pairs `(ψ_k, θ)` of complex fields whose lift lies in
`𝒟(G_{k+1}(□'))` and whose complex small solution satisfies `RegMixedIneq` with `ε` in place
of `δ_k`. -/
def DeltaPrimeC : Set ((Torus d (M1 * N₁ * L ^ (k + 1 - k)) → Fin N → ℂ) ×
    (Torus d (M1 * N₁ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ)) :=
  {p | InUnionDomainC (genCubeMixed hm y0 Om hOm) (bgC0 d L N) (bgC1 d L N) μ
      (mixedDataC h hm y0 Om hOm p.1 p.2) ∧
    RegMixedIneq (genCubeMixed hm y0 Om hOm) a μ (mixedDataC h hm y0 Om hOm p.1 p.2)
      ((L : ℝ) ^ k) νk ε (cubeNbhd M1 N₁ L (k + 1) c n 1 y0 \ Om)
      (cubeNbhd M1 N₁ L (k + 1) c n 1 y0 ∩ Om) (cubeNbhd M1 N₁ L (k + 1) c n 1 y0)}

end Mixed

end DeltaC

/-! ### The H7 domain -/

section H7

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]
  {N : ℕ}

/-- A complex field `y ↦ ψ_j(y) ∈ ℂ^N` on the `j`-blocks, for every scale `j`. -/
abbrev MultiFieldC (S : Setting) (n : ℕ → ℕ) (M K N : ℕ) : Type :=
  (j : ℕ) → Torus S.d (M * n K * S.L ^ (K - j)) → Fin N → ℂ

/-- The fine set of the cubes `W ⊂ 𝕋_{j+1}` as a level-`(j+1)` set, a union of `(j+1)`-blocks
(`Ω_{j+1}` in the level-`(j+1)` torus of the step `j → j + 1`). -/
noncomputable def omegaLevel (M1 c j : ℕ) [NeZero M1] [NeZero c] (W : Set (Torus S.d (n j))) :
    Finset (Torus S.d (M1 * (c * n j) * S.L ^ j)) :=
  cubePre M1 (c * n j) S.L j (S.L ^ j * (c * M1)) (n j) W

theorem omegaLevel_blockUnion (M1 c j : ℕ) [NeZero M1] [NeZero c] (W : Set (Torus S.d (n j))) :
    IsBlockUnion S.L (M1 * (c * n j)) j j (omegaLevel (S := S) (n := n) M1 c j W) :=
  (isCubeUnion_cubePre (M1 := M1) (N₁ := c * n j) (L := S.L) (q := j) (le_refl j)
    (by simp) W).isBlockUnion (le_refl j)

variable (M1 c : ℕ) [NeZero M1] [NeZero c]
  (hM : M = c * M1) (hnn : ∀ i, i < K → n i = S.L * n (i + 1))
  (a : LocalHistory S n M K) (k : ℕ) (hkK : k ≤ K)
  (Xf : Set (Torus S.d (M * n K * S.L ^ K)))
  (aw : ℕ → ℝ) (μs ε ε1 νs : ℕ → ℝ) (h : Fin N → ℂ)

/-- The cubes of `(Ω^c_j)^{∼3}`, `Ω^c_j = Z_j ∖ Ω_j`, in `𝕋_j`. -/
def omegaCNb (r j : ℕ) : Set (Torus S.d (n j)) :=
  nbhd r {y | CubeSub (S := S) (n := n) M K j y (a.Z j \ a.Omega (j - 1))}

/-- **Definition II.3.5 (c), (1.36)**, first kind: for every `1 ≤ j ≤ k` and every cube `□ ⊂ X`
of `𝕋_j` with `□ ⊂ (Ω^{∼3}_{j+1})^c ∖ (Ω^c_j)^{∼3}`, the complex field `ψ_j` (transported to
the level-`j` torus) lies in `Δ^c_j(□; 1, ε_j)`. -/
def DeltaDomain1 (ψ : MultiFieldC S n M K N) : Prop :=
  ∀ j (hjk : j ≤ k) (y : Torus S.d (n j)), CubeSub (S := S) (n := n) M K j y Xf →
    (∀ x, cubeMap n S.L M K j x = y → cubeMap n S.L M K (j + 1) x ∉ omegaNb a k 3 (j + 1)) →
    y ∉ omegaCNb a 3 j →
      (fun z => ψ j (torusCast (histScale_eq hM hnn le_rfl (hjk.trans hkK)) z)) ∈
        DeltaC (M1 := M1) (N₁ := c * n j) (L := S.L) (q := j) aw (μs j) (ε j) h c (n j) y

/-- **Definition II.3.5 (c), (1.36)**, second kind: for every step `i → i + 1` with
`i + 1 ≤ k` and every cube `□ ⊂ X` of `𝕋_{i+1}` with `□ ⊂ Ω^{∼3}_{i+1} ∩ (Ω^c_{i+1})^{∼3}`, the
pair `(ψ_i, ψ_{i+1})` (transported to the level-`(i+1)` torus) lies in
`Δ'^c_{i+1}(□; (¾, 5/4), ε_i)`, with `Ω_{i+1}` the level-`(i+1)` set of the cubes of
`Ω_{i+1} = a.Omega i`. -/
def DeltaDomain2 (ψ : MultiFieldC S n M K N) : Prop :=
  ∀ i (hik : i + 1 ≤ k) (y : Torus S.d (n (i + 1))),
    CubeSub (S := S) (n := n) M K (i + 1) y Xf →
    y ∈ omegaNb a k 3 (i + 1) → y ∈ omegaCNb a 3 (i + 1) →
      ((fun z => ψ i (torusCast (histScale_eq hM hnn (q := i + 1) (Nat.le_succ i)
          (hik.trans hkK)) z),
        fun z => ψ (i + 1) (torusCast (histScale_eq hM hnn (q := i + 1) le_rfl
          (hik.trans hkK)) z)) :
          (Torus S.d (M1 * (c * n (i + 1)) * S.L ^ (i + 1 - i)) → Fin N → ℂ) ×
          (Torus S.d (M1 * (c * n (i + 1)) * S.L ^ (i + 1 - (i + 1))) → Fin N → ℂ)) ∈
        DeltaPrimeC (M1 := M1) (N₁ := c * n (i + 1)) (L := S.L) (k := i) aw (μs (i + 1))
          (ε i) (νs i) h (c := c) (n := n (i + 1)) (by simp) y
          (omegaLevel (S := S) (n := n) M1 c (i + 1)
            {z | CubeSub (S := S) (n := n) M K (i + 1) z (a.Omega i)})
          (omegaLevel_blockUnion (S := S) (n := n) M1 c (i + 1) _)

/-- **Definition II.3.5 (c), (1.37)**: `|ψ'_j| < ε_{1,j}` on the `j`-blocks inside
`X ∩ (Ω_{j+1} ∖ Ω''_{j+1})`, `0 ≤ j ≤ k - 1`. -/
def FluctDomain (ψ' : MultiFieldC S n M K N) : Prop :=
  ∀ j, j < k → ∀ y : Torus S.d (M * n K * S.L ^ (K - j)),
    BlockSub (S := S) (n := n) j y (Xf ∩ (a.Omega j \ a.OmegaDD j)) → vn (ψ' j y) < ε1 j

/-- **Definition II.3.5 (d)**: the **H7 domain** of the history `a` at `X`: the complex
multiscale field in `(1.36)`, the complex fluctuation field in `(1.37)` and the external field
`g : 𝕋 → ℂ^N` with `‖g‖_{ℓ¹} < 1`. -/
def H7Domain (ψ ψ' : MultiFieldC S n M K N) (g : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ) :
    Prop :=
  DeltaDomain1 M1 c hM hnn a k hkK Xf aw μs ε h ψ ∧
  DeltaDomain2 M1 c hM hnn a k hkK Xf aw μs ε νs h ψ ∧
  FluctDomain a k Xf ε1 ψ' ∧
  ∑ x, ∑ i, ‖g x i‖ < 1

end H7

end Balaban.LargeField
