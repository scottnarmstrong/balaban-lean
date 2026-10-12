module

public import Balaban.LargeField.Region.Hull
public import Balaban.LargeField.Geometry.Coarsen
public import Balaban.LargeField.Geometry.Openings
import Mathlib.Tactic.Linarith

/-!
# One step of the region calculus as set functions (Part I, Definition I.3.1)

The step `k → k+1`: `n₀ = n_k = L n₁`, `n₁ = n_{k+1}`, `Z_k ⊆ 𝕋_k`, the new large-field cubes
`P, Q, R, S ⊆ 𝕋_{k+1}` with the constraints (R4)-(R6). All neighbourhoods of sets in `𝕋_{k+1}` are
taken in `𝕋_{k+1}`. With `ρ' = ⌊R_{k-1}⌋`, `ρ = ⌊R_k⌋`:

* `U_k = Z_k^≈ = Z_k^{∼(ρ'+1)}`, `U'_k = U_k^↑`;
* `Ω' = Op_{ρ+2}(U'^{∼3})`, `Ω = Op_1(P^{∼3}; Ω')`;
* `F'' = Q^{∼(ρ+2)} ∪ R^{∼(2ρ+4)}`, `Ω'' = Op_1(F''; Ω)`;
* `F^Z = (Ω''ᶜ)^{∼4} ∪ S^∼`, `Z^{(0)} = Op_{⌊2R_k⌋+3}(F^Z)ᶜ`, `Z^pre = Hull_{crit}(Z^{(0)})` or
  `Z^{(0)}`.

The case `k = 0` of the document (audit P1-07) is the case `Z = ∅`: then `U = U' = ∅` automatically
(a neighbourhood of `∅` is empty), so no separate definition is needed.

The radius hypotheses (RH) of Part I (audit P1-03) are `RadiusHyp`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban

/-! ### Generic facts on neighbourhoods and blocks -/

section Generic

variable {d n : ℕ}

theorem nbhd_zero [NeZero n] (X : Set (Torus d n)) : nbhd 0 X = X := by
  ext y
  rw [mem_nbhd]
  constructor
  · rintro ⟨x, hx, h⟩
    have : y = x := supDist_eq_zero.mp (Nat.le_zero.mp h)
    exact this ▸ hx
  · intro hy; exact ⟨y, hy, by simp [supDist_self]⟩

theorem nbhd_empty (m : ℕ) : nbhd m (∅ : Set (Torus d n)) = ∅ := by
  ext y; simp [mem_nbhd]

theorem nbhd_union (m : ℕ) (A B : Set (Torus d n)) : nbhd m (A ∪ B) = nbhd m A ∪ nbhd m B := by
  ext y; simp only [mem_nbhd, Set.mem_union]
  constructor
  · rintro ⟨x, hx | hx, h⟩
    · exact Or.inl ⟨x, hx, h⟩
    · exact Or.inr ⟨x, hx, h⟩
  · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
    · exact ⟨x, Or.inl hx, h⟩
    · exact ⟨x, Or.inr hx, h⟩

theorem nbhd_mono_right {m : ℕ} {X Y : Set (Torus d n)} (h : X ⊆ Y) : nbhd m X ⊆ nbhd m Y :=
  nbhd_mono le_rfl h

theorem nbhdNeg_subset [NeZero n] (m : ℕ) (X : Set (Torus d n)) : nbhdNeg m X ⊆ X := by
  intro y hy
  by_contra hyX
  exact hy (subset_nbhd m Xᶜ hyX)

theorem nbhdNeg_mono {m : ℕ} {X Y : Set (Torus d n)} (h : X ⊆ Y) : nbhdNeg m X ⊆ nbhdNeg m Y := by
  intro y hy hy'
  exact hy (nbhd_mono le_rfl (Set.compl_subset_compl.mpr h) hy')

/-- If `x` is at distance `≥ m` from every point within `1` of `v`, it is at distance `≥ m + 1`
from `v`. -/
theorem far_of_nbhd [NeZero n] {x v : Torus d n} {m : ℕ} (hm : 1 ≤ m)
    (h : ∀ w, supDist v w ≤ 1 → m ≤ supDist x w) : m + 1 ≤ supDist x v := by
  by_contra hlt
  obtain ⟨y, h1, h2⟩ := exists_split (x := x) (z := v) (a := m - 1) (b := 1) (by omega)
  have := h y (by rw [supDist_comm]; exact h2)
  omega

/-- A set is a union of `L`-blocks. -/
def IsLBlockUnion (L : ℕ) (Ω : Set (Torus d n)) : Prop :=
  ∀ x ∈ Ω, ∃ c, x ∈ lblock L c ∧ lblock L c ⊆ Ω

theorem opening_isLBlockUnion (L m : ℕ) (F : Set (Torus d n)) : IsLBlockUnion L (opening L m F) := by
  rintro x ⟨c, hx, hc⟩
  exact ⟨c, hx, fun y hy => ⟨c, hy, hc⟩⟩

theorem openingIn_isLBlockUnion (L m : ℕ) (F Ω : Set (Torus d n)) :
    IsLBlockUnion L (openingIn L m F Ω) := by
  rintro x ⟨c, hx, hΩ, hc⟩
  exact ⟨c, hx, fun y hy => ⟨c, hy, hΩ, hc⟩⟩

theorem openingIn_empty [NeZero n] {L : ℕ} (m : ℕ) {Ω : Set (Torus d n)}
    (hΩ : IsLBlockUnion L Ω) : openingIn L m ∅ Ω = Ω := by
  ext y
  constructor
  · rintro ⟨c, hy, hΩ', -⟩; exact hΩ' hy
  · intro hy
    obtain ⟨c, hc, hcΩ⟩ := hΩ y hy
    exact ⟨c, hc, hcΩ, by rw [setDist_eq_top_iff.mpr (Or.inr rfl)]; exact le_top⟩

end Generic

/-! ### Radius hypotheses and widths -/

/-- The radius hypotheses (RH) of Part I, §I.3.1 (audit P1-03): `λ` nondecreasing, `λ_j ≥ 1`,
`0 ≤ R_j ≤ R_base λ_j²`, `R_base ≥ 4L + 20`. -/
structure RadiusHyp (L : ℕ) (Rbase : ℝ) (lam R : ℕ → ℝ) : Prop where
  mono : Monotone lam
  one_le : ∀ j, 1 ≤ lam j
  nonneg : ∀ j, 0 ≤ R j
  le : ∀ j, R j ≤ Rbase * lam j ^ 2
  base : (4 * L + 20 : ℝ) ≤ Rbase

/-- The radius unit `r_j = ⌈R_base λ_j²⌉`. -/
noncomputable def radiusUnit (Rbase : ℝ) (lam : ℕ → ℝ) (j : ℕ) : ℕ := ⌈Rbase * lam j ^ 2⌉₊

/-- The component width `ω_j = 2 ⌊R_base λ_{j-1}²⌋ + L + 11` (`j ≥ 1`), `ω_0 = L + 11`. -/
noncomputable def omegaW (L : ℕ) (Rbase : ℝ) (lam : ℕ → ℝ) : ℕ → ℕ
  | 0 => L + 11
  | j + 1 => 2 * ⌊Rbase * lam j ^ 2⌋₊ + L + 11

theorem omegaW_succ (L : ℕ) (Rbase : ℝ) (lam : ℕ → ℝ) (j : ℕ) :
    omegaW L Rbase lam (j + 1) = 2 * ⌊Rbase * lam j ^ 2⌋₊ + L + 11 := rfl

/-! ### The set functions of Definition I.3.1 -/

namespace Region

variable {d n0 n1 : ℕ}

/-- (R1) `U_k = Z^{∼(ρ'+1)}` with `ρ' = [R_{k-1}]`. -/
def U (r : ℕ) (Z : Set (Torus d n0)) : Set (Torus d n0) := thick r Z

/-- (R2) `U'_k = U_k^↑`. -/
def Uprime (L n1 r : ℕ) (Z : Set (Torus d n0)) : Set (Torus d n1) := blockMap L n1 '' U r Z

/-- (R3) `Ω' = Op_{ρ+2}(U'^{∼3})`. -/
def OmegaPrime (L ρ : ℕ) (U' : Set (Torus d n1)) : Set (Torus d n1) := opening L (ρ + 2) (nbhd 3 U')

/-- (R4) `Ω = Op_1(P^{∼3}; Ω')`. -/
def Omega (L : ℕ) (P Ω' : Set (Torus d n1)) : Set (Torus d n1) := openingIn L 1 (nbhd 3 P) Ω'

/-- (R5) `F'' = Q^{∼(ρ+2)} ∪ R^{∼(2ρ+4)}`. -/
def FDD (ρ : ℕ) (Q R : Set (Torus d n1)) : Set (Torus d n1) := nbhd (ρ + 2) Q ∪ nbhd (2 * ρ + 4) R

/-- (R5) `Ω'' = Op_1(F''; Ω)`. -/
def OmegaDD (L : ℕ) (F Ω : Set (Torus d n1)) : Set (Torus d n1) := openingIn L 1 F Ω

/-- (R6) `F^Z = (Ω''ᶜ)^{∼4} ∪ S^∼`. -/
def FZ (Ω'' S : Set (Torus d n1)) : Set (Torus d n1) := nbhd 4 Ω''ᶜ ∪ nbhd 1 S

/-- (R6) `Z^{(0)} = Op_{⌊2R_k⌋+3}(F^Z)ᶜ`, the argument `ρ2` stands for `⌊2R_k⌋`. -/
def Z0 (L ρ2 : ℕ) (F : Set (Torus d n1)) : Set (Torus d n1) := (opening L (ρ2 + 3) F)ᶜ

/-- (R7) the new large-field cubes. -/
def newCubes (P Q R S : Set (Torus d n1)) : Set (Torus d n1) := P ∪ Q ∪ R ∪ S

/-- (R8) `Z^pre`: the hull closure of `Z^{(0)}` (with the critical side `b`) if `k+1 ≤ k₀`
(`crit = some b`), `Z^{(0)}` itself otherwise (`crit = none`). -/
noncomputable def Zpre [NeZero n1] (ω : ℕ) (crit : Option ℕ) (X : Set (Torus d n1)) :
    Set (Torus d n1) :=
  match crit with
  | none => X
  | some b => hullClosure ω b X

theorem subset_Zpre [NeZero n1] (ω : ℕ) (crit : Option ℕ) (X : Set (Torus d n1)) :
    X ⊆ Zpre ω crit X := by
  cases crit with
  | none => exact subset_rfl
  | some b => exact subset_hullClosure X

end Region

/-- The data of one step `k → k+1` (Definition I.3.1): the region `Z_k ⊆ 𝕋_k`, the radii
`R_{k-1}, R_k`, and the new large-field cubes `P, Q, R, S ⊆ 𝕋_{k+1}` with the constraints
(R4)-(R6): `P ⊆ Ω'`, `Q ⊆ Ω^{∼3}`, `R ⊆ Ω`, `S ⊆ Ω''^{∼-3}`. -/
structure RegionStep (d L n0 n1 : ℕ) (Rprev Rk : ℝ) where
  /-- The region `Z_k`. -/
  Z : Set (Torus d n0)
  /-- The new cubes `P_{k+1}`. -/
  P : Set (Torus d n1)
  /-- The new cubes `Q_{k+1}`. -/
  Q : Set (Torus d n1)
  /-- The new cubes `R_{k+1}`. -/
  R : Set (Torus d n1)
  /-- The new cubes `S_{k+1}`. -/
  S : Set (Torus d n1)
  P_sub : P ⊆ Region.OmegaPrime L ⌊Rk⌋₊ (Region.Uprime L n1 ⌊Rprev⌋₊ Z)
  Q_sub : Q ⊆ nbhd 3 (Region.Omega L P
    (Region.OmegaPrime L ⌊Rk⌋₊ (Region.Uprime L n1 ⌊Rprev⌋₊ Z)))
  R_sub : R ⊆ Region.Omega L P (Region.OmegaPrime L ⌊Rk⌋₊ (Region.Uprime L n1 ⌊Rprev⌋₊ Z))
  S_sub : S ⊆ nbhdNeg 3 (Region.OmegaDD L (Region.FDD ⌊Rk⌋₊ Q R)
    (Region.Omega L P (Region.OmegaPrime L ⌊Rk⌋₊ (Region.Uprime L n1 ⌊Rprev⌋₊ Z))))

namespace RegionStep

variable {d L n0 n1 : ℕ} {Rprev Rk : ℝ} (st : RegionStep d L n0 n1 Rprev Rk)

/-- `U_k`. -/
abbrev U : Set (Torus d n0) := Region.U ⌊Rprev⌋₊ st.Z
/-- `U'_k`. -/
abbrev Uprime : Set (Torus d n1) := Region.Uprime L n1 ⌊Rprev⌋₊ st.Z
/-- `Ω'_{k+1}`. -/
abbrev OmegaPrime : Set (Torus d n1) := Region.OmegaPrime L ⌊Rk⌋₊ st.Uprime
/-- `Ω_{k+1}`. -/
abbrev Omega : Set (Torus d n1) := Region.Omega L st.P st.OmegaPrime
/-- `F''_{k+1}`. -/
abbrev FDD : Set (Torus d n1) := Region.FDD ⌊Rk⌋₊ st.Q st.R
/-- `Ω''_{k+1}`. -/
abbrev OmegaDD : Set (Torus d n1) := Region.OmegaDD L st.FDD st.Omega
/-- `F^Z_{k+1}`. -/
abbrev FZ : Set (Torus d n1) := Region.FZ st.OmegaDD st.S
/-- `Z^{(0)}_{k+1}`. -/
abbrev Z0 : Set (Torus d n1) := Region.Z0 L ⌊2 * Rk⌋₊ st.FZ
/-- `𝒩_{k+1}`. -/
abbrev newCubes : Set (Torus d n1) := Region.newCubes st.P st.Q st.R st.S
/-- `Z^pre_{k+1}`. -/
noncomputable abbrev Zpre [NeZero n1] (ω : ℕ) (crit : Option ℕ) : Set (Torus d n1) :=
  Region.Zpre ω crit st.Z0

theorem P_sub' : st.P ⊆ st.OmegaPrime := st.P_sub
theorem Q_sub' : st.Q ⊆ nbhd 3 st.Omega := st.Q_sub
theorem R_sub' : st.R ⊆ st.Omega := st.R_sub
theorem S_sub' : st.S ⊆ nbhdNeg 3 st.OmegaDD := st.S_sub

end RegionStep

end Balaban.LargeField
