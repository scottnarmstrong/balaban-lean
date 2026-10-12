module

public import Balaban.LargeField.Operators.Quiet

/-!
# The five small-field functions of `R` (Part III, Definition III.5.1)

For a ripe component `Z` with localized history `a` (fine sets), the scale `k`, the core scale
`k₁ ≤ k`, the five indicator functions

* `chiTilde` (item 1, P7 (2.18)): `ψ_k ∈ Ψ̃_k(Z^c_0 ∩ (Ω^c_k)^{∼3}; 3δ_k)`;
* `chiS` (item 2, "the second decomposition"): `∏ χ_k(□)` over the `π_k`-cubes
  `□ ⊂ Z''^c_0 ∩ (Ω^c_k)^{∼3} ∩ Z`;
* `chiZero` (item 3): `∏ χ^0_{k₁,½}(□)` over the `π_{k₁}`-cubes `□ ⊂ U^c ∩ U^{∼6}`, where
  `χ^0_{k₁,½}` is `χ_{k₁}` with `δ_{k₁}` replaced by `½ δ_{k₁}` and `ψ_{k₁}` by `ψ'_{k₁}`
  (`psiPrime`);
* `chiDD` (item 4, P7 (2.61), `χ''`): `|δψ(y)| < δ_{j,1}` for the blocks `y` of the set `D''`
  of layer `j`;
* `chiZDD` (item 5, P7 (3.20), `χ_{Z''}`): `∏ χ_k(□)` over the `π_k`-cubes `□ ⊂ Z''_0 ∩ Z`.

The sets `Z_0`, `Z''_0` (Definition III.3.1), the core set `U`, the layer `Λ_{k₁}`, the field
`δψ` (§III.4.4) and the vector `ψ_0` (Definition III.3.4) are the *arguments* of the definitions:
the definitions are given on their whole carrier, for arbitrary values of these arguments.  All five
are indicator functions of conditions on real configurations (`charFn`), with values in `{0, 1}`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

section Defs

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {ϱ : ℝ}

/-- `ψ ∈ Ψ̃_k(X; δ)` at one scale: `|ψ_k(y) - ψ_k(y')| < δ` for the adjacent `k`-blocks `y, y'`
contained in the fine set `X` (the bonds of `T^{(k)}_1` in `X`) and `||ψ_k(y)| - 1| < δ` for the
`k`-blocks `y ⊂ X` (P7 p. 501). -/
def PsiTildeOne (k : ℕ) (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (X : Set (Torus S.d (M * n K * S.L ^ K))) (δ : ℝ) : Prop :=
  (∀ y y' : BlockAt S n M K k,
      BlockSub (S := S) (n := n) (M := M) (K := K) k y X →
      BlockSub (S := S) (n := n) (M := M) (K := K) k y' X →
      y ≠ y' → BlockAdj (S := S) (n := n) (M := M) (K := K) ⟨k, y⟩ ⟨k, y'⟩ →
        ‖ψ y - ψ y'‖ < δ) ∧
    ∀ y : BlockAt S n M K k, BlockSub (S := S) (n := n) (M := M) (K := K) k y X →
      |‖ψ y‖ - 1| < δ

variable (a : LocalHistory S n M K) (k : ℕ)

/-- The fine set `(Ω^c_k)^{∼3}` (`Ω^c_k = Z_k ∖ Ω_k` of the localized history). -/
def omegaCFine (r : ℕ) : Set (Torus S.d (M * n K * S.L ^ K)) :=
  fineSet (S := S) (n := n) M K k (omegaCNb a r k)

/-- The region `Z^c_0 ∩ (Ω^c_k)^{∼3}` of `χ̃_k`, with `Z_0` given (`Z^c_0 = Z ∖ Z_0`). -/
def tildeRegion (Z0 : Set (Torus S.d (M * n K * S.L ^ K))) :
    Set (Torus S.d (M * n K * S.L ^ K)) :=
  (a.Z k \ Z0) ∩ omegaCFine a k 3

/-- **Definition III.5.1 item 1** (P7 (2.18)): the condition `ψ_k ∈ Ψ̃_k(Z^c_0 ∩ (Ω^c_k)^{∼3}; 3δ_k)`. -/
def ChiTildeProp (Z0 : Set (Torus S.d (M * n K * S.L ^ K))) (δk : ℝ)
    (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) : Prop :=
  PsiTildeOne k ψ (tildeRegion a k Z0) (3 * δk)

/-- `χ̃_k` (Definition III.5.1 item 1). -/
noncomputable def chiTilde (Z0 : Set (Torus S.d (M * n K * S.L ^ K))) (δk : ℝ) :
    (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) → ℝ :=
  charFn (ChiTildeProp a k Z0 δk)

/-- The `π_k`-cubes `□ ⊂ Z''^c_0 ∩ (Ω^c_k)^{∼3} ∩ Z` of the second decomposition. -/
def chiSCubes (Z0DD : Set (Torus S.d (M * n K * S.L ^ K))) : Set (Torus S.d (n k)) :=
  {y | CubeSub (S := S) (n := n) M K k y (tildeRegion a k Z0DD)}

variable (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (cs : OpConsts)
  (hv : EuclideanSpace ℝ (Fin N))

/-- The product `∏_{□ ∈ A} χ_q(□)` of the cube characteristic functions of Definition II.3.2
item 1 at scale `q` with tolerance `δ` over a set `A` of `π_q`-cubes, applied to a field on the
`q`-blocks. -/
noncomputable def chiProd (q : ℕ) (hqK : q ≤ K) (δ : ℝ) (A : Set (Torus S.d (n q)))
    (ψ : BlockAt S n M K q → EuclideanSpace ℝ (Fin N)) : ℝ :=
  cubeProd (fun y0 => chiK (M1 := g.M1) (N₁ := g.c * n q) (L := S.L) (q := q) (N := N) cs.aw
      (cs.mu q) δ (fun i => hv i) g.c (n q) y0) (cubeFin (S := S) A)
    (blockCfgOf g hnn le_rfl hqK ψ)

/-- `χ_S` (Definition III.5.1 item 2): `∏ χ_k(□)` over the `π_k`-cubes
`□ ⊂ Z''^c_0 ∩ (Ω^c_k)^{∼3} ∩ Z`, with tolerance `δ_k`. -/
noncomputable def chiS (hkK : k ≤ K) (Z0DD : Set (Torus S.d (M * n K * S.L ^ K))) :
    (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) → ℝ :=
  chiProd g hnn cs hv k hkK (cs.delta k) (chiSCubes a k Z0DD)

/-- `ψ'_{k₁}` of Definition III.5.1 item 3: `ψ_{k₁}` on `Λ_{k₁} ∩ U^{∼3}` (and off `Λ_{k₁}`),
`ψ_0` on `Λ_{k₁} ∖ U^{∼3}`; `Lam` is the fine set `Λ_{k₁}`, `U3` the fine set `U^{∼3}`. -/
noncomputable def psiPrime (k1 : ℕ) (Lam U3 : Set (Torus S.d (M * n K * S.L ^ K)))
    (psi0 : EuclideanSpace ℝ (Fin N)) (ψ : BlockAt S n M K k1 → EuclideanSpace ℝ (Fin N)) :
    BlockAt S n M K k1 → EuclideanSpace ℝ (Fin N) := by
  classical
  exact fun y => if BlockSub (S := S) (n := n) (M := M) (K := K) k1 y (Lam \ U3) then psi0 else ψ y

/-- The `π_{k₁}`-cubes of `U^c ∩ U^{∼6}` (`U` a set of `π_{k₁}`-cubes). -/
def chiZeroCubes (k1 : ℕ) (U : Set (Torus S.d (n k1))) : Set (Torus S.d (n k1)) :=
  {y | y ∈ nbhd 6 U ∧ y ∉ U}

/-- `χ^0` (Definition III.5.1 item 3): `∏ χ^0_{k₁,½}(□)` over the `π_{k₁}`-cubes
`□ ⊂ U^c ∩ U^{∼6}`; `χ^0_{k₁,½}` is `χ_{k₁}` with `δ_{k₁}` replaced by `½ δ_{k₁}` and `ψ_{k₁}`
by `ψ'_{k₁}`. -/
noncomputable def chiZero (k1 : ℕ) (hk1K : k1 ≤ K) (U : Set (Torus S.d (n k1)))
    (Lam U3 : Set (Torus S.d (M * n K * S.L ^ K))) (psi0 : EuclideanSpace ℝ (Fin N)) :
    (BlockAt S n M K k1 → EuclideanSpace ℝ (Fin N)) → ℝ := fun ψ =>
  chiProd g hnn cs hv k1 hk1K (cs.delta k1 / 2) (chiZeroCubes k1 U)
    (psiPrime k1 Lam U3 psi0 ψ)

/-- The fine set `D'' = (𝔹_k ∩ Z^c_{k₁} ∩ Ω^c_k) ∖ (Λ_{k₁} ∩ U^{∼3})` of Definition III.5.1
item 4: `Zk1` is the fine set `Z_{k₁}`, `Lam` the fine set `Λ_{k₁}` and `U3` the fine set
`U^{∼3}`. -/
def ddRegion (B : GeneratingSet S.d S.L (M * n K) K ϱ)
    (Zk1 Lam U3 : Set (Torus S.d (M * n K * S.L ^ K))) : Set (Torus S.d (M * n K * S.L ^ K)) :=
  ({x | x ∈ B.Ω 1} ∩ (a.Z k \ Zk1) ∩ (a.Z k \ a.Omega (k - 1))) \ (Lam ∩ U3)

/-- **Definition III.5.1 item 4** (P7 (2.61)): `|δψ(y)| < δ_{j,1}` for all blocks `y` of `D''` of
layer `j` (`1 ≤ j ≤ K`); `δ1 j = δ_{j,1}`, `dpsi = δψ` (§III.4.4). -/
def ChiDDProp (B : GeneratingSet S.d S.L (M * n K) K ϱ)
    (Zk1 Lam U3 : Set (Torus S.d (M * n K * S.L ^ K))) (δ1 : ℕ → ℝ)
    (dpsi : MultiField S n M K N) : Prop :=
  ∀ j, 1 ≤ j → j ≤ K → ∀ y : BlockAt S n M K j,
    BlockSub (S := S) (n := n) (M := M) (K := K) j y
      (ddRegion a k B Zk1 Lam U3 ∩ {x | x ∈ B.layer j}) → ‖dpsi j y‖ < δ1 j

/-- `χ''` (Definition III.5.1 item 4). -/
noncomputable def chiDD (B : GeneratingSet S.d S.L (M * n K) K ϱ)
    (Zk1 Lam U3 : Set (Torus S.d (M * n K * S.L ^ K))) (δ1 : ℕ → ℝ) :
    MultiField S n M K N → ℝ :=
  charFn (ChiDDProp a k B Zk1 Lam U3 δ1)

/-- The `π_k`-cubes `□ ⊂ Z''_0 ∩ Z` of item 5. -/
def chiZDDCubes (Z0DD : Set (Torus S.d (M * n K * S.L ^ K))) : Set (Torus S.d (n k)) :=
  {y | CubeSub (S := S) (n := n) M K k y (Z0DD ∩ a.Z k)}

/-- `χ_{Z''}` (Definition III.5.1 item 5, P7 (3.20)): `∏ χ_k(□)` over the `π_k`-cubes
`□ ⊂ Z''_0 ∩ Z`, with tolerance `δ_k`. -/
noncomputable def chiZDD (hkK : k ≤ K) (Z0DD : Set (Torus S.d (M * n K * S.L ^ K))) :
    (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) → ℝ :=
  chiProd g hnn cs hv k hkK (cs.delta k) (chiZDDCubes a k Z0DD)

end Defs

/-! ### Basic properties: values in `{0, 1}` -/

theorem charFn_mem_Icc {X : Type*} (P : X → Prop) (x : X) : charFn P x ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  rw [charFn_apply]
  split_ifs <;> simp

theorem charFn_eq_zero_or_one {X : Type*} (P : X → Prop) (x : X) : charFn P x = 0 ∨ charFn P x = 1 := by
  classical
  rw [charFn_apply]
  split_ifs <;> simp

section Props

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {ϱ : ℝ}
  (a : LocalHistory S n M K) (k : ℕ) (g : Geo S n R M)
  (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (cs : OpConsts) (hv : EuclideanSpace ℝ (Fin N))

/-- The product of cube characteristic functions takes values in `[0, 1]`. -/
theorem chiProd_mem_Icc (q : ℕ) (hqK : q ≤ K) (δ : ℝ) (A : Set (Torus S.d (n q)))
    (ψ : BlockAt S n M K q → EuclideanSpace ℝ (Fin N)) :
    chiProd g hnn cs hv q hqK δ A ψ ∈ Set.Icc (0 : ℝ) 1 := by
  unfold chiProd cubeProd
  exact ⟨Finset.prod_nonneg fun _ _ => (charFn_mem_Icc _ _).1,
    Finset.prod_le_one₀ (fun _ _ => (charFn_mem_Icc _ _).1) fun _ _ => (charFn_mem_Icc _ _).2⟩

theorem chiTilde_mem_Icc (Z0 : Set (Torus S.d (M * n K * S.L ^ K))) (δk : ℝ)
    (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    chiTilde a k Z0 δk ψ ∈ Set.Icc (0 : ℝ) 1 := charFn_mem_Icc _ _

theorem chiS_mem_Icc (hkK : k ≤ K) (Z0DD : Set (Torus S.d (M * n K * S.L ^ K)))
    (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    chiS a k g hnn cs hv hkK Z0DD ψ ∈ Set.Icc (0 : ℝ) 1 := chiProd_mem_Icc g hnn cs hv _ _ _ _ _

theorem chiZero_mem_Icc (k1 : ℕ) (hk1K : k1 ≤ K) (U : Set (Torus S.d (n k1)))
    (Lam U3 : Set (Torus S.d (M * n K * S.L ^ K))) (psi0 : EuclideanSpace ℝ (Fin N))
    (ψ : BlockAt S n M K k1 → EuclideanSpace ℝ (Fin N)) :
    chiZero g hnn cs hv k1 hk1K U Lam U3 psi0 ψ ∈ Set.Icc (0 : ℝ) 1 :=
  chiProd_mem_Icc g hnn cs hv _ _ _ _ _

theorem chiDD_mem_Icc (B : GeneratingSet S.d S.L (M * n K) K ϱ)
    (Zk1 Lam U3 : Set (Torus S.d (M * n K * S.L ^ K))) (δ1 : ℕ → ℝ)
    (dpsi : MultiField S n M K N) :
    chiDD a k B Zk1 Lam U3 δ1 dpsi ∈ Set.Icc (0 : ℝ) 1 := charFn_mem_Icc _ _

theorem chiZDD_mem_Icc (hkK : k ≤ K) (Z0DD : Set (Torus S.d (M * n K * S.L ^ K)))
    (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    chiZDD a k g hnn cs hv hkK Z0DD ψ ∈ Set.Icc (0 : ℝ) 1 := chiProd_mem_Icc g hnn cs hv _ _ _ _ _

end Props

end Balaban.LargeField
