module

public import Balaban.LargeField.Background.MinimalGenSet
public import Balaban.Localization.CubeAligned
public import Balaban.Localization.SupportMargin
public import Balaban.Background.Data
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The basic properties of P3's local generating set `B_j(X)` (alignment, range, locality, covariance)

The object is the landed `minimalGenSet hj X` of `Balaban.LargeField.MinimalGenSet`, `hj : j ≤ q`:
the top domain is `Ω_j = cubeInterior j X`, each lower layer is `Ω_n = nearStep n Ω_{n+1}` (add the
`C_n`-cubes within cube-index distance `5 L`), and the separation is `minSep L M₁ = 5 L M₁`.  No new
definition is made here.

This is the full-level form of P3 (4.4)-(4.6): the top layer is the polymer itself.  The
mixed-level recurrence (intersections with ambient layers) is a separate package.  No class
definition is changed and no claim is made about which generator the class terms use.  The object
is not a parent for the landed fluctuation engine: its `Ω₁` is not the whole torus
(`LocalGenNeg`), and its separation `5 L M₁` cannot satisfy `BgSetting.hr`/`hr₀`.

Contents (`LOCALGEN.md` §3, §4):

* alignment: `cubeInterior j X = X` for `X` a union of `C_j`-cubes (`localGen_cubeInterior_eq`),
  the top layer is `j` with top domain `X` and nothing above (`localGen_top_Ω`, `localGen_layer_top`,
  `localGen_Ω_of_gt`), and `CubeAligned (minimalGenSet hj X) m₁` (`localGen_cubeAligned`; it needs
  no hypothesis on `X`, since every layer is by construction a union of cubes);
* range: the layer-by-layer range (3.1) (`localGen_layer_range`), the uniform envelope (3.2)
  (`localGen_dataSites_range`, which is the landed `dataSites_near`) and monotonicity of the data
  sites (`localGen_dataSites_mono`);
* locality: the layers on a set `A` depend only on `X` within `12 M₁ L ^ j` of `A`
  (`localGen_local`, `localGen_layerIndex_local`);
* covariance: translation by a vector aligned to the `C_j` grid (`localGen_translate_Ω`).

Source: P3 pp. 68-69, (4.4)-(4.6).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background Finset

set_option linter.unusedSectionVars false

variable {d M1 N₁ L q : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

/-! ### Cells and cube indices -/

/-- Two sites have the same `𝒞_n`-cube index iff they lie in the same cell of side `L ^ n M₁`. -/
theorem fineCubeIdx_eq_iff_sameCell {n : ℕ} (hn : n ≤ q) {x y : Torus d (M1 * N₁ * L ^ q)} :
    fineCubeIdx M1 N₁ L q n x = fineCubeIdx M1 N₁ L q n y ↔ SameCell (L ^ n * M1) x y := by
  constructor
  · intro h μ
    have h1 := congrArg ZMod.val (congrFun h μ)
    unfold fineCubeIdx at h1
    rw [blockMap_apply, blockMap_apply, blockCoord_val (fine_eq_cube hn),
      blockCoord_val (fine_eq_cube hn)] at h1
    exact h1
  · intro h
    funext μ
    unfold fineCubeIdx
    rw [blockMap_apply, blockMap_apply]
    unfold blockCoord
    rw [h μ]

/-- Membership in a layer of `B_j(X)` depends only on the `𝒞_n`-cube of the site. -/
theorem localGen_mem_minLayer_iff {j n : ℕ} (X : Finset (Torus d (M1 * N₁ * L ^ q)))
    {x x' : Torus d (M1 * N₁ * L ^ q)}
    (hc : fineCubeIdx M1 N₁ L q n x = fineCubeIdx M1 N₁ L q n x') :
    x ∈ minLayer M1 N₁ L q j X n ↔ x' ∈ minLayer M1 N₁ L q j X n := by
  rcases lt_trichotomy n j with h1 | h1 | h1
  · rw [minLayer_of_lt X h1, mem_nearStep, mem_nearStep, hc]
  · subst h1
    rw [minLayer_self, mem_cubeInterior, mem_cubeInterior, hc]
  · rw [minLayer_of_gt X h1]; simp

/-! ### T1: alignment -/

section Aligned

variable {j : ℕ} (X : Finset (Torus d (M1 * N₁ * L ^ q)))

/-- **(a)** If `X` is a union of cells of side `L ^ j M₁` (the `C_j`-cubes), then
`Ω_j(X) = X` (P3 (4.4)). -/
theorem localGen_cubeInterior_eq (hj : j ≤ q)
    (hX : IsCellUnion (L ^ j * M1) (X : Set (Torus d (M1 * N₁ * L ^ q)))) :
    cubeInterior M1 N₁ L q j X = X := by
  apply Finset.Subset.antisymm (cubeInterior_subset X)
  intro x hx
  refine (mem_cubeInterior X).2 fun y hy => ?_
  have hs : SameCell (L ^ j * M1) y x := (fineCubeIdx_eq_iff_sameCell hj).1 hy
  exact hX x (by exact_mod_cast hx) y hs

/-- **(b)** The top domain of `B_j(X)` is `X`. -/
theorem localGen_top_Ω (hj : j ≤ q)
    (hX : IsCellUnion (L ^ j * M1) (X : Set (Torus d (M1 * N₁ * L ^ q)))) :
    (minimalGenSet hj X).Ω j = X := by
  rw [minimalGenSet_Ω, minLayer_self, localGen_cubeInterior_eq X hj hX]

/-- **(b)** There is no layer above `j`: `Ω_n = ∅` for `n > j`. -/
theorem localGen_Ω_of_gt (hj : j ≤ q) {n : ℕ} (h : j < n) : (minimalGenSet hj X).Ω n = ∅ := by
  rw [minimalGenSet_Ω, minLayer_of_gt X h]

/-- **(b)** The top layer of `B_j(X)` is `j`, and it is `X`. -/
theorem localGen_layer_top (hj : j ≤ q)
    (hX : IsCellUnion (L ^ j * M1) (X : Set (Torus d (M1 * N₁ * L ^ q)))) :
    (minimalGenSet hj X).layer j = X := by
  ext x
  rw [GeneratingSet.mem_layer, localGen_top_Ω X hj hX, localGen_Ω_of_gt X hj (Nat.lt_succ_self j)]
  simp

/-- **(b)** The layers above `j` are empty. -/
theorem localGen_layer_of_gt (hj : j ≤ q) {n : ℕ} (h : j < n) :
    (minimalGenSet hj X).layer n = ∅ := by
  ext x
  rw [GeneratingSet.mem_layer, localGen_Ω_of_gt X hj h]
  simp

/-- **(b)** Every site of `X` has layer index `j` (`1 ≤ j`). -/
theorem localGen_layerIndex_top (hj : j ≤ q) (hj1 : 1 ≤ j)
    (hX : IsCellUnion (L ^ j * M1) (X : Set (Torus d (M1 * N₁ * L ^ q))))
    {x : Torus d (M1 * N₁ * L ^ q)} (hx : x ∈ X) : (minimalGenSet hj X).layerIndex x = j := by
  refine GeneratingSet.layerIndex_eq (minimalGenSet hj X) hj1 hj ?_
  rw [localGen_layer_top X hj hX]; exact hx

/-- **(c)** Every domain `Ω_n(B_j(X))`, `n ≤ j`, is a union of `C_n`-cubes (cells of side
`L ^ n M₁`).  No hypothesis on `X` is needed. -/
theorem localGen_isCellUnion (hj : j ≤ q) {n : ℕ} (hn : n ≤ j) :
    IsCellUnion (L ^ n * M1) ((minimalGenSet hj X).Ω n : Set (Torus d (M1 * N₁ * L ^ q))) := by
  intro x hx y hy
  have hc := (fineCubeIdx_eq_iff_sameCell (le_trans hn hj)).2 hy.symm
  rw [Finset.mem_coe, minimalGenSet_Ω] at hx ⊢
  exact (localGen_mem_minLayer_iff X hc).1 hx

/-- **(c)** `B_j(X)` is cube aligned in the landed sense of `CubeAligned`, for `M₁ = L ^ m₁`,
`2 ≤ m₁`.  No hypothesis on `X` is needed: the divisibility `L ^ m₁ ∣ M₁ N₁` is automatic. -/
theorem localGen_cubeAligned (hj : j ≤ q) {m₁ : ℕ} (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁) :
    CubeAligned (minimalGenSet hj X) m₁ := by
  refine ⟨hm₁, by rw [hM1]; exact Dvd.dvd.mul_right (dvd_refl _) _, ?_⟩
  intro n _ hnq x x' hcell
  have hs : SameCell (L ^ n * M1) x x' := by
    have : L ^ n * M1 = L ^ (n + m₁) := by rw [hM1, pow_add]
    rw [this]; exact hcell
  have hc := (fineCubeIdx_eq_iff_sameCell hnq).2 hs
  exact localGen_mem_minLayer_iff X hc

end Aligned

/-! ### T2: range -/

section Range'

variable {j : ℕ} (X : Finset (Torus d (M1 * N₁ * L ^ q)))

/-- **Range, layer by layer** (`LOCALGEN` (3.1)): the landed `exists_near_of_mem_minLayer` for the
domains of `B_j(X)`. -/
theorem localGen_layer_range (hj : j ≤ q) {n : ℕ} (hnj : n ≤ j)
    {x : Torus d (M1 * N₁ * L ^ q)} (hx : x ∈ (minimalGenSet hj X).Ω n) :
    ∃ y ∈ X, (L - 1) * supDist x y + (5 * L + 1) * (M1 * L ^ n) ≤
      (5 * L + 1) * (M1 * L ^ j) :=
  exists_near_of_mem_minLayer X hj hnj hx

/-- **Uniform envelope** (`LOCALGEN` (3.2)): every data site `Ω₁ ∪ collar` of `B_j(X)` is within
sup-distance `r_j = 11 M₁ L ^ j + 1` of `X`.  This is exactly the landed `dataSites_near`. -/
theorem localGen_dataSites_range (hL : 2 ≤ L) (hj : j ≤ q) {x : Torus d (M1 * N₁ * L ^ q)}
    (hx : x ∈ dataSites (minimalGenSet hj X)) :
    ∃ y ∈ X, supDist x y ≤ 11 * M1 * L ^ j + 1 :=
  dataSites_near X hL hj hx

/-- **Monotonicity of the data sites**: `X ⊆ X'` gives `dataSites B_j(X) ⊆ dataSites B_j(X')`
(from `minimalGenSet_mono`: `Ω₁ ⊆ Ω₁'`, and a collar site of `X` is in `Ω₁'` or in the
collar of `X'`). -/
theorem localGen_dataSites_mono (hj : j ≤ q) {X' : Finset (Torus d (M1 * N₁ * L ^ q))}
    (h : X ⊆ X') : dataSites (minimalGenSet hj X) ⊆ dataSites (minimalGenSet hj X') := by
  intro x hx
  have hΩ : (minimalGenSet hj X).Ω 1 ⊆ (minimalGenSet hj X').Ω 1 := minLayer_mono h 1
  rcases (mem_dataSites _).1 hx with h1 | h1
  · exact (mem_dataSites _).2 (Or.inl (hΩ h1))
  · obtain ⟨-, x0, hx0, hadj⟩ := (mem_collar _).1 h1
    by_cases h2 : x ∈ (minimalGenSet hj X').Ω 1
    · exact (mem_dataSites _).2 (Or.inl h2)
    · exact (mem_dataSites _).2 (Or.inr (mem_collar_of_adj _ (hΩ hx0) h2 hadj))

end Range'

/-! ### T3: locality -/

section Local

variable {j : ℕ} {X X' : Finset (Torus d (M1 * N₁ * L ^ q))}

/-- **Locality on a set** (`ρ_j = 12 M₁ L ^ j`, the radius of the landed `minLayer_local`): if `X`
and `X'` agree within sup-distance `12 M₁ L ^ j` of a set `A`, then `B_j(X)` and `B_j(X')` have the
same domains on `A`. -/
theorem localGen_local (hL : 2 ≤ L) (hj : j ≤ q) {A : Finset (Torus d (M1 * N₁ * L ^ q))}
    (h : ∀ x ∈ A, ∀ y, supDist x y ≤ 12 * M1 * L ^ j → (y ∈ X ↔ y ∈ X'))
    {x : Torus d (M1 * N₁ * L ^ q)} (hx : x ∈ A) (n : ℕ) :
    x ∈ (minimalGenSet hj X).Ω n ↔ x ∈ (minimalGenSet hj X').Ω n := by
  rw [minimalGenSet_Ω, minimalGenSet_Ω]
  by_cases hn : n ≤ j
  · exact minLayer_local X hL hj hn (h x hx)
  · rw [minLayer_of_gt X (by omega), minLayer_of_gt X' (by omega)]

/-- **Locality of the layers** on `A` (same hypothesis as `localGen_local`). -/
theorem localGen_layer_local (hL : 2 ≤ L) (hj : j ≤ q) {A : Finset (Torus d (M1 * N₁ * L ^ q))}
    (h : ∀ x ∈ A, ∀ y, supDist x y ≤ 12 * M1 * L ^ j → (y ∈ X ↔ y ∈ X'))
    {x : Torus d (M1 * N₁ * L ^ q)} (hx : x ∈ A) (n : ℕ) :
    x ∈ (minimalGenSet hj X).layer n ↔ x ∈ (minimalGenSet hj X').layer n := by
  rw [GeneratingSet.mem_layer, GeneratingSet.mem_layer, localGen_local hL hj h hx n,
    localGen_local hL hj h hx (n + 1)]

/-- **Locality of the layer index** on `A` (same hypothesis as `localGen_local`). -/
theorem localGen_layerIndex_local (hL : 2 ≤ L) (hj : j ≤ q)
    {A : Finset (Torus d (M1 * N₁ * L ^ q))}
    (h : ∀ x ∈ A, ∀ y, supDist x y ≤ 12 * M1 * L ^ j → (y ∈ X ↔ y ∈ X'))
    {x : Torus d (M1 * N₁ * L ^ q)} (hx : x ∈ A) :
    (minimalGenSet hj X).layerIndex x = (minimalGenSet hj X').layerIndex x := by
  by_cases h1 : x ∈ (minimalGenSet hj X).Ω 1
  · obtain ⟨n, hn1, hnq, hl⟩ := GeneratingSet.exists_layer _ h1
    rw [GeneratingSet.layerIndex_eq _ hn1 hnq hl,
      GeneratingSet.layerIndex_eq _ hn1 hnq ((localGen_layer_local hL hj h hx n).1 hl)]
  · have h2 : x ∉ (minimalGenSet hj X').Ω 1 := fun h2 => h1 ((localGen_local hL hj h hx 1).2 h2)
    rw [layerIndex_of_not_mem _ h1, layerIndex_of_not_mem _ h2]

end Local

/-! ### T5: covariance under translations of the `C_j` grid -/

section Translate

omit [NeZero L] [NeZero M1] [NeZero N₁] in
theorem blockCoord_add_of_dvd {ℓ P m : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = P * m)
    (x a : ZMod ℓ) (ha : P ∣ a.val) :
    blockCoord P m (x + a) = blockCoord P m x + blockCoord P m a := by
  unfold blockCoord
  have e : (x.val + a.val) % ℓ / P = (x.val + a.val) / P % m := by
    have : (x.val + a.val) % ℓ = (x.val + a.val) % (P * m) := by rw [← hℓ]
    rw [this, Nat.mod_mul_right_div_self]
  rw [ZMod.val_add, e, ZMod.natCast_mod, add_comm x.val a.val,
    Nat.add_div_of_dvd_right ha, Nat.cast_add, add_comm]

/-- The cube index is additive for translations aligned to the grid of the cubes. -/
theorem fineCubeIdx_add {n : ℕ} (hn : n ≤ q) (x a : Torus d (M1 * N₁ * L ^ q))
    (ha : ∀ μ, L ^ n * M1 ∣ (a μ).val) :
    fineCubeIdx M1 N₁ L q n (x + a) = fineCubeIdx M1 N₁ L q n x + fineCubeIdx M1 N₁ L q n a := by
  funext μ
  simp only [fineCubeIdx, blockMap_apply, Pi.add_apply]
  exact blockCoord_add_of_dvd (fine_eq_cube hn) _ _ (ha μ)

omit [NeZero L] [NeZero M1] [NeZero N₁] in
theorem supDist_add_add_right {m : ℕ} [NeZero m] (x y c : Torus d m) :
    supDist (x + c) (y + c) = supDist x y := by
  unfold supDist
  congr 1
  funext i
  rw [Pi.add_apply, Pi.add_apply, add_sub_add_right_eq_sub]

variable {j : ℕ} (a : Torus d (M1 * N₁ * L ^ q))

private theorem translate_aux (ha : ∀ μ, L ^ j * M1 ∣ (a μ).val) (hj : j ≤ q)
    (X : Finset (Torus d (M1 * N₁ * L ^ q))) :
    ∀ (t : ℕ) (x : Torus d (M1 * N₁ * L ^ q)),
      x + a ∈ minLayerAux M1 N₁ L q j (X.map (Equiv.addRight a).toEmbedding) t ↔
        x ∈ minLayerAux M1 N₁ L q j X t := by
  have hmem : ∀ y, y + a ∈ X.map (Equiv.addRight a).toEmbedding ↔ y ∈ X := fun y =>
    Finset.mem_map' (Equiv.addRight a).toEmbedding
  intro t
  induction t with
  | zero =>
    intro x
    show x + a ∈ cubeInterior M1 N₁ L q j _ ↔ x ∈ cubeInterior M1 N₁ L q j X
    rw [mem_cubeInterior, mem_cubeInterior]
    constructor
    · intro H y hy
      have := H (y + a) (by rw [fineCubeIdx_add hj y a ha, fineCubeIdx_add hj x a ha, hy])
      exact (hmem y).1 this
    · intro H y hy
      have e : y = (y - a) + a := by abel
      have h2 : fineCubeIdx M1 N₁ L q j (y - a) = fineCubeIdx M1 N₁ L q j x := by
        have := fineCubeIdx_add (d := d) (M1 := M1) (N₁ := N₁) (L := L) hj (y - a) a ha
        rw [← e, hy, fineCubeIdx_add hj x a ha] at this
        exact (add_right_cancel this).symm
      rw [e]
      exact (hmem _).2 (H _ h2)
  | succ t ih =>
    intro x
    show x + a ∈ nearStep M1 N₁ L q (j - (t + 1)) _ ↔ x ∈ nearStep M1 N₁ L q (j - (t + 1)) _
    have hn : j - (t + 1) ≤ j := Nat.sub_le _ _
    have han : ∀ μ, L ^ (j - (t + 1)) * M1 ∣ (a μ).val := fun μ =>
      (Nat.mul_dvd_mul_right (pow_dvd_pow L hn) M1).trans (ha μ)
    have hnq : j - (t + 1) ≤ q := hn.trans hj
    rw [mem_nearStep, mem_nearStep]
    constructor
    · rintro ⟨y, hy, hd⟩
      refine ⟨y - a, (ih _).1 (by rwa [sub_add_cancel]), ?_⟩
      have e : y = (y - a) + a := by abel
      rw [e, fineCubeIdx_add hnq _ a han, fineCubeIdx_add hnq _ a han,
        supDist_add_add_right] at hd
      exact hd
    · rintro ⟨y, hy, hd⟩
      refine ⟨y + a, (ih y).2 hy, ?_⟩
      rw [fineCubeIdx_add hnq _ a han, fineCubeIdx_add hnq _ a han, supDist_add_add_right]
      exact hd

/-- **Translation covariance** (the "paving covariance" of the class): for a translation by a
vector `a` whose coordinates are multiples of the side `L ^ j M₁` of the `C_j`-cubes, a site
`x + a` lies in the domain `Ω_n` of `B_j(X + a)` iff `x` lies in the domain `Ω_n` of `B_j(X)`. -/
theorem localGen_translate_mem (hj : j ≤ q) (ha : ∀ μ, L ^ j * M1 ∣ (a μ).val)
    (X : Finset (Torus d (M1 * N₁ * L ^ q))) (n : ℕ) (x : Torus d (M1 * N₁ * L ^ q)) :
    x + a ∈ (minimalGenSet hj (X.map (Equiv.addRight a).toEmbedding)).Ω n ↔
      x ∈ (minimalGenSet hj X).Ω n := by
  rw [minimalGenSet_Ω, minimalGenSet_Ω]
  unfold minLayer
  split_ifs
  · exact translate_aux a ha hj X _ x
  · simp

/-- **Translation covariance**, as an equality of domains: `Ω_n(B_j(X + a)) = Ω_n(B_j(X)) + a`.
Reflections and coordinate permutations are not treated: they would need the cube-index map to
commute with the symmetry (a permutation of coordinates does; a reflection `x ↦ c - x` does only
if `c + 1` is a multiple of the cube sides, and then it reverses the order of the indices). -/
theorem localGen_translate_Ω (hj : j ≤ q) (ha : ∀ μ, L ^ j * M1 ∣ (a μ).val)
    (X : Finset (Torus d (M1 * N₁ * L ^ q))) (n : ℕ) :
    (minimalGenSet hj (X.map (Equiv.addRight a).toEmbedding)).Ω n =
      ((minimalGenSet hj X).Ω n).map (Equiv.addRight a).toEmbedding := by
  ext y
  obtain ⟨x, rfl⟩ : ∃ x, y = x + a := ⟨y - a, by abel⟩
  rw [localGen_translate_mem a hj ha X n x]
  exact (Finset.mem_map' (Equiv.addRight a).toEmbedding).symm

end Translate

end Balaban.LargeField
