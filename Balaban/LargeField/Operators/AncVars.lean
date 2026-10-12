module

public import Balaban.LargeField.Operators.Setup
public import Balaban.LargeField.Operators.Kernel
public import Balaban.LargeField.Operators.Ancestors
public import Balaban.LargeField.Region.Lineage

/-!
# Operator packages and the variables of the ancestors (Part II, Definition II.5.8, (II.3))

* `OpPkg`: an operator of a localized history at level `k`: the integrated variables `A`, the
  kernel `(K, b)` and the domain on which the kernel can be non-zero;
* the geometry of the lineage (`Vsites_anc`, Lemma I.3.15) and the inclusion
  `I(Y, 𝔞|_Y) ⊆ I(Z', 𝔞)` of the variables of an old part (`ancInc`, `ancRestrict`, `ancOut`);
* `preVars`: the variables integrated by the pre-operator.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section LocOp

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- An operator of a localized history at level `k`: the set `A` of internal variables it
integrates, its kernel `(K, b)`, and its domain (on which the kernel can be non-zero). -/
structure OpPkg (N : ℕ) (R : ℕ → ℝ) (a : LocalHistory S n M K) (k : ℕ) where
  /-- the internal variables integrated by the operator -/
  A : Set (InternalVars a k)
  /-- the kernel `(K, b)` -/
  T : LFKernel (OutT N R a k) (SubCfg N a k A) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N)
  /-- the domain: the kernel vanishes off it -/
  dom : OutT N R a k → SubCfg N a k A → Prop
  vanish : ∀ o x hv, ¬ dom o x → T.K o x hv = 0

/-! ### The geometry of the lineage -/

section Geometry

variable {H : RegionHistory S n R k0 K}

/-- Every cube of `𝕋_k` is the cube of a site of the fine torus (`k ≤ K`). -/
theorem exists_site_of_cube (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K)
    (y : Torus S.d (n k)) : ∃ x : Torus S.d (M * n K * S.L ^ K), cubeMap n S.L M K k x = y := by
  have hℓ : M * n K * S.L ^ K = (S.L ^ k * M) * n k := fine_eq hnn hkK
  have hc := card_blockFibre (d := S.d) (ℓ := M * n K * S.L ^ K) (N := S.L ^ k * M) (m := n k)
    hℓ y
  have hpos' : 0 < (blockFibre (S.L ^ k * M) (n k) y :
      Finset (Torus S.d (M * n K * S.L ^ K))).card := by
    rw [hc]
    have := NeZero.ne S.L
    have := NeZero.ne M
    positivity
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos'
  exact ⟨x, mem_blockFibre.mp hx⟩

/-- The cubes of `Z_k` of the localized history of `Y` lie in `Y`. -/
theorem Zcubes_loc_sub {k : ℕ} (hkK : k ≤ K) (Y : H.Comp k) :
    Zcubes (H.localHistory M K k Y) k ⊆ (Y.1 : Set (Torus S.d (n k))) := by
  intro y hy
  obtain ⟨x, hx⟩ := exists_site_of_cube (M := M) H.F.hnn hkK y
  have h := hy x hx
  have h2 : cubeMap n S.L M K k x ∈ (Y.1 : Set (Torus S.d (n k))) := h.2
  rwa [hx] at h2

/-- The component `Z'` lies in the cubes of `Z_{k+1}` of its localized history. -/
theorem Zcubes_loc_top {k : ℕ} (hkK : k ≤ K) (Z : H.Comp k) :
    (Z.1 : Set (Torus S.d (n k))) ⊆ Zcubes (H.localHistory M K k Z) k := by
  intro y hy x hx
  refine ⟨?_, ?_⟩
  · show cubeMap n S.L M K k x ∈ ((H.locRH k Z).step k).Z
    rw [locRH_Z Z le_rfl hkK, lin_self, hx]
    exact hy
  · show cubeMap n S.L M K k x ∈ (Z.1 : Set (Torus S.d (n k)))
    rw [hx]; exact hy

theorem thick_mono' {m : ℕ} [NeZero m] (r : ℕ) {X Y : Set (Torus S.d m)} (h : X ⊆ Y) :
    thick r X ⊆ thick r Y := nbhd_mono le_rfl h

/-- **Lemma I.3.15**: `V_Y ⊆ V_{Z'}` for an old part `Y` of `Z'`, on fine sites. -/
theorem Vsites_anc (geo : Geo S n R M) {k : ℕ} (hK : k + 1 ≤ K) {Y : H.Comp k}
    {Z' : H.Comp (k + 1)} (hY : Y ∈ H.parts k Z') :
    Vsites R (H.localHistory M K k Y) k ⊆ Vsites R (H.localHistory M K (k + 1) Z') (k + 1) := by
  intro x hx
  obtain ⟨hrem, hs⟩ := (H.mem_parts k Y Z').mp hY
  have hL : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne _)
  have hYY : blockMap S.L (n (k + 1)) '' Zcubes (H.localHistory M K k Y) k ⊆
      (Z'.1 : Set (Torus S.d (n (k + 1)))) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hs ⟨y, Zcubes_loc_sub (by omega) Y hy, rfl⟩
  have h1 := thick_nbhd_coarsen (H.F.hnn k (by omega)) hL (geo.hRmono k) hYY hx
  rw [cubeMap_succ H.F.hnn hK] at h1
  have hdiv : (1 + S.L - 1) / S.L ≤ 1 := by
    rw [show 1 + S.L - 1 = S.L by omega, Nat.div_self hL]
  exact nbhd_mono hdiv (thick_mono' _ (Zcubes_loc_top hK Z')) h1

end Geometry

/-! ### The variables of the ancestors inside those of the component -/

section Anc

variable {H : RegionHistory S n R k0 K}

theorem ancInc_mem {k : ℕ} (hK : k + 1 ≤ K) {Y : H.Comp k} {Z' : H.Comp (k + 1)}
    (hY : Y ∈ H.parts k Z') (p : InternalVars (H.localHistory M K k Y) k) :
    BlockSub (S := S) (n := n) (M := M) (K := K) (↑(Fin.castSucc p.1.1)) p.1.2.2
      (varSet (H.localHistory M K (k + 1) Z') (↑(Fin.castSucc p.1.1)) p.1.2.1) :=
  fun x hx => varSet_mono hK hY p.1.1.2 p.1.2.1 (p.2 x hx)

/-- The internal variable of the component `Z'` that is the variable `p` of its old part
(`j < k` is also `< k + 1`). -/
def ancInc {k : ℕ} (hK : k + 1 ≤ K) {Y : H.Comp k} {Z' : H.Comp (k + 1)} (hY : Y ∈ H.parts k Z')
    (p : InternalVars (H.localHistory M K k Y) k) :
    InternalVars (H.localHistory M K (k + 1) Z') (k + 1) :=
  ⟨⟨Fin.castSucc p.1.1, p.1.2.1, p.1.2.2⟩, ancInc_mem hK hY p⟩

theorem isSpin_ancInc {k : ℕ} (hK : k + 1 ≤ K) {Y : H.Comp k} {Z' : H.Comp (k + 1)}
    (hY : Y ∈ H.parts k Z') (p : InternalVars (H.localHistory M K k Y) k) :
    (ancInc hK hY p).isSpin = p.isSpin := rfl

/-- The restriction of a configuration of the variables `A'` of `Z'` to those of its old part
`Y`, given that the variables `A_Y` of `Y` are among `A'`. -/
def ancRestrict {k : ℕ} (hK : k + 1 ≤ K) {Y : H.Comp k} {Z' : H.Comp (k + 1)}
    (hY : Y ∈ H.parts k Z') {AY : Set (InternalVars (H.localHistory M K k Y) k)}
    {A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
    (hA : ∀ p ∈ AY, ancInc hK hY p ∈ A') (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A') :
    SubCfg N (H.localHistory M K k Y) k AY :=
  fun p => x ⟨ancInc hK hY p.1, hA p.1 p.2⟩

theorem measurable_ancRestrict {k : ℕ} (hK : k + 1 ≤ K) {Y : H.Comp k} {Z' : H.Comp (k + 1)}
    (hY : Y ∈ H.parts k Z') {AY : Set (InternalVars (H.localHistory M K k Y) k)}
    {A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
    (hA : ∀ p ∈ AY, ancInc hK hY p ∈ A') :
    Measurable (ancRestrict (N := N) hK hY hA) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- The output of the old part `Y`: the large-field variable `ψ_k` of `Z'` on the blocks of `V_Y`. -/
noncomputable def ancOut {k : ℕ} (Y : H.Comp k) (Z' : H.Comp (k + 1))
    {A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A') :
    OutT N R (H.localHistory M K k Y) k :=
  fun y => subVarField N x k y.1

theorem measurable_ancOut {k : ℕ} (Y : H.Comp k) (Z' : H.Comp (k + 1))
    (A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))) :
    Measurable (ancOut (N := N) (R := R) Y Z' (A' := A')) :=
  Measurable.of_eval fun y => measurable_subVarField k y.1

/-- Restriction of a configuration of `A'` to the new variables. -/
def newRestrict {k : ℕ} (a : LocalHistory S n M K) {A' : Set (InternalVars a (k + 1))}
    (h : newVars a k ⊆ A') (x : SubCfg N a (k + 1) A') : NewCfg N a k :=
  restrictSub h x

theorem measurable_newRestrict {k : ℕ} (a : LocalHistory S n M K) {A' : Set (InternalVars a (k + 1))}
    (h : newVars a k ⊆ A') : Measurable (newRestrict (N := N) a h) :=
  measurable_restrictSub h

end Anc

section PreVars

variable {H : RegionHistory S n R k0 K}

/-- The variables integrated by the pre-operator of `Z'`: the new variables and the variables of
the operators of the old parts. -/
def preVars {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k) :
    Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1)) :=
  {p | p ∈ newVars (H.localHistory M K (k + 1) Z') k ∨
    ∃ (Y : H.Comp k) (hY : Y ∈ H.parts k Z') (q : InternalVars (H.localHistory M K k Y) k),
      q ∈ (sub Y hY).A ∧ ancInc hK hY q = p}

theorem preVars_new {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k) :
    newVars (H.localHistory M K (k + 1) Z') k ⊆ preVars hK Z' sub :=
  fun _ hp => Or.inl hp

theorem preVars_anc {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (Y : H.Comp k) (hY : Y ∈ H.parts k Z') :
    ∀ p ∈ (sub Y hY).A, ancInc hK hY p ∈ preVars hK Z' sub :=
  fun p hp => Or.inr ⟨Y, hY, p, hp, rfl⟩

end PreVars

end LocOp

end Balaban.LargeField
