module

public import Balaban.LargeField.R.WindowOfHistory
public import Balaban.LargeField.R.WindowCollarGeom
import Mathlib.Tactic.Linarith

/-!
# The regularity set of the actual window (COLLAR-FIX §2, inner face; Definition II.5.6)

Survey (T0).  At the step `k₁ - 1 → k₁` of the localized history of a ripe component `Z`
(`H.locRH k Z`, a region history without removals), Definition II.5.6 puts

* `χ_{k₁}(Ω^{∼-3}_{k₁} ∩ Z_{k₁})` on the cubes of `regDeep`, and
* `χ'_{k₁}(Ω_{k₁} ∩ (Ω^c_{k₁})^{∼3} ∩ Z_{k₁})` on the cubes of `regBand`.

Here `Ω_{k₁}` is `((H.locRH k Z).step (k₁ - 1)).Omega` (a set of `π_{k₁}`-cubes; the step `i` of the
history ends at scale `i + 1`) and `Z_{k₁} = ((H.locRH k Z).step k₁).Z`.  The landed history records
`Ω` and `Z` but not the interface band as a set, so `regDeep`/`regBand` are defined here from the
formula of the definition (`nbhdNeg 3 = (·^c)^{∼3}` complemented, `nbhd 3`).  The generating-set layers
of the window are read from them by `mem_locGen_succ` (`x ∈ Ω_{i+1}(𝔹_k) ↔ cube ∈ (step i).Omega`).

* `regCubes_eq`: the union of the two supports is `Ω_{k₁} ∩ Z_{k₁}`;
* `regSetT`: the set of `k₁`-blocks whose cube lies in `regCubes` (the regularity set `T`);
* `regSetTExt`: `T` together with the blocks adjacent to it (the exit blocks of the paths);
* `windowOfHistory_hcT_layers`, `windowOfHistory_hwT_layers`: the cube incidences `hcT`, `hwT` stated on
  the layer formula `(core.Ω₁ ∩ Z_{k₁}) ∪ (B.Ω₁ ∩ (Z ∖ Z_{k₁})) ∪ (bdry.Ω₁ ∩ (U^∼ ∖ Z))` of
  Definition III.2.1 (not through `WindowPieces.Hyp`, which is false for this window).

The landed `hwT` is too strong as printed (it has no adjacency to `Z_{k₁}`; and a window block lies off
`Z_{k₁}`, hence off the supports of `χ`, `χ'`, which only act on cubes of `Z_{k₁}`): the correct form is
`windowOfHistory_hwT_layers`, with the exit blocks in `regSetTExt`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Finset

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) {k : ℕ} (Z : H.Comp k)

/-- `Ω_q` of the localized history of `Z`, as a set of `π_q`-cubes: `Ω_{i+1} = (step i).Omega`
(the step `i → i + 1`); `Ω_0 = ∅`. -/
def regOmega : (q : ℕ) → Set (Torus S.d (n q))
  | 0 => ∅
  | i + 1 => ((H.locRH k Z).step i).Omega

/-- `Z_q` of the localized history of `Z`, as a set of `π_q`-cubes. -/
def regZ (q : ℕ) : Set (Torus S.d (n q)) := ((H.locRH k Z).step q).Z

/-- The cubes of `Ω^{∼-3}_q ∩ Z_q` on which `χ_q` acts at the step `q - 1 → q`
(LF-RECONSTRUCTION Definition II.5.6; `Ω^{∼-3} = ((Ω^c)^{∼3})^c`, P6 p. 4). -/
def regDeep (q : ℕ) : Set (Torus S.d (n q)) := regZ H Z q ∩ nbhdNeg 3 (regOmega H Z q)

/-- The cubes of `Ω_q ∩ (Ω^c_q)^{∼3} ∩ Z_q` on which `χ'_q` acts at the step `q - 1 → q`
(LF-RECONSTRUCTION Definition II.5.6, second factor of `K^q`). -/
def regBand (q : ℕ) : Set (Torus S.d (n q)) :=
  regZ H Z q ∩ regOmega H Z q ∩ nbhd 3 (regOmega H Z q)ᶜ

/-- The union of the supports of the retained characteristic functions at the step `q - 1 → q`. -/
def regCubes (q : ℕ) : Set (Torus S.d (n q)) := regDeep H Z q ∪ regBand H Z q

/-- **The two supports cover exactly `Ω_q ∩ Z_q`** (Definition II.5.6). -/
theorem regCubes_eq (q : ℕ) : regCubes H Z q = regZ H Z q ∩ regOmega H Z q := by
  ext y
  simp only [regCubes, regDeep, regBand, Set.mem_union, Set.mem_inter_iff, nbhdNeg,
    Set.mem_compl_iff]
  constructor
  · rintro (⟨hz, hn⟩ | ⟨⟨hz, ho⟩, -⟩)
    · refine ⟨hz, ?_⟩
      by_contra hO
      exact hn (subset_nbhd _ _ hO)
    · exact ⟨hz, ho⟩
  · rintro ⟨hz, ho⟩
    by_cases h3 : y ∈ nbhd 3 (regOmega H Z q)ᶜ
    · exact Or.inr ⟨⟨hz, ho⟩, h3⟩
    · exact Or.inl ⟨hz, h3⟩

variable {M : ℕ} [NeZero M] [NeZero S.L]

/-- **The regularity set `T`** (COLLAR-FIX §2): the `q`-blocks of the level-`k` fine torus contained
in the supports of the retained characteristic functions `χ_q`, `χ'_q` of the step `q - 1 → q`. -/
def regSetT (M q : ℕ) [NeZero M] : Set (BlockAt S n M k q) :=
  {b | blockCube S n M k q b ∈ regCubes H Z q}

/-- `T` together with the `q`-blocks adjacent to it: the blocks a path of `T` may exit to
(the first window block, off `Z_q`). -/
def regSetTExt (M q : ℕ) [NeZero M] : Set (BlockAt S n M k q) :=
  {b | ∃ b' ∈ regSetT H Z M q, b = b' ∨ AdjT b' b}

theorem regSetT_subset_ext (M q : ℕ) [NeZero M] : regSetT H Z M q ⊆ regSetTExt H Z M q :=
  fun b hb => ⟨b, hb, Or.inl rfl⟩

theorem mem_regSetT {q : ℕ} {b : BlockAt S n M k q} :
    b ∈ regSetT H Z M q ↔ blockCube S n M k q b ∈ regCubes H Z q := Iff.rfl

/-- A site of `Z_q` lying in `Ω_q(𝔹_k)` has its `q`-block in `T`. -/
theorem jBlock_mem_regSetT (hkK : k ≤ K) {q : ℕ} (hq1 : 1 ≤ q) (hqk : q ≤ k)
    {hL : 2 ≤ S.L} {hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j}
    {x : Torus S.d (M * n k * S.L ^ k)} (hxZ : x ∈ H.locFine Z M q)
    (hxO : x ∈ (H.locGen Z M hkK hL hR).Ω q) :
    jBlock S.d S.L (M * n k) k q x ∈ regSetT H Z M q := by
  have hnn : ∀ i, i < k → n i = S.L * n (i + 1) := fun i hi => H.F.hnn i (lt_of_lt_of_le hi hkK)
  rw [mem_regSetT, cubeMap_jBlock hnn hqk, regCubes_eq]
  refine ⟨hxZ, ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, q = i + 1 := ⟨q - 1, by omega⟩
  exact (mem_locGen_succ (hkK := hkK) (hL := hL) (hR := hR) (Z := Z) (M := M) (by omega)).1 hxO

section Window

variable {H Z} {g : Geo S n R M} (hkK : k ≤ K) (hW : H.RipeWindow k Z)

/-- **`hcT`** (COLLAR-FIX §2, inner face; Definition II.5.6): a site `c` of `Z_{k₁}` adjacent to a site of
the window generating set (stated on the layer formula `(core.Ω₁ ∩ Z_{k₁}) ∪ (𝔹_k.Ω₁ ∩ (Z ∖ Z_{k₁})) ∪
(𝔹_k(U_k).Ω₁ ∩ (U^∼_k ∖ Z))` of Definition III.2.1, so for the actual window and without
`WindowPieces.Hyp`) has its `k₁`-block in the regularity set `regSetT`.  Since the collar of the window
generating set is the set of sites off `Ω₁(G)` adjacent to `Ω₁(G)`, this is `hcT` of
`inner_collar_in_regular_T` (`collarIn`).  Source: the margin of Lemma III.4.6
(`windowOfHistory_hmargin_layers`: `c ∈ Ω_{k₁}(𝔹_k)`), `c ∈ Z_{k₁}`, and `regCubes_eq`. -/
theorem windowOfHistory_hcT_layers :
    ∀ x ∈ ((windowOfHistory H Z g hkK hW).core.Ω 1 ∩ (windowOfHistory H Z g hkK hW).Zk1) ∪
        ((windowOfHistory H Z g hkK hW).full.Ω 1 ∩
          ((windowOfHistory H Z g hkK hW).Z \ (windowOfHistory H Z g hkK hW).Zk1)) ∪
        ((windowOfHistory H Z g hkK hW).bdry.Ω 1 ∩
          ((windowOfHistory H Z g hkK hW).Unb \ (windowOfHistory H Z g hkK hW).Z)),
      ∀ c, Adj x c → c ∈ (windowOfHistory H Z g hkK hW).Zk1 →
        jBlock S.d S.L (M * n k) k (S.k1 k) c ∈ regSetT H Z M (S.k1 k) := by
  intro x hx c hadj hcZ
  have hΩ := windowOfHistory_hmargin_layers (g := g) hkK hW x hx c hadj
  rw [windowOfHistory_full_Ω] at hΩ
  rw [windowOfHistory_Zk1, mem_locFineFin] at hcZ
  exact jBlock_mem_regSetT H Z hkK (hW.k1_pos hkK) (k1_le hW) (hL := H.F.ok.two_le_L)
    (hR := fun j _ _ => g.hRlow j) hcZ hΩ

/-- **`hwT`, corrected form** (COLLAR-FIX §2; Definition II.5.6): a site `x` of `Ω₁(G)` off `Z_{k₁}`
adjacent to a site `c` of `Z_{k₁}` has its `k₁`-block in `regSetTExt`, the `k₁`-blocks of the supports
and the blocks adjacent to them.  The block of `x` itself is not in `regSetT` (it lies off `Z_{k₁}`),
and the landed `hwT` carries no adjacency to `Z_{k₁}`; both are corrected here. -/
theorem windowOfHistory_hwT_layers :
    ∀ x ∈ ((windowOfHistory H Z g hkK hW).core.Ω 1 ∩ (windowOfHistory H Z g hkK hW).Zk1) ∪
        ((windowOfHistory H Z g hkK hW).full.Ω 1 ∩
          ((windowOfHistory H Z g hkK hW).Z \ (windowOfHistory H Z g hkK hW).Zk1)) ∪
        ((windowOfHistory H Z g hkK hW).bdry.Ω 1 ∩
          ((windowOfHistory H Z g hkK hW).Unb \ (windowOfHistory H Z g hkK hW).Z)),
      ∀ c, Adj x c → c ∈ (windowOfHistory H Z g hkK hW).Zk1 →
        jBlock S.d S.L (M * n k) k (S.k1 k) x ∈ regSetTExt H Z M (S.k1 k) := by
  intro x hx c hadj hcZ
  have hT := windowOfHistory_hcT_layers (g := g) hkK hW x hx c hadj hcZ
  refine ⟨_, hT, ?_⟩
  rcases jBlock_eq_or_adjT (k1_le hW) hadj with h | h
  · exact Or.inl h
  · exact Or.inr (adjT_symm' h)

/-- The top layer of the core piece `𝔹_{k₁}(W)` is `k₁`: `Ω_{k₁+1}(core) = ∅`. -/
theorem windowCore_not_mem_succ (q : ℕ) (hqk : q ≤ k) (x : Torus S.d (M * n k * S.L ^ k)) :
    x ∉ (windowCore H Z g q hqk).Ω (q + 1) := by
  intro hx
  have : torusCast (by rw [geo_base_eq g]) x ∈
      minLayer g.M1 (g.c * n k) S.L k q (fineMin g q (coreW H Z q)) (q + 1) :=
    (castN_mem (geo_base_eq g) _ (q + 1) x).1 hx
  rw [minLayer_of_gt _ (by omega)] at this
  exact Finset.notMem_empty _ this

/-- **Classification of `hcoreTop`** for the actual window: since the core piece has no layer above `k₁`,
`hcoreTop` (every site of `Z_{k₁} ∩ Ω₁(core)` is in the layer `k₁` of the core) says exactly that every
site of `Z_{k₁} ∩ Ω₁(core)` is in `Ω_{k₁}(core)`. -/
theorem windowOfHistory_hcoreTop_iff :
    (∀ x ∈ (windowOfHistory H Z g hkK hW).Zk1, x ∈ (windowOfHistory H Z g hkK hW).core.Ω 1 →
        x ∈ (windowOfHistory H Z g hkK hW).core.layer (S.k1 k)) ↔
      ∀ x ∈ (windowOfHistory H Z g hkK hW).Zk1, x ∈ (windowOfHistory H Z g hkK hW).core.Ω 1 →
        x ∈ (windowOfHistory H Z g hkK hW).core.Ω (S.k1 k) := by
  refine forall₂_congr fun x hx => imp_congr_right fun h1 => ?_
  rw [GeneratingSet.mem_layer]
  exact ⟨fun h => h.1, fun h => ⟨h, windowCore_not_mem_succ (g := g) _ (k1_le hW) x⟩⟩

/-- `hcoreTop` fails for the actual window as soon as `Z_{k₁}` contains a site of `Ω₁(core)` outside
`Ω_{k₁}(core)` (a lower layer of the core inside `Z_{k₁}`); this is the situation of the padding of the
minimal generating set (Lemma II.2.3 (c)) around `W = (Z_{k₁}ᶜ)^{≈2}`. -/
theorem windowOfHistory_not_hcoreTop_of_lower {x : Torus S.d (M * n k * S.L ^ k)}
    (hx : x ∈ (windowOfHistory H Z g hkK hW).Zk1)
    (h1 : x ∈ (windowOfHistory H Z g hkK hW).core.Ω 1)
    (hn : x ∉ (windowOfHistory H Z g hkK hW).core.Ω (S.k1 k)) :
    ¬ ∀ x ∈ (windowOfHistory H Z g hkK hW).Zk1, x ∈ (windowOfHistory H Z g hkK hW).core.Ω 1 →
        x ∈ (windowOfHistory H Z g hkK hW).core.layer (S.k1 k) :=
  fun h => hn (((GeneratingSet.mem_layer _).1 (h x hx h1)).1)

end Window

end RegionHistory

end Balaban.LargeField
