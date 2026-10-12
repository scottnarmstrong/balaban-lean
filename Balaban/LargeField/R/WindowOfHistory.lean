module

public import Balaban.LargeField.R.WindowGenGlue
public import Balaban.LargeField.R.ChainSetting
public import Balaban.LargeField.R.GainPos
public import Balaban.LargeField.Operators.Setup
public import Balaban.LargeField.Characteristic.Analytic
public import Balaban.LargeField.Background.MinimalGenSet
public import Balaban.LargeField.Background.CubeUnion
public import Balaban.Localization.P6PairOp

/-!
# The window pieces of a ripe component (Part III, Definition III.2.1, Lemma III.1.2)

`windowOfHistory H Z g hkK hW` is the `WindowPieces` of a ripe component `Z` of scale `k`
(`hW : H.RipeWindow k Z`, `g : Geo S n R M` the typing `M = c M₁`, `c ≥ 14`), built from the history
objects of LF-RECONSTRUCTION §III.0.2 and Definition III.2.1:

| field | source object |
|---|---|
| `full` | `𝔹_k`, the localized generating set `H.locGen Z M …` (Lemma I.3.10) |
| `core` | `𝔹_{k₁}(W)`, the minimal generating set (Definition II.2.2) of the fine set of `W = (Z_{k₁}ᶜ)^{≈2}` at scale `k₁` (`≈` adds `⌊R_{k₁-1}⌋ + 1`) |
| `bdry` | `𝔹_k(U_k)`, the minimal generating set of the fine set of `U_k = Z^≈` at scale `k` (`≈` adds `⌊R_{k-1}⌋ + 1`) |
| `Zk1` | the fine set of `Z_{k₁} = Lin_{k₁}(Z)` (`H.locFine Z M k₁`) |
| `Z` | the fine set of `Z = Z_k` (`H.locFine Z M k`) |
| `Unb` | the fine set of `U_k^∼ = (Z^≈)^{∼1}` |

The three generating sets live on the common torus `Torus d (M n_k L^k)`; the minimal ones are built on
`Torus d (M₁ (c n_k) L^k)` (`M = c M₁`) and transported by `GeneratingSet.castN`.  The separation
constants are `L M R_base` (`𝔹_k`) and `5 L M₁` (minimal sets); the common constant of the structure
is the smaller, `winSep`.

Derived premises of `WindowCollarGeom` / `DeltaPsiCollar` (each for `W = windowOfHistory H Z g hkK hW`):
`windowOfHistory_hZ`, `_hOmK1`, `_hOmK`, `_hZk1top` (Lemma III.1.2 (f), from `compl_Omega_subset`,
`locFine_mono`, `locFine_not_mem_Omega`), `_hsupp` (range of the minimal sets, Lemma II.2.3 (c)),
`_hbdry`, `_hcore` (Lemma I.3.5 (g) through `coreW_nbhd_subset_Omega`), `_hmargin_layers`/`_hmargin`
(Lemma III.4.6 margin), `_hexitLayer` (Lemma I.3.5 (f)).

`windowOfHistory_not_hyp_of_boundary_pair`: `W.Hyp` itself is false for this window (its margin clause
for the core piece contradicts the fact that `𝔹_{k₁}(W)` fills the collar of `Z_{k₁}`), so
`windowOfHistory_hmargin` (stated with `hWh : W.Hyp`) is vacuous; the form
`windowOfHistory_hmargin_layers` is stated on the layer formula of Definition III.2.1 and does not use `Hyp`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Finset

section Relax

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-- A generating set with separation `ϱ` is one with any smaller separation `ϱ'`. -/
def _root_.Balaban.Multiscale.GeneratingSet.relax (G : GeneratingSet d L N₀ k ϱ) (h : ϱ' ≤ ϱ) :
    GeneratingSet d L N₀ k ϱ' where
  Ω := G.Ω
  top := G.top
  subset := G.subset
  blockUnion := G.blockUnion
  separation := fun j hj1 hjk x hx y hy =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right h (by positivity)) (G.separation j hj1 hjk x hx y hy)

@[simp] theorem _root_.Balaban.Multiscale.GeneratingSet.relax_Ω (G : GeneratingSet d L N₀ k ϱ)
    (h : ϱ' ≤ ϱ) (j : ℕ) : (G.relax h).Ω j = G.Ω j := rfl

theorem castN_mem {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (h : N₀ = N₀')
    (G : GeneratingSet d L N₀ k ϱ) (j : ℕ) (x : Torus d (N₀' * L ^ k)) :
    x ∈ (GeneratingSet.castN h G).Ω j ↔
      torusCast (by rw [h]) x ∈ G.Ω j := by
  subst h
  rfl

end Relax

namespace WindowPieces

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The margin clause of `WindowPieces.Hyp` fails as soon as the core piece contains a site `y` of
`Z_{k₁}` within `ϱ L^n` of a site `x` off `Z_{k₁}` (`1 ≤ n < k`, `y ∈ Ω_{n+1}(core)`). -/
theorem not_hyp_of_core_near (W : WindowPieces d L N₀ k ϱ) {n : ℕ} (hn1 : 1 ≤ n) (hnk : n < k)
    {x y : Torus d (N₀ * L ^ k)} (hy : y ∈ W.core.Ω (n + 1)) (hyZ : y ∈ W.Zk1) (hx : x ∉ W.Zk1)
    (hd : Green.torusDist d (N₀ * L ^ k) x y ≤ ϱ * (L : ℝ) ^ n) : ¬ W.Hyp := by
  intro h
  have := h.margin 0 n hn1 hnk y (by simpa [pieces] using hy) (by simpa [pieces] using hyZ) x
    (by simpa [pieces] using hx)
  linarith

end WindowPieces

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) {k : ℕ} (Z : H.Comp k) {M : ℕ} [NeZero M] [NeZero S.L]
  (g : Geo S n R M)

open Classical in
/-- The fine set (a finset of the level-`k` torus) of the region `Z_j = Lin_j(Z)` of the localization. -/
noncomputable def locFineFin (j : ℕ) : Finset (Torus S.d (M * n k * S.L ^ k)) :=
  Finset.univ.filter fun x => x ∈ H.locFine Z M j

theorem mem_locFineFin {j : ℕ} {x : Torus S.d (M * n k * S.L ^ k)} :
    x ∈ H.locFineFin Z j ↔ x ∈ H.locFine Z M j := by
  classical
  simp [locFineFin]

/-- The torus sizes agree: `M₁ (c n_k) = M n_k`. -/
theorem geo_base_eq : g.M1 * (g.c * n k) = M * n k := by
  have h := g.hM
  calc g.M1 * (g.c * n k) = (g.c * g.M1) * n k := by ring
    _ = M * n k := by rw [← h]

/-- The common separation constant of the three pieces: `min {L M R_base, 5 L M₁}`. -/
noncomputable def winSep : ℝ := min ((S.L : ℝ) * M * S.Rb) (minSep S.L g.M1)

/-- The coarse set `W = (Z_{k₁}ᶜ)^{≈2}` of the core, at scale `k₁` (`≈` adds `⌊R_{k₁-1}⌋ + 1`),
for the localized region `Z_{k₁} = Lin_{k₁}(Z)` (LF-RECONSTRUCTION §III.0.2). -/
def coreW (q : ℕ) : Set (Torus S.d (n q)) :=
  thick2 ⌊R (q - 1)⌋₊ (((H.locRH k Z).step q).Z)ᶜ

/-- The coarse set `U_k = Z^≈` of the boundary piece, at scale `k` (`≈` adds `⌊R_{k-1}⌋ + 1`). -/
def bdryU : Set (Torus S.d (n k)) := thick ⌊R (k - 1)⌋₊ (Z.1 : Set (Torus S.d (n k)))

/-- The coarse set `U_k^∼` (the one-neighbourhood of `U_k`). -/
def bdryUnb : Set (Torus S.d (n k)) := nbhd 1 (bdryU H Z)

/-- The fine set of a set of `π_j`-cubes, on the level-`k` torus `Torus d (M n_k L^k)`. -/
noncomputable def fineFin (j : ℕ) (A : Set (Torus S.d (n j))) :
    Finset (Torus S.d (M * n k * S.L ^ k)) := by
  classical
  exact Finset.univ.filter fun x => cubeMap n S.L M k j x ∈ A

theorem mem_fineFin {j : ℕ} {A : Set (Torus S.d (n j))} {x : Torus S.d (M * n k * S.L ^ k)} :
    x ∈ fineFin (k := k) (M := M) j A ↔ cubeMap n S.L M k j x ∈ A := by
  classical
  simp [fineFin]

/-- The fine set of `A` on the minimal-generating-set torus `Torus d (M₁ (c n_k) L^k)`: the sites in
the `π_j`-cubes (side `L^j (c M₁)`) of `A`. -/
noncomputable def fineMin (j : ℕ) (A : Set (Torus S.d (n j))) :
    Finset (Torus S.d (g.M1 * (g.c * n k) * S.L ^ k)) :=
  cubePre g.M1 (g.c * n k) S.L k (S.L ^ j * (g.c * g.M1)) (n j) A

/-- The core piece `𝔹_q(W_q)` (Definition III.2.1 with `q = k₁`), on the level-`k` torus `Torus d (M n_k L^k)`. -/
noncomputable def windowCore (q : ℕ) (hqk : q ≤ k) :
    GeneratingSet S.d S.L (M * n k) k (winSep g) :=
  GeneratingSet.castN (geo_base_eq g)
    ((minimalGenSet (M1 := g.M1) (N₁ := g.c * n k) hqk
      (fineMin g q (coreW H Z q))).relax (min_le_right _ _))

/-- The boundary piece `𝔹_k(U_k)` (Definition III.2.1), on the level-`k` torus. -/
noncomputable def windowBdry :
    GeneratingSet S.d S.L (M * n k) k (winSep g) :=
  GeneratingSet.castN (geo_base_eq g)
    ((minimalGenSet (M1 := g.M1) (N₁ := g.c * n k) (le_refl k)
      (fineMin (k := k) g k (bdryU H Z))).relax (min_le_right _ _))

/-- The full piece `𝔹_k`, the localized generating set (Lemma I.3.10). -/
noncomputable def windowFull (hkK : k ≤ K) :
    GeneratingSet S.d S.L (M * n k) k (winSep g) :=
  (H.locGen Z M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j)).relax (min_le_left _ _)

/-- **Definition III.2.1 / LF-RECONSTRUCTION §III.0.2**: the window pieces of a ripe component `Z`
of scale `k` (`core scale k₁ = S.k1 k`). -/
noncomputable def windowOfHistory (hkK : k ≤ K) (hW : H.RipeWindow k Z) :
    WindowPieces S.d S.L (M * n k) k (winSep g) where
  core := windowCore H Z g (S.k1 k) (by have := hW.core_window.1; rw [hW.core_k1]; omega)
  full := windowFull H Z g hkK
  bdry := windowBdry H Z g
  Zk1 := H.locFineFin Z (S.k1 k)
  Z := H.locFineFin Z k
  Unb := fineFin (k := k) (M := M) k (bdryUnb H Z)

section Range

variable {H Z g}

theorem blockMap_torusCast {d a b N N' m : ℕ} (h : a = b) (hN : N = N') (x : Torus d a) :
    blockMap N' m (torusCast h x) = blockMap N m x := by
  subst h; subst hN; rfl

/-- The `π_q`-cube of a fine site, read on the minimal-generating-set torus. -/
theorem cubeMap_eq_castBlock (q : ℕ) (x : Torus S.d (M * n k * S.L ^ k)) :
    cubeMap n S.L M k q x =
      blockMap (S.L ^ q * (g.c * g.M1)) (n q)
        (torusCast (by rw [geo_base_eq g] : M * n k * S.L ^ k = g.M1 * (g.c * n k) * S.L ^ k) x) := by
  have hN : S.L ^ q * M = S.L ^ q * (g.c * g.M1) := congrArg _ g.hM
  exact (blockMap_torusCast _ hN x).symm

/-- The range of a minimal generating set, on the history torus: every site of `Ω_1(𝔹_q(A))` lies in a
`π_q`-cube equal or adjacent to a cube of `A` (Lemma II.2.3 (c), with `M = c M₁`, `c ≥ 14`). -/
theorem cubeMap_nbhd_of_mem_cast (hL : 2 ≤ S.L) (hnn : ∀ i, i < k → n i = S.L * n (i + 1)) {q : ℕ} (hqk : q ≤ k)
    {A : Set (Torus S.d (n q))} {ϱ' : ℝ} (hϱ : ϱ' ≤ minSep S.L g.M1)
    {x : Torus S.d (M * n k * S.L ^ k)}
    (hx : x ∈ (GeneratingSet.castN (geo_base_eq g)
      ((minimalGenSet (M1 := g.M1) (N₁ := g.c * n k) hqk (fineMin g q A)).relax hϱ)).Ω 1) :
    cubeMap n S.L M k q x ∈ nbhd 1 A := by
  rw [castN_mem, GeneratingSet.relax_Ω] at hx
  have hP : g.M1 * (g.c * n k) * S.L ^ k = (S.L ^ q * (g.c * g.M1)) * n q := by
    rw [nn_eq_pow' hnn hqk, ← pow_sub_mul_pow S.L hqk]
    ring
  have hM12 : 12 * g.M1 ≤ g.c * g.M1 := Nat.mul_le_mul_right _ (by have := g.hc; omega)
  obtain ⟨y, hy, hd⟩ := minimalGenSet_range (X := fineMin g q A) hL hqk hM12
    hP (x := torusCast (by rw [geo_base_eq g]) x) ((Background.mem_dataSites _).2 (Or.inl hx))
  rw [fineMin, mem_cubePre] at hy
  rw [cubeMap_eq_castBlock (g := g) q x]
  exact mem_nbhd.2 ⟨_, hy, hd⟩

end Range

section Fields

variable {H Z g}
variable (hkK : k ≤ K) (hW : H.RipeWindow k Z)

/-- `Ω_i(B)ᶜ ⊆ Z_i` for the full piece, `1 ≤ i ≤ k`. -/
theorem windowOfHistory_compl {i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k)
    {x : Torus S.d (M * n k * S.L ^ k)} (hx : x ∉ (windowOfHistory H Z g hkK hW).full.Ω i) :
    x ∈ H.locFine Z M i :=
  compl_Omega_subset (hkK := hkK) (hL := H.F.ok.two_le_L) (hR := fun j _ _ => g.hRlow j)
    (Z := Z) (M := M) hi hik hx

theorem windowOfHistory_full_Ω (j : ℕ) :
    (windowOfHistory H Z g hkK hW).full.Ω j =
      (H.locGen Z M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j)).Ω j := rfl

theorem windowOfHistory_Zk1 :
    (windowOfHistory H Z g hkK hW).Zk1 = H.locFineFin Z (S.k1 k) := rfl

theorem windowOfHistory_Z : (windowOfHistory H Z g hkK hW).Z = H.locFineFin Z k := rfl

theorem windowOfHistory_Unb :
    (windowOfHistory H Z g hkK hW).Unb = fineFin (k := k) (M := M) k (bdryUnb H Z) := rfl

theorem k1_le (hW : H.RipeWindow k Z) : S.k1 k ≤ k := by
  have := hW.core_window.1; rw [hW.core_k1]; omega

/-- Lemma III.1.2 (f): `Z_{k₁} ⊆ Z`. -/
theorem windowOfHistory_hZ :
    (windowOfHistory H Z g hkK hW).Zk1 ⊆ (windowOfHistory H Z g hkK hW).Z := by
  intro x hx
  rw [windowOfHistory_Zk1, mem_locFineFin] at hx
  rw [windowOfHistory_Z, mem_locFineFin]
  exact locFine_mono hkK (k1_le hW) le_rfl hx

/-- Lemma III.1.2 (f): `Ω_1(B)ᶜ ⊆ Ω_{k₁}(B)ᶜ ⊆ Z_{k₁}`. -/
theorem windowOfHistory_hOmK1 :
    ∀ x, x ∉ (windowOfHistory H Z g hkK hW).Zk1 → x ∈ (windowOfHistory H Z g hkK hW).full.Ω 1 := by
  intro x hx
  have hk1 := hW.k1_pos hkK
  by_contra hn
  apply hx
  rw [windowOfHistory_Zk1, mem_locFineFin]
  refine windowOfHistory_compl (g := g) hkK hW hk1 (k1_le hW) (fun h => hn ?_)
  exact (windowOfHistory H Z g hkK hW).full.Ω_antitone le_rfl hk1
    (by have := k1_le hW; omega) h

/-- Lemma III.1.2 (f): `Ω_k(B)ᶜ ⊆ Z`. -/
theorem windowOfHistory_hOmK (hk : 1 ≤ k) :
    ∀ x, x ∉ (windowOfHistory H Z g hkK hW).Z → x ∈ (windowOfHistory H Z g hkK hW).full.Ω k := by
  intro x hx
  by_contra hn
  apply hx
  rw [windowOfHistory_Z, mem_locFineFin]
  exact windowOfHistory_compl (g := g) hkK hW hk le_rfl (fun h => hn h)

/-- Lemma III.1.2 (f): `Z_{k₁} ∩ Ω_{k₁+1}(B) = ∅`. -/
theorem windowOfHistory_hZk1top :
    ∀ x ∈ (windowOfHistory H Z g hkK hW).Zk1,
      x ∉ (windowOfHistory H Z g hkK hW).full.Ω (S.k1 k + 1) := by
  intro x hx
  rw [windowOfHistory_Zk1, mem_locFineFin] at hx
  rw [windowOfHistory_full_Ω]
  rcases Nat.lt_or_ge (S.k1 k) k with h | h
  · exact locFine_not_mem_Omega h hx
  · have : S.k1 k = k := le_antisymm (k1_le hW) h
    rw [this, (H.locGen Z M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j)).top]
    simp

/-- The boundary piece lies in the layers of `B` outside `Z` (Lemma III.1.2 (f), `Ω_n(B)ᶜ ⊆ Z_n ⊆ Z`):
the premise `hbdry` of `window_parent_refines`. -/
theorem windowOfHistory_hbdry :
    ∀ m, 1 ≤ m → m ≤ k → (windowOfHistory H Z g hkK hW).bdry.Ω m ∩
        ((windowOfHistory H Z g hkK hW).Unb \ (windowOfHistory H Z g hkK hW).Z) ⊆
      (windowOfHistory H Z g hkK hW).full.Ω m := by
  intro m hm1 hmk x hx
  obtain ⟨-, hx2⟩ := Finset.mem_inter.1 hx
  have hxZ := (Finset.mem_sdiff.1 hx2).2
  rw [windowOfHistory_Z, mem_locFineFin] at hxZ
  by_contra hn
  apply hxZ
  have := windowOfHistory_compl (g := g) hkK hW hm1 hmk (fun h => hn h)
  exact locFine_mono hkK hmk le_rfl this

/-- Lemma III.1.2 (f), P7 (2.1): the support of the boundary piece, `Ω_1(𝔹_k(U_k)) ⊆ U_k^∼`. -/
theorem windowOfHistory_hsupp :
    ∀ x ∈ (windowOfHistory H Z g hkK hW).bdry.Ω 1, x ∈ (windowOfHistory H Z g hkK hW).Unb := by
  intro x hx
  rw [windowOfHistory_Unb, mem_fineFin]
  exact cubeMap_nbhd_of_mem_cast H.F.ok.two_le_L
    (fun i hi => H.F.hnn i (lt_of_lt_of_le hi hkK)) le_rfl (min_le_right _ _) hx

/-- Lemma I.3.5 (g) for a history without removals: `(((Z_{i+1})ᶜ)^{≈2})^{∼(m+1)} ⊆ Ω_{i+1}` for
`m ≤ 3` (`≈` adds `⌊R_i⌋ + 1`). -/
theorem coreW_nbhd_subset_Omega {i : ℕ} (RH : RegionHistory S n R k0 K) (hrem : ∀ j, RH.rem j = ∅)
    (hR0 : 0 ≤ R i) {m : ℕ} (hm : m ≤ 3) :
    nbhd (m + 1) (thick2 ⌊R i⌋₊ (((RH.step (i + 1)).Z)ᶜ)) ⊆ (RH.step i).Omega := by
  have hZ : (RH.step (i + 1)).Z =
      (RH.step i).Zpre (S.omega (i + 1)) (critOpt S k0 (i + 1)) := by
    have := RH.Z_eq (i + 1)
    rw [hrem] at this
    simpa [FlowSteps.Zpre] using this
  intro y hy
  by_contra hyO
  rw [hZ] at hy
  have hd := (RH.step i).thick2_Zpre_compl_disjoint hR0 (S.omega (i + 1)) (critOpt S k0 (i + 1))
  have key : ∀ X : Set (Torus S.d (n (i + 1))), nbhd (m + 1) X ⊆ nbhd m (nbhd 1 X) := by
    intro X z hz; rw [nbhd_nbhd, Nat.add_comm 1 m]; exact hz
  have hy' := key _ hy
  obtain ⟨w, hw, hyw⟩ := mem_nbhd.1 hy'
  refine Set.disjoint_left.1 hd hw (Or.inl ?_)
  exact mem_nbhd.2 ⟨y, fun h => hyO ((RH.step i).OmegaDD_subset_Omega h), by
    rw [supDist_comm]; omega⟩

/-- A site whose `π_q`-cube is within `m + 1 ≤ 4` of `W_q` lies in `Ω_q(B)` (Lemma I.3.5 (g)). -/
theorem full_mem_of_nbhd (q : ℕ) (hq1 : 1 ≤ q) (hqk : q ≤ k) {m : ℕ} (hm : m ≤ 3)
    {c : Torus S.d (M * n k * S.L ^ k)}
    (h : cubeMap n S.L M k q c ∈ nbhd (m + 1) (coreW H Z q)) :
    c ∈ (windowFull H Z g hkK).Ω q := by
  obtain ⟨i, rfl⟩ : ∃ i, q = i + 1 := ⟨q - 1, by omega⟩
  have hR0 : 0 ≤ R i := le_trans (by have := H.F.ok.two_le_Rb; linarith) (g.hRlow i)
  have hO := coreW_nbhd_subset_Omega (H.locRH k Z) (fun j => rfl) hR0 hm h
  exact (mem_locGen_succ (hkK := hkK) (hL := H.F.ok.two_le_L) (hR := fun j _ _ => g.hRlow j)
    (Z := Z) (M := M) (by omega)).2 hO

/-- The core piece lies in the layers of the full piece (the margin of Lemma III.4.6 for the core, with
Lemma I.3.5 (g)): a site of `Ω_m(𝔹_q(W_q))`, `1 ≤ m ≤ q`, is in `Ω_q(B) ⊆ Ω_m(B)`. -/
theorem windowCore_subset_full (q : ℕ) (hq1 : 1 ≤ q) (hqk : q ≤ k) {m : ℕ} (hm1 : 1 ≤ m)
    {x : Torus S.d (M * n k * S.L ^ k)} (hx : x ∈ (windowCore H Z g q hqk).Ω m) :
    x ∈ (windowFull H Z g hkK).Ω m := by
  by_cases hmq : m ≤ q
  · have h1 : x ∈ (windowCore H Z g q hqk).Ω 1 :=
      (windowCore H Z g q hqk).Ω_antitone le_rfl hm1 (by omega) hx
    have hn := cubeMap_nbhd_of_mem_cast (g := g) H.F.ok.two_le_L
      (fun i hi => H.F.hnn i (lt_of_lt_of_le hi hkK)) hqk (A := coreW H Z q) (min_le_right _ _) h1
    have hmem := full_mem_of_nbhd (g := g) hkK q hq1 hqk (m := 0) (by omega) hn
    exact (windowFull H Z g hkK).Ω_antitone hm1 hmq (by omega) hmem
  · exfalso
    have : torusCast (by rw [geo_base_eq g]) x ∈
        minLayer g.M1 (g.c * n k) S.L k q (fineMin g q (coreW H Z q)) m :=
      (castN_mem (geo_base_eq g) _ m x).1 hx
    rw [minLayer_of_gt _ (by omega)] at this
    exact Finset.notMem_empty _ this

/-- **Lemma III.1.2 (f) / Lemma III.4.6 (core margin)**: `Ω_m(𝔹_{k₁}(W)) ⊆ Ω_m(𝔹_k)`, hence
`hcore` of `window_parent_refines`. -/
theorem windowOfHistory_hcore :
    ∀ m, 1 ≤ m → m ≤ k → (windowOfHistory H Z g hkK hW).core.Ω m ∩
        (windowOfHistory H Z g hkK hW).Zk1 ⊆ (windowOfHistory H Z g hkK hW).full.Ω m := by
  intro m hm1 _ x hx
  exact windowCore_subset_full (g := g) hkK (S.k1 k) (hW.k1_pos hkK) (k1_le hW) hm1
    (Finset.mem_inter.1 hx).1

/-- Adjacent sites have `π_j`-cubes at index distance `≤ 1`. -/
theorem cubeMap_adj (hnn : ∀ i, i < k → n i = S.L * n (i + 1)) {j : ℕ} (hj : j ≤ k)
    {x c : Torus S.d (M * n k * S.L ^ k)} (hadj : Adj x c) :
    supDist (cubeMap n S.L M k j x) (cubeMap n S.L M k j c) ≤ 1 := by
  have hP : M * n k * S.L ^ k = (S.L ^ j * M) * n j := by
    rw [nn_eq_pow' hnn hj, ← pow_sub_mul_pow S.L hj]; ring
  have h1 : supDist x c ≤ 1 := by
    have h2 := supDist_le_torusDist x c
    have h3 := Multiscale.Adj.torusDist_le hadj
    have : (supDist x c : ℝ) ≤ 1 := h2.trans h3
    exact_mod_cast this
  have hpos : 1 ≤ S.L ^ j * M := Nat.one_le_iff_ne_zero.2 (by
    have := NeZero.ne S.L; have := NeZero.ne M; positivity)
  exact supDist_blockMap_le_one (M1 := M) (N₁ := n k) (L := S.L) (q := k) hP hpos x c h1

/-- A site off `Z_{q}`, and a site of `Ω_1(𝔹_q(W_q))`, have all their neighbours in `Ω_q(B)`: the margin
of Lemma III.4.6 (Lemma I.3.5 (g), range of the minimal sets). -/
theorem windowOfHistory_nbr_mem_full (q : ℕ) (hq1 : 1 ≤ q) (hqk : q ≤ k)
    {x c : Torus S.d (M * n k * S.L ^ k)} (hadj : Adj x c)
    (hx : x ∈ (windowCore H Z g q hqk).Ω 1 ∨ x ∉ H.locFineFin Z q) :
    c ∈ (windowFull H Z g hkK).Ω q := by
  have hnn : ∀ i, i < k → n i = S.L * n (i + 1) := fun i hi => H.F.hnn i (lt_of_lt_of_le hi hkK)
  have hadj' : supDist (cubeMap n S.L M k q c) (cubeMap n S.L M k q x) ≤ 1 := by
    rw [supDist_comm]; exact cubeMap_adj hnn hqk hadj
  refine full_mem_of_nbhd (g := g) hkK q hq1 hqk (m := 1) (by omega) ?_
  rw [show (1 : ℕ) + 1 = 2 from rfl]
  rcases hx with hx | hx
  · have hn := cubeMap_nbhd_of_mem_cast (g := g) H.F.ok.two_le_L hnn hqk (A := coreW H Z q)
      (min_le_right _ _) hx
    obtain ⟨w, hw, hxw⟩ := mem_nbhd.1 hn
    have ht := supDist_triangle (cubeMap n S.L M k q c) (cubeMap n S.L M k q x) w
    exact mem_nbhd.2 ⟨w, hw, by omega⟩
  · have hxZ : cubeMap n S.L M k q x ∈ (((H.locRH k Z).step q).Z)ᶜ := by
      rw [mem_locFineFin, mem_locFine] at hx; exact hx
    have hW : cubeMap n S.L M k q x ∈ coreW H Z q := by
      unfold coreW thick2 thick; exact subset_nbhd _ _ (subset_nbhd _ _ hxZ)
    exact mem_nbhd.2 ⟨_, hW, by omega⟩

/-- **Lemma III.4.6 margin** (premise `hmargin` of `inner_collar_parent_layer`), in terms of the layers of
the window generating set `(core ∩ Z_{k₁}) ∪ (B ∩ (Z ∖ Z_{k₁})) ∪ (𝔹_k(U_k) ∩ (U_k^∼ ∖ Z))`: a neighbour of
a site of `Ω_1` lies in `Ω_{k₁}(B)`. -/
theorem windowOfHistory_hmargin_layers :
    ∀ x ∈ ((windowOfHistory H Z g hkK hW).core.Ω 1 ∩ (windowOfHistory H Z g hkK hW).Zk1) ∪
        ((windowOfHistory H Z g hkK hW).full.Ω 1 ∩
          ((windowOfHistory H Z g hkK hW).Z \ (windowOfHistory H Z g hkK hW).Zk1)) ∪
        ((windowOfHistory H Z g hkK hW).bdry.Ω 1 ∩
          ((windowOfHistory H Z g hkK hW).Unb \ (windowOfHistory H Z g hkK hW).Z)),
      ∀ c, Adj x c → c ∈ (windowOfHistory H Z g hkK hW).full.Ω (S.k1 k) := by
  intro x hx c hadj
  have hk1 := hW.k1_pos hkK
  have hqk := k1_le hW
  have hZ := windowOfHistory_hZ (g := g) hkK hW
  refine windowOfHistory_nbr_mem_full (g := g) hkK (S.k1 k) hk1 hqk hadj ?_
  rcases Finset.mem_union.1 hx with h | h
  · rcases Finset.mem_union.1 h with h | h
    · exact Or.inl (Finset.mem_inter.1 h).1
    · exact Or.inr (Finset.mem_sdiff.1 (Finset.mem_inter.1 h).2).2
  · exact Or.inr fun hz => (Finset.mem_sdiff.1 (Finset.mem_inter.1 h).2).2 (hZ hz)

/-- **Lemma III.4.6 margin**, the form `hmargin` of `inner_collar_parent_layer`
(only meaningful when `W.Hyp` holds; see `not_hyp_of_core_near`). -/
theorem windowOfHistory_hmargin (hWh : (windowOfHistory H Z g hkK hW).Hyp) :
    ∀ x ∈ ((windowOfHistory H Z g hkK hW).windowGenSet hWh).Ω 1, ∀ c, Adj x c →
      c ∈ (windowOfHistory H Z g hkK hW).Zk1 →
      c ∈ (windowOfHistory H Z g hkK hW).full.Ω (S.k1 k) := by
  intro x hx c hadj _
  rw [WindowPieces.windowGenSet_Ω] at hx
  exact windowOfHistory_hmargin_layers hkK hW x hx c hadj

/-- **Premise `hexitLayer`** (Lemma III.1.2 (f), Lemma I.3.5 (f)): a site off `Z_{k₁}` adjacent to
`Z_{k₁}` lies in the layer `k₁` of `B`. -/
theorem windowOfHistory_hexitLayer :
    ∀ x, x ∉ (windowOfHistory H Z g hkK hW).Zk1 → ∀ c, Adj x c →
      c ∈ (windowOfHistory H Z g hkK hW).Zk1 → x ∈ (windowOfHistory H Z g hkK hW).full.layer (S.k1 k) := by
  intro x hx c hadj hc
  have hk1 := hW.k1_pos hkK
  have hqk := k1_le hW
  refine (GeneratingSet.mem_layer _).2 ⟨?_, ?_⟩
  · by_contra hn
    exact hx (by
      rw [windowOfHistory_Zk1, mem_locFineFin]
      exact windowOfHistory_compl (g := g) hkK hW hk1 hqk hn)
  · rcases Nat.lt_or_ge (S.k1 k) k with hlt | hge
    · intro hxO
      rw [windowOfHistory_full_Ω, mem_locGen_succ hlt] at hxO
      rw [windowOfHistory_Zk1, mem_locFineFin, mem_locFine] at hc
      have hnn : ∀ i, i < k → n i = S.L * n (i + 1) :=
        fun i hi => H.F.hnn i (lt_of_lt_of_le hi hkK)
      rw [← cubeMap_succ hnn (by omega)] at hxO
      have hfar := ((H.locRH k Z).step (S.k1 k)).fine_far (by have := H.F.ok.two_le_L; omega)
        (hnn _ hlt) hxO hc
      have h1 := cubeMap_adj hnn hqk hadj
      omega
    · have : S.k1 k = k := le_antisymm hqk hge
      rw [this, windowOfHistory_full_Ω, (H.locGen Z M hkK H.F.ok.two_le_L _).top]
      simp

/-- **`W.Hyp` is false for the actual window** (LF-RECONSTRUCTION Definition III.2.1): if `k₁ ≥ 2` and
`Z_{k₁}` has a boundary pair (a site `y ∈ Z_{k₁}` adjacent to a site `x ∉ Z_{k₁}`; this holds as soon as
`Z_{k₁}` is a nonempty proper subset of the connected torus), the margin clause of `GluePieces.Hyp`
for the core piece fails: the core `𝔹_{k₁}(W)`, `W = (Z_{k₁}ᶜ)^{≈2}`, contains every site of `Z_{k₁}`
next to `Z_{k₁}ᶜ`. -/
theorem windowOfHistory_not_hyp_of_boundary_pair (h2 : 2 ≤ S.k1 k)
    {x y : Torus S.d (M * n k * S.L ^ k)} (hadj : Adj x y)
    (hy : y ∈ (windowOfHistory H Z g hkK hW).Zk1) (hx : x ∉ (windowOfHistory H Z g hkK hW).Zk1) :
    ¬ (windowOfHistory H Z g hkK hW).Hyp := by
  have hqk := k1_le hW
  have hnn : ∀ i, i < k → n i = S.L * n (i + 1) := fun i hi => H.F.hnn i (lt_of_lt_of_le hi hkK)
  obtain ⟨m, hm⟩ : ∃ m, S.k1 k = m + 1 := ⟨S.k1 k - 1, by omega⟩
  -- `y` lies in the core piece at its top layer `k₁`
  have hyc : y ∈ (windowCore H Z g (S.k1 k) hqk).Ω (S.k1 k) := by
    have hcu : IsCubeUnion g.M1 (g.c * n k) S.L k (S.k1 k) (fineMin g (S.k1 k) (coreW H Z (S.k1 k))) :=
      isCubeUnion_cubePre hqk (by rw [nn_eq_pow' hnn hqk]; ring) _
    have hxZ : cubeMap n S.L M k (S.k1 k) x ∈ (((H.locRH k Z).step (S.k1 k)).Z)ᶜ := by
      have := hx; rw [windowOfHistory_Zk1, mem_locFineFin, mem_locFine] at this; exact this
    have hnb : supDist (cubeMap n S.L M k (S.k1 k) y) (cubeMap n S.L M k (S.k1 k) x) ≤ 1 := by
      rw [supDist_comm]; exact cubeMap_adj hnn hqk hadj
    have hW' : cubeMap n S.L M k (S.k1 k) y ∈ coreW H Z (S.k1 k) := by
      unfold coreW thick2 thick
      refine subset_nbhd _ _ (nbhd_mono (by omega) subset_rfl (mem_nbhd.2 ⟨_, hxZ, hnb⟩))
    have h1 : torusCast (by rw [geo_base_eq g]) y ∈
        fineMin g (S.k1 k) (coreW H Z (S.k1 k)) := by
      rw [fineMin, mem_cubePre, ← cubeMap_eq_castBlock (g := g)]; exact hW'
    refine (castN_mem (geo_base_eq g) _ _ y).2 ?_
    show _ ∈ minLayer g.M1 (g.c * n k) S.L k (S.k1 k) _ (S.k1 k)
    rw [minLayer_self, hcu.cubeInterior_eq]; exact h1
  have hϱ : 1 ≤ winSep g := by
    have hL := H.F.ok.two_le_L
    have hMpos := NeZero.pos M
    have hM1 := NeZero.pos g.M1
    have hRb := H.F.ok.two_le_Rb
    have hLr : (2 : ℝ) ≤ S.L := by exact_mod_cast hL
    have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
    have hM1r : (1 : ℝ) ≤ g.M1 := by exact_mod_cast hM1
    unfold winSep minSep
    have hLM : (2 : ℝ) ≤ (S.L : ℝ) * M := by nlinarith
    refine le_min ?_ ?_
    · nlinarith
    · nlinarith
  refine WindowPieces.not_hyp_of_core_near _ (n := m) (by omega) (by omega) (x := x) (y := y)
    ?_ hy hx ?_
  · have : m + 1 = S.k1 k := hm.symm
    show y ∈ (windowCore H Z g (S.k1 k) hqk).Ω (m + 1)
    rw [this]; exact hyc
  · have h1 := Multiscale.Adj.torusDist_le hadj
    have hLr : (1 : ℝ) ≤ (S.L : ℝ) ^ m := one_le_pow₀ (by exact_mod_cast NeZero.pos S.L)
    nlinarith

end Fields

end RegionHistory

end Balaban.LargeField
