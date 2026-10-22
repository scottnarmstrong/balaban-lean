/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.G0Expand
public import Balaban.LargeField.R.GasIdentity
public import Balaban.LargeField.R.BPrimeRTie
public import Balaban.LargeField.R.RGasRepR4Decor

/-!
# G0: `ℬ′` and `ℛ″` of the output of `R` on one torus

P7 (3.26)–(3.29), printed pp. 527–528; LFR Definition III.10.3, Lemma III.10.4, Lemma III.10.5,
Definition III.10.6 (`notes/phase1/LF-RECONSTRUCTION.md` §III.10); ruling R4 (the decorated
couplings `b_X(S) = ℬ(X, 𝔸′ ∪ S) - ℬ̂(X; 𝔸′) + ℬ′_X(S)`, the operator form); ruling R12 (the
histories with a removal record contribute `0`; the removed components are in `ℬ′`, `ℛ″`).

**The gas of a kept configuration** (P7 (3.26), LFR (3.26′)).  Fix a torus with its pre-`R`
representation `rep` (`rec.F.lf nK`) and its small-field context `C`, and a kept configuration: the
members `Kc` (the components of `Y_k` with their localized histories), the region `Y = Y_k`, the
hole `S₀ = Ω^c_k ∩ Y_k`, and the kept boundary terms `keptT X = ℬ̂(X; 𝔸′)` (on `𝒳(𝔸′)`).
* heavy objects: the **removed clusters** `𝒞` of `Kc` (`RemCluster`, Definition III.10.3) built from
  the ripe members `(Z, 𝔞)` of the configurations of the pre-`R` histories (`remMembers`); their
  full support is `S(𝒞) = ⋃ Z^{∼2ω_k}` closed under the hole (compatibility and contact through the
  charged supports `S(𝒞) ∖ S₀`, which is `S(𝒞)` when `S(𝒞)` misses the hole, the (H-op) geometry);
  weight `τ_𝒞 = a(𝒞; 𝔸′) ∏_{(Z,𝔞) ∈ 𝒞} T^rem(Z) e^{E_k|Z|_k}` (`admFactor`, the removed weights
  `pres.w`);
* light objects: the domains `X` (sets of cubes of `𝕋_k`) decorated by the nonempty set `S` of
  clusters whose core `X` meets (`gasNear`), with the coupling of ruling R4
  `b_X(S) = r4Coupling old fresh kept X S`:
  `old X S = ℬ^{(k)}(X, 𝔸′ ∪ S)` (the pre-`R` boundary term of the pre-`R` history whose scale-`k`
  configuration is `Kc ∪ S`, at its fields `pres.fld`; `ℬ̂(X; 𝔸′)` for `S = ∅`),
  `kept X = ℬ̂(X; 𝔸′)`, `fresh X S = ℬ′_X(S)` (A4's `rFresh`, P7 (3.22)–(3.25), old small-field
  region `(Y ∪ ⋃_{𝒞 ∈ S} c(𝒞))ᶜ`, new region `Yᶜ`);
* internal variables and reference measure: `∏_b pres.Ω b`, `⨂_b pres.μ b` ((H-op)).
`gasP X e` is the local term `P^{(k)}(X; 𝔸′)` of its cluster expansion (`decP`, P7 (3.28)) at the
external variables `e = (ψ, ψ′, h, g)`.

**The outputs** (LFR Definition III.10.6):
* `bPrimeTorus`: `ℬ′(𝔸′, X) = ℬ̂(X; 𝔸′) + P^{(k)}(X; 𝔸′) 1[X ∩ Y_k ≠ ∅]` for a removal-free history
  `𝔸′` (the term of `ℬ̂` is the field `rep.B`; only the domains `bdryDoms (Ω_k(𝔸′)) Y_k` are read
  by `bdrySum`); for a history with a removal record `ℬ′ = rep.B` (its term is `0`, R12);
* `remTorus`: `ℛ″_m(X; ψ_k, h, g) = P^{(k)}_∅(X; ψ_k, h, g)`, the term of the expansion of the gas
  with **no kept region** (`Kc = ∅`, `Y = ∅`, no hole), at the index `m = m₀ + m₁` (P7 (3.29)),
  on the Def-6 polymers that are unions of cubes of `𝕋_k`, read at the block field, `h`, `g` of
  the Def-6 fields.

The removed weights in operator form, the reference measure and the fields of the pre-`R`
histories are the (H-op) presentation `RemPres` (W2's export; not constructed here).
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset MeasureTheory Balaban Balaban.Polymer Balaban.LargeField.Def7 Balaban.SmallField

namespace Balaban.LargeField.G0

section Torus

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N k : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}

/-- The external variables `(ψ, ψ′, h, g)` of a boundary term (the arguments of `Rep.B`). -/
abbrev BExt (S : Setting) (n : ℕ → ℕ) (M K N : ℕ) : Type :=
  MultiFieldC S n M K N × MultiFieldC S n M K N × (Fin N → ℂ) × (GIdx S n M K N → ℂ)

/-! ### Configurations and removed clusters -/

variable (M k) in
/-- **The scale-`k` configuration of a history** (Definition III.10.1): the components of
`Z^pre_k` with their localized histories. -/
def configMembers (A : LabHist S n R k0 K) : Finset (ConfigPair S n M K k) :=
  Finset.univ.image fun c : A.H.Comp k => (c.1, A.H.localHistory M K k c)

variable (M k) in
/-- **The kept configuration of a removal-free history** as a `HistConfig` (its members are
`configMembers`; the empty configuration if they are not a configuration). -/
def keptConfig (A : LabHist S n R k0 K) : HistConfig S n R k0 K M k :=
  if h : (∀ m ∈ configMembers M k A, m.2 ∈ localizedHistories (S := S) (n := n) R k0 K M k m.1) ∧
      ∀ m ∈ configMembers M k A, ∀ m' ∈ configMembers M k A, m ≠ m' →
        ∀ x ∈ m.1, ∀ y ∈ m'.1, S.omega k ≤ supDist x y then
    ⟨configMembers M k A, h.1, h.2⟩
  else HistConfig.empty

/-- **The removed members** of the torus: the ripe members `(Z, 𝔞)` of the scale-`k`
configurations of the pre-`R` histories (Definition III.10.3, "removed component"). -/
def remMembers (rep : Rep S n R k0 K M N geo cs P k) : Finset (ConfigPair S n M K k) :=
  (rep.hist.biUnion (configMembers M k)).filter (IsRipeMember R k0 K M k)

/-- The removed members as a type. -/
abbrev RemMem (rep : Rep S n R k0 K M N geo cs P k) : Type := ↥(remMembers rep)

/-- The members of a family of removed members, as configuration pairs. -/
def memPairs {rep : Rep S n R k0 K M N geo cs P k} (C : Finset (RemMem rep)) :
    Finset (ConfigPair S n M K k) :=
  C.map (Function.Embedding.subtype _)

/-- **The removed clusters of a kept configuration** (Definition III.10.3): the families of removed
members that are removed clusters of `Kc`. -/
def RemCl (rep : Rep S n R k0 K M N geo cs P k) (Kc : HistConfig S n R k0 K M k) : Type :=
  {C : Finset (RemMem rep) // RemCluster Kc (memPairs C)}

noncomputable instance (rep : Rep S n R k0 K M N geo cs P k) (Kc : HistConfig S n R k0 K M k) :
    Fintype (RemCl rep Kc) := by
  unfold RemCl; infer_instance

variable {rep : Rep S n R k0 K M N geo cs P k} {Kc : HistConfig S n R k0 K M k}

/-- The support `S(𝒞) = ⋃_{Z ∈ 𝒞} Z^{∼2ω_k}` of a removed cluster, as a set of cubes. -/
def clSupp (Cl : RemCl rep Kc) : Finset (Torus S.d (n k)) :=
  Finset.univ.filter (· ∈ clusterSupp S n M K k (memPairs Cl.1))

/-- The core `c(𝒞) = ⋃_{Z ∈ 𝒞} Z` of a removed cluster, as a set of cubes. -/
def clCore (Cl : RemCl rep Kc) : Finset (Torus S.d (n k)) :=
  Finset.univ.filter (· ∈ clusterCore S n M K k (memPairs Cl.1))

/-- The members of a set of removed clusters. -/
def remSet (Sc : Finset (RemCl rep Kc)) : Finset (ConfigPair S n M K k) :=
  Sc.biUnion fun Cl => memPairs Cl.1

variable (rep Kc) in
/-- **The decoration relation**: the domain `X` meets a removed component of the cluster (P7
p. 527; LFR §III.10.3, "the `X` that meet a removed component"). -/
def gasNear (X : Finset (Torus S.d (n k))) (Cl : RemCl rep Kc) : Prop :=
  ¬ Disjoint X (clCore Cl)

/-- The closure of a set of cubes under the nearest-neighbour components of the hole `S₀` that it
meets (the full support of an object of the gas). -/
def holeCl (S₀ X : Finset (Torus S.d (n k))) : Finset (Torus S.d (n k)) :=
  X ∪ Finset.univ.filter fun b => ∃ a ∈ X, a ∈ S₀ ∧ b ∈ nnComp (S₀ : Set (Torus S.d (n k))) a

/-! ### The (H-op) presentation of the removed members -/

variable (rep) in
/-- **The operator form of the removed members** ((H-op); W2's export, not constructed here): the
internal variables of the removed members as a product over the cubes `b` of `𝕋_k` of measurable
spaces `Ω b` with reference probability measures `μ b`; the removed weight `T^rem(Z) e^{E_k|Z|_k}`
of each member as a function of the external variables and the internal configuration
`Φ ∈ ∏_b Ω b` (P7 (3.26), LFR (3.26′): the removed operator without front functions, acting on the
internal variables of `Z`); the multiscale and fluctuation fields
`(ψ̃, ψ̃′)` of the pre-`R` history `𝔸′ ∪ S` (the kept fields with the fields of the removed members
of `S`), at which its boundary terms are evaluated; and the constants `a₁`, `ν`, `rho` of the
re-expansion `ℬ′` (`rBPrime`). -/
structure RemPres where
  /-- the internal variables of the removed members on a cube -/
  Ω : Torus S.d (n k) → Type
  [ms : ∀ b, MeasurableSpace (Ω b)]
  /-- the reference probability measures of (H-op) -/
  μ : ∀ b, Measure (Ω b)
  /-- the removed weight `T^rem(Z) e^{E_k|Z|_k}` of a member -/
  w : RemMem rep → BExt S n M K N → (∀ b, Ω b) → ℂ
  /-- the fields `(ψ̃, ψ̃′)` of the pre-`R` history with the removed members `S` -/
  fld : Finset (ConfigPair S n M K k) → BExt S n M K N → (∀ b, Ω b) →
    MultiFieldC S n M K N × MultiFieldC S n M K N
  /-- the coefficient constant of the backgrounds of `ℬ′` -/
  a₁ : ℝ
  /-- the mass of the backgrounds of `ℬ′` -/
  ν : ℝ
  /-- the decoupling radius of `ℬ′` -/
  rho : ℝ

attribute [instance] RemPres.ms

/-- `RemPres` is inhabited (the trivial presentation: one point, no weight). -/
instance : Nonempty (RemPres rep) :=
  ⟨{ Ω := fun _ => Unit, μ := fun _ => Measure.dirac (), w := fun _ _ _ => 0,
     fld := fun _ e _ => (e.1, e.2.1),
     a₁ := 0, ν := 0, rho := 0 }⟩

/-! ### The gas of a kept configuration and its local terms -/

section Gas

variable {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N))
  (vc : Def7v2.CorrCoef S.d) (pres : RemPres rep) (Y : Set (Torus S.d (n k)))
  (S₀ : Finset (Torus S.d (n k))) (keptT : Finset (Torus S.d (n k)) → BExt S n M K N → ℂ)

variable (Kc) in
/-- **The heavy weight of a removed cluster** (LFR (3.26′)): the admissibility factor
`a(𝒞; 𝔸′)` times the product of the removed weights of its members. -/
def gasTau (Cl : RemCl rep Kc) (e : BExt S n M K N) (Φ : ∀ b, pres.Ω b) : ℂ :=
  (admFactor Kc (memPairs Cl.1) : ℂ) * ∏ m ∈ Cl.1, pres.w m e Φ

variable (Kc) in
/-- **The old boundary term `ℬ^{(k)}(X, 𝔸′ ∪ S)`**: for `S = ∅` the kept term; otherwise the term
of the pre-`R` history whose scale-`k` configuration is `Kc ∪ S` (on its boundary domains), at the
fields of that history, and `0` if there is no such history. -/
def gasOld (X : Finset (Torus S.d (n k))) (Sc : Finset (RemCl rep Kc)) (e : BExt S n M K N)
    (Φ : ∀ b, pres.Ω b) : ℂ :=
  if Sc = ∅ then keptT X e
  else if h : ∃ A ∈ rep.hist, configMembers M k A = Kc.members ∪ remSet Sc then
    if X ∈ bdryDoms (OmegaCube h.choose.H k) (h.choose.H.F.Zpre k) then
      rep.B h.choose X (pres.fld (remSet Sc) e Φ).1 (pres.fld (remSet Sc) e Φ).2 e.2.2.1 e.2.2.2
    else 0
  else 0

variable (Kc) in
/-- **The new boundary term `ℬ′_X(S)`** of P7 (3.22)–(3.25) (A4's `rFresh`): old small-field
region `(Y ∪ ⋃_{𝒞 ∈ S} c(𝒞))ᶜ`, new region `Yᶜ`, at the block field `ψ_k` (the scale-`k` part of
`ψ`). -/
def gasFresh (X : Finset (Torus S.d (n k))) (Sc : Finset (RemCl rep Kc)) (e : BExt S n M K N) :
    ℂ :=
  C.rFresh hv vc e.2.2.2
    (fun Sc' : Finset (RemCl rep Kc) => (Y ∪ ⋃ Cl ∈ Sc', (clCore Cl : Set (Torus S.d (n k))))ᶜ)
    Yᶜ pres.a₁ pres.ν pres.rho (e.1 k) X Sc

variable (Kc) in
/-- **The decorated coupling** `b_X(S) = ℬ(X, 𝔸′ ∪ S) - ℬ̂(X; 𝔸′) + ℬ′_X(S)` (ruling R4,
`r4Coupling`). -/
def gasCoupling (X : Finset (Torus S.d (n k))) (Sc : Finset (RemCl rep Kc)) (e : BExt S n M K N)
    (Φ : ∀ b, pres.Ω b) : ℂ :=
  r4Coupling (fun X' Sc' => gasOld Kc pres keptT X' Sc' e Φ)
    (fun X' Sc' => gasFresh Kc C hv vc pres Y X' Sc' e) (fun X' => keptT X' e) X Sc

variable (Kc) in
/-- **The local term `P^{(k)}(X)` of the gas of the kept configuration** (P7 (3.27)–(3.28); LFR
Lemma III.10.5): `decP` on the cube graph of `𝕋_k` with the hole `S₀`, the removed clusters as
heavy objects (support `S(𝒞)` closed under the hole, weight `gasTau`), the
domains decorated by the clusters they meet as light objects (full support the hole closure of
the domain, weight `e^{b_X(S)} - 1`), and the reference measure `pres.μ`. -/
def gasP (X : Finset (Torus S.d (n k))) (e : BExt S n M K N) : ℂ :=
  decP (Localization.latGraph S.d (n k)) S₀ (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl)) (fun X' => holeCl S₀ X') (gasNear rep Kc)
    (fun Cl Φ => gasTau Kc pres Cl e Φ)
    (fun X' Sc Φ => gasCoupling Kc C hv vc pres Y keptT X' Sc e Φ)
    pres.μ X

end Gas

/-! ### `ℬ′`: the boundary terms of the output on one torus -/

section BPrime

variable {m₁ : ℕ} {ϱ : ℝ} (rep) (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N))
  (vc : Def7v2.CorrCoef S.d) (pres : RemPres rep)

/-- The hole `S₀ = Ω^c_k ∩ Y_k` of a kept history. -/
def holeOf (A : LabHist S n R k0 K) : Finset (Torus S.d (n k)) :=
  Finset.univ.filter fun b => b ∉ OmegaCube A.H k ∧ b ∈ (A.H.step k).Z

/-- The kept boundary terms `ℬ̂(X; 𝔸′)` of a kept history, on its boundary domains `𝒳(𝔸′)`. -/
def keptTermOf (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k))) (e : BExt S n M K N) : ℂ :=
  if X ∈ bdryDoms (OmegaCube A.H k) (A.H.step k).Z then rep.B A X e.1 e.2.1 e.2.2.1 e.2.2.2
  else 0

/-- **`ℬ′` of the output of `R` on one torus** (LFR Definition III.10.6; P7 (3.26)–(3.28)): for a
removal-free history `𝔸′` and a domain `X` meeting `Y_k`, the kept term `ℬ̂(X; 𝔸′)` (`rep.B`) plus
the local term `P^{(k)}(X; 𝔸′)` of the gas of removed clusters of the kept configuration of `𝔸′`;
otherwise `rep.B` (a history with a removal record has the term `0`, ruling R12). -/
def bPrimeTorus (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ ψ' : MultiFieldC S n M K N) (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ) : ℂ :=
  rep.B A X ψ ψ' h g +
    if (∀ j, j ≤ k → A.H.rem j = ∅) ∧ ((X : Set (Torus S.d (n k))) ∩ (A.H.step k).Z).Nonempty then
      gasP (keptConfig M k A) C hv vc pres (A.H.step k).Z (holeOf A) (keptTermOf rep A) X
        (ψ, ψ', h, g)
    else 0

end BPrime

/-! ### `ℛ″`: the new remainder on one torus -/

section Rem

variable {m₁ : ℕ} {ϱ : ℝ} (rep) (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N))
  (vc : Def7v2.CorrCoef S.d) (pres : RemPres rep)

/-- The `k`-block of the fine torus of a site of the Def-6 torus. -/
def blockOfSite (x : Localization.CTorus S.d S.L C.N₁ m₁ k) : BlockAt S n M K k :=
  Multiscale.jBlock S.d S.L (M * n K) K k (bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT x))

/-- The block field `ψ_k` read off a Def-6 field (constant on the `k`-blocks, `sfLiftKC`). -/
def blockOf (ψ : Def6.Fld S.d S.L C.N₁ m₁ k N) : BlockAt S n M K k → Fin N → ℂ :=
  fun y => ψ (Function.invFun (blockOfSite C) y)

/-- The source `g` on the fine torus read off a Def-6 field (`sfG`). -/
def gOf (G : Def6.Fld S.d S.L C.N₁ m₁ k N) : GIdx S n M K N → ℂ :=
  fun p => G (Function.invFun (fun x => bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT x)) p.1) p.2

/-- The constant `h` read off a Def-6 field (`constFld`). -/
def hOf (G : Def6.Fld S.d S.L C.N₁ m₁ k N) : Fin N → ℂ := G 0

/-- The external variables of the gas with no kept region: the multiscale field with the block
field `ψ_k` at the scale `k` and `0` elsewhere, no fluctuation field, `h`, `g`. -/
def extOf (ψ hh g : Def6.Fld S.d S.L C.N₁ m₁ k N) : BExt S n M K N :=
  (fun j y => if hj : j = k then
      blockOf C ψ (cast (congrArg (fun i => Torus S.d (M * n K * S.L ^ (K - i))) hj) y) else 0,
    0, hOf C hh, gOf C g)

/-- **`ℛ″` of the output of `R` on one torus** (LFR Definition III.10.6; P7 (3.29)): at the index
`m = m₀ + m₁` and a Def-6 polymer `X` that is the fine set of a set of cubes of `𝕋_k`, the local
term `P^{(k)}_∅` of the gas with no kept region (no kept member, `Y = ∅`, no hole, no kept term) on
those cubes; `0` otherwise. -/
def remTorus (nn : ℕ) (X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k))
    (ψ hh g : Def6.Fld S.d S.L C.N₁ m₁ k N) : ℂ :=
  if nn = C.m₀ + m₁ ∧ X = C.sset ↑(C.tSetOf X) then
    gasP HistConfig.empty C hv vc pres ∅ ∅ (fun _ _ => 0) (C.tSetOf X) (extOf C ψ hh g)
  else 0

end Rem

end Torus

end Balaban.LargeField.G0
