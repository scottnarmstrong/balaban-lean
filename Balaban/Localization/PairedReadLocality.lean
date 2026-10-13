/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.PairedLocalAgree
public import Balaban.Localization.P6PairGraph
public import Balaban.Localization.I5Param

/-!
# Restricted-read locality of the paired composite (VMOD-39 §5, package 5)

Nothing about the physical P6 scalar, its read set `A_X`, the covariance square-root term or the
support of the coefficients on active cells only is proved here; that statement is open
(`OPEN-P6-ACTIVE-COMPOSITE-LOC`) and is the subject of a question to the author.  This file
transports the proof of `PairedLocalAgree.paired_locality` to a functional that reads the paired raw
datum only on a set `R` of sites.

## Anatomy of `paired_locality` (T1)

Hypotheses and their role in the proof (`s`, `s'` the two parameter families, `J` the marked set):

* `hS hF hM hM₂ hκ hδ0 hδε hε hδ hνε hδ₀ hδ₁`, `Sb`, `Sm`, `HB` : constants and footprint-locality
  of the two decoupled problems; used only inside `paired_fields_agree` (global).
* `cc`, `hinj` : the cube of each parameter; `hinj` is used to rewrite `relParams … univ s` as
  `relParams … J s` (`relParams_univ_eq`), and in `paired_fields_agree` (global).
* `X₁` : the uncut core; only in `relParams` and `IsIncUnion` (global).
* `Yf`, `hG` : `Yf J` and the two incidence unions with cells inside `Yf J`; used by
  `paired_fields_agree` (global, once per `J`).
* `hXY` : `X₁ ⊆ Yf J`.  Used only to define `hXs`, `hXm` (the dependency sites of every
  `x ∈ dataSites Gx` lie in `Yf J`) and `hself` (every `x ∈ dataSites Gx` lies in `Yf J`).  Quantified
  over all `x ∈ dataSites Gx` in `hXs`, `hXm`, `hself`; the first component then uses `hXs x`,
  `hXm x` and `hself x` at the single site `x`, the second uses `hself x`.
* `hdepb`, `hdepm` : `composeDep Gx Hb x ⊆ X₁`, `composeDep Gx Hm x ⊆ X₁` for all `x ∈ dataSites Gx`;
  used only to build `hXs`, `hXm`.
* `Gx` : the composing generating set; `dataSites Gx` is where `pairedRaw` is non-zero.
* `Fb`, `hFb`, `Sol`, `hSol` : the solution selectors, used to identify the selected solutions with
  the solutions of `paired_fields_agree` (global; per `J`, not per site).
* `E` : the functional.  It takes the whole raw datum (no restricted argument, no spectators).
* conclusion `LocalityAEOn …` : the data `(u, ψ)`, `(u', ψ')` in `PairedDomain`, parameters in the
  polydisc supported on `J`, agreement of parameters on the cells inside `Yf J`, and `PairedAg`.

The per-site statement is the body of the last two `refine`s: the paired raw datum at a site `x` is
equal for the two sides as soon as the fields of `paired_fields_agree` agree (global) and
`composeDep Gx Hb x ∪ composeDep Gx Hm x ⊆ Yf J` (when `x ∈ dataSites Gx`).  Here it is
`pairedRaw_agree_at`.  `paired_locality_on` is the restricted-read theorem; `paired_locality_of_on`
recovers the landed theorem (read set = all sites).

Section `Seed` (T5) shows that the joint closure for an arbitrary seed `U` satisfies the graph
hypotheses needed (no `X₁ ⊆ U`), and contains the nearest-neighbour components of its seed sites.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}

section ReadLocality

variable {ϱx : ℝ} {C : DecCover d L N₁ m₁ K} {Hb : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} {Kc Cx : ℝ}
  {c₁ BG cstar BG₂ κ δ ε δ₀ δ₁ : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c₁ BG)
  (Sb : Dec2.FootLocal C Hb a ν Kc Cx) (HB : BgHyp d L K ϱ' a ν) (hκ : 0 ≤ κ)
  (hM : c₁ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
  (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2)
  (hF : Dec2.FamSpec d L Kc Cx cstar BG₂) (Sm : Dec2.FootLocal C Hm a ν Kc Cx)
  (hM₂ : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
  (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
  {ι : Type*} [DecidableEq ι] [Fintype ι] (cc : ι → ℕ × CTorus d L N₁ m₁ K)
  (hinj : Function.Injective cc) (X₁ : Finset (CTorus d L N₁ m₁ K))
  (Yf : Finset ι → Finset (CTorus d L N₁ m₁ K))
  (hG : ∀ J : Finset ι, ∃ Ab Am : Finset (ℕ × CTorus d L N₁ m₁ K),
    Dec2.IsIncUnion C Hb a ν X₁ (J.image cc) (Yf J) Ab ∧
    Dec2.IsIncUnion C Hm a ν X₁ (J.image cc) (Yf J) Am ∧
    (∀ P ∈ Ab, ∀ x ∈ cubeP P, x ∈ Yf J) ∧ (∀ P ∈ Am, ∀ x ∈ cubeP P, x ∈ Yf J))
  (Gx : GeneratingSet d L (N₁ * L ^ m₁) K ϱx)
  {Fb : Dec2.DecParams C × RawData d L (N₁ * L ^ m₁) K N →
    (Hb.Ω 1 × Fin N → ℂ) × (Hb.Ω 1 → ℂ)}
  (hFb : ∀ (s : Dec2.DecParams C) (D : BgData Hb N), (∀ P, ‖s P‖ ≤ Real.exp κ) →
    InDomainC Hb ν δ ε D → ∀ (φ : Hb.Ω 1 × Fin N → ℂ) (α : Hb.Ω 1 → ℂ),
      Dec2.IsDecBg C Hb a ν (rho4 d L N BG κ) s D φ α → Fb (s, rawOf D) = (φ, α))
  {Sol : Dec2.DecParams C × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
  (hSol : ∀ p : Dec2.DecParams C × Edat Hm N, (∀ P, ‖p.1 P‖ ≤ Real.exp κ) →
    DecHyp Hm a ν false p.2.2.1 p.2.1 p.2.2.2.1 p.2.2.2.2 δ₀ δ₁ →
      (Sol p).1 = dphi Hm (Dec2.decG C Hm a ν p.1) p.2.2.1 p.2.1
        (pertSource Hm a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
      Dec2.DecFixed C Hm a ν p.1 false p.2.2.1 p.2.1
        (pertSource Hm a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
      Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)))

include hS Sb HB hκ hM hδ0 hδε hε hδ hνε hF Sm hM₂ hδ₀ hδ₁ hinj hG hFb hSol

/-- **Per-site agreement of the paired raw datum (T2).**  For data `(u, ψ)`, `(u', ψ₂)` of the
paired domain, parameter families `s`, `s'` in the polydisc supported on `J` that agree on the cells
inside `Yf J`, and data in `PairedAg`, the paired raw data at a site `x` coincide (both components)
as soon as, when `x ∈ dataSites Gx`, the dependency sets of `x` for the two operators lie in
`Yf J`.  No other site is involved. -/
theorem pairedRaw_agree_at (J : Finset ι) (u u' : RawData d L (N₁ * L ^ m₁) K N)
    (ψ ψ₂ : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (hu : (u, ψ) ∈ PairedDomain C Hb Hm ν a BG κ δ ε δ₀ δ₁)
    (hu' : (u', ψ₂) ∈ PairedDomain C Hb Hm ν a BG κ δ ε δ₀ δ₁)
    (s s' : ι → ℂ) (hs : s ∈ supN J (Real.exp κ)) (hs' : s' ∈ supN J (Real.exp κ))
    (hpar : ∀ i ∈ J, Pset m₁ (cc i) ⊆ (↑(Yf J) : Set (CTorus d L N₁ m₁ K)) → s i = s' i)
    (hAg : PairedAg Hb (Yf J) u u' ψ ψ₂) (x : Torus d (N₁ * L ^ m₁ * L ^ K))
    (hxb : x ∈ dataSites Gx → ∀ y ∈ composeDep Gx Hb x, y ∈ Yf J)
    (hxm : x ∈ dataSites Gx → ∀ y ∈ composeDep Gx Hm x, y ∈ Yf J) :
    (pairedRaw C Hb Hm Gx a Fb Sol (relParams C X₁ cc Finset.univ s) (u, ψ)).1 x =
        (pairedRaw C Hb Hm Gx a Fb Sol (relParams C X₁ cc Finset.univ s') (u', ψ₂)).1 x ∧
      (pairedRaw C Hb Hm Gx a Fb Sol (relParams C X₁ cc Finset.univ s) (u, ψ)).2 x =
        (pairedRaw C Hb Hm Gx a Fb Sol (relParams C X₁ cc Finset.univ s') (u', ψ₂)).2 x := by
  classical
  obtain ⟨D, hDu, hD, hex⟩ := hu
  obtain ⟨D₂, hDu₂, hD₂, hex₂⟩ := hu'
  simp only at hDu hDu₂
  subst hDu hDu₂
  obtain ⟨Ab, Am, hIb, hIm, hAb, hAm⟩ := hG J
  rw [relParams_univ_eq hinj hs.1, relParams_univ_eq hinj hs'.1]
  have hR : (1 : ℝ) ≤ Real.exp κ := Real.one_le_exp hκ
  have hn1 : ∀ P, ‖relParams C X₁ cc J s P‖ ≤ Real.exp κ := fun P =>
    norm_extS_relParams_le hR (fun i => (hs.2 i).le) P
  have hn2 : ∀ P, ‖relParams C X₁ cc J s' P‖ ≤ Real.exp κ := fun P =>
    norm_extS_relParams_le hR (fun i => (hs'.2 i).le) P
  obtain ⟨φ, α, hI, Hh⟩ := hex _ hn1
  obtain ⟨φ₂, α₂, hI₂, Hh₂⟩ := hex₂ _ hn2
  have hF1 := hFb _ D hn1 hD φ α hI
  have hF2 := hFb _ D₂ hn2 hD₂ φ₂ α₂ hI₂
  obtain ⟨hfld, hfix, hsm⟩ := hSol (relParams C X₁ cc J s, flEdat Hb Hm (φ, α) D.Ψ ψ) hn1 Hh
  obtain ⟨hfld₂, hfix₂, hsm₂⟩ :=
    hSol (relParams C X₁ cc J s', flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂) hn2 Hh₂
  have hparJ : ∀ i ∈ J, (∀ x ∈ cubeP (cc i), x ∈ Yf J) → s i = s' i := by
    intro i hi hsub
    refine hpar i hi (fun x hx => ?_)
    exact Finset.mem_coe.2 (hsub x (mem_cubeP.2 hx))
  obtain ⟨hα, hφ, hδα, hdphi⟩ := paired_fields_agree hS Sb HB hκ hM hδ0 hδε hε hδ hνε hD hD₂ hF Sm
    hM₂ (cc := cc) (hinj.injOn) hs hs' hIb hIm hAb hAm hparJ hAg hI hI₂ Hh Hh₂ hδ₀ hδ₁ hfix hsm
    hfix₂ hsm₂
  have hself : x ∈ dataSites Gx → x ∈ Yf J := fun hx =>
    hxb hx x (self_mem_composeDep x)
  dsimp only [pairedRaw]
  rw [hF1, hF2]
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · by_cases hx : x ∈ dataSites Gx
    · congr 1
      · refine composeField_congr (G := Gx) (G' := Hb) a (fun y hy jj => ?_)
          (fun jj => congrFun (hAg.1 x (Or.inl (Finset.mem_coe.2 (hself hx)))).1 jj) i
        have hyY := hxb hx y hy
        by_cases hyΩ : y ∈ Hb.Ω 1
        · rw [svec_of_mem' _ hyΩ jj, svec_of_mem' _ hyΩ jj]
          exact hφ ⟨y, hyΩ⟩ hyY jj
        · rw [svec_of_not_mem Hb _ hyΩ jj, svec_of_not_mem Hb _ hyΩ jj]
      · refine composeField_congr (G := Gx) (G' := Hm) a (fun y hy jj => ?_)
          (fun jj => congrFun (hAg.2 x (Or.inl (Finset.mem_coe.2 (hself hx)))) jj) i
        have hyY := hxm hx y hy
        by_cases hyΩ : y ∈ Hm.Ω 1
        · rw [svec_of_mem' _ hyΩ jj, svec_of_mem' _ hyΩ jj]
          change (Sol (relParams C X₁ cc J s, flEdat Hb Hm (φ, α) D.Ψ ψ)).1 (⟨y, hyΩ⟩, jj) =
            (Sol (relParams C X₁ cc J s', flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂)).1 (⟨y, hyΩ⟩, jj)
          rw [hfld, hfld₂]
          exact hdphi ⟨y, hyΩ⟩ hyY jj
        · rw [svec_of_not_mem Hm _ hyΩ jj, svec_of_not_mem Hm _ hyΩ jj]
    · rw [composeField_of_not_mem _ _ _ hx, composeField_of_not_mem _ _ _ hx,
        composeField_of_not_mem _ _ _ hx, composeField_of_not_mem _ _ _ hx]
  · by_cases hx : x ∈ Gx.Ω 1
    · simp only [hx, ↓reduceIte]
      have hxd : x ∈ dataSites Gx := (mem_dataSites Gx).2 (Or.inl hx)
      exact congrFun (hAg.1 x (Or.inl (Finset.mem_coe.2 (hself hxd)))).2 i
    · simp [hx]

/-- **Restricted-read locality (T3).**  If `E` depends on its argument only through the values at
the sites of `R` (`hE`), and for every `J` the dependency sets of the sites of `R` lie in `Yf J`,
then `E ∘ pairedRaw` is local in the `LocalityAEOn` sense.  There is no hypothesis `X₁ ⊆ Yf J`. -/
theorem paired_locality_on (R : Set (Torus d (N₁ * L ^ m₁ * L ^ K)))
    (hdep : ∀ J : Finset ι, ∀ x ∈ R, x ∈ dataSites Gx →
      (∀ y ∈ composeDep Gx Hb x, y ∈ Yf J) ∧ ∀ y ∈ composeDep Gx Hm x, y ∈ Yf J)
    (E : RawData d L (N₁ * L ^ m₁) K N → ℂ)
    (hE : ∀ ψ ψ' : RawData d L (N₁ * L ^ m₁) K N,
      (∀ x ∈ R, ψ.1 x = ψ'.1 x ∧ ψ.2 x = ψ'.2 x) → E ψ = E ψ') :
    LocalityAEOn (Real.exp κ) (PairedDomain C Hb Hm ν a BG κ δ ε δ₀ δ₁)
      (fun i : ι => Pset m₁ (cc i)) (fun J => (↑(Yf J) : Set (CTorus d L N₁ m₁ K)))
      (fun J u u' => PairedAg Hb (Yf J) u.1 u'.1 u.2 u'.2)
      (fun u s => E (pairedRaw C Hb Hm Gx a Fb Sol (relParams C X₁ cc Finset.univ s) u)) := by
  rintro J ⟨u, ψ⟩ ⟨u', ψ₂⟩ hu hu' s s' hs hs' hpar hAg
  exact hE _ _ fun x hx =>
    pairedRaw_agree_at hS Sb HB hκ hM hδ0 hδε hε hδ hνε hF Sm hM₂ hδ₀ hδ₁ cc hinj X₁ Yf hG Gx hFb
      hSol J u u' ψ ψ₂ hu hu' s s' hs hs' hpar hAg x (fun h => (hdep J x hx h).1)
      (fun h => (hdep J x hx h).2)

/-- **The landed theorem from the restricted-read one (faithfulness check).**  This is the
statement of `PairedLocalAgree.paired_locality`, with the read set all sites. -/
theorem paired_locality_of_on (hXY : ∀ J, ∀ y ∈ X₁, y ∈ Yf J)
    (hdepb : ∀ x ∈ dataSites Gx, ∀ y ∈ composeDep Gx Hb x, y ∈ X₁)
    (hdepm : ∀ x ∈ dataSites Gx, ∀ y ∈ composeDep Gx Hm x, y ∈ X₁)
    (E : RawData d L (N₁ * L ^ m₁) K N → ℂ) :
    LocalityAEOn (Real.exp κ) (PairedDomain C Hb Hm ν a BG κ δ ε δ₀ δ₁)
      (fun i : ι => Pset m₁ (cc i)) (fun J => (↑(Yf J) : Set (CTorus d L N₁ m₁ K)))
      (fun J u u' => PairedAg Hb (Yf J) u.1 u'.1 u.2 u'.2)
      (fun u s => E (pairedRaw C Hb Hm Gx a Fb Sol (relParams C X₁ cc Finset.univ s) u)) :=
  paired_locality_on hS Sb HB hκ hM hδ0 hδε hε hδ hνε hF Sm hM₂ hδ₀ hδ₁ cc hinj X₁ Yf hG Gx hFb
    hSol Set.univ
    (fun J x _ hx => ⟨fun y hy => hXY J y (hdepb x hx y hy), fun y hy => hXY J y (hdepm x hx y hy)⟩)
    E (fun _ _ h => congrArg E
      (Prod.ext (funext fun x => (h x trivial).1) (funext fun x => (h x trivial).2)))

/-- **Vanishing of coefficients (T4).**  The restricted-read theorem is already the `LocalityAEOn`
hypothesis of `coef_eq_zero_of_not_connected_on` with `Yc J := Yf J` (as sets) and the agreement
`PairedAg`; the reflexivity `Ag C u u` is `PairedAg.refl`.  What is not supplied here is the
polydisc analyticity of `s ↦ E (pairedRaw …)` (needed only for the sum formula of
`abstract_expansion_on`). -/
theorem paired_coef_eq_zero_of_not_connected_on (hκ' : 0 < κ)
    (R : Set (Torus d (N₁ * L ^ m₁ * L ^ K)))
    (hdep : ∀ J : Finset ι, ∀ x ∈ R, x ∈ dataSites Gx →
      (∀ y ∈ composeDep Gx Hb x, y ∈ Yf J) ∧ ∀ y ∈ composeDep Gx Hm x, y ∈ Yf J)
    (E : RawData d L (N₁ * L ^ m₁) K N → ℂ)
    (hE : ∀ ψ ψ' : RawData d L (N₁ * L ^ m₁) K N,
      (∀ x ∈ R, ψ.1 x = ψ'.1 x ∧ ψ.2 x = ψ'.2 x) → E ψ = E ψ')
    {u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    (hu : u ∈ PairedDomain C Hb Hm ν a BG κ δ ε δ₀ δ₁) {J : Finset ι}
    (hJ : ¬ IsConnectedFamily (fun i : ι => Pset m₁ (cc i))
      (fun J => (↑(Yf J) : Set (CTorus d L N₁ m₁ K))) J) :
    coef (fun s => E (pairedRaw C Hb Hm Gx a Fb Sol (relParams C X₁ cc Finset.univ s) u)) J = 0 :=
  coef_eq_zero_of_not_connected_on (Real.one_lt_exp_iff.mpr hκ')
    (paired_locality_on hS Sb HB hκ hM hδ0 hδε hε hδ hνε hF Sm hM₂ hδ₀ hδ₁ cc hinj X₁ Yf hG Gx hFb
      hSol R hdep E hE)
    (fun _ _ _ => PairedAg.refl _ _ _ _) hu hJ

end ReadLocality

namespace Dec2

section Seed

variable {C : DecCover d L N₁ m₁ K} {Hb : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {X₁ : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
  {U : Set (CTorus d L N₁ m₁ K)}

/-- **Graph hypotheses for an arbitrary seed (T5).**  For `Y_f(J) := jointSites … (J.image cc) U`
with any seed `U` (not required to contain `X₁`), the two incidence unions and the cell conditions of
`paired_locality_on` hold. -/
theorem seed_graph_hyps {ι : Type*} [DecidableEq ι] (cc : ι → ℕ × CTorus d L N₁ m₁ K) :
    ∀ J : Finset ι, ∃ Ab Am : Finset (ℕ × CTorus d L N₁ m₁ K),
      IsIncUnion C Hb a ν X₁ (J.image cc) (jointSites C Hb Hm a ν X₁ (J.image cc) U) Ab ∧
      IsIncUnion C Hm a ν X₁ (J.image cc) (jointSites C Hb Hm a ν X₁ (J.image cc) U) Am ∧
      (∀ P ∈ Ab, ∀ x ∈ cubeP P, x ∈ jointSites C Hb Hm a ν X₁ (J.image cc) U) ∧
      (∀ P ∈ Am, ∀ x ∈ cubeP P, x ∈ jointSites C Hb Hm a ν X₁ (J.image cc) U) := fun _ =>
  ⟨_, _, isIncUnion_joint_b, isIncUnion_joint_m, fun _ hP => (joint_cell hP).2,
    fun _ hP => (joint_cell hP).2⟩

/-- **The nearest-neighbour step.**  A reached site `x` and a nearest neighbour `y` of `x` that
are both incidence sites of the operator `Hb`, or both of `Hm`, give a reached site `y`. -/
theorem jointSites_nn_step {x y : CTorus d L N₁ m₁ K}
    (hx : x ∈ jointSites C Hb Hm a ν X₁ 𝒞 U)
    (hxy : (Adj x y ∧ x ∈ incSites C Hb a ν X₁ 𝒞 ∧ y ∈ incSites C Hb a ν X₁ 𝒞) ∨
      (Adj x y ∧ x ∈ incSites C Hm a ν X₁ 𝒞 ∧ y ∈ incSites C Hm a ν X₁ 𝒞)) :
    y ∈ jointSites C Hb Hm a ν X₁ 𝒞 U := by
  by_cases hne : x = y
  · exact hne ▸ hx
  · have hne' : (Sum.inl x : IncV d L N₁ m₁ K) ≠ Sum.inl y := fun h => hne (Sum.inl_injective h)
    rcases hxy with h | h
    · exact mem_jointSites.2 (JointIn.adjB ⟨hne', Or.inl ⟨h.2.1, h.2.2, h.1⟩⟩ (mem_jointSites.1 hx))
    · exact mem_jointSites.2 (JointIn.site (JointIn.adjM ⟨hne', Or.inl ⟨h.2.1, h.2.2, h.1⟩⟩
        (JointIn.site (mem_jointSites.1 hx))))

/-- **The closure contains the nearest-neighbour components of its seed (T5).**  Every site reached
from a seed site `s ∈ U` by a chain of nearest-neighbour steps through incidence sites (each step
inside the incidence sites of one of the two operators) lies in the joint closure.  For the sites
of `X₁ ∩ Ω₁` the incidence-site condition is automatic, so the closure contains the nearest-neighbour
components of `X₁ ∩ Ω₁(H)` that meet `U`. -/
theorem jointSites_nn_component {s y : CTorus d L N₁ m₁ K} (hs : s ∈ U)
    (h : Relation.ReflTransGen (fun x y : CTorus d L N₁ m₁ K =>
      (Adj x y ∧ x ∈ incSites C Hb a ν X₁ 𝒞 ∧ y ∈ incSites C Hb a ν X₁ 𝒞) ∨
      (Adj x y ∧ x ∈ incSites C Hm a ν X₁ 𝒞 ∧ y ∈ incSites C Hm a ν X₁ 𝒞)) s y) :
    y ∈ jointSites C Hb Hm a ν X₁ 𝒞 U := by
  induction h with
  | refl => exact seed_mem_jointSites hs
  | tail _ hstep ih => exact jointSites_nn_step ih hstep

end Seed

end Dec2

end Balaban.Localization
