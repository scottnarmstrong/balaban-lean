/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2Background

/-!
# The decoupled background field at labelled cut parameters

P7 (3.22)–(3.25) compares the old and the new background configuration of the operation `R`
(two generating sets of the scale `k`), and the localization expansion of the difference
(P3 §4) needs both as functions of **one** vector of cut parameters.  The cut parameters are
indexed by labels `c i` (`i : ι`) of cubes; a cover `C` reads them through a label map `π` from
its own cubes to the labels (`labParams C π c s`: `s i` at a cube `P` with `π P = c i`, `1` at
every other cube).  For the cover of the new generating set `π` is the identity on its cubes; for
the old one it is the cube of the new set above (Lemma 2 of the design note).  The parameters
enter the cube parametrix `G*_s = ∑_z s_z χ_z G^{(z)}` of each operator with its own cover.

* `labS`, `labParams`: the label vector and the parameters of a cover;
* `analyticAt_labParams`, `norm_labParams_lt`, `labParams_one`;
* `decBgField_eq_of_analytic`: the decoupled background field (`Dec2.decBgField`) is the value of
  the analytic map of Theorem I-4b (i) (`Dec2.i4b_analytic`) on its domain;
* `analyticOnNhd_decBgField_comp`: `(u, v) ↦ decBgField (p v) (D u)` is analytic on `Su ×ˢ Sv`
  for analytic data and parameter maps landing in the domain of Theorem I-4b, `Su`, `Sv` open;
* `decBgField_one_eq`: at all parameters `1` it is the background field `bgFieldC` (`i4b_one`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis

/-! ### The label vector -/

section Labels

variable {d L N₁ m₁ K : ℕ} {ι : Type*}

open Classical in
/-- **The label vector of the cut parameters**: `s i` at the label `c i`, `1` at every other
label. -/
noncomputable def labS (c : ι → ℕ × CTorus d L N₁ m₁ K) (s : ι → ℂ)
    (q : ℕ × CTorus d L N₁ m₁ K) : ℂ :=
  if h : ∃ i, c i = q then s h.choose else 1

theorem labS_of_eq {c : ι → ℕ × CTorus d L N₁ m₁ K} (hc : Function.Injective c) (s : ι → ℂ)
    (i : ι) : labS c s (c i) = s i := by
  classical
  unfold labS
  split_ifs with h
  · exact congrArg s (hc h.choose_spec)
  · exact absurd ⟨i, rfl⟩ h

theorem labS_of_not_mem {c : ι → ℕ × CTorus d L N₁ m₁ K} (s : ι → ℂ)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : ∀ i, c i ≠ q) : labS c s q = 1 := by
  classical
  unfold labS
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    exact absurd hi (hq i)
  · rfl

theorem labS_one (c : ι → ℕ × CTorus d L N₁ m₁ K) (q : ℕ × CTorus d L N₁ m₁ K) :
    labS c (fun _ => (1 : ℂ)) q = 1 := by
  classical
  unfold labS
  split_ifs <;> rfl

theorem norm_labS_lt (c : ι → ℕ × CTorus d L N₁ m₁ K) {s : ι → ℂ} {R : ℝ} (hR : 1 < R)
    (hs : ∀ i, ‖s i‖ < R) (q : ℕ × CTorus d L N₁ m₁ K) : ‖labS c s q‖ < R := by
  classical
  unfold labS
  split_ifs
  · exact hs _
  · simpa using hR

theorem norm_labS_le (c : ι → ℕ × CTorus d L N₁ m₁ K) {s : ι → ℂ} {R : ℝ} (hR : 1 ≤ R)
    (hs : ∀ i, ‖s i‖ ≤ R) (q : ℕ × CTorus d L N₁ m₁ K) : ‖labS c s q‖ ≤ R := by
  classical
  unfold labS
  split_ifs
  · exact hs _
  · simpa using hR

variable [Fintype ι]

theorem analyticAt_labS (c : ι → ℕ × CTorus d L N₁ m₁ K) (q : ℕ × CTorus d L N₁ m₁ K)
    (s₀ : ι → ℂ) : AnalyticAt ℂ (fun s : ι → ℂ => labS c s q) s₀ := by
  classical
  by_cases h : ∃ i, c i = q
  · have e : (fun s : ι → ℂ => labS c s q) =
        fun s => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) h.choose) s := by
      funext s
      unfold labS
      split_ifs
      rfl
    rw [e]
    exact ContinuousLinearMap.analyticAt _ _
  · have e : (fun s : ι → ℂ => labS c s q) = fun _ => 1 := by
      funext s
      unfold labS
      split_ifs
      rfl
    rw [e]
    exact analyticAt_const

/-- **The parameters of a cover `C` read from the label vector through the label map `π`.** -/
noncomputable def labParams (C : DecCover d L N₁ m₁ K)
    (π : ℕ × CTorus d L N₁ m₁ K → ℕ × CTorus d L N₁ m₁ K) (c : ι → ℕ × CTorus d L N₁ m₁ K)
    (s : ι → ℂ) : Dec2.DecParams C :=
  fun P => labS c s (π P.1)

theorem analyticAt_labParams (C : DecCover d L N₁ m₁ K)
    (π : ℕ × CTorus d L N₁ m₁ K → ℕ × CTorus d L N₁ m₁ K) (c : ι → ℕ × CTorus d L N₁ m₁ K)
    (s₀ : ι → ℂ) : AnalyticAt ℂ (fun s => labParams C π c s) s₀ := by
  rw [analyticAt_pi_iff]
  intro P
  exact analyticAt_labS c (π P.1) s₀

omit [Fintype ι] in
theorem norm_labParams_lt (C : DecCover d L N₁ m₁ K)
    (π : ℕ × CTorus d L N₁ m₁ K → ℕ × CTorus d L N₁ m₁ K) (c : ι → ℕ × CTorus d L N₁ m₁ K)
    {s : ι → ℂ} {R : ℝ} (hR : 1 < R) (hs : ∀ i, ‖s i‖ < R) (P : C.cubeIdx) :
    ‖labParams C π c s P‖ < R :=
  norm_labS_lt c hR hs _

omit [Fintype ι] in
theorem labParams_one (C : DecCover d L N₁ m₁ K)
    (π : ℕ × CTorus d L N₁ m₁ K → ℕ × CTorus d L N₁ m₁ K) (c : ι → ℕ × CTorus d L N₁ m₁ K) :
    labParams C π c (fun _ => 1) = fun _ => 1 := by
  funext P
  exact labS_one c _

end Labels

/-! ### The decoupled background field as an analytic function -/

section Field

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ}

/-- **The decoupled background field is the value of the analytic map of Theorem I-4b (i)** on the
domain of the theorem: parameters `|s_P| < e^κ` and a datum of the union domain. -/
theorem decBgField_eq_of_analytic {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase C H a ν Kc Cx) (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F : Dec2.DecParams C × RawData d L (N₁ * L ^ m₁) K N →
      (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ)}
    (hF : ∀ (s : Dec2.DecParams C) (D : BgData H N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC H (bgC0 d L N) (c7 d L N BG κ) ν D →
      ∀ (φ : H.Ω 1 × Fin N → ℂ) (α : H.Ω 1 → ℂ),
        Dec2.IsDecBg C H a ν (rho4 d L N BG κ) s D φ α → F (s, (D.Ψ, D.h)) = (φ, α))
    {s : Dec2.DecParams C} (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData H N}
    (hD : InUnionDomainC H (bgC0 d L N) (c7 d L N BG κ) ν D) :
    Dec2.decBgField C H a ν (rho4 d L N BG κ) s D = (F (s, (D.Ψ, D.h))).1 ∧
      Dec2.decBgMult C H a ν (rho4 d L N BG κ) s D = (F (s, (D.Ψ, D.h))).2 := by
  obtain ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hDd⟩ := hD
  obtain ⟨φ, α, hI, hu, -⟩ := Dec2.i4b_exists_unique hS S HB hκ hM (s := s)
    (fun P => (hs P).le) hδ0 hδε hε hδ hνε hDd
  obtain ⟨e1, e2⟩ := Dec2.decBg_eq hI hu
  have hFv := hF s D hs ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hDd⟩ φ α hI
  rw [e1, e2, hFv]
  exact ⟨rfl, rfl⟩

/-- **Joint analyticity of the decoupled background field** in the data and the parameters: for a
data map `D` with analytic raw data on an open set `Su`, landing in the union domain, and a parameter
map `p` analytic on an open set `Sv` with `|p v P| < e^κ`, the field `(u, v) ↦ φ_k(p v; D u)` is
analytic on `Su ×ˢ Sv`. -/
theorem analyticOnNhd_decBgField_comp {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase C H a ν Kc Cx) (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] [NormedAddCommGroup V]
    [NormedSpace ℂ V] {Su : Set U} {Sv : Set V} (hSu : IsOpen Su) (hSv : IsOpen Sv)
    {D : U → BgData H N} (hDan : AnalyticOnNhd ℂ (fun u => ((D u).Ψ, (D u).h)) Su)
    (hDdom : ∀ u ∈ Su, InUnionDomainC H (bgC0 d L N) (c7 d L N BG κ) ν (D u))
    {p : V → Dec2.DecParams C} (hpan : AnalyticOnNhd ℂ p Sv)
    (hp : ∀ v ∈ Sv, ∀ P, ‖p v P‖ < Real.exp κ) :
    AnalyticOnNhd ℂ (fun q : U × V => Dec2.decBgField C H a ν (rho4 d L N BG κ) (p q.2) (D q.1))
      (Su ×ˢ Sv) := by
  obtain ⟨F, hFan, hF⟩ := Dec2.i4b_analytic hS S HB hκ hM
  intro q hq
  -- the analytic composite
  have hcomp : AnalyticAt ℂ (fun q : U × V => (F (p q.2, ((D q.1).Ψ, (D q.1).h))).1) q := by
    have hin : AnalyticAt ℂ (fun q : U × V => (p q.2, ((D q.1).Ψ, (D q.1).h))) q :=
      ((hpan q.2 hq.2).comp analyticAt_snd).prod ((hDan q.1 hq.1).comp analyticAt_fst)
    have hFq : AnalyticAt ℂ F (p q.2, ((D q.1).Ψ, (D q.1).h)) :=
      hFan _ ⟨hp q.2 hq.2, D q.1, hDdom q.1 hq.1, rfl⟩
    exact analyticAt_fst.comp (AnalyticAt.comp (g := F)
      (f := fun q : U × V => (p q.2, ((D q.1).Ψ, (D q.1).h))) hFq hin)
  refine hcomp.congr ?_
  have hopen : IsOpen (Su ×ˢ Sv) := hSu.prod hSv
  filter_upwards [hopen.mem_nhds hq] with q' hq'
  exact ((decBgField_eq_of_analytic hS S HB hκ hM hF (hp q'.2 hq'.2) (hDdom q'.1 hq'.1)).1).symm

/-- **At all parameters `1` the decoupled background field is the background field** of Theorem
5.2 (`bgFieldC`), for a datum of the union domain (`Dec2.i4b_one`). -/
theorem decBgField_one_eq {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase C H a ν Kc Cx) (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {D : BgData H N}
    (hD : InUnionDomainC H (bgC0 d L N) (c7 d L N BG κ) ν D) :
    Dec2.decBgField C H a ν (rho4 d L N BG κ) (fun _ => 1) D = bgFieldC H a ν (bgC0 d L N) D := by
  obtain ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hDd⟩ := hD
  obtain ⟨φ, α, hI, hu, -⟩ := Dec2.i4b_exists_unique hS S HB hκ hM (s := fun _ => 1)
    (fun P => by simpa using Real.one_le_exp hκ) hδ0 hδε hε hδ hνε hDd
  obtain ⟨-, h1, -⟩ := Dec2.i4b_one hS S HB hκ hM hδ0 hδε hε hδ hνε hDd hI
  rw [(Dec2.decBg_eq hI hu).1, h1]

end Field

end Balaban.LargeField
