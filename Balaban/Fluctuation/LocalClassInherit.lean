/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2
public import Balaban.SmallField.XiPerturb
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The inherited levels of the local successor class: domain monotonicity

P4 Theorem 2 (1.8), p. 682: the terms `ℰ^{(j)}`, `ℳ^{(j)}`, `j ≤ k`, of the class at step `k + 1` are
the terms of the class at step `k`, restricted to the new (smaller) domains, with the same
generating sets `𝔹_j(X)` and the same bounds.  In Lean the terms of a level `j ≤ k` are kept
(`Tm'.E j = Tm.E j`, `Tm'.M j = Tm.M j`, `Tm'.gs j = Tm.gs j`) and the clauses of these levels
transfer to every field domain whose level-`j` part is contained in the old one
(`SFTermClauses.inherit_le`, the restriction `SFTermClauses.mono` level by level).

For the wide domain `xiFieldDom a μ ε` (`Ξ^c_j(𝔹; 1, ε_j)` with the kernel sequence `a` and the
background mass `μ`) the inclusion holds when the radius decreases at fixed `(a, μ)`
(`xiFieldDom_dom_of_eps_le`).  The step changes `(a, μ)` as follows.

* **Kernel weights.**  Along the free flow `a_{n+1} = a₁ a_n / (a_n + a₁ L⁻²)` (`compWeight_succ`)
  the weights of the connecting problem matched at step `k` do not depend on `k`:
  `aIdeal L k (compWeight L a₁ k) = compWeight L a₁` (`aIdeal_compWeight`).
* **Mass of the fluctuation step.**  The unrenormalized coefficient `ν_{k+1,u} = ν_k L²`
  (P4 (3.1)-(3.2)) has the same fine-unit mass: `physMass L (k + 1) (ν_k L²) = physMass L k ν_k`
  (`physMass_succ_mul_sq`).  Hence the main domain of the class (`IsSFFamily.toXi`) is **the same
  field domain** before and after the fluctuation step (`xiFieldDom_unrenorm_succ`), and the old
  terms keep all their clauses there.

**What is not proved here (the renormalized mass).**  The renormalization changes the fine mass
by the factor `(1 + ξ₃)/(1 + ξ₂)` (`Flow.nuSeq`: `ν_{k+1} = ν_k L² (1 + ξ k 2) / (1 + ξ k 1)`).  The
inclusion `Ξ^c_j(𝔹_j(X); 1, ε^{(k+1)}_j)` at the new mass `⊆ Ξ^c_j(𝔹_j(X); 1, ε^{(k)}_j)` at the old
mass is P4 (4.19) (proof deferred by P4 to the localization paper).  It needs (i) a strict gap
`ε^{(k)}_j - ε^{(k+1)}_j ≳ |ξ| ε_j`: P4 (H.1) takes `ε^{(k)}_j = α₀ (1 + Σ_{n ≥ k} n⁻²) L^{-jα}`
(tail indexed by the **step**), whereas the landed `Consts.eps` = `epsSeq` indexes the tail by the
**level** `j`, so `ε^{(k+1)}_j = ε^{(k)}_j` and there is no gap; (ii) the response of the
backgrounds of `𝔹_j(X)` to the change of mass (BG Proposition 5.1 with the source
`(μ' - μ)(h - φ)`) in the norms of `XiBounds`/`XiCBounds`, at the level `j` of the generating set;
the landed form (`exists_isRenSol`, `RenormExpLemma35.lean`) is stated on `XiCOne`, the top level
of the torus.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6

/-! ### The radius -/

section Radius

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}

theorem xiCBounds_mono_eps {ν σ ε ε₂ : ℝ} {Dr Dc : BgData G N}
    {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φr φc : G.Ω 1 × Fin N → ℂ}
    {αr αc : G.Ω 1 → ℂ} (hσ : 0 ≤ σ) (hε0 : 0 < ε) (hε : ε ≤ ε₂)
    (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc) :
    XiCBounds G ν σ ε₂ Dr Dc Ψ'' h'' φr φc αr αc := by
  have h1 : σ * ε ≤ σ * ε₂ := mul_le_mul_of_nonneg_left hε hσ
  have h2 : σ ^ 2 * ε ≤ σ ^ 2 * ε₂ := mul_le_mul_of_nonneg_left hε (by positivity)
  have hε2 : 0 < ε₂ := hε0.trans_le hε
  have hp : ∀ x : Torus d (N₀ * L ^ k), 0 < G.spacing x := fun x => by
    have := G.spacing_ge_one x; linarith
  have e : ∀ e : ℝ, 0 < e → (σ * e) ^ 2 / e = σ ^ 2 * e := fun e he => by field_simp
  refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x => ?_, fun x => ?_, fun x hx => ?_,
    fun z hz z' hz' hadj => ?_, fun x hx => ?_, fun x => ?_⟩
  · obtain ⟨g1, g2⟩ := hb.grad x hx μ
    exact ⟨g1.trans_le (div_le_div_of_nonneg_right h1 (hp x).le),
      g2.trans_le (div_le_div_of_nonneg_right h1 (hp x).le)⟩
  · exact (hb.lap x hx).trans_le (div_le_div_of_nonneg_right h2 (by have := hp x; positivity))
  · exact (hb.mult x).trans_le h2
  · exact (hb.val x).trans_le hε
  · exact (hb.close x hx).trans_le h2
  · exact (hb.collarBond z hz z' hz' hadj).trans_le h1
  · have := hb.hAbs x hx
    rw [e ε hε0] at this
    rw [e ε₂ hε2]
    exact this.trans_le h2
  · exact (hb.hDot x).trans_le (pow_le_pow_left₀ (mul_nonneg hσ hε0.le) h1 2)

/-- `Ξ^c_n(𝔹; σ, ε) ⊆ Ξ^c_n(𝔹; σ, ε₂)` for `ε ≤ ε₂` (the realizations are kept). -/
theorem xiC_mono_eps {a : ℕ → ℝ} {ν σ ε ε₂ : ℝ} {n : ℕ} {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ}
    {h₀ : Fin N → ℝ} {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hσ : 0 ≤ σ) (hε : ε ≤ ε₂)
    (h : XiC G a ν n σ ε Ψ₀ h₀ Ψ'' h'') : XiC G a ν n σ ε₂ Ψ₀ h₀ Ψ'' h'' := by
  obtain ⟨hs, hε0, Dr, Dc, hXr, hC, hU, hb⟩ := h
  exact ⟨hs, hε0.trans_le hε, Dr, Dc, ⟨hXr.1, hXr.2.1, xiBounds_mono hσ hε0.le hε hXr.2.2⟩, hC,
    hU, xiCBounds_mono_eps hσ hε0 hε hb⟩

end Radius

section Domain

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **Domain monotonicity in the radius** (P4 (4.19) at fixed coefficients): a pair of the level-`j`
domain of `xiFieldDom a μ ε'` lies in the level-`j` domain of `xiFieldDom a μ ε` when
`ε'_j ≤ ε_j`, for every generating set. -/
theorem xiFieldDom_dom_of_eps_le {a : ℕ → ℝ} {μ : ℝ} {ε ε' : ℕ → ℝ} {j : ℕ} (hε : ε' j ≤ ε j)
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Ψ h : Fld d L N₁ m₁ K N}
    (hp : (xiFieldDom a μ ε' : FieldDom d L N₁ m₁ K N ϱ).dom j G Ψ h) :
    (xiFieldDom a μ ε : FieldDom d L N₁ m₁ K N ϱ).dom j G Ψ h := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', e1, e2, hX⟩ := hp
  exact ⟨Ψ₀, h₀, Ψ'', h'', e1, e2, xiC_mono_eps zero_le_one hε hX⟩

end Domain

/-! ### The coefficients of the step -/

section Coefficients

/-- **The weights matched at step `k` along the free flow do not depend on `k`**:
`aIdeal L k (compWeight L a₁ k) = compWeight L a₁` (`a_n = a_k (1 - L^{-2k})/(1 - L^{-2n})` with
`a_k = a₁ (1 - L⁻²)/(1 - L^{-2k})`). -/
theorem aIdeal_compWeight {L k : ℕ} (hL : 2 ≤ L) (hk : 1 ≤ k) (a₁ : ℝ) :
    aIdeal L k (compWeight L a₁ k) = compWeight L a₁ := by
  funext n
  have hL1 : (1 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 1 < L)
  have hLk : (1 : ℝ) < (L : ℝ) ^ k := one_lt_pow₀ hL1 (by omega)
  have hne : (1 : ℝ) - (((L : ℝ) ^ k) ^ 2)⁻¹ ≠ 0 := by
    have h1 : (1 : ℝ) < ((L : ℝ) ^ k) ^ 2 := one_lt_pow₀ hLk (by norm_num)
    have : (((L : ℝ) ^ k) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    linarith
  unfold aIdeal compWeight
  rw [inv_pow, inv_pow, div_mul_cancel₀ _ hne]

/-- **The fine-unit mass of the fluctuation step is unchanged**: the unrenormalized coefficient
`ν_{k+1,u} = ν_k L²` (P4 (3.1)-(3.2)) has `ν_{k+1,u} L^{-2(k+1)} = ν_k L^{-2k}`. -/
theorem physMass_succ_mul_sq {L : ℕ} [NeZero L] (k : ℕ) (νk : ℝ) :
    physMass L (k + 1) (νk * (L : ℝ) ^ 2) = physMass L k νk := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  unfold physMass
  field_simp
  ring

/-- **The renormalized fine mass**: with `ν_{k+1} = ν_k L² (1 + x)/(1 + y)` (P4 (5.28), `Flow.nuSeq`
with `x = ξ₃`, `y = ξ₂`) the fine mass of the backgrounds is multiplied by `(1 + x)/(1 + y)`. -/
theorem physMass_succ_renorm {L : ℕ} [NeZero L] (k : ℕ) (νk x y : ℝ) :
    physMass L (k + 1) (νk * (L : ℝ) ^ 2 * (1 + x) / (1 + y)) =
      physMass L k νk * ((1 + x) / (1 + y)) := by
  have e : νk * (L : ℝ) ^ 2 * (1 + x) / (1 + y) = νk * (L : ℝ) ^ 2 * ((1 + x) / (1 + y)) := by
    ring
  rw [e, ← physMass_succ_mul_sq k]
  unfold physMass
  ring

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The main domain of the class is unchanged by the fluctuation step** (`IsSFFamily.toXi`:
`xiFieldDom (aIdeal L k a_k) (physMass L k ν_k) ε`): along the free flow (`a_k = compWeight L a₁ k`)
and with the unrenormalized coefficient `ν_{k+1,u} = ν_k L²`, the field domains of the steps `k`
and `k + 1` coincide (for every torus).  So the terms of the levels `j ≤ k` satisfy at step `k + 1`
the clauses they satisfied at step `k` (`SFTermClauses.inherit_le` with the identity inclusion). -/
theorem xiFieldDom_unrenorm_succ (hL : 2 ≤ L) {k : ℕ} (hk : 1 ≤ k) (a₁ νk : ℝ) (ε : ℕ → ℝ) :
    (xiFieldDom (aIdeal L (k + 1) (compWeight L a₁ (k + 1)))
        (physMass L (k + 1) (νk * (L : ℝ) ^ 2)) ε : FieldDom d L N₁ m₁ K N ϱ) =
      xiFieldDom (aIdeal L k (compWeight L a₁ k)) (physMass L k νk) ε := by
  rw [aIdeal_compWeight hL (by omega), aIdeal_compWeight hL hk, physMass_succ_mul_sq]

end Coefficients

/-! ### The inherited clauses -/

section Inherit

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The clauses of the inherited levels** (P4 Theorem 2 (1.8): `ℰ^{(j)}_{k+1} = ℰ^{(j)}_k`,
`ℳ^{(j)}_{k+1} = ℳ^{(j)}_k` for `j ≤ k`, restricted to the new domains).  Let `Tm` satisfy the term
clauses on `Dom` and let `Tm'` agree with `Tm` at the levels `j ≤ k` (terms and generating sets,
`gs = 𝔹_j(X)` unchanged).  If the level-`j` parts of `Dom'` lie in those of `Dom` for `j ≤ k`, then
the slices at the levels `1 ≤ j ≤ k` of all clauses of `SFTermClauses P Dom' Tm'` hold (the bounds
`E₀ e^{-κ d_j(X)}`, `c₉ ξ_j^{…} e^{-κ d_j(X)}` of the old class are kept). -/
theorem SFTermClauses.inherit_le {P : Consts} {Dom Dom' : FieldDom d L N₁ m₁ K N ϱ}
    {Tm Tm' : Terms d L N₁ m₁ K N ϱ} (hcl : SFTermClauses P Dom Tm) {k : ℕ} (hkK : k ≤ K)
    (hsub : ∀ j, j ≤ k → ∀ G Ψ h, Dom'.dom j G Ψ h → Dom.dom j G Ψ h)
    (hE : ∀ j, j ≤ k → Tm'.E j = Tm.E j) (hM : ∀ j, j ≤ k → Tm'.M j = Tm.M j)
    (hgs : ∀ j, j ≤ k → Tm'.gs j = Tm.gs j) :
    -- `gs_spec`
    (∀ j, 1 ≤ j → j ≤ k → ∀ X, IsPolyDom P.m₀ j X →
      X ⊆ ↑((Tm'.gs j X).Ω 1) ∧ ∀ i, j < i → (Tm'.gs j X).Ω i = ∅) ∧
    -- `analyticE`
    (∀ j, 1 ≤ j → j ≤ k → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N => Tm'.E j y X p.1 p.2)
        {p | Dom'.dom j (Tm'.gs j X) p.1 p.2}) ∧
    -- `analyticM`
    (∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N =>
          Tm'.M j x X p.1 p.2.1 p.2.2)
        {p | Dom'.dom j (Tm'.gs j X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1}) ∧
    -- `rotE`
    (∀ j, 1 ≤ j → j ≤ k → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X →
      ∀ R : Matrix (Fin N) (Fin N) ℂ, IsRot R → ∀ Ψ h, Dom'.dom j (Tm'.gs j X) Ψ h →
        Dom'.dom j (Tm'.gs j X) (rotField R Ψ) (rotField R h) →
        Tm'.E j y X (rotField R Ψ) (rotField R h) = Tm'.E j y X Ψ h) ∧
    -- `pavingGS`
    (∀ j, 1 ≤ j → j ≤ k → ∀ X, IsPolyDom P.m₀ j X →
      ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L P.m₀ j, ∀ i,
        (((Tm'.gs j (r '' X)).Ω i : Finset (CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K)) =
          r '' (((Tm'.gs j X).Ω i : Finset (CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K))) ∧
    -- `eucE`
    (∀ j, 1 ≤ j → j ≤ k → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X →
      ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L P.m₀ j, ∀ Ψ h,
        Dom'.dom j (Tm'.gs j X) Ψ h → Dom'.dom j (Tm'.gs j (r '' X)) (actField r Ψ) (actField r h) →
        Tm'.E j (blockBase L j (r y)) (r '' X) (actField r Ψ) (actField r h) = Tm'.E j y X Ψ h) ∧
    -- `eucEloc`
    (∀ j, 1 ≤ j → j ≤ k → ∀ hjK : j ≤ K, ∀ y,
      ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j, ∀ Ψ h,
        Dom'.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjK) Ψ h →
        Dom'.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjK) (actField r Ψ) (actField r h) →
        Eloc P.m₀ Tm' j (blockBase L j (r y)) (actField r Ψ) (actField r h) =
          Eloc P.m₀ Tm' j y Ψ h) ∧
    -- `rotM`
    (∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X →
      ∀ R : Matrix (Fin N) (Fin N) ℂ, IsRot R → ∀ Ψ h g, Dom'.dom j (Tm'.gs j X) Ψ h →
        Dom'.dom j (Tm'.gs j X) (rotField R Ψ) (rotField R h) →
        Tm'.M j x X (rotField R Ψ) (rotField R h) (rotField R g) = R.mulVec (Tm'.M j x X Ψ h g)) ∧
    -- `eucM`
    (∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X →
      ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L P.m₀ j, ∀ Ψ h g,
        Dom'.dom j (Tm'.gs j X) Ψ h → Dom'.dom j (Tm'.gs j (r '' X)) (actField r Ψ) (actField r h) →
        Tm'.M j (r x) (r '' X) (actField r Ψ) (actField r h) (actField r g) = Tm'.M j x X Ψ h g) ∧
    -- `eucMloc`
    (∀ j, 1 ≤ j → j ≤ k → ∀ hjK : j ≤ K, ∀ x,
      ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j, ∀ Ψ h g,
        Dom'.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjK) Ψ h →
        Dom'.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjK) (actField r Ψ) (actField r h) →
        Mloc P.m₀ Tm' j (r x) (actField r Ψ) (actField r h) (actField r g) =
          Mloc P.m₀ Tm' j x Ψ h g) ∧
    -- `localE`
    (∀ j, j ≤ k → ∀ y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
      Tm'.E j y X Ψ h = Tm'.E j y X Ψ' h') ∧
    -- `localM`
    (∀ j, j ≤ k → ∀ x X Ψ Ψ' h h' g g', (∀ z ∈ X, Ψ z = Ψ' z ∧ h z = h' z ∧ g z = g' z) →
      Tm'.M j x X Ψ h g = Tm'.M j x X Ψ' h' g') ∧
    -- `boundE`
    (∀ j, 1 ≤ j → j ≤ k → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X → ∀ Ψ h,
      Dom'.dom j (Tm'.gs j X) Ψ h → ‖Tm'.E j y X Ψ h‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X)) ∧
    -- `boundM`
    (∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X → ∀ Ψ h g,
      Dom'.dom j (Tm'.gs j X) Ψ h → Def6.l1 g < 1 →
      vn (Tm'.M j x X Ψ h g) <
        P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
          Real.exp (-P.κ * sizeJ P.m₀ j X)) := by
  have hEl : ∀ j, j ≤ k → ∀ y (Ψ h : Fld d L N₁ m₁ K N),
      Eloc P.m₀ Tm' j y Ψ h = Eloc P.m₀ Tm j y Ψ h := fun j hj y Ψ h => by
    unfold Eloc; rw [hE j hj]
  have hMl : ∀ j, j ≤ k → ∀ x (Ψ h g : Fld d L N₁ m₁ K N),
      Mloc P.m₀ Tm' j x Ψ h g = Mloc P.m₀ Tm j x Ψ h g := fun j hj x Ψ h g => by
    unfold Mloc; rw [hM j hj]
  refine ⟨fun j hj1 hjk X hX => ?_, fun j hj1 hjk y X hX hy => ?_,
    fun j hj1 hjk x X hX hx => ?_, fun j hj1 hjk y X hX hy R hR Ψ h h1 h2 => ?_,
    fun j hj1 hjk X hX r hr i => ?_, fun j hj1 hjk y X hX hy r hr Ψ h h1 h2 => ?_,
    fun j hj1 hjk hjK y r hr Ψ h h1 h2 => ?_, fun j hj1 hjk x X hX hx R hR Ψ h g h1 h2 => ?_,
    fun j hj1 hjk x X hX hx r hr Ψ h g h1 h2 => ?_, fun j hj1 hjk hjK x r hr Ψ h g h1 h2 => ?_,
    fun j hjk y X Ψ Ψ' h h' hX => ?_, fun j hjk x X Ψ Ψ' h h' g g' hX => ?_,
    fun j hj1 hjk y X hX hy Ψ h h1 => ?_, fun j hj1 hjk x X hX hx Ψ h g h1 hg => ?_⟩
  · rw [hgs j hjk]; exact hcl.gs_spec j hj1 (hjk.trans hkK) X hX
  · rw [hE j hjk, hgs j hjk]
    exact (hcl.analyticE j hj1 (hjk.trans hkK) y X hX hy).mono fun _ hp => hsub j hjk _ _ _ hp
  · rw [hM j hjk, hgs j hjk]
    exact (hcl.analyticM j hj1 (hjk.trans hkK) x X hX hx).mono fun _ hp =>
      ⟨hsub j hjk _ _ _ hp.1, hp.2⟩
  · rw [hgs j hjk] at h1 h2
    rw [hE j hjk]
    exact hcl.rotE j hj1 (hjk.trans hkK) y X hX hy R hR Ψ h (hsub j hjk _ _ _ h1)
      (hsub j hjk _ _ _ h2)
  · rw [hgs j hjk]; exact hcl.pavingGS j hj1 (hjk.trans hkK) X hX r hr i
  · rw [hgs j hjk] at h1 h2
    rw [hE j hjk]
    exact hcl.eucE j hj1 (hjk.trans hkK) y X hX hy r hr Ψ h (hsub j hjk _ _ _ h1)
      (hsub j hjk _ _ _ h2)
  · rw [hEl j hjk, hEl j hjk]
    exact hcl.eucEloc j hj1 hjK y r hr Ψ h (hsub j hjk _ _ _ h1) (hsub j hjk _ _ _ h2)
  · rw [hgs j hjk] at h1 h2
    rw [hM j hjk]
    exact hcl.rotM j hj1 (hjk.trans hkK) x X hX hx R hR Ψ h g (hsub j hjk _ _ _ h1)
      (hsub j hjk _ _ _ h2)
  · rw [hgs j hjk] at h1 h2
    rw [hM j hjk]
    exact hcl.eucM j hj1 (hjk.trans hkK) x X hX hx r hr Ψ h g (hsub j hjk _ _ _ h1)
      (hsub j hjk _ _ _ h2)
  · rw [hMl j hjk, hMl j hjk]
    exact hcl.eucMloc j hj1 hjK x r hr Ψ h g (hsub j hjk _ _ _ h1) (hsub j hjk _ _ _ h2)
  · rw [hE j hjk]; exact hcl.localE j y X Ψ Ψ' h h' hX
  · rw [hM j hjk]; exact hcl.localM j x X Ψ Ψ' h h' g g' hX
  · rw [hgs j hjk] at h1
    rw [hE j hjk]
    exact hcl.boundE j hj1 (hjk.trans hkK) y X hX hy Ψ h (hsub j hjk _ _ _ h1)
  · rw [hgs j hjk] at h1
    rw [hM j hjk]
    exact hcl.boundM j hj1 (hjk.trans hkK) x X hX hx Ψ h g (hsub j hjk _ _ _ h1) hg

/-- **The inherited clauses on the radius-shrunk wide domain**: `SFTermClauses.inherit_le` with
`Dom = xiFieldDom a μ ε`, `Dom' = xiFieldDom a μ ε'`, `ε'_j ≤ ε_j` for `j ≤ k` (same kernel weights
and mass; for the fluctuation step these are the coefficients of both classes,
`xiFieldDom_unrenorm_succ`).  Stated as the inclusion of the level-`j` domains used by
`SFTermClauses.inherit_le`. -/
theorem xiFieldDom_sub_of_eps_le {a : ℕ → ℝ} {μ : ℝ} {ε ε' : ℕ → ℝ} {k : ℕ}
    (hε : ∀ j, j ≤ k → ε' j ≤ ε j) :
    ∀ j, j ≤ k → ∀ (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (Ψ h : Fld d L N₁ m₁ K N),
      (xiFieldDom a μ ε' : FieldDom d L N₁ m₁ K N ϱ).dom j G Ψ h →
      (xiFieldDom a μ ε : FieldDom d L N₁ m₁ K N ϱ).dom j G Ψ h :=
  fun j hj _ _ _ hp => xiFieldDom_dom_of_eps_le (hε j hj) hp

end Inherit

end Balaban.SmallField.Def6v2
