/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5FluctChain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma DL with the fluctuation: the point facts

The composite of P3 (4.41) at a realizable point `Θ = D ∈ Ξ^c_K(𝔹_{k+1}; 1, ε')`, a decoupling vector
`s` in the polydisc and a fluctuation `ψ'` with `|ψ'| < δ₁` on the data sites of `H⁻`:

`F(s; Θ, ψ') = 𝓔(X; ψ(𝔹_j(X), 𝔹_k(X); ψ(𝔹_k(X), 𝔹_{k+1}; Θ, s) + δψ(𝔹_k(X), 𝔹_k; ψ', s)))`

(with `δψ` the composition of the pair `(δφ, ψ')`, P3 (4.17)) is computed through the analytic
functions `F₁` (Theorem I-4b), `Sol` (Theorem I-4a, mode P) and `F_k` (Theorem 7.2), and for a
layer-constant `ψ'` its argument lies in `Ξ^c_j(𝔹_j(X); C₀, ε₃)` (`point_facts_fl`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset Matrix

section Setting

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}

/-- **The numerical conditions of the fluctuation** (beyond `ChainNum`): `δ₁` is the radius of the
ball of `ψ'`, `δfl ≥ N (5 K₂' + 1) δ₁` bounds the composed fluctuation (FLDATUM (4)),
`ε₂ = C₀² ε' + K₂' δ₃`,
`ε₃ = ε₂ + K₂' δfl`; the constants `BG₂` belong to the Green's function family of `(C, H⁻)`. -/
structure FlNum (d L N : ℕ) [NeZero L] (BG BG₂ κ eps δ₃ δ₁ δfl : ℝ) : Prop where
  δ₁_pos : 0 < δ₁
  δ₁_le : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8)
  B_le : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤
    deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8)
  B_one : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤ 1
  phi_lt : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2
  flb : N * (5 * (cK2' d L N (famConst d L BG₂ κ) * δ₁) + δ₁) ≤ δfl
  δfl_nn : 0 ≤ δfl
  δfl_le_one : δfl ≤ 1
  c1_f : xiC1 d * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃) + 5 * δfl ≤ bgC1 d L N
  star_f : δfl ≤ deltaStar d L N
  K1s_f : bgK1 d L N * (xiC1 d * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃)) ≤ deltaStar d L N
  sm_f : bgK1 d L N * (xiC1 d * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃)) +
    cK2 d L N * δfl < bgC0 d L N
  small₃ : (4 * d + 6) * ((2 * d + 1) * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ +
    xiK2 d L N * δfl)) ≤ 1
  th₃ : xiC1 d * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) ≤ thm73C1 d L N

end Setting

section Psi

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {ν : ℝ}

/-- The datum of a point of `Ψ̃^c(δ, ε)` is of norm `< 1 + 2δ + ε` at the data sites. -/
theorem vn_Psi_lt {δ ε : ℝ} (hδ : 0 ≤ δ) {D : BgData G N} (hD : InDomainC G ν δ ε D)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ dataSites G) : vn (D.Ψ x) < 1 + 2 * δ + ε := by
  obtain ⟨Ψ, h, Ψ', h', hP, hΨ, -⟩ := hD
  have h1 : vn (D.Ψ x) ≤ vn (fun i => D.Ψ x i - (Ψ x i : ℂ)) + vn (fun i => (Ψ x i : ℂ)) :=
    vn_le_sub_add _ _
  have e : (fun i => D.Ψ x i - (Ψ x i : ℂ)) = Ψ' x := by
    funext i; rw [hΨ x hx i]; ring
  rw [e, vn_ofReal] at h1
  have h2 := hP.c2a x hx
  have h3 : rn (Ψ x) ≤ 1 + δ := by
    have hr2 := hP.r2 x hx
    have hs : ∑ i, Ψ x i ^ 2 ≤ (1 + δ) ^ 2 := by
      have := (abs_lt.1 hr2).2
      nlinarith
    unfold rn
    calc Real.sqrt (∑ i, Ψ x i ^ 2) ≤ Real.sqrt ((1 + δ) ^ 2) := Real.sqrt_le_sqrt hs
      _ = 1 + δ := Real.sqrt_sq (by linarith)
  linarith

omit [NeZero L] in
theorem K4_pos {BG κ : ℝ} (hBG : 0 ≤ BG) (hd : 0 < d) : 0 < K4 d L N BG κ := by
  have hB1 := famConst_ge_one (L := L) hBG κ hd
  have h1 := cK2'_nonneg (d := d) (L := L) (N := N) (B := famConst d L BG κ) (by linarith)
  have h2 := lemma53Const_pos d L
  unfold K4
  have : (0 : ℝ) ≤ (N + 1 : ℝ) * cK2' d L N (famConst d L BG κ) := by positivity
  positivity

end Psi

section Facts

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}

variable (Gp Gk Hm) in
/-- The raw datum of `𝔹_k(X)` obtained by composing the background field with `Θ = u.1` and the
fluctuation field `δφ(ψ', s)` with `ψ' = u.2`: `ψ(𝔹_k(X), 𝔹_{k+1}; Θ, s) + δψ(𝔹_k(X), 𝔹_k; ψ', s)`,
with `δψ = composeField 𝔹_k(X) 𝔹_k a δφ ψ'` (P3 (4.17)). -/
noncomputable def D1rawFl (a : ℕ → ℝ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N →
      (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (s : Dec2.DecParams (coverOf Gp))
    (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) :
    RawData d L (N₁ * L ^ m₁) K N :=
  (fun x i => composeField Gk Gp a (F₁ (s, u.1)).1 u.1.1 x i +
      composeField Gk Hm a (Sol (s, flEdat Gp Hm (F₁ (s, u.1)) u.1.1 u.2)).1 u.2 x i,
    fun x i => by classical exact if x ∈ Gk.Ω 1 then u.1.2 x i else 0)

variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

/-- **The hypotheses of the fluctuation** on the pair `(C, H⁻)`, `C = coverOf Gp`: the constants of
the Green's function family, the pair structure `FootLocal`, the order `𝔹_k(X) ≺ 𝔹_k ≺ 𝔹_{k+1}` and
the dependency of the composition on `X₁`. -/
structure FlSetting (N : ℕ) (Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁) (Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm)
    (a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ) (X₁f : Finset (CTorus d L N₁ m₁ K)) : Prop where
  hS2 : Dec2.DecSpecs d L Kc Cx c₂ BG₂
  SM : Dec2.FootLocal (coverOf Gp) Hm (compWeight L a₁) ν Kc Cx
  hM2 : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁
  hPm : Precedes Gk Hm
  hPmp : Precedes Hm Gp
  depm : ∀ x ∈ dataSites Gk, ∀ y ∈ composeDep Gk Hm x, y ∈ X₁f
  num : FlNum d L N BG BG₂ κ eps δ₃ δ₁ δfl

/-- **The point facts of Lemma DL with the fluctuation, with a composition constant
`1 ≤ b ≤ C₀`**: the composed datum of `𝔹_k(X)` lies in `Ξ^c_K(𝔹_k(X); 1, ε₃)` and its composition
with `𝔹_j(X)` in `Ξ^c_j(𝔹_j(X); b, ε₃)`, `ε₃ = b² ε' + K₂' δ₃ + K₂' δfl`.  At `b = 1` (P3 (4.29),
(4.37)): `Ξ^c_j(𝔹_j(X); 1, ε' + K₂' δ₃ + K₂' δfl)`. -/
theorem point_facts_fl_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Fk : RawData d L (N₁ * L ^ m₁) K N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
      s ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D)
    {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ} (hψ : ∀ x ∈ dataSites Hm, vn (ψ' x) < δ₁)
    (hψc : IsLayerConstant Hm ψ') :
    ∃ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ),
      IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α ∧ F₁ (s, rawOf D) = (φ, α) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁
        (flEdat Gp Hm (φ, α) D.Ψ ψ') ∧
      (Sol (s, flEdat Gp Hm (φ, α) D.Ψ ψ')).1 = δφ ∧
      XiCData Gk (compWeight L a₁) ν K 1
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
        (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc) ∧
      D1rawFl Gp Gk Hm (compWeight L a₁) F₁ Sol s (rawOf D, ψ') =
        rawOf (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc) ∧
      D2raw Gk Gj (compWeight L a₁) Fk
          (rawOf (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)) =
        rawOf (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc))
          (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)) ∧
      XiCData Gj (compWeight L a₁) ν j b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
        (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc))
          (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)) := by
  classical
  have hd0 : 0 < d := by have := hB.HBp.hd; omega
  have hκ0 := hB.hκ.le
  have hE1 : 1 ≤ Real.exp κ := Real.one_le_exp hκ0
  have hc1 := one_le_xiC1 d
  have hε := hB.num.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hDom := xiCData_inDomainC hB.HBp hB.num.small1 hD
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hB.num.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hB.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC hB.HBp hδ0 hδ0' hδ1 hDom
  have hsle : ∀ P, ‖s P‖ ≤ Real.exp κ := fun P => (hs P).le
  -- the old facts
  obtain ⟨φ, α, hI, hFeq, hst, hD1, -, -⟩ := point_facts_of_one_le hb₁ hbC hB hF₁ hFk hs hs1 hD
  obtain ⟨φ', α', hI', hu', -, -, hbb⟩ := i4b_exists_unique hB.hS hB.Sp hB.HBp hB.hκ.le hB.hM
    hsle hδ0 le_rfl hδ0' hδ1 hνε hDom
  obtain ⟨rfl, rfl⟩ := hu' φ α hI
  -- the strict inequalities of the fluctuation data
  have hK4 : 0 < K4 d L N BG κ := K4_pos hB.hS.fam.2.1 hd0
  have hB4 : 0 < K4 d L N BG κ * (xiC1 d * eps) := mul_pos hK4 hδ0
  have hphi : ∀ x : Gp.Ω 1, vn (fun i => φ (x, i)) < 3 / 2 := by
    intro x
    have hxd : (x : CTorus d L N₁ m₁ K) ∈ dataSites Gp := (mem_dataSites Gp).2 (Or.inl x.2)
    have h1 := vn_Psi_lt hδ0.le hDom hxd
    have h2 := vn_le_sub_add (fun i => φ (x, i)) (D.Ψ x)
    have h3 := hbb.val x
    have h4 := hF.num.phi_lt
    nlinarith
  set e := flEdat Gp Hm (φ, α) D.Ψ ψ' with he
  have hstrict : StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ e :=
    flEdat_strict hF.hPmp hbb hB4 hphi hF.num.δ₁_pos hψ
  obtain ⟨hfld, hfix, hs6, hsK, hdp, huniq⟩ := hSol (s, e) hs hstrict
  set δφ := (Sol (s, e)).1 with hδφ
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hF.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hF.num.δ₁_pos.le
  have hδΨ : ∀ x ∈ dataSites Gk,
      vn (fun i => composeField Gk Hm (compWeight L a₁) δφ ψ' x i) ≤ δfl := fun x _ =>
    (flPsi_bound hF.hPm (by have := hB.HBp.hL; omega) hB.ha₁ hV hF.num.δ₁_pos.le hdp.val
      (fun y hy => (hψ y hy).le) x).trans hF.num.flb
  -- the numerical conditions at `b² ε' + K₂' δ₃ (+ K₂' δfl)`, from those at `C₀² ε'`
  have hb2 : b ^ 2 * eps ≤ scaledC0 d ^ 2 * eps :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hbC 2) hε.le
  have hbb : b ^ 2 * eps + xiK2 d L N * δ₃ ≤ scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ := by
    linarith
  have hbb' : xiC1 d * (b ^ 2 * eps + xiK2 d L N * δ₃) ≤
      xiC1 d * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃) :=
    mul_le_mul_of_nonneg_left hbb (by linarith)
  have hK1 := (bgK1_pos (d := d) (L := L) (N := N)).le
  have hsmall₂ : (4 * d + 6) * ((2 * d + 1) * (b ^ 2 * eps + xiK2 d L N * δ₃)) ≤ 1 :=
    le_trans (by gcongr) hB.num.small₂
  have hc1f : xiC1 d * (b ^ 2 * eps + xiK2 d L N * δ₃) + 5 * δfl ≤ bgC1 d L N := by
    linarith [hF.num.c1_f]
  have hK1sf : bgK1 d L N * (xiC1 d * (b ^ 2 * eps + xiK2 d L N * δ₃)) ≤ deltaStar d L N :=
    le_trans (mul_le_mul_of_nonneg_left hbb' hK1) hF.num.K1s_f
  have hsmf : bgK1 d L N * (xiC1 d * (b ^ 2 * eps + xiK2 d L N * δ₃)) + cK2 d L N * δfl <
      bgC0 d L N := by
    have := mul_le_mul_of_nonneg_left hbb' hK1
    linarith [hF.num.sm_f]
  have hX3 : XiCData Gk (compWeight L a₁) ν K 1
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
      (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc) :=
    xiCData_perturb hB.HBk hF.num.δfl_nn hF.num.δfl_le_one hsmall₂ hc1f
      hF.num.star_f hK1sf hsmf (flPsi_layerConst hF.hPm _ δφ hψc) hδΨ hst
  have hrawD : D1rawFl Gp Gk Hm (compWeight L a₁) F₁ Sol s (rawOf D, ψ') =
      rawOf (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc) := by
    refine Prod.ext (funext fun x => funext fun i => ?_) rfl
    show composeField Gk Gp (compWeight L a₁) (F₁ (s, rawOf D)).1 D.Ψ x i +
      composeField Gk Hm (compWeight L a₁) (Sol (s, flEdat Gp Hm (F₁ (s, rawOf D)) D.Ψ ψ')).1
        ψ' x i = _
    rw [hFeq]
    exact (flDatum_Ψ hB.hP hF.hPm _ φ δφ D ψ' hψc x i).symm
  have hUk := xiCData_unionC hX3
  have hFk' := hFk _ hUk
  refine ⟨φ, α, δφ, hI, hFeq, hstrict, rfl, hX3, hrawD, ?_, ?_⟩
  · rw [D2raw_rawOf, hFk']
  · have hbbb : b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl ≤
        scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl := by linarith
    have hsmall₃ : (4 * d + 6) * ((2 * d + 1) *
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)) ≤ 1 :=
      le_trans (by gcongr) hF.num.small₃
    have hth₃ : xiC1 d * (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) ≤ thm73C1 d L N :=
      le_trans (mul_le_mul_of_nonneg_left hbbb (by linarith)) hF.num.th₃
    exact i5_stage2_of_one_le hb₁ hB.ha₁ hB.HBk hB.HBj hB.hq hB.colj hsmall₃ hth₃ hB.hj hX3

/-- **The point facts of Lemma DL with the fluctuation.** -/
theorem point_facts_fl (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Fk : RawData d L (N₁ * L ^ m₁) K N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
      s ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D)
    {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ} (hψ : ∀ x ∈ dataSites Hm, vn (ψ' x) < δ₁)
    (hψc : IsLayerConstant Hm ψ') :
    ∃ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ),
      IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α ∧ F₁ (s, rawOf D) = (φ, α) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁
        (flEdat Gp Hm (φ, α) D.Ψ ψ') ∧
      (Sol (s, flEdat Gp Hm (φ, α) D.Ψ ψ')).1 = δφ ∧
      XiCData Gk (compWeight L a₁) ν K 1
        (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
        (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc) ∧
      D1rawFl Gp Gk Hm (compWeight L a₁) F₁ Sol s (rawOf D, ψ') =
        rawOf (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc) ∧
      D2raw Gk Gj (compWeight L a₁) Fk (rawOf (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)) =
        rawOf (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc))
          (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)) ∧
      XiCData Gj (compWeight L a₁) ν j (scaledC0 d)
        (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
        (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc))
          (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)) :=
  point_facts_fl_of_one_le (one_le_scaledC0 d) le_rfl hB hF hF₁ hFk hSol hs hs1 hD hψ hψc

end Facts

end Balaban.Localization
