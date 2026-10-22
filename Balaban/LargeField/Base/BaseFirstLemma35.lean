module

public import Balaban.LargeField.Base.BaseFirstActionClass
public import Balaban.Fluctuation.RenormIdentity
public import Balaban.Fluctuation.RenormExpLemma35

/-!
# Lemma 3.5 (i) at the first step

The renormalization identity of the first step.  With the data `D = D(ψ)` at the renormalized mass `ν`
and `Du = D((1+ζ)ψ)` at the unrenormalized mass `νu`, `ν(1+ξ₂) = νu(1+ξ₃)`, the backgrounds `bgField` of
the two data satisfy, on the real data domain of the single-scale generating set,
`β(1+ξ₃) · action(Du, φu) = β · action(D, φ) + β (C₁ - C₂)` (`baseFirst_lemma35`).  Combined with
`baseFirst_action_eq_class`, the physical first-step action `A₁(e_{θ_u}; θ_u)` at the renormalized field
`θ_u = (1+ζ)θ` equals the class's action at `D(θ)` plus the explicit terms `C₁, C₂`
(`baseFirst_physical_eq_class_add`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Fluctuation Matrix

variable {d N L n : ℕ} [NeZero L] [NeZero n]

omit [NeZero n] in
/-- The datum of the renormalized field: scaling the coarse field scales the lifted field. -/
theorem firstDatum_scale {N₀ : ℕ} [NeZero N₀] (ϱ : ℝ) (hc : N₀ * L ^ (1 - 1) = n) (ζ : ℝ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (h : EuclideanSpace ℝ (Fin N)) :
    (∀ x i, (firstDatum ϱ hc ((1 + ζ) • θ) h).Ψ x i = (1 + (ζ : ℂ)) * (firstDatum ϱ hc θ h).Ψ x i) ∧
      ∀ x i, (firstDatum ϱ hc ((1 + ζ) • θ) h).h x i = (firstDatum ϱ hc θ h).h x i := by
  classical
  have hG : ∀ x : Torus d (N₀ * L ^ 1), x ∈ (GeneratingSet.single (d := d) (L := L) (N₀ := N₀)
      (k := 1) ϱ).Ω 1 := fun x => by simp [GeneratingSet.single, singleΩ]
  refine ⟨fun x i => ?_, fun x i => ?_⟩
  · have hx : x ∈ dataSites (GeneratingSet.single (d := d) (L := L) (N₀ := N₀) (k := 1) ϱ) :=
      (mem_dataSites _).2 (Or.inl (hG x))
    unfold firstDatum
    rw [liftSingle_Ψ _ _ _ hx, liftSingle_Ψ _ _ _ hx]
    simp
  · unfold firstDatum
    rw [liftSingle_h _ _ _ (hG x), liftSingle_h _ _ _ (hG x)]

section Class

variable {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}

omit [NeZero n] in
/-- **Lemma 3.5 (i) at the first step, class form.**  For the data `D = D(θ)` and
`Du = D((1+ζ)θ)` of the top generating set at scale `1`, both in the real data domain, at the masses
`ν`, `νu` with `ν(1+ξ₂) = νu(1+ξ₃)`:
`β(1+ξ₃) · action(Du, bgField Du) = β · action(D, bgField D) + β Re(C₁ - C₂)`, in `ℂ`, with
`C₁ = renormC1` at the old background and `C₂ = renormC2` at the perturbation `bgField Du - bgField D`. -/
theorem baseFirst_lemma35 (aw : ℕ → ℝ) {ν νu β ξ₂ ξ₃ ζ : ℝ}
    (hν : ν * (1 + ξ₂) = νu * (1 + ξ₃)) (hc : N₁ * L ^ m₁ * L ^ (1 - 1) = n)
    (H : BgHyp d L 1 ϱ aw ν) (Hu : BgHyp d L 1 ϱ aw νu)
    (h : EuclideanSpace ℝ (Fin N)) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (hD : InUnionDomainR (topGS d L N₁ m₁ 1 ϱ) (bgC1 d L N) ν (firstDatum ϱ hc θ h))
    (hDu : InUnionDomainR (topGS d L N₁ m₁ 1 ϱ) (bgC1 d L N) νu
      (firstDatum ϱ hc ((1 + ζ) • θ) h)) :
    let G := topGS d L N₁ m₁ 1 ϱ
    let D : BgData G N := firstDatum ϱ hc θ h
    let Du : BgData G N := firstDatum ϱ hc ((1 + ζ) • θ) h
    ((β * (1 + ξ₃) * action G aw νu Du (bgField G aw νu Du) : ℝ) : ℂ) =
      ((β * action G aw ν D (bgField G aw ν D) : ℝ) : ℂ) +
        (β : ℂ) * (renormC1 G aw ν ξ₂ ξ₃ ζ D (bgField G aw ν D) -
          renormC2 G aw νu ξ₃ (bgMult G aw νu Du) (bgField G aw ν D) (bgField G aw νu Du)) := by
  intro G D Du
  have hG : IsLevel G 1 := isLevel_levelGS le_rfl le_rfl
  obtain ⟨hΨ, hh⟩ := firstDatum_scale ϱ hc ζ θ h
  have h71 := theorem71 (G := G) H hD
  have h71u := theorem71 (G := G) Hu hDu
  have hreal : D.IsReal := by
    obtain ⟨δ, _, _, hDδ⟩ := hD
    exact isReal_of_inDomainR hDδ
  have hrealu : Du.IsReal := by
    obtain ⟨δ, _, _, hDδ⟩ := hDu
    exact isReal_of_inDomainR hDδ
  have key := lemma35_i_complete hG aw (β := β) hν hΨ hh h71.2.2.1.1 h71u.2.2.1.1
  have e1 := action_cast Du hrealu (fun x i => (h71u.2.1 x).1 i) (a := aw) (ν := νu)
  have e2 := action_cast D hreal (fun x i => (h71.2.1 x).1 i) (a := aw) (ν := ν)
  rw [← e1, ← e2] at key
  push_cast at key ⊢
  exact key

/-- **The physical first-step action at the renormalized field, in terms of the class.**  With
`θ_u = (1+ζ)θ`, `e_u = baseSectorCenter` at the unrenormalized mass `νu` and `a₀ = aw 1`:
`β(1+ξ₃) · A₁(e_u; θ_u) = β · action(D(θ), bgField) + β (C₁ - C₂)`, where `A₁` is the physical action
`energy νu h e_u + (a₀ L^d/(2L²)) Σ_y |θ_u(y) - (Q e_u)(y)|²` (`baseFirst_action_bgField_of_eq`) and the
right side is the class's action at the renormalized mass `ν` plus the explicit counterterms. -/
theorem baseFirst_physical_eq_class_add (aw : ℕ → ℝ) (a₀ : ℝ) (ha : aw 1 = a₀) {ν νu β ξ₂ ξ₃ ζ : ℝ}
    (hν : ν * (1 + ξ₂) = νu * (1 + ξ₃)) (hN : N₁ * L ^ m₁ = 1 * n)
    (hc : N₁ * L ^ m₁ * L ^ (1 - 1) = n)
    (H : BgHyp d L 1 ϱ aw ν) (Hu : BgHyp d L 1 ϱ aw νu)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (hD : InUnionDomainR (topGS d L N₁ m₁ 1 ϱ) (bgC1 d L N) ν (firstDatum ϱ hc θ h))
    (hDu : InUnionDomainR (topGS d L N₁ m₁ 1 ϱ) (bgC1 d L N) νu
      (firstDatum ϱ hc ((1 + ζ) • θ) h)) :
    let G := topGS d L N₁ m₁ 1 ϱ
    let D : BgData G N := firstDatum ϱ hc θ h
    let Du : BgData G N := firstDatum ϱ hc ((1 + ζ) • θ) h
    let eu : Torus d (L * n) → EuclideanSpace ℝ (Fin N) :=
      baseSectorCenter ϱ aw True νu h ((1 + ζ) • θ)
    let ecu : CfgT d N L n := fun x => ⟨eu x,
      mem_sphere_zero_iff_norm.mpr
        (baseSectorCenter_unit ϱ aw True νu h hh (bgHyp_ite_of trivial Hu) ((1 + ζ) • θ) x)⟩
    ((β * (1 + ξ₃) * (energy d N (L * n) νu h ecu +
        (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
          ∑ y : Torus d n, ‖((1 + ζ) • θ) y - baseQ d N L n ecu y‖ ^ 2) : ℝ) : ℂ) =
      ((β * action G aw ν D (bgField G aw ν D) : ℝ) : ℂ) +
        (β : ℂ) * (renormC1 G aw ν ξ₂ ξ₃ ζ D (bgField G aw ν D) -
          renormC2 G aw νu ξ₃ (bgMult G aw νu Du) (bgField G aw ν D) (bgField G aw νu Du)) := by
  intro G D Du eu ecu
  have hA := baseFirst_action_bgField_of_eq (N₀ := N₁ * L ^ m₁) hN hc ϱ aw a₀ ha True trivial νu h hh
    Hu ((1 + ζ) • θ) hDu
  have hA' : action G aw νu Du (bgField G aw νu Du) =
      energy d N (L * n) νu h ecu +
        (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
          ∑ y : Torus d n, ‖((1 + ζ) • θ) y - baseQ d N L n ecu y‖ ^ 2 := hA
  rw [← hA']
  exact baseFirst_lemma35 (β := β) (ξ₂ := ξ₂) (ξ₃ := ξ₃) aw hν hc H Hu h θ hD hDu

omit [NeZero n] in
/-- **Lemma 3.5 (ii) at the first step: the bound for `δφ = φu - φ`.**  On the top generating set at
scale `1`, for the solution map `F` of the perturbed system (`exists_isRenSol`, parameters of
Proposition 5.1 for the class radius `ε` and polydisc radius `r`), the datum `D(θ)` of the class domain
`Ξ^c_1(𝔹; 1, ε)` and the real parameter `t = (t₁, t₂, t₃)`, `‖t‖ < r`: if `(φu, αu)` is the small
solution of the renormalized datum `D((1 + ε t₁) θ)` at the mass `ν(1+t₂)/(1+t₃)`, then
`F(D, t) = (φu − φ, αu − α)` with `(φ, α) = (bgFieldC, bgMultC)` of `D(θ)`, and
`‖φu − φ‖_*, |αu − α|₂ ≤ 8 K₂ ε ‖t‖`. -/
theorem baseFirst_deltaPhi (aw : ℕ → ℝ) {ν ε r : ℝ} (H : BgHyp d L 1 ϱ aw ν) (hε : 0 < ε)
    (hr : r ≤ 1 / 16) (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1)
    (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    (hK : bgK1 d L N * (xiC1 d * ε) + 3 * r ≤ deltaStar d L N)
    (hζ : 8 * ε * r ≤ deltaStar d L N) :
    ∃ F, IsRenSol (N := N) (topGS d L N₁ m₁ 1 ϱ) aw ν ε ε r (8 * ε) F ∧
      ∀ (hc : N₁ * L ^ m₁ * L ^ (1 - 1) = n) (h : EuclideanSpace ℝ (Fin N))
        (θ : Torus d n → EuclideanSpace ℝ (Fin N)),
        XiCOne (topGS d L N₁ m₁ 1 ϱ) aw ν ε (firstDatum ϱ hc θ h) →
        ∀ (t : Fin 3 → ℝ), ‖(fun i => ((t i : ℝ) : ℂ))‖ < r →
        ∀ {φu : (topGS d L N₁ m₁ 1 ϱ).Ω 1 × Fin N → ℂ} {αu : (topGS d L N₁ m₁ 1 ϱ).Ω 1 → ℂ},
        IsSmallSolution (topGS d L N₁ m₁ 1 ϱ) aw (ν * (1 + t 1) / (1 + t 2)) (c6 d L N / 2)
          (firstDatum ϱ hc ((1 + ε * t 0) • θ) h) φu αu →
        SupBounds (topGS d L N₁ m₁ 1 ϱ)
            (φu - bgFieldC (topGS d L N₁ m₁ 1 ϱ) aw ν (bgC0 d L N) (firstDatum ϱ hc θ h))
            (cK2 d L N * (8 * ε * ‖(fun i => ((t i : ℝ) : ℂ))‖)) ∧
          Small (topGS d L N₁ m₁ 1 ϱ)
            (αu - bgMultC (topGS d L N₁ m₁ 1 ϱ) aw ν (bgC0 d L N) (firstDatum ϱ hc θ h))
            (cK2 d L N * (8 * ε * ‖(fun i => ((t i : ℝ) : ℂ))‖)) := by
  obtain ⟨F, hF⟩ := exists_isRenSol (G := topGS d L N₁ m₁ 1 ϱ) (N := N) H hε hr hsm hc1 hK hζ
  refine ⟨F, hF, fun hc h θ hD t ht φu αu hs => ?_⟩
  obtain ⟨hΨ, hh⟩ := firstDatum_scale ϱ hc (ε * t 0) θ h
  have heq := hF.eq_bg H hε hsm hc1 hD (t := t) ht hΨ hh (c₀ := c6 d L N / 2) (by linarith) hs
  have hsup := hF.sup _ hD _ ht
  have hsmall := hF.small _ hD _ ht
  rw [heq] at hsup hsmall
  exact ⟨hsup, hsmall⟩

end Class

end Balaban.LargeField
