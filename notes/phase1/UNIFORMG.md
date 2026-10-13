# UNIFORMG — one physical solution map for all admissible sources

**PROVED (source fact).** Audited main commit: `bd66854fe1529855055d7efbfceaa9840877456c`. The landed `renormPhysicalZero_onFibre_half_of_families` binds `g` and `hg` before `∃ F Fcut` (`Balaban/Inhabited/RenormPhysicalRecord.lean:50-55,95-113`), so its logical statement permits different `F` for different sources. The actual producer `renLoc_fields_union_scale_of_tower_at` has no source parameter (`Balaban/Inhabited/RenJoinClassWitness.lean:101-110`); its call and the cut-map choice use only scale data (`RenormPhysicalRecord.lean:143-155`).

## T1. Candidate exact Lean statements

**OPEN (unelaborated declaration).** The following copies the landed binder/record surface and changes only the quantifier order needed for uniformity. `q` stays before the coefficient families; `cE` and `cM` are single families for all `g`. The landed `hanM`, `hlocM`, `hbdM`, `hsuppM` are already source-uniform because `cM` is a function of the physical parameter; **`hvalM` is not**: in main it mentions one fixed `g` at `RenormPhysicalRecord.lean:87-94`. Here `hvalM` explicitly covers every admissible `g`. The final `∀g` is inside `∃F Fcut`, after all source-independent fields.

```lean
open Classical in
theorem renormPhysicalZero_onFibre_half_uniform {κmin : ℝ} (R : StepTowerTheta κmin)
    (hR : renDetFibreMin ≤ κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (hβ : 0 < β) (Xcut : Set (CTorus 3 3 N₁ R.m₁ (k + 1)))
    (q : ℝ) (hq : q ≤ 1)
    {κ B κM BM : ℝ} (hB : 0 ≤ B) (hBM : 0 ≤ BM)
    (cE : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))) →
      physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ)
    (cM : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 →
      physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ)
    (hanE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ T, AnalyticOnNhd ℂ (fun θ => cE z θ T) (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t))
    (hlocE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ T, ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ θ' ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        cE z θ T = cE z θ' T)
    (hbdE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖cE z θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsuppE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, cE z θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hvalE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).E1locC
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z =
        ∑ C, cE z (⟨rawOf D', rawOf_mem_rawSub _⟩, (0 : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 → ℂ)) C)
    (hanM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ T, AnalyticOnNhd ℂ (fun θ => cM y i θ T) (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t))
    (hlocM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ T, ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ θ' ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        cM y i θ T = cM y i θ' T)
    (hbdM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖cM y i θ T‖ ≤ BM * Real.exp (-κM * dExt T))
    (hsuppM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, cM y i θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hvalM : ∀ (g : Fld 3 3 N₁ R.m₁ (k + 1) 2),
      (∑ x, ∑ j, ‖g x j‖) < q →
      ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g y i =
        ((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
          ∑ C, cM y i (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2 → ℂ) ×
          (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 → ℂ),
    ∃ Fcut : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) Xcut → ℂ) →
        (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2 → ℂ) ×
          (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 → ℂ),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2) (R.t / 2)
        R.r₀ (8 * (R.t / 2)) F ∧
      AnalyticOnNhd ℂ (fun p : (RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ)) ×
          (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) Xcut → ℂ) => Fcut p.1 p.2)
        (expDom (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2)) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) Xcut → ℂ)
            (fun _ => Real.exp R.κ)) ∧
      (∀ D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2,
        XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2) D →
        ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ)) ∧
      ∀ (g : Fld 3 3 N₁ R.m₁ (k + 1) 2),
        (∑ x, ∑ j, ‖g x j‖) < q →
      RenormExpInputOn (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2)
        R.r₀ (renCK 3 3 2 R.BG R.κ) (8 * (R.t / 2)) F
        (fun z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))) =>
          blockSites 3 3 N₁ R.m₁ (k + 1) k z)
        (fun z => renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
        (fun p => renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1))))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
        (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min κ κM)) (min (3 / 2 * R.κdec) (min κ κM)) 1
        (hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
            Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)) + B)
        0 BM 0 (fun (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))) (D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2) (ξ : Fin 3 → ℂ) =>
          if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
          then ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
            (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).E0locC
              (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z else 0) (fun _ _ _ => 0) (fun (p : ((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2) (D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2) (ξ : Fin 3 → ℂ) =>
          if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
          then (((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ)))⁻¹ *
            ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
              (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).M0C
                (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)) p.2
          else 0) (fun _ _ _ => 0)
        (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ))
```

**OPEN (unelaborated declaration).** The four-consequence version keeps the landed budgets and value functions verbatim; its one `F` precedes `∀g`. The three energy conclusions and the observable conclusion are all within that quantifier.

```lean
open Classical in
theorem renormPhysicalZero_onFibre_half_consequences_uniform {κmin : ℝ} (R : StepTowerTheta κmin)
    (hR : renDetFibreMin ≤ κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (hβ : 0 < β) (Xcut : Set (CTorus 3 3 N₁ R.m₁ (k + 1)))
    (q : ℝ) (hq : q ≤ 1)
    {κ B κM BM : ℝ} (hB : 0 ≤ B) (hBM : 0 ≤ BM)
    (cE : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))) →
      physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ)
    (cM : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 →
      physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ)
    (hanE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ T, AnalyticOnNhd ℂ (fun θ => cE z θ T) (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t))
    (hlocE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ T, ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ θ' ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        cE z θ T = cE z θ' T)
    (hbdE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖cE z θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsuppE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, cE z θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hvalE : ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))), ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).E1locC
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z =
        ∑ C, cE z (⟨rawOf D', rawOf_mem_rawSub _⟩, (0 : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 → ℂ)) C)
    (hanM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ T, AnalyticOnNhd ℂ (fun θ => cM y i θ T) (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t))
    (hlocM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ T, ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ θ' ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        cM y i θ T = cM y i θ' T)
    (hbdM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖cM y i θ T‖ ≤ BM * Real.exp (-κM * dExt T))
    (hsuppM : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ θ ∈ (physV (R.toStepTower.step k hk N₁ ν β p₁) (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t),
      ∀ T, cM y i θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hvalM : ∀ (g : Fld 3 3 N₁ R.m₁ (k + 1) 2),
      (∑ x, ∑ j, ‖g x j‖) < q →
      ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2), ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g y i =
        ((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
          ∑ C, cM y i (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2 → ℂ) ×
          (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 → ℂ),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2) (R.t / 2)
        R.r₀ (8 * (R.t / 2)) F ∧
      ∀ (g : Fld 3 3 N₁ R.m₁ (k + 1) 2),
        (∑ x, ∑ j, ‖g x j‖) < q →
      (∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))) (εR : ℝ), 0 ≤ εR → εR ≤ R.r₀ →
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min κ κM))
          (1 * ((3 + 6) * (renCK 3 3 2 R.BG R.κ * (R.t / 2)) ^ 2 *
            blockWeight (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (blockSites 3 3 N₁ R.m₁ (k + 1) k z)) * εR ^ 1)
          (fun D ξ => renC1On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2)
            (blockSites 3 3 N₁ R.m₁ (k + 1) k z) D.Ψ D.h
            (bgFieldC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D) ξ) term) ∧
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min κ κM))
          (1 * (17 / 32 * ((2 : ℕ) * ((3 + (bgK1 3 3 2 * (xiC1 3 * (R.t / 2)) +
            renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * (R.t / 2)) * R.r₀ + 2)) *
            (renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * (R.t / 2))) ^ 2)) *
            blockWeight (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (blockSites 3 3 N₁ R.m₁ (k + 1) k z)) * εR ^ 2)
          (fun D ξ => renC2On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1)
            (blockSites 3 3 N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ)
            (bgMultC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D +
              (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term) ∧
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min κ κM))
          ((hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
            Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)) + B))
          (fun D ξ => if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
          then ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
            (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).E0locC
              (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z else 0) term)) ∧
      ∀ (p : ((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2) (εR : ℝ), εR ≤ R.r₀ →
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1))))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min κ κM))
          (BM + 1 * (renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * (R.t / 2))) * εR ^ 1)
          (fun D ξ => (if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
          then (((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ)))⁻¹ *
            ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
              (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).M0C
                (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)) p.2
          else 0) + (F ((D.Ψ, D.h), ξ)).1 p) term)
```

## T2. Proof layout and corollaries

- **PROVED (source fact).** `RenormPhysicalRecord.lean:143-168` computes `e=t/2`, the common rate bound, `F,hF,h1,h2,h3`, `Fcut,hFa,hFe`, the fibre inclusion, and determinant nonnegativity without inspecting `g` or `hg`. Move that block before `intro g hg`; retain the chosen witnesses in the outer existential.
- **OPEN (routine refactor).** After `refine ⟨F,Fcut,hF,hFa,hFe,?_⟩`, use `intro g hg`. Reuse `renormExpInputOn_zero_of_fields hsub h1 h2 ... h3 ...` (`RenormPhysicalRecord.lean:169-170`); the energy leaf at `:171-174` is unchanged, and the observable leaf at `:175-179` uses `renM0_siteRecord_union_of_family ... g q hq hg ... (hvalM g hg _ _)`. The record term for `expM0` may be selected separately for each `g`.
- **OPEN (routine refactor).** For consequences, choose `F,Fcut` once from the new uniform record; then `intro g hg`, let `I := hI g hg`, and apply the same four consumers `thm31g_C1_on`, `thm31g_C2_on`, `thm31g_Eu_zero_of_fields_on`, `thm31h_zero_of_fields_on` (`RenormPhysicalRecord.lean:310-325`). This adds approximately two binder/projection lines to the existing 16-line proof, after the record proof's approximately 37 existing lines are rearranged.
- **REFUTED (direct move-and-corollary).** The landed theorem cannot become a corollary of the stated uniform theorem while keeping its text unchanged: its fixed-source `hvalM` supplies only the identity at its input `g`, whereas the uniform theorem requires that identity for every admissible source. There is no implication from the former to the latter (`RenormPhysicalRecord.lean:87-94`).
- **OPEN (shared-core repair).** Put the moved 37-line construction in a private helper with `∃F Fcut, source-independent fields ∧ ∀g, hg → hvalM_g → RenormExpInputOn … (M0θ g) …`, where `hvalM_g` is the landed fixed-source value clause. The uniform theorem follows by `hvalM g hg`; the existing theorem follows by supplying its one `hvalM` at its fixed `g`, with no statement change. Expect roughly 40-50 helper proof lines and 5-10 lines per wrapper, excluding long declarations. The helper is an implementation proposition, not a replacement mathematical root.

## T3. Record-field obstruction check

**PROVED (definition inspection).** `RenormExpInputOn` takes `F` before `E0θ` and `M0θ` (`Balaban/Fluctuation/RenormExpInputOn.lean:69-77`). Its `sub`, `locC1`, `locC2`, and `locDφ` fields are independent of `g` (`:78-89,95-98`); `expE0` is independent of `g` (`:90-91`); only `expM0` mentions the source-indexed `M0θ` (`:99-100`). Both old fields have the zero functions and zero budgets (`RenormPhysicalRecord.lean:125-142`; `RenormExpInputOn.lean:249-267`). Thus no field type forces a new `F` per source. `Fcut` and its endpoint are also source-independent (`RenormPhysicalRecord.lean:98-112,154-155`).

**OPEN (verification limit).** The candidate declarations and refactor are statement/proof plans only. No Lean build or elaboration was run, as requested.
