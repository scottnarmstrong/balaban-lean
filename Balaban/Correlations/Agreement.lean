/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.Box

/-!
# Torus independence of the terms of Root-F

Conditional on the clauses of Root-F; consumed by the Root-C provider.  From the agreement clause
of Root-F: on the images of the finite subsets `A` of the box `boxZ d R`, `4 R ≤ ℓ, ℓ'`, the
values `T_j(a, A; 0)_i` (`value_agree`) and the derivatives `D_{w,k} T_j(a, A; 0)_i`
(`fderiv_agree`) of two admissible tori coincide.
-/

@[expose] public section

open scoped Classical

namespace Balaban.Correlations

open Balaban Finset

section Line

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem fderiv_eq_deriv_line {f : E → ℂ} (hf : DifferentiableAt ℂ f 0) (v : E) :
    fderiv ℂ f 0 v = deriv (fun ζ : ℂ => f (ζ • v)) 0 := by
  have h1 : HasDerivAt (fun t : ℂ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const v
  have h2 : HasFDerivAt f (fderiv ℂ f 0) ((fun t : ℂ => t • v) 0) := by
    simpa using hf.hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv.symm

end Line

variable {d N L M kf : ℕ} {β ν : ℝ} {h : EuclideanSpace ℝ (Fin N)} {κ c₉ δ : ℝ}
  {T : RootFFamily d N}

section

variable {ℓ ℓ' R : ℕ} [NeZero ℓ] [NeZero ℓ']

theorem term_eq_zero_of_not_mem_image (hcl : RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ)
    (hR : 4 * R ≤ ℓ) (j : ℕ) {a : Fin d → ℤ} (ha : a ∈ boxZ d R) {A : Finset (Fin d → ℤ)}
    (hA : A ⊆ boxZ d R) (haA : a ∉ A) :
    T ℓ j (embedZ ℓ a) (A.image (embedZ ℓ)) = 0 := by
  refine hcl.1 j _ _ fun h' => ?_
  obtain ⟨a', ha', hh⟩ := mem_image.1 h'.2.1
  exact haA (embedZ_injOn hR (Finset.mem_coe.2 (hA ha')) (Finset.mem_coe.2 ha) hh ▸ ha')

omit [NeZero ℓ] [NeZero ℓ'] in
theorem box_cond (hR : 4 * R ≤ ℓ) (hR' : 4 * R ≤ ℓ') {A : Finset (Fin d → ℤ)}
    (hA : A ⊆ boxZ d R) : ∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ) ∧ 4 * |y μ| < (ℓ' : ℤ) := by
  intro y hy μ
  have h1 := mem_boxZ.1 (hA hy) μ
  have h2 : (4 * R : ℤ) ≤ ℓ := by exact_mod_cast hR
  have h3 : (4 * R : ℤ) ≤ ℓ' := by exact_mod_cast hR'
  constructor <;> linarith

theorem value_agree (hcl : RootFClauses d N L M β ν h kf κ c₉ δ T)
    (hℓ : M * L ^ (kf + 1) ∣ ℓ) (hℓ' : M * L ^ (kf + 1) ∣ ℓ') (hR : 4 * R ≤ ℓ)
    (hR' : 4 * R ≤ ℓ') (j : ℕ) {a : Fin d → ℤ} (ha : a ∈ boxZ d R) {A : Finset (Fin d → ℤ)}
    (hA : A ⊆ boxZ d R) (i : Fin N) :
    T ℓ j (embedZ ℓ a) (A.image (embedZ ℓ)) 0 i =
      T ℓ' j (embedZ ℓ' a) (A.image (embedZ ℓ')) 0 i := by
  by_cases haA : a ∈ A
  · have hag := hcl.2 ℓ ℓ' hℓ hℓ' j a A 0 haA (box_cond hR hR' hA)
    exact congrFun hag i
  · rw [term_eq_zero_of_not_mem_image (hcl.1 ℓ hℓ) hR j ha hA haA,
      term_eq_zero_of_not_mem_image (hcl.1 ℓ' hℓ') hR' j ha hA haA]
    simp

theorem fderiv_agree (hcl : RootFClauses d N L M β ν h kf κ c₉ δ T)
    (hℓ : M * L ^ (kf + 1) ∣ ℓ) (hℓ' : M * L ^ (kf + 1) ∣ ℓ') (hR : 4 * R ≤ ℓ)
    (hR' : 4 * R ≤ ℓ') (j : ℕ) {a w : Fin d → ℤ} (ha : a ∈ boxZ d R) (hw : w ∈ boxZ d R)
    {A : Finset (Fin d → ℤ)} (hA : A ⊆ boxZ d R) (i k : Fin N) :
    fderiv ℂ (termComp T ℓ j (embedZ ℓ a) (A.image (embedZ ℓ)) i) 0
        (sourceDelta (embedZ ℓ w) k) =
      fderiv ℂ (termComp T ℓ' j (embedZ ℓ' a) (A.image (embedZ ℓ')) i) 0
        (sourceDelta (embedZ ℓ' w) k) := by
  by_cases haA : a ∈ A
  · rw [fderiv_eq_deriv_line (termComp_analytic (hcl.1 ℓ hℓ) j _ _ i 0
      zero_mem_sourceBall).differentiableAt,
      fderiv_eq_deriv_line (termComp_analytic (hcl.1 ℓ' hℓ') j _ _ i 0
      zero_mem_sourceBall).differentiableAt]
    congr 1
    funext ζ
    have hg : ∀ (m : ℕ) [NeZero m], 4 * R ≤ m →
        (fun z : Torus d m => (fun u : Fin d → ℤ => if u = w then ζ • (Pi.single k (1 : ℂ) : Fin N → ℂ)
            else 0) fun μ => ZMod.valMinAbs (z μ)) = ζ • sourceDelta (embedZ m w) k := by
      intro m _ hm
      funext z
      by_cases hz : z = embedZ m w
      · subst hz
        have : (fun μ => ZMod.valMinAbs (embedZ m w μ)) = w := funext (valMinAbs_embedZ hm hw)
        simp [this, sourceDelta]
      · have hne : (fun μ => ZMod.valMinAbs (z μ)) ≠ w := by
          intro heq
          apply hz
          rw [← embedZ_valMinAbs z, heq]
        simp [hne, sourceDelta, Pi.single_eq_of_ne hz]
    have hag := hcl.2 ℓ ℓ' hℓ hℓ' j a A
      (fun u => if u = w then ζ • (Pi.single k (1 : ℂ) : Fin N → ℂ) else 0) haA
      (box_cond hR hR' hA)
    simp only [hg ℓ hR, hg ℓ' hR'] at hag
    simp only [termComp]
    exact congrFun hag i
  · have h1 := term_eq_zero_of_not_mem_image (hcl.1 ℓ hℓ) hR j ha hA haA
    have h2 := term_eq_zero_of_not_mem_image (hcl.1 ℓ' hℓ') hR' j ha hA haA
    have e1 : termComp T ℓ j (embedZ ℓ a) (A.image (embedZ ℓ)) i = fun _ => 0 := by
      funext g; simp [termComp, h1]
    have e2 : termComp T ℓ' j (embedZ ℓ' a) (A.image (embedZ ℓ')) i = fun _ => 0 := by
      funext g; simp [termComp, h2]
    rw [e1, e2]
    simp

end

end Balaban.Correlations
