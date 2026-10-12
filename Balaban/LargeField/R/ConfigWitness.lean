module

public import Balaban.LargeField.R.ConfigAdm
public import Balaban.LargeField.History.InhabitedJoint

/-!
# The configuration structures are inhabited (hard rule 10)

For the joint witness of the large-field counter (`JointWitness.jointWitness`) the empty configuration is a
configuration at every scale, and it is admissible (the region history of the witness has no
components).  `HistConfig.empty` is a configuration for every choice of parameters.
-/

@[expose] public section

namespace Balaban.LargeField

/-- `HistConfig` is inhabited for every choice of parameters (the empty family). -/
theorem nonempty_config {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M k : ℕ}
    [NeZero M] : Nonempty (HistConfig S n R k0 K M k) :=
  ⟨HistConfig.empty⟩

/-- Non-vacuity of `IsAdmConfig`: for the joint witness of the counter, the empty configuration is
an admissible configuration at every scale. -/
theorem isAdmConfig_empty_joint (M k : ℕ) [NeZero M] :
    letI := JointWitness.jointWitness.nz
    ∃ F : HistConfig JointWitness.jointWitness.S JointWitness.jointWitness.n JointWitness.jointWitness.R JointWitness.jointWitness.F.k0
        JointWitness.jointWitness.F.kf M k, IsAdmConfig F := by
  let _ := JointWitness.jointWitness.nz
  refine ⟨HistConfig.empty, JointWitness.jointWitness.H, JointWitness.jointWitness.hadm, ?_, ?_⟩
  · intro c
    exact (JointWitness.jointWitness_isEmpty_comp k).elim c
  · simp [HistConfig.empty]

end Balaban.LargeField
