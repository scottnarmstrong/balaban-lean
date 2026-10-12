module

public import Balaban.LargeField.R.ConfigAdm
public import Balaban.LargeField.History.InhabitedJoint

/-!
# The configuration structures are inhabited (hard rule 10)

For the joint witness of the large-field counter (`JointWitness.jointWitness`) the empty configuration is a
configuration at every scale, and it is admissible (the region history of the witness has no
components).  `Config.empty` is a configuration for every choice of parameters.
-/

@[expose] public section

namespace Balaban.LargeField

/-- `Config` is inhabited for every choice of parameters (the empty family). -/
theorem nonempty_config {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M k : ℕ}
    [NeZero M] : Nonempty (Config S n R k0 K M k) :=
  ⟨Config.empty⟩

/-- Non-vacuity of `IsAdmConfig`: for the joint witness of the counter, the empty configuration is
an admissible configuration at every scale. -/
theorem isAdmConfig_empty_joint (M k : ℕ) [NeZero M] :
    letI := JointWitness.jointWitness.nz
    ∃ F : Config JointWitness.jointWitness.S JointWitness.jointWitness.n JointWitness.jointWitness.R JointWitness.jointWitness.F.k0
        JointWitness.jointWitness.F.kf M k, IsAdmConfig F := by
  let _ := JointWitness.jointWitness.nz
  refine ⟨Config.empty, JointWitness.jointWitness.H, JointWitness.jointWitness.hadm, ?_, ?_⟩
  · intro c
    exact (JointWitness.jointWitness_isEmpty_comp k).elim c
  · simp [Config.empty]

end Balaban.LargeField
