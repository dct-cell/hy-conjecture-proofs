import Problem05a.Proofs.Hereditary

namespace Problem05a
universe v

theorem ideals_of_B_projective (I : Ideal B) : Module.Projective B I := by
  infer_instance

theorem globalDimension_B_le_one : GlobalDimensionLE.{0,v} B 1 :=
  globalDimensionLE_one_of_ideals_projective B ideals_of_B_projective

end Problem05a
