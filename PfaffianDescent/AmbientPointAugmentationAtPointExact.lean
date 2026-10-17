import PfaffianDescent.AmbientPointAugmentationStalkKernel
import PfaffianDescent.AmbientPointKoszulPointPrime

/-! # Exactness of the actual Koszul augmentation at the standard point -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization MvPolynomial
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K
local instance ambientPointAugmentation_atPointPrime (x : Proj PS) :
    (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

set_option backward.isDefEq.respectTransparency false in
/-- At the actual standard point, the image of the actual final Koszul
map equals the kernel of the original point restriction morphism. -/
theorem ambientPointAugmentation_last_stalk_exact_at_point (k : Spec (.of K)) :
    Function.Exact
      ((schemeModuleStalkFunctor (Proj PS) (ambientPointKoszul_point K k)).map
        (pointGlobalTraceP3CoordinateKoszulLast K))
      ((schemeModuleStalkFunctor (Proj PS) (ambientPointKoszul_point K k)).map
        (ambientPointKoszul_augmentation K)) := by
  let x := ambientPointKoszul_point K k
  let hx : X (0 : Fin 4) ∈ (pointIdeal PS x).primeCompl :=
    ambientPointKoszul_point_mem_basicOpen K k
  intro z
  rw [ambientPointAugmentation_stalk_eq_zero_iff K k z,
    ← ambientPointKoszul_point_stalk_parameters_span_maximal K k,
    ← threeGeneratorLast_range]
  change ambientPointKoszul_unitStalkCoordinate K x z ∈
      LinearMap.range (threeGeneratorLast
        (ambientPointKoszul_stalkParameter K 1 0 x hx)
        (ambientPointKoszul_stalkParameter K 2 0 x hx)
        (ambientPointKoszul_stalkParameter K 3 0 x hx)) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(ambientPointKoszul_stalkTripleCoordinate K 0 x hx 1).symm a, ?_⟩
    apply (ambientPointKoszul_unitStalkCoordinate K x).injective
    rw [ambientPointKoszul_last_unit_stalk_coordinates,
      AddEquiv.apply_symm_apply]
    exact ha
  · rintro ⟨w, rfl⟩
    exact ⟨ambientPointKoszul_stalkTripleCoordinate K 0 x hx 1 w,
      (ambientPointKoszul_last_unit_stalk_coordinates K 0 x hx w).symm⟩

end PfaffianDescent.ProjectiveNegativeTwist
