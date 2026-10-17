import PfaffianDescent.AmbientRationalPointCoordinates
import PfaffianDescent.AmbientPointKoszulNativeEvaluationOverlap

/-! # A centered homogeneous basis for every actual native rational point

The original scheme morphism is retained: its normalized affine coordinates
produce an invertible basis, and actual chart overlap identifies the resulting
basis point with that morphism.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial

namespace PfaffianDescent
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- Every actual rational point over the native coefficient map is an
actual centered-basis point; no chosen-coordinate premise is required. -/
theorem ambientRationalPoint_exists_basis
    (i : Spec (.of K) ⟶ Proj PS)
    (hi : i ≫ AllCharacteristics.HomogeneousProjective.ambientToBase = 𝟙 _) :
    ∃ (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det),
      ambientPointKoszul_basisPoint M hM = i := by
  have hib : i ≫ AllCharacteristics.HomogeneousProjective.ambientToBase =
      Spec.map (CommRingCat.ofHom (RingHom.id K)) := by
    simpa using hi
  obtain ⟨j, v, hvj, hv, hpoint⟩ :=
    ambientRationalPoint_exists_normalized_evaluation K (RingHom.id K) i hib
  obtain ⟨M, hM, hMv⟩ := ambientPointKoszul_exists_basis_for_vector v hv
  refine ⟨M, hM, ?_⟩
  exact (ambientPointKoszul_basisPoint_eq_nativeEvaluationPoint M hM v hMv j hvj).trans hpoint

/-- An actual native projective rational point over the coefficient map
is a closed immersion. -/
theorem ambientRationalPoint_isClosedImmersion
    (i : Spec (.of K) ⟶ Proj PS)
    (hi : i ≫ AllCharacteristics.HomogeneousProjective.ambientToBase = 𝟙 _) :
    IsClosedImmersion i := by
  obtain ⟨M, hM, hpoint⟩ := ambientRationalPoint_exists_basis K i hi
  subst i
  infer_instance

end PfaffianDescent
