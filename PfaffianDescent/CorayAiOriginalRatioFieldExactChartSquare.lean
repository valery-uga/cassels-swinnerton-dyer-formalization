import PfaffianDescent.CorayOriginalBasisRatioField
import PfaffianDescent.CorayBoundedOriginalEvaluationRationalMap

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

section
variable {K L : Type u} [Field K] [CommRing L] [Algebra K L]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  [IsIntegral (hypersurface p hp)]
variable (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
  (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
variable {m : ℕ}
  (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy)) (a : Fin m)

/-- Literal normalized full-basis coordinates in the SAME existing ratio
field, using exactly the original structure hom and actual function field. -/
def cubicThroughPointOriginalBasisRatioFieldCoordinates :
    let F := (hypersurface p hp).functionField
    letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    Fin m → cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a := by
  let F := (hypersurface p hp).functionField
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  exact fun i => ⟨@Div.div F (inferInstance : Div F)
    (show F from cubicThroughPointBasisGenericCoordinates p hp n y hpy j b i)
    (show F from cubicThroughPointBasisGenericCoordinates p hp n y hpy j b a),
    cubicThroughPointGeneric_normalized_mem_originalBasisRatioField p hp n y hpy j b a (b i)⟩

/-- The defining SAME E generator set is the literal original normalized
basis coordinate set. This equality is independent of image dimension. -/
theorem cubicThroughPointOriginalBasisRatioField_eq_normalizedBasisAdjoin001 :
    let F := (hypersurface p hp).functionField
    letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a =
      IntermediateField.adjoin K (Set.range (fun i =>
        @Div.div F (inferInstance : Div F)
          (show F from cubicThroughPointBasisGenericCoordinates p hp n y hpy j b i)
          (show F from cubicThroughPointBasisGenericCoordinates p hp n y hpy j b a))) := by
  rfl

/-- The actual normalized coordinates generate the ENTIRE SAME E as a
field. This is derived from its definition, not a generation certificate. -/
theorem cubicThroughPointOriginalBasisRatioFieldCoordinates_adjoin_eq_top001 :
    let F := (hypersurface p hp).functionField
    letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    let E := cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a
    IntermediateField.adjoin K
      (Set.range (cubicThroughPointOriginalBasisRatioFieldCoordinates p hp n y hpy j b a)) =
        (⊤ : IntermediateField K E) := by
  let F := (hypersurface p hp).functionField
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let E := cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a
  apply IntermediateField.map_injective E.val
  rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val,
    ← Set.range_comp']
  exact (cubicThroughPointOriginalBasisRatioField_eq_normalizedBasisAdjoin001 p hp n y hpy j b a).symm

end

section
variable {K L : Type u} [Field K] [CommRing L] [Algebra K L]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
  [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
variable (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
  (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
variable {m : ℕ}
  (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy)) (a : Fin m)

include hp0 in
/-- The original anchor normalizes to the literal unit in SAME E. -/
theorem cubicThroughPointOriginalBasisRatioFieldCoordinates_anchor_eq_one001 :
    let F := (hypersurface p hp).functionField
    letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    cubicThroughPointOriginalBasisRatioFieldCoordinates p hp n y hpy j b a a = 1 := by
  let F := (hypersurface p hp).functionField
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let xi : Fin m → F := fun i => cubicThroughPointBasisGenericCoordinates p hp n y hpy j b i
  have ha : xi a ≠ 0 := cubicThroughPointBasisGenericCoordinates_ne_zero p hp hp0 n y hpy j b a
  apply Subtype.ext
  change xi a / xi a = 1
  exact div_self ha

/-- The ACTUAL original projective affine chart maps to SAME E and then
via its literal inclusion to ORIGINAL F by exactly the already stored
original generic chart map. No image-field or differential outcome is assumed. -/
theorem cubicThroughPointOriginalBasisRatioField_projectiveChartMap_comp_val_eq001 :
    let F := (hypersurface p hp).functionField
    letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    let E := cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a
    let xE := cubicThroughPointOriginalBasisRatioFieldCoordinates p hp n y hpy j b a
    E.val.toRingHom.comp
      (projectiveEvaluationChartMap (algebraMap K E) xE a
        (by
          change cubicThroughPointOriginalBasisRatioFieldCoordinates p hp n y hpy j b a a ≠ 0
          rw [cubicThroughPointOriginalBasisRatioFieldCoordinates_anchor_eq_one001 p hp hp0 n y hpy j b a]
          exact one_ne_zero)) =
      cubicThroughPointBasisGenericChartMap p hp hp0 n y hpy j b a := by
  let F := (hypersurface p hp).functionField
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let E := cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a
  let xE := cubicThroughPointOriginalBasisRatioFieldCoordinates p hp n y hpy j b a
  have hOne : xE a = 1 := cubicThroughPointOriginalBasisRatioFieldCoordinates_anchor_eq_one001 p hp hp0 n y hpy j b a
  have hCoeff : E.val.toRingHom.comp (algebraMap K E) =
      schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp) := by
    ext c
    exact E.val.commutes c
  apply projectiveChartMap_ext a
  · rw [RingHom.comp_assoc, projectiveEvaluationChartMap_base, hCoeff]
    exact (projectiveEvaluationChartMap_base
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp))
      (cubicThroughPointBasisGenericCoordinates p hp n y hpy j b) a
      (cubicThroughPointBasisGenericCoordinates_ne_zero p hp hp0 n y hpy j b a)).symm
  · intro i
    change E.val (projectiveEvaluationChartMap (algebraMap K E) xE a (by rw [hOne]; exact one_ne_zero)
      (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a i)) =
      cubicThroughPointBasisGenericChartMap p hp hp0 n y hpy j b a
        (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a i)
    rw [projectiveEvaluationChartMap_coordinate,
      cubicThroughPointBasisGenericChartMap_coordinate, hOne, div_one]
    rfl

end
end PfaffianDescent.Coray
