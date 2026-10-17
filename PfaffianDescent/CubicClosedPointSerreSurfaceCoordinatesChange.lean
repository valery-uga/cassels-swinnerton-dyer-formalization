import PfaffianDescent.CubicClosedPointSerreSurfaceCoordinatesBasis
import PfaffianDescent.ProjectiveLinearCoordinateSchemeIso

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreSurfaceCoordinates_equationIdeal_map
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    (equationIdeal (linearSubstitution M p) (linearSubstitution_homogeneous M hp)).toIdeal =
      (equationIdeal p hp).toIdeal.map (linearSubstitutionEquiv M hM).toRingHom := by
  change Ideal.span ({linearSubstitution M p} : Set (MvPolynomial (Fin 4) K)) =
    (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).map
      (linearSubstitutionEquiv M hM).toRingHom
  rw [Ideal.map_span, Set.image_singleton]
  rfl

/-- Literal projective coordinate substitution gives an actual scheme
isomorphism over the original coefficient field. -/
def cubicClosedPointSerreSurfaceCoordinates_schemeIso
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    hypersurface p hp ≅ hypersurface (linearSubstitution M p)
      (linearSubstitution_homogeneous M hp) :=
  linearCoordinateChangeSchemeIso M hM _ _
    (cubicClosedPointSerreSurfaceCoordinates_equationIdeal_map M hM p hp)

theorem cubicClosedPointSerreSurfaceCoordinates_schemeIso_toBase
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    (cubicClosedPointSerreSurfaceCoordinates_schemeIso M hM p hp).hom ≫
      hypersurfaceToBase (linearSubstitution M p) (linearSubstitution_homogeneous M hp) =
      hypersurfaceToBase p hp :=
  linearCoordinateChangeSchemeIso_hom_toBase M hM _ _
    (cubicClosedPointSerreSurfaceCoordinates_equationIdeal_map M hM p hp)

/-- Smoothness is preserved for the actual transformed projective cubic. -/
theorem cubicClosedPointSerreSurfaceCoordinates_smooth
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] :
    Smooth (hypersurfaceToBase (linearSubstitution M p)
      (linearSubstitution_homogeneous M hp)) := by
  let e := cubicClosedPointSerreSurfaceCoordinates_schemeIso M hM p hp
  have hb := cubicClosedPointSerreSurfaceCoordinates_schemeIso_toBase M hM p hp
  have hi : e.inv ≫ hypersurfaceToBase p hp =
      hypersurfaceToBase (linearSubstitution M p) (linearSubstitution_homogeneous M hp) := by
    rw [← hb, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  haveI : Smooth e.inv := inferInstance
  haveI : Smooth (e.inv ≫ hypersurfaceToBase p hp) := inferInstance
  rw [← hi]
  infer_instance

/-- The literal transformed cubic remains nonzero under the polynomial
algebra automorphism attached to the actual matrix. -/
theorem cubicClosedPointSerreSurfaceCoordinates_nonzero
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (p : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) :
    linearSubstitution M p ≠ 0 := by
  intro h
  apply hp0
  apply (linearSubstitutionEquiv M hM).injective
  change linearSubstitution M p = linearSubstitution M 0
  rw [map_zero]
  exact h

end PfaffianDescent
