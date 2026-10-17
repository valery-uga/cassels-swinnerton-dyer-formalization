import PfaffianDescent.ActualP3QuadraticRestrictionChartComparison
import PfaffianDescent.IntrinsicFiniteTripleQuadraticDimension

/- SOURCE ONLY / UNVERIFIED. Literal actual H0(I_Z(2)) dimension in the
finite three-quadric net setting. Intrinsic regularity/saturation/rank equality
are discharged by the accepted actual original-scheme finite-net provider;
the actual H0 dictionary is discharged by the new universal chart theorem. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual sheaf-global quadratic dimension for SAME original Z included
scheme-theoretically in an actual finite three-quadric complete intersection. -/
theorem sectionFour_actual_ideal_quadratic_global_dimension_three_of_finite_triple
    {K : Type u} [Field K]
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 8) :
    Module.finrank K (SchemeModuleGlobalSectionsOver
      (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist
        (l ≫ quotientProjMap (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
        (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2))) = 3 := by
  rw [p3ActualIdealQuadratic_finrank_eq_intrinsic]
  exact intrinsicFullQuadraticSystem_finrank_eq_three_of_finite_triple f g h hf hg hh l hZ

/-- Actual sheaf-H0 version of the accepted original finite-net containment
wrapper. Its containment hypothesis is scheme-theoretic i.ker, not carrier
containment or a desired regularity/dimension/global-section certificate. -/
theorem sectionFour_actual_ideal_quadratic_global_dimension_three_of_finite_net
    {K : Type u} [Field K]
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))]
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase f hf)]
    (hker : (tripleCompleteIntersectionToHypersurface f g h hf hg hh).ker ≤ i.ker)
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ hypersurfaceToBase f hf) = 8) :
    Module.finrank K (SchemeModuleGlobalSectionsOver
      (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (i ≫ hypersurfaceToAmbient f hf)
        (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2))) = 3 := by
  rw [p3ActualIdealQuadratic_finrank_eq_intrinsic]
  exact sectionFour_intrinsic_full_quadratic_dimension_three_of_finite_net
    f g h hf hg hh i hker hZ

end PfaffianDescent
