import PfaffianDescent.QuarticTwistedCubicSeparableClosure
import PfaffianDescent.QuarticTwistedCubicGeometricPresentation

/-!
# Separable geometric presentations of twisted cubics

The data in this file is the coordinate-level form of the hypothesis that a
projective curve becomes a twisted cubic after separable base change.
-/

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K]

/-- A three-quadric projective curve together with a coordinate
identification of its separable base change with the standard twisted cubic.
The structure is data-valued, so its equations and coordinate change can be
used to construct the resulting scheme isomorphism. -/
structure SeparableStandardTwistedCubicPresentation
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) where
  equations : Fin 3 → MvPolynomial (Fin 4) K
  equations_homogeneous : ∀ i, (equations i).IsHomogeneous 2
  ideal_eq_span : I.toIdeal = Ideal.span (Set.range equations)
  coordinate_change : GL (Fin 4) (SeparableClosure K)
  coordinate_change_standard :
    (Ideal.span (Set.range (fun i => MvPolynomial.map
      (algebraMap K (SeparableClosure K)) (equations i)))).map
      (linearSubstitution (coordinate_change :
        Matrix (Fin 4) (Fin 4) (SeparableClosure K))).toRingHom =
      standardTwistedCubicIdeal (SeparableClosure K)

/-- After separable base change, the projective curve is the standard twisted
cubic up to an invertible linear coordinate change. -/
def SeparableGeometricallyStandardTwistedCubic
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) : Prop :=
  ∃ M : GL (Fin 4) (SeparableClosure K),
    (I.toIdeal.map (MvPolynomial.map (algebraMap K (SeparableClosure K)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) (SeparableClosure K))).toRingHom =
        standardTwistedCubicIdeal (SeparableClosure K)

/-- The intrinsic quadratic ideal calculation and a separable geometric
standardization produce the coordinate certificate used by descent. -/
noncomputable def separableStandardTwistedCubicPresentation_of_quadraticPiece
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgen : quadraticPieceGenerates I)
    (hI : Module.finrank K (homogeneousIdealPiece I 2) = 3)
    (hgeo : SeparableGeometricallyStandardTwistedCubic I) :
    SeparableStandardTwistedCubicPresentation I := by
  let Q : Fin 3 → MvPolynomial (Fin 4) K := Classical.choose
    (exists_three_quadrics_generating_of_quadraticPieceGenerates I hgen hI)
  have hQ : (∀ i, (Q i).IsHomogeneous 2) ∧ I.toIdeal = Ideal.span (Set.range Q) :=
    Classical.choose_spec
      (exists_three_quadrics_generating_of_quadraticPieceGenerates I hgen hI)
  let M : GL (Fin 4) (SeparableClosure K) := Classical.choose hgeo
  have hM : (I.toIdeal.map (MvPolynomial.map (algebraMap K (SeparableClosure K)))).map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) (SeparableClosure K))).toRingHom =
        standardTwistedCubicIdeal (SeparableClosure K) := Classical.choose_spec hgeo
  refine ⟨Q, hQ.1, hQ.2, M, ?_⟩
  have hbase : I.toIdeal.map (MvPolynomial.map (algebraMap K (SeparableClosure K))) =
      Ideal.span (Set.range (fun i => MvPolynomial.map
        (algebraMap K (SeparableClosure K)) (Q i))) := by
    rw [hQ.2, Ideal.map_span]
    congr 1
    ext p
    constructor
    · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Q i, ⟨i, rfl⟩, rfl⟩
  rw [← hbase]
  exact hM

/-- The descended ground-field linear coordinate change of a separable
standard presentation. -/
noncomputable def SeparableStandardTwistedCubicPresentation.groundCoordinateChange
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (p : SeparableStandardTwistedCubicPresentation I) : GL (Fin 4) K :=
  Classical.choose (separableClosure_standardPresentation_descends p.equations
    p.coordinate_change p.coordinate_change_standard)

/-- The descended coordinate change carries the original homogeneous ideal to
the standard twisted-cubic ideal. -/
theorem SeparableStandardTwistedCubicPresentation.groundCoordinateChange_spec
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (p : SeparableStandardTwistedCubicPresentation I) :
    I.toIdeal.map (linearSubstitution
      (p.groundCoordinateChange : Matrix (Fin 4) (Fin 4) K)).toRingHom =
      standardTwistedCubicIdeal K := by
  rw [p.ideal_eq_span]
  exact Classical.choose_spec (separableClosure_standardPresentation_descends p.equations
    p.coordinate_change p.coordinate_change_standard)

/-- The all-field separable certificate supplies the ordinary ground
twisted-cubic presentation used by the projective-coordinate API. -/
theorem SeparableStandardTwistedCubicPresentation.toGroundPresentation
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (p : SeparableStandardTwistedCubicPresentation I) :
    GroundTwistedCubicPresentation I :=
  ⟨p.groundCoordinateChange, p.groundCoordinateChange_spec⟩

/-- A separable standard twisted-cubic presentation has a rational section
over the ground field. -/
theorem SeparableStandardTwistedCubicPresentation.has_rational_section
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (p : SeparableStandardTwistedCubicPresentation I) :
    ∃ s : Spec (.of K) ⟶ scheme I, s ≫ toBase I = 𝟙 _ := by
  have hdet : IsUnit ((p.groundCoordinateChange : Matrix (Fin 4) (Fin 4) K).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit p.groundCoordinateChange)
  exact splitTwistedCubic_has_rational_section I
    (p.groundCoordinateChange : Matrix (Fin 4) (Fin 4) K) hdet
    p.groundCoordinateChange_spec

/-- The projective curve of a separable standard twisted-cubic presentation
is the projective line over the ground field. -/
noncomputable def SeparableStandardTwistedCubicPresentation.schemeIsoProjectiveLine
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (p : SeparableStandardTwistedCubicPresentation I) :
    scheme I ≅ projectiveLineProj K := by
  exact p.toGroundPresentation.schemeIsoProjectiveLine

/-- A quadratically generated three-dimensional projective ideal which is
separably the standard twisted cubic is the projective line over the ground
field. -/
noncomputable def schemeIsoProjectiveLine_of_quadraticPiece
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgen : quadraticPieceGenerates I)
    (hI : Module.finrank K (homogeneousIdealPiece I 2) = 3)
    (hgeo : SeparableGeometricallyStandardTwistedCubic I) :
    scheme I ≅ projectiveLineProj K :=
  (separableStandardTwistedCubicPresentation_of_quadraticPiece hgen hI hgeo).schemeIsoProjectiveLine

end PfaffianDescent.QuarticNet
