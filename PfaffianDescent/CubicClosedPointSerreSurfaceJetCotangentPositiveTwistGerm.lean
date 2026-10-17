import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentLinearChartResidue
import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The actual ambient morphism inverse to division by the cubic chart
basis. Its source is the structure sheaf, and its target is the actual
positive-three twist. -/
def cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1) :
    SheafOfModules.unit (scheme I).ringCatSheaf ⟶
      positiveSheafOfModules (grading I) 3 :=
  unitToZeroTwist (grading I) ≫ zeroTwistToPositiveZero (grading I) ≫
    positiveMulHomogeneous (grading I) (degreeOnePower (grading I) ell 3) 0

/-- Applying the actual inverse chart basis morphism to the actual
structure-function q/ell³ gives the restricted actual homogeneous section. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom_fraction
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (ell : grading I 1) (q : grading I 3) :
    ((Scheme.Modules.toPresheaf (scheme I)).map
      (cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom I ell)).app
      (op (Proj.basicOpen (grading I) (ell : CoordinateRing I)))
      ((ProjectiveSpectrum.Proj.awayToSection (grading I) (ell : CoordinateRing I)).hom
        (Away.mk (grading I) ell.2 3 (q : CoordinateRing I)
          (by simpa using q.2))) =
    (positiveSheafOfModules (grading I) 3).presheaf.map
      (homOfLE (show Proj.basicOpen (grading I) (ell : CoordinateRing I) ≤ ⊤ from le_top)).op
      (PresheafOfModules.sections.eval
        (positiveGlobalSectionOfHomogeneous (grading I) 3 q) (op ⊤)) := by
  apply Subtype.ext
  funext x
  change algebraMap (CoordinateRing I)
      (Localization.AtPrime (positivePointIdeal (grading I) x.1))
      ((degreeOnePower (grading I) ell 3 : grading I 3) : CoordinateRing I) *
    (((ProjectiveSpectrum.Proj.awayToSection (grading I) (ell : CoordinateRing I)).hom
      (Away.mk (grading I) ell.2 3 (q : CoordinateRing I)
        (by simpa using q.2))).val x).val =
    Localization.mk (q : CoordinateRing I) ⟨1, Submonoid.one_mem _⟩
  have ha := ProjectiveSpectrum.Proj.awayToSection_apply (grading I)
    (ell : CoordinateRing I)
    (Away.mk (grading I) ell.2 3 (q : CoordinateRing I) (by simpa using q.2)) x
  erw [ha, Away.val_mk]
  rw [Localization.mk_eq_mk', IsLocalization.map_mk']
  simp only [RingHom.id_apply]
  erw [Localization.mk_one_eq_algebraMap]
  have he : (ell : CoordinateRing I) ∈
      (positivePointIdeal (grading I) x.1).primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    exact (ProjectiveSpectrum.mem_basicOpen (grading I)
      (ell : CoordinateRing I) x.1).mp x.2
  exact IsLocalization.mk'_spec'
    (M := (positivePointIdeal (grading I) x.1).primeCompl)
    (Localization.AtPrime (positivePointIdeal (grading I) x.1))
    (q : CoordinateRing I) ⟨(ell : CoordinateRing I) ^ 3, Submonoid.pow_mem _ he 3⟩

end PfaffianDescent
