import AllCharacteristics.PrescribedLaurentPencilGenericPoint
import AllCharacteristics.CubicPencilSmooth
import AllCharacteristics.ProjectiveBaseChange
import Mathlib.Algebra.Polynomial.Monomial

/-! SOURCE ONLY / UNVERIFIED. Actual k((t)) generic equation and the
scheme isomorphism to the SAME actual pencil pullback. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HomogeneousProjective
universe u
variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

def polynomialToLaurentCoefficientMap : Polynomial k →+* LaurentSeries k :=
  (algebraMap (PowerSeries k) (LaurentSeries k)).comp Polynomial.coeToPowerSeries.ringHom

theorem polynomialToLaurentCoefficientMap_injective :
    Function.Injective (polynomialToLaurentCoefficientMap (k := k)) :=
  (FaithfulSMul.algebraMap_injective (PowerSeries k) (LaurentSeries k)).comp
    (Polynomial.coe_injective k)

theorem laurentCoefficientField_infinite : Infinite (LaurentSeries k) :=
  Infinite.of_injective (polynomialToLaurentCoefficientMap (k := k))
    polynomialToLaurentCoefficientMap_injective

def prescribedLaurentGenericEquation (p g : MvPolynomial (Fin 4) k) :=
  (prescribedPowerSeriesPencil p g).map
    (algebraMap (PowerSeries k) (LaurentSeries k))

theorem prescribedLaurentGenericEquation_homogeneous
    {p g : MvPolynomial (Fin 4) k}
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) :
    (prescribedLaurentGenericEquation p g).IsHomogeneous 3 :=
  (prescribedPowerSeriesPencil_homogeneous hp hg).map _

theorem prescribedLaurentGenericEquation_eq_polynomialMap
    (p g : MvPolynomial (Fin 4) k) :
    prescribedLaurentGenericEquation p g =
      (cubicPencil p g).map (polynomialToLaurentCoefficientMap (k := k)) := by
  exact MvPolynomial.map_map _ _ _

theorem prescribedLaurentGenericEquation_ne_zero
    {p g : MvPolynomial (Fin 4) k} (hg0 : g ≠ 0) :
    prescribedLaurentGenericEquation p g ≠ 0 := by
  rw [prescribedLaurentGenericEquation_eq_polynomialMap]
  intro h
  apply cubicPencil_ne_zero_of_right hg0
  apply MvPolynomial.map_injective _ polynomialToLaurentCoefficientMap_injective
  simpa only [map_zero] using h

theorem prescribedLaurentGenericEquation_smooth
    {p g : MvPolynomial (Fin 4) k}
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) (hg0 : g ≠ 0)
    [Smooth (hypersurfaceToBase g hg)] :
    Smooth (hypersurfaceToBase (prescribedLaurentGenericEquation p g)
      (prescribedLaurentGenericEquation_homogeneous hp hg)) := by
  have h := cubicPencil_map_smooth (polynomialToLaurentCoefficientMap (k := k))
    polynomialToLaurentCoefficientMap_injective hp hg hg0
  simpa only [prescribedLaurentGenericEquation, prescribedPowerSeriesPencil,
    MvPolynomial.map_map, polynomialToLaurentCoefficientMap] using h

def prescribedLaurentGenericCubicIso
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) :
    hypersurface (prescribedLaurentGenericEquation p g)
        (prescribedLaurentGenericEquation_homogeneous hp hg) ≅
      prescribedLaurentPencilFiber p g hp hg :=
  hypersurfaceBaseChangeIso (algebraMap (PowerSeries k) (LaurentSeries k))
    (prescribedPowerSeriesPencil p g) (prescribedPowerSeriesPencil_homogeneous hp hg)

theorem prescribedLaurentGenericCubicIso_hom_base
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) :
    (prescribedLaurentGenericCubicIso p g hp hg).hom ≫ pullback.snd
        (hypersurfaceToBase (prescribedPowerSeriesPencil p g)
          (prescribedPowerSeriesPencil_homogeneous hp hg))
        (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))) =
      hypersurfaceToBase (prescribedLaurentGenericEquation p g)
        (prescribedLaurentGenericEquation_homogeneous hp hg) :=
  hypersurfaceBaseChangeIso_hom_snd _ _ _

theorem prescribedLaurentGenericCubicIso_inv_base
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) :
    (prescribedLaurentGenericCubicIso p g hp hg).inv ≫
      hypersurfaceToBase (prescribedLaurentGenericEquation p g)
        (prescribedLaurentGenericEquation_homogeneous hp hg) =
      pullback.snd (hypersurfaceToBase (prescribedPowerSeriesPencil p g)
          (prescribedPowerSeriesPencil_homogeneous hp hg))
        (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))) := by
  rw [← prescribedLaurentGenericCubicIso_hom_base p g hp hg]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end AllCharacteristics
