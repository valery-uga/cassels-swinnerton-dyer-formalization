import PfaffianDescent.CorayBoundedOriginalEvaluationRationalMap
import PfaffianDescent.CoraySchemeTheoreticImageIntegral
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian

/-! Source-only / unverified. The scheme-theoretic image is constructed
from the SAME stored generic evaluation point. Its support is the actual
image closure. No image dimension, differential rank or member-selector
hypothesis is introduced. The image structure map is ORIGINAL K. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped AlgebraicGeometry PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual finite-dimensional ambient projective scheme is locally
Noetherian over the original coefficient field. -/
theorem projectiveEvaluationAmbient_isLocallyNoetherian {K : Type u} [Field K]
    (m : ℕ) :
    IsLocallyNoetherian
      (scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K))) :=
  LocallyOfFiniteType.isLocallyNoetherian
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)))

section
variable {K L : Type u} [Field K] [CommRing L] [Algebra K L]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
  [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
variable (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
  (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
variable {m : ℕ}
  (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
  (a : Fin m)

/-- Compactness of the actual field spectrum and quasi-separatedness of
the actual projective target discharge quasi-compactness internally. -/
theorem cubicThroughPointBasisGenericPoint_quasiCompact :
    QuasiCompact (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a) := by
  letI : IsLocallyNoetherian
      (scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K))) :=
    projectiveEvaluationAmbient_isLocallyNoetherian m
  infer_instance

/-- The actual scheme-theoretic image of this exact basis evaluation. -/
def cubicThroughPointBasisEvaluationImage : Scheme.{u} :=
  (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a).image

/-- The actual closed inclusion into the original projective target. -/
def cubicThroughPointBasisEvaluationImageInclusion :
    cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a ⟶
      scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) :=
  (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a).imageι

/-- The image structure map retains the independently existing original
coefficient field; no new scalar action is installed. -/
def cubicThroughPointBasisEvaluationImageToBase :
    cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a ⟶ Spec (.of K) :=
  cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a ≫
    toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K))

/-- The specified generic evaluation factors through its own image. -/
def cubicThroughPointBasisGenericPointToImage :
    Spec (hypersurface p hp).functionField ⟶
      cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a :=
  (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a).toImage

theorem cubicThroughPointBasisGenericPointToImage_factorization :
    cubicThroughPointBasisGenericPointToImage p hp hp0 n y hpy j b a ≫
      cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a =
        cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a :=
  Scheme.Hom.toImage_imageι _

theorem cubicThroughPointBasisEvaluationImageInclusion_isClosedImmersion :
    IsClosedImmersion
      (cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a) := by
  change IsClosedImmersion
    (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a).imageι
  infer_instance

/-- Actual global image closure, not an affine surrogate or a supplied
image-support certificate. -/
theorem cubicThroughPointBasisEvaluationImage_range :
    Set.range (cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a) =
      closure (Set.range (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a)) := by
  letI := cubicThroughPointBasisGenericPoint_quasiCompact p hp hp0 n y hpy j b a
  change Set.range (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a).imageι = _
  rw [Scheme.IdealSheafData.range_subschemeι]
  exact Scheme.Hom.support_ker _

theorem cubicThroughPointBasisGenericPointToImage_isDominant :
    IsDominant (cubicThroughPointBasisGenericPointToImage p hp hp0 n y hpy j b a) := by
  letI := cubicThroughPointBasisGenericPoint_quasiCompact p hp hp0 n y hpy j b a
  change IsDominant (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a).toImage
  infer_instance

/-- Integrality is proved from the actual function-field source, not
assumed for the image. It does not assert geometric integrality. -/
theorem cubicThroughPointBasisEvaluationImage_isIntegral :
    IsIntegral (cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a) := by
  letI := cubicThroughPointBasisGenericPoint_quasiCompact p hp hp0 n y hpy j b a
  exact schemeImage_isIntegral
    (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a)

/-- Properness comes from the actual closed image inclusion into the
actual projective ambient space over ORIGINAL K. -/
theorem cubicThroughPointBasisEvaluationImageToBase_isProper :
    IsProper (cubicThroughPointBasisEvaluationImageToBase p hp hp0 n y hpy j b a) := by
  change IsProper
    ((cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a).imageι ≫
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)))
  infer_instance

/-- The image factorization respects the SAME original surface structure
map, with the generic field-point identity retained. -/
theorem cubicThroughPointBasisGenericPointToImage_toBase :
    cubicThroughPointBasisGenericPointToImage p hp hp0 n y hpy j b a ≫
      cubicThroughPointBasisEvaluationImageToBase p hp hp0 n y hpy j b a =
        (hypersurface p hp).fromSpecStalk (genericPoint (hypersurface p hp)) ≫
          hypersurfaceToBase p hp := by
  change (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a).toImage ≫
    ((cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a).imageι ≫
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K))) = _
  rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  exact cubicThroughPointBasisGenericPoint_toBase p hp hp0 n y hpy j b a

end
end PfaffianDescent.Coray
end
