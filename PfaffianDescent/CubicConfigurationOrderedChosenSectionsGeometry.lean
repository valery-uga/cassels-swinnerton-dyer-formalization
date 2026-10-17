import PfaffianDescent.CubicConfigurationOrderedChosenSectionsSupport
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGroundSelectedCanonicalMarked

/-! One ordered-support specialization of an abstract
chosen-section record. The caller derives the field stalk and original-coordinate
identity from its actual old seed; this leaf derives support and avoidance. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[irreducible]
def cubicConfigurationOrderedThreeChosenSections_geometry
    {K E : Type u} [Field K] [CharZero K] [Field E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
    [IsIntegral (cubicConfigurationBase p hp 3)]
    (c : Spec (.of E) ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    (β : (cubicConfigurationBase p hp 3).functionField →+* E)
    (hβ : Spec.map (CommRingCat.ofHom β) ≫
      (cubicConfigurationBase p hp 3).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 3)) =
      c ≫ configurationQuotientMap (equationIdeal p hp) 3)
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫ cubicConfigurationToBase p hp 3)
    {D : Scheme.{u}} [IsAffine D]
    (ι : D ⟶ hypersurface p hp) [IsClosedImmersion ι] :=
  let F := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  letI : Algebra F E := β.toAlgebra
  let x := hypersurfaceToBase (p.map a.hom) (hp.map a.hom)
  let f := cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp
  let D₃ := cubicConfigurationGenericFiniteSubscheme p hp 3 a ha
  letI : IsFinite (D₃.val.subschemeι ≫ x) := D₃.property.1
  letI : Field Γ(D₃.val.subscheme, ⊤) :=
    cubicClosedPointSerreFiniteZeroResidual_groundSelectedIsFieldField
      (cubicClosedPointSerreFiniteZeroResidual_groundSelectedMarked_isField p hp hp0 a ha)
  let j₃ := finiteSubschemeDatumSpecMap x D₃
  fun {P Q Z : Scheme.{u}}
    (pp : P ⟶ Spec (.of F)) (qp : Q ⟶ Spec (.of F))
    (zero : Z ⟶ pullback x pp) [IsClosedImmersion zero]
    (q : Spec (.of F) ⟶ Q) (hq : q ≫ qp = 𝟙 _)
    (v : Q ⟶ P) (hv : v ≫ pp = qp)
    (d : SerreActualChosenMarkedSections x pp zero
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v))
    (n : Fin 3)
    (hf : IsField ((pullback (zero ≫ pullback.snd x pp)
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v)).presheaf.stalk
        ((d.δ n) (IsLocalRing.closedPoint E))))
    (hOriginal : serreActualChosenFibre_marked x pp zero
        ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v) d.δ n ≫ f =
      (c ≫ (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 n).left)
    (hOriginalAvoid : ((c ≫ (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 n).left)
      (IsLocalRing.closedPoint E) ∉ Set.range ι) =>
    let hsupport := cubicConfigurationOrderedThreeChosenSections_identification
      p hp hp0 c β hβ a ha pp qp zero q hq v hv d n hOriginal
    let hout := serreActualChosenMarkedSections_coefficientMarked_not_mem_range
      a.hom p hp ι pp zero
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v) d n
      ((c ≫ (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 n).left)
      hOriginal hOriginalAvoid
    serreActualChosenMarkedResidualGeometry_of_sections x pp qp zero
      (cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint a.hom p hp ι)
      j₃ q hq v hv d n hf hout hsupport

end PfaffianDescent
