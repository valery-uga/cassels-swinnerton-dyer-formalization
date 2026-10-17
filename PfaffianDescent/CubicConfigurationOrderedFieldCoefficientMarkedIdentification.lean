import PfaffianDescent.CubicConfigurationOrderedFieldCanonicalPoint
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGroundSelectedSupport
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGroundSelectedRingField
import PfaffianDescent.CubicPointTraceFieldBaseChangeNegativeTwist

/-! A literal coefficient-cubic marked map with the actual original coordinate
and coefficient-base maps is the native degree-three support point. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[irreducible]
def cubicConfigurationOrderedThreeFieldCoefficientMarked_identification
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
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫ cubicConfigurationToBase p hp 3) :=
  let F := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  letI : Algebra F E := β.toAlgebra
  let P := p.map a.hom
  let hP := hp.map a.hom
  let base := hypersurfaceToBase P hP
  let f := cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp
  let D := cubicConfigurationGenericFiniteSubscheme p hp 3 a ha
  letI : IsFinite (D.val.subschemeι ≫ base) := D.property.1
  letI : Field Γ(D.val.subscheme, ⊤) :=
    cubicClosedPointSerreFiniteZeroResidual_groundSelectedIsFieldField
      (cubicClosedPointSerreFiniteZeroResidual_groundSelectedMarked_isField p hp hp0 a ha)
  letI : Algebra F Γ(D.val.subscheme, ⊤) := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ base)
  let j := finiteSubschemeDatumSpecMap base D
  fun (m : Spec (.of E) ⟶ hypersurface P hP)
    (hmBase : m ≫ base = Spec.map (CommRingCat.ofHom β))
    (k : Fin 3)
    (hmOriginal : m ≫ f = (c ≫ (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 k).left) =>
    (show m (IsLocalRing.closedPoint E) = j (IsLocalRing.closedPoint Γ(D.val.subscheme, ⊤)) from by
      let α := cubicConfigurationOrderedFieldComponentAlgHom p hp 3 c β hβ a ha k
      let d := Spec.map (CommRingCat.ofHom α.toRingHom) ≫ j
      have hdBase : d ≫ base = Spec.map (CommRingCat.ofHom β) := by
        dsimp only [d]
        rw [Category.assoc, finiteSubschemeDatumSpecMap_toBase, ← Spec.map_comp]
        congr 1
        ext x
        exact α.commutes x
      have hdOriginal : d ≫ f =
          (c ≫ (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left) ≫
            (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 k).left := by
        apply (cancel_mono (hypersurfaceToAmbient p hp)).1
        simpa only [d, j, f, cubicPointTraceFieldBaseChangeCubicCoefficientMap,
          Category.assoc, hypersurfaceToAmbient, projectiveCoefficientMap_comp_quotientProjMap]
          using cubicConfigurationOrderedFieldComponentAlgHom_canonicalPoint_actualMarkedPoint
            p hp 3 c β hβ a ha k
      have hmd : m = d := by
        apply (isPullback_projectiveCoefficientMap a.hom (equationIdeal p hp)
          (equationIdeal P hP) (equationIdeal_map a.hom p hp)).hom_ext
        · exact hmOriginal.trans hdOriginal.symm
        · exact hmBase.trans hdBase.symm
      rw [hmd]
      change j ((Spec.map (CommRingCat.ofHom α.toRingHom)) (IsLocalRing.closedPoint E)) = _
      exact congrArg j (Subsingleton.elim _ _))

end PfaffianDescent
