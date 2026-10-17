import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridCanonicalMarkedPoint
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridResidueCoefficients
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridChartComponentRatios
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridGenericCoordinates
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridGenericCoefficients

/-! Actual canonical generic sixteen-point component maps transport the
native cubic restriction kernel to any literal ordered chart-zero lift. -/
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_canonicalSixteen_nativeKernel_orderedTransport
    {K E : Type u} [Field K] [Field E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 16).toScheme]
    [IsIntegral (cubicConfigurationBase p hp 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 16 ≫
      cubicConfigurationToBase p hp 16)
    (z : (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left)
    (hz : configurationQuotientMap (equationIdeal p hp) 16 z =
      (cubicConfigurationBase p hp 16).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 16))
        (IsLocalRing.closedPoint (cubicConfigurationBase p hp 16).functionField))
    (U : Scheme.{u})
    (i : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left)
    (t : Fin 16 → (U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
      (coordinate (equationIdeal p hp) 0)))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
        (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0)
        (by decide : 0 < 1) =
      (i ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 16)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 16 k).left)
    (c : Spec (.of E) ⟶ U)
    (g : (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left.residueField z →+* E)
    (hg : Spec.map (CommRingCat.ofHom g) ≫
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left.fromSpecResidueField z =
        c ≫ i) :
    let Q := cubicConfigurationBase p hp 16
    let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap p hp 16 a ha
    let b := cubicSixteenOrderedLiftFunctionFieldHom p hp z hz
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField E := (g.comp b).toAlgebra
    let j := D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
      hypersurfaceToAmbient (p.map a.hom) (hp.map a.hom)
    ∀ T : NormalizedAmbientChart Q.functionField Γ(D.val.subscheme, ⊤) (Fin 4)
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q.functionField)) j,
      ∀ s : homogeneousSubmodule (Fin 4) Q.functionField 3,
        s ∈ LinearMap.ker (homogeneousSectionRestriction T.x 3) →
        voisinDegreeTenSelectedAvoidance_mapCubicSection (L := E) s ∈
          LinearMap.ker (homogeneousSectionRestriction
            (fun l k => (Spec.preimage (c ≫ t k)).hom
              (linearChartCoordinate (equationIdeal p hp) (coordinate (equationIdeal p hp) 0)
                (coordinate_mem (equationIdeal p hp) 0) l)) 3) := by
  dsimp only
  let Q := cubicConfigurationBase p hp 16
  let O := (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left
  let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 16 a ha
  let b := cubicSixteenOrderedLiftFunctionFieldHom p hp z hz
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  letI : Algebra Q.functionField E := (g.comp b).toAlgebra
  letI : Algebra K E := ((g.comp b).comp a.hom).toAlgebra
  let j := D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
    hypersurfaceToAmbient (p.map a.hom) (hp.map a.hom)
  intro T s hs
  let φ := fun k => voisinDegreeTenSelectedAvoidance_extendComponent g
    (cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom p hp a ha z hz k)
  have hcoeff : (g.comp b).comp a.hom =
      (Spec.preimage (c ≫ i ≫ (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 16).hom)).hom :=
    voisinDegreeTenSelectedAvoidance_canonicalSixteen_coefficients_at_residueFactor
      p hp a ha z hz (c ≫ i) g hg
  have hratios : ∀ k l, (φ k (T.x 0))⁻¹ * φ k (T.x l) =
      (Spec.preimage (c ≫ t k)).hom (linearChartCoordinate (equationIdeal p hp)
        (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0) l) := by
    intro k
    have hbase := voisinDegreeTenSelectedAvoidance_orderedChartLift_fieldPoint_baseRingHom
      (equationIdeal p hp) 16 U i t ht c k
    have hbase' : (Spec.preimage (c ≫ t k)).hom.comp
        (GradedChart.baseMap (grading (equationIdeal p hp))
          (z := coordinate (equationIdeal p hp) 0)) = algebraMap K E :=
      hbase.trans hcoeff.symm
    have hmarkedE :=
      voisinDegreeTenSelectedAvoidance_canonicalSixteen_extendedComponent_actualMarkedPoint
        p hp a ha z hz (c ≫ i) g hg k
    apply voisinDegreeTenSelectedAvoidance_nativeComponent_ratios_at_actualChartPoint
      a.hom p hp (φ k) j T (c ≫ t k) hbase'
    rw [Category.assoc]
    refine hmarkedE.trans ?_
    have hchart := congrArg
      (fun v : U ⟶ hypersurface p hp => (c ≫ v) ≫ hypersurfaceToAmbient p hp) (ht k)
    have hι : Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 16) =
        (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 16).ι := rfl
    simpa only [hι, orderedConfigurationProjectivePoint, Category.assoc] using hchart.symm
  have hnorm : ∀ k, (Spec.preimage (c ≫ t k)).hom
      (linearChartCoordinate (equationIdeal p hp) (coordinate (equationIdeal p hp) 0)
        (coordinate_mem (equationIdeal p hp) 0) 0) = 1 := by
    intro k
    obtain ⟨hzero, _, _, _⟩ :=
      voisinDegreeTenSelectedAvoidance_orderedChartLift_fieldPoint_normalizedPoint
        (equationIdeal p hp) 16 U i t ht c k
    exact hzero
  exact voisinDegreeTenSelectedAvoidance_nativeCubicKernel_orderedTransport_of_componentRatios
    φ T.x _ hnorm hratios s hs

end PfaffianDescent
