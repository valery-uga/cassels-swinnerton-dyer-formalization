import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreNativeRankOriginal
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicCoefficientGlobalDimension

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
variable {K E : Type u} [Field K] [Field E]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
variable [hB : IsIntegral (cubicConfigurationBase p hp 3)]
local instance : IsIntegral (projectiveConfigurationQuotientOpen
    (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) 3).toScheme := hB
variable [hordered : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
local instance : IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 3).left := hordered
variable (c : Spec (.of E) ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
variable (β : (cubicConfigurationBase p hp 3).functionField →+* E)
variable (hβ : Spec.map (CommRingCat.ofHom β) ≫
    (cubicConfigurationBase p hp 3).fromSpecStalk
      (genericPoint (cubicConfigurationBase p hp 3)) =
    c ≫ configurationQuotientMap (equationIdeal p hp) 3)
variable (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
variable (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫
    cubicConfigurationToBase p hp 3)


open ProjectiveNegativeTwist

/-- Actual native unit-minor restriction onto and kernel dimension three over
the genuine unordered field; pulled section dimension is derived internally. -/
abbrev pointSplittingCubicSerreNativeRank_restriction_surjective_kernel_three
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    {A : Scheme.{u}}
    (aRank : A ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    (chart : Fin 3 → C.ι) (marked : ∀ i, A ⟶ (C.U (chart i)).toScheme)
    (hmarked : ∀ i, marked i ≫ (C.U (chart i)).ι =
      (aRank ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 i).left)
    (m : (Fin 3 × ULift.{u} (Fin 2)) ↪ Fin 9)
    (hm : IsUnit (Matrix.det (Matrix.submatrix
      (serreIncidenceNativeAffineEvaluationMatrix (hypersurfaceToBase p hp) e C h9 chart marked) id m)))
    (cA : Spec (.of E) ⟶ A) (hcA : cA ≫ aRank = c) := by
  letI : Algebra K (cubicConfigurationBase p hp 3).functionField := a.hom.toAlgebra
  let s := serreIncidenceCubicCoefficientPulledSerre a.hom p hp e C
  let Cs := serreIncidenceCubicCoefficientPulledCover a.hom p hp e C
  have hold := pointSplittingCubicSerreNativeRank_original_evaluation_surjective
    p hp c β hβ a ha e C h9 aRank chart marked hmarked m hm cA hcA
  have hglobal := pointSplittingCubicSerrePulledEvaluation_surjective
    p hp c β hβ a ha e C hold
  have hnew := serreIncidenceCubicCoefficientGlobalSections_finrank
    (F := (cubicConfigurationBase p hp 3).functionField) p hp e C
  have hsource : Module.finrank (cubicConfigurationBase p hp 3).functionField
      (SchemeModuleGlobalSectionsOver (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (show _ from s.E)) = 9 := hnew.trans h9
  exact pointSplittingCubicSerre_restriction_surjective_kernel_three
    p hp c β hβ a ha s Cs hglobal hsource

end PfaffianDescent
