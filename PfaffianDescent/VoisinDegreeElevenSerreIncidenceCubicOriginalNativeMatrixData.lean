import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerrePulledEvaluationSurjective
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeTensorMatrix
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceTensorMatrixOperator
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreKernel

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
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

def serreIncidenceCubicOriginalMarkedPoint (i : Fin 3) : Spec (.of E) ⟶ hypersurface p hp :=
  (c ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3)) ≫
    (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 i).left

def serreIncidenceCubicOriginalNativeMatrix
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    {B : Scheme.{u}} (chart : Fin 3 → C.ι)
    (marked : ∀ i, B ⟶ (C.U (chart i) : Scheme.{u})) (cB : Spec (.of E) ⟶ B)
    (ρ : Fin 6 ≃ (Fin 3 × ULift.{u} (Fin 2))) : Matrix (Fin 6) (Fin 9) E :=
  ((serreIncidenceNativeAffineEvaluationMatrix (hypersurfaceToBase p hp)
    e C h9 chart marked).map (fieldPointΓevaluation cB)).submatrix ρ id

def serreIncidenceCubicOriginalNativeCoordinates
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    {B : Scheme.{u}} (chart : Fin 3 → C.ι)
    (marked : ∀ i, B ⟶ (C.U (chart i) : Scheme.{u})) (cB : Spec (.of E) ⟶ B)
    (hpoint : ∀ i, (cB ≫ marked i) ≫ (C.U (chart i)).ι =
      serreIncidenceCubicOriginalMarkedPoint p hp c i)
    (ρ : Fin 6 ≃ (Fin 3 × ULift.{u} (Fin 2))) :=
  (serreIncidenceThreePointCoordinateEquiv e.E (ULift.{u} (Fin 2))
    (serreIncidenceRankTwoAffineCover e C) chart (fun i => cB ≫ marked i)
    (serreIncidenceCubicOriginalMarkedPoint p hp c) hpoint).trans
      (LinearEquiv.piCongrLeft E (fun _ : Fin 6 => E) ρ.symm)

end PfaffianDescent
