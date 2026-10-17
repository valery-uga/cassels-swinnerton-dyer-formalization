import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGroundSelectedSupportCanonicalMarkedResidual
import PfaffianDescent.SerreActualCanonicalMarkedResidualInputs

/-! The checked actual residual construction consumes a derived marked record
on the literal coefficient pullback. This isolates canonical Serre middle-term
conversion from the native chosen-seed geometry. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
open SerreExtensionData
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[irreducible]
def cubicClosedPointSerreFiniteZeroResidual_groundSelected_support_canonical_marked_record_residual_eight
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
    [IsIntegral (cubicConfigurationBase p hp 3)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫ cubicConfigurationToBase p hp 3)
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hL : Module.finrank K L = 11)
    (e : SerreExtensionData (hypersurface p hp)
      (closedImmersionIdealTwist i (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (C : SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)] :=
  let F := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  let P := p.map a.hom
  let hP := hp.map a.hom
  let x := hypersurfaceToBase P hP
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp)).obj e.E
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let e' := cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalSerre a.hom p hp i e C
  let C' := cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalCover a.hom p hp i e C
  let D := serreIncidenceRankTwoAffineCover e' C'
  let pp := schemeModuleGlobalSectionsProjectiveParametersToBase x M
  let zero := D.projectiveSectionLocalZeroGluedToAmbient x M
  letI := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient x M
  letI := serreSectionUniversalZeroToParameters_isProper x M D
  let i' := cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint a.hom p hp i
  fun {L₃ : Type u} [Field L₃] [Algebra F L₃] [FiniteDimensional F L₃]
    (j₃ : Spec (.of L₃) ⟶ hypersurface P hP) [IsClosedImmersion j₃]
    (hj₃ : j₃ ≫ x = Spec.map (CommRingCat.ofHom (algebraMap F L₃)))
    (h3 : Module.finrank F L₃ = 3)
    {E : Type u} [Field E] [Algebra F E] {Cfg : Scheme.{u}}
    (d : SerreActualCanonicalMarkedResidualInputs (E := E) (Cfg := Cfg) x pp zero i' j₃) =>
    cubicClosedPointSerreFiniteZeroResidual_groundSelected_support_canonical_marked_residual_eight
      (E := E) (L₃ := L₃) p hp hp0 a ha i hi hL e C j₃ hj₃ h3
      d.cfg d.marked d.hm d.t d.ht d.s d.hW d.hsp d.n d.hout d.hpoint d.y d.hy d.hySurface

end PfaffianDescent.ProjectiveNegativeTwist
