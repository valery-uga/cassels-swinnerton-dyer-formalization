import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCoefficientSerre
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
open SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K L : Type u} [Field K] [Field L] (g : K →+* L)
  (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  {D : Scheme.{u}} [IsAffine D] (i : D ⟶ hypersurface p hp) [IsClosedImmersion i]
  (e : SerreExtensionData (hypersurface p hp)
    (closedImmersionIdealTwist i
      (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
  (C : SerreExtensionRankTwoAffineCover e)
local instance : IsAffineHom (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) :=
  serreIncidenceCubicCoefficientMap_affine g p hp

/-- The canonical spectrum source of the SAME actual pulled support. -/
def cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint :
    Spec (.of Γ(pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i, ⊤)) ⟶
      hypersurface (p.map g) (hp.map g) :=
  (pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i).isoSpec.inv ≫
    pullback.fst (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i

instance cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint_isClosedImmersion :
    IsClosedImmersion (cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint g p hp i) := by
  dsimp only [cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint]
  infer_instance

def cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalSerre :
    SerreExtensionData (hypersurface (p.map g) (hp.map g))
      (closedImmersionIdealTwist
        (cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint g p hp i)
        (positiveSheafOfModules (grading (equationIdeal (p.map g) (hp.map g))) 3)) :=
  cubicClosedPointSerreFiniteZeroResidual_coefficientSourceSerre g p hp i e C
    (pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i).isoSpec.symm

def cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalCover :
    SerreExtensionRankTwoAffineCover
      (cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalSerre g p hp i e C) :=
  cubicClosedPointSerreFiniteZeroResidual_coefficientSourceCover g p hp i e C
    (pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i).isoSpec.symm

theorem cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalSerre_middle :
    (cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalSerre g p hp i e C).E =
      (Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp)).obj e.E := rfl

theorem cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalSerre_inclusion :
    (cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalSerre g p hp i e C).inclusion =
      (serreIncidenceCubicCoefficientPulledSerre g p hp e C).inclusion := rfl
end PfaffianDescent.ProjectiveNegativeTwist
