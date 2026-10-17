import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCoefficientIdealTwistIso
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicCoefficientSerre
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceRetargetCover
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
  {D : Scheme.{u}} (i : D ⟶ hypersurface p hp) [IsClosedImmersion i]
  (e : SerreExtensionData (hypersurface p hp)
    (closedImmersionIdealTwist i
      (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
  (C : SerreExtensionRankTwoAffineCover e)

/-- The actual pulled Serre data has the actual pulled closed-point ideal
and the native new positive-three twist as its quotient. -/
def cubicClosedPointSerreFiniteZeroResidual_coefficientSerre :
    SerreExtensionData (hypersurface (p.map g) (hp.map g))
      (closedImmersionIdealTwist
        (pullback.fst (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i)
        (positiveSheafOfModules (grading (equationIdeal (p.map g) (hp.map g))) 3)) :=
  (serreIncidenceCubicCoefficientPulledSerre g p hp e C).retarget
    (cubicClosedPointSerreFiniteZeroResidual_coefficientIdealTwistIso g p hp i)

def cubicClosedPointSerreFiniteZeroResidual_coefficientCover :
    SerreExtensionRankTwoAffineCover
      (cubicClosedPointSerreFiniteZeroResidual_coefficientSerre g p hp i e C) :=
  serreIncidenceRetargetCover (serreIncidenceCubicCoefficientPulledSerre g p hp e C)
    (serreIncidenceCubicCoefficientPulledCover g p hp e C)
    (cubicClosedPointSerreFiniteZeroResidual_coefficientIdealTwistIso g p hp i)

theorem cubicClosedPointSerreFiniteZeroResidual_coefficientSerre_middle :
    (cubicClosedPointSerreFiniteZeroResidual_coefficientSerre g p hp i e C).E =
      (Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp)).obj e.E := rfl

/-- The same data and native cover after the canonical spectrum source
identification, retaining the literal pulled support. -/
def cubicClosedPointSerreFiniteZeroResidual_coefficientSourceSerre
    {Z : Scheme.{u}}
    (v : Z ≅ pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i) :
    SerreExtensionData (hypersurface (p.map g) (hp.map g))
      (closedImmersionIdealTwist
        (v.hom ≫ pullback.fst (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i)
        (positiveSheafOfModules (grading (equationIdeal (p.map g) (hp.map g))) 3)) :=
  (serreIncidenceCubicCoefficientPulledSerre g p hp e C).retarget
    (cubicClosedPointSerreFiniteZeroResidual_coefficientIdealTwistSourceIso g p hp i v)

def cubicClosedPointSerreFiniteZeroResidual_coefficientSourceCover
    {Z : Scheme.{u}}
    (v : Z ≅ pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i) :
    SerreExtensionRankTwoAffineCover
      (cubicClosedPointSerreFiniteZeroResidual_coefficientSourceSerre g p hp i e C v) :=
  serreIncidenceRetargetCover (serreIncidenceCubicCoefficientPulledSerre g p hp e C)
    (serreIncidenceCubicCoefficientPulledCover g p hp e C)
    (cubicClosedPointSerreFiniteZeroResidual_coefficientIdealTwistSourceIso g p hp i v)

theorem cubicClosedPointSerreFiniteZeroResidual_coefficientSourceSerre_middle
    {Z : Scheme.{u}}
    (v : Z ≅ pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i) :
    (cubicClosedPointSerreFiniteZeroResidual_coefficientSourceSerre g p hp i e C v).E =
      (Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp)).obj e.E := rfl
theorem cubicClosedPointSerreFiniteZeroResidual_coefficientSourceSerre_inclusion
    {Z : Scheme.{u}}
    (v : Z ≅ pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i) :
    (cubicClosedPointSerreFiniteZeroResidual_coefficientSourceSerre g p hp i e C v).inclusion =
      (serreIncidenceCubicCoefficientPulledSerre g p hp e C).inclusion := rfl

theorem cubicClosedPointSerreFiniteZeroResidual_coefficientSourceSerre_projection
    {Z : Scheme.{u}}
    (v : Z ≅ pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i) :
    (cubicClosedPointSerreFiniteZeroResidual_coefficientSourceSerre g p hp i e C v).projection =
      (serreIncidenceCubicCoefficientPulledSerre g p hp e C).projection ≫
        (cubicClosedPointSerreFiniteZeroResidual_coefficientIdealTwistSourceIso g p hp i v).hom := rfl
end PfaffianDescent.ProjectiveNegativeTwist
