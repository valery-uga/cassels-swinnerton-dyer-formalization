import PfaffianDescent.ActualPointLocalSectionClassRestrictTop
import PfaffianDescent.ActualOriginalPositiveTwoPointBasisCoefficient

/- SOURCE ONLY / UNVERIFIED. The SAME actual original homogeneous
coordinate-square section, restricted to any actual point-containing open,
has unit coefficient under the internally constructed original O2 Iso. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def actualOriginalPositiveTwoLocalBasisSection
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (U : (hypersurface p hp).Opens) :
    (positiveSheafOfModules (grading (equationIdeal p hp)) 2).val.obj (op U) :=
  (positiveSheafOfModules (grading (equationIdeal p hp)) 2).val.map
    (homOfLE (show U ≤ ⊤ from le_top)).op
      ((actualOriginalPositiveTwoBasisSection p hp P hP).val.app (op ⊤)
        (1 : Γ(hypersurface p hp, ⊤)))

lemma actualOriginalPositiveTwoLocalBasisCoefficient_one
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (U : (hypersurface p hp).Opens)
    (hU : (hypersurface p hp).fromSpecResidueField P.1 ⁻¹ᵁ U = ⊤) :
    (actualOriginalPositiveTwoPointTrivialization p hp P hP).hom.val.app (op ⊤)
      (actualPointLocalSectionClass ((hypersurface p hp).fromSpecResidueField P.1)
        (positiveSheafOfModules (grading (equationIdeal p hp)) 2) U hU
        (actualOriginalPositiveTwoLocalBasisSection p hp P hP U)) =
      (1 : Γ(Spec (.of ((hypersurface p hp).residueField P.1)), ⊤)) := by
  have h := actualPointLocalSectionClass_restrict_unitHom
    ((hypersurface p hp).fromSpecResidueField P.1)
    (positiveSheafOfModules (grading (equationIdeal p hp)) 2) U hU
    (actualOriginalPositiveTwoBasisSection p hp P hP)
  exact (congrArg (fun z =>
    (actualOriginalPositiveTwoPointTrivialization p hp P hP).hom.val.app (op ⊤) z) h).trans
      (actualOriginalPositiveTwoPointBasisCoefficient_one p hp P hP)

end PfaffianDescent
