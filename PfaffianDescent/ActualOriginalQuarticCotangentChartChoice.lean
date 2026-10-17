import PfaffianDescent.ProjectiveClosedPointCoordinates
import AllCharacteristics.ClosedPointAlgebra
import Mathlib.FieldTheory.Perfect

/- SOURCE ONLY / UNVERIFIED. A single actual original point chart is derived
and fixed for the quotient-class map. No chosen chart certificate is public. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

structure ActualOriginalQuarticCotangentChart
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) where
  index : Fin 4
  residue : ChartRing (equationIdeal p hp) index →+* (hypersurface p hp).residueField P.1
  residue_surjective : Function.Surjective residue
  base : letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    residue.comp (chartBaseMap (equationIdeal p hp) index) =
      algebraMap K ((hypersurface p hp).residueField P.1)
  factorization : Spec.map (CommRingCat.ofHom residue) ≫ chartι (equationIdeal p hp) index =
    (hypersurface p hp).fromSpecResidueField P.1

def actualOriginalQuarticCotangentChartChoice
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    ActualOriginalQuarticCotangentChart p hp P :=
  Classical.choice (by
    letI : Algebra K ((hypersurface p hp).residueField P.1) :=
      AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    obtain ⟨j, rho, hrho, hbase, hfac⟩ :=
      closed_projective_point_chart (K := K)
        (L := (hypersurface p hp).residueField P.1) (equationIdeal p hp)
        ((hypersurface p hp).fromSpecResidueField P.1)
        (AllCharacteristics.pointAlgebra_spec (hypersurfaceToBase p hp) P.1).symm
    exact ⟨⟨j, rho, hrho, hbase, hfac⟩⟩)

theorem actualOriginalQuarticCotangentChartChoice_contains_original_point
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    P.1 ∈ Set.range (chartι (equationIdeal p hp)
      (actualOriginalQuarticCotangentChartChoice p hp P hP).index) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let L := (hypersurface p hp).residueField P.1
  refine ⟨(Spec.map (CommRingCat.ofHom C.residue)) (IsLocalRing.closedPoint L), ?_⟩
  have h := congrArg (fun q => q (IsLocalRing.closedPoint L)) C.factorization
  exact h.trans ((hypersurface p hp).fromSpecResidueField_apply P.1 _)

end PfaffianDescent
