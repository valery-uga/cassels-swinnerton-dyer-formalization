import PfaffianDescent.ActualOriginalPositiveTwoLineFromNativeDualMap
import PfaffianDescent.ActualOriginalGlobalCanonicalQuadraticPhiNativeEquality

/- SOURCE ONLY / UNVERIFIED. Recover the quotient of the GENUINE global
Omega(2) fiber from the SAME actual native dual map and original residue,
then compute its action on genuine AMBIENT ideal quadratic sections.
All source/target/global-native comparisons are derived internally. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

lemma actualOriginalPositiveTwoLineFromNativeDualMap_globalPhi_coefficient
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r)
      (s : ActualOriginalPointIdealQuadraticSections p hp P),
      actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred
        (actualOriginalGlobalCanonicalQuadraticPhi p hp P s) =
          (phi (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s)).snd := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  letI : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
    (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  intro phi hred s
  rw [actualOriginalGlobalCanonicalQuadraticPhi_eq_native p hp P hP s]
  exact actualOriginalPositiveTwoLineFromNativeDualMap_Phi_coefficient p hp P hP phi hred s

end PfaffianDescent
