import PfaffianDescent.ActualClosedPointConormalNativeTensorFiber
import PfaffianDescent.SurjectiveResidueTensorConormal
import PfaffianDescent.ActualOriginalQuarticCotangentChartChoice

/- SOURCE ONLY / UNVERIFIED. Actual conormal sheaf fiber of the SAME
original closed quartic point is its native residue ideal I/I^2. Native
chart, residue surjectivity, closed immersion and ambient factorization
are all derived from the original point. No desired comparison premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def actualOriginalQuarticConormalNativeEquiv
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let F := (moduleSpecΓFunctor (R := .of L)).obj (actualClosedImmersionConormalModule q)
    letI : Module K F := Module.compHom F (algebraMap K L)
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    letI : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    F ≃ₗ[K] (RingHom.ker C.residue).Cotangent := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let F := (moduleSpecΓFunctor (R := .of L)).obj (actualClosedImmersionConormalModule q)
  letI : Module K F := Module.compHom F (algebraMap K L)
  letI : IsScalarTower K L F := IsScalarTower.of_compHom K L F
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let R := ChartRing (equationIdeal p hp) C.index
  letI : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  let e := actualClosedPointConormalNativeTensorFiberEquiv_of_factorization q
    (chartι (equationIdeal p hp) C.index) C.residue C.residue_surjective C.factorization
  exact (e.restrictScalars K).trans
    ((surjectiveResidueTensorConormalEquiv C.residue C.residue_surjective).restrictScalars K)

end PfaffianDescent
