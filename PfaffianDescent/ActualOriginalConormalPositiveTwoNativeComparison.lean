import PfaffianDescent.ActualOriginalIdealQuadraticConormalClass
import PfaffianDescent.ActualOriginalIdealQuadraticPositiveTwoPhi
import PfaffianDescent.SeparableResidueCotangentKaehlerFiber

/- SOURCE ONLY / UNVERIFIED. The SAME native original I/I^2 maps by the
ACTUAL canonical conormal map into genuine Omega(2) using its native twist
generator. Phi factors this real conormal class exactly. No arbitrary
conormal/fiber comparison certificate is supplied. Global across-chart
conormal SHEAF/twist identification remains an additional assembly step. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory TensorProduct KaehlerDifferential
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def actualOriginalConormalPositiveTwoNativeEquiv
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let R := ChartRing (equationIdeal p hp) C.index
    let L := (hypersurface p hp).residueField P.1
    let E2 := (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (actualCubicPositiveTwoDifferentials p hp))
    letI : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    (RingHom.ker C.residue).Cotangent ≃ₗ[K] E2 := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) P
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let R := ChartRing (equationIdeal p hp) C.index
  let L := (hypersurface p hp).residueField P.1
  let E2 := (moduleSpecΓFunctor (R := .of L)).obj
    ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
      (actualCubicPositiveTwoDifferentials p hp))
  letI : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  letI : Module K E2 := Module.compHom E2 (algebraMap K L)
  letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
  let rho : R →ₐ[K] L :=
    { C.residue with commutes' := fun c => RingHom.congr_fun C.base c }
  let c := separableResidue_cotangentKaehlerFiberEquiv rho C.residue_surjective
  let E := actualCubicPositiveTwoOriginalNativePointFiberEquiv p hp
    ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
  exact (c.restrictScalars K).trans (E.symm.restrictScalars K)

lemma actualOriginalIdealQuadraticPositiveTwoPhi_conormal_factorization
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    actualOriginalConormalPositiveTwoNativeEquiv p hp P hP
      (actualOriginalIdealQuadraticConormalClass p hp P hP s) =
        actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s := by
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) P
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let R := ChartRing (equationIdeal p hp) C.index
  let L := (hypersurface p hp).residueField P.1
  letI : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  let E := actualCubicPositiveTwoOriginalNativePointFiberEquiv p hp
    ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
  apply E.injective
  rw [actualOriginalIdealQuadraticPositiveTwoPhi_native_coefficient]
  change E (E.symm (kerCotangentToTensor K R L
      ((RingHom.ker C.residue).toCotangent
        ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
          actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩))) = _
  rw [E.apply_symm_apply, kerCotangentToTensor_toCotangent]
  rfl

end PfaffianDescent
