import PfaffianDescent.ActualOriginalNativePhiJetHZeroSheafSquare163

/-! SOURCE ONLY / UNVERIFIED163. EVERY original quotient q:E→N with
actual dim_L N=1 is normalized only in its target. SAME original q constructs
SAME ell=e∘q and actual embedded dual jet; no quotient or Z selection. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Literal true ideal-sheaf H0 image equals the EXACT original q∘Phi
kernel for EVERY one-dimensional quotient. The image map is the genuine
sheaf inclusion for the SAME associated jet, as proved by the native square. -/
theorem actualOriginalOneDimensionalQuotient_nativePhiHZero_injective_and_range_eq_kernel163
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (N : Type u) [AddCommGroup N]
    [Module ((hypersurface p hp).residueField P.1) N]
    (hN : Module.finrank ((hypersurface p hp).residueField P.1) N = 1)
    (q : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1] N)
    (hq : Function.Surjective q) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let E2 := ActualOriginalPositiveTwoFiber p hp P
    letI : Module K N := Module.compHom N (algebraMap K L)
    letI : IsScalarTower K L N := IsScalarTower.of_compHom K L N
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
    let e := oneDimensionalQuotientTargetEquiv L N hN
    let ell := e.toLinearMap.comp q
    let hell : Function.Surjective ell := e.surjective.comp hq
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    Function.Injective (actualOriginalNativePhiJetHZeroSheafInclusion163 p hp P hP ell hell) ∧
      LinearMap.range (actualOriginalNativePhiJetHZeroSheafInclusion163 p hp P hP ell hell) =
      LinearMap.ker ((q.restrictScalars K).comp (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP)) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let E2 := ActualOriginalPositiveTwoFiber p hp P
  letI : Module K N := Module.compHom N (algebraMap K L)
  letI : IsScalarTower K L N := IsScalarTower.of_compHom K L N
  letI : Module K E2 := Module.compHom E2 (algebraMap K L)
  letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
  let e := oneDimensionalQuotientTargetEquiv L N hN
  let ell := e.toLinearMap.comp q
  have hell : Function.Surjective ell := e.surjective.comp hq
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  let t := (q.restrictScalars K).comp
    (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP)
  let tEll := (ell.restrictScalars K).comp
    (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP)
  let f : N →ₗ[K] L := e.toLinearMap.restrictScalars K
  have hcomp : tEll = f.comp t := by
    ext s
    rfl
  have hker : LinearMap.ker tEll = LinearMap.ker t := by
    rw [hcomp]
    exact linearMap_kernel_postcomp_injective163 t f e.injective
  have hRange :
      LinearMap.range (actualOriginalNativePhiJetHZeroSheafInclusion163 p hp P hP ell hell) =
        LinearMap.ker tEll :=
    linearMap_range_eq_kernel_of_equiv_square163 tEll
      (actualOriginalNativePhiJetHZeroSheafInclusion163 p hp P hP ell hell)
      (actualOriginalPositiveTwoNativeJetHZeroKernelEquiv p hp P hP ell hell)
      (actualOriginalNativePhiJetHZeroKernelEquiv_sheaf_square163 p hp P hP ell hell)
  have hinj : Function.Injective
      (actualOriginalNativePhiJetHZeroSheafInclusion163 p hp P hP ell hell) := by
    intro s z hsz
    apply (actualOriginalPositiveTwoNativeJetHZeroKernelEquiv p hp P hP ell hell).injective
    apply Subtype.ext
    rw [actualOriginalNativePhiJetHZeroKernelEquiv_sheaf_square163 p hp P hP ell hell s,
      actualOriginalNativePhiJetHZeroKernelEquiv_sheaf_square163 p hp P hP ell hell z]
    exact hsz
  exact ⟨hinj, hRange.trans hker⟩

end PfaffianDescent
