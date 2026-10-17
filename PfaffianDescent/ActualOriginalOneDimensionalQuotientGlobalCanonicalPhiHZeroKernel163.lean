import PfaffianDescent.ActualOriginalOneDimensionalQuotientNativePhiHZeroKernel163
import PfaffianDescent.ActualOriginalGlobalCanonicalQuadraticPhiNativeEquality

/-! SOURCE ONLY / UNVERIFIED163. Final exact canonical-map adapter.
It preserves original q, chosen target e, actual associated Z_q, nilpotent
jet ideal and GENUINE sheaf H0 inclusion; no independent existence result. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Manuscript906–933 for EVERY arbitrary one-dimensional quotient:
true ambient H0(I_Zq(2)), viewed by its proved original sheaf inclusion
into V=H0(I_P(2)), is EXACTLY ker(q∘global canonical Phi). -/
theorem actualOriginalOneDimensionalQuotient_globalCanonicalPhiHZero_injective_and_range_eq_kernel163
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
      LinearMap.ker ((q.restrictScalars K).comp (actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P)) := by
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
  let tNative := (q.restrictScalars K).comp
    (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP)
  let tGlobal := (q.restrictScalars K).comp
    (actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P)
  have hker : LinearMap.ker tNative = LinearMap.ker tGlobal := by
    dsimp only [tNative, tGlobal]
    rw [actualOriginalGlobalCanonicalQuadraticPhi_eq_native_linearMap p hp P hP]
  have hNative := actualOriginalOneDimensionalQuotient_nativePhiHZero_injective_and_range_eq_kernel163
    p hp P hP N hN q hq
  exact ⟨hNative.1, hNative.2.trans hker⟩

end PfaffianDescent
