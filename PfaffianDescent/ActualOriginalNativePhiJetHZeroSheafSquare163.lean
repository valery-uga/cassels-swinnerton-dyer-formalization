import PfaffianDescent.ActualOriginalNativePhiJetHZeroSheafInclusionPrefix165

/-! SOURCE ONLY / UNVERIFIED163. SAME original point, SAME embedded dual jet,
and the actual ambient ideal-sheaf H0 inclusion. The commutative square is
proved, not imposed as a comparison input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The missing literal square: forgetting the native-Phi kernel gives
exactly the genuine sheaf-induced H0 inclusion, on every section. -/
lemma actualOriginalNativePhiJetHZeroKernelEquiv_sheaf_square163
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
    (actualOriginalPositiveTwoNativeJetHZeroKernelEquiv p hp P hP ell hell s).val =
      actualOriginalNativePhiJetHZeroSheafInclusion163 p hp P hP ell hell s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  exact linearEquiv_submodule_eq_of_val_eq163
    (intrinsicFullQuadraticSystem
      ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)))
    (p3ActualIdealQuadraticIntrinsicLinearEquiv
      ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)))
    (actualOriginalPositiveTwoNativeJetHZeroKernelEquiv p hp P hP ell hell s).val
    (actualOriginalNativePhiJetHZeroSheafInclusion163 p hp P hP ell hell s)
    ((actualOriginalNativePhiJetHZeroKernelEquiv_polynomial163 p hp P hP ell hell s).trans
      (actualOriginalNativePhiJetHZeroSheafInclusion_polynomial163 p hp P hP ell hell s).symm)

end PfaffianDescent
