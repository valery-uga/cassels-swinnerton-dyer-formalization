import PfaffianDescent.ActualP3QuadraticDictionaryFactorNaturality
import PfaffianDescent.ActualOriginalGlobalCanonicalPhiJetHZeroKernel

/-! SOURCE ONLY / UNVERIFIED. SAME original point, SAME embedded dual jet,
and the actual ambient ideal-sheaf H0 inclusion. The commutative square is
proved, not imposed as a comparison input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The genuine induced H0(I_d(2)) -> H0(I_P(2)) map. The factorization
of the original reduced point through d is the proved native reduction. -/
def actualOriginalGlobalCanonicalPhiJetHZeroSheafInclusion
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
    SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)) →ₗ[K]
      ActualOriginalPointIdealQuadraticSections p hp P := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫
    quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := by
    dsimp only [r, i, q, d, L]
    rw [← Category.assoc, actualOriginalPositiveTwoNativeJetEmbedding_reduction]
  exact actualAmbientClosedIdealTwistHZeroFactorInclusion
    (ambientToBase (R := K) (σ := Fin 4)) i r q hfac
    (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)

/-- The existing kernel equivalence preserves the original polynomial. This
uses its actual construction, including the value-preserving ofEq at the
last global/native Phi step. -/
lemma actualOriginalGlobalCanonicalPhiJetHZeroKernelEquiv_polynomial
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
    (p3ActualIdealQuadraticIntrinsicLinearEquiv
      ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp))
      ((actualOriginalGlobalCanonicalPhiJetHZeroKernelEquiv p hp P hP ell hell s).val)).val =
      (p3ActualIdealQuadraticIntrinsicLinearEquiv
        (d ≫ quotientProjMap (equationIdeal p hp)) s).val := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let E2 := ActualOriginalPositiveTwoFiber p hp P
  letI : Module K E2 := Module.compHom E2 (algebraMap K L)
  letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  let EP := p3ActualIdealQuadraticIntrinsicLinearEquiv
    ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp))
  let EZ := p3ActualIdealQuadraticIntrinsicLinearEquiv
    (d ≫ quotientProjMap (equationIdeal p hp))
  have hforget :
      (actualOriginalGlobalCanonicalPhiJetHZeroKernelEquiv p hp P hP ell hell s).val =
      (actualOriginalPositiveTwoNativeJetHZeroKernelEquiv p hp P hP ell hell s).val := by
    dsimp only [actualOriginalGlobalCanonicalPhiJetHZeroKernelEquiv,
      LinearEquiv.trans_apply]
    rfl
  rw [hforget]
  dsimp only [actualOriginalPositiveTwoNativeJetHZeroKernelEquiv,
    LinearEquiv.trans_apply, submoduleKernelThroughLinearEquiv]
  exact congrArg (fun z : intrinsicFullQuadraticSystem
    ((hypersurface p hp).fromSpecResidueField P.1 ≫
      quotientProjMap (equationIdeal p hp)) => z.val) (EP.apply_symm_apply _)

/-- The missing literal square: forgetting the global-Phi kernel gives
exactly the genuine sheaf-induced H0 inclusion, on every section. -/
lemma actualOriginalGlobalCanonicalPhiJetHZeroKernelEquiv_sheaf_square
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
    (actualOriginalGlobalCanonicalPhiJetHZeroKernelEquiv p hp P hP ell hell s).val =
      actualOriginalGlobalCanonicalPhiJetHZeroSheafInclusion p hp P hP ell hell s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫
    quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := by
    dsimp only [r, i, q, d, L]
    rw [← Category.assoc, actualOriginalPositiveTwoNativeJetEmbedding_reduction]
  intro s
  apply (p3ActualIdealQuadraticIntrinsicLinearEquiv q).injective
  apply Subtype.ext
  calc
    _ = (p3ActualIdealQuadraticIntrinsicLinearEquiv i s).val :=
      actualOriginalGlobalCanonicalPhiJetHZeroKernelEquiv_polynomial p hp P hP ell hell s
    _ = _ := (p3ActualIdealQuadraticIntrinsicLinearEquiv_factor_naturality
      i r q hfac s).symm

/-- Whole K-linear-map form of the square, with the actual kernel subtype. -/
lemma actualOriginalGlobalCanonicalPhiJetHZeroKernelEquiv_sheaf_square_linearMap
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let E2 := ActualOriginalPositiveTwoFiber p hp P
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
    (LinearMap.ker ((ell.restrictScalars K).comp
      (actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P))).subtype.comp
      (actualOriginalGlobalCanonicalPhiJetHZeroKernelEquiv p hp P hP ell hell).toLinearMap =
      actualOriginalGlobalCanonicalPhiJetHZeroSheafInclusion p hp P hP ell hell := by
  dsimp only
  ext s
  exact actualOriginalGlobalCanonicalPhiJetHZeroKernelEquiv_sheaf_square p hp P hP ell hell s

end PfaffianDescent
