import PfaffianDescent.ActualP3QuadraticFactorData165
import PfaffianDescent.OneDimensionalQuotientKernelTransport
import PfaffianDescent.ActualOriginalPositiveTwoNativeJetHZeroKernel
import Lean.Util.FoldConsts

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

/-- The original reduced point factors through the SAME native jet.
This ordinary equality cut keeps the native reduction proof opaque. -/
lemma actualOriginalNativePhiJetHZeroReduction163
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K
      ((hypersurface p hp).residueField P.1)
      ((hypersurface p hp).residueField P.1)).toRingHom) ≫
      (actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell ≫
        quotientProjMap (equationIdeal p hp)) =
      (hypersurface p hp).fromSpecResidueField P.1 ≫
        quotientProjMap (equationIdeal p hp) :=
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  (Category.assoc
    (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K
      ((hypersurface p hp).residueField P.1)
      ((hypersurface p hp).residueField P.1)).toRingHom))
    (actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell)
    (quotientProjMap (equationIdeal p hp))).symm.trans
      (congrArg
        (fun f => f ≫ quotientProjMap (equationIdeal p hp))
        (actualOriginalPositiveTwoNativeJetEmbedding_reduction p hp P hP ell))

/-- Store the genuine factor inclusion and its proved own-type polynomial law
in one context. This is a constructed witness, not a supplied certificate. -/
def actualOriginalNativePhiJetHZeroFactorData164
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :=
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
  let hfac : r ≫ i = q :=
    actualOriginalNativePhiJetHZeroReduction163 p hp P hP ell hell
  p3ActualIdealQuadraticFactorData165 i r q hfac

/-- The actual original factor map with its own inferred type. -/
def actualOriginalNativePhiJetHZeroFactorMapOwn165
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :=
  (actualOriginalNativePhiJetHZeroFactorData164 p hp P hP ell hell).val

/-- The actual original polynomial law with its own inferred type.
No paper-facing TYPE annotation or repeated scalar context occurs here. -/
def actualOriginalNativePhiJetHZeroFactorLawOwn165
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :=
  (actualOriginalNativePhiJetHZeroFactorData164 p hp P hP ell hell).property

/-- The genuine induced H0(I_d(2)) -> H0(I_P(2)) map. The factorization
of the original reduced point through d is the proved native reduction. -/
def actualOriginalNativePhiJetHZeroSheafInclusion163
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
      ActualOriginalPointIdealQuadraticSections p hp P :=
  actualOriginalNativePhiJetHZeroFactorMapOwn165 p hp P hP ell hell

/-- Identity with the stored own-type map; the public definition is a
single projection, so this proof does not rebuild any scalar context. -/
lemma actualOriginalNativePhiJetHZeroSheafInclusion_eq_factorData164
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    actualOriginalNativePhiJetHZeroSheafInclusion163 p hp P hP ell hell =
      (actualOriginalNativePhiJetHZeroFactorData164 p hp P hP ell hell).val :=
  Eq.refl ((actualOriginalNativePhiJetHZeroFactorData164 p hp P hP ell hell).val)

/-- The accepted native kernel equivalence preserves the original polynomial. This
uses its actual construction, without any global/native map comparison. -/
lemma actualOriginalNativePhiJetHZeroKernelEquiv_polynomial163
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
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
    (p3ActualIdealQuadraticIntrinsicLinearEquiv
      ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp))
      ((actualOriginalPositiveTwoNativeJetHZeroKernelEquiv p hp P hP ell hell s).val)).val =
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
  dsimp only [actualOriginalPositiveTwoNativeJetHZeroKernelEquiv,
    LinearEquiv.trans_apply, submoduleKernelThroughLinearEquiv]
  exact congrArg (fun z : intrinsicFullQuadraticSystem
    ((hypersurface p hp).fromSpecResidueField P.1 ≫
      quotientProjMap (equationIdeal p hp)) => z.val) (EP.apply_symm_apply _)

/-- A bounded cancellation cut. Equality of the underlying polynomial values
under a linear equivalence to an actual submodule implies equality in its
original domain. No instance or geometric comparison is supplied. -/
lemma linearEquiv_submodule_eq_of_val_eq163
    {K V W : Type u} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : Submodule K W) (e : V ≃ₗ[K] S) (x y : V)
    (h : (e x).val = (e y).val) : x = y := by
  exact e.injective (Subtype.ext h)

lemma actualOriginalNativePhiJetHZeroSheafInclusion_polynomial163
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
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
    (p3ActualIdealQuadraticIntrinsicLinearEquiv
      ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp))
      (actualOriginalNativePhiJetHZeroSheafInclusion163 p hp P hP ell hell s)).val =
      (p3ActualIdealQuadraticIntrinsicLinearEquiv
        (d ≫ quotientProjMap (equationIdeal p hp)) s).val :=
  actualOriginalNativePhiJetHZeroFactorLawOwn165 p hp P hP ell hell


end PfaffianDescent

