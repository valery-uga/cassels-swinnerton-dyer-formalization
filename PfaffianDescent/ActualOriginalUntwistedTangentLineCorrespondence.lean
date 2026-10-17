import PfaffianDescent.OneDimensionalQuotientDualProjectivization
import PfaffianDescent.ActualOriginalAllSingleSupportQuotientCorrespondence
import PfaffianDescent.ActualCubicPositiveTwoDifferentialPointFiber

/-! SOURCE ONLY / UNVERIFIED. Literal lines in the dual of the SAME
original untwisted cotangent fiber correspond to ALL original embedded
rank-eight singleton-support schemes. Untwisting and all class equivalences
are constructed internally. Representative maps retain the supplied immersion.
The class statement does not assert equality with an untrivialized target
N tensor O(-2) representative. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual Omega(S/K)|P fiber, with the original relative base map. -/
abbrev ActualOriginalUntwistedCotangentFiber
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) :=
  (moduleSpecΓFunctor (R := CommRingCat.of ((hypersurface p hp).residueField P.1))).obj
    ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
      (schemeRelativeDifferentials (hypersurfaceToBase p hp)))

abbrev ActualOriginalUntwistedQuotientClasses
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) :=
  Quotient (surjectiveOneDimensionalQuotientSetoid
    ((hypersurface p hp).residueField P.1) (ActualOriginalUntwistedCotangentFiber p hp P))

/-- Actual tangent lines, represented without an assumed basis or dual comparison. -/
abbrev ActualOriginalTangentLines
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) :=
  {H : Submodule ((hypersurface p hp).residueField P.1)
      (Module.Dual ((hypersurface p hp).residueField P.1)
        (ActualOriginalUntwistedCotangentFiber p hp P)) //
    Module.finrank ((hypersurface p hp).residueField P.1) H = 1}

/-- Use the independently derived SAME actual point untwist, no certificate input. -/
def actualOriginalPositiveTwoUntwistEquiv
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) :
    ActualOriginalPositiveTwoFiber p hp P ≃ₗ[(hypersurface p hp).residueField P.1]
      ActualOriginalUntwistedCotangentFiber p hp P :=
  actualCubicPositiveTwoDifferentialPointFiberEquiv (K := K)
    (L := (hypersurface p hp).residueField P.1) p hp
    ((hypersurface p hp).fromSpecResidueField P.1)

def actualOriginalPositiveTwoQuotientClasses_untwistEquiv
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) :
    ActualOriginalPositiveTwoQuotientClasses p hp P ≃
      ActualOriginalUntwistedQuotientClasses p hp P :=
  surjectiveOneDimensionalQuotientClasses_sourceEquiv
    (actualOriginalPositiveTwoUntwistEquiv p hp P)

def actualOriginalPositiveTwoQuotientClasses_tangentLineEquiv
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) :
    ActualOriginalPositiveTwoQuotientClasses p hp P ≃ ActualOriginalTangentLines p hp P :=
  (actualOriginalPositiveTwoQuotientClasses_untwistEquiv p hp P).trans
    (surjectiveOneDimensionalQuotientClasses_dualLineEquiv
      (L := (hypersurface p hp).residueField P.1)
      (V := ActualOriginalUntwistedCotangentFiber p hp P))

section
variable {K : Type u} [Field K] [PerfectField K]
  (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  (P : closedPoints (hypersurface p hp))
  (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)

/-- Full arbitrary-Z correspondence for quotients of the ACTUAL untwisted Omega. -/
def actualOriginalUntwistedQuotientCorrespondence :
    ActualOriginalUntwistedQuotientClasses p hp P ≃
      ActualOriginalRankEightEmbeddedJetClasses p hp P :=
  (actualOriginalPositiveTwoQuotientClasses_untwistEquiv p hp P).symm.trans
    (actualOriginalAllSingleSupportQuotientCorrespondence p hp P hP)

/-- Literal manuscript tangent-line equivalence over the SAME original surface. -/
def actualOriginalTangentLineCorrespondence :
    ActualOriginalTangentLines p hp P ≃ ActualOriginalRankEightEmbeddedJetClasses p hp P :=
  (actualOriginalPositiveTwoQuotientClasses_tangentLineEquiv p hp P).symm.trans
    (actualOriginalAllSingleSupportQuotientCorrespondence p hp P hP)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The tangent-line inverse retains the actual given i and its internally
constructed dual presentation; no phi, quotient or class equivalence is supplied. -/
theorem actualOriginalTangentLineCorrespondence_inverse_given_immersion
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hSupport : Set.range i = {P.1})
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ hypersurfaceToBase p hp) = 8) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let U := actualOriginalPositiveTwoUntwistEquiv p hp P
    ∃ e : Γ(Z, ⊤) ≃ₐ[K] DualNumber ((hypersurface p hp).residueField P.1),
      ∃ ell : ActualOriginalUntwistedCotangentFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
          (hypersurface p hp).residueField P.1,
        ∃ hell : Function.Surjective ell,
          actualOriginalPositiveTwoNativeJetEmbedding p hp P hP (ell.comp U.toLinearMap) =
            Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Z.isoSpec.inv ≫ i ∧
          actualOriginalTangentLineCorrespondence p hp P hP
            (surjectiveOneDimensionalQuotientClasses_dualLineEquiv
              (Quotient.mk _ ⟨ell, hell⟩)) =
            Quotient.mk _ (actualOriginalRankEightEmbeddedJetOfImmersion
              p hp P i hSupport hZ) := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let U := actualOriginalPositiveTwoUntwistEquiv p hp P
  let C := actualOriginalAllSingleSupportQuotientCorrespondence p hp P hP
  let G := actualOriginalPositiveTwoQuotientClasses_tangentLineEquiv p hp P
  let A : ActualOriginalRankEightEmbeddedJetClasses p hp P :=
    Quotient.mk _ (actualOriginalRankEightEmbeddedJetOfImmersion p hp P i hSupport hZ)
  obtain ⟨e, ellE, hellE, hemb, hInv⟩ :=
    actualOriginalAllSingleSupportQuotientCorrespondence_inverse_given_immersion
      p hp P hP i hSupport hZ
  let ell := ellE.comp U.symm.toLinearMap
  have hell : Function.Surjective ell := hellE.comp U.symm.surjective
  let a : ActualOriginalPositiveTwoQuotientClasses p hp P := Quotient.mk _ ⟨ellE, hellE⟩
  have hround : ell.comp U.toLinearMap = ellE := by
    apply LinearMap.ext
    intro x
    change ellE (U.symm (U x)) = ellE x
    rw [U.symm_apply_apply]
  have hclass : actualOriginalPositiveTwoQuotientClasses_untwistEquiv p hp P a =
      Quotient.mk _ ⟨ell, hell⟩ := by
    rfl
  have hg : G a = surjectiveOneDimensionalQuotientClasses_dualLineEquiv
      (Quotient.mk _ ⟨ell, hell⟩) :=
    congrArg surjectiveOneDimensionalQuotientClasses_dualLineEquiv hclass
  have hForward : C a = A := by
    change C.symm A = a at hInv
    have h := congrArg C hInv
    exact ((C.apply_symm_apply A).symm.trans h).symm
  refine ⟨e, ell, hell, ?_, ?_⟩
  · exact (congrArg (actualOriginalPositiveTwoNativeJetEmbedding p hp P hP) hround).trans hemb
  · change C (G.symm (surjectiveOneDimensionalQuotientClasses_dualLineEquiv
      (Quotient.mk _ ⟨ell, hell⟩))) = A
    have hinv : G.symm (surjectiveOneDimensionalQuotientClasses_dualLineEquiv
        (Quotient.mk _ ⟨ell, hell⟩)) = a :=
      (congrArg G.symm hg).symm.trans (G.symm_apply_apply a)
    exact (congrArg C hinv).trans hForward

end
end PfaffianDescent
