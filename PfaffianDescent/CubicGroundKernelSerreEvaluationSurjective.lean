import PfaffianDescent.CubicGroundKernelSerreEvaluationWitness
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentSerreFiberDimension
import PfaffianDescent.CubicSerreEvaluationSixLinearAlgebra

/-! Full normalized cubic-kernel derivatives imply surjectivity of the
ACTUAL Serre global-section evaluation on the ACTUAL three point fibres.
The derivative comparison is proved bijective, rather than assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
open ProjectiveNegativeTwist
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicGroundKernelSerre_actualEvaluation_surjective_of_kernelDerivativeSpan
    {F L E : Type u} [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra F E]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (hP0 : P ≠ 0)
    [Smooth (hypersurfaceToBase P hP)]
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) F)).Modules]
    [HasExt.{u} (hypersurface P hP).Modules]
    (ell : grading (equationIdeal P hP) 1)
    (g : Away (grading (equationIdeal P hP)) (ell : CoordinateRing (equationIdeal P hP)) →+* L)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
      (equationIdeal P hP) ell g)]
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading (equationIdeal P hP))
      (z := (ell : CoordinateRing (equationIdeal P hP)))) = algebraMap F L)
    (e : SerreExtensionData (hypersurface P hP)
      (closedImmersionIdealTwist
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
          (equationIdeal P hP) ell g)
        (positiveSheafOfModules (grading (equationIdeal P hP)) 3)))
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (B : Basis (Fin 9) F
      (cubicHomogeneousChartRestriction (equationIdeal P hP) ell ell.2 g).ker)
    (φ : Fin 3 → (Away (grading (equationIdeal P hP))
      (ell : CoordinateRing (equationIdeal P hP)) →+* CubicSurfaceFirstJet E))
    (β : Fin 3 → (L →ₐ[F] E))
    (hres : ∀ i, cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap (φ i) =
      (β i).toRingHom.comp g)
    (hspan : Submodule.span E (Set.range (fun k : Fin 9 => fun i : Fin 3 =>
      (φ i ((B k).1.1.eval₂
        (AllCharacteristics.GradedChart.baseMap (grading (equationIdeal P hP))
          (z := (ell : CoordinateRing (equationIdeal P hP))))
        (linearChartCoordinate (equationIdeal P hP) ell ell.2))).snd)) = ⊤) :
    Function.Surjective
      (cubicGroundKernelJetSectionEvaluation (equationIdeal P hP) ell g hbase φ β hres e.E) ∧
    Function.Bijective
      (cubicGroundKernelSerrePointDerivative (equationIdeal P hP) ell g φ
        (fun i => (β i).toRingHom) hres e.E e.projection) := by
  have hV := cubicClosedPointSerreSurfaceJetCotangent_serreThreeFiber_native_finrank_six e C
    (fun i => cubicGroundKernelJetPoint (equationIdeal P hP) ell (φ i))
  apply cubicSerreEvaluationSix_surjective_of_globalDerivativeWitnesses _ _ hV _ hspan
  intro k
  exact cubicGroundKernelSerre_exists_tensorEvaluationDerivativeWitness P hP hP0 ell g
    hbase e.toSequenceData (B k).1 (B k).2 φ β hres

end PfaffianDescent
