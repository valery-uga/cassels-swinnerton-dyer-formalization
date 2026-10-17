import PfaffianDescent.CubicGroundKernelJetPointBase

/-! Actual global Serre sections supply the literal derivative vectors of
the actual chart restriction kernel, through native tensor evaluation. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
open ProjectiveNegativeTwist
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def cubicGroundKernelJetSectionEvaluation
    {F L E : Type u} [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra F E]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) (ell : grading I 1)
    (g : Away (grading I) (ell : CoordinateRing I) →+* L)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I)
      (z := (ell : CoordinateRing I))) = algebraMap F L)
    (φ : Fin 3 → (Away (grading I) (ell : CoordinateRing I) →+* CubicSurfaceFirstJet E))
    (β : Fin 3 → (L →ₐ[F] E))
    (hres : ∀ i, cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap (φ i) =
      (β i).toRingHom.comp g)
    (M : (Proj (grading I)).Modules) :
    E ⊗[F] SchemeModuleGlobalSectionsOver (toBase I) M →ₗ[E]
      (∀ i : Fin 3, (moduleSpecΓFunctor (R := CommRingCat.of E)).obj
        ((Scheme.Modules.pullback (cubicGroundKernelJetPoint I ell (φ i))).obj M)) :=
  cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
    (toBase I) (fun i => cubicGroundKernelJetPoint I ell (φ i))
      (fun i => cubicGroundKernelJetPoint_toBase I ell g hbase (φ i) (β i) (hres i)) M

theorem cubicGroundKernelSerre_exists_tensorEvaluationDerivativeWitness
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
    (e : SerreExtensionSequenceData (hypersurface P hP)
      (closedImmersionIdealTwist
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
          (equationIdeal P hP) ell g)
        (positiveSheafOfModules (grading (equationIdeal P hP)) 3)))
    (q : homogeneousSubmodule (Fin 4) F 3)
    (hq : cubicHomogeneousChartRestriction (equationIdeal P hP) ell ell.2 g q = 0)
    (φ : Fin 3 → (Away (grading (equationIdeal P hP))
      (ell : CoordinateRing (equationIdeal P hP)) →+* CubicSurfaceFirstJet E))
    (β : Fin 3 → (L →ₐ[F] E))
    (hres : ∀ i, cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap (φ i) =
      (β i).toRingHom.comp g) :
    ∃ s : SchemeModuleGlobalSectionsOver (hypersurfaceToBase P hP)
      (show (hypersurface P hP).Modules from e.E),
      cubicGroundKernelSerrePointDerivative (equationIdeal P hP) ell g φ
        (fun i => (β i).toRingHom) hres e.E e.projection
        (cubicGroundKernelJetSectionEvaluation (equationIdeal P hP) ell g hbase φ β hres e.E
          (1 ⊗ₜ[F] s)) =
      fun i => (φ i (q.1.eval₂
        (AllCharacteristics.GradedChart.baseMap (grading (equationIdeal P hP))
          (z := (ell : CoordinateRing (equationIdeal P hP))))
        (linearChartCoordinate (equationIdeal P hP) ell ell.2))).snd := by
  obtain ⟨s, hs⟩ := cubicGroundKernelSerre_exists_globalJetLift P hP hP0 ell g hbase e q hq
    φ (fun i => (β i).toRingHom) hres
  refine ⟨s, ?_⟩
  unfold cubicGroundKernelJetSectionEvaluation
  rw [cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor_one_tmul]
  funext i
  erw [cubicGroundKernelSerrePointDerivative_pullback_apply]
  exact hs i

end PfaffianDescent
