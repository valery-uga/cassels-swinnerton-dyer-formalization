import PfaffianDescent.CubicGroundKernelPolynomialGlobalLift
import PfaffianDescent.CubicSurfaceSerreGlobalLifting

/-! Native Serre lifting transfers actual cubic kernel derivatives to
actual bundle sections and their actual three point fibres. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
open ProjectiveNegativeTwist BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem pointProjection_pullbackSection
    {X Y : Scheme.{u}} (r : Y ⟶ X)
    {M N : X.Modules} (π : M ⟶ N)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    SheafOfModules.sectionsMap ((Scheme.Modules.pullback r).map π)
      (pullbackSection r M (isIso_pullbackUnitComparison _) (M.unitHomEquiv s)) =
    pullbackSection r N (isIso_pullbackUnitComparison _) (N.unitHomEquiv (s ≫ π)) := by
  have h := sectionsMap_pullbackSection r π (isIso_pullbackUnitComparison _) (M.unitHomEquiv s)
  rw [← M.unitHomEquiv_comp_apply] at h
  exact h

theorem cubicGroundKernelSerre_exists_globalJetLift
    {F L : Type u} [Field F] [Field L] [Algebra F L]
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
    {E : Type u} [Field E]
    (φ : Fin 3 → (Away (grading (equationIdeal P hP))
      (ell : CoordinateRing (equationIdeal P hP)) →+* CubicSurfaceFirstJet E))
    (β : Fin 3 → (L →+* E))
    (hres : ∀ k, cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap (φ k) = (β k).comp g) :
    ∃ s : SheafOfModules.unit (hypersurface P hP).ringCatSheaf ⟶ e.E,
      ∀ k,
        cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernelPointFiberDerivative
          (equationIdeal P hP) ell g (φ k) (β k) (hres k)
          ((SheafOfModules.sectionsMap
            ((Scheme.Modules.pullback
              (Spec.map (CommRingCat.ofHom
                (cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap (φ k))) ≫
                cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism
                  (equationIdeal P hP) ell)).map e.projection)
            (pullbackSection
              (Spec.map (CommRingCat.ofHom
                (cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap (φ k))) ≫
                cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism
                  (equationIdeal P hP) ell)
              (show (hypersurface P hP).Modules from e.E)
              (isIso_pullbackUnitComparison _) (e.E.unitHomEquiv s))).val (Opposite.op ⊤)) =
        (φ k (q.1.eval₂
          (AllCharacteristics.GradedChart.baseMap (grading (equationIdeal P hP))
            (z := (ell : CoordinateRing (equationIdeal P hP))))
          (linearChartCoordinate (equationIdeal P hP) ell ell.2))).snd := by
  classical
  let I := equationIdeal P hP
  let Q := closedImmersionIdealTwist
    (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)
    (positiveSheafOfModules (grading I) 3)
  let qC := cubicGroundKernelPolynomialClass I q
  have hqC := cubicGroundKernelPolynomialClass_fraction_zero I ell g hbase q hq
  obtain ⟨v, hv, _⟩ :=
    cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernel_globalLift I ell g qC hqC
  obtain ⟨s, hs⟩ := cubicSurfaceSerre_projection_globalSections_surjective P hP hP0 e
    (show SchemeModuleGlobalSectionsOver (hypersurfaceToBase P hP) Q from v)
  have hs' : s ≫ e.projection = v := hs
  refine ⟨s, ?_⟩
  intro k
  erw [pointProjection_pullbackSection, hs']
  have hd := cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernelPointFiberDerivative_apply
    I ell g qC hqC v hv (φ k) (β k) (hres k)
  rw [cubicGroundKernelPolynomialClass_fraction_eq I ell q] at hd
  exact hd

end PfaffianDescent
