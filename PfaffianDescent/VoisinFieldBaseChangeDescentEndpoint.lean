import PfaffianDescent.VoisinFieldBaseChangeFiniteFreeCover
import PfaffianDescent.VoisinFixedLinearSystemDescentEndpoint

/-!
# Fixed-linear-system endpoint with proved field base change

This specializes the descent endpoint to the actual field base change.  Its
canonical global-sections map is bijective by the finite-free Čech theorem,
so no base-change bijectivity hypothesis remains.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

noncomputable section

/-- Field-base-change specialization of the evaluation-natural endpoint.
The global-sections base-change equivalence is supplied by the finite-free
affine-cover theorem rather than assumed. -/
theorem SchemeModuleFiniteFreeAffineCover.no_generic_projectiveSection_fieldMember_of_fieldBaseChangeEvaluation
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {A Q : Scheme.{u}} [IsIntegral Q]
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    [Fintype C.ι] [DecidableEq C.ι]
    (qBase : Q ⟶ Spec (.of K))
    (n : ℕ) (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (havoid : Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField) ∉
      fixedLinearSystemBadLocus qBase base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
        marked hmarked
        (C.projectiveSectionLocalZeroGluedToAmbient base M))
    (r : Spec (.of L) ⟶ Q)
    (hr : r (IsLocalRing.closedPoint L) =
      Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField))
    (hrBase : r ≫ qBase =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (s : SchemeModuleGlobalSectionsOver
      (schemeFieldBaseChangeToField (L := L) base)
      ((Scheme.Modules.pullback
        (schemeFieldBaseChangeToOriginal (L := L) base)).obj M))
    (hs : s ≠ 0)
    (hlocalEvaluation : ∀ (i : Fin n)
      (ij : (C.projectiveSectionOpenCover base M).I₀)
      (ri : Spec (.of L) ⟶
        (C.projectiveSectionOpenCover base M).X ij),
      ri ≫ C.projectiveSectionOpenCoverToSurface base M ij =
          r ≫ marked i →
      ∀ a : I,
        ∃ geometricEvaluation :
            SchemeModuleGlobalSectionsOver
              (schemeFieldBaseChangeToField (L := L) base)
              ((Scheme.Modules.pullback
                (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) →ₗ[L] L,
          geometricEvaluation.comp
              (C.globalSectionsFieldBaseChangeLinearEquiv base M).toLinearMap =
            LinearMap.liftBaseChange L
              (C.projectiveSectionLocalBasisCoordinateEvaluationLinearMap
                base M ij ri a) ∧
          geometricEvaluation s = 0) :
    False := by
  let hbaseChange :=
    C.globalSectionsFieldBaseChangeLinearMap_bijective (L := L) base M
  apply C.no_generic_projectiveSection_fieldMember_of_pullbackBaseChangeEvaluation
    base M
    (schemeFieldBaseChangeToField (L := L) base)
    (schemeFieldBaseChangeToOriginal (L := L) base)
    qBase n marked hmarked havoid r hr hrBase hbaseChange s hs
  intro i ij ri hri a
  obtain ⟨geometricEvaluation, hcompat, hzero⟩ :=
    hlocalEvaluation i ij ri hri a
  refine ⟨geometricEvaluation, ?_, hzero⟩
  change geometricEvaluation.comp
      (schemeModuleGlobalSectionsFieldBaseChangeLinearEquiv
        (L := L) base M hbaseChange).toLinearMap = _
  rw [C.canonicalGlobalSectionsFieldBaseChangeLinearEquiv_eq
    (L := L) base M]
  exact hcompat

end

end PfaffianDescent
