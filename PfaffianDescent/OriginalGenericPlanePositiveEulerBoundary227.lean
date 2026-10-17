import PfaffianDescent.OriginalGenericPlaneThickSectionBoundary227
import PfaffianDescent.OriginalGenericPlaneCubicHOneRank226
import PfaffianDescent.CorayProperGeometricallyIntegralUnitSectionsRankOne
import PfaffianDescent.SchemeModuleFinitePointSequenceBalance

/-! SOURCE ONLY227. Positive ORIGINAL Euler number forces nonempty actual
own-support through the existing whole-cokernel rank balance. Only then is
the original thick connecting map asserted nonzero. No duplicate H1 cut. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Choose a genuine frame at the generic point while the scheme is abstract.
The frame and monomorphism are derived from ordinary rank-one local geometry. -/
private theorem positiveEulerSection_shortExactNativeCut227
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M)
    (s : M.val.obj (op ⊤)) (hs : s ≠ 0) :
    (ShortComplex.cokernelSequence (schemeModuleTopSectionHom M s)).ShortExact := by
  obtain ⟨U, hgU, ⟨eU⟩⟩ := hM (genericPoint X)
  exact (schemeModuleTopSectionHom_mono_and_cokernelSequence_shortExact
    (X := X) (K := k) pi M hM U hgU eU s hs).2

/-- Existing whole-section rank balance prevents empty actual quotient
support when the SAME middle coefficient has positive Euler number. The
unit H0/H1 ranks are explicit intermediate inputs; original geometry below
constructs them rather than assuming a genus or Euler conclusion. -/
theorem actualUnitSequence_positiveEuler_support_nonempty227
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (.of K)) (M : X.Modules)
    (phi : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ M)
    (hphi : (ShortComplex.cokernelSequence phi).ShortExact) :
    let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
    let Q := cokernel phi
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (SchemeModuleOpenSectionsOver pi O ⊤) →
    Module.finrank K (SchemeModuleOpenSectionsOver pi O ⊤) = 1 →
    Module.Finite K (schemeModuleCohomology X O 1) →
    Module.finrank K (schemeModuleCohomology X O 1) = 1 →
    Module.Finite K (SchemeModuleOpenSectionsOver pi Q ⊤) →
    Subsingleton (schemeModuleCohomology X Q 1) →
    0 < (Module.finrank K (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
      Module.finrank K (schemeModuleCohomology X M 1) →
      (schemeModuleStalkSupport Q).Nonempty := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  dsimp only
  intro h0 h0rank h1 h1rank hQ hQ1 hEuler
  by_contra hNonempty
  have hEmpty : schemeModuleStalkSupport (cokernel phi) = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hNonempty
  letI : Subsingleton (SchemeModuleOpenSectionsOver pi (cokernel phi) ⊤) :=
    schemeModule_sections_subsingleton_of_support_empty (cokernel phi) hEmpty ⊤
  have hQrank : Module.finrank K (SchemeModuleOpenSectionsOver pi (cokernel phi) ⊤) = 0 :=
    Module.finrank_zero_of_subsingleton
  have hBalance := (schemeModuleShortExact_finite_second_and_h0_h1_balance pi
    (ShortComplex.cokernelSequence phi) hphi h0 h1 hQ hQ1).2.2
  change Module.finrank K (SchemeModuleOpenSectionsOver pi M ⊤) +
      Module.finrank K (schemeModuleCohomology X
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1) =
    Module.finrank K (SchemeModuleOpenSectionsOver pi
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⊤) +
      Module.finrank K (SchemeModuleOpenSectionsOver pi (cokernel phi) ⊤) +
      Module.finrank K (schemeModuleCohomology X M 1) at hBalance
  rw [h0rank, h1rank, hQrank] at hBalance
  omega

/-- ORIGINAL smooth cubic, SAME arbitrary locally rank-one M and SAME
nonzero section, with positive ORIGINAL Euler number, give nonzero of the
literal global thick-cokernel connecting AddHom. Native own-support and
point/simple-pole geometry are all derived internally. -/
theorem originalGenericPlane_positiveEulerSection_boundaryNonzero227
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    let F := GenericHyperplaneField K
    let pE := genericPlaneCubic p
    let hpE := genericPlaneCubic_isHomogeneous p hp
    let X := hypersurface pE hpE
    let pi := hypersurfaceToBase pE hpE
    letI : HasExt.{u} X.Modules := schemeModules_hasExt X
    letI : Linear F X.Modules := schemeModulesLinearOver pi
    ∀ (M : X.Modules), schemeModuleLocallyRankOne M →
      ∀ (s : M.val.obj (op ⊤)), s ≠ 0 →
        0 < (Module.finrank F (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
          Module.finrank F (schemeModuleCohomology X M 1) →
        ∃ hphi : (ShortComplex.cokernelSequence (schemeModuleTopSectionHom M s)).ShortExact,
          (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hphi).postcomp
            (show X.Modules from SheafOfModules.unit X.ringCatSheaf) (zero_add 1) ≠ 0 := by
  classical
  dsimp only
  let F := GenericHyperplaneField K
  let pE := genericPlaneCubic p
  let hpE := genericPlaneCubic_isHomogeneous p hp
  let X := hypersurface pE hpE
  let pi := hypersurfaceToBase pE hpE
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  letI : HasExt.{u} X.Modules := schemeModules_hasExt X
  letI : Linear F X.Modules := schemeModulesLinearOver pi
  letI : Smooth pi := smoothCubic_actualGenericPlaneCubic_smooth p hp hp0
  letI : IsIntegral X := smoothCubic_actualGenericPlaneCubic_isIntegral p hp hp0
  letI : GeometricallyIntegral pi := smoothCubic_actualGenericPlaneCubic_geometricallyIntegral p hp hp0
  have hUnit0 := integralProperGeometricallyIntegral_unitTopSections_finite_and_finrank_one pi
  have hUnit1 := smoothCubic_genericPlaneCubic_unit_cohomology_one_finite_finrank_eq_one226 p hp hp0
  intro M hM s hs hEuler
  let phi := schemeModuleTopSectionHom M s
  have hphi : (ShortComplex.cokernelSequence phi).ShortExact :=
    positiveEulerSection_shortExactNativeCut227 (k := F) (X := X) pi M hM s hs
  letI : IsIntegral (scheme (equationIdeal pE hpE)) :=
    (show IsIntegral X from inferInstance)
  have hData := planeCubic_nonzeroRankOneSection_nativeSupportCohomologyData227
    (k := F) pE hpE (genericPlaneCubic_ne_zero p hp hp0) M hM s hs
  have hQ0 := hData.2.1
  have hQ1 := hData.2.2
  have hSupport := actualUnitSequence_positiveEuler_support_nonempty227 pi M phi hphi
    hUnit0.1 hUnit0.2 hUnit1.1 hUnit1.2 hQ0 hQ1 hEuler
  exact originalGenericPlane_nonemptySectionSupport_boundaryNonzero227 p hp hp0 M hM s hs hSupport

end PfaffianDescent.Coray
