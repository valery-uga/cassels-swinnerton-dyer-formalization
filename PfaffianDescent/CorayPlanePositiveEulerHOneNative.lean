import PfaffianDescent.OriginalGenericPlaneThickSectionBoundary227
import PfaffianDescent.ActualUnitCokernelRankOneHOneVanishing226

/-! SOURCE ONLY / UNVERIFIED. The genuine frozen original point/diagonal
geometry produces the boundary internally. This module consumes that producer,
not a boundary, trace, conormal, positive-degree vanishing or genus certificate.
All endpoints are characteristic zero and keep the SAME original plane curve,
coefficient, field action, ENTIRE cut and literal native ideal-twist sequence.
The actual positive-boundary producer remains a separately checked prerequisite;
this source draft asserts no acceptance status for imported geometry. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MvPolynomial Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native LES consequence on an abstract scheme, retaining the constructed
boundary existential and whole unit-rank pair until the actual226 application. -/
private theorem positiveEulerSection_nativeHOneConsumerCut001
    {k : Type u} [hField : Field k] {X : Scheme.{u}}
    [hExt : HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (.of k)) (M : X.Modules)
    (phi : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ M) :
    letI : Linear k X.Modules := schemeModulesLinearOver pi
    (∃ hphi : (ShortComplex.cokernelSequence (C := X.Modules) phi).ShortExact,
      (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hphi).postcomp
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) (zero_add 1) ≠ 0) →
    (Module.Finite k (schemeModuleCohomology X
        (SheafOfModules.unit X.ringCatSheaf) 1) ∧
      Module.finrank k (schemeModuleCohomology X
        (SheafOfModules.unit X.ringCatSheaf) 1) = 1) →
    Subsingleton (schemeModuleCohomology X (cokernel (C := X.Modules) phi) 1) →
    Subsingleton (schemeModuleCohomology X M 1) := by
  dsimp only
  intro hBoundaryData hUnitData hQuotientOne
  obtain ⟨hphi, hBoundary⟩ := hBoundaryData
  exact @actualUnitCokernel_cohomologyOne_subsingleton_of_rankOne_boundaryNonzero226.{u}
    k hField X hExt pi M phi hphi hBoundary hUnitData.1 hUnitData.2 hQuotientOne

/-- Project only the SAME entire section-cokernel H1-zero capability while
its original Fin3 equation is abstract; no numerical cycle tail is specialized. -/
private theorem positiveEulerSection_nativeQuotientHOneCut001
    {k : Type u} [hField : Field k]
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    [hIntegral : IsIntegral (scheme (equationIdeal p hp))]
    (M : (scheme (equationIdeal p hp)).Modules) (hM : schemeModuleLocallyRankOne M)
    (s : M.val.obj (op ⊤)) (hs : s ≠ 0) :
    let X := scheme (equationIdeal p hp)
    let Q := cokernel (schemeModuleTopSectionHom M s)
    letI : HasExt.{u} X.Modules := schemeModules_hasExt X
    Subsingleton (schemeModuleCohomology X Q 1) := by
  dsimp only
  have hData := @planeCubic_nonzeroRankOneSection_nativeSupportCohomologyData227.{u}
    k hField p hp hp0 hSmooth hIntegral M hM s hs
  exact hData.2.2

/-- Combine the entire quotient-H1 construction with the native LES while
Fin3 p/k remain abstract. The original wrapper only supplies its genuinely
constructed boundary family and unit-rank pair, with the SAME base action. -/
private theorem positiveEulerSection_nativePlaneWholeHOneCut001
    {k : Type u} [hField : Field k]
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    [hIntegral : IsIntegral (hypersurface p hp)] :
    let X := hypersurface p hp
    let pi := hypersurfaceToBase p hp
    letI : HasExt.{u} X.Modules := schemeModules_hasExt X
    letI : Linear k X.Modules := schemeModulesLinearOver pi
    ∀ (M : X.Modules), schemeModuleLocallyRankOne M →
      ∀ (s : M.val.obj (op ⊤)), s ≠ 0 →
        (∃ hphi : (ShortComplex.cokernelSequence (schemeModuleTopSectionHom M s)).ShortExact,
          (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hphi).postcomp
            (show X.Modules from SheafOfModules.unit X.ringCatSheaf) (zero_add 1) ≠ 0) →
        (Module.Finite k (schemeModuleCohomology X
            (SheafOfModules.unit X.ringCatSheaf) 1) ∧
          Module.finrank k (schemeModuleCohomology X
            (SheafOfModules.unit X.ringCatSheaf) 1) = 1) →
        Subsingleton (schemeModuleCohomology X M 1) := by
  dsimp only
  let X := hypersurface p hp
  let pi := hypersurfaceToBase p hp
  letI hNativeExt : HasExt.{u} X.Modules := schemeModules_hasExt X
  letI : Linear k X.Modules := schemeModulesLinearOver pi
  letI hNativePlaneIntegral : IsIntegral (scheme (equationIdeal p hp)) :=
    (show IsIntegral X from inferInstance)
  intro M hM s hs hBoundaryData hUnitData
  have hQuotientOne := @positiveEulerSection_nativeQuotientHOneCut001.{u}
    k hField p hp hp0 hSmooth hNativePlaneIntegral M hM s hs
  exact @positiveEulerSection_nativeHOneConsumerCut001.{u}
    k hField X hNativeExt pi M (schemeModuleTopSectionHom M s)
    hBoundaryData hUnitData hQuotientOne

/-- Abstract whole-function application: no concrete original M/section is
beta-specialized outside this symbolic Fin3 field/equation context. -/
theorem positiveEulerSection_nativePlaneWholePropertyCut001
    {k : Type u} [hField : Field k]
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    [hIntegral : IsIntegral (hypersurface p hp)] :
    let X := hypersurface p hp
    let pi := hypersurfaceToBase p hp
    letI : HasExt.{u} X.Modules := schemeModules_hasExt X
    letI : Linear k X.Modules := schemeModulesLinearOver pi
    (∀ (M : X.Modules), schemeModuleLocallyRankOne M →
      ∀ (s : M.val.obj (op ⊤)), s ≠ 0 →
        0 < (Module.finrank k (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
          Module.finrank k (schemeModuleCohomology X M 1) →
        ∃ hphi : (ShortComplex.cokernelSequence (schemeModuleTopSectionHom M s)).ShortExact,
          (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hphi).postcomp
            (show X.Modules from SheafOfModules.unit X.ringCatSheaf) (zero_add 1) ≠ 0) →
    (Module.Finite k (schemeModuleCohomology X
        (SheafOfModules.unit X.ringCatSheaf) 1) ∧
      Module.finrank k (schemeModuleCohomology X
        (SheafOfModules.unit X.ringCatSheaf) 1) = 1) →
    ∀ (M : X.Modules), schemeModuleLocallyRankOne M →
      ∀ (s : M.val.obj (op ⊤)), s ≠ 0 →
        0 < (Module.finrank k (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
          Module.finrank k (schemeModuleCohomology X M 1) →
        Subsingleton (schemeModuleCohomology X M 1) := by
  dsimp only
  let X := hypersurface p hp
  let pi := hypersurfaceToBase p hp
  letI : HasExt.{u} X.Modules := schemeModules_hasExt X
  letI : Linear k X.Modules := schemeModulesLinearOver pi
  intro hBoundaryFamily hUnitData M hM s hs hEuler
  exact @positiveEulerSection_nativePlaneWholeHOneCut001.{u}
    k hField p hp hp0 hSmooth hIntegral M hM s hs
    (hBoundaryFamily M hM s hs hEuler) hUnitData


end PfaffianDescent.Coray
