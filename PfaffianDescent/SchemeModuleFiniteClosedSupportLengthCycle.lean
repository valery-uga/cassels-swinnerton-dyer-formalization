import PfaffianDescent.SchemeModuleFiniteClosedSupportOriginalBaseGerms
import AllCharacteristics.CycleDegreeAssembly

/-! Actual effective cycles from native finite-support module stalk lengths.
This is the small finite-sum companion to the global weighted endpoint.
No finite scheme, Cartier divisor, numerical word degree or section existence
is postulated. Depends on UNVERIFIED weighted006 and generic germ001.
SOURCE ONLY / UNVERIFIED. Root alone compiles. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory AllCharacteristics
open scoped BigOperators
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual finite effective sum with native module-length multiplicities
at the actual closed support points. No frame enters its definition. -/
def schemeModuleFiniteClosedSupportLengthCycle
    (M : X.Modules) (C : Set X) (hC : C.Finite)
    (hclosed : ∀ x ∈ C, IsClosed ({x} : Set X)) : EffectiveZeroCycle X := by
  classical
  letI : Fintype C := hC.fintype
  exact ∑ x : C, Finsupp.single (show closedPoints X from ⟨x.1, hclosed x.1 x.2⟩)
    (Module.length (X.presheaf.stalk x.1) ((schemeModuleStalkModuleFunctor X x.1).obj M)).toNat

/-- Its actual scheme degree is exactly the native-length weighted sum. -/
theorem schemeModuleFiniteClosedSupportLengthCycle_degree
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (C : Set X)
    (hC : C.Finite) (hclosed : ∀ x ∈ C, IsClosed ({x} : Set X)) :
    letI : Fintype C := hC.fintype
    EffectiveZeroCycle.degree pi (schemeModuleFiniteClosedSupportLengthCycle M C hC hclosed) =
      ∑ x : C, (Module.length (X.presheaf.stalk x.1)
        ((schemeModuleStalkModuleFunctor X x.1).obj M)).toNat * pi.residueDegree x.1 := by
  classical
  letI : Fintype C := hC.fintype
  rw [← EffectiveZeroCycle.degreeLinearMap_apply]
  change EffectiveZeroCycle.degreeLinearMap pi
    (∑ x : C, Finsupp.single (show closedPoints X from ⟨x.1, hclosed x.1 x.2⟩)
      (Module.length (X.presheaf.stalk x.1) ((schemeModuleStalkModuleFunctor X x.1).obj M)).toNat) = _
  rw [map_sum]
  simp only [EffectiveZeroCycle.degreeLinearMap, Finsupp.linearCombination_single, smul_eq_mul]

/-- The SAME actual length cycle has degree the dimension of actual original-K
top sections, through the proved germ decomposition and local weighting. -/
theorem schemeModuleFiniteClosedSupportLengthCycle_degree_eq_topSections_finrank
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (M : X.Modules) (C : Set X) (hC : C.Finite)
    (hclosed : ∀ x ∈ C, IsClosed ({x} : Set X))
    (hsupport : schemeModuleStalkSupport M ⊆ C)
    (hlength : ∀ x : C, IsFiniteLength (X.presheaf.stalk x.1)
      ((schemeModuleStalkModuleFunctor X x.1).obj M)) :
    EffectiveZeroCycle.degree pi (schemeModuleFiniteClosedSupportLengthCycle M C hC hclosed) =
      Module.finrank K (SchemeModuleOpenSectionsOver pi M ⊤) := by
  classical
  letI : Fintype C := hC.fintype
  exact (schemeModuleFiniteClosedSupportLengthCycle_degree pi M C hC hclosed).trans
    (schemeModuleOriginalBaseTopSections_finite_and_weighted_finrank
      pi M C hC hclosed hsupport hlength).2.symm

end PfaffianDescent.Coray
