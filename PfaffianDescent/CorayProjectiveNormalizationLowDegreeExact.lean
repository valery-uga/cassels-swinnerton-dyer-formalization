import PfaffianDescent.CorayGenericNormalizationLowDegreeExact
import PfaffianDescent.CorayGlobalSectionsChosenAffineDefect
import PfaffianDescent.SheafModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.AlgebraicGeometry.Noetherian

/-! Primitive original-equation Coray caller for actual normalization LES.
Infrastructure, support and affine choice are constructed from the literal
projective intersection. The target is the actual pushforward Ext group;
no normalization-cohomology comparison or genus formula is asserted.
STATUS: UNVERIFIED SOURCE ONLY. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- For the literal smooth-cubic/projective-intersection inputs, the ACTUAL
normalization inclusion induces a surjection on Ext¹ from the structure
module, and its kernel is the ACTUAL connecting image from Hom(O_X,Q).
No support, affine choice, QC, Ext vanishing, Noetherianity, HasExt, Mono,
short-exactness, exactness, or comparison certificate is supplied. -/
theorem projectiveIntersection_genericNormalization_cohomologyOne_surjective_and_kernel
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
      integralGenericPointMap_quasiCompact X
    Function.Surjective
      (schemeModuleCohomologyMap X (genericNormalizationUnitToPushforwardUnit X) 1) ∧
      (schemeModuleCohomologyMap X (genericNormalizationUnitToPushforwardUnit X) 1).ker =
        (genericNormalizationHomConnecting X).range := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let Q := genericNormalizationQuotientSheaf X
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  letI : LocallyOfFiniteType (toBase I) := inferInstance
  letI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (toBase I)
  obtain ⟨U, _, hsU, _⟩ :=
    projectiveIntersection_genericNormalizationQuotient_exists_affineOpen
      p q hp hp0 n hq hnot (genericPoint X)
  have hclosed : IsClosed (schemeModuleStalkSupport Q) :=
    projectiveIntersection_genericNormalizationQuotient_stalkSupport_isClosed
      p q hp hp0 n hq hnot
  exact
    ⟨genericNormalization_cohomologyOneMap_surjective_of_closedSupport_subset_affine
      X (toBase I) hclosed U.1 U.2 hsU,
      genericNormalization_cohomologyOne_ker_eq_connecting_range X⟩

end PfaffianDescent.Coray
