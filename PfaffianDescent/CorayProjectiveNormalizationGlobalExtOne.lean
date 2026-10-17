import PfaffianDescent.CorayGenericNormalizationGlobalExtOne
import PfaffianDescent.CorayGlobalSectionsChosenAffineDefect
import PfaffianDescent.SheafModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.AlgebraicGeometry.Noetherian

/-! Primitive Coray caller for ACTUAL normalization-quotient H¹ vanishing.
Closed support, the affine neighborhood, cover, QC, Ext inputs, and ordinary
Ext/local-Noetherian infrastructure are derived from the original geometry.
This does not prove genus subtraction, Riemann--Roch, or the full descent.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ACTUAL global canonical normalization quotient of the literal
integral projective intersection has vanishing ACTUAL degree-one cohomology.
The original homogeneous equations, smooth cubic, and nonmembership remain
the primitive inputs. No support, affine choice, QC, Ext vanishing, cover,
local Noetherianity, or HasExt certificate is supplied by the caller. -/
theorem projectiveIntersection_genericNormalizationQuotient_cohomology_one_subsingleton
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    Subsingleton (schemeModuleCohomology X (genericNormalizationQuotientSheaf X) 1) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let Q := genericNormalizationQuotientSheaf X
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : LocallyOfFiniteType (toBase I) := inferInstance
  letI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (toBase I)
  obtain ⟨U, _, hsU, _⟩ :=
    projectiveIntersection_genericNormalizationQuotient_exists_affineOpen
      p q hp hp0 n hq hnot (genericPoint X)
  have hclosed : IsClosed (schemeModuleStalkSupport Q) :=
    projectiveIntersection_genericNormalizationQuotient_stalkSupport_isClosed
      p q hp hp0 n hq hnot
  exact genericNormalizationQuotientSheaf_cohomology_one_subsingleton_of_closedSupport_subset_affine
    X (toBase I) hclosed U.1 U.2 hsU

end PfaffianDescent.Coray
