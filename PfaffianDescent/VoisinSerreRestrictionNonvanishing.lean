import PfaffianDescent.SerreExtensionFoundation
import PfaffianDescent.SheafModuleFlasque

/-!
# The restriction-to-cohomology step in Voisin's Serre construction

For the short exact sequence of a finite closed subscheme, a failure of
surjectivity on the concrete restriction of global sections yields the
nonzero first ideal-sheaf cohomology class used by Serre duality.
-/

noncomputable section

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

/-- The exact cohomological consequence of Voisin's strict section-dimension
inequality.  Once the geometric degree-two restriction map is identified
with this map of sections, its nonsurjectivity produces
`H¹(I_Z ⊗ L) ≠ 0` without any further cohomological assumption. -/
theorem closedImmersionIdealTwist_not_cohomology_one_subsingleton_of_sectionsMap_not_surjective
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (L : X.Modules) [HasExt.{u} X.Modules]
    [PreservesFiniteLimits (schemeModuleTensorRight L)]
    [PreservesFiniteColimits (schemeModuleTensorRight L)]
    (hnot : ¬ Function.Surjective (SheafOfModules.sectionsMap
      (closedImmersionIdealTwistSequence i L).g)) :
    ¬ Subsingleton (schemeModuleCohomology X
      (closedImmersionIdealTwist i L) 1) := by
  exact not_schemeModuleCohomology_one_subsingleton_of_sectionsMap_not_surjective
    X (closedImmersionIdealTwistSequence i L)
    (closedImmersionIdealTwistSequence_shortExact i L) hnot

/-- The degree-eleven Serre conclusion after replacing its literal source
and target section spaces by surjective homogeneous and affine-coordinate
parameterizations.  The remaining projective calculation is exactly the two
surjectivity statements and their compatibility with restriction. -/
theorem closedImmersionIdealTwist_not_cohomology_one_subsingleton_of_section_parameterizations
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (L : X.Modules) [HasExt.{u} X.Modules]
    [PreservesFiniteLimits (schemeModuleTensorRight L)]
    [PreservesFiniteColimits (schemeModuleTensorRight L)]
    {V T : Type*}
    (source : V → (closedImmersionIdealTwistSequence i L).X₂.sections)
    (target : (closedImmersionIdealTwistSequence i L).X₃.sections → T)
    (hsource : Function.Surjective source)
    (htarget : Function.Surjective target)
    (restriction : V → T)
    (hcompat : ∀ v, target (SheafOfModules.sectionsMap
      (closedImmersionIdealTwistSequence i L).g (source v)) = restriction v)
    (hnot : ¬ Function.Surjective restriction) :
    ¬ Subsingleton (schemeModuleCohomology X
      (closedImmersionIdealTwist i L) 1) := by
  exact not_schemeModuleCohomology_one_subsingleton_of_section_parameterizations
    X (closedImmersionIdealTwistSequence i L)
    (closedImmersionIdealTwistSequence_shortExact i L)
    source target hsource htarget restriction hcompat hnot

end PfaffianDescent
