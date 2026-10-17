import PfaffianDescent.VoisinHypersurfaceActualGlobalSections
import PfaffianDescent.VoisinClosedSubschemeConstantDetection
import PfaffianDescent.VoisinCartierInverseTwist
import PfaffianDescent.VoisinProjectiveThreeGlobalFunctions

/-!
# Constant functions on a smooth cubic from the ambient calculation

The cubic hypersurface restriction theorem transfers the calculation of
global regular functions on projective three-space to the actual cubic
surface. The canonical ambient ground-field map is bijective by the
four-chart Laurent calculation, so the final smooth-cubic results below
have no extra geometric premise.
-/

namespace PfaffianDescent.ProjectiveNegativeTwist

open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

universe u

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- Global functions on a smooth cubic are constant once this is known on
its ambient projective three-space. -/
theorem p3_smoothCubicGlobalFunctions_surjective_of_ambient
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hambient : Function.Surjective
      (affineFunctionHom (ambientToBase (R := K) (σ := Fin 4)))) :
    Function.Surjective (affineFunctionHom (hypersurfaceToBase p hp)) := by
  have hcomp : hypersurfaceToAmbient p hp ≫
      ambientToBase (R := K) (σ := Fin 4) =
      hypersurfaceToBase p hp :=
    quotientProjMap_toBase (equationIdeal p hp)
  rw [← hcomp]
  exact affineFunctionHom_surjective_of_restriction_surjective
    (ambientToBase (R := K) (σ := Fin 4))
    (hypersurfaceToAmbient p hp) hambient
    (p3_smoothCubicGlobalFunctions_restriction_bijective K p hp hp0).2

/-- Every nonempty closed subscheme of a smooth cubic detects its global
functions; consequently its ideal sheaf has no nonzero global section. -/
theorem p3_smoothCubicNonemptyIdeal_sections_subsingleton_of_ambient
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hambient : Function.Surjective
      (affineFunctionHom (ambientToBase (R := K) (σ := Fin 4))))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp)
    [IsClosedImmersion i] [Nonempty Z] :
    Subsingleton (IdealSheafDataModule.closedImmersionModule i).sections := by
  exact closedImmersionModule_sections_subsingleton_of_nonempty_constants
    (hypersurfaceToBase p hp) i
    (p3_smoothCubicGlobalFunctions_surjective_of_ambient K p hp hp0 hambient)

/-- In the Cartier-divisor formulation, the preceding ideal-section
vanishing is exactly `H⁰(O_S(-Z)) = 0`. -/
theorem p3_smoothCubicInverseCartierTwist_sections_subsingleton_of_ambient
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hambient : Function.Surjective
      (affineFunctionHom (ambientToBase (R := K) (σ := Fin 4))))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp)
    [IsClosedImmersion i] [Nonempty Z]
    (H : RegularPrincipalImmersion i) :
    Subsingleton H.inverseCartierTwist.sections := by
  exact p3_smoothCubicNonemptyIdeal_sections_subsingleton_of_ambient
    K p hp hp0 hambient i

/-- Every global regular function on a smooth cubic hypersurface in `P³`
comes from its ground field. -/
theorem p3_smoothCubicGlobalFunctions_surjective
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    Function.Surjective (affineFunctionHom (hypersurfaceToBase p hp)) := by
  exact p3_smoothCubicGlobalFunctions_surjective_of_ambient K p hp hp0
    (ambientToBase_affineFunctionHom_bijective K).2

/-- The ideal sheaf of every nonempty closed subscheme of a smooth cubic
has only its zero global section. -/
theorem p3_smoothCubicNonemptyIdeal_sections_subsingleton
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp)
    [IsClosedImmersion i] [Nonempty Z] :
    Subsingleton (IdealSheafDataModule.closedImmersionModule i).sections := by
  exact p3_smoothCubicNonemptyIdeal_sections_subsingleton_of_ambient
    K p hp hp0 (ambientToBase_affineFunctionHom_bijective K).2 i

/-- For a regular effective Cartier divisor, this is the global-section
vanishing of its inverse twist. -/
theorem p3_smoothCubicInverseCartierTwist_sections_subsingleton
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp)
    [IsClosedImmersion i] [Nonempty Z]
    (H : RegularPrincipalImmersion i) :
    Subsingleton H.inverseCartierTwist.sections := by
  exact p3_smoothCubicInverseCartierTwist_sections_subsingleton_of_ambient
    K p hp hp0 (ambientToBase_affineFunctionHom_bijective K).2 i H

end PfaffianDescent.ProjectiveNegativeTwist
