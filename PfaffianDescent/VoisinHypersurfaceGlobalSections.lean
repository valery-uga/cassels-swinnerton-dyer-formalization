import PfaffianDescent.VoisinProjectiveCubicCohomology
import PfaffianDescent.VoisinSerreTwistSectionInjection
import PfaffianDescent.VoisinGlobalExtVanishing
import PfaffianDescent.VoisinNegativeTwistGlobalH0

/-!
# Global sections of a projective hypersurface restriction

The canonical restriction sequence for a nonzero homogeneous equation has
left term a negative twist and middle term the structure sheaf. If that
negative twist has vanishing zeroth and first cohomology, restriction is a
bijection on global sections. The result below applies this fact to the
actual cokernel sequence constructed for `Proj`; it does not assume that the
cokernel has already been identified with the structure sheaf of the closed
hypersurface.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u

namespace ProjectiveNegativeTwist

variable {A σ : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Global sections of the ambient structure sheaf map bijectively to those
of the hypersurface cokernel, provided the equation's negative twist has
vanishing `H⁰` and `H¹`. -/
theorem zeroRestrictionSequence_sectionsMap_bijective
    [IsDomain A]
    [HasExt.{u} (Proj 𝒜).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj 𝒜).ringCatSheaf)]
    {d : ℕ} (s : 𝒜 d) (hs : (s : A) ≠ 0)
    [Subsingleton (sheafOfModules 𝒜 d).sections]
    [Subsingleton (schemeModuleCohomology (Proj 𝒜)
      (sheafOfModules 𝒜 d) 1)] :
    Function.Bijective (SheafOfModules.sectionsMap
      (zeroRestrictionSequence 𝒜 s).g) := by
  letI : Subsingleton (zeroRestrictionSequence 𝒜 s).X₁.sections := by
    change Subsingleton (sheafOfModules 𝒜 (0 + d)).sections
    simpa only [zero_add] using
      (inferInstance : Subsingleton (sheafOfModules 𝒜 d).sections)
  letI : Subsingleton (Ext.{u}
      (SheafOfModules.unit (Proj 𝒜).ringCatSheaf)
      (zeroRestrictionSequence 𝒜 s).X₁ 1) := by
    change Subsingleton (schemeModuleCohomology (Proj 𝒜)
      (sheafOfModules 𝒜 (0 + d)) 1)
    simpa only [zero_add] using
      (inferInstance : Subsingleton (schemeModuleCohomology (Proj 𝒜)
        (sheafOfModules 𝒜 d) 1))
  exact sectionsMap_bijective_of_shortExact_of_left_h0_h1_vanish
    (zeroRestrictionSequence 𝒜 s)
    (zeroRestrictionSequence_shortExact 𝒜 s hs)

/-- The degree-three instance used for a cubic surface in projective
three-space. -/
theorem cubicCokernel_sectionsMap_bijective
    [IsDomain A]
    [HasExt.{u} (Proj 𝒜).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj 𝒜).ringCatSheaf)]
    (cubic : 𝒜 3) (hcubic : (cubic : A) ≠ 0)
    [Subsingleton (sheafOfModules 𝒜 3).sections]
    [Subsingleton (schemeModuleCohomology (Proj 𝒜)
      (sheafOfModules 𝒜 3) 1)] :
    Function.Bijective (SheafOfModules.sectionsMap
      (zeroRestrictionSequence 𝒜 cubic).g) :=
  zeroRestrictionSequence_sectionsMap_bijective 𝒜 cubic hcubic

end ProjectiveNegativeTwist

namespace ProjectiveNegativeTwist

open MvPolynomial

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- On projective three-space the `H¹(O(-3))` hypothesis in the cubic
restriction theorem is already proved by the finite Čech resolution.
Only `H⁰(O(-3))=0` remains as an assumption here. -/
theorem p3_cubicCokernel_sectionsMap_bijective_of_negativeH0
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf)]
    (cubic : PS 3) (hcubic : (cubic : MvPolynomial (Fin 4) K) ≠ 0)
    [Subsingleton (sheafOfModules PS 3).sections] :
    Function.Bijective (SheafOfModules.sectionsMap
      (zeroRestrictionSequence PS cubic).g) := by
  letI : Subsingleton (schemeModuleCohomology (Proj PS)
      (sheafOfModules PS 3) 1) :=
    (p3_negativeTwist_cohomology_one_and_two_subsingleton K 3).1
  exact cubicCokernel_sectionsMap_bijective PS cubic hcubic

/-- For a nonzero cubic in four variables, ambient global functions restrict
bijectively to sections of its canonical cokernel sheaf. The needed negative
twist `H⁰` and `H¹` vanishings are both proved for projective three-space. -/
theorem p3_cubicCokernel_sectionsMap_bijective
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf)]
    (cubic : PS 3) (hcubic : (cubic : MvPolynomial (Fin 4) K) ≠ 0) :
    Function.Bijective (SheafOfModules.sectionsMap
      (zeroRestrictionSequence PS cubic).g) := by
  letI : Subsingleton (sheafOfModules PS 3).sections :=
    p3_negativeTwist_sections_subsingleton_of_pos K 3 (by decide)
  exact p3_cubicCokernel_sectionsMap_bijective_of_negativeH0 K cubic hcubic

end ProjectiveNegativeTwist
end PfaffianDescent
