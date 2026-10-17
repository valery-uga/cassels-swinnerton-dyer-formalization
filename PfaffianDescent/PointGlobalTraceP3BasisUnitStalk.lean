import PfaffianDescent.PointGlobalTraceP3BasisBiproductStalk
import PfaffianDescent.AmbientPointKoszulUnitStalk

/-! # The actual final degree-one Koszul map in native unit-stalk coordinates

The actual unit-stalk coordinate is independent of the chosen basis. The
original final matrix agrees with the three-generator matrix in the same
native ring coordinate used by the closed-point restriction map.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization MvPolynomial

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K
variable (f : Fin 4 → homogeneousSubmodule (Fin 4) K 1)

local instance pointGlobalTraceP3Basis_unitPointIdeal_prime (x : Proj PS) :
    (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero twist trivialization is the canonical degree-zero inclusion. -/
theorem pointGlobalTraceP3Basis_localTrivialization_zero
    (j : Fin 4) (x : Proj PS) (hx : (f j).val ∈ (pointIdeal PS x).primeCompl)
    (r : AtPrime PS (pointIdeal PS x)) :
    localTrivialization PS (pointIdeal PS x) (f j) hx 0 r =
      atPrimeToZeroTwistStalk PS (pointIdeal PS x) r := by
  apply Subtype.ext
  change r.val * Localization.mk 1
      ⟨((degreeOnePower PS (f j) 0 : PS 0) : MvPolynomial (Fin 4) K), _⟩ = r.val
  simp [degreeOnePower]

set_option backward.isDefEq.respectTransparency false in
/-- The native structure-ring coordinate agrees with the zero-twist
coordinate under the actual unit-to-zero-twist isomorphism. -/
theorem pointGlobalTraceP3Basis_unitStalkCoordinate_compat
    (j : Fin 4) (x : Proj PS) (hx : (f j).val ∈ (pointIdeal PS x).primeCompl)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj
      (SheafOfModules.unit (Proj PS).ringCatSheaf)) :
    pointGlobalTraceP3Basis_stalkCoordinate K f j x hx 0
      ((schemeModuleStalkFunctor (Proj PS) x).map (unitIsoZeroTwist PS).hom z) =
    ambientPointKoszul_unitStalkCoordinate K x z := by
  obtain ⟨a, rfl⟩ := (presheafOfModules_unitStalkAddEquiv (Proj PS).presheaf x).surjective z
  let t := localTrivialization PS (pointIdeal PS x) (f j) hx 0
  have hr : ambientPointKoszul_unitStalkCoordinate K x
      ((presheafOfModules_unitStalkAddEquiv (Proj PS).presheaf x) a) = Proj.stalkIso' PS x a :=
    congrArg (Proj.stalkIso' PS x)
      ((presheafOfModules_unitStalkAddEquiv (Proj PS).presheaf x).symm_apply_apply a)
  rw [hr]
  change t.symm (stalkToFractionModule PS 0 x
      ((schemeModuleStalkFunctor (Proj PS) x).map (unitToZeroTwist PS)
        ((presheafOfModules_unitStalkLinearEquiv (Proj PS).presheaf x) a))) =
    Proj.stalkIso' PS x a
  apply t.symm_apply_eq.mpr
  exact (unitToZeroTwist_stalkMap_compat PS x a).trans
    (pointGlobalTraceP3Basis_localTrivialization_zero K f j x hx _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual final sheaf differential into the unit sheaf is the explicit
last Koszul matrix in native `Proj` structure-ring stalk coordinates. -/
theorem pointGlobalTraceP3Basis_last_unit_stalk_coordinates
    (j : Fin 4) (x : Proj PS) (hx : (f j).val ∈ (pointIdeal PS x).primeCompl)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj
      (⨁ pointGlobalTraceP3CoordinateTriple K 1)) :
    ambientPointKoszul_unitStalkCoordinate K x
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3BasisKoszulLast K f) z) =
    threeGeneratorLast
      (pointGlobalTraceP3Basis_stalkParameter K f 1 j x hx)
      (pointGlobalTraceP3Basis_stalkParameter K f 2 j x hx)
      (pointGlobalTraceP3Basis_stalkParameter K f 3 j x hx)
      (pointGlobalTraceP3Basis_stalkTripleCoordinate K f j x hx 1 z) := by
  rw [← pointGlobalTraceP3Basis_unitStalkCoordinate_compat K f j x hx]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rw [pointGlobalTraceP3BasisKoszulLast, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  exact pointGlobalTraceP3Basis_last_stalk_coordinates K f j x hx z

end PfaffianDescent.ProjectiveNegativeTwist
