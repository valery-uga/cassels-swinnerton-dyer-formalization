import PfaffianDescent.AmbientPointKoszulBiproductStalk

/-! # The actual final point Koszul stalk map in native structure-ring coordinates -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization MvPolynomial

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K

local instance ambientPointKoszul_unitPointIdeal_prime (x : Proj PS) :
    (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero twist trivialization is the canonical degree-zero inclusion. -/
theorem ambientPointKoszul_localTrivialization_zero
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl)
    (r : AtPrime PS (pointIdeal PS x)) :
    localTrivialization PS (pointIdeal PS x) ⟨X j, isHomogeneous_X K j⟩ hx 0 r =
      atPrimeToZeroTwistStalk PS (pointIdeal PS x) r := by
  apply Subtype.ext
  change r.val * Localization.mk 1
      ⟨((degreeOnePower PS ⟨X j, isHomogeneous_X K j⟩ 0 : PS 0) : MvPolynomial (Fin 4) K), _⟩ = r.val
  simp [degreeOnePower]

/-- The actual unit-module stalk in the native homogeneous local ring,
using the structure-ring stalk comparison and native `Proj.stalkIso'`. -/
def ambientPointKoszul_unitStalkCoordinate (x : Proj PS) :
    (↑((schemeModuleStalkFunctor (Proj PS) x).obj
        (SheafOfModules.unit (Proj PS).ringCatSheaf)) : Type u) ≃+
      AtPrime PS (pointIdeal PS x) :=
  (presheafOfModules_unitStalkAddEquiv (Proj PS).presheaf x).symm.trans
    (Proj.stalkIso' PS x).toAddEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The native structure-ring coordinate agrees with the zero-twist
coordinate under the actual unit-to-zero-twist isomorphism. -/
theorem ambientPointKoszul_unitStalkCoordinate_compat
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj
      (SheafOfModules.unit (Proj PS).ringCatSheaf)) :
    ambientPointKoszul_stalkCoordinate K j x hx 0
      ((schemeModuleStalkFunctor (Proj PS) x).map (unitIsoZeroTwist PS).hom z) =
    ambientPointKoszul_unitStalkCoordinate K x z := by
  obtain ⟨a, rfl⟩ := (presheafOfModules_unitStalkAddEquiv (Proj PS).presheaf x).surjective z
  let t := localTrivialization PS (pointIdeal PS x) ⟨X j, isHomogeneous_X K j⟩ hx 0
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
    (ambientPointKoszul_localTrivialization_zero K j x hx _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual final sheaf differential into the unit sheaf is the explicit
last Koszul matrix in native `Proj` structure-ring stalk coordinates. -/
theorem ambientPointKoszul_last_unit_stalk_coordinates
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj
      (⨁ pointGlobalTraceP3CoordinateTriple K 1)) :
    ambientPointKoszul_unitStalkCoordinate K x
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3CoordinateKoszulLast K) z) =
    threeGeneratorLast
      (ambientPointKoszul_stalkParameter K 1 j x hx)
      (ambientPointKoszul_stalkParameter K 2 j x hx)
      (ambientPointKoszul_stalkParameter K 3 j x hx)
      (ambientPointKoszul_stalkTripleCoordinate K j x hx 1 z) := by
  rw [← ambientPointKoszul_unitStalkCoordinate_compat K j x hx]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rw [pointGlobalTraceP3CoordinateKoszulLast, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  exact ambientPointKoszul_last_stalk_coordinates K j x hx z

end PfaffianDescent.ProjectiveNegativeTwist
