import AllCharacteristics.AffineInvariantLocalization

/-!
# Quotient localization with its constructed action

These comparisons start with an action only on the original algebra. The
action on its localization, its compatibility with the coefficient ring,
and the localization of the invariant quotient are constructed internally.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable (G : Type v) [Group G] [Finite G]
variable [MulSemiringAction G A] [SMulCommClass G R A]
variable (t : FixedPoints.subalgebra R A G) [IsLocalization.Away t.val B]

/-- The canonical localization action gives the actual invariant-ring comparison. -/
noncomputable def canonicalInvariantLocalizationEquiv :
    letI := localizedGroupAction A B G t.val t.property
    letI : SMulDistribClass G A B := smulDistribClass_localizedGroupAction A B G t.val t.property
    letI : SMulCommClass G R B := smulCommClass_of_equivariant_algebra_tower R A B G
    Localization.Away t ≃+* FixedPoints.subalgebra R B G := by
  let := localizedGroupAction A B G t.val t.property
  let : SMulDistribClass G A B := smulDistribClass_localizedGroupAction A B G t.val t.property
  let : SMulCommClass G R B := smulCommClass_of_equivariant_algebra_tower R A B G
  let := equivariantFixedSubalgebraAlgebra R A B G
  exact (invariantLocalizationAlgEquiv R A B G t).toRingEquiv

/-- The constructed action makes the invariant localization an actual quotient open. -/
theorem isOpenImmersion_canonicalInvariantLocalization :
    letI := localizedGroupAction A B G t.val t.property
    letI : SMulDistribClass G A B := smulDistribClass_localizedGroupAction A B G t.val t.property
    letI : SMulCommClass G R B := smulCommClass_of_equivariant_algebra_tower R A B G
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (equivariantFixedSubalgebraMap R A B G))) := by
  let := localizedGroupAction A B G t.val t.property
  let : SMulDistribClass G A B := smulDistribClass_localizedGroupAction A B G t.val t.property
  let : SMulCommClass G R B := smulCommClass_of_equivariant_algebra_tower R A B G
  exact isOpenImmersion_affineInvariantLocalization R A B G t

/-- Quotient and localization are Cartesian for the constructed localization action. -/
theorem isPullback_canonicalInvariantLocalization :
    letI := localizedGroupAction A B G t.val t.property
    letI : SMulDistribClass G A B := smulDistribClass_localizedGroupAction A B G t.val t.property
    letI : SMulCommClass G R B := smulCommClass_of_equivariant_algebra_tower R A B G
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (affineInvariantQuotientMap R B G) (affineInvariantQuotientMap R A G)
      (Spec.map (CommRingCat.ofHom (equivariantFixedSubalgebraMap R A B G))) := by
  let := localizedGroupAction A B G t.val t.property
  let : SMulDistribClass G A B := smulDistribClass_localizedGroupAction A B G t.val t.property
  let : SMulCommClass G R B := smulCommClass_of_equivariant_algebra_tower R A B G
  exact isPullback_affineInvariantLocalization R A B G t

end AllCharacteristics
