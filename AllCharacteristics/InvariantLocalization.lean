import AllCharacteristics.InvariantSubalgebraMaps

/-!
# Invariants commute with localization at a fixed denominator

For a finite group, the actual invariant subalgebra of an equivariant
localization is the localization of the original invariant subalgebra.
The proof uses invariant numerators and invariant inverses. It retains
zero divisors and imposes no restriction on the characteristic.
-/

namespace AllCharacteristics
universe u v
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B]
variable (G : Type v) [Group G] [Finite G]
variable [MulSemiringAction G A] [MulSemiringAction G B]
variable [SMulCommClass G R A] [SMulCommClass G R B] [SMulDistribClass G A B]
variable (t : FixedPoints.subalgebra R A G) [IsLocalization.Away t.val B]

/-- The invariant subalgebra of the localization is itself the localization
of the original invariant subalgebra at the same fixed denominator. -/
theorem isLocalizationAway_fixedSubalgebra :
    letI := equivariantFixedSubalgebraAlgebra R A B G
    IsLocalization.Away t (FixedPoints.subalgebra R B G) := by
  let := equivariantFixedSubalgebraAlgebra R A B G
  apply IsLocalization.Away.mk t
  · apply (isUnit_fixedSubalgebra_iff R B G _).mpr
    change IsUnit (algebraMap A B t.val)
    exact IsLocalization.Away.algebraMap_isUnit t.val
  · intro b
    obtain ⟨n, a, ha, h⟩ := exists_invariant_localization_numerator G t.val t.property b.val b.property
    refine ⟨n, ⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    exact h
  · intro a b h
    have he : algebraMap A B a.val = algebraMap A B b.val := congrArg Subtype.val h
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq t.val he
    exact ⟨n, Subtype.ext hn⟩

/-- The canonical algebra isomorphism comparing localization of invariants
with invariants of the actual localization. -/
noncomputable def invariantLocalizationAlgEquiv :
    letI := equivariantFixedSubalgebraAlgebra R A B G
    Localization.Away t ≃ₐ[FixedPoints.subalgebra R A G] FixedPoints.subalgebra R B G := by
  let := equivariantFixedSubalgebraAlgebra R A B G
  have : IsLocalization.Away t (FixedPoints.subalgebra R B G) :=
    isLocalizationAway_fixedSubalgebra R A B G t
  exact IsLocalization.algEquiv (Submonoid.powers t) _ _

/-- The localization comparison preserves every original invariant coefficient. -/
theorem invariantLocalizationAlgEquiv_algebraMap (a : FixedPoints.subalgebra R A G) :
    letI := equivariantFixedSubalgebraAlgebra R A B G
    invariantLocalizationAlgEquiv R A B G t
      (algebraMap (FixedPoints.subalgebra R A G) (Localization.Away t) a) =
        equivariantFixedSubalgebraMap R A B G a := by
  let := equivariantFixedSubalgebraAlgebra R A B G
  exact (invariantLocalizationAlgEquiv R A B G t).commutes a

end AllCharacteristics
