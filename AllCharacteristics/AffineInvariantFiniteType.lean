import AllCharacteristics.AffineInvariantQuotient
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finiteness of the invariant coefficient algebra

The Artin--Tate lemma proves finite generation of the actual invariant
subalgebra over a noetherian coefficient ring. Consequently the affine quotient
is noetherian and its structure morphism is locally of finite presentation.
The proof has no condition on the characteristic or on the group order.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable (R A : Type u) [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
variable (G : Type v) [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
variable [Algebra.FiniteType R A]

/-- The invariant subalgebra of a finite group is finitely generated over the
original noetherian coefficient ring. -/
instance finiteType_fixedSubalgebra : Algebra.FiniteType R (FixedPoints.subalgebra R A G) :=
  ⟨fg_of_fg_of_fg R (FixedPoints.subalgebra R A G) A
    (inferInstance : Algebra.FiniteType R A).1
    (inferInstance : Module.Finite (FixedPoints.subalgebra R A G) A).1 Subtype.val_injective⟩

/-- The actual finite-group invariant algebra is noetherian. -/
instance isNoetherianRing_fixedSubalgebra : IsNoetherianRing (FixedPoints.subalgebra R A G) :=
  Algebra.FiniteType.isNoetherianRing R (FixedPoints.subalgebra R A G)

/-- The actual affine quotient scheme is locally noetherian. -/
instance isLocallyNoetherian_affineInvariantQuotient :
    IsLocallyNoetherian (affineInvariantQuotient R A G) := by
  change IsLocallyNoetherian (Spec (.of (FixedPoints.subalgebra R A G)))
  infer_instance

/-- The quotient's original coefficient-ring structure map is locally of finite type. -/
instance locallyOfFiniteType_affineInvariantQuotientToBase :
    LocallyOfFiniteType (affineInvariantQuotientToBase R A G) := by
  change LocallyOfFiniteType (Spec.map
    (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G))))
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType.{u})).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- The quotient's original coefficient-ring structure map is locally of finite presentation. -/
instance locallyOfFinitePresentation_affineInvariantQuotientToBase :
    LocallyOfFinitePresentation (affineInvariantQuotientToBase R A G) := by
  infer_instance

end AllCharacteristics
