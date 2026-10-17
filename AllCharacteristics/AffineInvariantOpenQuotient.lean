import AllCharacteristics.AffineInvariantOpenDescent
import Mathlib.AlgebraicGeometry.Restrict

/-!
# The actual quotient morphism on an invariant open

The restricted quotient is constructed as a morphism of schemes. Its square
with the original affine quotient is Cartesian, so integrality, surjectivity,
and the finite and proper properties pass to the restricted quotient.
-/

open AlgebraicGeometry CategoryTheory
open scoped Pointwise
namespace AllCharacteristics
universe u v
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (G : Type v) [Group G] [Finite G]
variable [MulSemiringAction G A] [SMulCommClass G R A]
variable (U : (Spec (.of A)).Opens)
variable (hU : ∀ (p q : PrimeSpectrum A) (g : G),
  q.asIdeal = g • p.asIdeal → p ∈ U → q ∈ U)

/-- The actual quotient map from a stable open to its descended quotient open. -/
noncomputable def affineInvariantOpenQuotientMap :
    U.toScheme ⟶ (affineInvariantQuotientOpen R A G U hU).toScheme :=
  IsOpenImmersion.lift (affineInvariantQuotientOpen R A G U hU).ι
    (U.ι ≫ affineInvariantQuotientMap R A G) (by
      rintro y ⟨x, rfl⟩
      exact ⟨⟨affineInvariantQuotientMap R A G x.val, ⟨x.val, x.property, rfl⟩⟩, rfl⟩)

/-- The restricted quotient morphism commutes with both actual open inclusions. -/
theorem affineInvariantOpenQuotientMap_ι :
    affineInvariantOpenQuotientMap R A G U hU ≫
      (affineInvariantQuotientOpen R A G U hU).ι = U.ι ≫ affineInvariantQuotientMap R A G := by
  exact IsOpenImmersion.lift_fac _ _ _

/-- Restriction to a stable open is the full base change of the affine quotient map. -/
theorem isPullback_affineInvariantOpenQuotientMap :
    IsPullback (affineInvariantOpenQuotientMap R A G U hU) U.ι
      (affineInvariantQuotientOpen R A G U hU).ι (affineInvariantQuotientMap R A G) := by
  apply IsOpenImmersion.isPullback
  · exact (affineInvariantOpenQuotientMap_ι R A G U hU).symm
  · simpa only [Scheme.Opens.opensRange_ι] using affineInvariantQuotientOpen_preimage R A G U hU

/-- The quotient of a stable open is integral. -/
instance isIntegralHom_affineInvariantOpenQuotientMap :
    IsIntegralHom (affineInvariantOpenQuotientMap R A G U hU) :=
  MorphismProperty.of_isPullback (P := @IsIntegralHom.{u})
    (isPullback_affineInvariantOpenQuotientMap R A G U hU).flip inferInstance

/-- Every point of the descended quotient open has a point above it in the original open. -/
instance surjective_affineInvariantOpenQuotientMap :
    Surjective (affineInvariantOpenQuotientMap R A G U hU) :=
  MorphismProperty.of_isPullback (P := @Surjective.{u})
    (isPullback_affineInvariantOpenQuotientMap R A G U hU).flip inferInstance

/-- For an algebra of finite type the quotient morphism of a stable open is finite. -/
instance isFinite_affineInvariantOpenQuotientMap [Algebra.FiniteType R A] :
    IsFinite (affineInvariantOpenQuotientMap R A G U hU) :=
  MorphismProperty.of_isPullback (P := @IsFinite.{u})
    (isPullback_affineInvariantOpenQuotientMap R A G U hU).flip inferInstance

/-- For an algebra of finite type the quotient morphism of a stable open is proper. -/
instance isProper_affineInvariantOpenQuotientMap [Algebra.FiniteType R A] :
    IsProper (affineInvariantOpenQuotientMap R A G U hU) := by
  infer_instance

end AllCharacteristics
