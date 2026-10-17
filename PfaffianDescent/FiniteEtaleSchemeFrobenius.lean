import PfaffianDescent.FiniteSchemeAlgebra
import PfaffianDescent.ReducedFiniteAlgebraFrobenius
import PfaffianDescent.TraceFrobenius
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Frobenius functionals on finite étale schemes

For a finite étale scheme over a characteristic-zero field, the coefficient
algebra is finite étale and hence reduced.  Its trace functional therefore
gives the nondegenerate multiplication pairing needed for residual lengths.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory Module

universe u

variable {K : Type u} [Field K] [CharZero K]
variable {X : Scheme.{u}}

/-- A finite scheme over a characteristic-zero field is étale when its
coefficient algebra is reduced.  This lifts the corresponding finite-algebra
criterion to the scheme-theoretic complete intersections used below. -/
theorem finiteScheme_etale_of_reduced
    (f : X ⟶ Spec (.of K)) [IsFinite f] [IsReduced Γ(X, ⊤)] :
    Etale f := by
  letI : IsAffine X := isAffine_of_isAffineHom f
  letI := finiteSchemeCoefficientAlgebra f
  have hfinite := finiteSchemeCoefficient_finite f
  haveI : Algebra.Etale K Γ(X, ⊤) := reduced_finite_algebra_etale
  have hring : (algebraMap K Γ(X, ⊤)).Etale :=
    RingHom.etale_algebraMap.mpr inferInstance
  have hspec : Etale
      (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hring
  rw [finiteSchemeCoefficient_spec f] at hspec
  letI : Etale (X.isoSpec.inv ≫ f) := hspec
  letI : Etale X.isoSpec.hom := inferInstance
  have hcomp : Etale (X.isoSpec.hom ≫ (X.isoSpec.inv ≫ f)) := inferInstance
  simpa only [← Category.assoc, X.isoSpec.hom_inv_id, Category.id_comp] using hcomp

/-- A finite reduced scheme over a characteristic-zero field is étale.
This is the scheme-level form of `finiteScheme_etale_of_reduced`, matching
the reduced complete intersections produced by the geometric argument. -/
theorem finiteScheme_etale_of_isReduced
    (f : X ⟶ Spec (.of K)) [IsFinite f] [AlgebraicGeometry.IsReduced X] :
    Etale f := by
  exact finiteScheme_etale_of_reduced f

/-- The coordinate algebra of a finite étale scheme over a
characteristic-zero field admits a Frobenius functional. -/
theorem finiteEtaleScheme_exists_frobeniusFunctional
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] :
    letI := finiteSchemeCoefficientAlgebra f
    ∃ ell : Module.Dual K Γ(X, ⊤), IsFrobeniusFunctional ell := by
  letI : IsAffine X := isAffine_of_isAffineHom f
  letI := finiteSchemeCoefficientAlgebra f
  have hfinite := finiteSchemeCoefficient_finite f
  have hspec : Etale
      (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))) := by
    rw [finiteSchemeCoefficient_spec f]
    infer_instance
  have hring : (algebraMap K Γ(X, ⊤)).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp hspec
  haveI : Algebra.Etale K Γ(X, ⊤) := RingHom.etale_algebraMap.mp hring
  haveI : IsReduced Γ(X, ⊤) :=
    Algebra.FormallyUnramified.isReduced_of_field K Γ(X, ⊤)
  exact reducedFiniteAlgebra_exists_frobeniusFunctional

omit [CharZero K] in
/-- The coordinate algebra of a finite étale scheme is a finite étale
algebra over the ground field. -/
theorem finiteEtaleScheme_coordinateAlgebra_etale
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] :
    letI := finiteSchemeCoefficientAlgebra f
    Algebra.Etale K Γ(X, ⊤) := by
  letI : IsAffine X := isAffine_of_isAffineHom f
  letI := finiteSchemeCoefficientAlgebra f
  have hspec : Etale
      (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))) := by
    rw [finiteSchemeCoefficient_spec f]
    infer_instance
  have hring : (algebraMap K Γ(X, ⊤)).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp hspec
  exact RingHom.etale_algebraMap.mp hring

omit [CharZero K] in
/-- The algebra trace pairing on the coordinate algebra of a finite étale
scheme is nondegenerate.  Unlike the existential Frobenius-functional
statement above, this fixes the functional to be the canonical algebra
trace, as required by the residue formula in the Serre-duality comparison. -/
theorem finiteEtaleScheme_traceForm_nondegenerate
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] :
    letI := finiteSchemeCoefficientAlgebra f
    (Algebra.traceForm K Γ(X, ⊤)).Nondegenerate := by
  letI : IsAffine X := isAffine_of_isAffineHom f
  letI := finiteSchemeCoefficientAlgebra f
  have hfinite := finiteSchemeCoefficient_finite f
  haveI : Algebra.Etale K Γ(X, ⊤) :=
    finiteEtaleScheme_coordinateAlgebra_etale f
  exact traceForm_etale_nondegenerate

end PfaffianDescent
