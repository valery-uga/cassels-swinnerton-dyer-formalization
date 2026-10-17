import PfaffianDescent.LocalExtResidueInjective
import PfaffianDescent.TraceFrobenius
import PfaffianDescent.FiniteEtaleSchemeFrobenius

/-!
# Trace duality for the finite-support Ext endpoint

The local complete-intersection calculation identifies the relevant
degree-two Ext group with residue coordinates on a finite zero-scheme.
For a finite etale coordinate algebra, the trace pairing then turns those
coordinates into the dual of the scheme's global functions.

This file records that last composition independently of the geometric
proof that a particular global Ext group has the required residue-coordinate
equivalence.  Consequently the remaining quotient-side obligation is a
literal global-to-local Ext comparison, rather than an opaque Serre-duality
hypothesis.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace PfaffianDescent

universe u v w

variable {K A : Type u} {E : Type w} {B : Type v}
  [Field K] [CommRing A] [Algebra K A]
  [FiniteDimensional K A]
  [AddCommGroup E] [AddCommGroup B] [Module K B]

/-- The finite-support duality endpoint in the form used by the paper: once
local residue coordinates have been assembled into the coordinate algebra
`A = Γ(Z, O_Z)`, the trace pairing identifies the Ext group with
`Dual_K Γ(Z, O_Z)` directly. -/
noncomputable def finiteSupportExtCoordinateTraceDualAddEquiv
    (localResidueEquiv : E ≃+ B)
    (residueToCoordinate : B ≃ₗ[K] A)
    (htrace : (Algebra.traceForm K A).Nondegenerate) :
    E ≃+ Module.Dual K A :=
  (localResidueEquiv.trans residueToCoordinate.toAddEquiv).trans
    (finiteAlgebraTraceDualEquiv htrace).toAddEquiv

@[simp]
theorem finiteSupportExtCoordinateTraceDualAddEquiv_apply
    (localResidueEquiv : E ≃+ B)
    (residueToCoordinate : B ≃ₗ[K] A)
    (htrace : (Algebra.traceForm K A).Nondegenerate) (z : E) :
    finiteSupportExtCoordinateTraceDualAddEquiv
        localResidueEquiv residueToCoordinate htrace z =
      finiteAlgebraTraceDualEquiv htrace
        (residueToCoordinate (localResidueEquiv z)) := rfl

theorem finiteSupportExtCoordinateTraceDualAddEquiv_apply_apply
    (localResidueEquiv : E ≃+ B)
    (residueToCoordinate : B ≃ₗ[K] A)
    (htrace : (Algebra.traceForm K A).Nondegenerate) (z : E) (a : A) :
    finiteSupportExtCoordinateTraceDualAddEquiv
        localResidueEquiv residueToCoordinate htrace z a =
      Algebra.trace K A
        (residueToCoordinate (localResidueEquiv z) * a) := by
  rw [finiteSupportExtCoordinateTraceDualAddEquiv_apply,
    finiteAlgebraTraceDualEquiv_apply]

/-- Finite-étale specialization of the coordinate trace-duality endpoint.
The canonical trace form is supplied by the geometry of the finite scheme,
so callers need only identify their local residue coordinates with its
global coordinate algebra. -/
noncomputable def finiteEtaleSupportExtCoordinateTraceDualAddEquiv
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f]
    (localResidueEquiv : E ≃+ B)
    (residueToCoordinate :
      letI := finiteSchemeCoefficientAlgebra f
      B ≃ₗ[K] Γ(X, ⊤)) :
    letI := finiteSchemeCoefficientAlgebra f
    letI : FiniteDimensional K Γ(X, ⊤) :=
      finiteSchemeCoefficient_finite f
    E ≃+ Module.Dual K Γ(X, ⊤) := by
  letI := finiteSchemeCoefficientAlgebra f
  letI : FiniteDimensional K Γ(X, ⊤) :=
    finiteSchemeCoefficient_finite f
  exact finiteSupportExtCoordinateTraceDualAddEquiv
    localResidueEquiv residueToCoordinate
      (finiteEtaleScheme_traceForm_nondegenerate f)

@[simp]
theorem finiteEtaleSupportExtCoordinateTraceDualAddEquiv_apply
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f]
    (localResidueEquiv : E ≃+ B)
    (residueToCoordinate :
      letI := finiteSchemeCoefficientAlgebra f
      B ≃ₗ[K] Γ(X, ⊤)) (z : E) :
    letI := finiteSchemeCoefficientAlgebra f
    letI : FiniteDimensional K Γ(X, ⊤) :=
      finiteSchemeCoefficient_finite f
    finiteEtaleSupportExtCoordinateTraceDualAddEquiv
        f localResidueEquiv residueToCoordinate z =
      finiteAlgebraTraceDualEquiv
          (finiteEtaleScheme_traceForm_nondegenerate f)
        (residueToCoordinate (localResidueEquiv z)) := by
  rfl

theorem finiteEtaleSupportExtCoordinateTraceDualAddEquiv_apply_apply
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f]
    (localResidueEquiv : E ≃+ B)
    (residueToCoordinate :
      letI := finiteSchemeCoefficientAlgebra f
      B ≃ₗ[K] Γ(X, ⊤)) (z : E)
    (a : letI := finiteSchemeCoefficientAlgebra f; Γ(X, ⊤)) :
    letI := finiteSchemeCoefficientAlgebra f
    letI : FiniteDimensional K Γ(X, ⊤) :=
      finiteSchemeCoefficient_finite f
    finiteEtaleSupportExtCoordinateTraceDualAddEquiv
        f localResidueEquiv residueToCoordinate z a =
      Algebra.trace K Γ(X, ⊤)
        (residueToCoordinate (localResidueEquiv z) * a) := by
  letI := finiteSchemeCoefficientAlgebra f
  letI : FiniteDimensional K Γ(X, ⊤) :=
    finiteSchemeCoefficient_finite f
  exact finiteSupportExtCoordinateTraceDualAddEquiv_apply_apply
    localResidueEquiv residueToCoordinate
      (finiteEtaleScheme_traceForm_nondegenerate f) z a

/-- Compose an additive residue-coordinate equivalence, its identification
with a finite coordinate algebra, and the nondegenerate trace pairing. -/
noncomputable def finiteSupportExtTraceDualAddEquiv
    (localResidueEquiv : E ≃+ B)
    (residueToCoordinate : B ≃ₗ[K] A)
    (htrace : (Algebra.traceForm K A).Nondegenerate) :
    let p : Spec (.of A) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K A))
    letI := Module.compHom Γ(Spec (.of A), ⊤)
      (schemeOpenBaseRingHom p ⊤)
    E ≃+ Module.Dual K Γ(Spec (.of A), ⊤) := by
  let p : Spec (.of A) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K A))
  letI := Module.compHom Γ(Spec (.of A), ⊤)
    (schemeOpenBaseRingHom p ⊤)
  exact (localResidueEquiv.trans residueToCoordinate.toAddEquiv).trans
    (finiteAffineGlobalFunctionsTraceDualEquiv htrace).toAddEquiv

@[simp]
theorem finiteSupportExtTraceDualAddEquiv_apply
    (localResidueEquiv : E ≃+ B)
    (residueToCoordinate : B ≃ₗ[K] A)
    (htrace : (Algebra.traceForm K A).Nondegenerate) (z : E) :
    let p : Spec (.of A) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K A))
    letI := Module.compHom Γ(Spec (.of A), ⊤)
      (schemeOpenBaseRingHom p ⊤)
    finiteSupportExtTraceDualAddEquiv
        localResidueEquiv residueToCoordinate htrace z =
      finiteAffineGlobalFunctionsTraceDualEquiv htrace
        (residueToCoordinate (localResidueEquiv z)) := by
  rfl

/-- Evaluation formula for the finite-support trace-duality equivalence.
It makes explicit that a residue coordinate `a` acts on a function `s` by
the algebra trace of `a * s`. -/
theorem finiteSupportExtTraceDualAddEquiv_apply_apply
    (localResidueEquiv : E ≃+ B)
    (residueToCoordinate : B ≃ₗ[K] A)
    (htrace : (Algebra.traceForm K A).Nondegenerate) (z : E) :
    let p : Spec (.of A) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K A))
    letI := Module.compHom Γ(Spec (.of A), ⊤)
      (schemeOpenBaseRingHom p ⊤)
    ∀ s : Γ(Spec (.of A), ⊤),
      finiteSupportExtTraceDualAddEquiv
          localResidueEquiv residueToCoordinate htrace z s =
        Algebra.trace K A
          (residueToCoordinate (localResidueEquiv z) *
            specGlobalFunctionsLinearEquiv K A s) := by
  dsimp
  let p : Spec (.of A) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K A))
  letI := Module.compHom Γ(Spec (.of A), ⊤)
    (schemeOpenBaseRingHom p ⊤)
  intro s
  rw [finiteSupportExtTraceDualAddEquiv_apply]
  exact finiteAffineGlobalFunctionsTraceDualEquiv_apply
    htrace (residueToCoordinate (localResidueEquiv z)) s

end PfaffianDescent
