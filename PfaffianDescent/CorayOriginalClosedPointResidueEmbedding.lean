import AllCharacteristics.ClosedPointAlgebra
import AllCharacteristics.HomogeneousProjective
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! A K-algebra embedding of the SAME original closed-point residue field
into the given algebraically closed K-field. Actual pointAlgebra actions. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual residue field of a closed point on a finite-type K-scheme
embeds over K into the given algebraically closed extension. Finiteness is
derived from the original point and structure morphism; no embedding input. -/
theorem originalClosedPoint_exists_residueAlgEmbedding
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (P : closedPoints X) :
    letI := pointAlgebra f P.1
    ∃ psi : X.residueField P.1 →ₐ[K] Ω, Function.Injective psi := by
  letI := pointAlgebra f P.1
  letI : Module.Finite K (X.residueField P.1) := closedPoint_moduleFinite f P
  letI : Algebra.IsAlgebraic K (X.residueField P.1) :=
    Algebra.IsAlgebraic.of_finite K (X.residueField P.1)
  let psi : X.residueField P.1 →ₐ[K] Ω := IsAlgClosed.lift
  exact ⟨psi, psi.injective⟩

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Finite projective coordinates internally give finite type for the SAME
original homogeneous quotient. The SAME original P therefore has a genuine
K-residue embedding into Ω; no primality, relevance, characteristic, model,
incidence positivity, degree or component-count hypothesis is required. -/
theorem originalProjectiveClosedPoint_exists_residueAlgEmbedding
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (P : closedPoints (scheme I)) :
    letI := pointAlgebra (toBase I) P.1
    ∃ psi : (scheme I).residueField P.1 →ₐ[K] Ω, Function.Injective psi := by
  letI : LocallyOfFiniteType (toBase I) := (isProper_toBase I).toLocallyOfFiniteType
  exact originalClosedPoint_exists_residueAlgEmbedding (toBase I) P

end PfaffianDescent.Coray
