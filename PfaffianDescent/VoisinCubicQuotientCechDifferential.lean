import PfaffianDescent.SmallCoverSectionRepresenterCechDifferential
import PfaffianDescent.VoisinQuotientCechExtComparison

/-!
# Differential comparison for the cubic-surface coordinate cover

The general small-cover theorem is instantiated for the four coordinate
opens of a homogeneous quotient.  The categorical and universe-lift
calculation is performed abstractly, so this specialization stays within the
default elaboration limit without unfolding the quotient coordinate ring.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K]

local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The termwise Yoneda equivalence for the four quotient-coordinate opens,
expressed using the generic small-cover construction. -/
noncomputable def cubicQuotientSectionRepresenterCechHomEquiv
    (I : HomogeneousIdeal PS) (m n : ℕ) :
    ((quotientSectionRepresenterCechChain I).X n ⟶
        sheafOfModules (grading I) m) ≃
      (quotientNegativeTwistCechComplex I m).X n :=
  smallCoverSectionHomEquiv (Proj (grading I)).ringCatSheaf
    (quotientCoordinateOpen I) (sheafOfModules (grading I) m) n

/-- Evaluation of the cubic-quotient Yoneda equivalence at an ordered
coordinate intersection. -/
lemma cubicQuotientSectionRepresenterCechHomEquiv_apply
    (I : HomogeneousIdeal PS) (m n : ℕ)
    (h : (quotientSectionRepresenterCechChain I).X n ⟶
      sheafOfModules (grading I) m)
    (f : Fin (n + 1) → Fin 4) :
    smallCoverCechTermEquivPi (Proj (grading I)).ringCatSheaf
        (quotientCoordinateOpen I) (sheafOfModules (grading I) m) n
        (cubicQuotientSectionRepresenterCechHomEquiv K I m n h) f =
      sectionRepresenterCechHomEquivPi
        (Proj (grading I)).ringCatSheaf
        (fun j : ULift.{u} (Fin 4) => quotientCoordinateOpen I j.down)
        (sheafOfModules (grading I) m) n h
        (fun j => ULift.up (f j)) :=
  smallCoverSectionHomEquiv_apply (Proj (grading I)).ringCatSheaf
    (quotientCoordinateOpen I) (sheafOfModules (grading I) m) n h f

/-- The termwise cubic-quotient Yoneda equivalence intertwines the
section-representer boundary and the raw Cech differential. -/
lemma cubicQuotientSectionRepresenterCechHomEquiv_d
    (I : HomogeneousIdeal PS) (m n : ℕ)
    (h : (quotientSectionRepresenterCechChain I).X n ⟶
      sheafOfModules (grading I) m) :
    cubicQuotientSectionRepresenterCechHomEquiv K I m (n + 1)
        ((quotientSectionRepresenterCechChain I).d (n + 1) n ≫ h) =
      (quotientNegativeTwistCechComplex I m).d n (n + 1)
        (cubicQuotientSectionRepresenterCechHomEquiv K I m n h) :=
  smallCoverSectionHomEquiv_d (Proj (grading I)).ringCatSheaf
    (quotientCoordinateOpen I) (sheafOfModules (grading I) m) n h

end PfaffianDescent.ProjectiveNegativeTwist
