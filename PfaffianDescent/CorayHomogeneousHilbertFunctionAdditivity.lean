import PfaffianDescent.HomogeneousProjection
import AllCharacteristics.HomogeneousProjective
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Lean.Elab.Tactic.Omega

/-!
# Genuine degreewise Hilbert-function union/intersection additivity

Actual relations in the SAME polynomial homogeneous piece and its literal
quotient give rank-nullity. Homogeneous polynomial projection derives sum of
relations internally. Native finite-dimensional lattice additivity then proves
actual quotient Hilbert-function additivity in EVERY degree. No component
slope, eventual Hilbert polynomial or degree-additivity certificate is supplied.
SOURCE ONLY / UNVERIFIED: root owns compiler/audit.
-/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual degree-d polynomial relations of the WHOLE homogeneous ideal. -/
def homogeneousIdealGradeRelations
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (d : ℕ) :
    Submodule K (homogeneousSubmodule (Fin 4) K d) :=
  (I.toIdeal.restrictScalars K).comap (homogeneousSubmodule (Fin 4) K d).subtype

/-- Actual homogeneous coordinate quotient dimension and actual homogeneous
relation dimension sum to the SAME polynomial homogeneous piece dimension. -/
theorem homogeneousCoordinateGrade_finrank_add_relations
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (d : ℕ) :
    finrank K (grading I d) + finrank K (homogeneousIdealGradeRelations I d) =
      finrank K (homogeneousSubmodule (Fin 4) K d) := by
  let f := (Ideal.Quotient.mkₐ K I.toIdeal).toLinearMap.domRestrict
    (homogeneousSubmodule (Fin 4) K d)
  have hrange : LinearMap.range f = grading I d := by
    rw [LinearMap.range_domRestrict]
    rfl
  have hker : LinearMap.ker f = homogeneousIdealGradeRelations I d := by
    ext x
    change Ideal.Quotient.mk I.toIdeal x.1 = 0 ↔ x.1 ∈ I.toIdeal
    exact Ideal.Quotient.eq_zero_iff_mem
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hker] at h
  exact h

/-- Homogeneity DERIVES that every degree-d relation in I+J decomposes into
an actual degree-d I-relation plus an actual degree-d J-relation. -/
theorem homogeneousIdealGradeRelations_sup
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (d : ℕ) :
    homogeneousIdealGradeRelations (I ⊔ J) d =
      homogeneousIdealGradeRelations I d ⊔ homogeneousIdealGradeRelations J d := by
  ext x
  constructor
  · intro hx
    change x.1 ∈ I.toIdeal ⊔ J.toIdeal at hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    have ha' : homogeneousComponent d a ∈ I.toIdeal :=
      homogeneousComponent_mem_of_mem I.isHomogeneous ha d
    have hb' : homogeneousComponent d b ∈ J.toIdeal :=
      homogeneousComponent_mem_of_mem J.isHomogeneous hb d
    refine Submodule.mem_sup.mpr
      ⟨⟨homogeneousComponent d a, homogeneousComponent_mem d a⟩, ha',
        ⟨homogeneousComponent d b, homogeneousComponent_mem d b⟩, hb', ?_⟩
    apply Subtype.ext
    change homogeneousComponent d a + homogeneousComponent d b = x.1
    rw [← map_add, hab, homogeneousComponent_eq_self x.2]
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    change a.1 + b.1 ∈ I.toIdeal ⊔ J.toIdeal
    exact Submodule.add_mem_sup ha hb

private theorem homogeneousIdealGradeRelations_inf
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (d : ℕ) :
    homogeneousIdealGradeRelations (I ⊓ J) d =
      homogeneousIdealGradeRelations I d ⊓ homogeneousIdealGradeRelations J d := by
  ext x
  rfl

/-- For the ACTUAL homogeneous coordinate rings, the union/intersection
Hilbert functions satisfy additivity in EVERY degree. Here I∩J defines the
scheme-theoretic union and I+J the scheme-theoretic intersection. No distinctness,
primality, reducedness or eventual slope/certificate hypothesis is supplied. -/
theorem homogeneousCoordinateGrade_union_intersection_finrank_additivity
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (d : ℕ) :
    finrank K (grading (I ⊓ J) d) + finrank K (grading (I ⊔ J) d) =
      finrank K (grading I d) + finrank K (grading J d) := by
  have hI := homogeneousCoordinateGrade_finrank_add_relations I d
  have hJ := homogeneousCoordinateGrade_finrank_add_relations J d
  have hInf := homogeneousCoordinateGrade_finrank_add_relations (I ⊓ J) d
  have hSup := homogeneousCoordinateGrade_finrank_add_relations (I ⊔ J) d
  have hRelations := Submodule.finrank_sup_add_finrank_inf_eq
    (homogeneousIdealGradeRelations I d) (homogeneousIdealGradeRelations J d)
  rw [← homogeneousIdealGradeRelations_sup, ← homogeneousIdealGradeRelations_inf] at hRelations
  omega

end PfaffianDescent.Coray
