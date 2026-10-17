import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeAffineMatrix
import PfaffianDescent.CubicFullJetEvaluationMatrix
import Mathlib.RingTheory.Localization.Away.Basic

/-! # The actual rank-six determinant localization

A surjective specialization of the native relative evaluation matrix selects
its six-column minor internally.  That minor is a nonzero regular function,
and localization gives an actual invertible pivot while preserving the
witness field point.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u v
set_option backward.isDefEq.respectTransparency false

/-- A field-valued rank witness internally selects a nonzero relative minor. -/
theorem serreRelativeEvaluation_exists_nonzero_minor
    {R : Type u} [CommRing R] {F : Type v} [Field F]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix ι κ R) (f : R →+* F)
    (hsurj : Function.Surjective (Matrix.toLin' (M.map f))) :
    ∃ m : ι ↪ κ, (M.submatrix id m).det ≠ 0 ∧
      IsUnit (f (M.submatrix id m).det) := by
  obtain ⟨m, hm⟩ := exists_unit_columnMinor_of_surjective (M.map f) hsurj
  have hm' : IsUnit (f (M.submatrix id m).det) := by
    rw [RingHom.map_det]
    exact hm
  refine ⟨m, ?_, hm'⟩
  intro hz
  exact hm'.ne_zero (by rw [hz, map_zero])

/-- The selected determinant makes the actual pivot invertible over its
literal localization ring. -/
theorem serreRelativeEvaluation_minor_isUnit_on_localization
    {R : Type u} [CommRing R]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι κ R) (m : ι ↪ κ) :
    IsUnit ((M.submatrix id m).map
      (algebraMap R (Localization.Away (M.submatrix id m).det))).det := by
  change IsUnit ((algebraMap R (Localization.Away (M.submatrix id m).det)).mapMatrix
    (M.submatrix id m)).det
  rw [← RingHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit (M.submatrix id m).det

/-- The actual native Serre matrix selects the relative six-column minor
from surjectivity at the actual marked field-valued configuration. -/
theorem serreIncidenceNativeAffineEvaluationMatrix_exists_nonzero_minor
    {F L : Type u} [Field F] [Field L] {X A : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of F)) (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : Module.finrank F
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (chart : Fin 3 → C.ι) (markedA : ∀ i, A ⟶ (C.U (chart i)).toScheme)
    (b : Spec (.of L) ⟶ A)
    (hsurj : Function.Surjective (Matrix.toLin'
      ((serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart markedA).map
        (fieldPointΓevaluation b)))) :
    ∃ m : (Fin 3 × ULift.{u} (Fin 2)) ↪ Fin 9,
      ((serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart markedA).submatrix id m).det ≠ 0 ∧
      IsUnit (fieldPointΓevaluation b
        ((serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart markedA).submatrix id m).det) :=
  serreRelativeEvaluation_exists_nonzero_minor _ _ hsurj

end PfaffianDescent
