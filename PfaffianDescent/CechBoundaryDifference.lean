import PfaffianDescent.CechExtDegreeTwo

/-! # A boundary witness retaining its actual cochain and equation -/
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u v
structure DegreeTwoBoundaryDifference {A : Type u} [Category.{v} A] [Abelian A]
    (C : ChainComplex A ℕ) (Y : A)
    (z z' : DegreeTwoCocycle (C.d 3 2) (Y := Y)) where
  cochain : C.X 1 ⟶ Y
  differential_comp : C.d 2 1 ≫ cochain = z.1 - z'.1
end PfaffianDescent
