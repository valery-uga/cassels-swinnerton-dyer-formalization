import PfaffianDescent.VoisinQuotientCechExtComparison

/-!
# A component formula for formal-coproduct Cech differentials

This isolates the categorical calculation from any particular graded ring.
Keeping the cover and presheaf abstract prevents the elaborator from
unfolding a projective quotient while proving the alternating-coface formula.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

namespace PfaffianDescent

universe w v v' u u'

variable {C : Type u} [Category.{v, u} C] [HasFiniteProducts C]
variable {A : Type u'} [Category.{v', u'} A] [Preadditive A] [HasProducts A]
variable {ι : Type w}

/-- Delete one entry from a tuple with arbitrary values. -/
def cechDeleteTuple {n : ℕ} (i : Fin (n + 2))
    (f : Fin (n + 2) → ι) : Fin (n + 1) → ι :=
  fun j => f (i.succAbove j)

/-- The cosimplicial object of presheaf sections on a formal-coproduct
Cech nerve. -/
noncomputable def formalCoproductCechCosimplicial
    (U : ι → C) (P : Cᵒᵖ ⥤ A) : CosimplicialObject A :=
  (FormalCoproduct.cosimplicialObjectFunctor
    (FormalCoproduct.mk _ U).cech).obj P

set_option backward.isDefEq.respectTransparency false in
/-- A component of the raw Cech differential is the alternating sum of
the face restriction maps. -/
lemma formalCoproductCech_objD_comp_π
    (U : ι → C) (P : Cᵒᵖ ⥤ A) (n : ℕ)
    (f : Fin (n + 2) → ι) :
    let E := (FormalCoproduct.mk _ U).cech
    AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (formalCoproductCechCosimplicial U P) n ≫
        Pi.π (fun j : (E.obj (op (SimplexCategory.mk (n + 1)))).I =>
          P.obj (op ((E.obj (op (SimplexCategory.mk (n + 1)))).obj j))) f =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (Pi.π (fun j : (E.obj (op (SimplexCategory.mk n))).I =>
            P.obj (op ((E.obj (op (SimplexCategory.mk n))).obj j)))
          (cechDeleteTuple i f) ≫
        P.map ((E.map (SimplexCategory.δ i).op).φ f).op) := by
  dsimp only
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Preadditive.zsmul_comp]
  apply congrArg ((-1 : ℤ) ^ (i : ℕ) • ·)
  dsimp only [formalCoproductCechCosimplicial, CosimplicialObject.δ,
    FormalCoproduct.cosimplicialObjectFunctor_obj_map]
  exact Pi.lift_π _ f

end PfaffianDescent

