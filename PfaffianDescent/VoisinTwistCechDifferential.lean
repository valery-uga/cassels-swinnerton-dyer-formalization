import PfaffianDescent.VoisinTwistCechAggregate

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial
open CategoryTheory.Limits
open scoped AddMonoidAlgebra BigOperators
universe u
namespace PfaffianDescent.ProjectiveNegativeTwist

open LaurentLocalization AwayCechExact

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The cosimplicial section object underlying the raw Cech complex. -/
noncomputable def p3CechCosimplicial (m : ℕ) :
    CosimplicialObject AddCommGrpCat :=
  (CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
    (CategoryTheory.Limits.FormalCoproduct.mk _
      (p3StandardOpen (K := K))).cech).obj
    (modulePresheaf PS m).presheaf

/-- Projection of a Cech coface onto one ordered intersection. -/
lemma p3Cech_coface_comp_π (m n : ℕ) (i : Fin (n + 2))
    (f : Fin (n + 2) → Fin 4) :
    let E := (CategoryTheory.Limits.FormalCoproduct.mk _
      (p3StandardOpen (K := K))).cech
    let P := (modulePresheaf PS m).presheaf
    (p3CechCosimplicial K m).δ i ≫
        Pi.π (fun j : (E.obj (Opposite.op (SimplexCategory.mk (n + 1)))).I =>
          P.obj (Opposite.op ((E.obj (Opposite.op (SimplexCategory.mk (n + 1)))).obj j))) f =
      Pi.π (fun j : (E.obj (Opposite.op (SimplexCategory.mk n))).I =>
          P.obj (Opposite.op ((E.obj (Opposite.op (SimplexCategory.mk n))).obj j)))
        (deleteTuple i f) ≫
      P.map ((E.map (SimplexCategory.δ i).op).φ f).op := by
  dsimp only
  simp only [p3CechCosimplicial, CosimplicialObject.δ,
    CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor_obj_map]
  exact Pi.lift_π _ f

set_option backward.isDefEq.respectTransparency false in
/-- Component formula for the differential of the raw Cech complex in every
nonnegative degree. -/
lemma p3Cech_objD_comp_π (m n : ℕ) (f : Fin (n + 2) → Fin 4) :
    let E := (CategoryTheory.Limits.FormalCoproduct.mk _
      (p3StandardOpen (K := K))).cech
    let P := (modulePresheaf PS m).presheaf
    AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (p3CechCosimplicial K m) n ≫
        Pi.π (fun j : (E.obj (Opposite.op (SimplexCategory.mk (n + 1)))).I =>
          P.obj (Opposite.op ((E.obj
            (Opposite.op (SimplexCategory.mk (n + 1)))).obj j))) f =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (Pi.π (fun j : (E.obj (Opposite.op (SimplexCategory.mk n))).I =>
            P.obj (Opposite.op ((E.obj (Opposite.op (SimplexCategory.mk n))).obj j)))
          (deleteTuple i f) ≫
        P.map ((E.map (SimplexCategory.δ i).op).φ f).op) := by
  dsimp only
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Preadditive.zsmul_comp]
  exact congrArg ((-1 : ℤ) ^ (i : ℕ) • ·)
    (p3Cech_coface_comp_π K m n i f)

/-- The face map deletes the indicated tuple entry. -/
lemma p3Cech_face_index (n : ℕ) (i : Fin (n + 2))
    (f : Fin (n + 2) → Fin 4) :
    let E := (CategoryTheory.Limits.FormalCoproduct.mk _
      (p3StandardOpen (K := K))).cech
    (E.map (SimplexCategory.δ i).op).f f = deleteTuple i f := by
  rfl

/-- The open-set map underlying a Cech face is the product of the projections
which omit the indicated tuple entry. -/
lemma p3Cech_face_openMap (n : ℕ) (i : Fin (n + 2))
    (f : Fin (n + 2) → Fin 4) :
    let E := (CategoryTheory.Limits.FormalCoproduct.mk _
      (p3StandardOpen (K := K))).cech
    (E.map (SimplexCategory.δ i).op).φ f =
      Pi.lift (fun j : Fin (n + 1) =>
        Pi.π (fun a : Fin (n + 2) =>
          p3StandardOpen (K := K) (f a)) (i.succAbove j)) := by
  rfl

end PfaffianDescent.ProjectiveNegativeTwist
