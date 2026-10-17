import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Category.CommAlgCat.Basic

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} [CommRing R]

/-- The contravariant Spec map of an actual algebra map respects the original base. -/
lemma algebraHomSpecMap_overBase298
    {A D : Type u} [CommRing A] [CommRing D] [Algebra R A] [Algebra R D]
    (f : A →ₐ[R] D) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R D)) := by
  have h : f.toRingHom.comp (algebraMap R A) = algebraMap R D := by
    apply RingHom.ext
    intro r
    exact f.commutes r
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

variable {X Y : CommAlgCat.{u} R}

/-- An original algebra Iso X≅Y yields Spec X≅Spec Y by applying Spec
 to its inverse coefficient map. No replacement ring equivalence is chosen. -/
def commAlgebraSpecIso298 (e : X ≅ Y) : Spec (.of X) ≅ Spec (.of Y) :=
  Scheme.Spec.mapIso ((forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).mapIso e).symm.op

lemma commAlgebraSpecIso_hom298 (e : X ≅ Y) :
    (commAlgebraSpecIso298 e).hom =
      Spec.map (CommRingCat.ofHom e.inv.hom.toRingHom) := rfl

lemma commAlgebraSpecIso_inv298 (e : X ≅ Y) :
    (commAlgebraSpecIso298 e).inv =
      Spec.map (CommRingCat.ofHom e.hom.hom.toRingHom) := rfl

lemma commAlgebraSpecIso_symm298 (e : X ≅ Y) :
    (commAlgebraSpecIso298 e).symm = commAlgebraSpecIso298 e.symm := rfl

lemma commAlgebraSpecIso_overBase298 (e : X ≅ Y) :
    (commAlgebraSpecIso298 e).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R Y)) =
      Spec.map (CommRingCat.ofHom (algebraMap R X)) := by
  rw [commAlgebraSpecIso_hom298]
  exact algebraHomSpecMap_overBase298 e.inv.hom

end PfaffianDescent
