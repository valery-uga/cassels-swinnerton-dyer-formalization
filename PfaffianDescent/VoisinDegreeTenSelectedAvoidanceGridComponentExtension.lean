import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridRestrictionTransport

/-! Component maps retain their exact marked point after the literal
generic residue-field map into the determinant-open fraction field. -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u

def voisinDegreeTenSelectedAvoidance_extendComponent
    {F A B E : Type u} [CommRing F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B]
    (g : B →+* E) (φ : A →ₐ[F] B) :
    letI : Algebra F E := (g.comp (algebraMap F B)).toAlgebra
    A →ₐ[F] E := by
  letI : Algebra F E := (g.comp (algebraMap F B)).toAlgebra
  exact { toRingHom := g.comp φ.toRingHom
          commutes' := fun r => congrArg g (φ.commutes r) }

theorem voisinDegreeTenSelectedAvoidance_extendedComponent_exactMarkedPoint
    {F A B E : Type u} [CommRing F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B] (g : B →+* E) (φ : A →ₐ[F] B)
    {X : Scheme.{u}} (j : Spec (.of A) ⟶ X) (marked : Spec (.of B) ⟶ X)
    (hmarked : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j = marked) :
    letI : Algebra F E := (g.comp (algebraMap F B)).toAlgebra
    Spec.map (CommRingCat.ofHom
      (voisinDegreeTenSelectedAvoidance_extendComponent g φ).toRingHom) ≫ j =
      Spec.map (CommRingCat.ofHom g) ≫ marked := by
  letI : Algebra F E := (g.comp (algebraMap F B)).toAlgebra
  change Spec.map (CommRingCat.ofHom φ.toRingHom ≫ CommRingCat.ofHom g) ≫ j = _
  rw [Spec.map_comp, Category.assoc, hmarked]

end PfaffianDescent
