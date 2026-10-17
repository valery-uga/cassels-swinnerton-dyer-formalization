import PfaffianDescent.SerreActualCanonicalChosenFibreFiniteDescent

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u

/-- Associate the actual field-extension parameter before descending the
canonical chosen fibre's finiteness to its original ground parameter. -/
theorem serreActualCanonicalChosenGroundFibre_isFinite
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {Z P Q : Scheme.{u}} (z : Z ⟶ Q) [IsProper z]
    (v : P ⟶ Q) (b : Spec (.of F) ⟶ P)
    [Finite (pullback z
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ b) ≫ v) : Scheme)] :
    IsFinite (pullback.snd z (b ≫ v)) := by
  let r := Spec.map (CommRingCat.ofHom (algebraMap F E))
  let e := pullback.congrHom (show z = z from rfl) (Category.assoc r b v)
  letI : Finite (pullback z (r ≫ (b ≫ v)) : Scheme) :=
    Finite.of_injective e.inv e.inv.injective
  exact serreActualCanonicalChosenFibre_isFinite_of_fieldBaseChange_finite
    (E := E) z (b ≫ v)

end PfaffianDescent
