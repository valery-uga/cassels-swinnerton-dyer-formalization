import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodPointFinite
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalFibreBaseChange

/-! A proper canonical chosen fibre is finite over the ground field if its
actual field-base-change fibre has finite support. Reducedness is unnecessary. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreActualCanonicalChosenFibre_isFinite_of_fieldBaseChange_finite
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {Z P : Scheme.{u}} (z : Z ⟶ P) [IsProper z]
    (t : Spec (.of F) ⟶ P)
    [Finite (pullback z (Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t) : Scheme)] :
    IsFinite (pullback.snd z t) := by
  let d := pullback.snd z t
  let r := Spec.map (CommRingCat.ofHom (algebraMap F E))
  let e := serreIncidenceCanonicalFibreBaseChangeIso z t d
    (Iso.refl (pullback z t)) (by simp only [Iso.refl_hom, Category.id_comp, d]) r
  letI : Finite (pullback d r : Scheme) := Finite.of_injective e.hom e.hom.injective
  letI : Finite (pullback z t : Scheme) :=
    cubicClosedPointSerreFiniteZeroResidual_fieldBaseChange_finite_descend (E := E) d
  letI : LocallyQuasiFinite d :=
    LocallyQuasiFinite.of_finite_preimage_singleton d (fun _ => Set.toFinite _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite d

end PfaffianDescent
