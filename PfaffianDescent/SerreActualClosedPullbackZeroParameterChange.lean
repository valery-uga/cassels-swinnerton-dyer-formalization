import PfaffianDescent.SerreActualClosedPullbackZeroIso
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! The actual closed zero-family comparison persists after restriction to a
parameter open, or after selecting a parameter point.  Finiteness and flatness
of the restricted old family transfer to the restricted new family. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

variable {T X Y Z W P U : Scheme.{u}}
variable (i : Z ⟶ X) (j : W ⟶ Y)
variable [IsClosedImmersion i] [IsClosedImmersion j]
variable (f : T ⟶ X) (g : T ⟶ Y)
variable (h : i.ker.comap f = j.ker.comap g)
variable (a : T ⟶ P) (b : U ⟶ P)

/-- No additional comparison of the parameter morphisms is assumed: it follows
from the actual closed-family comparison over their common ambient scheme. -/
def serreActualClosedPullbackZero_parameterChangeIso :
    pullback b (pullback.fst f i ≫ a) ≅
      pullback b (pullback.fst g j ≫ a) :=
  asIso (pullback.map b (pullback.fst f i ≫ a)
    b (pullback.fst g j ≫ a)
    (𝟙 U) (serreActualClosedPullbackZeroIso i j f g h).hom (𝟙 P)
    (by simp only [Category.comp_id, Category.id_comp])
    (by
      simpa only [Category.comp_id, Category.assoc] using
        (serreActualClosedPullbackZeroIso_hom_fst_assoc i j f g h a).symm))

@[reassoc]
theorem serreActualClosedPullbackZero_parameterChangeIso_hom_fst :
    (serreActualClosedPullbackZero_parameterChangeIso i j f g h a b).hom ≫
        pullback.fst b (pullback.fst g j ≫ a) =
      pullback.fst b (pullback.fst f i ≫ a) := by
  simp only [serreActualClosedPullbackZero_parameterChangeIso, asIso_hom,
    pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc]
theorem serreActualClosedPullbackZero_parameterChangeIso_hom_ambient :
    (serreActualClosedPullbackZero_parameterChangeIso i j f g h a b).hom ≫
        pullback.snd b (pullback.fst g j ≫ a) ≫ pullback.fst g j =
      pullback.snd b (pullback.fst f i ≫ a) ≫ pullback.fst f i := by
  simp only [serreActualClosedPullbackZero_parameterChangeIso, asIso_hom,
    pullback.map, pullback.lift_snd_assoc, Category.assoc,
    serreActualClosedPullbackZeroIso_hom_fst]

include h

/-- Transfer finiteness on the chosen open or fibre, rather than assuming that
the entire parameter family is finite. -/
theorem serreActualClosedPullbackZero_parameterChange_isFinite
    [IsFinite (pullback.fst b (pullback.fst g j ≫ a))] :
    IsFinite (pullback.fst b (pullback.fst f i ≫ a)) := by
  rw [← serreActualClosedPullbackZero_parameterChangeIso_hom_fst i j f g h a b]
  infer_instance

theorem serreActualClosedPullbackZero_parameterChange_flat
    [Flat (pullback.fst b (pullback.fst g j ≫ a))] :
    Flat (pullback.fst b (pullback.fst f i ≫ a)) := by
  rw [← serreActualClosedPullbackZero_parameterChangeIso_hom_fst i j f g h a b]
  infer_instance

end PfaffianDescent
