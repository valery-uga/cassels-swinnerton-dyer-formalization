import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualEtaleFibreStalkField
import Mathlib.AlgebraicGeometry.Morphisms.Finite

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_fibre_finite_etale_of_iso
    {S P Z D : Scheme.{u}} (z : Z ⟶ P) (t : S ⟶ P) (d : D ⟶ S)
    [IsFinite d] [Etale d] (v : D ≅ pullback z t)
    (hv : v.hom ≫ pullback.snd z t = d) :
    IsFinite (pullback.snd z t) ∧ Etale (pullback.snd z t) := by
  have he : pullback.snd z t = v.inv ≫ d := by
    rw [← cancel_epi v.hom]
    simp only [Iso.hom_inv_id_assoc]
    exact hv
  constructor <;> rw [he] <;> infer_instance

theorem cubicClosedPointSerreFiniteZeroResidual_field_fibre_stalks_of_iso
    {K : Type u} [Field K] {P Z D : Scheme.{u}}
    (z : Z ⟶ P) (t : Spec (.of K) ⟶ P) (d : D ⟶ Spec (.of K))
    [IsFinite d] [Etale d] (v : D ≅ pullback z t)
    (hv : v.hom ≫ pullback.snd z t = d) (x : (pullback z t : Scheme)) :
    IsField ((pullback z t).presheaf.stalk x) := by
  let h := cubicClosedPointSerreFiniteZeroResidual_fibre_finite_etale_of_iso z t d v hv
  letI : Etale (pullback.snd z t) := h.2
  exact cubicClosedPointSerreFiniteZeroResidual_unramifiedField_stalk_isField
    (pullback.snd z t) x

end PfaffianDescent
