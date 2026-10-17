import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualMarkedEtaleParameterOpen
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_marked_isOpenImmersion
    {Z P Y : Scheme.{u}} (g : Z ⟶ Y) (j : P ⟶ Z)
    [Mono j] [Etale (j ≫ g)]
    (hr : Set.range j ⊆ (cubicClosedPointSerreFiniteZeroResidual_etaleOpen g : Set Z)) :
    IsOpenImmersion j := by
  let W := cubicClosedPointSerreFiniteZeroResidual_etaleOpen g
  have hr' : Set.range j ⊆ Set.range W.ι := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨j z, hr ⟨z, rfl⟩⟩, rfl⟩
  let l := IsOpenImmersion.lift W.ι j hr'
  have hl : l ≫ W.ι = j := IsOpenImmersion.lift_fac _ _ _
  let h := W.ι ≫ g
  letI : Etale h := cubicClosedPointSerreFiniteZeroResidual_etaleOpen_etale g
  letI : Etale (l ≫ h) := by
    change Etale (l ≫ (W.ι ≫ g))
    rw [← Category.assoc, hl]
    infer_instance
  letI : Etale l := Etale.of_comp l h
  letI : Mono l := mono_of_mono_fac (f := W.ι) (g := l) hl
  letI : IsOpenImmersion l := IsOpenImmersion.of_flat_of_mono l
  rw [← hl]
  infer_instance

end PfaffianDescent
