import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeEtaleOpen
import Mathlib.AlgebraicGeometry.Morphisms.Proper

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def cubicClosedPointSerreFiniteZeroResidual_markedEtaleParameterOpen
    {Z P Y : Scheme.{u}} (g : Z ⟶ Y) (j : P ⟶ Z) [IsProper (j ≫ g)] : Y.Opens :=
  ⟨((j ≫ g) '' (j ⁻¹' (cubicClosedPointSerreFiniteZeroResidual_etaleOpen g : Set Z))ᶜ)ᶜ,
    ((j ≫ g).isClosedMap _
      ((cubicClosedPointSerreFiniteZeroResidual_etaleOpen g).isOpen.preimage j.continuous).isClosed_compl).isOpen_compl⟩

theorem cubicClosedPointSerreFiniteZeroResidual_mem_markedEtaleParameterOpen
    {Z P Y : Scheme.{u}} (g : Z ⟶ Y) (j : P ⟶ Z) [IsProper (j ≫ g)] (y : Y) :
    y ∈ cubicClosedPointSerreFiniteZeroResidual_markedEtaleParameterOpen g j ↔
    ∀ z : P, (j ≫ g) z = y → j z ∈ cubicClosedPointSerreFiniteZeroResidual_etaleOpen g := by
  change y ∉ (j ≫ g) '' (j ⁻¹' (cubicClosedPointSerreFiniteZeroResidual_etaleOpen g : Set Z))ᶜ ↔ _
  constructor
  · intro h z hz
    by_contra hj
    exact h ⟨z, hj, hz⟩
  · intro h
    rintro ⟨z, hz, he⟩
    exact hz (h z he)

theorem cubicClosedPointSerreFiniteZeroResidual_markedEtaleParameterOpen_marked_range
    {Z P Y : Scheme.{u}} (g : Z ⟶ Y) (j : P ⟶ Z) [IsProper (j ≫ g)]
    (z : P) (hz : (j ≫ g) z ∈ cubicClosedPointSerreFiniteZeroResidual_markedEtaleParameterOpen g j) :
    j z ∈ cubicClosedPointSerreFiniteZeroResidual_etaleOpen g :=
  (cubicClosedPointSerreFiniteZeroResidual_mem_markedEtaleParameterOpen g j _).mp hz z rfl

end PfaffianDescent
