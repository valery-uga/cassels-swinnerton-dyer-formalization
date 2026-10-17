import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualMarkedOpenImmersion

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (j : Y ⟶ Z) : Y.Opens :=
  j ⁻¹ᵁ cubicClosedPointSerreFiniteZeroResidual_etaleOpen g

theorem cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen_isOpenImmersion
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (j : Y ⟶ Z)
    (hj : j ≫ g = 𝟙 Y) :
    IsOpenImmersion
      ((cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen g j).ι ≫ j) := by
  let V := cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen g j
  letI : Mono j := mono_of_mono_fac (f := g) (g := j) hj
  letI : Etale ((V.ι ≫ j) ≫ g) := by
    rw [Category.assoc, hj, Category.comp_id]
    infer_instance
  apply cubicClosedPointSerreFiniteZeroResidual_marked_isOpenImmersion g (V.ι ≫ j)
  rintro _ ⟨y, rfl⟩
  exact y.property

def cubicClosedPointSerreFiniteZeroResidual_threeMarkedSectionOpen
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (j : Fin 3 → (Y ⟶ Z)) : Y.Opens :=
  ⨅ i : Fin 3, cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen g (j i)

theorem cubicClosedPointSerreFiniteZeroResidual_threeMarkedSectionOpen_isOpenImmersion
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (j : Fin 3 → (Y ⟶ Z))
    (hj : ∀ i, j i ≫ g = 𝟙 Y) (i : Fin 3) :
    IsOpenImmersion
      ((cubicClosedPointSerreFiniteZeroResidual_threeMarkedSectionOpen g j).ι ≫ j i) := by
  let V := cubicClosedPointSerreFiniteZeroResidual_threeMarkedSectionOpen g j
  letI : Mono (j i) := mono_of_mono_fac (f := g) (g := j i) (hj i)
  letI : Etale ((V.ι ≫ j i) ≫ g) := by
    rw [Category.assoc, hj i, Category.comp_id]
    infer_instance
  apply cubicClosedPointSerreFiniteZeroResidual_marked_isOpenImmersion g (V.ι ≫ j i)
  rintro _ ⟨y, rfl⟩
  exact (show V ≤ cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen g (j i)
    from iInf_le _ i) y.property

end PfaffianDescent
