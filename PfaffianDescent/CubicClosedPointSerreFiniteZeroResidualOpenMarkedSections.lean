import Mathlib.AlgebraicGeometry.Restrict
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualEtaleOpenTransport
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualMarkedSectionOpen

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def cubicClosedPointSerreFiniteZeroResidual_openMarkedSection
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (j : Y ⟶ Z) (hj : j ≫ g = 𝟙 Y)
    (U : Y.Opens) : (U : Scheme) ⟶ (g ⁻¹ᵁ U : Scheme) :=
  IsOpenImmersion.lift (g ⁻¹ᵁ U).ι (U.ι ≫ j) (by
    rintro _ ⟨y, rfl⟩
    refine ⟨⟨j (U.ι y), ?_⟩, rfl⟩
    change g (j (U.ι y)) ∈ U
    have he : g (j (U.ι y)) = U.ι y :=
      congrArg (fun f : Y ⟶ Y => f (U.ι y)) hj
    rw [he]
    exact y.property)

theorem cubicClosedPointSerreFiniteZeroResidual_openMarkedSection_comp_source
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (j : Y ⟶ Z) (hj : j ≫ g = 𝟙 Y)
    (U : Y.Opens) :
    cubicClosedPointSerreFiniteZeroResidual_openMarkedSection g j hj U ≫ (g ⁻¹ᵁ U).ι = U.ι ≫ j :=
  IsOpenImmersion.lift_fac _ _ _

theorem cubicClosedPointSerreFiniteZeroResidual_openMarkedSection_section
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (j : Y ⟶ Z) (hj : j ≫ g = 𝟙 Y)
    (U : Y.Opens) :
    cubicClosedPointSerreFiniteZeroResidual_openMarkedSection g j hj U ≫
      g.resLE U (g ⁻¹ᵁ U) le_rfl = 𝟙 (U : Scheme) := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    cubicClosedPointSerreFiniteZeroResidual_openMarkedSection_comp_source]
  simp only [Category.assoc, hj, Category.comp_id, Category.id_comp]

theorem cubicClosedPointSerreFiniteZeroResidual_openMarkedSection_mem_transfer
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (j : Y ⟶ Z) (hj : j ≫ g = 𝟙 Y)
    (U : Y.Opens) (y : (U : Scheme))
    (hy : y ∈ cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen
      (g.resLE U (g ⁻¹ᵁ U) le_rfl)
      (cubicClosedPointSerreFiniteZeroResidual_openMarkedSection g j hj U)) :
    U.ι y ∈ cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen g j := by
  let l := cubicClosedPointSerreFiniteZeroResidual_openMarkedSection g j hj U
  have hpost := cubicClosedPointSerreFiniteZeroResidual_etaleOpen_mem_postcomp
    (g.resLE U (g ⁻¹ᵁ U) le_rfl) U.ι (l y) hy
  rw [Scheme.Hom.resLE_comp_ι] at hpost
  have hglobal := cubicClosedPointSerreFiniteZeroResidual_etaleOpen_mem_under_openImmersion
    (g ⁻¹ᵁ U).ι g (l y) hpost
  have he : (g ⁻¹ᵁ U).ι (l y) = j (U.ι y) :=
    congrArg (fun f : (U : Scheme) ⟶ Z => f y)
      (cubicClosedPointSerreFiniteZeroResidual_openMarkedSection_comp_source g j hj U)
  change j (U.ι y) ∈ cubicClosedPointSerreFiniteZeroResidual_etaleOpen g
  exact he ▸ hglobal

end PfaffianDescent
