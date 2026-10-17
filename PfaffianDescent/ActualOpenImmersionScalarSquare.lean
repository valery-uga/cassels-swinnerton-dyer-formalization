import PfaffianDescent.SchemeBaseScalarPresheaf
import Mathlib.AlgebraicGeometry.OpenImmersion

/- SOURCE ONLY / UNVERIFIED. The constants on an open subscheme agree with
restriction of the SAME actual global structure morphism. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {k : Type u} [CommRing k] {Y X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact actual scalar square; it is derived from the scheme maps and is
not a chart-comparison premise. -/
theorem actualOpenImmersion_baseScalar_square
    (f : Y ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (CommRingCat.of k))
    (U : Y.Opens) :
    (schemeBaseScalarPresheafMap (f ≫ g)).app (op U) ≫ (f.appIso U).inv =
      (schemeBaseScalarPresheafMap g).app (op (f ''ᵁ U)) := by
  unfold schemeBaseScalarPresheafMap
  simp only [Scheme.Hom.comp_appTop, Category.assoc]
  rw [f.appIso_inv_naturality (homOfLE (show U ≤ ⊤ from le_top)).op]
  have htop : f.appTop ≫ (f.appIso (⊤ : Y.Opens)).inv =
      X.presheaf.map (homOfLE (show f ''ᵁ (⊤ : Y.Opens) ≤ ⊤ from le_top)).op := by
    exact f.app_appIso_inv (⊤ : X.Opens)
  rw [← Category.assoc f.appTop, htop]
  rw [← Functor.map_comp]
  congr 2

end PfaffianDescent
