import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeStalkQuotient
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualAffineIdealComap

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_affineClosedFibre_kernel
    {X Y B : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : X ⟶ Y) (i : B ⟶ Y) [IsClosedImmersion i]
    (z : (pullback g i : Scheme)) :
    RingHom.ker ((pullback.fst g i).stalkMap z).hom =
      (i.ker.ideal ⟨⊤, isAffineOpen_top Y⟩).map
        ((X.presheaf.germ ⊤ (pullback.fst g i z) trivial).hom.comp g.appTop.hom) := by
  have hi : i.ker = Scheme.IdealSheafData.ofIdealTop
      (i.ker.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    simp [Scheme.IdealSheafData.ofIdealTop_ideal]
  have hk : (pullback.fst g i).ker = Scheme.IdealSheafData.ofIdealTop
      ((i.ker.ideal ⟨⊤, isAffineOpen_top Y⟩).map g.appTop.hom) := by
    rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, hi,
      cubicClosedPointSerreFiniteZeroResidual_affineIdeal_comap]
    simp [Scheme.IdealSheafData.ofIdealTop_ideal]
  rw [← cubicClosedPointSerreFiniteZeroResidual_affineIdeal_germ_eq_stalkMap_kernel
    (pullback.fst g i) ⟨⊤, isAffineOpen_top X⟩ z trivial, hk,
    Scheme.IdealSheafData.ofIdealTop_ideal]
  simp [Ideal.map_map]

def cubicClosedPointSerreFiniteZeroResidual_affineClosedFibre_stalkQuotient
    {X Y B : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : X ⟶ Y) (i : B ⟶ Y) [IsClosedImmersion i]
    (z : (pullback g i : Scheme)) :
    (X.presheaf.stalk (pullback.fst g i z) ⧸
      (i.ker.ideal ⟨⊤, isAffineOpen_top Y⟩).map
        ((X.presheaf.germ ⊤ (pullback.fst g i z) trivial).hom.comp g.appTop.hom)) ≃+*
      (pullback g i).presheaf.stalk z :=
  (Ideal.quotEquivOfEq
    (cubicClosedPointSerreFiniteZeroResidual_affineClosedFibre_kernel g i z).symm).trans
      (((pullback.fst g i).stalkMap z).hom.quotientKerEquivOfSurjective
        ((pullback.fst g i).stalkMap_surjective z))

end PfaffianDescent
