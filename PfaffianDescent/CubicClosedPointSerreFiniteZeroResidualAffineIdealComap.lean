import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_affineIdeal_comap
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (I : Ideal Γ(Y, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop I).comap f =
      Scheme.IdealSheafData.ofIdealTop (I.map f.appTop.hom) := by
  apply le_antisymm
  · rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
    apply Scheme.IdealSheafData.le_of_isAffine
    rw [Scheme.IdealSheafData.ofIdealTop_ideal,
      Scheme.IdealSheafData.ideal_map_of_isAffineHom]
    simpa using (Ideal.le_comap_map (f := f.appTop.hom) (I := I))
  · apply Scheme.IdealSheafData.le_of_isAffine
    rw [Scheme.IdealSheafData.ofIdealTop_ideal]
    have h := (Scheme.IdealSheafData.ofIdealTop I).le_map_comap f
    have ht := h ⟨⊤, isAffineOpen_top Y⟩
    rw [Scheme.IdealSheafData.ofIdealTop_ideal,
      Scheme.IdealSheafData.ideal_map_of_isAffineHom] at ht
    have ht' : I ≤ Ideal.comap f.appTop.hom
        (((Scheme.IdealSheafData.ofIdealTop I).comap f).ideal ⟨⊤, isAffineOpen_top X⟩) := by
      simpa using ht
    simpa using Ideal.map_le_iff_le_comap.mpr ht'

end PfaffianDescent
