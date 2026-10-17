import PfaffianDescent.BundleSectionZeroLocusNaturality

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_affinePair_comap_top
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [IsOpenImmersion f] (I : Y.IdealSheafData) (a b : Γ(Y, ⊤))
    (hI : I = Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {a} ⊔ Ideal.span {b})) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      Ideal.span ({f.appTop a, f.appTop b} : Set Γ(X, ⊤)) := by
  rw [hI, BundleSectionZeroLocus.idealSheafData_comap_ofIdealTop_of_isOpenImmersion]
  simp [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_sup,
    Ideal.map_span, Set.image_singleton, Ideal.span_insert]

end PfaffianDescent
