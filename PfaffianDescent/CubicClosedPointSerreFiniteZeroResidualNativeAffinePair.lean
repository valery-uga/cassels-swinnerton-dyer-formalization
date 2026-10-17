import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeAffineFibreParameter
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualFibrePairQuotient
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualArtinianFibreStalk

/-! # Actual affine pair germs and actual local base parameters -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_spec_parameter_generates_maximalIdeal
    {A : Type u} [CommRing A] (y : Spec (.of A))
    (t : A) (ht : y.asIdeal = Ideal.span {t}) :
    IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk y) =
      Ideal.span ({(Spec (.of A)).presheaf.germ ⊤ y (by trivial)
        ((Scheme.ΓSpecIso (.of A)).inv t)} : Set ((Spec (.of A)).presheaf.stalk y)) := by
  letI : Algebra (CommRingCat.of A) ((Spec (.of A)).presheaf.stalk y) :=
    StructureSheaf.stalkAlgebra (CommRingCat.of A) y
  letI : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of A) y
  have h := IsLocalization.AtPrime.map_eq_maximalIdeal y.asIdeal
    ((Spec (.of A)).presheaf.stalk y)
  rw [ht, Ideal.map_span, Set.image_singleton] at h
  exact h.symm

theorem cubicClosedPointSerreFiniteZeroResidual_spec_pairZero_stalkMap_kernel
    {B : Type u} [CommRing B] (a b : B)
    (z : Spec (.of (B ⧸ Ideal.span ({a, b} : Set B)))) :
    let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({a, b} : Set B))))
    RingHom.ker (i.stalkMap z).hom = Ideal.span
      ({(Spec (.of B)).presheaf.germ ⊤ (i z) (by trivial) ((Scheme.ΓSpecIso (.of B)).inv a),
        (Spec (.of B)).presheaf.germ ⊤ (i z) (by trivial) ((Scheme.ΓSpecIso (.of B)).inv b)} :
        Set ((Spec (.of B)).presheaf.stalk (i z))) := by
  let I := Ideal.span ({a, b} : Set B)
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let e := (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv
  have hk : i.ker.ideal ⟨⊤, isAffineOpen_top _⟩ = I.comap e.toRingHom := by
    rw [specMap_ker_ideal_top]
    change (RingHom.ker (Ideal.Quotient.mk I)).comap e.toRingHom = _
    rw [Ideal.mk_ker]
  have hspan : i.ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span ({e.symm a, e.symm b} : Set Γ(Spec (.of B), ⊤)) := by
    rw [hk]
    calc
      _ = I.map e.symm := (Ideal.map_symm e).symm
      _ = _ := by rw [show I = Ideal.span ({a, b} : Set B) from rfl, Ideal.map_span, Set.image_pair]
  letI : IsClosedImmersion i := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  dsimp only
  rw [← cubicClosedPointSerreFiniteZeroResidual_affineIdeal_germ_eq_stalkMap_kernel
    i ⟨⊤, isAffineOpen_top _⟩ z (by trivial), hspan, Ideal.map_span, Set.image_pair]
  rfl

end PfaffianDescent
