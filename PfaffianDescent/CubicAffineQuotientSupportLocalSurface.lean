import PfaffianDescent.ArbitraryFiniteFamilySurfaceStalkIntake
import PfaffianDescent.NativeFiniteSubschemePushOpen314

/-!
Actual finite-colength affine
quotients on arbitrary cubic opens supply regular local surface rings at
all their support points.  No regularity, dimension, or closed-point
certificate is accepted as an input.
-/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

theorem cubicAffineQuotient_support_localSurface001
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (a : Spec (.of A) ⟶ hypersurface p hp) [IsOpenImmersion a]
    (ha : a ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (J : Ideal A) [Module.Finite K (A ⧸ J)] (z : PrimeSpectrum (A ⧸ J)) :
    IsRegularLocalRing (Localization.AtPrime
      (Ideal.comap (Ideal.Quotient.mk J) z.asIdeal)) ∧
      ringKrullDim (Localization.AtPrime
        (Ideal.comap (Ideal.Quotient.mk J) z.asIdeal)) = 2 := by
  let Q := A ⧸ J
  let j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let i := j ≫ a
  let F := hypersurfaceToBase p hp
  have hiF : i ≫ F = Spec.map (CommRingCat.ofHom (algebraMap K Q)) := by
    change (j ≫ a) ≫ F = _
    rw [Category.assoc, ha, ← Spec.map_comp]
    rfl
  letI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K Q))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI : IsFinite (i ≫ F) := by rw [hiF]; infer_instance
  letI : IsClosedImmersion j :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  letI : IsClosedImmersion i := nativeFiniteClosedThroughOpen_isClosed314 j a F
  obtain ⟨_, hreg, hdim, _, _⟩ := finiteEmbeddedCubicFieldFamily_stalk_intake001
    p hp hp0 i z
  let y : PrimeSpectrum A := PrimeSpectrum.comap (Ideal.Quotient.mk J) z
  letI : IsIso (a.stalkMap y) :=
    ((IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion a)).2 y)
  let e1 := (asIso (a.stalkMap y)).commRingCatIsoToRingEquiv
  let e2 := (Spec.stalkIso (.of A) y).commRingCatIsoToRingEquiv
  let e := e1.trans e2
  letI : IsRegularLocalRing ((hypersurface p hp).presheaf.stalk (a y)) := hreg
  exact ⟨IsRegularLocalRing.of_ringEquiv e,
    (ringKrullDim_eq_of_ringEquiv e).symm.trans hdim⟩

end PfaffianDescent
end
