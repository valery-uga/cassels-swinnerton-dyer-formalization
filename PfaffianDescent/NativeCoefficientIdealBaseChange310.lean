import PfaffianDescent.FiniteFlatHilbertTestPoints195
import AllCharacteristics.ResidueSpecialFiber

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Arbitrary whole affine-ideal quotients form the literal Cartesian square
after any coefficient ring map. No polynomial-coordinate restriction. -/
lemma nativeCoefficientIdealQuotient_isPullback310
    {C D : Type u} [CommRing C] [CommRing D] (f : C →+* D) (I : Ideal C) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom f)) := by
  let q := Ideal.quotientMap (I.map f) f Ideal.le_comap_map
  have hc : (Ideal.Quotient.mk (I.map f)).comp f = q.comp (Ideal.Quotient.mk I) := by
    apply RingHom.ext
    intro x
    exact (Ideal.quotientMap_mk (I := I.map f) (J := I) (f := f)
      (H := Ideal.le_comap_map) (x := x)).symm
  have hk : RingHom.ker (Ideal.Quotient.mk (I.map f)) =
      (RingHom.ker (Ideal.Quotient.mk I)).map f := by
    rw [Ideal.mk_ker, Ideal.mk_ker]
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (AllCharacteristics.isPushout_of_surjective_of_ker_map f (Ideal.Quotient.mk I)
      (Ideal.Quotient.mk (I.map f)) q
      Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective hc hk)).flip

/-- Native whole coefficient kernels retain the exact extended affine ideal. -/
lemma nativeCoefficientIdealKernel_comap310
    {C D : Type u} [CommRing C] [CommRing D] (f : C →+* D) (I : Ideal C) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap
        (Spec.map (CommRingCat.ofHom f)) =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f)))).ker := by
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact wholeIdeal_comap_eq_of_isPullback195
    (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f))))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (Spec.map (CommRingCat.ofHom f)) (nativeCoefficientIdealQuotient_isPullback310 f I)

/-- An internally derived image equality supplies exact native coefficient
ideal-sheaf compatibility for descent. -/
lemma nativeCoefficientIdealImageKernel_comap310
    {C D : Type u} [CommRing C] [CommRing D] (f : C →+* D) (I : Ideal C) (J : Ideal D)
    (h : I.map f = J) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap
        (Spec.map (CommRingCat.ofHom f)) =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).ker :=
  (nativeCoefficientIdealKernel_comap310 f I).trans
    (congrArg (fun K : Ideal D => (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).ker) h)

end PfaffianDescent
end
