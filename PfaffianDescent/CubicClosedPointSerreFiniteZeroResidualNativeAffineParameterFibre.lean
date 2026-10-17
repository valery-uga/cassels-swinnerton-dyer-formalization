import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeAffineFibreParameter
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualArtinianFibreStalk
import AllCharacteristics.SmoothSchemeRegularity

/-! # Actual point-fibre geometry on literal local parameter quotients -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def cubicClosedPointSerreFiniteZeroResidual_nativeAffine_asFibre_parameter_stalkRingEquiv
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (x : Spec (.of B))
    [((Spec.map (CommRingCat.ofHom g)) x).asIdeal.IsMaximal]
    (t : A) (ht : ((Spec.map (CommRingCat.ofHom g)) x).asIdeal = Ideal.span {t}) :
    let f := Spec.map (CommRingCat.ofHom g)
    ((Spec (.of B)).presheaf.stalk x ⧸ Ideal.span
      ({f.stalkMap x ((Spec (.of A)).presheaf.germ ⊤ (f x) (by trivial)
        ((Scheme.ΓSpecIso (.of A)).inv t))} : Set ((Spec (.of B)).presheaf.stalk x))) ≃+*
      (f.fiber (f x)).presheaf.stalk (f.asFiber x) := by
  let f := Spec.map (CommRingCat.ofHom g)
  have e := cubicClosedPointSerreFiniteZeroResidual_nativeAffineFibre_parameter_stalkRingEquiv
    g (f x) t ht (f.asFiber x)
  let P : (Spec (.of B)) → Type u := fun v =>
    ((Spec (.of B)).presheaf.stalk v ⧸ Ideal.span
      ({f.stalkMap v ((Spec (.of A)).presheaf.germ ⊤ (f v) (by trivial)
        ((Scheme.ΓSpecIso (.of A)).inv t))} : Set ((Spec (.of B)).presheaf.stalk v))) ≃+*
      (f.fiber (f x)).presheaf.stalk (f.asFiber x)
  have hpoint : f.fiberι (f x) (f.asFiber x) = x := f.fiberι_asFiber x
  exact cast (congrArg P hpoint) e

/-- Quasi-finiteness of the actual affine zero map supplies Artinianness of
its actual stalk quotient by the local base parameter. -/
theorem cubicClosedPointSerreFiniteZeroResidual_nativeAffine_parameter_quotient_artinian
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) [LocallyQuasiFinite (Spec.map (CommRingCat.ofHom g))]
    (x : Spec (.of B)) [((Spec.map (CommRingCat.ofHom g)) x).asIdeal.IsMaximal]
    (t : A) (ht : ((Spec.map (CommRingCat.ofHom g)) x).asIdeal = Ideal.span {t}) :
    let f := Spec.map (CommRingCat.ofHom g)
    IsArtinianRing ((Spec (.of B)).presheaf.stalk x ⧸ Ideal.span
      ({f.stalkMap x ((Spec (.of A)).presheaf.germ ⊤ (f x) (by trivial)
        ((Scheme.ΓSpecIso (.of A)).inv t))} : Set ((Spec (.of B)).presheaf.stalk x))) := by
  let f := Spec.map (CommRingCat.ofHom g)
  letI := cubicClosedPointSerreFiniteZeroResidual_isArtinianRing_fibre_stalk
    f (f x) (f.asFiber x)
  exact (cubicClosedPointSerreFiniteZeroResidual_nativeAffine_asFibre_parameter_stalkRingEquiv
    g x t ht).symm.isArtinianRing

/-- Regularity and dimension of the actual fibre stalk transfer to the
literal local quotient constructed here. -/
theorem cubicClosedPointSerreFiniteZeroResidual_nativeAffine_parameter_quotient_regular_dim_two
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (x : Spec (.of B))
    [((Spec.map (CommRingCat.ofHom g)) x).asIdeal.IsMaximal]
    (t : A) (ht : ((Spec.map (CommRingCat.ofHom g)) x).asIdeal = Ideal.span {t})
    [IsRegularLocalRing (((Spec.map (CommRingCat.ofHom g)).fiber
      ((Spec.map (CommRingCat.ofHom g)) x)).presheaf.stalk
        ((Spec.map (CommRingCat.ofHom g)).asFiber x))]
    (hd : ringKrullDim (((Spec.map (CommRingCat.ofHom g)).fiber
      ((Spec.map (CommRingCat.ofHom g)) x)).presheaf.stalk
        ((Spec.map (CommRingCat.ofHom g)).asFiber x)) = 2) :
    let f := Spec.map (CommRingCat.ofHom g)
    let Q := (Spec (.of B)).presheaf.stalk x ⧸ Ideal.span
      ({f.stalkMap x ((Spec (.of A)).presheaf.germ ⊤ (f x) (by trivial)
        ((Scheme.ΓSpecIso (.of A)).inv t))} : Set ((Spec (.of B)).presheaf.stalk x))
    IsRegularLocalRing Q ∧ ringKrullDim Q = 2 := by
  let e := cubicClosedPointSerreFiniteZeroResidual_nativeAffine_asFibre_parameter_stalkRingEquiv
    g x t ht
  constructor
  · exact IsRegularLocalRing.of_ringEquiv e.symm
  · exact (ringKrullDim_eq_of_ringEquiv e).trans hd

end PfaffianDescent
