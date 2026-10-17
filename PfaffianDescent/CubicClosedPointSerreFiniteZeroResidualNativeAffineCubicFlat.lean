import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeAffineCurve
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeOpenSurfaceFibre
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeClosedFibrePoint

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An actual quasi-finite pair-zero chart in the constant smooth cubic
family over an actual regular PID curve chart is flat.  The regular surface
fibre and finite-colength quotient are obtained from the actual geometry. -/
theorem cubicClosedPointSerreFiniteZeroResidual_nativeAffine_pair_zero_flat_of_open_cubic_curve
    {K C B : Type u} [Field K] [CommRing C] [IsDomain C] [IsPrincipalIdealRing C]
    [CommRing B] [IsNoetherianRing B]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (k : Spec (.of C) ⟶ Spec (.of K)) (g : C →+* B)
    (j : Spec (.of B) ⟶ pullback (hypersurfaceToBase p hp) k) [IsOpenImmersion j]
    (hj : j ≫ pullback.snd (hypersurfaceToBase p hp) k = Spec.map (CommRingCat.ofHom g))
    (a b : B)
    [LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.span ({a, b} : Set B)))) ≫ Spec.map (CommRingCat.ofHom g))]
    (hR : ∀ y : Spec (.of C), IsRegularLocalRing ((Spec (.of C)).presheaf.stalk y))
    (hdR : ∀ y : Spec (.of C), ringKrullDim ((Spec (.of C)).presheaf.stalk y) ≤ 1) :
    Flat (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({a, b} : Set B)))) ≫
      Spec.map (CommRingCat.ofHom g)) := by
  let f := Spec.map (CommRingCat.ofHom g)
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({a, b} : Set B))))
  letI : Flat f := by
    dsimp only [f]
    rw [← hj]
    infer_instance
  letI : IsClosedImmersion i := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  apply cubicClosedPointSerreFiniteZeroResidual_nativeAffine_pair_zero_flat_of_curve g a b hR hdR
  dsimp only
  intro z _
  exact cubicClosedPointSerreFiniteZeroResidual_surface_open_fibre_stalk_regular_dim_two
    p hp hp0 k f j hj (f (i z)) (f.asFiber (i z))
      (cubicClosedPointSerreFiniteZeroResidual_closed_asFibre_of_quasiFinite_zero i f z)

end PfaffianDescent
