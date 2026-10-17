import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeAffineCubicFlat
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeAffineProductChart
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualAffineFlatTransport
import AllCharacteristics.FlatIdealSubscheme

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicClosedPointSerreFiniteZeroResidual_nativeProduct_pair_zero_flat
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (U : (hypersurface p hp).affineOpens)
    {E : Scheme.{u}} [IsAffine E] [IsDomain Γ(E, ⊤)] [IsPrincipalIdealRing Γ(E, ⊤)]
    (k : E ⟶ Spec (.of K))
    [IsNoetherianRing Γ(pullback (U.1.ι ≫ hypersurfaceToBase p hp) k, ⊤)]
    (I : (pullback (U.1.ι ≫ hypersurfaceToBase p hp) k).IdealSheafData)
    (a b : Γ(pullback (U.1.ι ≫ hypersurfaceToBase p hp) k, ⊤))
    (hI : I.ideal ⟨⊤, by
      letI : IsAffine (U.1 : Scheme.{u}) := U.2
      exact isAffineOpen_top _⟩ = Ideal.span ({a, b} : Set _))
    [LocallyQuasiFinite (I.subschemeι ≫ pullback.snd (U.1.ι ≫ hypersurfaceToBase p hp) k)]
    (hR : ∀ y : E, IsRegularLocalRing (E.presheaf.stalk y))
    (hdR : ∀ y : E, ringKrullDim (E.presheaf.stalk y) ≤ 1) :
    Flat (I.subschemeι ≫ pullback.snd (U.1.ι ≫ hypersurfaceToBase p hp) k) := by
  letI : IsAffine (U.1 : Scheme.{u}) := U.2
  let T := pullback (U.1.ι ≫ hypersurfaceToBase p hp) k
  let f : T ⟶ E := pullback.snd (U.1.ι ≫ hypersurfaceToBase p hp) k
  let J := I.ideal ⟨⊤, isAffineOpen_top T⟩
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let e := AllCharacteristics.idealSubschemeIsoSpecQuotient I
  have he : e.hom ≫ q = I.subschemeι ≫ T.isoSpec.hom :=
    AllCharacteristics.idealSubschemeIsoSpecQuotient_hom_comp I
  have hc : e.hom ≫ (q ≫ Spec.map f.appTop) = (I.subschemeι ≫ f) ≫ E.isoSpec.hom := by
    rw [← Category.assoc, he, Category.assoc, Scheme.isoSpec_hom_naturality,
      ← Category.assoc]
  let ei : Arrow.mk (I.subschemeι ≫ f) ≅ Arrow.mk (q ≫ Spec.map f.appTop) :=
    Arrow.isoMk e E.isoSpec hc
  letI : LocallyQuasiFinite (q ≫ Spec.map f.appTop) :=
    (MorphismProperty.arrow_mk_iso_iff @LocallyQuasiFinite ei).mp inferInstance
  have hR' : ∀ y : Spec Γ(E, ⊤), IsRegularLocalRing ((Spec Γ(E, ⊤)).presheaf.stalk y) := by
    intro y
    letI := hR (E.isoSpec.inv y)
    exact IsRegularLocalRing.of_ringEquiv
      (asIso (E.isoSpec.inv.stalkMap y)).commRingCatIsoToRingEquiv
  have hdR' : ∀ y : Spec Γ(E, ⊤), ringKrullDim ((Spec Γ(E, ⊤)).presheaf.stalk y) ≤ 1 := by
    intro y
    rw [← ringKrullDim_eq_of_ringEquiv
      (asIso (E.isoSpec.inv.stalkMap y)).commRingCatIsoToRingEquiv]
    exact hdR (E.isoSpec.inv y)
  let j := cubicClosedPointSerreFiniteZeroResidual_affineProductOpenChart
    (hypersurfaceToBase p hp) U k
  have hj : j ≫ pullback.snd (hypersurfaceToBase p hp) (E.isoSpec.inv ≫ k) =
      Spec.map f.appTop :=
    cubicClosedPointSerreFiniteZeroResidual_affineProductOpenChart_comp
      (hypersurfaceToBase p hp) U k
  have hlit : Flat (q ≫ Spec.map f.appTop) := by
    change Flat (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ Spec.map f.appTop)
    have hJ : J = Ideal.span ({a, b} : Set Γ(T, ⊤)) := hI
    letI : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span ({a, b} : Set Γ(T, ⊤))))) ≫ Spec.map f.appTop) := by
      rw [← hJ]
      infer_instance
    letI : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span ({a, b} : Set Γ(T, ⊤))))) ≫ Spec.map (CommRingCat.ofHom f.appTop.hom)) := by
      rw [CommRingCat.ofHom_hom]
      infer_instance
    rw [hJ]
    exact cubicClosedPointSerreFiniteZeroResidual_nativeAffine_pair_zero_flat_of_open_cubic_curve
      p hp hp0 (E.isoSpec.inv ≫ k) f.appTop.hom j hj a b hR' hdR'
  exact (MorphismProperty.arrow_mk_iso_iff @Flat ei).mpr hlit

end PfaffianDescent
