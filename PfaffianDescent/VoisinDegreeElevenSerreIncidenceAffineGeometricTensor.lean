import PfaffianDescent.VoisinDegreeElevenSerreIncidencePullbackNonempty
import PfaffianDescent.VoisinFieldBaseChangeOpen
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Native coefficient tensor of a geometrically integral actual affine chart -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceGeometric_sourceOpen
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [GeometricallyIntegral base]
    (U : X.Opens) [Nonempty (U : Scheme.{u})] :
    GeometricallyIntegral (U.ι ≫ base) := by
  constructor
  intro L hL g Z fst snd h
  letI : Surjective g := (surjective_iff g).mpr (fun x =>
    ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩)
  letI : IsIntegral (pullback base g) :=
    GeometricallyIntegral.geometrically_isIntegral g _ _ (.of_hasPullback base g)
  letI : Nonempty (pullback (U.ι ≫ base) g : Scheme.{u}) :=
    serreIncidencePullback_nonempty (U.ι ≫ base) g
  let a := pullbackRightPullbackFstIso base g U.ι
  letI : Nonempty (pullback U.ι (pullback.fst base g) : Scheme.{u}) :=
    ⟨a.inv (Classical.choice (inferInstance : Nonempty (pullback (U.ι ≫ base) g : Scheme.{u})))⟩
  letI : IsIntegral (pullback U.ι (pullback.fst base g)) :=
    isIntegral_of_isOpenImmersion (pullback.snd U.ι (pullback.fst base g))
  letI : IsIntegral (pullback (U.ι ≫ base) g) := IsIntegral.of_isIso a.hom
  exact IsIntegral.of_isIso h.isoPullback.inv

theorem serreIncidenceGeometricAffine_tensor_isDomain
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} [IsAffine X] (base : X ⟶ Spec (.of K))
    [GeometricallyIntegral base] :
    letI := RingHom.toAlgebra (schemeOpenBaseRingHom base ⊤)
    IsDomain (L ⊗[K] Γ(X, ⊤)) := by
  letI := RingHom.toAlgebra (schemeOpenBaseRingHom base ⊤)
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  letI : IsIntegral (schemeFieldBaseChange (L := L) base) :=
    GeometricallyIntegral.geometrically_isIntegral g _ _ (.of_hasPullback base g)
  have h : IsIntegral (Spec (.of (L ⊗[K] Γ(X, ⊤)))) :=
    IsIntegral.of_isIso (affineSchemeFieldBaseChangeIso (L := L) base).hom
  exact (affine_isIntegral_iff (.of (L ⊗[K] Γ(X, ⊤)))).mp h

end PfaffianDescent
