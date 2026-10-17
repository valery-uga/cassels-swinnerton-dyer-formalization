import PfaffianDescent.VoisinDegreeElevenSerreIncidenceAffineConfigurationFunctions
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Actual affine section functions and literal ring homomorphisms -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceSpecMap_ΓSpec_inv
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (a : A) :
    (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso (.of A)).inv a) =
      (Scheme.ΓSpecIso (.of B)).inv (φ a) := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  exact (congrArg (fun f : CommRingCat.of A ⟶ Γ(Spec (.of B), ⊤) => f a) h).symm

theorem serreIncidenceAffineConfiguration_function
    {A K : Type u} [CommRing A] [CommRing K]
    {B Q : Scheme.{u}} [IsAffine B] (b : B ⟶ Spec (.of K)) (v : Q ⟶ Spec (.of K))
    (e : Spec (.of A) ⟶ pullback b v) (g : Γ(B, ⊤) →+* A)
    (hf : e ≫ pullback.fst b v = Spec.map (CommRingCat.ofHom g) ≫ B.isoSpec.inv)
    (a : Γ(B, ⊤)) :
    e.appTop ((pullback.fst b v).appTop a) = (Scheme.ΓSpecIso (.of A)).inv (g a) := by
  have h := congrArg Scheme.Hom.appTop hf
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    serreIncidenceAffineConfiguration_isoSpec_inv_appTop] at h
  exact (congrArg (fun f => f a) h).trans (serreIncidenceSpecMap_ΓSpec_inv g a)

end PfaffianDescent
