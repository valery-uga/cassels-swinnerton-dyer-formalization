import PfaffianDescent.CubicClosedPointSerrePointSplittingAffineTensor
import AllCharacteristics.FiniteSigmaSpec

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- An actual spectrum isomorphism gives the coordinate-ring isomorphism
in the opposite direction, using Spec's genuine preimage. -/
def pointSplittingRingEquivOfSpecIso {R S : Type u} [CommRing R] [CommRing S]
    (e : Spec (.of R) ≅ Spec (.of S)) : R ≃+* S := by
  let f : CommRingCat.of R ⟶ CommRingCat.of S := Spec.preimage e.inv
  have hf : Spec.map f = e.inv := Spec.map_preimage _
  haveI : IsIso (Spec.map f) := hf ▸ inferInstance
  exact RingEquiv.ofBijective f.hom (isIso_SpecMap_iff.mp inferInstance)

/-- The actual split-cover scheme comparison induces the literal split
coordinate algebra. Applications construct the cover from ordered incidence. -/
def pointSplittingFiniteCoordinateRingEquiv
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {D : Scheme.{u}} (q : D ⟶ Spec (.of F)) [IsFinite q]
    (n : ℕ)
    (e : (∐ fun _ : ULift.{u} (Fin n) ↦ Spec (.of E)) ≅
      pullback q (Spec.map (CommRingCat.ofHom (algebraMap F E)))) :
    letI := finiteSchemeCoefficientAlgebra q
    (E ⊗[F] Γ(D, ⊤)) ≃+* (ULift.{u} (Fin n) → E) := by
  letI := finiteSchemeCoefficientAlgebra q
  exact pointSplittingRingEquivOfSpecIso
    ((pointSplittingFinitePullbackTensorIso q).symm ≪≫ e.symm ≪≫
      asIso (sigmaSpec (fun _ : ULift.{u} (Fin n) ↦ CommRingCat.of E)))

end PfaffianDescent
