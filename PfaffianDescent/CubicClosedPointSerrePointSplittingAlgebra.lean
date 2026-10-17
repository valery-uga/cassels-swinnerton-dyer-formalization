import PfaffianDescent.CubicClosedPointSerrePointSplittingRing
import PfaffianDescent.CubicClosedPointSerrePointSplittingAffineTensorProjection
import AllCharacteristics.ConstantCovers

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def pointSplittingAlgEquivOfSpecIso
    {E R S : Type u} [Field E] [CommRing R] [CommRing S] [Algebra E R] [Algebra E S]
    (e : Spec (.of R) ≅ Spec (.of S))
    (he : e.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap E R)) =
      Spec.map (CommRingCat.ofHom (algebraMap E S))) : R ≃ₐ[E] S := by
  let a := pointSplittingRingEquivOfSpecIso e
  refine { a with commutes' := ?_ }
  have h : CommRingCat.ofHom (algebraMap E R) ≫ CommRingCat.ofHom a.toRingHom =
      CommRingCat.ofHom (algebraMap E S) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    change Spec.map (Spec.preimage e.inv) ≫ _ = _
    rw [Spec.map_preimage]
    exact he
  intro c
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) c

/-- The genuine split cover over E gives the E-algebra splitting of the
actual finite coordinate algebra. The only compatibility is its structural
map, discharged by native configuration projection lemmas. -/
def pointSplittingFiniteCoordinateAlgEquiv
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {D : Scheme.{u}} (q : D ⟶ Spec (.of F)) [IsFinite q] (n : ℕ)
    (e : (∐ fun _ : ULift.{u} (Fin n) ↦ Spec (.of E)) ≅
      pullback q (Spec.map (CommRingCat.ofHom (algebraMap F E))))
    (he : e.hom ≫ pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap F E))) =
      AllCharacteristics.constantCoverToBase (ULift.{u} (Fin n)) (Spec (.of E))) :
    letI := finiteSchemeCoefficientAlgebra q
    (E ⊗[F] Γ(D, ⊤)) ≃ₐ[E] (ULift.{u} (Fin n) → E) := by
  letI := finiteSchemeCoefficientAlgebra q
  let s := asIso (sigmaSpec (fun _ : ULift.{u} (Fin n) ↦ CommRingCat.of E))
  apply pointSplittingAlgEquivOfSpecIso
    ((pointSplittingFinitePullbackTensorIso q).symm ≪≫ e.symm ≪≫ s)
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]
  rw [pointSplittingFinitePullbackTensorIso_hom_base, he]
  rw [AllCharacteristics.constantCoverToBase_spec_factor]
  change s.inv ≫ s.hom ≫ _ = _
  simp

end PfaffianDescent
