import PfaffianDescent.CubicClosedPointSerrePointSplittingAlgebra
import PfaffianDescent.CubicClosedPointSerrePointSplittingAffineTensorCoordinate

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable {D : Scheme.{u}} (q : D ⟶ Spec (.of F)) [IsFinite q] (n : ℕ)
variable (e : (∐ fun _ : ULift.{u} (Fin n) ↦ Spec (.of E)) ≅
  pullback q (Spec.map (CommRingCat.ofHom (algebraMap F E))))
variable (he : e.hom ≫ pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap F E))) =
  AllCharacteristics.constantCoverToBase (ULift.{u} (Fin n)) (Spec (.of E)))

def pointSplittingFiniteComponentPoint (i : ULift.{u} (Fin n)) : Spec (.of E) ⟶ D :=
  Sigma.ι (fun _ : ULift.{u} (Fin n) ↦ Spec (.of E)) i ≫ e.hom ≫ pullback.fst _ _

include he in
theorem pointSplittingFiniteComponentPoint_toBase (i : ULift.{u} (Fin n)) :
    pointSplittingFiniteComponentPoint q n e i ≫ q =
    Spec.map (CommRingCat.ofHom (algebraMap F E)) := by
  unfold pointSplittingFiniteComponentPoint
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.hom, he]
  simp [AllCharacteristics.constantCoverToBase]

include e he in
def pointSplittingFiniteComponentAlgHom (i : ULift.{u} (Fin n)) :
    letI := finiteSchemeCoefficientAlgebra q
    Γ(D, ⊤) →ₐ[F] E := by
  letI := finiteSchemeCoefficientAlgebra q
  letI : IsAffine D := isAffine_of_isAffineHom q
  let δ := pointSplittingFiniteComponentPoint q n e i
  let a : Γ(D, ⊤) →+* E := (Spec.preimage (δ ≫ D.isoSpec.hom)).hom
  refine { a with commutes' := ?_ }
  have h : CommRingCat.ofHom (algebraMap F Γ(D, ⊤)) ≫ CommRingCat.ofHom a =
      CommRingCat.ofHom (algebraMap F E) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    change Spec.map (Spec.preimage (δ ≫ D.isoSpec.hom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap F Γ(D, ⊤))) = _
    rw [Spec.map_preimage, finiteSchemeCoefficient_spec q]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact pointSplittingFiniteComponentPoint_toBase q n e he i
  intro c
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) c

theorem pointSplittingFiniteComponentAlgHom_spec [IsAffine D]
    (i : ULift.{u} (Fin n)) :
    letI := finiteSchemeCoefficientAlgebra q
    Spec.map (CommRingCat.ofHom (pointSplittingFiniteComponentAlgHom q n e he i).toRingHom) =
      pointSplittingFiniteComponentPoint q n e i ≫ D.isoSpec.hom := by
  letI := finiteSchemeCoefficientAlgebra q
  exact Spec.map_preimage _

/-- The coefficient-algebra isomorphism's spectrum map is the literal
composite of the split cover with the canonical affine tensor presentation. -/
theorem pointSplittingFiniteCoordinateAlgEquiv_spec :
    letI := finiteSchemeCoefficientAlgebra q
    Spec.map (CommRingCat.ofHom (pointSplittingFiniteCoordinateAlgEquiv q n e he).toRingHom) =
    (asIso (sigmaSpec (fun _ : ULift.{u} (Fin n) ↦ CommRingCat.of E))).inv ≫
      e.hom ≫ (pointSplittingFinitePullbackTensorIso q).hom := by
  letI := finiteSchemeCoefficientAlgebra q
  exact Spec.map_preimage _

/-- The split-coordinate map on a pure tensor uses the SAME actual component
of the actual finite scheme, not a replacement family of algebra embeddings. -/
theorem pointSplittingFiniteCoordinateAlgEquiv_one_tmul
    (a : Γ(D, ⊤)) (i : ULift.{u} (Fin n)) :
    letI := finiteSchemeCoefficientAlgebra q
    pointSplittingFiniteCoordinateAlgEquiv q n e he (1 ⊗ₜ[F] a) i =
      pointSplittingFiniteComponentAlgHom q n e he i a := by
  letI := finiteSchemeCoefficientAlgebra q
  letI : IsAffine D := isAffine_of_isAffineHom q
  let ρ := pointSplittingFiniteCoordinateAlgEquiv q n e he
  let ev := Pi.evalRingHom (fun _ : ULift.{u} (Fin n) => E) i
  let inc : Γ(D, ⊤) →+* E ⊗[F] Γ(D, ⊤) := Algebra.TensorProduct.includeRight.toRingHom
  have h : Spec.map (CommRingCat.ofHom (ev.comp (ρ.toRingHom.comp inc))) =
      pointSplittingFiniteComponentPoint q n e i ≫ D.isoSpec.hom := by
    rw [show CommRingCat.ofHom (ev.comp (ρ.toRingHom.comp inc)) =
      CommRingCat.ofHom inc ≫ CommRingCat.ofHom ρ.toRingHom ≫ CommRingCat.ofHom ev from rfl]
    rw [Spec.map_comp, Spec.map_comp]
    rw [pointSplittingFiniteCoordinateAlgEquiv_spec]
    rw [← ι_sigmaSpec (fun _ : ULift.{u} (Fin n) => CommRingCat.of E) i]
    simp only [Category.assoc, asIso_inv, IsIso.hom_inv_id_assoc]
    rw [pointSplittingFinitePullbackTensorIso_hom_coordinate]
    rfl
  have hp := pointSplittingFiniteComponentAlgHom_spec q n e he i
  rw [← hp] at h
  have hr := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa [ρ, ev, inc, pointSplittingFiniteComponentAlgHom] using DFunLike.congr_fun hr a

end PfaffianDescent
