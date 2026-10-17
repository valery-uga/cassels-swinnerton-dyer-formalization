import PfaffianDescent.FiniteSchemeAlgebra
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Native finite coefficient algebra comparison from an actual field-spectrum isomorphism -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def serreIncidenceFiniteIsoFieldPointEquiv
    {F R : Type u} [Field F] [Field R] [Algebra F R]
    {D : Scheme.{u}} (q : D ⟶ Spec (.of F)) [IsFinite q]
    (e : Spec (.of R) ≅ D)
    (he : e.hom ≫ q = Spec.map (CommRingCat.ofHom (algebraMap F R))) :
    letI := finiteSchemeCoefficientAlgebra q
    Γ(D, ⊤) ≃ₐ[F] R := by
  letI := finiteSchemeCoefficientAlgebra q
  letI : IsAffine D := isAffine_of_isAffineHom q
  let φ : Γ(D, ⊤) →+* R := (Spec.preimage (e.hom ≫ D.isoSpec.hom)).hom
  have hs : IsIso (Spec.map (CommRingCat.ofHom φ)) := by
    change IsIso (Spec.map (Spec.preimage (e.hom ≫ D.isoSpec.hom)))
    rw [Spec.map_preimage]
    infer_instance
  letI := hs
  letI : IsIso (Scheme.Spec.map (CommRingCat.ofHom φ).op) := hs
  letI : IsIso (CommRingCat.ofHom φ).op :=
    isIso_of_reflects_iso _ Scheme.Spec
  letI : IsIso (CommRingCat.ofHom φ) := isIso_of_op _
  let f : Γ(D, ⊤) →ₐ[F] R :=
    { __ := φ
      commutes' := by
        intro x
        have hcoef : CommRingCat.ofHom (algebraMap F Γ(D, ⊤)) ≫
            CommRingCat.ofHom φ = CommRingCat.ofHom (algebraMap F R) := by
          apply Spec.map_injective
          rw [Spec.map_comp]
          change Spec.map (Spec.preimage (e.hom ≫ D.isoSpec.hom)) ≫
            Spec.map (CommRingCat.ofHom (algebraMap F Γ(D, ⊤))) = _
          rw [Spec.map_preimage, finiteSchemeCoefficient_spec q]
          simpa only [Category.assoc, Iso.hom_inv_id_assoc] using he
        exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcoef) x }
  apply AlgEquiv.ofBijective f
  exact (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom φ)).mp inferInstance

end PfaffianDescent
