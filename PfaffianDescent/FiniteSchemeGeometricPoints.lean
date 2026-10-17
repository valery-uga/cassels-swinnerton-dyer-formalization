import PfaffianDescent.FiniteSchemeAlgebra

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of K)) [IsFinite f] [IsAffine Z]

/-- An evaluation of the actual global-section algebra defines a geometric
scheme point, with its coefficient field retained. -/
noncomputable def finiteSchemeGeometricPoint :
    letI := finiteSchemeCoefficientAlgebra f
    (Γ(Z, ⊤) →ₐ[K] L) → (Spec (.of L) ⟶ Z) := by
  letI := finiteSchemeCoefficientAlgebra f
  exact fun ev => Spec.map (CommRingCat.ofHom ev.toRingHom) ≫ Z.isoSpec.inv

lemma finiteSchemeGeometricPoint_over_base :
    letI := finiteSchemeCoefficientAlgebra f
    ∀ ev : Γ(Z, ⊤) →ₐ[K] L,
      finiteSchemeGeometricPoint f ev ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  letI := finiteSchemeCoefficientAlgebra f
  intro ev
  change (Spec.map (CommRingCat.ofHom ev.toRingHom) ≫ Z.isoSpec.inv) ≫ f = _
  rw [Category.assoc, ← finiteSchemeCoefficient_spec f, ← Spec.map_comp]
  congr 1
  ext a
  exact ev.commutes a

lemma finiteSchemeGeometricPoint_injective :
    letI := finiteSchemeCoefficientAlgebra f
    Function.Injective (finiteSchemeGeometricPoint (L := L) f) := by
  letI := finiteSchemeCoefficientAlgebra f
  intro ev₁ ev₂ h
  change Spec.map (CommRingCat.ofHom ev₁.toRingHom) ≫ Z.isoSpec.inv =
    Spec.map (CommRingCat.ofHom ev₂.toRingHom) ≫ Z.isoSpec.inv at h
  have he := Spec.map_injective ((cancel_mono Z.isoSpec.inv).mp h)
  ext a
  exact congrArg (fun g => g a) he

end
end PfaffianDescent
