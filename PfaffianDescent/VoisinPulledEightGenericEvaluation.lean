import PfaffianDescent.VoisinAffineChartGenericEvaluation

/-! Eight regular sections pulled from affine chart elements specialize
to their actual generic residue-field values. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory

universe u

theorem pulledEightAffineSections_genericFieldValue
    {A F : Type u} [CommRing A] [Field F]
    (U : Scheme.{u})
    (s : Spec (.of F) ⟶ U)
    (t : Fin 8 → (U ⟶ Spec (.of A)))
    (r : Fin 4 → A) :
    let f : Γ(U, ⊤) →+* F :=
      (Scheme.ΓSpecIso (.of F)).hom.hom.comp s.appTop.hom
    let x : Fin 8 → Fin 4 → Γ(U, ⊤) := fun k j =>
      (t k).appTop.hom ((StructureSheaf.globalSectionsIso A).hom (r j))
    ∀ k j, (Spec.preimage (s ≫ t k)).hom (r j) = f (x k j) := by
  dsimp only
  intro k j
  exact specPreimage_comp_apply_eq_appTop_evaluation U s (t k) (r j)

end PfaffianDescent
