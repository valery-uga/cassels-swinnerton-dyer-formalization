import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGlobalSectionsFieldFrame

/-! # Literal field-extended section coefficients in the native pulled frame -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceGlobalSectionsFieldBasis_repr_tmul
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} [CompactSpace X] {N : X.Modules}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (a : L) (s : SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))
    (i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base
      (show X.Modules from e.E)))) :
    (serreIncidenceGlobalSectionsFieldBasis (L := L) base e C).repr
      (schemeModuleGlobalSectionsFieldBaseChangeLinearMap (L := L) base
        (show X.Modules from e.E) (a ⊗ₜ[K] s)) i =
      algebraMap K L ((Module.finBasis K
        (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))).repr s i) * a := by
  let f := serreIncidenceGlobalSectionsFieldFrame (L := L) base e C
  change ((Module.finBasis K (SchemeModuleGlobalSectionsOver base
    (show X.Modules from e.E))).baseChange L).repr (f.symm (f (a ⊗ₜ[K] s))) i = _
  rw [f.symm_apply_apply, Module.Basis.baseChange_repr_tmul]
  exact Algebra.smul_def _ _

end PfaffianDescent
