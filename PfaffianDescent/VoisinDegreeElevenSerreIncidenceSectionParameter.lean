import PfaffianDescent.VoisinFixedLinearSystemUniversalChart

/-! # Actual section parameters from the actual global section basis -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- A nonzero actual bundle global section has a literal normalized
projective parameter over any field extension. Its coordinates are computed
from the actual finite basis, rather than supplied as a parameter witness. -/
theorem serreIncidenceSection_exists_native_parameter
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (s : SchemeModuleGlobalSectionsOver base M) (hs : s ≠ 0) :
    let V := SchemeModuleGlobalSectionsOver base M
    let c : Fin (Module.finrank K V) → L := fun i =>
      algebraMap K L ((Module.finBasis K V).repr s i)
    ∃ (j : Fin (Module.finrank K V))
      (b : finiteDimensionalProjectiveChartRing K V j →+* L)
      (t : Spec (.of L) ⟶ schemeModuleGlobalSectionsProjectiveParameters base M),
      c j ≠ 0 ∧
      b.comp (chartBaseMap (finiteDimensionalProjectiveIdeal K V) j) = algebraMap K L ∧
      Spec.map (CommRingCat.ofHom b) ≫ finiteDimensionalProjectiveChartι K V j = t ∧
      (∀ i, b (chartCoordinate (finiteDimensionalProjectiveIdeal K V) j i) =
        (c j)⁻¹ * c i) ∧
      t ≫ schemeModuleGlobalSectionsProjectiveParametersToBase base M =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  dsimp only
  let V := SchemeModuleGlobalSectionsOver base M
  let c : Fin (Module.finrank K V) → L := fun i =>
    algebraMap K L ((Module.finBasis K V).repr s i)
  have hc : c ≠ 0 := by
    intro h
    apply hs
    apply (Module.finBasis K V).repr.injective
    ext i
    have hi := congrFun h i
    change algebraMap K L ((Module.finBasis K V).repr s i) = 0 at hi
    have hz := (algebraMap K L).injective (hi.trans (map_zero _).symm)
    simpa using hz
  exact exists_finiteDimensionalProjectiveParameter_normalized_of_ne_zero c hc

end PfaffianDescent
