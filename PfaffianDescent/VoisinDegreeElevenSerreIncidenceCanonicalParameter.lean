import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSectionParameter
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCanonicalNonzero

/-! # The actual canonical Serre section has actual projective parameters -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Any actual point of the surface makes the actual canonical Serre section
nonzero. Its actual basis coordinates therefore construct an actual
normalized section parameter over any field extension. -/
theorem serreIncidenceCanonicalSection_exists_native_parameter
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of K)) (e : SerreExtensionData X N)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (x : X) :
    let V := SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)
    let c : Fin (Module.finrank K V) → L := fun i =>
      algebraMap K L ((Module.finBasis K V).repr e.inclusion i)
    ∃ (j : Fin (Module.finrank K V))
      (b : finiteDimensionalProjectiveChartRing K V j →+* L)
      (t : Spec (.of L) ⟶ schemeModuleGlobalSectionsProjectiveParameters base
        (show X.Modules from e.E)),
      c j ≠ 0 ∧
      b.comp (chartBaseMap (finiteDimensionalProjectiveIdeal K V) j) = algebraMap K L ∧
      Spec.map (CommRingCat.ofHom b) ≫ finiteDimensionalProjectiveChartι K V j = t ∧
      (∀ i, b (chartCoordinate (finiteDimensionalProjectiveIdeal K V) j i) =
        (c j)⁻¹ * c i) ∧
      t ≫ schemeModuleGlobalSectionsProjectiveParametersToBase base (show X.Modules from e.E) =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  exact serreIncidenceSection_exists_native_parameter base (show X.Modules from e.E)
    e.inclusion (cubicClosedPointSerreFiniteZeroResidual_canonicalGlobalSection_nonzero e x)

end PfaffianDescent
