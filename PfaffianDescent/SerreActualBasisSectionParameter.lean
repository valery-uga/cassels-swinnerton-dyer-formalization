import PfaffianDescent.SerreActualProjectiveBasisParameter
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSectionParameter

/-! A section specified in a transported basis has a literal parameter in
the canonical global-section projective space. The normalized coordinates
are calculated by the actual basis-change matrix. -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open scoped Matrix
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreActualBasisSection_exists_native_parameter
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (b : Basis (Fin 9) K (SchemeModuleGlobalSectionsOver base M))
    (v : Fin 9 → K) (hv : v ≠ 0) :
    let V := SchemeModuleGlobalSectionsOver base M
    let c : Fin (finrank K V) → L := fun i =>
      algebraMap K L (((finBasis K V).toMatrix b *ᵥ v) i)
    ∃ (j : Fin (finrank K V))
      (f : finiteDimensionalProjectiveChartRing K V j →+* L)
      (t : Spec (.of L) ⟶ schemeModuleGlobalSectionsProjectiveParameters base M),
      c j ≠ 0 ∧
      f.comp (chartBaseMap (finiteDimensionalProjectiveIdeal K V) j) = algebraMap K L ∧
      Spec.map (CommRingCat.ofHom f) ≫ finiteDimensionalProjectiveChartι K V j = t ∧
      (∀ i, f (chartCoordinate (finiteDimensionalProjectiveIdeal K V) j i) =
        (c j)⁻¹ * c i) ∧
      t ≫ schemeModuleGlobalSectionsProjectiveParametersToBase base M =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  let V := SchemeModuleGlobalSectionsOver base M
  let s : V := ∑ i, v i • b i
  have hs : s ≠ 0 := by
    intro h
    apply hv
    calc
      v = (b.repr s : Fin 9 → K) := (Basis.repr_sum_self b v).symm
      _ = 0 := by rw [h]; simp
  have hc : (fun i : Fin (finrank K V) =>
      algebraMap K L (((finBasis K V).toMatrix b *ᵥ v) i)) =
      fun i => algebraMap K L ((finBasis K V).repr s i) := by
    funext i
    apply congrArg (algebraMap K L)
    have h := Basis.toMatrix_mulVec_repr b (finBasis K V) s
    rw [show (b.repr s : Fin 9 → K) = v from Basis.repr_sum_self b v] at h
    exact congrFun h i
  obtain ⟨j, f, t, hj, hb, hft, hcoordinates, ht⟩ :=
    serreIncidenceSection_exists_native_parameter (L := L) base M s hs
  refine ⟨j, f, t, ?_, hb, hft, ?_, ht⟩
  · intro hz
    apply hj
    exact (congrFun hc j).symm.trans hz
  · intro i
    exact (hcoordinates i).trans (congrArg₂ (fun a b : L => a⁻¹ * b)
      (congrFun hc j).symm (congrFun hc i).symm)

/-- Reconstructing the normalized canonical section gives exactly a
nonzero scalar multiple of the section specified in the original basis. -/
theorem serreActualBasisSection_normalized_section
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (b : Basis (Fin 9) K (SchemeModuleGlobalSectionsOver base M))
    (v : Fin 9 → K) (j : Fin (finrank K (SchemeModuleGlobalSectionsOver base M))) :
    let V := SchemeModuleGlobalSectionsOver base M
    let c := (finBasis K V).toMatrix b *ᵥ v
    ∑ i, ((c j)⁻¹ * c i) • (finBasis K V) i =
      (c j)⁻¹ • (∑ i, v i • b i) := by
  dsimp only
  let s := ∑ i, v i • b i
  have hc : (finBasis K (SchemeModuleGlobalSectionsOver base M)).toMatrix b *ᵥ v =
      (finBasis K (SchemeModuleGlobalSectionsOver base M)).repr s := by
    have h := Basis.toMatrix_mulVec_repr b
      (finBasis K (SchemeModuleGlobalSectionsOver base M)) s
    rw [show (b.repr s : Fin 9 → K) = v from Basis.repr_sum_self b v] at h
    exact h
  rw [hc]
  simp only [mul_smul, ← Finset.smul_sum, Basis.sum_repr]
  rfl

end PfaffianDescent
