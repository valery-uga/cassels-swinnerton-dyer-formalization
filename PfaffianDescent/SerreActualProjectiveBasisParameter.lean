import PfaffianDescent.ProjectiveFrameNaturality
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceParameterRankChartMap
import Mathlib.LinearAlgebra.Matrix.Basis

/-! An actual basis of global sections gives an actual projective parameter
isomorphism. The matrix explicitly converts it to the canonical basis used
by the universal section family. -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open scoped Matrix
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def projectiveBasisCoordinateIso
    {K : Type u} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {n : ℕ} (b c : Basis (Fin n) K V) :
    projectiveFrameCoordinateSpace (R := K) n ≅
      projectiveFrameCoordinateSpace (R := K) n where
  hom := projectiveFrameCoordinateMap (c.toMatrix b) (b.toMatrix c)
    (b.toMatrix_mul_toMatrix_flip c)
  inv := projectiveFrameCoordinateMap (b.toMatrix c) (c.toMatrix b)
    (c.toMatrix_mul_toMatrix_flip b)
  hom_inv_id := projectiveFrameCoordinateMap_comp (b.toMatrix c) (c.toMatrix b)
    (c.toMatrix_mul_toMatrix_flip b) (b.toMatrix_mul_toMatrix_flip c)
  inv_hom_id := projectiveFrameCoordinateMap_comp (c.toMatrix b) (b.toMatrix c)
    (b.toMatrix_mul_toMatrix_flip c) (c.toMatrix_mul_toMatrix_flip b)

@[reassoc]
theorem projectiveBasisCoordinateIso_toBase
    {K : Type u} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {n : ℕ} (b c : Basis (Fin n) K V) :
    (projectiveBasisCoordinateIso b c).hom ≫
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
    toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) :=
  projectiveFrameCoordinateMap_toBase (c.toMatrix b) (b.toMatrix c)
    (b.toMatrix_mul_toMatrix_flip c)

/-- The matrix used by the actual projective isomorphism is the change of
coordinates of the same actual section. -/
theorem projectiveBasisCoordinateIso_section_coordinates
    {K : Type u} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {n : ℕ} (b c : Basis (Fin n) K V) (s : V) :
    c.toMatrix b *ᵥ b.repr s = c.repr s :=
  Basis.toMatrix_mulVec_repr b c s

theorem projectiveBasisCoordinateIso_sum_coordinates
    {K : Type u} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {n : ℕ} (b c : Basis (Fin n) K V) (v : Fin n → K) :
    c.toMatrix b *ᵥ v = c.repr (∑ i, v i • b i) := by
  simpa only [Basis.repr_sum_self] using
    projectiveBasisCoordinateIso_section_coordinates b c (∑ i, v i • b i)

def serreActualProjectiveBasisParameterIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver base M) = 9)
    (b : Basis (Fin 9) K (SchemeModuleGlobalSectionsOver base M)) :
    scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)) ≅
      schemeModuleGlobalSectionsProjectiveParameters base M :=
  (projectiveBasisCoordinateIso b (finBasisOfFinrankEq K _ h9)).trans
    (serreIncidenceNineParameterIso base M h9).symm

@[reassoc]
theorem serreActualProjectiveBasisParameterIso_toBase
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver base M) = 9)
    (b : Basis (Fin 9) K (SchemeModuleGlobalSectionsOver base M)) :
    (serreActualProjectiveBasisParameterIso base M h9 b).hom ≫
      schemeModuleGlobalSectionsProjectiveParametersToBase base M =
    toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)) := by
  change ((projectiveBasisCoordinateIso b (finBasisOfFinrankEq K _ h9)).hom ≫
    (serreIncidenceNineParameterIso base M h9).inv) ≫ _ = _
  rw [Category.assoc, ← serreIncidenceNineParameterIso_toBase base M h9,
    Iso.inv_hom_id_assoc, projectiveBasisCoordinateIso_toBase]

end PfaffianDescent
