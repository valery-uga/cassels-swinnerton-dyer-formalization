import PfaffianDescent.GrassmannianLocalModuli
import PfaffianDescent.GrassmannianSubmoduleBaseChange

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {A B : Type u} [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B) (m n : ℕ)

/-- Extension of coefficients of an actual Grassmannian scheme point. -/
noncomputable def grassmannianAlgebraPointMap (p : GrassmannianAlgebraPoint K A m n) :
    GrassmannianAlgebraPoint K B m n :=
  ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ p.1, by
    rw [Category.assoc, p.2, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact φ.comp_algebraMap⟩

lemma grassmannianAlgebraPointMap_chart (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) A) :
    grassmannianAlgebraPointMap K φ m n (grassmannianChartAlgebraPoint K A m n σ T) =
      grassmannianChartAlgebraPoint K B m n σ (T.map φ) := by
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    (grassmannianChartEvaluation K T ≫ grassmannianChartι K σ) = _
  rw [← Category.assoc, grassmannianChartEvaluation_map]
  rfl

variable [IsLocalRing A] [IsLocalRing B]

/-- The local moduli equivalence is compatible with scalar extension of the actual ambient submodules. -/
theorem grassmannianLocalModuliEquiv_naturality (p : GrassmannianAlgebraPoint K A m n) :
    (grassmannianLocalModuliEquiv K B m n (grassmannianAlgebraPointMap K φ m n p)).toSubmodule =
      grassmannianSubmoduleBaseChange φ.toRingHom (grassmannianLocalModuliEquiv K A m n p).toSubmodule := by
  obtain ⟨⟨σ, T⟩, rfl⟩ := grassmannianChartAlgebraPoint_surjective K A m n p
  rw [grassmannianAlgebraPointMap_chart, grassmannianLocalModuliEquiv_chart,
    grassmannianLocalModuliEquiv_chart]
  exact (grassmannianChartSubmodule_baseChange φ.toRingHom σ T).symm

end
end PfaffianDescent
