import PfaffianDescent.IncidenceGlobalModuli

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable {A D : Type u} [CommRing A] [CommRing D]

/-- Scalar extension of a genuine quotient with its isotropic triple. -/
noncomputable def incidenceQuotientPointMap (φ : A →+* D) (p : IncidenceQuotientPoint A) :
    IncidenceQuotientPoint D :=
  ⟨grassmannianQuotientMap φ p.1,
    fun k => ambientAlternatingKernelMap φ p.1.toSubmodule (p.2 k)⟩

end
section
variable (K : Type u) [CommRing K] {A D : Type u} [CommRing A] [CommRing D]
  [Algebra K A] [Algebra K D]

/-- Precomposition of an incidence point by an arbitrary coefficient homomorphism. -/
noncomputable def incidenceAlgebraPointMap (φ : A →ₐ[K] D) (f : IncidenceAlgebraPoint K A) :
    IncidenceAlgebraPoint K D :=
  ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f.1, by
    rw [Category.assoc, f.2, ← Spec.map_comp]
    exact congrArg (fun ψ : K →+* D => Spec.map (CommRingCat.ofHom ψ)) φ.comp_algebraMap⟩

lemma incidenceQuotientMorphism_naturality (φ : A →ₐ[K] D)
    (p : IncidenceQuotientPoint A) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ incidenceQuotientMorphism K p.1 p.2 =
      incidenceQuotientMorphism K (incidenceQuotientPointMap φ.toRingHom p).1
        (incidenceQuotientPointMap φ.toRingHom p).2 := by
  apply incidence_hom_ext K
  · rw [Category.assoc, incidenceQuotientMorphism_toGrassmannian,
      incidenceQuotientMorphism_toGrassmannian]
    exact grassmannianQuotientMorphism_naturality K p.1 φ
  · rw [Category.assoc, incidenceQuotientMorphism_toTriples,
      incidenceQuotientMorphism_toTriples]
    exact alternatingTripleEvaluation_map K φ (fun k => (p.2 k).1)

lemma incidenceQuotientAlgebraPoint_naturality (φ : A →ₐ[K] D) (p : IncidenceQuotientPoint A) :
    incidenceAlgebraPointMap K φ (incidenceQuotientAlgebraPoint K A p) =
      incidenceQuotientAlgebraPoint K D (incidenceQuotientPointMap φ.toRingHom p) := by
  apply Subtype.ext
  exact incidenceQuotientMorphism_naturality K φ p

/-- The global incidence classification commutes with arbitrary base change, including nonflat maps. -/
theorem incidenceGlobalModuliEquiv_naturality (φ : A →ₐ[K] D) (f : IncidenceAlgebraPoint K A) :
    incidenceGlobalModuliEquiv K D (incidenceAlgebraPointMap K φ f) =
      incidenceQuotientPointMap φ.toRingHom (incidenceGlobalModuliEquiv K A f) := by
  apply incidenceQuotientAlgebraPoint_injective K
  calc
    _ = incidenceAlgebraPointMap K φ f := incidenceGlobalModuliEquiv_inverse K _
    _ = incidenceAlgebraPointMap K φ
        (incidenceQuotientAlgebraPoint K A (incidenceGlobalModuliEquiv K A f)) :=
      congrArg (incidenceAlgebraPointMap K φ) (incidenceGlobalModuliEquiv_inverse K f).symm
    _ = _ := incidenceQuotientAlgebraPoint_naturality K φ _

end
end PfaffianDescent
