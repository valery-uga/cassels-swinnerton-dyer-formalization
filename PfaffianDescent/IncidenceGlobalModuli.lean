import PfaffianDescent.IncidenceSchemeIsotropy

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A]

lemma incidenceQuotientAlgebraPoint_injective :
    Function.Injective (incidenceQuotientAlgebraPoint K A) := by
  rintro ⟨W, B⟩ ⟨Z, C⟩ h
  have hW : W = Z := by
    apply grassmannianQuotientAlgebraPoint_injective K
    apply Subtype.ext
    change grassmannianQuotientMorphism K W = grassmannianQuotientMorphism K Z
    have hh := congrArg (fun p : IncidenceAlgebraPoint K A => p.1 ≫ incidenceToGrassmannian K) h
    change incidenceQuotientMorphism K W B ≫ incidenceToGrassmannian K =
      incidenceQuotientMorphism K Z C ≫ incidenceToGrassmannian K at hh
    simpa only [incidenceQuotientMorphism_toGrassmannian] using hh
  subst Z
  have hB : (fun k => (B k).1) = fun k => (C k).1 := by
    apply alternatingTripleEvaluation_injective K
    have hh := congrArg (fun p : IncidenceAlgebraPoint K A => p.1 ≫ incidenceToTriples K) h
    change incidenceQuotientMorphism K W B ≫ incidenceToTriples K =
      incidenceQuotientMorphism K W C ≫ incidenceToTriples K at hh
    simpa only [incidenceQuotientMorphism_toTriples] using hh
  have hBC : B = C := by
    funext k
    exact Subtype.ext (congrFun hB k)
  subst C
  rfl

/-- Every affine-base incidence point comes from an actual finite projective quotient and isotropic triple. -/
lemma incidenceQuotientAlgebraPoint_surjective :
    Function.Surjective (incidenceQuotientAlgebraPoint K A) := by
  intro f
  let fW : GrassmannianAlgebraPoint K A 3 3 :=
    ⟨f.1 ≫ incidenceToGrassmannian K, by
      rw [Category.assoc, incidenceToGrassmannian_toBase]
      exact f.2⟩
  let W := grassmannianGlobalModuliEquiv K A 3 3 fW
  have hW : f.1 ≫ incidenceToGrassmannian K = grassmannianQuotientMorphism K W :=
    (congrArg Subtype.val (grassmannianSchemeQuotient_point K fW)).symm
  obtain ⟨B, hB⟩ := alternatingTripleEvaluation_exists K (f.1 ≫ incidenceToTriples K) (by
    rw [Category.assoc, incidenceToTriples_toBase]
    exact f.2)
  have hi := incidence_scheme_isotropic K W B f.1 hW hB.symm
  let C : IncidenceQuotientFiber A W := fun k => ⟨B k, hi k⟩
  refine ⟨⟨W, C⟩, ?_⟩
  apply Subtype.ext
  apply incidence_hom_ext K
  · exact (incidenceQuotientMorphism_toGrassmannian K W C).trans hW.symm
  · exact (incidenceQuotientMorphism_toTriples K W C).trans hB

/-- The global incidence scheme represents actual isotropic triples over every coefficient algebra. -/
noncomputable def incidenceGlobalModuliEquiv (A : Type u) [CommRing A] [Algebra K A] :
    IncidenceAlgebraPoint K A ≃ IncidenceQuotientPoint A :=
  (Equiv.ofBijective (incidenceQuotientAlgebraPoint K A)
    ⟨incidenceQuotientAlgebraPoint_injective K, incidenceQuotientAlgebraPoint_surjective K⟩).symm

lemma incidenceGlobalModuliEquiv_point (p : IncidenceQuotientPoint A) :
    incidenceGlobalModuliEquiv K A (incidenceQuotientAlgebraPoint K A p) = p :=
  (incidenceGlobalModuliEquiv K A).apply_symm_apply p

lemma incidenceGlobalModuliEquiv_inverse (f : IncidenceAlgebraPoint K A) :
    incidenceQuotientAlgebraPoint K A (incidenceGlobalModuliEquiv K A f) = f :=
  (incidenceGlobalModuliEquiv K A).symm_apply_apply f

end
end PfaffianDescent
