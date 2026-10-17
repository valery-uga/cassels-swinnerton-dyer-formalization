import PfaffianDescent.SchemeAffineFunctions

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] (ι : Type) {A : Type u} [CommRing A] [Algebra K A]

noncomputable def polynomialSchemeEvaluation (a : ι → A) :
    Spec (.of A) ⟶ Spec (.of (MvPolynomial ι K)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) a).toRingHom)

lemma polynomialSchemeEvaluation_toBase (a : ι → A) :
    polynomialSchemeEvaluation K ι a ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial ι K))) =
        Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
  change Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) a).toRingHom) ≫ _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (MvPolynomial.aeval (R := K) a).comp_algebraMap

/-- Every affine-space point over the base is evaluation at its coordinate tuple. -/
lemma polynomialSchemeEvaluation_exists (f : Spec (.of A) ⟶ Spec (.of (MvPolynomial ι K)))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial ι K))) =
      Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    ∃ a : ι → A, polynomialSchemeEvaluation K ι a = f := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective f
  have hC : φ.hom.comp (algebraMap K (MvPolynomial ι K)) = algebraMap K A := by
    have hb : Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial ι K)) ≫ φ) =
        Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
      rw [Spec.map_comp]
      exact (congrArg (fun f => f ≫ Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial ι K)))) hφ).trans hf
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hb)
  let a : ι → A := fun i => φ.hom (MvPolynomial.X i)
  refine ⟨a, ?_⟩
  have he : (MvPolynomial.aeval (R := K) a).toRingHom = φ.hom := by
    apply MvPolynomial.ringHom_ext
    · intro k
      change MvPolynomial.aeval _ (MvPolynomial.C k) = φ.hom (MvPolynomial.C k)
      rw [MvPolynomial.aeval_C]
      exact (RingHom.congr_fun hC k).symm
    · intro i
      exact MvPolynomial.aeval_X _ _
  exact (congrArg (fun f => Spec.map (CommRingCat.ofHom f)) he).trans hφ

end
end PfaffianDescent
