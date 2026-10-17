import PfaffianDescent.IncidenceProjectiveKernels
import PfaffianDescent.IncidenceAlgebraPoints
import PfaffianDescent.IncidenceEmbedding
import PfaffianDescent.AmbientAlternatingBaseChange
import PfaffianDescent.PolynomialSchemePoints

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable {R : Type*} [CommRing R]

/-- Write an actual isotropic triple in the graph coordinates of a quotient chart. -/
noncomputable def incidenceChartPointOfForms
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) R)
    (B : Fin 3 → AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)))
    (hB : ∀ k, alternatingRestriction R _ (grassmannianChartSubmodule R σ T) (B k) = 0) :
    IncidenceGraphPoints R :=
  ⟨Matrix.toLin' T, fun k =>
    (alternatingKernelTransportEquiv (graphCoordinatePermutation R σ.symm)
      (Matrix.toLin' T).graph (grassmannianChartSubmodule R σ T) rfl).symm ⟨B k, hB k⟩⟩

lemma incidenceChartPointOfForms_original
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) R)
    (B : Fin 3 → AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)))
    (hB : ∀ k, alternatingRestriction R _ (grassmannianChartSubmodule R σ T) (B k) = 0)
    (k : Fin 3) : incidenceOriginalForm σ (incidenceChartPointOfForms σ T B hB) k = B k :=
  (alternatingTransport (graphCoordinatePermutation R σ.symm)).apply_symm_apply (B k)

/-- The ambient coefficient tuple of three actual alternating forms. -/
noncomputable def alternatingTripleCoordinates
    (B : Fin 3 → AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R))) : AlternatingTripleIndex → R :=
  fun i => alternatingCoordinates (incidenceAmbientBasis R) (B i.1) i.2

lemma alternatingTripleCoordinates_injective : Function.Injective (alternatingTripleCoordinates (R := R)) := by
  intro B C h
  funext k
  apply (alternatingCoordinates (incidenceAmbientBasis R)).injective
  funext s
  exact congrFun h (k, s)

lemma alternatingTripleCoordinates_map {S : Type*} [CommRing S] (φ : R →+* S)
    (B : Fin 3 → AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R))) :
    alternatingTripleCoordinates (fun k => ambientAlternatingMap φ (B k)) =
      φ ∘ alternatingTripleCoordinates B := by
  funext i
  exact congrFun (ambientAlternatingMap_coordinates φ (B i.1)) i.2

end
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A]

/-- Evaluation in the affine scheme of triples, using actual alternating forms. -/
noncomputable def alternatingTripleEvaluation
    (B : Fin 3 → AlternatingTwoForms A ((Fin 3 → A) × (Fin 3 → A))) :
    Spec (.of A) ⟶ alternatingTripleScheme K :=
  polynomialSchemeEvaluation K AlternatingTripleIndex (alternatingTripleCoordinates B)

lemma alternatingTripleEvaluation_toBase
    (B : Fin 3 → AlternatingTwoForms A ((Fin 3 → A) × (Fin 3 → A))) :
    alternatingTripleEvaluation K B ≫ alternatingTripleToBase K =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) :=
  polynomialSchemeEvaluation_toBase K _ _

lemma alternatingTripleEvaluation_injective : Function.Injective (alternatingTripleEvaluation K (A := A)) := by
  intro B C h
  apply alternatingTripleCoordinates_injective
  have he := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  funext i
  exact (MvPolynomial.aeval_X (alternatingTripleCoordinates B) i).symm.trans
    ((RingHom.congr_fun he (MvPolynomial.X i)).trans (MvPolynomial.aeval_X _ _))

lemma alternatingTripleEvaluation_map {D : Type u} [CommRing D] [Algebra K D]
    (φ : A →ₐ[K] D) (B : Fin 3 → AlternatingTwoForms A ((Fin 3 → A) × (Fin 3 → A))) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ alternatingTripleEvaluation K B =
      alternatingTripleEvaluation K (fun k => ambientAlternatingMap φ.toRingHom (B k)) := by
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) (alternatingTripleCoordinates B)).toRingHom) = _
  rw [← Spec.map_comp]
  have he : φ.comp (MvPolynomial.aeval (R := K) (alternatingTripleCoordinates B)) =
      MvPolynomial.aeval (R := K) (alternatingTripleCoordinates (fun k => ambientAlternatingMap φ.toRingHom (B k))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, alternatingTripleCoordinates_map]
    rfl
  exact congrArg (fun ψ : AlternatingTripleRing K →ₐ[K] D => Spec.map (CommRingCat.ofHom ψ.toRingHom)) he

/-- A common-isotropic triple gives a scheme point on every chart representing its submodule. -/
noncomputable def incidenceIsotropicChartMorphism
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) A)
    (B : Fin 3 → AlternatingTwoForms A ((Fin 3 → A) × (Fin 3 → A)))
    (hB : ∀ k, alternatingRestriction A _ (grassmannianChartSubmodule A σ T) (B k) = 0) :
    Spec (.of A) ⟶ incidenceScheme K :=
  incidenceChartEvaluation K (incidenceChartPointOfForms σ T B hB) ≫ incidenceChartι K σ

lemma incidenceIsotropicChartMorphism_toGrassmannian
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) A)
    (B : Fin 3 → AlternatingTwoForms A ((Fin 3 → A) × (Fin 3 → A)))
    (hB : ∀ k, alternatingRestriction A _ (grassmannianChartSubmodule A σ T) (B k) = 0) :
    incidenceIsotropicChartMorphism K σ T B hB ≫ incidenceToGrassmannian K =
      (grassmannianChartAlgebraPoint K A 3 3 σ T).1 := by
  rw [incidenceIsotropicChartMorphism, Category.assoc, incidenceChartι_toGrassmannian,
    ← Category.assoc, incidenceChartEvaluation_toGraph]
  change grassmannianChartEvaluation K (LinearMap.toMatrix' (Matrix.toLin' T)) ≫ grassmannianChartι K σ = _
  rw [LinearMap.toMatrix'_toLin']
  rfl

lemma incidenceIsotropicChartMorphism_toTriples
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) A)
    (B : Fin 3 → AlternatingTwoForms A ((Fin 3 → A) × (Fin 3 → A)))
    (hB : ∀ k, alternatingRestriction A _ (grassmannianChartSubmodule A σ T) (B k) = 0) :
    incidenceIsotropicChartMorphism K σ T B hB ≫ incidenceToTriples K =
      alternatingTripleEvaluation K B := by
  rw [incidenceIsotropicChartMorphism, Category.assoc, incidenceChartι_toTriples,
    incidenceChartEvaluation_toTriples]
  have he : incidenceOriginalCoefficients σ (incidenceChartPointOfForms σ T B hB) =
      alternatingTripleCoordinates B := by
    funext i
    exact congrArg (fun C => alternatingCoordinates (incidenceAmbientBasis A) C i.2)
      (incidenceChartPointOfForms_original σ T B hB i.1)
  rw [he]
  rfl

lemma incidence_hom_ext {X : Scheme.{u}} (f g : X ⟶ incidenceScheme K)
    (hW : f ≫ incidenceToGrassmannian K = g ≫ incidenceToGrassmannian K)
    (hB : f ≫ incidenceToTriples K = g ≫ incidenceToTriples K) : f = g := by
  apply (cancel_mono (incidenceEmbedding K)).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc, incidenceEmbedding_fst] using hW
  · simpa only [Category.assoc, incidenceEmbedding_snd] using hB

end
end PfaffianDescent
