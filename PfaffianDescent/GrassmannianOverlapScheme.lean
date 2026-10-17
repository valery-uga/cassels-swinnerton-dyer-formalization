import PfaffianDescent.GrassmannianMinor
import Mathlib.AlgebraicGeometry.OpenImmersion

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {m n : ℕ}

noncomputable def grassmannianChartScheme (m n : ℕ) : Scheme.{u} :=
  Spec (.of (GrassmannianChartRing K m n))

/-- The coordinate algebra of a genuine principal-open chart overlap. -/
abbrev GrassmannianOverlapRing (σ : Equiv.Perm (Fin m ⊕ Fin n)) :=
  Localization.Away (grassmannianOverlapPolynomial K σ)

noncomputable def grassmannianOverlapScheme (σ : Equiv.Perm (Fin m ⊕ Fin n)) : Scheme.{u} :=
  Spec (.of (GrassmannianOverlapRing K σ))

noncomputable def grassmannianOverlapι (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianOverlapScheme K σ ⟶ grassmannianChartScheme K m n :=
  Spec.map (CommRingCat.ofHom (algebraMap (GrassmannianChartRing K m n) (GrassmannianOverlapRing K σ)))

instance grassmannianOverlapι_isOpenImmersion (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    IsOpenImmersion (grassmannianOverlapι K σ) := by
  exact inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (GrassmannianChartRing K m n) (GrassmannianOverlapRing K σ)))))

lemma grassmannianOverlapι_opensRange (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    (grassmannianOverlapι K σ).opensRange =
      PrimeSpectrum.basicOpen (grassmannianOverlapPolynomial K σ) :=
  Scheme.Hom.opensRange_localizationAway (R := .of (GrassmannianChartRing K m n)) _

/-- The universal graph entries in the localized chart algebra. -/
noncomputable def grassmannianOverlapUniversalMatrix (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Matrix (Fin n) (Fin m) (GrassmannianOverlapRing K σ) :=
  fun i j => algebraMap (GrassmannianChartRing K m n) (GrassmannianOverlapRing K σ)
    (MvPolynomial.X (i, j))

lemma grassmannianOverlapUniversal_aeval (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    MvPolynomial.aeval (fun ij : Fin n × Fin m => grassmannianOverlapUniversalMatrix K σ ij.1 ij.2) =
      Algebra.algHom K (GrassmannianChartRing K m n) (GrassmannianOverlapRing K σ) := by
  apply MvPolynomial.algHom_ext
  intro ij
  exact MvPolynomial.aeval_X _ _

/-- The universal graph in the localized algebra belongs to both charts. -/
lemma grassmannianOverlapUniversal_bijective (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Function.Bijective (graphTransitionFirst
      (graphCoordinatePermutation (GrassmannianOverlapRing K σ) σ)
      (Matrix.toLin' (grassmannianOverlapUniversalMatrix K σ))) := by
  apply (graphOverlapDeterminant_isUnit_iff _ _).mp
  rw [← grassmannianOverlapPolynomial_eval K σ, grassmannianOverlapUniversal_aeval]
  exact IsLocalization.Away.algebraMap_isUnit (grassmannianOverlapPolynomial K σ)

/-- The normalized matrix in the other chart, over the actual overlap algebra. -/
noncomputable def grassmannianOverlapTransitionMatrix (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Matrix (Fin n) (Fin m) (GrassmannianOverlapRing K σ) :=
  LinearMap.toMatrix' (graphTransition
    (graphCoordinatePermutation (GrassmannianOverlapRing K σ) σ)
    (Matrix.toLin' (grassmannianOverlapUniversalMatrix K σ))
    (grassmannianOverlapUniversal_bijective K σ))

/-- Evaluation of a chart matrix in the overlap lifts to the localization. -/
noncomputable def grassmannianOverlapLift {A : Type u} [CommRing A] [Algebra K A]
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) A)
    (hT : IsUnit (graphOverlapDeterminant (graphCoordinatePermutation A σ) (Matrix.toLin' T))) :
    GrassmannianOverlapRing K σ →ₐ[K] A :=
  IsLocalization.Away.liftAlgHom (grassmannianOverlapPolynomial K σ)
    ((grassmannianOverlapPolynomial_eval K σ T).symm ▸ hT)

lemma grassmannianOverlapLift_apply {A : Type u} [CommRing A] [Algebra K A]
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) A)
    (hT : IsUnit (graphOverlapDeterminant (graphCoordinatePermutation A σ) (Matrix.toLin' T)))
    (p : GrassmannianChartRing K m n) :
    grassmannianOverlapLift K σ T hT (algebraMap _ _ p) =
      MvPolynomial.aeval (fun ij : Fin n × Fin m => T ij.1 ij.2) p :=
  IsLocalization.Away.lift_eq _ ((grassmannianOverlapPolynomial_eval K σ T).symm ▸ hT) p

lemma grassmannianOverlapLift_unique {A : Type u} [CommRing A] [Algebra K A]
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) A)
    (hT : IsUnit (graphOverlapDeterminant (graphCoordinatePermutation A σ) (Matrix.toLin' T)))
    (h : GrassmannianOverlapRing K σ →ₐ[K] A)
    (hh : ∀ i j, h (grassmannianOverlapUniversalMatrix K σ i j) = T i j) :
    h = grassmannianOverlapLift K σ T hT := by
  apply IsLocalization.algHom_ext (Submonoid.powers (grassmannianOverlapPolynomial K σ))
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  change h (grassmannianOverlapUniversalMatrix K σ i j) =
    grassmannianOverlapLift K σ T hT (algebraMap _ _ (MvPolynomial.X (i, j)))
  rw [hh, grassmannianOverlapLift_apply, MvPolynomial.aeval_X]

end
end PfaffianDescent
