import PfaffianDescent.IncidencePointNaturality
import PfaffianDescent.GrassmannianOverlapScheme
import Mathlib.Algebra.MvPolynomial.Rename

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K]

/-- The incidence overlap is defined by the same graph minor as its Grassmannian base. -/
noncomputable def incidenceOverlapPolynomial (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) : IncidenceGraphRing K :=
  MvPolynomial.rename (Sum.inl : Fin 3 × Fin 3 → IncidenceGraphIndex) (grassmannianOverlapPolynomial K σ)

lemma incidenceOverlapPolynomial_eval {A : Type u} [CommRing A] [Algebra K A]
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (p : IncidenceGraphPoints A) :
    MvPolynomial.aeval (incidenceGraphPointCoordinates A p) (incidenceOverlapPolynomial K σ) =
      graphOverlapDeterminant (graphCoordinatePermutation A σ) p.1 := by
  rw [incidenceOverlapPolynomial, MvPolynomial.aeval_rename]
  have hc : incidenceGraphPointCoordinates A p ∘ Sum.inl =
      fun ij : Fin 3 × Fin 3 => LinearMap.toMatrix' p.1 ij.1 ij.2 := by
    funext ij
    rfl
  rw [hc]
  have h := grassmannianOverlapPolynomial_eval K σ (LinearMap.toMatrix' p.1)
  simpa only [Matrix.toLin'_toMatrix'] using h

abbrev IncidenceOverlapRing (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :=
  Localization.Away (incidenceOverlapPolynomial K σ)

noncomputable def incidenceOverlapScheme (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) : Scheme.{u} :=
  Spec (.of (IncidenceOverlapRing K σ))

noncomputable def incidenceOverlapι (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceOverlapScheme K σ ⟶ incidenceGraphScheme K :=
  Spec.map (CommRingCat.ofHom (algebraMap (IncidenceGraphRing K) (IncidenceOverlapRing K σ)))

instance incidenceOverlapι_isOpenImmersion (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    IsOpenImmersion (incidenceOverlapι K σ) := by
  exact inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (IncidenceGraphRing K) (IncidenceOverlapRing K σ)))))

lemma incidenceOverlapι_opensRange (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    (incidenceOverlapι K σ).opensRange = PrimeSpectrum.basicOpen (incidenceOverlapPolynomial K σ) :=
  Scheme.Hom.opensRange_localizationAway (R := .of (IncidenceGraphRing K)) _

/-- The universal common-isotropic graph and triple over the overlap ring. -/
noncomputable def incidenceOverlapUniversal (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    IncidenceGraphPoints (IncidenceOverlapRing K σ) :=
  incidenceGraphPointMap (algebraMap (IncidenceGraphRing K) (IncidenceOverlapRing K σ))
    (incidenceGraphUniversal K)

lemma incidenceOverlapUniversal_coordinates (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceGraphPointCoordinates (IncidenceOverlapRing K σ) (incidenceOverlapUniversal K σ) =
      fun j => algebraMap (IncidenceGraphRing K) (IncidenceOverlapRing K σ) (MvPolynomial.X j) := by
  rw [incidenceOverlapUniversal, incidenceGraphPointMap_coordinates, incidenceGraphUniversal_coordinates]
  rfl

lemma incidenceOverlapUniversal_aeval (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    MvPolynomial.aeval
      (incidenceGraphPointCoordinates (IncidenceOverlapRing K σ) (incidenceOverlapUniversal K σ)) =
      Algebra.algHom K (IncidenceGraphRing K) (IncidenceOverlapRing K σ) := by
  rw [incidenceOverlapUniversal_coordinates]
  apply MvPolynomial.algHom_ext
  intro j
  exact MvPolynomial.aeval_X _ _

lemma incidenceOverlapUniversal_bijective (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    Function.Bijective (graphTransitionFirst (graphCoordinatePermutation (IncidenceOverlapRing K σ) σ)
      (incidenceOverlapUniversal K σ).1) := by
  apply (graphOverlapDeterminant_isUnit_iff _ _).mp
  rw [← incidenceOverlapPolynomial_eval K σ, incidenceOverlapUniversal_aeval]
  exact IsLocalization.Away.algebraMap_isUnit (incidenceOverlapPolynomial K σ)

/-- The complete normalized incidence point, with transported forms, on the other chart. -/
noncomputable def incidenceOverlapTransitionPoint (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    IncidenceGraphPoints (IncidenceOverlapRing K σ) :=
  incidencePointTransition (graphCoordinatePermutation (IncidenceOverlapRing K σ) σ)
    (incidenceOverlapUniversal K σ) (incidenceOverlapUniversal_bijective K σ)

noncomputable def incidenceOverlapLift {A : Type u} [CommRing A] [Algebra K A]
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (p : IncidenceGraphPoints A)
    (hp : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation A σ) p.1)) :
    IncidenceOverlapRing K σ →ₐ[K] A :=
  IsLocalization.Away.liftAlgHom (incidenceOverlapPolynomial K σ)
    ((incidenceOverlapPolynomial_eval K σ p).symm ▸ (graphOverlapDeterminant_isUnit_iff _ _).mpr hp)

lemma incidenceOverlapLift_apply {A : Type u} [CommRing A] [Algebra K A]
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (p : IncidenceGraphPoints A)
    (hp : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation A σ) p.1))
    (q : IncidenceGraphRing K) :
    incidenceOverlapLift K σ p hp (algebraMap _ _ q) =
      MvPolynomial.aeval (incidenceGraphPointCoordinates A p) q :=
  IsLocalization.Away.lift_eq _
    ((incidenceOverlapPolynomial_eval K σ p).symm ▸ (graphOverlapDeterminant_isUnit_iff _ _).mpr hp) q

lemma incidenceOverlapLift_unique {A : Type u} [CommRing A] [Algebra K A]
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (p : IncidenceGraphPoints A)
    (hp : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation A σ) p.1))
    (h : IncidenceOverlapRing K σ →ₐ[K] A)
    (hh : ∀ j, h (algebraMap (IncidenceGraphRing K) (IncidenceOverlapRing K σ) (MvPolynomial.X j)) =
      incidenceGraphPointCoordinates A p j) :
    h = incidenceOverlapLift K σ p hp := by
  apply IsLocalization.algHom_ext (Submonoid.powers (incidenceOverlapPolynomial K σ))
  apply MvPolynomial.algHom_ext
  intro j
  change h (algebraMap _ _ (MvPolynomial.X j)) = incidenceOverlapLift K σ p hp (algebraMap _ _ (MvPolynomial.X j))
  rw [hh, incidenceOverlapLift_apply, MvPolynomial.aeval_X]

end
end PfaffianDescent
