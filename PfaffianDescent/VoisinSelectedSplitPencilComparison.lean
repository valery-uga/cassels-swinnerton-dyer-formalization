import PfaffianDescent.VoisinQuadraticKernelSpecialization
import PfaffianDescent.VoisinQuadraticKernelBasisIdeal

/-!
# Comparing the selected local frame with the split pencil

The regular open-chart frame specializes to two homogeneous quadrics.
When the selected fiber is the normalized split witness, these quadrics
span the same restriction kernel as the standard split pair.
-/

namespace PfaffianDescent

open MvPolynomial

universe u v

noncomputable def splitQuadraticPencil
    (L : Type v) [Field L] :
    Fin 2 → homogeneousSubmodule (Fin 4) L 2 :=
  ![(⟨(X 1 * X 2 : MvPolynomial (Fin 4) L),
    (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)⟩),
    (⟨(X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L),
      (isHomogeneous_X L 3).mul
        (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
          (isHomogeneous_X L 3))⟩)]

theorem quadraticSelectedOpenBasisSpecialized_span_eq_normalized_kernel
    {R : Type u} [CommRing R]
    {L : Type v} [Field L]
    (m : Fin 8 ↪ AllCharacteristics.UniversalHomogeneous.Monomials (Fin 4) 2)
    (x : Fin 8 → Fin 4 → R)
    (f : R →+* L)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (x k j))).det)
    (y : Fin 8 → Fin 4 → L) (c : Fin 4 → L)
    (hc : ∀ k, (homogeneousLinearForm c).eval (y k) ≠ 0)
    (hfx : ∀ k j, f (x k j) = normalizedVectorInLinearChart c (y k) j)
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := L)
        (fun j k => y k j : Fin 4 → Fin 8 → L) 2))
    (hquad : ∀ k,
      (X 1 * X 2 : MvPolynomial (Fin 4) L).eval (y k) = 0 ∧
      (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval (y k) = 0) :
    Submodule.span L
      (Set.range (quadraticSelectedOpenBasisSpecializedHomogeneous m x f hm)) =
    LinearMap.ker (homogeneousSectionRestriction (K := L)
      (fun j k => normalizedVectorInLinearChart c (y k) j :
        Fin 4 → Fin 8 → L) 2) := by
  obtain ⟨hnormsurj, _⟩ :=
    split_quadrics_span_normalized_eight_evaluation_kernel
      y c hc hsurj hquad
  have hcoords : (fun j k => f (x k j) : Fin 4 → Fin 8 → L) =
      (fun j k => normalizedVectorInLinearChart c (y k) j) := by
    funext j k
    exact hfx k j
  have hsurj' : Function.Surjective
      (homogeneousSectionRestriction (K := L)
        (fun j k => f (x k j) : Fin 4 → Fin 8 → L) 2) := by
    rw [hcoords]
    exact hnormsurj
  have hspan := quadraticSelectedOpenBasisSpecializedHomogeneous_span_eq_kernel
    m x f hm hsurj'
  rw [hcoords] at hspan
  exact hspan

/-- If two independent homogeneous quadrics are the full vanishing pencil
of the selected eight points, the specialized regular frame spans their
pencil after normalization in the common linear chart. -/
theorem quadraticSelectedOpenBasisSpecialized_span_eq_quadratic_pair
    {R : Type u} [CommRing R]
    {L : Type v} [Field L]
    (m : Fin 8 ↪ AllCharacteristics.UniversalHomogeneous.Monomials (Fin 4) 2)
    (x : Fin 8 → Fin 4 → R)
    (f : R →+* L)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (x k j))).det)
    (y : Fin 8 → Fin 4 → L) (c : Fin 4 → L)
    (hc : ∀ k, (homogeneousLinearForm c).eval (y k) ≠ 0)
    (hfx : ∀ k j, f (x k j) = normalizedVectorInLinearChart c (y k) j)
    (q r : MvPolynomial (Fin 4) L)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hlin : LinearIndependent L
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) L 2), ⟨r, hr⟩])
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := L)
        (fun j k => y k j : Fin 4 → Fin 8 → L) 2))
    (hquad : ∀ k, q.eval (y k) = 0 ∧ r.eval (y k) = 0) :
    Submodule.span L
      (Set.range (quadraticSelectedOpenBasisSpecializedHomogeneous m x f hm)) =
        Submodule.span L (Set.range
          (![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) L 2), ⟨r, hr⟩] :
            Fin 2 → homogeneousSubmodule (Fin 4) L 2)) := by
  obtain ⟨hnormsurj, hkernel⟩ :=
    quadrics_span_normalized_eight_evaluation_kernel
      y c hc q r hq hr hlin hsurj hquad
  have hcoords : (fun j k => f (x k j) : Fin 4 → Fin 8 → L) =
      (fun j k => normalizedVectorInLinearChart c (y k) j) := by
    funext j k
    exact hfx k j
  have hsurj' : Function.Surjective
      (homogeneousSectionRestriction (K := L)
        (fun j k => f (x k j) : Fin 4 → Fin 8 → L) 2) := by
    rw [hcoords]
    exact hnormsurj
  have hspan := quadraticSelectedOpenBasisSpecializedHomogeneous_span_eq_kernel
    m x f hm hsurj'
  rw [hcoords] at hspan
  exact hspan.trans hkernel

theorem quadraticSelectedOpenBasisSpecialized_span_eq_split_pencil
    {R : Type u} [CommRing R]
    {L : Type v} [Field L]
    (m : Fin 8 ↪ AllCharacteristics.UniversalHomogeneous.Monomials (Fin 4) 2)
    (x : Fin 8 → Fin 4 → R)
    (f : R →+* L)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (x k j))).det)
    (y : Fin 8 → Fin 4 → L) (c : Fin 4 → L)
    (hc : ∀ k, (homogeneousLinearForm c).eval (y k) ≠ 0)
    (hfx : ∀ k j, f (x k j) = normalizedVectorInLinearChart c (y k) j)
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := L)
        (fun j k => y k j : Fin 4 → Fin 8 → L) 2))
    (hquad : ∀ k,
      (X 1 * X 2 : MvPolynomial (Fin 4) L).eval (y k) = 0 ∧
      (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval (y k) = 0) :
    Submodule.span L
      (Set.range (quadraticSelectedOpenBasisSpecializedHomogeneous m x f hm)) =
        Submodule.span L (Set.range (splitQuadraticPencil L)) := by
  have hnorm := quadraticSelectedOpenBasisSpecialized_span_eq_normalized_kernel
    m x f hm y c hc hfx hsurj hquad
  have hsplit :=
    (split_quadrics_span_normalized_eight_evaluation_kernel
      y c hc hsurj hquad).2
  simpa only [splitQuadraticPencil] using hnorm.trans hsplit

private theorem range_fin_two_eq_pair
    {α : Type*} (v : Fin 2 → α) :
    Set.range v = ({v 0, v 1} : Set α) := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro ha
    rcases ha with h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩

/-- The complete-intersection homogeneous ideal obtained from the
specialized regular frame is the split ideal at the selected fiber. -/
theorem quadraticSelectedOpenBasisSpecialized_ideal_eq_split
    {R : Type u} [CommRing R]
    {L : Type v} [Field L]
    (m : Fin 8 ↪ AllCharacteristics.UniversalHomogeneous.Monomials (Fin 4) 2)
    (x : Fin 8 → Fin 4 → R)
    (f : R →+* L)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (x k j))).det)
    (y : Fin 8 → Fin 4 → L) (c : Fin 4 → L)
    (hc : ∀ k, (homogeneousLinearForm c).eval (y k) ≠ 0)
    (hfx : ∀ k j, f (x k j) = normalizedVectorInLinearChart c (y k) j)
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := L)
        (fun j k => y k j : Fin 4 → Fin 8 → L) 2))
    (hquad : ∀ k,
      (X 1 * X 2 : MvPolynomial (Fin 4) L).eval (y k) = 0 ∧
      (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval (y k) = 0)
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3) :
    tripleCompleteIntersectionHomogeneousIdeal p
      (quadraticSelectedOpenBasisSpecializedHomogeneous m x f hm 0).1
      (quadraticSelectedOpenBasisSpecializedHomogeneous m x f hm 1).1
      hp
      (quadraticSelectedOpenBasisSpecializedHomogeneous m x f hm 0).2
      (quadraticSelectedOpenBasisSpecializedHomogeneous m x f hm 1).2 =
    tripleCompleteIntersectionHomogeneousIdeal p
      (splitQuadraticPencil L 0).1 (splitQuadraticPencil L 1).1 hp
      (splitQuadraticPencil L 0).2 (splitQuadraticPencil L 1).2 := by
  have hspan := quadraticSelectedOpenBasisSpecialized_span_eq_split_pencil
    m x f hm y c hc hfx hsurj hquad
  rw [range_fin_two_eq_pair, range_fin_two_eq_pair] at hspan
  exact tripleCompleteIntersectionHomogeneousIdeal_eq_of_quadratic_span
    p hp
    (quadraticSelectedOpenBasisSpecializedHomogeneous m x f hm 0)
    (quadraticSelectedOpenBasisSpecializedHomogeneous m x f hm 1)
    (splitQuadraticPencil L 0) (splitQuadraticPencil L 1) hspan

/-- The specialized selected-frame complete intersection agrees with the
one defined by any independent quadratic pair spanning the full vanishing
kernel of the eight selected points. -/
theorem quadraticSelectedOpenBasisSpecialized_ideal_eq_quadratic_pair
    {R : Type u} [CommRing R]
    {L : Type v} [Field L]
    (m : Fin 8 ↪ AllCharacteristics.UniversalHomogeneous.Monomials (Fin 4) 2)
    (x : Fin 8 → Fin 4 → R)
    (f : R →+* L)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (x k j))).det)
    (y : Fin 8 → Fin 4 → L) (c : Fin 4 → L)
    (hc : ∀ k, (homogeneousLinearForm c).eval (y k) ≠ 0)
    (hfx : ∀ k j, f (x k j) = normalizedVectorInLinearChart c (y k) j)
    (q r : MvPolynomial (Fin 4) L)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hlin : LinearIndependent L
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) L 2), ⟨r, hr⟩])
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := L)
        (fun j k => y k j : Fin 4 → Fin 8 → L) 2))
    (hquad : ∀ k, q.eval (y k) = 0 ∧ r.eval (y k) = 0)
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3) :
    tripleCompleteIntersectionHomogeneousIdeal p
      (quadraticSelectedOpenBasisSpecializedHomogeneous m x f hm 0).1
      (quadraticSelectedOpenBasisSpecializedHomogeneous m x f hm 1).1
      hp
      (quadraticSelectedOpenBasisSpecializedHomogeneous m x f hm 0).2
      (quadraticSelectedOpenBasisSpecializedHomogeneous m x f hm 1).2 =
    tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr := by
  have hspan := quadraticSelectedOpenBasisSpecialized_span_eq_quadratic_pair
    m x f hm y c hc hfx q r hq hr hlin hsurj hquad
  rw [range_fin_two_eq_pair, range_fin_two_eq_pair] at hspan
  exact tripleCompleteIntersectionHomogeneousIdeal_eq_of_quadratic_span
    p hp
    (quadraticSelectedOpenBasisSpecializedHomogeneous m x f hm 0)
    (quadraticSelectedOpenBasisSpecializedHomogeneous m x f hm 1)
    ⟨q, hq⟩ ⟨r, hr⟩ hspan

end PfaffianDescent
