import PfaffianDescent.VoisinPlaneConicLocalCartier

/-!
# Pointwise Cartier equations on principal-open refinements

The four functions `ell, q, a, b` generate the unit ideal precisely when
their principal opens cover the affine chart. Localizing at any prime then
makes one of these functions a unit. The conic relation turns its two-
generator ideal into a regular principal ideal in that actual local ring.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

/-- The conic ideal is regular principal in every prime localization of a
domain when its two equations and two cubic coefficients generate the unit
ideal. The condition `ell ≠ 0 ∨ q ≠ 0` prevents the zero ideal from being
mistaken for an effective Cartier divisor. -/
theorem conicIdeal_atPrime_regularPrincipal_of_span_top
    {A : Type u} [CommRing A] [IsDomain A]
    (ell q a b : A)
    (h : ell * a + q * b = 0)
    (hnonzero : ell ≠ 0 ∨ q ≠ 0)
    (hcover : Ideal.span ({ell, q, a, b} : Set A) = ⊤)
    (P : PrimeSpectrum A) :
    let f : A →+* Localization.AtPrime P.asIdeal := algebraMap A _
    ∃ z : Localization.AtPrime P.asIdeal, IsRegular z ∧
      Ideal.span ({f ell, f q} : Set (Localization.AtPrime P.asIdeal)) =
        Ideal.span ({z} : Set (Localization.AtPrime P.asIdeal)) := by
  dsimp only
  let B := Localization.AtPrime P.asIdeal
  let f : A →+* B := algebraMap A B
  have hfinj : Function.Injective f :=
    IsLocalization.injective B P.asIdeal.primeCompl_le_nonZeroDivisors
  have hnonzeroB : f ell ≠ 0 ∨ f q ≠ 0 := by
    rcases hnonzero with hell | hq
    · exact Or.inl (fun hz => hell (hfinj (hz.trans (map_zero f).symm)))
    · exact Or.inr (fun hz => hq (hfinj (hz.trans (map_zero f).symm)))
  have hrel : f ell * f a + f q * f b = 0 := by
    simpa only [map_add, map_mul, map_zero] using congrArg f h
  have hcoverB : Ideal.span ({f ell, f q, f a, f b} : Set B) = ⊤ := by
    have hm := congrArg (Ideal.map f) hcover
    simpa only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
      Ideal.map_top] using hm
  exact conicIdeal_regularPrincipal_of_local_span_top
    (f ell) (f q) (f a) (f b) hrel hnonzeroB hcoverB

/-- The Jacobian unit-ideal condition on an actual cubic affine chart
gives a regular-principal conic ideal at every point of that chart, provided
the chart is a domain and the conic ideal is nonzero there. -/
theorem planeConic_cubicChart_atPrime_regularPrincipal_of_jacobian_top
    {K : Type u} [Field K]
    (p ell q a b : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (h : p = ell * a + q * b)
    (j : Fin 4)
    [IsDomain (ChartRing (equationIdeal p hp) j)]
    (hnonzero :
      let I := equationIdeal p hp
      ell.eval₂ (chartBaseMap I j) (chartCoordinate I j) ≠ 0 ∨
        q.eval₂ (chartBaseMap I j) (chartCoordinate I j) ≠ 0)
    (hjac :
      let I := equationIdeal p hp
      Ideal.span (Set.range (fun i : Fin 4 =>
        (pderiv i p).eval₂ (chartBaseMap I j) (chartCoordinate I j))) = ⊤)
    (P : PrimeSpectrum (ChartRing (equationIdeal p hp) j)) :
    let I := equationIdeal p hp
    let f : ChartRing I j →+* Localization.AtPrime P.asIdeal := algebraMap _ _
    ∃ z : Localization.AtPrime P.asIdeal, IsRegular z ∧
      Ideal.span
          ({f (ell.eval₂ (chartBaseMap I j) (chartCoordinate I j)),
            f (q.eval₂ (chartBaseMap I j) (chartCoordinate I j))} :
            Set (Localization.AtPrime P.asIdeal)) =
        Ideal.span ({z} : Set (Localization.AtPrime P.asIdeal)) := by
  dsimp only at hnonzero hjac ⊢
  let I := equationIdeal p hp
  let evI := eval₂Hom (chartBaseMap I j) (chartCoordinate I j)
  have hcover : Ideal.span
      ({evI ell, evI q, evI a, evI b} : Set (ChartRing I j)) = ⊤ :=
    planeConic_coefficientIdeal_top_of_jacobian_top
      p ell q a b h evI hjac
  have hrel : evI ell * evI a + evI q * evI b = 0 := by
    simpa only [evI, I, MvPolynomial.coe_eval₂Hom] using
      planeConic_cubicChart_relation p ell q a b hp h j
  exact conicIdeal_atPrime_regularPrincipal_of_span_top
    (evI ell) (evI q) (evI a) (evI b) hrel hnonzero hcover P

end PfaffianDescent
