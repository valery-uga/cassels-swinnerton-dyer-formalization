import PfaffianDescent.VoisinProjectiveNontrivialEquationOpen
import PfaffianDescent.VoisinCubicIntersectionChart

/-!
# Regular intersection charts at field points of the nontrivial equation family

The field-point theorem for Voisin's relative nontrivial-equation open
produces a cubic regular modulo the smooth fixed surface. The chart kernel
theorem turns that witness into a regular principal equation on every
standard affine chart of that surface.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A pair of cubic equations has a regular principal intersection equation
on every standard chart of the first cubic. -/
def CubicIntersectionRegularOnCharts
    {S : Type u} [Field S]
    (a : MvPolynomial (Fin 4) S) (ha : a.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous 3) : Prop :=
  ∀ j : Fin 4,
    RingHom.ker (cubicIntersectionChartMap a ha p hp j) =
      Ideal.span ({normalizedCubicSection a ha p hp j} :
        Set (ChartRing (equationIdeal a ha) j)) ∧
    IsRegular (normalizedCubicSection a ha p hp j)

theorem cubicIntersectionRegularOnCharts_of_regularModSurface
    {S : Type u} [Field S]
    (a : MvPolynomial (Fin 4) S) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase a ha)]
    (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous 3)
    (hregular : ∀ x : MvPolynomial (Fin 4) S,
      p * x ∈ Ideal.span ({a} : Set (MvPolynomial (Fin 4) S)) →
        x ∈ Ideal.span ({a} : Set (MvPolynomial (Fin 4) S))) :
    CubicIntersectionRegularOnCharts a ha p hp := by
  intro j
  exact cubicIntersectionChartMap_ker_eq_regularEquation a ha ha0 p hp hregular j

section FieldPoint

variable {K R S : Type u} [Field K] [CommRing R] [IsDomain R]
  [IsNoetherianRing R] [Algebra K R] [Field S] [Algebra R S]
  [Algebra K S] [IsScalarTower K R S]
variable (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
variable [Module.Flat R (CoordinateRing J)]
variable (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
variable (hRank : ∀ x : PrimeSpectrum R,
  Module.rankAtStalk (grading J 3) x = q)
variable (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
variable (hmap : Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal = C.toIdeal)
variable (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
variable [Smooth (hypersurfaceToBase (a.map (algebraMap K S))
  (ha.map (algebraMap K S)))]
variable (s : Spec (.of S) ⟶
  pullback (flatGradedProjectiveFamilyNontrivialOpenToBase
    J r q e hRank a ha ha0)
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))
variable (hs : s ≫ pullback.snd
  (flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0)
  (Spec.map (CommRingCat.ofHom (algebraMap R S))) = 𝟙 _)

include J r q e hRank hmap ha0 s hs in
/-- A field point of the relative nontrivial-equation open gives a cubic in
the fibre ideal whose intersection with the fixed smooth cubic has a regular
principal equation on every standard affine chart. -/
theorem flatGradedProjectiveFamilyNontrivialOpen_fieldPoint_regularCharts :
    ∃ (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0),
      p ∈ C.toIdeal ∧
      CubicIntersectionRegularOnCharts (a.map (algebraMap K S))
        (ha.map (algebraMap K S)) p hp := by
  obtain ⟨p, hp, hp0, hpC, hregular, _⟩ :=
    flatGradedProjectiveFamilyNontrivialOpen_baseChange_fieldPoint_regular
      J r q e hRank C hmap a ha ha0 s hs
  have haS0 : a.map (algebraMap K S) ≠ 0 := by
    intro hzero
    apply ha0
    exact MvPolynomial.map_injective (algebraMap K S)
      (RingHom.injective (algebraMap K S)) (by simpa using hzero)
  exact ⟨p, hp, hp0, hpC,
    cubicIntersectionRegularOnCharts_of_regularModSurface
      (a.map (algebraMap K S)) (ha.map (algebraMap K S)) haS0
      p hp hregular⟩

end FieldPoint
end PfaffianDescent
