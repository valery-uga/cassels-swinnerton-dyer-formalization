import PfaffianDescent.ProjectiveChartRegularPrincipalIdealBaseChange
import PfaffianDescent.VoisinChartBaseIdealRegular

/-!
# Residue-regular equations and canonical ideal-sheaf base change

On a local flat projective model, residue-field regularity gives
regularity both on the original chart and after reduction by any base
ideal. This discharges the regularity hypotheses in the affine
canonical ideal-sheaf base-change theorem.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A residue-regular homogeneous section gives canonical ideal-sheaf
base change along every quotient of the coefficient ring, for any
surjective chart map whose kernel is its normalized equation. -/
theorem isIso_residueRegularChartIdealBaseChange
    {T B : Type u} [CommRing T] [IsLocalRing T] [CommRing B]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) T))
    [Module.Flat T (CoordinateRing J)]
    (C₀ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (IsLocalRing.ResidueField T)))
    (hJC₀ : J.toIdeal.map
      (MvPolynomial.map (algebraMap T (IsLocalRing.ResidueField T))) = C₀.toIdeal)
    {d : ℕ} (s : grading J d)
    (hreg : IsRegular
      (homogeneousCoefficientSection J C₀ hJC₀ s : CoordinateRing C₀))
    (j : Fin 4)
    (q : ChartRing J j →+* B) (hq : Function.Surjective q)
    (hker : RingHom.ker q = Ideal.span
      ({Away.mk (grading J) (coordinate_mem J j) d
        (s : CoordinateRing J) (by simpa using s.2)} : Set (ChartRing J j)))
    (I : Ideal T)
    (Cᵢ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) (T ⧸ I)))
    (hJCᵢ : J.toIdeal.map
      (MvPolynomial.map (algebraMap T (T ⧸ I))) = Cᵢ.toIdeal) :
    let g := chartCoefficientMap (algebraMap T (T ⧸ I)) J Cᵢ hJCᵢ j
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom q)) :=
      IsClosedImmersion.spec_of_surjective _ hq
    IsIso (closedImmersionIdealBaseChangeHom
      (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom q))) := by
  let x : ChartRing J j := Away.mk (grading J) (coordinate_mem J j) d
    (s : CoordinateRing J) (by simpa using s.2)
  let g := chartCoefficientMap (algebraMap T (T ⧸ I)) J Cᵢ hJCᵢ j
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom q)) :=
    IsClosedImmersion.spec_of_surjective _ hq
  have hx : IsRegular x :=
    chartSection_regular_of_residue_regular J C₀ hJC₀ s hreg j
  have hg : IsRegular (g x) := by
    change IsRegular (chartCoefficientMap (algebraMap T (T ⧸ I)) J Cᵢ hJCᵢ j
      (Away.mk (grading J) (coordinate_mem J j) d
        (s : CoordinateRing J) (by simpa using s.2)))
    rw [chartCoefficientMap_homogeneousSection]
    exact chartRing_allIdealFibre_regular_of_residue_regular
      J C₀ hJC₀ s hreg I Cᵢ hJCᵢ j
  exact isIso_regularPrincipalSurjectiveAffineIdealBaseChangeHom
    g q hq x hx hg hker

/-- For the actual intersection with a homogeneous hypersurface, a
residue-regular equation gives the canonical ideal-sheaf comparison on
each standard chart after reduction by any coefficient ideal. -/
theorem isIso_residueRegularHypersurfaceChartIdealBaseChange
    {T : Type u} [CommRing T] [IsLocalRing T]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) T))
    [Module.Flat T (CoordinateRing J)]
    (C₀ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (IsLocalRing.ResidueField T)))
    (hJC₀ : J.toIdeal.map
      (MvPolynomial.map (algebraMap T (IsLocalRing.ResidueField T))) = C₀.toIdeal)
    (p : MvPolynomial (Fin 4) T) {d : ℕ} (hp : p.IsHomogeneous d)
    (hreg : IsRegular
      (homogeneousCoefficientSection J C₀ hJC₀
        (polynomialClassInGrading J p hp) : CoordinateRing C₀))
    (j : Fin 4) (I : Ideal T)
    (Cᵢ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) (T ⧸ I)))
    (hJCᵢ : J.toIdeal.map
      (MvPolynomial.map (algebraMap T (T ⧸ I))) = Cᵢ.toIdeal) :
    let q := chartQuotientMap J (J ⊔ equationIdeal p hp)
      (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) j
    let g := chartCoefficientMap (algebraMap T (T ⧸ I)) J Cᵢ hJCᵢ j
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom q)) :=
      IsClosedImmersion.spec_of_surjective _
        (chartQuotientMap_surjective _ _ _ j)
    IsIso (closedImmersionIdealBaseChangeHom
      (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom q))) := by
  let q := chartQuotientMap J (J ⊔ equationIdeal p hp)
    (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) j
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom q)) :=
    IsClosedImmersion.spec_of_surjective _
      (chartQuotientMap_surjective _ _ _ j)
  have hker : RingHom.ker q = Ideal.span
      ({Away.mk (grading J) (coordinate_mem J j) d
        ((polynomialClassInGrading J p hp : grading J d) : CoordinateRing J)
        (by simpa using (polynomialClassInGrading J p hp).2)} :
        Set (ChartRing J j)) := by
    rw [chartQuotientMap_ker_eq_equation]
    exact congrArg (fun x : ChartRing J j => Ideal.span ({x} : Set _))
      (eval₂_chartCoordinate_eq_fraction J j p hp)
  exact isIso_residueRegularChartIdealBaseChange J C₀ hJC₀
    (polynomialClassInGrading J p hp) hreg j q
    (chartQuotientMap_surjective _ _ _ j) hker I Cᵢ hJCᵢ

/-- The same concrete two-cubic chart comparison holds for every
coefficient ring map. Relative flatness of the quotient chart, deduced
from residue regularity, keeps the equation regular after arbitrary
base change. -/
theorem isIso_residueRegularHypersurfaceChartIdealBaseChange_any
    {T S : Type u} [CommRing T] [IsLocalRing T] [CommRing S]
    (f : T →+* S)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) T))
    [Module.Flat T (CoordinateRing J)]
    (C₀ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (IsLocalRing.ResidueField T)))
    (hJC₀ : J.toIdeal.map
      (MvPolynomial.map (algebraMap T (IsLocalRing.ResidueField T))) = C₀.toIdeal)
    (p : MvPolynomial (Fin 4) T) {d : ℕ} (hp : p.IsHomogeneous d)
    (hreg : IsRegular
      (homogeneousCoefficientSection J C₀ hJC₀
        (polynomialClassInGrading J p hp) : CoordinateRing C₀))
    (j : Fin 4) :
    let Q := J ⊔ equationIdeal p hp
    let hJQ : J.toIdeal ≤ Q.toIdeal := by
      rw [HomogeneousIdeal.toIdeal_sup]
      exact le_sup_left
    let q := chartQuotientMap J Q hJQ j
    let g := chartCoefficientMap f J
      (coefficientChangedHomogeneousIdeal f J)
      (coefficientChangedHomogeneousIdeal_toIdeal f J) j
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom q)) :=
      IsClosedImmersion.spec_of_surjective _
        (chartQuotientMap_surjective _ _ _ j)
    IsIso (closedImmersionIdealBaseChangeHom
      (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom q))) := by
  let Q := J ⊔ equationIdeal p hp
  let hJQ : J.toIdeal ≤ Q.toIdeal := by
    rw [HomogeneousIdeal.toIdeal_sup]
    exact le_sup_left
  let q := chartQuotientMap J Q hJQ j
  let x : ChartRing J j :=
    p.eval₂ (chartBaseMap J j) (chartCoordinate J j)
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom q)) :=
    IsClosedImmersion.spec_of_surjective _
      (chartQuotientMap_surjective _ _ _ j)
  have hx : IsRegular x := by
    change IsRegular (p.eval₂ (chartBaseMap J j) (chartCoordinate J j))
    rw [eval₂_chartCoordinate_eq_fraction J j p hp]
    exact chartSection_regular_of_residue_regular J C₀ hJC₀
      (polynomialClassInGrading J p hp) hreg j
  have hker : RingHom.ker q = Ideal.span ({x} : Set (ChartRing J j)) := by
    exact chartQuotientMap_ker_eq_equation J p hp j
  have hflat : (q.comp (chartBaseMap J j)).Flat :=
    flat_hypersurfaceIntersectionChart_of_residue_regular
      J C₀ hJC₀ p hp hreg j
  exact isIso_chartQuotientMap_idealBaseChange_of_flat_regular
    f J Q hJQ j x hx hker hflat

end PfaffianDescent
