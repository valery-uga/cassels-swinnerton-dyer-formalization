import PfaffianDescent.RegularAfterBaseIdealPushout
import AllCharacteristics.ProjectiveChartBaseChange
import AllCharacteristics.ProjectiveCoefficientMap
import PfaffianDescent.VoisinResidueGradedMultiplication
import PfaffianDescent.ProjectiveCoefficientIdealMap
import PfaffianDescent.FlatPrincipalChartMap
import PfaffianDescent.VoisinChartDirectSystem
import PfaffianDescent.QuotientChartKernel

/-!
# Transferring regularity from base-ideal chart fibres

The actual projective chart coefficient square is a pushout. Therefore
regularity of a section on the changed chart is exactly the regularity
needed in the quotient of the original chart by a coefficient ideal.
-/

namespace PfaffianDescent

open MvPolynomial
open HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
open scoped nonZeroDivisors

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A regular section on the actual chart after reduction modulo a base
ideal is regular in the corresponding quotient of the original chart. -/
theorem chartSection_baseIdealQuotient_regular_of_changed_regular
    {R : Type u} [CommRing R]
    (I : Ideal R)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) (R ⧸ I)))
    (hJC : J.toIdeal.map
      (MvPolynomial.map (algebraMap R (R ⧸ I))) = C.toIdeal)
    (j : Fin 4) (x : ChartRing J j)
    (hx : IsRegular
      (chartCoefficientMap (algebraMap R (R ⧸ I)) J C hJC j x)) :
    IsRegular
      (Ideal.Quotient.mk (I.map (chartBaseMap J j)) x) := by
  letI : Algebra R (ChartRing J j) := (chartBaseMap J j).toAlgebra
  exact isRegular_baseIdealQuotient_of_pushout I
    (chartCoefficientMap (algebraMap R (R ⧸ I)) J C hJC j)
    (chartBaseMap C j)
    (isPushout_chartCoefficientMap (algebraMap R (R ⧸ I)) J C hJC j)
    x hx

/-- Coefficient change sends the normalized homogeneous equation on one
actual chart to the normalized equation of the changed homogeneous class. -/
theorem chartCoefficientMap_homogeneousSection
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hJC : J.toIdeal.map (MvPolynomial.map (algebraMap R S)) = C.toIdeal)
    {d : ℕ} (s : grading J d) (j : Fin 4) :
    chartCoefficientMap (algebraMap R S) J C hJC j
        (Away.mk (grading J) (coordinate_mem J j) d
          (s : CoordinateRing J) (by simpa using s.2)) =
      Away.mk (grading C) (coordinate_mem C j) d
        (homogeneousCoefficientSection J C hJC s : CoordinateRing C)
        (by simpa using (homogeneousCoefficientSection J C hJC s).2) := by
  rw [← chartGradedCoefficientMap_eq]
  exact AllCharacteristics.gradedAwayMapOfEq_mk
    (gradedCoefficientMap (algebraMap R S) J C hJC)
    (coordinate J j) (coordinate C j)
    (gradedCoefficientMap_coordinate (algebraMap R S) J C hJC j)
    (coordinate_mem J j) (coordinate_mem C j) d
    (s : CoordinateRing J) (by simpa using s.2)

/-- Residue-field regularity supplies the exact all-base-ideal
non-zero-divisor condition for a normalized section on an actual chart
of a local flat projective model. -/
theorem chartSection_allIdealQuotient_regular_of_residue_regular
    {T : Type u} [CommRing T] [IsLocalRing T]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) T))
    [Module.Flat T (CoordinateRing J)]
    (C₀ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (IsLocalRing.ResidueField T)))
    (hJC₀ : J.toIdeal.map
      (MvPolynomial.map (algebraMap T (IsLocalRing.ResidueField T))) = C₀.toIdeal)
    {d : ℕ} (s : grading J d)
    (hreg : IsRegular
      (homogeneousCoefficientSection J C₀ hJC₀ s : CoordinateRing C₀))
    (j : Fin 4) (I : Ideal T)
    (Cᵢ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) (T ⧸ I)))
    (hJCᵢ : J.toIdeal.map
      (MvPolynomial.map (algebraMap T (T ⧸ I))) = Cᵢ.toIdeal) :
    IsRegular
      (Ideal.Quotient.mk (I.map (chartBaseMap J j))
        (Away.mk (grading J) (coordinate_mem J j) d
          (s : CoordinateRing J) (by simpa using s.2))) := by
  apply chartSection_baseIdealQuotient_regular_of_changed_regular
    I J Cᵢ hJCᵢ j
  rw [chartCoefficientMap_homogeneousSection]
  exact chartRing_allIdealFibre_regular_of_residue_regular
    J C₀ hJC₀ s hreg I Cᵢ hJCᵢ j

/-- The same statement with the base-ideal fibre taken canonically,
providing exactly the hypothesis of the flat principal-chart criterion. -/
theorem chartSection_fibrewiseRegular_of_residue_regular
    {T : Type u} [CommRing T] [IsLocalRing T]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) T))
    [Module.Flat T (CoordinateRing J)]
    (C₀ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (IsLocalRing.ResidueField T)))
    (hJC₀ : J.toIdeal.map
      (MvPolynomial.map (algebraMap T (IsLocalRing.ResidueField T))) = C₀.toIdeal)
    {d : ℕ} (s : grading J d)
    (hreg : IsRegular
      (homogeneousCoefficientSection J C₀ hJC₀ s : CoordinateRing C₀))
    (j : Fin 4) :
    ∀ I : Ideal T,
      IsRegular
        (Ideal.Quotient.mk (I.map (chartBaseMap J j))
          (Away.mk (grading J) (coordinate_mem J j) d
            (s : CoordinateRing J) (by simpa using s.2))) := by
  intro I
  exact chartSection_allIdealQuotient_regular_of_residue_regular
    J C₀ hJC₀ s hreg j I
    (coefficientChangedHomogeneousIdeal (algebraMap T (T ⧸ I)) J)
    (coefficientChangedHomogeneousIdeal_toIdeal
      (algebraMap T (T ⧸ I)) J)

/-- The normalized equation itself is a non-zero-divisor on each actual
chart.  This is the zero-base-ideal case of fibrewise regularity. -/
theorem chartSection_regular_of_residue_regular
    {T : Type u} [CommRing T] [IsLocalRing T]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) T))
    [Module.Flat T (CoordinateRing J)]
    (C₀ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (IsLocalRing.ResidueField T)))
    (hJC₀ : J.toIdeal.map
      (MvPolynomial.map (algebraMap T (IsLocalRing.ResidueField T))) = C₀.toIdeal)
    {d : ℕ} (s : grading J d)
    (hreg : IsRegular
      (homogeneousCoefficientSection J C₀ hJC₀ s : CoordinateRing C₀))
    (j : Fin 4) :
    IsRegular
      (Away.mk (grading J) (coordinate_mem J j) d
        (s : CoordinateRing J) (by simpa using s.2)) := by
  let x : ChartRing J j :=
    Away.mk (grading J) (coordinate_mem J j) d
      (s : CoordinateRing J) (by simpa using s.2)
  have hq : IsRegular (Ideal.Quotient.mk (⊥ : Ideal (ChartRing J j)) x) := by
    have h := chartSection_fibrewiseRegular_of_residue_regular
      J C₀ hJC₀ s hreg j (⊥ : Ideal T)
    rw [Ideal.map_bot] at h
    exact h
  have hinj : Function.Injective
      (Ideal.Quotient.mk (⊥ : Ideal (ChartRing J j))) :=
    ((Ideal.Quotient.mk_bijective_iff_eq_bot _).mpr rfl).1
  change IsRegular x
  exact isRegular_iff_mem_nonZeroDivisors.mpr
    (mem_nonZeroDivisors_of_injective hinj
      (isRegular_iff_mem_nonZeroDivisors.mp hq))

/-- A principal quotient of an actual chart of a local flat projective
model is flat over the base when its homogeneous equation is regular in
the residue-field coordinate ring. -/
theorem flat_principalChartMap_of_residue_regular
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
    (g : ChartRing J j →+* B) (hg : Function.Surjective g)
    (hker : RingHom.ker g = Ideal.span
      ({Away.mk (grading J) (coordinate_mem J j) d
        (s : CoordinateRing J) (by simpa using s.2)} : Set (ChartRing J j))) :
    (g.comp (chartBaseMap J j)).Flat := by
  letI : Algebra T (ChartRing J j) := (chartBaseMap J j).toAlgebra
  letI : Module.Flat T (ChartRing J j) :=
    chartRing_flat_of_coordinateRing_flat J j
  have hφ : (chartBaseMap J j).Flat := by
    change Module.Flat T (ChartRing J j)
    infer_instance
  apply flat_comp_of_surjective_principal_kernel
    (chartBaseMap J j) hφ g hg
    (Away.mk (grading J) (coordinate_mem J j) d
      (s : CoordinateRing J) (by simpa using s.2)) hker
  intro I
  exact isRegular_iff_mem_nonZeroDivisors.mp
    (chartSection_fibrewiseRegular_of_residue_regular
      J C₀ hJC₀ s hreg j I)

/-- The class of a homogeneous polynomial in the corresponding degree of
an actual homogeneous coordinate quotient. -/
noncomputable def polynomialClassInGrading
    {T : Type u} [CommRing T]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) T))
    (p : MvPolynomial (Fin 4) T) {d : ℕ} (hp : p.IsHomogeneous d) :
    grading J d :=
  ⟨Ideal.Quotient.mk J.toIdeal p, ⟨p, hp, rfl⟩⟩

/-- The actual affine chart of the intersection with a homogeneous
hypersurface is flat over a local coefficient ring if the added equation
is regular in the residue-field coordinate ring of the fixed family. -/
theorem flat_hypersurfaceIntersectionChart_of_residue_regular
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
    (j : Fin 4) :
    ((chartQuotientMap J (J ⊔ equationIdeal p hp)
      (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) j).comp
      (chartBaseMap J j)).Flat := by
  let s := polynomialClassInGrading J p hp
  apply flat_principalChartMap_of_residue_regular J C₀ hJC₀ s hreg j
    (chartQuotientMap J (J ⊔ equationIdeal p hp)
      (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) j)
  · exact chartQuotientMap_surjective _ _ _ j
  · rw [chartQuotientMap_ker_eq_equation]
    exact congrArg (fun x : ChartRing J j => Ideal.span ({x} : Set _))
      (eval₂_chartCoordinate_eq_fraction J j p hp)

end PfaffianDescent
