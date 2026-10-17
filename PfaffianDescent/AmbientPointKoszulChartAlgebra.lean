import PfaffianDescent.AmbientPointKoszulLocalAlgebra
import PfaffianDescent.AmbientPointKoszulGeometry
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Coordinate Koszul exactness on actual ambient projective charts

The `X0` chart is explicitly the polynomial ring in `X1/X0`, `X2/X0`,
`X3/X0`. On each other coordinate chart, one of the three equations is
one. These statements concern the actual homogeneous chart rings; passage
from chart modules to the global negative-twist sheaves is a separate step.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent

universe u

/-- Degree-two Koszul exactness is preserved by a ring equivalence. -/
theorem ambientPointKoszul_exact_middle_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (f g h : R)
    (hex : LinearMap.range (threeGeneratorFirst f g h) =
      LinearMap.ker (threeGeneratorMiddle f g h)) :
    LinearMap.range (threeGeneratorFirst (e f) (e g) (e h)) =
      LinearMap.ker (threeGeneratorMiddle (e f) (e g) (e h)) := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (threeGenerator_middle_comp_first _ _ _)
  · intro x hx
    change threeGeneratorMiddle (e f) (e g) (e h) x = 0 at hx
    have hy : (e.symm x.1, e.symm x.2.1, e.symm x.2.2) ∈
        LinearMap.ker (threeGeneratorMiddle f g h) := by
      apply Prod.ext
      · simpa [threeGeneratorMiddle] using congrArg (fun z : S × S × S => e.symm z.1) hx
      · apply Prod.ext
        · simpa [threeGeneratorMiddle] using congrArg (fun z : S × S × S => e.symm z.2.1) hx
        · simpa [threeGeneratorMiddle] using congrArg (fun z : S × S × S => e.symm z.2.2) hx
    rw [← hex] at hy
    obtain ⟨a, ha⟩ := hy
    refine ⟨e a, ?_⟩
    apply Prod.ext
    · simpa [threeGeneratorFirst] using congrArg (fun z : R × R × R => e z.1) ha
    · apply Prod.ext
      · simpa [threeGeneratorFirst] using congrArg (fun z : R × R × R => e z.2.1) ha
      · simpa [threeGeneratorFirst] using congrArg (fun z : R × R × R => e z.2.2) ha

/-- Degree-one Koszul exactness is preserved by a ring equivalence. -/
theorem ambientPointKoszul_exact_last_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (f g h : R)
    (hex : LinearMap.range (threeGeneratorMiddle f g h) =
      LinearMap.ker (threeGeneratorLast f g h)) :
    LinearMap.range (threeGeneratorMiddle (e f) (e g) (e h)) =
      LinearMap.ker (threeGeneratorLast (e f) (e g) (e h)) := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (threeGenerator_last_comp_middle _ _ _)
  · intro x hx
    change threeGeneratorLast (e f) (e g) (e h) x = 0 at hx
    have hy : (e.symm x.1, e.symm x.2.1, e.symm x.2.2) ∈
        LinearMap.ker (threeGeneratorLast f g h) := by
      simpa [threeGeneratorLast] using congrArg e.symm hx
    rw [← hex] at hy
    obtain ⟨a, ha⟩ := hy
    refine ⟨(e a.1, e a.2.1, e a.2.2), ?_⟩
    apply Prod.ext
    · simpa [threeGeneratorMiddle] using congrArg (fun z : R × R × R => e z.1) ha
    · apply Prod.ext
      · simpa [threeGeneratorMiddle] using congrArg (fun z : R × R × R => e z.2.1) ha
      · simpa [threeGeneratorMiddle] using congrArg (fun z : R × R × R => e z.2.2) ha

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The actual standard ambient chart is a polynomial ring in three variables. -/
def ambientPointKoszul_chartPolynomialEquiv :
    MvPolynomial (Fin 3) K ≃+* Away PS (X (0 : Fin 4)) :=
  ((renameEquiv K (finSuccAboveEquiv (0 : Fin 4))).toRingEquiv.trans
    (coordinateOneQuotientEquiv (R := K) (0 : Fin 4)).symm.toRingEquiv).trans
      (ambientChartPresentationEquiv (R := K) (0 : Fin 4))

set_option backward.isDefEq.respectTransparency false in
/-- The chart polynomial equivalence preserves base coefficients. -/
theorem ambientPointKoszul_chartPolynomialEquiv_C (a : K) :
    ambientPointKoszul_chartPolynomialEquiv K (C a) =
      AllCharacteristics.GradedChart.baseMap PS (z := X (0 : Fin 4)) a := by
  change ambientChartPresentationEquiv (R := K) 0
    ((coordinateOneQuotientEquiv (R := K) 0).symm
      (renameEquiv K (finSuccAboveEquiv (0 : Fin 4)) (C a))) = _
  rw [renameEquiv_apply, rename_C]
  have hc : (coordinateOneQuotientEquiv (R := K) (0 : Fin 4)).symm (C a) =
      Ideal.Quotient.mk (coordinateOneIdeal (R := K) (0 : Fin 4)) (C a) :=
    (coordinateOneQuotientEquiv (R := K) (0 : Fin 4)).symm.commutes a
  rw [hc]
  change ambientChartPresentationEquiv (R := K) (0 : Fin 4)
    (Ideal.Quotient.mk (ambientChartPresentationIdeal (R := K) (0 : Fin 4)) (C a)) = _
  rw [ambientChartPresentationEquiv_mk]
  exact eval₂Hom_C _ _ a

set_option backward.isDefEq.respectTransparency false in
/-- Each of the polynomial variables is the corresponding normalized coordinate. -/
theorem ambientPointKoszul_chartPolynomialEquiv_X (i : Fin 3) :
    ambientPointKoszul_chartPolynomialEquiv K (X i) =
      ambientChartCoordinate (R := K) (σ := Fin 4) 0 i.succ := by
  change ambientChartPresentationEquiv (R := K) 0
    ((coordinateOneQuotientEquiv (R := K) 0).symm
      (renameEquiv K (finSuccAboveEquiv (0 : Fin 4)) (X i))) = _
  rw [renameEquiv_apply, rename_X]
  change ambientChartPresentationEquiv (R := K) 0
    (coordinateOneQuotientInverse (R := K) 0 (X (finSuccAboveEquiv (0 : Fin 4) i))) = _
  rw [coordinateOneQuotientInverse, aeval_X]
  change ambientChartPresentationEquiv (R := K) (0 : Fin 4)
    (Ideal.Quotient.mk (ambientChartPresentationIdeal (R := K) (0 : Fin 4))
      (X (finSuccAboveEquiv (0 : Fin 4) i).1)) = _
  rw [ambientChartPresentationEquiv_mk]
  simp only [ambientChartEvaluation, eval₂Hom_X', finSuccAboveEquiv_apply, Fin.succAbove_zero]

/-- Under the actual chart polynomial equivalence, point restriction is
evaluation at the affine origin. -/
theorem ambientPointKoszul_chartMap_comp_polynomialEquiv :
    (ambientPointKoszul_chartMap K).comp (ambientPointKoszul_chartPolynomialEquiv K).toRingHom =
      eval₂Hom (RingHom.id K) (0 : Fin 3 → K) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      ambientPointKoszul_chartPolynomialEquiv_C, ambientPointKoszul_chartMap_base,
      eval₂Hom_C, RingHom.id_apply]
  · intro i
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      ambientPointKoszul_chartPolynomialEquiv_X, ambientPointKoszul_chartMap_coordinate,
      eval₂Hom_X', Pi.zero_apply]
    fin_cases i <;> rfl

/-- Point restriction on its actual ambient chart is surjective. -/
theorem ambientPointKoszul_chartMap_surjective :
    Function.Surjective (ambientPointKoszul_chartMap K) :=
  fun a => ⟨AllCharacteristics.GradedChart.baseMap PS (z := X (0 : Fin 4)) a,
    ambientPointKoszul_chartMap_base K a⟩

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the actual point restriction is generated by the three
normalized coordinate equations. -/
theorem ambientPointKoszul_chartMap_ker :
    RingHom.ker (ambientPointKoszul_chartMap K) =
      Ideal.span ({ambientChartCoordinate (R := K) (σ := Fin 4) 0 1,
        ambientChartCoordinate (R := K) (σ := Fin 4) 0 2,
        ambientChartCoordinate (R := K) (σ := Fin 4) 0 3} : Set (Away PS (X (0 : Fin 4)))) := by
  let e := ambientPointKoszul_chartPolynomialEquiv K
  have hcomap : (RingHom.ker (ambientPointKoszul_chartMap K)).comap e.toRingHom =
      idealOfVars (Fin 3) K := by
    change RingHom.ker ((ambientPointKoszul_chartMap K).comp e.toRingHom) = _
    rw [ambientPointKoszul_chartMap_comp_polynomialEquiv, ambientPointKoszul_eval_zero_ker]
  have hrange : Set.range (X : Fin 3 → MvPolynomial (Fin 3) K) = {X 0, X 1, X 2} := by
    ext p
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  have hmap : (idealOfVars (Fin 3) K).map e.toRingHom =
      Ideal.span ({ambientChartCoordinate (R := K) (σ := Fin 4) 0 1,
        ambientChartCoordinate (R := K) (σ := Fin 4) 0 2,
        ambientChartCoordinate (R := K) (σ := Fin 4) 0 3} : Set (Away PS (X (0 : Fin 4)))) := by
    rw [idealOfVars, hrange, Ideal.map_span]
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    change Ideal.span ({ambientPointKoszul_chartPolynomialEquiv K (X 0),
      ambientPointKoszul_chartPolynomialEquiv K (X 1),
      ambientPointKoszul_chartPolynomialEquiv K (X 2)} : Set _) = _
    simp [ambientPointKoszul_chartPolynomialEquiv_X, Fin.succ]
  rw [← hmap, ← hcomap]
  exact (RingHom.ker (ambientPointKoszul_chartMap K)).map_comap_of_surjective
    e.toRingHom e.surjective |>.symm

/-- The actual point chart quotient is its coefficient field, via the
canonical chart restriction map. -/
def ambientPointKoszul_chartQuotientEquiv :
    (Away PS (X (0 : Fin 4)) ⧸
      Ideal.span ({ambientChartCoordinate (R := K) (σ := Fin 4) 0 1,
        ambientChartCoordinate (R := K) (σ := Fin 4) 0 2,
        ambientChartCoordinate (R := K) (σ := Fin 4) 0 3} : Set (Away PS (X (0 : Fin 4))))) ≃+* K :=
  (Ideal.quotEquivOfEq (ambientPointKoszul_chartMap_ker K).symm).trans
    (RingHom.quotientKerEquivOfSurjective (ambientPointKoszul_chartMap_surjective K))

/-- The quotient-field identification is induced by the actual point chart map. -/
theorem ambientPointKoszul_chartQuotientEquiv_mk (r : Away PS (X (0 : Fin 4))) :
    ambientPointKoszul_chartQuotientEquiv K
      (Ideal.Quotient.mk
        (Ideal.span ({ambientChartCoordinate (R := K) (σ := Fin 4) 0 1,
          ambientChartCoordinate (R := K) (σ := Fin 4) 0 2,
          ambientChartCoordinate (R := K) (σ := Fin 4) 0 3} : Set (Away PS (X (0 : Fin 4))))) r) =
      ambientPointKoszul_chartMap K r := by
  unfold ambientPointKoszul_chartQuotientEquiv
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ r

/-- The affine last differential and actual point restriction form an exact pair. -/
theorem ambientPointKoszul_chartZero_exact_augmentation :
    Function.Exact
      (threeGeneratorLast (ambientChartCoordinate (R := K) (σ := Fin 4) 0 1)
        (ambientChartCoordinate (R := K) (σ := Fin 4) 0 2)
        (ambientChartCoordinate (R := K) (σ := Fin 4) 0 3))
      (ambientPointKoszul_chartMap K) := by
  intro r
  change r ∈ RingHom.ker (ambientPointKoszul_chartMap K) ↔
    r ∈ LinearMap.range (threeGeneratorLast
      (ambientChartCoordinate (R := K) (σ := Fin 4) 0 1)
      (ambientChartCoordinate (R := K) (σ := Fin 4) 0 2)
      (ambientChartCoordinate (R := K) (σ := Fin 4) 0 3))
  rw [threeGeneratorLast_range, ambientPointKoszul_chartMap_ker]

set_option backward.isDefEq.respectTransparency false in
/-- Injectivity of the first differential on the actual point-containing chart. -/
theorem ambientPointKoszul_chartZero_first_injective :
    Function.Injective (threeGeneratorFirst
      (ambientChartCoordinate (R := K) (σ := Fin 4) 0 1)
      (ambientChartCoordinate (R := K) (σ := Fin 4) 0 2)
      (ambientChartCoordinate (R := K) (σ := Fin 4) 0 3)) := by
  let e := ambientPointKoszul_chartPolynomialEquiv K
  have he : e.symm (ambientChartCoordinate (R := K) (σ := Fin 4) 0 1) = X 0 := by
    have hX : e (X 0) = ambientChartCoordinate (R := K) (σ := Fin 4) 0 1 := by
      simpa [e, Fin.succ] using ambientPointKoszul_chartPolynomialEquiv_X K (0 : Fin 3)
    rw [← hX]
    exact e.symm_apply_apply _
  intro x y hxy
  apply e.symm.injective
  apply mul_left_cancel₀ (X_ne_zero (0 : Fin 3) : (X 0 : MvPolynomial (Fin 3) K) ≠ 0)
  have h := congrArg (fun z : Away PS (X (0 : Fin 4)) ×
    Away PS (X (0 : Fin 4)) × Away PS (X (0 : Fin 4)) => e.symm z.2.2) hxy
  simpa only [threeGeneratorFirst, LinearMap.coe_mk, AddHom.coe_mk, map_mul, he] using h

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at degree two in the actual point-containing chart ring. -/
theorem ambientPointKoszul_chartZero_exact_middle :
    LinearMap.range (threeGeneratorFirst (ambientChartCoordinate (R := K) (σ := Fin 4) 0 1)
      (ambientChartCoordinate (R := K) (σ := Fin 4) 0 2) (ambientChartCoordinate (R := K) (σ := Fin 4) 0 3)) =
    LinearMap.ker (threeGeneratorMiddle (ambientChartCoordinate (R := K) (σ := Fin 4) 0 1)
      (ambientChartCoordinate (R := K) (σ := Fin 4) 0 2) (ambientChartCoordinate (R := K) (σ := Fin 4) 0 3)) := by
  have h := ambientPointKoszul_exact_middle_of_ringEquiv
    (ambientPointKoszul_chartPolynomialEquiv K) (X 0) (X 1) (X 2)
    ambientPointKoszul_polynomial_exact_middle
  simpa [ambientPointKoszul_chartPolynomialEquiv_X, Fin.succ] using h

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at degree one in the actual point-containing chart ring. -/
theorem ambientPointKoszul_chartZero_exact_last :
    LinearMap.range (threeGeneratorMiddle (ambientChartCoordinate (R := K) (σ := Fin 4) 0 1)
      (ambientChartCoordinate (R := K) (σ := Fin 4) 0 2) (ambientChartCoordinate (R := K) (σ := Fin 4) 0 3)) =
    LinearMap.ker (threeGeneratorLast (ambientChartCoordinate (R := K) (σ := Fin 4) 0 1)
      (ambientChartCoordinate (R := K) (σ := Fin 4) 0 2) (ambientChartCoordinate (R := K) (σ := Fin 4) 0 3)) := by
  have h := ambientPointKoszul_exact_last_of_ringEquiv
    (ambientPointKoszul_chartPolynomialEquiv K) (X 0) (X 1) (X 2)
    ambientPointKoszul_polynomial_exact_last
  simpa [ambientPointKoszul_chartPolynomialEquiv_X, Fin.succ] using h

set_option backward.isDefEq.respectTransparency false in
/-- On every other coordinate chart one point equation is a unit, hence
the actual affine coordinate Koszul complex is exact with surjective last map. -/
theorem ambientPointKoszul_chartNonzero_exact (j : Fin 4) (hj : j ≠ 0) :
    Function.Injective (threeGeneratorFirst (ambientChartCoordinate (R := K) (σ := Fin 4) j 1)
      (ambientChartCoordinate (R := K) (σ := Fin 4) j 2) (ambientChartCoordinate (R := K) (σ := Fin 4) j 3)) ∧
    LinearMap.range (threeGeneratorFirst (ambientChartCoordinate (R := K) (σ := Fin 4) j 1)
      (ambientChartCoordinate (R := K) (σ := Fin 4) j 2) (ambientChartCoordinate (R := K) (σ := Fin 4) j 3)) =
    LinearMap.ker (threeGeneratorMiddle (ambientChartCoordinate (R := K) (σ := Fin 4) j 1)
      (ambientChartCoordinate (R := K) (σ := Fin 4) j 2) (ambientChartCoordinate (R := K) (σ := Fin 4) j 3)) ∧
    LinearMap.range (threeGeneratorMiddle (ambientChartCoordinate (R := K) (σ := Fin 4) j 1)
      (ambientChartCoordinate (R := K) (σ := Fin 4) j 2) (ambientChartCoordinate (R := K) (σ := Fin 4) j 3)) =
    LinearMap.ker (threeGeneratorLast (ambientChartCoordinate (R := K) (σ := Fin 4) j 1)
      (ambientChartCoordinate (R := K) (σ := Fin 4) j 2) (ambientChartCoordinate (R := K) (σ := Fin 4) j 3)) ∧
    Function.Surjective (threeGeneratorLast (ambientChartCoordinate (R := K) (σ := Fin 4) j 1)
      (ambientChartCoordinate (R := K) (σ := Fin 4) j 2) (ambientChartCoordinate (R := K) (σ := Fin 4) j 3)) := by
  apply ambientPointKoszul_exact_of_any_unit
  have hj' : j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj' with rfl | rfl | rfl
  · exact Or.inl (by rw [ambientChartCoordinate_self]; exact isUnit_one)
  · exact Or.inr (Or.inl (by rw [ambientChartCoordinate_self]; exact isUnit_one))
  · exact Or.inr (Or.inr (by rw [ambientChartCoordinate_self]; exact isUnit_one))

end PfaffianDescent
