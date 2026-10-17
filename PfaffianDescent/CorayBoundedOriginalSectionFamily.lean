import PfaffianDescent.CorayHomogeneousCurveChoice
import Mathlib.Algebra.Algebra.Prod
import PfaffianDescent.ProjectiveClosedPointCoordinates
import AllCharacteristics.ClosedPointAlgebra

/-! Source-only, unverified. The actual bounded-degree section family on
the original cubic, with cubic relations removed BEFORE taking the
through-point kernel. Coordinate algebras and all dimensions are over K.
No regularity, integral member, or tangent nonvanishing is assumed. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

section
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]

/-- Actual finite-coordinate evaluation on the cubic coordinate ring.
The only incidence input is that the defining cubic vanishes. -/
def cubicCoordinateAlgebraEvaluation
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap K A) x = 0) :
    CoordinateRing (equationIdeal p hp) →ₐ[K] A :=
  Ideal.Quotient.liftₐ (equationIdeal p hp).toIdeal (MvPolynomial.aeval x) (by
    have hle : (equationIdeal p hp).toIdeal ≤
        RingHom.ker (MvPolynomial.aeval x).toRingHom := by
      apply Ideal.span_le.mpr
      intro a ha
      obtain rfl := Set.mem_singleton_iff.mp ha
      exact hpx
    intro a ha
    exact hle ha)

@[simp]
theorem cubicCoordinateAlgebraEvaluation_mk
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap K A) x = 0)
    (q : MvPolynomial (Fin 4) K) :
    cubicCoordinateAlgebraEvaluation p hp x hpx
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal q) =
      q.eval₂ (algebraMap K A) x := rfl

/-- Actual degree-n sections, rather than a numerical dimension proxy. -/
def cubicGradeCoordinateEvaluation
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap K A) x = 0) :
    grading (equationIdeal p hp) n →ₗ[K] A :=
  (cubicCoordinateAlgebraEvaluation p hp x hpx).toLinearMap.domRestrict _

/-- The full actual degree-n section family through the given original
residue coordinates, modulo ALL cubic relations in that degree. -/
def cubicThroughCoordinateSections
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap K A) x = 0) :
    Submodule K (grading (equationIdeal p hp) n) :=
  LinearMap.ker (cubicGradeCoordinateEvaluation p hp n x hpx)

/-- Every actual quotient-grade vector has a SAME-degree homogeneous
polynomial representative. -/
theorem cubicGradeSection_exists_polynomial_representative
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (s : grading (equationIdeal p hp) n) :
    ∃ q : MvPolynomial (Fin 4) K, q.IsHomogeneous n ∧
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal q = s.1 := by
  have hs : s.1 ∈ (homogeneousSubmodule (Fin 4) K n).map
      (Ideal.Quotient.mkₐ K (equationIdeal p hp).toIdeal).toLinearMap := s.2
  obtain ⟨q, hq, hqs⟩ := Submodule.mem_map.mp hs
  exact ⟨q, hq, hqs⟩

/-- Through-point vectors are EXACTLY polynomial representatives of the
prescribed degree vanishing at the same coordinates. -/
theorem cubicThroughCoordinateSections_mem_iff
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap K A) x = 0)
    (s : grading (equationIdeal p hp) n) :
    s ∈ cubicThroughCoordinateSections p hp n x hpx ↔
      ∃ q : MvPolynomial (Fin 4) K, q.IsHomogeneous n ∧
        q.eval₂ (algebraMap K A) x = 0 ∧
        Ideal.Quotient.mk (equationIdeal p hp).toIdeal q = s.1 := by
  constructor
  · intro hs
    obtain ⟨q, hq, hqs⟩ := cubicGradeSection_exists_polynomial_representative p hp n s
    refine ⟨q, hq, ?_, hqs⟩
    have he : cubicCoordinateAlgebraEvaluation p hp x hpx s.1 = 0 := hs
    rw [← hqs] at he
    exact he
  · rintro ⟨q, hq, hx, hqs⟩
    change cubicCoordinateAlgebraEvaluation p hp x hpx s.1 = 0
    rw [← hqs]
    exact hx

variable [FiniteDimensional K A]

/-- The bounded family retains the actual H_n-d count on the quotient,
not merely in the polynomial space before cubic relations are removed. -/
theorem cubicThroughCoordinateSections_finrank_lower_bound
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (n : ℕ) (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap K A) x = 0) :
    (n + 3).choose 3 - n.choose 3 - finrank K A ≤
      finrank K (cubicThroughCoordinateSections p hp n x hpx) := by
  letI : Module.Finite K (grading (equationIdeal p hp) n) :=
    Module.Finite.iff_fg.mpr ((homogeneousSubmodule_fg (Fin 4) K n).map
      (Ideal.Quotient.mkₐ K (equationIdeal p hp).toIdeal).toLinearMap)
  have h := PfaffianDescent.finrank_sub_le_finrank_ker
    (cubicGradeCoordinateEvaluation p hp n x hpx)
  rw [cubicSurface_grade_finrank p hp hp0 n] at h
  exact h

/-- Coray A(i)'s five-dimensional (projective dimension at least4)
through-P family is an actual vector space, not an input rank certificate. -/
theorem cubicThroughCoordinateSections_finrank_ge_five
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (n : ℕ) (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap K A) x = 0)
    (hsize : finrank K A + 5 ≤ (n + 3).choose 3 - n.choose 3) :
    5 ≤ finrank K (cubicThroughCoordinateSections p hp n x hpx) := by
  have h := cubicThroughCoordinateSections_finrank_lower_bound p hp hp0 n x hpx
  omega

end

open AlgebraicGeometry CategoryTheory

/-- Actual ORIGINAL closed P supplies its own canonical residue algebra,
its recovered chart, and the bounded quotient family count. No replacement
residue degree, coordinates, or evaluation-incidence premise is given. -/
theorem cubicOriginalClosedPoint_exists_bounded_section_family
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (n : ℕ) (P : closedPoints (hypersurface p hp)) :
    let S := hypersurface p hp
    let pi := hypersurfaceToBase p hp
    letI := AllCharacteristics.pointAlgebra pi P.1
    ∃ (j : Fin 4) (g : ChartRing (equationIdeal p hp) j →+* S.residueField P.1),
      g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K (S.residueField P.1) ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal p hp) j =
        S.fromSpecResidueField P.1 ∧
      ∃ hpx : p.eval₂ (algebraMap K (S.residueField P.1))
          (fun i => g (chartCoordinate (equationIdeal p hp) j i)) = 0,
        (n + 3).choose 3 - n.choose 3 - pi.residueDegree P.1 ≤
          finrank K (cubicThroughCoordinateSections p hp n
            (fun i => g (chartCoordinate (equationIdeal p hp) j i)) hpx) := by
  classical
  intro S pi
  letI := AllCharacteristics.pointAlgebra pi P.1
  letI : Module.Finite K (S.residueField P.1) :=
    AllCharacteristics.closedPoint_moduleFinite pi P
  letI hClosed : IsClosedImmersion (S.fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  obtain ⟨j, g, hgs, hgbase, hgpoint⟩ :=
    @PfaffianDescent.closed_projective_point_chart K (S.residueField P.1)
      (inferInstance : Field K) (Scheme.instFieldCarrierResidueField S P.1)
      (AllCharacteristics.pointAlgebra pi P.1) (Fin 4) (equationIdeal p hp)
      (S.fromSpecResidueField P.1) hClosed
      (AllCharacteristics.pointAlgebra_spec pi P.1).symm
  have hpI : p ∈ (equationIdeal p hp).toIdeal :=
    Ideal.subset_span (Set.mem_singleton p)
  have hpx := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem
    (equationIdeal p hp) j p hpI)
  rw [hom_eval₂, hgbase, map_zero] at hpx
  refine ⟨j, g, hgbase, hgpoint, hpx, ?_⟩
  have h := cubicThroughCoordinateSections_finrank_lower_bound p hp hp0 n
    (fun i => g (chartCoordinate (equationIdeal p hp) j i)) hpx
  rw [AllCharacteristics.closedPoint_finrank_eq_residueDegree pi P] at h
  exact h

end PfaffianDescent.Coray
end
