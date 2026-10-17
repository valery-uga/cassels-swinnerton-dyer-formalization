import PfaffianDescent.CorayActualComponentHilbertDegree
import AllCharacteristics.FiniteSchemeCycle

/-!
# Same actual component hyperplane cycle realizes its intrinsic Hilbert degree

The original p/q minimal-component caller constructs the actual finite linear
section. Its own native fundamental cycle, including all actual multiplicities
and full ORIGINAL-K residue degrees, pushes along the literal quotient immersion
with degree equal to that component's actual coordinate Hilbert degree. The
section, cycle and degree are all constructed; none is a desired certificate.
SOURCE ONLY / UNVERIFIED; root owns compiler/audit.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Construct the ACTUAL hyperplane section and its own native fundamental
cycle, on the SAME original selected prime component, with genuine geometric
cycle degree identified with its actual coordinate Hilbert degree. -/
theorem selectedProjectiveMinimalComponent_exists_linearSectionCycle_hilbertDegree
    {K : Type u} [Field K] [Infinite K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ∃ (H : MvPolynomial (Fin 4) K) (hH : H.IsHomogeneous 1), H ∉ C.toIdeal ∧
      ∃ hfinite : IsFinite (toBase (C ⊔ equationIdeal H hH)),
        letI := hfinite
        let i := PfaffianDescent.schemeQuotientMap C (C ⊔ equationIdeal H hH) le_sup_left
        letI := PfaffianDescent.schemeQuotientMap_closedImmersion C (C ⊔ equationIdeal H hH) le_sup_left
        ∃ zS : EffectiveZeroCycle (scheme (C ⊔ equationIdeal H hH)),
          EffectiveZeroCycle.degree (toBase C) (pushforwardClosedCycle i zS) =
              actualCurveCoordinateHilbertDegree C ∧
            actualCurveCoordinateHilbertDegree C ≤ 3 * n := by
  classical
  letI : C.toIdeal.IsPrime := hCmin.isPrime
  obtain ⟨H, hH, hnotC, hfinite, _N, _hN, hbound⟩ :=
    selectedProjectiveMinimalComponent_exists_affineHilbertFunction p q hp hp0 n hq hnot C hCmin
  let S := C ⊔ equationIdeal H hH
  letI : IsFinite (toBase S) := hfinite
  let i := PfaffianDescent.schemeQuotientMap C S le_sup_left
  letI : IsClosedImmersion i := PfaffianDescent.schemeQuotientMap_closedImmersion C S le_sup_left
  have hbase : i ≫ toBase C = toBase S := PfaffianDescent.schemeQuotientMap_toBase C S le_sup_left
  have hdegree : actualCurveCoordinateHilbertDegree C = finiteSchemeRank (toBase S) :=
    (primeComponent_linearSection_degree_and_eventualIncrement C H hH hnotC).1
  obtain ⟨zS, hzS⟩ := exists_effectiveZeroCycle_degree_finiteSchemeRank (toBase S)
  refine ⟨H, hH, hnotC, hfinite, zS, ?_, hdegree.trans_le hbound⟩
  rw [degree_pushforwardClosedCycle, hbase, hzS]
  exact hdegree.symm

end PfaffianDescent.Coray
