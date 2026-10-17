import PfaffianDescent.CorayOriginalQuinticPolynomialResidual
import PfaffianDescent.CoplanarConicDescent
import PfaffianDescent.ProjectiveClosedPointCoordinates
import PfaffianDescent.HomogeneousChartPrime
import PfaffianDescent.LinearChartCoordinates
import PfaffianDescent.CorayMinimalPointSelection
import AllCharacteristics.ClosedPointAlgebra

/-! SOURCE ONLY / UNVERIFIED. Construct the actual coordinate dichotomy of
the SAME original degree-five closed point. The dependent branch constructs
its actual plane equation and uses the conic residual. The independent branch
uses the actual polynomial residual, retaining the full original residue
field and original ground field. No noncoplanarity or smaller point premise.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem recoveredChart_homogeneous_zero_mem_point
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (g : ChartRing I j →+* L)
    (hgbase : g.comp (chartBaseMap I j) = algebraMap K L)
    (P : scheme I)
    (hgpoint : chartι I j (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L)) = P)
    (a : MvPolynomial (Fin 4) K) (n : ℕ) (ha : a.IsHomogeneous n)
    (hzero : a.eval₂ (algebraMap K L) (fun i => g (chartCoordinate I j i)) = 0) :
    Ideal.Quotient.mk I.toIdeal a ∈ P.asHomogeneousIdeal.toIdeal := by
  let z := coordinate I j
  let hz : z ∈ grading I 1 := coordinate_mem I j
  have hfrac : g (Away.mk (grading I) hz n (Ideal.Quotient.mk I.toIdeal a)
      (by simpa using polynomial_class_mem_grading I a ha)) = 0 := by
    rw [← eval₂_linearChartCoordinate_eq_fraction I z hz a ha]
    change g (a.eval₂ (chartBaseMap I j) (chartCoordinate I j)) = 0
    rw [hom_eval₂, hgbase]
    exact hzero
  have hmem : Ideal.Quotient.mk I.toIdeal a ∈
      (chartι I j (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L))).asHomogeneousIdeal.toIdeal := by
    apply (homogeneousChart_prime_membership (grading I) z hz
      (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L)) n
      (Ideal.Quotient.mk I.toIdeal a) (polynomial_class_mem_grading I a ha)).mpr
    change g (Away.mk (grading I) hz n (Ideal.Quotient.mk I.toIdeal a)
      (by simpa using polynomial_class_mem_grading I a ha)) ∈
        (IsLocalRing.closedPoint L).asIdeal
    rw [hfrac]
    exact Ideal.zero_mem _
  rw [hgpoint] at hmem
  exact hmem

private theorem dependentCoordinates_actual_plane
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (g : ChartRing I j →+* L)
    (hgbase : g.comp (chartBaseMap I j) = algebraMap K L)
    (P : scheme I)
    (hgpoint : chartι I j (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L)) = P)
    (hdep : ¬ LinearIndependent K (fun i => g (chartCoordinate I j i))) :
    ∃ c : Fin 4 → K, c ≠ 0 ∧
      Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c) ∈ P.asHomogeneousIdeal.toIdeal := by
  classical
  obtain ⟨c, hcSum, i, hci⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hc : c ≠ 0 := by
    intro hz
    apply hci
    exact congrFun hz i
  have hell : (homogeneousLinearForm c).IsHomogeneous 1 := by
    unfold homogeneousLinearForm
    exact IsHomogeneous.sum _ _ _ (fun k _ => isHomogeneous_C_mul_X (c k) k)
  have heval : (homogeneousLinearForm c).eval₂ (algebraMap K L)
      (fun k => g (chartCoordinate I j k)) = 0 := by
    simpa only [homogeneousLinearForm, eval₂_sum, eval₂_mul, eval₂_C, eval₂_X,
      Algebra.smul_def] using hcSum
  exact ⟨c, hc, recoveredChart_homogeneous_zero_mem_point
    I j g hgbase P hgpoint (homogeneousLinearForm c) 1 hell heval⟩

/-- The actual original degree-five closed point supplies a smaller actual
original-K closed point prime to three. Coplanarity/noncoplanarity is derived
from its canonical residue chart, not supplied. Characteristic zero is the
honest restriction inherited from the independent-coordinate normalization.
No smoothness, genus, GI, auxiliary selection, or image-rank premise. -/
theorem originalCubic_degree_five_closedPoint_exists_smaller_closedPoint
    {K : Type u} [Field K] [CharZero K]
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (P : closedPoints (hypersurface f hf))
    (hP : (hypersurfaceToBase f hf).residueDegree P.1 = 5) :
    ∃ R : closedPoints (hypersurface f hf),
      Nat.Coprime ((hypersurfaceToBase f hf).residueDegree R.1) 3 ∧
      (hypersurfaceToBase f hf).residueDegree R.1 ≤ 4 ∧
      (hypersurfaceToBase f hf).residueDegree R.1 <
        (hypersurfaceToBase f hf).residueDegree P.1 := by
  classical
  letI : Infinite K := Infinite.of_injective (fun n : ℕ => (n : K)) Nat.cast_injective
  let S := hypersurface f hf
  let I := equationIdeal f hf
  let L := S.residueField P.1
  letI := pointAlgebra (hypersurfaceToBase f hf) P.1
  letI : Module.Finite K L := closedPoint_moduleFinite (hypersurfaceToBase f hf) P
  letI hclosed : IsClosedImmersion (S.fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  have hdim : Module.finrank K L = 5 :=
    (closedPoint_finrank_eq_residueDegree (hypersurfaceToBase f hf) P).trans hP
  obtain ⟨j, g, _hgs, hgbase, hgpoint⟩ := @closed_projective_point_chart
    K L (inferInstance : Field K) (inferInstance : Field L)
    (pointAlgebra (hypersurfaceToBase f hf) P.1) (Fin 4)
    I (S.fromSpecResidueField P.1) hclosed
    (pointAlgebra_spec (hypersurfaceToBase f hf) P.1).symm
  let x : Vec L 4 := fun i => g (chartCoordinate I j i)
  have hpoint : chartι I j (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L)) = P.1 := by
    change (Spec.map (CommRingCat.ofHom g) ≫ chartι I j) (IsLocalRing.closedPoint L) = P.1
    rw [hgpoint]
    exact Scheme.fromSpecResidueField_apply (X := S) P.1 _
  by_cases hx : LinearIndependent K x
  · have hfx : f.eval₂ (algebraMap K L) x = 0 := by
      have h := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I j f
        (Ideal.subset_span (Set.mem_singleton f)))
      rw [hom_eval₂, hgbase, map_zero] at h
      exact h
    obtain ⟨R, hRcop, hRle, hRsmall⟩ :=
      originalNoncoplanarQuintic_exists_smaller_originalCubic_closedPoint hdim f hf x hx hfx
    exact ⟨R, hRcop, hRle, by simpa only [hP] using hRsmall⟩
  · obtain ⟨c, hc, hplane⟩ := dependentCoordinates_actual_plane I j g hgbase P.1 hpoint hx
    obtain ⟨s, hs⟩ := cubic_coplanar_degree_five_conic_descent f hf P hP c hc hplane
    obtain ⟨R, hR⟩ := closedPoint_degree_one_of_section (hypersurfaceToBase f hf) s hs
    refine ⟨R, ?_, ?_, ?_⟩
    · rw [hR]
      decide
    · rw [hR]
      decide
    · rw [hR, hP]
      decide

end PfaffianDescent.Coray
