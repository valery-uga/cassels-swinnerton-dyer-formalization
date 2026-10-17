import PfaffianDescent.PerfectFieldConjugateQuartets
import PfaffianDescent.ProjectiveGeneralPosition
import PfaffianDescent.FieldPointOpenFactorization
import PfaffianDescent.CubicSurfacePointEvaluation
import PfaffianDescent.HomogeneousChartPrime

/-! The actual geometric scheme points of a nonplanar field point of degree
four or five are in general position over a perfect field. A common linear
chart is descended from one geometric point; its coordinates and all four
geometric evaluations are recovered from the literal scheme morphisms. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem fieldPoint_linearChart_coordinates_independent
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (i : Spec (.of L) ⟶ scheme I)
    (hplane : ¬ ∃ c : Fin 4 → K, c ≠ 0 ∧
      Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c) ∈
        (i (IsLocalRing.closedPoint L)).asHomogeneousIdeal)
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (g : Away (grading I) z →+* L)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) =
      algebraMap K L)
    (hpoint : Spec.map (CommRingCat.ofHom g) ≫
      Proj.awayι (grading I) z hz (by decide : 0 < 1) = i) :
    LinearIndependent K (fun j => g (linearChartCoordinate I z hz j)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  have heval : (homogeneousLinearForm c).eval₂ (algebraMap K L)
      (fun j => g (linearChartCoordinate I z hz j)) = 0 := by
    simpa only [homogeneousLinearForm, eval₂_sum, eval₂_mul, eval₂_C, eval₂_X,
      Algebra.smul_def] using hc
  have hfrac : g (Away.mk (grading I) hz 1
      (Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c))
      (polynomial_class_mem_grading I (homogeneousLinearForm c)
        (homogeneousLinearForm_isHomogeneous c))) = 0 := by
    rw [← eval₂_linearChartCoordinate_eq_fraction I z hz
      (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c),
      hom_eval₂, hbase]
    exact heval
  have hmem : Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c) ∈
      (i (IsLocalRing.closedPoint L)).asHomogeneousIdeal := by
    have hpt := congrArg (fun f => f (IsLocalRing.closedPoint L)) hpoint
    change Proj.awayι (grading I) z hz (by decide : 0 < 1)
      (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L)) =
        i (IsLocalRing.closedPoint L) at hpt
    rw [← hpt]
    apply (homogeneousChart_prime_membership (grading I) z hz
      (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L)) 1
      (Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c))
      (polynomial_class_mem_grading I _ (homogeneousLinearForm_isHomogeneous c))).mpr
    change g _ ∈ (IsLocalRing.closedPoint L).asIdeal
    rw [hfrac]
    exact Ideal.zero_mem _
  have hc0 : c = 0 := by
    by_contra h
    exact hplane ⟨c, h, hmem⟩
  exact congrFun hc0 j

theorem perfectField_fieldPoint_projectiveGeometricGeneralPosition
    {K L : Type u} [Field K] [PerfectField K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (i : Spec (.of L) ⟶ scheme I)
    (hi : i ≫ toBase I = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hdim : finrank K L = 4 ∨ finrank K L = 5)
    (hplane : ¬ ∃ c : Fin 4 → K, c ≠ 0 ∧
      Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c) ∈
        (i (IsLocalRing.closedPoint L)).asHomogeneousIdeal) :
    ProjectiveGeometricGeneralPosition I i := by
  classical
  intro z hz q hq hqbase e he c hc
  let α : Fin 4 → (L →ₐ[K] AlgebraicClosure K) := fun k =>
    { __ := (Spec.preimage (q k)).hom
      commutes' := by
        intro a
        have heq : CommRingCat.ofHom (algebraMap K L) ≫ Spec.preimage (q k) =
            CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) := by
          apply Spec.map_injective
          rw [Spec.map_comp, Spec.map_preimage, ← hi]
          exact hqbase k
        exact congrArg (fun f => f.hom a) heq }
  have hα (k : Fin 4) : Spec.map (CommRingCat.ofHom (α k).toRingHom) = q k :=
    Spec.map_preimage (q k)
  have hαinj : Function.Injective α := by
    intro k l h
    apply hq
    rw [← hα k, ← hα l, h]
  let j : Spec (.of (Away (grading I) z)) ⟶ scheme I :=
    Proj.awayι (grading I) z hz (by decide : 0 < 1)
  letI : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (Proj.awayι (grading I) z hz (by decide : 0 < 1)))
  have hjbase : j ≫ toBase I = Spec.map
      (CommRingCat.ofHom (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))) := by
    change Proj.awayι (grading I) z hz (by decide : 0 < 1) ≫
      (Proj.toSpecZero (grading I) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (grading I 0)))) = _
    rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    rfl
  have h0 : Spec.map (CommRingCat.ofHom (α 0).toRingHom) ≫ i =
      Spec.map (CommRingCat.ofHom (e 0)) ≫ j := by
    rw [hα]
    exact (he 0).symm
  let l := fieldPointOpenLift j i (α 0).toRingHom
    (Spec.map (CommRingCat.ofHom (e 0))) h0
  let g : Away (grading I) z →+* L := (Spec.preimage l).hom
  have hg : Spec.map (CommRingCat.ofHom g) = l := Spec.map_preimage l
  have hpoint : Spec.map (CommRingCat.ofHom g) ≫ j = i := by
    rw [hg]
    exact fieldPointOpenLift_fac j i (α 0).toRingHom
      (Spec.map (CommRingCat.ofHom (e 0))) h0
  have hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) =
      algebraMap K L := by
    have heq : CommRingCat.ofHom
        (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) ≫
        CommRingCat.ofHom g = CommRingCat.ofHom (algebraMap K L) := by
      apply Spec.map_injective
      rw [Spec.map_comp, ← hjbase, ← Category.assoc, hpoint]
      exact hi
    exact congrArg CommRingCat.Hom.hom heq
  have hcomp (k : Fin 4) : (α k).toRingHom.comp g = e k := by
    have heq : CommRingCat.ofHom g ≫ CommRingCat.ofHom (α k).toRingHom =
        CommRingCat.ofHom (e k) := by
      apply Spec.map_injective
      apply (cancel_mono j).mp
      rw [Spec.map_comp, Category.assoc, hpoint, hα]
      exact (he k).symm
    exact congrArg CommRingCat.Hom.hom heq
  let p : Fin 4 → L := fun j => g (linearChartCoordinate I z hz j)
  have hp : LinearIndependent K p :=
    fieldPoint_linearChart_coordinates_independent I i hplane z hz g hbase hpoint
  let M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K) := fun k j => α k (p j)
  have hrow : LinearIndependent (AlgebraicClosure K) M.row :=
    perfectField_conjugate_quartet_independent hdim p hp α hαinj
  have hcol : LinearIndependent (AlgebraicClosure K) M.col :=
    Matrix.linearIndependent_col_iff_row.mpr hrow
  have hsum : ∑ j, c j • M.col j = 0 := by
    funext k
    change (∑ j, c j • M.col j) k = 0
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
    have hcoords (j : Fin 4) : e k (linearChartCoordinate I z hz j) = M k j := by
      change e k _ = (α k).toRingHom.comp g _
      rw [hcomp]
    simpa only [hcoords] using hc k
  exact funext (Fintype.linearIndependent_iff.mp hcol c hsum)

end PfaffianDescent
