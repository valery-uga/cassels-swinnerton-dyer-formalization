import PfaffianDescent.PerfectFieldClosedQuarticOriginalTangentSubscheme
import PfaffianDescent.ActualP3QuadraticRestrictionChartComparison

/-! UNVERIFIED draft: the same original-point construction with its dimension
stated using genuine ideal-sheaf global sections. No new input certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem perfectField_closedQuarticPoint_exists_original_tangentSubscheme_actualHZero
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (h4 : (hypersurfaceToBase p hp).residueDegree x.1 = 4)
    (hspan : ProjectiveGeometricGeneralPosition (equationIdeal p hp)
      ((hypersurface p hp).fromSpecResidueField x.1)) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) x.1
    letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) x
    let L := (hypersurface p hp).residueField x.1
    letI : Module.Finite K (DualNumber L) := QuarticNet.dualNumber_moduleFinite
    ∃ q : Spec (.of (DualNumber L)) ⟶ hypersurface p hp,
      ∃ hq : IsClosedImmersion q,
        letI : IsClosedImmersion q := hq
        q ≫ hypersurfaceToBase p hp =
          Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber L))) ∧
        Set.range q = {x.1} ∧
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom L L L).toRingHom) ≫ q =
          (hypersurface p hp).fromSpecResidueField x.1 ∧
        ∃ hfinite : IsFinite (q ≫ hypersurfaceToBase p hp),
          @AllCharacteristics.finiteSchemeRank K _ _ (q ≫ hypersurfaceToBase p hp) hfinite = 8 ∧
          (∃ (J : Type u) (_ : Fintype J), Fintype.card J = 4 ∧
            Nonempty (pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
              (q ≫ hypersurfaceToBase p hp) ≅
              ∐ fun _ : J => Spec (.of (DualNumber (AlgebraicClosure K))))) ∧
          3 ≤ finrank K (SchemeModuleGlobalSectionsOver
            (ambientToBase (R := K) (σ := Fin 4))
            (closedImmersionIdealTwist
              (q ≫ hypersurfaceToAmbient p hp)
              (ProjectiveNegativeTwist.positiveSheafOfModules
                (homogeneousSubmodule (Fin 4) K) 2))) := by
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) x.1
  letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) x
  let L := (hypersurface p hp).residueField x.1
  letI : Module.Finite K (DualNumber L) := QuarticNet.dualNumber_moduleFinite
  obtain ⟨q, hq, hbase, hsupport, hreduce, hfinite, hrank, hsplit, hdim⟩ :=
    perfectField_closedQuarticPoint_exists_original_tangentSubscheme p hp hp0 x h4 hspan
  letI : IsClosedImmersion q := hq
  refine ⟨q, hq, hbase, hsupport, hreduce, hfinite, hrank, hsplit, ?_⟩
  rw [p3ActualIdealQuadratic_finrank_eq_intrinsic]
  exact hdim


/-- The noncoplanar actual closed point supplies geometric spanning internally. -/
@[irreducible]
def perfectField_noncoplanarClosedQuarticPoint_exists_original_tangentSubscheme_actualHZero
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (h4 : (hypersurfaceToBase p hp).residueDegree x.1 = 4)
    (hplane : ¬ ∃ c : Fin 4 → K, c ≠ 0 ∧
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm c) ∈
        x.1.asHomogeneousIdeal.toIdeal) :=
  perfectField_closedQuarticPoint_exists_original_tangentSubscheme_actualHZero p hp hp0 x h4
    (perfectField_cubic_closedPoint_degree_four_general_position p hp x h4 hplane)

end PfaffianDescent
