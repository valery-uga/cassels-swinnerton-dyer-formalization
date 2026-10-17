import PfaffianDescent.CorayGenericHyperplaneNoTangency
import PfaffianDescent.SmoothCubicFieldPointChartGradient

/-! SOURCE ONLY / UNVERIFIED148. The actual original smooth cubic and actual
field-point chart construct all normalized-point and nonzero-gradient data
internally. This is the actual no-tangency producer needed for generic smooth
plane-section assembly; it does not claim the still-missing native scheme
smoothness/integrality or elliptic line-bundle section bound. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- At every actual chart point, after ANY field extension of the generic
hyperplane field, the gradient of the original smooth cubic cannot be
proportional to the literal generic hyperplane normal (1,t_0,t_1,t_2).
The actual chart equation, normalized coordinate, coefficient independence,
and nonzero gradient all come from their constructions inside the proof. -/
theorem smoothCubic_actualFieldPoint_not_genericHyperplane_normal
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    [Algebra (GenericHyperplaneField K) M]
    [IsScalarTower K (GenericHyperplaneField K) M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (j : Fin 4) (g : ChartRing (equationIdeal p hp) j →+* M)
    (hbase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M) :
    let x : Fin 4 → M := fun i => g (chartCoordinate (equationIdeal p hp) j i)
    ¬ ∃ c : M,
      MvPolynomial.aeval x (MvPolynomial.pderiv (0 : Fin 4) p) = c ∧
      ∀ i : Fin 3,
        MvPolynomial.aeval x (MvPolynomial.pderiv i.succ p) =
          c * algebraMap (GenericHyperplaneField K) M
            (genericHyperplaneCoefficient (K := K) i) := by
  let x : Fin 4 → M := fun i => g (chartCoordinate (equationIdeal p hp) j i)
  change ¬ ∃ c : M,
    MvPolynomial.aeval x (MvPolynomial.pderiv (0 : Fin 4) p) = c ∧
    ∀ i : Fin 3,
      MvPolynomial.aeval x (MvPolynomial.pderiv i.succ p) =
        c * algebraMap (GenericHyperplaneField K) M
          (genericHyperplaneCoefficient (K := K) i)
  rintro ⟨c, hc0, hcs⟩
  have hxj : x j = 1 := by simp only [x, chartCoordinate_self, map_one]
  have hpx : MvPolynomial.aeval x p = 0 := by
    have hz := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem
      (equationIdeal p hp) j p (Ideal.subset_span (Set.mem_singleton p)))
    rw [hom_eval₂, hbase, map_zero] at hz
    exact hz
  obtain ⟨a, ha⟩ :=
    PfaffianDescent.smoothCubic_fieldPoint_chart_exists_nonzero_retained_partial
      p hp hp0 j g hbase
  change MvPolynomial.aeval x (MvPolynomial.pderiv a.1 p) ≠ 0 at ha
  have hc : c ≠ 0 := by
    intro hczero
    have hall : ∀ i : Fin 4, MvPolynomial.aeval x (MvPolynomial.pderiv i p) = 0 := by
      intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · exact hc0.trans hczero
      · rw [hcs k, hczero, zero_mul]
    exact ha (hall a.1)
  have hg0 : MvPolynomial.aeval x (MvPolynomial.pderiv (0 : Fin 4) p) ≠ 0 := by
    rw [hc0]
    exact hc
  apply genericHyperplane_no_normalizedPoint_gradientRatios p hp hp0 x j hxj hpx hg0
  intro i
  rw [hc0]
  exact hcs i

end PfaffianDescent.Coray
