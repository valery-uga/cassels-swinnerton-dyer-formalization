import PfaffianDescent.CorayActualSmoothCubicGenericNoTangency
import AllCharacteristics.HomogeneousChartEvaluation
import AllCharacteristics.ProjectivePointCoordinates

/-! SOURCE ONLY / UNVERIFIED149. Construct the literal chart field-point map
from original normalized coordinates, then consume source148's genuine actual
no-tangency producer. The public normalized-point caller assumes neither a
chart map nor a nonzero-gradient nor a generic smooth-section conclusion. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Normalized coordinates satisfying the original equation construct an
actual homomorphism from the original chart ring, with its original coefficient
map and the SAME coordinate values. -/
theorem normalizedHomogeneousPoint_exists_actualChartHom
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d)
    (x : Fin 4 → M) (j : Fin 4) (hxj : x j = 1)
    (hpx : MvPolynomial.aeval x p = 0) :
    ∃ g : ChartRing (equationIdeal p hp) j →+* M,
      g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M ∧
      ∀ i, g (chartCoordinate (equationIdeal p hp) j i) = x i := by
  let I := equationIdeal p hp
  let f : MvPolynomial (Fin 4) K →+* M := MvPolynomial.eval₂Hom (algebraMap K M) x
  have hker : I.toIdeal ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    rintro q hq
    obtain rfl := Set.mem_singleton_iff.mp hq
    exact hpx
  let e : CoordinateRing I →+* M := Ideal.Quotient.lift I.toIdeal f hker
  have hecoord (i : Fin 4) : e (coordinate I i) = x i := by
    exact (Ideal.Quotient.lift_mk I.toIdeal (a := MvPolynomial.X i) f hker).trans
      (MvPolynomial.eval₂Hom_X' (algebraMap K M) x i)
  have hej : e (coordinate I j) = 1 := (hecoord j).trans hxj
  let g : ChartRing I j →+* M :=
    AllCharacteristics.GradedChart.liftCoordinateOne (grading I) (coordinate I j) e hej
  refine ⟨g, ?_, ?_⟩
  · apply RingHom.ext
    intro a
    change AllCharacteristics.GradedChart.liftCoordinateOne (grading I) (coordinate I j) e hej
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := coordinate I j) a) = algebraMap K M a
    rw [AllCharacteristics.GradedChart.liftCoordinateOne_baseMap]
    change e (Ideal.Quotient.mk I.toIdeal (MvPolynomial.C a)) = algebraMap K M a
    exact (Ideal.Quotient.lift_mk I.toIdeal (a := MvPolynomial.C a) f hker).trans
      (MvPolynomial.eval₂Hom_C (algebraMap K M) x a)
  · intro i
    change g (AllCharacteristics.GradedChart.normalized (grading I)
      (coordinate_mem I j) (coordinate I i) (coordinate_mem I i)) = x i
    rw [AllCharacteristics.GradedChart.liftCoordinateOne_normalized]
    exact hecoord i

/-- Original cubic smoothness and actual normalized coordinates internally
produce the chart field map and nonzero gradient. The literal generic plane
normal cannot equal the cubic gradient up to ANY scalar. -/
theorem smoothCubic_normalizedPoint_not_genericHyperplane_normal
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    [Algebra (GenericHyperplaneField K) M]
    [IsScalarTower K (GenericHyperplaneField K) M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : Fin 4 → M) (j : Fin 4) (hxj : x j = 1)
    (hpx : MvPolynomial.aeval x p = 0) :
    ¬ ∃ c : M,
      MvPolynomial.aeval x (MvPolynomial.pderiv (0 : Fin 4) p) = c ∧
      ∀ i : Fin 3,
        MvPolynomial.aeval x (MvPolynomial.pderiv i.succ p) =
          c * algebraMap (GenericHyperplaneField K) M
            (genericHyperplaneCoefficient (K := K) i) := by
  obtain ⟨g, hbase, hg⟩ :=
    normalizedHomogeneousPoint_exists_actualChartHom p hp x j hxj hpx
  have hx : (fun i => g (chartCoordinate (equationIdeal p hp) j i)) = x := funext hg
  have h := smoothCubic_actualFieldPoint_not_genericHyperplane_normal p hp hp0 j g hbase
  dsimp only at h
  rw [hx] at h
  exact h

end PfaffianDescent.Coray
