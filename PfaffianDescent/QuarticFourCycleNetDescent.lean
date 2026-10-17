import PfaffianDescent.QuarticFourCycleQuadricBasis
import PfaffianDescent.QuarticJetNet
import PfaffianDescent.QuarticNetKoszul
import PfaffianDescent.QuarticFourCycleIndependence
import PfaffianDescent.PolynomialIdealDescent

/-!
# Descent of the four-cycle finite tangent net

The finite four-cycle calculation over a splitting field likewise descends
the three-quadric ideal membership to the original ground field.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial Module

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

theorem cubic_mem_ground_ideal_of_fourCycle_geometric_net
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (hQ : ∀ i, (Q i).IsHomogeneous 2) (hQI : LinearIndependent k Q)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (b c d e : K)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hQvan : ∀ i : Fin 3, ∀ r : Fin 4,
      aeval (tangentDualPoint (skewTangentDirections 0 b c d e 0) r)
        (linearSubstitution M (map (algebraMap k K) (Q i))) = 0)
    (hFvan : ∀ r : Fin 4,
      aeval (tangentDualPoint (skewTangentDirections 0 b c d e 0) r)
        (linearSubstitution M (map (algebraMap k K) F)) = 0) :
    F ∈ Ideal.span (Set.range Q) := by
  let G : Fin 3 → MvPolynomial (Fin 4) K :=
    fun i => linearSubstitution M (map (algebraMap k K) (Q i))
  have hG : ∀ i, (G i).IsHomogeneous 2 :=
    fun i => linearSubstitution_homogeneous M ((hQ i).map (algebraMap k K))
  have hGI : LinearIndependent K G :=
    (polynomial_linearIndependent_map Q hQI).map'
      (linearSubstitutionEquiv M hM).toLinearEquiv.toLinearMap
      (LinearMap.ker_eq_bot.mpr (linearSubstitutionEquiv M hM).injective)
  have hmem (i : Fin 3) : G i ∈
      Ideal.span (Set.range (fourCycleScaledQuadricPolynomials b c d e)) :=
    homogeneous_tangent_quadric_mem_fourCycleScaled_ideal b c d e hb hc hd he
      (G i) (hG i) (hQvan i)
  have heq : Ideal.span (Set.range G) =
      Ideal.span (Set.range (fourCycleScaledQuadricPolynomials b c d e)) :=
    quadric_ideal_eq_of_independent G (fourCycleScaledQuadricPolynomials b c d e)
      hG (fourCycleScaledQuadricPolynomials_homogeneous b c d e) hmem hGI
  have hFmem : linearSubstitution M (map (algebraMap k K) F) ∈
      Ideal.span (Set.range (fourCycleScaledQuadricPolynomials b c d e)) :=
    cubic_mem_fourCycleScaled_ideal_of_nonzero_tangent_vanishing b c d e hb hc hd he
      (linearSubstitution M (map (algebraMap k K) F))
      (linearSubstitution_homogeneous M (hF.map (algebraMap k K))) hFvan
  rw [← heq] at hFmem
  exact polynomial_mem_span_of_linearSubstitution_map_range_descends M hM Q F hFmem

end QuarticNet
end PfaffianDescent
