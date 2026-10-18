import AllCharacteristics.UniversalSecantPolynomial
import AllCharacteristics.ConjugateParameterSplitting
import AllCharacteristics.ConjugateUniversalTangentCoordinates
import AllCharacteristics.TangentHyperplaneCoordinateSurjectivity

/-! Convert actual tangent directions into the six raw
Weil parameters using the checked inverse pair map. This is an exact vector
specialization and does not depend on a rational map's chosen domain. -/

noncomputable section
namespace AllCharacteristics
open PfaffianDescent MvPolynomial
open scoped BigOperators
universe u

/-- The original gradient matrix covers every tangent direction after any
field extension, with coordinates obtained simply by omitting the pivot. -/
theorem mapped_tangentHyperplane_direction_eq_matrix_coordinates
    {L E : Type u} [Field L] [Field E] (f : L →+* E)
    (c : Cubic L 4) (p : Fin 4 → L) (d : Fin 4 → E)
    (k : Fin 4) (hk : (MvPolynomial.pderiv k c.toMvPolynomial).eval p ≠ 0)
    (hd : (c.map f).mixed (fun i => f (p i)) d = 0) :
    ((hyperplaneInclusion (fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval p) k).map f).mulVec
      (fun j => d (k.succAbove j)) = d := by
  rw [map_hyperplaneInclusion]
  apply hyperplaneInclusion_mulVec_coordinateOmission_of_dot_eq_zero _ k
    (fun h => hk (f.injective (by simpa using h))) d
  rw [mixed_map_eq_gradient_dot] at hd
  simpa only [mul_comm] using hd

/-- Two independently prescribed matrix tangent directions are represented
by one common six-parameter tuple at the two distinct residual roots. -/
theorem exists_weil_parameters_for_two_matrix_directions
    {L E : Type u} [Field L] [Field E] (f : L →+* E)
    (M N : Matrix (Fin 4) (Fin 3) L) (a b : L) (hab : a ≠ b)
    (dp dq : Fin 4 → E) (u v : Fin 3 → E)
    (hu : (M.map f).mulVec u = dp) (hv : (N.map f).mulVec v = dq) :
    ∃ z : ConjugateTangentParameterIndex → E,
      (M.map f).mulVec (fun j => z (0, j) + f a * z (1, j)) = dp ∧
      (N.map f).mulVec (fun j => z (0, j) + f b * z (1, j)) = dq := by
  have habE : f a ≠ f b := fun h => hab (f.injective h)
  obtain ⟨w, hw⟩ := (conjugateAffinePair_bijective (f a) (f b) habE).surjective (u, v)
  let z : ConjugateTangentParameterIndex → E := fun ij =>
    if ij.1 = 0 then w.1 ij.2 else w.2 ij.2
  have hfirst : (fun j => z (0, j) + f a * z (1, j)) = u := by
    funext j
    have h := congrFun (congrArg Prod.fst hw) j
    simpa [z, conjugateAffinePair] using h
  have hsecond : (fun j => z (0, j) + f b * z (1, j)) = v := by
    funext j
    have h := congrFun (congrArg Prod.snd hw) j
    simpa [z, conjugateAffinePair] using h
  refine ⟨z, ?_, ?_⟩
  · rw [hfirst]
    exact hu
  · rw [hsecond]
    exact hv

/-- Every scaled secant preimage formed by actual tangent directions lifts
to an exact specialization of the universal raw polynomial coordinates. -/
theorem exists_raw_universal_secant_specialization_of_preimage
    {L E : Type u} [Field L] [Field E] (f : L →+* E)
    (c : Cubic L 4) (p q : Fin 4 → L)
    (M N : Matrix (Fin 4) (Fin 3) L) (a b : L) (hab : a ≠ b)
    (dp dq target : Fin 4 → E) (s : E)
    (u v : Fin 3 → E) (hu : (M.map f).mulVec u = dp) (hv : (N.map f).mulVec v = dq)
    (hpre : Cubic.secantResidualPoint (c.map f)
      (Cubic.tangentResidualPoint (c.map f) (fun i => f (p i)) dp)
      (Cubic.tangentResidualPoint (c.map f) (fun i => f (q i)) dq) = s • target) :
    ∃ z : ConjugateTangentParameterIndex → E,
      (fun i => MvPolynomial.eval₂ f z (universalTwoTangentSecantPolynomial c p q M N a b i)) =
        s • target := by
  obtain ⟨z, hzM, hzN⟩ := exists_weil_parameters_for_two_matrix_directions
    f M N a b hab dp dq u v hu hv
  refine ⟨z, ?_⟩
  rw [eval₂_universalTwoTangentSecantPolynomial, hzM, hzN]
  exact hpre

end AllCharacteristics
