import AllCharacteristics.KollarUniversalSecantHomogeneousDetection
import AllCharacteristics.SmoothCubicGenericSecantPreimage
import AllCharacteristics.KollarResidualBaseChange

/-! The actual generic target constructs the preimage and
all six parameters. The only geometric center input is the field-stable
no-contained-line property proved by the residual-center basechange route.
No dominance, target genericity, chosen frame, or preimage certificate is an
input of this witness assembly. -/

noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry HomogeneousProjective PfaffianDescent MvPolynomial
universe u

set_option backward.isDefEq.respectTransparency false in
theorem universal_secant_generic_witness_of_geometric_centers
    {k L K : Type u} [Field k] [Field L] [Field K] [IsAlgClosed K]
    (α : k →+* L) (β : L →+* K)
    (c0 : Cubic k 4) (hhom : c0.toMvPolynomial.IsHomogeneous 3)
    (hc0 : c0.toMvPolynomial ≠ 0)
    [Smooth (hypersurfaceToBase c0.toMvPolynomial hhom)]
    (p q : Fin 4 → L)
    (hp : (c0.map α).eval p = 0) (hq : (c0.map α).eval q = 0)
    (hpq : (c0.map α).mixed p q ≠ 0) (hqp : (c0.map α).mixed q p ≠ 0)
    (hnoP : GeometricallyNoContainedLineThrough ((c0.map α).map β) (fun i => β (p i)))
    (hnoQ : GeometricallyNoContainedLineThrough ((c0.map α).map β) (fun i => β (q i)))
    (kp kq : Fin 4)
    (hkp : (MvPolynomial.pderiv kp (c0.map α).toMvPolynomial).eval p ≠ 0)
    (hkq : (MvPolynomial.pderiv kq (c0.map α).toMvPolynomial).eval q ≠ 0)
    (a b : L) (hab : a ≠ b) :
    let M := hyperplaneInclusion (fun i => (MvPolynomial.pderiv i (c0.map α).toMvPolynomial).eval p) kp
    let N := hyperplaneInclusion (fun i => (MvPolynomial.pderiv i (c0.map α).toMvPolynomial).eval q) kq
    let r := universalTwoTangentSecantPolynomial (c0.map α) p q M N a b
    r ≠ 0 ∧ ∀ (G : MvPolynomial (Fin 4) k) (d : ℕ), G.IsHomogeneous d →
      G.eval₂ ((algebraMap (MvPolynomial ConjugateTangentParameterIndex L)
        (FractionRing (MvPolynomial ConjugateTangentParameterIndex L))).comp (MvPolynomial.C.comp α))
        (fun i => algebraMap (MvPolynomial ConjugateTangentParameterIndex L)
          (FractionRing (MvPolynomial ConjugateTangentParameterIndex L)) (r i)) = 0 →
      G ∈ Ideal.span ({c0.toMvPolynomial} : Set (MvPolynomial (Fin 4) k)) := by
  let cL := c0.map α
  let cK := cL.map β
  let FK := c0.toMvPolynomial.map (β.comp α)
  have hFK : FK.IsHomogeneous 3 := hhom.map (β.comp α)
  have hFK0 : FK ≠ 0 := by
    intro hzero
    exact hc0 (MvPolynomial.map_injective (β.comp α) (β.comp α).injective
      (by simpa only [map_zero] using hzero))
  letI : Smooth (hypersurfaceToBase FK hFK) :=
    smooth_hypersurfaceToBase_map (β.comp α) c0.toMvPolynomial hhom
  letI : (Ideal.span ({FK} : Set (MvPolynomial (Fin 4) K))).IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic FK hFK hFK0
  have hcK : cK.toMvPolynomial = FK := by
    rw [Cubic.toMvPolynomial_map, Cubic.toMvPolynomial_map, MvPolynomial.map_map]
  have hhomK : cK.toMvPolynomial.IsHomogeneous 3 := by rw [hcK]; exact hFK
  letI : Smooth (hypersurfaceToBase cK.toMvPolynomial hhomK) :=
    (smooth_hypersurfaceToBase_congr FK cK.toMvPolynomial hFK hhomK hcK.symm).mp inferInstance
  let E := cubicGenericTargetField FK
  let κ : K →+* E := cubicGenericTargetCoefficientMap FK
  let z : Fin 4 → E := cubicGenericTargetCoordinates FK
  let f : L →+* E := κ.comp β
  let M := hyperplaneInclusion (fun i => (MvPolynomial.pderiv i cL.toMvPolynomial).eval p) kp
  let N := hyperplaneInclusion (fun i => (MvPolynomial.pderiv i cL.toMvPolynomial).eval q) kq
  let r := universalTwoTangentSecantPolynomial cL p q M N a b
  have hpK : cK.eval (fun i => β (p i)) = 0 := by rw [Cubic.eval_map, hp, map_zero]
  have hqK : cK.eval (fun i => β (q i)) = 0 := by rw [Cubic.eval_map, hq, map_zero]
  have hpqK : cK.mixed (fun i => β (p i)) (fun i => β (q i)) ≠ 0 := by
    rw [Cubic.mixed_map]
    exact (map_ne_zero β).mpr hpq
  have hqpK : cK.mixed (fun i => β (q i)) (fun i => β (p i)) ≠ 0 := by
    rw [Cubic.mixed_map]
    exact (map_ne_zero β).mpr hqp
  have hz : (cK.map κ).eval z = 0 := cubicGenericTargetCoordinates_on_cubic FK cK hcK
  have hgeneric : ∀ P : MvPolynomial (Fin 4) K,
      P ≠ 0 → P.totalDegree ≤ 2 → P.eval₂ κ z ≠ 0 :=
    fun P hP hd => cubicGenericTarget_lowDegree_ne_zero FK hFK hFK0 P hP hd
  have hnoZ : Cubic.NoContainedLineThrough (cK.map κ) z :=
    cubicGenericTarget_no_contained_line FK hFK hFK0 cK hcK
  obtain ⟨dp, dq, s, hdp, hdq, hs, -, -, hpre⟩ :=
    exists_two_tangent_secant_preimage_of_smooth_generic_target κ cK hhomK
      (fun i => β (p i)) (fun i => β (q i)) hpK hqK hpqK hqpK hnoP hnoQ z hz hgeneric hnoZ
  let u : Fin 3 → E := fun j => dp (kp.succAbove j)
  let v : Fin 3 → E := fun j => dq (kq.succAbove j)
  have hu : (M.map f).mulVec u = dp :=
    mapped_tangentHyperplane_direction_eq_matrix_coordinates f cL p dp kp hkp hdp
  have hv : (N.map f).mulVec v = dq :=
    mapped_tangentHyperplane_direction_eq_matrix_coordinates f cL q dq kq hkq hdq
  obtain ⟨params, hparams⟩ := exists_raw_universal_secant_specialization_of_preimage
    f cL p q M N a b hab dp dq z s u v hu hv hpre
  have hr : r ≠ 0 := by
    let A := MvPolynomial ConjugateTangentParameterIndex L
    exact polynomial_coordinate_vector_ne_zero_of_nonzero_specialization
      (RingHom.id A) Function.injective_id (MvPolynomial.eval₂Hom f params)
      r z (cubicGenericTargetCoordinates_ne_zero FK hFK hFK0) s hs hparams
  refine ⟨hr, ?_⟩
  intro G d hG hzero
  exact homogeneous_relations_of_universal_secant_actual_preimage α β c0.toMvPolynomial
    cL p q M N a b hab dp dq u v hu hv s hs hpre G d hG hzero

end AllCharacteristics
