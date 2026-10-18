import AllCharacteristics.KollarSmoothGenericResidual
import AllCharacteristics.ResidualTangentPolynomialData

namespace AllCharacteristics

open AlgebraicGeometry HomogeneousProjective PfaffianDescent MvPolynomial Polynomial

universe u

abbrev KollarGenericLineField (k : Type u) [Field k] :=
  FractionRing (MvPolynomial (Fin 3) k)

noncomputable abbrev kollarGenericMappedCubic
    {k : Type u} [Field k] (c : Cubic k 4) : Cubic (KollarGenericLineField k) 4 :=
  c.map (algebraMap k (KollarGenericLineField k))

noncomputable abbrev kollarGenericMappedBasePoint
    (k : Type u) [Field k] : Fin 4 → KollarGenericLineField k :=
  fun i => algebraMap k (KollarGenericLineField k) (kollarBasePoint k i)

/-- A normalized smooth cubic, over any ground field, constructs the entire
descended universal polynomial family.  The field extension, involution,
valid tangent pivot, and scalar descent are all produced internally. -/
theorem exists_kollarNormalized_descended_polynomial_family
    {k : Type u} [Field k] (c : Cubic k 4)
    (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hp : c.eval (kollarBasePoint k) = 0)
    (hsec : c.mixed (kollarBasePoint k)
      (kollarAffineLineDirection k (fun _ => 0)) ≠ 0)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hhom)] :
    letI : Fact (Irreducible (kollarGenericResidualPolynomial c)) :=
      ⟨kollarGenericResidualPolynomial_irreducible_of_smooth c hhom hp hsec⟩
    letI : Fact (Irreducible (Cubic.lineResidualPolynomial
        (kollarGenericMappedCubic c) (kollarGenericMappedBasePoint k)
        (kollarGenericProjectiveLineDirection k))) := ⟨by
      change Irreducible (kollarGenericResidualPolynomial c)
      exact kollarGenericResidualPolynomial_irreducible_of_smooth c hhom hp hsec⟩
    ∃ (σ : AdjoinRoot (kollarGenericResidualPolynomial c) ≃ₐ[KollarGenericLineField k]
        AdjoinRoot (kollarGenericResidualPolynomial c)) (j : Fin 4)
      (s : AdjoinRoot (kollarGenericResidualPolynomial c))
      (R : Fin 4 → MvPolynomial ConjugateTangentParameterIndex (KollarGenericLineField k)),
      σ ≠ AlgEquiv.refl ∧
      (MvPolynomial.pderiv j
        ((kollarGenericMappedCubic c).map
          (algebraMap (KollarGenericLineField k) (AdjoinRoot (kollarGenericResidualPolynomial c)))).toMvPolynomial).eval
        (residualLineRootPoint (kollarGenericMappedCubic c) (kollarGenericMappedBasePoint k)
          (kollarGenericProjectiveLineDirection k)) ≠ 0 ∧
      s ≠ 0 ∧
      (∀ i, MvPolynomial.map
        (algebraMap (KollarGenericLineField k) (AdjoinRoot (kollarGenericResidualPolynomial c)))
        (R i) = MvPolynomial.C s * residualLineUniversalSecantPolynomial
          (kollarGenericMappedCubic c) (kollarGenericMappedBasePoint k)
          (kollarGenericProjectiveLineDirection k) σ j i) ∧
      ((kollarGenericMappedCubic c).map MvPolynomial.C).eval R = 0 := by
  let K0 := KollarGenericLineField k
  let c0 := kollarGenericMappedCubic c
  let p0 := kollarGenericMappedBasePoint k
  let d0 := kollarGenericProjectiveLineDirection k
  let q0 := Cubic.lineResidualPolynomial c0 p0 d0
  have hp0 : c0.eval p0 = 0 := by
    change (c.map (algebraMap k K0)).eval
      (fun i => algebraMap k K0 (kollarBasePoint k i)) = 0
    rw [Cubic.eval_map, hp, map_zero]
  have hsec0 : c0.mixed p0 d0 ≠ 0 :=
    kollar_generic_projective_line_secantCoefficient_ne_zero c hsec
  have hdir0 : c0.eval d0 ≠ 0 :=
    kollar_generic_projective_line_eval_ne_zero_of_smooth c.toMvPolynomial hhom c rfl hsec
  have hirr0 : Irreducible q0 :=
    kollarGenericResidualPolynomial_irreducible_of_smooth c hhom hp hsec
  have hsep0 : q0.Separable :=
    kollarGenericResidualPolynomial_separable_of_smooth c hhom hp hsec
  letI : Fact (Irreducible q0) := ⟨hirr0⟩
  letI : Fact (Irreducible (Cubic.lineResidualPolynomial
      (kollarGenericMappedCubic c) (kollarGenericMappedBasePoint k)
      (kollarGenericProjectiveLineDirection k))) := ⟨by
    change Irreducible q0
    exact hirr0⟩
  obtain ⟨σ, j, hσ, hj, _⟩ := exists_residualLine_universal_conjugate_tangent_pair
    c0 p0 d0 hp0 hsec0 hdir0 hirr0 hsep0
  obtain ⟨s, R, hs, hR, hRc⟩ := exists_descended_residualLineUniversalSecantPolynomial
    c0 p0 d0 hp0 hdir0 hirr0 hsep0 σ hσ j hj
  exact ⟨σ, j, s, R, hσ, hj, hs, hR, hRc⟩

end AllCharacteristics
