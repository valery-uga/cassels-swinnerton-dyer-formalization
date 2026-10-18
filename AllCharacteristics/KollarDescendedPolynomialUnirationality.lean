import AllCharacteristics.KollarUniversalSourceCubicEvaluation
import AllCharacteristics.HomogeneousRelationDescentAlongScaling
import AllCharacteristics.PolynomialSecantDescentCubic

namespace AllCharacteristics

open AlgebraicGeometry HomogeneousProjective PfaffianDescent MvPolynomial

universe u

/-- Exact constant scalar descent transfers the raw universal family's
homogeneous relation detector to an actual dominant rational map from affine
nine-space over the original ground field. -/
theorem isUnirationalOver_of_kollar_descended_raw_detector
    {k : Type u} [Field k]
    {L : Type u} [Field L]
    [Algebra (FractionRing (MvPolynomial (Fin 3) k)) L]
    (c : Cubic k 4) (hhom : c.toMvPolynomial.IsHomogeneous 3)
    [IrreducibleSpace (hypersurface c.toMvPolynomial hhom)]
    (r : Fin 4 → MvPolynomial ConjugateTangentParameterIndex L)
    (R : Fin 4 → KollarUniversalLocalizedParameterRing k) (s : L)
    (hr : r ≠ 0) (hs : s ≠ 0)
    (hR : ∀ i, MvPolynomial.map
      (algebraMap (FractionRing (MvPolynomial (Fin 3) k)) L) (R i) =
        MvPolynomial.C s * r i)
    (hRc : ((c.map (algebraMap k (FractionRing (MvPolynomial (Fin 3) k)))).map
      (MvPolynomial.C : FractionRing (MvPolynomial (Fin 3) k) →+*
        KollarUniversalLocalizedParameterRing k)).eval R = 0)
    (hrawdetect : ∀ (G : MvPolynomial (Fin 4) k) (d : ℕ), G.IsHomogeneous d →
      G.eval₂ ((algebraMap (MvPolynomial ConjugateTangentParameterIndex L)
        (FractionRing (MvPolynomial ConjugateTangentParameterIndex L))).comp
          (MvPolynomial.C.comp
            ((algebraMap (FractionRing (MvPolynomial (Fin 3) k)) L).comp
              (algebraMap k (FractionRing (MvPolynomial (Fin 3) k))))))
        (fun i => algebraMap (MvPolynomial ConjugateTangentParameterIndex L)
          (FractionRing (MvPolynomial ConjugateTangentParameterIndex L)) (r i)) = 0 →
        G ∈ Ideal.span ({c.toMvPolynomial} : Set (MvPolynomial (Fin 4) k))) :
    IsUnirationalOver k (hypersurface c.toMvPolynomial hhom)
      (hypersurfaceToBase c.toMvPolynomial hhom) := by
  let K0 := FractionRing (MvPolynomial (Fin 3) k)
  let B := MvPolynomial ConjugateTangentParameterIndex L
  let T := FractionRing B
  let α : K0 →+* L := algebraMap K0 L
  let μ : KollarUniversalLocalizedParameterRing k →+* B := MvPolynomial.map α
  let ι : B →+* T := algebraMap B T
  let κT : k →+* T := ι.comp (MvPolynomial.C.comp (α.comp (algebraMap k K0)))
  have hbase : (ι.comp μ).comp (kollarUniversalLocalizedCoefficientMap k) = κT := by
    rw [RingHom.comp_assoc, kollarUniversalLocalizedCoefficientMap_map]
  have hsC : (MvPolynomial.C s : B) ≠ 0 := by
    simpa only [ne_eq, MvPolynomial.C_eq_zero] using hs
  have hR0 : R ≠ 0 := descended_polynomial_vector_ne_zero r R s hs hr hR
  apply isUnirationalOver_hypersurface_of_kollarUniversalPolynomial
    c.toMvPolynomial hhom R hR0 (kollarUniversalPolynomial_cubic_equation c R hRc)
  intro G d hG hzero
  exact homogeneous_relation_of_descent_scaling_after_embedding
    μ ι (IsFractionRing.injective B T)
    (kollarUniversalLocalizedCoefficientMap k) κT hbase R r
    (MvPolynomial.C s) hsC hR (Ideal.span {c.toMvPolynomial}) hrawdetect
    G d hG hzero

end AllCharacteristics
