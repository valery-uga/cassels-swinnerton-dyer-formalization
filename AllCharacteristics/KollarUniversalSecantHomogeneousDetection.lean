import AllCharacteristics.KollarGenericTargetOriginalRelations
import AllCharacteristics.KollarUniversalSecantParameterPreimage
import AllCharacteristics.HomogeneousRelationsFromPolynomialSpecialization

/-! The raw polynomial secant, its actual geometric
preimage, and the explicit generic target field yield homogeneous relation
detection over the original field. There is no genericity, dominance, or
chosen rational-map-domain hypothesis in this assembly. -/

noncomputable section
namespace AllCharacteristics
open PfaffianDescent MvPolynomial
universe u

theorem homogeneous_relations_of_universal_secant_actual_preimage
    {k L K : Type u} [Field k] [Field L] [Field K]
    (α : k →+* L) (β : L →+* K)
    (F : MvPolynomial (Fin 4) k)
    [(Ideal.span ({F.map (β.comp α)} : Set (MvPolynomial (Fin 4) K))).IsPrime]
    (c : Cubic L 4) (p q : Fin 4 → L)
    (M N : Matrix (Fin 4) (Fin 3) L) (a b : L) (hab : a ≠ b)
    (dp dq : Fin 4 → cubicGenericTargetField (F.map (β.comp α)))
    (u v : Fin 3 → cubicGenericTargetField (F.map (β.comp α)))
    (hu : (M.map ((cubicGenericTargetCoefficientMap (F.map (β.comp α))).comp β)).mulVec u = dp)
    (hv : (N.map ((cubicGenericTargetCoefficientMap (F.map (β.comp α))).comp β)).mulVec v = dq)
    (s : cubicGenericTargetField (F.map (β.comp α))) (hs : s ≠ 0)
    (hpre : Cubic.secantResidualPoint
      (c.map ((cubicGenericTargetCoefficientMap (F.map (β.comp α))).comp β))
      (Cubic.tangentResidualPoint
        (c.map ((cubicGenericTargetCoefficientMap (F.map (β.comp α))).comp β))
        (fun i => ((cubicGenericTargetCoefficientMap (F.map (β.comp α))).comp β) (p i)) dp)
      (Cubic.tangentResidualPoint
        (c.map ((cubicGenericTargetCoefficientMap (F.map (β.comp α))).comp β))
        (fun i => ((cubicGenericTargetCoefficientMap (F.map (β.comp α))).comp β) (q i)) dq) =
      s • cubicGenericTargetCoordinates (F.map (β.comp α)))
    (G : MvPolynomial (Fin 4) k) (d : ℕ) (hG : G.IsHomogeneous d)
    (hzero : G.eval₂
      ((algebraMap (MvPolynomial ConjugateTangentParameterIndex L)
        (FractionRing (MvPolynomial ConjugateTangentParameterIndex L))).comp
          (MvPolynomial.C.comp α))
      (fun i => algebraMap (MvPolynomial ConjugateTangentParameterIndex L)
        (FractionRing (MvPolynomial ConjugateTangentParameterIndex L))
          (universalTwoTangentSecantPolynomial c p q M N a b i)) = 0) :
    G ∈ Ideal.span ({F} : Set (MvPolynomial (Fin 4) k)) := by
  let E := cubicGenericTargetField (F.map (β.comp α))
  let A := MvPolynomial ConjugateTangentParameterIndex L
  let Q := FractionRing A
  let κ := cubicGenericTargetCoefficientMap (F.map (β.comp α))
  let f : L →+* E := κ.comp β
  let r := universalTwoTangentSecantPolynomial c p q M N a b
  obtain ⟨params, hparams⟩ := exists_raw_universal_secant_specialization_of_preimage
    f c p q M N a b hab dp dq (cubicGenericTargetCoordinates (F.map (β.comp α)))
    s u v hu hv hpre
  let ψ : A →+* E := MvPolynomial.eval₂Hom f params
  have hbase : ψ.comp (MvPolynomial.C.comp α) = κ.comp (β.comp α) := by
    ext x
    exact MvPolynomial.eval₂_C f params (α x)
  apply homogeneous_relations_of_polynomial_specialization
    (MvPolynomial.C.comp α) (algebraMap A Q) (IsFractionRing.injective A Q)
    ψ (κ.comp (β.comp α)) hbase r
    (cubicGenericTargetCoordinates (F.map (β.comp α))) s hs hparams
    (Ideal.span {F}) _ G d hG hzero
  intro H e he hH
  exact cubicGenericTarget_original_relation_detection (β.comp α) F H hH

end AllCharacteristics
