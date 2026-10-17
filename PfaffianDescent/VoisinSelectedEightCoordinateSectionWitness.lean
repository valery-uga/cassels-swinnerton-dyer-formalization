import PfaffianDescent.VoisinSelectedVectorCoordinateSpecialization
import PfaffianDescent.VoisinNormalizedQuadraticMinor
import PfaffianDescent.VoisinQuadraticGenericKernelRank
import PfaffianDescent.VoisinQuadraticMinorOpenChart
import PfaffianDescent.VoisinSelectedSplitPencilComparison
import PfaffianDescent.VoisinPulledChartEquationVanishing

/-!
# The selected eight-point witness has regular relative coordinates

The integral affine ordered chart now carries eight by four regular
coordinate sections whose selected-fiber values are the normalized
vectors. The same witness has the unit quadratic minor and the proper
finite étale degree-eight member.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_generic_eight_selected_coordinate_sections_with_minor
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      ((genericCubicTensor K).map φ)
    Smooth (hypersurfaceToBase p hp) ∧
      ∃ (y : Fin 8 → Fin 4 → L)
        (hzero : ∀ k, p.eval (y k) = 0)
        (c : Fin 4 → L)
        (hc : ∀ k, (homogeneousLinearForm c).eval (y k) ≠ 0)
        (m : Fin 8 ↪ AllCharacteristics.UniversalHomogeneous.Monomials (Fin 4) 2)
        (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
        (hInt : IsIntegral (cubicConfigurationBase p hp 8)),
        letI : IsIntegral (cubicConfigurationBase p hp 8) := hInt
        ∃
        (U Q : Scheme.{u}) (_ : IsAffine U) (_ : IsAffine Q)
        (i : U ⟶ (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).left)
        (j : Q ⟶ cubicConfigurationBase p hp 8)
        (r : U ⟶ Q)
        (a : Spec (.of L) ⟶ U)
        (tBase : U ⟶ Spec (.of L))
        (t : Fin 8 → (U ⟶ Spec (.of
          (Away (grading (equationIdeal p hp))
            (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
              (homogeneousLinearForm c))))))
        (x : Fin 8 → Fin 4 → Γ(U, ⊤))
        (f : Γ(U, ⊤) →+* L)
        (hminor : IsUnit (eightPointQuadraticEvaluationMinor m
          (fun k j => f (x k j))).det)
        (b : Module.Basis (Fin 2) (FractionRing Γ(U, ⊤))
          (LinearMap.ker (Matrix.toLin'
            (eightPointQuadraticEvaluationMatrix
              (fun k j => algebraMap Γ(U, ⊤)
                (FractionRing Γ(U, ⊤)) (x k j))))))
        (g : Localization.Away (quadraticMinorDet m x) →+* L),
        IsOpenImmersion i ∧ IsOpenImmersion j ∧ Surjective r ∧
        IsIntegralHom r ∧ IsFinite r ∧
        IsIntegral U ∧ IsIntegral Q ∧
        genericPoint (cubicConfigurationBase p hp 8) ∈ Set.range j ∧
        i ≫ configurationQuotientMap (equationIdeal p hp) 8 = r ≫ j ∧
        Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
        DegreeEightQuadraticRestrictionKernelProperMemberExists p hp D ∧
        Function.Surjective
          (homogeneousSectionRestriction (K := L)
            (fun j i => y i j) 2) ∧
        (∀ i, (X 1 * X 2 : MvPolynomial (Fin 4) L).eval (y i) = 0 ∧
          (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval (y i) = 0) ∧
        IsUnit (eightPointQuadraticEvaluationMinor m y).det ∧
        IsUnit (eightPointQuadraticEvaluationMinor m
          (fun k => normalizedVectorInLinearChart c (y k))).det ∧
        IsUnit ((eightPointQuadraticEvaluationMinor m x).map
          (algebraMap Γ(U, ⊤) (FractionRing Γ(U, ⊤)))).det ∧
        Module.finrank (FractionRing Γ(U, ⊤))
          (LinearMap.ker (Matrix.toLin'
            (eightPointQuadraticEvaluationMatrix
              (fun k j => algebraMap Γ(U, ⊤)
                (FractionRing Γ(U, ⊤)) (x k j))))) = 2 ∧
        IsUnit ((eightPointQuadraticEvaluationMinor m x).map
          (algebraMap Γ(U, ⊤)
            (Localization.Away (quadraticMinorDet m x)))).det ∧
        g.comp (algebraMap Γ(U, ⊤)
          (Localization.Away (quadraticMinorDet m x))) =
            (Scheme.ΓSpecIso (.of L)).hom.hom.comp a.appTop.hom ∧
        a ≫ tBase = 𝟙 (Spec (.of L)) ∧
        f = (Scheme.ΓSpecIso (.of L)).hom.hom.comp a.appTop.hom ∧
        (∀ k j, f (x k j) = normalizedVectorInLinearChart c (y k) j) ∧
        (∀ k, (p.map (affineFunctionHom tBase)).eval (x k) = 0) ∧
        (∀ k, ((homogeneousLinearForm c).map
          (affineFunctionHom tBase)).eval (x k) = 1) ∧
        Submodule.span L (Set.range
          (quadraticSelectedOpenBasisSpecializedHomogeneous m x f hminor)) =
            Submodule.span L (Set.range (splitQuadraticPencil L)) ∧
        (∀ k j, a.appTop.hom (x k j) =
          (StructureSheaf.globalSectionsIso L).hom
            (normalizedVectorInLinearChart c (y k) j)) ∧
        (∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
          (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
            (homogeneousLinearForm c))
          (polynomial_class_mem_grading (equationIdeal p hp)
            (homogeneousLinearForm c)
            (homogeneousLinearForm_isHomogeneous c))
          (by decide : 0 < 1) =
          (i ≫ Over.Hom.left
            (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
            (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left) ∧
        x = pulledEightLinearChartCoordinates (equationIdeal p hp)
          (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
            (homogeneousLinearForm c))
          (polynomial_class_mem_grading (equationIdeal p hp)
            (homogeneousLinearForm c)
            (homogeneousLinearForm_isHomogeneous c)) U t ∧
        tBase = i ≫
          (orderedFamilyConfigurationOver
            (hypersurfaceToBase p hp) 8).hom := by
  dsimp only
  let p := ((genericCubicTensor K).map φ).toMvPolynomial
  let hp := cubic_toMvPolynomial_isHomogeneous_three
    ((genericCubicTensor K).map φ)
  obtain ⟨hsmooth, y, hzero, c, hc, m, A, B, D, hm,
    hcoord, hAB, hD, hEt, hmember, hsurj, hquadrics, hInt,
    U, Q, hUa, hQa, i, j, r, hi, hj, hsurjr, hintr, hfinr, hUi, hQi,
    hAi, hBj, hgenericQ, hcomm, hinside, ⟨a, ha⟩, ht⟩ :=
    exists_generic_eight_properMember_affineChart_reaching_generic K φ
  let t (k : Fin 8) := Classical.choose (ht k)
  have ht' (k : Fin 8) := Classical.choose_spec (ht k)
  let z : CoordinateRing (equationIdeal p hp) :=
    Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm c)
  have hz : z ∈ grading (equationIdeal p hp) 1 :=
    polynomial_class_mem_grading (equationIdeal p hp)
      (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
  let x := pulledEightLinearChartCoordinates (equationIdeal p hp) z hz U t
  have hy (k : Fin 8) :
      ∀ q ∈ (equationIdeal p hp).toIdeal, q.eval (y k) = 0 :=
    cubicVector_zero_equationIdeal p hp (y k) (hzero k)
  have hx : ∀ k j, a.appTop.hom (x k j) =
      (StructureSheaf.globalSectionsIso L).hom
        (normalizedVectorInLinearChart c (y k) j) :=
    pulledEightLinearChartCoordinates_value_of_selectedConfiguration
      (equationIdeal p hp) c y hy hc U i A a ha t ht' hcoord
  have hnorm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k => normalizedVectorInLinearChart c (y k))).det :=
    eightPointQuadraticEvaluationMinor_isUnit_det_normalized y c hc m hm
  letI : IsIntegral U := hUi
  haveI : IsDomain Γ(U, ⊤) := inferInstance
  let f : Γ(U, ⊤) →+* L :=
    (Scheme.ΓSpecIso (.of L)).hom.hom.comp a.appTop.hom
  have hf (k : Fin 8) (j : Fin 4) :
      f (x k j) = normalizedVectorInLinearChart c (y k) j := by
    have h := congrArg
      (fun s : Γ(Spec (.of L), ⊤) =>
        (Scheme.ΓSpecIso (.of L)).hom.hom s) (hx k j)
    have hcancel :
        (Scheme.ΓSpecIso (.of L)).hom.hom
          ((StructureSheaf.globalSectionsIso L).hom
            (normalizedVectorInLinearChart c (y k) j)) =
          normalizedVectorInLinearChart c (y k) j :=
      (Scheme.ΓSpecIso (.of L)).inv_hom_id_apply _
    exact h.trans hcancel
  have hnorm' : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (x k j))).det := by
    convert hnorm using 1
    congr 2
    funext k j
    exact hf k j
  have hgeneric : IsUnit ((eightPointQuadraticEvaluationMinor m x).map
      (algebraMap Γ(U, ⊤) (FractionRing Γ(U, ⊤)))).det :=
    eightPointQuadraticEvaluationMinor_generic_unit f m x hnorm'
  have hminorF : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => algebraMap Γ(U, ⊤)
        (FractionRing Γ(U, ⊤)) (x k j))).det := by
    rw [← eightPointQuadraticEvaluationMinor_map]
    exact hgeneric
  have hkernel : Module.finrank (FractionRing Γ(U, ⊤))
      (LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix
          (fun k j => algebraMap Γ(U, ⊤)
            (FractionRing Γ(U, ⊤)) (x k j))))) = 2 :=
    eightPointQuadraticEvaluationMatrix_kernel_finrank_two
      (fun k j => algebraMap Γ(U, ⊤)
        (FractionRing Γ(U, ⊤)) (x k j)) m hminorF
  let b := eightPointQuadraticEvaluationMatrix_kernelBasis
    (fun k j => algebraMap Γ(U, ⊤)
      (FractionRing Γ(U, ⊤)) (x k j)) m hminorF
  let g := quadraticMinorSelectedPointLift m x f hnorm'
  have hopen : IsUnit ((eightPointQuadraticEvaluationMinor m x).map
      (algebraMap Γ(U, ⊤)
        (Localization.Away (quadraticMinorDet m x)))).det :=
    quadraticMinor_isUnit_on_principalOpen m x
  have hg : g.comp (algebraMap Γ(U, ⊤)
      (Localization.Away (quadraticMinorDet m x))) = f :=
    quadraticMinorSelectedPointLift_comp m x f hnorm'
  have hcomp : Submodule.span L (Set.range
      (quadraticSelectedOpenBasisSpecializedHomogeneous m x f hnorm')) =
        Submodule.span L (Set.range (splitQuadraticPencil L)) :=
    quadraticSelectedOpenBasisSpecialized_span_eq_split_pencil
      m x f hnorm' y c hc hf hsurj hquadrics
  let tBase : U ⟶ Spec (.of L) :=
    i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom
  have hA : A ≫ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).hom = 𝟙 (Spec (.of L)) := by
    obtain ⟨hB, _⟩ := hD
    have hmap := configurationQuotientMap_toBase (equationIdeal p hp) 8
    have h₁ := congrArg
      (fun z : (orderedFamilyConfigurationOver
        (toBase (equationIdeal p hp)) 8).left ⟶ Spec (.of L) => A ≫ z) hmap
    have h₂ := congrArg
      (fun z : Spec (.of L) ⟶ cubicConfigurationBase p hp 8 =>
        z ≫ cubicConfigurationToBase p hp 8) hAB
    calc
      A ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom =
          A ≫ (configurationQuotientMap (equationIdeal p hp) 8 ≫
            configurationQuotientToBase (equationIdeal p hp) 8) := h₁.symm
      _ = (A ≫ configurationQuotientMap (equationIdeal p hp) 8) ≫
          configurationQuotientToBase (equationIdeal p hp) 8 :=
            (Category.assoc _ _ _).symm
      _ = B ≫ cubicConfigurationToBase p hp 8 := h₂
      _ = 𝟙 (Spec (.of L)) := hB
  have hat : a ≫ tBase = 𝟙 (Spec (.of L)) := by
    dsimp [tBase]
    rw [← Category.assoc, ha]
    exact hA
  have hpvan : ∀ k, (p.map (affineFunctionHom tBase)).eval (x k) = 0 := by
    have hp_mem : p ∈ (equationIdeal p hp).toIdeal := by
      change p ∈ Ideal.span {p}
      exact Ideal.subset_span (Set.mem_singleton p)
    exact pulledEightLinearChartCoordinates_equation_zero
      (equationIdeal p hp) z hz U i t ht' p hp hp_mem
  have hnormone : ∀ k, ((homogeneousLinearForm c).map
      (affineFunctionHom tBase)).eval (x k) = 1 := by
    exact pulledEightLinearChartCoordinates_denominator_one
      (equationIdeal p hp) c U i t ht'
  exact ⟨hsmooth, y, hzero, c, hc, m, D, hInt,
    U, Q, hUa, hQa, i, j, r, a, tBase, t, x, f, hnorm', b, g,
    hi, hj, hsurjr, hintr, hfinr, hUi, hQi, hgenericQ, hcomm,
    hEt, hmember, hsurj, hquadrics, hm, hnorm, hgeneric, hkernel,
    hopen, hg, hat, rfl, hf, hpvan, hnormone, hcomp, hx, ht', rfl, rfl⟩

end PfaffianDescent
