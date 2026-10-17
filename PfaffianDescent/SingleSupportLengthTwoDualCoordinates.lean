import PfaffianDescent.LengthTwoLocalDualClassification
import PfaffianDescent.SingleSupportProjectiveCoordinates
import PfaffianDescent.AmbientNormalizedChartAlgebraNaturality
import PfaffianDescent.FourTangentDualCoordinates

/-! Universal actual-scheme parametrization of a supplied local length-two
subscheme over an algebraically closed field. This applies independently to
each of four geometric components, without arithmetic descent hypotheses. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every supplied singleton-support length-two subscheme has its OWN dual
algebra and generating coordinates. The exact original ambient immersion
is recovered after the actual Spec equivalence; no equation/geometry
comparison or fabricated locality is an input. -/
theorem singleSupport_lengthTwo_actual_dual_coordinates
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)] (P : closedPoints (scheme I))
    (hSupport : Set.range i = {P.1}) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    (AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 2) →
    ∃ (j : Fin 4) (x : Fin 4 → Γ(Z, ⊤)) (hxj : x j = 1)
      (eA : Γ(Z, ⊤) ≃ₐ[K] DualNumber K) (a v : Fin 4 → K),
      a j = 1 ∧ v j = 0 ∧ v ≠ 0 ∧
      (∀ r, eA (x r) = TrivSqZeroExt.inl (a r) + TrivSqZeroExt.inr (v r)) ∧
      Function.Surjective (aeval (R := K) (fun r => eA (x r))) ∧
      ambientNormalizedCoordinateChartPoint (F := K) (fun r => eA (x r)) j
        (by rw [hxj, map_one]) =
        Spec.map (CommRingCat.ofHom eA.toRingHom) ≫ Z.isoSpec.inv ≫ i ≫ quotientProjMap I := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  intro hZ
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  letI : IsLocalRing Γ(Z, ⊤) := singleSupport_globalSections_isLocalRing i P.1 hSupport
  have hA : finrank K Γ(Z, ⊤) = 2 :=
    (finiteSchemeCoefficient_finrank (i ≫ toBase I)).trans hZ
  obtain ⟨e0⟩ := lengthTwoLocal_dual_equiv hA
  let eA := e0.symm
  obtain ⟨j, g, hgs, hgb, hpoint⟩ := singleSupport_projective_actual_chart I i P hSupport
  let x : Fin 4 → Γ(Z, ⊤) := fun r => g (chartCoordinate I j r)
  have hxj : x j = 1 := by simp only [x, chartCoordinate_self, map_one]
  have heval : (aeval (R := K) x).toRingHom =
      g.comp (eval₂Hom (chartBaseMap I j) (chartCoordinate I j)) := by
    apply RingHom.ext
    intro p
    change p.eval₂ (algebraMap K Γ(Z, ⊤)) x = g (p.eval₂ _ _)
    rw [hom_eval₂, hgb]
  have hgen : Function.Surjective (aeval (R := K) x) := by
    change Function.Surjective (aeval (R := K) x).toRingHom
    rw [heval]
    exact hgs.comp (eval₂_chartCoordinate_surjective I j)
  let a : Fin 4 → K := fun r => (eA (x r)).fst
  let v : Fin 4 → K := fun r => (eA (x r)).snd
  have hcomp : eA.toAlgHom.comp (aeval (R := K) x) =
      aeval (R := K) (fun r => eA (x r)) := by
    apply MvPolynomial.algHom_ext
    intro r
    simp only [AlgHom.comp_apply, aeval_X]
    rfl
  have hdualgen : Function.Surjective (aeval (R := K) (fun r => eA (x r))) := by
    rw [← hcomp]
    exact eA.surjective.comp hgen
  have hv : v ≠ 0 := by
    intro hv0
    have hconstant : aeval (R := K) (fun r => eA (x r)) =
        (TrivSqZeroExt.inlAlgHom K K K).comp (aeval (R := K) a) := by
      apply MvPolynomial.algHom_ext
      intro r
      simp only [AlgHom.comp_apply, aeval_X]
      apply TrivSqZeroExt.ext
      · rfl
      · change v r = 0
        exact congrFun hv0 r
    obtain ⟨p, hp⟩ := hdualgen (TrivSqZeroExt.inr (1 : K))
    rw [hconstant] at hp
    have h := congrArg TrivSqZeroExt.snd hp
    exact (zero_ne_one : (0 : K) ≠ 1) (by simpa using h)
  refine ⟨j, x, hxj, eA, a, v, ?_, ?_, hv, ?_, hdualgen, ?_⟩
  · simp [a, hxj]
  · simp [v, hxj]
  · intro r
    exact (TrivSqZeroExt.inl_fst_add_inr_snd_eq (eA (x r))).symm
  · change ambientNormalizedCoordinateChartPoint (F := K)
        (fun r => eA.toAlgHom (x r)) j _ =
      Spec.map (CommRingCat.ofHom eA.toAlgHom.toRingHom) ≫
        Z.isoSpec.inv ≫ i ≫ quotientProjMap I
    rw [ambientNormalizedCoordinateChartPoint_algHom eA.toAlgHom x j hxj]
    rw [ambientNormalizedCoordinateChartPoint_eq_original_chart I j g hgb,
      ← Category.assoc (Spec.map (CommRingCat.ofHom g)), hpoint]
    simp only [Category.assoc]

end PfaffianDescent
