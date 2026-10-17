import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeTensorMatrix

/-! The literal actual evaluator constructs an integral affine
configuration chart on which the actual native matrix has rank six. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreActualEvaluation_exists_integral_affine_rank_chart
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {X B : Scheme.{u}} [IsIntegral B] {N : X.Modules}
    (base : X ⟶ Spec (.of F)) (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : finrank F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (marked : Fin 3 → (B ⟶ X)) (c : Spec (.of E) ⟶ B)
    (r : Fin 3 → (Spec (.of E) ⟶ X)) (hpoint : ∀ i, c ≫ marked i = r i)
    (hr : ∀ i, r i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F E)))
    (honto : Function.Surjective
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        base r hr (show X.Modules from e.E))) :
    ∃ (A : Scheme.{u}) (a : A ⟶ B) (chart : Fin 3 → C.ι)
      (markedA : ∀ i, A ⟶ (C.U (chart i)).toScheme)
      (cA : Spec (.of E) ⟶ A),
      IsAffine A ∧ IsOpenImmersion a ∧ IsIntegral A ∧ cA ≫ a = c ∧
      (∀ i, markedA i ≫ (C.U (chart i)).ι = a ≫ marked i) ∧
      Function.Surjective (Matrix.toLin'
        ((serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart markedA).map
          (fieldPointΓevaluation cA))) := by
  obtain ⟨A, a, chart, markedA, hAffine, hOpen, hc, hmarkedA⟩ :=
    serreIncidenceNativeAffineChart_exists_at e C marked (c (IsLocalRing.closedPoint E))
  letI : IsAffine A := hAffine
  letI : IsOpenImmersion a := hOpen
  have hrange : Set.range c ⊆ Set.range a := by
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint E := Subsingleton.elim _ _
    subst z
    exact hc
  let cA : Spec (.of E) ⟶ A := IsOpenImmersion.lift a c hrange
  have hcA : cA ≫ a = c := IsOpenImmersion.lift_fac a c hrange
  letI : Nonempty A := ⟨cA (IsLocalRing.closedPoint E)⟩
  letI : IsIntegral A := isIntegral_of_isOpenImmersion a
  refine ⟨A, a, chart, markedA, cA, hAffine, hOpen, inferInstance, hcA, hmarkedA, ?_⟩
  apply serreIncidenceNativeAffineEvaluationMatrix_surjective_of_actual_tensor_evaluation
    base e C h9 chart markedA cA r _ hr honto
  intro i
  calc
    (cA ≫ markedA i) ≫ (C.U (chart i)).ι =
        cA ≫ (markedA i ≫ (C.U (chart i)).ι) := Category.assoc _ _ _
    _ = cA ≫ (a ≫ marked i) := congrArg (fun f => cA ≫ f) (hmarkedA i)
    _ = (cA ≫ a) ≫ marked i := (Category.assoc _ _ _).symm
    _ = c ≫ marked i := congrArg (fun f => f ≫ marked i) hcA
    _ = r i := hpoint i

end PfaffianDescent
