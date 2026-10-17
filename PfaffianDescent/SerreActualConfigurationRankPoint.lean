import PfaffianDescent.SerreActualConfigurationRankFactory

/-! The native principal rank chart retains the SAME original evaluation
point. This identity is needed to seed the good finite-zero open with the
canonical Serre section. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def SerreActualConfigurationRankChartAtPoint
    {F E : Type u} [Field F] [Field E] {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of F)) [IsSeparated base]
    (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : finrank F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (r : Fin 3 → (Spec (.of E) ⟶ X)) : Prop :=
    ∃ (A : Scheme.{u}) (a : A ⟶ (orderedFamilyConfigurationOver base 3).left)
      (chart : Fin 3 → C.ι) (markedA : ∀ i, A ⟶ (C.U (chart i)).toScheme)
      (cA : Spec (.of E) ⟶ A),
      IsAffine A ∧ IsOpenImmersion a ∧ IsIntegral A ∧
      (∀ i, markedA i ≫ (C.U (chart i)).ι =
        (a ≫ Over.Hom.left (orderedFamilyConfigurationι base 3)) ≫
          (orderedFamilyCoordinate base 3 i).left) ∧
      (∀ i, (cA ≫ markedA i) ≫ (C.U (chart i)).ι = r i) ∧
      ∃ m : (Fin 3 × ULift.{u} (Fin 2)) ↪ Fin 9,
        IsUnit (Matrix.det (Matrix.submatrix
          (serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart markedA) id m))

theorem serreActualConfigurationRankChartAtPoint_of_actual_evaluation
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of F)) [IsSeparated base]
    [GeometricallyIntegral base] [Flat base] [UniversallyOpen base] [LocallyOfFiniteType base]
    (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : finrank F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (r : Fin 3 → (Spec (.of E) ⟶ X))
    (hr : ∀ i, r i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F E)))
    (honto : Function.Surjective
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        base r hr (show X.Modules from e.E))) :
    SerreActualConfigurationRankChartAtPoint base e C h9 r := by
  obtain ⟨c, hc, hcmarked⟩ := serreActualEvaluation_exists_orderedConfiguration base e C r hr honto
  let B := (orderedFamilyConfigurationOver base 3).left
  letI : Nonempty B := ⟨c (IsLocalRing.closedPoint E)⟩
  letI : IsIntegral B :=
    isIntegral_orderedFamilyConfigurationOver_of_geometricallyIntegral base 3
  let marked : Fin 3 → (B ⟶ X) := fun i =>
    Over.Hom.left (orderedFamilyConfigurationι base 3) ≫ (orderedFamilyCoordinate base 3 i).left
  have hcmarked' : ∀ i, c ≫ marked i = r i := by
    intro i
    exact (Category.assoc _ _ _).symm.trans (hcmarked i)
  obtain ⟨A, a, chart, markedA, cA, hAffine, hOpen, hInt, hcA, hmarkedA, h6⟩ :=
    serreActualEvaluation_exists_integral_affine_rank_chart
      base e C h9 marked c r hcmarked' hr honto
  letI : IsAffine A := hAffine
  letI : IsOpenImmersion a := hOpen
  letI : IsIntegral A := hInt
  have hpoints : ∀ i, (cA ≫ markedA i) ≫ (C.U (chart i)).ι = r i := by
    intro i
    rw [Category.assoc, hmarkedA i, ← Category.assoc, hcA]
    exact hcmarked' i
  obtain ⟨m, hd, hdc⟩ := serreIncidenceNativeAffineEvaluationMatrix_exists_nonzero_minor
    base e C h9 chart markedA cA h6
  let d := Matrix.det (Matrix.submatrix
    (serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart markedA) id m)
  let U := A.basicOpen d
  obtain ⟨v, hv⟩ := serreIncidenceFieldPoint_lift_basicOpen cA d hdc.ne_zero
  letI : IsAffine (U : Scheme.{u}) := inferInstance
  letI : Nonempty (U : Scheme.{u}) := ⟨v (IsLocalRing.closedPoint E)⟩
  letI : IsIntegral (U : Scheme.{u}) := inferInstance
  have hm := serreIncidenceNativeAffineEvaluationMatrix_minor_unit_on_basicOpen
    base e C h9 chart markedA m
  refine ⟨(U : Scheme.{u}), U.ι ≫ a, chart, (fun i => U.ι ≫ markedA i), v,
    inferInstance, inferInstance, inferInstance, ?_, ?_, m, hm⟩
  · intro i
    calc
      (U.ι ≫ markedA i) ≫ (C.U (chart i)).ι =
          U.ι ≫ (markedA i ≫ (C.U (chart i)).ι) := Category.assoc _ _ _
      _ = U.ι ≫ (a ≫ marked i) := congrArg (fun f => U.ι ≫ f) (hmarkedA i)
      _ = ((U.ι ≫ a) ≫ Over.Hom.left (orderedFamilyConfigurationι base 3)) ≫
          (orderedFamilyCoordinate base 3 i).left := by simp only [marked, Category.assoc]
  · intro i
    calc
      (v ≫ (U.ι ≫ markedA i)) ≫ (C.U (chart i)).ι =
          ((v ≫ U.ι) ≫ markedA i) ≫ (C.U (chart i)).ι := by simp only [Category.assoc]
      _ = (cA ≫ markedA i) ≫ (C.U (chart i)).ι :=
        congrArg (fun f => (f ≫ markedA i) ≫ (C.U (chart i)).ι) hv
      _ = r i := hpoints i

end PfaffianDescent
