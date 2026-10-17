import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeMinorChart
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeSerrePlane

/-! # Actual field rank six internally selects the native open plane incidence -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceNative_exists_rank_open_plane
    {K L : Type u} [Field K] [Field L]
    {X B : Scheme.{u}} [IsAffine B] [IsIntegral B] {N : X.Modules}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (b : B ⟶ Spec (.of K)) (chart : Fin 3 → C.ι)
    (marked : ∀ i, B ⟶ (C.U (chart i) : Scheme.{u}))
    (hmarked : ∀ i, (marked i ≫ (C.U (chart i)).ι) ≫ base = b)
    (c : Spec (.of L) ⟶ B)
    (h6 : Function.Surjective (Matrix.toLin'
      ((serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart marked).map
        (fieldPointΓevaluation c)))) :
    let D := serreIncidenceRankTwoAffineCover e C
    letI := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base
      (show X.Modules from e.E)
    ∃ (m : (Fin 3 × ULift.{u} (Fin 2)) ↪ Fin 9) (U : B.Opens)
      (v : Spec (.of L) ⟶ (U : Scheme.{u}))
      (hU : ∀ i, (((U.ι ≫ marked i) ≫ (C.U (chart i)).ι) ≫ base) = U.ι ≫ b)
      (hAffine : IsAffine (U : Scheme.{u})),
      letI := hAffine
      IsIntegral (U : Scheme.{u}) ∧ v ≫ U.ι = c ∧
      IsUnit ((serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart
        (fun i => U.ι ≫ marked i)).submatrix id m).det ∧
      let I := serreThreePointSectionIncidenceIdeal (U.ι ≫ b) base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base (show X.Modules from e.E))
        (fun i => (U.ι ≫ marked i) ≫ (C.U (chart i)).ι) hU
        (D.projectiveSectionLocalZeroGluedToAmbient base (show X.Modules from e.E))
      ∃ q : scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) Γ(U, ⊤))) ≅
          I.subscheme,
        q.hom ≫ I.subschemeι ≫ pullback.fst (U.ι ≫ b)
          (schemeModuleGlobalSectionsProjectiveParametersToBase base (show X.Modules from e.E)) =
          toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) Γ(U, ⊤))) ≫
            (U : Scheme.{u}).isoSpec.inv ∧
        IsOpenMap (I.subschemeι ≫ pullback.fst (U.ι ≫ b)
          (schemeModuleGlobalSectionsProjectiveParametersToBase base (show X.Modules from e.E))) := by
  let D := serreIncidenceRankTwoAffineCover e C
  letI := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base
    (show X.Modules from e.E)
  obtain ⟨m, hd, hdc⟩ := serreIncidenceNativeAffineEvaluationMatrix_exists_nonzero_minor
    base e C h9 chart marked c h6
  let d := ((serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart marked).submatrix id m).det
  let U := B.basicOpen d
  obtain ⟨v, hv⟩ := serreIncidenceFieldPoint_lift_basicOpen c d hdc.ne_zero
  letI : IsAffine (U : Scheme.{u}) := inferInstanceAs (IsAffine (B.basicOpen d))
  letI : Nonempty (U : Scheme.{u}) := ⟨v (IsLocalRing.closedPoint L)⟩
  letI : IsIntegral (U : Scheme.{u}) := inferInstance
  have hU : ∀ i, (((U.ι ≫ marked i) ≫ (C.U (chart i)).ι) ≫ base) = U.ι ≫ b := by
    intro i
    simpa only [Category.assoc] using congrArg (fun f => U.ι ≫ f) (hmarked i)
  have hm := serreIncidenceNativeAffineEvaluationMatrix_minor_unit_on_basicOpen base e C h9 chart marked m
  refine ⟨m, U, v, hU, inferInstance, inferInstance, hv, hm, ?_⟩
  exact serreIncidenceNativeSerre_exists_plane base e C h9 (U.ι ≫ b) chart
    (fun i => U.ι ≫ marked i) hU m hm

end PfaffianDescent
