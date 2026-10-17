import PfaffianDescent.VoisinDegreeElevenSerreIncidenceMinorOpen

/-! # The actual principal configuration chart carries the invertible native minor -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceBasicOpen_function_isUnit
    (B : Scheme.{u}) [IsAffine B] (d : Γ(B, ⊤)) :
    IsUnit ((B.basicOpen d).ι.appTop d) := by
  change IsUnit (algebraMap Γ(B, ⊤) Γ(B.basicOpen d, ⊤) d)
  exact IsLocalization.Away.algebraMap_isUnit d

theorem serreIncidenceFieldPoint_lift_basicOpen
    {F : Type u} [Field F] {B : Scheme.{u}}
    (c : Spec (.of F) ⟶ B) (d : Γ(B, ⊤)) (hd : fieldPointΓevaluation c d ≠ 0) :
    ∃ v : Spec (.of F) ⟶ (B.basicOpen d : Scheme.{u}), v ≫ (B.basicOpen d).ι = c := by
  have hx : c (IsLocalRing.closedPoint F) ∈ B.basicOpen d := by
    apply (B.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤)
      (c (IsLocalRing.closedPoint F)) trivial d).mp
    intro hz
    exact hd (fieldPointΓevaluation_eq_zero_of_Γevaluation_eq_zero c d hz)
  have hr : Set.range c ⊆ Set.range (B.basicOpen d).ι := by
    rintro y ⟨x, rfl⟩
    rw [(B.basicOpen d).range_ι]
    have he : x = IsLocalRing.closedPoint F := Subsingleton.elim _ _
    rwa [he]
  exact ⟨IsOpenImmersion.lift (B.basicOpen d).ι c hr,
    IsOpenImmersion.lift_fac _ _ _⟩

theorem serreIncidenceNativeAffineEvaluationMatrix_comp
    {F : Type u} [Field F] {X A B : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of F)) (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : Module.finrank F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (chart : Fin 3 → C.ι) (marked : ∀ i, B ⟶ (C.U (chart i)).toScheme) (a : A ⟶ B) :
    serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart (fun i => a ≫ marked i) =
      (serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart marked).map a.appTop.hom := by
  funext r k
  unfold serreIncidenceNativeAffineEvaluationMatrix serreThreePointRelativeEvaluationMatrix
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem serreIncidenceNativeAffineEvaluationMatrix_minor_unit_on_basicOpen
    {F : Type u} [Field F] {X B : Scheme.{u}} [IsAffine B] {N : X.Modules}
    (base : X ⟶ Spec (.of F)) (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : Module.finrank F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (chart : Fin 3 → C.ι) (marked : ∀ i, B ⟶ (C.U (chart i)).toScheme)
    (m : (Fin 3 × ULift.{u} (Fin 2)) ↪ Fin 9) :
    let d := ((serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart marked).submatrix id m).det
    IsUnit ((serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart
      (fun i => (B.basicOpen d).ι ≫ marked i)).submatrix id m).det := by
  let A := serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart marked
  let d := (A.submatrix id m).det
  change IsUnit ((serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart
    (fun i => (B.basicOpen d).ι ≫ marked i)).submatrix id m).det
  rw [serreIncidenceNativeAffineEvaluationMatrix_comp]
  change IsUnit (((B.basicOpen d).ι.appTop.hom.mapMatrix (A.submatrix id m)).det)
  rw [← RingHom.map_det]
  exact serreIncidenceBasicOpen_function_isUnit B d

end PfaffianDescent
