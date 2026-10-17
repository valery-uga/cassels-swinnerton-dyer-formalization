import PfaffianDescent.DependentPointEvaluationDistinct
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointSectionEvaluationThree
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentSerreFiberDimension

/-! The actual rank-six section evaluator internally proves that its
three actual extension-field point morphisms are distinct. -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreSurfaceJetCotangent_actualEvaluation_points_injective
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of F)) (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (r : Fin 3 → (Spec (.of E) ⟶ X))
    (hr : ∀ i, r i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F E)))
    (honto : Function.Surjective
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        base r hr (show X.Modules from e.E))) : Function.Injective r := by
  let A := { q : Spec (.of E) ⟶ X //
    q ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F E)) }
  let V : A → Type u := fun q =>
    (moduleSpecΓFunctor (R := CommRingCat.of E)).obj
      ((Scheme.Modules.pullback q.val).obj (show X.Modules from e.E))
  let r' : Fin 3 → A := fun i => ⟨r i, hr i⟩
  let ev : ∀ q : A,
      E ⊗[F] SchemeModuleGlobalSectionsOver base (show X.Modules from e.E) → V q :=
    fun q => cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluationTensor
      base q.val q.property (show X.Modules from e.E)
  have hne : ∀ i, ∃ v : V (r' i), v ≠ 0 := by
    intro i
    obtain ⟨q⟩ := cubicClosedPointSerreSurfaceJetCotangent_serreFiber_exists_nativeLinearEquiv
      e C (r i)
    let v : ULift.{u} (Fin 2) →₀ E := Finsupp.single (ULift.up 0) 1
    have hv : v ≠ 0 := by
      intro hz
      have := congrArg (fun w : ULift.{u} (Fin 2) →₀ E => w (ULift.up 0)) hz
      simpa [v] using this
    refine ⟨q.symm v, ?_⟩
    intro hz
    apply hv
    simpa using congrArg q hz
  have hinj : Function.Injective r' :=
    dependentPointEvaluation_points_injective V r' ev honto hne
  intro i j hij
  exact hinj (Subtype.ext hij)

end PfaffianDescent
