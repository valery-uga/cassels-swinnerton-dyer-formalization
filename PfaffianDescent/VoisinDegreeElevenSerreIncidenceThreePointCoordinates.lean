import PfaffianDescent.VoisinDegreeElevenSerreIncidencePointChartCoordinates
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointSectionEvaluationThree

/-! # Native coordinates of the actual three-point tensor evaluator -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

def serreIncidenceThreePointCoordinateEquiv
    {E : Type u} [Field E] {X : Scheme.{u}} (M : X.Modules)
    (I : Type u) [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I) (chart : Fin 3 → C.ι)
    (q : ∀ i, Spec (.of E) ⟶ (C.U (chart i) : Scheme.{u}))
    (r : Fin 3 → (Spec (.of E) ⟶ X))
    (h : ∀ i, q i ≫ (C.U (chart i)).ι = r i) :
    (∀ i : Fin 3, (moduleSpecΓFunctor (R := CommRingCat.of E)).obj
      ((Scheme.Modules.pullback (r i)).obj M)) ≃ₗ[E] ((Fin 3 × I) → E) := by
  let e := fun i => serreIncidenceSpecFibreCoordinateEquiv E I
    ((Scheme.Modules.pullback (r i)).obj M)
    (serreIncidencePointChartFreeIso (C.U (chart i)) M I (C.trivialization (chart i))
      (q i) (r i) (h i))
  exact {
    toFun := fun v a => e a.1 (v a.1) a.2
    invFun := fun v i => (e i).symm (fun a => v (i,a))
    left_inv := by
      intro v
      funext i
      exact (e i).symm_apply_apply (v i)
    right_inv := by
      intro v
      funext a
      exact congrFun ((e a.1).apply_symm_apply (fun b => v (a.1,b))) a.2
    map_add' := by
      intro v w
      funext a
      exact congrFun ((e a.1).map_add (v a.1) (w a.1)) a.2
    map_smul' := by
      intro a v
      funext b
      exact congrFun ((e b.1).map_smul a (v b.1)) b.2 }

theorem serreIncidenceThreePointCoordinateEquiv_tensor_section
    {K E : Type u} [Field K] [Field E] [Algebra K E] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    (I : Type u) [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I) (chart : Fin 3 → C.ι)
    (q : ∀ i, Spec (.of E) ⟶ (C.U (chart i) : Scheme.{u}))
    (r : Fin 3 → (Spec (.of E) ⟶ X))
    (h : ∀ i, q i ≫ (C.U (chart i)).ι = r i)
    (hr : ∀ i, r i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (s : SchemeModuleGlobalSectionsOver base M) (a : Fin 3 × I) :
    serreIncidenceThreePointCoordinateEquiv M I C chart q r h
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        base r hr M (1 ⊗ₜ[K] s)) a =
    fieldPointΓevaluation (q a.1)
      (sectionCoordinateOfFreeIso I
        (localFreeIsoOfOver (C.U (chart a.1)) I (C.trivialization (chart a.1)))
        (restrictSectionToOpen (C.U (chart a.1)) (M.unitHomEquiv s)) a.2) := by
  rw [cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor_one_tmul]
  exact serreIncidencePointChartFreeIso_field_coordinate (C.U (chart a.1)) M I
    (C.trivialization (chart a.1)) (q a.1) (r a.1) (h a.1) (M.unitHomEquiv s) a.2

end PfaffianDescent
