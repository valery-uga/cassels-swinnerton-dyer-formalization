import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationFiber
import PfaffianDescent.AffineFreeModuleBaseChange
import PfaffianDescent.SchemeModuleGlobalSectionsTop

/-! # Dimension of the actual restriction target at a degree-three point -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual rank-two cover constructs a ground-field linear coordinate
for the actual pullback global sections at a field-valued point. -/
theorem cubicClosedPointSerreDegreeThreeEvaluationDimension_exists_linearEquiv
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {M : X.Modules} (base : X ⟶ Spec (.of K))
    (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (j : Spec (.of L) ⟶ X)
    (hj : j ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    Nonempty (SchemeModuleGlobalSectionsOver (j ≫ base)
      ((Scheme.Modules.pullback j).obj (show X.Modules from e.E)) ≃ₗ[K]
        (ULift.{u} (Fin 2) → L)) := by
  obtain ⟨t⟩ := cubicClosedPointSerreDegreeThreeEvaluationFiber_exists_freeIso e C j
  rw [hj]
  let pL : Spec (.of L) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  let E : (Spec (.of L)).Modules :=
    (Scheme.Modules.pullback j).obj (show X.Modules from e.E)
  letI := Module.compHom Γ(Spec (.of L), ⊤) (schemeOpenBaseRingHom pL ⊤)
  exact ⟨schemeModuleGlobalSectionsLinearEquivOpenTop pL E ≪≫ₗ
    moduleOpenTopLinearEquivOfFreeIsoOver pL (ULift.{u} (Fin 2)) E t ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ => specGlobalFunctionsLinearEquiv K L)⟩

/-- The actual target at a field-valued point has twice its residue-field
degree. The rank-two coordinate is constructed from the actual cover. -/
theorem cubicClosedPointSerreDegreeThreeEvaluationDimension_finrank
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    {X : Scheme.{u}} {M : X.Modules} (base : X ⟶ Spec (.of K))
    (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (j : Spec (.of L) ⟶ X)
    (hj : j ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    Module.finrank K (SchemeModuleGlobalSectionsOver (j ≫ base)
      ((Scheme.Modules.pullback j).obj (show X.Modules from e.E))) =
        2 * Module.finrank K L := by
  obtain ⟨q⟩ := cubicClosedPointSerreDegreeThreeEvaluationDimension_exists_linearEquiv
    base e C j hj
  rw [q.finrank_eq, Module.finrank_pi_fintype]
  simp

/-- A degree-three field point imposes exactly six ambient scalar values
on the actual rank-two bundle. -/
theorem cubicClosedPointSerreDegreeThreeEvaluationDimension_finrank_eq_six
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {M : X.Modules} (base : X ⟶ Spec (.of K))
    (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (j : Spec (.of L) ⟶ X)
    (hj : j ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hL : Module.finrank K L = 3) :
    Module.finrank K (SchemeModuleGlobalSectionsOver (j ≫ base)
      ((Scheme.Modules.pullback j).obj (show X.Modules from e.E))) = 6 := by
  letI : FiniteDimensional K L := Module.finite_of_finrank_pos (by rw [hL]; omega)
  rw [cubicClosedPointSerreDegreeThreeEvaluationDimension_finrank base e C j hj, hL]

end PfaffianDescent
