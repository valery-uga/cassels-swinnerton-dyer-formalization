import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationPullbackFiniteDimension
import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationFiniteKernel

/-! # Actual vanishing sections of the pulled-back original extension -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- A rank-three actual finite field datum imposes six conditions on the
actual pullback of the original rank-two bundle. -/
theorem cubicClosedPointSerreDegreeThreeEvaluationPullbackFiniteKernel_exists_nonzero
    {F : Type u} [Field F] {X Y : Scheme.{u}} {M : X.Modules}
    (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (f : Y ⟶ X) (base : Y ⟶ Spec (.of F))
    (D : FiniteSubschemeDatum base 3) (hField : IsField Γ(D.val.subscheme, ⊤))
    (hsections : 9 ≤ Module.finrank F (SchemeModuleGlobalSectionsOver base
      ((Scheme.Modules.pullback f).obj (show X.Modules from e.E)))) :
    ∃ s : SchemeModuleGlobalSectionsOver base
        ((Scheme.Modules.pullback f).obj (show X.Modules from e.E)),
      s ≠ 0 ∧ cubicClosedPointSerreDegreeThreeEvaluationMap base D.val.subschemeι
        ((Scheme.Modules.pullback f).obj (show X.Modules from e.E)) s = 0 := by
  let N := (Scheme.Modules.pullback f).obj (show X.Modules from e.E)
  let V := SchemeModuleGlobalSectionsOver base N
  let W := SchemeModuleGlobalSectionsOver (D.val.subschemeι ≫ base)
    ((Scheme.Modules.pullback D.val.subschemeι).obj N)
  change 9 ≤ Module.finrank F V at hsections
  letI : FiniteDimensional F V := Module.finite_of_finrank_pos (by
    change 0 < Module.finrank F V
    omega)
  have htarget : Module.finrank F W = 6 :=
    cubicClosedPointSerreDegreeThreeEvaluationPullbackFiniteDimension_finrank_eq_six
      e C f base D hField
  letI : FiniteDimensional F W := Module.finite_of_finrank_pos (by rw [htarget]; omega)
  exact exists_ne_zero_mem_ker_of_finrank_lt
    (cubicClosedPointSerreDegreeThreeEvaluationMap base D.val.subschemeι N) (by
      change Module.finrank F W < Module.finrank F V
      change 9 ≤ Module.finrank F V at hsections
      omega)

end PfaffianDescent
