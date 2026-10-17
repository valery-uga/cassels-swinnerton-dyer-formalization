import PfaffianDescent.ExtSourceIsoCoefficientNaturality

/-! # Writing an actual Ext pullback trace in an additive source coordinate -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace PfaffianDescent
universe u v w l k
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {L : Type l} [AddCommGroup L] {K : Type k} [AddCommGroup K]

/-- Write an additive trace in an additive coordinate without reducing either
constructed geometric map during elaboration. -/
def additiveTraceCoordinateAddHom {A : Type u} [AddCommGroup A]
    (e : A ≃+ L) (tr : A →+ K) : L →+ K :=
  tr.comp e.symm.toAddMonoidHom

theorem additiveTraceCoordinateAddHom_evaluate_class
    {A : Type u} [AddCommGroup A] (e : A ≃+ L) (tr : A →+ K) (z : A) :
    additiveTraceCoordinateAddHom e tr (e z) = tr z := by
  change tr (e.symm (e z)) = tr z
  exact congrArg tr (e.symm_apply_apply z)

/-- Composition of an actual source coordinate, Ext pullback and additive trace. -/
def extPullbackTraceCoordinateAddHom {P Q Y : C} {n : ℕ}
    (e : Ext.{w} Q Y n ≃+ L) (g : P ⟶ Q) (tr : Ext.{w} P Y n →+ K) :
    L →+ K :=
  tr.comp (((Ext.mk₀ g).precomp Y (zero_add n)).comp e.symm.toAddMonoidHom)

/-- Evaluating in the coordinate gives precisely the actual geometric pullback trace. -/
theorem extPullbackTraceCoordinateAddHom_evaluate_class {P Q Y : C} {n : ℕ}
    (e : Ext.{w} Q Y n ≃+ L) (g : P ⟶ Q) (tr : Ext.{w} P Y n →+ K)
    (z : Ext.{w} Q Y n) :
    extPullbackTraceCoordinateAddHom e g tr (e z) =
      tr ((Ext.mk₀ g).comp z (zero_add n)) := by
  change tr ((Ext.mk₀ g).comp (e.symm (e z)) (zero_add n)) = _
  rw [AddEquiv.symm_apply_apply]

/-- The same construction when the actual trace is supplied as an additive
equivalence; converting that equivalence to a hom happens in this small context. -/
def extPullbackTraceCoordinateAddHomOfTraceEquiv {P Q Y : C} {n : ℕ}
    (e : Ext.{w} Q Y n ≃+ L) (g : P ⟶ Q) (tr : Ext.{w} P Y n ≃+ K) :
    L →+ K :=
  extPullbackTraceCoordinateAddHom e g tr.toAddMonoidHom

theorem extPullbackTraceCoordinateAddHomOfTraceEquiv_evaluate_class
    {P Q Y : C} {n : ℕ}
    (e : Ext.{w} Q Y n ≃+ L) (g : P ⟶ Q) (tr : Ext.{w} P Y n ≃+ K)
    (z : Ext.{w} Q Y n) :
    extPullbackTraceCoordinateAddHomOfTraceEquiv e g tr (e z) =
      tr ((Ext.mk₀ g).comp z (zero_add n)) :=
  extPullbackTraceCoordinateAddHom_evaluate_class e g tr.toAddMonoidHom z

end PfaffianDescent
