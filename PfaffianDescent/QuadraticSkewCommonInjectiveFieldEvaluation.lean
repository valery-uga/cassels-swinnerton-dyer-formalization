import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Localization.FractionRing

/-! SOURCE ONLY / UNVERIFIED. Construct a common coefficient field for
the ORIGINAL coordinate domain and its finite quadratic coefficient field.
This is an actual fraction-field/algebraic-closure construction, not a
rationality or coordinate-reconstruction certificate. -/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.SecondComposite005
universe u
variable (k A E : Type u) [Field k] [CommRing A] [Algebra k A]
variable [Field E] [Algebra k E]

structure CommonFieldEvaluation where
  Target : Type u
  [field : Field Target]
  [algebra : Algebra k Target]
  coordinate : A →ₐ[k] Target
  coefficient : E →ₐ[k] Target
  coordinate_injective : Function.Injective coordinate

attribute [instance] CommonFieldEvaluation.field CommonFieldEvaluation.algebra

/-- Over an actual coordinate domain the common field evaluation is
constructed internally, including injectivity of its original coordinate
map and its finite coefficient-extension embedding. -/
def commonFieldEvaluation [IsDomain A] [FiniteDimensional k E] :
    CommonFieldEvaluation k A E := by
  let K := FractionRing A
  let L := AlgebraicClosure K
  let e : A →+* L := (algebraMap K L).comp (algebraMap A K)
  letI : Algebra A L := e.toAlgebra
  letI : Algebra k L := (e.comp (algebraMap k A)).toAlgebra
  let eₐ : A →ₐ[k] L :=
    { __ := e
      commutes' := fun _ => rfl }
  let f : E →ₐ[k] L := IsAlgClosed.lift
  exact
    { Target := L
      coordinate := eₐ
      coefficient := f
      coordinate_injective :=
        (RingHom.injective (algebraMap K L)).comp (IsFractionRing.injective A K) }

end PfaffianDescent.QuadraticSkewRationality.SecondComposite005
