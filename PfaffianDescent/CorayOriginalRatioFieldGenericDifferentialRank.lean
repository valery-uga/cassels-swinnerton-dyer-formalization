import PfaffianDescent.CorayOriginalGenericDifferentialDimensionAndSmoothImage
import PfaffianDescent.CorayOriginalBasisRatioFieldFiniteSeparable
import Mathlib.RingTheory.Etale.Field

/-! The exact original E->F field inclusion gives a genuine generic
Kähler map of rank2 in the SAMEEtrdeg2 branch. This is a field-level
producer; spreading to the native surface jet matrix remains separate.
SOURCE ONLY / HELD. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module KaehlerDifferential
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

section
variable {K L : Type u} [Field K] [CharZero K] [CommRing L] [Algebra K L]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
  [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
variable (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
  (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
variable {m : ℕ} (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy)) (a : Fin m)
local notation "F" => Scheme.functionField (hypersurface p hp)
local notation "φ" => schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)
local notation "E" => cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a

/-- Derived separability of ORIGINAL F / SAME E constructs the canonical
exact generic differential comparison. No injectivity/rank certificate. -/
def cubicThroughPointOriginalBasisRatioField_genericDifferentialEquiv :
    letI : Algebra K F := RingHom.toAlgebra φ
    Algebra.trdeg K E = 2 → (F ⊗[E] KaehlerDifferential K E) ≃ₗ[F] KaehlerDifferential K F := by
  letI : Algebra K F := RingHom.toAlgebra φ
  intro hE
  letI : Algebra.IsSeparable E F :=
    (cubicThroughPointOriginalBasisRatioField_finite_separable_of_trdeg_two
      p hp hp0 n y hpy j b a hE).2
  letI : Algebra.FormallyEtale E F := Algebra.FormallyEtale.of_isSeparable E F
  exact KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K E F

include hp0 in
/-- The actual canonical field differential map is bijective, derived
from SAME branch separability. The map is its literal mapBaseChange. -/
theorem cubicThroughPointOriginalBasisRatioField_genericDifferential_bijective :
    letI : Algebra K F := RingHom.toAlgebra φ
    Algebra.trdeg K E = 2 → Function.Bijective (KaehlerDifferential.mapBaseChange K E F) := by
  letI : Algebra K F := RingHom.toAlgebra φ
  intro hE
  letI : Algebra.IsSeparable E F :=
    (cubicThroughPointOriginalBasisRatioField_finite_separable_of_trdeg_two
      p hp hp0 n y hpy j b a hE).2
  letI : Algebra.FormallyEtale E F := Algebra.FormallyEtale.of_isSeparable E F
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K E F
  constructor
  · intro x y h
    apply e.injective
    simpa only [e, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply] using h
  · intro x
    obtain ⟨y, hy⟩ := e.surjective x
    refine ⟨y, ?_⟩
    simpa only [e, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply] using hy

include hp0 in
/-- The source and target of the genuine generic differential have
ORIGINAL-F dimension exactly2. Together with canonical-map bijectivity
this is the genuine generic rank2 field statement. -/
theorem cubicThroughPointOriginalBasisRatioField_genericDifferential_finrank_two :
    letI : Algebra K F := RingHom.toAlgebra φ
    Algebra.trdeg K E = 2 →
      Module.finrank F (F ⊗[E] KaehlerDifferential K E) = 2 ∧
      Module.finrank F (KaehlerDifferential K F) = 2 := by
  letI : Algebra K F := RingHom.toAlgebra φ
  intro hE
  have he := cubicThroughPointOriginalBasisRatioField_genericDifferentialEquiv
    p hp hp0 n y hpy j b a hE
  have hF := smoothCubic_originalFunctionFieldKaehler_finrank_two p hp hp0 j
  exact ⟨he.finrank_eq.trans hF, hF⟩

end
end PfaffianDescent.Coray
end
