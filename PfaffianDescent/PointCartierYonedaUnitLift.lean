import PfaffianDescent.PointGlobalTraceKoszulCartierHomotopy
import PfaffianDescent.PointCartierYonedaRegularKoszul
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The unit-normalized Cartier lift

For `p = f*u + g*b + h*c` with `u` a unit, the surface two-parameter
Koszul cocycle pulls back to the ambient degree-two cocycle given here.
Its chosen lift has degree-three differential `p*u⁻¹`. All identities
refer to the existing orientations of the actual Koszul differentials.
-/

noncomputable section

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Abelian
open scoped nonZeroDivisors

universe u

variable {R : Type u} [CommRing R]

/-- The principal Cartier coefficient extension. -/
def pointCartierYonedaCoefficientComplex (p : R) : ShortComplex (ModuleCat R) :=
  ModuleCat.shortComplexOfCompEqZero (LinearMap.lsmul R R p)
    (Ideal.Quotient.mkₐ R (Ideal.span {p})).toLinearMap (by
      apply LinearMap.ext
      intro x
      change Ideal.Quotient.mk (Ideal.span {p}) (p * x) = 0
      rw [map_mul, Ideal.Quotient.mk_singleton_self, zero_mul])

theorem pointCartierYonedaCoefficientComplex_shortExact (p : R) (hp : p ∈ R⁰) :
    (pointCartierYonedaCoefficientComplex p).ShortExact := by
  dsimp [pointCartierYonedaCoefficientComplex]
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact (LinearMap.lsmul R R p)
      (Ideal.Quotient.mkₐ R (Ideal.span {p})).toLinearMap
    rw [LinearMap.exact_iff]
    ext x
    change Ideal.Quotient.mk (Ideal.span {p}) x = 0 ↔ (∃ y, p * y = x)
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩, fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩⟩
  · intro x y hxy
    apply sub_eq_zero.mp
    apply mem_nonZeroDivisors_iff_left.mp hp
    change p * x = p * y at hxy
    rw [mul_sub, hxy, sub_self]
  · exact Ideal.Quotient.mkₐ_surjective R _

/-- The degree-two lift with unit-normalized orientation. -/
def pointCartierYonedaUnitLift (v : Rˣ) (b c : R) : R × R × R →ₗ[R] R :=
  (LinearMap.lsmul R R (v⁻¹ : Rˣ)).comp
    (pointGlobalTraceCartierHomotopyTwo (v : R) b c)

@[simp]
theorem pointCartierYonedaUnitLift_apply (v : Rˣ) (b c : R) (x : R × R × R) :
    pointCartierYonedaUnitLift v b c x =
      (v⁻¹ : Rˣ) * (c * x.1 - b * x.2.1 + (v : R) * x.2.2) := rfl

/-- The top differential of the lifted surface cocycle is multiplication
by the Cartier equation, with the explicit invertible factor `v⁻¹`. -/
theorem pointCartierYonedaUnitLift_comp_first
    (f g h : R) (v : Rˣ) (b c : R) :
    (pointCartierYonedaUnitLift v b c).comp (threeGeneratorFirst f g h) =
      LinearMap.lsmul R R ((f * (v : R) + g * b + h * c) * (v⁻¹ : Rˣ)) := by
  apply LinearMap.ext
  intro x
  change (v⁻¹ : Rˣ) *
    pointGlobalTraceCartierHomotopyTwo (v : R) b c (threeGeneratorFirst f g h x) = _
  rw [pointGlobalTraceCartierHomotopy_degreeThree]
  change (v⁻¹ : Rˣ) * ((f * (v : R) + g * b + h * c) * x) =
    ((f * (v : R) + g * b + h * c) * (v⁻¹ : Rˣ)) * x
  ring

/-- The ambient degree-one chain comparison with the two parameters `g,h`
on the Cartier quotient. -/
def pointCartierYonedaUnitRetractionOneLift (v : Rˣ) (b c : R) :
    R × R × R →ₗ[R] R × R where
  toFun x :=
    (x.2.1 - b * (v⁻¹ : Rˣ) * x.1,
      x.2.2 - c * (v⁻¹ : Rˣ) * x.1)
  map_add' x y := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' a x := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply] <;> ring

def pointCartierYonedaUnitRetractionOne (p : R) (v : Rˣ) (b c : R) :
    R × R × R →ₗ[R] (R ⧸ Ideal.span {p}) × (R ⧸ Ideal.span {p}) :=
  (LinearMap.prodMap (Ideal.Quotient.mkₐ R (Ideal.span {p})).toLinearMap
    (Ideal.Quotient.mkₐ R (Ideal.span {p})).toLinearMap).comp
      (pointCartierYonedaUnitRetractionOneLift v b c)

/-- The degree-two surface cocycle on the ambient free resolution. -/
def pointCartierYonedaUnitCocycleMap (p : R) (v : Rˣ) (b c : R) :
    R × R × R →ₗ[R] R ⧸ Ideal.span {p} :=
  (Ideal.Quotient.mkₐ R (Ideal.span {p})).toLinearMap.comp
    (pointCartierYonedaUnitLift v b c)

theorem pointCartierYonedaUnitCocycleMap_comp_first
    (f g h p : R) (v : Rˣ) (b c : R)
    (heq : p = f * (v : R) + g * b + h * c) :
    (pointCartierYonedaUnitCocycleMap p v b c).comp (threeGeneratorFirst f g h) = 0 := by
  rw [pointCartierYonedaUnitCocycleMap, LinearMap.comp_assoc,
    pointCartierYonedaUnitLift_comp_first, ← heq]
  apply LinearMap.ext
  intro x
  change Ideal.Quotient.mk (Ideal.span {p}) ((p * (v⁻¹ : Rˣ)) * x) = 0
  simp only [map_mul, Ideal.Quotient.mk_singleton_self, zero_mul]

end PfaffianDescent
