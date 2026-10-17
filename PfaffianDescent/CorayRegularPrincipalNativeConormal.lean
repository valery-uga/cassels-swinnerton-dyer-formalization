import PfaffianDescent.RegularPrincipalIdealFree
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Isomorphisms

/-! Native conormal of an actual regular principal equation.
SOURCE ONLY / UNVERIFIED. No numerical adjunction, RR or Hodge claim. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u v

/-- The genuine class of a times x in (x)/(x)^2. -/
def regularPrincipalConormalMap {A : Type u} [CommRing A]
    (x : A) (hx : IsRegular x) :
    A →ₗ[A] (Ideal.span ({x} : Set A)).Cotangent :=
  (Ideal.span ({x} : Set A)).toCotangent.comp
    (regularPrincipalIdealLinearEquiv x hx).toLinearMap

/-- Regularity derives the exact kernel, rather than assuming conormal
rank or a quotient identification. -/
theorem regularPrincipalConormalMap_ker {A : Type u} [CommRing A]
    (x : A) (hx : IsRegular x) :
    LinearMap.ker (regularPrincipalConormalMap x hx) =
      Ideal.span ({x} : Set A) := by
  let I := Ideal.span ({x} : Set A)
  ext a
  change I.toCotangent
    ⟨a * x, Ideal.mul_mem_left I a (Ideal.subset_span (Set.mem_singleton x))⟩ = 0 ↔ a ∈ I
  rw [I.toCotangent_eq_zero]
  have hpow : I ^ 2 = Ideal.span ({x ^ 2} : Set A) :=
    Ideal.span_singleton_pow x 2
  rw [hpow]
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
    have heq : a * x = (x * b) * x := hb.trans (by ring)
    have hcancel : a = x * b := hx.right heq
    rw [hcancel]
    exact Ideal.mul_mem_right b I (Ideal.subset_span (Set.mem_singleton x))
  · intro ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
    apply Ideal.mem_span_singleton.mpr
    exact ⟨b, by rw [hb]; ring⟩

/-- SAME quotient and SAME actual Ideal.Cotangent, with canonical forward
map induced by multiplication by x and the native cotangent projection. -/
def regularPrincipalConormalLinearEquiv {A : Type u} [CommRing A]
    (x : A) (hx : IsRegular x) :
    (A ⧸ Ideal.span ({x} : Set A)) ≃ₗ[A]
      (Ideal.span ({x} : Set A)).Cotangent := by
  let I := Ideal.span ({x} : Set A)
  let f := regularPrincipalConormalMap x hx
  have hf : Function.Surjective f :=
    I.toCotangent_surjective.comp (regularPrincipalIdealLinearEquiv x hx).surjective
  exact (Submodule.quotEquivOfEq I (LinearMap.ker f)
    (regularPrincipalConormalMap_ker x hx).symm).trans
      (f.quotKerEquivOfSurjective hf)

/-- Restriction keeps the independently canonical original ground action
through A; no action is transported using the resulting equivalence. -/
def regularPrincipalConormalGroundLinearEquiv
    {K : Type v} [Field K] {A : Type u} [CommRing A] [Algebra K A]
    (x : A) (hx : IsRegular x) :
    (A ⧸ Ideal.span ({x} : Set A)) ≃ₗ[K]
      (Ideal.span ({x} : Set A)).Cotangent :=
  (regularPrincipalConormalLinearEquiv x hx).restrictScalars K

/-- Actual immersion chart conormal, with OWN kernel and native quotient.
The actual chart generator and its regularity are derived from H. -/
theorem RegularPrincipalImmersion.chart_conormal_linearEquiv
    {X Z : Scheme.{u}} {i : Z ⟶ X}
    (H : RegularPrincipalImmersion i) (j : H.Index) :
    Nonempty ((H.A j ⧸ RingHom.ker (H.ringMap j).hom) ≃ₗ[H.A j]
      (RingHom.ker (H.ringMap j).hom).Cotangent) := by
  obtain ⟨x, hx, hkernel⟩ := H.principal j
  rw [hkernel]
  exact ⟨regularPrincipalConormalLinearEquiv x hx⟩

end PfaffianDescent
