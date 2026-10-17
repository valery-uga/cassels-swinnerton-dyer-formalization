import PfaffianDescent.VoisinFiniteSupportTraceDuality
import PfaffianDescent.VoisinSerreDualExtKernel

/-!
# Finite-support constructor for Voisin's Serre-duality square

This turns the quotient-side residue calculation into the exact comparison
consumed by the Serre extension.  Naturality is requested pointwise as the
standard trace-residue identity; the equality of dual vectors then follows
by extensionality.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace PfaffianDescent

universe u v w

/-- Construct the complete Ext-kernel comparison from finite-support residue
coordinates, a nondegenerate finite-algebra trace form, the already computed
middle equivalence, and the pointwise trace-residue naturality formula. -/
noncomputable def serreDualExtKernelComparisonOfFiniteSupportTrace
    {K A : Type u} {B : Type w} {V : Type u} [Field K]
    [CommRing A] [Algebra K A] [FiniteDimensional K A]
    [AddCommGroup B] [Module K B]
    [AddCommGroup V] [Module K V]
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    (M Q Y : C) (g : M ⟶ Q) (restriction : V →ₗ[K] A)
    (localResidueEquiv : Ext.{w} Q Y 2 ≃+ B)
    (residueToCoordinate : B ≃ₗ[K] A)
    (htrace : (Algebra.traceForm K A).Nondegenerate)
    (middleEquiv : Ext.{w} M Y 2 ≃+ Module.Dual K V)
    (hnaturality : ∀ (z : Ext.{w} Q Y 2) (q : V),
      middleEquiv ((Ext.mk₀ g).comp z (zero_add 2)) q =
        Algebra.trace K A
          (residueToCoordinate (localResidueEquiv z) * restriction q)) :
    SerreDualExtKernelComparison K V A M Q Y g restriction where
  quotientEquiv :=
    finiteSupportExtCoordinateTraceDualAddEquiv
      localResidueEquiv residueToCoordinate htrace
  middleEquiv := middleEquiv
  naturality z := by
    apply LinearMap.ext
    intro q
    change middleEquiv ((Ext.mk₀ g).comp z (zero_add 2)) q =
      finiteSupportExtCoordinateTraceDualAddEquiv
        localResidueEquiv residueToCoordinate htrace z (restriction q)
    rw [hnaturality,
      finiteSupportExtCoordinateTraceDualAddEquiv_apply_apply]

/-- Product-coordinate form of the finite-support Serre-duality comparison.
After presenting the finite étale coordinate algebra as a product of finite
field algebras, it is enough to verify the naturality identity as the sum of
the pointwise trace-residue identities.  The passage back to the single
global algebra trace is automatic. -/
noncomputable def serreDualExtKernelComparisonOfProductTrace
    {K A I : Type u} {L : I → Type u} {B : Type w} {V : Type u}
    [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A]
    [Fintype I]
    [∀ i, CommRing (L i)] [∀ i, Algebra K (L i)]
    [∀ i, FiniteDimensional K (L i)]
    [AddCommGroup B] [Module K B]
    [AddCommGroup V] [Module K V]
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    (M Q Y : C) (g : M ⟶ Q) (restriction : V →ₗ[K] A)
    (localResidueEquiv : Ext.{w} Q Y 2 ≃+ B)
    (residueToCoordinate : B ≃ₗ[K] A)
    (htrace : (Algebra.traceForm K A).Nondegenerate)
    (middleEquiv : Ext.{w} M Y 2 ≃+ Module.Dual K V)
    (e : A ≃ₐ[K] (∀ i, L i))
    (hnaturality : ∀ (z : Ext.{w} Q Y 2) (q : V),
      middleEquiv ((Ext.mk₀ g).comp z (zero_add 2)) q =
        ∑ i, Algebra.trace K (L i)
          (e (residueToCoordinate (localResidueEquiv z)) i *
            e (restriction q) i)) :
    SerreDualExtKernelComparison K V A M Q Y g restriction :=
  serreDualExtKernelComparisonOfFiniteSupportTrace
    M Q Y g restriction localResidueEquiv residueToCoordinate htrace
      middleEquiv (by
        intro z q
        rw [hnaturality]
        exact (trace_mul_eq_sum_components_of_algEquiv L e
          (residueToCoordinate (localResidueEquiv z)) (restriction q)).symm)

end PfaffianDescent
