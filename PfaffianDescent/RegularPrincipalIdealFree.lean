import PfaffianDescent.VoisinRegularPrincipalProjectiveCharts

/-!
# Rank-one ideals of regular principal immersions

Multiplication by a non-zero-divisor identifies the ambient ring with its
principal ideal. Thus the ideal of each chart of a regular-principal
immersion is free of rank one. This is the algebraic local-freeness input
for the divisor line bundle.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory

universe u

/-- Multiplication by a non-zero-divisor identifies a ring with its
principal ideal as modules over that ring. -/
noncomputable def regularPrincipalIdealLinearEquiv
    {A : Type u} [CommRing A] (x : A) (hx : IsRegular x) :
    A ≃ₗ[A] Ideal.span ({x} : Set A) := by
  let m : A →ₗ[A] Ideal.span ({x} : Set A) := {
    toFun a := ⟨a * x,
      Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton x))⟩
    map_add' a b := by
      apply Subtype.ext
      simp only [add_mul, Submodule.coe_add]
    map_smul' a b := by
      apply Subtype.ext
      simp [smul_eq_mul, mul_assoc]
  }
  apply LinearEquiv.ofBijective m
  constructor
  · intro a b hab
    exact hx.right (congrArg Subtype.val hab)
  · intro y
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp y.property
    refine ⟨a, Subtype.ext ?_⟩
    change a * x = y.1
    calc
      a * x = x * a := mul_comm a x
      _ = y.1 := ha.symm

/-- Every affine chart kernel in a regular-principal immersion is a free
rank-one module over the ambient chart ring. -/
theorem RegularPrincipalImmersion.kernel_linearEquiv
    {X Z : Scheme.{u}} {f : Z ⟶ X}
    (H : RegularPrincipalImmersion f) (j : H.Index) :
    Nonempty (H.A j ≃ₗ[H.A j] RingHom.ker (H.ringMap j).hom) := by
  obtain ⟨x, hx, hker⟩ := H.principal j
  rw [hker]
  exact ⟨regularPrincipalIdealLinearEquiv x hx⟩

theorem RegularPrincipalImmersion.kernel_moduleFree
    {X Z : Scheme.{u}} {f : Z ⟶ X}
    (H : RegularPrincipalImmersion f) (j : H.Index) :
    Module.Free (H.A j) (RingHom.ker (H.ringMap j).hom) := by
  obtain ⟨e⟩ := H.kernel_linearEquiv j
  exact Module.Free.of_equiv e

end PfaffianDescent
