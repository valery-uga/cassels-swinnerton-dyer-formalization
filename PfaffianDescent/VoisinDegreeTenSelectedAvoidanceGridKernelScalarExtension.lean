import PfaffianDescent.VoisinQuadraticPencilScalarExtension
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridGenericFinite

/-! A native cubic-kernel basis spans the full ordered cubic kernel after
scalar extension. This is the four-dimensional counterpart of the quadratic
pencil comparison; it admits arbitrary sixteen-point normalized coordinates. -/

noncomputable section
open MvPolynomial AlgebraicGeometry
open AllCharacteristics.UniversalHomogeneous
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def voisinDegreeTenSelectedAvoidance_mapCubicSection
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (q : homogeneousSubmodule (Fin 4) K 3) : homogeneousSubmodule (Fin 4) L 3 :=
  ⟨q.1.map (algebraMap K L), q.2.map (algebraMap K L)⟩

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_cubicFamily_linearIndependent_after_scalarExtension
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι : Type*} (q : ι → homogeneousSubmodule (Fin 4) K 3)
    (hq : LinearIndependent K q) :
    LinearIndependent L (fun i => voisinDegreeTenSelectedAvoidance_mapCubicSection (L := L) (q i)) := by
  have hraw : LinearIndependent K (fun i => (q i).1) :=
    hq.map' (homogeneousSubmodule (Fin 4) K 3).subtype
      (Submodule.ker_subtype _)
  have hmapped := quadraticPolynomial_linearIndependent_after_scalarExtension
    (L := L) (fun i => (q i).1) hraw
  apply LinearIndependent.of_comp (homogeneousSubmodule (Fin 4) L 3).subtype
  exact hmapped

theorem voisinDegreeTenSelectedAvoidance_span_eq_kernel_of_four_independent_members
    {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {W : Type*} [AddCommGroup W] [Module F W]
    (T : V →ₗ[F] W) (q : Fin 4 → V)
    (hmem : ∀ i, q i ∈ LinearMap.ker T)
    (hli : LinearIndependent F q)
    (hdim : Module.finrank F (LinearMap.ker T) = 4) :
    Submodule.span F (Set.range q) = LinearMap.ker T := by
  let H := LinearMap.ker T
  have hliH : LinearIndependent F (fun i : Fin 4 => (⟨q i, hmem i⟩ : H)) := by
    apply LinearIndependent.of_comp H.subtype
    exact hli
  have hcard : Fintype.card (Fin 4) = Module.finrank F H := by
    change Fintype.card (Fin 4) = Module.finrank F (LinearMap.ker T)
    rw [hdim]
    decide
  have hspan : Submodule.span F
      (Set.range (fun i : Fin 4 => (⟨q i, hmem i⟩ : H))) = ⊤ :=
    hliH.span_eq_top_of_card_eq_finrank hcard
  exact (Submodule.span_range_subtype_eq_top_iff H hmem).mp hspan

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_cubicBasis_span_kernel_after_scalarExtension
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {W : Type*} [AddCommGroup W] [Module L W]
    (q : Fin 4 → homogeneousSubmodule (Fin 4) K 3)
    (hq : LinearIndependent K q)
    (T : homogeneousSubmodule (Fin 4) L 3 →ₗ[L] W)
    (hmem : ∀ i, voisinDegreeTenSelectedAvoidance_mapCubicSection (L := L) (q i) ∈
      LinearMap.ker T)
    (hdim : Module.finrank L (LinearMap.ker T) = 4) :
    Submodule.span L (Set.range (fun i : Fin 4 =>
      voisinDegreeTenSelectedAvoidance_mapCubicSection (L := L) (q i))) =
      LinearMap.ker T := by
  exact voisinDegreeTenSelectedAvoidance_span_eq_kernel_of_four_independent_members
    (F := L) T (fun i : Fin 4 =>
      voisinDegreeTenSelectedAvoidance_mapCubicSection (K := K) (L := L) (q i))
    hmem (voisinDegreeTenSelectedAvoidance_cubicFamily_linearIndependent_after_scalarExtension
      (L := L) q hq) hdim

end PfaffianDescent
