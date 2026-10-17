import PfaffianDescent.PerfectFieldConjugateQuartets
import PfaffianDescent.ProjectiveGeneralPosition
import AllCharacteristics.ProjectivePointCoordinates
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The actual four geometric points spanning projective three-space force
any normalized chart coordinates to be a basis of the degree-four residue
field. No basis, geometric embeddings, or splitting certificate is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem perfectField_quartic_fieldPoint_chart_coordinates_independent
    {K L : Type u} [Field K] [PerfectField K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (i : Spec (.of L) ⟶ scheme I)
    (hi : i ≫ toBase I = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (h4 : finrank K L = 4)
    (hspan : ProjectiveGeometricGeneralPosition I i)
    (j : Fin 4) (g : ChartRing I j →+* L)
    (hbase : g.comp (chartBaseMap I j) = algebraMap K L)
    (hpoint : Spec.map (CommRingCat.ofHom g) ≫ chartι I j = i) :
    LinearIndependent K (fun a => g (chartCoordinate I j a)) := by
  classical
  let full : Fin 4 ≃ (L →ₐ[K] AlgebraicClosure K) :=
    (Fintype.equivFinOfCardEq
      ((AlgHom.card K L (AlgebraicClosure K)).trans h4)).symm
  let q : Fin 4 → (Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of L)) :=
    fun a => Spec.map (CommRingCat.ofHom (full a).toRingHom)
  have hq : Function.Injective q := by
    intro a b hab
    apply full.injective
    have h := Spec.map_injective hab
    ext x
    exact congrArg (fun f => f.hom x) h
  have hqbase : ∀ a, q a ≫ (i ≫ toBase I) =
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) := by
    intro a
    dsimp only [q]
    rw [hi, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext c
    exact (full a).commutes c
  let e : Fin 4 → (ChartRing I j →+* AlgebraicClosure K) :=
    fun a => (full a).toRingHom.comp g
  have he : ∀ a, Spec.map (CommRingCat.ofHom (e a)) ≫ chartι I j = q a ≫ i := by
    intro a
    change Spec.map (CommRingCat.ofHom g ≫ CommRingCat.ofHom (full a).toRingHom) ≫
      chartι I j = _
    rw [Spec.map_comp, Category.assoc, hpoint]
  apply Fintype.linearIndependent_iff.mpr
  intro c hc a
  have hgeom : (fun b => algebraMap K (AlgebraicClosure K) (c b)) = 0 := by
    apply hspan (coordinate I j) (coordinate_mem I j) q hq hqbase e he
    intro b
    have h := congrArg (full b) hc
    simpa only [map_sum, Algebra.smul_def, map_mul, AlgHom.commutes, map_zero,
      RingHom.comp_apply, e, linearChartCoordinate, chartCoordinate,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h
  apply (algebraMap K (AlgebraicClosure K)).injective
  simpa using congrFun hgeom a

theorem perfectField_quartic_fieldPoint_exists_actual_chart_basis
    {K L : Type u} [Field K] [PerfectField K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (i : Spec (.of L) ⟶ scheme I)
    (hi : i ≫ toBase I = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (h4 : finrank K L = 4)
    (hspan : ProjectiveGeometricGeneralPosition I i) :
    ∃ (j : Fin 4) (g : ChartRing I j →+* L),
      g.comp (chartBaseMap I j) = algebraMap K L ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι I j = i ∧
      ∃ b : Basis (Fin 4) K L,
        (∀ a, b a = g (chartCoordinate I j a)) ∧ b j = 1 := by
  classical
  obtain ⟨j, g, hbase, hpoint⟩ := exists_chart_hom_eq_of_point I (algebraMap K L) i hi
  have hLI := perfectField_quartic_fieldPoint_chart_coordinates_independent
    I i hi h4 hspan j g hbase hpoint
  let b : Basis (Fin 4) K L := basisOfLinearIndependentOfCardEqFinrank hLI (by simp [h4])
  have hb (a : Fin 4) : b a = g (chartCoordinate I j a) := by
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hLI (by simp [h4])) a
  refine ⟨j, g, hbase, hpoint, b, hb, ?_⟩
  rw [hb, chartCoordinate_self, map_one]

end PfaffianDescent
