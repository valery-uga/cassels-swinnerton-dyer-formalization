import PfaffianDescent.CubicLineResidual
import PfaffianDescent.QuadraticConjugateDescent
import Mathlib.FieldTheory.SeparableClosure

namespace PfaffianDescent

open Polynomial Module
open scoped IntermediateField

universe u

/-- An irreducible separable polynomial generates a separable extension through
its adjoined root. -/
theorem adjoinRoot_isSeparable_of_irreducible_separable
    {K : Type u} [Field K] (q : K[X])
    (hirr : Irreducible q) (hsep : q.Separable) :
    Algebra.IsSeparable K (AdjoinRoot q) := by
  let _ : Fact (Irreducible q) := ⟨hirr⟩
  have hq0 : q ≠ 0 := hirr.ne_zero
  have hlead : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq0
  have hunit : IsUnit (C q.leadingCoeff⁻¹) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hlead))
  have hrootsep : IsSeparable K (AdjoinRoot.root q) := by
    rw [IsSeparable, AdjoinRoot.minpoly_root hq0]
    exact hsep.mul_unit hunit
  let _ : Algebra.IsSeparable K K⟮AdjoinRoot.root q⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K (AdjoinRoot q)).mpr hrootsep
  let e : K⟮AdjoinRoot.root q⟯ ≃ₐ[K] AdjoinRoot q :=
    (IntermediateField.equivOfEq (IntermediateField.adjoin_root_eq_top q)).trans
      IntermediateField.topEquiv
  exact AlgEquiv.Algebra.isSeparable e

/-- A separable irreducible quadratic polynomial generates a quadratic Galois
extension through its adjoined root. -/
theorem adjoinRoot_isGalois_of_irreducible_separable_natDegree_two
    {K : Type u} [Field K] {q : K[X]} [Fact (Irreducible q)]
    (hsep : q.Separable) (hdegree : q.natDegree = 2) :
    IsGalois K (AdjoinRoot q) := by
  have hirr : Irreducible q := Fact.out
  let _ : FiniteDimensional K (AdjoinRoot q) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hirr.ne_zero).basis
  let _ : Algebra.IsSeparable K (AdjoinRoot q) :=
    adjoinRoot_isSeparable_of_irreducible_separable q hirr hsep
  apply isGalois_of_finrank_two_of_separable
  rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  exact hdegree

namespace Cubic

/-- If the residual quadratic on a cubic line is irreducible and separable,
its root supplies a nonzero cubic point over a quadratic Galois extension. -/
theorem exists_quadratic_galois_lineResidual_point
    {K : Type u} [Field K] {n : ℕ}
    (c : Cubic K n) (p d : Vec K n)
    (hp0 : p ≠ 0) (hp : c.eval p = 0) (hdir : c.eval d ≠ 0)
    (hirr : Irreducible (lineResidualPolynomial c p d))
    (hsep : (lineResidualPolynomial c p d).Separable) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : IsGalois K L) (x : Vec L n), finrank K L = 2 ∧ x ≠ 0 ∧
        (c.map (algebraMap K L)).eval x = 0 := by
  let q := lineResidualPolynomial c p d
  let _ : Fact (Irreducible q) := ⟨hirr⟩
  let L := AdjoinRoot q
  let _ : FiniteDimensional K L :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hirr.ne_zero).basis
  let _ : Algebra.IsSeparable K L :=
    adjoinRoot_isSeparable_of_irreducible_separable q hirr hsep
  let _ : IsGalois K L :=
    adjoinRoot_isGalois_of_irreducible_separable_natDegree_two hsep
      (lineResidualPolynomial_natDegree_eq_two c p d hdir)
  let a : L := AdjoinRoot.root q
  let x : Vec L n := (fun i => algebraMap K L (p i)) +
    a • (fun i => algebraMap K L (d i))
  have hroot : Polynomial.eval₂ (algebraMap K L) a q = 0 := by
    change Polynomial.eval₂ (algebraMap K (AdjoinRoot q)) (AdjoinRoot.root q) q = 0
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root q
  have hdegree : q.natDegree = 2 :=
    lineResidualPolynomial_natDegree_eq_two c p d hdir
  have hdim : finrank K L = q.natDegree := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, x,
    hdim.trans hdegree, ?_, ?_⟩
  · exact linePoint_ne_zero_of_eval_zero_eval_ne_zero (algebraMap K L)
      c p d hp0 hp hdir a
  · exact eval_linePoint_of_lineResidual_root (algebraMap K L) c p d hp a hroot

/-- In characteristic zero, irreducibility already gives the separability
needed for the quadratic Galois line-residual construction. -/
theorem exists_quadratic_galois_lineResidual_point_of_charZero
    {K : Type u} [Field K] [CharZero K] {n : ℕ}
    (c : Cubic K n) (p d : Vec K n)
    (hp0 : p ≠ 0) (hp : c.eval p = 0) (hdir : c.eval d ≠ 0)
    (hirr : Irreducible (lineResidualPolynomial c p d)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : IsGalois K L) (x : Vec L n), finrank K L = 2 ∧ x ≠ 0 ∧
        (c.map (algebraMap K L)).eval x = 0 :=
  exists_quadratic_galois_lineResidual_point c p d hp0 hp hdir hirr hirr.separable

end Cubic
end PfaffianDescent
