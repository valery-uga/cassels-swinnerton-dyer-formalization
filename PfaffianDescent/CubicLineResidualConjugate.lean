import PfaffianDescent.CubicLineResidualGalois

/-!
# Conjugate roots of a cubic line residual

An irreducible residual quadratic on a line through a cubic point has two
conjugate roots in its quadratic Galois root field.  This file packages their
corresponding cubic points and the exact coordinate conjugacy required by the
moving two-tangent construction.
-/

namespace PfaffianDescent

open Polynomial Module
open scoped IntermediateField

universe u

namespace Cubic

/-- A nonidentity automorphism of an irreducible adjoined-root field moves its
chosen root. -/
theorem adjoinRoot_root_ne_of_algEquiv_ne_refl
    {K : Type u} [Field K] (q : K[X]) [Fact (Irreducible q)]
    (σ : AdjoinRoot q ≃ₐ[K] AdjoinRoot q)
    (hσ : σ ≠ AlgEquiv.refl) :
    σ (AdjoinRoot.root q) ≠ AdjoinRoot.root q := by
  intro hroot
  apply hσ
  apply AlgEquiv.ext
  intro x
  have h : σ.toAlgHom =
      (AlgEquiv.refl : AdjoinRoot q ≃ₐ[K] AdjoinRoot q).toAlgHom := by
    apply AdjoinRoot.algHom_ext
    simpa using hroot
  exact DFunLike.congr_fun h x

/-- Every automorphic image of the chosen adjoined root is another root of the
same ground-field polynomial. -/
theorem eval₂_adjoinRoot_root_apply_algEquiv
    {K : Type u} [Field K] (q : K[X]) [Fact (Irreducible q)]
    (σ : AdjoinRoot q ≃ₐ[K] AdjoinRoot q) :
    Polynomial.eval₂ (algebraMap K (AdjoinRoot q))
      (σ (AdjoinRoot.root q)) q = 0 := by
  calc
    Polynomial.eval₂ (algebraMap K (AdjoinRoot q))
        (σ (AdjoinRoot.root q)) q =
      Polynomial.eval₂ (σ.toRingHom.comp (algebraMap K (AdjoinRoot q)))
        (σ (AdjoinRoot.root q)) q := by
          congr 3
          ext x
          exact (σ.commutes x).symm
    _ = σ (Polynomial.eval₂ (algebraMap K (AdjoinRoot q))
        (AdjoinRoot.root q) q) := by
          exact (Polynomial.hom_eval₂ q (algebraMap K (AdjoinRoot q))
            σ.toRingHom (AdjoinRoot.root q)).symm
    _ = 0 := by
          rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root q, map_zero]

/-- Applying a ground-field automorphism to a point on a fixed line applies it
only to the line parameter. -/
theorem algEquiv_linePoint
    {K : Type u} [Field K] {n : ℕ} (p d : Vec K n)
    {q : K[X]} [Fact (Irreducible q)]
    (σ : AdjoinRoot q ≃ₐ[K] AdjoinRoot q) (a : AdjoinRoot q) :
    (fun i => σ (((fun i => algebraMap K (AdjoinRoot q) (p i)) +
      a • (fun i => algebraMap K (AdjoinRoot q) (d i))) i)) =
      (fun i => algebraMap K (AdjoinRoot q) (p i)) +
        (σ a) • (fun i => algebraMap K (AdjoinRoot q) (d i)) := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
    σ.commutes]

/-- In characteristic zero, an irreducible residual quadratic produces its two
nonzero conjugate cubic points in a quadratic Galois extension.  The displayed
coordinate identities are the inputs used when tangent residuals at these
points are joined by a secant. -/
theorem exists_quadratic_galois_conjugate_lineResidual_points_of_charZero
    {K : Type u} [Field K] [CharZero K] {n : ℕ}
    (c : Cubic K n) (p d : Vec K n)
    (hp0 : p ≠ 0) (hp : c.eval p = 0) (hdir : c.eval d ≠ 0)
    (hirr : Irreducible (lineResidualPolynomial c p d)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : IsGalois K L) (σ : L ≃ₐ[K] L) (a : L) (x y : Vec L n),
      finrank K L = 2 ∧ σ ≠ AlgEquiv.refl ∧ σ a ≠ a ∧
      x ≠ 0 ∧ y ≠ 0 ∧
      (c.map (algebraMap K L)).eval x = 0 ∧
      (c.map (algebraMap K L)).eval y = 0 ∧
      x = (fun i => algebraMap K L (p i)) +
        a • (fun i => algebraMap K L (d i)) ∧
      y = (fun i => algebraMap K L (p i)) +
        (σ a) • (fun i => algebraMap K L (d i)) ∧
      (fun i => σ (x i)) = y ∧ (fun i => σ (y i)) = x := by
  let q := lineResidualPolynomial c p d
  let _ : Fact (Irreducible q) := ⟨hirr⟩
  let L := AdjoinRoot q
  let _ : FiniteDimensional K L :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hirr.ne_zero).basis
  let _ : Algebra.IsSeparable K L :=
    adjoinRoot_isSeparable_of_irreducible_separable q hirr hirr.separable
  let _ : IsGalois K L :=
    adjoinRoot_isGalois_of_irreducible_separable_natDegree_two hirr.separable
      (lineResidualPolynomial_natDegree_eq_two c p d hdir)
  have hdim : finrank K L = 2 := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
    exact lineResidualPolynomial_natDegree_eq_two c p d hdir
  obtain ⟨σ, hσ⟩ := exists_nontrivial_galois_aut_of_finrank_two hdim
  let a : L := AdjoinRoot.root q
  let x : Vec L n := (fun i => algebraMap K L (p i)) +
    a • (fun i => algebraMap K L (d i))
  let y : Vec L n := (fun i => algebraMap K L (p i)) +
    (σ a) • (fun i => algebraMap K L (d i))
  have ha : Polynomial.eval₂ (algebraMap K L) a q = 0 := by
    change Polynomial.eval₂ (algebraMap K (AdjoinRoot q)) (AdjoinRoot.root q) q = 0
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root q
  have hσa : Polynomial.eval₂ (algebraMap K L) (σ a) q = 0 := by
    change Polynomial.eval₂ (algebraMap K (AdjoinRoot q))
      (σ (AdjoinRoot.root q)) q = 0
    exact eval₂_adjoinRoot_root_apply_algEquiv q σ
  have ha_ne : σ a ≠ a := by
    change σ (AdjoinRoot.root q) ≠ AdjoinRoot.root q
    exact adjoinRoot_root_ne_of_algEquiv_ne_refl q σ hσ
  have hx0 : x ≠ 0 := by
    exact linePoint_ne_zero_of_eval_zero_eval_ne_zero (algebraMap K L)
      c p d hp0 hp hdir a
  have hy0 : y ≠ 0 := by
    exact linePoint_ne_zero_of_eval_zero_eval_ne_zero (algebraMap K L)
      c p d hp0 hp hdir (σ a)
  have hx : (c.map (algebraMap K L)).eval x = 0 := by
    exact eval_linePoint_of_lineResidual_root (algebraMap K L) c p d hp a ha
  have hy : (c.map (algebraMap K L)).eval y = 0 := by
    exact eval_linePoint_of_lineResidual_root (algebraMap K L) c p d hp (σ a) hσa
  have hxy : (fun i => σ (x i)) = y := by
    exact algEquiv_linePoint p d σ a
  have hσsq : σ.trans σ = AlgEquiv.refl :=
    galois_involution_of_finrank_two σ hσ hdim
  have hyx : (fun i => σ (y i)) = x := by
    funext i
    rw [← congrFun hxy i]
    have h := DFunLike.congr_fun hσsq (x i)
    change σ (σ (x i)) = x i at h
    exact h
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    σ, a, x, y, hdim, hσ, ha_ne, hx0, hy0, hx, hy, rfl, rfl, hxy, hyx⟩

end Cubic
end PfaffianDescent
