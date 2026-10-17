import PfaffianDescent.PerfectFieldActualQuarticOriginalTangentSubscheme
import PfaffianDescent.PerfectFieldClosedPointGeometricPosition
import AllCharacteristics.ClosedPointAlgebra

/-! The length-eight construction is attached to the original closed point.
Every coordinate basis, differential, splitting map, and quadratic-system
certificate is derived internally. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Literal original-point version of the tangent length-eight construction.
The geometric spanning assumption is on the actual algebraic-closure points
of the original residue-field immersion. -/
@[irreducible]
def perfectField_closedQuarticPoint_exists_original_tangentSubscheme
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (h4 : (hypersurfaceToBase p hp).residueDegree x.1 = 4)
    (hspan : ProjectiveGeometricGeneralPosition (equationIdeal p hp)
      ((hypersurface p hp).fromSpecResidueField x.1)) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) x.1
    letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) x
    let L := (hypersurface p hp).residueField x.1
    letI : Module.Finite K (DualNumber L) := QuarticNet.dualNumber_moduleFinite
    ∃ q : Spec (.of (DualNumber L)) ⟶ hypersurface p hp,
      IsClosedImmersion q ∧
      q ≫ hypersurfaceToBase p hp =
        Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber L))) ∧
      Set.range q = {x.1} ∧
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom L L L).toRingHom) ≫ q =
        (hypersurface p hp).fromSpecResidueField x.1 ∧
      ∃ hfinite : IsFinite (q ≫ hypersurfaceToBase p hp),
        @AllCharacteristics.finiteSchemeRank K _ _ (q ≫ hypersurfaceToBase p hp) hfinite = 8 ∧
        (∃ (J : Type u) (_ : Fintype J), Fintype.card J = 4 ∧
          Nonempty (pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
            (q ≫ hypersurfaceToBase p hp) ≅
            ∐ fun _ : J => Spec (.of (DualNumber (AlgebraicClosure K))))) ∧
        3 ≤ finrank K (intrinsicFullQuadraticSystem
          (q ≫ quotientProjMap (equationIdeal p hp))) :=
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) x.1
  letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) x
  let L := (hypersurface p hp).residueField x.1
  letI : Module.Finite K (DualNumber L) := QuarticNet.dualNumber_moduleFinite
  let hd : finrank K L = 4 :=
    (AllCharacteristics.closedPoint_finrank_eq_residueDegree
      (hypersurfaceToBase p hp) x).trans h4
  let H := perfectField_actualQuarticPoint_exists_original_tangentSubscheme
    (K := K) (L := L)
    p hp hp0 ((hypersurface p hp).fromSpecResidueField x.1)
    (AllCharacteristics.pointAlgebra_spec (hypersurfaceToBase p hp) x.1).symm hd hspan
  H.elim fun q hq => hq.elim fun _ hy =>
    let hs : Set.range q = {x.1} := hy.2.2.1.trans
      ((hypersurface p hp).range_fromSpecResidueField x.1)
    hy.2.2.2.2.elim fun hfinite hrest =>
      ⟨q, hy.1, hy.2.1, hs, hy.2.2.2.1,
        hfinite, hrest.1, hrest.2.1, hrest.2.2.2.1⟩

/-- Ground noncoplanarity supplies geometric spanning over a perfect field;
no independent geometric-position certificate is an extra input here. -/
@[irreducible]
def perfectField_noncoplanarClosedQuarticPoint_exists_original_tangentSubscheme
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (h4 : (hypersurfaceToBase p hp).residueDegree x.1 = 4)
    (hplane : ¬ ∃ c : Fin 4 → K, c ≠ 0 ∧
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm c) ∈
        x.1.asHomogeneousIdeal.toIdeal) :=
  perfectField_closedQuarticPoint_exists_original_tangentSubscheme p hp hp0 x h4
    (perfectField_cubic_closedPoint_degree_four_general_position p hp x h4 hplane)

end PfaffianDescent
