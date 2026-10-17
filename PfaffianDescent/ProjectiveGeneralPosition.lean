import PfaffianDescent.FiniteSchemeGeometricPoints
import PfaffianDescent.FiniteProjectiveIdeal
import PfaffianDescent.ReducedFivePointAlgebra
import Mathlib.LinearAlgebra.Matrix.Nonsingular

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- No four distinct geometric scheme points of the embedded subscheme lie in
one hyperplane. In any common linear chart, a linear form vanishing at all four
points must have zero coefficient vector. The points and chart lifts are
actual scheme morphisms; no choice of global coordinates occurs in the definition. -/
def ProjectiveGeometricGeneralPosition
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) : Prop :=
  ∀ (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (q : Fin 4 → (Spec (.of (AlgebraicClosure K)) ⟶ Z)), Function.Injective q →
    (∀ k, q k ≫ (i ≫ toBase I) =
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) →
    ∀ (e : Fin 4 → (Away (grading I) z →+* AlgebraicClosure K)),
    (∀ k, Spec.map (CommRingCat.ofHom (e k)) ≫
      Proj.awayι (grading I) z hz (by decide : 0 < 1) = q k ≫ i) →
    ∀ c : Fin 4 → AlgebraicClosure K,
      (∀ k, ∑ j, c j * e k (linearChartCoordinate I z hz j) = 0) → c = 0

/-- Geometric general position of the embedding implies general position of
its actual normalized global coordinates. -/
theorem ProjectiveGeometricGeneralPosition.algebra
    {I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)}
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsFinite (i ≫ toBase I)] [IsAffine Z]
    (hp : ProjectiveGeometricGeneralPosition I i)
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (g : Away (grading I) z →+* Γ(Z, ⊤))
    (hg : Spec.map (CommRingCat.ofHom g) ≫ Proj.awayι (grading I) z hz (by decide : 0 < 1) =
      Z.isoSpec.inv ≫ i) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    AlgebraGeometricGeneralPosition (K := K) (fun j => g (linearChartCoordinate I z hz j)) := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  intro ev hev
  let q := fun k => finiteSchemeGeometricPoint (i ≫ toBase I) (ev k)
  let e := fun k => (ev k).toRingHom.comp g
  have hq : Function.Injective q :=
    (finiteSchemeGeometricPoint_injective (i ≫ toBase I)).comp hev
  have he (k) : Spec.map (CommRingCat.ofHom (e k)) ≫
      Proj.awayι (grading I) z hz (by decide : 0 < 1) = q k ≫ i := by
    change Spec.map (CommRingCat.ofHom g ≫ CommRingCat.ofHom (ev k).toRingHom) ≫ _ = _
    rw [Spec.map_comp, Category.assoc, hg]
    rfl
  have H := hp z hz q hq
    (fun k => finiteSchemeGeometricPoint_over_base (i ≫ toBase I) (ev k)) e he
  let M : Matrix (Fin 4) (Fin 4) (AlgebraicClosure K) :=
    fun k j => ev k (g (linearChartCoordinate I z hz j))
  change LinearIndependent (AlgebraicClosure K) M.row
  apply Matrix.linearIndependent_col_iff_row.mp
  apply Matrix.mulVec_injective_iff.mp
  change Function.Injective M.mulVecLin
  apply LinearMap.ker_eq_bot.mp
  rw [Matrix.ker_mulVecLin_eq_bot_iff]
  intro c hc
  apply H c
  intro k
  change ∑ j, c j * M k j = 0
  have h := congrFun hc k
  simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply, mul_comm] using h

end
end PfaffianDescent
